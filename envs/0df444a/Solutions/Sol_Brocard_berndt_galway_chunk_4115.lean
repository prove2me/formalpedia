-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4115
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:36:48.842806+00:00
-- url     : https://prove2.me/submissions/2395d3c9-97ab-421d-9d5a-46c130c3041c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 739928057 ≤ n < 740107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 739929307 1250 739928057 739928087
    0x30315080a0210111b0306070f09090f020c19120509010503240d03080109150f230901090c0945060608010306230606310501 55
    0x11098103110180300040c00000041e0100d5541124030962101221600540304540404e401000d91446083d090b5403c403807a03c800450076200640d842440440d503d0b440c001082c8000b9420300310070410021290301c9182103140c982c4000d8034280d000d03561039203418081070102e2040c044401d011424044003441040d28180fa0345080391410f5131110008109010250240480c1240d1542445419190b4050142c000c000580060f40807081e506014001c1d04e001d00c22801441e0424444003c580300c1001014243c034400c000309542c1c141845003d0710000d0b02c0807004000144008400603482c1d031a52059402007210020100c2e4008480d000209112807660080001c80451060403022030b5090402450022100510354040a07014140c280ca8451750700c3c1c500c1d071903860548081030095003c40b46a0580303010701814400c110402d807140300c02010b910a4140300300341d03100110381c1ca86043e80082c10440003001c00b511241032545041c084031a000440300008075044c4104010558000382d1070181109 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 739930557 1250 739929307 739929341
    0x703090e0106031406060a0207050a090c0206091c0807030f020f0405120f07061103090a09021e04050d02010e01052b0e190807050f0d03050106030b060306010c021e06030906040303 79
    0x200b5020385090340400500071074841e00700407c101c0b240d64800c00540005150007401050002c2d5510281c10090800a0291006002e80c00c00100e40c000c0001e055002c0d21003420000074100540c1000319040100685072108040e22504a070b100c0d45014000b81607a040744030305081e03555140c10100140c94003600310481483d001003103803074000c51002c14100102c03003107410a5448207104280c464114418080d21035030008600c500401c00201c40e80c0903040d00c0143c3c101004802031840700240d254001d80c0324880e400365540c84400d0055204012002c40c04106041041c10031200c0600100f5800015143c0744021140c0c40e021248400c40d030151903042214803014015a040d5408000b40742c24400e08050300380c0704006540130030132804011841d42e080c20402914040a0035150042c0940428400e60307000a0403c01a046285081c800316401004140c41710195040d1560078440100d0301c60f1011603100c94040384000040c0c880d5002140f0504145001e007030316140901e405000c48102140c00f031a000c0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 739931807 1250 739930557 739930571
    0xe090d0f0c030828050c180109030506150103060918060c0c02090103120216060201061a03010e18010209040905010b0a0905131e02120d0809060601090b07080f0703090e010603 77
    0x2903040f5a80c25004407603c20340010321944180711800ca1500342c2030141211349000d040012070484440500341c200140c03154101c81c02c0240700112407000792404082e14a0300094007003503582d6400ca084000c481b0b01030402040440ea81c19a003821188003445650318a024402800104280b501c2607003150304180c14006540f42c001e801140c944101408024148040c040792070541074020411a1007120486a00003510342d143e21009001c1c0c1100d20451520900001420700f41c103402c0d000743d9058035080150491513039126030304840c802d251648200d805560805c814440d54542d230041c2980b4900a4001040010744007050103a1003a8592041410a14060074000e85a68040310410b8541d00407180d40c0701d1040100c100c580000104034000c0d8002c014044040c01c59802080709510040745885545d000c0c0d860720b101e41c3d1107000c2125074a00142d4103907010301c5004400c1c006010b4050160144600b09100319204c50101e0b80941343c160082a561746d804c0000e03d503812500f5016141500d8180080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 739933057 1250 739931807 739931813
    0x1403090709050916030c0801060506090d06051009020f25050c1509040204120b0a33080102030106090f0f05010207032a06050c0705010e060909100e090d0f0c 69
    0x1034040d03015206405440780302094503000100b1400040f00400b440d85070001d9643e15160001714030074424007171203508100c00001c5510b440b0040d181c00c82400b61107041100380b240e40b01380c0104402440760905029480001c070b440101480988400803040c41020b682d100001200d00c02c000c04841a200c2c200100e4200800040020880e854103e00c00d4600e0148500c2440c0380e44103d015074040280c005101180000d02d0000e4030381940171590285070b00701515140c44450405560061013800480501403d154810070004080703038641001c908010701400b622100c846007a43e0083c1d01203400145440403d000c20007884429400400c6e0b0030510940c114a03250010351100030921003e8040d1105540181c1e0003240e4002061446c82400781c5078080070b880d4500070b01079821074a503a1006110700c03000403c4650081540d8103519a00429607820200d850703081146c00540100403081e18061354034001102005500b1407405089940003601403d00b034410024040700b0610100b208000c003039480d031704c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 739934307 1250 739933057 739933063
    0x20d0e0c0f030f0d111207050709050a0218060d09060218090106020601060e040f142a040608010e0901090c06050307021c0e0d0203070815090f060708071107150c03140309 75
    0x4200e09080c1034103c0c1884180c0941811865061b85a611400051200410001140c807505031b0b140c4c00c404000365101d20380c0d036074100d005403103c8014403116500480084d02d0000d028041342500101d02048150390303503440c071082c4e03000115072107040304100320b0f4403a40c1d140a44060380900028802000258900034000b4055820707015524043c5503101410f10700b6414070f0700700070f1110300044d14240c85030900c00a1081d911300340d442503080380c0e01d8036040051170302e03901c0c0100c078100c0c0c0c45952038030105c0c0d0905501001c00c00001d001c1c1700d403e42d13030740c401d8600140c08680981d00420003070b00d03116200d18090780c0180c01d00d100c00e481c140143c0a080071034503001d50070250441140ca0150707400d859001035840401e20b801c2c2c07540c00c40803442c410103c1d80b034a402d02c00e0105600c92081d4400703403060070645040141d9100020f890b01404240300030005111903110b002d007850328a80e91000c0b0355134241d17548103040b850500c01e40f5100004032507440c2041410f400a5910030502080c58005103546020746055807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 739935557 1250 739934307 739934323
    0xb120a08031311100206060103151d100807030302030c1605010f0503041419020a0f030f0213112a120910020c1c02090c03010e0f0703020d0e0c0f030f 66
    0x71040c01020300400a2040d22000710f40f46038000b6020319290400050041d6072060308551590019090050030700b0700b041c0154141080300c00c5a18660100c0b10070194081c0d081e040205146001c0d055101d001589900c01c100d20401140603802840c0c0d99034610203114184911045408440c2e44002c40401080e64003041c1c840c1ea420742031400b683c503a1214540b0b04015107540341c403082d49102d442e40300f0f400c1d50340540001403014400c80d100c5009659450f14001c800005c4e00c03014000100c8825040301505000d10f0b030084c00c4a0400f4000381e03d52403500300e034040c0c0e0001010150030103d5844600310081030a04aa088400c0c0440148031550020305903c030540704200015000b54010008140c40600030800070004240040ca20303022010849c80241104134803440c264800d800328008034010056980c00c90f03059440d05201e0201c0ea60b40c80d40080711000e4050080c104269082041c2c4124808500c50404148410006023404c821440b0030045122840b11b0810322980241c62008a5002c000900c0c0c0b0f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 739936807 1250 739935557 739935571
    0x708130501020601210b04210306060e030a0b070e03031909170a0b0c0a23090a170d050a0519110d031103150f0d080c010609090f0228090b120a0803 65
    0xe00c903940d845c078140c210303244900c1e111003000d40d1002d4000001602754116805030303600c49d551401d81ca4181e004155071644202c5004d00001d0044021401041c410011031002d0b10000e021207281c00d8465414020a0b65448144800202980400c0c4540a4102183c088000c290b1006100d100d0954a902c0500311011381350141d60440014080e1105001c1c0d82c00c81c490382c2c00700c841c84010414105944000c0d40c0046002c81c0b0903010034901252801d03049140d00f09941d0603000030f050405601605031450382c03000280e001405014896107203c070012510b180c044260380da80d44030380300c4e40002d51186041c0f1072019420a06040200ca58070704503c0c030303050300c0d03000c84108013161054030b490340440c28900e240180584c1003101e04880c3c1091001407030082803104603083c02002982e032b5584141c401c0310803005004007030301180883d1602500e400710002c080c50515181e02c1a060103c0703000d9902d00b129541c8a0300c001622015034180c549410b003030104840c9414009001c07940d210b56036042c01840010902 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 739938057 1250 739936807 739936823
    0x15030b01090f0e150418061d01020a1d03011b0309060f02090d06090c0f0e0907050d020a09091a0a06030201021b01080c0d0e0a11040516091505070813050102060121 72
    0x341340c1a640ca42103076241224503140a025906a41814009084102e150048008015000d0010440140308440360880c095440011801d41d82c100c590142d06d1450446600d59241e90100b44000d0016942e0310380c549007500d000503281014500b98050780c083c0115800140d205114280868071000c8001240a07409040003035050800d203440306d1046120b40040b501b120a4200126004036000c42c424003556804040b226102e03558810006502c8024000a42000313401904210180440d000783d901540300b00d03541c10403a0302c01442100b10b250108c502c014041d0325104c1c200190358060084a0300c60b0f8000700900e600340d0b018400a05000300250250702d5203140041c0700d0021410591054198106140603038181e0500c9042248000141c1c0d18040d00c100d2071728001c6201d0302c054400c503009007a40340e11103000592600182c0800000e58109110a101c020040c10000482003001408964240e2082c0e4100c0e034140760009141401c140c0010003401c11640c1d0703110644c2c1c0e020400d440c070141d000c140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 739939307 1250 739938057 739938091
    0xc0501050c011407022404020f04110c12040501120b03031614010203040803100509061f020c0303040306020d050711120f12090709050a09021804020a15030b01090f0e 73
    0x2141e0040c0581841e10180d40c07615418803400c543e0118110014101d140146c0301500300c402c04a582158050710025801115480e44900c0c40c140307070704050380c0c0c406d285800504020400001c4c5040901d100c0104048501c00503040c402d9682040c0002d000e0346902c1010013000c8110008281c1e0b82c89156515400f03011500c145004000108840f2241510342400964490406240c15070060b00309032a01c46032003960f4000420f080c100400003d00c0303180010040950001608510101da4101540d420b0450150394022005514100010b00095214201c0180c1c0c94041900c90001c0300d002610070801c011211560000c120701c0000c3c0a000200c02036002c5590f40c9061240c002688a09040074914800d01810448140700c04103030113003180d0b8441000d0000ba9501c54a042c1200c440c004029070008907000100f68400c0c4e0920403591203817000d04400d00003600c80f0f190140d8103c108080400117907c942881c0900d503441030011005125100c40395001c40e040a01c2d125241100a0046015840020f4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 739940557 1250 739939307 739939327
    0x50a02041a0d0905100b01091d07110c04320412140d0515030c040b0a0b09040908070803041e0201090303080603010f020c0a060501170733031d06040c050105 69
    0x21240f50156030003400c4890260910030044050494114014041081d400c000504803103400c0005240700a02c0090340d00300e9548107010f442e41507550088a00c80d00c5410300140f4251242d1080e0f6441c5c621340302c6203014065140b241c0c0c40c21586809500021528981c00f071200189214105109208050070040311449800d00d01182d5402111081d85400b414a81440221040e00640303560444040d000d50f099448000d0a220070345a8081a0a4024503045c80400c421607200024242030308006001148e5039105440c0d0303240641001501b034400e00000000e0104002132180c0c126a40e0300821000701548009800107480d01c112448044d080c04620000290141d0b0294007610802c200a40219241da82d000129035035011401401c540080c0b911001061440582030400e500d003150400a001c1c544c00c1250f001036540b00e18002e4038040b890768038070404c040100b00d08001c800e1036503500001c021500401d96490f40500e05800c003400d40014080c000841c40c8070200358187e80003800e01580e942c2c5200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 739941807 1250 739940557 739940561
    0x71d0415032306070c03030c090b030105010f020102091315081504140a02030d0210060605130504020715050a090308060d1101181e0f050109080a0204090f1203050a050a02041a0d 78
    0x1151005406050200315030360360003031121740e5042d001e60382c2008801c000303084c266003201d07403401051035004080c00100510b6108505d010030a00b654800076061000341c4000c242c51141001d03484c1500c64031501501600301d4a200000010700141c8000c20b030080803032313950600c0540040c0000d094504500301d40c038401c0c4030030020181015805011124541c06600c4c0003901d40b141c40014040315402e248002411621420540e000242c0131071640104928000800c402507104060440307050680b446032450001c181d100b458480c844401d00030a0700b070340f24036000345030390303801000c1c10b2107600000380d8500880c1d20702c00801d82c54482801c2c40f02203106000b1b04588210103607400492280402094014409691007024044454a0504150f9144c40741c0c01520152810300a03404280c3c8051740140240c60f05800540300c10b4050030024011082640303801d8011007007a20f8030008240c840c410700010300a1846940d034000401c80086007420309200ca809610018041c005034458004100008150229 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 739943057 1250 739941807 739941863
    0x3011a030c091f030501060309080301121103070605070201090b0f1e090312090f010c24110f0a0207090e12071b1508070203030c030c0c0a0506071d041503 68
    0x800f11840d01910501c001c21918803200f83d240064101800014803c0c028050081c40307540c44a029400c40c3c0c00e009103c0503036805001d0984002c501d5401403030039070302c0038051a8050100c2c0c0e81c83c01d540b03c4890001414800301036001d1005520108101100302034503506980078030b00040f80c0c0c81110241c3d40c3c51440786000d11213500340d0500440082d101c0c6440300c2001440c5078001a66511065100400195080400d05030302624034400554050050920300d20b66026036503050600186503060101d481c805500071795480101083e0002d10501c06540401c00b000050003010b4050002045c0180f0203521003600000d114100b85001c41d030142040501091002c5810040f481400060f0f5100e20300740b8903918218815001c40c3c1c0282c0880e0081e413002c4101e0b0710649404000618644030031143c078000c0e074810b1890358610f0143c200d26030005501401039900841440d954000780381c00341ca01d2030340c40758101c4407424401e91420420701c50b5201d132a10440b0449402286180144403880400b040220364 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 739944307 1250 739943057 739943059
    0xa0c06090f02060f2814070311070902120a1a060a050405190611010e0c1c02181807030b06010e0a090c022b08040b0627160503011a030c09 61
    0x108003044032400312805000d5040901c0400e1090709490031906007440c2c01c01407220f001482c00090104070351b000c100101030b500d129240c001618040724903528105010790b0410030085400090a0201100e1458041e801070040b9004000801d08041440486a0b543d070b08507004060210700911142d0051081d00d00408001d040e0f202044154000360880c00d030701d4080d1502103049c41341c140005440503c510300319000000006d01207607030008100035900300c01c11010444d1300e40103d42e0f1401a03c48454031602c400540c9803001050501c548000e030341c4201e0588135103465021031403c0006c02c00703412005420440a00f40400030035406004203601e51103641041c0d603900c1c14602c41c0500d0640c00648070500240340070a010503c0c4504e10010002800c1c1e424800005010b80003150128440e044015004880282220b079514102001e0488505081c41e680700108d420800b0418500b01c44021805406007a140652030340d814815424204618880c854150301c0c404400110302001740c0c000c440344440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 739945557 1250 739944307 739944319
    0x40902040b040e0c120a0b0f0d030305151c060c0e030f030a0e04020921010e07080f060108060712020c01060302061210050303090112150e01030c17030a0c06090f02 72
    0x41c8a801099155001d40705112100700c102c0006100c2d20070100a490031a40142c4d060403168a446072038074040d000007601254002000198489155640c411000000d407081e1008078540c9003070004a41c200b010590564011102494078203000f0356909030642059078040f10000d4000440c0c0c1007216000e4015100039003601c03800c0d180c00d50b0f00000201510748200b603a510b000140f8083d000740404d900501e070819411400c07002c001510103041c480d0603000f401d501000000d1030304555100c86e16100c0039034017800d4250003007038002d010581e040c410b041c0500400002890242081500200040c4850901d0410075070b01146140d07103000b0a40100000f550014400303501d4401c0529034003102501030380c802ca910307501c2c6440011a81004000c2c0c40c04050141c44403007902c903075604040c1c040d02c100d00011103010001407000c500c40c00b5840740300d8080c1d802058000031890414902160011141e1002e2907140d100f4400303c2152039010446508865001001089500d0b4a15020620f4158240000d601c86 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 739946807 1250 739945557 739945559
    0x20309041a10180902040605040302060726131410180b03010e0610030b1f030204050409061d01140c0a1806120b091303110a0501230703050907061404090204 69
    0x240d44414030f02c140501c2d6500000c9820b03940e9208204900c81c074801d0002041d0300b0701c020000741ca0708801400c1d000780603000c1e0084031003501c00700481481104840032468076010951141034680b0b0b5402c0d8003d00808822100c03001004400208001400c03052401080090503914040030038100c0510300600503141c2550b10b0b0750312480e030007090711000ca40d414000d60031241e28441480c42030180b88a401800b800d0a1840b0030214103000740203103183c00110603da020000000d6640b164803421050500841d00000c0c1080c12595880040c4c1409050301d8040e81000007007202d034200c2001c02030b0022815000165114005441a2002c210f00752080104032030715240040d94135040080351140d0480f21038104081b40c804400c101401009450b882092060030301108002401600f5a80e0048442c50488485207a0760781c40c13500b56680400301d414201c00d1261941240c41000d004a030b000142800d081c401c514000c6620342da162220b03c14403007000405a000034060b4140400c9030080e2100500c01d540c0c0e6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 739948057 1250 739946807 739946839
    0x6230402210411040c02030a08150f03030c10060f150509040b12010b03100e07050607050a0c030602091309030f080a0f06030f14070e040809040609020307030b090106080601020309041a 81
    0x40142c0c0c3e40c089002d82c3c1002105500103101008440103407074a0380702d80440742c0b24032248021700050401d4003a000304480301c0c540c6a0380d03401c002414800052500407c02cbc0c0e410820803c0948501d94040039000c0707004030044c0030184841c80107940c0c0e5800e0b8a00551150800c3d00051f02030208886000d40000d203101c50301d270074540190070260140030150201d80ca01a01c403075030341c41100c8183c0080b120b290800c000a1115190a0009040840c000d008480030702c415030310390fa80220150340c4212401c8d5400a03402c0d0550510f030075000b403e80754030001001428540c2c2c401900c09019821004104844000004d07507001c41c40d80401c44101c0021820003072191a0f150000f90030f2240b04041d83d49243c83c4140204d0b9103400210b00040d600d8415142c0300a4441d0ba0320010680c10559890398017603200c00010820001501c00703544540040d03900401c01c0880902071004030700c01a000b610810140000700406640c001044410703242066a001406040d0600c804400801c100303d510ba22000d01c1d6400303850307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 739949307 1250 739948057 739948073
    0x1020a121107122907050a0c050708060c0a0201050c040302010e0907030e010507050c060a0209030721061505040e0105010e0c0f120406091505060108181c03060801062304022104 78
    0xb5219142c4c4c8071102e0700504e040201d05a090032500000010820131041800d00c1c4103c000059003881074044603103a94032656250308043c2c040fa5071080082001ca40070015603070900170307603400c581c450242516003070941d00000e00c0c2108014030300d030240f403901c030100701424469842104c8940151000300240d0500980007091980094503040301c07480f03504042581010244200d0b8201c50f0010000c0116038600401c121710501c0c4540340700d10031024038491801058507401100c100803100090000c4113414203041000710b840b1400100010f0307240000501000d04040045900421000c40c80da8880000d01c3d4a010325106003601d0104081c482402e0204018031900700703880142c030441082215401e100c0403101119401c5682600040001c4003085a18544400c82607801c103010f801d686281a2a1448515120a6003144400695103120422108900384201030242140b0b010300c4d21581c516100310207040801d81007070f0b840b49a00082001042c02c5080701d10105501d43c5203804801d140c42c4c1002c0034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 739950557 1250 739949307 739949333
    0xc022406030d0305060d0b04140601080106150f080a0e010209120d032306060702040b090702060604060b09030715090807030f11010504060219140a0c1401020a12110712 74
    0x701910942c0440c0709424082e0041d41d100b800e000d007890848034003a40340c0c5080d2503c01b510a48a00d00340c94000d60381a0010f215081c041c0c40340700300109006c0d01c2c00030502001000302000c40c0c00c1282c0b441c071250403a50700c90b0107075400001d075102c04101000005265402489504991540010100c07440b600713201c80801c00a8002c440e0b520108038078584591407102c2991402c17249000a5800b60010300c0e50f00e4110007a210b21400030b400092035081c6407011620920041e104240540d011004000051405015401c05070007011481e81c14590404e000c0ba5980500e07000f61450075000c00810f05510344102c200500802c92842201c003115038a04103444403442905080d240482d410a0050080d4003e000721400c650302a401080180d14020030190034080481046620252564110483c80020458614054080c0729850051441c080800c2028034410200d5819900309805000100e00c41e5109541ca42c1c1c11030070140c0c01c1051414506042900d44c0d0070980c502c098a241d050103002d07523250441 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 739951807 1250 739950557 739950559
    0x71106130338062b0b100f080d03021804050103050a061b0f0e032d0f010b0f190302030f031309091106030919060606022104051e0d03050702011d0907030c022406 71
    0x1813906c90301c2c0c030b503141761121040c002c2d00c1031a800240c03e04005071083c0d005214504030000c030840f0312a01407001800f580d0003a803050f900d5500c041558014000c0510030684184c0200480c42c084110b8484041c1003404090f580c2c1c4103020074804c12881549090280e10031204548040410704c2509007803003071092034194440b080c640b0907141c0c06803d40c40c1c1403180092100f00240707120071101c00101000101c3c20a20659034481860250010051300c04118040281c40c464000c0d640b1002c0b00302245416103c00c0d8009944581000b00444c08103880c4201219001d4007503031115529503828109926210a0303100e9509449903161880c000d002099100788259409a0b094400c004508040c28500c8592030700c18007400d92007088104100c0c5010410004084c11006903c0d2648014030001051200300700d50a6000c50800540c000440d03030302580300d004484070720001c1c1009003094000f040c3e1000006282905043d6a44400780707002c0d008004500c060003501c02d0340030b10008801131b100400801594a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 739953057 1250 739951807 739951831
    0x6070506040c171221040803180105060904110d1202070603052511010608011e050c0f0d02091203030a06090f060605071106130338062b0b 61
    0xb00d8030041000c1614940700c0300302d00408600402510108566100a40c0c800481141100d0701e460781d8145da40051140c0e0092030b00f1a105c3c13401020342061014842a070f00001c0e45001d040010f030b030b030b01c00682d42e400136002880d142200c0054130116044c001400b50240110340c20b94040006a0360000310141540c001e0f590610640c0c40f051944490301d8108656081044140c2141010f080c0c412010401c0140c600000856441c1e6110035890868201e0744080603440d4210302c0e40820f040141c056150003030b10951510740b600141c0203030007030680030300c03180850103d4000550044584d11003003a00010990641901c0e540d00700b45184c0c1004099074421440401e0a21003200d01d841e6044c455842240c0054460520303003c16503541280c00011012480d9128100384481c03d00e01d0041c0f2036600145200d00720145004140302c048800510404118103980440505031601030f0035205404c503085101030b1240051410750030000310580b00c404031106200840800540144039039681000e010708920642 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 739954307 1250 739953057 739953059
    0xf170d02030a0c0e030c010e0a090e0f1c02061f05130911010813031101111917150d030c02150a170403090e1009020703052a120c0c06070506040c 64
    0x4199040b035001304056500d40c100080020555000705180d4130030940050104001a1321410084215085400b0b82404e55000c0c54106420140401203141d40b036645501035940080c403114000e54807000106159250b09408464000200380c0340b00f404003410004014030416420000d00d800141500101138546005194665001d035020340460790040c00d000c10140041e0701582c03001c2d5800380416014051566035042e207122484003d902921012604404551a945a000380180700d441d03d400c9101203c000541408524001c80ca0501c098030000d4444213403005071800e080d5030108007408040c5d000120078581c442d180303142034020b2030710841545420380d10020481d0b041d140404100c0d0001c020a010030810f000500d100b01e0403075800030780703601c03000d450035111445501aa00f01500450202e940890850010703d290510386c00280030b09000f01100400c20080540d40d0011440c1c48407510900042c0c120b0800c0080c803003809100006072003a0780d40c1d5072170318003295940c60450f0180c501d40003401c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 739955557 1250 739954307 739954331
    0x70e130605060d030e100c0204180b01080304060e0103320618011203051e0a120513150c0525020f0117061504031a0106110c06070f170d02030a 63
    0x669038486402d81d1740c10040c07149510600000c074070034100c0c030014046d00341040c0b001a5108c1c017845401d4000800c560680020910f030034041020107030003040051300280001c0c0030803a840140900041001d20b00820700d0464041d8090094051b9404a4001712403510210104040f05819602802007a16000700800002d20801030003c03082c002c0c059520200f402c49404a8810406081080c0d60080302c0400d40c511540500d40d43d50122038108042040e00b1139001c000903503441000d9000e00c210a90403024080c0c0c0c2d031120740601a158070b81c0405a03a84100c01d61182c441d000359443da200c00c03041c400c180c1a080c0040000e1090300c05040303101d042c0c0318201c003040d54490b820f200d1501a03041c02d80000e070b0300d4803800c0250401d41040c600d8868142840b000001c5405000903032020502d9490308403095050280082501c04411100f0407141c4c00340c0011580750302d030031b0110390586801c10f40c8501c01d01110b03c3d00c92658002016400c4901c400400c00924030001940114069401c2400400041003401c3c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 739956807 1250 739955557 739955569
    0x13150e150412090e180c06070308070314070e040509120d1a01090509010b160206030c0d050903040602100e0708160e0112080a0e130609061d1017070e13060506 70
    0x40034081138900d12001040044e8207140d036044008150300d0684840c445034402140003500140d50a400290390b4401740900581c00d80300306c072801803003248500100e29152001600c05035000e20140c0c000d0342c0d100005602e454051105d8106421991078003507485101e0820000a00078a5040c10717000030340b8a80d049030319800345810a00305c0c3c00140040700d05a11b0f0001408294014a05514002c240c00303c5210041c0c0e62480190f00c6050140c01007600d0f0150080904101c030ba0040c4584200d03841000103100e560340001e82a100326100e1072000c0b801005c0461b045007004e005500002c010302c0b4014080c003542541c4207100064035000758585440d80c1e81c5080c0480040c403401c6021380091010000d0010503845107a07017900e0601c0c068088040c110b000b141ca1411140e90b0380c0006000c4e40d0315a0140304c0e400049120080c3d00300c0b11b10001c4424180244c0320b000b130401d03030320650614130140c45800c82c9446017407160340f008045510304220b0601d00855854940406101c04640d40752801d000600c2030700e068 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 739958057 1250 739956807 739956809
    0xd4802031612150e0a14031201030b0108010516021f060f12030f030902011b291e160318120f121a0f040e120c060f13150e15041209 58
    0x6000240340508060b20b46c2000f0a004885100042c001006080700400308105518000c512030131003000e0750b40c50030500c00c0c2150b0300039060380d9030b507054a03c01c41040c3e980010540000307548803180c1903080b00104111030040400ba07010042c10320403200006682c4245400d4000f040740280c0340d1804820702c5003c21000c035406000000d010459855031102d4046c1e2089948842c80d20404038960200c1d000041007019850f2034210803000e00b41e800c200619403810300c00703818036102d040310184800c0c103104106014006100b500d105c10581e42d060502810400c0c80e41007041c980d00301000c0c02188087d1341c3c0003007000750b51030540c20128020040340100612640320300346a1045401c08224080b031040b0400c1190a4042651a48551030340d494003100310701400a04610221960680e45d15410711a809081c13510092909182d04008001c000310003001c400c42007025540b040103800d045441014100090961b400d0058017840b6148440011618902c01d180c06036000b12003000d0840302e281021180c110003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 739959307 1250 739958057 739958081
    0xb0901030c1e03050705160620070b0a0207020a1503020702010815010c0b0a021e0720030d08040317090d020f01022104060204080d480203161215 64
    0x403404146141611a03801305410070395500c0d05601d80145009415207210600605840c107540e40c0d235460b031125180740303510060a1000e048207400c1c10400e4486a01e680802002d0203001038001030007104540c0c640d9403000c040c21500c035409109003c040c0d40103000350885030040703004c2404407000c42c5031590303c3c40d041c041c4074005942e45140040c2a030750b13072500541c02801000c1d0319902444402041b10900411a0312069404140340e1105280c2c209400c15034901003414007200d100c100c02d00c0d99a00c0c04100345131120060b040035030107900c80d441d04550351503054000000003901c10080c800034800100d40c400211809500710f0300e40392248001d0a080b0f1040b9600e1040307903d2182418100d5842610b41d0640c000d001313030001400c069581c030300342d42400b16140c54140011915030303558101e410351401d0480c4101107091142182e130a080203c3c160601e5907040c120006001c40310304011950304102241034002e00c0040c00c0c42c2159141c1c524050b0042140c0d044500740c1d500003d10f2000311300d41c81452141c443d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 739960557 1250 739959307 739959347
    0x180303030112060b01030b36090d050a0e150a1d010e041e1401050901090b221b020616030e0601170a080309030306040c05090a051908070b0901030c 65
    0x8100d0f550b400c000e113040104281859190900c00d895a5180030010a9840098440605d690f1800c0c52405040c21103606651907181302c0c000744045030000203256400403005003016a40e46003c01c0c0181c4407100070700102648403240e543c88227168004000a000b2241298807641404203c00d00342141200c01c1c6051280000d02003001c3c000c47d4a4a600071800080c4d1480c8452001308003003150000340c841300000d04c5814004000100035070b040280a80f401421440c00411090004078001140a8106e81e00c00c40000d44043d440c02e01c0c810198402d8501034035013088032680342100700000c1d40702c200449000f04540340b48002e4400c100d009001d5201c1000030b03240980543c1e8204201c2d44d400720744413460183c030303807084081c0180002d01c41300c000c5d401084898015034480c980403081005035400001c1120030408144070341450317074450700810b805880013243c00c5081c1d20302813850040300a08139070000000c1d00c110a000030307095142c50020040c1c10020b9074140000f51410f00117440c3e0704040e42415611701 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 739961807 1250 739960557 739960589
    0x3020313061d060f010e0c040f450605150f1b06070305090c27063c0402041a0705070312050c100b0307030f06090203010606051803030301 61
    0x41031a8818442092441007801d40e0b40250420680b8003202112044945080d20005118510003004070a9026044241e0300b4a4141446207605185a00d0300c21a0424040421040740000c880b55408000401655607080c0c02e50244040d450b29548403084121000d28254010a80d410224000741031015137050b09031521a030640401d1555019541402e0300e01d00966910a040f503050100031f0180c41566000300d241c0c00c0c003170002400e18044246261007012452041ba048503245414440c0600c0101550401c0303949200204904500c64426654a082003c0f0301e41126940601c55100b80a030b000e041107002410315050108030301c241e000e40a11a8140c41d010060b6400080051076058420400e0303031002a41c99480c00481e80c1002c05d28404600003003005a0101c000708040180852544820b01c010401c010100e07031182d44501024100c1205101c0b402d0a100c26504500b00c12907004e0000c021140e6188001400768104105410304100102c0040721685400401d403411f84801c208591041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 739963057 1250 739961807 739961813
    0x40503120f0702060301031a0a0212070e220c030e0a03081605090d030f0e040501030c05010e12100603021c030f050918040803070306050a03080403080a12090602130603020313 77
    0xe0741081802001966003000301c200107031250000395008507c107111b0f11025000c082813880042c50b000700240062403040c008030352450525203100350446580e0828401c848400c0001c41d03500690444a0415120080301c90310081d00554044104460780e82d40c1046100f410450740c54840311a072901800080f405400700d2210704943c5211240980720f42480c0749401e0101002c03400c060100f0809501060320784d030b0701d01821038011140d0220124122010492503065039101300800c0114040c01c0d0400c00c4511122019444600b01d4560703030006502160788840c20742d1820005001c02d80022400f501002140c0300824403a051525016541621220b40780c41c680c0f0706c103d896030000703008142d01a039980c04608040032078042c000e026500840c03120383c1c0d91409901c090140c1d44954402d601501028100300085540c0f4001d40f41901c0c0e021103041e60340d020808085510001115100309403070f01d0241c0c1c1d181040209c1d4020000c0d0300c0307602c0e9103548242e560301d07080d0201e0104403406c408041c407a41a001c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 739964307 1250 739963057 739963093
    0xe0a0206190c0f0f0308130203121b030706060815040305030a0230071103270a0f0b030f0109020a021e10181704030818040b0d0501050f060105040503 66
    0x1401e030501d030111103404039484600180305400c80541d110a01c0b40014000d00d41e100e43c515034849101c150381008900c40b64042640c1d16030061008a40000114800f490454550801d410303104440080780d440301030504100b4003c051a216480706440b588104902c001c10402e0090b01c50381c0c00d0303110309003140c0d200040c090283d0b00103040e82101003141802c01c80030803441d40f03865008500300e1f900d20040d031078121400f4100740c109843c02c90300350b841448000107181c420403c5064120b0340e4202c1c101624981c5002c19007006890f00941d0003081c1c0400082003000c041006144100003244040c909640c0e5102201e00328820044485c0c0103070032031a40f01c82c1003004640000345400116044445c0c0c11109440c42080380c40f02040b05618031080c1c8010340c10f02061100d0042c000c0804043c0c2490300b841c5503182ca0140c4035243d1101302e03804034494040504d6441d42d01548900c42c0141c01071b9009102c1c1d2400341d008250446103d8050002900482c1030b551040e810b4a00b40e50010b4000c10f03100041d4014258 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 739965557 1250 739964307 739964347
    0xf0606030f06060403020612090d09150e0a030b090a060f02041d191b03060f0506071704080105010308280203040b1c0c02030c2a040e010b0d030509040e0a0206 70
    0xd08890204000030040e1540d8000b011103440c26000c50348c0e0780c00e120014500708480040c003c020048080030034000c001402c00152800607940c20107031100c03001c2a011545c072100607071001d03010341c1108003004402c000c04030701101040c0c4146401c00c1000010800741049014500030700c00c0700103442842c0d00f401e0804406132900410003004085010038100200d100740ea40380100d002114401c42640d01146405004413000b6003500a0307008840c5040101041c06c500520310083d1841030f1008600001a005404803405000340e64000c1c0152360712400c1c00807181c1e10518080c40307a5620181c01d4001d4007055020341301e04101d00da001e946001c7c13a006005c209900440d608404202e14614404c12003c072a1058038112607090700a55191180342e20302c42e042c800f10000f14100300c0340154501c0c507648140250b00c100d03104102c0d0300090100300201c450f401400060911500001d00350618410f03d90054041c06581200310340600c215901d1409881e00d51100c010002c1d0441014400c0407441454446c00700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 739966807 1250 739965557 739965559
    0x909020f040509010c12060308031614030a0c140c0a030f020102090916110d1b0c03081303020307062d0e1009030b01050901080d080c0d090c0504050f0606030f06 71
    0x820300c6480c0e40040c04445082d02c0906080e0b40d80d4045085268001d144c04581c0e0440460400205d881e41d2207061551000a200c84203500040c0228400507000c0d2049280030219030b21000d0300c030b00d41503070300000520300300860b10f012482648140652103850b60840310301c0310008020709001201070b1343c1601e5070701c0c0034002007003995001d006421790394490307500d0684160750028000808400444028010f15005803410f01a83c1110220b42050340d0005207003030b003491049a804d9518080c50610a1110605800007017800d000080c0559032009004600c000740c82c001c405603003609644600c1030b50341c0c09400000340c507094501001020105203038280d078440030b0301e241403070900c0c52a4000000c5803140054501004201d4a1b103007801845107040056026100c190f440045c1c5504182d0241e40c0c44a040da540420403800a0004580300e0b0f0b41802ea88507458403c1b0203101c240400e00e000c03260300700c1c1402854040c502e003c000030f042c040c80c2c961040c02034401400080c44c549610001d510b030103600424075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 739968057 1250 739966807 739966819
    0x30e06181924020d050f10060e012001020703031b0e0d06020702181f140d030306050406060509032107080c0c060d06030b09150a020c010b04060807080607090f090902 73
    0x51200b08101649000360010540182e41e110783c441d207442100c0c0040e1521800016a4003008141070000b0b000b40151403450030300c02a035051080040b600074001c00400c00e00e682e2800f00c42056090150042d0a10034441c0c1c50034000705800e003074090640c1250030b0186001034a45e80c009030ba1414680031103070f1421b0103040058613020340c030f4002c40d00a82c10701142c56042d0340c1280400c220041481c5c61074a034030900d175a2030031b00c2500c0c2c0600d10300b03903205111045100300805d08243c0202350080d4001c100400002d0320a0205998070750000e08070340c021140170b5000740501d00e400b9140c0d1155442500c03075011804a605c0c01c104190300c0f40001c0e50041202d410342480f45125031b200c25542d04000c1d0045424041020518508616000c58904001741040d400c5038046d644c40c4554803491020181c0c011007140006880d034010543d07450140461a05440d0003d03c1c00c5404511310101082e180c0076211854112074468039440c004580e502d049204c2d01400006180c0240600b4610743c0120304014001049 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 739969307 1250 739968057 739968083
    0x7020102010f020406021f020a0504050f03192603010e070c02010203040e010e1602030703020a060b0f0d05011515090e0c0403210801090e030d09140706030e061819 72
    0xb010303049078829085070015920036100800b0103a040d10180408418040065040264240000c1c05600031800b5480c1b05449144060034282c8080051450f98151248000c07648816414105209a007500c4100400d155038908064000d003c41c003203e040716101322610314a60380d003080440c2ca140799080d007281140070400000a4078420348a2150203030401050702049070401c02858200b0000c50494082550024403009020a4011400304800b5402c0803001c5500030500740042c80b041100c0d0102c5a00280360441501880b8055104030040140d1510300c080d4a903c0d8003d218031000c804000c940010718142040c45050f040030300d0541c120004d002520306268a039a40c0900000842c03200b542c000e02c00306065001e00b5440f01c0014014401c1c00010000c81001250741d580700c0c403c075041c50351240d454008600401481d51180010014282d0a4030a216100c56000f1b02500001580041c241f29980100300b00b4180d0202c041400200740c07005001082c84000103d0540301541030030317903540c0e1803500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 739970557 1250 739969307 739969331
    0x2100c0c080609070e0f0a090501110c03210903030a0908040e0106030c030c081b0c030903060f0103060507140706330801140105030a03050d180b040b16020606060702010201 76
    0xc20000540804000b90541c0d103840d0844902e8031445a02c6440030000708818440910810b90200303401c01115540898280a14100329000d80481c192078800d840000441c102c603440c0c0400035004050814440c800303400c1a591026194100554009629820401c0807440f11169640f15860300c0c1e12a81c101030070191354251001080320241d002d2804240c0b662041d23980079925100755840d5000a040192007030900301025103c0305041b00c010803000f90b0006003101000c00030001e544000c0e00c01401c0302c44518001c404258040c40a1008130f50301401c0801250710140200c841d0250050311049071806c003241350302e40d00050003030085440d030030304106804100b1520180b442207041002240c81500044d2030302c980d55086801618048036003040c010014449d558001c14a2008103405150981d19800b01850100c0141042e00070001441882c140d5481000f040c549000e1003280a2044204585d54298020560000040c0f107403005800c000009082d81c5880300c0600402801072000081681e8400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 739971807 1250 739970557 739970573
    0x120627070c0b1003061b080c0a090308180319020603152202130618140117040605060a050d0c29040f09060b2d0909100501030513030c02100c 62
    0xaa0760005a51a451044c07050003100d004940b06118100ca05e00316548403e40014858030340a0a180d0805000088090482d07105030305160146030090040360341c904202001c3d28050400b407181c28001d005240350041c80f80402901c2c0c0c51403a8019251328a10740d120201c1d904488818448a540500082c0310315041c0142c010041c02c003140082c00c0160340d6207060300584041c80d101d903c0b19080000000040c01070610f80043c0c00c049071600c40286110b080717180c0068801c004d9240110343c0e85141141040280400794003c0782c0160020f6400010003500c2d0020300c00300c0c15a4040203401c0c150200d4042003850400c40c04001e00510707400494101c04441481441c080c1c0c4568043d0041283c04001070000544d14450f1500078220400c030989040c03801c0c4850300e8921050704000b010319420f0100048101101400c84803001e200900490151418840000204110380600744c002841d000c0011041e4102c000210990341c4c02d030701d86840d0680389600b0001e403c4001e80000080100304103000d4005a044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 739973057 1250 739971807 739971811
    0xb030601060c110a080f100b0a03020a090906021e070b0f131104020405030111030604180b040803060f130e0c0a0506071707082116090501050a17090102120627070c0b 73
    0x39000210708001d100e0b09448c441509503109480d00441000181d0700e142c9903004845010b0000304020841d410702c04000e0240c10072003140001042c2d0414203641a0f40010410320744a202e410400380c40e0031920b00c90300c0108440d200c0c2c50704640495074003c101816003004003203100a001514041d01c030f0700401e0035610144084200c564000c4240445464076028040c030400800300e60800180f41501c5010b41000041c2019201d11000008118580c6175901e0917055040064819500e003035034051303080020924842150601d02404104000c40e01c1d024296004480004264505250f030540700c1c1c03040c0d6001e10044030b22415003000807078001540b550243c00031021200124290b52480409111014401040b13250904445e401030740c42150099454000c0d07a030300380303086900e40c500c55000351075105070702d08100155a5030604005e417501d0305400070b0040f954590b0900201d07031911414011502d082c0c46020021403aa0404122100e000c8141c803a4072902c907240003206e40119407690721000e041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 739974307 1250 739973057 739973083
    0x304021e03030d0902040608060c07080703090510080a0e0d1d0103090b040602070b070e1f172e0e0a0216120f140c0a2a090b0102010b030601060c110a08 67
    0x450310010f0646c501885901d00034220319001d4491460100c85c450a00e01c940c1000030620080410080141881040f00101600003e4064000c1900c0a4409088800100d8044070464202506180758400100b2020030131441600e80c4010080041141615504426111410103603103400500110f403400114500581c081c840c01a515501800c10080e425001441c0f881848156648142661203984104841c55a036014246502100200031078503600440c500c0e0f040b5500e0307607003030101603030450b4080341c0d0001e01c00044118945680300d92410300c402c035201d007800e10000c000002e080000f183d001400206210b01c0b000704141d10716916001070195546009002641c80c41c1402415071300300520182148012000605081c00400d00f40e41e00c080c840d2000b0208240802e070320408421100c4c441c001030b8400340d00d116a558842200e68005d200c6414500d005608040841e4910b04020a40ca07040e40c4440c3d403016100c00740f5803281000302100e010040d4200d001804001403022080c0003e40003901 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 739975557 1250 739974307 739974311
    0xe0601270612120c080d0b0105040503010903030509160f0314010213060305190e0d0c1509030e09130b0109050c1e0a12021911030c0601121a0c0304021e03030d 70
    0x260700c0c1080b0038200c40d00b03c440410300141c40c4051021881a100740c0702c5880900202007504030940703004030707034500656010a130150f017090042c01c01c140c0c050300441d01c59200d182c12900700b040300301e074202e0303100001e8416801c0140d07081a061010400e80400c00203c00d48500001d446c03d50b2103460384c11901c0b41548054002a643d105100c9110f00030f2459003100e2584030300c18070050b402c620790740e51142400e6a03400b040c496003d042d4420448464a0103641c84010601044041d115050140c480c204569042c2d1280d0300746400101096a480c91014085030461340ea21041da00b4401084010140545034000207901402440720500c0c00202007406880031001040d281c00551708054007075682000e107d04841d006001a41c14004100b80c0d01d480101c840c90181c4007540144a03440c25485151000d0149004000002c1070b0064020000304606120310003c813004140f902c4086100d03042654a103840707100400102d00549014044045808004001d10300600c01c04c1c00040c0c0f4691151901900e165 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 739976807 1250 739975557 739975589
    0xe0a0f080a0e010c03090b0310180b010323060907020309060414010806040603020913020a0302030307050604140313060c02130c0905010f05160611070803190608010e06012706 77
    0x3075801501072110324000c2c203103c0130116107a680500f4004050090038581800400010f03000b90710311841000400a48203625260440a558080684499441103020a00b40800c00354003204004d41700382502224000714445881d060b08110382d6000190000046200502c800b082c143e035258010001844014032241540e18600009425604028052803045240040070405621a01001c82c0c3c032081050115404240340d200203201d40105400281d0544408560308003000400100030380036600616020107000c0408600070b581c1d104855489400302303000c071010803605000d00d8107010a00d2008086040c404030181e41c050441e10402c07404c20006810300c208002558104100c0c010195191610510b41840d11889850244540742d000389600c1c0d48101c0d91400e94044802e40710740e00d90000750702d030b0f80c0d08100d64813034443d46480c003044082a1400c08006400d00c014851030602c455044003601c0140c1c170388099003444000750b03802d20650001003002884240e80030f225203005080305111081d016 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 739978057 1250 739976807 739976827
    0x40e0702030409050105060c21070c030b0a06050901030c0501030c0e1201050f07021605130204050303160c0e061c11030d1e02010608120a0318030e0916050d0e0a0f08 73
    0x541c0d0180d01160146008002ca240742d0f0f01e001c22740d00f041030101422010742110541c90006280b03e541c074058a140100e940c04402c21000d0038106010791807102051140380c1d2210100510382d04c0030701c0028400c0d10201420405075009402c1000e2440d07841c05c0c07c49400a00101060f24100b0b00c4c25203650b0760b5941c001308100080021140e81e0084014030003401c80b034441601178419001c150180d540304112410110040680b180c0464000d02000340c1929103405020f142d00101c2101b000f0110b80040d1112804908002e07103001c60341c4100c0d0000c00c08011405203070119901030301031703c2007990f0340c40000a400100b91410040e00103c80915620104102c418000586824143c440008216410500200440340e00082c1c0669901c1340100c101c0d6981615030740035001081c41c0450800d040f0b55200002052581080030525294019a41c00920ba038403005184035035002d81d0084008500141710492411060341d00c408031404d140400c40e86012060388a64a280e907403218102d401d04000550401c0e6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 739979307 1250 739978057 739978061
    0x51f0801021b010213170a1403040f09090804030b061201020408030903010506180106081e0c09011b02210106030215030405070614030406231005030c03060426040e0702030409 77
    0x1e4000b80000031400c1c01c0c2203071900070040d0402d204000b403401a10200c0c00070b258050080620b05940a0243d03406400c0c1050f4054803500644544c0020300512140011001c030300d8000c5c9000241c2c03051640d450f280c00d6a80c0c140c1200c5003d028203810aa40410724129440248018030261040394020350b01e40007860100340c00c1d14030051900e4041c00fa800c030422214000303074003000c1c1960041d00b010859951008220600012000800c0907409004400e0100148401c0001c040c544802ea0300c0340d04d9001b05000c40800d407562850000d401c520303000364803076043c1d4100c413001d0760840a0400100d1555500d80004000400c450501d0401000002c00c0c04200314080010500074600c41c02d1050400d185402a00c1c403901008001520b5144c462400c92440e40c0300560014602c100c0b03400f810940d01b801d0b801e8002100142c0a403900038402c8416007602840c0000341c0300d11669003c401084070f560740445400302001c00c014035941100c0c06020114000c0c03c80039025208201c151b004540f030f01c0c41c041180b02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 739980557 1250 739979307 739979347
    0x20f1c0b10030209030d0c03020f101b0809070b0a140d020a0905120a0807031707080702071a07061d0712061d0a02040b0324010312020705030709051f080102 69
    0x1c00d05204010b014a240c402140400031080c041c181104c60110b0303803d01fa401c00b1140340c0c64141a00610341c0c04810300109510416104114001103c0e20042600e0b007a81d03060016111035580354400c80042000b0240f2500801d00236100780350070443c0707050040c400300b140d82051441c2c0c0384451300852040e070481e034011024001803804951140c08200002e10450321111000c0003d0b041c00400504001898005e03c0070208544510341c1410851911610003003500c00140c8088005004890b800030310110b01d045003200c418540040706160214542d0f80c0300084c4030b546010140205820000c0781300c443c0900200c0e00801c80415241a5621145001804c9481d054100900e80c0c00244003040c071481c0c00107404c0081903065a0000d01502030000081c5040c42261142c0102041e038000a042e050b6080d807143d04030ba1264101c4918034140103c1a0b0b10f50300540034030742c0c240d070145000708000e0b08c0315002035400c503100140d003007868aa104840703a2003a01c01d8014510300d1b034000540c0c0300750380c4440095007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 739981807 1250 739980557 739980589
    0x40609050f0607031e031503140105070801050f120f030316090509010b07020105090307050319050c100203161104051305101505040b120f0a050607180306020f1c0b 72
    0x351512a8641c0d01501c03010311840da9044050b0720170800d0f2500d03406580500c43c84855401c08008041e82c91600ca02d2121040903050345039428500490300c51409140198165039000340380408401e01c02c028004644601270342d27607481d0f1040d078030340720901c0409000840c001c001c001c0d03d03640c0c0079000e000c01602040880e84501c0c0201c20707880c010010030701c0d62020358401543c24603103c4ea0310038454000034602034042e00b24590501818005403580c03201c018901001c0c1e8803a50a13116494031071410031a50b0490030315a0390158000f0440d94280c3da52041c00000d600d0b10400d11a40c6010480c000305044490445051000e00705800c1d50f4820300c07504200d03481411035000300500c04217484048010084000b4410580226100d8280c1486640c440a00490420910303040f2034250000e00b00352039a40100076010386841c01003d011402c01072040c07840d41e4407160490200040186542d440e0f60080d400140c0400c0c4462060080c40c801c56251880344411124016010803254484010400729100000c004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 739983057 1250 739981807 739981819
    0xc1801050d05010311180f0a110d0e21090a0e1f0b0901110f070b0a05040506070606031e110d11060a0909060f03021804020d0804091406012d1202040609050f 69
    0x40044490307c851190700076540400815000c0420240015500442c215284418100a2804146a40005c01001c1405d08040380100903038207045480c0f42e441000360654220828542c113004250100e201a90081c0c488200e00300c003400c03e003400c103450240c0c81d000214907401c0043e090701550380c0403905245210790f03280640450300c0c555882c15520b00c102d11a41610003000314a05103154000c0e0141d034000c0001800d000d680390058a4030b0801804580801c544030340d40c5210500c0c2e54461140b2038403441d688800a80049003c1b44200714080c02d03004412154000c1000b00000d2079214100540b8011401d80c5456290f40c0c1410000400e5444641040c10a078924502c100050f9554858100e904090480550728680716800030400c99210b0000141000200190000783d01c3c1d080e500810741042c12104280807074540030011500a01d0310240070554003001c00e000c0d140520845c1b5040c50007101424009079443c101c80c6904145d0b0020f5200901141e1700c10410000c90401c100c194a040b4011689 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 739984307 1250 739983057 739983061
    0x271401050a170405030f0a120e0a0c1e0f0902030910111e0d020307020a120509010e0405130b150102190314031003022d0103050c1801050d0501031118 66
    0x302010b0000b41c00481c810001004207091140c1030044514007803221541e0b5964080765034018000440b03640048400b1071a05010f2441c040002c42c1c0f8042403a80800c615408174070305204401002907600400c0c2520f0104c2c0c50004200130040040e80040085401c01750312850030807011410818100c012181d510f051400391280c02c04804c003200d6030030190b104402003101011803150074174002c06e01e003030507450701c00402e000c0c00540004511f56498481c00b00360042c208070700c0c03040b9141c2c014204194080340d60f440800e8554070b01078001e40d070300c444a80704050100700191600004280107a072650a8034078149103501041d6414405800403904041105c0320001d465500102202100141080a10b0700400499480c0156451480040d500200780700500d4030720307910300703858038246010b81c1c1849421611160700550080c0141849021007903000e50401d00c2140700d00540321404e041c0759040180030409848500d40a10803d4080c5001d8004800072002202c1404103610714203010026400d0b00340b003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 739985557 1250 739984307 739984327
    0x608150a050105030606070f050d20070f1809051b030106080102090d060518030f04090b0904020a03121205100e180a0f0f02030d020f070f0503070e060127140105 71
    0xb200d030000d0069600d260781d90220f041525125020420061070340c010111042c4800e079001820311185501d1400c0c503590480010b4a095850780c042c80dc07480c0c8c24609040401420380d02401200c292500b0382d102140c60480d50f43da40342480c1210811807154651001910031508091040502600c5894000c5150101010000e01e03451342c1e10f4001481c5640300d20014555140a6144c1e0803010404411a40c8032001e055180444d07030041d00506503510b24200200340a071400e040340d18015a009800c5001003400c645035040f440c0f9a2110304020b1000d4400440704da01403030700c03403184a00e1440d03400c910400c2c10021b40ca880a5005000b5010304440b100103112025404581c40d2541d40d801070803907c208500789406e010000c55040c1c003940c18012016102c0101d43c001c600c2c140ca003521501500c44c00354681c0c00741520518903020f8560141e0000d04140541003074240040d401c00414107200210400200424a5020804020303290341d09045404000c05503d94001c0c0d00d131080c09007480750031711310140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 739986807 1250 739985557 739985567
    0x110109060507022107080309010816050a03050a0b100207050a05030109200406090f02030907051c0303020c0c210c010516110f090106031d030406090e0a0e03040608150a0501 76
    0x2c0000307842030a80d500340d0b154801c002603000c148511410243c45005545401a40d1641c000905490101d442400040c8820414042417a2041c08036107600f401d141d01c0600441c010200188034200325952420000003940d200d40751148500c4565000b00701a0b420f007001c1c0821035185920860181c2c0c100707050200001d000654130498505403094a140d2141d4100000d006441a40e011010407440d21000145035481d5400862280f01043d044418696a170780074044404100f0000200d03d0548460703d00c0003d200350000d005100c2280c0c1142d00200080c0c0001b0021249401440688005000203400103002448480c2d60040242840c40c240101c0c2401c0319070419960b18010100c070030075045c608065440301d02c8800380202c003904508503981c41c0e01002c3c0041400b00a0007050350b221115080b8820703000402c5605989959462050691900405040700710000e45298400313030315800c0d00420034100300090801414a5a540d10303881c2000e01941c0958120790700040c1c00340300c402c0800d0103181d03001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 739988057 1250 739986807 739986817
    0x1204060201110c0c150f07080d05180d05090a0308032a0a0906050a030f050a0e1b060406030b011101090602030f090c18060402070203010504060b0117011d06040e16031101090605 78
    0x1603582100e14011040350510603c6000c0050421b89800300e161801c0c000000302502e42500d104200300001d8560115059100c3c5030841e600b90308e503012164500e02d03944180050642510301402001c9665100ea0310742e07a00350012980181d40d0401800070000440c48134030030030319800851984900c1c000b2211401006855907001d420140280000c0302c80a2500c02e80c006014000212002c100a04060703403060080d080c100361485241c0306410803844480c0ca0075038808040480146800d02e021300c0c002d425000b800a60384c4131030601849240241c0c1141d4207000384820a4842e03038006a4a1070001075080d8082d002415502c0e540c0d000000c0d4460744e845201c2644403801ca20170096956070380d508005406880b6024000350503500f0901403104012050300140c0010303800340c85503080b2003500045190381810910032200d121980000070309640c60030240c4150050030141c07001c00c0180000d0f04447c0ba200901c01400c1003102011000c005004642e03047c540c601d0004d2801700512480d01d01f00170614051 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 739989307 1250 739988057 739988059
    0x507081608040b042415050f18060a05060304030203042301050a0305180106060806090106080402090a05070530070305090c19030507060c0317010b03150a05031204060201110c0c 78
    0x1c1c40c013290038000c1408803400f0080e5030f18459010314140c0074291000e0a042001e500398418400740100e494644031040b09650b8a014004c091000d00c02c60551924441c080d01c0715401000f071860100da00d4030b070600114401c50007500150743e03440c42d140356590f00107040b503200c0e2503044040c4810011681c2c06011245d4040701791501068a071285d48880c408007410a07460004d641c603000d00020025000315440c1e110341c0040301c25240903a81c2c1e20302a981488201d0f40254091000380024054101b142e000c00c0c0c110340e80303103822400c084000c58881007a003043d06200034010301011141908400c03246000c0e600a080385001e10960a08a50303059940703500035a054411000150403400350b00380c0c5c82d0460000e54000040710080790740c551000d030103000031007010b4000917a9921b0105401c3c62203025075048503c0f41c96201c0c07456403145018003065445110b1130764171150109000419580800044201146c0400d0059803180f4204000c0d0842d0440503070004100c83c14004168001d82c00314000e00d00b110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 739990557 1250 739989307 739989323
    0x40e1f1a10050324130e070f0f0303110a2303090a0e0a0b040b030c010c15090605090f0102070b040305030a02070f03050c0d031503080c030705010c0801090c0e030d050c03090301020d050708160804 86
    0xca030311b070850400b05681c01483c404202181d00044100041c1005000c40c0d005e900d0740c0f2074400b0445a026100c9040c1400500000380031076520320815480d81c000107840781144142c0b81800700d02d0000860340701c0c2c0da520041140f80c031141802041621032043c086902c004071020061302726100013103a251030000000c1414001c05200d01c10500540c0c0700c2180060301c0c00c540c00c001640d01c0b49401750043c001a0b640e201940b1031000c40456141c0148215455150803038010b82d480d075280e40e012a41c5034070040c1b17030300788698080c443c140005440c50b004140140c440d8031002c2d06d13072942e080321620788a622000442014100400c007012075010721405030641740c0040f0715036511444885890300e144a0524000c01541c44d040202d02200d502810640c1640c845690900c07003070541c0c1d401102c68003605503540ba890b07084030b800400c070180141c000380303400c20703008056a040100c000c00080c22038102c08001503403192600208460160b01507122540008d241d4880782d4200084600205400320082004102d0b20b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 739991807 1250 739990557 739990571
    0x51815060904050a1401170304030b06210c01020d2f03160605041104142e0b0909010e0c0a0c0606090c0e040e1f1a1005032413 56
    0x145421084a0740d89102501c240250700306200c00900801000b01d04650904404c40080b90310f40b1041d0390094807001c40c2000718105411a221110229005000c40e54425180310300c50f110f03680100040480e8012031405480841e00f420006030a0079540c41c3c0040811001d01011682e000105440e0346100050600c8901100350010000e441c504c500d407040c070303142071074041c0307038810086030b07802c2030b8440c40c890001c07191020100340602c010340c2c50765290700b0040d006080016800e8880d0300c403d4802ca2658a03269400c3c006030b01d1000f10030100f50b403c0f80103ca0b000040404550400749001c0e070044c6585100c2a249240c100390030340003070080b007041004210405c48000244103464001801030503030300f201003040a10006014103070300d03000e200550149083c030a84240608006c00c201800154400c0004250182e5a0000000b8a80f41d2001128070305011600251520340915800080e45c080d212a540c07428035001d47e820f0245091150740800300003030041a43d07034403000290804900c05680100c1d00c1c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 739993057 1250 739991807 739991809
    0x1020318130509031c0b012a06050c0a0912030e0613150801080c0103050105010e060c10020a0503010501120e0a030c1109040b150910122118051815 65
    0x121030444124000c60700344410b00c440321401200800da807003006156903d85c490a142608103aa429042880c003003000407040301508a0600c0402d02c00c0d0a8103c07061082c400603079074083c201c6106496101c10002c012034030255032600320803030b41c01406e00c1c0c6801c00b4540096903001818100c860041070700803100460300c101910702510407003000c0c10499000940054600304010502c0d06c1c24030440a00744911030f175003240d0354024400c6605a500c1a0b481d100350340d2504060007402c0d0301c60302c2290500c2c0300d080607044c0e98812500c042c000070100d540d10305980c2d501d048001051110316030b00d1603c00c2071900440100ca80400198050a0f50345030030801c080b000d803410103d41100359486081d4202c0310080402c400c0003c54240c0c18800d0074040620f1207510461020b12004403011200e01c14007000010040c08101f2081544011580c42034084c254581207001a00103072001d00754040c0b0219190401c0c14112030b0084034010701410f000d41e600ca05a14142039070600941d0050103007044002482c03101c0d112 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 739994307 1250 739993057 739993069
    0x2c0114060a0b0f0d110909061f050c1204030b090d08070e1009080a0308040209150a03140102040f061101232a040e041a012601091202060a1a01020318 66
    0x1810b10158010052005a1180c1700f01039803110303420303512561078500043c1e524170b4010044c9404050010000803210301e003807002d440d540d010161074811481112105000307203101c0305c0184042c43c402d5094000078202495160724040c0303864201c5061100d070004001c40c25921551150311000102c0340c0700d1400030803c9040c1c5507186c103600000c0d058041c010688050540003200f06024a1094070040c07107076901c0518840402c131411081b0341c0e000045440c10000f20b8590f442c4008120526800185400d1791810b40041e074104641c001c40120345c060485404a0f4405e00c02c450456101441c230038201107000361501c0d00d245004011034902c0740c0001c8586080d0b0400820744407110107518a40e0b9413141c9400d15014221411101110074807810344511034214038002e070280c12182110104511150802e0b50b00507102085005a5910365a44041401041c0380d0f4254030340f2035485401621150070b0100182040d1103080140d1703000441c042c041c2c2e620b81d9071300204aa000790078459000c55590a030a0001381c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 739995557 1250 739994307 739994317
    0x60402010c120e1f0f03020f0412080c0f0a0b09060609130606030b09031b030f0f07050f0a200f01050306010c03030e060a1d0a1e062c0114060a0b0f 65
    0x2070080b00c0104591043e0107844c0b0b030006842035176116081050100d100480591242500804041e40305100c20030011400281c441d00c1c1c20721503215181840300c206102c51522428041d91015039214504032401d1000802c5666085030301e00001c1c0040e403030302c940403c00c40000a0601680c010180d40f807141030010561005000c1c5503c43c0322401d0381e00340b00440c1075880c0c12504181001c29403040c4d040300304410010498001100074107500307003004001051a44543c00042050303809000d100300c2d903c2d00f080d0600409084503c40c4e10400c0f100c203ea00070304d107030030540d0041c400d00800815481840c03581e044400c0c1d82d440b06003407030000400d0b101031030210701030800000074116030b100d8030007032240052071b682003c5100d042e890000884286509903490382c03404850005419064550040b090042c450030500e01440d000b041c01040051607100c90305c0032280c200240020044c14001111000302c000e002c0e058203400742c10040781181c00e040300004c0300030341d0a1240d49030f00080028005000da403004184c030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 739996807 1250 739995557 739995559
    0x302060906191e031505040203040201050f0c1e01020c0715020a0c03080306031213032306040b06040b030309280e01080607020706031b0305040206160501060f08060402010c120e 78
    0x20000700b1010901034641032030140744041c001da03400300940c841c511074410030748070b58541c02c00000041d1070001030000944c401740050381048000c10018013180400ca006104072212200113119001124030200101041c81034450f9869004005a81e14020b0015005050300c81076081200f004074400d40c180c1c83d01e403041340300408040150300008140222400690710540055040c1e620703295000c50300341400d00c01d036101c0b46034440700a5805c0c00400d8a40000c0e041c074644000c02000f07080c0d60200d055280c0030003202e04884000c43c000401c880e9003403a00a241604105800540c104000710000071980a00c0e99036520100340c031441d20880c41341201c000800102140d00c005100b55841d90942521480211401c50161181003000910342e1b10070f12900004038418140c2a403c0d0a01100403009420080e0060340d00140c14040c040007105801368080c286446407000113012440c085003049200c0035035001260942014080102603604030b000344000030341c03140ca036424260340700c4002c0e05c02c3c1d03130b140d02c8013 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 739998057 1250 739996807 739996837
    0xf011d01090f0f031209081207030c08030109050405010b030318090a09060c0f020d09030c062609071406070f0f0807080706021810050a030e3301090b06040302060906 73
    0x6580c06070103c000c030030f0b03d0080181c40c80316102200159081e140da4840c2009650042281c000d190090308041c00c5240d21a2074028050107403901d904119400a80140031036503034450a2004018091241e01c107421000d03001f540c180751903c3c000301c1c4640c00015400b07002d604000d0019407000d00e0b40d0710001c88241d01030001c1041031201040200849005a1132901500c90a00c0d07240c031542c00b4202540c01c03a90320012603603c45081a008403420202000d84100d500200100c0d05840d0b403080000e0f503c6111414002d00c409880c0c040c042d4050911500c080e405000100702517070101d4003a44410038007540000024041c0450703864404524401c500004c0c02440d000314400013000003603002040070088004070000360f503181908105000c0c41c445086008180304101038489940039420405000d400f160070384404070020000c0c90a0303d085000c00400781d000203d0b40b1014628000c0727035203000d06000d240c104880c207907403c04140148950f000c003911850000c2000c0203165200004ca8020388120061 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 739999307 1250 739998057 739998059
    0xd0c11030109061d03180f030114091f0203010f0311030316060f05091506091b0408011b0f091e051e1002010b03061302030c030d0e0f0f011d01090f 65
    0x420b200034102803c0d082e130f260120040b854600700c000000c0d43c1e000d50343c1092060207100250104000912140766568041d501c405402a410b90580c0c0c1041c0324454400151600031812807201310440d01c640301c117107040c030f106000500195110058071004d8030380c80020300b800c0300c40080c00030745580a1114035030021050345000500300000c0d03812540242080c808148240d48545422940350a00d41103201c03031200380380b000107000c2e251148040341c100340c40c4002c294084880402d200fa0682c059040081d080e9103400c040c00c50030540015841c0b4036501c901d004550540d4000c0300505240b07292203481c8201c01001d009000d043c00c030482a000410004104200c2045400100780d0941001030041e44039503d1541e1254101d401030141c007071100e00050182016540d20a1014050740c003500c000d0740c040c4142e62802c94203850402803d541207180303844406880610f0400c001e0040400d000950140d032039a1102c000320b9800c032003032200d801c54080c0b90b0454000142c0048501030010740c8020400f11a40c08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 740000557 1250 739999307 739999313
    0x10b031b04060e010912150b0f10080907050919021809164e1d06070e06190309081606060906030507272307020703050d0c11030109 58
    0x300803000b400b402e07260440002e94406c2240e00c405c1c03500301c01134940c06500c50208800882a070200c003800400070200f20410b03035071074003082d51030380380241c40ca002c81d28460900144600420945004180454096440303140c0340445a841041c850220399886801040030715404074804100d41c58544054011010703031400d000401c18000e01e0800b03003c08601d1140741329a0f0402803282a0710980c140003810f2102c48581c1c19100300340b004501103901000e080da140c00040c0503003400b40b400c12915a550200c1960403010b84070341861000b808403c02c5c860301807072a071981d840d82c50a40324070040000054018401d60001039002c0c080302c85004041d84c2d00050301070300c1122031100c0c00304010300849080005688500c1508100c1d801404081c0c42c5910960b010400d0003072811780c0144c50f090b05007c11201000819000c4283d41044226020950000c912411654490550290301c030341588020a41030b0700e103442c0d9946a04180c2000030801501605e0f000600865040d015820391010b0020052000641 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 740001807 1250 740000557 740000567
    0x6030203121903050709060f140a1116140609041416090806010b09060a051303121e1d120f010b01230a0e04060308120a050a14010b031b0406 62
    0x1103920580d03964001900948601c03900c42c1a05c240d00c00e0b00e0b60b0703181904010b4292242864034052804011030040081031004040e00504205c4100e51079100d1141641c0c00320b5414030900c40140c20641d20f030590108103c403183d840b0881586030a03074807941c0d03070501e1102007005003055070302c401c10440c1c0d003e00b440008840a0380302c001911440d07035108180c3d501e0b01c0b143c0740c03584000c1c40f540e01c1c075003000c0c400941d0303515107200100011017060614a1400d20800c1c04201591718690090b51301c070070803208210f80540c0003142036030341305c00a032040c07910007404c0f14000e86043c40c81c41080714030301c50104e0107404032340301c01c41c0100da003542c1d010486041c40b041c6c180302d50107022407101d2a400200c0301c054060030111040f00b400200046101c4840c1048001d000807504c13024500030040c0d01c180c44002c00400b0580d10001007080d19101d2890001c2e9150038081c0034241d40303002e8039a031501898144915100400d40380300034190b40c002e2440c16520340b210b03031441588600e02480b1099021002030b0008141742c102c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 740003057 1250 740001807 740001817
    0xa050c030c04090b0a270c06030b04110324060c0115060507020108070f020c0d0b100e01050f06030a09050d11060f0708130218070e04110c0d0804060603020312 70
    0x110100d401c1c019550091000b550450700c001480c0e4011100421071030700c1c007908029a41c0c00b0807000c0b210710700c404100240260094540a503a6156502c81c1800059814021804203010035138052241c1032003174503840014840100501801030000710b000348034100000820850300b07001030265459420480d000f500070180010f14102c07041c000c0d0f02c00a04140a01d041c0e6284980584031107085076240c903019107040300d00c602c0340f42c00c601428031520002e0f903580d0035520945018014000180ca400c80a00c986d003c0c80342c0011100500020040003503542d114001c4003521019558203441303403544d4840801500310080020b0441c000c80000800d031036442001d07200c90240040441e503240e10740d1035040c500442d0540304580011f44040010b120288003404440140d80301500f481440f8558040c006903148081e240480007070786206803144985028000d841070288e106000c240b9003552052601d503540006c910b160300f030162000c0083d040c01080c1e4414801181c02409950b21400ca000030740d4015405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 740004307 1250 740003057 740003059
    0x20d020409062c0705060708031806010f0e0f0103080406030e10020309010207051c02100c11010606050a0f1d0108060111010908070209070e090f0604020c0111031824040f050a050c 79
    0x180c06000540f820000070111304079240a045185440099143c4501c0c96000401d0744003107904c41d081ba408144020480e850007400d4203511541c00381c1c10300e041d4403407001d00030344050311501440d401030001c140303c841100d0440b2503600780000e10985500003141400d0b0300e40b42c0403500d18404000c0101a10040d0020131549204500f600c00015040f00f804d8119441803d01c2c10043e4040903400c403100c04d6691100c030074400b0385c0c181420541800e029007400e4a5041d000600001c40201d400c41c0c0342604013461102000003400c2c4518500d41010744c810012072000b100310f04019840c40800d0160b4003c11200c0a04080d100c024001a0401c2c103100655900c50002240603009010004280340c0c070a4295121240c0000d000030441d0300c44801c2c0c83c04220000c1c101581c040e90800030b035529041e0034419084103508d145000e43e107914240c032540c5071340d00321981eaa0003660031050382c0c40d400100c101a00c03e91642a1b41d000c0f007031398955080030804907404060003002c41c4904c6100c1814080005480240110 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 740005557 1250 740004307 740004371
    0x604060c03230f041104020a0f1103072402090d050604020a050108011d0415150810050c030a090303061703090411130506030408091908010e1504020d02040906 70
    0x44a0402e16814411070740c51180b03084000740100320080c1040e003090390014010f501604108500c003000400720ba04c901e80703400108618804101d02941c2044005040310310000240d030910b01c04e501c6041c3d82010703c918104081c80e003030010040c045281d6060382c404160244c120003803095286842943c0e44010b1314264810b01d00007100080c0c540c0300d5a8081c2c1680e241e02540266001d51241100c403052014201f1a041c40e1710b08269001144a849500c140c000d040300362041c13152804942c1800c10103024600c011143c206402c114190254204594000405250028141d0510b0030110000c0006400c0060350f0b018402a501020600001411088100700c804214664460072546028442d110b840000343c10017090070011443c228024640c001d008941003850a183c4d54001070b070111080c5000c0c40f1001004409014216007445800316810041f40141400403181c0c1c0400513420303000740700038031998074064200110348031900601c08140c0d01c1070742401700c0c10b80380c292142010042c20155007214 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 740006807 1250 740005557 740005571
    0x61507050a030315050f0405270d120b0105031303140d0617010e0709020706141003050615010e120120091311030612070f120b15010207091d0604060c03 67
    0x20340c0138142084460050003034410000c51814000035001c0108410000a108040030b04c140b1880e00400c102e142030403001d8100580342da04064807901d22502c4108a0034941a0b51199a9810408894101207840004c52804000c0c4c0740440d1010308100358605446400701e1103080b6480d00c2d4101a09960801e1110802d00321078a119900f2100184e800300a0f980c0100001c0082c449980d00400f4624000c13080455041480c1c02c030403410000030b45024a504c10a40300400500c00e00348007840d048911008200107100900c80024020410031050601c6a1070400d800308a41500358130100302d0280e905002c0e0042c0040601c082a00c3c0c004c3c038225805802282420150a88580b0400c2810000f4604d0582181c0707034607051105140c1da4512030522032040c0c24010407506140c9030400c0c02828001d2101d09000c202d403400b100c0c0c0743c0d8003400c1400c114000c400354500d560b03008201c4006660040e840007660102d44000c09454011a0020a0b41c500482e01448207000c071030341007540c40c61030300e890034070041c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 740008057 1250 740006807 740006831
    0x308030f040c18020315030a0f060b0f0d0803011a0c03090616060528060308030c0a030905070306091b06050901030b0303041d1803040b0f0d0902090109091202010c050d0203061507050a0303 83
    0x95a1002c200402601c009c107070032000079003682e1182d0228140a45205108000d54000c240080041c0d841580d0100005c00104042202810346007000303540000c42c2418544c0340603215541e4006d2a940a100e10008907059400c641d841d0303c1002103c5d0480e10600860800e0351a81031510661170040d00200c140d1440c800e031100c4240a4141125032110f10b55185664141c0608045c0d00210260300400d902e4a0089021a40811040c000fa502070a400108400d5514290800c0582458185036200e803250b030400c1042c0e0403909860809c0b0b030a08020411001c4640003905611964004119525075106901000c249802000c3c0c81000c0000c82444420b481640e07985e41c3e805107103c0c7c458104010000c41070890101c2000d421100c591703440c041030762060742c0d00052405201b40c0000c2d45499445109030140000000d030114220241e000811201e06010b00c003c207688248500c18040350380020100d6220b46410714002031501700460100e0710341c40c1d1032600588410030780400341c0010303007854900191 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 740009307 1250 740008057 740008063
    0x90207060518150405030c0307140705031609181e1e0c030212070e070e0118230303070204061e08010b0d02040e01020904060f050117010308030f040c1802031503 71
    0x2240b0701401040c0854580000705542000140b040352503020600814004110400180c42144d101d50640341d410311800300c81d0381c85c0201c00d620081c440d0f1b001210100d40c10703c1968107102521a06180070442e891102030404080c09001e1000300b030a4044440e0a00405194040f80c0095210310048600c80020790114850104051005401d8000320003041005182081da80c1001c402241d080d84c4410356281068078800d00308440501c041500000c04c100203607400390101031850420010394030500d0a000032910806070003200481c0c00580007210b00c0140d5802c006a800c1568002c00601c01e0680700c019510040903565103a9452191038400440d58030810b0281442e40540a401c103130040d0b501da000c0001402d07a00b220242c00395400c0200c006d15443d9030047c070028001d1100c1d180c4400780f807c0001401003140c604824203903400780f07005000240300c0074102c2e500120100066601d0b0344603803c19031030394681644220402612a140760404c0c1c44141c02071032140c0091034580144030840d90034151 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 740010557 1250 740009307 740009341
    0x411b090f061011070906060e030303090c040c0201020d02030c091215190b040509070612020a0503010b070203030909011d0a020c0a140f0d020708010f0618020304110a0902070605 78
    0x18040c649400a84103041c65002c40c2000038540c603020742d03066410f000e403604040e8150040000c030354980f0401c1c00415005540d64881c1401500207501d07502c2c03c0b6420b0394070703501e90354510b0307100b1794803141e01c841907610035010740b100d22402c258110341d83e080408804000c1c1e440a8852401200401038402e20300c403003c21381280e02c10544000c040c10781e40e10846500448607c10303000c6110342d83e0f9a800ca806403903e20409201e00b00c82c0005110340740c10808060889031a0084034004580100b00340300041d0352000c00d4904543c808900701f9110000b600c002402c502038240c41941102da400000520704140c8a0449100b21103542080a151030b0886140180e02c6542403114199201c43d02c2c61001810380e0440724482110041605c4818040b400011f090a5582085400682c0496020301c01c01d8003e10880035000300040c0100130302c51414510360000c6084404141800e507020001400f40a14003080b45200f0340c0c010b158117445c54651803030a009410410041d64a54584400180c211410b0f6807402c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 740011807 1250 740010557 740010571
    0x1d010b0705070306020913090f0201030f0204141201023a06050a170709050702241326032d041106071a0a0212070804411b09 55
    0x7120340b034155140e850181d84602401a00490306810000341e24465100c0c0600c00c030301c9211200c000034054000102954012030b4000314841c8104801c1198801014901d0b080705000e4412001da41107042e451802401a560721642c9540c40310003920020511050030303140701000c400c95030342c3e10810f0542c80382103079280c0c00f40c9500601d0203902400005402c210601642101100301e03003020351a081e800c1c05031a8252440c0006da0720a949982c149009038901c1605e240380c3c4401811145402c44080142118001c00902502003019103170016148400500b205001040a596a00e04080300100c2b40641001c002c1c003003280c400040000003603d80b41840f40100c0c1c00180c12152a8000001c209032030340b00b2002140c0d01c00200302c0d0b14036540491003000784215198500183c807a01300d0480c1c8a2802d0340280380108100000302088001a01614508184440e0442c5024030480e0070f000e4440c2c191b50300d0620040110f07060751000d00c1d00400692814000e6400c0c00c20480e03952082d0500601010a0301d0741 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 740013057 1250 740011807 740011813
    0xd020105120f1e011505031512010204060909110301060509280501030e01021201090b04021c0608060106050c0d0c02121903020c0613090c0e060c060406050c0f0a030902010210061d010b0705 83
    0x2000d117291040001d950010380d406100f0040c00030032800580e040006000c103d0103a500030030704200803a00414800010140003406001000d46424030170094841405641e041c002d02241950664031010a402514507100090f045030900000308501546100d00c9428000b81c00d044403058441418029030b1042207221126034016404c01020f0009405400351403074000d07500744090820074803018107180c11100340c80740003c0c4050510201905050050b00309005220302044510200c5000042001c00440c2c3e524015036954554030018a006250b140d400c8000e1240940400c00c2c00c80300422415a24401d408990600080d881800304602580d03101d0f8020086000d000c02541920b03810900015205241200200c100c03035002440303076000f0741048240c980c4843e00704020003607184030710794000300366040182c1004d0541d010340c0e11521501000c0810552545107100c21a40200078030440340c1c00d080030070b100c61a150070703c500c0740510303801e506180c40400f500001042664401100c0c900703900320b409 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 740014307 1250 740013057 740013089
    0x2120709050d020d02031c03151a030a0504021306080d0f022d1203130528060b151801080c0a050304080f070203071d06090606090d020105120f1e01 65
    0x70495241c0c2c2d03144d0140c0c0c15004626503115020302d49044178030303210000e48001840c02700008580c21550841c0e00301881451ba0908010b288000303c50590341c2c08440844045416581c81c4003048481c1900d030b41004c540d6050a002043c0220007096802c4011480d556008032002030203030483e80c80070b0001400c0000e01005130b4041000c000040002c000d201080300304c6d0301615030402e00900b20780c011158905801c61b00b054200800605020018800c07070344900400c0500c10306003201ca0908580342006059135518020044961940c1c241410a1003c811580d525401d1014504080282c04c0c605180010b91783d000090640c076803501a601d20854560700c050440d5100c0c3e40d000c0665109485282c0c00401c1840801c0c01030f503040008c54003414100742c84907503054000300d00600807a40580624462031a00d0300700700e00d030340b500c8040d503c03002c800304c44020305154240010703581c521640c145103645a11901c200319050b000480c5a034040d4a072030030a507100085840101c2075000e001e0040844044000d19 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 740015557 1250 740014307 740014309
    0x10e160905100c14070303020609030408100c0c0512090f1e0105130b03070c0c0b0c10050a1103040c03050606011412070509130f0501050d020a0b0a03090804030602120709050d02 78
    0x640c2e201800042c0c02c140f682c0203019200e101403540d111103101010382c0a000144101035060107060b03004220304004604040c10b000f80c0c0d03a10392045c004014603180d83c0d40c0303404507158400d10921080c00d800100340c4a101d000241c24803500d83c08048007074080c0345803045103021400c1c0848606c05240400d020303402d046041d40c004440c140d10031072514065040a64020584403100002140502010780f21100400d4442c80d142d141c80460350f000c002240340502070070f9290300b4085941c1c00d90444030302001178607942c2c450710400200510a14039440301d001000300301c20010303a8502078060300c0c042c00c222451540d80000445680c1c054a010403078020781408003c1c1c0c24802004d1070394000520b8200703942010704180205070740c9500720500910098407140138202012180c82035501400090700d0901a214058003c6000e55080740b00380d004244001031940300c0a8460340c040f020a0f170b4400b1415990b91790b2800c1c01c0c0042c0d04103406800740d02c0000310224502c1c6000700308260407140046c282c4891600f441e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 740016807 1250 740015557 740015569
    0x3110408070e0a1b081006030501030209181914280f0501090222110c12030907080316030212070c031202010e0102040906171b130f090803010e160905 66
    0x1802c10b01c811520b514114545540002d89034036079480176512803800b440c0c40c2604003d01c1c03950350b002006140c0342c0001400540c03036091714107901540c0765006121b010641d546c0c803403428406001c90090390f6035040b040c9040014115040059590110803541c0c00308026151500201c95009440070f02c40402c0e5040c40003800320b030f507280c0d40180503030000182c0c00f1032500401c1108021180c00c41401071010b01c0050207103614460645d000ea2180440c505000300003540c141d48452424a4851418010000440c01c8030b04101c1100903044c2d0109403034803000020800314003080d4860049016004800c0c008440801270f406039031030a6003142031149090700c1c640340c088492203000c0b5480e0441d501c400c031400c000e140900081c001010303145000166145425400384c1140140c1c81e100400c0c4d006140c81c00c0d485281030480380e05200b000c8039059410a58501c4540c000d04a5004c10509141007032440800e000c180c502840c101c0e00c000a0300320095031170148a203915070b901030010011402d043d100b480141403031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 740018057 1250 740016807 740016811
    0xf150c073309090f1b020a240e070303031512080d0c03180b0a0c030207020303041a04031403040e0115230c1615020f0a030f091d0703110408070e 64
    0x98205418100e0b140d0b40000203031000d1422103088981c844141c0016180828407140c610752940c1b014004800c80b035521030145200e12401b02035000703008140794030092860350003540100b540300100c58180c0d66070310340038020304900700581d0031804010700c00060000c6624482e00550394010126032401801c100b10320010101007840504040d6504d1000748009500c0e61046c907640c0c001c0c1c00345e18503450b050001c981607412544030b0703404040c01480080c0c01078034000140d80a8880c0000305601c4520030400d050f491740506c4d4406095a02c04104440c41080c000c40140140d803a50341c40d0841316a02c0e400d00812005084076102d0000d03400104010403107086c081e001d5020b03075074081880c2c0347c40c402100c50780c9003d03140034034001e50907040c08080115101c2880000980001800504820500c0d46103031511515006800b034288441c0700e554030002c078487d244003400303052132120004034200c601e94000100c2e1022101400800c0c600981440009141c000340c40c11501004002d01c0d0050600b1001a003d40340 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 740019307 1250 740018057 740018159
    0xf011a01021c0815030109050c130908031504020f0a05120c0a050d0b0307090f021c0e030d090503070210020a020111011b11120c0d0909090b150f150c07 67
    0x450a80c0c403151703607006c0c00380f49401801200200240314400041100100c0807000c42c0158610304401d070350008030820282c070b50251038480680c1407140f119000c10040d11903003070078080f240c0340060345003010b981007009881d6a003405080101c0303e5803000381c0c000c99441001c60000100c3d605100080d035030b4116070084800000041c0580351441d40c0d07a11030b0400e0740d1707101884400068005c40c00f0a404400c8a5412030304000450703003806240480c000040d05d9208a00d02900e4803074542c003c41060200800c00c803684198090b001c002e2020400f10029280d00543c2002c90004943c06048040300b1014021250040b40a01013404500000d41d001c0e1901c0750810480b490320302807603100c0310140180c031303004d1b10310f810800028080522032840001c0102800d50031400e450b07031400300c5800104076909e10b41a4454082001c0c0d0380408500400541003101c0c116055a200c074015824000003014503028200e4005034400716061151112000504e4540b0036036800105000303000b40b12a0309031034140d1a011228 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 740020557 1250 740019307 740019331
    0x20619020a0203030406110105150a030b0a140c0a020c01021c2102040308090306010b040f06051b0a060f0e010e0c0f060f040605041a030601020a0305030603030c0f011a01021c08 78
    0x207159408281541c101d07500450110310350303100316a01900c00b07008031350b0b000070742c148442040900d04001400c010114040500446924000030300c2c0c024455028041c141d0032103081001c42c2c5000d0804554541c003001000005006e04468054103500000745050008410b00301e80e409d00103040c5086171111940010401c849040340b40c803500011403480144090b41c000c10301035598015910501d458508182e1182e1012002084200920707030950b8841001d544241c038041d59905c541144070241d1034000c03503414510380500078a940070030010303030302041554551600c10b0140c80d006807140d42c00c0b103690300200c103000e40103c3c42940b91441c160780070720142c4c2c0009214a091403004881c1c1000b60300550454804554001824054081202e4401c0030890754007000b28958502240000d407142207249000381070010100116207035a0f4281b042c0c0d0081540c070021078010041600017280a00404650708507124111045440194804107885208031080d0503600f0403c0d030003100c12107450200501c0001614 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 740021807 1250 740020557 740020573
    0x2313020910050a0b040303120b272d040b130f050d3902010e030a030c1406010506190c120e0301050f09120f0d05102102061902 56
    0x2954440c03105010340400509400000c1c280b00c240503031022142c01c107005024040c002000026404003030485410f51204020031040b41440120b5402c038084148648460000d03c84612640940f003146c910a2591881c1d100c0b00070480b80340c0b80c801c51501c04440c658880060000340104809048040c0c006051240113040403149032501074010a00840840707080d0444048110500d0384130008060011660002c140c1c0742c055844084c1c01c100b00c107001a0001d43c91030840f2030a580c000c3d289a4031080c40603098850520701441d004100c95000c04040311440c05d82d502c0048800800100281038030710140241c1d09c2c3c84861107409400605890103c020841a61000e4000172400c0001c00c090a001e611807440da6541d440815007560401460032503898107000c1044441040022540c0e140c41c10382c00c4055858850b4a858041403040b490541c0c0c2c01c40c1400b05000c3e0310110641400c1c100d428584215200011112020350a0711141038081e40c4208148040c030300d5440c91b8910302407150711031f0040f40d55203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 740023057 1250 740021807 740021809
    0xf0705090a0302060c030f3006010801050405190f06091104060503040321020a030b01030b0108101e030c080f0d02011a090a0f060e07110a020d2405010902040612231302 74
    0xc0d40c000d10408010b041c110141c051910741488110182c490a00708c01c240901e490340c0001c0400344144203131803081340c4402c04507090b007013500c44004008646000038000c00c881d900680e0003401003841003401706071a003513180111642030020742c2e00f07554443c0da4440c07554840f038900302e42207848424442107039000206841645956440100441000c0d5140411100b0300d01c000503044070700e01c030340e40b41c1400800e4080000d0800700302d94a034143c503401c4444009000d041700000c0c0b0100c085400041c00c0b04401070002c9505100090740c0303081024008125983c1000e1030b2000ca00b41c81903880340c500460740407200d2060030f00d4604501e40c1e0041c11400300141e2019080d8202d01a2a82c551080f40c5a101640510004940c4a640703003903214071100082c540a40300d03030b000c1071041d13143c040040c1001206d144500542000c4145e600052000d401c018401e070350312022128002e43c8070388581d001040601203840d0407001a80660f881c55480e250a04205541d1078210440c5414010290b00624001000030001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 740024307 1250 740023057 740023087
    0x100e01050d091a0f13061d060a06030c17060106120e060a1a0315040204020901110618071d0703150f0905040c12120c050c15030f0705090a0302060c03 66
    0x1001d0207146100c00c401180305038140803d00c0a03100460380403828013000181107080302034051003980141c0c0046d0402c204080c00300d10034060b901c0036506001d00001e21410b030b2407a81000054a0050024600107980c0e0300a4000d03019400c3c081034281e8000200422906000381051000b08400002c0071403102504803901f400c3c110308840c1008000d90312080940460808128010b042405030020585950003020b080b0b1702c810000c100030b21071500082c4071a4940d21502000d010664030f50100d4206050400e460109039000c030301040d104d40700c4e00741d000480301c0041c42103092480c8082403924140e150143d044001d4484201c500d400b10803108400070b06100c003090404020a00140c0000381401c0c24034001da2130200079070168040c001c4a82ca03038000f18464003409620400c150410000c00d071814501641040020000964841c40382c101100c1a2180c1c42c1c0154400c0444043c10907059a44020544140c002c003c005038220854660900040c142100203040490030b050442341040d150040c1410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 740025557 1250 740024307 740024321
    0xa09020c010507080a0c0215060a03080a091401090e0112061b020c1203130b030a1407030504060b1909091a07020d14030c1621020606010e0a05100e01050d 68
    0x800d41c0d558001c2000c2e1a0340b04070100c0e00702da0b41040910411025507002555001945100c0b50889802c0000c1100c50350350400301c10041d9401040161220f5599a01030801c8030b00d845100b4641000300d104040540c460140c0c0c10940b544544401c1081e400c0405c4004603c201c10012250302d41e94400c1441c010030503042401c01c41d1501e90003004000c10078420b1040c1d011000103200e095a000f0300086040180c0c0041007000c0c0c0c1e4908100c503860741e0764100454064400300c5c1d0b600480c00718003400d200754281c2c943c01c910f11a0307010701014404c6150700701c2448014000803988040d900032000050042010341d81051b40054007843c518109105000740507440c04c10151218005079001d4003650441c0c980205c15191a0402440ca45045203400c2d60980c1030380c41500c801d01d90b40c107000e864078000c0001c1d0480349039401c5c4c2e0b036001c081231000e4020310207569580141d40b40c07404039190303904500300e034a0071307003440020349d2006065080c41c41c803654003d0368051080e0304601e0500406021042c03941102d40300d055 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 740026807 1250 740025557 740025577
    0x4030305071a100503120310090c02100903030209090903070c0302121519061a0904110403060f0f291903020d0c06120614090c0409110417010c020d0e0a0902 69
    0x10f9a9910b0081010324004001c10340c0840c40100713100300300c0094090541034003240e003c02e4001c5141c0c94045422418845e415003000e440610306103842d01070660580c003504082c20240d070503650030b494401400d0341e071740503854009025030805201800107040800303004a03004040000c41d4035803541c001e100d05086504a0301c5010211003031403030004d812214010b440040030410300e15030b20743d8000f00c204051403060100c40d83c0150b032101c058040d9a005102124000e5812101c1048641a2803103540043e044d5161140c40007170400480b81e080d100041c4455185400c400f42644690040c0c100b40000c43c01d0100d031951040d10051000005601c8100ca80c030000d91050264011880c2012009004105200040c4602c40c7c94110700f40800309848041c115a000200e425880560344c00121003418400d58010104d0a401c062090030103006100c0504183e074144050700d5214100200c40c3d80c201c5148444c01001a405140c103015003d0051042c02030300400542921401ea440c0c101031410b070b03440300c80d40d2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 740028057 1250 740026807 740026831
    0x906040b0d15051c150e0d1116061d060301080a0b090601050907030e10020f0c06060d021f09030b0705090414010b1803030403050d0f090e060604030305071a 69
    0x4061411954850108899207800c4008803103030070500420b100612188801c60031850f400c0906042c001c59484400c8502c0442006100d400c244000c8680ca40001d01111000302c2d0000b0b04000802c00e0200d01402e142c1d00d030304521018030340b42000071504604070201442e0b080003058202c0b440393302c40703e0045000c0c3c21030300001c00d0072141720720b860fa1803c440148482d0b402c1e0442401440256101d10406421101900e0046102120f100005041c00300d00c011201d1194800a00c802400303072644003030300c0e0054424059900b01c3c2e441d42c00344090030010150082d845152800d400c2ca2110848d884821210107070b1070302c0344116840740d84543d04110180c400e503001c41c0c0d000c581040c1c2c0c2c1c5410300601c0445c0a0940389174405d540b4081103d00d01e4054010544400c4503480c4102c0a245c030b040042e50010b503040011200320600d00395007c1c1100c4414140500001c1c100c560100382031154441c907600a41001d0f00b490300d0705140d134904031400e4001c140101d950306c0d101c142d001030760700c00c1c0c031070550282e1a48904 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 740029307 1250 740028057 740028067
    0x201111806070b0a02070c17070302011202120f090d02061006051b1501030210030902130b01030e0a08030a0c080c22170c03010c0f090e040c05060a050d06060302070506070f050906040b 81
    0xe1f00021610b600c010741c010550201030304081000b20340e400840341d0a0800c003070800c003003c5002000e07000c2c0c8a04002404600b03800c200d44000702000d00c5005201d51000e4450742a03072040c2c200d80311007040350315042403241010301300f0515105100512483d0701c07540c0c072040c0c000d00171100d150070324400a1030107041c584044014420352500701900ca6840c0710a0a0800c8481c06a81c003240c490041003007020a02550b80c21100c1f4280d003e50440d100144141003030f16007241c994a020543c50b00192064086a46042c10f81400140506020750181c803040b400203040c990403940c0d5a5280d00c403d1500401007072070b81e0380003890700b41e00102c4140d544070081c05818005880310605086440349201002040414040350008a4000f40700d5415a00d14503c20781440d40c4a0038080e03c0800180e00c05a0070082c0003545141e4260312001800d212400e80c2001d000d10366030f03141c0840990098050180481c6c201d5000300340f806002c1c09a601c580700310303810810709088400700020480c5e0845d50001802d40e0700012 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 740030557 1250 740029307 740029313
    0x602061009050702061306020c070e090d210203100e09030d290913020d03091d07050a0e030109020a080106031a1005090c07120905100201111806070b0a0207 69
    0x30488001d4216040100128540000025a0f03000080e2469540e036001e04112030900019404071074922030450300700ca5030305540c4e6059554408007142c0c3e403403480c00f5030008070001038403038840154403200c4042c00b80da5aa0092644900944c0040e040c524000401d00f8000303141b0400c40301c054400c20358000559100c4044207001c8050311340807400154062003066412a010a524889032112003054850010302e0b50741030780030440342c5002c15019604c9028a00b118003050390103200441550b0300d03051071282c0e0f0850400c1141e44640c06982e402c002c10020300c40d0300c0c02184031f03050307086c0601d800400100b2004059004280300c6a60f6030801d035001d9469100500511a42c80001c9101e443c91455003e0345281017842802d540741c0a0080511500c0c04001180c003950189003650700300358011507906090081140040c040388214842c8501888040e00c0b03e107811401841703551b405100b5a081e4601e41542080a003100d80000c403581a8014010b00c10040801c4414908900c104040c50780107a9501c1681 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 740031807 1250 740030557 740030581
    0x30f090b0106030c03140712020909310201021b031f0c09081606030e1e03030709060816180b0f0a0806190506090411070c03020906030c010c1e0804060206 68
    0x40001ca06150030310420009900c581c0c06660f500c080e07d4548203c00c5250401890081c0c031803100201e60100c1480c0c1480350600005103a088004c8040d800240008041028075040b0f130300d074181c0030340507030051034030f080a00501014500809500070151401100030f0203d404550001700da4500c0c000d9038a0210903210342d00498106d0140444c07800500c0411040b10500380304800a0007004101030f03c0304a1150f108608012584c541c0600ea41e514010200410f0f2481d90f1360402c40702400010250b400000e403990080315100d00400350050741e58840d041403a000d0f00e0000070f00d0006c3c5c2461b01800d10005940c0c0b420340140c49c04007080e0498643d43c41d11808010444040540000c0c410001403c207003400c503400c1544282100e0381074400316107420740c8500080062a0000e440a4241000216002000346161080003940e1003100e5030076131611098107040c0d0300d410090351036000c01e0340c1d41e64038004142982403100580e401003080d4200c0d1040c9561b1a0300940045c0d129401507400300741030040c1c200c080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 740033057 1250 740031807 740031821
    0x120a0609031215031412031302040b010c080306041d0109200307120b090c0a0803090312040812161a100e0c041202010e040216021807020715030f090b010603 69
    0x1d0310b0240000c1c8108416540c42a4081c80024101ca014440c064980c03081844000301201b1108010b5440c1d03e400a00307005404036084089218925141d440d090960043c0503548520f500049180e00310369038041408010a0354850300c0701e00150700c00c000c68a0002c24001c100c2501e114003101e034a400f9148554101040d060442a40300f504204014480c083c10b02d48800d0015800200b4150552605c030103203410001c401034901d8006c00040c0010032447c0f8004020218144103608a418030342d0740d45140440c80c0964000e2160b946c20000000c480b101e454005000c6c0808541c20000b805030440d0745208a50400d8410302c0c958241031003c01080341042d010100042550603807000312403900e00d90781682441103024200d520580c080c00c00307041d644200c0d01400000806001155509402c3d2491051440b400c41c0c200d120b82c00c0c450324102c85004203010a030065103160002c15082d0300300080d84a43e000f00e02e46038400c05582d01c80c5002c0b41c0e816405100100c4c4d0056000704455410400300405480030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 740034307 1250 740033057 740033087
    0x706062c090321040f080412030f0c02060a0302070204141003033507050c011401090e0a1502030601050c060406231005060901140d2301080615120a060903 68
    0x428841241e141e6032540c0101484400e05600012603619440e00c041e8112100c28007508046c404900842c20001c0d1b00c445042c21406600d03440e034441c01c911811500302040c0c0400039000141403180f0241103000b40c000c0c00c802407005101250740b07a02e40d6030040c2680b400700e8080040c410744110810500d41c01401d281411540070048a60005511845860704043c0e00130580010000c0d000203603004c2d118005030f640480390742000340000c13400c1d0680c1180302da4080c050200104d190540c000001d107000100143c0c40da6200410b180000c10303912840009420041c221810300ca0308002c10341d400f01045c040f50784540d1085a00082c1c0d404002c000072071540440702500c07403482c0d0030030910a000600c4000281294401c0701e8003640e44010600403606202c11544500c1c1403000070880d0420004150040c05020440c40411101e13400441400c2a0070002032040c4052a0095800304015026801194450400c054000201804d003903854500d800300c602000c6e40c86a41e070ba030503841010381c404004001412 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 740035557 1250 740034307 740034313
    0x313030f02071d0a0b03011a01030c091a0a030608120c0d03091e1e0b0f07050301150c1a01290301080705130902030a1b0602190201050706062c09 64
    0x8246800007a1103804038410b1900560410000340131521a90009811008090300911160380d021110303007011840c1c01b02007800309050180714441c051090085100700c4588004402030340c072030f6a074100c0b100d510080010301050707241d0303e010881076002c0000c0085000c030100415a20a040004641004071410010080600702880300c0c011900350f265074010301c1040d0310032680070303003c628241c00009030003075040543d45c101c41c0c003c909004005d00d080384286d0308044898455900c0c0c54044802e071000b401080181c001c218102a4964810003030061080d03c603070030550914200c18a00000200c0980c0300d4685d1120843c4440c0c55a40f00b00b11108030b0b0002154030609550400300456100c5120380100e6000700a040100726480e0200e4101000741c50300501540c2c440c0c807460801401c0300c0107401c0d2550400c140c045001070b415100040786c194844030005d00840d00c0580b03038011a41075000c0b075000d6030403985a80010036840c02c4403050840e0051311041e1000b06a010f40f40141198000074114001c5030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 740036807 1250 740035557 740035559
    0x5310806160e0402091311040812122e0f1e0f050f060f0a0503010303080907060c170c010510050301180f02040e0709020a030507090909020d02100905060313030f0207 73
    0x50b040007007042c02140444016848040320800b06048180361400190ba481c02c001c1124550b1510b20700410560b40c0c881d0070f84080708004020613010341300d486182c00405100c00001807e044040c0580d441c1d108461200384012203102c40700b18040312060300803d40c1c2d80401e410800411440341785c0303035188012200110443c50320785106038182d40002c2c403901c2d008101c541c0600749590307610790860340704a17030190305680c9031841081c0040c103c0d0424001100800c1600001c14040c80c0c00240400840d00c1681d5100d20140c1c1076520144040c0d24441c03401c06000c0c0030700c140b403129030302809002c0c030400c0d260305008a9549040101429103103518003503000103070fa68030a00c0101d2486006141304a4060f240812922481c3d15010301e0b0802d954044660184045500703d5030301c0d80f5405c0030340100e01d81d560b6051001c0c0c07243c103420112181010005d61040c42c44040364010304082000c18042d40c100e0030440d5400e036a400114145030b1007100c1100c51032104c8a600420190030001102c100021407005080035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 740038057 1250 740036807 740036851
    0x30818091e1b0f0417151003030c0f020d030e09060103020f091c0c0e0402040b041a040f0e07080a0b0903090d03050f0910050c010b040b01050a05310806 67
    0x10202400303584460750201c45011100c4080300c210344255200025103950380d569401108803108101c0d1408055001e1a414060b02036040480c0600820711f40c0510b0384154610b69003500c0001c08110111003071540280b1040160f5540ca4004144501a032580201e000b051020880d84000003402c0c42c2c18584140521003000c8c0119080e01c08144055420445100707810b141940108044e4000824800340d0010226a00141404842c0180d2003a60103021408485c4c08103c2951798100c4102c1101e102c501c0400c2140c1340136040314190030042300c40014483e194014140c1031004030f410210096100d103000f0b004002040000540c0208000081c60501c0c51150024034102ea2616014041003400f14001d01d80130150310850b440b07068001c0000720441051140640150842d0b0130040e4254a4050f000c240c80c2820700400440c440165150f44c0303005000d12064515800c40d04c5189085204100401c0c42001e43c681065400c060703640480d010180b40416040c64604020704902100600c00045451 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 740039307 1250 740038057 740038111
    0xf030c0906080907030606080f0f0a0803060d02040f0609060501020c0301021e03040515010611160302010e041e060902130f05011b0302010e16080705010804020901090c050403081809 80
    0x16500989031020043c1c6881c02c2e1949403e03402e801c05010507180c4007000880704170008131243c08039041029190305114401d50503864290000000e812101d00304001807603460448017001d91280700810009284050071409400c42d17400350070408a0075524401400b0568040260380c0540c08120025850544040c0280448240100305410500c5022010500b048404d0100d11001d882c80c1c4400e09580da5106001400c95000001d209014090954005c0071680d10b011a00140e80d01a103a2140f441c10355018030009105100f40e82403203604c808200c421555107401880010865840007580b50781c030110810380201c074a5800504143c03003104082216982200304680c0d9480c0100c40b0400c0040f02d8181a4058200320a00d80100d00a601d00d110020408207440d009841032201290030950312440155100349080e200a0350160f0b00030010486001150050034a40391689000c9003001c0c0e0b00c1e03407045a1600b00a01c407200d0303044240e80112040c2826070032280c1c440341701004800c1e44143d81059000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 740040557 1250 740039307 740039309
    0x6100e0907031d070602030d061a0702220c0f08010510090b25081209033402091303020105010f0b18012105010302031c0824060d0f11030c0d1802120c010f030c09 71
    0x409003033780345032138010b0a0254084600b80311039004140700d5001c0f110001816030702e0a800714000f203100d600000c951400e040080c041c0501d110b440f07003d80701d810310800100381d0300000030f504030380c01c6c420380d010740d031131681600481e6180d00c42c2500076250b00f00380071100041403005140181c10350092102103c1500310b00060303541000d1b0b0380c0726941a900d08107800e8036030b0848143e010b50842410018094038042148660108030700950003002940d0300e91008044581503813043c80c2044a050000100c1249101e0036001185014140390302a42c10101106085040000340602299500d02c010001c0d41020302115501107202c1f500c00030041400780703000d040c441000e4108c0b10400022070400d0220a6025030403d400200101419125100c11110201900c4524208480c1e2424504e444d407106038480c05030390141c030a0f030701e01500385903080c038050004000e80c1c00c224520b07803100305003400941c0300c440d5a48501003090740500b0141d09442c001608440310440444209864a03802c0c0c0c4009600c048444 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 740041807 1250 740040557 740040559
    0x1c021501030f0614090f251e21050d02061603022a240603070e090c10030204051009060909020915030f06100e0907031d070602030d061a0702 62
    0x2c1c00d124185500100640c6001d0a41ca011000a1015080e80011a00310840101c0b04562220b031014403090030300c100104412100030000c00082c005042035000c4e0350103a20144107000c0d01d5681d1a8502024881c032003294130b40080025403041305210081c00000d1a8104500081195050800d085980c1000301d41c1c1d09402c0590104015843d07920a100e00c884140c0d08210700107035a5003201c0d80980b103140b000315089900441c0c0c1143c12004034a0301e4014424400200501551450b0808082991500500424150144110320203280e030310403000310689452680c0044c0c8860420701407040c070721498203641d424400000070070040c01d5840003d1005403025500c02580b034040500100350102c40917a900c42441c080481001402c0b00400c10741c3c1e22610046400003035448404409848003102c5e418019000400b2030700050301540203030804c030808c60400b8460703104118070811881c00c013061504070100503000003d4128001d0814000ca1018082e203c031745540d1402c82400d000d06d940b00380f503c02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 740043057 1250 740041807 740041823
    0x306010f031e0305120703020301230604260105040503090405330607170d06060807080f0709080a03120605030f1507030908130e1e0612030409020406021c02150103 72
    0xb001018407500035204083c0214030095118145510042c0c080c5d00240210f0501008040e020418255201252040000c01a00c424940790070054001800c903c000c106422403010100600c1098009210b20351249018001540d102c08418040100b1b4580252405660184d0703040c001c0c04248002e0501c0135140708541c00300302d0000c0241c01207035690060803000f41417204103414091011442e1b030010b0900310018401005110340360324055601074019904100040c081c0800200403400c01134011f0f40107081e6040000c1c0480d0b840400c0781c6000f860000031000180c0320368580302000054014400608812009040c2103112055815a0360549080403085820307494045105980030364408041c142e080b2800d190389070354407000002c812940d44141c0d5909481d107000036080c2101d46208002440b0390b100c502c0030755183d000c10055026410b040040f1540400c100c002480081031008000804058001d80385041103809103801e407800c00024101503400100050503030903c0408442c4c1566840150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 740044307 1250 740043057 740043113
    0x60e01050304111221070c090501062a08070303020715110a03021315170c03070c06050402041b0e03010e07060507080f0c1504020f0a0506090d0f02030604030c020306010f03 76
    0xb9910705040044038024101210f079890005e0304d0f00000901080340130381c52801c4060340d02c0c0c441008980c006d00c10350000480454107802000c0403046c0300200b6415680ca00131b1902d98946500e01e866200002c101d0119a0000701c1c802005036403200110205a01401001102c90b41090040b261040d84010303000c06030300007003020034040c00365008406400e1110b1940c0011440e10400350440103041e6080981c4072490000a1104107501c0489204441303907900d603580b124855032018050301c400740c030072644291520083c0c05401048801040304070030950b6100c0407400d0760001d044c04c4a1080e48070405613000300c54103002482e089011a9001c0e5030040c000356030b800c29400f2400050080301d0310602c030741c0600c0e1710a002c40710440000342e000703d0081310014051001d0100300100e2040c0b510500e81c02c00c5040c400f00c04245005007c402034a80511500c0c08400856070000c0c0c14104216022001b0a103400c1592003541410007109000d020a9504050130f00e055071120320080a41d062500c403000b50f82e0007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 740045557 1250 740044307 740044339
    0x4093e0d090b16120507050702040c0e13061a070b15010c12031e0203190507030b061201030606060f02070323150702010b040b0604050603060a081204060e0105030411 73
    0x3000740c014a41144440e80b1605084411401e40c00012400c6000601280c11205403100c0341d11565026070582d4039503a250900320ba083c8400741240c1003406080c0880d5200d00b020640b200307481d9030310000701c8100010f011741c04c040c0081021512500d9495410100340291790006244006550300220180c401c90301c05490840101c810480d0094020440200c40c02410b98007a00354000c0c00c004400900113031451024620414100e000c2200c2c49070a60500352440c841c0610740d81e0066401401e01d14000c02e422040901140c501e83c040c180820407080a00b0040003840010310031034004d403030b1624000d110311b403c0e108025580e074410300001e02020168030710004140302e80c40c02e254500c180c0b1000d50350300d800e2281d007010810300700b02c81e610055402d22842084514261003603030031034100204082d0504d42024180a85500010051600801846400710790341e1070420040c02e400728040b42c513660741c03820500e000340b20070344801465041c82428014000021010200030040801c240ea01d0b13006080303805 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 740046807 1250 740045557 740045561
    0x3070e010225120c0f0605070c090c020d0c05010b270a0c410a030515130f06031a04060f140c03190e0a03080915130804090204093e0d 59
    0x544048540c5e40e95040004a140c1c006024004441c0940c0f40c3c0c1010a60714410b0b607040c1c541d8540701a0040c0c0281d4001001c80380159056038056005000001e13812000c80b0102d03407100050300342601703191118040401480e412880e450390084c24420b081c0210b100c1d110020348107800080300c066800640182a1f040d41c20390100c1c95006025014546528007a8645d1142d0a68040c44035071000900740740010f249014001d140f02c8280c03002502180d4500b031003c07000300040c0041103078014081d898203000400b00f0310a0214250701080d0407407021381400c04c2d160441c100d805220203021228200105c14400c8182c2e6a0500d03401581c568965603280e440700e02a604490b40785185100d00c0d4940008040c400300009076150b0154444e071107030080d82d00d410030100c1d945c41400041079620320903200020f40119068010200c0303a4403542056080c141c82d9682c0c0c000ba60829000f58400598035414542405c0030b81c100d240c06041e11000c1040c032007008100a4403100c07191403110044020000c1e07050366903685a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 740048057 1250 740046807 740046809
    0x1063602180f030a05100902180a02030f13020a05090721021c09050a12050c01090501050708070c0b07080c0405040e0f06091c0f030f0203070e010225120c 68
    0x21404568510070300340300d100790505000030759010701000360b0b0046081c20005040b4401c81d0700200100301c1055514240340141500d160100e80205140504400030403003248050f0203107914010140e1603160204850101140003040e503c8544418407034403000d0307100d034401c0005503402070320721030999034401e007040d2051401011491495070180709007001001d01580500425490038a40f001511110548c42040e100e1010303029141d40c0041450b400001d083e118050302080c1c45040c880e0078440300b40c1001d821201700382002d9406944503820040d500703070700c490002e43c06130260400d000300214903100c0d20071807400105403c06110b0890081038521900d00c003968000c00c00100280842901d18056035120080150800d600e88108130100d4480c04012400511144ac0700400c1641e611451400b1a0034808140c8000245a1f9581200f0300704c1d240b80c0020b40c4036030300e651506045110420002880d214403607414550b401110311019002c1c0e255011680d084442c8a400504040128185030b1202581 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 740049307 1250 740048057 740048159
    0xc150209090a06060f02070501120c1e020102040657030e0a09090f0b13060203041131110903070f09180308012606100e090106 56
    0x445002c10205448a0b000b80003038800710b81d610310842c140410b041c2d0343d80c5043e015042c00305140320200000740d0910340c04a681d140300303490044880c42c818094100d04091030701c030000040c2d400003010700580b0380020010a04101c41c543c124051401410f0715600d00b06010141f5044114010b082840701c0c040141d88100c1c01070103040c5c0134080d03590340f03005010404204c0e010fa010b1344400000255651503071040410786504503802c0d140d004d019135121080341c070008002c916258550120b600c0403800031310207588914800d01e0f0703440e42d01203c0c4080200ca00c0c405820b00900d99001129004850b03d200d08014200d402e514001c00c0c0d48101030001d01040c01142c03001e940521461000050300b511a2595408480ca41c071810000340c02d6203040942c0c604101030000e008140004010045512884000f0107003801103502580d0f04088042041d040c138000b0340320466000e40c42e84061200710003044500e90007802d03840c001c1007c14944104035018040c544003a0b00903480d00015400c0c124510700d120011140c0d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 740050557 1250 740049307 740049319
    0x8060d0c080106030309080606030706080c04030c170105060f060412140303070e0a06020d020d0f1701030b0603010b01020102070c2c0c0706061413050901110408060a0c0c030c150209 80
    0x185401e951402400580310681c0011a48180020000790125440780540c40240240424909020707040e150028050424110b038002040000041510f01c2c0c140300282c491030140201c0d520010b600d01c1e080d2000501107601c00d00b042804800d0030340c2c8070000c03142100d0300d442c1c001c85440b80e91b04200303142c000c00c061001c940340400001c1144555000203802040c40045440a410b940c95410890352600c0300d01000c0d0140e48005043d0444070300070b000d4100104100d103444011030200d02c02038100100280c2c02102d0012074070052104c0c41c5001e026155201c0b1003071008606201c51911464000c100340d109412020411b003d614281c0300c03901029007280008620155a03e040c000c40c0c140e690703801444281c501074038082011640011188406020520042000f503600c0381c11040c220042c0f034007501942c12903684a0000012004050281c0014200300000d0002803911740a0f80d070030b440e031044d08031042005410b05800060780114202d402a81c000040c0320400d00958855802440740040c201e504c12 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 740051807 1250 740050557 740050559
    0x3020405030307121403040317060a120b06030d0c0510050601110f1f0207120e060d0c02030904060911030c0f0405150c10050106050f0d060e19060b090d0308060d0c 72
    0x100f030011131000000344550352580fa410264001c00110701040e10000d00041c1002140131300c041e814100150005d200400c81d41c5a995940380b0404000114241150154004d20800001c6e18040c80303054402d0440b41801c0c000703201c060b0380380c2e43c44401a00701000c1a540d91070104900d40d201e59070110600c80c020b02214001d00588000366680c0d1000c0311580d91041071200040138032040760080d196200e50042541c030014049100030388404009058154110f10f0501003040203514500803a4001f5103660050365840c8007410038001680c0b01900941a10f42c1030200700c0c0c3c4500d00303050440380e000b0f0382001865100d41d00302e0003001c5c9502c19980160360150101c10901510022000200041030700101203400d02122002c4c02000d03244244178000210700e040c0904c5200000e2400148041001543c0c001181a15903403101c5000009a0b02001c3c1c0e0341d070b021391a03048514507101d9480503025000b075480c100b40c42d603400613501110082e07000b4104080c01c3d01003443d41e111050f0640c013035030388150b00360340c81 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 740053057 1250 740051807 740051813
    0x40c050604031b06050901200f01020f120a02070b04031202040317181e0f030f030c010c091202030a060b0613090b0f010305060d03030c170a0f050a0b0a090c03020405030307 76
    0x550711070f550144503080140800903401d4022022903201c4c54042e1904100881710b0346808580144d50201c00b5121701858501e082c5a9a0a10050005030303d03502e40f080c0c403905140a50001e00c0e4000300b503c03415078410003581003c1000341c0b1425610550603d03104012088000c840d102900507075000905004c00c00310745d910040c504038090450804c40d40b0b10982c102c100c603020041c01400900c200c11020b41101801e240740d06155a50200040c40541142c1c0180000440d9914550083e00034141c80d075502d039000a002e56226044800403d405260000d044065400103900c824503c200145419684c421103111a1128001d84020602e004280b00c10f59694044007000350a68000440c40785030591220f0b0311540c040d220b018040d18015152404c46031403582c00740d00620310840041e0038449812944c2d0001e446029045201d102707482c0700440d8007481b03403580e581078403000703082442d4460420014910580301c1d220400300722000b10401058402c0b04900075002841150841505400006910018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 740054307 1250 740053057 740053073
    0x30c16050705010e041b03050c0c0709060f080f06070e0f0d0c1415090906030312010f080d080105031c11031204022106040803150d050a38040c05060403 67
    0x80b110203032902c40c01e58079200c040208894441d803c0b2800000c03200300d503040047c8203900c0b4540c00004440001e1801c1c5442d0242c0d840c28415600280099455041c280300b10b2502144580050545400822212514078555911100300404000401c5181400d5040e10340e6600303d10031740350754081c15100140c011400c100c42c041c0f1040c001c10311204000020412241030440300a4840600074515500b400c003048104a021603020700a550b05220a01c09100c401c41460122402001500c16582d800c81c40c001801c3e040c00c500442a10500c00c502c4010001910041540c804041c1e415032004040c111411042d2000460052019107604c808a03086030750300c480c0c243c114021402100c1c418055000d5400c0c40d0400c6000d00c1220340c1d2900600c2c04100001c860303c2c0a90740002e689a0514822800d110125148944011041c0d9403a130003049450300303000c6054407132007841101d40b4848514410b117040c1845d840c4940b0044120341c2408200003030601c41e044400c01d02074040100718a950365902c0c240390790 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 740055557 1250 740054307 740054309
    0x302060d05070f020f0c0402071103191401090c050112060905090115050f0d140a0f0b04020f041407051305060a0f39080c01331802030c160507 63
    0xb0205034001034900c0c0040c000122048109100401070407200d90640c03d22002e5006684212001102181e45c0c001c1b586e0140000f5110144941003054211610f050000803d000c178000e9442c075034580020500490002d00c814401d8403c2803c001845928a5580074014004d541c0303c4040e0070710303020600a5945064019504e04d12038208031034440c0740c85100300540302d5400e650485e0700c8030850303200400041c48070320202e07111103084c000e40e5101601500d40055090a1500440e1103100c0207042104601d40f120481c500e04400f510204000c00840148280207100a00040e080c0030001c9214800050000d07c80e10180c41c028000c9030719600d0040c800f500031446036004001041503e49a4100c2c04d0740c95040c0d5006400c00010b201004048100b00504c025454000382d58410040204c1d4a00e000709000d03400741800312184000c41c7c501198026030020400a9a210401320440001c02c1011034008001010382d008102c01684c0f03031618204040144070b40c461400b10003a041d683c0406118012070104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 740056807 1250 740055557 740055571
    0x30a050d0924110709021210091e020f0706060b04150f0207051c05011508070b040605032403060c120a1803030b0402091e0f0f280302060d05 62
    0x70440c0b03454500451041a501d5206110b4404111040e0441486006071000004501c0c01380c0700c1c21a02c458600c0c1c01e0780c0c0b00c070b000c142a200c1c0c034030306001c401348426030008002c10031014104092043c600100450348154507884400359004910b40c558030120f00c08807848550311a804101995541c00b072400e0681042c03044c0202224424000980745002c1c100d0056024090350140880c28180300400460340409043c1e6000321241c00d4020380001c50911440401240038610b8000302464010300d5803030608650044218000103200c100038007500a02580c0d00500302001018164481c50680c100c00034a2401c2e40358144109000c0c00303801c1d1b034030000a10112011400d000c00640c1c5048402041d074103070b012500b880b0791441d821207000c01d100307900c0f0400d660002880989031100400c00505c0740400c245009141c44400c0a60340618640b031110f1240200c07050b01ea06241100d504002024040b44510071324501000c40200d00c101c05161018101641d401402580c039000043d10000003043c04031000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 740058057 1250 740056807 740056817
    0xc0305041707080c03070302090c0c010914010b03070501020f1e0f010207081306030b010507060c0306090f06050306130809090405030d1409010c0c05031c060b0a0333090b010e030a050d 81
    0x4e00b03081c28003054400075030f50003400d070301c455031540100050603a000c034020356099540c0c0e40904000400101c1040d01d0b4000c0c050011902704820401c041c20039003103a103d1815580040e001444684002c561401401d0080501150718048402001d09152006807880b440794400aa000e041002c000045c01180071022890341c2d03e2901c0d65025070840749403601c0c19000c00c1092000c2c1c2d001070040d0b041022604000d19001c50465501c0041e002907440400c2c0b008602038480c20107100740d042c2080103c2d800141e8505a034820410b644551480c0d2003010642c50003849075500003030500c882002207408030403110108101603512051000031180064075203001550a04252031012485803061911881d0842c0103507207090340c03004841c0049466507030f0a0109645600700021690040d01c00b400d1220000c0e1404035840e042215105581910294071a10501101d109411038240118110042d90554140080c0c94a40c0c100140c0d501d4038201d4001d50705100d01d41c0190f0401c480441c0803a000c0200e41c8031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 740059307 1250 740058057 740058073
    0x50304080706181d180d0806012a06090f080a0c0b160e01301a01050406020c090a09020402220b090105031f0810140606070b0402010c030504170708 65
    0xf00d410303910a51195801c10300c0c0001482c1c0300010313950040ca812200c8172030695180544130b00054107000c0005030110105110804101c89940c102c209542045100d0313100700c00100100c640c003000c0e10300e1220040d0040d1343d203180c13440030041005428441542c1180c0c4180d11400441d000510034182d0a034100c41c00010800814020440f0500c0c094003c216501c1ea031002030103e000442d00c5440c0c00d140da50300c901e1140b1624080902c41c90340700d4800a05c00030040f0b1031000910206c11184000c0e4465410007000700410004140c3c003007003d220403c0211070b0940c81f0b031620500b08002e000c2900c0b01039480f87c07000038249400240c803043c0041e02280c05810081d999079134100c4100364042c10942c036012030340800005508002e2003400283c0081280c0815020355140c41c030281c03801d003189100c096400d80d03841d003201d59840b00c00460b651005007103c3c1985400560780c1c0d003094503100980024103000c000700c42c15003094011402c1d40c0c06059881100180c1c7c40c800c4202c103030b5802e01b501c25810b0798001e060f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 740060557 1250 740059307 740059337
    0x15090603020405090f1f0603020903010e06060135011706010906050607060e0f0105131a071e0e030f0102071a04020a03020907120507030c020d210c0507050304080706 73
    0x2c0c0d9040f510020007042e0503645220362188080c0c3d00501c0c000c078000c1c40e0103420a03010280902400903182c03c2c0e50058444034240145401c45031b9110b081300700c0d81e01110410129aa11201d410304040c002c3d04d00d80c070b041d4000e902815512450b503400171910300c3c9203c00441c6500d00c08075000c0754801e941c4100e61159a0b03903580e04d0103d45d00c5000702030b0011010040800811850f400503403540448404031080c07034500c0700526013118000e842091580594040440620110529044000b800c0201a03000e605101c140607008444281d28030051001e40f140307202040780120b0103802c40200140541e012201c001d5200c0f4000d41c070544007161b529603849288201c5111840f10035110b07640c09011415610704640030040c3c81000107001c001040404500c6032810300007400742d14001c1e61203860204810190001c0070b030404043e0652271080103034510b104000c40705250018145c0180600001541850111044409114055001d0890b120029000501d424001411400c541c44c0d585c9403000b0f074800d11 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 740061807 1250 740060557 740060561
    0x4050a06121b02031608090a06080412050405010e010e0d020d051f0b031002030c0d0f02250b0103031110021c060b12060108070c02030f070503100605031207030207080715090603 78
    0x8441e240161300504c2000b1182e002c050810281c140100c4c00981440420703400074007840c4490300101d0008900e402070004118414072052221001030601c1e40c1041d00700400204207242084070141000f6090100c022661030703c902d00c109003034011b4141c4a00028504003655552030f41103400c03201d0701c84541021040c071350a11410070904d40090140c071703280403c19130f0304011350002391252170050f40c10000c0e9141702c0032a00ca000b03c0c0d0301060a003d81c44000030580c058150f019034000c400540800c1080343d0004695040c00b50549602d4100101d03040002d404031840c0c613400700c243c0e0001c0c52000551841c0c5445550415203007509143c0c090000c00e4036400850464000e01d056841e2680c10800420020341c0101701155100200389000b080041c103e07000a0b29298800c50010300f180c0041106000b10f050034082c3c03502641000b88144425840e1801103541d4050894807001c0702d00010698070201032003071110f0300003040c80808548000d915803140c1070800c0855115680898141c4000049090184c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 740063057 1250 740061807 740061851
    0x50414090d0207050609060706060807080a110a0b1c060b071a07020c09010312120204031203050601090b070206030c0f03012606150906041103090a02090f151504050a0612 75
    0x3401c041d04041b2508240704140d00008000c0703411944a000100da101800c210200c01000c414004101c00e40c03890500056050b8100c844a001d1403100390140000444072044982c2e01e02400904103d090700d6013800801040035400100018100184510a00c08102113900c0c3d0b00c20303c10509061901d40840603a6a0307246604182d8001459a004101040c0c40c030240b104088618108603004400c0e26155000b2130780190021030f40d00c1d148942856010fa414815541d100da000e0034011401030034822017035424010b144009204040010005160089a17003e6902c003003444003800d0703120358465005040051040040390b0704401d05e40d01c210b618010020326280078080741c00d541c0d20306003024000d10140810082045810984030a801d204560691000b10310446212000d070401c09000c4c81004140c4002424004090741800140301c4a014020044009503008848800481850714079003402401a03602a580c06803015400085540c0c004d03100c03680070414504200701400031140450741c2d50b284 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 740064307 1250 740063057 740063059
    0x103120207094701050a030b090414010f1512080405090f010602150c0901141e0405040612120f110a230109030e010509031204080102070c0b072604050414090d020705 73
    0x400200f01e0003940100000c099003503443c034020402151510115140030410f940c00c03602020300e0241c100b07141d4802e00c15165a07001158080c81441320100c215900030b4201c1c000c0308001102405c0e88410480400100e8004000141001d0800d1a02100c008030802c404d1180f07802601410451229115481d0411032081606801d11801e00618000440b80c038100300f03008074101d000420800704400c0080880150341001101595a51400d040500051315202d5200301d01d1803a6030750f0070703500003030302d010007581d2013041c40c6424060001c80d0042140c1c00c80c851440c5d03e06ca0300a95090b10140103010144101c0f41012580d102c0340c0c56036007819142220600103000d800204900b0006285610a4004141c3d5200040c101d0b02803401510140645502c25400201c2ca82e5002070000c04110108d42100000c02c2d841c1815400d1000c01d40300c004006200181c0400c1044171110b1056841078010241d40190074007804c108404c51309500c0a00391a40281ca19a1991055082070b10101e88005903210540740 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 740065557 1250 740064307 740064431
    0x50904060305010621150c05091807020c0d1502030601090f03030c05120405060d09170d060f05010f080114010c080307020313090e0309090c160302150a050f010312020709 75
    0x1000c8840300009181c7c80b401c90041007030800c048540b80d41d80d5a180c0a0801006294070824100b00b00064901000d030b110890092101420000104009000881c12072102c1d181c05a0340c0d42da00c4004070b806104030b411100b11040848000710a15038081c100041c0548114125112515001c1855240740150310883d0740c801402c01c445568002c1c0c5401c200c0c40107101d1504401b0081c801d810001103070700000e042850290761660200b02000380b0786562401040e0a00700343c181622126001056079005000b003050400844c04207039200d91081d0304444103030307812039a912f803242071a290003500d940c04007625024000359030001080e04034151050112103044031000b5460625490248480c00e00000c1241c0311b0240103100d180074480440389465001c9110b54041c2205d05000c6825020301c0070041c181c0c2203010724050400100c0e05a11400f40d041d0790f00508120000b40c0091030880c50168150405210a41402c1c203c0303030042000b10458140115080301440c40d110400960004060060041e2184032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 740066807 1250 740065557 740065583
    0x6040603120309060b040203180606060909061c02030601090c230a0f030b180103150b10080408070614070912020d03033206041b0206070f050904060305010621 70
    0xd02036400320200070300c0b441012813805c101030005000c9800845044000704541c44604100d003605100e0356a10160488109041c80e10035000301e240c90034000c04a600906424030314032031002d213030301d01c1802d080d0307004040350269038603400c11b03401501c112080200030904610303012490728a00c05900034903064942040e410051080030031a603030007084a54605140e519000c01c00140c6560b104003020308003e0501c080294034603e811071031001b640c2c0c480580c540c50902c08410750754030000c481d00c6420480c600145c09882c0c6003801100c0d031060908c0100050724081d140b21207200d5410802c3c0c8140303140d07298541d03c50340c1c404000008a84da0350b402540062011051000680242e01044903c003c008003011216000b00411016149100184182c03056032010043d05280c5801001c880620300c00740f075075449144d120060759035070f0040d01c40c500b84401e4880ba1151944641c0c141c400039180200284050f0b507903420510300030021801901556a52400d84080c8080e02c03054013903c0c5913200d4005c0f5a04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 740068057 1250 740066807 740066843
    0xf03310f080a0e041a27011202150c060f060612460f020703050910230c0f0f060a0c0e042306030c010e0111010608030c0303090606040603 61
    0x7076840000c1281c1030002101038482203803a244100c1c6602ca074082c80115003000c824003001058801d584201c526460524001c2d07440c08400030324181190180c0c4422035001c03180b80f00040c44e4200829030f00c4685540419050400400010414011024090b00c1091602d40d28103202061145040d101e091564039404610041d082107460349050309030082c60104843d128090110000c21142d550700580148401700e084e603080ca20660034100603400d402c5282440d00e98000e404da0250749050380c414a0305003100b505850081141c0609210410030700d01c3d14800c07008a5110170340110300d110051b03208160b51440c40d00740014409002d4008040141540e5030754940e408068402c44002104100100e50300000a17100da01800d00619862110f51880040448025852080040055101389d0000c10592000e0344c01aa10440c44642803810000004440300310b40d025000c1980000c20620000031020030110010004e140101d41000c165496620f40104120a1b20014040900f8041c4460010021 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 740069307 1250 740068057 740068073
    0x91005130e330a29040609090b06090d02090411060a030f0f06060c0f1401051003021009060503070302090315040b0612011103160219050c012c060a050f03310f 70
    0x8650310700004c4194141058009448a402a901c00008502110b4080c00866207500644041a10a42d401400e0004441c0020b141d1404040007901544060b00450140800310114009400d0f01034038581c1d4035070318038a00400400c07404104c1440d2901c4e00c4007030075140076030b0b028510403204660f8440c0c621813050f440701828044220b504079202c00600c418450840400e0017900e00c034807000e04100d1800340c950f0040c0324101c0650f8401c2010420540b00c24480c0c40d40020982e500814035143c010f864001aa012a1600c0903642c0761407140f07041c4008010070401d2007805a44103190584902c020140650b280d9070a03511440700c50540b1107014000030f11814105440380050555903c1220026031816400e200d04d8a0041010b803065040b548004105580100800100000d65440003c0b80311450007842c007405450303500c07984589800100c8564080c420012f5824208104104c03a50320f040c02d1002c070141c242400118540d00015420661544910034800259030707801080c90f890403c402d698040d5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 740070557 1250 740069307 740069339
    0x30309010f18060215070807080a2c0106091805060103080702010c0b090f070807061e0c23010b0d0b190e0a0b040b0606091005130e330a 60
    0xc100700480400b040644050700c00700c030060041c1d40150000403002c5101c1c400340701000b0a090b061207d0700061041850340300c400c40703501510301c1e000050148150620006d66600c8010201020000c1c5880120800419400035003100c80d600c0040103506400c14144041d4400103102034041c1c1c0000c0d0041012601840080891360310500d007500a292150341e8901e00d1040a0710022040d51180346c0c07034035801c48200480f0b40035014940c020026117103071800c018030165410550950141407040e0340f48110340a40101c030030f09680288407107040003944000040d02059090041003e41c00c2c01c01012aa04014841401040d00442c007485595a500d20f0045902e259040c444e000d6945c4072101d84400c1018400300e4080d522415907036881d4181400c0c25110820042c101d1485032078100110201075403502401c0c407122250382440e80d1101d0303e422004034038003a154011040303000c500302041703c0280b6414210b04401600781c003c00461160600120850034014260364118900160030300075800b0b000c02c220 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 740071807 1250 740070557 740070587
    0x3100c020304061215180c0815060714010e0f01060e070c021e03070b070201031b0819020405090c091206010b09041802060f041a0304080d1116051b090603030901 71
    0x41200014500b081708803035429489105130f084001c04c1c501045006000302c1031010000e1a100d44a400c0890315410000c211030101c1c0d1041100241010801c0746e080f8203d043c83c00001c0c001c00c407858500c40312a480e200344558101c000d51900c1c0c00460310254640145000f00c0443d5103a400c001c0940d801d111048024074291160708010388414680c50b5000c0200310090603540809988403c02da01c000341c15290070080b07111010410b090280c3d149603001403807650101803030200c84440d100084551000b841660400d85e0000601c504000b000f00e42e42004000502c001d07541188509201c07100d0545036502070190068900c0c04100c078186070f14281d000720b264180c40300050304074520710b40d000030510740c0441e004501010020404010028156552420071659044141e00c0c503c0c1c5a070303a00c40288102504890143c1e40c40f603080c0112203841c02607808200780c541d49034440d07610030308040355105031045015a01c1c2032603d5480c0b510742450a045402080c000d0010350601c09940019204040c0c489210 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 740073057 1250 740071807 740071811
    0x705010305091501140a0b0414011b050d0203300c0c0f0102040e04110d050309040c09170105160c1e11061303020901060e0108040b1017010203010503100c0203040612 73
    0x56840c03501c80002e004d000389120100742a2107000e000a0000c051034030340c410141c604007400208841c02040c1c505034940c11091911000c01c2e110382600442c64205004068120f1140d0802040c0f25500080103114054003442d182042c500010200c44080190b081020741004880c804900c01c1c60200c000340058255050560b4100c010101014cc220703041a800b0401c11036800c02030200f80513a848081e80c0c100705c26140300c0010360150701c80a81d00d108080c13402d801107590f07007090991584250034080280c4468009890b40000425145020741002c2e500351010801c0304130340a041a00034046a001164041414a04003170042c0051014268412040c4c4440d5417804080d0010394809004207010100090003c0070103040d40103110503a14143c0048050040342c68041c042070f0f8104042a60240c0d000d841c1c1d40b0135a84a82250b400e5500302d50005903641c1620802840016041d0003440c1079440a4040b150030300003030101c0205503681c1a014202503001000306001d038a10511b05083c0d601681400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 740074307 1250 740073057 740073073
    0x13020405301f0e01060f03080c010b04020f1306080712050405030f0c070e010803070c030f0c0e070c061b090605030709050307030c05010e010e060f070501090203010507111509070501030509 83
    0x1100b801c0c00c2680c0016201e11503920203103080c0300100d119150900d00b000b002008250b080072040a044030041c040a4505140403954454920003500a0116040701800030340d210b02c0c0720145682560000200d610441030302940228200e40714114007886068290748800d0108417070301205004003005881511907001c100504080c03031001100600d030b1014002c00a20f61071b41782203112000000182c001852030380040240c6400301c1c00c43c14201c000c3c1e1f50066607100720401e0601c1e240003810310379440b000d00200f1501c20864220b4021040342c1529000d081d044c428161a101d03404804801140d1201c0465584001031003140d1080c0c015641c4003500d81000041e107510303200080c1c40c010302d607401201c0e442000c81e010300840d44d00c070210081d003800a003001c00e12550b056000584078000c1d00d180c2c00d40b00f000420710500307021094000c6064a138000e8000c00070b90606003802400e007481c07220046024403070b181c1010108404d42c0c606902ca049080003800540c2c7c24000110040c004c0541040e04031301c0385d006c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 740075557 1250 740074307 740074399
    0x90f060d050f09250303050f0903010914101e0506180103120f0c2f06041d01120b010e0606040902030a0606020106080f03040e07050c0703030e13020405 67
    0x1051034092842560440920318100b004107150080007221204810141c40c242c480910a811144080c0c91341801c2c11f03600c42210b07210215140c02400304041d419030a1043e02c0043c0100005c83e066850882420b03a1a1011030521640c2075905103e840b004a5400039040b100c00e03c00741d0f00c01074219400501030b07001a100302c0c0721030035140000e0301300b540d80240c0c5441a03070850b500400600b007405040d0804040c240c615494100e0b1700d000d46da8613a003a40000c4003010a10600c02c00302449940b0f40141116105c64442c0d6071002c41405031f10300da44642001200204010304010440b4842943c41001c040c4660f003800526013042a002c0c1000ea0060b2050101055400e410300286101d203942e5440040e5a81c50800001c3c203541d43c035403115000e50080e801401150303034080200da0944121031180e041c55220207208449521640c1808800c40c00341c1003010007003560012150b8202c050131610300f000002c103105e4120881c0304e00d01c1802e520200140c1e1109407011002626038080d03401c40c03c071a48400d5846 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 740076807 1250 740075557 740075561
    0xc05030f1b0d0b0405010909051c02011b0e090105061204082d0a1d011218050111030a0c090b040909020d061503051903090513180b0a0e010b0303090f060d 68
    0x990b0501d00315071103090601c8242440c0c42880e0052410f040f0a1044002c3c94803940e4807a1b50010582c035450841300480c0c220306001350041d4800750f5200740f0f80000c030080203d00502c1c104810321228801c1c10b005000252929112042c1c0d00005c2181102e10f2050b242c03555004c01c40d92080441004404032420301e0402084050000b201c6541c0c000ca803a582d501408100a281d0390312130202c518189001e040f41111a41e101004041c0340c100e20f440040e00314110403403041c1d03007161000c00500541c2000804010f070200000650300601d4221400c1c00110318000d41980d06c0030245c0035803030000310140310400140690781c010820050000c0d000c20605401c5031a0310081d90414428034428000b00c40041040000400001002a18040d2000b810003c107503802014101c2c640f140511030b80d20106102c08981b282d40c4180a5501c1080420104c56030a2a20030403c0e10300711030b40d0340203501d4a0340440300301e2410300516081400003006186040200410006580f030340d40ba029806c03210034808030782ca00c000b40c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 740078057 1250 740076807 740076817
    0x2a031d1005160b0f160906020309010302090414090d17130f0f02040e0615030a020303090f031f1d0309030a030f090306050a200a0c0b04020612070c0c06030c05030f1b 73
    0x4a0a40300b02031400d80c5500d19040311817000901005200b49007040199400300a0311a481c2003440c0160381c03000d01d00c0005019000151b101c00012a4074000d00010142c00103562010031084d403241207507400c60080110040324115184c2200d01c2c0b5403810302000620107166041010300c2002d01c1d000880c80c81d00805c0440340c0d000c1d070300c015590020060080d001e80000852028030b00442c01845c0c1f43c03c03540d01181e01ea0044d04a814050280700007002d000c0c0d6030074044030009039020b55841c40050f04921210010302200880011030310b03034180346400703010004002c03542c250304c02030010042100b16a03022500960003918800410a41e8030380480040c0c05802241d00521042e0030110b40300502082c8101d12040c03080b0485840301f010040e03403d40603040f07a800d5080308c5e00800360100c256075500104005128502c4a6030216035100c04015541c1d42240380d64480318096442c586a9585a001c00e034101d40342040d04401040b01800007850340b108014207580c2c0801503500c0b001d400c0304c0c400d07507182d03082c2c00c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 740079307 1250 740078057 740078071
    0x19090504050106030b101a0a02030c0f031315081807050612100506030105090106050913020a0314010b0414120a0204060329070c0b072a031d1005160b 66
    0x541c101081030012195144c1d030040d086d8035100c40b2092030f04884000e030020028500390a00008100034511500900c1071729103c1c00844151640c0e1f1040071541501e0f80d0000304004a440d02152012607807581115480005206a441d940c1d1141c80e540843d24000058004c407081030702c2160340105080c0c507407001030f01d4920f00921041d5082d080480741c01031078498a0300018082c210074001003151747c0d5203884a03030450b800750400c1a51070740d40902003810b000d8600d40c269541400000c142a04d1941523011119030034848600e50b074166215810000f0314070540c442c3d501e40100114010005181030004d80010707401d540210b80030419154003103810f4494960050345c5241a400c000301c1485050180481c0d0b0195501d5016540c1c07421040103032500341400d20107085140040300260003103000f0304c580c0c2707005154020b0603c04078007034611244204803499400c60024417a00244104a0740010304000708550081c500848480c121604030b90341c0d00942c03c1255640400b20403a4013280c44141c0c0705008402d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 740080557 1250 740079307 740079311
    0xc052709271903020f01020906190207050a0f170609100b0a0e0a050f011401080f130506010801020901180f050d02031c0503161d271302090906090a02190905040501 72
    0x42c2d50030040e05200e04403401c100346074010044d00010b43e94110848815400303071420008644035441d002c034a48040c4da04400e801c01000a030100b180d40310201445c0448108011420307081c1d407000301403038403240d050303502c1401c0c2c0c0d00404c600048102c00390081e86d10003038041c200ca504c040d035a800c08100d845e0152051040e5036595411700c80320101d002103e0340909055020189190410b200081202100500b00344000320302c0f002180f1120681c9000c00c004a40103001c4554658492480c64000d42c000c070728650110310b0f101200c04410389032030801d0085a070801600103015141c030040c840c4001c2000c03000c99140c000c8142c03007071036002e25501e2110480d10981d03400c0d8403441c0202400c000c000c000f04a00c4103001030b10008203c580c0103162a14200102610381420b1891506849400f640c240038002c0c9640c05000300b00320540e402002008803a80c002c40303200045481d01c004061b1903140550313241c407094100500c1c074405403d00902c0f18241104d0030307156180e0186e81e801e07642d0407a181907400301c1c2c4a035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 740081807 1250 740080557 740080603
    0xd2d021c0507050d051c030f020705100507030b030c091f120219080607030903050405030d12061703070b07050720120105090a11030f010c05270927 65
    0x6002c00c03041000d054281c1d18400d101c891034440d2036880c000060502c1409200c0c09401100520a40010760440b540180070b41d181d158515081c0e80303502e102c40c207a41a05107400000b4059500c00c0c080c21f14040d201a0103088a50b00490a002c4800001009611070070403420301c0c5801e0650801d1004001c02e00340001c01c898132103a20401c04100340c01c4000d03100904000ba0140424000840c405400c41201c0c01c000403840300d80c1c82d0555150065901c06585809401c1c03072280500c3e000011a040501e490404002e41501d03074050b096040c969248485040d48288040c20005102a440c903030821190704002c0c1c1030034495500c0040c0561748420703080d00d07441120704070a2a0308000006900c2c200c0100c0c001e12042c584002015078618958002a0107050101502e05041d1401c1c8400164205c00300d00034001201c007400050480e50150788019008075100b610142c00f41b03408001d0700110000102201c103e501e80050b9000c0c01c104103a4447c441602280d080e100883c0204003623201d0103148102c4a1001d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 740083057 1250 740081807 740081813
    0x21090a030e010507030516020f040501080d2607053402130c021c03020c012d0209030303040303110c0601150f02070b041203210b0f0d2d021c 62
    0x60520780102030512005004440c0040e820005035001c84414200200c500c1c007840c00000d8a2441e0360680d00d030018581000441c05000105441d24080e03869210b08081103103199110b1351820240220b00c18070780000022580281c446c000904100034401140c0440e10150f042514184050959120b494900542002c0031400c03d0805826403610b0413a08000032040d00c070000e5180c030445400492800c0310210b89090031800382d07041d82c000340490402040701d040da842e0b80b000952081240c1000c109540003004014088030700890340076040140155003151503658065014003281000354040e03060601003244402d60402c5000c2c001c020011002d4a4400c2c10071019141c07240700c09010307086421040381071040001400c215011502c401c5500c1e02c1c03c002c0d03030500705c03810b0243e028003c8070103925201c80075003654207412001c10040e04540074245403685408000309042940f000401d20b4071001c0c40d00d516170711031070202c0c0d505148040e99560100019400582455003602c014400d00112070584024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 740084307 1250 740083057 740083067
    0x618150c0e061207080a02120f0103020109080a03021207020f0303030709180905212106010815030d1d0d060203011d01180510030c0305010915110f21090a03 69
    0x4000000d4441c0c51602010b64030651203d403004203490180002507010a0840045504407408613400d0ba4a02c1d0103810541c8109004800a10050780066400b05011a078260b010401c00201a07258000741405450941840040e800812090364401000c4121641c240c40c01d10086120f0341465403107a640d00d0034140380040c006054070041d0017141c9020035203400a4800141e45117007800920f5020b082029541c802748980c07041c074044003602e052900c1c806905421240e04280a4002600d540d862980d804209138400a06d00d41a154598031401c5150300c024060f0711a1400c00445400841d0540c001c0030101c0d000c460801c80407116507034008010407011010180c082c1c59600c80c0d0381c100d82c081d4541400c3c0c20081400c050300c0b140c00742d650760200e030400c15015021001903074004180e10015650741451402400348070400c4d10041071107001001200500d11600c141101400c14050410f00a81150030094114610040c9020200702e4420541c0d407090790700c2845101e125009150503041c078900182 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 740085557 1250 740084307 740084327
    0x70506120f01450c09150c0309060c05070f1503181119050d0602030403110d12021c021b0d142b050f090106060203030c03040618150c 59
    0x1400d9440c43e0711400001c49003400382050f000080b2145148140344001c101c02c500c58940b4240c5240c0e14050b1661401500700d1039a0b41112080c05e00780c40c101d0b250000c141d514055100c4002c0c001021b10344d0901559000350b451182d0365002e20211400c40e03450300b00c981c28003000d40d0040400440814021000e981c0c1c14040d140b41402c032014251007a801e03e90380d0007161201200d40d940700d000010b400c0b04017429480e13281c40060030300034000350350090036050590007540240c03021790018404050394148610b0015100c080e407519903840415503c01d0900d400700a400620000105101c81300714002079404500140070b080d100070180c0005544d80009803841c201032441480140180f42c0384003e5a0800706007610740446410340001520f0312403603624100b600d580444610f01a1a2100b031018031448002428454240c14000704111a01c0d6001a40c0d41c3c001101d4007882c01100b0000200080c59540218401c0d4000d40c80c254940312896031158120340303051030803091855030b0f4680d60b480154021614a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 740086807 1250 740085557 740085569
    0x11032106151c090f0f0f210e1203070611040e071110020a14070c0f060c020319060603020a0b180a150e0f0a030b01090e03031611070506120f01 63
    0x10b441c1694034506408450110312882400960740e40b5218240a5040e61100c4207581c030040385400030009140020a0403542c60054440b44401031844803041035030450102e10a2880d220102510170701d4080011986412020114070700050104200260050044c0d0001007004028642c6503800c00302c1100c0b1101008100d01c007049200c1d50640819940450a000a4185040c0c05a43e030f501c1c585003514085401c2040081d520310004650041c0481c041d6450103540d40c02c420f1410269580e502180c13844a4030070f002c0c2d4540c000d5501494110341d4018011141803040c1000b04207507549800140e07030140503900a8000d2400059075052003440c20703030854014002100c030402c581e070070901200c81e40d91400d00d840c418840741d07c05e07819840d03031040d00803182d14000800c0c001d155030b2603161400b0384030390038881d480300d140c00c0500100d44020b000c01034900ca403030329162100c003034880b4a1040720091442100d18280b4010014045241c0d21414000c01001000300000901400c260741d003c003400d03005920003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 740088057 1250 740086807 740086849
    0xe0102071a100e07120b12072c04050f070518010905040c050301061203021908120c12040b160f081b091201090b0a02090901050111032106 61
    0x4400291a1241c0300982120404207001e107079642d4980819071041542000010812810410041c076600450f0541100d84030503061018030200414040310380c0058291011503040700c04248405c18000906e00344d001c101001c81045000b003160b10450341281502d094445402004001c4802082005280c0c01441e0544100711050071145440780c2148041c05080120350301c8001240034401c2c1c9145072000b4050007402040369a07a90504984440c0d0f00010490140c043c1c80380d000b41c500c4590343c0c8070084c245c00914061400c4a0407040e0785160f1401071142c0e108281c01e1100c03a59000040e210b25214510030110300d505407c080d1109506400061007100c10014030503088804c95610510381504081020400360903220580017100b400c0c01010300454104c010030150500c0000705420542d4060b004000e003c0e00c0d61900007908045e803081c4512541c00500c850010016540314000503001e0a11010a0743d00300250310740309000080d02624540316441c0300c00141b180d03500e000a01040011004000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 740089307 1250 740088057 740088067
    0x708181503150904020103150b0c010606020312011203120c0302180609031f06050d0c090b0108071707052514030c100908090a0f0608060f090f06040b150705010e0102 73
    0x41500c42c030407414001030041c2100c40c003080c00c40e402500b14603135076581c0d03081c50b0403081e031224005011904491200e01044d802c140380022040c1c000b0003111500c400031001310000703a00f008040380035510322010490400404000803003195505115546080180c1d0b41c2c09030741d9000c10310383d40100654903d00c080c031070700d01040751070300d25a0006002030024810001404002c610b0703002500c020a095404a0b402558a26000c82080b0381611400d0a8502101c0b0030003592140100443c1c00c400c04541010200d819a200b001c0680501c0c00c446a00401c1c5292152800400402c3c0718000c0600132500007560701030024517010000308000034084590142c0041d402e0191101c80709645a1241a0700d60001ea070368280c400178810050125106502d029243c000d5255643e0440e00a42025215510028200c03a021400d80d10b04030ba00e003142e0003c020504921030311664400f04848601506442e801640c65010180d2600d680c0c00c201c40070f4452501040c3c0703513203541c20003e09446040040000306c1e441001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 740090557 1250 740089307 740089321
    0x50333010b04052b0b1512010207140105040c090e031b030901020d080c1b0304091104090501050a03031202130f060f090f0b0703120b0d2a03080a050c030708181503 72
    0x1c9413480360401c80c121040d4480500b54801680a003542c40e4000300c041c281c80d4021581500200300d0b45104036006c10300094200849401c0369030680e002040340c2c040c1d0201300a41400d039041501e1120307145050320302c0c2103216048101d5644590110744d84513000802c1c42c0590f9a0103000d9031745000110b0034014020b190210074100c5501c070305152005076410305a410001c280b0704200b0b0f50301600010404005988189119190300e401a10174020380c10300b001c8c0085264241040940200c0c1d0307040d19100500f941081006000e500a103c0981c05105407000000744115244007120042c0302d1515501d001400c04600208207402e10b400c8401c4034940b00c941002814074440403102e42e00d4041c33800c42a415850700e40d440143c40c00b08003195000441d50308003014081e0385039646603a0207001808088441c10040c084070030500911014180b44000d20910f00700d907001d4002008480d400e1000e40b850016255100c2d0050b070004102c001e141d0350120400c441e01c0c200500100310001070310103032034103605c0c0c001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 740091807 1250 740090557 740090629
    0xc10080703152105010204080303070305010512030708310603150608060a090b030a0c080705040c1d011d0904120206061507030f0e0d06090308060604050333010b0405 73
    0x16100ba41a00103008510f81800020f41c10f5502410f8040c050f00d41da07040400000703015010a025071485911280450102a4000012150246d502100581c18000c640722401d1100042540d01410740359203480082c5503000c0c00060102501c2551000a4100110800010034610ba84c000c2800d101034101401b856988d00103005040b510818400308003141200c0c04607040810300b48006048003d20040440c59250101e400020340b4002d4808000400c40640e08980070986004c94003c80c82080a130420345512550240e900d0341c2c100d82c80814034004003404102e00d050222010b4802c0d100408080324140c1e81804941d0b0020700031100099180c3c2c210b140d5050300c0c4038030140102440440c12141c4a12030194459031802a4010281c048128460a0039005400154012030014209400040d2189440700c288c41c1a5000039005044402842050901e0302200540e40b4140000701e5040400c25a023480c1d403a406440b14005003601c661614050004c0702c0c0d88000e1104414a100ea1402d080040745 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 740093057 1250 740091807 740091839
    0x13050c0a0608162f16060e10022107050c01180e100f0303080405010c0815210d1701051008070302070c0e01140f04050601080403050c0c1008070315 65
    0x3110a4000d50042c26905a508030188422107050584000204140c0380300c040c1110516100001070b80d0160170405004001e4841c0742c058400820504101034203581044c48040c0c243d00c40303038012070b045a54505044001c0e42c92040e044612250000f0b000c2c010000180400c1840b6202820000e010040004030071540b408940a0101c42c01c0c6602e0018041350307000c09014000b0b22000041c190000d03181c0c2070080141804480a407519820141004d10151246000034860030f03200382e41242c0d00303020b0020011200110076021012000c030125500040005101101000da020b844288198880c1c9100102082c0141c0c001d42c403541503102c0c0009203503080448158099003500c0e0040e522807542c82e003000c0301603d60b0040380504044000105110000c41ca11a142230000c803440104a50b03c40100816a04121000c80c0060983c4000c034000034010405411320302c80310002e0b00c260803c00404a515440c203408007000050034102845801901849940c5450b20400104500a070034881c80b4000c94a01c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 740094307 1250 740093057 740093071
    0x3060c0405120705030a120e06070b01030302250b0703021f0608060711031204210504050102010e07151b0602030405030d0e010c021f0603140606030d1b0201210513050c0a0608 77
    0x103074107c0320300c01910443c1800c25600006100946924290030204100c003000d000c1180035115404020f4030000701900e17800312041080485444050900000501d1500142d10481c250b11402d044040354006d40d508902b8212048030b0001003043ca0100054a0000060008001d02c41102c0c0c0d4130381c82010220490b252412a484503c00c640c5407440d05910082c6181c00d14994451040c1480480951000c010700481c1c1c0c00341c0c000e003d000c0101c01155118000c42c420003055412030a803581c03800340541c20040d03500c5c3e07101c3c011070b038101580d46400059a10442d8100d0383c90700002102501d00c08544140480c4a0f410f20007044426202200079585d85072405501c641910034441c1c45888201c1d9030000d5001d50740c8481c001c1343d05ca51080840b56a2881075512520a0080c0e40703203107003054864044280450314240205c065140c55400645940a5419000c0c44081034080304410030445409020b01640c10003004140b600031a0a1490420840384c218a00c218030b480810010140d015550f6600b00103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 740095557 1250 740094307 740094323
    0x20907050a0c1106120a0e061e1b0c031201060f05070210030e01020c07140f010201051b070303090b040f0b0901020c0706050f04150f120b0604090e0c03060c0405120705030a 76
    0x8000b0000505a0189070003401205c80034404004250031075070030000c0d8802c041001c03584c4945400c4e5005d48180d10300000d041da00740743c070700c00503d07030f2083c40080c600e0081981c280c4030715000c400100075095601c403210803400311a400f0010010140d2000c1c3c1600d030242e140c43d0160400e489940064246021107210004040d02c1c6c18505100d86000e60450702650100821640c41c3d42ea10710340107414234010340c13407107100360f0255055002c1540180640c0d44100f1482c00c00340000e011290f41c2c0c40c107c0e000b5000039400c255030307600c006001603280c1b84014011805400240c58403080c40c079014546501c0104840c0b000e9005005c0c040a03030100080007402d0340c41e542809512001e2850300700041e40125400360251041000c140c81c071940e0449114041d001050313607049400104156180151181c055100f904040104810048191107904c0011608641c5007990102c140e04400030307260410980e03034203420755070010701000341d440c0030b50300b800900460f4000307003241300d107400002074030b809101e00c01404003c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 740096807 1250 740095557 740095583
    0x10e010309051513021e0105090d03090816150215011424120708060306190f0f0e071202131d031920060613110d09020907050a0c 57
    0x180c144034070038140c00c05411245613481c00d10402180d214130b1180990080c404220104079001c1240c80c0b03d0710300081a143c41e4646502041407201e0300b030701e05105800f004450240416121018401c151200c0d00ca20300011006013405180da245010480e580b1040d58000441e6460309940590000c0c1190080c503681d078041c1c2e50100201d48801f482004251402882c51600c0c4400102140070340712a0310440028001561618002d8442030f00540f400d0f6410303030100f07001464070916421082c40840750002e001c41c0c9007020008800940d10945488041c0c203840f440c14681c004410000c0c94014420380251412508003a008203101e40c0f4246400c000c4a5214940603002050354070100310900e11074011240c0e00c6903d000c0a00003006941c1544002442e08185405c50309502203032440e650fa10035015090b251260001c018458000b040c1c00034040d6151000e10104202100140240081032031011451420602c10032922a10040118042c041c082c400280c000c0c0d803284004141d185d00000c0c1d41102 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 740098057 1250 740096807 740096813
    0x61d0a030314091f023007060f140105150f0f09040b060c0606040f05190510080a03020c04050c030c030106030905031201032102120d050a060f0f030309090b010e010309 74
    0x502c994080c442c1c0004c005010440d01d0105440e08042c4211581e080e550425150042c0e4225484d044040120508507611444801c00c480d070001c1181d40e205502c00141c0500c030884003415142d6151401e4000000400100000d0805194802207651074001c0030b4030f001d00080301c0c20128000c0e05a070001c00040403a50210589482e444840c0c80c10000304001d0301c370500030900940d960b200b111010301541c01c0148101c0741009500a0500880705003c0c070b055050043c2c2d62070002004024480c8624848d40348000407a4403083c00a08040c50095000d49032000f07a20051000f0790310050000c62400408000f088a03505018054034151040f80c075003c9801d24445c288545503014812200707440f86d251000000401c192007901101a07855080d04118a4100110513a2242c3c280da0f1181c408006c10840e00d4002c0001c1c4d0300190b880510100d000030019291050b01404070b420343c000710069842143c0c00d10906411500c03400080061036820301c10000c901000801c00092040038a0625448031302c15020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 740099307 1250 740098057 740098097
    0x51c020d03110d1401061b080d0c180b0706050603071d070203040905150f031c05070204020f0d1d012309030c0d0216060315150507050604030306061d0a0303 69
    0x69962400018040a0304c61200c1c81a481400e10031000070039494139894400d00f842400d40300025420a520074144003010501d10003030a010f081210030002134407158000c003062620310801600c090b04251340c0300c81c0589001003c0b640090195032295104e44e40c1004002803828009511100392281c036112619003e03001c1c0d15500458010351804d50070402048600c1c0a107460b00d00903607100b1030300424010281c000b0b26482e00e002941507284200301d051880030140c01f9200a014a0703101400040ca4148000c0c400e1100e9000708468142c030a88403428610943d22402d01d0481491105000300301c0d0500070340070000e040441044c05008403014100064844006106a1306451696400c3d10b038103241c080300c001e49501c000b01c02c18066811080c40881c40d40c2c0701e48508846c0c2f907524100925243c0c100440d080d038012000001d0b00c01c104c004c10200c4000340050101c10b001d41e04c00d44002c0345c0b450a1402c050034141d24150042c068070003d1a420b102075544014480031290541002000318035007049803d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 740100557 1250 740099307 740099317
    0x4060e030d06150e09101a09060c060a060e01080d120b300d08010b130308041202090a180f11101e0c05030f1c050c0304051c020d0311 59
    0x541c2460010700140a4400c1c0c1010710b420f007010368901114200e16410020b00b41c0c000d0740c0c88402c0c040410b41c24402c01480302c050740040c101d410741c42e03820014103400003078041d17102402d040c0d0783d0341040c001d000304145240904006041c82507480c0403190b04180c1c25a588065840c5403000300320b045102245800c007541d000400c07040c0007500c01c00e8283c224010b000000405000c040c18080303071078044882560320104400c40c40d5007041d501c01c41282d2070041d00b888a40c025444128a0701e03d8054000700268ac0c03440107000034280700d20300c92110103141c0100881801c005011548031424103107100c403090000541007490a520104c0220b50611605241d2942c2202c0e204180c0c01181c1c51102003601c540280940c6444414103045000c600c1e54410700b2100c0d2169000001e005a209000c981000c1f01c0113409421710100c81d00d4200c4041001090132400c2d1001135949103006540081440305101050220130005111800c48a1341030240910007903850a1854895080683d100320000200f00c0c48011a8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 740101807 1250 740100557 740100577
    0x10e0c10051305060f0c060601110a020d05030c0304120606291c2c010c080414010b0423130309090c120e0105010518091216021e13020403050604060e03 67
    0x91713124000500d0311000c4d40e0000c00381010b248142c1001801d076600c80c003541c9007002d0f814000f0b041e41414980c2403017010710b914903048949002c1480240c004020030405480185501180111210034509128003126000c2d0468031200d075288107200041030401e03d00e084d07212400d0b046941d85103000200f1030048042c6140225403141440200d141001c1c044200d1204c13080c02103104c030034000040610a00321543c004540300070138200c2001401203054a811481170001c0f4074004078400d102d10002070100c5000b000c00084c0a903801c0460560301c4600d5291540c0507086200c0107148001d01e840140a03400d0520540704c0442e02d41c1101a9903600c0740307010000607903540c6410300c50844d68072f01d4039020b40824010749019100c103070190002003202c603500900a1a500000e08490fa14001182e4207035400103400c0701303c2d401000d216800584481038200780f11041204410034420080041111291180fa0201c065900601c02800810340200d4880d410a03840803000805110b209003060a41c01148840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 740103057 1250 740101807 740101819
    0x41703130b090f0a030b0a020306031e030310170a0212010207080d1b020d0f230c010c030f0905030904020a090b16030e150304030c2f03010e0c10051305 67
    0x5100d40407030015010740c8404603407429040c0465001c2c030031622000e01c00500316120601c00704160761000c1d4000e580048001d015142c0c40480d013040c60340e541080c11880780003980004100290305450300b5000000c1c155505070300d501c0e80c0c05038481695542d41d812029101d400040031002801e4030950444000baa40309841e41c7d00c541e00c44030340400400e591071103101d980410365441d1241c070b031000c18405040106501d0301030700d40c92800300841d8601c074042d5507220300c52052031801e2042c602c0e03030002d0070070300c1e0001c00041110350110100030196103424180b240080e0810100000152011055500b5200e042d40c00584907650050200c0c2c1a80141d80441140c0d02d0003d011800e1241c40c0030f191000901070789885e8600800a0140400101d0b074810110300300d841800400d000a200d040c40c003003030600440c0405a000e03280e8018078002204041803071640318030303108070401c1c03801c00b030113140360034849903000d00a5100c1d501d004c07072001900b140e8030004100c00006e004021003400b0101c080945000307440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 740104307 1250 740103057 740103059
    0x1b031e011e0204051005160b0a180609020a290708090603040c030c1d1303140c0d08011202090c0a090f0e04030201141b070201030e03340804170313 65
    0x6841c00941c0140100c5000340d40d8009602c1c03449004204860141ca15100180c940c280303d501c0b0300c1006c100c0a0100c4c10044c0d09c51583c070901007042d58070342c2d81042c060320000500b0030350f502c104544e0040c81c1c3d01070404090442600c03504103a00c40c82c20300d80088034051030740d6150414030346103000f4440d005c02e05520110100500043c441e00025250583e4410803040d202d8030389900c03860320442c144c410551105408600050109002e0440c1c0b40201c1f03210b402c0c400c00d814005500f40c8103541002e041c11100380e1040c650440030700d070b010007614010f20f110790003000c800c1340075004181c00344802440c40000c8540000c410521900c00d84010707000b45070703000c8045101a161510320f028503005540030350066003000d4040b10442248040c0c6030190500d410b202d0403c1310034041040040d04000d038241c1c10315603038802180e00d59800b8070003014080100d0706442104003086070300c6013205420011741a51050160035a9001034401d10485013641c800301d0400a0200c6940c1d0030f00d20f948102d40e1352901212510300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 740105557 1250 740104307 740104361
    0xf11070b2a1b030601060e0604030305091807080a0c030b060901030905070b070305190e0109090b01121104090608031303110d02190612020a090e041a09060106021b031e01 75
    0x486030700900700031001e440c0d403031b42d0b5400110383c0696280c0e0f40c941d009508020400009002d00004c01c1442c1010f400c81e41d055118110419460383e003240c000000c0b42074902000110001e6100c1e03117103d0b07201f03410100460034480003c00c85c030380200ea01c7e00e0305155680e00c00d60140001004680000e000c407412142c0c1e541c800340340c020000d41107120300d0030580c9640d80341400001e001c1e81c610310910394181d440f240d0461400d1141c002605c41d200d000b038144041416038805085c16030041078001641441c03100da075185000100022104658089a100d401c28400203071001e0460b050041101d410485440b01c02040c640003c0102815001c0291300c4101300407007080c000e0203683c50034212246500c482c4074034658202d8003030603845407da01d0b400044034060140400024410304a0701702e401401035aa140d0089681d82090700002e8482164682c885070040040c250b040240c014054800d0b00d4501c0c51392703e041e020a54401807546400e040d24440c507401251000254440300282075203280440d41040000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 740106807 1250 740105557 740105593
    0x62b0213090608030a031104050411120a110d0e011826030106140f07120801090b0a0312080a0b0415080c090103050c012d0f11070b2a 59
    0x300c60240800000d08002445144501c1220120340000020314a840361018044008101418940d000c8403002d100c00b154075101c3e807048083e500031106a0a540e40000004034400c0140100f803800c00509248003082c5081c40041907402a10030f9107408504501a5400305016003024495000c440002e12280000d00010540014107035640385003140e44054103454120952109000e008081070340e02c0261200241c030240104402065214824244046c0b95651440031800c1d0740e001c0d0000e030091005000c606240d10500c0c1c0c00358411140030400d04d240da510b408005034081100310610080c6000a07604a069400c00080d20000a1003040b140a040300d00d10401440c50180908510444d21415a0307400d00c08440da040e01d421000130100c503624007004407100116001780a074209401e02c622002030000c2c1c1c040e00803000c607545488001c04000c00d0020403050070b9448458050340140b42c02c02c280c41d868012141440c5240d005e841c0c0000806001a550301c06141c0290090702c5110300c0740c1040b544d08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 740107913 1106 740106807 740106817
    0x1e030b010219021909050f0c0711040209041805071502060903030610090801020a03021c0902010801051e271006080106050703121d1614062b02 63
    0xf80b048600392a00c0c0764441707003089403500b081c007041d942007406066020021601d60f60520b0050b458151000031224200382c00740e540095800d0480c0c0f120b030000e00c400c1202c015103003064016860721594981c03040c46502d091030140d100c02203c551020491500034851079000314210388421082048030461400f811051107501807000682040a0010b402c00202c0c50f14010b031110710584000e01c83c445c0c400b01c16000fa600e09059000181e81003054281920400e4540794008886e030f500c5034503046410b101c2264004004d4001009400f064080354400900c03000009109480b0100c2c2941d06940a00410003c9400c07a001801000d201d00f001c0d000340c038001d191030004104412440d10131122aa0001560041662821401c1c0d002c108814010807014403228861076140c0509035003520744801c01c00348a8040050300f00130550328140228809d001161600c048103003445d00b000029486 = true := by decide +kernel

theorem cover : BRFrame.Cov 739928057 740107913 := by
  have h0 := BRFrame.cov_init 739928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 739928057 ≤ n) (h2 : n < 740107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
