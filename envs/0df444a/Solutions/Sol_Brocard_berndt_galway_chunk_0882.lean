-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0882
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:25:44.325311+00:00
-- url     : https://prove2.me/submissions/19b1341d-95eb-490d-9af2-27894ff9d24b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 158453237 ≤ n < 158633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 158454487 1250 158453237 158453249
    0x9090c0302030f150a0c08391b070b121f060201150e090c0f0d0204020f03010f0b0a091a0408030a0207050a052e03060e040807120507030c1211010204 66
    0x1300080550504c0071802d44c0c081c1500304500e0600280820458204990301d034000d461803031640440a80901490445003c1c0941e48440a443c098040110640714010806a04071024000429000d0000c443d40c801180c0300e08401007005102d501145030052004582080340d144040d84082e42d8000360080001c1c1d10b80c03003100580c0d035070b000c044494400e6a802c18028111085444102e1503c0c3d215662101c0a6480b0b043c41220781c070741c0105080c1d494900c25080a0340103401113449000f01065000c1035030080c01801c21070b4402c580005000c01c1178034111451820315940d05038002d13140c800302c880c1404809010420003c418000896021303800c0002c2c2207442c445038001c210343d604d40f60a0000000707841e003005006881103900340b85d26280c010144a4030034002c1184601d02070b91810104c009022580101e250a00030206100521074054050911079025070785954140811403001d07600c41c845c4070801004281c40d1800039003c01e60b034080240d904407150502000c3c0c2881149540e089074001c0e0456 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 158455737 1250 158454487 158454493
    0x2040b030d1701060903030c02042c030705071e0e06032404020a08120f1c06320a030206030a0b090a0c020c06040305030f03090109080304121805090109090c0302030f 73
    0x200c642d01c0019108900510060400800b00d500b103132002840100700f01c90103405943c030b50b503a8459100880a10b44030410381041100043c004c1003440d10b4590380100000c0e240340c440c0010206401d080c2060120410b4441140e560302c4d1803400005440c00180142402c1c0d141c0166030702844501d040300181c00f80201c0e00950a0380b1803400b0f10421501400b0f0b50441d8000f41c0c80032440c060f0403c80036040307605900e21900a55194004020a0782840c101ca400001406041c41000100c042a19209030840502c03c0f00c180308898a5803444510401074066256112145500400240c1800401190002140500071170000d400ea40420002c58040e210804400d90304c1c00c3c84550180c4c10701c10510a0602140d5840c03600d0714503114956240500c029034070030b40030000003040c0ca1900940c8018250b96018011940320b2500d4145410b03a84107240340c01e4003288804007404001401c1c0e0000c0c1c1c003a2540146600c147d80d003480310000091401c85011616203101c000c000c00980d5040004110070310400000f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 158456987 1250 158455737 158455757
    0x150105161b0311120a02130e0a021503090d08041e02031908130e15040b030304180c030e0c01170619230d0b010e04030c12030e07140a1202040b030d 65
    0x10f108504e00015031100d407070341001088000580c0c80a045664021210402103140050040b201e4181b414409000303500440304044240041807590280d84902c1036541039500c0b128008000b41d4000c042181e000f13042d00318040180e69000d403100031062185001500301e52040c2000e00e0b240c10700c40f41d0071405590400001c075044611054034070404010313194000c441c804a0800c1c00515032844050f4003c60311441c0c89610880039920100156401424044c06519005c680d40700880c0041814034502c400080c1031401c2d91103d0440060300e0407200f241a59911405100d0884140c490350003c1c0100d540719401d04407410054480b1000c00b805400d01d50344000703100071500d100305180507401d4601c60107500040c10307a07808038004003a49811103210a5070222180d655241c2140e0018021a004008010603250304558992542c0081c00204052007143d48a40c0c1354542c3c909246281040c1d5984480203100034000a6018191101142d10242c07004c10181c3c45040064144034003500607000240388082c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 158458237 1250 158456987 158456989
    0x21010e0705090108070b03180c100305090d050a0c1101030b030709020309061f0e040f06020d050708010e1909060e030c030d0f0213050103020703091a0a08150105161b0311 75
    0x101450041004c10028503046291045031041070000801c8514a4245040a6807922005020011100100030881d840820b229240070b0003c05090b20600502d1040584004001c0e010300304940c0140c0051311209007840282d66000e0a140103000f89504243d101e8643c03101c252000c000d01806000460380250304c030b20700464a0b40c03a180f0002c00344015030000d1100818800b0303140b581c150030384210ba0b001039483c0d5614142651007040514005146a00c002848900302042c0e522041c00340210390380324036260341d860009107026603040d1143c1c00300c184520000b0845011035404124201d00c00c1c00041649005081c0581c15074000001c2418150000100714500110b140300d050140c1c0310400d000c600700210500d1000d0991098081c2d14145070b0f000440c00c0130b250294101e4001071111110011030341020702c5442c2c1c00e50b04600d4036500801d00355004511801444008400408010b03550b45090a01440101203d200385040944208030100044091480c11440040296014070224001049404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 158459487 1250 158458237 158458249
    0x8010b0402030106050a0807050918090d0f020c0f0d050f010e0f01020412030806040f0e030a18030b0c03130c2903060a0504051504020721090b0921010e0705 69
    0x8499a10032441000184440c03500842a01c03100d0780e00b89071608240d6121801942c2900c01c10303a40380c4d4880c1d080402c6401482e12464814400c440c0300e01525a10854004255400701ea804440ca001da006031003660503c0c2040e4a200d481c00d00021711340550f407070960303c84a04080400d0f52111060351500c10510030f4880401ca401c2400000500071881d040c40d18040b140c081d600c0140007820000da010220711590303120781000540004101080180d85510700e11280d5a0f81308400002c0401e40520f00103000040912101c0b04a030340140084a0a55901c822008030303520081100c2015070310840d12030042006100341001809148003c170a103144003a030b040035000e0002d105c0c1d00d40070404100700025602c5100d003c10803a0030546000c541c944554824644c60b101d40d00344181c2140c404111102806400c0140515402003031160988190403158200e0b542c562901542c10b20090070044c074141ca00f803142e8a00391402140401c100040301140c42142036940564450429a0010400380014608031f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 158460737 1250 158459487 158459501
    0x5010608060403050d0c2d080a02070803150411030717330102030c03070c0906090b100c0804030209010b12090613030c0501110a0914100c06090501110406090801 71
    0x80c600030441854030b580d0003049849141e840c251415120814002c1d50341c01100e010780ba202d02c03000f107450f044c100003640403503410070280850001100c1e103010a094a01034804c4130b044a400c54201c03441c69841020070003031640803c80b100e80066440b46160f0104c4072100240d80104110740d10704500244013019407180b800040c04951050308110707540e00300c03028010500010400b00d40302c503221100c20040144d003140208110b60007180400034200d000c000d4000d040c0c02c00d4a400c04800c200c1da944400582e000c0312100a40c003504408198080b107503560003000c0150b44903210701c24184c505500e030b07808510180802c2e40848154640032039807503640200e4244040d4850340d03480042c00c642c6089100703403407412441c5802409204440301c410043c0142900200310385041150200c0c0d440d0554400141043c00520403458a0984502c900300d191801c04403138803603d10a1341d22510041e981e42ca90b1402001d82d028226a075641c0e44800e2500c3c0b91030301c40904028061070704c07511880c03881c0204036802c0da83c1f1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 158461987 1250 158460737 158460749
    0xf060809010b0a03020108100308040915080c031203040f120801091407080c09060f031006140906070206031f0e060307060212040e1f03110f2e0504031707050106 71
    0x5041c1404001d0f1560b0f03403410100ca409103450b003840c0e01c40060307691440009030000741c4000400103000c0b5031401d0710f400004c80b0200c040c40c2480101d540d48251500c801d0114041b41d03060300101c0150703c4801d16140a140c2103401080b5644800c045941c0e580310402102490101140c8240c004005e401800e102d80034801c043d06009944a00d44408000d048901c000e10481c40250045100256901d501e402c4d2180030b00c0c0e6540d8241e80f030505038149403000c410380c0318020000d03040740140e00411442c0d40175580384085c09052103007000595420480560001040e000d15a1900c050726010380807a002d0f4840203142c0324080c1c0c01281072800904d4140702990b0402c4041d50301069000741e040d50312070700b00e500300c804e940380358001c544502e1200c90440d0042040003d04021400002c01840010f44107000c0494040341e14415041001080c041140ca03818041d94a006080d600e0036020a548172503807041d0b0145180651074103442c2c1d9580805466443c200220401002c600c40c010000c09110740006814 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 158463237 1250 158461987 158461991
    0x140c03191e0c060f0e07050907050705060f010509100602030d0c0e03010906050f1006080c030a0905060c09010207151d01030b03010f05090c0607050616091a0a081506090d0503040306060f06080901 86
    0x141a4943c246e40743d0051203860301034101c0100044246200d4415161b1195211054403030703600b030011440c0d442c0d46c0e0070b01540b84104c000c41c000c02c445c0d82c801129141115140d4010b94104130091050400406401c0b42c00340502070000c400c000302c2d507820312850580a102d001e00003054101607040e006004001413800000303d6900d2024001e15800c040340d0b0764004403240a05503039544070380408000c1d1074001e5000380703648505801d0117a0760460f134000e8041a80203070300b146c840a03a18060b40e01c00c0ca280794217032170200b0141000c45401307102d4148050701c0450181401b1a000e41d01c040401d0841c2c0c110b54410105680d544180311550304203025510400108542e41801c1505540360180c9820000c0c0c8900400c0094480e40f26030b0600409001d40284408031036401c603c40d21a103000c0860744804c2100b400140701d20009043c034034500703021051300c1001402d014204400d100c140038110030000f03000e480700d21042c4030000c0001c1d9180201d401401c0c0039074801000901d000b9014000640c05050b80009034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 158464487 1250 158463237 158463251
    0x9060d021e040819060b03010608030406081005010f080a090c0909060605060a0e011107030b0a09050c0d0c06030c1101050702070509010f0e04020d11091501140c03191e0c060f 77
    0x200c0b0000f90181340c112018042c0c4a0101c503850040b00925070b40c04c802d609542801d00004400d500800035004454054032074090590302c503240b40c0b401c60040d00600c0c1c0407030340143d82d40d02d10038441c912865002150b00340000360f1203040d46840e20b1080b82d40e03002c41c0c0100d80b541405001c0150a001c0c8000520060303540d94200000d180e0090305040c0c6012440d410060041c18400d48014200112401140c1054400681e42070802000000d0081000c081c1c0e00c0e4400c1c050030100908181c140c1610741e03504040c000000c0d03800e041049002d03001016550081180c1c001030b90044110078424180112590b030010080a460201804440304050348485c00c1d40c0f0f005a0b0401250350021615544590b0444030384900342c0c514640703180040c0003498440e8000c68081c2c00c02040c580c0d221620307040d0030801d1300c800525024240714210701c0d118892030381e01c542d00140152000410410b040740c0d02e4239498100b445103002d1020412511070910b0400c000012365140305141400640d00c10400c01115a01d0244000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 158465737 1250 158464487 158464499
    0xf150503010308040905060a09050106170112031e02010221090607110307060b01090305100902040f1a0d030201060302060705070e01060c03052713050a05010801050402090a05040809060d021e04 85
    0xf034003c81c411410300c41d8984000900c3c0703a4441c114400584003a46040042d0351311664002c08030440e80e01030005403102078001107210303841c0320710030110164540e540703070101c111204000c1d80000400030b0302d209643d001e2000c400075080704403000500c0b103000713003112b045443c01c29005071801501a09850038082464000383c0c82850100841e070500d900500301007050040340c80100d41c010302a43c0b01401c0303400b034110312485071481500040318482c001c44042c0183d07500c42042404442c070400a00d200c40e182240c07686120304250a5074601c2c4c40c00b90000184840d500e8012030b000d580408030468007a0400013040c41888080b066060141c022894045a46211590058041e1140d40c526232000704c003118007180c840360359115a00a0710009403100801c2a00c41d001c5102800041da0440d41403800c200010610100510602d44586c5d00140f01c104940c5070600720400801e40504142c44000c1c04208040c42510303400c000700081c21202000580d0346c03401612480382034888074018844400100010800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 158466987 1250 158465737 158465753
    0x203070903030e031c1d011b02120c0901150f020105060105090112062601051e18010207080708030103111008010b091906170a0501031a0402010512010f1505030103 72
    0x1d0340e03810700301659001d0f41c07100003c1c035001c4088400300d00456540c8480004943c8800c16510460700d20380c10122086410005450f0031400342e084100342d00c01060001c01603d040c200c24650880d60701e040c1d81c0c01d0803507000403600d640402d030002024880c50170b5036130f0303451035002c501039802601c0391000700300e14101400003c00d01d00c10b00807030b2810407403014200303840500b140d40124010240440420404258440d030151082d15582846146501c1d24002a04410301c8258507950311054241803091641c074500e860400341c00d02520062650b50a1100c40000340c440e4005020b40750040781810f440790315501c0e28900700c07010780603c540104000a07107040165040014281501d0b42c80038002e480700071110210f00e80c1e0040d008801800c800c0c81d800003038040d0b040342400703400780014911285207035919003400c019142c00780320042c420325800318001844014581d0403500a0300c149080340c07610702408000c083c034000030b0300310926007400050104541000b400500e003880301ca508013981551316541314160 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 158468237 1250 158466987 158466989
    0x190302060d11160302060105011106010503030d23070509040f0b030a020907180b070b0f0c2706030a0606020f0f031602060f0c0609010b060405030a0312060801090f0b06010302030709 80
    0x11910b07110a0032a0a6100c000140d59642c5035001c80500603401d1418000e55600c020312a55002c12064904600f2054001c1540c6068540243c005c602d8200000011801001d0305200065102c0000d0590040e811702c41144500610240c1d43d1161201040e00c00c100c121019410741040703103450701d0300010f903a80340440c400103c1c0b60110b84280550740ca01d0340941d007401c11507070460200a1150700124110090360007801d2001d01030030601480d982e8000803050301440175580070304000d0052000e0044a014084842c450361a01d030881040b60500d8400309d04180c00c11b4a1812034035448103024021550704006084401c9400b00c02070900b411b0009046889100d50650081041600c144000a64596100f141e04819400110a07900d040c60001c0c541c581000703980480d603950170607000d440c40341f80201c02d99003036130002000f03010030580300d94040d01e0740c5c00030b0f5040c80c000a880307540020300f41500380714079854540075103030110003103025140080582000501280c181881070051201c1e00303601c840954 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 158469487 1250 158468237 158468257
    0x6051008041b0503070801050a0f0507050706150f06020a0302060a020405060f0f041d070810060816031d010207060b09010e0c0a0c0606090e0d080f060f040906020705010b19030206 79
    0xb4058880703001038a0351503079420058051148440000c0e8800c0154030541c4642400d103410081498900c0300c11042c0c070400d4400600003030f001c2c0030f03800125030582e2120725084c41c85c40c54094001d617a10802c0c60400f5141e0300a80160300109031520a064061120907030044100004510f01800c240c001165401404901d016012000c5034050030880030700d00b2a4090480c5882070203040b15280d08144000c1012120040041c1041022030441c0c0c2540c2a05001d0707984580b1030001595032032481c00b008500751140002010307103d1041c040e021001c9040002e50207007913000542e0703078146420840150f40c0e103803014a0080e480e840042111038200311503140c01c400d00103001030f80c420724460212503400c4040e601800a900d070500004208260b0f9218032007840da41303001c2d103248140000058419502c100d82d00c280441000000480701e11f8009410f0500140007000081c158601d601c4132401c07030300100411140da0b0741d1803840801a1070f00111050032030f40450040e001150542e1b0104007240500b44c100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 158470737 1250 158469487 158469503
    0xd020609060109020c01060b04030804081002090102060c161203060617090c040e10111911210c0709020c072421022a0a0b01030b06150a05040303030605100804 70
    0x11925000c007908900d004005856407140c07a66128246180503a00cd032084a1003032103120003c0000340e0050080c0c0700d00e444141c0290200d69240c01100d0381310f074003400005814001e1f10203208005206d220120409032102d43d000a4150f0600344040c140300d521900c40b40070800c00b1010840c1e011000125102a807105036404501c42c160f110800d031a1102000d28842c1980c20880c6565054103d47c0140041030a402c29810316010490000e841d0030241c01849031035500f010900007950030000101c000441c1c0700352800d40c038007412904800d0410200b500200074054001031030810403441004203d01604003404034018822481d1101910000a03000e080c05002000e001d0844034440703100504a5114000415960b8580d100b0380c50403850f154240c4c0808114030503070b0f0b060031004006200a01c2c1980805009904c3e402c42d102c03c1c10714000100030b2a403144e01110010910140c0d0340280c40c0c0c0006540342c40f41c44034110b1070090300b42e90f080d8204500840740614650003160303210f03c059800681000403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 158471987 1250 158470737 158470747
    0x9081207060b030f0a15091119090f0912020d021e120a080604060609080c0f060d091b050904030905011824080a0203010f0302130209030a12020d02060906010902 71
    0x201001030a6224420b40c2c0c140203034050400041004960b01e08076a01c905a2502018507000d070701002c555440c0409400a04c0300c039915049030400009511102ca88181c0e400f19080d559403010095401010384900400c0e10340c1020420002c40010a000e2505603001a1401040d131800003959010240b000d02d0600c039081c1c25a40d1020800e002da114412002415150380e100c10a40c040d18404048e25040d001d14946580083c0701c038840c00c1c030b420956554a005e4142c0703150f40c000b000400c001c260392095102c3d100b0000b0b801d100683c3d1144810040c032996071036810a426000038000c090107a0b1105002d1813640c010400003da1140c02c0109880f801d091204408020195200c4208155080250300140003640440c3d41100d050a4151318440381c0d444c0b9000b82d075588040c009900007842000200c040c910000d10040c50880e000001d0f0313445560005040c206060000b0380b034500d00790025180c01da080d511184405906100900b01082d26000a0074a41030000039655107050512402c18887d50100f8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 158473237 1250 158471987 158471993
    0x51806100c0f0c030308041a0c0405060918010306060510030e060708090a170d0b04021303062d05040209180607050906040806090c0a060804050a020f0414040317010609081207 77
    0x400348840b81c0e042002c1000ca1a12490003911460040c0d40030349030b9019800d001e460b40108102d0310340c8030b402181c2c04181843e01d888103008180d04080511079004840b402c0e034880151503104114001c50181c007004c181545008140150091280070b008209400e010800c40c440e400040c5c47d681002d5036242958403640d4982c2d00504003500e0038401082201ca80550180c0c02d22514060084844c440d001000001541e0341004124400d034880785c0d003a1454900b040010405580c41034294800da005400c2c1c1003000c80540700e0800c043c8410107211255200e00740b00a40c206490b181da07100f00c211500317024004009800d2540c4e504014407410412000044219060701c41209a4008000c850100e900505045000e076440b0110702c5501c2d801400f06440014a0328071444041d03010320740200c0609200c200076024071000f419186180c681140d21404440d001c041c4008040b48514020b568aa0326171200c01c0b01d6a04040b81030f48810200040b02c10140000705003c190b829400e207001030410b41d640b00320300d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 158474487 1250 158473237 158473253
    0xf040201090b07121409090f070302070807050a0302070509010b030a1d0a030806090705070309060c0f0b13030305090123090709050f0106080f0f0103140f01050106030204051806100c 80
    0x1d04002d848400104520080182c060120160301d01544c9903c6036206228250b2011406620040c9600100d54004918141032809646800032151301c1c0140c41d00030240c541060355070198000300c4655010011001c14503070b05019842c041d200484010840d5407500d103220340c0502020f00640a02c0b5500e030301f850165050807500d13200d00d01c0d01c102942e006007545e00700541082c00413a17519000c0c01c007030000100c04601c10b10480380c0b40750f03041e2141003c0c035007042e81c02c642100340300b00c00b152880b210040b84c0e00400c8441030324522072502c003908148080c84606c0c009003030b07d0000e82a4039490781404900f120040003a041c0c880d09034072403d02c80f00c0134cd891094640c0350250f541c0c00310554a01d0503060184610030a0484c0303040e11801e40f108002e03525000341c0c8070b80608080783d084100d0311601c00180000740300e000d2464948400c40080341d40c3d6100b480b14290844a00385d000c41e02083c0d00103420086401c041c40301b200a448600f6500c905882c1400204d08135440a008400410140c0d90008040009403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 158475737 1250 158474487 158474489
    0xc071208161d0916120e190c1a0c010e010903050f09011b03030207021f09210507080d03180203030d020c0307050114071b02210309121608060f0f04020109 68
    0x28032144842c1069000c0318404c98902618500003044150b840041d460706004103c1c4108049004100c004206862490800c0740110202c0d4031520b02c502c001141e407120060480d20240707640c0c880d0b030364241007011030f400c46620041c0885146d06114400700441c0e0030405940b1549054030841d41d0341c200f408012203080c5550352902c1d401480b030980e03450a140d4190b0161a00a20a64070440012001040700d4500300034082901c0c0060f0400740107001c400031300c104000444c03d0707091105800010f643d480ea42080c1468021890395401b8101c40e40442d075140c000e203c11040301c80d0400170790810b1070300401d4481c4129958100d602d078000844520031201002103071a86031300300700200700c50f0344d00781c2203070b12018820340b8204e001442404107904211361b20810450000c3d401000ca5064240120101c072604100c00507191890005000c10603960301d840d41448032110403070300603040050512400302d41001094014550b40e902600800000a1502030169000000e411919415565500c0100c41181c12 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 158476987 1250 158475737 158475739
    0x103140a1b0501140424050903010f15060309080906070c03020d0c0e0609010b030601080603070906030804080f030405031f021c02090a06020f0c040e0c03060c071208161d 75
    0x4122925003980c10141c05400d5510036a510075060300194180101c40c041c6000b030700e26031886202558422415030300030203c0341c40c050600a00300940040043e08403444000d0800b0080c1d150010302c1c4084450a61000250080d0f00741044691143c2d242d46855020700c484840c002c10b4001140700c144020b60a00600a5500030138401e510215403805c64104081031045810440c8802c011821a180c6460101e05941d118400103085a840c1001110014000b41000b50503010300c94010840c2c0c0c4141c016000a5401180d0503503403285002e188a03c2e001d032240f00c1e086140c0003444280141ea0340032808000401e81c581c540c10016104c02c29002c000c1c81518414118155000b8100c445401c080d005411100c0c02200c20300c00307407130360741000742c1e2540306c09100c2c2c2c912030700b141103a04214076050f0b00242c081715070441104c07549202c601c042454000140c403c0000f2010201741d8004014880081043c1000c591800c000e20342868180e003070386811102400000e008021a1400c41c000c01101101d5098034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 158478237 1250 158476987 158477003
    0x703061e02030916080703020d0f030c060e0706080c0306030606060c100f060602150609011a04030807060519110702010f0e04060311040e0a020d0f0c09050c0901081e0103140a 77
    0x4124040c940d40300000c04ca100c003802e01c0f4820014561134041214400c40343c01400c06000401e0b02d54400b05441810a801c40500450f55007090218001c3e2180003032150b488001888070a04103c0003601550740100315a808881c00c104002841c0c502180135600200241d6030507880310307105104030b400c15440341e50780d40200e1300d40f505540392042945c10180c2114440c2c0c00b51421540d03c11038075420543d04880c955003000e1140010484417200070110710f12001290011420706413642c0d120081688101c03003d4820b541c951703092000da44800240c201d22482c0c05030081025641c4501e144007130f4092002c0c080d041c030011402c12101039025070003e4404500082040044944038a407014101254004c080e009a10b440e18000b880d90000540c45c2c046500142005104080c5546801c0c146c10380709030441d00401c4003440007620861324000c15005034601c818040e21143d08034001411050f00619140e0103001522000f644501c0d4804006c0c156a04003045401050441041504d045803940c3c00900c800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 158479487 1250 158478237 158478241
    0xb090a06020310032307060e030102040902030405030409110c0a030509011707080901050a0e030d180b07080406140402010509120c060a02030408010b0307150e0328020f04020c0703061e0203 83
    0x80754200b0410113483c4114002c84600d0594031100b000f08164504020b51607021020030700c0310501840096066080003030000d40707091380ba007100c5800c0c0d8106460845199001107418061651140512001c4040040c80e003404c2c03006141c4010f50301e80318104040e00380300d400200000c00740d200b24001500e0750542e014200242c1818030000b00090000c032611009546000042045030619004000100b03146600450030000780405000c01000b0340d14201ca40806801040c40018228811007441401c480d110b1f412281703050308140090701d450060704486603044004000060703822400f900c02180c5d040e1502920178900607a2685040240341300c265003c070b008190f162045031700000130800c0e58513610017030108151000c2810340d196040d004004010880c0c40038400010f10958003240b417240010708480d0603803030200040b0109804507198030300e4110140c03140c0c41541814000304003401400d07903046241418000c000c684072a25400020005070300d40f00100400800076900590002c5a010215564 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 158480737 1250 158479487 158479501
    0x6090903020a0201080601021c08090a210908010603080406050c07030212010f0605040507051e0d050a0209040507020a23010b06030702070503070b04080a08090102030d141012050a0b090a060203 85
    0x142c00e400030482c002407100300000c5d01940b000c20607004c44d412141021004c807944100688540750024124500e41c850001d034000404c100f4140c40464a040441c102e40b00c1d220f00d032004041542e130b600b1280e03da85c1021030401c0000e40080466007118958641241c0300c43d280081e0038140559948040e52041e00020001d20706801984000500044903070100015541d4500380004d4500440300000461014000040003c02c000800003080b4081d642c250314208527641050211601691440780742076001c20040401d040034410140c0012a1740010b00d4441256a20000c0310200381d000700500c4d210b81114508405401d4001255800c40204440d441c2e281c00301c03000b03642d4180c0744120b034070030f2003040f40004603050588100c0701030351101d00c05030801d44d0a1b07841e0010554000600541140701c100b0600c1c07050078482c8504504100b01068460090600c0d2180c0101807050740c010110b5100304501d040c0020381e00103210b18201d90700101a44142c2d43c0d01c024541004117212010309401e000100304400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 158481987 1250 158480737 158480743
    0x70c021503190b10030b030a0b070909052212020718020702030120071101091203110c060a020a0618020a031203050106050903061b0c0a060509010e0c030d05070201030609090302 78
    0x45103004102c0c401c007540030000c000341a00d07036152460b600310107600120301c021803082d04841059007002e403c866030f0b8141541e8803000c030102141c40c0030028065038000e000329003081c05059000140211034410655181020303250340680c10400515050b2803400c0d4134141c03802444544000c14010030032070901ca00c0041031078041c0d0301c120f108038401d500e00b90b400f440142801001700743c85101e1584203414805907030707540d500c03400030007800074184007000b40300140900000a00500d254440e5031500b41240e01540e00038a0040c0443e850ba02c103040030301080b40c1040c2e000404030a19604003c01198401d468004103064000c3c010001c4d420415050000c01400041e0700440e401740c0250b0384c00c101c0c0b80e9031500304540d05d0064404040c3d240c0c0190010541800c3c1b2075003140c155030045d000962605078415003c515040d0010300c200c48250300d460070040010000c0c45040300e8070000a002d00001184100020385410b14070109500380500030803003105691096100c000030b054003a000b046000304a00b00650307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 158483237 1250 158481987 158481991
    0x10f030606021b03490c060f09080c0a120807050a0309060608010203070906090617011205010b1e0301270b0a29031b0603070f020a0609030c0b0a02120a05070c021503 73
    0x82c12817034940a1850104803000c42940182555511901005e050362104060140303a0004500d00e92282c60007004555544000c002c5804024020a1140540e141100700c440500301c162050044e80010000119002021504403c0032031900041c641180d1404000400c4540c010340125031011081001c0c2e960400c000c031042c0e8026403180f41d007265803000b084450300d007920001080311104400401045548000d0840401e115400210303417150290081401c001d03008030b89200c0301070010005000d604080c4180042490b40e0304211081e00703442d030640600e6031040030000740030750b1680001440c101c415a2003020700030148140c40ca10f641c0a408400d403801101e40c2d695200c2e008000e00f03800c41082c4c120840300010310190802d811030341c0302e0a05407012807400003190258000c0040b103000040251290402c00703803107603c0c6d000044400d03050000000c40c00401d014101441040314056080b810002c1591001040358007040c0d540c1c074642c0444d80c2001c0c0d040300030b400142416032071800d0700010010358 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 158484487 1250 158483237 158483323
    0x1e0608010902090f06070203010f0510170a0506060904050f030403050d0329060a1b08030106080705030f01031209081e0615090a0b0a0b0a020303010302010f030606021b03 75
    0x1842907620341c1c030030404a1003900005580840740d80341124103410401c0c00b4010541c001000000c000c441c0d03030407000c181c070310896075448001c2c68682c06020000c0c0d90031260880004840c010080c50f00c003651400d68840c0302030a002c1c800c6901c1c400050401600304088d81c1d500c0e12400a69440366943c0c03a15981c1d41d0403040300400480d0030681500f8000140b8050400c0480031a80038100d500140014004141d00c409880020400744a106031641e00b0000b200c060224030035107142c1c0d074030740c50110001c1010601070003e00820000700103100c4400d400050b15070540760002c0740c07054464120101500c080200ba44068403500401d5140e040d8030400b143e131140c1c0e0031342f81000c0c1e902c680d444000340c101030003561100c075501414150101d01d030703907800e940080100038010700b0f0850080d4541704201c0e0b80f80c20203000031005a10020051085580c80030040c25469100d040c01d00c40b49041000294032074401a402d00f081d4841100d54000a03a030800c45200800384141180900c0c02094819030344d4900424510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 158485737 1250 158484487 158484497
    0x140703210819050403050c0102040b0403020f060f04090c0e1c03020114060d031805030102070503070507090603020d020103020304030201090c080706111617010b130f0e0105100506070c1e06 83
    0x250303000c900031048644900d40000d2603201d4842003120803002048054010340400009101c01041000240b0040c400307401d4030701110b521145544100107004100301c9806020b5a407d00c10040c0c001038031001d42c0c050f50314849021481d00c107040021166442c00400d460340c0001d4001241601c1d0710550328450525000303034000c2c800c10010342c6070043e01c41c006880d40c5801c55a450b007000b0201748601c2d642854004a40b00303010190780d4500001c0d00f6030f00800010f468903040020418100001002a0b4005003180c81061255a00c1d41c0c000444021140c1006814103030000001820075100b0740c400b2607040e90180480c0c1c50940c4950031555540c0c910700954001c140b40d003140d10b0440c1c90001d2102420200352800600e10740c02c1100144050151240412466403951030f111026038420f01651017408a00c1c1c030014602c5c41040d030b10010749240d85101000e41c0d260a00740040003a07003160010503201c0c151841d0340c1d1181207280c44240d03458590302c5074040401240300701180401100c90502250348941d12 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 158486987 1250 158485737 158485793
    0x2120103110a060e0f0117040303062402031207020c0901080c0a1a07062f0307081f050609010c0501060e0403030b0102030a08011a040b1b0d030903020712140703 71
    0x500110351043d015400c0803039060800305a05280103050b0448522042c54040406038143d88820300340c5409640c02ca020035190501405154a811407842241d9099414420f4042100d2006900c910811441044c0c0443c8900016010b50081096020300035010344a221b942d03035030382d8885031201e048109403442903052402c0007400340c2902d00b010074001b58208000d890a4001e503504401044800c0e211103c04079208032500c400910003a0000c00b00003031040c03d42d580e01c0d08200c000e01d0711100a081c1c000902c8001d005031101c1c0b0030310441c0000da40c8c05480d419512000000140c4000c81e00304001801c6600344407011802c20004170700a4061403003602e00340100350b403a4005903224001c1520305000030f8030107001049024240c4100401c030510f12003030145407a4889041440d136a01c03800869100c03950115010341c5d181d1b42001200300d1300c4601d240410a0041a540080d01c0303031014410106070b4815260103909200102140091030701d0000c0031540038035074034640422403400900c0c0000d02e000103404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 158488237 1250 158486987 158486989
    0x2040806130b09150112020d0b150405100810050a020c0703060b100c0f030507030e040c2105150f04020f0403030207030c080d051b0c0a0602030405150a020c061c0212010311 76
    0x182000342c03482c0354a881d84070340c1c06c0c280203403190080214281d0b40105c1046400010449021103a030046004640e96240d507100c040c02d00007a144082c0c0740c0d040d01c0f900d0403003c1044e604081010308401150324000712705d80c0c4442c2800c0b0013030301030301c20240e000d070041d080c00000f0407605901c0401c5181342551182e454031500e0303400b5280c44003c217201400f013941041c1c0e2800061b220303800030031095200342040410b240c5a080850b00312110b8805103000300303000d40b51b68002002c840300258070f40f50342c45130103208a20748203118018000c0b00b040054010110b105540c241030344c480d015211400d41a004003601c80360707641030080d5500510704c015200d0404030b20010440781d0011804000c040865209e4a00e45001c40d5829003083c0da2000d0b0201582c028455407907015922001c0100090400d580116140c6080000f040141001034840341c070309030000c1007100400f5070046a46901802d04403030341c5449034000f0f440b05050405c0c1a8801401e148005120381c03002034656040350581c0e020340040446030310410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 158489487 1250 158488237 158488243
    0x12160c0302092e05030d0c030311040b0304031209200109180506090c040f1208120115110715080907080111030414010504021e040b0603011706060a0f0308070602040806130b09 77
    0x10045a4061b0828404502c40f6405155102d503018840d10380001e40d90384401030541035030032603001808441400802d020034141d0040c001040d04180c00410040e0100ca5900d60301d50555640f00d20b0380b00540034144108c1c2e68041c070b0b1444010010410008410100341c0c900000405080b0341c02032040c07922001180b9032048240030b603011380c0c2c1740400c2024501d041200840b03041e008a90201c4410000300007500c0c160011120290007400c03032046201664180302005080540c152010702e0312540070010800c10201251901c409900d07403402c01481c95281c0300d4072581409200e401442056080620240301000b05c0d030019441107001d1284d02c0380c0c02d41003c00382426580103445c041c1d44510301c84400b105000e016055a51030900081000403040004d20100d01142c201341d20880031540355480b070080211042c4011580a40c04881900b203480c18080340c0301c6540340c07600018001a0b0003080c500100701c41a8100c80141c01c0250481e4080d181038118526402140c0c8405c031048864407000c5400c1c0c7c0000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 158490737 1250 158489487 158489489
    0x121303030c210b210a0203102a17070206070f08090d0305101e0515030108030f03061908030d0e0c01020c06090406032a050312160c0302092e 62
    0x1d10000001540d050140c90060f1191070304081d803102c01a2880349042c02c0f043c1c0c400c96406100700c040c0010a903203004260800030080000030b0307064100750040711608007400c0f101e540888046410480b8103400402282c442350510359801003103206801b40070782c0980000e0081c0c440e002d03550b12400840c05002084030210b03010364211801d80d02c42c0f0b821344600d500941000d036020490f4046940895602e08041c04018422094195030840994040c0005c1c240075a080302500801ca900c246154075022285945c1e00c01d82c03420a500710004000b00303030207550f0344502c0c0340c82d44024a6020b161a03191242c0f00d0b100d80c032440800101070b1421000b03120743d00020801d0109400140c014040ca40d0880f4140a16988411501035126940e1034002c40001d410701e0036610103103802e00c40c0c0021100c58181c8551080a01d401103803007540101d651094110030a4100c48503c2c0680200350089002440d1440d2044007a400084d4800702090800c40c03044026110b41109039480c0c02880c40b220300b984007043c2d4500c52 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 158491987 1250 158490737 158490767
    0x120601031b1b0b1008100b18072606041406010f1215060302040510020a2d0515060301141003170c0a0f03030c0201150911121303030c 59
    0xa100c0410842806950000700e501e04100c42010100c01d90307900c00422070401c90b440b03403a000001303800380324180301004100390510714040c0c00c028505100000400b807400000c10480c041c90b5a10009050500c43c04c4c0001c500c48142d030340c0c1c0320384201c803040800021a0846a00d8000da151801340c08011800d040000d016000c182c44030002c03107590030802c07190004c0c07134400c090350075464541c11400101c2051a80d001020183d40058275141048100100f03981c180e904202154271403455000440c42d400c0344190070b4025144c10501007045030a801610304042e140141c098040c00024180740103008624038842c0a0840c003c101c0c00400102c2802013801c15640c4000040701128107000046180d0f10a401c6c00c000d83d1006820880c0d00c40c461440e026030f90408640605400524004041d014028000303a00b0480c0020300540c043e50001c01c4da5080a031190b1024142c60f0003801d01c00301400703002c56400c0e20004500751114078002440600e14041002c040f40024a044440c107640d41c130507110780f41c0b4014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 158493237 1250 158491987 158492021
    0xe010e0603040f0803060f13050403020d09080607050d180b04030e060408030909060102070e13060606050436020d09050601050103021c0504050106150201090b0903040f0905040602070c0b12060103 86
    0x555132201811030300014500758000f40d251070b0307441c4030f55100620b404c010441c5000108051809140090a003401c00c03403040305002e1818070600040c1c00c00705606520906a01c0c181d5296841c2e00750940c058102003140307110040e000c801a8003408581507072148038500a4a0b038400301302c814018400107110310b2250b104140c105101b0a81c0c03528001c014150012014411200c01c0c580741e0b01d0703190101c88280c40d050076003440300150384104003035030050400400c1103092150406150108040020740c606019000302121200d132100f190b0030003101c003050106003403011034540000c1214034000b031501560641e114804c03030000056562180c008c441c18030917182518049055041581c4c0007400010b00200e615548461000c2400001c0391240844180d441d400070132601c1050418030103074180a810065075400420052024031a104601d108072a41090b0001b00d83d501c0c1e0070040c0090007005001001302103484000500c4071034034005010b03810402d28101c045074407010019412164681e0514a9080c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 158494487 1250 158493237 158493263
    0xe040f0f1d0c06031816090b010801150c020a0b0a050901020c04020a0c14030c0a0822030c1503020418020c0709140a021614030a020f06040206031f0b0a0e010e060304 73
    0x1c2000400385422290821508003070480f0740e0f81003400c02014030190000e06c00070103030030868501e65008256607008282820344495040050700030300450311182c4241400f120078022411511003100000041ca0000b01c0661945806580109558030203914140144540c1c02c9080381844c051084806003440d80d114494a26484e655207640403018020b646180c0c0028032100c001c03041e084c021503100354844d03443c1ca030744c03001000031610482e82002d011a40844141100303000150210b00700505880c2d82c440882d8510045100c04c9011344100d2300f1110380c0c03816040c01142d40c600543c0180020031044ca050f01e219a85501e1701004a500b203c2130701c41c610300740101141c0000b140b54000d22100c9090001441c07a1000c41c3c513580303043d140d0048010040e5100103082009280d041c8007800082c014000605400d040030380004409001c0502a9071000304e08000d8507280490380ca115034000c3c10300358016a21020303484405001003120003032050104d406080350000c2ca182010803288110340c803d225a0f00c80d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 158495737 1250 158494487 158494489
    0x100608030909070c08030c0714061611031b0a022404030f0804031e061805030708030603010b0909060a0b011b0f081b010e0c0603250e040f0f1d0c 64
    0xc10090564011300c40071100c0500411034000c02184101c502c030094503540e0350140303464500803040c440b403060260403070b5090045803520310190001e000c0061601a102d03803c3c5003c46425489201c2103820306850785a0070503c6158045000c0c070f90369000315078040a0b10580001d01c20081483c000718411440100020f200003200c3e8041d159429004105180c1065140d40d100610520310600d900c5040300d0303a12100b41003000a000e0312000000c00d402a20580101d0340d662540c90165010040420380c011000960740c3d10700f54068a03200c0e1004184d00d007113080500113103803103220559083c00d009050411301c0e1199405a80741e9625407044c1440207014442c1030701e03000e10311806080101c071001c500b0402102583c00d040b04904425515074000500c0c0740346120654541805404440d001c2c1c0c005004000e413155103141030400b100100e101c0f02048006400045604580c0c1c050b00c25403091401003110491400d50b4040000c0070040c0d03504104682c0c80c000c64000628420003101e4a03640900342c09009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 158496987 1250 158495737 158495749
    0x1b05030907030b011e05060a1407080c010504120314040308010501051b060705090f03010504030804021203090301090f03030c0c0818030a0203010c020607080a091104180b070306081006080309 84
    0x20000840081d103185a85a5507511503081c000e81c018a5160503101044a030380c8400f20304000204005c454403443c14204840207041c4030382058600109e10000303c1d0000c00e010900048072038804c9080000c101d680361516024008012400e40040000d14000a00b034030352400c0300049002da9099214182070381e00e8540115490750061100354051220452a054080401c1099500903c515100d054803080c2d4441400428803036110800d120741c0c107080920002c65004250301c3d4001d40c050395074954824100f07241620b1b61081c1d100d02c90f01586441c10013005d0151101200e11000e1207543d0038080e484e040302040380c204850342e402500301c0c1390810400040c0e807046e40703850801d401c010301560003100c20750f0006801c480c808003504000da0010010407482a500c42c0100c1c0d03010004240c200101000c92302e81643c12261400180d0256035243d10369814031801e18020114240d0040c410f803207602c0c0c8000b0081c040c0031b441c49255064401d025030b03502011130b64007420095032a001c0055080c01849010418 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 158498237 1250 158496987 158496991
    0x12100f0b071410111902030f0d0902010c0c06030501050906040203150603360609030a090312053009010c020307020d0c050303030907140f010206060108040804080f100f1b0503 77
    0x11441825035400040d10300307028491048503903c4451740c440404c103411460181c07228002c201107400130408807401001c8401034070103405860794001890345403440162001801400c1c0038143d84000036000802075850f07080305040e65400d558600c11901c400e0184426800b05440640b40c1442c61900101c0311304050340515840110541503003c3c03166034940100d00440c0407040124079044a003440c21100c03030100141c68200000c04004d62803e04458001401c1d01068000100001188808031130018401c1043d248031512081000681003c14440c02464500783d501d0070b88a0b00f807013000521110010310940c05c140c0c0c2d09402440c904030041d42045520310040d18100e5070002072200c0419162820000ba62103004188001e00c400d0703041003a00c4401040d0780c00301038411000e0700079a14990b6400305003503070070610038280348600392624541081e4900858100d400940305518080d51800b5000803080c09000c07840004011030341969111600b0b8400c50911909000e80d00301c41d0034002481440110303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 158499487 1250 158498237 158498273
    0x61306020409020a0203090306071b0f0804171605030601051e030a0b0711010b03030306011409150a0c030305010506040b09010804030314070815010801060e010c020f0612100f0b07 79
    0x10718180d1207210410480c3c110500000044c1d00c045001c03040d5040801c009a00890f00f801d140100b400703003510313952002c1d50346074000348180d40100515042180070b10517a0f000e002d0700101d51102e403240041ca42d94072031031260040840c0b5111000010b850501140c030074162000900f01c141c0d88008901d092458072511810306070140b189015140c08a115074400d54010b1400c0ea86080000c0c8510780c0312800d590278a540c2511035003040044c0034007aa006014a8554010090807a1301d501a0400062040b400e1060444509900240151459600c02d0040d84054800c0e01c00704500e07600c074028400140603500a50551480400038081a58000c420040d846442031802261960f44041c9070010380e2801d99a88002c2024001488807100a260340141e10f50004e20701800150b00d0084020100111005501d05210b00c88031908259250088200c44142003e82440d03641c000b10320240c800503030f003114009000c41804a0106005800301040002c4400d585030035414188513444e15081280da906081e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 158500737 1250 158499487 158499491
    0xa0c0e0924041d06011a12060301090b0126070f0b1e0d2018040c020c06030408040915030807061a13051906030b0412050c0f070303030605040608061306 67
    0x41c0080c0c1da00d5005000c850280f0500b0359805607001d201c120325144060b00051019031011b10b03180c41112810081c5c40c9110140c0d01080c50684507480800d00604480c54040c000043d8200085251343d005200314a4154803100f403850b88040c12000a83c561800d80518603980105400030412504400e0190090a03403503182d403008916a03180218840d4400e40003102003585500b00d424007020302d03910410031000c120001e5494050f003640c184103110040d030035081c8655a19010b10009500c2041210362060b000707044e1603500d0620b41010701c8603810902c1035801580c10300c0045038841c03070010080710072241d22500e600d090a107965940c0c00600403502007204507800c0052103d0080d55200c002c00d40c414a50000007901c1d00740251300e0700600c00300040c00111142008420000038042c0000c680d400f036007045814001000403070040300c45200f042c0007e60248141030040601e03140c0410840200c9101340c90801202c0c0d03444042c0401d8070381505c0b400c040e80c2c00a0740041e086801c48951000d0840c820240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 158501987 1250 158500737 158500801
    0x7060207090c0318030e0a052e030209030a14010e030a050703030e160b0901020c04021606021c05040c0e09010c0827030307020c130e06060d0f06140a0c0e09 69
    0x560004805900710940000d41b244045045608102c1c0b1860050041520320480d070b03002000507040700250522030f500c0c0001c00c140f41c0a845038400e9065a51340000203040d5821400c0508081d103409848030407041655182c82075003242c40c4d400108581580305541c41d4241008002d07202a8020081c03080814024001e41c000c000342102481d00b11000b07464060055611003e50200091070108158180c50240d03104219440c0c076001e040402d003d2180d84000c0159948c400698038030300c00485c030480348423401d050006020801c00c080310030006454640609036450f0391400e04090907900d840030400c0103c2d10410100c1c0048085c41003101c09200c81002a030803507650300c02c0640c0346070310031145480143c100000d403a1443c6030800b00340594082200c030500540820020080d102e88025042610462400c21680c0801ca005502e90601c940c000d84100070980445c40d0490700b1040403100345040703d00e0301185480c2c103801038900391040b14000e042540329946010030341a03107110406090301e042c600509 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 158503237 1250 158501987 158502011
    0x6040f03090503150a0b01111e0a0b090c030f0c130504140601030501020408070512060109090c030804030605010303030f051608060a0b030c04140603040f020423070810050307060207090c03 83
    0x7207a14510482a513502e040c51600300301d40f104980610582a04001021041d08502c800c00141c022191034140000c0c03c99170300c04912145440c0c125040108031010503400c00085907404101c0740104000de80565003906000e101c85510303010b15801e01a1301c24403207030f000401588142e1042e03070700600c651034610035041e9004e0700900c0c014090780304407103903900041c0c213104040007445918000d1105480c241c0d06100030108442d224281409840d000542d0390821009010080103050019900000c5e05c079902ca40380d04040c40905403d000c00d6000c6030508440c40b4a40215105407485052000e941341075000110030101c13031610011b0031895210302d0101000c6500801c0800a500070380107295a19529031074201c07140000d003140a1010702c5580148204004206c558110070034441d8111000034030011050720b410302408850014011065004c01006911500420114003c1342042c40b84128240d4900030196104818056000182c03c108000c0250a50380d420000950310142000700703c03843e10003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 158504487 1250 158503237 158503243
    0x7080c120c0f03150f01090305060103080f0702130e070b03040221100218090108060c19030204120b15040516080408040302040c05030103060c021209190302190e010f0806040f03090503 81
    0x284034642c020313003220641d0059150160070007258140071301b00f01031018a162240e07911000148405001d5440018284204c4040350084540e010b500801c9ca8081c00e060488a0700201480120003129115950011503104010300a90303201c0d50740103003101e4110381c542d0200342503444100c2214000384a00502038820342e40e00d0000d40000103c804d40e8105c110b0b1030b0b204000c0f181c0e2041c1d000c02c0458010b6000c0c04101c4103004c0071a0040d42c50500f0030900c00b1440a8200c0081c45203a124000309400d0200c040c0400c1410b60318240103200202402c025409a02d0402084a10039541c90b05914940d04114110740d02803c08140c0c854000c2e1900ca040c0748d41e9801003000d41d094013202d4400110b0000052040001e5803040d00b850161030310040c0b1441100600c03009851190016a900c0f6440c5140c03801c01105c40249000003841e4041d086c400e13844002c400e0880c040c1480c0c040d11002d56048800410742c20325070300c01c03841142d14a400a02c501d440d80d80715040003900d60030741030b4104480d5210200315a1410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 158505737 1250 158504487 158504491
    0x133030b0a0b120f04030c030c03050f13060206160503010501030c030e030d0b130504050a231506130506030705090c120f070e030109051c030e0106140907080c120c0f03 74
    0x441541036a6444140c46801d20310f41c0188208000e15800d030610011950110521548a9042c142090190b40301d00b0140c840c1c2c003505581030102940000c2c2c1d10308030205080040e0843d240d6808a41303150311004011004076404030003c1001550a0004110540c420f410139604041c02c0c0c10009100381c00d212805045921002b44048015101d102800090809a5025001070031403002000581400e90300c0548a10344a44080c00101000c84100c0400781d407024020000d2014800322a280101c54404001440c011140c04c0e2040d208115142003074145401114865640100600f406030b040c0b0b4100702880e00040c10304840d000080c4101e00d0f100c000303040d100d40250301842070401b9611b000350b8020000c281d0302e030707001d4040e034100784040700042d00004899100c2802084041410710300048101c000345030b4001214442d6083c4000003440300c4580b0301c44412400706481000780c6a039000800e488005d002d0798180c4034410200a1a060020300c0f05d6029040074042c0340d818070b0140341901d030b13021603042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 158506987 1250 158505737 158505749
    0x100302120a02012003030c09150c0a050706050c0705100c0506040807112e030b150c0105070503010605040b0706020f0a0e0f01140d050a06031a0106080133030b0a 71
    0x10000a00c2950f0304001190540038000301d08080035103580b10560b40320302000e0800c5600000100e202c0c1d80780c1c0c9e12001e0b00a540100f182c2c000c0c0d210500064400c2c4d413441407a50a031918042c60f0700201e100c0c0c3c8284203d42110714840002c0c0000e600d04401c2c03140c160a0710780808100650aa080b1000802c284051400780323004118072504c840b52418911010210034403000d03c03c106120f00c15100740594142c408000b21041014460031620b400d00307902400e401403003294400144c50440b11380f200300e03401802c04482d00d00c00030052036440c1102541c0c64802801803401249040c4003c21070f80003034000900f14a44100805414242c0743c1c074a00e030700b541242c0940d41c0400c448401e141100d007400e119202540009180110b40101e041d1100449407049484d280302503601c0b40e0008100b0501c82e00f00a00440c2d00800701d1041d0030319503600010408080c0900000205000d0000483c12920310a2281d96107901c259012081b03407a960080d100a040c800d440181922000d01107150f5a45d2004c00c1d0081c0b81d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 158508237 1250 158506987 158506993
    0x8180a021c050a050f1b010c1104090204051003170a17040f080a080105040f0603080901180f150f02010b01050d050415050405030c07090207081605030f07081902030c100510030212 79
    0x1114441c0241002080420115400c10103501901b150303030701074460300c0440c0c1c1184080e00012400804540905407002003e5081410b14080c00481d4044214000803280103000082e0341d28142d5007244081d10554441000084248108070098030356524901d410501c40c41006103010669601c543c016040403d0340000700e0144001080281858000d05455034403040b0200f01c918155a914145401a081094100300c142050181e00303039202150607028041c1e401c402d40c4181e660303288080b04240000c0214000400740c010341ca1040f40140031f04102400161100e90a0843e40c803000ba004040003070080c0d13061500c03080086402101445030601840c0110055652082100103813841c144c065403260012070701c10042800403a140c032040d42d0003090307440001c82c4e002c41141000f0307140d40150107119241c03200000f000000c1007101c0004110100c400441982c200c00e408038281e8490107043d540d05459088044400b14480c3d09500140c1d20110342c0740a5108c0c0c5032240c0105107500c8404215950a038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 158509487 1250 158508237 158508253
    0x9031504060b0a080a0507060f050f0f07020a0b180f181812040f051207030503040b0c1921090f06030504060b0904120e0a050d08070308180a021c050a05 67
    0x414410f410380d01030b103880c2c07004001400d219a5655030341c1d251071182c2c804105041c040c0782c110922410880d500841c1c1080159140d4140c009120074692000700100e10070140417600040f90034002e802c3e51f042220f44068204421940014001c620811040440d404901c00119283c5090111240341c0a4041c50404c100c8404d41c940e0020b241c0184410400889901840300b08900803e50f04c0c04c00540e04250f4820100341076005600c3d1034a40c680d00010000d001c04034000ca46072580c4406004521000401c8421101d03042100034541d1442400107006050011701401ca006412554541201c3d20781c80d04240481d0703a14801da8001009800440c000380e01e541c00d200500081d4041c0812005084606016500785940c0340021051003582240511980241c0da1aa275510040f900d8001c240161440b0610401450514140d80c45940202c010402d41c0d004203005500b8494101c0c07280311400014080800c1039020001c441208010364682c03110114030b00c00000d541070000c00170442c4220002c00f901c0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 158510737 1250 158509487 158509489
    0x51f03030f031d0a020f0402040f0b0a1806050405120c0301020a020f060a1503020d0804210501051003080f0f0c160e01060806010903063219020304021509031504060b 73
    0x1550b07a06500f0442041c0070080401c542c2c2e000710b00e0086550341103520f11b50701c05a0002041c06802241e200000b04c9402c400001036244414000344038140c2c0c0c0d5a514080c0014815582400b045036002e000000b0f10180010300c40790500025005100e0800c0c81100c094060a8000900ba03a2140c0741c0540160042103100164030010400e164002d0503604082c0620746440821180c03a01c0b103440003a102e400722000703010034040101c007207030050b1a02102d40143c00c0c6000d040700700076064900d07044921350300c0c00300040c55800d00581d612090b80d81c410b0303203689400703031520300140c042e04110400c600f00c0e0001c2218030b10707081003004a00b06040050700170868040c900000300c80000c40580c8407000340b00340e40d01000583ea82c0001d1110540b0781c030860000d40016507010082007c48400300d0300146003003210b1a4006408400c0085c0d120f0301c1e6456a50848404600c0030000340d010607034009400c44004503039524414091000b400032948040c0468421000c075451415900c40240d5003518030740c0c0e441240c2c60702 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 158511987 1250 158510737 158510741
    0x1030f0b030c0402031008251d07050d020c010212010e0610020a030f03060b0307090f320d0b04140606010509010518062109010b010e13051f03030f03 66
    0x1626920a008001a0220002107900d522011100c144034590002c002054441e410512030080c058403000c65901080907460802c1100c000851103405604203940022120700000e14036040d40d410a100012765121001d05607820b41050005504840d000d1048914140d000d10140c60f10080102e00708015514118600500b2040a003c0b1401040d0300807200b220b20b40c00151418243c3d074146885000c003002454114000d0a4640018039582000010700c01e40d9980842d141060f10403000d03145140b40d03a50200b20001e800a80c06800d8080b115602c403041c2501810130710850a82c1c090300d0100d41c240c00d41da078100c0c0d041c0c08503012180e43c12201884040e0a2080200d15030090003820014505210100040c0c014062543c2644d802e1410003000842d503142c0c8401c0c0e880314000720b20010351090500124248001040755115005d600e0107121301a07640c8621a04028008080c5c4100b00000a0b0b80540c0050306008204a882091601c003541412010000c0380c80290b000707640390741d10f0380c410301d500070f01b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 158513237 1250 158511987 158512001
    0x21191805100807081b0a080708010603150915050d08040f15090b0d0e0d030905060603030f0a050c071e080d0c080a0507050c0d050715180e0a09020d0309050103 70
    0x40641c03000500c50512070b41102d1120340024050426500315500c0800d4009a000102021084004007143e1001081e40111015004007417a0300c6100312aa25400114125240c00c0286009923024440030400441c443d44000a290305105560f181191988040b550030900242c1c1103d4120340000c0030003251072035140b160068134443c4070014224076004001072012440b8004d921080000040a2803040c4d11940700c5a4018409000e469480b00841c1020380105002041a82c00c2d008500001d04d4602c0c001c0216101041e0201c002c90601c826004121099042492690b0180c4901d000100310340380f201340792850005501440000050400d41c0d83c0c0d0520f083d120501c82484814503010000441583c03d91b01246641d10340142c60b5541e81c10803c2c0751901001100740c01c070000c403440c001800000303e426400c0d141200c220780810002103400310b030b04c2c0401100b45125138642d02c4040c400c088400c0709454016142d40000700e1001803c5d00041c21411049400702c0204480840400955816000b02c20b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 158514487 1250 158513237 158513239
    0x902040e061603050c0316120c08010906060801030807030f1403040f030306051c060209030c060c01020d0b0603090a0f030507060f050601020c1c0f0305042301021e21191805 76
    0x101440c02c22400028176400007400310000501002d0418940b01d03c6840047c9183c90407207424003c00c000607001925845083c0148991642420000f151190040211a0499034040301091034111591011103091280c400141e04000d50415030f0000d103180c800c080c50086000300046c044d4148d10f460b001d8112091588114050850540488414083c54160044c000d1300000050303965000b4400203414604074000c01ca45c010310110b2180365422055010b41661f402d103020801c0031041032801c00c9850b0004036905681c903801082c1074800a4028407001c10a9840390a20b83d003441d041d69104d10680d00c1d064140078030305540d801000519a4100003002c042602030382d4070240500980c030461210708078a800605010358001030034080500c240100c0d8000d001c00040c08140c01c1a514481c44104500610140144100a8401c0120321843d941025104100c1c0040c5204807016410711811080801c00ba1001c0d0410f00c40903141090305c0e0792981d460038041c3d884811460b500c2e804010340c650150040b0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 158515737 1250 158514487 158514491
    0xe030105150f0405091e01020702030106080705061b031207051911030708030c0705070611010606050f090f01020c130b03240105010c060902040c0c03081609050609040902040e061603 80
    0x8461640790214a00200b180540d400300f105e07954198114a0b1003e030702024038000203421803d00343c040041d80900724403442100280002036031b40391915540c440600032aa80103008200e04040301e0b011505010461074558150fa0404641d01c000114511085990102003400003440034002c1d01030308070081c03108600707007044031800d00c046014555a00031103400030000200000401c1010303181c203003910303c20b035441022901407d4403084020078181031007401c60450340c281040031a4460040041c2c03040300300c1200c91142081001d03c2040b00340c21701041900c1c1075000e007030800b0304d0310780701c482e601154103001c80703030100e80040c4220505103080c0281c00780800014401030002c40014890802d181110400d20b000c407903007000c500b0214000e0518460013940289440b05400c00310781c20007444841e440c000d03140c6e070140f9030b1401c814103202603185040c100080d101e14424029407070011702401d001e5001500010b841c0029a01003030884009040c0108168072840411000403003c44008100a00501d01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 158516987 1250 158515737 158515771
    0x1406010b0a0c050703140706090b0f090603070e0a0b0a0e0f0d06051e010305010c140703020601050402031b0708071b0e060f061908010603060603020a0e0405040c050307060e030105 79
    0x340401405160705050800951800307103428054100500005160420f1100c43c1801c0160191380d9190079501c110300c003143c5e000d0360000d1109038420903264580b03042a1424908240c1030b04114281d03000070304140038041c07074030004c07002522490003080c041c1c0b8081541c030769592007001c4c010380300ba45030018440c4110180c200303115030b075201c0045582083e603000d50f000c01c5a407518401e2600d0200c100d6070b42c04c00790f42d400f0000001e2000542140d01d1074101e80d190301c0011050b41031400c00314419441c016001d1380c0041e004002d5030409038003c0d0f80c44111a1030217080c0340c00e14101c0448a902540e01034800765004510302c814842d241c164481621b907501605408503113844c8040c45004001401c140c0710703105101900c84aa2203100803644940c0416284140341c446912010f083e409080c041d120000389030290100762240280300f154522416925503d070b0710901031040001500e00108211903801e1110700000d500e8800300b1110004d4041760b01c0d60180d00441c1d505150854000a000c0d8014000c3d11803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 158518237 1250 158516987 158516999
    0x5061f030b060d0b0702030306040c080f2410050c010522060506040209130c080109020a02070b0903030c121b01022701030b0319020301060b120105060a1812140601 72
    0x100104496100ca001d2007990744540014034402c50074400070306440c0d0302504201c10340c1d0b40400214803c600885081081440c4400101e030460402c84000903903c44000105e00120041c40c50511400c44c8013031502500b80500010424800405200d9008944040740d607200e10107003030041700c2d481684070b072114664514201001a100c420b029001d0306155031a0702042060701d47d0303011140e14100c0a4030402444001c0704c8e005c4010f1440c41d5000001404480000c00c0e034150314000c070340f0f90303210380e81c02440514140850344c00142d0015410710f506110410040c80103903014408000f2496101c1d81e01505c500c284e000300e0100700b030003000f40e0519910400c415410f102c008013a8041c81103a5948000c00c018010b00160001d01080c104d0a03418483c100c0000c034880d005815003500b4074030a80090210668502c9400904c4c001c00c030f0004102c11512005100301c5c100980640b07a80e1322146440301001c0008444941d600c0c0d025009642d44034007161210090100017090032040300c0c3c2400080000d90314280e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 158519487 1250 158518237 158518291
    0x1e0a08070201050c070e0c070b060d2a050d081306090807090506040f0603140d1707050901051e250b040303051008060108010c0f020d05040e04061d01090506 69
    0x2500c024140f01003c00d81c05030300b000410540029003000c24031400282008900d9500740c0d0080743c000c860a0031401c1c00142d0300d040801031008103070f41c010900d068080342e80d0f80741280c85600400c080144100d00d03c00191907680c1040c98031a01d801820f01c5665241305201126007111180c1050b010300000c40020045101c0024411040b41c000703602c000741b1525813600040281c14442c4a2070744990601c0000300c1800144900c500c42918110200ea0030804455010385412580c604c03461030a12205000950030350051000303225a410501d0102e01d001d81c0440d0000d101150300c03110720800d000201c1c82d0111682c011912110010814151070041d00c2503948641d141c5a00800c005c0815460720081000b120314018004041c03c0d020068461540c4c40d911b50900030070366003c80c000010681d072010b00d1402d00104108801070045d60390b191030306050081c01040320202030001c644003030341c0b0301400110440c0001c110310100612800414400c00b1740c02d0480c076180000e0091045d0f03044030701c10200301c180c1d48 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 158520737 1250 158519487 158519497
    0x1505120420030a0b15060d0c021b0117040f1403070308041e11040e01020409090809092d071209111207060f031a0a06051b03070803040b060d0804081e0a08 68
    0x1c440c2400c5222030460106d6120b0040841000c02903040c0801004a5900030400b120b176960144403d10441440000454103101d503841e2140201d204e00c0c0225001c90040d102001e19140030310300d8a1400b11190441d0ba10310b60041005400060303c001c00d100402038400c0d840da0760441c0303141803070291800a85804481d03100031211281308039a18600100703030f140203405540041c40641e408101c039001c0c40c10300200507408640e00b18401e64003080020180900e04002031002d280c2c4c40c03003001907055a5a00800002800f4101605101041e141014048060b000c1d0300e905d9442900c008030f40d040e600c1d00703001340f54170250700c2d044091300001000c0c40011341c00b58451400d06080d14002c44c0610300d103000880d500f082000303201c1c0c00c29000880400d849801000520040780c181d00100d040700c4030414415207a001e590402081e010042011a000c2540641d40b00e4207e44014101600a0681e40d620078055021360712648860700100042590001451502c00d400f03088000035141e40105691286210f101d9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 158521987 1250 158520737 158520751
    0x506010e0d0510020408030d0e071202061b07120203010b3307050f070f08060402031902030f01140a060503060613150b04080304031205070201091505120420030a0b 72
    0x2402150506002c001c019140c09403100790021507407640c90f40820354503580105280f0b10250305142c070a401844000804c04100c801e030261000303002045a00300285a030001d101a40c1c03030a41c114600b40139580a001540003010480091032032072300c0c0c52047c507094417a60b92041d4850410205071010131001c0010301050150b201d0003611341d64840c20f0240d2000c0c010303a2005011445086107402400c01d00088c11402e4448a440e807a50903561466000e6591804880003509500850b411810034815040748491080c8000d050b075140c40c800581103421200c0d45003205144d44460400c0c851100468491000904025000780c0681d00d0101d002c1035034030000b5150b0512460381c1e0b5405203070003a0b142d6154030207081c0c104140d55039142e486021550741d07081404140c404100078150b09191070700a030121065036a041e1030700d03c66107180c0185035502101044d00352060203420024850a45540014548118070a03010900700072448402124186813020036203029500ca04c0700d400c0030a41d15901c460340500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 158523237 1250 158521987 158521999
    0x13020313020f0103180501140907080d030c090302180106030b0d030203040e0406090b04150515090403032a03020301031101030e0a080a1b030c06110936010b0318010506010e 76
    0x2d80380012001085010342e103440d201108200e90f810003c06402040c40d400b000e8038032499640700d502c0d429454580354407a445459200042c8140254042c0c1c201c42c0e48030703119082807071005075203402146260b00c80981c881c080300b40307050043c40015018401d004444500381e030075000c041c11075a4040d6492086000d002d40000e00407001408112403a0004441c2d654001c9001030141812316110300076040b80000540300c24141000070b045d00045400d2040d174031a008144c0e07403007920307503171003d80040c2803241344044401c011907046c0902c0a82c0510203400302c0342c15900103a83c0c0d0704d50700745040b071080c248003994109070402c007144820f003000048002499401144c5150354106152054803400d03041c081c0a460035107041e1119003403541041d034518405001c1e0340148850203000c05404550b2040301c010651100c0304000e209182c030800709450103460403102c241d0000c2c0c0802d403080341000100368804031310760100004110702000d925991003503807042d8000030301650814000282500c40c040900c180980 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 158524487 1250 158523237 158523259
    0xf060f0c140102071a0906040c06081306050907030213020f07150e0a0f030e0f030d120204240210020403020f0f061908070306050a0e0406020307050d0c020c1302031302 74
    0x4104a00d80c0300480381d050008540c1c03044103107051210140d800c219801e4000700303d00000c0c805070b030201c2c019103c2c42e800810282c403d41049020340d8100320140a0703507100300c031480c48100055102d10489005681080041440501c0c6104102459803d05000610540184000d0064880340390035242a145c1c080d6481c014201018007103002840e00c03030700d00003d910070b0142c8903041c000140c903240d60841c0246d4458400d1030000e0280041d080c0e6100d10710f0b82681c8019070401080e4810801040a04071a2801520b087d5a0f4140da01070340180180301900301003a4072100c000260100700a1080000c408400d5003481d245400207094900700c2e070041307070240b050101940c4043c2d036804102d805840007603020050715184000020708442d421a58140881c1c6005004200c62030f0500105049810440320400d807590b603a59020060b4101070004000c3c40400c2c0710386414813a440c0201801100a80d00505030141c00c441005610078002500b07002d0070b40704000703101d030b603112248450f051250142c40c81c41c3c0b49 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 158525737 1250 158524487 158524493
    0x31e0902120102040306050601031404231e240c0301030809060904090c0302040b0409150c03060308160308010b030601020307140709022b0c120b031014100f060f0c 72
    0x10404500740007a840d480054044200081944003d01510b000c1c1c3e401c000c41c480004c10800c02c1c0310191005084805120501c040d00d2001141100d4028001801e882480903050004060000560806500d07a04424508805907103100c014586065441404054500b40744060040e14070040c04040d1032041700150300002519054101e0307000e14005442081050071505188890b61090700080b44500d0806407952101e2410f405a101c01c1500304916501c1c84003484030807801440010000c4c800c3c5a16080c00101103110480601f00104004041e140b90002501c0c0c001c0003090160064802c85070288244512030b6400401d03901c841c0c2d40102000320310114040041c0ca012125444840c400b400004c4c00d4540404200e442540806141084180800039080131416151510700301d0b400618011038a00c81406160812362515001400381da03042d118004030300c0f05540300030250441d0a405a4240085030704011001d90080140c100d134191032a052040082074500c41211000800084100260074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 158526987 1250 158525737 158525749
    0xc02100f031104090c021203150f0d0c03050a0506011d0f04110307121506060c0b1e07050c06100503060a02092803030207060306030b0a0906020c10050115031e0902 72
    0x40c0300004400c00f40c84903030700c241000c050055500000c0040c080d03220121080c103450015030b40940034040c0e180c0b174100540c00900913045e6042c2074940d4008003c58204c2c0103c4c2c1150740c45070165001d200600020310440c10200d103400c0c8103a012902030580706014150710300412440c00d42000000b00000e00984460418100e02100c0c5801a64140a4088002041032080d44500c014900c42c107180520b50032024071503011640c90348640f502240030060318400282610304030310391110022040a200101d03699100c128160101e07240380101c1d00026420b5041d503010410310f58088000008566110b0404d0003294585001030001034040c0d03004034a0030815a2103420400240c40410504101c503801c4000360b40941034144419409070050401c00320308030f48a402610244c90700010020042d4641c01461350040600325800e6566039400c2c860740c4000d42003032007280100d61604101062035410100c0c0581c04801414a01003450319000c507111361000c0188840c07250900c108800102d036607190010602c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 158528237 1250 158526987 158527001
    0x60e15031b04091b091505060a0e0303190509090906090c040507020c06070609060e070b040b03040c0b0d090209060f0d0f02060f04031505011a0909070e060703020109060c0c02100f03 80
    0x60401c10a603a0400103c45004d140304480c0001814010b04400d940c102040303084034018150800700405c072083d1030b01e01030802e00c008030310302408903450102030161000d075903100941040001040011024120f10b084040e1a820101c06400743c8414200301c0744c5c80b40d84100c4c55100d54003a42c0c55800046007213009100058821601500050b502c2c100781c1390420050000c03080c00c50304245482140c00b0304510004404041d83c0000b20601e00c0c040c18055600000d8100401c01c5a5141f00e0010119644c1002c00c080c000003102000702003801b04492040001000340149028000c03030b00040c044c0825510700c030009048607040a0b15021140c3d071030010401a1040c440c0035081124002800420040301d40340e5030b211905034482c1004580d072180b0340540341c1008208409910310060200300c1903480c004081076000101400c0c40301c2e4404194000c40c1c0503402c16207065016035035403001441481054001c1000c140e420345031040310790580303170b00080c41d0641c40c001107000c10a0358402200c585000b603110300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 158529487 1250 158528237 158528243
    0x309020307120326040302031611040204090b090a11040e04060b060f0a0906020601060c0b060103090203010e030c07050a0305030f0d020c15060111011e0207030507060f060e15031b0409 81
    0xd05000c941009000c00045440604e22a004200002010702d0900d211600035903160f8041c1d403500c6400d4405030071550001c0c6094a0401a48844c03c0140d9120701c0104018401e580c00454203803103840401c140d900004003141d0ba00d80c18600c610b007804480208a8056480d02c2000f2005510340b424164000c00ca01591140c025200040c00a207291001e00a41098901b039031301c9148258070780600f01d849643c2031003410301007803c88207100000b0b502c020b01c02d0740c0000189000592a082c0e60002807c0d00c00724441300c280764000141600d015103044c0402c80252009440c001c81d07562940d50383c680e5922400781065500305c00822044003010076501100d9200c00801704a0b1103a400d103460030f1500d41d07025070f0458003150124104e20601340c010301a8243c10740c10221943c41001116013482e02035030152404030100a0100071285c002482c51045203c0d020041c500010410304022903003034011400303008842e00ba1402e00c1002200c0d50b0006140240f103100c060180c40015030350000ca40030f000300c52001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 158530737 1250 158529487 158529509
    0x524040c210e07080c030a06050411150d060f050a06030203100314070f0611100b011112040515041206090c030f03020c100e01090b1b030d1a01030612030309020307 72
    0xc1c00d0340041e80082c082c6100000c240c540d81030382c40c024651380b404e4118901342c040d00601e82040c049460382c0d02c04ea9216000f1610000500d01410006060607040e02c03405c40c083c0c0c80403428211414003482010301802654402a405a0070710000404014440c86403a0030107030004001072082d040c070380310980250781c00904000401388503c0d005456248500610301902081100040c0e004d100b40e00e00c00d0640c2da4a00506000f01c1d40ca0f031a4000ba0020041441c14060b01c1140060452000c00080440d280703a14001d503240d900b0705040000507520300c85000c4149800340000d00541000301d0b00e075010310303920500000e2400b0440c0f0382801c600d0340950003c4d24880744c1484000070300da0042038041d2100350444d000d1812a50303001064404148092016000506008040c131006023020010152a40d01c0e1810b00e0700c031031019408600d10303030000e44210b4580c0c0e1640c101004001c1084078010252100742002c0c050036083c8205210b84860f64a8090100740d00c50f0840c00c02d40d1024000000903140441ca0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 158531987 1250 158530737 158530787
    0x4020904061806090213050402011b05030c030d060e1003021e01030605120102090f120309120a020616050606040203010e0c0706090804120209010e1e07030204080706080a0524040c 79
    0x3c944001e200b00d500582c0507100c10a517204c2010741c14402c2510460b4140c503029080d120050020203150441902140d0310710007080001a003401c10009082161043d5401007502420844071040c2100040c294444820301080305000603947c04c000504006401200701c031240c00801c0049016118651005800041c11310f403d10341c0f0386040d0006c20b60940c065034116004100c076014451980510702007113255401c10b010f01c140c03526094200071450010041100d5014100740c0002c0c4030781d0702c52070500c460103902d820180100a001d10030107074030174400c0310110305561602000812040700101358040305000000e1740000c2041a41c0060460394100b10ba10752910b490340c0025119062180e411307480340b0512400000c00c1d4100c0749005215000c42196158402c2641d10009000031000c4c1c41c52050603028040821044000c1000c8001006259280006070600381c9032541154000350000329040000c0c1c64600f0032860560403100c0d05042034400203018226424115581b04420068000260000701 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 158533237 1250 158531987 158531993
    0x13060e0f04200105041401090504020c01020c190201020601050d02010203070b0c0309070f080304260d03050a0c0503041110031d0601080708030a021207080f0a021609090803040209040618 82
    0x3528462842048101801c004400a1025040449081c2d03800184204410310078a50300000041d1240c0060604c2006140c03194006016a001115601520380d4041407c00d0a010f04012200c071403070804004001540300e50700001e481d040d05005490040d813010b410841164401c1044880464008400c0340040c1800e1800ea52180c3c0107803100111449040707004610031034549089011100c038030f80107514080c5030051200050382d040c1100c8611b10410181860b501c081803122102c1c40460b61b034009510b00e0480000c40c1100c042d4904403041050a00400001502803280d81c07240c41411125246400c55070b03c1d0403000342c840207200c42c00d201c50200303480c00401b50000c0e1860580319480e081d00c0c141900c400040f6a240202206031005900a50143d03420111280040603514040c441d66480c0800708640c0c0322450703108068803001a8031503500c003c0b461250301d6482c0003500103e6418000d440050311100780340c2c000504007901c1400110081010444c0c142d1100c0d00010082c80740c0005110181 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 158534487 1250 158533237 158533261
    0x12040f02010306050f1e0301110c010509060f01080c12030c032704020a140d02090a060206100801051b090d0b040b040b0919080c070513060807050402120613060e 71
    0x660201c1c0400d04003034000c40c03145010401c400380094003606200a06009051410046045044054155580d10405455107403c03500600d810f81c6100300205003820810303100740c42d0800040c1143c101045400044c440d0701d0740071443d4804c100003161410b0000403150441030840c81500400d6205110008103950788199050100c1c200710600185003100d202e0460512050380f18070012840010100743d1032800d1031a04002030520381c00b0311180142041c80c40030200f15042140d8000c4409a4050030411003100d207501003081c00303401c9c142c00034061410522500d00d04501c0b0001c1e9a404004041208080ca07246c040d08101c0c1c50f5000046181281480c0c2402182800242c40030b4134072503984030025100590000329510b500c1d60b14508480812100d4940e0700382a0494040c00040e401420030000c0d5035134591021001c22248450300059051500c03081e58a00783c01da80c0058019801030042914400c051400e841d445502a100c00030b940709a2004134000f014070b900f00d1050100c00380248810f00c2c2c042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 158535737 1250 158534487 158534513
    0xf1a090d03171003060b030102030411010c05030408030301090f0e0c03060c090f0a0605030103031b050601060f0309051e0c0a080705011b0f150b010e03060a0c02121b0111070c0902030c1204 83
    0xc01701080510002c0c41414280c2c0303c21540030704401038101c44090594481c07103001030980d018400303403400c103511a05101c0c195802a808101c90a0310f5010b00f0301080050710500c0242c0c07042100601c0b00c11880400b1940b80e200c0140b804000389404038890007180c4a104d0540d403078502c014a080b10603500e40c403010709150020300060f4005000000301c250788081115050640c1c0360024028905a86400c01c2102d1764220020308904150311401c2400014004118003445408400d14002c0b4881c07103040c042c1d1400400c0451144a0003182c8410003c8640200d6001c059550030300e8411142c4400052840c00c110000400034600f074040301507c0305215090003142840306c4a40018400b02c28020b00468104a6405125a0580002c0b0129280703a91940c07105c4541c6969005030391a503031001454146903000141d1040c000d92440145941c8040c0a21442800d40070172100030381480350b51b07220044c0d001c0c141d0080e20052940040800d45151a003402d8911a943c1e01c4240b06c01480e081c68014240000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 158536987 1250 158535737 158535743
    0xf04030605010b07050c0405071101183e01031503050321010321030609090516081920040204030305090f090601020a0b0618040302070f1a090d03171003 67
    0x1404001281c0f50610000300c078800c5401000826007028040c003000700602000d401541800b85002c5603c0c0310280078042c1c0b410014a90755032810454603400c0032249100580070903603040065800c5c0300711141101018440850021000c03003d905809001030300181403c01c0302d15042d2613510750000c00c02400000038281d10a01200092542710341c41c6044a400301d00703000c018000b4131070341e0440441c00c9d291500341d03c4085a070320b800305440350b68801640840b0a001d0065a0503005801c010031a101c001602000a0410788000c01c9030014800c5110140005900000e010301100300039a002c02800d948072280c0c03041d005200b10741c3c0e26503d00d0040c100340e10081149016001c40d17064406c0e149405c080781803003008107802602003800e5694441c589100024a00c1c0d0344444030342d14004000b40070b44615072146120b40c00500e896400c02c05d9540400925038447c444031a20b5490ba11400340800003952001581501c900d507411000303107801c4c0c4002c0d020755440034401e00c00004011819042d88516411240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 158538237 1250 158536987 158536991
    0x303070b0108071401090302010305040201180b07020102060f0601201015050102150702070b0c0f070306020903150417031801090c060306080105010b0702100210090825030c0b0a0209060f040306 85
    0x503450b02e0384484c070018248200e01040c0750300401c00255010303402076035200340f0500d060500d00442440e400101340300d60304003410245011603c0000c658042240c1a003000b52922952020b02d00000001c16020041705081c075043c03410101a58064400c100b004039070340415106020031042143c8100003e8403500c52940184240b180b0503031103e150b014280d0085402d54090b0901030308040307001503194440005481e5520901c8110101c9600a000042c050f500c510700141c3d071611010304041c507144403500c1c00703070311206900d040c080013410ba032440045001d02c00742e55607125911444a801103a00088c603610342542000c2c0000c0130800081d5594045e10102e440401c0f066072103251185c04c0b20000d003ea4142c400003081101c0241c60003180109194220f84116680d00d0b240c0140c08041d5040d0035011141d10101089200314066201104440b00a1000d0311000b460354a40b00100042e0314a100989005010b001054921103141c040310321440024200c203075110b0383c0000c684040c2e8410310095407154 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 158539487 1250 158538237 158538239
    0x5010609150510120e10090b100806070206070c03030b030a051e03090a03140102091809060a0b010219170a02030d06050d12080a020d0501140f09091e0c0303070b010807 74
    0x4645400c0f03200c0355200c075586012200e442040144018100c181c02c401040c031500384900c5e04002c1c03501900790a03a200d024005100c1c244140442094400354014002507046001045001940015050340c00030441c0360284404c0c0311b0741000c0d4010302201a040d41c05006508201c0c09221300002c6800d907103503240d14410780c000127004581e9124065410b191f030384403500322820800308140d407040d0034003900d40500043c58800740c280090805c1407002d01c000d401800101c100700707801c2000e0103013503400303485140180202030324100002d4503210400e42c042c2e02502c650024034213105090b002000c010b103511005668805070000065501d4101700c950825140c1005808611f81c103181c00108440c41d4440401c07080f09508680650301000d0050404860b0b0368240103411194040b4001c0300c0c001c2c0500d04038991160246014000b40b91048400940140d444100703001640000041017001030303142500181d25890703c200354505054800c0c61a0354140f00c089060028411403180c46412114942c0444000c9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 158540737 1250 158539487 158539489
    0x601030209010e01050730030f0903080a0e0f0609030909010f05010c03210f020c0d08040312090201110102122403060711011514010f0302040e060402090d050106091505 74
    0xa84103070415140021803c0b8400302455024602500708544584510b4000d54000720032031140c45c030401c0ca20100e0340101da0007030080c55054801da004245078200180034586841d200940718010241c140d00541d60384003200050600103110000c00e098000060303500c9030600b0094184e03260412291240b003101c031000002003c440040c2c030b070011030314181c44a80c40c0c01d615031001e54041c07038244800407104800748500c004909480c8201441c2410000006072240c0c00d00200501d84502e8030141020301032010207000c0443c1d0881e031110711082d05080089440038403407004803040502540070000a40c000704003509000941c00160380f003008081c41c0400500c00115035500380541600c0c0154064005d640480d4406105030781c0940c0201b041400810360303103008105040141e0040d80802d401401144000502d0340e44621030b0025000903103419424175042c25410b101641014000d64880c07030303000442150381d84a02c1126801c058122000708030003652929144040c0811324400302512124490125503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 158541987 1250 158540737 158540741
    0xa0b070f030b0414040b180f070f060e09061e06030103060f05060604210c0b0c07060201180507090f150e0403030b1e100504050a06051b0307030c0318120b0609060103 73
    0x1503142041c03060300c6072159106d5015901000e0241914200b010800f2800600100304441c00000703124000c008651404818801c0242d064014500300003c50202c500ca503a43c040c0c080d41c10000840d11083c1d48010f41c504007001030b4001c1c0303d00e50401c00c00b20000062015030350100c80e09288204003400300741e40318403c204032071184d07001c1e0114401e000e0780c03a1112038104112010810f03100e82c00301d03265079448291514850f048410407001c158031000c2c060040c0740e828024611a0411600300c0c40c040c2d440c43c0c0d10151038212034050351070701b1030307032034641d046000880d0300b2043d132100b00b101d0748090044e10340010407480e420849003600803d02f020819000781c00c0032301d80d00200d840c0070000310710b00c0e6010000300403000c0c4c10f010140f0f08201060001003a207075a02c1d50b0500040c449902c1d0b8603604d0b25a00d04d050184140b10300c3c14503082d0000c1c032500700844c0e08280c1a601c02030f4107142180040070314000390503264036250481c0f90b140458807580303410408000c3c881e5001e490101c601c8403403a6241001101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 158543237 1250 158541987 158542001
    0xe041a01060503191e090c060315050103020c0106050405070f020d0c020607060506010c05120417060702030403080d1b081e01050604050d03030902030a060902090c210601020a0b070f030b04 83
    0x50b500300000b0303000c11141105129903960b0b07500040b503020710360068590a01c41c900303a8a071a1070307614800803081106d0110440000c000504040c01408000c0d6062002181c00b44511410316800045200300000c00b98429805800d0040c0b040106041545005115010a0b201c10015100d4800040d00c0d40d801412080304035903004208514011840da84c41c4003600c0040d001e241880680d5500e8000a01e041c00070100e110b10801704107442d40c3c5441c4c0224a5507a04140320362403a00040140310007298080b08650640343c000001699174035540b00c40e1801089200c00349481318420428841c0c0a50f031180310345001d0b110f40001034405600d00508100f40207070a10441e83d20540801040006082145480d07081a01a0030300243c46545500440e003402c0000e0403c44080396a850003004500d802115540c00c5902000740714205035107180882e0104a005441800b029204000540d60340e00c00c001115403558000d4500302907040175400501620009007490021902b0006281034a007000e00c01e01d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 158544487 1250 158543237 158543249
    0x519021c030902030f0d111e0303040f0215040801021b0c010e0112090b041a180c0922060e072c04060207170405090708070806280e041a01 61
    0x5458140d4182080d0300030a0a2a02241c040c080c1c0c1c510300b00b803040140412001501291506401e55198042d02810300044102e000c103001200803000c0140d401c00000d42c0c2e070242d40002c666a000c000b03400003804050258483c00716a0200103808907007510103401401e0140c1102c03c41d5036040c0c0c2c80c0c0b201903898040d00c00c11030340000c0848598140a40c4283c090a0040c09640c40018200d2030a480d9010a4403085409581d420f880c50784c7d1a070716104440c0919440483c6805110325000c200c0d4941d902d034008440518405d40f04100898803103100e0078014040c3d81c815115510140c4054a8000081d0040c22000f03070b414001d040e800140c043c5020308c4030814000b603007400702c1481c03030071940c3c400c07461009801611025404e022400c009092003911031401c10240102980b514644810043e00200c018150001c002007201403101280c0c01800642c0c0081c003c8a001322005010300220400c0c0c03143c034002c21020211284002640500904106d000300c0c00f4018094814119008100c0f107140c00303104032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 158545737 1250 158544487 158544523
    0x23010e010e030604030315090c0e0a060906050d0c0e12060711120a1101020c19060b0103150e1f14270c0309160308030a0b040b0f1519051902 62
    0x4e800284280e001198115080d15080541c3c1e0f21164580212642022144089400100301182a203006c421100042403280340401100c2e081c000c00a00354054038404403403c0d901c644c0d40940080c01112607101120010b072900340b4001c01d50355940d580b01000c1c0d800740c0100380301800d4603104003008910810720005440881c0c1c07604a030303070f0b10403203c6440c0d1203260203555500b032182d4082c2903802c2c01070728100103244948007008120350a10a0803901c0701054070b8181407828a4401600c080a01c0c0c24089451152401001e584e4011003044040b8101d081002c5540903002d000c103001c1c21000780d81c10056010f0303030042c40f0020940542c5101d008203141c20400712280c603000171a072041c1d40780259400420310040d1506808620840350484003d074004513070041002c01040821005441000910300c0211820700c40b020409020804043c08a016103019181c2001c1501900242000721941c59500c40982c07403401c442c20000502d250032058840d0303074003102c0f0058060041d00c00141d0481e000c050543c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 158546987 1250 158545737 158545741
    0x336030d0f20060f0a020a090302090402130501091508060408030f04030c08030403020705012604020105250b040303150828050303280e0303130203010623010e010e0306 74
    0x251600000c01a640701044010b8480d81d0701220050070651500481200030003003424009103000e000e02d402400500400d10620000200b01d600c01d1128084a4042c1e4142c0f10640311400450003c118408407120407608290000a403c1d401d40e01840c64031201c540c409000c26103d1015035141d840030744020b008e0000500201d542c00e00e1000e041d0350058400e0411040070034440d51341011540044034181d01507007143c0410006541c020301045030001e03c0041e172040b0148030312940620710740b000c0c0000e8104600404c49800e11551f0301d1400d241180c440032104032211081c03415122009040300d00301c00180c200700320904011108c0424009881080010780310004120207107d0070112001c180105502600c400c4101048051000354010000304914046030846540c00c070061121080301e10662500c3c000004868078004020b698102d40d18a01050800f1620f000003409001e840c0c200400860ba070903910035880544010103416220203884110f84103200c0401507902044010441d44c042d004000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 158548237 1250 158546987 158547013
    0x315010902131511070b03010308032404090602030a0c090806041e0c03140d0203041412100e03120a0908030a020d1b0c0c0902030106050708070501020c033603 70
    0x40d1103040c03580100c0c400d442c2e503500701c1c03d0285100010014041a00d510400b0381601040c040a00030b40113902d0002d255500d50f644100341440010030783c000c048003c50042c164070b822051211640a4000d10900150549007803200c02584140c072494160382c68030454280d0f850041120300d04440d8080080c11003996a51650001c0c060440c20481013121511b030380340001a036600403140610b0242c45600c401c46501a04686800c0511a03c1401c0d07610601040020f8084082c55460605090f01c0125007003103603901071464140c080308800c00e01800d01c2c00d098002000000a00050072084150140a4a440c81258100d60451002270000f1f02d0400c0040e0307084120341c0060040c84441040000c074401d20075103400b41030103c14000400158405101d00900c00340c841c1c95001b07085002411441c551410b071010300544680107000301100808200c0301c0a12500390305550401841505482d5030b1442c1802c0400400e01e40641003821042d820448412691030341300030940c9a030040d00428070100201 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 158549487 1250 158548237 158548241
    0x1403070b040e100302130603020102010506030a0506070c140706020c09180607050906091002011d0118020d1b091d0307050706050310081002030601030b0319020607140a1a0603150109 80
    0x5003400303440c1c14040703c0040180c44030800356111066a5800203500380c10b5200080c25100080d054620076400644548081180410301d2500510301381054140e1030308a2605118800910803500362501842c80b000a100750081180c0a0071a801c44440955035102d040c2c10024410588001d942944044002011140500c0050103881d50003800d036824025150000b4a00265804600d00140d440b501083c0e11240740c42000080040180020300a041083e2418412a4910316010384285005142c18080c000b202000008800651004002d020740703401c03001c2c010b400c01c0700d409510036566107001d01800300040150b0f85660750140103000213501d85241103c030f5800151042901d007100c1c03840010700304000c018403040d8140b00800541c032403528000140881d038905601600a41007102c807a6180c0044041c18990035a040311400e4490242d42012201c119810a003076141e80326100b0810305020200305400815101c44c00500f2041e5191420302d030300d0b902c56070314160004256100500c0480c3e116 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 158550737 1250 158549487 158549491
    0x8060609092107060905070806130b060d1106070b0417030730020a032301060906080c0d0603050a05010609060602030f09030c041103010906060504050f060a0201091203061403070b040e 81
    0x140c842d0b50304019498071064100d07003900350104c400c1d61001c01e003001100d1090004507849401710f8504040b100d00d40e25160030480f0002e0069206881503913204080180c1900b01c0c00c2c589102405031622100607260049280070f0a440035156846504410b02040804070101c80c80303214160b0f602c1e0400c510141d074561961210450070000340c141840f40510903689440680450207036681d01040c0b20091048041e0340300340b68000d0032460031503540140000e0f0b4003c8070300c0e412603403186828a250781d54441090004d008400c2c05001350b905080d0004144580000c4203a021400fa0008200782a46c0300d074032100300d46140c45010056003060012000216201c070242184410107002c1e9440209180001021501ea60150764002c00000c8014007840750607108000c060002070820034505400c0c04d001680c0010860f03d650f118900004564200c0b920070340051081643c000d00358018920b0485015014142c103008070600c00741a03043e244024a40011b109085400800c2c20514060400404000321540 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 158551987 1250 158550737 158550793
    0x110c0d1d0d0f02150307020309010306080d0e090c0915180a0f050f031006090c0f0309030c0f11090a020d0e1b010807050f070804140d030e040203060109030b0f010806060909 76
    0x10054402d01307a14003c008522503085030740510390314501c80d8000f400700c4940d50400c16481c2d0000640c4a10a030700b1031580d6103409803c442c0381c1540c0d60b4003941100940300381a641038014038000480b100d03001c50400a810f134040c400e201c09042042d00d02c1400003072385042c42035000c0e640703464400304034034280140b0b01d8140180190030360b000b008624580300d00703807201980302c4110720fa5203030228200c645d0702203002880980300703240502080748240c500415800c034005020f041d40745003001500410110907600c4120b090082e2412844d45400b245007030094024520158034142824003d6034907002c04110985204044d003488215440103000440e102c8200070559428803c04011282c60f44600328040c10b5418810503046030755a007005000303040142443e200900a9140d0401ea00000b038200d190707040d0510050fa00141c4a5036620b0040347c0300521076002401c0680083d040c01501c140480b15981601c80d92000c80c1c00b1512981e0a0109011003218440c645820000c00c200d000c50404085980c2400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 158553237 1250 158551987 158551999
    0x904030e01050d1d0705100504090f02090d060c1b17030405030408120a0f030c02030313020a0f0e10050303030c030f0907030c1706070f0507060f110c0d1d0d0f02 71
    0x481c80d101142140d01300c010a0303200028660703016038003400810041010b0007017601d1810481c20510800b400310f0140d8001c4604603520341805406120b55681a58941e01008101e14100019414248010440c0440310030009909600840d8586010b8030001a60740d48441074503008500001181044d800181c8129040e0004000000b00341004211409001094040f000d568001c0c07048040e00345110080440207150a0030314105070580c0100c2a681e21500e51814210158518400034074600e030b884c0c10088124109510208403200b98502041c4601040c00b400d03188180c0390b5040650341d002c00c80355000240c10410004500740c3e52190059000304c400400c5981068407680c0e000c144200f10381299900002240d5800001001003080c603402202a080c01e4212030703110240200588501c801c09440d487d2641403441e14002c1e254050540c0842040c80d4503140c560040806454003c4c030302072107001400b6000320160414600003d051281001081070780034200c10b07600c60340300c2403100340181c3c0d102c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 158554487 1250 158553237 158553247
    0x5060f0408030403241b0f02120a05130b04121b090c0f0201140403081308131e3609020907111504080a0302160609050109031d0904030e0105 62
    0x80010000350020710711908041750b56042c0c00e64807121400d64988107803581401d11070b003200c14130526440320120700d00c1480c00c4000c40c0181d00c1c0580ca002c3d40114100c40100b00014003400c0c0580c814068040c0000711407400800a55544018541d0b0150b4080d12811650710f16400000484008801462000030101c40214540d64103160b000ca44000540c4004a400d007a07401c40b030983d080c4070398880d035404482c004c151707070500c2e403401020791800a00e02c0d5039403201c200c1c010003400992010b5440c803012511061681c40e0300c070345136800d004200c41030100707400a04010100b8908080c0380800c0011409410b00c0e80303056041c0000038400c02041c07000a0b05269030711456009a26000f02441c4694460f49400201d2514030440c6440d2044180001c2c503442180820b00000134070203000c540c032705105403402686403000f074030940d407100502c000700400f80f034034200301d00040107019040340d54002c0c040c6c2c0318141c4003032100590743c2801d044034074074540c44121040041c0c0081e002d10080c01506c1d42c10b140660400d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 158555737 1250 158554487 158554499
    0x207082d04030c05040b1207091802031e210306010c1104091a06040c0215090705030d02010e15130312020d0f0b0312090604061b060f1a01020705060405060f04 70
    0x1aa215820a94040c800f0250030f100e1410580510500750b101590203442c00c1c0b821800180d00e400305401144e20b05500c6550b02e0820041c0b10981b010001d40090a80d04181d10554030314030b00c100d17201800c80b0781c0d009400000ca4138504806d0110388010348603500618580e0751100445400180c92004c40d140310450100d4040c0d03889600c960210a403081e0801a800c101c030080300c0c42300310f800070985442103040c04540790050340d0114601c050551101c4010340b0a882d140302a41c2003036420b400198051042544260300540d05400c903094140004040d1004800d14182143c60003104881000d5125100712000c40024130802c03644083d00c00d05e02c0c0050414030b5441c0240280d80f200020100c0081d264909084140f03402d1006403135040c400c071502d9140c5907405000c241c06020f40e10034041484055803d251042401c03042c407508890348502c08118070507d00829100a1800000300e18904580c40c040a4845d4000a05242621002450703281001d10b400c080040d29889080060a00241032000107a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 158556987 1250 158555737 158555827
    0x120415091a040336150c0201030e120c100f060302010e09071713020109050603010302330a1709060708180a08040f03030f05131518030b19020708 64
    0x403401c0304140038418441d020400864600c4d80d5000341248140c0d481d601c86000341c0107101c0c1c851050742070a011500403192684c1c00d04016950000c59100c2000142d5a01c625a021540e841c0101c5101c004120f41c4240c0034088045070340a000c001e01080700c19200480d03518200808030351014151401020800b0003003030540b1509015a640760714125814024002c560304000c00b6000361806544450039036242d5000a034140e0251005040548007840b00e40b08946050721074004401501d100741603882c1100c0200038005030a00d000c59100c01c4130040030600e03564010039914015070f080c2d903803881c80d9111104000303401e00d641040741030503100b0541e4840024410402810007451142d80340740d44035281d801e001d883d00d030040d1810b030304002c0c1c10442070290600c42200784c0c0c141c542081800c14950b01040e000c0d02ea103515908107105080c44104000f00b049820201140700d5441d102d40444030100b0480890203030f0181070002480150b0902840c0c07076800d101000194181644501c0c42d044000c601c0c1c1c5a14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 158558237 1250 158556987 158557037
    0x703030b040f0e1c2309030f03030c04050f0405040b1f030f0602030f01060207030c0b03071202030a1a010c05070909080f03010305010501140a140d0c0b120415091a0403 74
    0x5600403041c00d030a104c44803194902c03461003070308150f042e640060044c0b0440100001280d103400001007031250583e101001014801c003003200c11242d490071300380c5c81c20905412610402d03114546122215080f420540075190103198808101049070b01c8104101740407134280d5005040140444000001054040c2c107401300746400b07242d005a070703802d10a5000c0d4000c04160880d0f025944011400c2001500380302c0060100c2d031403407a003a80c8a4945450031907501d403500c404540418004010701031109801e520024101c800880c0c20b0000d81040001903681c922681ca020303000c0e402c09003013001070a4054108862482c400d010040c80c00001c40c1c910780c2203400c04c0c1c01c2918a607542d44018800540c000342e012001d440111402034500340f6140288500010080e034903805544106c042a04210158104101620f82c010b105074680f46400a201c40c403000c2103c00380c54001d407031907400d060400f89104480106402035200500c0c4140c8600400d017000000d0004c03000c01114a5403808100c0102030108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 158559487 1250 158558237 158558261
    0x30a0f20090a080a08070f210f0207050a060905090a09170c0105010b0412060c0e0402040909020f09130210021504300f11120307030c1409060703030b040f 68
    0x2030321000c001c8280a041c03903964006450369400106420081040c50701a205840d901116030340c102d5032a444c1c0346104d503407038140600f88415401ca1030030030070307400c0803a9501c2d030b41c59982141c168585c0c490400004501500ca103a01143c0c060310f040c071140c2442811281d11002224002c5201c0305a5500d84d5a45500c002040414103408126500c0b1000f00f80075150041c01d54803c1c1070f0030503051042541503000c40c544001e007180c2d81e81c0780440b041405601c0c4000030f40802401152101d585a001c0c40181130700d4842248909a009074080c07891804540280c0511038418002501500d81d43c02e00c140300301e90028003402c0d8468040032011150903424910711840c400e031042405002004c401d10000c00002640d6004c07901604190040c1907131140144014506528020040c18a15403074641451008100c103c15076000200300002190503401482d0440c0080d642d4901586203075240b0140e90003a10b43d6580d2246040000e2400329209800220700b0f594010000074201c1d0083c5014011200302c40d584c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 158560737 1250 158559487 158559551
    0xf0e0a080301031709010f030f0e0f100f02130603090206040f09021207050901080a230a0b011427010e03030a0f08070302040f15051902010e01060614030a0f 69
    0x1071003002004d148070210940001038040c20319200c0030018020b400511000c1e010965202c40005402c8581e8102032200c070851000d848120244c2203460f61500c0e0840c140f4100e141c2015840b2070800540d02c01c866240300550340384400d09003480821001f034a41e806080c0c1c2c1c044c0e014440410038400040310f00340104440900181d07140295650040f91a200030b20071004c0c814240050701041c1d070004a401c0d8070103600080060a03050203241500016190200031100d1000c8000b0005810429032010075104800d8071190494943d02ca00d00c015445420300743c5407802d08450041950b443c2001d24503844d804141861224000441c0210703155030001a41d000010300001c020b544206d03004035006820085900c0c0a6103000d0510540300188145c0b40700e42c1e500c920300104d11940641c80707881500c3c3c080c801c115060900c1c80348224000e01030502000340380c1c121752818100085c00c901803481c0c6403160b2145c8522508503501c8802010051a60300e10200007035865003040103070400002240425600302c4004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 158561987 1250 158560737 158560739
    0x501110301080d03110f0909070201020d090503090a0519030b0907120602030f010b0310140d08040f08100c080606090103060509130605010503011505060f070203120c010e150a0f0e0a080301 83
    0x40102036505104001e0700c4030301704000e4030382c03240c000d20211200f01c501035420001c20748442c1c104070f0083c8070307424a0201461070481e200c006c01a02200418000070101d50345c21106880c2c4040101100c01104590142c003c903910410010b00d145501951060120083d110007555900c0290814521010b08891140d070000c02c0005180c81205110301400200c500e060541c41d003810700c203801d00c0c102c0c01071420300c074100c840d5540184d65601707211100340e274055907040d1120b03a40c3d0079018180ca5180200b600c54001e501c25240c10907003034410440708102030707924071219840e8102030200e1940080d00b0340341015142d04001c01c040e00c4a103401c07030084e00e408854210a00107400c044003221410307003242e03100386d050000080341d4070081e21485050f2603040f00e03001c0c4c0c0d92080000210b107510130040002c0d014001c502e4200c500c41d031520080d20207030203210028002c01e034001d180e503600c038180416551446140e40c40401c034159015441601c0c81120759100190041a0f03045a603c1d052600004682d003800c0000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 158563237 1250 158561987 158562013
    0x1306141003210e0f0310113708072d1404080604060209012109140a0b0708060a17070303020d05040e0f1504090f0b101809050111030108 60
    0x1195440c055071030242e92090561014010440034064040c50300c20145694050507a41d01405118628030521a0800489050740c0c513191041e00080e11042d8100c040a402c1940604511100b00001806540900c1300014090381520a010003902000030800c4e00030051a650321140301c1c5c42035600aa0585920f403145060004008004860209264501c1071204200c0c0c00c1e40001c40341d03002540400c0268480355400c00413141d0018100244010105113020f004940b074059006500d00b5005129120b060070300c0450080d40d41c102003000406403a08140000c255510514801d07800990081c4882c012550307945143c0d01415202c01c44683e5600704007010000c0580400140d1541c6e8101d0400d581403d01d400300c030480150f030060040c2d00c940c03104000650304030360000d001e0044001c01842040341e84103a0404804510305120304880b081d14490200e04580c440441c804116050340c41e020481c001c1100c64076000d4025800229200c2d0f40340d1100d6824182ca0401450180c40610020100c2e944261 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 158564487 1250 158563237 158563253
    0x7030f0b0f0a0b030c09060403080702031b0d060e0c0607110a080a030203030a0e010906110d050114100c05190b1b1905070201110610140306010602061306141003 71
    0x810703118024200c02107509403180c140302030803200e02009064030b03969807842c4400180b1880303581c0d990006002402108104c80000948450b07070003a41150325001e030740c40d00524480c966540e001d601004c1c2d0510180080c4203900401e00e80072014068030b10030120040032400030740019000f1550114425040102820194034a00081144500404014501d0b44002c3c0d101d210103040300307490980300d00030441e003402d094100c0006c2a9006104100149038a0040640c54200d46443d680144c01c0c1000042e020700f400c00c200d8800a00100750b580ea45075120401d99016101000448940c02600d40b210300c0c0094a00701075070f9540c010742090032180350400c00080249a03004a04001d00360502c200c280d400b22040884120a2143c10650740d251094001641c80c100003c007044411311900c403c11201c9040303c1c40d00012500d5000304044100f8a03a010161a217400340510b00041c0d0001000032692076a1004060341c40340503003c001411046e018820f05600030480f092410044047d0341001001221 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 158565737 1250 158564487 158564501
    0x6061413050f010e0c1216030b030114010b090112020a030e10060303020706050702130c030605041a13110708030412120504050a0206031b0309010902090c0414210607030f 75
    0xc55000c100a14040d00e48a00c2400103002e03070b5440160801c0050301440d5488200c42401c0c1e034041c0c543e10940750010140c0704000d00380000340006420154076807414141405080000442888402d00503030900605030300c03a41000308202c1c100f01107201032802550b1984001c1807204840d540c0807a000d6a5400c100d1310f440000c260003a0001c0c40c0540170004a0b80c085050740569030302d0b14046a8034440c5000082015210759040c0804610f001c003074940198041d841071007142e0701503505111110010703e80048010b810b5081a03082040c9480c1000361500c1a030000440442c40440301d0304259043d107030100310f9001140d04559a01500b0721101c19543c00141d813409217200341e0810b02003031905a841584806d46401c00074003c120100c0490511010a201403803c042c01460703180d01c074940304140340c1c0078010340749082c2e00420040c80460500c3c3c1c104c00848080c3d400040302e54110320442c1040c002c101c803269110845c1e241c01000c10464181040c030505000b00096030f40800d0100d40399101000300d42d50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 158566987 1250 158565737 158565769
    0x304030606061107150c02031c0e010507171b06010608070801120f0f030909090803010f140913030e13020d0605041b050309190b01080f0d05070210020a060614 70
    0x1084106500e507940010004107460b946050103044117034a0100b0380f20b111134100020b601d400707945440401510b840c480313450f035461940c2d0b030780d0f26490407000107403094031801350041c0544000d24210307041e200190300182200042584c4091510000002040c00c1c540203800c0000051100002e200e07255900c03810740d03405491004044201c404555407414003c925603070005110403001e21707404040c18040c039400001400c50100c103000d40c1141d03160422584d4400d00844001c00082d05022500e80c1a00095801c1c0d0032010b0840c04081d00c031130b00f1503140300c10011800c40c10041c29010115442d01c9807078210240c00a261005600d66403004008800d94603960042c0d40142d00e00402c0141544080d03e41c5040900b180c144640c0d2601d44401d07aa0410041d00790203035614810420040800ca4030107401d83c100e440040c140d400a0000d042c0030b54071440300d000501c0001d00b060010001601d015802055042c2c964011600c0030006556000c0035602c0b990301545007202d602e4004582802c0602061251004e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 158568237 1250 158566987 158566997
    0xa11010c05030f0604060e07030b18040308010e0408130e0411030d02031c09020306090604020a0e04050303060105210106030f0605010206011d04050709050c0d0b0105070f0311010207060e030403060606 88
    0x314240010300c240001800340c00c071200440c012030401c0c1c4850340b00ca4043c0269240d01000303032610b1203004d4007030700c9030a180c280a4038011000b0b540f04c6842c440300b680201da00d55a40030640c1d190540c01c1e00ba07500c020703000780d039154000c100b01c54030004690381e08001000091031140c0c10340f07094209032081c41c5850700c545000b40c1101c150002103e50100071101790003803e040e01607040342420700d0200240b40d8200020341600c540010b210018600041c400c1c8180d1007106c1c19050b0079120003240e1751001003500c000389154014008035440d903000d14041c00038180c40340d00e001c6100b00c00803400e007501d50081c5c0c00003000c60f69034051a0014116401a000900001e0009201e55450002c11211902d00d164026003819206404141042000d101d6100102141807041c405410108070340c551a5000403100400a440c2c10310380d89a0f540101c05407a840c58128a01c14108402a00c052f070b12005001c1c1800c8140d582000b811001544502c550a0011056002540c9640c11071800030211510768100340c081c09 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 158569487 1250 158568237 158568251
    0x1101050a080a0519050c030a114f060801060e0f0609010512012403050403050307080601110f1b010c1e05102301060302030c04051905030604080a1101 66
    0x65001800301c0d4104140030030004460352800c804a50604100750703c4090036080030103000c24003d03150042c50090b03210380c00820803410101821840c601c03554000340c08194580b2003900d41c115034001c82e858246c140c003000055007000c4101c220700b400e60001c2c14609009410000303020440d0b119407910b001d807000e410030700509680b040014003003a10b44145c1500c1818000b4103540c017648603009481074041d900800c0c2a140d40c50b4a8440b842002c2a01c01d00d100200c5849000c01d298031a00500e405207405441e20b40c503545500104680b0030000601760b60620900207c5070343c83c1041001ba1114081c0e40b070014004540c1c40c2c040004600340004d60703160422504c00041e101107000b0741d08000110740c041c040715028080034074015090080078541503130314074a46034400400d50b54801c0c15003144069040444c055a80360030040d0124041610460180001440280300d00d042c0034003184942e2607800410011207541c2c40000380f9101d4115801c03503181c0700104510b11600d4100440081c00c00440000784160303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 158570737 1250 158569487 158569507
    0x301060528241d1005090f030601080d020c0301140c030414060403033e092d01080f0f0a0c110111090a0909151e0603030c110105 57
    0x103581e254000701d00d000100c81810584808042021000744400728180a0416050807110104280400b501e40400e005058100c40741015407038060031110004c20501010814640031a6140c0010a5581e00002986210764403a44d00b044124001d04000c801800002104030000b405c2c00c0b010700c25207019078100760703082078108000801c40390f0081380c41900d551260390f030703007402c0841d01012602220310f4000c1d1000d0005055058000103c000200c40c0c0c2d1034036400d002d2541000240034a100311a107041042254806208800300814040a0041450b4a0f0100c4c2c804c2c1c0324003540d001c1c20112100610145000001e50300400f00650140d581d1510505510300504d409401e444024400e51130140e580d0040d40001d409031100044a881680080115007841240070714254845180c041c8241c1a1180000e0720b000342e40114543e00383c0c42807900c414841499a098060040084d80c0b8968010a042d6003410b00707941c0c0300d542d000f503019680d0040350112900341030341c6124401010a04100007005148c0c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 158571987 1250 158570737 158570749
    0xc0603060111150c0306120c031f060503060a05060f0a0b0a0309061d0a052e0203040215030f0106090501110c010c02030c0315010e0a09020307180f020c011a03010605 73
    0x200c04800c0c20025664108062510f0030144105010000c0340064070600402140306409984180c00540b20f01c005e08030080075481d9107505509085a1551260852030407080e10415600d00c49200c0c440e000c070f0a01c0e12000040d0503c14100c442c5150583e0310f0b000c200b2103140605580440c0728007a92203c401c6c0b800e03c04182082d10079581d40700700b459100c800348810005540c3c0035045400000c0712058000c0350788008241c403500341d060140ca2600c41c410303043d11140030380c00103a441d0b441e40204904111002d44604000b0b5003004000340c1c0c1c08801d01000f03088401d0050000c6d4404c40b051225044690304010015001711801e80006040040301440301030040c0b8005140d000c190b009080058004c5003070f2000074076103000145415018050503200040c4a03603000005810380780c00110141155848030720a800b128030380840070b1b61603448080100070a00744210740342d10f00078600e000496050681c40c1070505a03407000c109150300340e558000b03030b18022101c0612440280c0c421002804013510f440c0010349 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 158573237 1250 158571987 158571991
    0xb040c051602031e010e100509030a030911030d0504030611090609040213090213030506090f060f0919140c22020c01020d05070c05100507080106050c030912070501110c0603 76
    0x410740d02190001995020082e1504400c0c0c044504e001d500000e8940501901043c0c00828081c460340b15040c480040b00c0c0500c503c9500e002005609001344040228058071108000341c44200c0c001e08806140c2e2010303c210108043c058482590b11031561800408031800c1d0100f46526400c1480602e0050b500d4104442e14080121009a120079608220012900440d4880032040703100003010030405004031900012039000f1815038000399641004c4035100c1c1406c3d080499290001c2000900303056400801a42100c058811500c1510f401c0d030340e00e0f0001510000a0351112800124110300110030045050703280820745184541c0031882d0411446e42c0c2c2031f0100890300580104410030401c100354182d641781e0754082c1c0c00344502c3c10403031009031801d4001c07030095806000321140a00010200e0091ba8007550307003903071065483ea10340401140d42ea0407161201016000400440740a075070b41900d8a904142c6600150410b1880c1a0000d04030b8042c0300841c20040d0450a640e110560b01c05003a41c1d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 158574487 1250 158573237 158573257
    0x4050109050d080d09110312040e2d0c04141f0f0203072f2e09030f0b010f080705030a080304060b09010303030603020907050301210203101a040b040c05 67
    0x342c0c51481860002280e01900c8031034880d0519014031070f41406001d001d020101c00c03040d0140c03052100d40c0200d00780b21340700700e001e866501003c50000c504420704061b800485880e02001c0403900c0d500c00103080001d841d003550f14040e8100702160a0110142c16414001180c0b8210360791002000310103582c074450360141000303005020301442e503491200c5c000e10413210165030100030410810181c0e9122900f40441000d501515405100e001203142012412500e1080e8142d44032040d02d06203c41002d40002c3d00001e01b010401c1c030300c8000000401c03040c030206686115135095040341d8107102c2e003600e072450140e00080c1c031903004100801940c0c80100e5103240c0c0941000003169680c1e9035052a002416a202c116504009460000414158580d0040c005d503442183e62900c00c1d212031000303e456000c2805240303d03c80c0181c01c0b8014410354415450381027440901516844505a20900c040b24092140b0030b24542c5403800140c0c080c64075114020301d6003070486081000c29a000300040480c0a42c5241d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 158575737 1250 158574487 158574499
    0x30402100c02130c020106080708160b0304170c010906020a020f06070813080d060510020307050c191502011113050f040501060e1327061406100e0a050a150f050405010905 75
    0x1013416900c04c0d00841c01500d0102c1c00c0315a8180e540103129522580e02d01c84071140b030711010340410680c500c003017101d014079004090054103080d09031650089a000c202221855075032052580006001d80c005008076200d113801400310680f0200c6c1441c00c000d8001c5c04503040013049800c01c0400103c185a50001940200401d0b40380c00311a11003100402c0240c1250b5030003400303000c65040c8640e00200800066200788240c48004904005000e00409407404414001c080c1d1081481600120119480f150031184004294003001c256425802d0b4004607038440b410340e00b0141402241003089807000b41c4082034800b0011585130034401410301c482c195800f48a201c00c000d0f981c04058064100c100c641094100884000c0000201c00510300103541c0d00b1502030b820031403440348820107050340520036800074000071115203603540104c43e080300755850a80e00c00445c6c040071031b83d070b02c0e02005503000e4600341c003900c002c141c407140010309220041401c03a010401b04100c00d10850347c1c410303c1e42044441c19608 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 158576987 1250 158575737 158575751
    0x90916021902010c0f060203010f0e0c070210020a0614161103040501030b010909060e160216091112010b071b1215110c0a0312090b18030708040902030402100c0213 72
    0x48800b42c02091010b400760590040c5c0400b809016801117040f58820140d6031340b110f95a140050300341600301d0303c0c405c0d003003414040310001d814190400a00180305105071004c80c1c50550b5041c007115004000500602000000c0164000340030140910065080c200000d0941c3c8102259559208a0080342d040507100c0640b0485a4011070040740034182c0d03000203015030790300c618400c4c08842c4125085902c16851000b04002075002190103d114000c4507046ca40c0b007400d2106840142501008123994290100160b074a5503144500700e9001e4544070348602c0d903902340c4e402c0413503144850507400403035078907030207410040841484460340c03010b0303444004510a804245811130080510460b446030f0b44000040c00600443d01140802e00c42d480303038598481a03040b25250008403546904010080ba401e000031415185141d0f440c1c0400b907242c4800c6918006507607030b070016a600a9406060341907008014401140382801d45c09540e50080c0c500700340081c02035000554000da1014160440c5c90303035240 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 158578237 1250 158576987 158576989
    0x1090c0b0f18150a080a0b010807020a110a0b0a0e09010501050c03070f05030f070302010b090a15090906061d070e4c0c02030114070e120c04060605090916021902 71
    0x1255000300035100c2050342c1350244110043e08041c3c0c1143c1d042065458103042d01c0350396018034180d60064800b58020020765200f6035500006400c00400d465000c90040b000042944400713000700384110159860b00300f000c1c404c1d014041c3c0c4810680066050113418810760b18510000001d0700d00c0c40e03401c021b060302c100715241001425442010512081c00d00d001502000381601500038141c08a0165031301d4015545040110080f184100342410300c500d01900c040044e002c907900110340c1140a4480012001d81e618100628641555140407120720700340c081091064010045c200711a8007a42c2607081020402406200c4400c44000304a80507204070811000040801c0d04903171000007076005642014510801800c801c420f420b08030700c69802d280c40c500c0e1408901504a0143e0f60301e8a6070080c0d028404100215120040202c00540c41003074100155a56140540c030010301082d05c500da91002e00d8020b001440c0c4004250005040e01e0702230300280b16030b002458114510f0000e0b0b4441741e00d03000b84 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 158579487 1250 158578237 158578249
    0xc0f0a0c02040f1a1f0c15020315010210061505070f0b0f06030f030711060306060f030a0b12060601091e0b03090607080f0c070803100902070501090c0b0f18 69
    0x4000a50083d142c81c0d691080d040841e0b01803543c1c5200500003402e96a0008100120740410405081c0c2800c3c002d01d9501e000c40c0100306512055105650600810468954500480e041201d0210070024040420300c042d503010700010725034034a210801d000b22400d2111180b46400428191810010000f58100c24014100c40c9445031503807088410640342002c078440707a000001600c20a00c00e0184005402d21020004102c801c140e41c4448031034203445440f800c102890704002c28044d003064041241c00003e010300d02c019845803641d45000980d0381e0b0a4001d0046454059040e41c905038002d00903c1842e030f0300b10802108840c002c03109002003803000c148004000480d42c0c030040210380c0100910103c1c0b117011600c0f0788039400c6542e80e20440e58603602005c505180640c0c011400710302c2042000c0c04141144000c5030301142c06c07890098421741e140071141c1260b0000c5801d445503503413003954408100d4800f41c0000101007156481c0d06220724102d03021028440e64146200d0b540d04150750000c1c60300d0304 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 158580737 1250 158579487 158579507
    0x70b060406050622050a0f051c050f0a0c0b0315130b040c0306030b0f0403090e10150f080a0c0504052704030c120f05030a02132c0109050c0f0a 63
    0x90945030302c0c2d070b00740380ea00070303c0380c0710018500a42401130300e0118590a04a555a088816000c01490b401d1314040901410440401d03071080c08601814912000c00c00412900b411401544000c126400c1c150a0080c450301c1c1581001218160400501100308038812400c080b040c002c5600f086075a001d1900300c00145018240d0381d802a042140841ea4650194840001c80b409a5160300c02a910502e196820040448008020500b1030405001e203282c903010051740308820103146100f1549900402400c102414100c00000e800040c503030644c2c5510240c0207811010303080c070900c0303a00f64585001c0c0160249005850080c48140055880c0070700707001000c40f401d01150000201401e042c180185042180001611066a40e01d40003a42901c11103104400181698480703041d80c031580128006944150b80040450004400120389800c07681451b52200203d9021038054100141541c942110144d0100d103001e45014100110743d140f0200f210b04004500d403120343e41d10150301080d02c000f182 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 158581987 1250 158580737 158580739
    0xb0904080307111015050f10050720040f0617070320030703080a11071a030a0207230d020106050a05150a020313080106030204050a05040f2301140115090605070b06040605 75
    0x10500310701c0c40e0817010710400701550025105818803c0c0e4113402d000d100d111710000c0c1d83c0010400c00a00001c1000d808801100942003030510044c0c02620001409031000d00d1040040340c1d41c2c4401c2040300c0040c101c11080c0d100c400302d000d005110b1075a203a038040751800c03011242080e1382d0070004001c00e0ba01480b10030051a0b000c22419210700e5240c0c40102030407000080c9110502c100800443d0400d00c0d04108040b55030400010342c07644d528400030030081d410000302210740c2c46608200c0540b020441990a10100c040300c014540501da6841c001c5c2520138643c40076010700c4491405201d180c4445200403094841d40301c4450303648200304c0049241d880b44030360603c0e003801c3c20340e00460004410740003001101d0080743c040c0b02a0f100d034000c2508690043c0c1e0001d284058007500b6000141950301100810001e0340303079a071241c04d100c1d40b0280c01d4500c1400d4104c01d4540c03803401800a030540c00a44e404008041c40c0500d091824400080c115100380c11015065503001400070f88584d0f129000030000e090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 158583237 1250 158581987 158581991
    0xa0201050a021002040e060901080a110f01030603060c020a0b0c0c0304050411040e010611010515030307030c03030e0706050c01050108060606070605060a0f06052d09040515060c030304060b09040803071110 90
    0x546c0d03204003c0c04404c1641d003288030b02121310002810a0000820f04801c58020200d01c9044064408000248241940d201d06041c2c0b41c44000ac08249184a03202c00b0710002d4010304460300451905100c4094000c00e02d8888200c1404031060000c800801d85080c1c4205840000c0d00c02e81601c0d94403000e00650744010b008410742c000215040c4d034800122400445480004e00c807a450719242d41650003070a1410603050b520030f000b1280807a204402071115180242800580358000d401c4281c141145030b000035001c10700010702c0c410094005d200c0c042c010030200c030141c206420b10700006441442142c802034001501d03030022902036074880b80210010003407030030024102682d40750302030025044164105e400020250101c00c4002440110342e40183c00703100e003140307403840c1181003100030a4007600d80060000155006072041d00c0c0d01c0024103c071070300c0c8802144c0301c0c9820314109058500c4517250300d0146610b1024480041c0100c070580380c00080c2402d0104441390a610114038280540207010303c854 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 158584487 1250 158583237 158583239
    0x1b030f021e0d0e010902100c03090e01080a031b0c050909030d0f0c030506040605100c060e0102040620031303080c1c050a030c050c0307170d0c050301060e0d02030a0201050a02100204 80
    0x203031540020704240342000010b0209001c2c3d81802e5080791140c0201a40040d4540d10350704400b0322842810307101c1482803c0800e181502c0310010300c1d4500098101200542c0103031240818141c200080628807440d4200d40d0070a600281d580d045120b01601c61103000341654004500111010301c1500d00f5441c408104002400040400501900b1403402c944c020914000c0452214140341c0904d1040d500090840c0c4031490a104d804c80d10810850b9043e20140d0307660f18484560402800208010145642c450100d1240804404114100205914800c6d4000c06c05c1a61003079802110600b16604200c015840741002c6030620b0800d0190074100340c20030601804002840d420a01625070401c0b141d504002c051655002078500e840352440d15a07541d84140a200002032010210a070034140c111007842c00d02c00c01c0300f40b08054548409421001c10f0340400103001103988800450202c61080b200255003040e99004252140c0100401904206000400c1d00b100c6008200700c0d0302d0340c40b40c0c4d44119a26 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 158585737 1250 158584487 158584537
    0x150e0a0503120114030f060424140403091512020f090405130615060206060f031507020307110904110d0c0b0d090c0e1603050402010215010e07121b030f02 68
    0x68042402450b405070f130384844080301400c0004d114220b2041d02002003c541c1c507a62140b008034905c01e03042c0079100b0303038440131281c1403000c0d800f8041140445c15140701050038940360141281203550084102d0745140c454906005501c0310401c0c525082002c80181c0e03a000040345e0500d1403017070100c026002030425050010b81c5400c10581c1c8002c03405a5820854441442404202e51100d0b100e640c0c0180d10800c00301394180b07802041c4101180e401021581c507030130324040640300e0080840311100941c00c086103540500540c5240440e92840031505442a4a803076524240854044003a045c0550003280c000001c121140f5580d0028101d022602e0751070707403d40484000a0f10350840101c40c2480400000241c02c0c0744402d005000d00c91040b52030100801c00c8108800070007000340140c1c110700c142d0804400c640f040b890361901a103404001e130f0126180111024059a0080b0410100c480c9404000700c1100c06006a807280d07040705103008034412078800008000b03400b4100440c0100320701a14140c0007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 158586987 1250 158585737 158585767
    0x20304350f03090f07050a170703060c1706010c151a03010f020705160605040b0c010204050d03030b1008090607110109081204031d09130f0501050f0105010e0303030103150e0a0503 79
    0x4240303154002c03909000000c120700c80d05c0d16950b20a060b04441c882109008030410000148841d103414001c80760b03081e0340c07525800140d038485003141001c03c00030104452030a403032409040e4891001e090000004285994035500c01400050901e043e030b80c5c0c3c80110091100740440b0b0501d00100400034807044c070b00c20a8000c002d503c0880122050b05c64081804030305203200d103071082281c00303d4070380e0781c141403400c0229003403a0700100c02c050b00741d58204400714095503101c0b0320703507042c5010780c2c1c3c00035550f48000103004078045400010818400140e0401410141c00500e00d5804000c0e864041c0700301c40c1a0083d140502001d00703004109000106600d03d0007000c11100b103101e01d0190380c0c0d4040c0d1020080c1c0092540d00904007042d0811b461000043c4910841001c41c41d11612502065110285940303501d805c40e4000d0300c00756411100540104004d40e8480d15070724240c207085001c2c518551441d951020340000e80b0200804664850707900740401102800400025500801a2551680c0f15001c0d490 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 158588237 1250 158586987 158586991
    0x306013b0712090c0621110315060c06010603060f080a1101110c0a0306020a0e0907140f090603040b01033f110f0f0601061e03110d0608010605100201020304350f03 72
    0x5912207500710a00604002c1c0e005220103141c00c4200923103107440c0c0c10820010500202c2c0c1c490741210342003004d0100c22200f0010b0a000f050b0030390f0002200c9041403000d8548000b5a03204c8640d0b1f43c00300f660040410340c060515200303c0801d0034500c40d5064030092003070409440ca2100c6d03901603601c4c040001401103540082c100b80445079280ca8021010604101c00d448040e244500010309a00301001a040c000000340764020088404034184400c8100007102a80b0448048590450780001082040514400c82c400351401b029906050007480c60703003020001b054900403a004c2090300c42d0000c5c0500510940803100c110500352624044010320329541c5405107040d1403202d02c80c8900014460b40310b45150907103905100503003c94022440d004030007810b01c400001c00d951008005a201c1e802e03440c401d00000b0603840740041001c528000030014031100b042c80034401d590040081100180303030f2010b58221001e0300ba2040d44d002c1d05280640304c0340b260741440c4c0c0f448020700084010050b0700075030241d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 158589487 1250 158588237 158588267
    0x150f1305061c030c3011070e040f03020f0102040b090402070620120615030a020a090902040602010e1005010803190c0506040b0f0714041a07020306013b0712090c06 72
    0x144411102c81c40c005c1883d64603801c91100a156940c1c03500303465100d00317100800c0c602601d08688140ba00c0b5491042e100078260350032140203240c0c0644034101501800286664032541008500701881c000c40050940300c2c40300303c41e11441c2d00048490400032543e1003c075000c80f02c19881c1050480b03040036134220b64490403a0300010b111040c0001d419280070a081941501c50300b26031803c42c0c030b602411101940003003102400b40821036001050081c451f2020700300500c06a400403c0002100c1d1075a03080a40c2081c0c01c0760f030b440c10300005000c0b80c200041201c04842c900b96a415124081d1380c002c403000c00300c2200092950050609100500c082060620300071484941017003078640307507524180c41c071500b141c03a0304840a80500c401c000c2d00303039050410034215034604002854000d0607400a418480309030021049840d92082d6064070f003c03804c440900b01e031404500200540510f030303034401d00144018101c00804c01d8002d40382206100356003107600c8456101401900890b183e0300c0140000155072424 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 158590737 1250 158589487 158589503
    0x40b0906090304031104050603240123030309010e0109090204030b15010f080115020703141006210605070c061a03010c26040501090c0e150f1305061c030c 68
    0x7245a030040842200d00301c1e42d00a98551001300807005110241c94000c0c40d00340d0500a007101d800c012034040710124084141e6041d685120740c1041c0c41c0415501600207189082da00030100d100b070644002040390101103003420092024010000102c6050303003250052002240041000000c001c8141186402400d00f401c9000070540910011144107098404100000300d150004100320100c07818580110790fa544181e505041d2070b0340b103120340701d422803600d0505a406002c80c503d42070440e10070304005e488455041403070400f40c0034403000b0300c003501c0c0300140a10740c0c3e500101d0881400391403210907a41c0c0c0603009110341c0c034003c40c3c0207041d80c0991505c1e0303020b9400c10070034201c12071040d240c45202840040114445100090b0040d41d030792401003040311290b603604420b030041051503241500400b40d115090107945441d418074028400c08201d442d003c1e41c410b4081506643c1c9074120101180c11140d00025199692800100840d250548800c100c070a8007104100703041e48003200480041c050421 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 158591987 1250 158590737 158590741
    0x507080d0c0302070e131101200601050414090a06020a0c021c02010305060406051c080f041203171504050406090b1608010503060106081902041a0c100e1c110105040b0906 75
    0x301e030075881c21a10200d0200041003507030300140700007c0402c0a4441031500c041d40c02c0c01c000401c1c07041c00740803991003071a5001800411442c070707042c000c10380700014003c1442005e0411003110359850f24650380061000340c0204903105958030420420480940040905107c694602c0e415030090000c1030059001a0400000401a08260150900703d9401900c1481461808414280d0301c4401003c00c8580c8a01001000f82c3c00410174041c101400c000700068855204614010b0000841000750414400c6407031304020341310100c4418591075950071303180451030b41c1da686000401040c0113880200305806103c1803107000b64040c44c103485002065261000d043e6201c40415503101c500b40301d001c001907281c5e000201d810f150b284250401c2448500050705080c2c40f204541d000d400540085c0344100c7d0081200d0001c440200114800c0508054080040da850810785549504d011800c550080e010030618140f0244036240e0040381c1041c0c103000b04003a09003071408a4440106850001c40703880f40b900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 158593237 1250 158591987 158591999
    0x308090105090606031f14010305011d0606010e01031a0d0503030601021006030807060b21030706050a0c090b1c0f0c23040306050c0f0d090201080a06050d0b040507080d0c030207 78
    0x3c090f40161001401003880040480c2c294048002261141c1911070300d40c00003980b10361100420358042e5100e000003240ca014104104103030124800c81d03400480d4070103c14401180d80201e8071b50943c3c442840d011410141c0c41c00c0c4d4420051591914036003107461031080105000011010b580500403da0130340b0712f2503041c4c8500360107840081c040a00003607800c01c02d06001030a540e0011061000c050300040d40380d43c1c40001c031301d0199a480d4009000360000100302080103202d208881d441100540c1c100280d0400d00c4006220000b14000d5000c040000581d114040c80300305051220025003c806000c0c03510319182e038402401c24041c000c00400c1000344410f01c01010345c210704954843c070242d03071400c0500c0c540f00c1c0c0d405801d000e80b490705011410404842d100e4007441c010054050a0790003c40c0c44151403000500d0007500800141c4060b1074000280259560751a00f11083c941009041c040c903211403c040e802c0c14850b50103460203114a0440613402c581000444811501a13003c5d107000383c0e5200307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 158594487 1250 158593237 158593243
    0xb09092508010e0619090510030c0f140414060906030111070c03020306070f081906030c140a21060e07080a03020f012406030c020106050910181407081e04030809010509 74
    0x90903440307a5424202e03013800011b0707150340180d038402c001040503441c550b40d944074094000f21581090b098400c03c548140900001c80610380381f4000306880c200100d036108541d80e544030780040c00395032180c206100811910b99094010303c0c0518800c01030710b0b98400903441c2100d034107030441c8022406070140e4800929810b02911603080300d0103d40d180e00700c90340d8484800c2300702800d9030a10550015515100800800e10340d03164400034008042e0803101d48040d074800c110303014a16510180c011078104013002c041b0b44804401079801540158040f070398070003030b410050410055400041c403502c80c00261100785640096801c40150b5000000c2182d00031904540003c070058101610400d0202482040114840c1c0e000c0e030340d0341e403540c40006a00f83d29078001400b8a0b006075405803030300a400d0300600444000001d04040100141d400700400319032240e9200444c40b005080009100c1d40d480081c40c00e09907846540c1e220351010180b469546003034940605800340c1900d41c40391940c43c00700080d101d18000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 158595737 1250 158594487 158594509
    0x2010f0509160909120807110a030f02060612031909030206130e15010e0f1305070905190f03030c0c0e0a1d0d020c04050901020c190605060a0b09092508010e06 70
    0x601c0c00c005c1e020340d0b0070039542c1079006802602003180031000c0b1503402c0c1d002e100b0b88004501c03d0713492038070351320400d20f0083c07504501400302031007940ca0240d103445610b400001c030703240100ca048440003245207049040c6c0e0740041c0d540c070103900404001110b248006034541c08800341d8620b44840c46264660030b40c0e4000300641d400309140800c0402101116074038003844111007d10b0002d018407101c02d036070b441c06002d844c0182c078003801050080805101514181702c403c0003040440405e110f80da440c01510b44150783d414813010701030088100c1c4100500c00d0b1180c0c1c10000d482e8002e000d48442c02c0280403a001440700c0d25500300c04d10404a60054000008074400e003410066038001c01d0809000e2041000800020340151034540d82001000aa154103010401e05680030402c81031030040c441c01c00d5003d403000201703074500c0380c042c150050203004020001d0354400782061324a6042544c030044c40b09001c000b01258460008000c45824104503030000314241aa0001d00b80302d403154540c081400420f49103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 158596987 1250 158595737 158595743
    0x406031d030f090d050a03031d0f0304050f040b151c02070203030a1d120f07060807230f042403020c03070201030906110f04060801051005071202010f0509160909 71
    0x708110001038900c42d00080d003418100142208180c0840745c1d501d500d0401c50060071000f098a6a145800d0a2100598040070303100c808040c28002c02181e207007607181c0c8540d0150b54072810548100200c503031981e81c071161628001034036141d1034018a86000c4030b0754101465070703180e981c419049441001114001e86946650190041d420980e40981c02d442150701c52812003885090480500126a20b04103140c1500e08444041c2c081800c03140c081c1414542142c20240c00e000b075620500c108254003c900c0415080f010f60000500e404038140340d41170303200e550742908580c000454049070a0982140d0307100d031961802d00320036103182d0206040d81a40500680b009068105115000265009402411441e40b24400018001c81c002100350b8540d00706403108012500b001c00c05000d41e680020405003d000b0840324440306e5045030a00802c2445614001040a510351003074412660003500080242103503440c0501c22454480303001c03503580c01c40084822101288a0002401d40c8a6104000185d50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 158598237 1250 158596987 158596993
    0x90212010506030703110a0903030806060703020d0804052109030c090709050402090d14030901110a050607050d180602210c071403040801050403030b2107060e04021605030406031d 79
    0x1c41c050402c0042e4100400c41c0051688510038040880c00742001020504c034540c43e01600c10b070039402c000b02400d400608440c003409003000180040303900011380880074026490f190503c0da485c0d2500ca41880d465404280940140c481e00410b091030090240c44400400d03000c503100c99840c0e0b0104040380b03109850303c1c404151501011300290a0940040114460141840001910750781d25402070042d102d0844c03c1d10b401c0800c1c2d2140540e4040d1810700c1214220000300100d40098072540d4840700c020307200406002002517880052900d03a0840207a501c8d212621742d0941c0141e0600c40d02a51050038001900c1841d02007151808140c42c84a81c0103c0c0d1291800d42000025600c0c1e1481004000645400d0301c01400000354003c024011140310300d01c03958011400301c10003810b00c000d900700810040c980b40d20208402c0f4031290005038001c103d400718a89103140e030081c000420001c0c400c80c0074904030003c000f42da40040c460008028012a111035400300044050740c850740004c2d00c803084c20052150 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 158599487 1250 158598237 158598239
    0x516181401020307050609030901031401032d0b090c03060702011103040f030309151e0506011d0f18090f0d2102040e040506090c010509010e011b06060e1009021201 72
    0x490452004446800180110f919000c00c40d201d40d8a0101d044035690081e42c0005400085540c0c14000c2c410024a04211084a941903035038080b0101507001d659040c1d00061b00404154807810000c5d815195004001e80d41d00d0b051034512142c8ac1c6440070f9105001e4440e600104108034414401c418103901440001421501c49503a01844c40520300c00a508150f01c07540d145002c1400e014801d1484904500c00182020440c40581147c0001501a00106141a04102031a41c02210b036801d82e402c002400c07001501c01c8000103511410034203000d504203007038500e4040c10401002c54180140200e1080313800d404000305005542d40000400b038800a8218800c41042d00b0898103807011202110b00301605180d1a82d40700440e070101220700740e82c0d542c40b40080c40304054082c072501009020a2030024070340484100041d00d200740c45940e280c10425415240406a68040600041c21754007400c00d01c6090703034840035180c412000b600e4600030400702100c00150b403081c030310071654040031404403400c050b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 158600737 1250 158599487 158599499
    0x52505030d080a0603170d0c0e090c0c0a0c0602010c030609060308040519120f021c02090105060d0605040c02031b0f0a06051801090803011e0e0402121609051618 71
    0x80b4502400d01d9000130f4071214080002201c07510460303c084000005151a80d0042480c0025505851098010310034030038520300268980c55201d680c4001265100d83e540c11003d45600e00e0004003000150004248a10101c4d0841d41900080b414200958081c04510340b550002d0741110361912008144c041c00304410061400e05a50018580a480c8c480114282d564910356106000c5003e080305c444118518810451070081038105202d41ea900544103846e2041c0d01188442d001801103074460140842c000d40989842d42081c0b000d00b401410a004a40d010000a50380390003240c0322440a0740c942400403001d40000440d603d03050b10041c000c190464554503024014180603183e01c8602500c0c0320703122520002409001d4600e4468a00b156507589002c0b181c0250780d400300202050f44040309410010b001c80c8440260704a0b80448425103036050700342a10303145c10119505e101051043d00400510300c4101d6018603c0340354000c1c03214201c1c511180045601880002d40030140e4080120180302e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 158601987 1250 158600737 158600747
    0x50603010f05090c130b070204111e1c0212010504060803071502090a0e07120b1504090209030a1a06030606100818100603050f0c01020c1309060906050103052505030d 73
    0x100490311301151a041c442d01c1c406040c0706403500007400c3e2100001d07400341103013403d1191001e088205017005042940040030340d6aa10399441c008a8030400210744006000d800145484480e401c09104550714000c1d280761000d4140b00740704640c85149440400103180101104544000340d2101880480b0003042d041480250003941800741c001d07140742c5022a1841180112500400c140d031200e10010400404420640700600744d40b0b401403001482000181152109450584610716409612540c401011910b81888504080d041010244500600402d454031440c0900000c1c1c1c196007040c2d840c6028069810380107005000040d4011001030012901070323101c942d0240080080c0c41c2d0300c2c00384440600982d0255001503606820042110102c0c0700300308011000c07502e080c000b900310364800303030005520303408001ca002d02d80d40d848100105c104082076020800c0240e01c20010805561a070a000e41c2e9035003800c00400c2d541c0e40880d000d401021800200c00105e4030024020701c20b076501424101c45c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 158603237 1250 158601987 158601991
    0x4060c140a1407140102121b1e090301090c0e010b0319020a12021b0f060c03010b0f07020303040e0103050c121b0d0b01030b1006050309031204031b0606050a050603010f0509 76
    0x54000c10074403c8a00040700000c00c000e4280807040050388a40c0d11440a8441c00f41c0640740c80c0e02ca801d4070348071914141904003078400052000000302180f40005a04240e5481072400480c0d047d482d1074100340410004c090f04100b9038981800751071040e80c031181448a07a100680c0c01840c240c411034824010400c080d0010032041c4007034504004400c07002e21421050380c0106801088107a08020f4041040c4401c0000c000c0806051004140500b0076401c2c044183c4018007450020070000248a4200e40c0854201e550265000d0200c03580d45a86002c200c80440080c00100c0301c41c061a01c04003214900b0840e003c02c0d50203008082c24828100c41e400440f000ea41845950304940015606d4001c14005040c0318003d60181441c00014a00304d1102c00d01101240c10460a018040c401d110a030000002659024030020205010549603400c050310320041c07040185060170616a00b440401015800420031600155100d4004544800411000b40024010510f030a41241d9080249180c48000d4903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 158604487 1250 158603237 158603267
    0x506090f0301090f031110090210050a1b06020a0836071205010207050712050604020f060913060f0f03030e0607080f0c0703031404050d0b0405031b0604060c140a 71
    0x1940d28903a500e50740c054140500517004200718242884082d00705010b4009801d613070b008108400421a40014103a2a2400780003003000b4020030409140d5008200340d5140051044840d2140351035460703c036019500214070340c80090040001700722203400d101d0131444030300a1108898120740c002405020410804861086144038210f000525215078180c05000c150080c1c0015989040e1405d1062804c0090b90180034502250070945d00032031b1300441e0b1284c00660450b840311080740ca03500041c0a03401545805030740052403d81c24100480150302c1702c2c0031690f40080c4280d61960761401c25001c25840e00c0040c0c0410740962111100e031030160020290030f4030800d071003400e000d014000d10f1050f40000080c0c2805134821801807040c5600019a0040060404505803510b41060049110321840f200001c03c0494050007007000c0100900503500c8001d40c103150b074101101100c4c0220b546142c2650240c1702c107407500b181c046080e407141010019864482000c5840c0c6010b03e5808c4900380385412800c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 158605737 1250 158604487 158604491
    0x3020f1e040606030204090501060806010816170708040203070819060b030a050102070f03020105011e0504091a071d03150712060b070f0b1f05060a0210051008060a060506090f0301 79
    0x1600303075502c0c0700314405070400341e40060704c0d1410000d01608940c0f040e0407517814040b00d07004000c0d0b40e80e4445107181d8040c0806600b0303902000c802c1c1040c0e941c101d10b015162000e114000800401e02d43c80704030507100c1e0340202d0840c2c8034036580d090b4098031001002e50303c00c002c0450042e040c0c0800c801d80c2124589000290407910140350a440703407401ca07080280216a09603210511105040d42406194054000b0607000300781541c41034024040c8816511074640510344a41c0e0900501c1203041070703084400d00040c00b210315807802000041914040c000c1221100b044c440c682d103190b040c0007481c0b50381002224903041080c1c640c0c000c2903511340100074864024a440d22400301d0801c0c1d0f074501500c1004d201e1015000e40340d00c4d46c6400e081d00200107120760388036201070b200b01c09c3e0803014100c0c3d082229420b8075402e59460801d1022410250201c41d0722284908110511044a010400c034401321143c0c0e5041c0c5410b43c035012400000d8802d00d02c201544140b003402803000034030301502005d82d00c1d0401000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 158606987 1250 158605737 158605789
    0x15050a020a080705010204030b01060905030a0204231017030903070e2728020a05040b010302090604030f060b090702250e090a05070b1c02130f0e0601170103020f 71
    0x507002c0150300900046a007079401260803c00c00860066841c00741425003414208241018007095690444e401e002c1d01c10341d02c030f00900303c81136016448150801a180d00151840c034201d01629200c0c9043e03c6007000b28a10600007291200d0040180c8080f2407009000d441c2240c9071509004d2550005040480e2910400010324407e8070103001424584400d803020b000d4151044e106031513018200b42082c614400115a0800107a1320401013000b030340c1c0211000500003185100490007130085074042504450001408401d02580e0986001001e200f48000e011490440c4c4c280128080c003680c4075009a030114601d800d2a1444180c80c0189403c40e003511045a03030342d407014150b00481503400c24166004032824005201c030030f214840c050069000d519180245a00207460b040d1051210400c0d1a03030f012918820140d480318102c80100110641122a2601d90047d03603464142a150103001c81c00c168940071a540001d0b03000e50403a90010710342e10314945407406008201c02c2c85580b40c50a1140049 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 158608237 1250 158606987 158606993
    0xd0204080604030804031d0603280903020f10110711060d1a011404080c091008070e0f150603040803040311070b0703031401080d0c0303141305060a0615050a020a 71
    0x1c8911480c00396450b54020b0800303043c00b5150141c0c58078140d901c0700314118001d9898a4003422250403091640d0304101c15881000407a8010f6003500c480400c5a040070615030905500040003d81703500d407074040d00c443c40c480030600d000304c4205001e14006070303005010150114008a24400c0301201c040c1402d0701d442c13a020f4448089407641081d040104460740c00000c6956440b0031500a64140c4c0c101d814a018100b645650b5070307842c01c0880070b01c650f50b9100010460b903050340e810720040c130152045401c5503480c0c042c41112034108690b0b2202550072500003510700755003007001100c6628081c02032440d40d1240c2d01e03848481c2e4030007130054080c000655844044d54804120840007050510015500e40b60a468020700782c907036520301e41c1e403807840003070051004040100300030300060f020341860545000c9618083c2c0152500119142c4441000c804000038000d81540c2039010034829000d517226959100f000002325507050207000310000785415a1001756000340020701e40e2204030300446440034041e0f030f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 158609487 1250 158608237 158608243
    0x7050709060306020322021e06160503090306160c060902060c0d090503010b030c0a0510091d0103020a0801091101050906070203061302101106071404090e0109120905060f0d020408 79
    0x703401152444d0303001040040e40d0700004211001c001c00c0a5101e01040d60940004144c0040c1c40410145441d018010120a6480c801110002c0c90507002d450b100000d07500b0801d03245e40144040d43d01902542e0700150b0001c0034080da600040c2c00c1500c4101d854036a549401c2c1c02070064000c01c07604000d007080750304542e00007006203e19203000fa56440703140070300704010b06007034a10800c6068080d03845083c8014040c0c4d01d203003042081d20000c0e1010024403055a80484000c0a1a401135030380840c800f5280b0b214000c04102e00341079a000340c4007140c035269901c0c1c40c2400ca4201a90242070110110800300c080e44c403420080c5400d541c01007140b4103184c0f03e40c001a040041c00c0e0f400c8002c00b88107481400460070441481603010340d1506002500703440c0c1d106400e03101c5100400710810420154803200042d4002c0341030320054180746404000d288400503105000700401401918050b44050700d5001107440b45000c030382070304e40282c00c040c140302d80d046803242150032420349107031031980030300002c10030350020 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 158610737 1250 158609487 158609489
    0x7050f180d0c03020118031709030a08300403360e040c080d02030304030318060c020609100203090a02060717030c040315020a0507080a020a021f02120304170705070906 74
    0x520082c00480380b40d803002501c803a4070215521030644000c1010004030721041062006c07100c094096030b0fa2200e50740e002904184408100410a40000c6101684040362584000311011200c0201c00c00c0202c20003403803902c21080320f00038000b0301100b816800b203111280e4401080004104110455004007000342944503003900300102103200700c6e003040180035241c1c1200b00104210320140c07502c1c0b028240001d459100c0104042e09158032380d0000d425003090500380072200c94100c103040004450920b0002c2d11202e050f6101c00c00fa20521040c0d0041401c01d100301ca000c0c03e004c0d001400341c030000394241701c0290000d05056428006c00b920151041480f14025031050b103045005503500c5040d0300e00844131544910350821464814003101059680040445804a0704407101540f00c200040c407c0b894011901c5c0000c0d007080e000b0341c07800c1c154590510540000f4401d80c090354a1001180d2049219000469003c0c1c03100003200c09441200c0c0b140402072444901030400c0d10880c1c2c2d02c2d0f90340c0805898407 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 158611987 1250 158610737 158610743
    0x30a060507120f090b010e130503030c04140102150106140f032a030f040b0604150603020a020106090b031e1e030a08010b070b010b09061c021e0307050f180d 69
    0x512510780c100e005080c4075070b280c0f01110a10402806401c1e45480b454114140603c1c260303a03540902107114680072682c0f42800076404801c03240e80307190030f18070100d407900148162003450300c00c0e03000b1407600c0d8008035058108103007050040180743e28020084901c20702941a80109030010402115002401030007035105800d05182859101e14030a0350350304404200a400c00d0000741803080c0041d080c1581d50154226400c0a00f00850781c40f005d0004d0010f000d0024440204081c8003400601c0c10f400da000780482a00c07a07002004050340e540411400c0c7d5072080c000b198581c00044000d98414280d81c030500400e40400115130f504030038151610030082c8038850004190713001052140b822540854000c1c09401c1268041c0d0601c22642e460900186042c012a0481000405c1900417521008150391400d1451212811000c1140d1101d0000794000b804580c40c8480b00d40004080e070a02100700c0340138402d11795806242c048895a502c4264100d100107892038444000c01d5401c07544c40c068130b070102c180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 158613237 1250 158611987 158611997
    0x250501060608060d081c0e01050f150d0218040c0e0106092c150616080c06011217300708010504110a0c0f0218010312020a0b011202030a060507 63
    0x104015020b810000b000f000c1034070410041340994000b0b1040f00070350785d1499081090000001c2050041c034040c0c18a11100070484d803900b410048100d002100480c043c1c03c1c1c0d5100c01307810b00590000d1001c5449030781c10283d009920208120040c000081e61079521601601600a1294690820a450680c00e900603000030701c1020381030020700c01e111003280708041c44203140c0040710785901d40103040d403d0040c07120380000041c284241c0c3c50b4403078600312403081c48203180201c1a042e040c40c19001640102e44d60f80d8813845a1000451442e807100601103299400840c50200b590040542c04007130f038000300c48040070600d010462160341e03141c001c10a8040e4020003081c02c80d1710302006c1c01003403a0343c146d11591043d800c0081e40000307124600c0c03c98104a45615049000d10554180003045802c001030081d00050300150208400d09041e81d09416680b1400c1d601ca0045242c10040781c0d035a006403c064840346514004200110003102d884c1252032000d4291100308030783e07444800417104115184800301d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 158614487 1250 158613237 158613239
    0x406060b0c100e03070c0b03071116060210180803040c0914060f0d0206040510050f03010b07050f0303010e012612030105100513031b0f0f060e011e030225050106 71
    0x1002c500601c0410f032070314401107040085a0300d6860002e030180c410801d900c0000808940514455a80c646800c24108101d607103d0101c1004008001c1484c842c4400501070b0150b40762002c00c05004400840c1f46030004070107800443e4989403140d5002500444806419001c000f585014600621000c0703041d0800414103031400c0410b00c20000d203000030152044120b482042c00690f5a44240d4080c2e8100340c0b4108034194014000f90780901c40c2402100c0001c1001c40006600d029a800030540031f441170058481841c410303a4155038034002030188010588510700180516000100740c19803190b00240a003404170703580698142065201420b811140b003000006103d00c0c10503c41e413149a41d00742c40c145140c0064076403500d070b4851082c080144400a40d10740b6070007242000310040040c000342c0e200c00b03d0103a65203a103025800f40a100301000b10f000804a01e900b0340c0220070101c10128540c42028000080c1070048000350b0040760418010344180f544803e5105821404000c1d00c0c0c418800000c4035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 158615737 1250 158614487 158614513
    0x90503091206040203060a0f0204030c26030c06070315031a04020307080705010c0b04061d060108012703080c0f0c0601081504030203041502071203031d030408150406060b0c 76
    0x400003800d0003031100d41c4048280001a200011210740c043c7c1ca0160000d9485617040c400d8029200b07540c00900810403002012510030b00991030b910851902c410281100c2c0118250240c4a0248a020300d03640e0b0802d0000a180f1406030700510708990b10500d5100941c1d46a075605800c40d9150840d001d9110003001c10003045090401405c070141045000402501e8940b40c00208031300710000e001859a404c520220b0300300300c541d070442041a0291100301608070808103000395276504c02d200301e07071156080464914200540d051000c01c1964003d6905000c02d109803030503a940000509062a805010000d6540342841e00e409000705a901a02612143d4501810a03107811341614513507040350103a07014440026000030071201100c1003034a181c055401e40350f9041e4288410b07030b800031a1a849420703c0604056156000c0d501c0030a0320214012103401c2e00c10381710340e2070203203000c0d15400d548414007050341a041b440850740c2c0148184008105a13445481003501a0000043d110066114500002e09 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 158616987 1250 158615737 158615749
    0x80a2d02070902090607030e0402090306071101050a05070504030201050711041505030c060a0e1002010609050a02031609180b030c0a060c020a121e060b0406151b08040905090a0609050309 82
    0x401e10b080d030540c104008074000502030300c10038900900340070140ba5100002d84503a01603c0b008000203060b100713240780004001e0150400441c03407042c29464900043c04000141c419940038804a664060034a815640150341c6a440200155407004840445800e039581d0350113170502404000030040741184c1340006240c40d103054561001c0c8101d800703021341c94809030b01210b030060710740040340c0e84400076440100590040c9080e803c4524100d040c1401c000400c1c0c1541c0095000d1209031001940824000c0300842d1002d10500520442c0e0a00c8455150051010b030410300010030010f0994018070700c550000303414480507600040100d603203c03002c0c0c0706615160030014001c0c1404000640b06400b01d03035a49400024034500c201810258045103000e010082c1d00064241c0740c090010030089490b442e00c1c5250300e040c0848080021088110003580c10401c8101429940c3e2003005c1c07508103801c0c18480001790400400010340303880b4410141d0f0200c0c40e50702070254030074010320185989842110034808 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 158618237 1250 158616987 158616989
    0x121a0115020d09051c030909090804050a060c050607030e150f091c0e090705070602070b01050a080c0d0f0f0b010603060602100e03070b071116140904020d080a2d0207 73
    0x140038110342e0400454070b07040034005170b84c40d61075214a41003801d86420b441079412070700201c0c0410b242100e40c9040000c1c1c0030040050b284129020641d096483c4030860f01c508000d50010015008800070407122406604010f190408040c01c0c3c502d03c00040c0031500707144500300c41d0170032400c40c410306011a208050052420140280d40c0841c90500c1c03099000d0149072010032414081c020703400000303180500c154142c801060f400b10041d90740da400b03420040383c100020f00500d8456041d070640040c0741400040c0075910b03000c000d000380403007601e10380b2200400d0550344c40a80350307140c81005110021310000c1100c3d003c0d20840d100083c01ca410f154000340b40952030020000d47c40c2c80d007200701c078500c1400815900201e910140d03580316540d400030704903003468145403165a284201c90f41460b21460450000042c1c030362280300901086007203802c10403c02070a07039000c0d40000000b1840300100310341c1700c010f1807072400d28200852846c10500c07915a2122004141c0200340081c1170341144040d03410702542c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 158619487 1250 158618237 158618263
    0x1209070b03040b090c092509060c020d0501060e0405030703020606010c2004060f0902180910031707050615090709031203020901090305030a0203040e160504121a011502 74
    0x419a00e003880045019480040c0c0041c141034071420014901280400038200b01340c00c09080305030141861006c04502405982c1c103c050f44c90320f129005403251180c00d280381110841d6554495075505c41d002e000104502e4607040e41c50b03541703800002c94021031090b07145000b140b0890085948100c5424001e0030208050079a604105400010b20045080748407882c2d24400781d05661400c41d203950000400900b11603118101c1402d5417030700040c94201d41d030702501007202407103083e1419800e104104002c910302200c02d541d10300c089250030310210321814407240c1c0141e00720840f1031611265445451401000725007400d5a000d928000020a08012010742d4001089003071400310b2600b1a990310b031042d00110645010190b0105401803580c0c4640b81d40f0b8019074211040e01c0e52080203010003501c83c0e100c0e020f006a20031540002c941c0204407400c05100400f01e5070388440c01c00d0b0503d82d5048100c40031510548100c0b070001c2030400107500c40c8001500821386060315201c01e9030a45006410312081000503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 158620737 1250 158619487 158619493
    0x506070806100809010b09040c06030b030102040510050708040f03061b050316031a060403060c02060115120b0f10020703050607170f0c1306030b04060b090612041e06021209 76
    0x301010b0348075140c0d0140b400380395081c040c0141c2da030180c13014014040d0780d00740c1c0d40c464608000d002c14082c2c0640c0034000d50300b069406008050302e8005141c00e0340b147d8441c998010400c10300002a80c3d2098001e400002c6c0303d200c1c403d14255032003880400c001d07500e8005030baa082c1d444034404903869603031400c0302d0303803507410f08009045180c0900c0d00050f85840020074001d040c1c48222050403400c1109014000020041115445603240d0078210001c000745203540e005031003107500200b4040c1401d410a405040a40c0c0d03102c180d454401c00c007401401c084450305410480b80c0303034180619507907511444215034255004103203561850a00d00d00d4000003420700010301c0340729241d10b10705a1030640c0c0240d000200703001c0b80c0d440d40c84210300c50009224044400c1242d2411100225600e5416045040e01210450f01404090b403909100807243c4515040c40da8000e5040100c58412002c00c0e074620b910074000da0201006461242c900107152500390001c8414036400100ca024820300706664641161b000001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 158621987 1250 158620737 158620741
    0x6030501060519030f020714010c0806060403080f071a09100e0d0305130c0e010602070e011d04050f010e0123040503030105191d01090c0809060615040b1605060708 72
    0x41d02500ca5141407030603001804500c1003c85001e03030440180c207521901d003195100c01505110f600c0d450100c1500f065542030564004d1841c4c0f080030114001c050003406145060714581c0d590046501c443d902605840051001d200130504d00700e203080e60940e004140301c5030b1385408080c4a08001c4050307460b1b82c3c2c103450441d071003e00c4c0000040c400c54030010760030300060a4403841c12380380c2d18006800c0000c00d650851600403030740340320f101207440c100c034040e8003100d08540e110140307658120001d0280180c643c00c07400882c00c2d02c1c8900d49020340c1083c021000d890304c85072240150785c2560401201c451082c0e440710061031200d8200c0e400b42103400500b030065501780c10a591440c0d204e1006101d4a84102c01d440300340014501c1e98401d20340100002d2a940070f000010304a000c2000b482407041c280c2c2245003801e2600002e000b0b0025a203c4c982c82e5024010b580d5900d4100b101c84404100302e490000014800070581c400001c0040041136484255025884264548503181c50f000401d400304010703600007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 158623237 1250 158621987 158621999
    0x20606030109170c120705072417070e0d050303090f01330906080709050901020705061f080102030c0408190302030301061202070b15040f0606080a0c0e090903040f06030501 76
    0x4a001c0e00c4080c1d400c00581e40740b1804404034170744000e2220303201400030001b60420410100090701e104842c00f0b10082c1e010f00d07050300d52007907003800c2c8a010b83e00803a410700f201640c00c01e91100c8480d0f00034010b0922601560030500031401c2000540e00440341640004207000e83e02c0c10802070140342c41d00120090020017000300182c1000c2c0741c0288802e816620700d10040c115061414000700c0605000c0004001540d0780d082c503595a034210b4840c1c000d10514007000f08070010018004c84440540101c010131450304c0c2c4881080e154550884c4c09014050000341c0412a00c40c00e000440c01421520802074542c1d0400300200d0402d5003013519003030290b0000704d040002940100a9a044641904146814011010210340603110b081e50040200d01c054042050f001c503540c5084c0c071810810340f000c02c0010000d040003001c40e107007805040003081206000900b201490f030027a80700c0c0780c0c9500e8a6035100021031f0124a035003509840c01d0300d29400c0410248114089100c10b440100450300e400c0c07065501d424 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 158624487 1250 158623237 158623253
    0x10e030c030d0c0e0d03120b061206010e030c120c130606020d0e0f06030a1a03010203070c0209150907051b031608130b1804050108060609070f03111306020606030109 73
    0x4220192040e183e0559141c418003500c0311a01051000d4010503802c0c00718a8010321044c1c000c625000018030704803004040d4108030050b507140318000200128140c46031001911002c0d040400c069142c030a43d0400c00e0341c1d880d0028201034001440f4014080349081004201c1041d8105a071030310040d05c5c0a40405c0440c1d40000c0003210840a803c01011350146900450301c0f14980c101c1e4181c1011002007400b2502600d60b00c041115041d0b9010a140000c0200c01c0600380d2000356400750015499417600c13805843e1502d101c540104c243e481c0c10850924860124070142d2040310050040341c004505041c030b401c600e0611100540b6140d0245185c4800014085d160003280744000e818400b01150014a00150540c10341c06480100e582036200c0c0c032260380780c8947c140c1012a143c017540c01d00c000003481c170800040d1f06004500041981c00b135551003c904480650489000c2c404140d2035040910154011000408900b001d4034500340d512420400d020307181000140c5031500a80c0b401c4071040100c0d08903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 158625737 1250 158624487 158624497
    0x1207050303041218060806012007060e01032a080a0903171e0a0605120f06010b07051e060609060d020d020103150806010816060804030e04020f04090e0f010e030c03 72
    0x21030303550f1a16849660450f010f4500040d003e80c192150840031a1540d085030840c2e1260a09903a00701d404c0003403046034408280c0c0f40d15005960382c4841000d108a50003510100d01000042c136001400035454105604201c42e5030031600da0200340700ea00c864417191b00080c803e42c03214600c0410701080880ea580200900d45410340c69290f100c0c0e490100e00203041c0100c010354211100700c0d00b48641d00b810702c03a520050406101d854807941301012050084640402c11001c031600c042c0c0a00b0050707280036500041d0b40c1c040b0ba4202c0b514004e070101401b26101d44110403e00704502c2005121602d001e1090010880002d444944194202240000184d82d000100e4030b1071030342880c010030740700c103481c803a06808010381d00701c0c5540e030042900120750400700103451100d824950352810344181e541c500540e542d1106480c0038000501c8495050b010341002e400902c0500b80900d0b07006c1c581030740e07850050119012440c1620391380c2c1244001006c502c0b0240169400303014034101031450305d2011610b0a64034404c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 158626987 1250 158625737 158625743
    0x1c02221e0c0201180b0609040320060117010903140c121303030e04020301080d032a05030412110a0609050a02220606050414011b05030c0d0206011a0d02031902041403120705030304 79
    0x84580054205440b4070910380141c0e4038410700c0a05078aca00700b48181c031003800f40503690304013900d07000e1500c2c6030005000303030400c040c0c15843e03402550101051186666214030220220751151030341c0e807040762112034020700004420b0703994616000c0c214600244a85c03034083e0075a20071401440103000742e01002c80d603e4019440c038100000c4050440b62a11801c4220200c0c1c0c00454044580c2c484180d50000b00841c0f2852003084c01310a48000d4030b0781a15803090a941c0700905a00000387c600000d03895a11810400e0700a20032070750042d407240d00281ea03c5010483c1441c088800214040a40d0b199000c1d04004d004c40d42041d505103420b000d019032040d01034444050402550005102e0440b02032074086402c160840705a03562054075248941e99020258003c0005200301d0740005051003200c0400e240c5622002c01862034864152403680c06500b010300712000c0c40a0140e8540c081c81660300c000d100411040041c00b24141c803000c20541000c40340320079212070345020400100081c1c008402c0b02e51080d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 158628237 1250 158626987 158626999
    0x8100506010207230d020405090f10020301081f020f0a0504080d0e0f1c0b040501020702100f090605070317040302010b03010f0902210304090212061c02221e0c0201180b06 75
    0x1484c540001c1e4034600506011350400d02d424103119030100c0c0440d022130b49100305400c0b14010020310002d0341c100d1009208100a5802c580040180c01072400009031284030782d100c0150074049141000038031075011a0040010400c00901004003100a000301d110b40c0c182c90030300c00600c03030300c08003c503c0c6140030780c040a03c0351807200f0080701090700da42d8075110055041001c03030855150500d000d6000750303c03d0400764420304a11181c4161180304a1101e0401001da070783d84076080e8a405400d8420750441c0804805004880b0126024050620720061081e4007079030011072504040350a0500f1a91940f254000c00c0381000d4017000582c03216403040d542e00411440d64011003c5655109045002d95080200102d000040c8008008965000d260040d44101c56084442040782003580002126140c000e40000e408006108070050303030445881d045010940100305050800800303a0018218240900520340d6030450f1994103a0910848030540e5100681e00d403031502940380c60074440d900030000d6200708 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 158629487 1250 158628237 158628299
    0x90d12022b081609180504020a0f06050a0503130506090706030e16051e100305060f040c020c10180303050403140303091203040312060e04020312090f090603031308100506010207 78
    0x51142c10781398001c060301c10203e414626501859000742000383c809a1081c1c40e200400b0498220300d01ca038400300c030501d4846900c0c040d00510300f56007641005020706015050b91100c0d4000c0b40e01880320724850121a03000e03000b501d04084c40a8115031407500020010392010fa42c95150314100c0004800b658800c840300301d910002e4101c03046074a0801240305400c130262001681e1600d0b0550007842c0609001c403030442015170344000348811144c1c200c01e00780c016801046250401e003007005600a00c5d24540c41c0c02c50342464920780362142c422050380100d00142d0f00003402c106000080032801d288d00f080e0b1001d50b20318184080401d5481c0c40383e140c1c81041000c00000319041500031110340d000003c1035001071000030b075100340428000d081220164000c0c0651104074243d240007108072941001b00824000c1003054000c1406120980200540d4240c40108485800b0b1190810680024541c0900907d40d5030703a8400c1740e009440d8043d14860540d88200d005005201c06c0e064048402c16207548245504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 158630737 1250 158629487 158629531
    0x621030c0102131403030313110f0a0611070503070e070f0e100504080c040c05180a1a030103031407020310020f0d0c05030a06050105041406090d12022b08 68
    0x40c4200ca060320020340c800503522581d51003040011044a85643c400c8505a18603002c0c135803030b884100c0305248400705c0c4500200015004009608201c0d8000c0d001d010300401c2400459000c080d150051004501c060b01b644003541001c0003004007424044d0094040c2d03e00d02050742e2800b140241180090242c4800d0480420388144900054203030001d00b642c0000410040240035079011b070280041d07501038624000210304143c094801160b080e5900c00746000a0059407403106820062119800040c201d07000500e849240311414201c003200d051142d903540345142c05400c3d04c400b203010440807541400144003681e0046400039500351030510140e03888039600030140c094426030000c0403d9500d014460b0b10203551080155102c0e5100c0c5500b04940780e181e600568031400781d4070032018810080300040105050041c094000480b01400e03003000ba80a03a80c51840715020b0094010040e4494618444403102250b0f000c0c1c0c0748401c008a009a0340c5060100400c0010001c051120040c1a01d000e0001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 158631987 1250 158630737 158630743
    0x20607080705070b070209010e091b03100203252a0609150507080a060b0717090a08010c02070509060d060c02070b070302010f0c03020a051806040302060a11060f0621 73
    0x4000d501c002900d0f5850b032200c0c030001c4143c000c40d10981c0a4100c80d40042403404040505034011005c2c40000c02ca010315124691500700e109a800380e03050300070340368980360340c00391400a140036260f084009180ca48290a05d10034020a910a840400a591210b08000e115109881c10800040f904002c440140f40c05c2200c058160818014404143c44100c480414811303842680901501d595880440e25440d407060b05940703560045e080420010022540005c1c29000110061201c40c0303607040c24101410b0006000e001d0940c00345020365100c00502c1c00070343c1d050250344040c15085070802c8150601c84086000d10505880081c101561001052000d5000700300c5640181600d094441d80c40511380340080c003234110030200854982c2803404e800e401902034029210452080c2c1e036141c0c00c00120f003485900088110152170b4214804000c0400542c540b00300400341a4200d0300c43e52048080750044500d4664000d04001c140c200d07da003403018990311422082558814200c598004c81040d59600341 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 158633093 1106 158631987 158631997
    0x20c01021b1011010605040203070c050105060103090c0e04030905060a02160b040b0a1b0c032d1e02040b0d06050907060f0509040c110105090c0a05030a0f02060708 72
    0x4442031107081c07804a1000d0000010403174680d6903000ca0b040b42d1003942e140000401c181410424003c003402520703000442882c00b007007031401075100c805450011380203000115881d40003190a152103020324001504000346020f40c0c034020390030080d41d20321a141141184810356640001e0004401040da0211060041410724103044d41004540b50450140c0d140703040070600702940081050814250055480342c401143c0d40c0103140740000f403944d041800e10006c400e4050442000505c0100c11040c480384070400102130704c40c01d10000b0050160f40c04030303903008005d4040d0b1005000d080d40001c3d004450200a0350800c507142d0302d0460b010b42041d080d4502046081096420904040d400040d440c0024908240c0004884001c182034450075503590504c0ea201001a041e58500309401d00002d1608400404554419a44681503080c012078044d00c28000400c0c56414095a581218 = true := by decide +kernel

theorem cover : BRFrame.Cov 158453237 158633093 := by
  have h0 := BRFrame.cov_init 158453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 158453237 ≤ n) (h2 : n < 158633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
