-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1135
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:23:36.212334+00:00
-- url     : https://prove2.me/submissions/69f37c5d-d7c5-44f3-935a-718e4da4f088

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 203956834 ≤ n < 204136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 203958084 1250 203956834 203956861
    0x2210402040507030b0603061302040b070303020414042904111215100203070303090203070b130e0901270f050d030e0f300405060304060c02010c11120a03021908 71
    0xf0000c00d4074040500550355118016250040c0301078132502103034500b140a01000b48203c0c5c000103040303540819100100740e4190000c00560b40d01c0d20b6000c203541688010301c0b05841200300c50300c0c03180072040704495032209864030340b400d417800040c40481e0344580740c10030302000e5101c445440300000740c19080000032052401c605c134940d1030984801e8101c07120404d00035140d00944000030b00f0151560001011b555040002d80041e01818080907912000c124034074103030002074822210301d9507000700081c49944040c860f40110840c2401c070740c0410741c003a006655101207448022250500f004050b500855002c1140e4400701800d51000540c4054544840d4034160078101070240991284a01500000f8410b038070803000301c242600099810b0000315000c1c0180516004541c01240100070002805030300c2d00107084050464000b0400c1c0c3ca17100d4800c0b40e5020110342c00c4900c69021045111421410394010194000d003841c0060034005500491071140101c440d4210003c0c0000c0c1c01e210300200a4070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 203959334 1250 203958084 203958091
    0x806040b09060a2310030c0909050103020f040c0201020c0a050304090b030304180e0f0a0f0314120115030906020c010603030e01020609060a090804170a0b130b0f0a022104020405 78
    0x100c0440c107a00d0800e0000b00350a40798002c03040c1d9000300c1800060b0004802d4640c080709940100050007140701d00390020f0003444c4000b02140000c00307200c000564a05984901d50603680c01500038042c0310300c01000d10015000b48040079003190741c00c00001e5a01e100600c152600c013480b400103141e40317a02c1c2c480c001e010781c1c41110540e807003500108020020700c00055176508803d54402c5000c111130f01d05c00000f0b1309082200421ba00c40f0b005071094030081001c1e000001e200b07588a51200300e40c525603c20345200d503000f1481084000310100c3c3c010701407404c4442d80d4440c2d000e00c5140c0803c060384d4903a91002030343c00440d95480580c1d11048140708068002e10121844542840200007618144005595650303000d03007560140c2d03588072a03032018484580100d80c0686409504016280c9024404a43c0d0308242c440598008035000c0115070013130818030342400100c3d0441c1c0751110b181c0300c4c0c6002d4240100d0240140e40460790070080000b1010900c44114013854002d031503004985003600600c0243e03207008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 203960584 1250 203959334 203959339
    0x7030905100605181015020f010c090501020d1103040f080610050303070f060b0105040b040e0708090304080a0611090d0305121003170a12020c0a050705090c1b01140103030806040b 79
    0x14024041915000c14040d6854004c0110403295102d00301445000700041e003018121600009680c02c2d40c50300000c5c4003104a40f450000c00840301c4007501210140c2c1c09004442c0142c0040c598260030074400c03008001900781d05410b072480c0942e1003104100d000704035813000b0b54a8000c58200504013210920304801408264007451401c00c0560b69946252204240101000d0317480011800c0c0d641704500780da016201c2c0740c1580d66195102c6000000c5081c0849841000503c0300e000185180000b01c2030f5000c13a03004400800c4200300a984101c042c1c150303000010440034040c4a030388043c0d55001d1040380102d01030f031030b120b5807038102e1085140d02c00c0005141c03904085c1607a030100000764203002c0400c0340144d4803010b16203c00c89040c084800019120304414002c3c00814140c00c50203010906041d450b206400700c03a000d42d41d881c107100d660342c01250000c3d00c0160a2000f0002c0013180c94804030800d140d0800001c10034280d54003030040840a0300254006540d030010802d540c2058440c0f01e1240104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 203961834 1250 203960584 203960591
    0x721090201110c06041205070e0705040e1b0a050a050f04121a04050307030e060706050103140c120709020306030a05030307030c03110304170d09141c081b07020609090703090510 78
    0x2400404c040384114803401d03080002058504003400410b01540c8050410f100350015a03042480e00101243c0241c0510f03140e04070520041040030700c684901d8240c0307800c90300e6000d0601050800c240d400340c00c6100480300740f000400003000c0e405115001080070303142007006002040c40034104130001c0d070a29060200504c05804c203001c003003180001541c2e511545881c24102d800c00003004100540200c000040980d424400040100043c0c65101d142101c45001111003e460f080200034001880c81025200e03908080340030b21000005800456200201030215480c0f0406980c0f40c43c59980215071800019a540140a03c880d0340350040014440c00041c8607030a45c100303a140d980010114030101d03100800c001801c4101c142851300943e40701070b00b21203203c004080c04030300f107034480400c1201e1007c85451490604091402450a94040c00e03900b411101001c06a08040712250b200c0c8100743e07031145090040718420780e46c0507122449a513003a500031440c0703c1c05203049464034041c1071507131060b41e09 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 203963084 1250 203961834 203961853
    0x306121a093912010c021218091003170901030c0509011e030e0304031103060601020609060103030c0203031b030702040e0d120b0409060e06040b0105040603030f08072109020111 78
    0x1c00240c0014941148038a800340d504110b4010210075845020040d04081100f4581120300e6041d4088030040145400396840d955031820105980d1141000000c6058900c4116403003074200040f9403a8000c1d811502c824107543c07680c4401d50f4420030380c00d02c1001d070303440042c14500303030b50b4140124030f10291241001e6062580007000600060707070041c529140c0004540000340b00c144280c0110105540c00401d0b255581c0d00c80c00c0c130300801020000c0c2d1901a12640e8042441c3e03510008190b440340c8130407030280603980d00350f035011204942901c0042c2e80c144800e10400c4840b044081d410240603403032900440d50384400344140401d0700d1100302c902499030400c00200b0307170f0b20303030041d14124001da00243c00044034404000003400400031100080c2066242c040c9030400400000380d03e501640c0200c076660040d0313980740c2c200400c0c1d40da10301000b40094060345000401c107001d0411107400c001726080c60100d0285462250345526a41c0c111000c00948400030304056503041880c160605011343c001e800c6602 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 203964334 1250 203963084 203963113
    0x606090608150a090c020d0e0603040507120303112701080403020c04020a0201020c03030c030118020304171833091f12020f0301030b0708060904080a0306121a09 71
    0x150040c110040c1d0031682d420025140d40d442e0008019110341d00c41001034400c1c400b0020f5840200c0c60448004c00c480c004c04001c01c0ca490700a90b44615800801000c0c0c081c05d1500004d18a407281c0c000b24203150716040d86843e41d40681c80070f080d000d031407110402c0f4010740c906103581100c1c1d44150010b052103140303030a000110364086241c246811040e82c003d603644a04403802c038020300ca9482607050b42c0c0008801c0c07050040c0582d0065040380d050700385043d0191103a404407000ca200c1680c000300300401e60301242030002446009000084809011152015001c50114451100c581e02000d49410303040c0013000d202e060310710150403500a038600b11f030401c0390320343c0443e210000c0780e401084a00fa481c000b61807070350b22540f41c4803c003040d060030954540300e80020410040e0000e0104458000440000031201849600341d01e22810000780030082d9511151a022240e81c407000d8404100350700c030000400c0101d030200d4510112403080901c4503444072241031200003000080c010152903003001441400d6103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 203965584 1250 203964334 203964347
    0x9160206161b060b10050a020c0108040602040e180d09030f020f0604030c06030911040903080a05060a0801020703120c0e1f020c0a0b0c07080105060a030f0c0e0f0a06060906 76
    0x604400e50007464500307810141c0b40c0655002c0c40d194404001e000d4441003110641041e02444415070f0407903606a170100003a51a4010002c46100590101040c0c005540c803030808181c0060060b540145420b4403440040014081101c10003a080045040e1081001c020411900d800c41a445c2150001d4255907802090b111003100181c46090007030f66045a0b030740c5200442e0004d5a00821f00c0740100ea90300c2000c0d000d010246400d1f5000300741c00303038100303171a0030640201090305515560381991746e03480039000d03801004040e02094000201d0075022450800920062119600944614150303192400c0071205a030b6002c0300403010000704119030b00300c503100e800e02c0d450501c10740c0c901240c08803981c0b80700307e24020003030b280315601c2001782d0000255824581e0080074180c40703840540e5250386d01c41900c5826100700340d84058200d40c1d03529081001c42c1d00c040030804114807540c03446d585035a55001c10550608150307887d040002000701070064000091040900800d40340c00d080810314038010003d00907 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 203966834 1250 203965584 203965591
    0x1109100f270e1b030601180203040501060305030d1a06090a03170d0c0507031d0307090b0f0d0822060e04020c150c0c070e31170909160206 61
    0x450865545408090804880c044102900000204039841c10540b0107035645801c5000c5a4401400e01054075090902040c00c0f81681c00d10b92409802481c00d804a01c005d5000038000d0b1415540da00b0048002102803000302050302094001140710300c48484c26001502210381524403a010420800c3d2468a42d07010586c03c403500034202090300c0c080308019003050701c150321120000c94948260440d07041c1d000009000b8035802031380c0300708a031080300c02c69081e0348145282c203940c940e00c06201080300403010782014800640281110041402c6500401c5160340d50000c11175440d8130116135180200301ca00030312500b903140c0c2c1c00b01d854400d2a004000e0f00c03541003480050301031600001d048041e6417080080c5842410f003120300b0390700c034a450300c152407003a0041452000b060058401c00a0299410310b41c0500844043c034070098580002c41c950600b13003051000b5a0392002501d811500898501e0300000344d166205414aa43d440d46001041280c80c4010181d05d954804c450804000540c0010540d03070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 203968084 1250 203966834 203966849
    0x6090f0605180904020d061b030506010c0b04020f01030603050105130611030c040909170a0206070809070521070806190b0d0816060608160f0e0402090714161109100f 73
    0x3c0392034070f002041c0c16540b840c1c0068026401c0840900d000640300301040e0400c00165402c00168880800440383c9041070340000d410187c8840c04a400f52921842c01c00050301c05040000c0c0c055504da9495082d18001c8400c00003c0c0d03a030142010600401d406080945020014968918503046080064500aa010300f806540e070780d51100c1d0400a450050018169480321910340b51517a6103030095a80e901290035070000b40d5480b0116048a10001700041540e00041c181c200da0050360720b11100e800c6103080305e40f00c01d00c05c02c0e8000a80c00401e12065010702030b2117a803001c1c07000c0b580c6894030a55400f130480c0c0f805008409803490200e240d0500b40c0d000072000e003050301d003600d5250034107001400c600c0e0000704440c01080021800c000440c400e07041100c01030200c0c0c5c00d0260380ca034500c0084c05411203000c0c0d048090b20700090b0019100b1040b50f403c8207076422102d41020360040b00940306040b81101284da161b491602e03007595103031000c01113606c0704402c001c0001060803c41c00110444880c403a1340d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 203969334 1250 203968084 203968099
    0x906090f141e0d06050103021c1208090a0804271803080c0405180a0c0905090c1608131a070218091c0f020f07050307060c050705060c06010e0711070e06030a0501050106090f060518 79
    0x10302d5034800f3700545110329080001c050715039403915566001c5162420310046151000f019162050445000ea240c42443c05e0505c2c07080a078907030b103065603981c1f401032a02880c0704003080f0100c4c0d2507581107034010b0542e0407442030400f1483c1c502c002400b00d612a000e00810720021150800495441010003540203401c002031584841561a4000b0760b0300c1081d00092003564041550050f2644941094044844002c19481c00e41c1a100124205205000c0e020390413082480070184541021480250010790001c115030409000d00c1402e404038046c842074400007440040c010341616070400c21081070f94540780280140c0e51070200040c1e0388031500c3c8501024810308040400c1400000e2020f4001448013401c030540c3d4141c0050b00301e44401007405540103600044c03010410303241c841e25403c81044600001020801d00b082010709a07408010401a031500c1401c41c0e040015a080c019907000705031035214580c0c018200300c0000c5000c400c41d0060030801000b40b0980d0440031255404180424050341c015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 203970584 1250 203969334 203969341
    0x3280201020d0c030506010e0415090506120a150f050601020709050c221a160b1005030d03050403140f07060b04020405100906090f141e0d06050103021c1208 69
    0x140d01900550080d403100ca8a082100214180c264000601c20a0240c1c0c40010040d03c03001000100c0c1d400f11902203a0361706000703090144010a61005400c01c40003001c500c80b1115115042d86000b40d0a241100c1011100c000300080300150700035070f404c00d01d02d25010301c128941b00c1d00003580e42c1c03918420011402e4841e408030b01210800400c4075138042c0d240300b544100b1580a00b0111251142d8410303412180007001c2d40ac2226480c0b1401d4482030007115100c661050155143e080c0f6180001c0c2c041905000a40000031321543c00300240d059240d042d071008a407a2a06007806081211070118181c94240d0410400e4504121003003181c004d142e014200041005441022800030b00031504030f40c2e08040c020340c841e401c00b40c0003080c0c1001c071413580d42e0389035503039407200460515100071303205600384100462280c1446140c040b0080345c90051940b80412080032810004020a03080c4200fa108a5502e00c0140f003581800c40c80f482d10a514417a078000c4c001459992260144001180c8800300030010703020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 203971834 1250 203970584 203970587
    0x310020d050c18040f0e01090c0e0c0906160309180506040e0f0a061d030a0207090c030908040b160c0b040f090b0306060d15021206041508060105010c06020403060608060f090328 78
    0x485c500c6c440304000700700c0103010345041d400c441407a00600e802c5104080000300d0241d42c1c0002c8505031080506000c1c01d212400701c804080300b42c18a801c03010b11014510204003507048a8503036a040c0c941d1000400c05041000502c011914103240000880c0c02010700440f9202000541056441d40514001110602041203004850700020700d4185800300103225040154001000004d0311920001001005031280003503085909500004103400303818002040000c0344140a420b81e05c510f0520940200d08507500c5801245240c1c2200600c03ca01090500520400346000f001601502400b080881c00740344c006035480f074000704458072904004240008018001f0306034100f07409100c1055482d26480b100141007100d080300c940b401185400306900b04c240301c50103001c00f21890300d0068829a420140111081188260700b51a003135000c01002001405d14410715005040c00c1c005000a4101000c0703a001190014210302d803550b105110b2400760380020383d18015084101e0b00c1440340c50303040090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 203973084 1250 203971834 203971841
    0x110f040b0406030b0601020f01150b0f090a15020f03030103150c092301140a0c0803060a1a13120b161704030903051e070b070206090310020d050c18040f 67
    0x60081d0440e0a00000004000b44424800c0c01803200741c017601d15904400c50124200e500001e20b621b0076180b2174508014402e40c0e6401004c1d103015014100c2d140c8000354020440060096020a00d008040f01d0034035070b03d66051000402c1200c0c4000a10303e15495070300c481d040e140c00340340d0300e860385075072a8060784007540560450b000404940d61000c21641d40545d0340c1003100000300d001030104604400000f64800c0c10001c8504030080364981e00300b0801c0c0c80e224100c00f80c1008004a0304100450008618810040c400701b11400c2514012030341c0e8244461510300c171602c542d103d4102503c041c203200001400311251107903c070400440b0a00202e09103802111449050005503010025000c144000c0c1580b208034101964011021101c020301e412000301d4001000103000260b0390001c0c40240480c002200081078010f00060010f814440c4000000b13041c41c00c0c00b190040510b500103800d42c642e0695015032903002204c4640c19040140e61060108411110410540729540c0e480307005209035841c0d031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 203974334 1250 203973084 203973101
    0xf05030615120705070b130b15121002070c060c02100f030b13020a0f1115150307081608010c0503130f06060b0a0201050906100302060705030c0105070804020f010903110f04 76
    0x2500706207a400c0070f5402800703a90104100342c0d0840c0d601c4001905608a80b41903505031075010f0395240c0a95034146904d501a00b014039a2a0321a03901c080e401d080c004204440d80185603034040040c0e41f0f1800e0320700240405160f0740500d0501100341009005079680c5841c440c008030303842c1040c205107000a50228001e10710111115400710f131005960039050801d030b01810700c0c581d0b01d80700c0c409800c0401c042500e10020502c100c90346684404102400442c0c6044c20710342000329842400200003902c40000e0810034180c000111540c80700094400c0140c0002d103550080921400070003824800500c01021888010408900c0184e41e56011042080a02001c1b84c1d40c5d8001c03004200180c0c80e012140c000e6440405031400640c200b001203424098045202e500900004c680703400320030301d1903082c041190050b003c00d8501e40000e001c1c4a440340020b008480c80f80009907211255841c02d0f02c1000921142c0c445114100070500708103200007540c85006d410342000840314000b80c030a07641d00043c0501000d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 203975584 1250 203974334 203974357
    0x12021002040b0405130603021e0f060c060f011d0f07120e1c09050f040504030c05010e0109021f0905040f09050f030703030501050321030406090506130b01060f05030615 74
    0xc0c00050400c070b410060025110100da50694070030b41c612204007070b600c41e03000c040e52000407070003821442005043e0020040300003600c40c02c400d203141d200140554100007000085500705404108069840301e10507809408cca8018003240c1c1200101015411001030002c03524400c000049001c40b40141d4140c04a610280070510506846203040c81d126480c483c004c0030a040c1c1d10518005550041401000380d074070141c09121444208030401c005844084d00c294180b240406804021070001c1c040c100a40b540d072070000c54920014418411000301a0b00d0200503070141c0300e41c40c80c90550004007101192812580810001e00b0803a20900030600d144008026104e08004d0740303850700380880a04a500d0194808100070ba90380c109251f00c40390b00e1081a40d040340382102c10030240c4d9906000e19041030140c3d0001031718188981c0c846181881c1134601e41c15030708440c102c44080200d981c0d507031805403215151400c8032100210014019000141c422807249030300281d0040c0c0c0c07110710820341d040400c55 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 203976834 1250 203975584 203975587
    0x509010305180a0c030308060f011e1b050607021b130e100e0705150406020709090804030c03030839030a0207060606110d09120b0a0609050c1803010908040312021002 73
    0x1145010300300e01131a84803c80c04039a00300001041454030001c10070108006849485850701d0417002045844103044100c01403006000c86082c090b135109040f007041030300c98801001d5600308514007914022004a00c004111560308403e0103540350350350180c691f40c120300c50100da15041c1165042c100044c4400d9441828a8034000c180b10301c000040140496900b958401e111100c030442e100700a10490107800d025a20220702080b88a0381d9610140905000c3c0e81010f040c84c1d04c99a41d4140d4000a900641c0002d4001d03007842100f100b400f042c0d1407205001000c2c2440000202c82d100d6807101203081c1c2c030020220104c00a007003058290116211542d11a0f1308001664840201174060041d4203103a07401c0c1d00c21140c0701c0c00e07075074002d410400c2561500c1640c8141e0080030755485e411514002c0c05800104d0710340303000158600c01c6004042c054414103120949500c1d42808210b0320440f0103400070b01c2a810907005c00b000c560b92800710780540703400a4003807810849d5030301e060b80303090913084090800c18030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 203978084 1250 203976834 203976853
    0x2010c0203031603090b0406081807081c0e0f031009060b03030a1e081e040501021201080705120601290c0a05100c0509010f030b0d150e1903050901030518 68
    0xa0362510780f80300910984865010a4645c00c0031000d0340a01c3c050a4081141040400d0100001d0100313400741024200c1190050364035580e1042c20248040c1c000b0502c00b1300d8100018003d80c000d41d08042c5520169001c000d150b4111000a5440303e4400221640a983d1b500d10f9003400802d40291401580190440e682d0703039581036005040e21241262141a120240f0a403070150b485a203d0078019002000703101600101c500d00540810f8014100b04c030690340c01c03c84842e1100d54168041d0090003d10003414803076207050280f0400d4010440c0507601604440010f04c8011b08401001c1c41760620440d4011240c0039400341c2826074811a0403290151241c09400f40400ad000100758002146100090003c3e120541e0195941e000f00489940400c1c0c5460540b1041c61283d07220042e5041e00a0101e00c014205840c1c400d400280701045e180707469110300740442c600e0720402c02d2081c00700054100d80001017654400900900404945504141e1280c0100c0d42c0120048500502c9503100d0094840400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 203979334 1250 203978084 203978107
    0x1c140105011e0203030103030815040c1e0309020108160903020607050601230f010c062c0f03120f04020f0414060a0f060e0105030c04150f080115170402010c020303 72
    0x5000348100d07400100200303141c81c0b108001007010740c2540443d400840c21079007181c0c0c0c280c5114200034529009914000700b5002c0c1a43c4500036034101e80f07180d86a00d032841841c200407803010443d03280d43c2c3c1d0526081040c001c0050342c3c0300000b5540640e003411030341300c8402401000c960036001c951019601ca440030070b030f41051120101d40103040b10b00c5000c2243c090800c002d46486603101a90886500110440c0201d08550148418240c1c461292500144120080c104c1031011004000c08a0f030b20b00f201d41001c0c000c0c6400b0480740c03210400c080020b5040c035016550507d07500c80020002c06100d0041c002003400c41d11130f80000c0c041c20340c000380148200ca0f100c6240620b01002120080c1c0b040600c0400099550010010f00c000c0d01c03102d07504e141481d18164015a0268009485507800c410100800140b82c1c00d5280b0f400c4049885668a00080c40c650100034001041a002a607a04441448211040f6080108003002e000d03810051a100c5e681c5000698209880b0140039425010005003405d21a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 203980584 1250 203979334 203979371
    0x30a060503070e190510050603250f080606190507080c0a030c02040f050103020112020f1303030e030618060103030e010e09070302030a18021302072307180c141c 71
    0x2240902c650410104c2c03d0180341c0c080c1c0d1001e65090416000841084c80340d8107040f001164810b04024000c0d031442d4500c0b1080c500c0440455101c40040d00318040039850550180c1c603140c1102c2e00f221081d091000702a00e0a0720240c1400f40c402c28001d0000d09401004035880a41e811000c040041e41e01c481c0180c14040c080402e01c010491056281c6041c10702c952450b4882e00d4180c13074060755910000c2c82c01c0b000a00007948034019494440009011241340c81582ca120007000c1c40c400e683d00340f09106140281890303c3c4002c0c10117010301103102d0401032149c000242d102d0440c3d8041c07500c0c0340c9050075400107072403030391085c9403890b003007038034030b810400707410707007540065016443c140d0f001c0282440792440600c071a4000c4400035400700b407040c604140582140c0140100901594401d408040d0204401e501200b504500301c0b00341d0070480e02045230311220703411a40b480181800030303c080954071b0002414400c0004c0c8031070b05e0003030103e0318007224890040d40ca0400c01c2001810030484403202500d01c00b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 203981834 1250 203980584 203980591
    0x320405040606030e06040303050705041e03030f1b020d0602040e0a0c020f070602060105090a0e06040f060b04110a0810050406090e0d0f080a0b030a020d0f0309080d090b030a060503070e 81
    0x2541c01c11000040861003889100a00c64102000c4c10303180c0c03211350701140903010140c0504104801400045208848000f07a2009202c2c9401c000e11032618501c2d003d084100b09001000c14040402c1c0442115441c0308032891000c1d074111151080a041843e000000b0f000d1600014016401202002000805a03110710380e4541c403074003207650304440715641c00e50f905860301421005130084801000181421140701750404003581001c030300781d541c80a003d0729198048500782d889101750030615047c801313248585c0058100940b028400280d040201d00110700c240c549100400074940c000502480c0d110002d40c0c007a00b00108140003d41d601d100c1e0901078030b40861601154056403040150040c018405a2003911454849031000e41d18074040c5c600800100c2c2d903094140c000e2014010040c0d50341e069120110784108504c1c1030490007400e00800901e8150020101c5501450b10400d4003608614003004884000404980d26500e8841c0380c00580003683c01150188140100858080e4143c207802c0c1c803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 203983084 1250 203981834 203981839
    0x20403060509070f06020c06030907030501091a060d0305040501111c110114131205071a091b21070f0603020c06070203070c0504051e0a0f0b01021c320405 68
    0xc02c80d1101c01000b104c07411885080056400034600c1c104900b00361014503480a0b202060b9001c00d07641c0e40f215400c0d90313010344044600c0e4498141d0000c20000303180d030346604440d003942c20741c0107000329650151481c411801200d043c4071000d0b01c00f070840b80b0200510080080c2415040ba00528a21405400114000303000071480d401c012050041c1c060381291a403003a9900200c091044486850310008442401d24000800604101c503c0200c1c220341d04208824850309610b40d000d03d410140d5070f0030306504003a117140018144060806c95510009091001745025914a4611800c0f030301d80351500d00301d03074040031000c0f0116100050b401d4140c1e01506902c0e0f07503030082c1c41881d40c907401c0c120380302c2c072a51600606620700001e042c042400c007640609c0d402610124143c282d420300c2011643c44003030442d1242e21090700c54141c80750700d44a5000304a02d44c2001c0c0024034444200048010351f0749411040201088080c3c0c03c01c800600958805084100210707207160f81c00a05806030401d1544140074850 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 203984334 1250 203983084 203983093
    0xc010e0108100303050c0a08030106050d0c05031e090106090f0f0507023c0303041103010b03070605070b13140307050715120b01230d11120406050c0d020403060509 72
    0x54503035014905407803040c0c9000281041243c215601564650042e14000302d140c4103000a00b4006103a03a80110301900c0c07291565038403081e95440000580311000c000004002c418028490040e520400c071004070b1000c4d080f0a0300325a16586054014000c1d60700000ca00e80c108144003003140c0c8560b0003509081c0000c130050000c1d0380e40d070b030081c6c0c1e5420800e8503007146071000c041501011010020030b0000b84034003507041d06641a003408071a1450f0400d54060342c0c111a01421700d06549000d01c00c00005140503405001140d20b4a18064924001d1501c0a010441050001004400c40c0c04081c8000750740903c0107030000469035000b56030398010300000c8881c0c0c481d0f22000300740030800318404000004071b0740e00c1040320104911100081c1c4003000856040c0704400c0c1403c116a9000e2100e028400303404000b150319101001011425a00b4000c0301c1e038071401e810881d10300702001898440760f21540006000c282502e940d40e50028904c11008807445007440400c01104000c1540c2203107014514503008c64 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 203985584 1250 203984334 203984357
    0x12020d0518010603050d1b0209041101030c09260c03010222050d024905060a0e07030321090605070e0f0f0f0a05030d02031b0c010518210c01 62
    0x542c00c0790a1804050000e910a00040e00c501d0310a43e09a030000c2500841403130001525400300750306010545003210f40700050060a400d550345072081c61100d80d843d151518a580c501310400800b1000f80704103411803c512413000d05025400c010003590120064001c541d42e6504464940b03020305000046043c003405660001001d00d49a182e84036142e130001c054182c1d504490000e4200450b4003014441a41a82446005c620301100e070600d0018186030303110204407480e844c15a00b00000103124524140c0390a01100c1d43d0390b00003984a00b5aa494105034100b1441c82c10b03242d103000c01c0748004070000d41c100b040802c03c00c602a084680108a1512032800e90a41542040400c801060200f07802086445540c1c17801c0c948900913158400b005001094030303944420229060501ca00000005607200040030f1484010030601103070900c1142001c0c0c46e40d0845032000805600ca01c91100340d05803c00c001c074070305035a0344081d0045110503020184400c035890340040341c1c0b6840c1400050b404130b200703803284 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 203986834 1250 203985584 203985631
    0x2f060108030306030d05070506191e020306100311040501050a200c0f0103050402010804020f060d09060608120f19120f0b01030501090e03030135060906010911030a0c12020d05 77
    0x3a47c0302c695100d0b020305055568040c00d50340e05450100ea0300f0959450750b5900b021040404244006000b1652001d0780d02d203003800c14810594000300c0d50f141010310342808095005110419a02601d0007403800c0f682c3d8014028048507120004200410140180900e250f9000d40000b0840c100c0c2d10140e40e803000c0c00c4030007030040d4101c030030455020b800301c0d00250004005141c1082c554030181c400520450820101e2120fa00403580e580404032101941e030742e024031816200300321603c200d8034810700f5240743c403031108000c0c5201c0c0107090322801c080c0090205030a110340a00704c030b10944a40b074442004101803c056110280c25580403072408a07241c0000400d514284d40070303032104140804011441d50b441e10140d44100b03606016a01303c0101111001c10b48125400203101130351000d14000c00c46400c012980c103007403400603800541054940062050983c002038141e0398000440c107000502d41605440655450908030144440c141c40007610380024441c5902140c01400b1300043d602078800c51940 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 203988084 1250 203986834 203986837
    0x5070513080309090106110a0f051207140f030a17090106120602210606040b032d0901060b0720130608030408010608030a08010513090203070e0405010e0d2f060108030306030d05 78
    0x3080811f94000e01e00c1400490785070641070120b0fa00c2201203a0010380c01d140130b007920740c224001c00c592030080c44004285012003084048000107620000c1c500e8011180f13000360411900e9071481120403000d10028050010070b5121800415035003200c64010f204914001000358802d20601802d040d0043c07551a0203411100070b04d10071030000e00405e2810b801c10301740c4846c581000300740c2c00400c0f0305006102001032032001088180d000d0384d06000c40c075040c420121130a4a507981c0190b01c40c80c20910038100860040748031504c8007407024002e040d0b048800800b00c1d45c0e45003080c42c20070029080000010391300d40c0000007081111000c400070040c0c0c41d2541d000644034400c0e0301c1c0d04030000e0718440040c0403030324010580400f11b1900c00c500081c8240207030301183c103101040d40030200d52401c0104000a115080c041d0129800c0000046d014442c1d8140e4042d1151f03194038030340110244649042c00f04074010500b00400200e06000321006580c1d1811000e9480d40100c502d203000703024005080c03051900440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 203989334 1250 203988084 203988107
    0x1030308160c05031c0216050703021203031005040c0302070f032604210203040f0f060e010806090703020c010b04020c0d02070501110312041e0606062006040605070513080309090106 80
    0xf0041c43c0340a007080000b90050381400d107000c2d03409031700b08403200b0520003920021404911400207810001d25600410a0b004510440d840243c1c004004024080168400c5482075502c11540010074841c81c08044001340500c0c1c100410704a0f108104a00340760b002502e55011040d841ca03a8180c21081d100c2151482d40240c600800c840e11040701c1c0d00780b800c158903111090100714411603081580d2092100c410075901c0d442120074000c190014406203a201000310750740c131030a007480811400d254012560104008000100301035020443e205401c41c2904003a500f000014070a42d00c40002c0c4160320f8903840c0d41f9110001503c60550700140c076500a101180d40c143c007030b030095402c040a1410004205100800498200305030001000d1500d09a22440444c20301521000500da0b0801d0780241040f400800404c0e83c1c12040103401d44040400507480764099803042020443e5140c000d81031b503090051200701e5601d080310940c0071406420002c0a0705e90320300100d075141a40c1e60781c1d2900f940c402d542d16 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 203990584 1250 203989334 203989343
    0xd0c02030601082b020a0b0c040e0609010b0a0e30010606020109050a11010c0b0108010516020c060a03020f0c06010308030a0f090f0b0910050a021c1103040b090106050901030308160c 80
    0x8108200d0020212244e0381107840980182c03025081c041c0d450304800700080b20302c0c00d800c040c04103041c05884a540c28156001d0300607a0f2000c290f50600840b01c80c03502461700ea40e41044180f4507680c20584500101054041000548041c00c01540342000384060304c1c0482c0e038045611703040b000644148140600b10480750040d0281043c160036445001340c0f0300344801c400c0d0500c0f844d103620b84d0014090100b41402032031070000000d0301b820940d141d10383c184401c0c01c1c140215840031100c098550b84800c21104501c00b00d003001a07951110b01ca102140e07004800045000e801204000401e0000100003980701d0f2030800410488081516610004c4a00001c00580722072402100c400024900b5002941c002c3e520900310340c1e04510800501040d44d1040b15500ca8807500411940d100400300030180200c0d10f6800c000f4010410415180c8149000081c4060040503131074011070021071b0700390300000283c140500034074043d40e181d080c00350860009a1700b9103402c001213504600150f1089186886c0c0c603502c0f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 203991834 1250 203990584 203990623
    0x50d0b030a0f080c010207150b010807080903030a0c020c0d062c0a021314100503150c0a0e01091d0615090a05010503070e091306050c0f0f16050d0c0203060108 70
    0x654072210f116400801032820389650810101c800301e210400742000d040c0400d0b50108450b81e00000050030ba83c0054120b00500800c9014400010400700c00e0b640c0c0904410300008002a0b041c034201d26200c00796401c1364200c07041284071400e0101c26004a060340d8011080191010040318201034124100a150355080e009107421703038018507040a00c00c50030742484401181280d038450040d04480826541401c011400843c00c006070b0400740880c0c44003142030b01c20744400d45884c10010159100d1540c1786001c014100d00d0140c5240e00600d81e82c07000d4690100d516003000b4440c19840c000420940301c2e80d110f1840204407960384d024280c01c95081400141420109030b00e00070054516402c00f800100520a941c20308010b16111110b03c1449901d05248142c008511400c0182c1101c81c080d01400c9220020031089031554043d004640660154003080c95540054001d0910b0312051100e0080250140700d480c000c1040e480000400c0160084040e80c0550b42d84481280d0358805124242e203503034a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 203993084 1250 203991834 203991863
    0x61e060c0b060f04020c010506100215041101051c0f060f18050703020415020604060f0501060206180a2a0b0306010207060309050307060606050705070806040b0112060e0d050d0b030a 80
    0x907403140030760000d401505280c1c0941d002c000240580c2c11907040802d060f903445040220074504120283c2c460801800980403402c00410344600d00900180042c1c0b01d20200144560280d00ca5002c613079204544105215042c404003001030050903108886c1c14009003400d5010802c584d021501c0c074215601e4950f01580f0380569030284000d003000070a03a0041c0341d824840000c244500f0081c1c134030b40c05103941c00b4210394030b0603281260890707109030041020742d46407000612046400003041608102e40080c000380490500361018900040e074a00201128030095503a240c0040a1081035082d0304909013001c03005407200c00000c040d000c01c54850f80140c0c0f000d10200021400381e840308150a0048040e41c1c989a4580c403000155a0350f540184000f500019848080c8001404118068203052020f06100d0505495814000f035045c060000425002c1c40800200403c543c000c1e000141120709444190f02ca104028005400c02d2201150f61401c1080c860344914000c2801c0c0d00c078543c40032491407000d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 203994334 1250 203993084 203993093
    0x4030c0b1908131202010606031401030b06012114040308060907020601172a01110a020904030503092a100306080a06020a091a0304020411120c030604090206040306061e060c 76
    0x600140814556105860f08400800c04031070b21410488016000824080d02e03014004046030700034031000c4c030940070032001440082e401e50a82a080341003407038225003078041c04003101c40d01e102e00b00c10040218940340010794151038143d030451085001e0744908041340e80c0d9130103108070011300700c81c10303001a08054014000c103100d0160f04801c40e0b070b250b400c840e003020704c4844001150186400061451001007251000703036078851400041c101642c4003800c03170341c1516400316001e0728000d04000c0c1880004800101410300c10405050345a01070b203100d02e0742c6002003024031859042c102080e80031f0010080145040c0b800303401580c088580c0000140140742c01901d07000f000790030140100e81041101700c00001e800c0c100d10101e411b1011004404c580c0c90070a0320401c02100d81002803035004460905c4940e41245414940d20ba01c0148031a100342d50b641d030080094010405000e0003948203502080100512103158400d20544d03040c0042d54480e0b000000b0751200c041514800c1000103042104685d0025 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 203995584 1250 203994334 203994347
    0x90c18051503010b03060a0513080d0506090c040b04121103010203160e01020309092a0c010501091413140f19020a08010b10030f1506050a021606090306090f02040c020304030c0b19 79
    0xd0318012450701800c2e41d9000500d41c0700c4488042f0715900c8005000071844e01c52441500940105040380c41d2518281502500b40101d120380071014020100c0b42003882014082d07404a520014001c5540789020703a00c1c8047c01010500b58000981000043c1c52954000011948080c2d0010329542650359040080c41c0b105085a0b02d61140814804520407010613901c0902050719445001003155818200f48104440c209810480202803002c24000800340780000c5030052074001112903120030142e000c941c80c2c00c80e81d042241041c4a210b00000c44811100b1a111030140700710307503a098060b5a0302c06036090300c014075081c5078031584103c400401f25010b03a11400c0000e120202c040781002d00300c101401110f0036030348214003181d00010400c45d800c0c1e05003c0b80261030817045407628000d0900800400542c698000200b02c5a83c0b49a0780b02440744a014042c0700c0d560041c01072000d807002003c029100d4020b8481182d48042c05000440d9481c00300050f40d400e40c2a486040440300d50240d000c0701e02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 203996834 1250 203995584 203995591
    0x3090f060d09120206070521130206040b070c1401090b071509031e030e12130b0301030309031202010c0e0d060b0307091e0603050709090c18051503010b03060a05 71
    0x8003000104802102402541042c90046801c0c0c0e2a94140100190038039100400041c20420300b0007852400c024440d000c00705082d10b41948108560f1290341c0b2070043c1e40a40d0002e5809140400d00055049010005200d52031003042d9080c082c1d03686605800f0000139000342e6501143d50420b05100c0c074400c0002070302031a4040c0ba800800d41c15190f9002e000c40d02580800d030b0014000c00c0b003039422100a0b030040301c04440e0900e030800c0707035203020304506440c1c64501030340c40c0080c03000040380308580400f000020043c0031401d01883d80d03541d50389001790140030240b004507090b0001915090300c060040c421850300c0c1d00d040d2030f503c4210800c1400c20101e18a03c600440e0000d036101010411520100000f40c0a00705505001402d8030010004402040c00407443d00021800c206051000507004504c44088604102c000b0910180602e400c0040c2c3d00d55402c09110111481105203468005400a6000307c40041c1c40c41c6a0b5400501458240c0340803014007034040c1d0103200032540120031540141c2d0f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 203998084 1250 203996834 203996839
    0xa030303090305160b01140d0b07141c02090109050a0308070b040c0305060a1d19060e0304150207060e0409080316022d070501020705150a050f0c0a05010f0501050303090f 75
    0x3d4012440d041e03084000e40407000340c8454100c10018840d4149004481c407c01400329412140162a50340351080079100030194000c01803650701c54145000c0040940703940c440042c00d10442411402e141c0c0c0c0094020203c0306000810080e0006000d00f00360368600c05882e040fa4140e4508a80b507103400d40d2144014008480d0240d540000001198040c4009030083c40100e0011a2400191030701c58100702003850fa0718456041691503505251211002c918401e42c80400480d074856000c1100d411401035502070403441800c8506400d855a0110344082912069110318084410300818401250a840350082c800030040000c5114840c40c8260100e5403c0076104445409048104007205404491102e4040070349490300c2c42e0803c00107210440c05440284002c04840e80b51000082a01c050394151408001000034060380b024440c03402c41340c3d42d107400b16080f551403000410a40e40c4904283c000d42c0c9951a1003252100b000d11400386074120350004001b1424141c88208111020004204065 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 203999334 1250 203998084 203998087
    0xb1006090b09061b06040c14030c0409060b0405090303010f14090103020f030a0804140901170d120b0a062109080d0e0c0d08130603090201050a210905030406090f03020a030303090305 80
    0x282e002c8015002c8100c0c4c68150160405041038034007100c2070f4250750000302c241c44001c032500044e5200040d0140f0108001c0700d0100740341c8801d0070308100a100c1441c01d150054104020440320400000045040345c40c0d2117a103041080d0307217019217a5000f08581c0c030300760302001c1000100f000d80380104400a40305801016910300142e51ba603140f4a81d40580d00110000005c85100100361400700940313401440f060901c20541d40c0c040e9401031302c5058081c0d190050016004d4030324001203540c0d01504a06d0b0015041500c840d0b20f03076002070704604039204d100070030072a03000d441c1c0c105c11468003030450f4450f4081c0005003010102080003020700020380d803282080c07191009840469540784001c0e8050790046461594610711601c081c3c5a1002607005101410704000a203030050344d00000700d0700380c40ca081c502043c48603003c504050708010204082c0c20b0144c10b00000c00c083c018040020001c540b40d680341d6101e5140d854030010b14411440c84003035403200703403404100042402a04000c40301c0344a0718055 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 204000584 1250 203999334 203999347
    0xf081923100617011505030304050105160b0910050a140c0d2a08090607050304060b060702040c0f020f07050a09020a03150b09010306270902030c030f01090b1006090b0906 75
    0x140441d84203074804103800ea0800a0190f001c0b00030720a031101e0b4846200b54009450030714000c030b543d0f88114401d02d8100000011805680c030f01401e04000c003544d0200c0d40000034141a070266507036030401200c030b60b100791500011a104000c0da1040c0310030042c2040004072076a4450344118000e4024242145403107803501403600c1806201c0701c0c00880940040201a01c0f844183c100410b402c000400f0240254003690600c40c80c2504202901d0348140e2280000c1a10442c0703201007103081c040c2d6007000790454181070701c1c0910b150308080407000d220300d642d0845130b40700d0300615491360b981d0085c41075a03000181c00400384060003603a0020a484010f504004c142c100c1d01d03510301b0482240503880109000000305070b4065669041c001c1000a00560340008c540e498480d03c1403110200002030082c0040da910f1142e0119202408060760070040117090740d0320901109446406400328400440d01c3d0320213000020a01c50710f04000c1002e5942540c1c0e918041410501000516413044a00ca5807150382070205 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 204001834 1250 204000584 204000613
    0x411030d120e07050a03080c120f07060b0a1d0a090f120e01081b07020f040f020403050c030d020d1b06090614090703030e04020a11070f081923 63
    0x18419032450554a5903034203519180d80c20215a040c80e14103529801c5850200482d980d50302c08407042d60380103150f040d43c4500b4a6070316482e2124088040780b1150000c101e1150450540c006801c0080c003036881400411000c6040084128140c080c00c0d407404054000071221302818051183d0260712070b6000214030545407940c503a5003170940170455050180d50390609001d5845524010300806c2800c2418403030403c45041c410007140d03046e94481c0d003800031454000707656510500c4407a0410189c0100101042d13940d20030040e50050206030386610540d64840e0b401e0600090411110007258050b200c0c00b2042e00007110075070400750f00220402d234465000f03408216030b4410006414070030b48001903d81c41002c6071144448008054144503004903400b040402d0b0071081c800424003084400680c0d920304170006441061144030b040445204440c004034510b01c8003c20141592a0101142c01d01c40d68846070b42130200d020342008009072610100510384c142c00d500c444102514680544400c0d1011624 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 204003084 1250 204001834 204001843
    0xf06050405030702120706051b2b030608030403020f360417031026250e10030b040204020f07030207051201020c1c021219030b1e0108041103 62
    0xa00703841d542c00009144045240562145401880440c0a40b5206150110280103070103000341d04554201440d44085140c182071040c1890f6800844103200c00340503041054a846a818004502003450004049880030001098a0450b903005120707108000a078014842c041d940e110355542074412010030416021400500200d03402c511006c03100c040d04d41414001c0300d20200a4804181003403c00a001e00506506c0514080d20300d4a42041c9044500c0c00146031200451004d0201034083d50700d20008408101c4003520740280128a0752000640f207030458507420b0030503250f13000100359483d410400641c040c080c4941c000d0005000604002d59600f102c9407a9112010460058020f50004d05c55458490001281e40c000440210b003000030300e1103001c0c1e9444c101c41a9801c458000c10341401024803c0024031204800074510603161030694002000020400c84602c001c6410441d964000b401c06d94108101900c12080d10510340038000010341c0d0500002c1c00c1952040a040300c1581961010003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 204004334 1250 204003084 204003091
    0x13090f061514190815090c010e01020607080612030a111002090d0609060605120c1005130e13050a14010c020c0108040b0403110613050c0301020309070533030103060b0f090a090f0605 80
    0x800c00005458641001420071f0f43d0000396905018280da42d040e9140d80c0041c02c213520495034140035001d40c94190001e40750000e4074006003061302c0005042050190712054414844658104942d030034117042c0a0441079000384414242c0251a80000001141d110b401030581540a2140068000c1e02c40d4041420f0110509441000354040c081080443c14145014100c1429034500203040002646405841d840e8500c901d210301524200441d40750b4510714004d03005c090b403000440d4020500c518103080005800c0c027070707000c242d4030700808868503500105104003510300594582c001640e40795074803014050041c10a404000308103400600b00c0c901002500e0085000c9a807980d051036072460314174681740d104213003d800380e4010300900c4084a000148002039601c1260b40304202004400c0603075019a003074010b142c4030103004115420303031400c4200940c10780f801003c00307010003c2004140b14403003040002d207a030000ca0000006d00074039825400704080c6c0e4460141102103a01686840b4156401070303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 204005584 1250 204004334 204004363
    0x7110a0b070b150f040e0102041508061206070f1b020d05070f123c1a0f09060703020a0c051005330402070213090f0615141908 56
    0x58040140800b00d4005039119480c610300700b19112180000c20642805981228000c68888113504c901a0b030a4059401802e11f104c0f5000349180951801044008280c800500030302100c0501c146580780031030382d20f2042000c0d403510101c407801d0741c60441c2c00d9145001e118a04003040c1c0302207001030b03454144407001e4078041c90003043d02c5400c1844a01c40c1075420750142c1c01c0001e14200c0e01300065090610f10114140c1211001e058905840c000c1181405201c1d10b405543d042c20404001c001c03200c4e00d500e0b2260440d1035010215a6040e004140480f8252010640c603448440000c51443c401c0c0c004004ac40114a8080700184040d030f41c1d030b4170f40041d14100c000519101c1c1d040180300d4000d1106d17220310302081a00b6924a820b030710a1190325a401640190246800199038800e544502d03a110010000000e4204240241c50030114441c03500c641c802c5440600f0a00e0803030030420f400e10021b082e240032a440c6040c0c5807003481000005441541002c4241c01445800520b00d4418410110b408580 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 204006834 1250 204005584 204005587
    0x2d09070305190317040203010b09041b05040506010804230706020f060604090201080714120a1b0302030114010804021201060807061710030b0a0603150f0e06040b040807110a0b 77
    0x1980303482402c118608940a0540c1011684407000c60740c41040010307101c0350103d01007815201d600201e4054148400704e03d400c51902c00038001040006042c18149420b11400081e034079840b10f003007109a40c0e0558100d40022058408280890940c6c40d054450204100a407012130b10200d08031800d00003164007003000b50f000350407040c00d120814040680e1003102210100440e040541c006416814050078400422800303480c41c80085000303100f100c87c0100160b00f014003600d00b215810340a4407011116101007582d030b005c0030315002c0c0a4000da0f41610700400030440d801e6102401182c60303801c018016070b44400c1c1c0a408441c418800c1c850f900c080c150b144041c000d00e0303040c04405800302c80344046540035003240e602002001000c0013190740a0f40c1e401194500a519803401e03100241506c0c0d0406442ca40c07059800310403084140c0e00c070920340980b01c0303014416081d882c50a00e8071140d00f00e4024000c1f40e2200c1c000b9001682c000000d0480781e02c02d00d40046c5050720301e004210079071180c0e00700c0c0b0001c010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 204008084 1250 204006834 204006839
    0x14011409101b0228080409020405031603050601050114070b0a05010e010f0308270a0f05011103030124110109050a0314030603120901090509100f1d2d0907 68
    0x10740d0040d03440c0c42c440c02010548010b00c402c0c00a541c0d101c000d0741d070408070424450700d0350f140ca0040e14035001250440071258595844d0800758000390b1040c414548280300c1c41042e104a008070740240000c494000c4060800d6a107001c0064454008030b400d40190510704100c200e000840c03840301ca50180c44030303040020b2150705181c20540c4400c0181c112221078050500108000703540d50b0115005040d010b0b6512103809520101c0c641d82800c2c4150146c1c0c8203442d201c000c00c54001c8030401100b150400d81e10f000d88008000121910b038402800303100c10004003000c2c1d41c1c8982c4041d800d007582e510418508104100804001e0300c0c00c4540301c40c01100c26400180640c1c0a0582c0885a00c040c0c403074607006185141403803000241da9100d0b4800016149401203001d805a0780900e9807100203080c0a08101c0c05483c01102c0f000703e04041d4000c04d0303401c2c0980e4002040d14060300c0d42c800e0080000050500c40e5444e40a00c1e90018100b40504000390041c00304d068407440480a2401d020b070340204e0040c94103e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 204009334 1250 204008084 204008113
    0x103050d140309030910120c1106010603110403060b01110303040605040204051023041b09090614010c06050421030911030f0a020603041401110c010f0c080414011409 73
    0x100070a6062a0800c020700520582200100844503c07400440d001c25649110030019035038130180440c1c0245062501100c0c0c040c080e081184030f00058054019505103a0301c82c40160201c40700c0402522020006100610014a041e8800780d00604141005620300d5401c200640c42d40c1c0c411101260001e07120024441141445d000d1642c11198803810700001c28280340e000403034001a001000203c41c0c0300354500307400b5191507000100c12035009414240c0380c511207001a1044000b0b10130002c92030f217050750000d11a021070700130410304801603607507401d40145626048003a1102400503205401c0114101c130341c03484c20000c04a0583c40c90b48006c42c030500b0b42d06190102107009c0d810035000c0d4114120b030349440d841c04109000501d60444080351242c0313a6040070300d107902d840d40c902140d41d071810380300c03804504060010340544014240203104070103000a804003501c451850000100d0142c03c00300f00040c6034903c0c513a060388411800015141d6071003e40500513402550324001c5038000d60b0070521680c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 204010584 1250 204009334 204009347
    0x190305100c030203040812070c0203010527030f0306010c17030118050a0605030d0c030201020706050124020f0a03030c0507120e030d020705060a0305060a0f09060f14010c1e0b0103050d 81
    0x107400703003801c604603e8184c40daa5014030450309155000280350001030f143c940500c0480810030b0300079000300460716010f44c52520942001140c0108102c40704a8265440d000004032010b41a01000c898199107c2c000152400003110030f040303a420f001c800150346540031000c00380d80244200f1070712005804509a14004840002e0905080341d1300304502400341e42c600044007001901a80340c0720448541c2c5003001ca009000e0114010011420007000090901702c0f44801540d08058070350350494101110f9050380d840c200a10113241d0b90300301621440201c0c0c06580081050030190030140d00d007612540d240c4000140f940101c102040c04144070310103034201000911081102c034001056000e0034040015598001c43c0b0b5080101525000010040e88401d07204400030000384c00713400c091940f0f860005010740644d0040f180341d50442100040c1c0b60442d42982480148181c44804698240e41c0721840075041314504201c002c4400c64102d000a00ba070007059008601a4016007400c80c000f50008099 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 204011834 1250 204010584 204010601
    0xe03160b01050112020711061e04030818010f0804110d05010e070303110106061b050f0303180d080402010c0615050a0305160602070e0c03100902030a0b01090501141819030510 77
    0x84d51040c4030210004100e20681e400c5c0b030408446e000d48075240c07011011900000d54043c0d20281d80d01160000411071845d0152951006050341000c180011000440f61408002d01f828005443c000119000c50b01c954101e40500401602e0b8509100050321020300352042c2c142c4000c026800040300b00103065025005590752000341c002440201d141400003000640c03c03100e100c144c86501807071882000360401070030a4801081c01540d03180c0c5400c03078074908107400c00c1002c44428000c03030680f4000d0b1481030301100e120b168140c68100100b042500d074440241441d60109140c1d02004102203800c1e030b21810b05038000c40c4920010040000307204604c074000b05c03203540000b00755840078070180011601e1503a00d590124041e4200303612551140c030049800d003880c0e880160494400000c0c031203940081e4110011950080c0c1340c0c8480299034000454000c110320500e1604100e05104a407010203000c6152000000024204140f4201b00c410032000440305a1080b52540e00120791490f070035615019501c40f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 204013084 1250 204011834 204011867
    0x207020616020a080f0d120603140d030b06030f04030f30061e060f0203120c04080c09010e0705090301090203060a02070510020301050f0d020d060905030406140315040e03160b010501 80
    0x40c2120041d407900d60300c10312030f4031030f1060000703817111403410011f6580104020350300560b28a409426550b0440e1b00d030041410044006410040c5200903402c0c1003048a0040d500c0e10602c98003555241c81c201c580b1181d64207450100f28008138100d44c606040c5165101c0340711040c29511150180d01001400c448059008507403a198210740018202507404010701100d115040038509a1180302040703045128612504100f50348010621400000d0b080140065070601c00454100d44c2c1c0d41010041206001d1040e003050080903400105070610440182113200405000400e10050319400642001c0b000c80d1400e00c166800700f850340034440708014820481c4514101140f941d4180004901d0b2a00240c40e1980150030b542d01002c1107488007001810003540102c2d040282c152a4900350392a0391240c0704140c0055482c103030081d00401080c2c22030703014903243d070301481c041c1e100c010030300001e405040e004604902090000012512900d130341183e00b18860f0300b1104003981010000343c1894207142081c103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 204014334 1250 204013084 204013093
    0x31101032a2007050f1207090b100c0507260111250b0703020a051b07030b01051c0f0503040302030607050301090501060807120509010b040c02010203010302041103040c060f030207020616020a08 85
    0xc140010440b80103548040e05c260492403050000300711300e5203081500021030f10428600050b0900981e00c40300502600315020001c0f0343d41490300319072107410084068295005800100600c003244141c4075082046000301c400034030910a4003d003112194800003000400000d4250b02c0c032010f03015131182d019070501c0c1113021201e05890f0a803950100808040915900013402a4164064015070341c02201400900c00076400315048651100301a01c01155100102070000c58281740010100c1140c03034007080060684109625428902c100c0100f01f600c40d030008100100140e2014041180f08413155216656254900b220360400c0b590160305c104208088081400542da91000355004100c1d08050045000d80710f108010b401004440c00559005292080d004103594064010314101c80c0219020000120000104042e03840110f4000300000d504240a0001c0c5028940c5a040e040407840c0040c106051540410781f43d9004807000708901d0601420300c0210f103084207180010b0f00c25034002c0d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 204015584 1250 204014334 204014387
    0x10f05040204271118090d08090c0d170f0a080f09031c0c032a02060a0c05040b0a0e06070b010503061e06010f05070204050c0c1b0a031101032a 63
    0x20300800214005013032450810100003260f8540d4405250141200200c5000d42040c2c0d4901e03031303905121196500070440306070010b6485040800d8a120560010305400130010840c1c1c0c90700915141d8003001421407a0a00002c04140082c00141924240540307a182007030801000c403c4103200018410f9055610030417008228248071040891074004071200851407004000c800d0f400351550400c00d00d8102200d4510a0040403120700030354080c92680c0a54201c0d49641c02c00400f17039203004c4014804103804120821601e20128010461a25140752107000345e0005070008130a03074001e05040d5022412140103004038901400134a410080140b8880300c02d1362407184407079a0000c000d00d000d042c080c01110000341c19005904070b440c8294010010000e62908ca50b400407d40c110380e280484920413041100107410903a0038540070440010300e4551001d241d96114950051039030344035410191103803ca1078a00150308010540f0080c182900709000701340000c02419160045d0202e003880d461f00780305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 204016834 1250 204015584 204015641
    0x30304031b03051b0f060f090301050405010f2003160921060c051206100306030519060b1504091e09030806012705060304110613212012010f05040204 66
    0x100765105c07105035101d64441c2c4850414440d1400b910071441c1e050b5080400304400c104042d800817221821b600810000c01c14106905441c1282079000c40d041c40e04208042554101080c28002c0481014544501e07143e407180b02c3c207441c03c04885044114045c02d104441d04001040c0141c20100c80c05103481c070704000803030136185694500070346118002c10501d51a0201d25101e50803403030107181c1101c00c4962504445031103008211100c40705841e0580b8200b0bc2c42094600320411482844c210189141486e08200000b8000e0169a0321078105100403100444030441c0c60203800e800f2802600c40c03044902e003c0001400f04e0700e0b0040800148240008030449106500540030305489007a180c0c207031250785602c3c042c6e8140740e04400c2e00b82e03c2000802d9842800d2401341c2c1030010354040c1e100503010044504040d08865000d40c0004085504004c400c48115940c210122040c1d00d00030859104507801c482034070708444c1404003150026485500b04401c2d401d180c002c030199500210a1481202c0010340c2c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 204018084 1250 204016834 204016849
    0x112020a05090f030f012309010506030a080d06120305190302030915040501110c0604030f0201050c03040f15110904061505090d1106030a05010e1609050f030304031b03051b 76
    0x510b144142e04918001e001c5031801c01400500100300002000024005601d1000d40e265442c10048004c46140010300e8104041c01818040c0f5405002400114810303a10305546070050080014001d40da5100052004408405c40d52024025151a5500c4100c04049101005100014001d0600400500c0300300500000c10040300c207504402c044003611b6500e002030140c0345440354582c10385008a40b44420103804210701e80524404c0d00d13a040d05601c0d6210a074241c07601110303410040340051000401048a042c0c0c401f114600c50125210030682103000d5001300c1d10b410340f03405540070001c5103c40460501d031059202030012a80c1c2e40f0800c2c6411600140a841000a580d00403c00603480d041008600d08401c81d507450001c011940700d10741900700c5402088244510943c2c043d040010844015090402001c241d46030355604500398101b20510a124015401c0550148000c00c400004260f14100304a485100a85007081113859414441d280c0444880c1101d8a0701803003802d61a00d03920b245 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 204019334 1250 204018084 204018097
    0xc090111060415020c010204050607120f032007021c080301150908280f050307030f0c230a060509011505010206010e06010c030c0206030405060f0a09030806040510050a0807050112020a05 82
    0x250140c3c0c3c40100b005250302a018551009e0307040f200100300003041003414105070103881a103503100d85911140c68000c50980300304800380d000c4001d0010380c002042d5981001448882d0000d0710150b0a181c00c410016070304250b8a00648110001200503c50b01001e10509805035003903191581c1101d0a004003241c4600024180c1e40c400d04825510840c1501e0010350b4480150700041c00e034146100c107043c4542c0340c0d07210044c201c00040c620329054148038055040710b104147c118251160400e094214580c03c4414440c0c8105d2a00c0b80c04c803c48005541030180510410b00700c0004a00056201d03500103113825a03821040c195040300340144080360130120130590084092030424040713400d505080d910600d2a1070040c1d0049000802c10050100005206020f252140074181746030380d030708490f6030851707072030440040003d81035101240d00383c40c0030340046400855442c6c00360f1b80c2039075460005d040004954817143c0c0a81000404004560b0000c419101d5500110029450070110440042091280e030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 204020584 1250 204019334 204019373
    0x1090b03150111100213050604081009020102010b130f36570b0f190801061e14210109020919030c1208070b0c0901110604 54
    0x1050a0354035a02caa4101605003c880040e80c60500f201501c1c00f01960045c1c0310b0580009001c1400552070070b001044030200c456020240c043c100c1c07400005005080e804134141c1c1150b4894117002c0079640d5210507507602d003014100001d684a44501d044007950221a60f43c0c504401602c85030014401c82e9042501c2505040000c5980420516041240301c0b035600086028500d454800541c180b442a01141c11030b20030906924401c038040703000003c400015501e06616a0216070810044115401810004401100d202e04080c4850000107034a09100380d00e600040d00c88004002c0c180d0400140a400007480b00c803113044030498100034144e02920101100203000005010340f00840717083d14940b0b07040e03201e840c40c142540e40d6205d407000f039001008840d12035460480045101c51000001c4403c07241c2c46500101440e02e0410369244030001c00005039104241000800002032a00044030b2107096000030540e140d8103450001010b164100d00320b04440d070b00c00c1050001190642002c1c3d820030540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 204021834 1250 204020584 204020611
    0x308010b0d0603150b12060c04060e040603060f02070b0f010803030c030a180309061b05060606030903040305060f0a060b07021f0509030a1115030f010330030e06010501090b03 77
    0x410652030700814190384054180940503040300c0e00780c1803980214601c81404c030350300e050159502682c01c4d00e07884243d400c040625001c1108100d42c0b40959a00f4440100003000060015a40c0e102e0400b503030b07030704502120142d500055041c00c0145400d0300c507402c140040c6121882d903041564140e07a80c400501380e4540150040300080c00d90480d600701083e901d51300c0030141d01c8003000707203000b50481c3e0260007181d011070701302e004a55000881c0004050580e03001802485192140030070f002e2603900240c0402c015000c100000300c0816000c0010701e00a50721031141c0b48441c6050701224044586030303045264100c20401001c0c001d640c600300580a440f030b0120340446036100c0d501c000d071250310498801c00d4250040002017030512140c6180c03003480302e80c00e9076400e90b821604984031000e440103d070b580d1784419003440184041901004404c603500714005a014520380c02061020950084038504000030b602c841780b48a60440c18081c081c01400203081800c1d52504281c00503c035404020b0030031150144 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 204023084 1250 204021834 204021847
    0x9062301030f02071506090513020a05100509030f0c09060a0308030a05061306062102040f1802070804090c1d010909020d0207060615080106020a03080a09150c0c1506030308010b 78
    0x841d41281e80f02d640c0a00e448030740112401703500f009440e00e445421055440c10001810040c0e00540010701140e009090800303090606040185600084d449801000360a005d200c400340c0b802c1207140c02400190340107001010180c0100030f01110700801e03060103800701c040200002000101030b48e41100e100078002c41c3c1c40c0d4400d80400c0502080c03441c0d04040606281c0300080e0160132041c01c3c0c05100102800307416010400307124005074421842208910f00017071a0801c0030548010306103455400d00000517140000035241c501e500d0300960040c42109603184d140034503d680011400b801600d110010543c503802ca80d00190490002d03100340c004442d00000d09104030b220365070440c0e0041d940800b040090b681c5914800503008904041c00010403001070010440600024004e140c040c0c0c142d43c0c040155031540c10f01d101511180c442102c4481d034054140d440d41c5428000c0340d507100d42d1942d0b0010091640e05152809203019201e82c03210074545802840401e911080b401d0542e118010070994418 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 204024334 1250 204023084 204023111
    0x804060b0f04020a031a06030412211a1201050103050c040f0f06090c080c0301050306010311191401020106090e03040b130906030f06110306030c0f0a080a0605010906230103 76
    0x410307091100da801440092000d6405400d40d20895082581c90300707058442005509124a42c4000e44002d04500d40701d000d4440c02500ca40e0900c000fa504001681c007110b009071190030141c407100c6880300e010314581030781400307a03090009410045408800092000d540340d03495180c0c079a40b8407541d1a014549500b49601000039607046160410344821f010003640d81d55100044c0100044006980000c0715507004c120446890b1040c1d13416290002c002c2c00300341c1d00c1d6079500d980c0c5404008841c0c3e0080080000300d071406804d4440c0c0801000c0d442c13039810340585140002800c50766180c20100c0100e01d04032902807060000002c3d10103440003c541a6075a0340310700249d10300000760754440305819040410207c10004148004080300e0b1250800740b250300d80c2002060380c1800700b112a00d4140e4441311800c04507180128042035000c1018016402c00d94444001904000c0141c00603948180c0341d41c0100207821680c459a002400303081c4013554001008840c80414841c40d140141c105500c4050038880c04 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 204025584 1250 204024334 204024349
    0x14060f0a050306010e0906011211010f09050d050705030d020106061b020102070b1c320a0e0304080604050c09012409120f051b0d020603100305030c0a060b010509010804060b 76
    0x8107070050459005694600c907180800d0b0040b06c481200d0b0147c1c500014805035441c00107005c0c158890401c3c06451609001142c040403140d610004200f945007000559484e070300c10074007180703010b40d014061450400e0281450900c18441503421a0300d0f1490402c03030a540894443c0700e01c004582c0004800c40700c1c0c00101c3c40d00546c0d4014042d54080002c00c0c082c15060310070300c151030320a13180c0140711540c03104a102042d114040060400303100f44103041140d0700394100240d5402280302000081c442d600e9190305203075400940110445501400078001400020811401e03007280c1111a40120360500000b004081d10b101c402c0340c580030000d80c961a1090081000001a203040001c150100800d030424041215820405803503900175045e100a2103211001d283c80d17203600240c00203d111106500340440d540c00201602143c0d20781d0200403000440c244018035622034060001c021041240c02d054049814602189051080c200880301c4c459070402c0140e90300075049100065200d00c0c42d404280003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 204026834 1250 204025584 204025589
    0xd03030b33030c0d021210050105042102010201151d01051005040501050304080910170a05090d050f04030b0406140f070c140c09010609090b0312040308160b010b12090114060f0a 78
    0x4903070020600c400e1b13002c1c0200c0f803640719400c40d0246000ea03035901d00064800c1c0c0318a010303414202aa4010400300900d420f04640c0b1410300c18400054010400c8001c00170481507508000240010076104000000d000f141d8680034020455591880e9203000402074110f02c00c138070603030f4140b03c00440080c01380021075041d11003d1601410610070a08a04d0004110b41980b000d246010b01100001c42d050540b244650b074172800c40302000f02912002c14006440c0e54100404120519a0412020001661450010703000e10f11680c004034001b13810302c010040b0f100c0002d010700c1042c2c031000108a1f8550384060751b4011190080007410b0024199000c550422080e2500950400480d10000440b5030b48860840100c40000c2005c001820401d0209501c0b10300c01d4842040303040c01484103101040c1260000c000341d840c80078228070080460398440105000036406000c52085c08078a49109140d88040703243e104400500030422080400381014900c0006014ac070700600884c903400d030580c0c6400140360701 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 204028084 1250 204026834 204026857
    0x170c010807050d11040302120d230d021c11030f01030f06020405040212060307061106010e070905030a0309030203010b061204060b030f1009061b080a0b0d020d03030b33030c 76
    0x9604144e48404003607841031200320702404041104001685012401c080d11000c59941c4048100800c651240095480465610079860400400c0010f408620050080d143c00410f0623000150b400448411110600313108036030640d080003042007045c001200141034070751103011070302080100e0030040028000c540045402c140b000401080741100e03564082d00c1848124101c4180b2900c0e2982100c4030039005410b2030313071a0b01250040c001c0505c00e0104179884209803a050750f00036501c10029150400018054000c6145644180194103080c050081130900513a01d40b45407890559580c141c1100007000507051981e641c03411f03c40b07650148801e5242c3d1503040d0440d0783e00c4c08000d4650009290b1700100701c2e2002e10301044603482c01d1442045030300c800d8860301c1d03128265482561000c0506000d820b4240d1040c0644007810050717035460220769501d40243d5001888a001d0310920400c180303070545c120381105000480c8100c8a005410035504d540642c040b1940325103989881311810700900c04e9034203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 204029334 1250 204028084 204028091
    0x302040e010b03100504060b071113060e04050706030204060504050f040e061e0f0708180c0a030b0a14090304091a09040f02240a260702060907170c010807050d 70
    0x1020b41d5218061406070341c410814415040e42c40e0100800c40b9043d10902c800342d00c041c480000402c100d508950807282003c3d20705612600e00f00f40d000205e880c3c68002e00140c2092800740002c0c04020803120015140d80d0508518007400c11034060b0040c052032050b87c0c4110003030301021196480d90341050360204c010b6000c030307041800d03d130103c51147c584540c45c20800b4001c43c0c0008810144103c1110f010301d0b40c5480e034014a4071a81c40703464501010280130762044c81090400358084c0c5821003600000c1d8001c2800081905155403500140c521100001c1001910a400c6c4094200088101c038100d40d900c0000083d002100241e50380e08080d080c00d91039104290100304014000b03600e43c0c0307100c0e05c1c0c0b003180d0001214400307074504007500780d03000245078040c5400d04c00100b425025021954401100200c80f002c1210b0b040ea05014064086400c0801030b0498030070312034031110800c0301d80050400084280c4a4040520115a440b10601c0b40b040c10044e1034070100314210302a10484030341100342102071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 204030584 1250 204029334 204029339
    0x20f07090b031516030e070b0d020304021e18090f01020c03090316140405070519020706030e0a050604200d0503030613060311010c02030111040f03051e060708070302040e01 76
    0x404080c00101d0083c021580314200140150000d503104408410030b916040c080310204130002c028071080d11010b4421070340045141d08442014200721180b55002698034940b920600074016440d10440105100501180b6400e9648030704001c511074012141c040f2658901c1400351238401d40510311042948002003242c810f02c0044001e05203c1170580c1210980a521500d45200c2d031031510074081d4030324284c9400c030380070b1805401c41038008403c0d103482800c0c50010001191541da45450000140c0e000003410051160940940c0e030a45440714040e04901e9140c0c7c458a0311464014002402d0380003440c10000e00b03403255901403020071303000707000e268880c00700d45081a9240c2c4142da80c14841c402e000d16406010700c103805100180c0380d01811500c1004482c1006541486a405040303038595260350641540d0302502c0090310041100c89541120035255040203800e00c1703007000e281180008a00d070200d001e0724000403e00d810940602c1c0288041e0b90b0140100d00a0041e500706400c01d03c0e180000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 204031834 1250 204030584 204030599
    0x907050a06080603010c111c02010902061c05090f0307081e03010f170d09051201140c090901050405040c0302010c0f0219090c022a060708031312030b1f020f07 70
    0x180f072040000364001c2244ca6120b803025201741401c02c6050100b584000c035021710070710344031580d201c00061900000c900340d1000c2d03001031241d1b00b06510051089070740314111030000849020300e0f0b8020318107101410429004140840c0c0300d12840030044d001e40400110000061829055421141e803402096510f0356118220301c0710541c0d55100d11045003080d0509520300a1021501d00074000051f2900452140b80ca824000069400380200004d0355070344505007048110130341d00503c51110400e00a581d00b014408010020b901a0040ca0080307280608020000d804180200d054940909066908d1416450034010303c00e401c2c10300030342040000c9a0b000709002c0740d2011105441c0c2d018001d2142c2c04914404a030380309085008800c04010380922404942d850000910a6000150045161070080e844041ca558001c1d200c07800111000c240000c1880303403e4000d03444e03803c050303d000c3c8442000c0000044030034030518218440540d8113045208184d0081080103186181d00058503105655001c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 204033084 1250 204031834 204031847
    0x80703030e06090d1227030e1201060509010e1b0c06040c0e060a140103020f0c0c011419050306010c050f0c190b0f0307140f18040b0112050907050a06 66
    0x8070701e0034407824011440c60b95000c5409404ca840d00d9642c500007292102048018010300244400e9a050501020080c99507640c45001c2140c0139441c4c0404166a880a0002100307401c250300000380d02d88101400345540f00452641182e15480c0518016125004910300c41d5410400199010000080e100300a0f940420490721842c02a144401e4480c0d56607400c50964104032090380e8040b00c0030800344000ca92445602030310b10030601d401800c10200c0c041c0b040d4554411003508000d9130084c82c1c454629a440410b181048031030071a21030900c807100310000301e21451095981d06001b0084006002648130b907441e65503094018080321807032040d0b000e10304e0b20b401005489a002e103044041c00440b913030033071403003a040743d4600311ba840c5000c042001e400240c0d04044c121404001504c0365104148858402415410001100c4150f8621000c0050f444601e02044030034011410821440c03041e80c1c22a040c49100c1d00c00c1003011565075100661113080c62001c2d00b0590b4443c030b00f81c201140244c1d1242 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 204034334 1250 204033084 204033101
    0x90607030e10030c020606010804111507060e0d02030a14091c0b0105030d0e120309060307090608100b0306060a1101060602010e0c0307031707030504090f0903182d0308070303 77
    0x9a58034001660b80c1e00480079100020700b8440941e00510114895500c264815030740030f401151645060303038620000650454480118007035600010584e40240019232003030b43d40301188200108400007030780c1d1011b074803400f405140ca400e0005102c0400043d603181c1040b2030003001d0003052400c600340c60401e06898040805819100180311034004506d5040025141580381903540324101c66004d039a0800c001d1010150700c4401c3d6020500c819244e6498090143d130044c044c540703800c613040c1e05000c4001c141c4c00d401044004c03012804c400408c02000240c045980201c030503105507540740b0300c005040d80e01c801e141030304001c03c1d072806800188269040d440310054416180c159a2000c1c2c0010805660744503138080a084c003a1728244030200d000e420030040a010b40702c1d08140d800d00d50340d50402411943ea00840c000c00c6926820087c04050b0310500d01b5007141c600380044002c290405039240701007580c1030140540010b0400f0750003451103200c146500295400184c403507880d4240d14006000d0901003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 204035584 1250 204034334 204034339
    0x3030603120206010b270301050c0c160b0d0b030309030f060a3615050901060f09090308010e0c2503080603030414090c0d091412040b160305090607030e 67
    0x22210407000d640301090440c100d60361086240e0614403000c94004412000d04000c03030750090641100c03901c40d1020f0084038807541c2781034511622100030074a006e0400d41c0720442401804030000b0140711103413408094511b01c0da48104000f03025021038007c40d00d1032250b0600c040e414410b614642d120024000360300e030700c50b6510000a010b0a6007021102081241010314000c110403a50006903604d8040746078010102c0c014601c1e1003c07440c100c04010b0846070213607400951651904070601681c8001c0c0340b01c00061511550401c00e00c1120f4038010203058041c052410441c450784041a00005804250341100029901c94600d44003a20543c0744580d405a50032004694128002070040c6804400d5a0450340c252202880648482d8204940001d000703210b50400c1c0c2050210510038020f0384107081c0034078400c50324029902d409803100c0f403418034400004a0404820041405809010030035204107031310000c3d410f084900b05103001c1d200c9000b40b040080d0015070229200040c103038045029907944005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 204036834 1250 204035584 204035603
    0x405010b010e0102120304060209120303040308070c0201020c190b0d0605030c03160e07030f050405010906110c0c01050903031b07150c020604050f040b03011109090901051005240703030603 83
    0x1803500640340452040da0305400350b0003606038401c1d80b450860003168428840c241c010318103106980002c1d031828030b1014100a0358804003c01c01091f40100f52036070014000c2c04c0c40b03039801050383d0000b50b031244d071010918014000c07000100454000c1c19040406080c039542e150341ca403000c003040d08004200130301c15070f40310b0302ca101040d03030303483c240403030395140e000544002820301c9810000403030b03a5071602420309420550385081c000b0359010580b01c1c1501440c4034000100b050802c500b405800c5d54945044200d90310b03404c0210001c1c1d128005182c0021240a007400c603180e8000d200000e04500540c0740200e400039581c64038445a075008201c0d00190303140054038958041c151a0304a1b490128018002e40021040009100d1031070035205610072030302e004202242c4c3c0325004000c41d081d1030003c1060000000d000c2000717500e0f03240138801d0301c1c4c0c01002d06000700454903040701e901c0706409080c41000e0081041c0d04d20201009400f044400c4029494802d459890950380350040080100d8030054031038022 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 204038084 1250 204036834 204036851
    0x70308060604060504061b08041202010e190603090305160b0f0112080d09060b030708031b06220f06050408123304060f0f030c0b0a05070821040506040501 68
    0x1080d4082d201960b00f2560b42a007420f003491410380341c3d001c2001442200800503404140058180030003003000c1c0014240344216100c103480050318410403041000d2040b1000031050f5182e100c1d07120180308a40c101c0c5800325040b12141401c0d9181d00c00c2c16058852074006100c41011300c00c00c030740780e14021200390042c0100c40c2c0c0c2c3c41320040c803008d10110004000d8541040f0110803c0c016412038401d140c090840007403081c82200001c1d10301101e50b0b101c1313040c0782c001103001034100c0c1400044c44200801c6102070325035403404950840e5441038200307048d2060000ca49400c070900c02400b0b4502c443e90ba03c03140810607820503080c00407064004000355000028200f0004e0480314588000c0300802c59000c0d0001c030000c10040544000c048884001500107031784640000e0618501134045009140c5240f422a0071421824021050701840c1c0203d00300360703400c0000001c05a40b201c202e42040390080c6203640c6500d652800e10030300300e880780d8500c06107001c0a41804288403002c6451030040d4480e0008100007403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 204039334 1250 204038084 204038089
    0x80a020717070302041d01020307030e0c040c021018050d05040504050c07050a0f14120417030a081b0715020d050702010506060a11010605102a0b0a09020d050f0307030806 75
    0x50140700501c60360b41140c001040141440d0b000001e014002415440c100d2602140307490898008451001c0007944a00341003c0500c0c1c00d220856030691b040d1001c1c04980030030080070356140c0e0721f04072a47c0380544e41c00d1039807003104004030441c843c1030748030040d0380100032441c40c0140543c00c80d0041603c11442c15020036000e02d925400c8500b0f00303911801409079050141c0300e6811250300198141c0741a003410303510703021540c0c06000c4100d209601d00c4000d0740322418256034802c40b48640c0f0301158140e0003007003007021058101180d2a0311441d4184aa5881103c81c004440c2034001c18400038110551f07c1c003801e80d084640d801802c80b03040780c4507042080d982c50361822400d075032081c2c0d01141c1182040010000d038a04c078542141044103070030008a201035680020808040f0800e0741d01d00041c48400c240e0601030740e030040b440440821f47c4034011420300d15440310940b40b6409441d117521103030b46845580440d15804032403000d00343c200c815500d29801140c140c58582d40952000c40003d8030396000641c442c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 204040584 1250 204039334 204039359
    0xa1802090d0c1e1809030c0507060f020c090106022e09030c032c120f060f0601020f0c09130501090c06180b040e0705130308071506120f290103080a0207 67
    0x301c006180a44403034003510100e43c0200841c5c0380a42c10021101e40400c00f20314104185001004c06607202901030150304d50003030800b41c0714030426104144103c010420303e5400154a0100403025041101402c40c100e01810314500340c44490160b981003841a0043c5904802e5980a042c02611628585524101c4800c1c1d20010a4001c220084482080000c94100710342140e42c4074807800100c404140f103c513501032808004441c28181c80302c3e001c0400642d540c0c1403140c8054812801c1c0182481e918020008070302c104000c00c4040360b07455560758041880000d40001000c160400c0701c0d00c0c9000c0c0c84840041038011921646204541210030004900c1e81c69000c40b411a10040400200707a218440c080312241d20071081e003005040c080d2404004a50b440c130080140520822440001c00440c1c1000815580f890740309102049030405401d01180300c8003444240340383d220882c600e407190450940c0c03003030480303c41d50708440302640c800201c100a01e040081c500c0030174030703002c5502c425030391544040070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 204041834 1250 204040584 204040589
    0x5030c030601061206050307080705120609070b030a060b0a0c020418030e04020702030a022e08041101080405030d020c01140c0306010903080c010b04090302060a0b060301050a1802090d0c1e 83
    0x141d07011000422803548518031180810700340d00c4000c601c1c1541d480003e40303090740c550001030582d005150108000c0c507000000104407061b10001e440c052030311004050700c0c0d0300a4401c0b041d0881000001421030030f11540030a01400e042c01013240c960320b9540d001011200408400c0740281c4c9004402c044200c140d070a442041603269031020202a448414000603400454049800d84a0300c03860000503556412800c030b00694120725200a8501100880c0140c6150b01480003808000c10502c03000c203a00e201c40030300c0b210080c00c01c0074103500d0b1442c04c02d16510804000481c03892011503540d04a003010b400400500c801e4148080740358031050643c0c06984003e07104035001c80d250396000c000082031080030300a050580d80002640491040108060b00c2d4410000c60058020780c0401520103024441e61044000aa0b16141036604117400318020500c4c034011003206182d800016590078003541c0444020381405042c0d680350501c286000411603000340582450440c14030315240c42441b5041d0139004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 204043084 1250 204041834 204041839
    0xf08011703040501120905010203010821120a02030411041b020f07060206061002030d050f0412031e15170312010608040f06092618040b0604050f0102102405030c 71
    0x7030b00789010011740d015483c00e030407580640d46034180300020440a2001e10700070482c06010b0040302d02c041c0c1440103040d05044282001e05824484c0e0700851a41043e0980e008020358401070f92a2114140414140184c2c1384071644242404e0442c2c114514101c50080200d036140c00f154640341070003020701d4888419000d021300503482000010381610381000405200c4e14180180e80c42d002d40300c1282c034159030f81110003000b820700b010240410800c01343c040d107404000d5460108030b40c14840003c04801481c00e5541000103458407010900008400c3c1820010450503102c11000c80d4000c0090380c80c2e8000e10340301e5118007100d000026580303004010b02e900c210b80c01904c1c031454600d60b580d500c00a06841c0000d4030246e0386103101844d0600d04041035050601042e072340d5a1181c10384075242180c020144101401030f41130418024980d19550103803000c1c0c400880b0311607094844a00101d00d00030400740e2905041e0b06002c2c400308084a2404482488000b03981da20301e50941300c5007407540da900050075054 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 204044334 1250 204043084 204043087
    0xb0901120308040201210501150807021b1c050c03011503110d0602040b07060e2503021002120d090201020606010903032016080303010f0f0b04060f0318030f08011703 73
    0x4002031294192543c041c0c4141050340d406000c20103c41c40b00200c4600449100303598030014440b07003440300380d454201100380c40c0080003450034200094450f5803851854502c49000c41e21005c0c282d40e10000c0100d684550b911344070700c04016041040d9603c100c540d10038000e5283c00c0f0507110806001031142c06a0350040000300107408100240001010301200549d901c550a10000c684242d050005092040c01500003155110640c42802d06141110480e0310700ba803042c80c1c4100484543c09a41011a9011036410b41042c103801c030300f40d080c520440c8814440d04d2000070000314118440e84281a0035000ba421203890365522001911411000c4c0030180108100310240300810712481600441014240c0945441100901d0f0001103006a0b801071041500040014090f1074010401c500c000d22112014100c01c034036180301c0c2c0b00e0b14030940c0114000c1024617104091650f0082c1c0100740e00e40802d4107904903800c01070078014003182944c40c0110000e410000001b0f1000600d001c0c08036207120f400c0c084c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 204045584 1250 204044334 204044369
    0x3110c030f120c0c0706081510050d0c020708101a100c1a0f15030a080301060c0b0a09020d120c08030115031406030c010c030e0a031a0c0a0e01050304020103090507030c05040b0901 79
    0xa1f43d20810040001005205880c11407036240c890b0403c005104045898031900c404860701d040d419039045042101c11540b02003010403001000088011000b4910a00001c071428400c0c1c1e500e0980f51070b12003032034000d0f42885400c01c03800e82c4407980b044103601403520f42621400c1c0a0b40a0110b020940d01c04410f00c0740007000c20782140070104c2110803948001d003251001e91071546c500c07083d50001d9000070040307001c0804440034401a086070a500000103003040003070314001d82c0000c2c4d086400c040d015182c181c1a004c0e00c0304650040b140d090f022a0042480c98036513039265081200c0498a02000d0b000904191000c10b140340300e105c2e068010f0000402424100200341c00444009904c0324040c0d04110b2410282843c035204c8040a10180d8049c4140c032100903160440c0350030800014103820a000f20070810b42d0081a07020001c2c2c01c0810302440c0c503d0f41e84c0c45600040340030344190038000d031090083c954000100011074007544212072054409011920f20041040040c5609100e05080100b001500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 204046834 1250 204045584 204045587
    0x4090b130210031803080612010f0b0319051504140109110a0e060f040f09020603090303041403070c0b1605010c090303030b0111031602061606060315050903090103110c030f120c0c0706 81
    0xe10b81c0f04031f000d808807983c9801ca107241c9007507600b407030321200c0b8403a66a0065441c6003424001d10803152125000d92100c40031039a10365903120305110421601c03800c10408282084551003c2031596905070f002403000c1e00310307800c010803442e0646082034480c440c20300001134680491410144900001031004202555030810311020704503034000c8880d0030395150210030060390f58401030360064040600441d00ca03d4289815180c4c42146850028160710034040f450000d03242085207002d52f0760080c81e0a4460140405281482680d4a402440e550801c5020f218159000c4103403011240603650030b012240c0f44000543c4c0d038120154400640e40c00c20480981d54040003482400c000d4409000c8610300711100100007030390104850200c54694444008100344a0030f0380201e090000403013020003c0f030a20030070032036407131141c200d1850502d9200e52456800349510401d84035914020401e0300d07030312030551901740a258404120803072180b41c1d4201103807100360700c007058924440e03049000b0711206060000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 204048084 1250 204046834 204046847
    0x15092102040e010c080f06090c030408070f020a030318050108010602070608191e0c080c030708130206040f180e0c130e03040f0e0a1a010c0204090b130210031803 71
    0x4166086502c80e90440440c4009110305036000d91243d594aa81e4108034002d048000c4c00607040902c603c401c10280818035130000100c0381c000b80d00100207955518685840580d4000c142d20207035024940c04000024181c03c1290903e41c0003880710300e445100c0e12230005560140c028059800180d020310300512406001c0e8400640101540484160051030320300f2800658031005141d460004110507440c1c4a07084a00a50801c25502d08214205203840301e064803160200404070410064100c0c01b02c0ca242000b8414102a00c2e0090155a03966440701c4803d540000d20348240100001502240d1b403900c4440d205402d80720b10360202811214810713508004bc00c10104ca503e10405130b0321b0002008010013003004000801d015490030340d00600c0d050016420078002864410094180000107000038020340f41020595000d01b000d541c0b03283c550001ca4028251482c0040c00c9070310010134003444404091800c1c0c11a803080300c80e03c5512000300400c400b90380751207a180715026125140300000a00400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 204049334 1250 204048084 204048149
    0xc01030911040e0d0f03140610031803020c0a06050304021003020a09080118030e3a0c0807030b06061305010c17070b0415020c0a060e0c0909071509 65
    0x302205162030039800000c04603a41107801c01019800425884e07001604a1000300c4920558182044aa4001c41010ba050707880101864800c1405036000c4442e580a640080003004803082c04801c003141c24600079648100302c042c118822641c807400042d034541f00f44112803203254050002d200c1c861083c1002d03000b079000081d52800340082c4806c082852002441124840052090310343c036820150309000d400601d158003054080c0d50010b28491401c40380b96214640c03080211000308c020201c0302100c10070318144171001452803407106000100902c0006031441560b001e00303401103094407000200101c42c46402d0740b070f83c80e001010001b0086580150342071120f10b40606c047c00c580d01c900800c40300c42035120b500101c031084000f00600c02440310840c161440071528040443c5441e40c48100306640c0d85007114002d100940740c5411891820f000d2101120000d4040c001d040141000d0340c0e0360313807118464092030f40782c81095400307064205d01c910700180031902500a5500710613140b000c028400511b00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 204050584 1250 204049334 204049343
    0x20c040203150d03021501051f0c05120705010506090f160804051504150606030c091802070804080307030f05070309170106031713090504170c070b031302010e010309050c010309 78
    0x240050545070b01d802d03c1804001d40302c0d5002d000680403200154410042c10380001c1d0144862a032120180201004c0000300c041107410440414103083c03801c28500100c440000310701c0c800c04111201000015000b01d03010b943c1c1214400c8145d500c2140f021016001120a40c020602500c0620703c443d0080304c040e42c000d4042c2040d00e81d43e03078403803190503844101690119440841840c0c22142402c0a10401c1c2c0981210324007030001040081004180078424040c00707581a0442d080700800324941d0b4100c403c020f40c0600055110b0ba541d60340941c0701d40100a081c0c0100c0d5000344103001e000d20034001ca45d4521740c952a0364025a0030312201410051101e0342120071917607107000100200d43d03080c80c0c3c60003901c000310441303a513249600741c01c000601250f48081d071003900b84020702000640e84113425082500041c2c0194507001c008004501e000c985a000900f043e2001081c070150f566250207031049503000b030300d51514101c01180110300f200c0008001410702d4211624251541d8802d4200b0070049006 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 204051834 1250 204050584 204050611
    0xf0a02010b03030a050406030e0601051f050706090807030210090c030b070c0203070f050a09110306010f0215070e040b060c070537050918100c1205040606051e01020c040203 76
    0x701c0c0c5158009001c4d000852804241008001d6040c060b41c002401e601001e0229940740c9804100c1c003481c1c1c0740304030700381c1601c3d4203800004503ca10291070340f440e00418103021700d001034105903003aa1302015081c0c0041c02000611108010075000d0b04401a5001411442071455a01e505600c00c00280c900c900f002004003440000d42d40400880c00686003480180c00d1551500c000c202e8031418691291b90f03910f082400c2d8074410f000d21801e0720741c48107080c2400c1d00702d0000c6180403810301c51040c07141c07c20000e0650134022210351003445980c05d0f403c291420400204202c080000d9800703190340500706640032079003d20003420a1001100a650201a040000c080c408000c51040d410030140c0c981002100e58100101c1c5820a2050b4020803c0700c0c1c481c400301800d0004e1740c1c4850100350348541d803a446c0c0482186891140e05502d00354600d2900070091800c191600c500038181e42d100e035500c10382d0fa540d40d8280160b12401ca03142e8501c030580042030b0000296040c0b0000c0c0d04014041d4213403441 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 204053084 1250 204051834 204051851
    0xb030a111905040e0606091b22050603090106090f0e06150111030703030f180f03050703200f0106090c0f0804060b06030403020d0215060a0b030a111902210f0a0201 72
    0x2140d0245014200310340000d0721240c40c0c00c00074014107c01c02860156050000e00c55001c1c0c0ca4850f100710b900b903940002c0034000c00c0c40c083c0d0050410344100e50146820100c00000c001d2404010341c01502078818083d414070961156051030760941d068171100e40c40517040706000c030b8548901d10000154100060500181301c000e28111541190007020059010070703162402003042c1c034442e1245410304841510840c0072802a03441c0c1c00c010404e10000141401000244041410b0003051030309401140d40300c20003220020324182e075807100000d0b05c441819600b081c2c0003180d031030158020721901c004651b841301d001c1c0790150030440c1c0c04e6101400a50351545e5410404141d034a40100861007207001340c00400c1405804030300240f60103442001484541409000d00215a65062906c030071103554a50b072544076140c01005030028060140460002c03040069840030000c0c400420580c400c5141d005e50302520081480d000c0c03544041003606450704010006400c0340442d80d40a44081c641c144000140e001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 204054334 1250 204053084 204053089
    0x31509250903021e0a180b01090905040c0620010c0c0210030504051b1503011e08030412080a17041506060302030c030402040c1403130c081b060d0b091003060b030a111905 75
    0x1d0300a144281d801f0740b00e90200420356002448840146181c00b410000e40c80c0075144c416900280e07000306010480303961001c1541480d0042c1c2c52140c24580d0000b045003080610010300400d40c000d8089000308040200c5201e428024031070184900e4003c0050544040341c69200d59203080141d07080340c0e0040d04500745004003a02c0c1409103010b00301109800424811800780c50500d00001d920620450b80108818080b54071042c052601c010391005a00c1d88603000a131041d02c2100621820000b0800d512023040284140030307100c00c82c07075100003408001d541e0721a07008500381e2108030780d20038040000b0030102d80107042c6030b4405024480e152400c83c050070450525060564000d41c1c040d486a60080c04010501c070f00c1e0b40c0003600170440000107000100281c01c0b06c2d0950150f11303441074842c420110340107858501c190051084600010300d54020340c40d140c444080c80030050700080d1f40c818506010242c00d424001103c3c080140c01031940d40788044100100a03902c910155551034106541070001802d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 204055584 1250 204054334 204054359
    0x70c120507050105010e0105030c060f040e060f03031903050c0703021e1203070906031a0d020409021309140d110a0b070905040504050d081f0b031509250903021e0a 72
    0x301701c184003070246c1e075142c0001c00d413401112880807072040d0000c010152001038500121800c032003604075021250340d00c3c0c81c00220b8440740c4c5003119406000000c2d1005001007a025101d00004094400b048103032034255000c4002d000c0d1600040142e0700c540d10102a8144044a03105001406c800b11404c8240d400d03500a0181c200b90307442c0d000b003441c02c4010b01000e501406120003650000c1c3d05410900b0341080001e4000c1446100a030145035522601c1056403600c000746092940030b80401c1c4010a070902e002c4e1401400d8023601d01c3c0074064a00b0b06c44409105072400f0082007503410080080c030b0019103908040d608050800e005202c03007050b0005598540317004580c231032401003001d4007280e04a80c201900c00c2900405440c40c60b5415940882d5040200054009451080c1e11440d00c1e42c2d54425044003401c014003210350301c494004100480e24541400c04203c0e801048160004122682400c1d00d009800e40002588107052007a00e1019483c078020050f00c8410044c401d2115a5031805034400e407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 204056834 1250 204055584 204055589
    0x1081e1207050607020c0d2f030303014113060519150e0603070e0a0902070c0302030709140c0d090b0106050a021b03030d020901020304030c09050601030e06070c12050705010501 78
    0x125082407040000d503903018408500001c40550750348002000c030340d623182c0001011280c0001007110110b00051580c17200b20500000160180481e580c81d40c49140070860f80e241c650915070581c00441c941c1c45403002802d200c182d6881c441440d09807880c62a001c020300010340c0c0c00c1e100300d0141c2c6c951000903180e0300c4124046803102c41c940981407a504220b40301403104c00300c03606501400403454035070400d6200d500c1126840b02092a00511030500c26000840b29900c617441076003854008076a400901503005012021240308408440c00fa0303645041e0801622040e8288004420b1500d0005202440d11002803c1c0b1250283d000114100340d60368100707404500380c201d100040c1d404605180f040c0d4041003e02e039450000f8550032000d003034104c0025582d03c562844960341c00d80214407086e080c3d00070815100a154450400da18141d110440a0010001280e0190009007003454407140d5000c042030b00c5002c3c404a0765944008402034030392800780c6043e00c0310001000b40c200248070105e002031154501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 204058084 1250 204056834 204056843
    0x30f15110405040b010c02091b0c0105010b130501091a0f0423030106090608070302041d03030c0d06090501051e24030f010e010b04150c060e0a0c090501081e1207 71
    0x455070700345000c3c4821203010705400c1e4144030904601c080540d4a14030580ea00852589224614409003250400107029812641071150300700303000030038003281500140c01c10dd01d110304000806540c1e0070044910310303c0d40c071684521040340300c580000d111000009048404046030120300d02a902e880380c9003c038501c1500206608149900c10415203828010b10000304000c010a0281c681003410481c0c592450b0b120091007a55518482c48040d041c0c2040416070051040030749032203282c140e154401990164500c950840e19101c1c02040d4100d40344070f2641130b610084e01410103801c9a9628a00c82004904995031100200301104a03142034181c03200801c007056902c290300e81c14114699003148a040e00440c0c200320030000140715810184e4282c40c2101e070b0401d5a0b1010406920040d2018100c007100500a241071004250705003030005511108140304101140815680e8802300013100d20038082d918490300700500c03508101801e800d40303c41e00103001064442c443d80c00c4907000404c0c1d00034041102c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 204059334 1250 204058084 204058087
    0x209010303120b15091201060e07110f030a0e040902040609060603140112021804060e100203150409031209080d2a180909050c0315090c011701030f1511 67
    0x14035421180501500c5043c140c0e40c04e511895102040301c01c078010029200d0145070b0a6850300641c0209400510080c11022110181070034400070080403208403200c1c0111728490160003005040001040300c1c0000703402e076034103100301c54078500f000041d250001d07080e07a126840b05030216003400984138410040680e03440c0010046c034000000c400c810b00503800220411401c0c038561015846200d0481d5010b4201c030000501903035a450088000c000300d0001c200544501e1030700e21650600d0781e00a60090b075218070a42141140c0744100404d0310443d44004000171804c0340040442e0f4440d8001260182c460307030407503080071211078403102201c1c581e521030103c1061807004c4981e0348500503c00d000262403071600c0c000c906919800e813180c81107148a0302010559030702c81ba4083c0720040c072044000190050646d0100404c080034201c0203c02902d01c0040ca00564020f40300540c042c036402c1d50111100707480b00226038a5a21a03c0749038900c21016a03140c00c5054000500381202c0c496010b10485407400c45 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 204060584 1250 204059334 204059357
    0x70905090d09030507060503191b0e1c2d050c0108010e04031b02012f070f24020c03030a050c0d031a09040204110d090b09031306080c070209010303 65
    0x3585000201c1003a4018044180c90500c08500f020a40380180d17082c40c1801c0d503694a615052100c0c1c03403412200068800c1ca41501000b0507846500c414980032419656413449050420404c58900c02c01383c0c001c05404558080000041c07900f001c000154461801c5a54100340a50f8161140f0700f01d184003100c40750080d50030100c940d038101001501600d0012440c4185250581d00030f040091030b000300c0441818260616000c40e8421200c1418070290021000d030200c9400f803080900e074006019401c11400f542901041414840089404403811130346401d090080300000c856640f0070310640c13401140101299021a88c4081000707081c1d0155a036642031b585c2a045070318508000c0c1c0240d0b60800c1500301000c1c12807030340d0110580c520302c1b001180c10309581d131160310005004240c0c10b1000c40800b440414054202103455005802e818025200044540e4442c0c0c5183e481c0c0c0300b00d400e0090501c1c2e40762414030003140300300c20369544100d20510143c0b40581980000b80310707009c240d00403000180071001d80c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 204061834 1250 204060584 204060601
    0x31b130e160201020a0c03111903051201090b0d06020c0f160320010c03120f050a060905010b0a05070b09030c03030114040e0714010e0d020a1d0709050108010b1b070905 74
    0x106040c1c07a44000c6013444000d4030018209141070201a04000c142d2206102107070b02400400e1b62420200d40001c0102c4481c40c0240c02d5800c103e4201d441152264000248080b841c00760311043c0c43c004003100c4100c580351341c4150003500718050700085442008100f00010004000003100b41d440e644400341120310307501d0540c030101c001854201040c05030035030a82c07040e40c0080180701080d9150500c86d610800e07401d0540e0003880824241021281040180300300e10100b43c0c444030036a004980b0602c001da80340c8100c5000303407158007000b2002803420010344000c1080c584070b40d90042a08800d2fa494500614000e07403443d0030a800049802c2c504a403400b51310b151601c2910380813920a030140491a15000385070502c0f9080b0698070341446401030740b0004540d03845003060704040e402000c05420945906000e0421610356142e50780c075052070710100d03203483d004014600403580140d50344600d0380e0810410303094940004802c83d07100d00b0110a62000c000041c01a2806410102d07400612484c1540d403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 204063084 1250 204061834 204061861
    0x19080706023d050c19030b01021203100510170c0306010f0c03020d08060f0d06140f040c0303030b0402090405040b040b06060708040b070f1e02040b040c05031b130e 72
    0x907681229105419520350801015220942c0784001960004455581149024a0348914441038174510360b1001a044e400f034060f0301410083c0004e034222900e00c4000c0060746424071068881d054042412842081140743c40403140340180c0d10b9151890b104014441d4100e0f03041e1080d02c100428450100c2080415640003040074941e101b20300c1c0030200300c8bd10b910041e4807680c40145441c20008114000740240d200c03044095422900900168034800881c14400000c203084440500729100110114090b1506412114043c6030000c203425041031a546d4240d00801d240009a90080c0c1c080c0b100d9040740d551481024421400b82c401d821141c640340c40c2904800b4001800c062180a050020001050740340094505549000746042ea507004941840b070301d2840700c2c82c0018101c60009601c483c1010903504540320032403094405005e071200080420003922846080031000480c28000503a503440040341c100f10a000d6186914605a02c05e203041401c183d50b500105940c14901040c00205c010340e08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 204064334 1250 204063084 204063133
    0x3091203030921050909040c1502010603152003090a080715050c03070507020405130204060308131d070e0a0905010f030302060a05070225080d030b0102010b0a0308091908070602 78
    0x10343c1d003000c0e690f1101d014025000d5110714901484150b0001000c010524803400e002c2c4c400c034180940c1035200c51200034060a02c038041220f81810f0a0890450050b843c02540d9850f58156102a00c0104101c3c00e01d026400c0240829180c7c0314460601d804160345a008008541c007a260302030b445e0701022588404c0d00c0018050000c140001c10030012669813220940e41303403903811103010605498250803030003102c00c400c0c40a544103181040000420545400500304209000700c401390807030b0f40300001684400d40c0700110840c2c0e094100090300d550701c03034046070200740b100809030321802e520b40e400c1c182150400d80081141100480050043c103404009803540201000700501071031901520080d210b2000c01910000f8602c1100e503094440b9a80f042200500410310880e001951003410060240041949542c055480c0185240b031500306840d10105880c2c0055041d841c0001060900c45181941c0d114070002c00d01c0e91002144142c01408074034000c01a907030041100100403200d81200c00d1082 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 204065584 1250 204064334 204064373
    0x21030201062102010e01210c020319020c030f0703050307060506062106010201060b07171b01020d060e060909070e1008010906140c04060f0e0f0d03020d020708070605040b07030912030309 82
    0xe0001d0002c82010f280c01f61800407212008203601c1b803442c0099155014005a220910080b4900403851660000f2403e0450f03004800716040d04400d600c800c0d0b207404d0716020140171600200040c170301041d41b58010940240c00036103038515141c2d0740c3d20380c20345456400800401803112031090008560342400b480e03000e08050b4a6891030300000e540c1d0070b1407111664918042101e00820241e6150401e0303170205010415002c000d40d035400340c8400d43c000401240c081d000564502e076000c0fa8180c140300d06910b12071342001c0010b186107410803041000440c2c00800c41e81002100001c0462460030a0180c2440c1c07070302c901001300c2c0c244031030041d6030b05122008041c000a5401440708100066001c80c066407240d00301d08010107003081c10070104096508280b01550001200503010041560001d4001600c11403a82603d1002c0d441e02042c58681e003191081c200040d40600c001e01c01d08091100070003c852182c00c2c204641e03592040f0019142203054402d0700407a43d52031600052047c0710f5207149100001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 204066834 1250 204065584 204065597
    0x919150225240c08130504110906030f2205010b04050106030903120207110406060e0909010606090311040e010516020d1707120e0102220e0121030201062102010e01 72
    0x100b21548076240400c2800d42000303082d910303180ca0410301584042036402d820404d03460340c0c0c03503094a198042c5503032441040e0281e8a042040c0c0c2501c56160240d441300c074001080549507880c1c2c05d04203a0340900140c9412916903402140070010072146d8010b0b20313958890000819030180d181c00300070803030b24140d20040505003031031a41400070390f100640c620500e4030a000107071680070b5414940c0c0f011002e4072809400c24600f03440442d00c0f40e0090070754540554101c0d089849507485106542c280e0360f031445903101081d01c401052000035580d18106080b44409800002c00890364912542907a0090351000b0803072110612801e03000d9818800b0404218947c101a058140c03c1100d141c0800c8000b13140f01c04000c0200781c842da200b011904611000b20155000755192800100003c0c280e800c0600c502c00c440c4294440098400034644100b4121060f04031241118400444504640d100702682282103543e0740780e0101c0e90407214207107100440d14816200c0070740e650510014281950982d10079050150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 204068084 1250 204066834 204066839
    0x1a0702060703050a030905070b030a0b040911040c0302071208100e01030506060607060207020307031b0e0610030b030f0609070302040e0c030d1404050604121205030c0919150225 78
    0x1240800c40740100d40c03502c2c10b5680d48401250803801440040b0b0010218040e03c03200280c54075001000d9070048120000410440640604200031200907030f500802c4105001c0345000c0340e00d019405841c84030300c1810054506a007540e904051103002d580a400890010814082040001000302c3c7c081c0180080c070403055410754848603540e00000f40b080d445024001964800c1100320b405441d41103501408840c1480c0e12880d1003118005c0b08030028148400c1d4100000310135400040040c00b4000141450060b0303003102c401140075007012140b4a070107100e1901849640401082194420b91110b400340c03040070b04510400c800e0790ba058441c00301640c0302e003014001c00c3d0740100b02c410202d200b904081846090503a80d200c010f010301e03804560320150202c0d0000e484a50913007038485040c8250344008018040340fa0540b1107010a1380c80d14030707000c020301c585000340c201002003650008200b40c0d0300c4d030650750702c40c0001103042c006c2d642040180c002e060075940113405500d60740c08084803403c10341d0b5001d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 204069334 1250 204068084 204068089
    0x14060d0b1302010c060c080106030b03070608060d0f05060c0c0d08150906131406130e0304090203060d080a0201090c0f051503040c05090709181509050a0f0f061a0702 73
    0xc0e000c1c1c640c107201e034400302a650071a070040c40d0344541c45602c0141401484802940a80b04031001d00c03898001c6030070000c4142d0f6038980416414155822030304c336040d158030f4030340600c92816440c45080b200c00211582c03a802150040080500c102031100f03040d5541e8405071005400c155071030302c208007481015418060703840c103094a0b20000e44810b842c08040da42d90f11000460480080582c03000481c80d00112081e12400e499040341306500540f94941003117100d60349401180c00c1d900300210940c205000030b004810760340d002940c008200a05040d4008501e841d600b480d03511881003007026039900d03e140030070050180004001820080100c103001407030000482c0f8074411040389695100340000000d003c000e421001030010380381c060070070f407040e180649014040700d295015030300c030941c680030308440440001c0c01402781a0f88451010354495180a01c0c0001500000d80319a1b0031a46034102e55110880c1d5106c4c004401d41070110202e010303480e01003c0c0741c0b0801d2440703100c20001400c0041c100540c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 204070584 1250 204069334 204069353
    0x60504060e06100e12010903020f1b0d0312020301090212060f060301061115040f030207090516030c020c04050a02090a05010c0807030807110d0f0311070f060b0f1314060d 75
    0x6603a00718070340303115000855204c460b103005183d100480000d2408040320550089030075a1294003241c480d60300340507030329558500300e0048a80007100f6590109680c200081200c800714483c4c10200d41d90001c2c80c0c0c4100903a0006d0b0019101164007051082000c4180024190080d1083d600340a071452480c2c089401407005004010620001e500914500344080280d031100e0455a10f2280460038a441c0070b05485020000030383c0140b0440300c1c08031703290b902482503a0081118a204407041c0e0800101a4041c200140e07644003075000300000381200d034650340102c9106070030454006959014100030414140d80d1500502d0410024482a100003440346040354001901030070240c03071390380d120a001c4400100c048441c82c518001c040b03001c52544e820103d90030220b06252801d00140c66000d401c1c51413070013a180050f04c801c07411800c0c54085411035110b0401d094016011302c1c10b02d1a0302022695904503d2050000503503500307044a01c00940d01c0c18560852022229901105041c0e20b4450a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 204071834 1250 204070584 204070591
    0x7030e060a1404180509060f01031211031b0706030603020105040311060415111507081b04080703050c03060112170a031e0203060103110c030a050906040522060504060e 74
    0x6150025030005894000c0b1824400c1c6500d241c5842d9441c1e4a8070414404a034602543c0c1d400c0320304040c04194803540202d00140704807408001091660f00e1a104c060f01d103a21004030784144070341c2007184031601f0007c1c00107240c46040152070b640c0d1200c8120400c3e1a10041382d00682c00c0503c0c00f17105000613a8040d0886045a400c00d102814880214000810512582d03001c1c101c0b00c40c02240201d5429082411402c0d5800d500d02a40e040404440c90701c0d5607060110307503401c001440c40b40022001442c5070044201c2412100c0310b039040c181c603824814503202041c0c0040d01c60741c1c421421900d0307a10b81040360a01600c000d1440040038226691b40300c2e9070b000d10700c012400007040450b210f62024402da02204a034800c003040c0e100e02d8080c100d1080c000303500a43c2c040b800241040360307080c020451001100c80111138240190b1400403282c200700c40726048800b415510007000c000c00500d56669046030140e003c0c0d00c020340c032407208c16050b41000300e5034154003850041d1300b460b5040062020700301c1e59960 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 204073084 1250 204071834 204071839
    0x4060f0e03010b09070206100801092301090c141203120c0c100c080f06030c030c0f0424151b02010806010c0f060b011b020603011403030d0501080303060f0607030e 72
    0x1658442100081c2c0035046400509421504160400003100d81c00155180522010b003414124907440303d0b070700c41c00d82d40680f001405900303002848004a80c02985403011700d0030003900001d01034405507114458481540c0c0040c5004011400d006001c2c5400d0141506122481c0c0007140b07080c113000b01030000100014580d400e0604003051a1040000500c41c580c2086003140307040001100104002e0010b010680d0f448003078031040e000103400360070005080d102c1d00500400074100c0006482c00c10240c1d00701000071640054540c400c2c80324600340340886400500c4070041d518480ea0070440d8140c1d0380402408940300b04142d004c20260034411450812004c030790213180c00d2006540704401601c8503500d240e80184410140030030802400040c5e8030203170350404240da80c0d034414075841200000041c1200806548000100300421090302042101000b507140034041d28200043c0c10200002c480c0d00741c1c000600c5810000c100940c1d4030f003000d01c050f0311010071500141404400d8800415007280d0b084081e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 204074334 1250 204073084 204073097
    0x1101030f0203060907140403080c030717070f11060c010513020906030a1113020f190306050126041416061407121202040503030406050c16031205181309120504060f 72
    0x40c0c50701b16840445010b15004402940d540e420200074a6803a440396406a070040721b4100f10f050350782c1d4040304854125401c4610240034528586608191200d210b155552000b010003240c951080280600e0384590b049080040d1104400c3c0180310075103000400c01031290b0404440300e000101c05407e22003680406031600c2c050020b81e82d03d01d000912943c1e111010700000410304c50342640e00308220329020402564103128456031800151010800300860128600300c0740e8078049105010310100e584180503503104800c03001030314805d07070410140800465550524039828800306400502440381400482c8041b03140440d2500d443d055412100020700030420149110002e00c04290150340140c80011b066aa80329070760f80c4060007a50120218103040c2c09443c1c003c118050a411201c0c0c00c5940004605184410481040340c0c1648203181450f01140210107280032a01c07080c031005110580100c00040c2c6103600e0900201c1294003058120402c10108000e201c940c1d406546010402458207068 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 204075584 1250 204074334 204074357
    0x12091315030308100509040809100f0212070510091406090607050a0c03030e030d091a0903070b070909050c030106020f0d0f030c02030405122a030d0c06020c06041101030f0203060907 80
    0x228103102c80c07071748080c1e8041c45c1401072100740500d00f0b00414921108a0762104c91100002e000d90f0005680140d51001d030f000064001d1031212590010a82d40d440b403000c1d40e1164a1038081e030000c0b1005030350103072180704e070210010745a40d07001c02c14107070003400500003040c00b46040c980c0201184120502e542c10004c81801c0e00c01054040d42210040588600c1540d881b149400c24060003040404070a45005c00c174407080758084c881004503103010349681c0703015600c0d2089a40321201089801703014101004246100002d110034039100d030b58001d268091065589504d003100080c6816018509090590030200940c00e40c541c0040d000c0c0c1002d0a00e040118110101c035005900f14004d9034030284d04030b94481d458100501e4041510301007180584c00e546180d0703040c00c1001550010b41c0700d000390594000100390100302c2c06000c6501200381b24520251400d101c6041c45414071906442c121500049901000d08568050080903400d0f20852000c600354644440011100340020b4000320034000480c22a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 204076834 1250 204075584 204075601
    0xf08073503091002061e0112020d030210050403121b080114060702060c010207060606110304091e0e0601090c030207080d020903120408160b07080306120102040812091315030308 78
    0x303071880d405000f80b40750881200c010001e5140d202c02c840c2415030300c8540e217602d0141502d11500e00d05a4150010103104801240c0c04e00100c030341c1c0c00000f81c0544c4900c5590400e44145402624070403403082e0b48105110111102c414280c9010280700c01c19613000702034040c1c081c2d5101c3c60103411140c140e074601104a01100106800381f081c280d000c1d402007070000b0001c3c82010150010b2005a1160b00f00304941035441c281120380c1071962a9010098100300002c0100000306d8000008003d06080c03000300c00300c0002c054904444542d9041d103559000174004202c02451441a84104a81810306615040c030650703450f101c51044000309005241d01150040558404020410746000f900601550750398032007141c11b0b56031010301e078042180a2100d0300840e00c00210700030f55500c90790203075240c0d045450700d2017000482c00075603007110341c1503500b404009150347c1c0400c4031041b2b286516400560320052102480800902c0c0c00f1068101400d140c1a800d100c6180040081126058546039070301d92100e80301d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 204078084 1250 204076834 204076837
    0xd0e031605012f01020d06051908030316180801050f09010b0109061103090607080705010e011a122d0709060b0a05030a0b0a0e060916080c070203010906060f08073503 73
    0x241d42010b0740c40460103c0032a6007e51084065031800c9a03905100c0a4010702c4001c0f003032460140710b03026001400482c01042c815400514582882c0c1490320328902054042e0401d20300540c48200941e4540701400402c80c0008040e80e00b140c0c8c03101c0203010901d0040c0000c0d09004061185108100002244040300b20090081c0c4450020080641c0e645a80505040c03170030b9005180103132201c0d4030704180c90080c0d03a07051254110b102015004e620071018024100f111019000c00e070614640100c59415080b99038082d005040742c8006046080c002c01c881308035034940020780d04046c1500b450b040d424400324001c078040d5001503036503141881c3d407a5140c1c2d200784c0103000f11034001030b00704210340303004141600c0195000c0c1c4900d609a540303642695601d00c0303551078810b8443d4484045409880403501000d035041c0240ba0150014002080300412555010119007241c0d201d950140d85009041c080200144103030f5000701103644800107003450f0012002003000c496803000101821402c00284070400900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 204079334 1250 204078084 204078167
    0x11030c330705010b09010909020d0f020402120405011a0609060d050c0d021207120b0d020609010e030a060506090603070303080a0c030b030d080a0e0106140607140d0e03160501 77
    0x11a03198803011145400c030f001c0c0ca4216150361103035202500110308100544180280c84d5001010b260080740d40342c454000c0c0c0c4003464002ea802c690200056900780c1c170000f4a0902452194000062aa18110020054041c0e850345030b0700c01c00c0200b15400440d42e039181942c0c017034a044031000545440f82404641c0911505425210307103400407429116824150705070612030421a00c5480b064412500c1e04022a000150101d61240214a40c1c5002d030500d407018051004041c10180c0e4218001f00000e440c181002000b00c030826120b40c01c109140c14540e407c0c81e0000300680080a1580c11542c3c0034103045c4000b4200406603555000d07a0f01c085221f604403030310f4070301f01409541a0303243d1103c00030110b100c00c49458074402c1c00c0c040c10341071201c01440740030704a503403c0000a030518061000c008403070f0300143e02030710600c00664010920742e200717004c000104182c5440d0000c4110600c070905d400c12170541c014400347d07010703590204a580d800c084540604440c2c426030b900502f022003114000c014050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 204080584 1250 204079334 204079429
    0xc0705060402041817130b0408030a0c05030d1509060509071209240c02011a0a0506070c09110a0f0503010f030b0916150e0a05030a03120209100c11030c 67
    0x2a240c60510060300282807080b02a00540386c61030302c0e45044140c0d072081e449501c045600412100941c00e04c903c12820900b445181a0303481e00840c80410003d68030044452900030b142c4030300400841500e8032a050080000b51551040e0707203880341002e800c81140d0810414403a4568040404100300c00d001036040c40c4580c12500e82403903d40b4031400007041c032031080001643c07908044200681c100d02c1c458030721110003800d4018103400c103810303c0242c1d04003800407682d11006e2080400c83d003686c2e0041078001c030106422562035100f440710080203032290800c0b1310184401000103121082034202a01d041c0c0b90042050b64240e1074140485103811388144200f0304201030400003081c80c0358009d04840d0440006e588140070f81000e04100300614215108966042e070102d07200310300080c0101c00001c0d464440200050500c07401101140c10200303d04004400605c41e0b8141c40104003800b88100c5801c00c05500801a008001002c14600516070030422a10400c0c51948101c50310b10b40d03d1001d200824 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 204081834 1250 204080584 204080603
    0x1409011a090d080711030a1203200706050f0705030415021b0d0801082a01033305090901051509090102070212030c010c0206070203190306030506041104050c07050604020418 76
    0x71802d100381d45412542c000c58030301103090517009007443d0001e0403402d6140c100d4071140103062110701c01c2d4020102031101c01c581085041400d5401701410010b0b111241c002e110204113441c00c01e8640c0e40b40c11009104000380310007482440081010b02d40c0c00107500740080b000507030320303803c00d4820170002003220094642441841c000d03810460744102c6090413241d40d20111a1080481c208110342010189490701d0b03003200d075082c140420340c400d41103a034181349002c0b0051000d02000400720450307003640780f02c50382c9041c98410811150a0400300c41d0382c020300a800820150408440e110f0003c000b408070a8842c0c0310040104140390005e41c126405240d004160902200310942070580f03d41040c416081d5030352034443e44000d50b41c00422000e21501865000c0c619046143c00301341d080386c03480c00a0b0420150f0700c03070010002850800c0460301031401040c030b0080300b8069a08000960782d00401e40c10844106020701c030002500001c1c0760b03801c16070403100450300c0d58041c5010a03070280c894a000d0318000a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 204083084 1250 204081834 204081859
    0x6032304060b0f030102270117090309131b030c050417060a05060d0b0705030a0f0c0201020c0106060e0a170f03160c050a050105040e04110402180103061409011a09 72
    0xa0340c0e00041c4802e030240c1d450040e602403903003050b00300d000c0d140e840e540b60311085003014003200e1415400d0780c03c01c10505020000c0520041a54040b10007103542407038a520000b0420854075007450300c405072101e101301c1400103480c081d640c0d1921001c05a64a0245526048480d03d41c03030007401036902a1000d010345511045000e110b259071444251140c513402464400401c1d06800c3c40c8001010342c6070031401180c2c0a854050b0210780c107510050180a1a075074943c0c0b074080b0165903024001101c0c80d00c2c0d00240e25103248290329401c4840c56400700c4148002450140030940701e040b000e070100c030000c0510001a582c00f100a6041c02455080c41c0517901001072041d10819035800c010200c2030003121039450b115128028000c0011060150702d012900510042088010354034032694090b20075032206d800700c000340c8045400d0f038010410210752583d10448010700e9503410301c00c0d4401805a880f108025080c03610114150b1401800f500014020303148429207150100800c07600c9601c00600311044c01c44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 204084334 1250 204083084 204083093
    0x3020d1113090b090609220501020d1e05160c06110a08010314060103021305060103020c01110901140301050d02040b0d150603230d0302031003021201020a080c03040c06032304 77
    0x5042c001c840d01d691a0031800040ca052041c0c4076481114054401401900d86280c00e000d07800c60002140b50312901241560300146c4280080c0a08440004001c111810f00400342c3d000c550013140080710785032034603041100d0800fa401001004020908007510800098180304029044032901c4645615002481401d425071107403110b41200d0051034030810341c44078803010030341340c84013848081c0d030041c4000700f908022040c50b404260804014140189450043c110b0a402d58140141603404040045004012035070007000c44e030041c0d1640a203c0f0302d15810107002402c001c05c1c000000e070065658604415041e2a88210000a190054105021400c65040d01c2c00070340400e010454548440c0400c40c103040c0f41c0204214000700300500a04004200c1190850003500005d00b28281001c26906c0000941c030ac9131501c01014551070f0000d41e482032285000f5102d0a006801c2d0a8884400c00420001c00d5039940c281050b03600c0c600d00400e9080560701c0001004460b04040300156808005000030403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 204085584 1250 204084334 204084367
    0x709170616050c060604050c070203061003031d180703200a140a1b02190902120f0603030403060c02030d0f0c0e010201060f120212120a0e0f0d0303020d11 68
    0x401d104190641c01014801003140d4a006000320f40d401584078002140d064505074000c1039101052040003030030504182c001034039110054440e003550280a120900a2546c42030785181000760707242100700c004403060085a040b403d542421f2106100b9107020a0301c09109030406040c091540403003241140d0491100005940015078100101c0c0034440e0704100401038005440400700c03035440d0490f240300900040d50801040450880e4003040030311407480e08800340e155107805450b0315840141c58000c040c2540e0201440a0715510b0100d8141007000400d82e03000045030280c0303901107004108155240303030a9146010b00880c0c0703d07015040141c3c52198444640c4244900300c3c01e541c40050702141c00e4016405c8a41a0040318000b0b1000c10042c00b00080b0040c1e00c0b0400c074400f428808520204820550a020201c01380c207ca40c0d07000211060b4840e404107000010700341c00c541d20502d036403000d40060082030050b000201032540106202d55180c0c0b5aa00c032040110301e50444036650403944000c544407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 204086834 1250 204085584 204085591
    0x90f010e0a0606050405040b0d140109030e04060806071b0506040803070f030519090c0305030d0e0d08060d020f0d0215040f060504080a03110a0c150806010e03100507091706 76
    0xe0340200000030503001190040702c088441a489403441c09061509100c0584441a03141d03801900300e00182c0001000700d150084152369600c00090160464900140100000100548a9030514005000c103c10104445401800c10305120782e0140032010010144a081000036240d801080104010300c18000002c6100c0c45d2203030b5070000600140c00d001cde022200c040d2203010101d40c0400004c00d25071483d034009010ba90250070f4000e04c0d696a5501c05155a100791111403c8945401e100c1c00d901d00204800075070701b412800e040105217445004583c0303003181494060700c1103003079201095880d1901e62403804c41d10b4001d03040d400a40507451108030130341c0c000d2140542d40d42c441003002444174810000c0d50243d0701030310301134481c3e10b0140e182190581007d0400c440c0314003419200e4000511060407100040c80281c018140c0f080b00c007407000e040703204000d0081d41031114050000e07000ba580070a00448018a0040014031901c4038502201c49071019041000080c1d60701c003102601c0440010500d10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 204088084 1250 204086834 204086849
    0x100209040507110a03080601030e2a10020604020d14030a0305100801060518250306060e0108070c14030f0a03020c06090a2001020c06120f07030e1b0609090f01 70
    0x3040d02c2d0200111010302591416500c1500304626240010b445140040c2d0002014500800c00c200c070100010706182c0719201541b00c1c04519406001e0030302e603041e2600040e150884030040c15240f5814043d46648009100030b1113010460380520400c41e25030041440c42203c4400c49441d00d0000d007000d0000d01041e12841d2003104050000600e904050288005407180648510440724001a4200c0502d034050444100500516502c4028a40340c4409a8041200785e6000c2496480c2240160540e0429243c2904003c1260100842c880d00409a05e150b6507022051030840c042e40641e0703038254014002285012840024031302c4109034117401401c594091101502d42e15241d401d802551604803d4005103051142d960301c008508600030603013041101170041c0e98082000c500050481d42c0310820024130b19415105001c0f0010f410265594815641e04013040b4203c520040d4903900c40b2030a41001002c903c0411840c1c681d01d81c001035071288003000e050300009051a0544202e2000c00b40603040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 204089334 1250 204088084 204088091
    0x50f030c0d1415092a0304060209120d120203100501181a0c12071a0702072121090506070201030617030a02060f060904060908072001090b040803090d0c030510020904 73
    0x1014119203850480c0b05170016544007030790344101c800b041619040208203a8043d64203002e4884540c48092039415078400c913601a0401851103030014100910803075410104c00e04c14020490f040c3d40000070f11099841c01d0a02c0d00e280140c84043c043d6010681d0480c0c440083c0d1100c8000415440c08013902c0410030000a440001c5e101060013440c900950001030f000459401d20041d00110442c9080c1d00a111481642c030308586036001c000b00d07000200c1d8035110018070380c1620018004551180d91401d07055559055103900354080091130058540030304c502c1441c00040136021a030103544514010004402074241c60170784400007036100c0c1c00c03002450b00940200c00000e0380001d44060305d1032094000411007042c84d100c940700c00e0010101c107141107652003000c0101c003012410042d140510403150b00a03c02c203540310300000400d081038a0380002c00416051009100032900072064445440055a01000c600c10a09207008004170690025103d0700910154010008031a0010003040c47e06031400d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 204090584 1250 204089334 204089341
    0xf06090b0d080301050603090a05010c020a140a0b0a330f08162105010e1e0c0607110102011104230a03020d0201031a100801080d050f030c0d141509 65
    0x481c40308401d030014800c40081006003e1842e10302d003c0c58214405100301c414a042982d125421214100e01c40b01c096401891140104082c80034040140781c040e202611032035044d640c0e80034049002800030007660f500c841c202503542841742560034100c1442c0207000000c03070b40138816040b4000d03103000380f4240c1d1020104c0460583c8000520250641122050080343c03071030020b84140c10120700b00c469031540c140d00000707804240d02340a88a032614428004d8640d070340041c00613412401c1420038848003500320402d001601d60301c00f01554401500714400b10154103040e0300403070040c019020992400300c00800e021600405266007441404400e484141d02c0111807000c0120041143c0b00080d03200e524000402c00551007500300441c004c043c0c103030320701945000074001581c032038040f52500002210710004108986080040d000c07502c0d4907003002442c1001c07008441110340720041201c41d9002000841d400380d86055401450f141e130361042002e460341022084c1540322103400110910915a07400032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 204091834 1250 204090584 204090589
    0x80705011109060304060b031c110c010219060f14070801080f06100621060b070b06040902010906110c03030414011d0913031205010b030105120102070308010b09060705010f06090b 79
    0x45440c4003000422503404e641c2d83e41e8a203c00707804808086901402141014045c4055a1090000054542e1070341003101c0140e89065242c00061514141117610800400000000c1e540d001c1c000ba540011011a10104801c4441701034144030214044100d10b4504008405520202c8030f0b041c0c4d5140c02c152004002110394203a5654030650384414401d0001d0402c121150050980f6940144008011056900c07601c50070703022155198440f500151002440c0010006180003042d44400211303401c01003050503800080010505000780c2051101035000c80103014410004980318103401400c6983d030315143c0080c54100c02c080c1e01c010740443e06035071400501c0c00801d441403030821009000c0d000e055407008000200c00b46070040c150140090340000c403072600c40c1e41c000c41e03020f403450303070421540e951610092000302c08a202e03801d14a64414891000003a40c0550b84504403101e0300400c5880d0200713100001c40c44d1040060040072503107000510400451140c00c02811240d0071a800c00c07101440e28103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 204093084 1250 204091834 204091837
    0x11b080405010503090114010305210f090411070b10050f0105031614040503190c0506030f040f11030f0105010515040e06040e0f0f030301091104060509040b1c0807050111 75
    0x100821100040c0000d00c1030303501c03078000b0f15405000c02c0004101c05410b0440034001690230703002550140c02118203035160301c080c4034214481c03440d4491810f2402010750055501405500d04c958807d036100d22011810441e00f0041c1c5503800d802103140310311401c114100c6c40c894542413080c3c5020b0b05410710b89a040d907004105030fa00c6425044130040710302d000782e20102c0c0c035a5094010701c51140b00c180408909514100403590504504200c61111003006003022101b2400d13583c8042d10400d410030402540060510180f6001a0302c21040240103003140380044150403130300016034161240342c020302c80c1c400c01504043d040b24815100140e500c40b07143d104400c0c600c00e50181110803000b04010880c9400c1c0350707012020080608098901080603070750140e04000d40700410660591012005000091b410f01c03500f00d043c5c0707550740388915040c038020b00500135020348007209200c3c5039aa07072141507a4070b4000c0070301e0b411002054004000441c41c41c029080780c110000640700c0390b10300071000c1c000b00503c80 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 204094334 1250 204093084 204093137
    0x2406070206070b0603011d150a0204030f03210e010b010f020606031509121c060602030414090717070906080f01050f091306021303021306050616020609060a0203030601 74
    0x41041d403801d100c64803410352050014141c103405640c2d07500e000039901c00c010222030f55500204060100410541100c0505a40145c454007050b07104200410003e440210200d100715814108800c880310401c008c0b80e0b4520b1054441080c00e800c1c840302d507140b01019404048480380c241c03100c410721004120308030f0b40c0f10401c80f2056055480301c8109606150608401c03944840680c04a900e00c800c40c51102e503040c1c0200e8681c0c440c0030341c18840342c01c102c1082d0144001a001900c01541041e2a149105c60102c005070401d60051051602007074209200c0c6071800800d4200703028004060911050040451019101b150001002480421031108170701c0d502604a5500611154044280404004a058010303242d5510740905105400001d0050b0020300350354118015602c500f14a0344c0140301040788400340e641c207040c1c6041400d002980e1030506a03110b60395503407408a491129440400d205126150015502144c00300d01d109140364000015031181c0d9080e601d240c94081001100890820b80a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 204095584 1250 204094334 204094339
    0xc0a150c0c23010c0f08090607120f1806090b0f060d1403090a1403100e060103080c0f0f070512161802210703060b071e020117190507090e0c0f0c0624060702 69
    0x42810f6003c0503e82c4c00101903227040c2c490000398060540330074208028203400c2124115141e40012042c0665110f0103540602c0008076103101c0d140c00c100103400024a050010500001100041c206074401c00c01d850304208090018480980c035840110203490401956510034443c4141544069056025000900040000501c016400c0d6030fa60307015904500c0d581520340c444c0c0107220340c094404022000450b044040501115400c1a040c01301140064200d800d29600000e00c2105424070b50081e003007216115100c14600c09004844000031780b01e05210306407001003100c404402020269802d8bc0145415101041b0a6603a1a1000803a004051000e00340c915140c010400392048008119a00b501c145071202030700710520940c901d80081900e080303024840c8010941c40d50700940c801d494102005041a6150364076020340d5146241c0002c2c999001c0350b0b000304e46d00c1e61000c9080f0650b03501c400d00d002650402d28255200d000c58440c41d603449003114216803001c88260804104441d0b20a801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 204096834 1250 204095584 204095597
    0xb030a080c030f0403060501060f080606070b281d070303020a080306010302040302130209030c01110d0c14060c07060f0603080304081605030c0a150c0c23010c0f08090607 75
    0x580e00c0d000840e40003004284203034001041807100b120428001400518800d64000802d0b50501c40002d100d000c141c4049024090310b00b050010980e50002920702840d4049400070b5107549150205a0078a00502585054202070040d40c02ca400103802001d03103001c0d02c5807100045011013090070380d202003e1101501503004aa05030010070314060045a011406042c00351410303680364080740c0241101658030164070307404540c007203085c6000c0c0302503802c0c800c1c01d180c03540103085030342040c0e61100d110721846800d01c1009690b440420162248081d0341900420a450a42c540b0b108000a590b00c2400c08590302440c01844406071421072080c0c909413a0000c040360300310b50301c43e03450b4622580010b0805681c0c00c0208103120010340104001c006181c0030f00d001d4064204075160810308041c80105124455003000b400410b5981d0141d18090300d01e0300f140c4048a02d0f0000c205107480b00b20200f0910410794207046001c1c3d040c41e0060440300c15140f296481d60030f10740e1540e0155440c2c1006648902c00143c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 204098084 1250 204096834 204096853
    0x240e060a0f06050c0a050d050c060a111801210507080106020105010e1b0702100518040203130609150615120b13020906160f0209100608060d030e06070b16030b03 71
    0x11800242400c0c80b406400c40e03803910156180c007480c1c40040d087c10000110006540003140030180030072500031354000001e020850a0b0000301c8000d001b175282d0854004200d0408284c84c0e8441c50002903624624030300d400c1904d141554000182070200c0341400414481c030000248144141301d04c2d412201c002800a00310740710b451900004000201c0038003c28141444003038056560340c2b4400040001540320255a001440349100c400104003400384d01c82d0307206104100c03600c41c4041d2000c41840c1e1100000071420703658580b03a0780c505003000301d5170481c0d46010300203e23040903003017455079440c07806840d0311004048441040d02902c0150950755002858816180110310841c0c0242c0300302c0000401e19402c05040c1c0f00180482c1c40103c20944000c4810310110741503040c4260f00640212105105910040c1888005461110003410142c02104aa00b0507000d151041425640080d402031140e5035802090400442444050341c907002c04440302050030540900030f1141d0700c01d0280103000307004440c6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 204099334 1250 204098084 204098087
    0x50304061803080c0f10090b04110a0e0f0105010806040b0d030e150a020309100f050a1209080d05330d050f01050705120c07020d1104240e060a0f06 65
    0x280003011081c0214981d1030100028241d84041d1a9402c95000248500754201c00400d1600041124800f0345500c1c01440e14049080c0c0000d840d405030b0131604030401300d0ba0700004079450203c035500031041a42c4100510035400d1100344468101c071000d996615203901c07003a0410013100e418400b9107038003028609e1702c00300190007000c5060466200074070740790300a40103510b100c00e1365200112160061b000010890054a040542507003040468030b05855540d240c0c4001030304900c209403140c4140004921240c45101d0b068210610740d81d407201c0c0e060f4840e00704031104006808180d03298071003022008042ca80e035421401690403140008440700c0c2d8464094014400700b40c180040603140350090310000c101c81c0400f40525070103980c255682c1e40d550403200080d0141214090648074032840c00f000707000d015981e140382c0541c0300c681101c442602020399200050007403200c0107102c940c1c8004501c1414044000da01104112005400843d11959981c005c10060b80352900a610700102644010300c00f1b00e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 204100584 1250 204099334 204099347
    0x1a060a0608091002031317040602070605030c0c010c031e15140a05090705070312060602071413050411040b03030906030a1503080c100c020613120c0c0e0f1305030406 73
    0x2500762003600c2001c8903c6100c00160b80c81140c8550710712138601e01d280200200c00c603075000c000b94000c525606207410f0a85c02902c0d4085841741c0750030040c5c0840481c548160400c11540316041c201e0003086a0350381000c01501401d03404d00c0701c9940d211101e42c62000c2020a0180d44031032848040780e96695414074500b11001152803418079007001d04020045901d0700c52041c503900402c0c0f9600c806803603490525005001c3d40c030049803601c503142007680030850583c00080c1c600a4405041180344c3e885c00030008641c01031b90200d20b0024040c02c00060000b44a80300c0080b1800110940d070034440d01c0b4501c4245079071b901c10503200f41d40240c820000114800505c0d880400d2002c814810b0720316243e07481d116615079801c04224120070350891410040c1da60658800c4403281c00042c0040c08080c5800c070380514202d810b40758041c20180340c2100014102e0304c40ca414100c400e07030110f202403019855038000003202a04a85542680da02e01002c5000e6070248103594030a00c0d48100250710703160a000f82150036 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 204101834 1250 204100584 204100591
    0x50a020907110f0105011403070e0402060a030e030d0b24030a02030c090a150905090106120e100c02010603060c03020301030b04170f03040f0b10060c0327030b01031a060a0608 77
    0x40001000c01080c2d900400d000030205500e1040c0040703619418000740706005100d603124070748241c0c0725090811502118403c0b440e80f040d01102c10a8a80034210000d0740503105181c20141d01e8000000c09442c1c01c1400d030700000d4940e90075141e002caa0310071400c00002440e520100d41c250800c007407000981d00450341e002554042d0b01035a000f0f051003444400300380c90000c035422400b42400c2c03482c00d044640c1d078001c140400900341103520000c95490642c002c1d20301807407140d0131181c1e10386400306450742140420003407400705e003840401c1000940520b0024028491408100c0d6403a05103002000000c0c401d0080d41e041c1c4c0e40205c030952194940e41d41e012844980b0030710b41c01c4003110030b01100034520010000343d40b0450080d00d4800615416282142c1d110900802d0507440d20f10301d90741030003086d038007020800312a54907040183c1e840345403410182c804100e000304a902e07141c138000080100104004140c0c100d900c00c604049076901c1d00c0b500126013210850f000307600305500c5d003400c2045c18480c43c4a15003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 204103084 1250 204101834 204101837
    0x9040b0402040e0c1e0f0301090c0c020a080a0c08010b0f010f021f05010905100311010513030b090f060106020316060c210b031002030c030703091a07030621050a020907 74
    0x2c2c240c3e0710780b448190707003200311807441c104000800d0141212541980b42400414150300141c07078661480504140c901041c020041134039551102581b44900400003c00607a40081c2130090703543d61440040c0c0d5502d400d0208a440c40070038000022800c205008100f0038440041402d4603030420900119080300c52031314886c007140300d0801760382c0401140421060200c1801c1e076020032103606015415064400c064070451011150240800205450750002e16186000f40f0b025035581018004040e0703020819000a000401140244108042c00248a00000f02da410035240c9a0781d8444040c4d03100c0c000c0c8808042d500307205220240c0001da440c0c0c0a44128419428001c8003508811141100c40c0b1051907000005540d52008244c50300d001c004440a50f6002007040d4914a840d00201c0303050301000d0a0345051544a0742c407501004101040d140e01c145880c402d40a041c0340071440200034100b03038400c440c940145244040d2400704940080f40c0e003690010000e02e86000c1756400d218401800400707420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 204104334 1250 204103084 204103087
    0xf05090c07080a020c0109060f020a020f03010b040e0604050c09070206010306020f0c0a1b0807031109040f0f050d030605090105010c111f0306050f010e1305070c0605041202060f01060509040b0402 86
    0x800142d0386001a02c040781d401d5004041c00101d030700c005041a0141d401c40824030480710510302c1d4595000032400d030f1055060310001c641101403804030380034201007044181c0c094103210079100829000100f662045000304125900096802c4c01e201401c01e00380d0b984401600400c006101046441e0000c0a0b500003408040349840102c0031542c1c1040c81c1c03a00100c0e8029141c00c01074000d805104c50000c06402420007074450180380d660350011150240c0c02050158101600080074000036122424000703400c280d81d4521120b0f83d203807150301c403c159010000841d140141c0070600c1e040c03001760117045e04d60603107611408210a4948040c03454581441c0e9034040704500114a80506a4074905414501d548002c81ca0909000401c60380580d04141c07039040000c2c20790803912941e03610200b130b0820301c0c07000347c00034040d10f6698041b42e01a8001601401850501e0280300802915403c2c900040c4025400c1da04507803120300308036038a01028811080019003e2241d0074040c82c1030350110f28456001803005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 204105584 1250 204104334 204104347
    0xf0309080405300304050307180b090708040b15090f1b0a090f050415050d0510060e090c030f030901030b0307090c09050907020307020109030609110d0c06030c090f05090c 75
    0x2d504103100d80101c03040010841c140e83c100c4581401252074680c1884082c42c01e0900f0320707011a50b103402a10030408546c1e4280c51454589035558003040c11103030003078610707005440c0400f03001e001648107030340440300008403100007822200200c0f1007003a1071000510154007602e40d9200c4110b40140039003605080314009001d440342c01c6444000307019810707850f200d00606c6442c01c00320048421701540201c0c010380c00c120b09074884000001076034041d14012168500010010300b4114540818201008044e91070308101089044100c078003103100700d003e0300c12100c42d00218814507071224207c000c200c446501c01e00c031202d060740c0680c01550f91001d01900b10340c421551074035000e080e070314001913020104444c000e060040d8244a03c0c0d0725448a83c40c0000c600d02031007070380001c012882c0790ac00030304226640c0000e80100944003c1d1000051b90090a40c1014003190500740d451800c18442e03500880d00d130048400744c040c0148103103812a96810702078a0780030716010600080050042010302c480e0001c00c070a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 204106834 1250 204105584 204105589
    0x9090a021b0c01090f051f0207080f2a011e02030706053405071e080d06140f06070816020a150206010f0b03130302120c0c04060b0a0f0309080405 64
    0x41c580402207600180100300700a0009440010b40c0e400103281d16490310030503c001d0300e5039032042d41c0a03003040d210486610180c040403400c04032903400a1405019620907080c031400d000894861070800452050203000000c040140180c90045070103001c161400a07803040180106010000e000307050069070f103044d28640c0e9844c03c5420860303600c4502d00541d40303409099541541d4440e1b4001c10881031b1000d0b004400c50141c4240520302c801001c51b04465a1801c2808030500e040350015403060300300d03488038801c42c1c011026107480e00401040104c010042d1105142c00c0ca68035030b20a00251440f8503118464661144950115800c60205607080d2241c80061322109500300081c403903003040c04c482d0340c21100001c0c1011070690200040400000b8280310007410201141e801001c1c00030a5501d981d5185026403c180c0c071400501d0040c40042207144203074001084811030803104460400000d901c1e00e00003a0f150140002440000c0c2290020300c0314140070b030b4040700d400c1e0b01401c0100d08250703a6800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 204108084 1250 204106834 204106867
    0x30d110d2d120b1002100510030c060206071205010f0b301506071208132009090109080301030b0709030807060f1b0e0d14030d0501051c0809090a02 65
    0x1c48800281c203415101d0181809105415401d442207604040814103410001d41da0030204441d202d2180c0e03940c0201c1c084154500c000c00003164052503410704541d0350080030351908000c803503034404259840c20003039200c107142c41114107070f40f941141d901087d0308020b00c2006a030000591828151809d54110041804c1c1403807241c070900800804d40d9052a180320040e0404411210312402509c080c82031800007220300c2d4010020880905d071411090391000c02d40800b610341002c000d000c0c0550b81c1000044103031508011000c404c0256214039081d110080b0590886160910141101509000520005498040f0f154102d03825280088050b5100d454074402980401000c442c11640c6d4407100c2e044c0e01080c000e4408075407120702145010801c000000c5c0582a041c0c00152141035540c0e51401000a00c02a040c0314043c14401c032616030741040040700082c542030007124400c60561046035080761a05442c60340643d030002d080f5040c000160704ac81000c80004d0704138a00c4039000e000d4010322120041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 204109334 1250 204108084 204108167
    0x1050f0c0c15013003080a0f140a0218010206130305090102120c0604021806100e0112050f0402010e060a0516060207080703020a06060b0721020f060106020705030d110d 74
    0x2429199100b4010a40180d05100c425010151038104104071380403d0b0040c5815078801648a00411a20700a41c0700754002c0c40413041940c101e00c1d80b40248501c0110b242d0240400184a8003407903d2406480016656104102c628203103404000341d02000080c89140640102c49041c0120b80200c0e86000c205600e94202000030905540800100407e6240103283c8200144880b4024000c50401a000c42d4029494250b68030500203024080c1046074401d1419800c0c012083c041040b0504100135001c00139079003981d0a0380040c44c1d40b0303000c0146142c094100c1e80700348000d0b01d038186450b02c1080c541d0322618a01e181a90b8681e03013400031601150b5500e005040c003500c207902406a0407814900102210210b400c0302c40000c00900c00440080c5082802c5011148141700e8140e1186514104a00d490300034000d50001e401440000a280e503000580001914821002d640e095200b1a000301c0e45240104113500030740c2c5c003a400601240f4050400316082d1840001c143c0c004016243d0244c02c42ca0303e84 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 204110584 1250 204109334 204109349
    0xc0a020d02040b1807031802030d030e07091109040b06120714131509090b030309010e0d12051c181509060507050901090e0f06010810080601090c0e0301050f0c0c1501 73
    0xb10400004a6151207101d4491011b21f60b1200b100300c1d00e40100c0d50758061540b078003003403503510100444205070400c5004000c102e03000052050302e180004a40d107a410000314a8048d81c20551503a46602e0b01c00c2c1950042c0c0c0100025084075a5030141c01c0382c000121403940c02040c074041013040c002050009100014101c00400d40503403140c5c0f000300600c0b01c900c65020070031003450904030600d1590003104540141300c0919102650344100c00001d90140501c00c4001c6c140b1441200a00c0900d03008009030401c011000041084404100c8074201980c20700e00403044145900710170072001031014040203900e030803070681c0016a048140d41c0e06086810581e1940f010510114040e011582e12051a001500d200040f80031242000b02c84171462060240200b810b201e1200d00107000311410340307403040c0141460001c584055030745018500041c0040030101d00054105c2c044005d0a060501505005d00c2c40d0740200d00143d6286031704051903400583c2d55901d2030094508041c00640303600640e901a0002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 204111834 1250 204110584 204110629
    0x1505040804030201021c02030318070506041d10050a060302030a02070b0f01080c12030a0807020a0807030302040905060d0308010303030e01240830070201090302040203070c060c050c0a020d02040b 86
    0x21800064508580c4040d0146c80321116440c0300d59866011050360742007100604810480038110440d142007411a41100341c010401007800103242f040e0002060701d20007a0581c82e44142c560032010420381b4114082d00350040b00000013003218602c01e90066a00c130581840050402c0341d00e130b80320114180d050701d0304000180501d00600131a4028032900c2c0c02120226031070b4100c8600c420702c0c55240d01500c0d4401091001c001c00007102d00c2d0091214071340056119a00a544a11074a0050020f40060090741c40e45841d0a0000361181014181d0102c0c3c640c0607190505c1c0e03a0f10b55581140075102e1206084420354075070000070f2018000c0b50000280071100c2d0329000d1a107040174211890502000c0d01d02007034401a0a100c45279031880030020039454405a1500c1d80d4880e5800140d800b44103d40c0000d4000b840001007010300c560112050920600c140c0c2c09001040704600111214010000204410b4005000100040c41c0c43d090409203a84085e001142c0400c1d034100003400c00c0ad01c0080c0d00c90241a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 204113084 1250 204111834 204111839
    0x3070507140c0f040c170408070b1015030207081c06120f05010b030109030c260f13080f0c011215120c0515030412090b0a030204030b10120f1505040804 67
    0x10107180c0c2c50383c094020b650400451441d903400400c0108105c44000c10140600c0c0400c06000c03980d0101c90007543c000d16a10b01d1420300b641c9443c004a0103102d5600c8941c0386600c1c0200c6540700703000300c803400da4202410506021308000c09015428002c0c80c00380b4819510f500000d103030420009a5600b182c081c048035494900b0ba402d02d5403d42d94231040d1140303c0e91400700c1410000e42c02411880c40150098145010301c54441d15040c0642c078200b901c1c0c80c8925021460049103091000205080ca01d9200307400c0c2510303034401d03030303169500e0507200d00a0729a04200782d240c016512030900a65440e980e004c0c041121a2021890594480c03030303820240703d8800340c00c0c1c2c21007881101c184ca0001048244d13410ba4418150380701c50022800003800c000c0207074003a08c55007408a44a0030004001c4d1003100031240d40c1d5503144001800960103840100d5150780444001350b541c0700d041504604590320039100b20001580b641c1e50a03504903a650701112642001c5c610a4013105a91254505c070740d1065026a68450 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 204114334 1250 204113084 204113089
    0xf1602130e07050603100315110d060311010c0809040f0207020d0c030c23010c030c051203010f093b2406042c0f030c0105011e140603070507140c 64
    0x102034100c1409100108180030511500a40c11002c40f5000b43d1182c1d4150b82e02202c3d20043d00703100c40080c809e048041681410b10a059000c501100c1c4160010030b001342c980760040d1241c00700503070003034142c6a080c0607040c05410725801c40846a000342000514144450340021256841954151313426030a240c414010000355110f641c01424144250000c5605003a06810140c1c075008600c2e410081883d860504041c016802050305c03e0b1700c541070b0350030f49905141c002801d40007441002c442d40b240400005440c503183c45906408045280a8000c00488020b00450490892480c51080340d070301840d0a0300d8401032100d441c1c00d80103040c840000203011841280c00b564064102445645014038004c0250b41c1180038900868081403600083c0452415990410300001451070540c00300140a8041050661181d8180c1700c890034400540104014a000c0c80740d0180501900254008040c001a01e810800355510040b140340591400c1c801d82c0d80d8181481d520205682c003a40410007000c01031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 204115584 1250 204114334 204114343
    0xb03010806091501060309020105120f06041a01090e100b030903030603070902040b030402040f020f0703030506100309020d240603081e0a050d05061201110d0612080f1602130e 77
    0x35482000608020110f1942e00d510784406105420a065450f44514116400f80f000d88000b00c8004071051910b01e0101700c03c2c040500100e90061084d450301001d0a40d0b400580709400b00c400040c0d6840480358201050840300d00c60142c05688100f608032030004109810f54000c40c4a054a14081d54907824000141403412006410030600c113801400140b01001903c1c05480c0d1040e0100e502040101883c00e01e10024803503100c0c40f0303181110015811041c160143c200e20301645040c0c0310081000703100f1000310111200048000d40c000c400e450884042a440c0241c0b1038034080d5200b40d1000056a1070415084407640e03841168a00b00c04102c9000c2286400001c00151035034002c2c00340f40800940300188240b250030b096080490362100450302c0ca0b107c04145100122243e4004c02180ca0b01d61120101c40d0010100e22170740340c0c100031001c94004000b07040018055408401a41400304521007681647c00c50b819030042c81482403480710150f640c0c4903c00f4041080c01400140303440c1451300303081c1070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 204116834 1250 204115584 204115591
    0x70602071b05041e150503100b0916020d0f0516030f0215190e010f060b13081207021002010e12030901060f031e021801081b090601090302280b03010806 67
    0xf18504000700b09406003204a140600c01e40100c00202c81c1a4003410350100d103042c6c1c004c0e5402d4405c68280461b2070030309501c0f280201608440303a000b07a640e403550140c9182e00f980a0000160407210704442468010702000c5016401c50500d14281200300500840030310340d011003600041c600070b080035600e64061004003903082400704500103501e40181c41c00042251405450215551074a98100306e801c00c0d44030701c0101481c40800d00a40b80e5903d02c1140b40d8115900c10341d64100180310006100c2c000103100c000890094000904200d103580802510b0030710305030040159525210889401c18003400403a610303032200e401141c1c0300d040040342c0d1350031a0015002085c0d4202c1c1c503c0f040c004104101e0144118003105004800a40c2031440803413405050391459800d0b2204803800031131407202c0810440780644c08944007100501d40c3e60100b2a04240c00c0c2d45c201e002c80c584510520250600300c2501d5810a2a20003180094100c040c41c4015029140d20150505034048018025200c05002e101e81 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 204118084 1250 204116834 204116839
    0xd050312071101090512030907030c1203030c020313090515030a060921020c040e0c10090303080f0114040903030605030f06060a17031c060306020c0d03061707170102070602071b05 79
    0x4613850380e03207003690394000c50440404e103480030002a60440c01080004040c1d13502c98242c0eaa4599a0f4000140c0d122014200b140400e06001301c41d0100c510000a840c000040480074001a5180284000081ca80600303640100000982c42c030300591401c00029075071500c2a48000381500e0141009003c01403501404c5454480c90030001c150b180d0300240d0101584000c82c3c0024045510900d05880d10143c0c0c07032400d4205960b2415528420303040200601128000d84601815684500d08030741c20541c24011442054100c40c0c04044505050348030781d521310f200e4103000499640703a0000919061054011036400c1d80031100b040024107081e064000101082440c0f400c0450354080c6d0281c4034040d4022031211407a03000c528400c00307901b60300400b0003140c0188046655000c00707440a03489a00e461154070100381801c40000394a100e18903130b0000803e0100140078261b091480300d279002d207010409201d640d9020b110007070114540748010151184156802c1d00d241c4100c0040d004003100c81d6000c41c0c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 204119334 1250 204118084 204118091
    0x303060b040b07080c0c0a08060a0f0612030f09050a090b03010b06070f0f1b090615020703050705040e070b190807020c0307060819090b0613060b04090b0d050312071101 74
    0x2c400242c00c0b00740c9545030791019141c1e44a89000401d1807500c044844d82540c480400c404c00509032101007035050040741c0340c190a0004d060021126410360302180328450b0744034881c1c0e842c440820b11400b00c0a1a41c52640b1b4090f0115650310000341d40480b00340c0140f00a25602c40b8088481d00e0244034036900a182a07a1050070660507888015051001141c0a8030f0b1800c141081d03030810030b144000c4102c00c040d8030700c00e4900d0390b201d000d44030090605000b644480710844203803008140c000950316007140d5000b001031101d10308010520018000380f001d1140d09204d010700124480c0a600040c194050b2030003070f070b16000c100c0c1110040610030090002c00554100180d600c205440210b4240d0640d1050305000d1405d0300d03510610364440a90f03400080d130152a00312503808001058150034016202258041004040100103908a03200c41c405c00342022402c001c2004140305a40140030f407014020510808a01039864950070340e070241d08000100c0c440c01c0700b0820010741190300d030418100c6800081 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 204120584 1250 204119334 204119339
    0x314180c04060e0a051314160501020a0b07110c030102030c09041104060c0602090f0904030201050402240706050709030503070b011d0603030d0e0102160b10060503100b0a1403130303060b04 83
    0x926001c0015042e800b26a4175000017a0131440e1205520786d442d6400325940c11005555034035692111000516014051240000003c043d8400070b6540d030300c1500540d0000342612408002da0b441c80f07100c2c0ca4050503000d4a00c000c400f070f540a101031449044009480790b90382000400300b20850740c4512040306456000d120602c0131941c09055400401c2e40004010381d00d409010010303201c0140c6500c0342d0340c000303055000c0000305036064020347d00484c4259500041c07862505124004107a000809600118050190b140414556041140c000d946402c05124640d00c980701d42d402c6030700c2000c040e10140d0000004200c2947d02c5581c00c001030400b00d00c0a581801c2603000207481c2c0c4600c064070600b1649560040d564540c0a5044601e048a0000303120150171061801b420504821034800d0381c1440b512800045007800364003128400d620710030b0070040060410b4006401500705030207110800ca0540502241e070340111004500070951840601c82a082c180f4006050310003e03080408020000c0c03104 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 204121834 1250 204120584 204120599
    0x40c09030c0905190b03010f0507030b091b0a0804110a0305060708010b0f160309050402130602070503010504020603220c030c080607020d0203090f040e0313030b130f0809010314180c0406 82
    0x51328807082d503c00003003400d840800c0040d0140048824403c24076103403200303100c0000e406501014082800b5130b642c00190740d43c1c00c8800068100400c081c2c1c01c1050410101c00e00134401c50745035a026104001da045925201f8011800c402c4003034104840f40c1e4084401e104482742c1000e2018010700040f080342c0e20b00740014408509034003690b540c540142440480f00000c05000302c443c030029080150045490700400440c02e4101100c521846000d030044081c081064181802220310a03500030b441035203540c54448040b00440c203d000d5502800009258000014284220560055006480700d94480741440c138581d00303261005d0032640c1590700c4040b50704d10544d0080f00369869240220380c40d5545010f80c0c0d01240203050341001021160100052000044445400800c2070340d004210140d415a0fa2100040d44002c05c0440940b0000c0308482640002c2d090704000c00001c041031401043e0010b035080d44500d4440103840360344e17540c019072074000780340c800070000b100080c0000c0340c082c4a07440ca880174 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 204123084 1250 204121834 204121861
    0x30c0c0f0510120f050c09040f02030f13170a021005010b0307021e030c07081510140d06020712020105150103230901060f08150115121505040c09030c0905 68
    0x2060000f44450045106a180d121445400c15504144124544014020429405400117a210b0391400c0c212200902061083d60302c2030b0070500090704a6100c0c1400e40048011401d400c5401d01c07110401d881002c402200602446852500108025040d01c0b400000340c60f0144c001e812902c10502c2040541503002801c3c200c052181c080740195007866108172403c42c4580e840405803403040000c000380d000000070f04024482500300c009841500c0e40a64041149603600c54030050144112915116142c0781c03444000151103600014a420040c1c2c0d28509004505840413000d07175965010040d40703002c1410040c40c05002481c0400034400001c0ca149a502ea00d8005840e10505110005881600035809100a001c0d01508101300e2552284100d56548a001600c58084010400004c0094940c4102001030380c40b910f50a0b20740c0840003c2000030f2521340c3c041c80f41031083c0700300000c2d07130b80b0b0745d211b40e43c0300b84403584e90081c846041d0b0904200340005507020282d00c80c40d100130820408552103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 204124334 1250 204123084 204123109
    0xa0b0d0209040219081207050d08071d01020a0f080c010606110a0b1902040305030a0e063126150403020a1202030f0d06060e01020627100207030c0c0f05 67
    0x94070710024906460b00ca40c0c482c030081d0840d000c81c0c0f01d0300d921078100040d100003804030f1500c22009c44400c4200000b08507003140040d90850040b44481054843c2e00001c0405031051000600c1281c07180780f410785030003000c00a526415a00d0460014149059403001c0c096100a0a01030030261001d8004460b030300d95403a08080c001d02420450300100d054415810048032155101707040a6446075141d04040351264884400c4030082880000c01500a01b0003409558441d59580746848075050250f00c401240c00c0702c62003c01198011010100d40c441c2d4206801602180d442807410700240020140d038604000007105140c281c60036810440044d900040c0c41000700e40c849010401c2d900c141c85e043e4514061944403030b0503200082186065041a0341c400c4040f5400d5586d10041100745034016030b150301d0240d43d2800c0076008070451200c0140481c5809400452540440e6109001400b401c1d003241c005100031400102c2c1d0102e20b001b40300b080d4035814060861038603d070002c01c0ca048006807001c020031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 204125584 1250 204124334 204124339
    0x50f010e1f03090807060501081e0304060f2706030c09080319020a1218090207050c15040b0f0d200423030604050604030305160206060f040603080d02030a0b0d02090402 74
    0x2010703241034281c440d0b00110450341d84800d4554a40382e2510b03203100a08002d0040804c00d00c0b17034240c025844420a0800b0000380d000340080d6240c10704001084860f400608054418818a03081410290041c6240491910303217081e2a40c00b510b05003c1c005003915210030001c0c040203000741c0c0a0154440102c1200c0035000444511302900700781c2c1c0030503414001288005001102c4141ca40320380c203600015601602d0001505501000b52a248040102d001e21280034001e0707404000d0700641424407215051440314110b001d10f05040d520030031580142c1c001c10310390400c1040881c410420340c0040c000c520382000c3e0216081014000c44140c40943d002d148180b010200107000d403800ca01c8898800303c0f00f44d00c1d0150595829240c1410081c2e13440c102aa0202c0c0081c2c81c00c000952848001e022000c0303144010350180965450300d03800c0007050944420815813003691842c00100148a4070010440c002410b400941c482c42c11440c200101d84011100b5806000f00201c5900143e0314951101d500c543d04 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 204126834 1250 204125584 204125629
    0xf0105160204060b071a0c070f02010f1206080705030613080a030f0b150a121503020f060c16140603010b0d02070c030c17160e0115030e16050f010e 65
    0x500000b4090100d07a408140e030348100044060502c03500b010480c6662215480307900300c035207900c507000c0c05611804130b0141410262495100043d0302c5402c1d070801e44040c41c50188004280c1c81142070803640a60700c2804540c0c0800010405801c050141c6984902c0700d80c03041401d4003007611414081d10407004504101551900b08894581c0c4640c405660000c001c1c191400302d40c482804400240d0120110201041c41c41d50034203403152881c059595580480a40d00340e4461541c0e09004011110400b40d5900c1102800401114001040270f000c01107800410828010324015080400d031616200d01d5008400410050001c10031a404841001000001c016624219410075122502803070b000206104045480000c0c0b0214200720180b640d000c035003d9a0000310090020b0b50048070700c3c032403a4141010140100031404c0010078407851f80b2081c2c03e012510090205849041180709030040c0900610210184024148051a080010801e0a090079061001000540e08504d07800070b80100d08d44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 204128084 1250 204126834 204126877
    0x30f03040b0f1e0f030f0a06050a060c060e0609070e070206103501020406030608061e09030d15031202010b010804110105160627080307030c0311070f060b0f0105 71
    0x80781d0f810f0803980c0c81c0790701d5400d40b242c03003000c4c8038007495100b9940d107804060080003040400c5041d2060310100c500040990079818a010815100c02810b2074064500c00d5965081c5007141c1c02c248401c0e845540454050007145040407801c04607044d0140c180801c550015003000038003140d06109009079209542c4209007104000c0868602008103c5500c01d411411071981d42c4410054015000740e900380d072410310826845513500d03541d42d90200c50000910040d08500e036290768191008075003184460095902d003648400d5594142c0700c8401120003c94081c00f01002800404c2c0c03402d09a40500d44020b11004a005000030300034a4050000340030364080385000e41c041d82c0164100c4402c0b555410b550f045411550800c00d00810b0008510410310410400900840361054030a05600394000c02e140d041d6146d54000324010014104100141540d4030385545559003645c01400340325102d6043c251919001e031804000343c52008800314010b2840c0e81550f04280c0c0c01c84140c401010203003160121151 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 204129334 1250 204128084 204128107
    0x30703050613150602070602010c050d02090d0b0103080301080c04330906090219030e0706120b0603130221070308130e070c05011505090105061e0a020c030f03040b0f 73
    0x101c00c000003042c1c1c1d454408106990300100c02004211105602501d0000b41c0d5401c069003030300c20901c041d0000400410910b07001085942c050030401d180078020800f54602a603400b1400942a0401e441d08600440108840340c3d04014942c00c40c2070a840601c00d51003078000b658000e084540800303a5104440b085040c241110707110903030040020781c0c402d200a9a0f03c0651070029800400c000c102c000846402d603c01500900a008490724100c2c01406424684201280e900704007440d1030012580f5070f4546040f990710074000d1030044005502010b8002841d01c1005407600060321544981a2a02001060b0b4100031071800116a002071081e60759501c13842d81036080400d503030070980d02200040103001034590b000d007030500f06612900013042030303a55013005100315003214400c1503404444403006120301d051403000b4001c64608a20043c04500c3c2d0018070f00d01c030b5000141064010782c484102d101c01840c0c10082c5202e5104000060b5261078101031700405a44914a607014000300000758001100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 204130584 1250 204129334 204129349
    0x901050a020f1917131203090905070e090f0601080604090303020c0105070206010e09070b0412060209030106032603011401030b0316030b04060c1b0314070c0801060603060b0c030307030506 83
    0x1100402c06480a41124a0b009501c1520004064800c2c05164100748440d84114040703c002c00c80000718184071914002c0c40302e203d040810021001c1004421002401010700c0c0110b6000b0303a45c5842d4090400c06c9a000d210f0300380c0303005288800303c42d60003040c0241a42c0003801c080d00070105850216500d41981815000b074400c80702e0740350480d0301e0310f000c21540340d9010518038141e5640184200868403010345603550b469a500030303000c500208120030010285000c0c0300303140c154070440c0c4c098101b01c0800c00082c2101e03010360003a1111030001c0c03800c4c1c1000c421000f0007180ca941030301e219400c55041c070900c599108100d000407414103079503140c0240243d80400c046032240415036171b5184410707201c0c0b80000c600c100944044440c2403c0c10580181c55014104049695074a103911140c40c4409072402c5030701c03d2a950000100c01c00401007100410b40450602c0050100703400049000340c54084028111080c9600a603150b81c01448003841483e07001c412642c00c06058600855a602c44100142d0305 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 204131834 1250 204130584 204130603
    0xa050a110f030108120315090601030905150a0b01050c0a0813030c180b040603030f0f05040b0c0109020a0f0513020f040b0a021c0509030a150207021011010507050f0901050a02 77
    0x800d2404240381c06a0481c6100840c140d400300700540d4280722040014074424002601c09405400c07214120f030825041420301141e2014052401040044840d21081c2c103051000700840300c082021800c00602140a0007020b4900340203181c0360345043c010b1940592250b00b00ba02c01040c0740000a000c08071044e42940d014091034000403080c02103540d41d180d00460545600490100508049141e5428585031203407034212901741d22442402c0350002403c60b090303000e444034002402410301002c1004030f87d280141c0b5100c20014000101011140108166203c080e882000e12515541d02032046031940100058021110400540c4030f03e0311485980c1c2070702641d006035a56420115032000c2550340080c441c08200070301c03a40d007001900c040303c0440e1107104071454560076034000c01261001078001c0308581e2070148694001401e044040e4001068020002c1e0800c00007101d005100b004800e083c481e0030b80100643c2016854200541c07911302041c052450018181700d001319045104074004d2044108 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 204133084 1250 204131834 204131861
    0x50c04050907030b060a03080702060c16060c230304150903061815050702120a030b03030403120206070e010c1113111e0c0604060b0a08030708031b070b0a050a 70
    0x100d490903070440e680c1c0781c00d180310559403102110b0215290382480600394055a40204030346140400d26001d00080b98085c2d07001d100284290b107050041c04035810b91100182100d669014410503080c108140d086c0d0010791105e41c1918441039181031086c0001c1101c00b107901000003168880d240704000d489000440c0c1c00500124102140c03a68401886046a401035204806002c0391000108040c1c0807200111180c80250740f000c0301500b001003104d03019050b49403041c500402d030700945001080c15500164011034619099180030901c140d010b0091640c040c101e80381c2080c0046031800000c1c020799281070050015000f507504076400361a680d9540054070300b001400e0105038811501c0b50090740c040c1d134410724010455040303101c411240304101c502c2850f10100800080c0c81d591154001041d103000050b50196102c01e00007801c19050000d041c0080c040c094107500c91426420f159072043c6c0c2002d0000340d44d4020003401d000140081d500d15046809a8070003e01342d42c4920010000f040e00600304030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 204134334 1250 204133084 204133091
    0x4111f030b010521062b031707140c0111041203020f1903081801090c050a0b0403020a15020f0a060506041103040305070b10051c05070911030103030c230f1e031204050c04 75
    0xc1d40c4a101d111804100748a40c1c0c1c0c0001c0c401034020000b0209234150340b5080054441c450b410b2076a11244082c040000d0900000129826100c03d4100705031b100d030740078050800c1075030444402d05405000d02c0ea010384445000e07050403500b00a00e1031711000c903c540102072120b8480400c04100d003020300d241032001d180300200500d944500b48610b0114161013450320680c0350350000304000ca4280e080d18100da902030402c4c480725090110202c1c103945000a13020451241041070780700d10a04000c1240c40c18007800000541c1c1c14082d00b444182c1c3c414440342001504e08200b88000240d00c0b804491100b500580441001d07110404141d00801e096405a035008035204a02e0f4081c1050303180c40d1070890303c5101103c000683e90680d40040d140b0b1015003200c4140b0074001000464010b50542100303601c00e49040324940a40e102480071648200e045004075840104000e085000420204600340181440242030706014928507569102d18000c2140340d502d61070124040080401a04c2c3d00b1103c01842030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 204135584 1250 204134334 204134389
    0x30315080c28051c0c0b03041205030403081f05030609010c09140f10020709020f07030806010810150905060f12130c030201050304111f030b01052106 66
    0x990703200800d60180d840b40e03914500203850b00c101c404070000051048a80c82c442c191904080081d48004c1c005520074001d002010100042c14007002d1030081d2200480e83d503140d00f007030700300a4000c0745994565014001c0c104140f002203500143d00320b5100d1140d2414168000c0380c02002141c480a03984103541506c07034482845031480301034000203180d20051392680c5030700f0340d190140000c20115814403500f0000720000c40403142003008044024172404d00403268001e0307950005004030303885000b564000d01d00c0450143c08059101c00c03950f4020400b444c11a040f81040c0c00c040c056800a441a44401461404182c0d00d450051120100400d0000c02203a100c510139141c9182c554840c0f500500005801c90028403624015080040e800d9000780e1180c02c1941140d00540d05035002030b209503190160b1624081c0156640a09007410990758091201ca18061030301c0902520002032119060200501514803e01480b1000c5407507140704451030a025210140400c065007440e060b080012602004c4a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 204136690 1106 204135584 204135599
    0x118020f01050c2503030f050a1d03101409190803040809130f0b030706030608060a0f1d011b03020711190f0e0411030f0601030f030315 60
    0x211404804c800808501301014a09103041403030154005004040e070042d0560403000c220305002d070901c1e000c0300000d80804200800102045a00b00704664544d48c100312107250310b00d01c048200052032000700882c7c2e511360125541489441440c0d4102e80c1d206203007503030055903900301c090a400c1da1111356403810558400460640c2c0003030680c6803841c854460f4840e8010210402c180041c1007020340d81894104031503544004140352402e0401c0050810208455901582207500084d4500c80c18440074020300e4220444030300188850411000024154400b4143d080b002200c04802f049800003207050344140640100f442d172200c0c64100340380c10038a0042e084d900304040105805916035889070100c2d2465402507902012503001d1006002c1c4000c5505600742094000d4109407520703881181d501c041c1840010045a1200300d10810305200394842114540e0700f420131603039103664110 = true := by decide +kernel

theorem cover : BRFrame.Cov 203956834 204136690 := by
  have h0 := BRFrame.cov_init 203956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 203956834 ≤ n) (h2 : n < 204136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
