-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4420
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:33:39.794133+00:00
-- url     : https://prove2.me/submissions/f0cf6143-dc61-4708-b6c8-e34befce237d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 794784172 ≤ n < 794964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 794785422 1250 794784172 794784181
    0x1020d0f0e04060303050316030b030c011116080604030807210c090b120601031d0309040f090210090807090c1b02010e030a0623060607030f020c120609060c0a090608 73
    0x8032100e00d440c041e260020700301070004c02031507040801107005c0c49180700e0704101a0b440c4030301101120004640950305811840402003250b101e0741d030311148100000150b541c44621000f40009089990340300f9156504014204401d15810103d040c1d400200380c241418038041032806580908400c000f24948141c1c3c0b45d000c01d141502c40d010340409130890000b4141e44e8422071409580b001d904031400e5000034248504421507488841a04200201e058011410710b03c1c10820030025020080c9298101c82e0f60340107030b0b00941d07517100031440c102c46a503e403040710383d00300150301e400c100c815040800b031182015500d0214035403220700c040890107003114200400006100496212001c1e615459061043d26009400e2050341d0b80101ca500d04014150454031500000016408101311441075000005220100c0428020716002101c0c041900c1540c000c054210300103480d00700503c100180e168820b20400c501c229041104641029030580101d0a0101e916001449987e00d4028041040400c80104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 794786672 1250 794785422 794785427
    0x20102010522140f010c020102040f0911041211330c0a1704170303090d090315090501090c060203090306130c0303180b0a0e010e090f01120503040e10081b01020d0f 72
    0x100c2130404203400070b100c030f82030200000303020350014000e4060503240c201d000145807a09110f0910b8081da080740c0d803401d10345003600d528000c0c1c1c02d403041070303034000c0b000c4821680990314640d1002c0e440ca24051100a581c10a0180c1840c0040b84104038103c22410003400c08c110100207a9903041c56072004000c480a980f5008007196401158801c0010301c0010040c01c50080d400710145210303050761000c880c65148881c8040300d191102c2d100c0502001049000d02203851155040202c4c041d000e5000460680015665251441e0055008070300580020030340c044a0700e014020560490100701040e00e0040040d204c8a80d0718246220040a0140148608003040e0088910718010046c1c3d060081c0c132b83d9400040070f850200300b0108140010710b80c01030482c0038541105d929000c0c1c1c6041d0914185682008003c1d09031860122080e40c0b54031003440006802c0200350140c9102e0302e0300e0071000300028070302000c0c1c0b4a00b1007400d40720504000021414001a40e002071121040107007444c0800308616052402e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 794787922 1250 794786672 794786683
    0xd140a060f020316110c060d14090f0f061509070201140705250b0a0b011b03050912010507091403191505070203031312141b0d0f020a08130b1602010201052214 70
    0x1c01c14800890800848000101d42f22681425990558212511807070318103403150800c6035012140c04040d51241c2d103900b040c0da10716900032203d000005032081d551b0001080e520084966400244000510640700007102078103014004a0601202d4018926651000300c0d80d401841e00302000c2d516030720174030168441d0b40300000003c09000d400040c50f285060040480c0d004d00d110030b008118010100d27042e60414030034035102c1d070b01650703071208074a0501000030010f0201407480daa05200e0356000704401402080702810f507a00c01c00801d0145428541d00c9820340390018114015500184100640418030203104806c00303501404e81440d040d49500251440c0220060740b2460302c602050800b8010302101948000d2161001152180030410108031100e170001111100181c00210442e000682500c0181040c080204400351000f51075801455407600400c1c08030842003556822003040d56028400d064000741c21b000340d0232508203400040d4424505601008000012500003403d151005111 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 794789172 1250 794787922 794787941
    0xd05040c1a030f0c18090612100e07090902150d0f020f0310080d090308031008030f0d0c03050c04051e0402191b020d140a060f020316110c060d 63
    0x541c038030904071440c01180c4582040310700198580403000450203035010842619070021201146400743c520307050901801940261089401c8000031145000502080c004060840380f41c42c800070b498180b0381161441c03d0766230fa000e061082d00d84403c0b60056101c101820224054440d80346941d07100145c7c0000c0100310019048420500c04240703c0d00c550901360040d806210407001311000207071901c082c1510b42a907a040d410125200c00c1082000034100805181d01c0308580d0b000f2007215070354903005030a641c0004501c206c0c10400261a54403d69903100313490840025207001c21003845c1001c80c00300ba500c15402405c4c45032680389104110381c14403844100381c28002500c00c0d03403105174610508a51404001441004c075072144400c03030b030b2643c800d103005404a4004000351428030840e1100140300c90f04c3c0603100e8260060040035404100c040c0501403440750407a10060380d915024070280c050b0186a0074030801c2150000c85c142d0401c100144960810508594542e035512030b20700d081d07008118840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 794790422 1250 794789172 794789189
    0xb0102120c0316030e0d0b0103140c1309050f01060b031009140601200a0b0a0605060712050a090e010303080f09240a0609051302090c120103030f1704200301060503030d05040c 77
    0xf00c082140700a007e5048030320840c2c0345080410340072812611190303010000340d0000300702c4036109400f074125080102070502850030b030b039001c00051050a081d03c40b0341e00801c1c0a100300100b84030341c400f441c809800c02000402420415440130040c640e90341c5c44041d100504208200c0150091f40d0f14282001d0078080d0583c0407650030311640e103000506400200c820500c806d15001000a107070030103004542d15581c1c41807154160f4504c006050312203800c102221000c1240c1030038042400007144100c00d01860081d1600c030b00614001a09610280300140709030703c650096045543d503c4c0700301090040c00007046210a40c41d50f1607034451002000c542d400715000e81d080805001c03034079481c0250900031900a442c1c120b4980d82d100d00000242c481c150300a04007092610041020900c00c04401440a83d00d00e40070410a4801c080c1904001c81a00c0c01d407501d4100140100d00d0484810a2048106040e4000d215241c41c0000003604c1c0c4c020f0483d07a200c0139845000207000c10905c4500403000d0700c070b4407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 794791672 1250 794790422 794790439
    0x106080f07121a100e06040302190b0301120605070f0507122c0405060108060904061104180c02010b01180e0c090604031b051c020112110d0b0102120c0316030e 70
    0x31058030406000c83d0440c14000e000040b40340300018071500002c00e18560140070a0f282c10318581c2440ba0410a02e1042480c18801070710111304502d8000046000b0b01c0740d00d034541e65401031402e1a1084400c044c0911040c008211030440700310750090305a4079040c1d0081442c1c2c19402c02e000042d28240d0f80001c08458109808100c03145c8075025201d00510044290b504000c0ca540380b00055440500a8900c03540c08001000000e00090158004100b000c45a071113550500c2c0d87c3d1344c448130f502da03018501d10460351344407003202c010580e09106100c10f001013480c00001d030b110381d4144031200b1101400343c100c141074503100140280740503c00b02ea44080020305442d55442c2d9904100c0090203502d8508040818225000282407500d07420080d452031225691300d5081e0401e074019180e1901400e586140c2c43d48400d444080a50380d44003409101b0060034002c0303034100c0d070980020709111903060f81e07280520301400701641c5550700206481c0c00382c02213182c00d00c80d43d40700e041c152800451001c000f648500c51 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 794792922 1250 794791672 794791691
    0x402011209171b0c01020a0f06020f030a0609150b0f0a090f1d0901091a0a0b18070f11060604200c03040f0b09130216060207050708150106080f0712 65
    0x203100c0240074003c1d240d8061843e140369882ca0340d4462001c11040c50041c0d0150b5207440209500041400805218110051402b0f0140b10050b0480d00b080f00d08415155851030108594013450207403406228451502043d2182405195a814050840c3c944102040442c078400042d024100c202e001e080040301c1c070050165038410a00600c011a00d46e816101d070300c280860300032403050080747c0c5c0842d40645868502d400369452690b60000003070200c001c0940f904c41107011a00d41c1540c1080c01004205144040d2500d0348025000281b855070340e100b000b083d2a20302e144424003148080d0050412107010034129114000c4030048050103501c52145000050300385c2d456000000100201d900032001d441d40c2c03a50354200b0b04803c0c01006c2e2483c1d0000c541c00d03614460f01d1103035801040d048803200c00f961a0301c5c0c06030b2140c0c030403a0030500003101c4662088805020840e801c00180b000e8516940344e0202542c10301d0340080aa5070040c014240380c184090205035494003a2102448440c0901000c2005c5241c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 794794172 1250 794792922 794792963
    0x918030d1803270b071109270a02010e120a12050a09050f1e03072d0906180b030312070e090601030510120501020403080a0203130b040e0402011209 65
    0x7000c5012070b0003080410008084001489114146881540011840c1c511900303e99401128100c80d0b505c01d070410036015a9441c00042c4c007681d0b035581c440340142c00014801d801030840c02110002648a2070300100180e80c0401c4086085000340c2d040c2c6c2e0046400b601031440c03c50550070061600c002c0c2074420340d0f40c0fa0b100001c0c1510b03135103681da0b10020130364990612615103800200d0716004503110043c1b2243c0c0f01504038525607450b010b0101d917452981c501040e00509030020440c1c0c000c03100000410b9441d40c1d0450300101030302c00c500081007403610303112400110049100d0b00034909520344c49004002d03503080c8203807031003001140301e04075062401c1d03180107010400f50489144107001c3c01020682701d51081c400c1d07a10404460000706241030800140d01d240321041c136421250356400304004400240b407407001c3c00b03120300560000d41e20740c22003a00b1580004820380210b1030544085c40100b003c6860034248a41060b02820800303002d941e06c0c0902c40150401d848060800a010a104a0b0303902 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 794795422 1250 794794172 794794211
    0x50c03062d06210106121b05030a0903091e06110105070c020d0c05151218032502120c01020f0a021507031b11030f1908210109290918030d 61
    0x1254038100103004d58902c0030041c3c00140701e0561f001650a0001446c110001da08c002c01d060701a007403100a00303a95550305003049145500382400e80c20010400c1180315049190282d80c01c0f9054001d00407864150802400341c107030058013a20400580340054103001d006040764014102c003424038200180c0c0d0001540700b5601c00b89802000551440c0000d461002d01d055500c6072128640207586406540507222074468550003140720310f007d446c1800c0005030f5030340410510003601c1e90080d0041c050b01300f0002e42040c0455821102c29042410341d000183c1c0d40d0458034180040d14030307031152a800c0d2401d084400c2812410f034003019401c01c0324058280b0200007011071106404500300e880c13005078400c4180d22040024583c101e134044c0050035100064450020b00444448500040e030f0000b5000c083c100001400c2e840071b51090390703a0101c08002d00000404000444112405003070441a41e0f0109021000040001c16815480e00e442602000203004580c5980e00c0e28005008841c3c40c0d480282800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 794796672 1250 794795422 794795447
    0x60903080a0c0815030708031204021009031a070c0609030c0605060a1a1605072405040308030601080421020c1f08010b090a0306050c03062d06210106 66
    0x25644000900448403500615030410000e50f07403000359484002c1504602c2800d811629414058103401280c034001c100040c26106c1d08038114803c06080900511000c0c03901d084540041040454061002c6900180c0840c440c0700c20038655101a542e03050200c030060701009000345805d04000034403060541c40b00039000f60b03901407802044103031100010080000420b10454205c8010024503c070541c0110026002100440030300c915451f03100d568ad01d00340110741c6c100b51a2640300384c4c0410581c0d90600c0c101140304190f4141140361504544500d420b80c00003d25280c1000600b40c0000c1c00c001b9030030341c10301820502c204541840f40c0304080180d192a01d81e165540503e10041501400e512400207542851403940c640f92856420080310f146254000700d0700d244c009a0b2030301d00100040c0c40b0f1041d42d101d17460f011052a203a040100030804110340e00b00c1c202484007404000d60a030301e82000c41d01e40c0c0d07800046844542c1c0783c1140402c1807806c050381c0304180307400c040e5a00000c0c0141d048178180c1000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 794797922 1250 794796672 794796677
    0x60315050703060b1806071104090f0525090504050c040606090602120735030c180d0b060607320d08010b0409091103101a090609042d060903 62
    0xa986506110b4141d005d0012000150400304400b6881c909010006091150103000b03030f00c501e02c14a40115003603c1c3c0c080c90882c0c4980d41000c2000921800348034046140e00030403895446045100100c5098920a0042c482001e6452010404000c020045140781501c040d00074400c0c59039610300a0704000d800d11401c4050f02078000d40210300034112040350381071799000d0003c003035540e03000c010324200600c0b6806004d201c4030070060040800c2e808801440c403070075800410a94440d0030203403541080260300c1c41c0380e0203001d0003188180018195118943c0c8094281da8803500e50010b400d20032411b150761034050139607020a0010204046550740e00c1000844618204c8504015940d01160140300c24070a408450006000c180030f07610540c0c104400081c0680c014490604d000c100080c1000e0710710004010640c1d0b02c40550700103081199042920807800c07600501e0038907002000c02d04010300180000c28146501c044442024007804600b00322000d10700c4020f420031000e1400c5001003a003c5010b42c01b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 794799172 1250 794797922 794797931
    0x71406010f0602070e1b07080f03220f0b2d040b0f01030b070c061b120608010c1b02060705060f04201f050c0115050a0602030a080c0904060315050703 66
    0x2c2d41400040e26000310f840180001d1201e0340c61070840180c069121159190302c8204010300c1e40841d82a001a08150a1400c09180e8906000c8485101505000c1e013a40100031050501008166040203004030540c0181009070580d84582610b0301c041c18488255411503180c2d840d86114000741c00a051040b441014600c0094990440300f5441540034880140140045000610224070840303003944150721854021504150a0b8214080800f80d41070f21000901e0115403041d001c041d5000b100c008041407802000740303d8440400030038401886000c03201c1d81040800150454544900701e59001e0741010540d81c9500740001800c000d417200747c605a507684140078803040e5000048081c02c0d0882001000014aa101400e01d120104e040d501070a09101041c003101c0c2000f0028018107403845d20800c0d2000c1114144020401483c11540081003154814000c05032969000020303603130002c041c40145626101254002005000b080e0401008105030203da009042c18a80001d070082c2c6040d1410700 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 794800422 1250 794799172 794799179
    0xc020a030e0118141c050a110a03060504061b05090a0521010603030206070822140a0c0803091f0509063604052401200304060e10050717030705071406010f 68
    0x1751100004030300640b15810029143c00001c049a0324140ca600001e8441342105540c2d8843c07804881080310150f0f8815229014489070044941c0c100c2080e084a04149084c40070b503402103814001c041c014540599170410190940c0c222021840e0a10b0260300700a111032a00c0e803800a407211415100da5000c16142c00104010500e10b0b142d0207502c02c66000401d040070350b1915048548548010b00c24a2406582c84810200301024511401f903c180ca0003036940741c7d42e10040c01900300c04682410440c01411104488069219003104c801d60030842c0d031184c0352410120450518020030710800f401d820011000a00955840454044d09004031001c100c0c50396642310307149101c0741c800b00070050b40c0c4040391400d81944c06065030440c40b10751708608004d07240208148500d91740c0141c210801040c1d40446402c418a014016075025403403624000703007021070b5982c0382e0701c0344141a03480005039000030000550113440782e0141c8224641000c0c5d02d1024005101140352161343c280030b08403035125500d02c0070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 794801672 1250 794800422 794800459
    0xa0504031202071e0b030714070c140a0801090809040b011209060525171e01030f02210703081b010203071205130b0f040203070302100513090c020a030e011814 70
    0x107011500559440c038610383d1031900c11501640236030105a00c480d014840301010075403095103000600303e481d01080c4414207000400910004591203100140e04100100e80058448020740d035140000340c401007854020345005030750010f002c861103510185032102020502519810240c01342186140700315408114070750660f034a20002c5104808110301104641d480300404454540c444e44100810980714000a0401c07940c0c0002c2c1e10658220744281c2e2000c05501e17000300c2034040e5480100c0091034000402c02c0c400d840c0c1c90903101c00340c0402c41c00704e40800307582c001d813000561a0f107101300219620b01e0018000381c1680c441290741c0708284c0c50080000d81100c20854220360154102c0510200c0d60399a8810703801d034020040049825000e0b0f00300010040c0c80748001c041c14034034291103442d11303030158012100780c08905a10042c402420042100e0506401243c500071a80c3c140c40c0452410050000503107d81c02e10220003a10b2104002c80010b5080e000c01030591074800465602428989503140d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 794802922 1250 794801672 794801729
    0xc050607170604060506190e12070305100501030c1205151f08030c0a0602130305010e0a031e05090402070302010605030f010e01060807030c120c030209180c030a12050a050403120207 80
    0x14641c010001704611a080107e4420214040c0103600e00114450035020100f403042c410202111282d80c0040800c1c810440180714903071110380340c01c0d400c11241d8035503124900d004803903101d00d0400d1850210600e040c003d0030310040300d00802d8440900f00e2414030109044090005d204086513109260b607010800364808006c4804c07204e500c1c00104117010041cbc039803000039405856244442e820102e00000010028018401481d0000000d01200c030114140641000c69219103682c6085080400c20041c5412005a4144150607500181ca45105260a038014900c40c2c110726418030402303082d4102000d05401c00d403440d030004030003400260395521300c25980d41001d00005200c0d041d012801e1200380c0342100c901501c2400340845001441d941e40106180803000d903803860821001c12410100c0340020010004400800d4000707007860141034569048180b004a00c8004011000170302c01c00c2a4070400c1643c014542108000e4650392411902a40d24010f03486000d040b03035480c1c0d4085000e1512080c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 794804172 1250 794802922 794802929
    0x12030f02010c05180f040f051b120103060504110a0308041a0405060a180b03100e0f09060c030a111605011524480201021c0c05060717060406 62
    0x851078106184108440c0489590055107900107101858003403696417030f4042d070340120300b02e0761000408c0e0919038086d121201c204403404000c1300080080c04a00035014004074116500442c000070303642c456282c407102038020740b01c07125800101d242001c81445409070050003140c2a02c0b0341302c40050008489000c0034025031041c0f1741d1000e414841c84000324021128004141d5280e418445115283c046c54051a002912800000300d120030050001e402e0480b4160303000000c4151102082c50011455540c50000410360140981c0220118920f000107821141d1139203074401c1071603114209508810340b130085080c0152079660134011401c0c100201c0115003425500c1d031403500001549000d05540c0d51180a01d6038104101c00350320044100064031041c4030345c000e0031340303601c2c420b00888207481c994010a60841018000c1da20b424040145e03000981d40080e151040343c1c2c2e601c80c50050005413660100100007034484c0c0a240304100100ba400303090741c15828071503407091039a40c40744000d20045030000d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 794805422 1250 794804172 794804177
    0x61401090503071a191e050924040b12040b220623130507060206060609090a02041208071406010e0f09010e0304080102090a0519290412030f02010c 65
    0x4000d20124844c851a000c032600c42d030110034070300301d015165004501004180c10000602d0810a14100c0341c4011003510364000b186030003820041140c00040441c1c03181c07003d5a100701c4002c5060044006030f901907900a107903040100e6100c954284084e0300c100001c0707034111061070030600015188088035035019030450060118104a00301c03070351501d000304001d20106919500b0400781000071981c0104407407150409455150002100c0e1514928003440c0350080b0044d9084142042025202c03042603d0a0080c00c403503180c10398442e0b902c0b00000344150b4009107034004c1e07519079160510000c1c1000304102d510401d0032026040380c0001c1947c40d51428000c0e030b01aa0300041c0850001300d40c444940345c03c22111345c000107041d54605101850b41c0c1c440e40c0041c10340d03500800d110b5641d25003120014010b08003911801080504454503400c00340850085020204034079865540d44c1c0c00f103894407645c0041c0070a030a0b66403900d0b840b00c2d0b680708124000880002e0b0750905018242403060142d02e5181400380c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 794806672 1250 794805422 794805433
    0x60909030912050c09071e111902040605060304080309070902030c091e031f0c050414010c08131d0601050a0c140f10051b0a090905180d03061401090503 67
    0x8500360900d02c07210076180361240e8000b2807116038803000d0366400303584c042d01c440404c00902c400e88000380000ca6080e03c14400310034100e00d621980480c40a000c100c49a400e44c512400c50310006008068a4000c41c4d0006404170810042000200045004201e20412100c900d071382c0c1c4403441c040e484120b90401200100b0b00400525003041d1803400c10020321381c025681003a000d2004070b45002003a0541d050550351889408203403144030700c1100340e01125450403600d0a4280031041003600ca424000b541081804203105040c0150304c0c06480d044450f4032035140e2034a030b881940012048086020b0550700c00d2000120702d03d503001e54110340c0c07480503e448080c075600f9140c4468202c401a080d00070014000c425025440307504c01d1181200744580e0340f40010b0581841200d01541240c44201001c1020b420030030314080716080013590040f170b06101e101041c1a80c4407140002061001084140c0314400d003c030f030442458058015906580031401e2031241c0302c0c268001103a200907188503080d09500b11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 794807922 1250 794806672 794806679
    0x2030907170a20060403140a12031a091806070c03020c01090608040f02210615060406080c0a05070c0305010203090c1c1103010e15010e0109020406050f090a150207090609090309 78
    0x482180c24154200103000c917090680e60380720124102c006a203280e030f803a007006c00d10204000404040c400f007514103140070056140a04d8184d4940307140380045500c1002a00001100c40c04900480501c1625080664250f420036000152082d541600110058000c0c810b0b07100ca9544901e082c07104840303d554034000d4507111619505140b4680e071405a030000708070007601c0a0245980309070b11090b800840205400c1c0b030882194034020300401240ca00c40c50080004010056105101a070400c070746000f49696075a1820054a4a00c1502002041c0f403170900c07400800d0100650245200382d11502c01d54241030b02c10030410909103007a02d5401c0c050381c1c2d010300d030402290301c90400384a4041c2c043c00000385400342c0c48020b0319000360078072190000120080140444401211803034014a00400254240342c10131201a04601680c440d800f080007001c6141651643d94040c01c00042603000781450781d00d4000c0b08003d44401c0e450050318411740c03c2c43d400050801e80c03803080703114080e010fa4407103050728107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 794809172 1250 794807922 794807963
    0xd030501080c1c030c02280e01030218090106030c12030305090d02030a120b180912130302011b17041e03020d060b120d020105061005130510110102030907170a 70
    0xa090f081030702004040780e60200182c4520107865a83e00c40c2e035008103802c0510b00c0c1076a6002145070800740d5107018440040005856000162642000c0907158a0980c4d450381c0006005100c150300107082c21441400006050030a181c9840b0124007a54050010360b4420702c2c130300e942d0200302ca070000069008002e07445401e0b1240030b1410130481401c40116045014000240e0100750b2003000180b041d5007c07082c80100d000c20000d075559035405480032030800d400217000c00e10100091001034144224212416031100d8000700844503903a01802d80014804801c0740900c81d50030500030b64500c100c02c00c0380c40101031a02d800e5441140e078001d088800300005545c03003201507c01d410300360360021110f08443c44d24400c103211040800849500001301441c02808114020748251301580500104100585100200104041c01d07610184c9010710000e00d40c100440b41c68010010710312440d48044144001c3c0342c004100c03803044a07085e020406500c00c00c8150305132190010103000b0520107482442160012 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 794810422 1250 794809172 794809219
    0x915020d060902040311121207240504060509070501020c0901180e0a03050a030c0302090f090403050c07032a08030d2007050d030f110d0b031e0d030501080c 69
    0x8106a401061465030ba4148000743d8005802c2145d00c0075114162003854200002c039030041c04892002416001180051a070a622900c00090b00c0d030042c40043c1d14011000303010700182450001030802161810b800c1c084020a000c3e1a14040781c012400001205d62000807044030f0601d008084803416440c080c2c00f00d08600710301c14096021601d48445427143c12050011280302c82c0a511001d513603e170290401012213005213205001d2610610001945480d665001862201c09030780c0500c3c035446600301a10313180601c01c5100c070507219104c2d0100c20802c2c201c100244808001383c66032014001500a0014201c0c0c81c019a4440d80c0309010b583d8601002e9000916140c21044007507a60f121010400725080d404400165000d901250a80080584c140304032084000f08081c1001004000004081a417052681d0002c030280c607803070000e0140c2c0d07061040c0c602d4000e501c80c90b014041e840000c800c0d19801d290092002080c0780c0800003d00c88408500c41c003080c02c0040150451407a070150320198031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 794811672 1250 794810422 794810437
    0x210110c0d050c03030f0406082202040207062004031109310606031101020d090501140f1908040b101535010f090b06031302031002180f04091502 64
    0x502c0b500d5588030f078680f81440200480c42c060040c4a42e03c5040c1030010303003031130406091021540c400d40c004e40c0207103421404280c0c800358101d40160340c07808a410510060904d9003d58200540c00010345981b5414060040046a01c1011103d400c150f41c1000c04c040c4080498002180001e041680c21000704506800030b40d8110b5060501d081c0342c0c50383c445004941c195002180e4000c00d56a0b0001150780410100800d140540742448007103090800017040d903151210f00000c031034408214910340c9007030303541980c018810590b01c1884428441000824805040d03805480070884c0f600490402d00792075411105403041c4a142405984030540300716030154034908090414000420007003008402103540c10400600344483c1a100d504280702016070611f82d03030141506a00d040d1084050307484d4442500c0e0b0002050104038030b03c11303050002c00d08000507541e1064002d840000c01100c0b09882a041d8403501c070301503c0d000090110031040c4000c0b02e94000c40076215640c8000203404081c810b4004020300c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 794812922 1250 794811672 794811683
    0x1327020c0a060f050403090e06032505060d090b0f04122a0c0f27050903040e0108060f0627040203160b07060e07050d08180a0605070210110c0d 63
    0x101101c1e03490302002c0791296510180c11540740c00900c8145a4405111170182c5410f1030f01c8146410311000099894440365400303480d51066606503504417034900034040091102814080d82c56090210038001040c00c500300311002111000400c410b14842c201e0580304039440010480348004402c016070f0b02001101d01161001d402c6d50704408840b180002102800e803203207210080c100e0400d000c000b904041da40020fa2588502502e140d40d00c200080298803000801c040000d07291981c201540c1584502e41125100d20407104c00000c80840000320184980301e070783c010740b00c5500d90504000241c000710400d490701100e440d2076010200e24440c0303900e401a100804444031002c074504420117100c92940501907400000c00c6ca64207005050050880300d20b00c81000d08245410b100000701c8243c81080c0c0906030700383c00310340882030032154032241500c5007004002100356981c1c0d8400404590006108030b014040490a0072211401511006603000c0351501810141c038880c0240100307000c011805685 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 794814172 1250 794812922 794812933
    0x3e07031a0a020706060e0405011b0f0e060c0d0210050a0903080403050a0c02090a0e06090a020a0e18071401030b0d030806130b1f1d011e02150901021327020c 69
    0x144c601d1081e00002c04040302c070300003076140c0b50419a0845030004403607084802c0b4844035100896020100402d0b9a0050403c015403080c00c0d0045200c0340035980400020b4450903409954698001999071680c00380351000380055030340c014041d020784041728401800b0540c4000400d00080c0610081c04881881c3d2410455101680d000680206825102c2d01015965006216401c14007882035640c803144000c01031001095a074049103024440e8400c0c3c4416540c000c01107160703101c3e009010b800d03002c1c00360b080f120385684400181c94502200c2e01142d0100c0c3c07405e00c1051a605201d40880e005075096259a00c041d5101020300002400386e104240030159919210380c0c45540c0c0210002624920b805040340d4050000340140500b18160031102d40380900950054043e1303030040501103201c0106a0038945200319140592400c42c00c0304d070302040c4807090001c000b091034055004d0400740d1001d900018403d40d448001ea4190700304a00780004000d407464018104c00b801d90010300400025504441c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 794815422 1250 794814172 794814187
    0x60c032703170a29030c0105180d05100608281101030f0209030318040501080313090b01110f06060102100c0c08130b070f050c040e0a020f013e07031a0a02 68
    0x440c8404804a0b40c04e03050143c2e4141c6803c0c2010028480440340c207003006841d1580b1700d00d0b10200c0030340d028407042c81a03100e6040c801c03c005041c84100e660000004040c0803881d2228850390703c400f014a0307000f8805440215200760803500f0307401c8202240d0800d107044600725000d001140508803030200d50704040c0d001c108040071510b081000700401498100b110400031044000c00051b01c1042e1b0040300e1962050001c2440110558884011664040d40014402242c0c00050720800c1c490481c0c0c1d403490155641005540901040452042c0401d0782513610032201a2940c0c411a0500014036000440d410007050010f80300000811018400c0107600b490b03a5600c3d0304032280f0382d1000302c044a220700e0b0b6500d0703d42007000c00c010300b070201e0408440502c18405498441650388400301c1c0081d20038a420000003840741d0041c0380d030404002c20100b000041c5500000861499494000d48100c5041c04064080708542c0c007045032821340758400c01c20700d52401c5140820010640160a006100da400c00074503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 794816672 1250 794815422 794815451
    0x702010c08040506070c0f050a08120d060b0c01091505090a020112020c06091b0337050303090d180e2e060903050f0c2803060c032703170a 61
    0x85c45414450303800c0c2d038699810b01d030107075102c08002c0e40301600403030080c0e10a0000c150007007030b0080f4403642c0c0e110003a1101030015101c40540120b620042d00d80f24005001c028520701074100412003030180c41d04c950007038010300400381202d4007200d4001c02508513070b102a00661240c0454403196040030740250502c0c290040d42420030409845503036940e84032046100300603445503c850090482180508041c11030009a4031301c004603450f01e0440da11440b19030080c2000ca41344041e848982060849480e881c1c40f4041300e58841951f0548404242c04080c280398103481b41d4000c0313040c0c40c0f1a520207070107038407942011021000041c0d20041c9814038048402440c8104081840c02400b8a6a4800000d03103107052071400c000c0c3d41d800c8107071590861440e11490340c441c0c1107481d940b507044582e1200340310b03464507202003540243d800080006003024400007856526401c00d66086481c14025419055008001c0030070004402c001008218012003000f1001c5080303900603484000d014004c02c2c1003450b580c90 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 794817922 1250 794816672 794816677
    0x219080d2d080f01150909020a02190602031905040203030702090603070e0c12160207031212020301120b0601021902041a12010501081603080409050c090a1401031803050702010c08040506 82
    0x14030000b0300580e0070404412010f0b50350314010081e5004141e02c0e994a100000c003642114080e1410803500003071030111151081080b0082403210805040c2007141d5854000080d50060344d0840c4007100c00203480c0d80840149c03184c14042c0754001c004601e048a107a0078060140700050220b68140140040020070750001c00c240b034491004200301a9a41220381018945410040c101000c07544540d4111030107a0303000180c09055a401800c41520130014990031141403005482c0e005445002200004215070f10001c1a45114454501070000b903890a00490b0f0340c4444000900c100d11f0740c402e544000d4102a40700c918210040388000e01c64034602008140d024541002c0020305030364030b00040110801c00c4c40b0b951503412001c150103604500c0d54403480410b01550107401d02d00c60392400803421201c9654200d071001e002c00b0300031380302240d5214080c002c040c01400c0745602080c240022072a8141005100c640085e516131101e5003801a9900116141000b16504440d0550100400315080c1d40d004d01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 794819172 1250 794817922 794818007
    0x153f1302190303050c0114071b02030f011a030c100c2907020a02011101050615310306050601020313030f2d0302160806010324020706090219080d 64
    0xc9482d9505c140720201130845842c0303039004601c0c0300f41000740144507a00038107a80c1e40031038581c1c0d410350005181c0002428100e080048000ba503107080030b449100454034901a007500812010b69809040c00010701003498501a12680094620070010300040c8422040b150204288854542c0e0070040010f1108446c0d029507062001d0307800614290115a480301c5000b0400b29420000c0c4050b04154001c2103000380b40c0c10305219040c5010880c0c50301d250300394240c80c003031a44413803c002d9086503803105500070b02168002501c02c0d80c18100010140d5000100b11084076000c00d41c9964080d280d03468580ba10303010600c1c121510038001c6d4003103043c0c8000031148120400d003291600d10a9142d803801901d03001580e0220f000864400d5410002907a000c510f250449410281c419030108018070520b1014a0070301d814034100c0c1c0702050300301c140010303913100d0044544207581c02e0071440a0034540d045945103c2c0b0a1150962110301c090501501c210440c1a140e034000c01004010503070196049660621001f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 794820422 1250 794819172 794819177
    0x2011404150b030c0f060c0c090424150902070609020a0e0108160e060d170a050a030b1212090a050d06020a0e060f070b0402153f1302190303 62
    0x4116400e500c1c06114030b003030300703501100188010050440403a8400000c0303420188244004200c0b1040d000c410301c010f03401a04000d0849a051134185007800341480349007940c16a400c002c0c03100a5240020303208010002041d010070002a40c40d0004503c00f030761140400311002c5071100c00c11401600e9507402c8402408504160b0001c9605164400b071401407220030b80c903c0580b07400c2c0c0412015445040c1c50f90044015100f03c000910303142003009100d40d440a14080400c0000b9864403800c0d40900a4500c10301d45a0f4107101141144003048003402021590340e5064001d15407207000000b84038001d0000c0d40d8040c0100b0122543c40b00003442003c0c2e612010759600303800080128030250310603040290008101c0300141080809441c602d030302e02503000e006205507480c00124066656984250300c916105030f598a5407550298031500e0550b00c4246083c844240841c0c404030400704105116100d4445980c1c600c03c540d6032010031070f0541c08001400e98108030b91b51126516847c07800020b0010f14041d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 794821672 1250 794820422 794820443
    0x402090a060e0f060111071206020c03070b0a0902030d03091e240b130207261c14100b0f1b01020f0a0216050f0603060f1f020c040203090705090702011404 68
    0x10006d454500658640742a0f0f4100000520040040042411446400400051301c402003070f51014607601c140036003e06080070310002c11a0402c00c1e030700031b400028400d505844440d00400000c2e0305442c446400140040d400000c034990260701209800c1a40c7d0007100c0d00f481804c20401416007940802034080312294a0301030100850401f10f1103200c59568050381140780c007101d5200d080e200b00070340510354a0030700340c4200b00e81030011410a03030300c2c2d51904886420740c02c0e0941204000a10340b441c401c00c0444c03040350000b000c10080030301250803104c03003030300d85842c1c42200242e44200754421039503864900440c41814015130400d102a0845030382144409556510380b420180c6480d07a000202203590201c40414009a1600712103800f620a00f03850070780d1a074a8600010701d11400c100d403442e800c501084480d00340001d0000a94404e105039400f07880c0703202c2c041c100f40030a0344401c46184816a000d040d041241c2e050080006620084c03501c000903030808a02c1c1401e0101600743d82c01d9918a811 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 794822922 1250 794821672 794821681
    0xf09060e13080a27050405010803090907050c030903030a091701090503090d061401080303040309150f032f3001060f05040801110901082505090105070c0b0c0c06030106080402090a060e0f 82
    0x38030442d400340ca52270340218104942000060074960303000340b015042010105140040c040d04000b03840094800806a0342c68910100004010780d400d44145c03020b4250249a1507410070041c42004019600710016528281e0040c051200300103600301700322113141d40d44125210200341c0280c0f0a01070011600650f42e42c0c10603082c000c0c4140c6c040e800408041c2c0382c2c1d003070000c5001d03003140d18090319186c20f040c0032400e010498030340d01d0b030070740c100e40329141d412500f04001d0811070115000780070280031580300e08070480d03004044440f2010300f003102d03204050b900001400341038090100304401c81601d00e0900d2400e52280303c110300b500d0f031468508140850100e041c444660700501c980d03501c4a03030595002d82d00062000c100c3c80070740400d112a014410b001030f54000e0b0340d22802c2120665500700c1c9501410030f40d5040d0000302c9521980c1e200c00c90340204140c46030107181200440341258804d54884807581c030345408200107640054109052995100c00001c0c41c2080b9a810314455640e03810030400c1442c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 794824172 1250 794822922 794822929
    0x10e0c010315080c04050703060e0709090c14090603060f0d0c0320032e020a050408060f16030509031b150609010f18060801060f09060e13080a2705 65
    0x10b1042d846802c01c1c1084105200c000c0001503d00310002040b90040380390b0b140c0c2070003607004200c250089403180e91503000b00180380ba0059010400c50b10103000c1042100c550b000200c1d00c0c0c4101c16401c0410500410801280d481c00002440d006500280755217249000007000030071003104120121460585800304000380712400e0b002060101204844400711440345001a0316010440e4500e10001d1000030b10103640f00d8803d07400503061070a004115542c880558001d44150403620410750184940c200050019014020b554055041c81081c1160814401426005006d0003042400a07104c14041002c00c54100c0d0b000c0b100340b140c21340281c00c4540100d0440b010b90b0343c0c001d0840d80103608240040001040d081641c40840d004040c009080071601c2c00e41c44082c0040307a003c1c038950b42c00e001e00800c04841c255200b904441580c0410401e840c0c2d64120600005012243c003006014210b513890041032803840113005661040c81d1800d00c014041100843e100051003030820a404407102c103010906 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 794825422 1250 794824172 794824181
    0x309020f0301290612070305090114010603060f08030408120a03180c0315050c220803040e0118060803030412030213080d110714100c0c080c130e0a170c010e0c0103 72
    0x83c070a43d8558a000c1480e040c5491400024104000b0140ea800008d01248000c0d8131803420131542c4620108039580d9024010094901c900030303a40070400c0301c0c10004e4014000070840d000c070303182c660103417912001c0250008499000b0380c200c68241900c40c030303106800603140c0d5020b00c0403070b226841d0011224118200b1052a800351000029141d180c0000e001100a1000c1a50030235500034919240a803038004105001ca0410361204032681720110700498994013030304500f4140ca42c0101c800410200d441d01c100d0584403244141038030742c0c004001060200c6c1c00e4000740708400c50541405480c14a0040700b07151785140c1580510803580002405180955111994842d6100c10f0030042c002c150400c000c0c01d0303800201d1066544228518008000024040d503044151190007188141c20285c1c3c82c950982c551000b040401c1c403a8554141400400965124112800103d03070010030b0905466030754030600c60000c51144002403010300030014065400d0007400c20a540260240122520081c005402e46 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 794826672 1250 794825422 794825501
    0x5100c02011a240a090503100e0607050703080403120209130506032104090c020c060c0106050a050607030f120f060305150c07030c03050304030323060117010f05010309020f0301 78
    0x151041c041e44184014140310410f03250200700300c0310307035138201c90b90083c0d4600d0000e50010b6010702400d00d4100207911203611500d2090700340000da484a9440b00411903007841785501c010082082603000c81c010920035001055a4420340000501e80780718800003614a20542202070900d0b61940108805418140300c1000841c1d110844a50403240301020111180594010780381510713501c1c0081010b56100300900307410090080d00c1c19903200030700000355001e400e09000b001d0081c00c0e91000040c881c10718504542d030007509561510381c9014149022168072121550b001c072900e80700d1020000484075445a00000e500c83c40c018041d0701c00c402e90381038241e00c008140c101036030404e21a05003c83d8004400c0300c007542d41850807540d03960ba6031070160300500d140030a004480788116440c0071030400c4942c1c464010740098a40080e07200d6602035401075100e00340a242406102000c04002c2c0d5400b0780c100c00e42003403004080300326414200e03000c80d0854010300700803010300d031042100302c50341c1e40c080c8111242c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 794827922 1250 794826672 794826679
    0x91801060e072705040e030a02070e16030c141306121407080c0706050412120b0f2101020c030307090906060221120f09070807030c0e0405100c02011a 66
    0x341c0c03600b244007a00e4460705803843c00b801c01030a2810580802c250003a100549401842008a80e0914501c40d41d070350442c080c0480036114502c1c02060b14031500d42510f22802e0342c00039450745010b51202c100d01404218100d202482003948c180313680341d080342000d071050300c00103d00c50f1111031905000419402c003261010705034030300e00010840c08a000e01e800e07541c00301c0c29040401d50b6441d0a4100f1541748a050304c00340c0100d142c4800d04c8200840300d4590448000b582d56800605694041c03410211145400e40640c8130b40013028a02260800c0b01c20f80c0d14117251010f42403020b40c04500142d0a80e480000101c00d02e410000400041541014920001d800110000c210090400c400a5071341c1c10441581442220300361103910380200d8481c1243d5410002120f1270110307081885c501c3d0f04030f15040c0c841c07400900509030301254802c0300080580841750085a07a10701e80b464008030344200f48025000fa01d050080a0b104c1c40c10041d00e002e0300142c10003590001504410f6942c00032060001607a4080c071 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 794829172 1250 794827922 794827949
    0x5030d0c1b03050f070f030207050114090310110d1401080607020a0b0f13080a0c0b0105030f1c0e0a1202040f020306030c040c024303020607030f030b09180106 70
    0x44160701198080a00d55040c10029500c0c1508a290181c900400030010a080c503d0720500f010164045518412138030b080c1c1b12a60840c04c0d902c00181503000303110080384c060744444400c58921010390031101140239010840361410200805103000d41d8842c20801a1004800d001000316450400c4400e501990910103450030130465515035400048c090720103260f94100c0000b0410381e03454000b000582c0c0303501040e06035a0314803141000c2c041200529080e112903840310f000182d14103011880b0810010080c0250104111108a10b01078a049540d4002000110f81c03e00441d900c803201c0190140042c8103c40860481c107104000a40c0c110100c0460300500520500c40544c0780000c0000461408a401140c1d400400d00c0882c580135a083d001e446004008030108607604d04140086003c140f0781e50646060040c0d400090201c180c07500c4029005501084200c010074030440ca0041d241031f113440c001c039501c2c0f011f000080300306609961203015800c0f00310303105182281c2449580d00502025408030f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 794830422 1250 794829172 794829197
    0xd0906051e04050d03050402010504091a0102070602070f03080d020906040e040b060301020a080f041a1501030614180405030c062d01050306010b1b0304090b032512030e040905030d0c 80
    0x191101d1101c44ea6005060b26403003c1001c6a000398143c0d006800e40c414200507441443d070b6007145490541d02c401d4052b018a800201e000c9102290303010541d00284640360704545140e50f0710a19600c03180c51658069401d1210301d410b5030303500300108000c00c0001c03041d060300c0c1482e0900443c03116010b03203018440e03072040050709172464200300900e91080c603076440c108241d80c503800c29468001202042c1140c1003c520100f12044c529030702c0d1481e0348030083e84c042003035a0321441240180c96101d880103500000003c019800114940c0c28164003d03c2070003981d0a003482d03116402e28042044d80d40c2905140c26415a2076014441410b05068640c60102d00c1810f51508000c00e856250602030410304046c00240d410340252584401d0700800541d104036961141d0700d00d107002c01401034280f0a07200740101d150320145400b070702c180d02e07920102819001c45518074182054200804001c42102440301c100b01e02112507a8901c02c14600b01c1c0140d014555640c05400b402007150811500381040c001c448c480d0a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 794831672 1250 794830422 794830433
    0x105071d0d0f02040f09050619110313020a08010c08011a0a122f03010906080607120b181005090903070f080c0a02100201020703090902030c1e0d0906051e04 69
    0x55560742c0040042001c402c1c01c1c000314002d00380e580c42d2050b606080c00170b80c60802600003880d5204011000c0303058003108440c0072240070b81e400c03c025400248410b001040c00e18040c24420651684001c0082d02d09c02c0e60b844a090030340f4880b0748070b039002c91101c5004010041c1d0f901003c0181e0800303203410500d4507000079006003040c40d9420150485c250f5412150302c541c500788100c0007903000403031802001a010740d181120540c0c001d0003036a031181c5c100000021034080c0040c0d10b40c012009501e079241101c03220480c84005010080003d80e00100c40f1000ea0740000d00c01002a024660030710300d10003803c1c00d25045c000c00d44070141110015600400154000c01d14030041440c1141c1c1c0b00644c25601e4021540c01841d00519803006503102e0b980c9040c900419405500501c01a4030980b1074901103070f500d9003050224041265100c041174004c112000590348595035040001c003010491a08100c009013110040300d81b00b00d000c07101e080c4d40380103111000305d800100c0c0c02a078400f4206107150b444c00d035481 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 794832922 1250 794831672 794831689
    0xc02160e070c150e0705040f0507020a080a2109030e06041203080a06150206090c0109060903020613092d05010f0b03040809090a06090c3207020a03050105071d 70
    0x510204002c2c15814000c10081c00818221482048014003084512048458840c090b62065904c10740c03404000920000f41802420700c142807980123010b2814031750b1501c00c5280c0c002c405d060204844503001da0115409030007a804001c1d100900010741c9906450041c107a640e41d50141841108240300800c03440d8240b00981c90319a40c1440d02d513003503441d07029030300010f8901074010b94400c1442c1d901c131409050703002803560310465070707507088507140c00d446001504c1c000514041c80001032030400081c40503040c20001411405010040340403881d94400c0340404550075110899800b01d5044500c01c08101c146260903420280824104165450410400400c807450f01c00c500c0201d0f000700004083c0107a01c41580c00c0040084d14030f1035146061042c80b00244014002c00b0703006e515008031202203511402c41d144a6003034007a4131070800088200ca404800403c0d0202107810941005500c0050b250609003200451044001040f2810003040c090500200a5481100c0d035441200c005c020f039440644 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 794834172 1250 794832922 794832931
    0xb3d0f022109010c020d0203060a090b0a0e06060f2d100e0d12050f21010611100e01060329090a030912031407050607080c0702032a030703060c02160e 66
    0xe01005802e13a40c0301203050b0403000d540196144c01481c0820400c0c0030580c1003006501c0c42900040c0003a80d032079810108a030410342c622011584981c0016510307050000d05414070450040121214042940182c500259190544c10340d5079481240c5110f50305100b0300b60a0a2a054208000c0b540c1c050800320f84c15552540002d04201901310b00000060302070030071602c80a2001004944d1840752081c207050008109814144642d007000002030140c1c8140b108490520b0104d024060440d404400c1c034014048040700c0d03200035540c030b101c00400511f00c9049048510b01c1c1d0043e400e0b0030b20801c4010171004a000700400002c0c1c210604100c0003e0f44602460700380c42c07400c90410340c418030600b811904203104042100015074002004002e001c03000491600c40c00042e41d0b1041150f840c1800741c0058040c0f031070025050341c030004a4404119580b1581d00322800b0b282c8488418606941c0001c1c42c0140ea035006681d00d0780c2d80c0820903c0c29905002800c1503044214110a4a900c1c02c010800c1c007810040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 794835422 1250 794834172 794834177
    0x60905040f0233030c0705030a050a020d1b0b0402043314010221041203050702120d051b0f01140702070b19030c030b060c010b0f040b3d0f02210901 65
    0xe2821074004003a28002c40d0800701b02d075141d0350f004001610741cbd4011001100503208901400c80c0c00d500c5140c02020051030030210b44c4450260f680d13019031144018108070703406a200e91214840408000400700c58078603902c2055101c07803005034041c0c10020702c0e42105103082030610091525903000540070041c3c40c960644254085000c3c1c214400600568020005418031b01c581d0a00b41940100909007250007111400c0d11941240e03002c03541c4503c810b00490110b5001d00000c000005070000e80c120031140441030311420710b14018014216440d0051780b003081f604940a2000c4954100710b040003070403040701010302c0c0c20082030709600340e10700b42c1d96200d0400d0f89515040c02900d209030003800615001508141d00c5400b15804540a021000c1c001801003d8010000c0300300d2503d4024080c0c0d10402611111954941c1c100590040100d1580c0054080d40b154244000c1c0144440103103a895140e130310520039245581e0000e04280c3c916010040d114229696030740c1c1005d510048035040b20090 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 794836672 1250 794835422 794835427
    0xc09060105070f06140402010215010f060f090801020706020c0613031e020f0a060e010f05060a09020f040e0123032d0703053a0806040906060905040f0233 68
    0x245001c0e05401c480d54001420303941441030580305580e0318945c840c00365100341c00380c80f203c1d030344009241210b407000d12403031034821050001003241902440490542081500c1c260700c80c175449049890a9a1201100311910740d40095039900b04c0c42e040c0401b58205a880d074a0680b0b00c4070940300249000304840b124041c0128080291450340c3c003c21060035112203030f00940c1c0c40020b0606101c0000e100308502c03800103500b40003041918801c10312456104860040081c400340c3d00f0254104000d4110100c1101d20034400c0201140301300158002e10300071300c003908100c2030000218860500d2451a08192802070303000d403031403100a292800d00381100306580d60454504198a0340b85034600011684081c0541c090b006506006200c0345000f40d00095000c821444040070b400c8519542c0300319030019400048003440410154075041e0491926140100c401248441e110341658007110703800e881c01c45000300294810421070401c1c551031985030b5101c050184011402007010411028625281403810000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 794837922 1250 794836672 794836687
    0x13150c2a0305010c110f150f0709052d04021c09021302070305091908030304150227040c1b0f06020c06040b01030c080102040b1c060e270c09060105 65
    0x11156910001c40c0c0180003807101c01c6a010014200c3c460702041d0361224041c4d8441640f8010000034000072003080b41c40030004a40e980c208001c2d8604000d44000d040160b00140000c0b2a616100100c0c07560390401c54115420041c549100c1b00d14402800e19400b460041c4600b040340088403c03c1400341040803c0072034851347d28070004500703800107200c810000b8404100c0c1e2003030580c45005451040010317203585600914245005010140030b1103400c81720352003080000c0018a00010300ca411100028016003000c0700c050f006402613003403c1102640d6001407440b0301031071802d40504505500241048800c0a080481041c500341b40190080c103940c40c0b07200340d082040000d6040355000c1c080c02040e0380150410b440c1c010b41c281c0c1c0a104c2910107603001403020660740b0041c42102c0c1202c4208503882c2c604101400030301c1e02c10009406440e4a144ea50900080620300e0f00003c51107580305282421580d042480e051442148007003000405a1120600d4942030712070840ca2a00154242030168640e4403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 794839172 1250 794837922 794837993
    0x60206011a09040f0c0504050324131407030b07271401091a13170a110f0306090c0307120c0509130503040b0a2a141213150c 55
    0x81d4213000c1d42c064035014030807501d680d010002c0c205550080381502c18603102d01842d81016440d03000286004500d503008520030490704600c5010581c41000744100302241c0034007580c18000194001e82da51009a000c0181d0315a0005a50f06403c01880344ca2207580b282407150501c018082c018030755084e490fa000c0030160b82c01000c0c81e0300204407941b0b11210206402e5421105a000186d4640c02509081404150001044011181410f03080f00800b000d260301d485a84c50998002036858011102210001c0036845c1031110a100b50740d00c900070b005c400041c80c01d143c0b6292907907105400d001c0c070540d81c5600080f5450a610b040310b204440b134004a48640040944070140c82c9070003803051000040004105075800c000d03007404500c40d22550712100c3c1d8000305881a65030482d2403800704801c0f180d4900000d9481460300d8a03443c040003203800c50040941800901da224180e0205000c0c4141c07400c00010038485007105285c01d491404854643d402d5840c149158050815081d42d080c03100c1d0101c0c0b000c01e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 794840422 1250 794839172 794839181
    0x10206100510054612020912010e15092b05090d030206091e150c1306020105010302030d09150806042003040c0f0b09060c07031b0f060206011a0904 65
    0x1404804c480d561001c0e40c00d051011848403d00119180480d10030811120114580303a181c0f0750740358444116003455200010700950000b00015840100f03203056080c42c103424851050310362204002030944040501241d080801c0c01401c00d07003a07503c40c020000007007079440044068150030a40071041b54202c20b4080e2064040c031030a03a07800c103181031241828540d0001d80c0901a50416099646000d00d603019220499507811049203a43e004080f9040122030068001da072080125200b5820f01c80c614000c41c48a0400b60301100c010303074440e001401546001e000380803014030305040004a2507d400440c04001c00e1682800e0180580d8400050043c1c9071900702001507220701886000911a101d00300070b0079081070b00e041d580da212440d000700301655000b03040d5058949400409040410020420030580c1c0064100107103400342020000018602e02d030410042c0c07a10000046c1e8050401000c0100100141d00103000c40d84104010019111244002c0c2c15800201007a290782c0c0c10303640040707000350 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 794841672 1250 794840422 794840437
    0x618050a09080f370c0c031b0801060e060108012c070518120606040f1103010b190e1f052106030c01171f0902030a05041101020610051005 61
    0xc800010308035038640e108401400784131401403d0307030100d070044094000c11002c5a02c85000c100c05120001250500035640001d04038442c00403100819101d54981c400da40300c003450400c4c41c0100300ba0a0010303c0080c040c100103018007191030042c901d07104000030001d04041c80b401c0c5200c0ca00c80b0000c1501000d2251070025200342c180800d1150819050003005035001901d404010759800315491400c0c030f0060000c001c80301c1030100400b8241c80f06010480100000085500c40700c0c0d440700e08050300c002c04d0020754001c000f4460002c1e10f0b403146003031480750500000380c100100080d0081141c07540d40e900942c40500345800c2601415140b514609944600c00c2d078510290841890007280910a82d0100c818491181036003510704d80003c3c83c005550341c1c2c0581c0031880f280a12200003900202c04502d455840c000d0f40c40c4800202507a602200040780e200340ca400d44140c0d160410c1000b4001381d980b03006640720003032004003c10719064483d075440f000c00d8002c1c0c0d8460048103000d0f6250341d00c100c043d00d130344 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 794842922 1250 794841672 794841683
    0x910210221073501060e030a060e03040815040c050d0503040b07240b1c0302150403090506030c07020103110403331503050f030a02060a020a02011506170108010618050a09 75
    0x81548407004864411a102c3c0c003015411500001155441c820079000d04002805030060181682e0703580d514010340795403400e5100c64072050000140080080008138180102d40840c90081c1c205802d10300680314082c1c104c1d82c002c8c50081030700300c00140008200c40c101c0d42a541813903251021031515000c0000042880441013104c0305641d072441c3c00aa01441c4482ca04440a07500364840801018041064074ae000c5c3c00b58015268642c010040c1c200300c80d034094400d1400d0700740180c0710400611581c0068070121a101d001085200443d41c0620840820740c1c48044114105455683e07014160040082c17031224402000c044100702c405452034500440403030701018498201c28580741c00c01368299210946552140610701c200c1c542010049444000f659800b070001695041c8205003c2d60011080404641da918013501604840c28000d002510f0301e90703500c0300301e0b10084880744070000341a0007140300c0382d2500c80308100d03002c40100710361040c2c4000c05012030540c0c3e550080c0e2004020740c403c090301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 794844172 1250 794842922 794842967
    0x21009060e0d0e03030909180607110d0507020a030818060a0e0114090904081b030d020d0b0103060e1b0d0507020d110c13020f091021022107 62
    0x41181640008802801075412103846604560045806242103040315030103400c100050425800d0400115500c122822282c24085040c0074210f45006000c46040303000540550106424000a01c002d41403080c0070718102d4100b0340503800051200c41148001410b1010001c1c41d03040021002c5184205594003c040b9038a40c400389a0140c411051301d413644d030006030000301e288003070040310042d10013820300903100714110307511030391400300540c449680d510031004004140b18000c070707042004100e00c200c0707607801507181c1000803054000d88480403075082c18142452824420950120a032582c0604d05032030303840c1440500e00d03d900c610312501444d201c946050900b0003501381e40004100c2d401100ea40e94140c600c0314921490358803418160390031540115100c41140c003030484c3c1e03005030142d61502140c0354601048003000410403500d2080060100700c29040d2540d4104142d00c200c2460120000c0561401d00c48600c1060583d1080843c40000140080820800c6104513030810011403140d0030101c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 794845422 1250 794844172 794844191
    0x50f12181c090b0403050c09220c030c0608090606060d0914010212010803030c0d090201090e13140c0306060d0302010612030302040509070f0c0f140712050105010503060c18010210 79
    0x100e500045030345007020400708070b0b00042c80744079041213078101e0740c014000c1c01105698a0400c0b6460300040d0900494100150306c1e04861041d104c1c1076120b25105d00c0840c043d2074503500d01a801c0c00c01c90741c40322060110a00c2000840d80c408200240d01c660304940c5c280d942c2801803424002803c08000240c200c0011074840c20040c1380550050642c0d6009902002c1c03582c0e41c03800b03016901d103c115082c940c640400d01c000820b0500d0740e0031031000c551050500081c83c0d43c031488400b41200f0101c0b0500000b41c06280085d0501032a1403141052441000241c8000c821a0020030380e01c00d005000d01d4011402d1400784814503100398010000751840c1c09005c001d112050600401a41003400f40610aa410b5004694454081d950b405510b0703104d07440310203440300c1c1521650404c0d003443c035083e50182141c00d005001264240148805061907200c640007003841800d009084030416001640241c0c426014813100111030400e0b24480b00c803041c0c0b0804004110360040b1304000700030300600d00260510070a00d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 794846672 1250 794845422 794845453
    0xf0e0318130204080c0922030e0112020c06070e090702070515070c0b0c0709180311010e01020301090c0206013303060909030e0907020a031b0804080a0303060302010f050f1218 77
    0x30001d10300c0072034009440e9180d1502c03040c601c25174000c150b00d5070601e00e03401100290040e0243c00e09c0322014103184c0d452030541c0b0300c81810399022000c44ea4141d0800000c002100350000d500b851100d40c142c07000c145615040300007a64030511402401d210300400c220030010b40c01c0c00411600142d60201039840b41c2c0e95910300c1c0c1c600f40d0304140342d801c1e9540102407011851381854425030440624600906004d20320f940c4080c0c40911207001800003654984800d2081440c00b400194002c1800020010b250304418600a052942c10713040b07541d1020701d04182041d402d000c82a00d4015000300010300c0c1c101d000c00e030000d50007440d45070b0000c0e8050303050500140a050700660106182081911541100c0d565108200c1e20b4022010000340401c4c0d4601c405000000c085200d2a8203d100340c80b413a00d01038881d0710b280e1401e107000c1d4003180001d071540f02c180300310f5034440e040c240c40105506040d4100320811031051400d00468003050360303030a20480090301510a4030038140714190610180c41c03c242d42d2113a0b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 794847922 1250 794846672 794846683
    0xf0b010806160e0108060d0c030b0a15050d03030b03100c0906080f101a130e0a14070806062a0607030b19090903021f0507030f0e031813020408 63
    0x900d9114051000000d0b000312a0340404005111640e803081000e403140c000540c3c00c0840901481d4028041c0c059510000d0400ca02d000041c501030720305901d0b24a40b5075071400650395281582d0310b425402c1030b010441078907007250000c9106d0703041c01d011915504c0d48001c6845e00213142c25800304582004170075064036412010300310640b401a82c03101055034414031243d41101095400c001c41008a01c4100f007009845658200991410f18841d850140100c9486407400541d801a11070003440034140020490f0324400c1c0c0146091042c4541081e207030401d006001d160300200101d01480002a43d050b1941d9668100c203200401084000b0032400115140d03503230b60300b08481080c0401d20f0010349403004d240191125201d444c0113032444030101d050500c090702501e0000c0085003544102c50f290040850202500e01104505d00e00008480c9400080101543c881a8082c00c03101d1404139084147e03100801120004a41c204c503540c0c210340c840e070100307440303949011310004014800320300410901e402056 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 794849172 1250 794847922 794847929
    0x301121b090c030b010903030219031e05030a0e06060d0303020d09060f1d0f10090516060203130f030b060d41031303140703120f021b03030d11070f0b01 67
    0x3030400c054001e01300192040c82e00c0e1b0001a0260b8807105200350b401c030040c988801b0305d81c460714001010442140130120014842c1742c52401060001c02001b5159520f8422400e049460000804882c2042e07170104a480444000140c109030b00000c0c50411542c80da042070450ba03510030710400195045841e807000419100b82594440403c180081060703c10004812501c014810301404580c2d0707441440c0c8004000c0e088040310a80140c0d054900d03081441e4107104010310281d0040d564410594000c409000303040d42180680b81d600c94820b102044140d00c1c016480321007568840c46958150070320030078402c5900100701c01070450016655031080d2203101201112142d003003a40b02107110a02e45900e0780501010004260340828003040803c40341c80c50f5440c00700b01d40003665261610383d03e5a00481c2c144481d00000300781940801510030b030341000440409009001e1504910035941c0000c1d44074400d14907444590f0392113003950b0004202c944c1c101d42904d40e1008080205080070b10301100e0b603801c24070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 794850422 1250 794849172 794849177
    0x40209060409050705040f0b0a030309080610060c1e0c0f050f01030902030c10110d18090216030509030c1f11030f0a2105150a09020403080301121b090c 67
    0x2004144141014010010500c0d4002c000d003c40909000174807009203080501c8690301e984034101d210240d141c17482c20402950096030f42e00c1e01a0706160340b0031b00e82480074001d04181c941142003040096480611180140d07442030100d29241c05482010640c00310485c1e02070040d028090000400c180c143c5100030498006a6410500d41040c1c8010750440c2c21140000c1e41540003910181c03031524059540c0e0420459a00740f000140c6100002c3d80d00d040d24ad803480a010078046d02c00d00e903c4140f1103905900801d504e2005615201d4807408214600740c480200509012001c03540c4585560706102c107060600002c1c11050b02c01408650550303401501a040d82c010444020320005460408802c44000c003142c0e540d003c0ca8000e078801308550290252040348001a4010f92052460301a4018140503000480b82c084182c10070300d003005a824607944c00405001d204020410008017558141d03070450300380c020005030008450400070644454031615500c5400c81000114034808103071320468a451a03903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 794851672 1250 794850422 794850439
    0xf051c06150314210309120c28050d030507090b160b1f031203110a021606020610090f0e030f040602070e040c1511101a04060605042d09050402 63
    0x3c1c0e40d03140c1010301d183c4408213601ea4010b06407046440020740e000740400003103c1c1e070b1143c561503400c80342d0812462600250415070303d010910f188114000c00036000d0944a02e00b15080707a581036565404102c0200c01e140d111000102e07224011440b0710300510950b40c060740c1e505402d2404004601c40700c0c1040360541441d00c08101641c0c8044407440f180300000d0000a0554216202c00039003a0b138041c008010142c0741d4640700c507143e10030700190040e2401500140007000031201804180000c03904560110b5004100704006103d600003804100d4140c5400007602100003500781e0f01a1800691568162000280721152051035400600c111040c543c2540c8070b02e5215110312100d488107440103070a40002010500c155003031004410100760075410300b0012030707900002260514102c0c0480e40841d42c3e84e8420100103c0c406040c440c840d4a00f00c42c1040103e040440c00750681c021030003a00035500a003042201e40c0c61090000781c005880b00c441d000c1c05035603100104405013904a078101e004101c0e6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 794852922 1250 794851672 794851703
    0x1203090e011811090609060d110a030b1f0f0c0303180311070b0408030703050c030706050903030a0605030f030403030e060c07180c11060f060612091b01090f051c061503 74
    0x39402607501d18103005045d03901d0000c0761803c21146401041505e01e4265455560300300c58083c07200200100e904035100801c1c00400781041101c20700e141d10345810000549600010000c0e03002e01484085032300c5060481030100e581c20120004c1050300c3e001d1050b070340031421400916421035180503440c520307d01103804081d140d24400c00f00b4040c0b4821400d00d98024840500064040e0000e460048240e0044900b44010394031944261203054412100f20f80001081c046000201d0203440080d0200380c00a000700600a400b41d6500d20440c440074003001a200e10741000f540c1d4200807100c001d58083d0448000d41d403150314140401c0b0b44003401441161074091171f010324600031204403c0091070704c3c3c090305003642c80100310751300000f00034021a4051000c2188071100501801d20070f000c0c1c1c020000804072941c804030f98145415941d49083d060182d80c0c4010841200c41e4460b075400d44005464001d540d00c0d41070007a0040910003040100200d05000c0d68052070610003902004482c025460030054060 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 794854172 1250 794852922 794852951
    0x9020903010501060903030503010302041122030209060105120a05060f1503060f012607091805090d030506130b06070b1f090c120504050c100807120b06041203090e0118 74
    0x182c5d4400140451818401040907152582c0403243c60094445031501d00420500310940c10880c1c500030403451000b204c4107109508100c90301d0b039808802030070040c1c54845d180d000401b9441008011041c0d461301c8000164040d29140b40710342007a00c01814002a50003540381d44045078008480e03060040105064000c483c1d8420500c0380301001d8100c1411000c5e00e00484914a901001403242c010300c40d041030009200d10341185640c012a40b4804001800d041a0220300e0a205203c1800c200700740c200014014250380720038401d010300c1180500040d20350a00c4010841c20b014401c400303003441d0100000c0001d4481d0340d400380e9140241a0b410301d0f40003900d60204400b15501664400005004051401d2403640c05500103030b0058001e0088030106010a00042c45c28202c80e000c81c00020a2042030040264102600d42d8980c0031090051000c581400b01044041c001c502c5960040c40c0d082020324107242c000c0e003070fa0004c0d10f0300d01901c00d059a160207200035203003150540700c5445d5150040d80b01d03002c030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 794855422 1250 794854172 794854187
    0x270a05150a0b04140606130806070f09050f0604170a0f501203011511030418021b10020c1e19031e0917150c031803040902090301050106 60
    0x1040f559040b611780ca0750030a02260303411140c904038100c00080d07000305006c101040701c3d91180003140c0d108800080740e00030040c0010f1540d031150b4001d0b5440320750354841d1740d01c94041d01c0946071820300301050b0018054807985843d850074030203005c00714442e401c002882401c1511140e0440b003034038280141a00c58400512429450f0b03404126104658554550400c0701c50000701130396800c904450b1007911072000c102e019802a484075505041c0e900d000325010381c001c40c00b010300c14101d2015604140c5445c04a4103210912a400b41100307600080c419030009404080041c1301400c0c030101d03a0080d03d640840402544405d403c0611b0744a0700450b50b000c0705020b80c0340b100350604000a07040c1c4140c1c2c0714107030401e8810a4421018454030201102c0f01d0303c2010904445040c095881209003071610403c403025051320800e00025420401d5a183c0e00f0303640c02034644d0480c038004411550380d603440d43e001c400c00a50703c0c1c11030541d0100203800540100990040e00b43c8034812402082184d03a00d003010350303054 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 794856672 1250 794855422 794855441
    0x307030b04141308090d0b0f0a0507090605030c0306130e010e100603020f1c2001080705040b0a12060513060e010b070b01120303020d1d0706020105270a05150a0b04 72
    0x100600015000060f136000040c1c00300510107051110314003901e654a480c61582121840540580d803c01c00101516034062143c0140860a04198a5080450007411407200511542e909040040814010b48400210003411740c0c02d5042001540680121180030b885c112510311514810a8103100c40340515110f003508581c0d00804081c460804a020b000700606a420b0348030f42c2410780034440021480252840050042050944071411206000540f0810f006030012042000a0109000c0703681c0d4070b0220b80391103150303041c1515807030108180304002d0001a041540c010784c5441610f41e9040c0e2942220f0b080d1034078905a040b0903a00c1d2020300c110f074040e40001a001da035944e001000f005103012440c048490080c42c01615140359082c1c018155400314007050045106804144280201441054040c0ca1607200902032414a990051038112110500e07586413000581442c003030150400410309440c0d0b120040c0d40a42203c1081c560481204a80b05841ca81c00c0840d908214a0a8071542c3d026 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 794857922 1250 794856672 794856691
    0x308090c060c0a112d0a0504060305150c03040317091e0f190215180603040c050f0a0e070e0d05010f020301180608070b0705010902030708030c1b0a0306110f0307030b0414 75
    0x3405e5210150030300032481668141c1d08224211700102d819251406131801a6000d1030042400e508941e01c5070036003080040c8038100380302045c001d000002e9880512180314140528130300c500d03500c1c0c6800c00c2d400c010b441d1040d03019820030f050710582003800c04a10740c01c80e01c640d1019510700d44440d440108a509586400130b40c440210346c2c40b00c082000c408090309500340c500341800c40ca811344801082d80c551042d141681d1400400104010030301d0100181c20785848203540080e01d075850100d070b02c3c14142000e02130900780043d180600c1800e17160024400302c1c49410000a0241ca1000d08003a80258008e000e203140030b018240c5089074690541c0038820440c1d1220000b8a940340c07030131058041a07001880c0c112065503c81c01c88101694040041c5009420b000010f0340c1d03904e100314091444c01c018404080038030001c109034418651341e41654001203d41080022030010140702d4440060710440010b040709040c08070521644070390580c441c140e00038003a5020081c29000d4050507003910000c035034070842c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 794859172 1250 794857922 794857969
    0x16023d0c02093103030f0617070504021804090c03020307060f2f060708072003040b0f0408070f0608011403031e0d02040e040c120209040308090c060c0a11 68
    0x107980680a2030900f03c009084601c14000d02c650b22181c411002d800d0094000980b201c8421000d0000d0b4403491004110101e9905d00408266201e6606c0d40e5a03449114401d80d40420360104a11460324100320407078005004105001035850800100319160200b40e0003840794682c00305101c1c1c01180100090000740e2980c42050f02c040400c858100b04c00c40303c00409a201045504842c1802c100840c01098191290003480c54007840082000403031074030007111390f800307452000c009140203c01c84c1c082c0c0e619140056039403c1c42850b890400c0c403603580140030f144100da20000701d04100b0500003041da601c81d40e8070754940e40d070b65400300c4022201d0b501d59a45604104111500071200501c8150211030200c06907080c4010501c501003282c0199001c0342004141a0821080180034184030014003038202c070150121007039030049a00e810004000a043c420100c2c0483c880c458100071072443c22030000c1c042a074682841c10101e446a55802c03007141d9030040c82030b8100321440c0800f102010382601084140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 794860422 1250 794859172 794859181
    0x307020616090506030f0603010c09060c0b100f0608040308101a13090c020703061107030f08181f0c0e0f010c0c080604060603031d0616023d0c0209 65
    0x888501d00d200715020700001500001d40c42e290700340518031070351485040d05040d140400605003503030b180300c00c4481000b034064402d002d050f402070307109014150016000b0001c0d9560171a0b11000c2c0a040e00200c0c3d100c80c40b41c10004d804c60380504014070480c800c2d640e0046c00d4a4206680c5e00d02c000c2e90041518015580403032122440c43c02028007503e86220008850302559641c1010072180aa404040144c2000000b801400814040e200c0300c1c0164450640c034107c036584005060344050b400d1b0100308084a008501d9000480303103442a02c03e444070a0f10141c1501c0425107003032000c0f022600303c07101d00b80000080740030300440385108400800340c401c50801d1110340045400d606000f504a681c440d018102080b06003040001903c00c0c0d1040c00009650380c250300707015000d28030081d520101105103499114680e01c81c034003902c8031200506450303452110f80348000340b000b6201c52455045c0d4104d1001c0191034802514200d6480d030a40101044003030300301c0604039202e2290b80d801a4203c2040342c040b5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 794861672 1250 794860422 794860441
    0x1404050d0f0503072f15090d080c010606030c090b033c010312180b1c060312120b010306050f090703091a0412090617040606090e10050105010503070206 67
    0x41442d20401c02e603403905900b40e40700040f12000001508070341c8003c050003403002d20250700c0c0020343e0508903203e01605078a013240190038416890b5680c0500440350000781008070800940d0300c651045002803010588074080140200b030703000303000000a12071100c005400b03044403040f6405400441c1030750001c8000044188661009400c4030403000e080707607041c20b80501e800c0042a005c1c44c421b1405040c800700000c0010241c49110348150010000325100700040181c4d242103075802c42c0d10b440641c22544074003403500c00600b26940094105a4480000120341e503008080d0351606480d02e204110402080340110100c9a03240a04d9030052485a0f070b0351514600010840d911940c3d0303180100c0c24412582d200f00e024425400c425468050742c9052104000102c52640f2440003180390010400c2d21f005401803499001c0101640081881d02c041000c4c0401c680000300901101c4100303114140041c10a5940c80d402810404096440c00c400071855610179070489001e002181d00500c0c0076117429246 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 794862922 1250 794861672 794861693
    0x90a060c12140408030d0603120314070e0307030602161502040f09020702120a03050d06080c01080a020307300e0111040b0310050d0c09150303120e0f0109121404050d 73
    0x100b07081c64014030000803864403c000824080d003d280c00441c0c000d26529002001c081d0740c40a280500d4100307440c6000c42c1c4110010240d101070903180c901304001f10040460b090040c01e810142c25140002600c902c17011013903150040062140304200c105180001409007240200d002d1031f840c030104940100005121500134000136400200b94003503503400743c0b420714036105142d50110081070011802281210706482414000c011105c0940301c45210f5800007099086d0003400d0405150380440400c0b02d02d0310500002680c0d04000e2850031455800c80420110400740c9190311442a0402d180c0e124801810300817000d00101086c2d6460501e41032038804400d54100410342080e0000d0362000241e140d071000316401c0110701402c800c0d000241003926002c10346001002c1d008115546400400000f42c1c000300d41201c3c5440da4000260f2140314048950070110b68408960096080c121034009100360054071010b100d0a54442c0152078440300003500d8240954440c80b80c1c00148440c8600104980c01c44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 794864172 1250 794862922 794862947
    0xc1c02180306180d050a02030c0304030302061909050303070c061506270e070c031b060f110315060d1e0c0e12071a0d0e0604020405150f04150506040308090a060c12 72
    0x1600c9c10f0804003110107240d0b8009900a400580c80402030101105442d0f800707134413007140c04c4002d100110858403205c0d40c900c4081d005a0400104070385040030300105500601d840461400101340090303480a0052903444d400c03501d0419103c00286a0075000181c2e400030084070030f02d400240040d0368600d015200c80c03801c48000d409108824440c41d01505060000344c6040e07105140024603014000b1000e4201c80e40401d0a1900c11000c00c180180d40c0c1d410221071006d08411204a507480282c0180000035044a50403400c140b04235840302e06013030b00d40c1c2d0044500e6640700e6950315405a219800c0100b24111503c4464a0381c2000d072043c880c0f000e90a0310100d804100b00685450804440c0003141220000c440038080c0d03402410a02045103414054250000300c000e100c1c00346501c0d140c0c000750308038a074102c0440c800c40d81c0d482c4e00c2450003421a242d10050170300074089903d982d66070420b0850303030b4040d6036924811074003e20b02081540c0200260800c1e50303004800c2d00303031010000405407100210001d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 794865422 1250 794864172 794864177
    0x3060f0302191a0d18050c0405150d03031e0504030c03030218061903110301140d050a061b08070801180f0f0606021f11030c1c02180306180d050a 64
    0x482c0032661089403e0301404212140382030750b58404451814030102d4655035052143c00740880090f034081900000c1c00d00c0398801c11940000e450300d40c950b00700100442c4080311034000b5200000441850707015030140034000b4403003890103400110762034a81c04640301100c1c02804a5110240708000c40e11947c0030f0701d6072403003501c2411000c1040c140004c0e00c0b500440414004004121252603005030315004060020103605255415941812240b80b49020704a113031a0084100161341018401e0030005008042e820000401c40887e2075a9040c58481510031480c020406140100d043d080c440d1101504036080030500c00031442e462421440900040550510702c552205d04418480425204200044c00c0c43d800400150301c0c0c10704519412490a001290168a011416007003003907801d00b100d5102500389c01480e42d8066103143c003c075640b4101c034040e02583c07011070142020400c0088010045c60120110340c0a0b0359000141c1c1c1c0c0c1802402000d48098120344200b440040c09070f0043c042c45141030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 794866672 1250 794865422 794865469
    0x30c120203070203150402011101050906060402090109050415170c01021506040e0f032a07060f020a0f060914015034051303020904030306140103060f0302 68
    0x10340001745000c1844060320b00d40b0164000344801c56070000c100880030203200d0028000d030728111400a40301c0b0030041c0b0741401240c0009074204141e1095200d0005840000c10070080110f28a00c0144c11b0402800340300e00b0ad9108100d58a94001c00044240384c40c40d05078024000c08108503103d007200d000c0940540d410545414440c0d22030340c0300307011200400740b60318002c6450700d102103014641400003040741029880c88941980a0340070208006003540c1440c202080c4400ca0614200e240c0031481c100076100610540000003004041d8000150301c42c026581024000c2032811141d080300c500b4000b4280002e61040302c6080c40701551340c01e80007103001078072140d11900062200c200850700e03801100c1031242c0703500c2041082c20004440c40300c03000c10610b008a0244444d0826081c491f46000d03643c0c18010007182c08280c0034201c41000021315400f400070400e50230580741c09400b170b180f02d000351036103034040900326015548a0b101c0d0b501190301d042c440d001c1c038501d03640038008181d900081d14003007074246 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 794867922 1250 794866672 794866687
    0x18051b060f0703031410051c0816060e0d0f05160204060504090b010914060108220c0b03090d03110403081e04081f02120a020a02070e01150801090603030c120203 71
    0x403034000d409058043d4802180542480f842d1004451005083e1248404540814015030700d40c0000e10104501c8c4913000d10a4900304d00f081c2802c0d0007504080d010503400c0b004e0740790421a00750080e0071062052812109540f8a8440c15039220901c00305210008200b03100400c0d0b115000c62401721094000341c000510030740c42e41d0100b000d50309031950a0310070080c500c004103d4014984220500400410107804403400e2400000780411405001400f07105050301e00481001e0400704078a00c0c0a034816000600b80f82d03076400d030b0310b02900b04a401044071302403120304546132806802a0500078200c0c0000e01e1600d400e42c2e941c5000c54100c8002010303202441c207004200c1c804098001c201800411006200d882c413200646058985d04281a0b0a018018003c0390144003048600541040c103040000d41c45a5145400300d00e40705141d4802c90000c0180c0c3c00010700f820081da0a1403488041e640e520102c5d0785c9030007810060f61814400140090300c80c0c00b9000106140c500110511007451040c2c0c0d24000c02c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 794869172 1250 794867922 794867947
    0x10110f0a1d0307060c0219060c0b1e0403090905070206250c06050c1c0b0f01080601022a0307050307080a022b03020c040b010e0a0509191e18051b06 65
    0x8003504000e0200722644501702c154544211014900c09128000e600c02c0d6040c150010f003070280c1c60900078081c041c0310000c180c16602c400c001036400b03003464240c000c4030f03d03080c24000c0031000b642c40307540392180c0f070200490b08642c030125110f486001c1490003480b08603942c0000800d42c0d0b5181c1c40c0c110810200007113410001d04140038150040b580f6410340c0d03490300c1440560041ca00703606507041540500d031040d02030392a10344840b040306451090900445a40d2090f0040c3d0034030707030000c02044001e02c0038480b03001440c11841281107040340580845004c3e41c0c03034805055a40d80a07010b442819441110098014070b84410f004410703500540350800f0040450280d00060080b00004a015812084100b00302e410b0074031171620026000d1800a00c00d01c2000041003810b6018061940035000010006d040004079030040070802451441c1088111040c00c4003e40300220010b006020f2800e10340600c04c04134184101c0d252068101010b81100a80c00144150b100c40c800403298000d44180480482c420 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 794870422 1250 794869172 794869183
    0x12051309110405010e10170402150715050106020a030504090c0216120506060a0e070f03181b0902070b010e091002160b090115031e0f030210110f0a1d03 67
    0x100c10703000036448508103000502000440c0f4017103030161100c051280074aa921190488050791041191005a01c503400801ea64941d2400510703500040010710500304008a003c10a40300d01441301048240d88909080ba02c440040c1800b0300019428002400151101c0d840680302213001e0040301c2c6481700301d44610284107000c0e0700030410412043c807050b05001c802c1c44140d0340315400b1962141c50a040801c40840080050b080004205080001c0c0c45101d000c0e0344014510b040005403200e82c40d02c00d1a1698198417003c0b410b01400304140c0000500a5560080e01c0704a58400314800d00d680c01c105410340c80c80350042082d40e26100d4030511520801d10b5100600703e40850a0115140c480d4178100820807040203006030000743e1401d101801c00364012492001070b20b5201c91401114015a0309001c0c8020144a014140064400d152410036800051864a860050300d081c00380e00440a020b861a001d80031030003600d10003c000e0711000c544641c00340003021601d003401b140e51402010110b480c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 794871672 1250 794870422 794870441
    0x30114070507120f0c0809150c03041d0903040614040b030f012c0a0209130e0c010822080319110a12090c0306050606070f050a1401050412051309 64
    0x800000d01c1c8418482c800001c2c825007031041c00c00d03182c03404070404000c2101082d10b502038000000411440307c0c99440401c0443e00c0c015003068503407a031300808110340d2258024450040030390b901c111082c0d0f40100701000244201107036000745040030b01d80003050b074500c4800c41041c0c81d50181044040751004809014600650343c440c030030b04a03903041c080620340003040024910528502c01003680501c80c0b0714040c00d03a110400c7c00c1c000d81c56440c1d003c0461040c050f07100c290702250381843c4942d1106a00040d00c04a0342000f40e903440d800f611280154100e41820811400e0207180c3c080084000c60b1480d002907410000b080146550550640e0000c0700300c0c1c001410341c0e0340c801c500086c0d460340e00d51b105403e109103001a10007000702c4020f030b42d210445596280320007400681c940b00001d90344da4841040c3c0e40c402d50002100c110454151401d55141c20b0400d10449540451003589520900148503480c4903a91118420701d101e41036103801e03506a048011801285103402c0d4011655100030300525910 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 794872922 1250 794871672 794871677
    0xe07080d080403030606020f0607030e03070512030915090a020d02062709010b1213080f0a020102070c09050114011107081e0f030310060e0a1d0f060a0b09040b03011407 74
    0x3802c040c54002e0179140c1590000781194440842043d070b11001003082d40e00b0640c80d01307000640340c184001c7d071421801480c2e405817050281042d80e04031402e115008520400d4400b059800b00701400101c451940703030540d09000c2c01e41c400c80840d001802c048001c101c0c0d490004041500700b0b141003a900a680540702081700d40110059062921801e110f5075442c0034180c080b1441c2d08100044800384500b100c000d021551004e0310402010600103040200d44040c080d900400b69200b07005000039001c0d60110908882140d48004009007139040c1b48165810381e50074038582c02d03c0456407001116600050003d406542c0100c1038009007040d410400320040f402003240c142c0440707802c14017080c03c2110070481c66100760002c008000510340f1541d40780060700c42900740809140da512001c1085d0040312707000030020889940d403469075415400e441701e1143d4200d01d801c2d00300b50f8445060048092042c07050001d8544207116401c81490b06070030492206002400002d00704e848445090003060080d40c0b07040c003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 794874172 1250 794872922 794872937
    0xa0509040f061a180408040e040b070216051005030402041d011a060403030c03050706020c10051510021b0f151306020606102604060b040606090f090e07080d 69
    0x3004400d0150310f260020042c01d05070725103410808a15809044101d100801113480d0001c0d0402a0120039240580006a0350b0f404a2410f46000f0045401c142c5804016201b846401c211a5904240140c240c8901074240381e01d42600410907546030300b003d0f0003240e01c141c45504414401c294680241c1641121800206088191401c000004280b850099009000401080c80800d07000044229002d60629010366641440e00b8030f000280900c42c0030403106d0250303400d403e07406107640d040305015103960840c0da018255068204018401040302c0c010250300045614035500025030140c01615501800071f00401804c1000500501d0320189003c00380c0030041800700f490b00e0011200006040c1a00090805040c078400154181311206003032410404c215111075200c5000501c0310751811001861a519800c2c903281070741c0981139070501c0034062407a19400003213548c070030861001110782031100c51110f1828044500050f041007038031451a031050800c0010b408000f0801484c0e03154880e9541c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 794875422 1250 794874172 794874203
    0x120e0f1605010e0607020a0e13060213030210110606090604020c03040e0f010e07020712020604090c093609050f0d030e060c03010e070f020705030d020a06050a27020a050904 76
    0x102420380c03c600460050038148185001078964120202c00e44441d040044c0301d664030700601007480910317180c0080c1118008120b4000c428036005070f8000f500e200b102c83c41c012840d43d0350100d0761801c01e45604841c542c00358001c2200c5003044488103402c15400741c40903143c107042030300a88c510341c410342c0800c0103030010004200b20100840300c900d000d040901c0c004c034814209440003c0d95444d40703000307140c0340301c0541141808540c3e80804032402000114000c1c030134004016005403405483d84070b521000701d040b01114202420040c03150181c40c0030314100f05180420300701c2c0d0000410fa844c8088079584a144404940104100050700d016800f559021074038aa070729541034100034003d40414100d40b000c0c40144010704141001c10340c0300d901454038804015408808030314189141e40071075018010b4004103c0302a501140c0c040249009480610564542c3c460708030480e12003024a03c0840e070b6103010b483e004040518407200c0f050000b410f10b11380c59103c1000075020326090310210b50361078483d100700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 794876672 1250 794875422 794875427
    0x106180b030106081b0105120106030b030d1b03050f0c0312041202030f18151819030b040b1f0f08061311060d0608010c0203040501110607120e0f160501 67
    0x120000e0500354024044070f07281c4008541d0301c02007900b0b0207401105007100303a1103692040b070680d40c80e10340b90311012009503954140503008140480e4058080e00a072003080721041c1c007541c8a40401040c0e0b22100c1c03140d08a50f10129400e420207000c80079402800c1042c2c68100c50204003520301ca280202100515013800e113007891030b440725109180c2c295002409640b25a40c4414207035408190b4152684000194100004080000040720700040b150003260301038010f01e0a101c3c2c1e44036aa01078131801308074140d004100a04e00c44900c00140030311003142c00500000d80304003031036400103144800a40d000c4134803082d0002c958200e4022161384404d0100070400c500007004055001004505c21403400f6065490745900749082d400e6083c0178a50004a01002c1c044a62015004042c81002046003454a9100035141e910a02c0b8107030010740480c200d640c83e280d02181d5117008588540312400321034002c05284000d0020810043c20364010745401000001040c0844801c400d6a5510034030070a0900300007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 794877922 1250 794876672 794876681
    0x91903140613110603070e0312180306010308041a0d0507021c0e2803061e0b03060f06010f0c080c0105161b0f1707050604020102010c030e1518010618 66
    0x80d00c141c21021090400702da01d900c400b2010a0058a107155aa84d5007401904d41094200c07407075815100c0c103100c0e07081c1270310803001811084034080c1403d80744e1443c031000c05550712001c1c04003511002c0100000c000040c40b0b4000411445010b081450800e007408a90504841c001c45240000d6004540000b015000d034201c0101203101c24108150b15a441001040c00311205c045500084250041d4a0304412185a8003e0040d03501520030701c102000b14010030403d040c2d050110b14140e0404100400515000c10207030f100b1844424404182d65401c4011104800810811810310402d080322001003141d0400030300186444d800003207542d050840d0310031031524003035030500200542c0104080042d110081c12410b055040700301840c50060340e06000b4501005012041c1d03001c800002c01d00100a40410554070590003600204081c1c1075068096042d6041004400c8060304903150004080400c0d00ca81500038a074000c112500500504404d82101c1c01500074007801c42c9611016020003141d8000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 794879172 1250 794877922 794877931
    0x30801091104081e0f010c02010209120d0f080406060e1807080c03030403240227040b01050d020c1005100905060f01020303270706090513090c0b0919031406 69
    0xc5180341030316102c1c0f1075445020802c600c103241100614071854820081202008148251008020b5000400d4021307000390f201941c01f50181c08408001800d400000c1041140d0140c0754540c090a0030740d24404407940c01c0b00130012140c050795030b100031512440032413800b8410012640d08580c110b41e5254090b01d0408140d000d0a03803a8044000404143c40105c10b4908a82d03000b41c1c81c020b01c0101c3d02a041791602c2011034003880c0351011a400195590707540c0e000400484c84900b0030110301042050006071440c0b00c001078007080041104144100f4503500402503440c6181c00d1303d01101e42211050107403142a035031220440e00740f40003880170304a00e100f290380003201201d0701c0c91701081001c0041e4481c00010488056100000d40019641d449010105190081c4005507100d080e2584809003010005000340c60060403c0031a07825404458469a400241c000c0d4000f428240381c20154042540a507420702d4001911034407884401c040b009062000c0c1d881404401c0c1011400210715181c002d00a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 794880422 1250 794879172 794879201
    0xa02040509090111040b0901090305190c09020a3510050f01030506090406020a02151f05031b1005120f1501261302090a0608370c03080703080109 64
    0x42c07024134090300e06411141240c6500b41c0168075601c025005884c0d1901036032014040780144440d0224414a294400070b4607481800c9890a01e40ca418441d0101d020f0104c0c00404509004901c1c1040341c01003510340f00f16107104003422014000d040c500701d0b140b04150390440d80040b00d070100f48158948040c10903c5e4080a190812151034000d00281c040d010203400544019800150248260310034011505844a10302d0181d54500340b212038101494850080c44525130800000483c0b10715001c10258241744400089218211b00e4a0800c06100300900c001414010704202d085180003030114580d200b0340681800c4410341c5000c0c0c2100c640c00917002000743c10043c907090b12070705140c51132020300300041001810600725518400700300d410301c1000d90065889801d00082120085c820740100f015126040181e9030166640b00350031860343d59030041d50300700c1e20340700402c03000c002d41c40c000c2d616410b402600c40d40c0400c0e580352608241a40011f2043d0000b0b5407203001400380c0300260041c0c4072500c4030207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 794881672 1250 794880422 794880431
    0x90902070804050d050703050a08070c06030b010e1909060609081c080f130611031621150b0f070308060d0c360e060f041113020409050a020405090901 66
    0x595840d8000e1046002c3c0c14443c012032044441844802c00c5008007940c0d05c842141e00304140ba0800192a0300001c0040b074014840617004a00349129014401c00c101c01a1101d41c0310001c0d80c42040304c03c01c0c0c090513910341440d079890b00107602002402007600400c4c0c9611044c401500b0080d13014207001d00100055103110100640e4201154800c3e0441d500043e240401d005540b6115155000c256010101910541c1058a030300ca00804480c01180181802203450040c000f0084090320301058031200d90984550300c9906140700c4030b1035086805590306141c0ca0400068644403900c120b5040b8041c1d07407640080c041268401c1580099a046d04181c0459086000d500305a517004c0031100341707004070900882010601803000714a0f00c1015141005403601300d600d561004030a100500c0c0038540740304c180c810880071883e00c814010b50306024a1300a81104180702c03c83c014050200c40c51401c00b52004e038204400203e04103140f181c10f000e8450f040380969903500c2d09007008007003d030190000b19640d151 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 794882922 1250 794881672 794881687
    0x2040c090f0f32100908060a1e0c0905030a0303240302030307020f0f04050a0e010609090b2a0a0e01110c010f0e0103060e0117120a0906050304060f1407090902 70
    0x214030052528103800c04022403684a100031441003203c10700104c2c1c0160306081c1c1d0403103242c3c0000303d4a09680400c4111485d558803104800300f03554403280e80048040601d030042020561603041070010b009942000c0c03c3c2d00f03540710042450071164140c1079000954078225103450320b607900e0018032a207264444204440d411500025107a10608030024443e0469000304a4680c030344005544c11900010b0081120f8134003122030f54085c00300500c60007115440c110000c1201c540e00e02c950200b081d040300c4143c034140d0b12228a400c4010701d0401e41d5111000d18049242c2030300c842d00040411103841d51341c0c10b400e40d4582d00054501c0c0001e0090320300a410121850703070981d90201608c820791701d4910f031030914001e0107001600100b41c160030050005151600115401e00c1c0c0c071101e4103040c100c0c441120410f441d000070b400d40318011a106200099026442004003a100d00701440d001406440001500d80715400128101d03491b03024948040d460240401030790743d41105e244001000c80c00000e51803c0035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 794884172 1250 794882922 794882939
    0x60d050c0405190203070c03030e160b0f0403021f030507140703030506190f0312030510092003150901090203271908122805040302010902040c090f0f 66
    0x32110940100e594000103140c01200e440d040c0042841c4034030455a904020320000c042107005d1800703038042410200906050540090000c2e05a5015030480138018240a56440c5943c454042c40640c40710502001c4003581e200700751132900d000440c4003000c80e000c2c9a0340c0641581da00a204000b40700d20f540003140f0010900c1d003140e50541c0d0510340003945543d590001075280c1c82e0707041031070100c3e041038038045100400c4102007410340780a64141559200100c03404c03000d56100311200c528020425800300100d00d070a42180b0810b010f40d40c02860070304ea200c024116982c1044808000380c1d03060180c01d801900741014940c0c00740135201000e5240d1b180181c5641401f020981500014070680d1218548490050002c6086001480395003130060880f400c0c5007001d600101c02030045583e03a14017150340d043c4500da4100c4161101c0c1c1e618008521400005001802c0c002e105400f0365480c1c100740c20059031903200d00064280161905949141403141c0030b07241300c6054100e03020175501198244032024 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 794885422 1250 794884172 794884183
    0xb04030c0e13080d090b1618060e010c0314362d090a1e0618050c0c070f06030f090b1f091104090f02030709060e06070203031b06060d05 60
    0x43d041a0303540d82d00e00d120f11100340101566100034042104041c244407520b681300203030004c18080c5598220070725400340406280c410261065401241001c2ca480189500038010300110390300906107941c0c2c85031502c24441d00c9a1210322101c0741c800c0d0344803216001c856035070807650488400000f110040f03903400b00466603541c00c083d03140c40c00c4202c6091400c0c40304019201c0861405000d002c60700c103410002a204040e000c01c1010742800600c402c2e0762011780c4003078030420048800b00010401c103000c48110400040c0b0010340740f03402d12074042100d07441c5482c041005800402c054840414508d14010b0010200ca0f480082e083c015400c0010390700100300290901a0880d920b903d005070380c28205031700a417203a5015801528980d06015025500800020107001194088042030050319140780403a0100d21044a200c4041807888005009070780c400d0005a81e0180082c140c28540210754000900e5900700450308001c46003120750341c858040050010640206054641640041460f81c80c1600c84 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 794886672 1250 794885422 794885461
    0x13060c0c030809030a0204181a0c030103060c050f070b0103050606061617130603050609070c0b15240403111014090103021b0c01020d090609030201050d0f0203010b04030c0e 76
    0x5110102d11140f0b84e50f000c1c4202106142d000307000b007080c1d00b60f808024883c0528000103680c2605485c8000792074515a803001d5100740c80090b4507a15584c219942c0000500013401c501c1d082100601008804001000003006a01e0017a080e4401c03540c90f5180081c0341502c010015402880d09020214400c0c00c00c0168820042e80000051249400302d1400401c500852480340820489403100180494140d0301c0540119000e40701120f10b80c1d12140d00303840e441c002e44d10050410f42c50b080000c1e00304424031066683d1520007403511860500e850403405a144040c40d412210b240001010010880b41e81d850004000d001e807940904070f01d02e414043d004240900410081901c0010801c00580c8aa4115003a041070b0105000c070340300610740c0041c0d0385c5140d864210f0152080b44281511680034540340000c580041c3d0f10305107900d08540c01143c0036004540400800d41c1c4804040711620700074000745020700481600c00c0c3d01c072841e43c00c01010b1400980d1002480c85008814096a8000f00c030301d9074800d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 794887922 1250 794886672 794886683
    0x81c020c03120d1103010e040308090c01081f08011d0f0f0c060307120c050408150108060112050a1e170c070905040f0215030601111c081f060513060c0c03 68
    0x407840f1094201c0302800081da00014043c10002c00491000c400b14035190081c0c0c007950321003c103540e905026030380e50070007281614041181480042d401c80b1003041c09078048070048018010a039034420b100c0b801d5070780381074010404504650b1501c1d60305008100e0038400ca50fa400040c0050003002000315119048510414014a000030014401a00846056984200c0039404008107100728200404940040c050000140030700031685030203036074820036a4140c40301040035001d9039181580207959049629401c94950059440c500049405d045400400b0303c1c07412400c00c00569217107001010705040d01407401c140c0c0f506004d4a10a9000019004262842d1a0f070001350340e159070900003404081104009d40c400c2c1841d901c1214100c042c00954007405085e202c0489460804401c5501c80045041414251108541644035a0b12036400507400450101010f00720f80a0b000e4440002c0803680c205e1000b10b40009000360075086080e40d01402810780b481d140e40c0701078607940c5240a03107a2620000e0321 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 794889172 1250 794887922 794887927
    0x50705122a0d0f03020309090c1812010e0303010e010f0b04080606010509040b060a17101d040602090a08030307090e01141002070b13080d02071503180804081c020c0312 74
    0x180c0c440c84240c1c45010b40200366200f0f15640c1d458001d660b64030400c103050141e103150011a44648d550320a450004581da1010000c02c80c0b008140300300d400c00100044407564a82d12a81e141c00010301c0214060400c401741c17a00150f0400d82c0600c060344c10781d802001c04000030041000021000708600b50019000d18000c0d9884500200003400b42c02d001c4566903101d4000101e18240680200d0104005001c9401ca103540f0355402543d81e9010085205804507030403050080d403030100200000766031082c031410340181440c0241d000f01d80c60007038541002c1610303030002042c07141960300582c040c40100210841c4003519030501800c907001d08500c0b1442400f03030845525100410b0b00030320210740641041402d1684881f5003c0803812100c0c000c1c0710302c0f00680500b0641580640c40070030000262811030840030540e004010b4114001e10045510b0700b181d407081c403402c10001d024100240001c2070b076180241040100081c94402c950908000401590310440c90000b294802141550010000c440c1258 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 794890422 1250 794889172 794889253
    0x7140d021e0709050915071d0f130c0203031806130206072a09060923090c031e060f0412111e0a121d0f12060405070512 53
    0xb071030010079402c9141d80e20b0520f0104881c0c5e02e00010784108091017050102d1031510341500030703602d016202200481c1c4014075150601035040c05070001c0c0c3c030640007400440340400803099040031a400d020012006800000c14024900880c1c86802a0305007d10040c00c11428803498480b0701c3d02c542540280692404a0342c4000e1207a002400042807200c01e08000d81100d8004084904012500600c11a640b4040000c1181400d80c462580700c0700b40003541c0f4138165008103c0c101017000080401917544200591103615032001d1002c94440010311401c0c40f00ca01d400360000d03040450044c21040c0107040c1c0800c010114507508000351503c122410410b0030001c10260103810140079880c24002e8905448480b90340301c00c00190300281c1c030701030a602d154040501c10115100030318041ca51041244609070503206150060990162400c000c0501500300b050710030042c2880000c90741035406406c600b50070449030514100b03400840340094047c100c80d03035a0942050b07000e0401c032403841c4d03c103900b011001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 794891672 1250 794890422 794890483
    0x90b0f0f0603030a0e01030b131508011401290c031305040507020a12231b03180f0406090c1101060b041a130308070605041a0717040302070906030807140d02 69
    0x18800300e00030301000c030010042c1441801078410b44ad440b01401d40600e81c00641c442c03042c466084c200c148010b1300280340c0d11b080100b5103442021040604858081c6090789013404071440244569075206002d180c4030001504880135200302036105a01450415040101559000c10100780f1684d000101494220b403880c800c0b6401001542c410040c80d031107410741200e2004400c00380890a10080d40321100d070040f100404c1e201d0140002e03441e01d9004205056503545041032a007000c4107005000060059561400740c0300b500c01440524010842160078481c200030700b07000350000303401000341180c6001d02c0d0407508094601c071050030345c2a03884042000d0320341a00014840f0010358100140c02d03201c000b80d0802c41c000740000d0b1802c480440ca59000000081000107007548113002036180d000140444418911800f0130040c0110114001d1100209545589100e680b01440c01444100c0c0c50700518a0189032444e600b400036982035011a001e040b400c2c0d4001041061b000c0352a020284400340075980 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 794892922 1250 794891672 794891681
    0x103020408062a070807110d1a06030a0605070329030a0201031e0203161b0b0f0702010b03030c0f0c1c290708071d280306090b0f0f0603030a0e0103 65
    0xb40c800f401002807980144010350f8040c1605901400301c01030802c00f04e20802c000c0c1001d42d00000c1c54080003461a01d25181c0100c40b5507030060025080d10300102c060b81c0c0d004121001114007d002c20f6032108882d03800c41901e50440c40445000ca01110124041d50000341d44440c08500281055142e401c92081000300700c0c80c545c0441c6442d2815900c904010720b945918002110074100000c0155906061020684104a1a0b40d40040d04104652a1840c079009190b2000301403074190b40d03d8080c170742c5950724200000c0110748040f0300582a1000002d00c054106490f05480703074802c0048044204180451103d4200c03007a03070201c010030040c00080481c41005d5a54128031020700902c404000440390050b4805101d04c00940d1341c080010b407100c444003000c80c02105515044105290410000222083e80110400014902034001c40c2c1e030b6652007080d00d42003a0201c4090400205100909103d40c50442c0c0094601c0b0480007546445808070740d403400b6081c0801c040180407038010300940d0180d40b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 794894172 1250 794892922 794892991
    0x12030115090e13031101091205030705090d080a0f021b4e21130503100c1812330902030f192901090f0506010302040806 53
    0x1030b0340529150040420070160f03001d40c016404182a81c00c4208801e01c18441e0847c12903100c00d03181d02001c0c100c10121140d802c010404010320a0802289006554020310306031b02d80d2292103030076a00d01c180701c03000340800b01c0c40c0111800d66010b5a0200d00c03008084410703001044043e80d00124103088181c8a0415403044445605990748003051500c0d40746000150490511031100c207200183c0070074124641d15108024400585000460903400c1c0d0716110000303142040c0e80410fa014a035458070002070034906d00d00015450103540f54141540701e03400143d40484c862140708035001d0716240150440c0600080d21008042d060711171440c2005213070103204200a041070282c03610315441d0425a000c01003210210680c030a10808040d60748500c0c0c0002c0f035a201460300700800e540002c5550311040d00240d1000c5000f2100c41d190f80d080c620130208810030340200040d003804229205441805c03001c40e2005003002d41050b0042000303002010000a040d50022125030700303014004000580c40708030034030008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 794895422 1250 794894172 794894189
    0x10170c0d141f0b070b0a0f1d0a0b070e0102030d09031806050a030e07060e120a021914090c0a05220b13050402030f04030f050f190206091203011509 65
    0x1002d0061020018290039040302c0d560106842c181d40741c0160000500602400070184020880002c0742040c0d580c10400c000006100b011074001d00140204943d5005200b1109440d4440d00300b4074144020142050303044011030418980000c04240000e480e4402c0086081c511519224210201407244401201e00c1107024245001d082d2a20401065648241c40c141c00203420030202e54400e40c008210300d4216a0940c0366004a00e0341c502c18031030404a0001081d100b40607212483c00541c0340ca509d100c003005140140610101e042c007490341300c101c3c3c05601d41400340701b8100400905041c07450450740c0c405284e0910507120350946000050108850781c41540d940c031440760016141601c4800303002000342d19000c1081c0c240c3c0b681705100c1240011607201c2d207200e40c081c0110300880d00884c2205400c4240e0324200303180c054101c4040304e10394006040c40600100ca01102c8441c254140000303030700b0494071805004286481c3715800702c0c50106004482625030401144101d25001c1c801ca48024152035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 794896672 1250 794895422 794895461
    0x30b040b0a08331e0a06180b010521330d0f0f0b160809100b03031b06010905070c0308010302010e030f0a060c02010e0d02030421150b10170c0d 63
    0x308500d0200d501c00c2060321300c030714400e0f0010031007640a50082406480580d00302514400340098480041d0000c841c103a0705001c1c082210390650114030721aa4030b01ca100366a81c140c6820180711542003008010280d100740010030310f003540c2034809500280c000181c100c50f550394440580c01c00501c8090300b0040180032440b20401d260400c07201c482c609105902d260840c0002007140c51054850050803904960140c1055151130400000740d805901403601c00b9044034145100084007403c0078079605a0601c0381c1d03100703500401c000803041c0903090b4451080d25040700441c00680c1d01a003074603010700009043c0000c82591841030307241040035540821381d5104403021204541020f200034500d50418800650034941d81081551001800c1300582c01c1c0d590046140c07a2030813544090302040800c151080c690142c43d80800b1528403217402400140b01000010486400c108001011010301c3c0c03100103000141d1880361202c0c2291509550040007070803026595106500400018282e1080c084054042d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 794897922 1250 794896672 794896681
    0x807020a17061801140610020c0907030906050c071112190c0e06090103050a03120908040303050d2a0e040b040624181707030b07030b040b0a0833 64
    0xa4a28090b070400d02da081000c044140c861402d882285c000c0c0d404003a40c840103d440c50034410f04002c001c40541c8181d0f101c682010300011010501500d4000010b615844640103101080c400c10f900010150106460b014150355100401141025018800d003120619a00214800c0c0b02640e00e40c4031072030a110b01f10b50035280681607a1a1070050b10079004511340054400d00700305002c0f9041e01c1e0000c005080b01c481c00c1d41c0032204210a03090b80100c403601d402c10080018a0440a40701443c8a40c940e180c42c2e41c044150902204c0041c96002c2110b4200704d101c110300ba01c3e100205408013118500068080b86210104001d04610807134507421138603060300081d0410000d40c01c20702100c061413802081149400d8111003030400c0d5028110580301424080180c3c201080c0c04084a180c400142c510280d580e40703500100010494008000c2515850070809514042c820b803407944204882d5421080d05007040e0300c1d036510701c02204490402d0b407003019107007404804101512202801600b00c9840c0f80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 794899172 1250 794897922 794897969
    0x902040f031505060306061014191205041e1e0b0106080903120a090f02090a02030a150f090b06120705090f040513020105030a110d0903090602190807020a 68
    0x116110070744042c0301000c42c41a01680c01d004241c068040200200070945442c8100094921050100b030f0174000c0701302c480388540300c0d22000b6080c18001c0c81402003001e10403034405800c064503c030000250600d81000c0000180211446078040291645503d45140b4145450b600c3c00401140f1a000301284104040030803000c064594141d6455545024158036005156552402400300c2d50b010151a4400641210702035400b0000413402455812105019a004141c40741c009654101030290000208040d081e25400354944c91010400d180081c0c03450580c00420001c1c0c20b000e030602003038482d4000345c4a503644d08140c2e100007024808402113400c1c0400050a90350003600c42601522901c9030440f4030f4a02441142d1041d261540c988052501940c01140d4036400203050130340c120b41d6240c2d050344903407012000c1c2461071100340c00000c0c020a01e08000e0000a59036000d10115030101201c0444049440c003552581680044d80036140c0709540f000560840320782d0040d81c56100c000340321003081d40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 794900422 1250 794899172 794899199
    0x71e0e0418030e0306040c050609060f0706060503061302010c140102040f080a15090f02090703020c030409151203090605090301140c0d0e03040f120f02030607050309010c090f0519090204 82
    0x10b02c2600c8070a00051860b00f4581c42d03101c1140d000e4030221080382c00b08080d0815000030280484000c1c0013621707103e012204000c0c1c5070440390064450a68840c0203000c80d007400c101154100390309001c1001c1810460740000d1016502d203100500c400b151116031001000250162009000510301c0c818156884111955a44036095001d507a100603000d80b1050010503882007920341600080f40d01d601ca4159028030140c10005860f0a003015800c20400c40c103483c09002410250519510104032422080042656440b4507000041000604080b10380060b4008041104650403402c1c0541ca4054400001740103044000e00c080d582c14000c02044001d040c200b006200c00001003604101d107060b40c3c9002c50f6a0701841c007403001c030054130030401e120ac2941d0320301c0b0400440c0309083c141e00e88803855001c81c0c1083e0081d1010f0021407004404d010a1403400c0c058000a0070301440c002e071005240600e90034403280d092103964082d0300c80b04000c4204415614251001d0322400e44103650304c503510785403041c130701 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 794901672 1250 794900422 794900471
    0x607020d14032805180f13060f05090702061f12240903020706140c1204060f0f0801031e05070b0d06050a0b0f1c0623010305071e0e04 59
    0x904481800040000c1184844030180c0f41d0707a91003134140b81444144401e041d210100c400d6004224699a0049503030340783d41e101e074081a100b00420141c1c0b8029074401e689985400c60382c8600c203000104945158005900e035409070840fa0581e818400d114004427940079150011b2120300c2c0103050090500002846514040060140b0b0480d8011403082000c00c0f00c28403103000300140c201140404c111845014140a0780d01801d1146180240352040d481c036001001100c10600b1501040401001c1e4122401c40000d02c124100b184420a150100030070746041404000c1c0403030780d007200d5007008845c0001d0703c00c881603002d01211404d40d210007030000b20790881d07a81e40d02450704000c8003156609000342118100d400343c041580c10401c010b50324003041d03007040ca21040341e264030300c050509401d03040c02070000400d62400342c48200842006035000041583c10000d0505040030700748410154041407800b180d40d012440002015101d040072184051002e85040c0e21a0902e0000d0603007012080c28045d40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 794902922 1250 794901672 794901697
    0x61d06150a1d0609130c180905040303200d0c050903012309031e0c01020f0f0a1b02030303040f0204060f08100e0105090601090b04090b27030906090607020d1403 71
    0x1442c50102c2045118419144030750b030000b004409503e106442030708070324403501160405260810f00041c141ca41c545035648021201c031703111000d0205060f00340c880d0180c0d00030fa041c0320100c011940040f10b0700521800c1007141c0b01659943c051070709603204c1c5098a903541802002800700c1044103074440c00078041105110000c0c03070a10f0225405010010451340780b464131001100040e5031441010406030488480c0d210340b55020400c034010000035131300800d500a8420065615200010401040742d5540d1240d40544885c400b4080d026945c0041034a50143c4d0064081c4904480c5101060140c07900354000840201c511801040d071210211300000111003070882001401c2c0f000003000e00f60f80c4250b41002d01d80e04084014044e11050f40c0081610354406080483c084a8940c5d8002c15244203c0b00354403813012050480c1d03003a10540c200c2280d13403402d4500450400501100080e83c52240d00700e603070300c5001d0006400741191201d400c81084250004100c9500610b41c80ca60b5869900c82d40030440e1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 794904172 1250 794902922 794902967
    0x7051e0a1202010c0914060705070f06020d030c0522150548030c030f0405030c0f090619031205030412090e01030f0317040503041701061d06150a 64
    0x820368414866809804951703500c0210040c44c06c55240c0342845861002070704068200b10340004a4000c01c0008001d0543d05021a60180740c00750003403c140102100707404050600448100c00c580c441c0075180d000c3c00194420308400da085a115044103003503485500108103c15102c503843e50804080c210006c0d0400100308036100484400d10102d14901e5011b440b19035064110007010300c2c0203004000c12503040c0880340307010b0040e03098614640060201c0c1441d490005402d02090600b8018440c51840c240c40544a006000d00042c03101d04005081c540241c92001c900034450500100380c1d4015a00b0440544100c860b00e2401002030740304580903100c040c6086040c5030303918821b000090032140301a140052036400e503a1022800d008160050301007041c880081401040005040c500a42c03080004664440c500072038130000120071f9088180a9242c20700070030407074044684c03000005da8813044400302903451000003408400003561625213120b010411900d00d44d08134001c6c501c1000b58180201d0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 794905422 1250 794904172 794904203
    0xc12090f09010308030a02030c12090120210702030f0706060303170c0406081518010501020d1409190b0a0302030103110d150b04240f0905040c030807051e0a 69
    0x40e48490030710005203024810000100207860711f502668000c101c5200c8940303045040c1d41c800e6007a68085c0c50300b40301655100c0512407084805c00c1030404c00e40a120308142400c50380d040c22400c54000d0880710407451051400030342d1070391003441164800340f442103085866170341c94100440101507078002100456441c0c00080b1104214000007803140e54448a582e161a043c00001c56501c02c0141c08002c00741c0c050f010144161b0b50f4016114039044d58130072130326821b40c508400242740500645403042808406000c0bc4451510101212041d01d402d9400c194502c601c51108118601e07554440503c100f0081004480740380c0c150011070403640070304400c06800e41080100030700812507500052080c4036400300c03005018030f80e1b008011000310080c00044c1d03a600740c0c3c20544c040e1000075080722012080940902c1403100c90000700b4060041c4a0741004503181c0b0f5030310302c84c09800b0b41c000a0002540480c903c000c010040002c82d04542215040040318920700d841c641e42d410341ca00040720300e0740f64203c403803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 794906672 1250 794905422 794905429
    0x3040902072307050a060c030c0b0106020a05060c1303080f040f080a12020c090a0f0b10050705100c05070b0901020d0908120a1103060f01020a05190b090c13050c0c12090f 75
    0x10400e544004000b401030506d81030041d1483c0e203c540044051142000c0c191004c28280f83c80b590090010360068169110703603141190418034003c0c5016582001800995080e0b0203644d100780a480c1c2c8121b05070b949914030301000941d40a6a409103c242c200080d012405141c0420140328040c840c452000c07040d00718040598881c00646400d64100340e2060002d48000d00710781258141e0303082c00c1000145a00c3c42d00c007248040048681c0d880101e02c0014121f010410300700418840d11241c5101041741108201e40204070344289070010f42a16011000302d49144001e50482c1d8454000607400c0103078007114038009526030003074400c82c07808004000019001c0c8900d4000c174030000225400d0a461983d03002c0811200818a4031311504503c075040c2414000b41c020840e00303481c606d4410541014900740d18000e05071100c000e00c0301502e6005900b000403039454218400301060304201c0e01143c944c1da00c610b00c10250203214904030041c03159401002445060000900003a20140d40500d1408955800d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 794907922 1250 794906672 794906683
    0x70e03120f12041103101d060c0d0c050408070e04290408130e1503070b040b030604230708090c041a0603090a0f0602041409040209070c0203030409020723 68
    0x400e0803810002ca401c0c800c141491254810b104804a20a00c03245070082850f0403044050748440507598528101411420800d80c40324401100041502e03250401c3c1188050285500412045451f04800d4150900039400d0310081d00d40142280c004907540d0b586541103282c107640681c0c4041c0c0e14000180f40c0c040c10a503503403040c82e480c058001f030381d115691880419880340c0340c8000e21007400c200204111007a000418050501160a6443c1c00359260415040507042c1c4d008080704541040100070085546050702da01ca94101c0d030000d2182a9041031003081808a80d1030540026484d080085840e081070710a40a144040120780021201400b0700c82102e40089155600600d0951203152500d4000e004652000017a02524092800f030b0351980382c0c0ca44503c0044031059000308040c81078003010300003055811411241e500b006e080c1900401c0318110041c042da010403031004414815074500b081100c0003405044400c659880f40c1d0309210703c00f110941100c20810806020b4159103001c009030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 794909172 1250 794907922 794907937
    0xc07090f270213020a0509040c031e020c010213090e06010e280b09010807090b040506011209020d0b100e1605040e092109190f061b0803070e0312 64
    0x1250380d50560200850101e2284404200d91000101c0c990b040c0400b80c3c0e00240020144030b0b10b48a0f1940348940411040e80c900107242c070205880c007101001003101c0b80c40f0800b00000c01500059441600d81c85542c064401c1d100030503038080c541c1c2c07000100c1943c1640700000914108080d5034940c0d0302c40544e020000400d642101440080403924022a0481e5501c90090980d1250000d000c42a040200d48042d90991042a081c0c00080e07041000b400b607070045410604080b54104002d1030000c00213800104c80142d901c0650740d03a01c058000b107441e0034000c04400c58009081180c4c0d0b00c3d0280c11000034000600601c043c298075080440c840c560419021601c4010741d4440504045c10036816800b14000100300b46d035280304000503202e07070080f2981d6112411049141da00e96407980c82c0c090001c124000c90956031030703040c1c281040000e661031860074010b0f81c140d0f140181d140009101d00d5040900070700000b42030604000306204d03031140c02080060781008181c0560b030500700e0780b80004003540074100c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 794910422 1250 794909172 794909201
    0xb040603020306060f0303090d03050901020f0105101503090c03110310140412200d0f020c10050f04030b0c07020a0803070b040b100305032209020a0e0409020d080c07090f 75
    0x103002c66001d02c1d0104412145050103400caa05008c500c10024540300000300081c0c000c100005101150303540d051242c0b198403801c110092085081c08405008102e541d441050349013000c000510320f03483e20981200e40750070742142041001c9612400c00441400c400c1c0c42042c400c0c81600040c01c5401e0003401104c5483d50416141c0005a07115126145040d800380c0d01541080162051200b500285121281d85054030310f0042080c121541e4016100c1e5004c06800401c7d907200700040680d80c1d4840c80c08202800103460026200c4001301c030310071403034040c5401c01041c00c0101d400f00611040c2e200094503189008403004843c0c59079071981c0c43c1d100c0c41110006001d401401001a012401607005181c100d500111144406684c0303499080c1160401140c0002021b08205003160b26010120303500c01825200d0000c61900070b840310040d1151a00701030641c041c50b190400c2c4819565035002c0040096000494203503140c00041e40030742c840055001e5903d90524041f842540c020661003003c60000341c51 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 794911672 1250 794910422 794910433
    0x1231201090614011b0215180a0f0b070f11120a0c0f06120509150c090301050603060106120f06241b0b28022a06100e100b0a0806040b0406030203 64
    0x4c5d19600540e03900718080e40c0250030801049421a0131000412040083d89041007a0704495400c00c003a440b0660302040c1001c051b40420b00c4010100c208aa540d140c1c07002c0703110396034442e0780781c07001c1050001095035a01000d00d443d2101e107080c0115000e00c04902c0740411035081c5484001803c0b06009a00512001a4076004040c50007000756024582000c40e4008032140601c80410041104000310381503886c814021442c071203941405d004854001d00b048000d42143e40c107000d001000c03071141031000407115460b17410f8000f83c500c2d2540104050074000c988500028418030560b4040c0750b2850a00c80080e25079601c0c0c2a09019a495001002c0e5102c40707007015585912540004010041d9a020070307403406400c4076620141d15200410b9441e5400590031040e8200d450310340ea10801c0c80007021541c4e000081000245038100130740100380c50400a08112580724811030183d0403d4a0b009409030030320009a166501703810070720381481082d049030244003c0c81e8003007d00042d2902c81c0b10013034055110707 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 794912922 1250 794911672 794911697
    0x10305012102060a02010207021005070605060a030b0a0b04061502030c1b0d030309020f04060311132705070e0405011406030a020a0308030c09031f0c050304050c0123120109061401 79
    0x800f000f4041304041d8030000d0300b410010b4001079203544500f42100b004c01c000065010801066009d49980440200c58144a40b8a1600c488001b00c0e0000e160110b043c0e0340d001c070480c1503600d80c2d0080300500800c5407440c41000390300502940c1c80d031112260120710700c14400500a031412002c0040b41002003e07184120a452996040d0007901c440030080341e100803600e44e5500c0b1904c951060030000c502450006218292103401e001c0301546003e00c01042d1030800c0038040010603010080c0c48120341c1c0000c013a5420710a410424180300558000c41c40300c1c190b84013804141b0505410080384d810300103840340b2142d11075400b010340e10748a141000f07400c80c1d04541c0c2040850100c0c0c000c1c0d90300c111580d0722280385c440344800113402d00040116403407070302c650308205802440007481041ca00340303528180302c0d1444c10710ba240c941e030703c080c807a01e002d040000805203c4407100f081108405000d244038051034a800d0300b02078041d034586003400760b03424061030140700250203102010004034030395068503041c850030107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 794914172 1250 794912922 794912929
    0x60f131e0e092109030a1104061217092202040f150225050a03140705040501051302070f121d0405100b0d02160f061406010e132009010305012102 64
    0x41c850791881d0781080a000e103200d0f5072028004040407a04c220501048100c41d0408c00044540c6d40d00090070b250006034207500001e261003140145101d40e210829100c0360180005020014240c48001e580c1c40542c03c090b00008440d0003510aa40101c482110200d4a0302c005aa81040582e880f5005074410701c0e480c07001c200e2241142c035100601d0f012100c3c4558860010a000301c016074002c541c1040e00d2210700076031500074031458018150440c1c6c148020b515280004612814188003018401d5000460400f0001100303100080319601c4024004210559000546203105480d0040b0840303401c07500c42c111034501840f600c0e2080d2510700740043e510b402c0010701c40260304101180a02540e00b00032101b025002c9030350200070248142e0340c0074000491840d041080d60f590510701c4205100305403e02401c2d81c0c120405461000003600c22045500c4602d103041701601600c4030307050409801503400301c002c00342c4000400d0507110a890500c4240d0742c403e14102c030a440103100b24401c100d0703810300e10010314 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 794915422 1250 794914172 794914213
    0xb060a0c020f01020f0f030a080c04030c050907050d11091c020105450a090e0606010f050706141b09030a0809031608030a030b1e060f131e0e09 63
    0xb4810302c1200c0841035039040192400c518012215540c2e400807400094080c0d00a41040c2d00001c010805814030f40343d41e03200c05440d0340318000c8900c00c00d07460001071042445502503600000c181401440550030303c0d40b0f4034110758003d9140303e019100741482800803407005c002c0344c140c1ca607060359002e2501010a008d103003290003544030b10308050980150b02030092105640c00303010003801414140c1e100707072039010400d090380c095001c82c282500307007003c0754100349002c504c3c42c0d413125081c02c00749510614810101d0b581e1044440003840e09240c0740320a0501d00101c10800c1c03207030500800138074000742c2054400d0002d0044ca0441903155200342d1000700065181405000c110101500315034512405c1100329003410b91a800098440d4000301360780441592500410702460016550520400900d80d00040035a070b5036a4031038010b4a00145056055004508450180b1210701c120404181c0307031848a0f500c0840742c0003040f00a80d2105022401544150381240100c1c40c4400402084400340400096032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 794916672 1250 794915422 794915449
    0x6090406020f0c010e07091b050315040b060c060702010c170114120a030c02150304081215041a0909030c030a0305040f0212150c0a0212070f060c0507060b060a0c02 72
    0xc2e80502c180042ca1034240180820345050ba07010f015041d080c0100130701200c0103400c0a9034901c0d2102c0044081e950007004880d004654200040140c940f26000701e4050101e10442c1c1c2e0300034100149405c507884003c00e500d800b4951039802400f00102c1c005d400c030354903604c0102d460008850074004109500400c44c0100001c203029040c8003414000820b0103081046048056011642d1701e0007010071403620030504221584601034107415414240c44030507050040442ca40c02d280c50178070104042084103e03400b402c07248004d0040c80405075103103050210040051515003c2d892060220b981008080291a100b10b015002076080440f45d100c214040c143c05002619540c510010030400341c0c807134100c08502040251b0043c0821081d010340f00300300d49001041001c07100e606002c2c18481da903000c21803021083c0e50701c80c500e0329045e00d401c2440e05407900000c0200078502d41204130380440e801001a210741401424108200e003500801c1c490035201d244c41c0440010102154040113242426040410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 794917922 1250 794916672 794916697
    0xa090504020d060e0f090c0d08030703090309081f0b0a0b19050403060f02031f0806064606080c03060d08090d0b100611060f1b0301030c0501090b030609040602 70
    0x51580d11058903000b04c405035440c183c1c540040c002c0101e003007010003940620303003010755501060480d0b035201c2011900010744114109034544109000b40761003661150080c18000301524141040d04900f0344503c0c2c02c00f03000c900000d042051241c1549007903281e000071243e400340c1c410716124900c10381103c1c429a4155990501005202c00701c0440d42512032001c02c40300c183e00041e528100880c1c20552400745c090906440000311506000454002c0341441d00000295108880c042c1c0c01c00e1300c6000c02610b01e0759075085c5e01c101141d84c40d00d5040017081e0500000b01c010030616203070326180c04844144003203c0ca0050b11408002056090421003180040741c1d000d520401c0c10985050005001c41006540680700708142e0380c140031084101c030b100440201024106154502c2181c280c03691500c00090400c40451031103c00031701034841d000c443c07a60400d40c5048140e034079a16440c244030101c50070b0041c0c1d4005000f0441c0490189451400c03640580c2c40105900015038560f030b100e8002e90f0003d84070461 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 794919172 1250 794917922 794917931
    0x120a0c0c0501110a09090533040e01060f06020610050f120604060614030c1e0a030507030507030c090e030d0e0c0a061d03030a05180d08040308030a050c0a090504020d 73
    0x1141c400c0c803c511164100c00d86041e0f0315040d915004018000540107a04c0052404003805000120b184d4403040840700318074640030400c0011340c010409042541600d40041c180f11221041d40010360140055901c094240d000054607a03000300d96920080f21300d001c0c00c00311904148400d1400d41d0521081d000d00400080c03c4400c540501c5007032074800e031000c51340c4980b9540240004180c5541d2410082d000750000c0481d6441280020043c52000907980400110180c281c14151034482e8504043e5410400700c5200f2552454426542d04d07241c401038036004080e15000c502d03502c140c000e003078124030800c0c029420810003041e0b000044c42d0100310301c01c41c0e108000712102030703071100d400000040174103403103c019046102e81583c040c0712480d40d50922980003046820f095981100035600114105482d2140002c00c8030301107182207140708405032001d9800304001040111140007140b24101180342030001b901c5410086446000fa03018010204071024020303c01c1b42059805000d100007040740c04078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 794920422 1250 794919172 794919197
    0x309010c3b0a06050306010906050a0507030e040204031e1401020304120f02010e19060e01051315020d14070e01110c01050c0c120a022b080a030902031e01060b120a0c 73
    0x105056030b564071000208a01000b081110b60300403a8600043c40c80b82441442c004038840028032904c50717110700030f0600210f01400940350300c0d01d5041d60040d5512080b2007102c0007420290100e003d03501c050071540c268084002c2041c01034103000707982c019035124840d20740c0d55841110548075580e08541c0d840c1159603a003d800c0d40c80c407042003060f81219032020450a10029403c1150036503000b503c0c624032036030514090001013102c00f000311800307d403c01d034091000f40e05101c1ca07038080d12a60051032503483c00c106c02c0300b1201005d0903400d8004c2070700d43c07a47c401c9a00d4050040d1010000481c4444030740d04501099800d0703501900c003c041c01240481924040c1e0300d901d00103a0302030032040301c61103264061102c01c011410800000070b040c2202e0707003000740714242c4058040d901902061004180720303408074000503554003c1d084a00d80d954020151407200c14000301001004202c0440704d00e1070360902d00c0001e01d0030950b50450f48801244584400036507a040400009040c050703006900308074400d05031030b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 794921672 1250 794920422 794920429
    0x1020d0504210314070509120a03031509050f01061b0c1712040b09100309080d15090204050f09040309031a040605101202151b030309010c3b 62
    0x1a129602c079103100000b000e00381c24003003035600c0400309410030700d4904014030403011809621035a215050b894201e6654090380f01044461070360b10005d24242c460130000d00c0030590503420084800c0898001c1c50040e81e501c60300b200940d42d041c1c0300c140c22541000014444544204900681c0803000c0c84580c010a0381562018503900313040c7c2c000b80c0c248080051481001e50244400300c0004a50001d85003000c4c04d220001c0043e1003a400700903c50311803019440c140328000c3c2c220501140d04070002e25118441c100c40240035203000d410212200f90034400c04200c0300070760300c240c42c251103000d403007520b40401203010b201c40481c0140003034040c8224100000006030104030102d2414000d0074541403a42041d03d004e4044d2000a44a40e41214002c5804e00000c2030031800c2000954045410100807992061132084501c00da03001450840c0c80322407600b48004000004500030300107040200805100700c40b02310f6002e04c508084907240041e81810b40b60015100000e1a05140f0074032100160b2104038001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 794922922 1250 794921672 794921681
    0x1e0504080703051e010213150306031709040f0e19081209030c190201210e010e07050108010e0606043309030303450f0b04021c0809040e01020d 63
    0xc603807039804058480750140713805039001840d03103204c4001d40c248a080328040c1c0780f40d4400d014040880d804140340413003041c0320340c100030011030300080d071920722600780c1100f10103e51140c10307258041c90070140c0141c46002075110700400911b002002c0d00c11080207410610490507545415142542e05220740d4242e1107803a5a5203010301d906130001e41d66a601010710030b00307002c0c00305000341c94610824022005030b604107825049403c1a00140c0101c5000140d403c1d008081c0986034890941c40c00301443c00840c0001071040a81c2c00980741c44402c1e0380c0c0d1b40030070510142e00711200c58005200340000c001c0c1c20030001e01751500502e0605110440050000c0c058114540128118000350b0300202c00c00c24140c044c415603d05180b403c9100810641e0b51012001c0c0700120b0070b0040b80300c00024002030503111518800819181d01407051064500709007004214180161010b03403044026840b480b0000903200740c0c0341c4942c3d51100c140d40c14115404108401410011020300d011b5400300440c0c001c0490324411f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 794924172 1250 794922922 794922929
    0xe0f010204030c0b0a0f051b06090c151e0a1b061d030307020d11010e030c01051f120f0f02120d0e010e06041a070b0108031e0a1e05040807 61
    0x6071580c0c0340d824003000748070195200c00c442070b0041000d5141560700442620301c00b000d905050b0323500c00c00301120803030340f80c1c114a1b204c0c02d901807175051000d0518041100c10100c28201c80c3c043c0d1840d84441121011310820101c2082000354840c550103c2005a001d481104100d040100c85040c400912911280f42d102c422112a82d440f01c0488000c42c0d45a03c49603c8105840114290b28010310065500d4505c040c20300b0500170301c22134111542800750006421341207401c050302d84504414080c140601016113411a600e60a0480c10710403120740c0c0150022070380c0756201c61a0b41120381e150510b16140322001038803a190319900c01c4001d0b03200d4a10040b0ba6100220003030603d44a00707032000b02014020800030381001204003441c42c803581d0f02c8064800f40ca642100140c0440c0907903c00003611300c02d42500424040d10304000084800d00400a008802280d06d400c22000284ca02100400c3c8198075040c80410420b401402c03c4070304072199420255210700b03085d4a41500d50480500e00b0742d2a03031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 794925422 1250 794924172 794924203
    0x10203041d160807081b1b0a0203013c0f020705031308010507170901060e0708150a0b03040b0702070306110a18030803040201050304051002030f040308160e0f040e 72
    0x2002c0c01001c00c000140007003400304a1405443c0c60130456030041040c0c40240c04c004920300c10000800b00301080c20103c658032450110003447c1002920201d03611381e4200041603200e9482e2040c111003006084560b0200c4c0440e0011152804c007103910442443e421400030003100603643d111121040000b44001c00070540500010344d01d51412068200344900305400c0212640d0420080c0080e850b00049c40036002d4580f16900394480d500c43c02d440740180010360204610b42c2d803080c1407021454006564034002d000038910940c05400e224148518001148500441108104002404205401081900801d061041c2c7c2c445990340d88074030b401d80d454412010b602d6000000c0341504540c210600b001402d0205901d880030919544804071039010080000e8140a0008001400c01400f44174401074151640c038215200d08182d500351410a50803101280403400c40401b00c0d5020b61f0001d0920300700c520b0796482590300c50100041c841c180d00c400d42840d800c2616425101c28001060110441c94028030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 794926672 1250 794925422 794925479
    0x1722030c0513060f060f140d060f0b0702100c110d080307020d0c050c2b050604060507020c030c0f030c0d08090a051806010318050f061f0e01031101020304 68
    0x1a08002c2211099288400541c2c9443e80410070f0804004160003103400504020255100c450800d5800e00e010241c95001800005101759000e801e592110302600d12604860241684400d100c0301c080c441d0140280d803042c030801c0d82342c030400d00c680703690003069201d444042514540000400e10b0181004812104903002108120748a9030400c0200075030700382881d1483c4d86285680b2072176100c10420104a0160f08290800240786000c10660344588511064440c404e240700e00f061074a842064030125440da00b0140410321080c0700055801034143e004000e4152340100008018842400301c6559801d80180700d80031405950317440700b0421a13400745500320307641c00c800400c01c04410f809070403540c41055842311518408480548640d404a020b08000600741404d000e80b00240c400c90030000d00c207200c1c0e8800501488000f01c1e40d03c0c0600141405000f4030b90414040d4580c00f03209004000388502090b0040000c6681d000c80218038040600549107032940304c4d045000640d4a0b030400f0030002020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 794927922 1250 794926672 794926679
    0x1801020a031407034a01020d0b0a05090a0509071508100501080717150d06091a09030702040b04020c0303090601060807050310050d05071707090b0604031722030c 71
    0x5203269226609203010030145040c3c1001c10441c180005401818012014007201d0141003c1c0752400c0301881c0501e00e100406101c5d00c4c1078080c1d4085180c4100c1a03003004185011030801c403010806482004020380c01e03603942c01d480301004200080c03854101d032281d190001b40b001803030200301c44186055510030b0420300c0c0070200021003c043d5889641042080f07010000ca00364008a81d040b0038040b01e08150482e1180080d004001d01d00840d050f034090304c04e07180c0d002002510360004041d18070540c07503454110785015040403044011903100300705800c00c00c0444018a4654040e00c0b0120700104014103001000506038596002201c0d455407507444403005119003a0050105584040319152440c6146042560f00440000a00c5121301400140f064081009070a0000c4400f90800c0d0040c401d01c4400c2244403980c41070140f1943d19101d250680111b00307400c15408440c2a00d0b00103107909109441c00961850507070103002d030000e00d10b8039601400011440420302c500250b005020303201480d0704 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 794929172 1250 794927922 794927951
    0x60f080708060c03042a0b03010e060f03190c171e0a20130c0816030e061b040e0a0f0f0c0c0b0702010207060e01021914070b1801020a03 60
    0x56402981c4540e000d00100000044110100ca5001398800b00ca0a50030481ca00d10280303c00c076288100c45d0798203002d003011904500041c003640c1260041c0000784019120181448038040c1c10f60007454054100c0b1680550b1007101c1520711180c036105140e000d1407540c0d0f50300f2050500710203041c648010b03002950401360b102407000501c4091441c80f4081c5c0030f554115900d08551540d440351401e02458040480072066840d40c4034282c02d403003407400502504001ca403009000100446201000c0407582d0b841ca0480d80c401c0c800c1c685154040c60050002d078690b006201030011984c100c058030200100400309041c0701d0148158040d0103010f00100c0c2461071184417074103817001880d00010f298504140c00c0505a402155045081c3c1c010840071441e03103841e60104c0c064410140702400d4a03060904e40c4100080543c02403d50120240e40c0101550340c0600484070100080c0c0085000a024001100883d048050040d0898034201100c210344c4001d1000c1c9084e604203d9000c00031950300c0c81001c440c0c46 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 794930422 1250 794929172 794929183
    0x60b030705150403120306090f0905060c0a090e0612030703020f060f090d0c02010201020903070e0405070603090c0603020903031201080c090c2505010b09010f0f1e030201030e10060f08 81
    0x4012654290304a40006808455008501c406040020300145c1000741c14061392101d00909580e500070f01900807451544030240010081c00c0b50244a04400503030300310b1064081d40c0b00c402403aa00d40c44598a0300f07085100c41d0801a103025409001080b07400d0400c1001c000038104544260090a42180312000d0345092080c0200800340c0c040034401004070041c004112202d80701d6150902c0d00440c0c4580c00100e0080c00740341203032500b52250001c08214098061034192041e03118900720307460603031500340480549002141c0101350126548061080d240a40c0141031040c101a08590524403001404001143c0030b92042c08180c00c01901c2039442d00340107040d59400f1565200d0030b0714058003078103030700c4102c0d4420041007403194652800c803080140039004000008002044240c003961104c9003042803440f503105910070741d108044001200c0c1d20b1446400c00050ba2080fa441c6010300d907400545c060302c2c03d0b1035000c0ca80d000d4484241d01e4400588154000b60082e55110800c6030b00f0080d1540c07401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 794931672 1250 794930422 794930429
    0x5070516030c0f120804031e15020d0608190b070c08030a060503100b0907030c090305030406171302010e090601120f02041a1201050d051618050f040f0318080109060b0307 75
    0xa50450011303c0102e880d1808560469034081d492440010702a0340860604d900038000a010f040d0000a5a01c25000c9401402c00b42d41c8903181002075640e5501e60039660062441e40d8405000c1d86d040c1c00001c9000078030780d03aa1001e014144814032400c07560743c02c1c205500c1224124681c80e50f40205000710708003004850a1609000c60411520b40304c0800500c6100c00180036204241c0c54200551b401d601c901403860003560b0100850741c94980711040900044541641c808140c100f840c002142c8200a4881303e240b0f940603164110300c244601c040c040080c0c0001c10450501500036200754004001e441a1404062003034001600c880c2801d580d41c400060040c1c0c2ca03452480144160424040150417007411500101c40124442d00d8a14101e42449000c400a81c042403500c00c0c006841c211102d00102001040401041031340d68102400c240903100f540c014081a041c440003000082c01081c104101d1401417150030601e0303641c3c0c03150a0968403403074001c5561940743d4200000c1d909041207244003a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 794932922 1250 794931672 794931689
    0x9190501050f06090615030709050607080406080601080411091509070e1c030806040203100506030403030504020415080c0f0a090c0903140105160516060c0c120305011505070516030c0f 81
    0x1c2c14a80f000400044918a08110446c40000426200c2d4010f0620900401015204035114601d03428071500c03d40080c481c19010852100000301c0d1980700b424801d1240368084201040088500301f0312034120b5000b0111004070401d02600c84503507030f5280c5200c0c4910b141d655031034240c10f02d150a20103444415141220040c102802c810000f0b500a80b070070394482030603a001070f00d0f0350369121440200c401513881a60441000000d00040c0341e4180c1040c1d21440c0281c5003442042c2496080c1480c042003880383d880543c00204c4e4481c613518000003c0307146608018458070a05880e42000f0040766071a02e41c0c00c01054803081c0401c10019a00300c3e060018071000001c00c910301d45103881c00070030b402d01d11400d020007800003103003885040d0f0b518441008580208041049207281c0c000a400e5082c0310400b5a0414003102c0030202842c4a4003030117040e20f43e17190450781d180700710020a80b89134000000490301c6004003124040701080c041c5681000b1070162003030f600c090380351441c0018101126088140e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 794934172 1250 794932922 794932939
    0x7031805060426031804090f020603040311070605040b03010612090b090109140f07060f030603051b1e0a060309020a0306050a020703120b061e13140a0519050909190501050f06 77
    0x12407008882e81c0300185417040d20b020444913114a40f0112000c0540c0009501050100600061544c0b01c0750080c01842114210340d54107440c1c100030355607400359102c0e090340103400f00018444148201c03e1484131207010440031034904d6081e0744494a0010031110b8541603035407211010306111625a0459000c1c10000c0502000031f0324202440d21410280180706c20310880c08000c0001520030340c496401180c00405440b560320440003c450006002c1c084c06200342c0e51248180480f8105040c5041d0300c03030004110403001460036500381c000c2c1c00320190990b03104107950b400002181da0343c01054400e000000005a4900701860050001100011340114407880c0254050301a11a0070880d13039803252415007035412508001c0c00221521400c0c1c1000c021280c18040010008a00c01401c140d024040381c000b0301c901c2c0c441090000b04202144111030006000500300b0450070844400c030740000d450025101c1012a69042c0d0030980c695540403151a9514010040400798490b03003503030002022030791004c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 794935422 1250 794934172 794934187
    0x80d15120b04140d020d1e02070e13050f0c010314091b040b041d07080d1b050307020d0c0311010302030105010206040327030501052401050703180506042603 69
    0x591548000c0300040c80070108101050620108040d2070080032414022110710125618000303444812602c200801b040d401e203000c582d200100340048605112950081a40a2901c0d460013104400130703000c03c81e06c0d10b40703180c242e01003a030501400300d48094080041054040311000103080f14054030400f0b0340166074206001151801040d104210100c0c2e480c0015400041400980200700101758154003078585000301d414410170400a8251681b200c050340c0290795681c0d0815107031a0503111a0b400122614244030940e007010180c01e01242c064011a401c0c00c5140d40440c04004071048181c0e007408054008004101c07401c1d9801090400c2840d095096514000001c0d541d0b96015000400380440b1001d4010394042d002070441c040f228030032802d00066664207181d8000c0000b96120a99090301507020b0b444c2041c0342100e60b65404040e507035a442d000041d203007120308072421040d00032541e18031b0310000703129514880a4006018104a10809a40c130103400928031204c0c24802c8416403c18000d01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 794936672 1250 794935422 794935439
    0x220e011e030803040204020d0608100b0a140d08071b090e0102040605030f130b07050d1407050f0c030409060303120c090e01090f1407030204030c1205031905070f080d15 74
    0x9034226607000c8801e03510707500c1c0c600c00034004c1c1c01035a00ea4440c1514220000035104000140358a100d040c0d03190030044400700e48103004c5128220300980d40b42e107144030182081814400e660102e82c0e8040c0c81d406040840c2981c0384c9105003261070603403003804c3c0040c5050141034424420300794078040c101c000310315003482e0510150090100030032541c00c43d81000c0000700780c03040e5040600801b55020350b11183c1d914182c0d03070240c03042d00101d240000d010324114440d01501400c01e4454014105a100c1c907060a5441c01d00514642c090383da041c4041c04103100000383d00442c2e024150146100c0d486c2c0205030800c86814808881a03051031038100003056404010384000c030b500ea641511405c10b000b04070303801d942d00110050411003918008000c2002c040201456040c0d0261060343e1141e80c44c0d076186581c4901c2c0c03001d0b0810098000c5c2042c1c00030041c81d0b07a07100b000c1c81d24000b803003950b00b002807c02d0202c1d2180b1b00140109141a182640d00051990101d21b4034845d107a802105421940c46990405009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 794937922 1250 794936672 794936729
    0x1507080f16021005031603090f1a01090f1103130305070b090a200a060302090105132306040b0f030a1814010b010309030507021c0807120f03051302090c220e01 70
    0xe481c00d0588d12030b002400d001607802c010700c9581d08a00e503800700c0e0035429280a0741410900c0382d030f0741c0f071881d2081b11030030362426015200d0521580141b050440e11070030800d5511100f0f903481282484802c205c40000104c4150740c007440752110340007403d40b5950506002001698140781c000c0d0105840480140554400c1e80010035584240340042c0c41d240705074016125032141001040040307440c2000001d01d107082d118800c410040032150041c1c40c40740c080501113203016601914030001402d1101018290720107002e907a2006c48442c0215940c640500149080b04000c8015555141e24101e11103016809000f00d401040013840e00704600c103a00d4900030043d000b0745034001e1050b100d601800210716000c80c22600341c5034015088a43d54203907498440c8000208103804808201c464036070884aa01a203c0c0c80d01c6811035134925240c0707804075800c2040c0141e0080c50b40e414080144412000380d0442d0145101001030121102c44040c2010700c40d00003418168400c950160b01034008000081e200c0c2c90 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 794939172 1250 794937922 794937961
    0xa180303232701020c010e030414040207020d0602180402070b0f073b100c0b06010c030503040b250906020111072a08151905061507080f1602100503 65
    0x1002e0342c03118080d0180c5000e882510207a502c0396003000b004401d030990100007001101d0701200c0a07689400c1520520050340610000658030107060410940410301d241c000700101100c8003400d0415100040004081740c0100174103640700c0c0f03078003010040c504840c0704d403654020901d03003804540b14840d807140d00d01400c0ca07016a903800366040b034154080c100c2c1054500389000c10040c41c4005003551600001c103400d42842041e5050750109002c11030b154004c205c0c107104203030140d440a10310b0341c581c0c59012025102405506030340240700040a010060710700c010320002c4c00c0c0e03035442c0c0303540386040d4000342543c2c008079540700c900c101000605c0001d43c881d031a40441403078050072000c100c164154004d0b0f00c030419034020320440c06901d0451800c0826151091301c40c0d5a0a40218070000001002c1012030740b041b598942c1203080342c64080407580d40c0b000a4450302c0e10500502c0d03d8a009141d9021054104201807480030021284600440c0391002107482c501f000c9252031425490581d4401008100801 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 794940422 1250 794939172 794939221
    0xf200d081506270d11060a23070215030f061e0901060305060a08010b0d0209060d0f06050a180f02220f020a030b0303190342080102040b04030b0a18030323 68
    0x1c0c101103054000c1210100d030348400c82c90300744c0340400038240238080ea124007000c03440380c00400c620b0145400e81e04103890040102c445c1c10361465540c0c205206c030500922101c403604a2591049415596841004034060200b0b40c0c2d010645052460620455080c4c9400c4052143d0410b00540c0441d03c503898000c41c0f107601107440c0141c60b1103007408200040001e64018003400c00c080548000e11140350000381c06411903e2007000840c0c20b01c40010010b0003035030402800604002d1441c405860a07160341d03040c040415002c43d031600325804a90703080300c84003c03203540e40540100300d0700c80341d0360144036000e030700d100035001303103180c8003a0b81c0c20301c801d681114454400f455901c000c900c0c502980ba00701412200c51030f4031101911303c000b1910000c0060b1a40f03020380000c10580300410b0381d0006000303075030803a031b80c14051a017407500303507075804001030001000c01080c2562002000c0c0441060905100014000e842c00221050924035003e01d07142c0b000c1c03034000700043c81000d004da0400d6003d45030101c403038801c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 794941672 1250 794940422 794940427
    0x7050d050c15070c120317070503040320010e010e06130804030609060b060a02030919050d0308060402070210120c140412140d0f200d081506270d1106 66
    0x1e442d0480070b024003030010740440300040001c01c008210b82494850303d806074441d80000590818041032441c81224081c0c0001c5091000c40c0c0040e00400701c005244605840303d44113030101401441c01c403084141e0b0308805a45413915400c5210091003180e4106502c0700000800032402c0e152a4641d104600c00101340d00e6860305000240070680d8440210054006d00704c40d599501d925009650340c000d03907840c62003440c100761a920424420f000e01003c4460140c40c07540c0c501001d8406440c003981c01460700342c00603000c000660060b52115208500d000c0291601004050f215040d00200c800e01c0c1d0700034081c00500b44011491400c03250543e0111452607a40340c2c05003002d03150181d07021a071846400164407d0000c0040510b0300028000c4150300b29503210101d944454031000303216000303490340c0e007400d030821051542c0d03131807141d40031507845558450001551603480c004104550b100380b0f800b2107000410800b850000102c452902c03d1158119900800380310507403180b080030384150032020301c2000e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 794942922 1250 794941672 794941699
    0x7031e0905060c0109150203091516050702011b0c1d060a0b0a051e03090f010506060a0f09080d082e090c110a05060108010c0804030806090a090503190207050d050c 72
    0x9400161700c1d40d5211401241c04080d00c1c140d41e001c0e41081e07c0b40041409001031102800f080030751498420f0135295040d46602c045208103039243c0d03220f020141d040250144030309a01d488841500c40085d841100d6020005252180c9400d400c90b8620540442006a50621186580d5015000140c0d400050400d5540714050300503603c1e481403914005070a508210540f502d2100d03a0040c1d0f1150340da41050b01c0c0c2e54146660080d0803514225440b5501c40300600103441c0c0c0501c10600c89880300d845003446100c81d5106e400403454030103412001c20024000c0010031503e000388010f0400b980d20011611101140d542200160a40c41d5018081646503590860451644940710400e01c4105c04416120301400d01c1c00c2c069100e55090048064960030705145008140c0700d920364610558150b40d80c28426180c074400c0010004028103101e1026844071098804180f00f4002040000c2507405030342d100b0520260007a04002aa91286100341380120700000421070218206400345012140d440c4080c25 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 794944172 1250 794942922 794942947
    0x1060f02030f18090709050f041517010b2d06030618220503030a110f031504110d0902010f0221091c0c060305060603040309050f18090307031e090506 66
    0x1c0742c0f1802d6520840810600011a0300101d83c2025990152002c84000175507605101c250345000702d111403e282e08030700c2002181c5200320440c2c00c0d43d10860010440a000b07000141e4652000ea1001d060180c0080e0f8880c02c4d100c500c0e125080e0041d042d104a420340c5820780000f004400554040b9015000410000e41069070341e034007140c08440000200001d00c009414800e589407c03c8070103400f81440c0002540400c9005001e0716080d04418052502c0c40da81d44624075040c40381748080c0c40d0041e0f00d49803040070b0518840003819111281c60000261892a400010001d8407101064400c1d50000003507092101c10300900220b00740300d1090800d644540b21b1000c5240c140c4100c017210382e0403c030801c40c0010440708a1102c0201d50762a0303020701c55921120100501440183c400402041c80000700b0007481c18981c080c80c191810080c282455400c25100c2c055280c00216142c000a420015440d0201074004440700700c110503104481480c1c142040015024aa96002d854031495021400e85440d15 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 794945422 1250 794944172 794944207
    0x40b07082b06060906050d0f0e240f09030714010209221d071511010204061709010c0c0f11030a030f120504120809100c1d10082a0c06070801060f02030f 67
    0xa9002085403160a4441494007d004224030305105110ad0900410002002c62030342c5401910002d010b5132400ca000c2c0e41d0b11030a00c1001c16035514a540034020744160b640c80042d454089503818524010301040d041c00d450444030364541c0500034005402640d1f424200015034102503d0018201c00759001c0240b07015a28001e05c0031900c1855800003c010900c10fa10001c11425111451600c01035515010701043c26500784262110002e4175140103480032030450035500b0703640b6020b08a004011615003010070304041c240f40003a00030404400211318030690240700e00c8501c503610079042045040650300d5600841c4604881e03010400d800c0082402c2c243c050200560300056818200140d05000d940500010802c00a40c2c0d490880181c1d003083c00d08205809082d10740107070f59515496516003c0c4003035000c0c0c0d117242031176034148065510760145071038000a10071425500e005285c14038084900a04149058112100f00b2000010354552107400105803101800c50b0031031980c4501e600884002c032403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 794946672 1250 794945422 794945441
    0x90307121101020d02030a080412200109051608030403021002030f040f0e0a020c10110903010e0622020306150103200702040e0304050303040b07082b06060906050d0f 73
    0x840304501600c040140950000c04400001e8080e1400182e2443c070598490050240c42c00c0030503054030019000504070078407042007942c1800e1060108112014024507030400c01e5004411f0707135499000303c00703000f420842c0440b03401703030103003960741d0941022405a103d014510009004402070503442d4451030017402a180d41007510403e00d501c0c4c03503035a07920000444940c41200000785100b0003040030a00c442c000c64202e400c0a400801603c284100041c000340030201003001214001d0103040c0c201d580c2801451251840c1c0703030040005080105501a1107140b14116014640302003071001c0050f103009c1401d0b41e000002d007805c502414003200069010307000b48400041d882e5803880b1400c210b405140098518a8001d0310104600c03c2c00301c4072580c1e01e104a00680780d05520501c0200810700700e0200400312244200080c1b410960403401a0140c00c1d840084450304645100491000d00001c4c4150b6000b4552460004c1d0311a03d0b0000c0a8810301c1242001411541c49009914120101d41c0012109 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 794947922 1250 794946672 794946689
    0x712080c03210f07030908040311011106011509140102120d06080d080115020c010206060d020d12020109020102100903080c0702060c07060509010e0103060803093003250c0b090307 79
    0x540400a11901850302c00300ca00c0c034500003600c03022999051280c850401c00942c0200ea40f031405045480e84400d0b0700003104424100160983d01c910300c1207052040324000c150703000c40c1c00c0780400801c0300585251495000000000f200c401e4440c003582c1d0000722814003181c1320345150b40d12110300f41c2900c0949110f4001650070312500c1c114400c8164070803200341c1220040c11040d5071410301d94004980712280050140d0040e8800c001240c401c1c9441c081190f4041d10041c825001812141e0319961640c50300f09072003002d42d42d110070500c29540c050240110030780451800b08802d168550703020b042001c1c094220403e03000e0108140c000c40d01c80030111010307101d10104441695644010003030655001003442030001d80c440c444201c245d4001d004960903648501c01460900075242c0602600b034510303014042c0c0d40d01e0f4610807142040360410b80c0c010b080d001c1801455a8030743c48000a6a0058182042040c107255006c014002c00c00501e001001e0f61080071003a61b41d600e440c400a45000f0b06600030114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 794949172 1250 794947922 794947957
    0xa03060b0a0801060f03170918131a0709061e050a090e090a0c0b040806130204060515030405060114030307060b03120f0d0506031c12110d1a030712080c03 68
    0x1840080d6200207001c072480391030483c00f21f0b00100404a0640940410030360002c0f015007075000d0100c01084a03a41c8180c1000e90311600c0c8030313a51680c0c09060404150003421400d01c40511014542c003000c450701030005401c01743c14400141002501031000784407a9010004007041a1070990f00c42c0500308001d00190441c060141803c3e08804d468001d484000c440105000b00001049500e032010342e002c86a0500103400e580d030300c1950020085070340d00b10032a807150760b5580205180c4c6d20032040400300e500e040b030303416101d14027841c00e6480c002d01a001944501c0d058081c280082d9000402c5541460b4411800700702c0e8140c07a030100385031a0040d1040141202c004c035a903d00c0c0a011405030084960104060041d07403944e800303058540c0e03061040b500c4900008502080064024080288100341d0910009800b030702203100705080d50090b0500340f40c0580c40c1c46800001010000340342d40c045000301c2c050061181350400101900c0b40f46100105080b81c00b065500964505005981160141091291 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 794950422 1250 794949172 794949179
    0x203121e0708060906040e030423040204030c030506070215041e080a0203090112050103080a1119141615030f0e0709020c10020301060804020d060b0409050d17060a03060b0a080106 79
    0x249005400c6910f80c0c040e10000000a903686420302880c4001616140514030742030030805049062880b0b400c04070107203401303480b2421003529284024001140904001c070716550851a0007418004041c0c1424115800300040e08056030b000c020840d003250380034540ca00400a40d4084125a08102c440500708040c04201d01c0c0013160040014603030020240c0ea1038498901c201619000c451003030201600740841403007243c100710300070030b03030343e10303041e1883d021510344680307400618445204055007115480b498002d104403140b000c0100c19090000f4002c0341c55881d00f0000e000c12201041d2450000300f45c0c8816202068001541c0a02521078080b0155803959888100e401c029600080c40340207584107c050a801280c02c610a6034140c800300d41c1e5400064071a5001c2094918006a090380c1513550313119081c07100d5640e0320500007954414405860391404a00000e042c40090b1411805000040010000c103036a61840e20010380c1e40c00480021546140340110300501c500d0341001a01707619180020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 794951672 1250 794950422 794950427
    0x901170c090a0c02070b0c060c0307020a0b07121a2d09130318140402070212030a1215030b0f070e0a0e150402210a0b0d0c0302030c100203121e07 64
    0x31010030f0241c00b10340d100c82d03456944008034815500707124069008803012958040b41c010056410403000d20459030b41c020f20351600032000724240c2d4004041100c425035012180c0240c001c0c00800403c811100000300402004600e40002c50718500c000c001e940710030707039040c01d80000c2d010905801c0505030018030701c0d055901246106916506a020819210400c1800e0002c2c1c1411b5007584e0010030204440c081403000d0001a41201c0000c83e0301030030302c07001080048403c0029240c45145542c88184c001d510490820442d042600e0400c1e000103482400d1021a541451854000d41e20218100c0c590b61b035148103d8006454403000c0c1c2e03100e0001d03800000e0b0011101000380c0030301c90003c0c1c0005007480403800c20040344105043c41c00b002004072241c010740541c400340c290707204101140200e164a080f07000140c000d09a0b2004454081c86a4414419410304010f95004031801392400400000307002d40181d503074081e003106e8014121105001840c2002c1801c1040c0060003207180080e03180c20580e401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 794952922 1250 794951672 794951681
    0xe07030b011b140a030522030f0b04061127011d0111030405040c1d0d1707050c04050c042903010b0d1b0c1209050a14040e0f010504020315060901170c090a 68
    0x7ca000e07101d244501c00c410360845014202c1143e0380020003030340c111040e545218142c40018015101d040d43c80c40d9801c00c801c000002088205d810303a0030000b210105001c91802d13036901d0059941081403240740c03080750001ea0706021034210000d080002840d2400c158813403840c4240d030022a041428403202c90b01c00703034104609802c0d40010024900800b4041414850b50ba941c034080a08040380c0c440c252112984070900419082d40184141d420303624800021409490060b03500c07501103d0001420040e11400036031044100344400e01c42005103a0a07600c03d4030318001030051a100080c006445442d41e07a0540c44000c01760942503203c101d52448400142083c42010350541e0a40e042c08003402d03043d80701d030342060141d420003003c2c4d040b0a0708040c0610070007920030400d0345d0031039590b064107940f416040100180c03580b240360001c100c52130648141401d108440081c68030509034034091110b03a82d44d017110b5905507021090764005000e0302c0e000492824040b039000b982c120101c4020b0002504440c2c20 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 794954172 1250 794952922 794952937
    0x9141603021203070305070f0213060f05011701052b061a0915030d1b050a210804030c061e050f0f0610170606220e07030b011b140a0305 60
    0x400c000020510100e0307a0303c034410f0503001400075104000580015a400010442040c00a801d82410510049400d0111074281e001300c0700040349000c00700829030f40f01c0c843c1c44031568032140346041c95140c00701103280460503181140b0354141c4400d40d03044050004003080d4895402050034842040100440000e8020300d40445005203405000240802d0040300d204843c3d6401400078000d04d40320250855500085c641c0703180f42c109540309a0000300798204a0310480c40d01408503003126400005480b075400d480580d0b0241400500c40401c07002c280c11200c1e15104580143c4007003200410141000c0351421640c1d0841203040c80d00061000d1b212240710480d10400c1c1c10415034a40d5100c22040000c40c05090000600045480e900c1d109015404030105410a1020704040d08001d424041b44104c1060408402c541c092101400c02c05030742444600d5400128a0600b0421501c10300300080c010102c495450140e40d404001d810700700915083e01754030500b450b5003654650200e502d802012a404240e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 794955422 1250 794954172 794954179
    0x50303070c0614010e060919020a171b0316051b0c03071e090e0111192a0803071206090608010518060f1b030114310914160302 56
    0x1000c514807190f10111442c1038807030080204071a540c0307130710400c1103981c402443c000d81c402d041ca94401c201c00c11070000d0180c02d11507844d0a4441141e050640b40b01c4080240000400070300c02c10102d480700c0b408011603801c11a89000b00e0f140488800c81550140310b031800700e4001420f1300841c010034036004219100415811025034030300c0ca5844248a08842d400000ca440e01220414100003a01c0c60764404200d00810000106545455646204090700241d080d8601b4030700d8214441102c59121403692407404d40141e0382903440000d151419010f02c6c0891004200700f40000210303051034002c3e0251194024203640a0103041d441d036910b8009840944a911403540c00c1001280d1443c03001c2180d1104ca0b5122002845256a05a2283d00f52500a000b01c400340407502c1c0e072511500004801507001c0c11002c11031010418400c03090080ba02001303004a07540c590064180342c5a00c0c14084907840f2000d00c01ca0104c0ea1107114203006080c0d5454011180c035612030042c2108020121200c01421203000701c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 794956672 1250 794955422 794955431
    0x50c0105090606090c0702010903120c02090703050702030f0a1806050d0606031a011b0803040b01050901060c0f1709030a0501061401050403111e040e01090b0c0c15090a050303070c06 80
    0x5601c01d56511056958075031040643c0c0c00110381d040d0100240c84024014580b15198559a4503010380d11408620b030240050503000581041d03051442100750001d502d031400300f2051902d00c0f4001e44901444d0070f41200ca100000310241124407802000c0180c0102260440e44a42e40d80005409a800036090319031075802c0100c00514180244540301c071080c000301054800c070324110011110203007458035004038060541c042c400032400c0c09001c1c0d4070480c45540c21540b0f950400080120044050780050200b05144c160742c4d00141601c4260202698030008100b09403490750405800343c0195411b468043c03152440080c14000150400f8048440d00d02c1e00660b1103810360011202445240006032100441ca51007041c54144400c00704680340441c80a00b40019a00c000941652844480401d40b40c0d1a80386507003e20401341c0c041ca41010891505c5884c3c003044040e500c1d104d1181144031f40408801c140003c0d4415014490042502c0d84141601c2e92480d00340d6001c0c05076100800141c1d0301901d403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 794957922 1250 794956672 794956681
    0xd0203010216020a08120d020c0316110a050d031e020f101b0203030705070b0603100f02070b0a020405130221090708160b09100e0604060302120a05010501090323070303050c0105 78
    0x2c18035021006900d86e2191400f6840b0038220702035400700b11516101c0c841008413034000e20308160f2007500d183c41240c003969011002001c1180e05041504154032a2818110250019410500100a81d0f00021664102c440d135941c0907801c003607204401c44050b010718004031400c072100d507225100103000c6c2400c0c980741629100080341e13039000488003440803c004119000128403036401c1030b90f1007000182100e26100000950381d09903100704202425003600403400c8000c0101480640750301c071030b54080c00c40c1054601400110072840003500907422990000b80094420031800c60400150040d00b902402420007540c0d0702c0d502c503014441c10003140140b850185961290446403c05c4800c0c080796a070800c130b404420041641080000541880043d440d40d83c101e880300c801510060415031001602c4000a488480d0704000080040c4c031420314240040c080d0baa0420070000980343c10004c41e6610315501030303030f020b800b001505122929108440c4000700301580000141614800d5800030301081c0c94 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 794959172 1250 794957922 794957939
    0xd020c0105130503030f0901060b07030503012909060a0c02040617060903430b0105040b0118060807050c030301090b0f04020304030f0e010212180f010512010b090d0203010216020a 79
    0xc096030000c0140e08104041840c41c10a064407e800c103146000004810b41d403202c0d40f440c0d56000c844203d0120b8008001040010b00e919150315074909101069440f801d41240304003010720451218900c9500003007200340099200380d50300c855259014204001341a2120018a80ca40318482880d00b00c0c85540c0c000b405042c4048151000002098201c02d4a8008440d8183c00f0180d0f1640000010000004441c40c10940e41d0303007041c1c86800b90465115550500d02400b00303454a0403d0107043c040a2444100425800241e84c002c41d82185000c800329100d0307071011101c511620001190307a2001200110303c0c8051a03002214010003118240481131141c01800103a000c01c1300c002d00400e002c07401c818455402120847c40d0010140705840104010100c5990741e9000500300d4220701107809c5400c2160300b00341c58032410403907090912034107001404e8020ba01d1601c05004003034580002141d103d205854094002044a500070000d40d03c5940300701c00004001c00304d8006a10815510900081010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 794960422 1250 794959172 794959201
    0xe0c03102a140702060702190801051806010b0309011104080609070f0305031c0e03042d0e160c0b01030822061d0604030c0806040312020405011e090306020d020c0105 73
    0x80440c0c45054048600848550b1250401c4a059800042c2000350100580e128405e100071160001500e4001c103040c80d0030f040c2103e800402c0110f08040700c04201c07000342e400191041c111400d007218507540b41c0d19803034191301400095105c070303400c3c440220300424991004a0061702c40c3c40c03550204e80020780d880018200d0f1b810f683c807025155070410040100300928a2980b0848070b40e211101040c40142c0080c0949160710991148220200740b180c00002c00c2c054100c1400107000205011101a081044040700e604002d400d42c0071249001101920041c05080c00342115074003ca0783d4880c56075a41031010550340401c01c807901c0318403090501d03254011001094002d842003951600a2210860900f506050015403103950010040c0000000036508407a01c40c080c2845101034407207824186000b521144205030a00000360050105000781d0f6400521790141c0c010024220b1503810b0000c0707060f00d003203003d0340021705242c2c000900707000040c00d190000c101c0b54524000030441d03640c9140307101a40c0c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 794961672 1250 794960422 794960501
    0x210f1005060a05220b09090a030215041e030c050304030c050f040911150d0e0a020909010501060206040213020d0c0201050711211315020c0a0e0402130e0c0310 70
    0x40035040456010071316103400550410303003000040c25154010000b200c8540c1250002510343c810320940d02007640c1030100103001c0d03405000d18005410140d4540c9120880480c6514100320100f140341e050500c11000450030780e80184c20789540c0c1d6124200604544031718010a4081d1140300d4149802d82428821000c086400c0100c982800c5680420070002d5034045000b01103030081800450004c0360107100c0d00803c40f894100500800400d8810f01428070001442c48005901d844010040781d900414901d80c485ea044038052035446690104000900401d40071040203490514806891501548082d0143c0c44035241d000211801c40700159803840c100002c01e00f01c3d00200f14507025401850003400102c0e14542c030401c100d03030b2100ca09482138140600d4100040c0d0210b00c4624a03801c1c001c1100d0050440d5940c0f240651605401040f41013001c08003d180c5164ad0b0810300b07020080500c0f44c81809100141070b5819a84030481d00300c06060000d01110300c1b0303580c00c070f46c902c2c2d040d03107410030000c41 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 794962922 1250 794961672 794961679
    0x5030309090a020f09130e0105071d0120010c09030213020705070b090a0b03040507030b010906292502100806100f0c1203021b0d020c210f1005060a05 66
    0x102e5442c0d0701c07124042d4009001802c6074020610225055a0742c01680001c402200da60000300507036415021400c0d02c101500b03803024409803231510700d1113481e5607a14070404402801d100725030708981742c0d140440781c1ca0b02d68466880d51070454810030441c0d120440c0d0007120700072a40030b02d015480040110883c404c0d610010030503400074600300600031100d809440322040051910041c1b6035903443d100604d80c07080f01d0071207650304900320500420120007081e07070140011000400899041c940e02000e42d01c1c0701c0b400d200590000c0d8611004030b400f04400c0381c1e01003041103204140c10790010300c082c10b0361241103000c0344664000701410700f1f550300c9508041e10459004060b0201240300d00000c3d150710800d400d152040250760802c2c0c001040c00f841c841040e011440d6801039035400361420510104190b0203100c806900308020010106500140b90340000004503030360a903400d01790034140c1c4046882d00e2805050b008224200d03000170400305001c12880d41c100014040f40da81c15042001070510742c0601c070790 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 794964028 1106 794962922 794962939
    0x190e060916060c020613030c060906033c1103190b0f0a05060d1e020304021305010f060c060e0604140706090b090f01021216030905030309 61
    0xc2200304403500090241c10903800810b44854840c004c0c0c0300e6040821030401c040402543c04006503400440701482d079a441c0c0e8080c003c2170440c07190750b005c2454040821012600106150844c0d00e1002c10510b0703503982d1101d80101030f01d2403c603119025039128000f40720305076240003d40c00382400201c0000510040b8409138261404c61001501400c000c1c201c1240c0b64a0b642000c2c0140d50040750015111700300010450000d001c210b02440c80120058580344051324254019801280281c51041c20710340d104c160141552400e101d42d81b802e40c4003103802c00405108421195005200c1c00c40411a4000c0d60171107450080151411381c4c0348100340c107046a0000b420019640203020a041074289245007804000343c5014110941e8000c1c0c1c500401c8020b42e078030a2005d030340500030030b0324140e85800e101c10000f403144510042c11400f141e01d00f10301140b01c0c900003065500001006000f00c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 794784172 794964028 := by
  have h0 := BRFrame.cov_init 794784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 794784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 794784172 ≤ n) (h2 : n < 794964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
