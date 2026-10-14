-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2162
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:50:37.122351+00:00
-- url     : https://prove2.me/submissions/bda26621-b81a-484a-bb0d-f1f045ee502e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 388669064 ≤ n < 388848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 388670314 1250 388669064 388669081
    0x90d0605041506080309040c0e0d05010518070302060a080402130c0206070810081b04020c060c1315121508060c040e060901052101110304081b061021080a0206 70
    0x41804802c203201005a10b0902100640c0d80c0180e11415124030307210307001104400d115000b928401040640440740194092400b03d01030f00085a5100c00c242801c2c4d007001c0400d00015401d02100d8020342211325192103c40d007202e124600410a0340c000501c000300511010307961060b003070f9808280d40501010b0500700c2000708a0403018001e9060140f480000307000c1d0440120300303c6842d6001c10581ca602c00d03180004034002e402174051000d414014501003010750818080180056501c128484170190749640c02050311040c405050300c0003d03100581e803801c070903040e44641007500111045680035551174482900d4440c048a03542407203440418100700800c6407100c415002803044410590660500000c00c400003203800c0d49040c0c01d10105a591103031202984108282c0d0814000c0f166030b85407506000c5200c2d03000c85131345412b9005120030b41010110206481d4001d1058000c82d0048525249121501c245109175108914090900200000e88140010590107506401034141817424801 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 388671564 1250 388670314 388670333
    0xe040c02462d02091e0105010e04062301020f120a080a090c0312030b03120304080310320915240c0a03031506080408030a02270906040218060c03090d060504 69
    0x2285c105d08040090300404981401040c078155a407c4c1303406001040f407500000c02070850342c0e00c01d032141071014500d02d20240014400900100d0203800705c54801c1801143e070703076640c0745c1c0064089442c8428400514422320400c0d229401203104140420342180b01d445c5c43c4400d42c415402100c180030300b0031604404a0300342c015000b002008130003901c40c00741c1c08118a203103440014001006004008005401d80350400b406101902d500c04506074050282000e00da13000c19032691014626030103a600486500d00010800c3c41800d01c84d030b01c0c40d018036603c410320003043d074411205081c02ca1b0300c1000ba0722101190024102c00010b100081007001c800f400d02804a074441400400b01c0c82c0345203414040280c008603440d03002a408400c007556592440781a600070f01403120501d09076030b08010062018003000ca02c01c41d8450302207a078225544c846004001c101d2198002c118400c000800003c01c00e890142c000e8413083c00181d041c0ca00c0e090741000000c02005c5100c404440e540e6440c41400f00f485180c20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 388672814 1250 388671564 388671571
    0xb0108090a0305070b060111060f0f010e07020a150204050414040606060302030c12130b090f01060e130201030504020f04061d0702010207031d010e040c02462d0209 72
    0x4000c1c001200c0103840003451403155140180610b0b484402145031644a0480c0d165222074034025506581007465855003090b009442d05004004410001318403403c80c03100580c000c0d40307140c000701810044d41e9107203890700402c0c000c01490580e092200003825204c60092034902c1c1c0e04001c95940b146030506d4401c040b58115042502050300c18800c015404c40c40d002200d041119400740300d1070300e5640b03001d11080040350072002810281e01805106541c0780c00030b1004c000341090700090000039154014040c0300f902c210381d101c480c9600301c0031403409940a07902458000380007415440e00000c440b400308080d50f040380e224500c9561000c200034844084122841c4c0c01030120710003985000010344008000c04200491004600c22040d404c010a80c014050450954000b0f07000307005d0000c4001c0c0c040d4079520139801850003802018005558801074a05411000c540c070b410486014140c16610680e9001d4090200e450700e041100a550b0445e904107205900b06d001c0c4074040c1c090b02c0520604c1103824015 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 388674064 1250 388672814 388672831
    0xe0f010506010905130e19030e090403080106050c0c0301090309080d050a0e0f040912050301060e0109030b040305030c070c080705010f0e13050903090409110306010b07210903080d0b0108 82
    0x1c0c018940c1c2e00c40f204000700e40b021549541031010116003240105521980c1302054454004203106220805501c140c89074001e840702d407079800ca94001c0c4405020100e80050000307151703d00500c060350245014082c0c880703080088892404581c4003281c00c48611003403c0d8040740b20817404010301c110070042e480710210203207000390901c011200701404d443d20050490b84202410002d0034a41c0e10745074004000303a60032080f00140c000a02d072001c4c000b0b900a02903040000d81e000c030f90400702c3d4020385110741140e41c009540102c03661035840c11541c0703403c00303859140307840c004000d4900030078141104000900b03100d0010300601031801001506070341803030100d80180110b00fa2401741680d00e5030148141951242401704030f03079a41c1c4841d030342940302e1659002d41c0980f0304441003080c401c2001440b0421a81a41140d000da601c5018400301c0f402005002040881040e01c1030140c060f841030b112425030418107280b003045c0e481c0da070365852a4004081c08140340c0c2e55040c046040d0f6074000c121a070004100c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 388675314 1250 388674064 388674071
    0xe011d070f06021c0e0f0301021216020c21010608100c02011a210102040512070504140c0a0c081c050703110f09091b0a0503090f03131401020109080408010e0f01 71
    0x50190781d40e07651440d40c3c0c880e051000382e02217000c00c1e8031820350141c1c1480d0014021503440b88000e4a40070b0402d0300780e070615400c54459100c404518000a001c07410030000800310490311900c00c04041e0640d82500194115540b10700d40010914401c01c40b20428840c08a0041000b440d0610000c1c00c681c10802c0950641e442d0140030360150710364012504d42400c006e24101384000420070140c0c0644115402076400c181c0300c8400c64885080410b094080d80c40c21901170105c6003100d460589411800d0f1007900f0242010006030007458000c52002c1d9840388160302d0030b07080901600315071302d600c0c0c190200400115142d03010424043d60522807203508060100005062500581c044441405840501c41c0200c40d0080031580c3c0054402944140e120720000903542ca02d421003005000c0d401c10340b403921040c41240190580800080182e4a4078026030403c40b44041c5845d2004071443c030030101141c19956990820000305084c00000c00190840700c0c004900141082404c070f1600d501640390306440d914 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 388676564 1250 388675314 388675333
    0x60d02060405190509011707120804050607030c0803070f020607020a0302060a02090105040f151b050c060f0d090b19020403080306040209030709020d09031101090b0a0e011d070f0602 80
    0x440000307403020398005645240454880e090352281d80b080301d40025030312040040001995001d22010341c58450fa018068401aa42d03c0c281c030030000b981140c00602c28602800188038a040c440050004a40a0b19000b9035040381d43d15002105d40c0291750110010358643d00d0b000d00e6a404010440d00215640700a02d444001528001e442d8030028010040007500098100c0043e07205030143d40c0504035251390100d14540d00c40c651886100d291100c9800b080e400041c01d5145a580d810010040750440003401d4404180c10800101e40d005d220301710500d010600281d039480340705102c1c1d90b02c0c55201d003002e04100e0070000c21628880c00000d80c004051401000180b000a01e44019203401c00f0042d2009070329201c8040000c0c0c00e00040d5004492100c0c400320700c4492804080e0000c000c9603029850304044c040c0421403503800d0750704252003e001460824082020001160b1110381c400c00d03e00000140c0d05034a01819000c0000c10440b5210303584520000e10080850800009c010302d010b00082c52440e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 388677814 1250 388676564 388676569
    0x118050708040f060e01150b0703270e131505060a0510050d0504142a0d2f1503010905060d2004090b0a0e07060306051c0f0501020703020f06060d02 65
    0x1008183c0040c4071540f00c01c2095a10a002d40080b00c11104108070a980a500e0700401011500f20784c0f410b400103034202524006090803c10030481200100880709141401c1c00c98100c06064080d0040c039001e401c500401c00440c902d620300551810344008045842d041c404100043c08032a034015900c0307840c140410f58680380c0c000080b10045807080001040700d6031181042c03d40102d1540c40e10b4280d0042580b0713510b441000040864514214810036082d025840062162034402141c0043c000c42d82e400c0c1d10600c8207100320300844000a088030000036081e040003c02d030041ca02c3c02003000524400300050045032400e019180d8415030541c0c14016820807529000d80c1c43c2021102043c91b0782032020313808129112038200701606c5c0e40003c4440d0b81818545190001031a66803860b44290194071800f00b40f4a21a0245200300d0708024810b40411000480d0030009607880b00b02140c2c481d11800203400021428000b9108140c069000f07410170f0140f003a00182080c1c00205a1072052a5140103400184d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 388679064 1250 388677814 388677833
    0x1612021201060b041e1d041e0f0303050603070510120f181515170d03110a0e030a0c120c210b0a020d050114041508030d0b18011805070804 61
    0x440c0b2920001200711711901c011607800107a40c01595003503048140c1c1440e48104402440d024a100303110301420304a51a01d401c42040007a000100f110000000500202e486500407540216004080c0e580c1580d03608000b8050a034031800000c0451640580c4011691891103401c0d9501003201092042e20652900c00c6110b03940b149009000820444040c2c03160442c0b035000e40c65849030302d0b203c1c2c1c64141c0c540301c052014032160355800d0b6051240e9510081e00912a0041e9046c10180160b5a414107a40c5203045d148101500305813034240c8a42800000420705e60319500000f40556410384a8000302c03824900c500319610307005201e2002d24071000e22110170310240000d0800350482c8803030584e500c41000d02d40192103140282030f002402c0100101300c083c8091040c0ca09004102c40800c12140d05510480c92010284501c0340180c0091142c0f180c650440e0300001080000105185000304c401d0000120211080e004240c0d50040f0081e0425042407500c2020781180303150402d0352961805235500141c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 388680314 1250 388679064 388679069
    0x507050105071a0906100603090b0601031a091603060b070302060c0901090503011b1215030210031401080c151c0f060b040b07020f011119051612021201060b04 70
    0x10828000380040500818024900d015024681c0601d228200251607980d10841501d2120b101b08070190300041c154000c0c8141c0b8601c4d503002c00c0d010082d903035590056000b01464440205080d040f220580e80c60b40d16881854410b400c02d14851580d2030708040018103ca40d150004401280200035401c00300b60005111580103140a040660700d0032904012250300c121503102940644c00d100420418011521052141000e00d82d1018481c1c10036100322000e450a000613050081048003060016042c1161014480a501e0401150a5030284c43d5901e01d0803090340b003043c442d00455003045040c54014075000c50140d400194030f09194039051a8160208144000f80a182d0384070207560400c4100d802020041c8600581691103c0e91140010595030107a90b007203100b03195071100103103d5800b0b2145001c0d180450300041003458451000c031400340c59245016281131088500d948006480312051401608607401f600208001c07038818000400c1d00031a1000140c1d0400c0802e00ca5a540d45065604 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 388681564 1250 388680314 388680317
    0x7201014030901060b0c0d0201112106032811060a050414040906060f2c0f0408041211130b060a0c021c3f200a0302010e0c030a05070501 60
    0x6480e02d500c6180c41c01024182d1214a407440b010825030034050000ca071200340c0c050341d500207000c4031035440c00fa440d00c0e200313842000000301e0a5584205020f002100b5059201201400300e4801d0b41c89849200b0059407510101494035592180d510100321540503c0b402c20b1400340c400600703111200c24060200d00540c0900b00481107420404041c07039540b07801c03100010707400c884100308840e118a1140707400b81003400703030f44810740340c0c02c8052000b4544901212529000c10000101d15124102196020040075109440503c1c0130b010114801196180600800d44505060001c181c0020180b1241500316150b54004500e4a00d29400d43d407140c80498807802001d24145100c05490b1000a1031911440c9001002c42d01c411800801c108e150080011084035205401c00f611505140c482e2440000008100c0c0c804030312240440010701418500d25003030b2080d802895840b000080d094a440c1c060082640142c3d111504030311803d1061200e81c0100500303034058800020307151107841d0360710100c0c8582030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 388682814 1250 388681564 388681567
    0x3041a09030a060c052101090b030c090619152037051015080703050304030b0a02040305011a0f04140f07030b100903030212120f0c0408010207201014 66
    0x8070007072103034044800000212188191007000b0100c11601b11400340a4043c40da441d041c00e02a16107000904001c000000501141031542e0307040620840d1454001c58081200b020301c008126500e117150903062000c00b680c0ca0f00340d14900c90041e0103000703d52500c2282035402a08420b25550a100354840080d0f03c070500c0851000c52080486074a0500c0050290041c0140742202005201940029003062001e02000911944810200307403944114440104940e00030442000002d5a01d0a1992f100d40c0510005003041e55940f195406e40f07940031801c41140041d1208418280790103c04003a03803100c1a20304200d0340310b01c40d025159410010340384107554041e4400084401380b2076081001c801c3c030050092000c0b01032142000e89055114003046002d40500b0002d441c42a02103001d907840300d00100c03950981170b00c54412200c54924003422091080700104004102e0000900040c10028400c0c501485d84400f07581d240410b81e03a20195130b510502150100c2059030754412803045c0750420398545c06 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 388684064 1250 388682814 388682831
    0xf18190912030c021e060f010504060f18090c080a1a150105030c070f08030108070803030708281109030106050d21030b0a0e0a0b030d050d02070c05090903041a09030a06 74
    0xaa00d0188041c84224040c40c107107144c1c100000021039054000c1d52540c1e441f0b44103907212410041642c089000b40d0300c0700341444004105072030300301c00d0003010002c40d40c800040d201c2203034070b80500501094000f000c0c0d9600241c40340d01040840300e02c00661701c03012500b4184a04200c001144000b41411420b41004000b00100f800481c45a085804042c0c0c09810401c000c2e036249403942d00c6401c00d11548845000340d510004440802100300c0b4410b8030a0390700c442060b81c49400c80c031014040d1070701d401c4c210a40a0b510084025551050701d241200101038207444072a181308160948016400180c01449104249000201d42c1007a40c20a1015804c03a40c60040c0f81e028200e00404060041d26400f134462000091a00f0820210034000c1044010a11000c03d5103000d05503074400240380c44000580402c50b848080d551503010340704051050810946255495001034901c82c0181d4514072603800001c1c040204095101035007140704a55918a42002c49400c00241c94081001c3c0c0070301899119040c3c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 388685314 1250 388684064 388684067
    0x3050a0e061306080108060a06060e0907021f0219020a020904020f1309060f050a0b0109030b09030f22050d03080411120a14010c05070804140f18190912030c 69
    0x5550200030060040b84495a03201d0009160820a22621134540031301c0c40410380381c00301c500070f210560b550b80c0c4802e0300c40780d001014000d021074014941011805000c410002c900e412105c2041140c10000c4056207502c1f1801c86c1e894841d50708110311056501907100040182c0352240c01c268459011156007080b032660704017040c2a50040003010f400c051610300132804002080d48080200200c1c103404101c00c0e0303181240b0100300c44e81c400b840d0b40410f003542030800015402c40c0398030b5800000942568105050499003070b030b19801050701100d6020092950b00d0f40749101c0907544000b40000c0356042d80082e41034070040c00c1c2a5014202400b2300301c020503003014517191414250b0503041c5420480301e10b0181c90a00c1459901c840100913015403c00300c0b484a014820400d442d074250300444038a02d400d281c17210106403101659003480e0032058503001810203a07581440e4030980d80c80d90fa81c00000d860420141642c0d000e600c106144194a8034031907002099400402000c0c0710b2107418002141841d1800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 388686564 1250 388685314 388685317
    0x70e0118081e0c10120f05090c0f030106080a0f0204050a02041a09040b0a06120b100203090f040908070506070908070b040302121e0106090f050c12130203030304031e0c03050a0e06 79
    0x280e2070b0000c2d04604c940d41076540c803000320215250440f03410021600055940400d840f01524811500e910039640c4045030300c0c1c440510305100e400100001961555042241d0408141c0a000c0d0b035500300360400b0300107601b0140a040c0c1d200100c01c804601e01030500e43d11902c0308082e08140d504044000c18030400b19280c5a016081260004040048807503a030b02c40101101550401c1d0300c0000c2c00e08500501a050420000c0901a80e0350059404c04d03020000b40070b240401103005540c000d8640000c1342c04a80d00340001c4c4800e50048001d0100e900d050750010700718440940c044113507580044410842c01c0d03d440e040c0c4080d00c0e81203608500400050b415a4906580100d0013608004403100000d602d090540c00341046900310b8409001800c810011300084500842d00c50348200c104004003044441c6044500e41c0c00100c0e01c9100c0e140c0801900481e14542088904a000c194010350700604040c04c8102c0780b190104034600303804030303c0c25540c004016001f1501135200340030800d184c1200642da00c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 388687814 1250 388686564 388686583
    0x1505090708131a04020f0109180b0d0614090f150402060f090901061d0108150f1c111c020102070303050c0a050a1a060a0305060105090618070e0118081e 67
    0x2090010805580c4008076101c10381134508910401c40300c802d01c40d02d5401468030604440500030b002c05010b1100700d01001820780f00c81020707442902d021814001500d907225071001e06042c0c600440c1c05123020000c0c0341c941007200c211424107074000b400407501000b4090300180c1c416030503180d040e26401000011490780c029100300d150701c0b100381c00001c20125403003218541281c58001d40650124441e200548078010203980b4920507400d11488103040f82031510b00075014190242c909510b80c08440b002664115003003604880c209030403000c86200e441c1000000f58022a01074080c0224603080d40017070750b5420207100080c00d108000c1058100040240420154150004140d881c501414030f0441c3c4480d00c0c120060641403202804100a420f02141010a40303030310000411403a4200410003100740c13030003014158002c03005851a402c0c0442641c1c003500409141e200c0b5014070580c0000505002c41541c00c040040e1000c220801c8207413000100c0ea0384c1d02d1182c0100002c1503400054450600f1880d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 388689064 1250 388687814 388687823
    0xd0204080a030e13020a020a021504050a18060905012103090f060201020c0714030a080f0f0403050a020301050c1c11040b0703020f0f0a0b0105040b010903050f0a020103150509070813 80
    0x40c1c0e204401e0540101242c4280d40c0200d4005483c401c010940c00228000d6480350001640b24035100001814051441140c06469a00310b82c2070503075880000700580d0b42c0d50070075141c2d07010011900c6200001400748502822410906100f44d40c140f0402c004440ca4010302420402070b1200254141030190501d40007902145a00292041c1c96000c00b078042d40c0407100d0b200c00d511812000250045404c0408040e070328004002c0c0409100e580c450b5105508001440e040c42036041040d0404100114020304c0154480c2000d400b002185004050031035200414004202e0420041402d291000b19800c5828080b541c0000405450f0074901d41982e00881d040f21415a030006409428540c00054040c03001d00d100302150307981502000700301d4a8141046004203c110f442006000c5441c00d90041051054107240a079142680c0fa1903a42c5024041040c1070300070b410540c40c060555034580074818000d004914440c1c41c070b0b81f60101181d080e07580141108100441c1c1c0005c45d14007044503200ba44490b130071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 388690314 1250 388689064 388689073
    0x6031801020c03071b030c0501050f0910170f0411040c030b060f041e03050615010e100f0905010806030d0c0f05010207030305071b05060c03060112090c09050603210d020408 76
    0x182c1d14241c1d01d81c440301d07080d58001508141030030380100c0245590103807980f2821461096160100650b22031f080100b00594005041c840380c01982c50f283d00c00103c40c111340d5121080745001b8401c0301345250003d48480580100325007040080341c000d00084051400c2540d0008030f81407060b00807002000c50744030300ba9000000140f04402120300d20047c10031780b4000036611000034042d80640c030001a0320b12000781150410000200184044410b40c0e24403e01810b01180150321a00015482c41c0c942d061003020462a0568400450780041c0c048003130602030803c4152410140002a40c0342e5901d01400104143c0f06850410042c0c04000741810f181c1c1b00000f5500d0784824540540508011200000050801c083c81d07402501040d070900c500c0c50304403000d081151a80b00d035440855100600650600030741030513000380b20f080d42c400e03c20080e021303010901450f803d00000300c0550b0b5025180603c00c0c0d03c00c600441038403090741d000350030351840208200c0c0c3d02c811200c50034006e8000c80d84100a01c0c002e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 388691564 1250 388690314 388690327
    0x509010513090b0f0d050d1d09090a0507080307080403110d080c03030403170f131b03050f0d0306030803010902071104023106020c01110106032406081b0603180102 72
    0x20359000300100200403544544c1071003400090101c6507619901c058065032244c0e21072101d040c0203600d41032803107180a00c2c0f490207040a5000c1740810400b6900e80d086c5078003071034100d02400b5081c48600085c041c000040d62409070142c44254543c019400043d02590306030140d48041c4e510f080201041c1540000b0158945da0003070314082c1c4a800c112019008a078205c0c8418880d60306042c00948280c6400e10704420350b0301c1c1e2a1842c03a0070001c820301110190800c101e02c001b89036034510040d008500c2980205011030845807000c0c1809002c920f60305c24141848020300c006100241603e0540e00380384c50050702d94840d410040e905040141613990080d10004510114000c050700341e80c0c524107001c000303040b862580700101030407413498811400140c02c94000e0380c070590310400000d09149115000811b00307680b42e85a807102c0301071401d0700030303403400414228645040b000d0041d90001d02d6654080c080081c212a10081c004142d03d450904c28800000000d248a07840780401452500e81c1d07000310b40700c20 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 388692814 1250 388691564 388691579
    0x18310201110708070f1406040501051204050a240b0d0c06050a121401030201030b010c051c1205090c03060f0f060d020105120c0a1b0809040b01050d090506160f0f0509010513 76
    0x40060003043e206d4000d070740b4100414181031089604907001a5200d80c40c01002c2209901100341c0a0701c103c13428010410910046030f0905040c2c55034017600c1c80b0341c510000e9500b01200c122030702408020302400302110280d012500c00d041c020116002410104c2d40c5044500d01103034090307000d08402c0c0304589000c18004040e035507150b4083c10307640300ba02e04011220717074400151150a507010000300160700c8504011260041030702a03501c0903c490603d09108250110044141c48003141c6400c00750f8041d05a00b001468200400c0f40c0006012000c554142130065003a400e0580003070406e4050404100050304591060b000c841180121011019413800c08010a917520707800070201d1000a1105181e403200e03209902c1c03421200380e900200e45031410381c1e194180400b9024504015041c08024843c0c595028100d0103072400051007403014044034581048840d8110110f207009000f0000c0c1d0403c03609030160004c0380d01550412038108151201c0c04070340104d405104100b03503031b4030030064904000b4218 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 388694064 1250 388692814 388692839
    0xa0606020106082d0601180b06030603100209010e2d09090303060405130b090c03100204060507110d080d020a0f0806030c1201060801020a180501020f0a0b090c1831020111070807 78
    0x403e0540700c107100301d2410348c04200541c04203403003265154100c1c0390000d4130648240d00400c2c4404060511220100b0408002490502050010b0740d40e401c0d51900700b40c003500c0158581c080704400300e0f040e10b060306251032056982e0200400c1c0c9030182d0707550f201080080b0072040f0120425640207100f0b40c544d1034440199900c038a00030ba9400c4c040d11882118003184139540c000d0f18241c0d0300a81c0c40c9414002140c50785501c0340c91111203650007102c0750b81c075240441c040c2d40040c840004a40e40159641520b69402011301d48c00b02c250700104411213091225580d8046550000c41d00308441500c80a0074202055004192541c4441c01961000903d0414990040791079880320341d8545204080313594400040e6100d200c2d120901c0050340102c6c060300700040e02e058013260080101011030310224101c001080000000b020549036801d088810824182800320309054031040940c0400b081342180184000b900810b0b040003414030484a4220360201d01c2003000313000034160142100d40f216500d071144c0604 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 388695314 1250 388694064 388694099
    0xa0e01020706023d0c0206070f0309020904060504052a01080603011506051e0a091404060509060d112806140a0f03020c01050703050a0606020106082d0601 68
    0x141c0503412001460a00100c3c50704400c00880101c0c4d121641c03004000e0343c08800b407458904a441c0780d0031300d4a1404195104d2010600d003241c00521030781c140654068140a40342c00020300309418103556100586805030620340051340720501060980740d5152072420940b45000f007070701c0c60940c01350005880b4104c038856020039000f81c94101d11510342209050030780d110010200050401c00034200401803160000300460320b10000c001039442c0d941e10003401940d00800703034840018244941072008115428607065111300c120303800c0001500d0100411044140144868820b142c020302d00c8062100004140005080080018841a00d0045018108492a02151b140220004000c2031960084100d80240c9240d64115810100c2202040740d00707082d8141c2e08002c06400b80410820a08240940c0d4005d0a15840100fa2441e040c4800f0080710b0340c9034014021a8145101000207000125000c0e0f180032403c0320a44071400000c1da0b0588804400280920900c6040000940d400c020903c142c80c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 388696564 1250 388695314 388695317
    0xe090a020d1d0606010c02060d05150901060219060203070302040512150f1005150c0105160e0a140d050321060109060804021c061d03122206051504020a0e01 69
    0x340100b2481c610400c04101035140da20307034011000b040341c4d5070240c9805044a440109450f01c2d0588441000090710404e403155401c90b030011001308458a0021a41c40c050801440107100142d41d800040203d106407400140a2507400000301c0c1c0c00501c00e404139005860081c4c0000b0109050810455407880d514100315807810014012812140380100264001c04001e145904014203040400030182022002c40900440030000c07982c0c855000c4c01401c0c810b800c00e0465480307903454104040c00406190800d248500ba401e84240240380e40d601580751100001d0700d8072505d8100345d10b80b2a01e10b108041d100501c881500491041914801c407003644108001c0c1d9850165641c0c80c4000e403003080c0c040e01c0c002d6126035801c00d00d01020a40c0e0104441e5a0b000302004680100034828102856480c00c00818080d000010040584150441d001d0b4121440c02c2104803021242460200d120704a1900181032545540108140c0c80388404030945d4035a00800c1199a56690070001d00700c5082000804d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 388697814 1250 388696564 388696571
    0x2030c060f060303030f060316060f11030319053117030412050c0a0c0b0924030402060f13090209040509011b030905010908132103021c0e090a020d 65
    0x31198104400894080c007000f030019821600c1e24042c2d0210018000c2c02a50144100d100025541034140c80340380c0140200c2e140d41d00c0d8503000d200010543c5440c51780b810250b600810601903940b00e020344038051680703001d100040a48402d0002042440190360182815044c203001e00040445600c517a100c7c203100b201c655003134160f1001c94090500046a01074135400050812200b014040e40042c00c10110315401d941d50030003290b803107004e100070320780105200d5080851411844c1c20402500c4144500a00c002c01030240c5000700203c032448000c0c0300074000c0b2004240502c0d01c9a09030155030111a01d559004400d94942d080a402074201200c607a00c1103040101190b440281842902c4d45074055402e4810000200c46050b0040e02050b5400c55047d07695098040c0401c000760094507065020840b0113a52900c0c2000140c20343ca01c6600e1b00b00e4030f000c454100d400080e000a104083e80115940200030400c010009a0714048c6140e151600002020100900000312340c0c02441c1c10304001c042003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 388699064 1250 388697814 388697821
    0xb090411040b0d0203160e1b0f0f071205090f010206010e010b070203100c120f0504030c1b050a08030d0c0207120308070512040309030c2102060c1905100b010c0203100c021c02030c06 80
    0x10b00c4004101200d950103c0c0802c20a040327410a00c0c024201038941c15803c1c0e2500001e5620350020f0141d03503982c0700015001240c00055841c00c8660b4046941092000b001c0650410881210100043c0f00300e0316007040c001184000c5480a0002900482c0e400304200b04282d581800540390000842c40b21000924040d10803031100202e204003409150160785207070b0801800e98411b524283d00004100e0400e002c40301c00121a85c0b01b00c0303038101030a0300001450b103c0b0780004206040c0e400031882c510554002e25802e01450361080d42c030350107058243c50a80030741d464001e0107845c5889010000e84064145c1000c000c00d05402c42c1e00b0348103c074460610440742c40e580c0c030150101b01200c46800861110040381440152600c00f02034a8103119100680e1070051055601000002000300121480d0708181207180100c900c510030704098041c00e00341650501c16603400680c6504459100b1201c2558691506191510030441c590100414131050000c10940001c040d5407074204905c3e25265100b643c000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 388700314 1250 388699064 388699081
    0x6110c011a04020a120c03061205010209180f150109030b0c091201111e040e0f090c0102010c0c030503090111033102010c0b0c0f0706020d0b090411040b0d0203160e 72
    0x88071319101c2e456035080c0041d151140e0f050090994005030300c04040c0c44503004164111010180b140c4144a07200060352200001d00f88014075880051500e0700c100708004000541c0c480c42000d56118030715840d003502546030300340180c407002c4894201801700c035402d40c10030560500840040103800001c1b104400b005910a40d030324241c0d12a11100c90311140d0520940c10551000080c102e03030b0750b00d800785003810b09403241c0c011601a5170450706950300309040001e215415000340100300341004284000d00024031a50000b8011f00340301c000082c00c100000001808060080d0b000c0f80c1c0c1c03541c0c1f80d882140c0d2030a215580030300d61910035074040c40104101d80c05001c00c4240c0041201415030684401001d21b08035100c20040c2d003c000d1040205034003c10550621161410081040310310036030b801078540307403207550210071180141400d50280c8002c0b014000803960541442000704c008a6022a2003001140814020149014000e400d17129050076602040030881d80381080d180c0d8050520320170b65400c183d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 388701564 1250 388700314 388700317
    0x4060e0f09010510110f0f010213060c0305070807023106080109050705040213080a050706031b171005041d0105060303041805070c15060f0f0b03011206110c011a0402 73
    0x14140d40120131203194100740c0d01492200c081542d020050302d01401d001c03803995040864140401426035400105101d5450321010329a000e40700514004240181641c0d004e40244110f50001c2d080740004a07141085540781d040300c5072408004408400ca25840310300911050306250700c00c00c441b50803c800410600300500c1041401d81c0c0020061040f030345080b0910000f9801203100941104564401040d0b1040400c14103507050301c00d00c014107459203011402411500bc0907492415112481e01d59995607910000c0150b80f903c071800040c41c0e80e102d80b022400d41d2540c0350f001c10741140c00c0000024000200c940b141d142032429100900a1744c0c0d40004250300c9120b50f006055601403900101200000c2036440154007145a0902e000e2500007a21072000300740809600c1400319458410501c24540c8540524006128550fa8400d03a00c0c10155080102d000c14081d1031410300345059044144049a04040c020134161014143e40d5954818241e01070130f80e2804002d503010b1114080318003810a4130 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 388702814 1250 388701564 388701569
    0x90d0c2d05090a09020a060f0201050f0106051b010f1401030605061c030c02010216090e0c03120f0306210724090306050709090c030c020705030c01080106050a030905010204060e0f0901 81
    0x240c091a50a0900701081440e440280600482a0303403070030800f005071141a81030006d0400b0391110070310003268110007070035280c000f800070280304840d40040040c1a08401a2103504250781c441e100c08180001105c0c0c0101f82d12358074944464105508101845a0000c195068134001e030010710030307070395a44103200404c80d40551184400a2166146011074844d03000b00340f9083c0705206440c81c2c29040d40713071b071140050590031107030304a6a0350304103402c2c0440401c030f403403414075003030703002d040c407001a092000d400d405065001c1002590000c00035520350384250000d07155200785584182005010b612035a62103400d805a100d001550710032150707841e000350f04030a00003c0c1c960b50316070b0f002c1c1c10b550340c14000d0900500120180000381e800411210054040d41c0c3d0309504a980001c0c010440440c02071400b40715a10150098228102c885550b99010600c98103503101c0741402030359042c0c02c8038118020004039001a000b5480400c0201e98164400d822083d421012a849140043c0200c1000860202071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 388704064 1250 388702814 388702889
    0x2040302010819062403150501020d0f0516120f02010501030b01031e0f050c010f05040b04030308091f0b04050c0c0606040b01030b0603011401080916050d08090d0c 72
    0x500011031000f00c0500c961560f01e01c0e01000300d4050750f41d05104210b440c00c040407214050b1403001201219505114461908502241d1625501d240100107074030760808450302001c002d112036000c09514002c20889a00c80380e40c03900e62900d45054104034041104200c10700d800900c2180c1045a800e105020b03c0303050300d41040550695902c0c5603102c0d603211a41e001c02d00901c0e0410380303c94001c42e095034003108410f03008401900c0301e0a030000004145025641004003400018041400b19003000c0d001d0f5010b507070341424143c2c1c0d40e884000c0054500900d588282145480c0e002c110907000801d0380104200316810350301407016458401221120780926014051507510900010340d081c64242c000da080b070381060400280c84002c40000c9040c03940309030441c04e05069401803240307065078400d40ca0303603003c0d049502400b00c555030500c0400c0a40311038491a4451140114400c1c21320580804903600e0380c00c02082c03441490b9035480c207064090717174510844c00c0b0401c3c07143c0390f10504d05464031100f8055492 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 388705314 1250 388704064 388704077
    0x150f010618180c03061e030c050414040b040212030703021c0309031d01231206030d050d1a0402031602010b100e041a03010c08041518080901231c0204030201 69
    0x2e51040d0000348036040d121001c042d1202c00010710141d54214000e02e21209010080500e825400d04004015450b17105178000da142420410315421042080d075002940301034124080d4540d800017411603560000050098080045d40e08105900000c4101c48503450804810654800322401e9080311880c540c00b501203003844654219004c0c0c1040302d1813281005041848a0300e40380c214106100c56000d103103425010700001d111044001c0c164940713500c03950440081a0a51040d007008000303002e09181100d48a840c0d10101c621048025202194810040c04c2107480b4545404500f1261028007030210140d440c01d4504071690510700d245070000092612076035401000101030000401e68219031035207540100d1a04840ca9401780503065907508140c1e05c581113804c2605010030110028042026180e10f459055110792074890024200325404c0142d140c2c50700c1c1c41400503034040021600040e0418845140f21490480311005480c4202c070343c015107111803860903040d030100d200c7e42c0000707400b0521 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 388706564 1250 388705314 388705349
    0x1015080a1a131515020312010b07030e09041104020a0c06140106090b090609060d050103020306070c0507030b0402030a14011b020303010f050913120903031416080903150f010618 78
    0x8a0f0b0401c028000d0140c1c0c112034055600e1072071144003c500803039000140c20008698298800d600561405001c3c5240c840345415002c2e40c01401600040308024080c103590800034040c40154031200d00f10340400740c0199541c3d002c040004112039180803007216010303e0249140b190b0302c11000d04d103050300d13a02e40316807004900b0540c3c0d0741d80e540c2214034026800750b000c000302c0034503403a01030107071182c1503044002203055411071042500f4480001e1400301001210a00d00000c540c0010304401240d401c0b14030a001c9031194000700341003071058080a402d40c6c445031000500c1900562005c001c051030001c0f0000904400c15040780c81e80700c288900c2004100b00241404649400c940503a005a04c003090f06200566a0380d6641c44040c040c1117010100721180010024035421000f03210001c103c60302018607203a4206a00d601980c0f44070000b42608101085074411a02d0800c240b40d1943c0a800905c020341c5062144084240024003451000600c12036200c441d10041c40d4184041e50701e250000d182048 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 388707814 1250 388706564 388706599
    0x109020a12150f080102071a191505040203180d031118032a0a0501030615030506041811040e0105070807050a03020f1209070602030c07030b1015080a1a 67
    0x103450100085112140c2c140003d0348000b50301e000d80140000d200140e1161014240380318080500c655003850035480400b00b20880c00d11f000038104080300300000180060307404082c01400700d025003101e0303085032000040c4206034030b6050110072508030600c02c1360402c0000351811410354030b40854140203030406200d0201845800300c4180700251000d800c440c1c4081c070b07805100252001690300b562501e0640c1d0300c0d4000d10304004140002819003800c0510941d0318103a0228980c514034031102d410556684081410395880703400c011106055000302c600541e405007840b5804e45e070507511181c0b0030751500e40030305460f00d01801414481c801c02d031207510940c0d88000e0155406d5110344c3e10007041503401c1101c1e02d6070300008400b07007504c1e403174040344000740e464a903900900c3c1c480359411050a540c0240200d070b22004000841c481a40d070b01402c039414a40710004d003180d200300706070055441c40800c61200c185203640160158403682007080b09102c6030090003420010184840303d59a000015078101501c400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 388709064 1250 388707814 388707821
    0x14040b0306060c030a0f020d0e220b0a06030609060f0806011a0d14010503151005060a0e09013c09020304080c0609100606030509032b15030204050109020a12 69
    0x800b40a051600040300900d5040d0380c0041c07940000300d0b20074102070641070707410044403070b50790820b0170852403055000700080e052180d4440039011200000741480124052038100313002500001e08180350803600d412002d0043d0090340910b0660519066000494004030039943c0e0886000c00b01400c807690074905151031601c0c0c1c00b034105900b82000c020070020160343e40b1641e0b03002c01034803001c842203504082c10103040804805021803448808030500500607400508041110f40445403e65160000c06055454140e030241803540b00e04840000601d40144c0800b03038488444200c50310907100200d84a20203000b00000740d212a40b900c1000034480c0740e103e58004c68015004000d210f05016070703461828509030741210859000e030000340107440c449d0351600036400030b0961401c09201520f410f100c0c1035680d00910301c002d981d91981300e40701865515070303071840000c0e41c03120b8905211350080714200c241441150310003240960715280000440729943d00c2039900301e100655075490905000074448014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 388710314 1250 388709064 388709071
    0xc0c17070f0807080d0509011505040c02150a05070206070504060c0201120b060310090b031b13020c030d0501152a1e0506270607180f03200114040b03 66
    0x890700c040145008a11103401400401e4031400c800d65848401022690544002070072072850740e8146400c8140c0c04581c0143d580688506807000103060801c010120b00d03011148058010141d1458240300f0011115081244541215000c69400ba120010b0440b454032541c8281c10000d02c401d00c805005601c00c01c040c00022102110118590443e4000191140d00130b035048001402070082c00c01601c0d550740106840440214054286180300c4c00602c0000144c4141451264000141c43d10f0207070240c3c3e042d10075011100d41160303210302004045a0040100313024909541d44403110f90040740d84036580e20380da41c942122500340b4079010f4152440c07504031f078440101d903081c800d2017250503c0b004841c60b220240780a0070050016003449140c051010400c0c0940c841500d084001045d900304c000150103810106503d0701420f60400c244041f8000c50168001c90300105014100109102c11802c207109042059241c805684045800550b100e00309444e011039000000c0c4001c000219000000c2c1d1390 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 388711564 1250 388710314 388710323
    0x305040e070306090e03030906011406181801081b030615040f0e06070306090f05070203040e1e040305040602151009090215041e0e0105090c0306310c0c1707 69
    0xc283c0e03100d0020600b40d80305001001051340c0040200040311100700400c900400e101c0072a040d4141d890310205001e0301c00c403c080200c841138504180031588601040c1d07079003002140352280a55840310101900d81d6500c0305a084948003c1d03500000c41d00d00800d95070f0003141070104a00405912409000241020100310030b181076840c0d00701642624240300d054801c40305030340d001072080c1c180302170340c02150710718501081d965140c40c0810061640000440d019210688284252076030f0f0044507411480110f14003c1e0102190400d000c2019080800703002076900517002d4600c1c91400c540001400c05040703898009806641408010034540c543c0465140d600242c070b03000c0c00e0b80d07038115007034102c0d4829400f2000c04440c0012145c0c85020300500c1c28050700300d0000c000169494030b400118200000390a10079100c0780080032600b107a40e2310407a0384051205604c0071b104003014016141c01c03010031f1107080118609255140031180d20903020b0504040c0c0c403481e030300051031800d280304d000f680000f8070444 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 388712814 1250 388711564 388711571
    0x70806030a0f24020901090f08100b0a03050708060403081302010905060f040816030c0e04080f03100503010f0c1209021804031b080a090603020414040b1c03031a06070305040e0703 79
    0x20207041c10f010090301c40804808015940b86a46000107003d0890b60b40008641c104011060000e0040440c0c9520390750400240401c10701080b02c0080c83c14642540020514032a001002481250100c5c0320ba100324029180d114450740c1d40c5000d10064807500400038001000340c1028000380c500b11000c0c0100809000110341030030340300c580c11341c0f4042d000040c0103c000c040850410030446502c40c1000039000103040c0f9681400c2c290351300880d500842c2e00d100c00d9110040002841d044143c00c960004000c000d00a101051107201b22900a110903644440001e01094640240001a000c0c2d2412182e020342000440c00c100311a0300d000b000098801c03002c00000c0301d006c007c0340b107000034050b02c0e03103001d032550301e41c0c5050340c802c00340c10b051071a1700001c185801808200314664501610029a080c140da02082c84031540c80003503103031020004200d2071904111240e100f0325515501c001c200700048903e68081009000400c40b1500130310070001c0c0002c00800041c0400c0f0004410710780c00100504010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 388714064 1250 388712814 388712843
    0x501180e1e07080c27070e0604060c200a090203040c120311010e06130809010309021c11091b0c07030c03032604050c0d02030a02130c08070806030a0f 66
    0x1000540c0450101d610700b5480340c1c034244500782041c042064510001c880401c0074149034402241107500603080c00f050290324000060590340104603110707080400618650380c4a0311484050080c880005d016100640c00b0010000c40c003045040242481100401c8802c555107003018001c003a60004004407580800f5030350001d070b811000300e8018441d600c80c1c3c640c01e010307001d59002542110460780050b0702c154015018001070140c104145c00d605034004803000c0d40e803170a0314010b802504113054000e411058450843c07107032116540040c42814890190081c54050242c104048110700b030702c100069200036003088203040c10721402030800c0741c119415100300d555a901c62207000794031580241c000c104a40d4100035807000c24584010303a40e00c4074141c410503003415280c25036201d2144004601540c44a000d039400d554040281c4600310764010450303102d8655107582100902000840c90300444c0003100814150b40c052a001407180300003030010400880d0306e8450301c1804003003480c10743e1812002a0721 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 388715314 1250 388714064 388714093
    0xa05030106060905030d0c02010807200d081b0304050622080d1506110a0201050f0c010609020c0d0903030c1106040b030f0103030206010609030b040b06030319031a01030501180e 78
    0x4201c018520341c0c942c198024035000070305040030107084c10b80701003020300e0001d10010303a044500c4c03c0c0c0041c00703860000302050800380f498018003064000c8094502ca81606029140e0380006a144502c0e5a43d01c020512091024200790600080d640102503801070b40000d0030b60401404402c13210408401100c1188100c0c0d1034001035a030285c0e0004005d2030302d03101481c80110b495a0060000c1035507180c10940c440074061145c1e1541c2d0000c50090401c140040c1c5112044000c2050f103c021620320002c008a81e90303918840300070342c02500d403040715004218011007618001c040342c1d812603425840b8941150029511103800c283c030b0021040c2c1c001c01c14040422001c14002c060340c4254220b10a4941650442c20064907164059200000300110140c0c01c1c0700103071280e1803140e0019400290540302e902c0702c000103400c50250f4203c0354114030740c08502c0001c2c84d42c5900480200480741080003410b900075401142a190309020759000d40303100523203050318032a1365444004000070800568004100f21440f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 388716564 1250 388715314 388715321
    0x70b0702061318050609012601230f070201020f18011e0c0b090c0d03051b03030408070c060906200705090c250b0f04030207030804030812100e150a050301 68
    0x44044040032510300480c003000d69200d07464122404480800c1b0b03661410811a03100400000182c0400b03d200000543d52842500f025070b4004a000c0d494182c03074100a440f100d000011507525450a07019004a903000740188210b41e00940900ca00515240e6801419409a0340400113581000510240d4504200020740e0380781c0400e10641d40d080d400c40142c10b001c0d0b14803401030460f94540d0090308145c180b60f580c6000d002806689414611b80302e1681e17600c8022205000c640310192800000100010044080001e106892044e101c8211442c0c0b910001c640c8001e43c2c0c059900460003090410b8080c40ca094282540c00c0005400c48194a072500086148041c0a85142d0080c2d0008030322650046541d03c00d4290030b51400c1400d01146406840f080078051010305107240766600040460705140c070078001880030350f811404140e41c3d284d89151035074044d03000f400e140704291212008aa10822001c0b000740840d440a820410191641a240365004141000942e4000300d401000600d50b01c0a00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 388717814 1250 388716564 388716569
    0x2070b0316030b46120311011401361e02070c0b0927010905011220060c01060e011a1611040207020d060b1f02070b07020613 55
    0x724022140303680c400003400740c440301c105103446038540820403001a42101010b110300500c40b0860340d8024500c02c80242550b8401c0c041415003101c48a022804400ca10358000809100340e4480d2079002e000c0d95514225034421139880e80e480d40f6640104008000c06a000840070030420080800348414100c502020a9109610720246d84441b13890030010131503440c80300c1c0900c80b42030079071401140fa40c8a07689690180640300da2140085040c1c03e540c0c442694490f0210036034510301011041460681540705403d200c1c0d41c03c6241048008610720300207955486429a0104101d00b1070803203400c1c910200f84075482100c7d00302405009031440c1c3c0c142401201c00402601115080c19414410078402104417964402da61880801015003c9912100d0513a10680c01c0b1401d80c18860040c0001000b0380700714000658010b400000103001d016007a4070105c404903040318440d601d2000441d8030f0759030341107030726800001d600401c10812090805034020034800c0c0c8010501071901e802246c002c0500003558 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 388719064 1250 388717814 388717831
    0x30e010c060b0405150411090f10110601030602030919050c040905010b15121803070b040305120f0f0711070324060b041401020304050a03150924050f09060f0702070b03 74
    0x74070303000c0c0141c06c00c0d100b070322141041f1132581c41c9040d03001e83c0407e4505400040160241b002c070041d114140348146100d006001d0403105980b12540d53b0300b003040c00394000b40d5101040d801240c02040020b0310750300e003409485620a019040c2203602c43e041000409419406a800e5505c44403008044d6a480401e07040801c07c0384019074031901c1d280f2610502c8600240544003400e01c1c0c0c1a080301c40c1e140081900d1890b6449000400d10f40e0765494100d03014051031302211049550f400074060084400141d15108007071105c0e04400d0303a500d40360129004503401e400466517400400381800858900341e44584080c05041440803488038040e16482200c000381d001260750360003c43d060143d4201440ca03010408400d2009504260410000400e1401d075444000d1070405c075072002044a000d5030f0890409a03812003500300c0303500100e000c0d0900d642082c03440700c88014507150029000c030106c40034103400b030b01410000f800300307a644031020100305001900010030341c032800d0f070300244480c00c0d140203501c2140305 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 388720314 1250 388719064 388719091
    0x1c030207031e05030f100806040f05010e010c09181103041103070f1505030612070305030a02071d0402040209061b0721050d03152c0c07030e010c060b0405 68
    0x1400c0c01480d41410b00030000007154010071070414250702c1020b50743c2041c580454440315031100c4100030040c0c691580b061025014580421081c40101d13a8150001d40c0901c0c000d000000003200b40380d08030f800c1e199520000c18030801080c01900101900842905d000748070020305088502d0280302e403500100c4003281c10000c1029a11b442d400d0500480c00140750780c0b6030741a402406c0c26035202081390b045821008203c804000100c2c2c81e0380b55545010104480802d41c1e14039500c2c3c0c281030342c882e805041d0850151003000c1c800540780304002c0510b4000a207081c0902840c0e1503a03800c1001030340c40315480da83c1c012014010040c92500344c80c1210f80b030f480c401000300000e904d480101241007441c040358140c072803100e042e0040403030000b1400b007442d1581031a0024040039183c0310381642c21020b070081c03000d0080100ca01c040600c4040e801001c1082d100b0a05881a9291fa48a0000d403183c440c0060002d40a1156008654000c40e0560085803080001103a0f520140020404070b510841c0d245080d82071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 388721564 1250 388720314 388720327
    0x20f06041401060b0f0306091b1c060f08120d15080f0c041806092901140d170702180403030b18133206040c090b0d0201030e1c0302 58
    0x800d100f00801050303070400701802d1032004e0b01800c41d1800024a110b004604142c0001e40c441d80c00c00c00490040d460300025612000111f803079952209040200042e1140b801c403012641c043e0005c140000c44103410b0041c0f002e90510402c0c407800f90062218414402c0d250000701c43d15035802c0c05046c01500c0e001c0000c0081d0400f2548640c500501030b007445000b03d2805042841c011003240d540c0148a07000540403460041900e48400209940580c3d65410014008001010034600400c20304a9500c404a4101c201c444410803039041111030b4018000350803c8a0144800b50541c05800e606000a060032070084c0f8040341e5030310325581158100c001a594003030714101e6103020049400312000e03d08065480345402080741c88183c1411300c5c06056018441c081c080d2950401c2282c680c54054085100d074009642000740d5601c4005540c1281c03504103007400410340303080b035124061422000038071000e10b0101c1500150020b0030003100440c004d001d0030360900b500c0e44542074400c081407541d80d001070707a03080e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 388722814 1250 388721564 388721603
    0x24020106060e0913030926010b3a06090819030e06010513020f0c1507020105071d06070203150106171317071712090303070c030e01020f0604 62
    0x1282078000009000c0400038100c080d03103528100f5035014040100103a071110203030a0643d4120241c0d1f100c00e07140c400c80c51000d540500da2603840160102c81d00000d0104500c207404001c0d0700074902844100b80200402c512100209010140090141c0b00504c100b0180c0a522900c3c155030701e12a095544450000b500540300c02c0c0e41c226601c0b00c4130546001c0000d9114811180c2d00c0d10741c18440c1394819002400b480c4601c403110b50482d240c5403251002e440d522021041d443e500e403110151a4000442c0220010316207500600400f07210b07182c1541d039000b4800c6020030300000c44600f0044140c00030000d000c00001601c6c200039100000307400c02e200c414598902003006049003410302c940400c0050380c000f0f2042100b94030b0000c21600e644140004070004031005011264020080094080a4003282031300001028500600f41242e2000c8400e400d90742d0500038660744d100c00d0343e582001030801460480480e108100c2e46041031070510507600e114015180702480e1000a071800c3ea14040e11104d00c20301403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 388724064 1250 388722814 388722821
    0x3180e091c0c0803090a0b010b03070906050903240708070203251a15040c02070b042d03030804110f0d0b100b040801020414121b040219050904060e100302060d0204240201 75
    0x4107900344405203145062100105100c0036840dd181c1400008a000800742da0b09104408150300080e80302101c404002c0300340782c185601560f540003c2820380d00403c103058404000c55100fa00703001d5401d80300e82518a036641c2d4800d0002c0c1c0c195440b90b8010700d00c40030386240004c094001c00700884203641d034400e01d40c1003000f141d11040011003998840f01d403c02107040210140c500301c603050f460003001c4034032511009405005910000900c810740d850040304042c1c00c41c1046004034041c81c2c4039801802c04405004000c980042504d90040ba81344c054400503214034061039000c1c07040d0000400c001e0791102c40d100309401542141e404d80e500410b0901c04c506c00018607402122007100e010a1002030007200b20f850b4050b00780002e500004010072403000f9162501110f50181d0320840c520034a00c420000189180c0014590b14801c074241080021132a140051f560702480c0044483c010051441e401c000203a400f41e194041c1841e002d10002804881040d2044a51240a8031071500070398078000003401c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 388725314 1250 388724064 388724069
    0x506031f0b0a0807020c1c11040612050a120302030402090a0e0109050d1706040c1e020111070f11030109050316031106041212060b07030e01050c06010303180e091c0c0803090a0b01 79
    0x1001c20f0346211f41d1405172611181c10043e0030952200c16400c040011602504580d04400103440b1440344203020400001198045240280844000003000f80d5003241a88425113010394007440c40b402285500902c0d034441c07228030f4400800050504100d43d541801c0080c0342440e00d0100e10220603406c1c40003480e28003940d00a40841e8100702c01224140040c051200594020440300c1da003086610116000354052030381080c40c0b00032280c985031149008040b41130515411135484084217101039440c201402080c058944c8400590b080002042d006510b807500454142c003003142000c410300114106021303250145004050000703105140340005040000c4d4078290054507858840204880d800700710a82e0f600692520300b424800c0b0140d801201c1c280203003800072080380030b240000070406130040d0004206100c044001c6006950385d80c0d4005561008444951880d045a507030040100c1c403180340b07503807801c54904108072858050340f40e24445030000c40d0032228542c4407a064006001101c1e2a2900 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 388726564 1250 388725314 388725319
    0x61a0a09180b070210060f1a0c0c06030a23060909070f270507030e0f010b03030318070b0f0d060e07020c0405090705151903060506031f0b0a0807020c 66
    0x10300401ca11103020340c0144904040c1a070050030000c1000541309020600807610759240522445460340c1e000821000c0c184103c2c807520b425000341d410740031903c90a075044c0ca4400380261214002000911030341d6480102042851a42ea1520f0355603030b00051840d4922624040004c0b01c90b02d4100280700300307824090543d49503a40800300401050400c0b050741405e071501e5055184903803101c201d030208860b40300e0050700c8615061400300400e86a040d03000c440000c0b029000c8881c0140d50300100e5080f81c110300c1d034203601034004000245040a0b004200d0501da041c11003181c08807940c401119644c0c0d000041107956040000174156540e001c140124405014045601c0d180c81c200200040c2da202c030300359003460041c6c2c0c40d1310003d5001c80007403040b00300829000e400344070281c840300a201003a40c0020044030071820031542d0246003506c6442a1070030f80300098440340c80c0d51540307020040c0180800803031107110100c032000030900c24520400ba09060000e0f80381d0040e2407e05c414080d09024100d0007050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 388727814 1250 388726564 388726571
    0x11071209150302220e0603060c041802030408090307080303150414010504090516120b0916030f05011b0306051c030e011b050307050a12020f0304030201110109061a0a09 74
    0x4407032000d40c112450718488904006030b032080041004001e042441e614100d0250342a02d0001e04544084501c502c1450220207a4201c1c1d900da1a01101034059400b0340f8004000c80d03004c10508112540c001d43c0c1040c015603a02c0c1c2803a524500082c030b00031641d00054000c0c1c2011051060380c02050300f0401d01e9510841d0280940354030986440e40542e0144152072045c0d03110b0b100c030b05c1030000500403418404000302000907050384650803045441d40400041322000c3d50040080c040400c0406e80c04681003605903101074052641d1103440780712030540c030700fa10f05550719045491250b0f07480d08400148001a2030208219203407000300240100150b5403440344240844030345002a600c284074040901007400d00c0200900c2e080c110200c40001d03440028900d2000241240501100042c0f44240724840d50308509032000c0148101e0300c450103135920440507802440103000660150700c040385200d1a103000000c2c00101601c519040d034400c0d0032021815000e001c440d00080c01d00e6210900501000042132 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 388729064 1250 388727814 388727819
    0x20a030b0c34060b040e2d010902030a020904020105041d10060c0210050c120c1039030216030e04050c0f07060b0604030b07030b0316050102030a03050c0c0111071209 73
    0x2500b02c504801d5004140c0b0f540c0708100181d41c0d80311707030010104000c140c003115079845054514071500390f40c40c440315410326058400089041f0050240190281e400f60281002000c0b5509000d1800000b51040703042c00814040407806d100443c5100d4101803010f82081403509001d004075011003600c3e04582c1c100300114001c84050385910711000084d4886241031651074101912041c1400a10054001aa4070000303501040da00006003d1000542c8600308000484001003005201c150004176680c0e040c10f108480780c41314041081e00034164101c3e05025103440c45092451050078071a0504801007585240300b00054200b0748141684021001c0ca582d24060405150800724011000c00406041c1c84081010741d9496002c2a5002590311914002072814000c6c0c014020341041e02219009200394903108044450f4440000e080301c1041e0050341c070309511482d00301d01900000f07110390706400301000303048070030502403003104280740c81c0c0344550b074480c0c0851600d40f165044503c4000104281d91030705 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 388730314 1250 388729064 388729147
    0xb0f16030501290d02040303020304050405060a15030510031a0f0f1533180108060904020f040608060c04090e0c101b08030c0309060a0c05090d020a030b0c 68
    0xd1620b00d0200b908000c03820068030b195203411320070000b50010181c0081740c000f041680020151041c0c94007200d050140360b03109014402c0740556032240d0860150b104a61541c1e0074080d502171070b0810b1035400c54000300d03178603900c8407070192540b50780440c1110400c000300a10b01d20320924580d0080341000701410a81041001d581445051401c818400c101488012140041001d800c0e26102880c0340c9070707421136181042003078040e0003001c084c80c00d89542c1c01b03503010301350b20404100d03215481c000c01503540e40c0c940d5024400c1401b03480c0c440a800c155256000b0604010400c0810710408035110ba1650340c074200244030040d200001c4403145640d010050031320301903440310045e200c02d5001e0305e4202a01c1d00034424020701000340d080050001c0d80d000050060f1004031200545c49140d80300101e81c0c00e502c400720200112452500b882c0001002070061001e80d151101c8100c20310ba0009054101c0d4035125200d28030032203c180d401d60384034034000800003160041d480c0d002e030312500705c800c1c2004920001c0320f0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 388731564 1250 388730314 388730339
    0x112051006050f0d0e0601050312030103170d090c18140f0109051909050a020f010206070804022115040308070903080d0b060f120609150310180b0f16030501 69
    0x28030401c1c8607020a401c0030155403d400d0b6039440800400c1405040b43c5540c616031038403028065103010b8000d0f078901101c104150b0044904999000c00e485070300040324969451143c0110034401c5200e07403240e0b076210100b44013038142c0c0e000c1e001203040103041f401d00075604011103030701048941c00544000204840031a03070754a1541110749180000c1099a110503000c4c0f611070b10a0852054580740420100c14010001740d10f800300b0380301340c60000002c2c1c07601c001681d0300c410072218040000d001a00040060411152480515601a02c1c01d40540c203070021050500d03180c0d41c08540700c40420001c000a0651207800c0d207400030010f0918289050958540c800780e880b43e0450012000d442e40040c1e0030540b1039408840140380d2185045444006100701102e61603410f50b01a481040e988020a5000d00150300600101800500500002e603a41601d01c024100c2c0204451100c4001d140c0700010400e80481548901c4410300c0c00c003000e16144000040c1109004403200416240000500035a232036200b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 388732814 1250 388731564 388731569
    0xa05060c030601032004030209011a0307030903021c0c0c092a0e1c060f02031501030915060314100b0117060a181a0d020303090105030408070f080901120510 69
    0x29015a0701d9a4160060f0040c14458198203044680b542d0f48178106008040034005a03442282d5036045d503603840854406480c8202044641400c041020800a90283c0d003d10000f038880e00540d61400d1456155440120b51400a80c0c04500f041d1420030400c6421030f0108050050780c0c600300f04904070200345030709060032803004940704000c19150b004400d00030540c03664102401020b0101c1c105400314a881d8003140c0c142c003110600c5c00d00d01c2c1500d0761070b180c0c000c1d2882070241c90310091204014800440260090240a0794800404022400e11455901482000c1c6006855206c10840c41300c103d54600000388890426461411001010301d03079102d55551310400d10fa40410100d911600001650a40707180d00040300729094020075030074070029800c1040c0079030744d60701c40c0d2100f140c200c024000015503000000754160820082404a58040e401849d0054000c00c0858140341841d80c8900c59001580c2081d10034003400b28070300d803041d0b9202c3d0003680b10205044080c0958204984258001d03003ea0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 388734064 1250 388732814 388732831
    0x5071a04050316360507031d0105150103090804170a0b0f06060d09140a050105090f0f030f250f0c05180a1e0516141e07030c14070e0105030a0506 64
    0x6240040b40c41d440c156400050300014204208a0600346e80c054014140c4000c02d01c40500c0007842d400f0b003210103114040c81158001409121403400b20011001800c4140c82115482418030000c40c1704aa1003c520b03016130301100080c8511013690402c2040c8040081c010017650104104004e00d685910080d274450030f40d94240825002028502a0869020426032a0035841030031041c0040c80310540115024100c40002d6490500500850645480d9501c18101e503036481004070405240410300149a202d040e21810034440300c0c2203103c0c80f900002c00700e00f56052844e41d41c1c0c00701031120482c0e03032600408045441c0a01402806a003045d6408010040180319681c2c0303c1c034600901d50500c02801ca81c1c0c08002c208032610342080c0304140e8140050450000030307202203681d030a42d07031214226002c810150305683d40c200010007a20b14241d00902046003007008907000e00000a592240011546e0141e40c0540051400d00000c8404c03204161b00c280e03c258015586a0007287d0003080b0941c000d07210 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 388735314 1250 388734064 388734119
    0x80d020c1909020d090210030227011803030503270a022b0b090c060909040f050309040609020a0e1c0305030c041208030a0c092105071a04050316 64
    0x2441a14281c0440380e10212401c2d0002131407a043d1481036000f80a6039100300e600031019042604220224020320015805800300c0c8454444049d00b020710520820005262003e5000e00c010140f11000030030f940220049103020003071040c20300801c141010068012040001904580301c40070b9a40d90085401074000c04d510f035000f0028002d082800c900c2110403940b1030400222174a040307564020b08a91041c4e017401504807440f40c500d00740003101c0c1d44410061080415860b03d441d5421a5200c20304121924803040142c03640030344942c0240d400419840b0001a21410004009043c0400c05840c092198411804000b48100c60708500c0c0c040c0fa4041c60000d860396110301c52000b00b48915000769949001c5d0307022010802540000451150076001c1081c44940c0480200303a402c41a1402080160034071550800c500076500e642c2018214000c0040310740c3c8554442444c030210707030b00043c0c041c01c0c10300020301031001e03003803c00a4040100008031064485442c0907240c001413007001061940d03800c007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 388736564 1250 388735314 388735339
    0x30c020a171b030a09060e030304030215130801110403060507020c10050d090c0e160c1101140d14070219050607110f0d03020706060e07080114030313030b070801080d020c 75
    0xb08041919000088802101da0f0748200c400c010307000d1038107403058038002074040c0203d11860402109540441c1d0f1702030a03140058458403400b02e055041003490640341d4036801e42c00112140c00f40500c4008055609966940e00c0c2941000025a4070040650080d5480110441c03125100c040403c18050345502c0d100348c9540031462608064035100398083c3c1808003100010800c14000f4a071980208044c1c048240400c0c40510b040d070340c4427800b103009404048298407000595000c0c00381c0d46180f00500441c0d6140c4648040c000003142c1035001400400c0034800200801c0d81d404020140d8100c00000c1c82e884480c040350b503210368812004204008010300791180a8405504200b0030031568041c00070f0304e03802d100c002d4008000b504010f40595070075040003000180c0c0e400d600703843c0d40211a6965051810780c00c101880c100400304041c001e405100c104800c00c40c3c800f245020201952082041c1c20f05410700c90700c010300c41141038101b1080c0341c101da80749540075500043d00e080401c0d03064415031040403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 388737814 1250 388736564 388736587
    0x6060f09130803040506090f1605040b0a031e02210a020d0f020d06050a1a0609010c031211041a0310030b0603070b0409020a02070f08120d02040b0712030c020a17 71
    0x2141c0100082481c0c1e408000d0004112010920754440c90240c1d0072207090107a4640d120f580c46116203003010415050030030502007810260404a12914040c040301c00003952642c82552012092100300d9502101031400000c525000c100303419005100300034801313944425050790351104903030740d4020300c60703040d109408082100c245015082142c006040400c80303c91400d2001c0a090304813544607906160160940f07159103401140c0324000b0307020301410708003aa1f8000540f00380342d01450507402d008901102d000d030304041d4080c6d25070001c014001ca0f601c5902d042e25040740e4494004034a201d0310014030812130035a1249c40700a01300e0b0b4108140c111961211404241003265a40200c50040700029000c00c2c80744c026001800e0103070183c1d0813185201e5440c103161588074000d0040620170f8101c000d00500160180e4003400b00c40c210540c00515081e0b0310700100e00d59038003031041181c0c0320003c140c00f000307083d03014811411044100d0014240301c00e09a50b603000a40b03020ba040c1d0101e0000881c144850b078 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 388739064 1250 388737814 388737841
    0xd110309010c170720190c09060506120103030302130803040b0c0105010e151302090301020316020d0801031e051905070e0901090b0610200c0411270d050d030b100206060f09 76
    0xd929108400001d03201b1f820310b00380080c0741d8081c2031040e03403c0000005150806800701c80d81d440300348196201603401c41c2e8048020750312070840040203248030308000c12144d4061000b00001c02414600c0c0795078111004ac1d007820746d08141e1044404218002c1001200f2902440700c007203c1d03104595400804918a0400c0001c1c018002e107950198404000c101480e40842021110411b1540881d0b24410070080100d940c840c00b400010103d24040000d0006407030401c085004443c400c0c0141c1d512204008034850034030001c41000d0300c150744500000c000347c0b00d18250080d00042c0a2000b8081030116454401d140c0d00702401080c001e80f8a000703401090b40c40f40043e0140c9400280b03003c075000000e450380342c0c2e983d0307003d4041c180300b2807400d03c00482808161003140d6102d296502425840b03108282002c2c111402c001519803c1307034061000c000007400900c14600022050784000840004c034070107000708815400081015544500280a1940d9420221005a60003100c2045e110340c0c0301031a2a008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 388740314 1250 388739064 388739083
    0x703090b0301030f0212011509050c091206012108090f010e0607050a0b151e01031b02030a020c0a0501050d0510150201090219030213020d110309010c170720 69
    0xd8010110003c000c000340070410340040c0d8002c48040301e1000c6080c2402d42203506600212107884141c080803c0807030b015420142d80030b4182070082c1c5c2800005c0010078004800c0540c6410315400074001030007001c100d004003040103103c880044c41c0300480b603600c6c071449116202c0c0780391154035000580100c2d42e110703948540c10307400041c01c0c881d105c1009140a81c0d990380303080d00803507074581c50f200040c41da410b18215204024000401695042e0030f010b6065030a01030b8042e105040549821031954042d00e100303030903041190560b0085a5407181d16400a060002c0c40712110310481500d402000507070f901030155075103151445000036403500c6000040300340d181c07183d0096002803050100c0c443c00c560194415032002e0300948500c2403002d081c4603018a444840e010007544103018036110061120741c0d81c06400042e0b8910310005103100034851514494008032800319083e07444045040d40300ba4081d41c080c4038445a5120594207003090070700513200c94102c020fa81d4051094443c0c0003d03105003000200311 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 388741564 1250 388740314 388740329
    0xf0e0c04051807030f2003040203012406091e090b01171e010806040f080d0e1b19050307510809060c03131a1008030304110402070309 59
    0x5292003140c42c041c0c1c5400c0c112a1000400d182045030030301c4c035003d070041443d2010305148802811224204080e2140c0000e0403c1c2c2c0c02d0f40d42d40300c504e01900711078200c20003031981080b511080c0c40c0c40c0c40c9005103610300d160002d6640b41c25554030441c5c0003074690410303400e894000001040d0403044400484118080b2180d2074600e41c02c000902c001550582c00c03010101c604684400000e0303032605002540d60005890082c00c0c484440408801305503107101501401070f919401141c2c0d10720009000d880d1045912001021103030784091800146011305410f149424151952070182c0d141400094583d82c8602c550340c0302c1280d0082c40c1450700d000701020406102c0c10441942d07000100708201c01c1c003002194180208003002c00400500750300070b2080900c156440340c002c00b8141e44c4c4500036802500f01414005400d04001003101c001039580310545481c2050610050080c54101d1000500c1500c2e60b01400d4150820802c1c000810450412848100019200036907512194a0121070440c03850744200d9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 388742814 1250 388741564 388741579
    0x509180402101b03270f05030c15040b0a110d09090e010504050a02060d02120a02070201020106170c06071a07030504050c0111100c0e03030a030e060a060b090d170a020105011d010f0e0c0405 83
    0x30500680e260880548a0550485807884164402d00c64404ac206252040420b02070000f000920303648070080c0350030042032406614081c038022a0a00d40406000c400e0081000d044090194085030311030284039500d1440244114203180e1141e6440c0d9030b1014002c2d0007250001349201c420007241d011681240d215041051280c41c04113010790080d040000200e0055091002c001115000892546040340c540406800d080c4a86001c0040c25440180122102c100c5c2c004554040080c0c09251441400c1d01d44010415103003501d406400d0644042d201d03814405008001c800c6403c00003854403900c00d0003480000c03060b03640d980c00e8030010200c0440651610001a544543c00c1d4160000180d518280084400036140c02c011441520368500595006800510840401c0c0c501000300e01d28550140382c109200912104250081d0361045c00c220300940e4492004001c1c10b8030451000046903151071011103254100036600c54000703000d01c240e041201140f40459486072015080b107000f810000c1c002e170b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 388744064 1250 388742814 388742819
    0x3070c060e0a0317100806010e070e060f0304061b0207060507050a06061e0f0605030c13030b0a1e05041121061003060e010603021f0509180402101b0327 67
    0x24080d5410b4600c03880da04c0e29810204907140c281122110030b85070030304043c0c070712a0f081074000e005100e0000d00075400c0000d65408000360791036500042c1403083c1030142c80c030354a04c0c1c9403d080e81036030440d00c640c2924422310505004070381d41c007080c6c00703099900526140340d40b003000e4180340d440d14801c082c3c054507051038200001150400c4000600d010301130f0705400005c40f070f41d03400d401407014041d22034030340030070310801c00958007507030140090070900804036017400e0b0180c40f40c455811000e07044138094841640c038590480161106c4401e070500d540018414041d07807170207540310381c0e40d0341840c172400e80108410100c0da02d91a0071404008810640d003400c030340032845c250001d166046070610044c2e600c5494400c148502d04818024032090340c1d0080d0039503450039000702c11440d4104840000900301f0000348500005a5a501c0d001c52903d20114550483e908041c010818440500422407040c0b0081c064000350203843c2c003400c24103464150404000d82c600404203e2401144064056120115420b02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 388745314 1250 388744064 388744067
    0xd0504060309022706150406020a02120f1e12070f0b100b1206040e0d02060610020f061008060f0f0a0c09090e06040b010b0408030708130807030501051902030c03070c060e0a03 77
    0xc1a00c0380e1402c0750300c40000200c07906c850085200724042c5100580100c0f25070310140c00c2059000160501d10000c131020764140380c582c41e040502ca00700c0440c007131640c81400003000800300400650311a81e2103202d4582405503031035000c14156994018400760b035140001d100d80808424101c014501403040d00e641d401005511064068200e8050f0310803494881c84516045000030001c400d03510035001481da5455610400c8080061045914114811a00604001542417100900400c41c03405001c00740c0c0e061041c05420007100801c0b02c41412000c2003042141d0200c0b102e2550455100e400001d003074903204004807503426254100c96081070810907030303485a03000040d22034441d90207a4a481903990701d8000000b0303588a540301e107005070341c0140310080c04200b80385d00602035000d942e903020440c1542c601003103051008a50040c1c800365034450800c1590380a2001c0010403c0310294114036514100302c0d140d00600020b407185040004126070741c410401594448030003403408030111907000e06203180 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 388746564 1250 388745314 388745389
    0x705030a090501120b0306190605040e031207050c030406110a0209130209151008060f18090d030524041508030417030a0f110a17090f030d050406030902 67
    0xa182d001410031607074400000060b10800200417402000f03072440341c83c1d800750716a00b43d817291a9003031010381c1d94400094540e21403046d030300071070b40d0603001c1d641340c2885900d8480c1c1c0b140018a003500b8050b01b0803d210600c071340802154155089800e1807010051b501c00114900045004000d40100e03810b0144011296680c0501d81040d108690310100c070f60700da85100000211041107903800142240019404501841e05a540305030301520055680c460a00050407100c2910f0540741c038524600d050040203c410b000d07181441e00c40303041c00d02a40c10a00c1c03d0f030713003d028407041c030605c4403082c1c05040c4200c1e0f40e590052643e021003070f00c01145003612a0001600c1ea4024800e054404074408110110008080143c1d01c03801580d88407220150088007099030450360100403a4041d0261100034000207c0c2e5500004035001408061034032200070001b8084603415804071244640d000f807400d00390b43d42c1d1100c111801c3d50030300c2c41c1c00b00e0050310038404036129141203461040c0500c1c40703009801d0050388084 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 388747814 1250 388746564 388746569
    0x150902030619080c010e13091a01120b0a1d0106140109051806150c010e0c0901050306061e0112020c0607030b010507080403060207080f0c01090b090114011404020705030a09 76
    0x1611a50b500044604403800c1900324420f19509810005000f11a9805035906002100b070240203441d102c03549034050b03421110f13180d43c102c40c03824964410841c0256012680c81c00f50513a2000a10142100d8969581c82c000040001550544460043d506100382c10750101e5000104070083c40055210340c030050408884ca5401c5000078090840041c2600d049241c201c0d0380d40c4441001a4151074010034460300800440030210442010444070307940e48801d00c160310303003544981e01400d940c948001c10000d150704c0c1a84502d1113980403d040c41003179607070b00d81c9140004a42d09691007e07a40000e0050303e41000c24080781e442a0f1010414500c07010000c039481d0711501c003654007000404204401920a0700801f82c0c040c0c0b01c00780520051000500e0b5034002c0c003419005e03034929820302c030214110b40d20350390001031705508503512192484100090b0103055904006c0000003840352161510580003400b4052040c05961010031800003015191030741281c0303030309400005070384c0d0b00c01002c84041c1c0b4025461 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 388749064 1250 388747814 388747819
    0x28020f06090705060904090302010b03070308040807060305090d03051518090c01031817040b1812030a0f2604051b031b010806010905090a06030501150302030a0f061509020306 77
    0x800101d5500d00030488000703803100145102d0502d500300041c04021b048003c0201c05540da01c500c04001e5070390801c00000103500c5000741a41d0386040044003411300d02c06601c0138042c5800c001c240300040e04082050340c2d10000501c0c0015081ea5030810761400c400c4441d00f1140c01840034400e00b1803804418420368072401450044500d503c1c2c2100c01102191810541c0c0160f20031b0b0081180700051a480c8900d2141c2d1440743c4480c1030545038940e2040c01d50007141d800244e9039551052000900f80010031490136076400000d9400e14035081d5010b440d031440307a02e1001c00c002da40f9000440300c00070107110503500c0e04010840d151a1500e40b420640d980c5420044001685041140d171070f191a0001d0301840c40c1e01541c0340c40d2081e0b0310950054602d28070103031009051040d01d010100b22612180d1409110b02072600001c40c040d840d505205084842c110705540c01041c82c85014405600c00241c405915a0703c81480d80090300103003840c4001f000d070500240980d9555a1000480c540396401075130185008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 388750314 1250 388749064 388749073
    0x4090f15020c061015111015090b0301150b0a020a0510200c10022505061501080402100509010210020403120e041a090702011107050102030121030e040228020f 70
    0x8100400010051030311942240c03444600c1e543c2d0440f84141040c40201d5410740c12030382c7e4113209081c0101074494102011844003c03060080201ca08240035440300e44030705600800040410000800c081220790003140a40380b00016101243c40c42080f02d0b010050300101030702c2400d800c03c2c00c2c18020384200707400c4100031007941d4540103061f2107240440ea5401d515000809500c08103000380b0010f0f41200001d90414442140c0c01e03070b403000f0400b00c44040288560b02900f61844c1040d4081c00706030030503500604208101003000b0050310744105506003000b180c1001900c844107400101d203046010405592362900102e400402c000101c200704003014415110031011000135018032003240d2402d80c1e090440460400c10803081d0a14064203904400644004203250610031a603041c10742c800c2e10115040d84d8000010049404034000390b50000b102d00800c1d00c1d09040d80d4600802d41c58880500c28801c40d80000c1e00e0b01030030700e00d0514001104044007182c110b404603c5020303407560b900c07100c43c0d00103000d03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 388751564 1250 388750314 388750321
    0x914010b0c030426060f13020906010c0b0406060806011e0308090a0b0c0a17072f031b150703021c03021207050702090a051b1b120403110103091104090f15020c06 71
    0x201041c0c102c0c1f142c0c0031001111041c5000390204410020080d0425040c060603081040100e042040311038400d0b802a42d0200340c03189400c0c029450800c05900025110801000d20010b817000c0d0b80c290021a0b03044101d60b41c96130820710020303000366140e038000c41c41c01500203240c0303c0c03198011032612001030045071588610190201801d4443c420315800030448034281c005014201d0480401d2001d508000d80f03150070f200c41c07000c042440c16205008401d003e13803040302010501d180090420542c040741e45484e508120740399030045e44d2008641c01d941401c80e4072840390329006201c2d0b41581d4600e482020030701600e042c0050302800d05d61100b1002da008150740301c00200c240c1568081e0718052811301b44c103442d001d41c0098940d44150070800d000c0c80e42e03018190700d90004c002c0810809030302d001d1a200b915555407962409100381c40e4107040341030616044c005940b0100f50050518240340c1003d581c0428030304068904142889140c001c0185043d09101c09104222026406401d88070b02040c22504c4948 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 388752814 1250 388751564 388751581
    0xc030426010e16051c1b03020405010b090607080a020307060204140f041104050d1b090509060718121505040510110910030c1701030f0201090914010b0c03042606 71
    0x38100403040314a50110710013045141017070480303100c0c800c018608401c1a42c0fa1a507030389200d0004600d0b40c4106410140b806c0c0103600d040d1250742d004100c0001034501d08038038100841d626005060016100c03610210360303525841c0c000e2040700c820950002c011076489441e16807103010600301c0c0114a006240750341295101e1706091107194100e59480c41030900301450310781005030480d40c149044a415500c4541008050040b500100c00360501c8400800e641c80c011a5031464002c00402020801403903c0f5850b281c03080c80c41e202c86c152031844c9a0016050200d04011175400243c00311a6000713882e20040005000c40070070039046022000c50248030380200309010702c04900131000300340e41c004001e40d40095064000e510552800c4110b050808641182c081e151900e603009a0064400394140c680075070840d07a00400c03020181511010810a0081400c0b10700849441405540b0000b1000540804a40c0b01001910000c0c0001c03a100c42155400b51115148401135000c210780e184070b110007107240c60 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 388754064 1250 388752814 388752823
    0x1090e0a031d010306031a1b070803010608101725030507090b040612061a012c150a021b040c020a060203131703040c0609050607080c030426010e 64
    0x5034040c0d03201c01c1291500b070514103040301c1c0ea80800c0d042c5030b079540f00000002d280610303d00a0050742200440f0074501341c02d8184d40a0115400300400302c0042164400187e810700aa07410740300d4a103003141e21940c0e41d00c1d40e0b21042a0b1a0445a116440e42884251809002690051a102d16030241000c0b04900c801003171154540c0c00b0007000303604600d00a20014400307910124070080d001f440031814560b01e007000b21100032001d0090390b01544640e000d0003544180091940450403e180c440d010380c40d0404942c011907120003039001006000c801000699a0341018001c180c00c4565116035615100880655281030200701045d06120f02d043c080303c1840c3c144580003c1000580141c5121100c50b83c0f048001c3d4001840020402d00800651003c00c0000074502019400660010b50f00c0c2418101000301c001e156001c03508010a4010a0006072110002e4454480e8803400003600d5002c2055254203500860300605038661000710f05041c210351610604400d506800b0080103c00c0304180382c00d448 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 388755314 1250 388754064 388754083
    0x21091b010207180203060d0f2105070c0311030a060606021509010c05040501080405120f071b0b160c03051213080609031606091a1501050c0a0f0507030b09010501090e 73
    0x4412150400b020900221307001140d10201c01015801307500b1159841050703000c9000c00a5500700880074007000206252156404001c0090030003509001090351811000000ca0000a02c1d4820340031031229140c504000441d521544805e09004050710745400a55804156003803212442418000c1043c0034018450030300318081594400745000e041c00d00556000002510031150b40c450102590001d500c0d00014003010541c1d0089240d03209040e081652201004a1010084820a00301006500c1c1d8020803140544070a00c1842132144150500710301c03014069001031300e2401208030110042c0680c800426040940442221784142c80344103413076482c5011902070360f0030345c000c10501d400200e0041032606020310410300845d0406807a0354500d500c07048904112940c8030003030305001d07040344080c1c1c00031400e50742032070b009041c20003440718507554529210000d0300300c010300c82680060090a2040901641d000242c20600f801e1540007640201404d00c1a0702100f468049a203000c00340214400342d6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 388756564 1250 388755314 388755329
    0x4060203160813061d060f010609171c05090a15030516090b0702040f0e070510050703050d020c07170c010315060e1315080c04060803040506030a0221091b010207 71
    0x100c075001a41c8044c000c10b00380549001c10b90700b20041a024080030032844c0d00c190401c1d91424a103501d85500544030300c2c2d01d41c014918101001d01058080c6c100040ea440000e080c06540c1910010440c009031082e20507003510365000070460b000402c0d28000820480101809950208602c1d82d0b40c200803040c80056400c100d0015921030360800002142d5006000304d14002000015410311300da0a2504032148002401c11a03002448108014680004144880340050400b030380351558079074004180f8401c0701000080140e010071a01c010343c004001c503002814241118132031051410406a99032500007240c58002820060304940d40140d04044004490540d01d585044004003000c00450204200701c0036051a6115007205030807003000c11100040003403001400030643c00d48207000a403102d903005810786600400c0708003c2030312494104c80e0300030f80d030a02c01610b41000b24183c40144030881912000007200c1424450114800b2885aa403000000c440460503201000160380304c006034401c844 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 388757814 1250 388756564 388756591
    0x1d180f070801080a0609230d0e060c03040b1b07060504330f020a05010c0c021311030105060d11030114031507021e0a02060a0314090309030703020105070317040602031608 75
    0xd0046d422041140e44184045404884010490500031b440941680c080d548190001d8090030b070048a00d483c920303819206185007060318203105550b440b036445080d459590002d600c80b0300555036814103400d1101a000e80c0e581e140d41d6100248160007070300404030307a0b00d410501d81c107121001171107000f20f182c000242c0b07040c002480b0009aa034041906d86e0b600560241144040005000384200c0c02001d00940302c4203550491401030040d040c6041d614014002d103452a01400917017400c081c2d904548084070180d6036201c010240d20094021a9908020843c0200010415506004804006032002d90440b10030300d600200443c1c181c2d5003030b1071003c0941c10034810215192043c0a105a081845a044404100103075012a203a40d10003600000001d6031001070235030410300c407410b554002c00c04000a40c01d00c660040000e8a540c01032000a040c400c00103101b80401d0301801803401c022400c80d041090300c0c0f401d41400300196004841c6a907013001148140310303802d030003502c105004100d01c10026 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 388759064 1250 388757814 388757833
    0x1002070302150c1c02031503010501080a29010b090f04090b06150f1c1407022a060d090b090102070804050d2f1005030106020d1d180f07080108 63
    0x311154007014004501c0c0c0700d410001c0c4c1c0800260159940b408540c10500181e581c03401d000061307517400314400034510907414000104003400c4c0004030054560741182040d8030304601c0d03462420a0088007040d20041386264000003d0011445c00505800359050300c40c0a08144124100070468a074080000e00f640700303490100361541803000216007203550710420a407825424541130f90081c6c0240d656005035140e01d0ba55802c180c0f4060042d810051081070866500d4240301c0b00182d20390030040044008600c0b40030340c6030542004203007a03131132180e00030f0100e40e5030714402e6020401620840d0300955107442d10f84041140b00605200311055180c006400908080c00c0c0010401c1d40207540c0c2d42070f200300b884540300018416918000c5c102c4070951480d11020004c00e0f80070300c03103100c80800300c0b02c0c2401020700041029a0b00411406414901813501004401c220300c00d100d03010024202203500000c10361003000c100100020340c0b60084400d50748d0011507698607030044681820134006e661240d041301410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 388760314 1250 388759064 388759093
    0x1220120306061c0515090c0a230414120a0507060503070e09010b1201080606100c050307020402041e050a032001180b0d0b0301020f091203070204051005012705011b080f0901021002070302 82
    0x1c41407604001e485121000c1440e012a01c3d1504644c006401064004400001e01c0c40c1c1140133254802c01c3d03401401c101c80c00c1d500c0303d076200d1041d88100c10130700400000044001d885808511142d6500800140322541c440e00b2120003030f0080c018402c00c6c910400004240a2070008269124020040003001e2444054100311034182d0114012100b5100922180005a035140080e101a0a0aa02000b8040c00880b01300249070426840b0701d00400c0703407060600c08140d45072080400308146084085400f01d0f84001241c0a090700c4109611064a0241c041410380c1c0100050985190820dc1404142c4c4c0c010101401c030b124098180301321308000c2210660312304203429100c14040070360042e40c0c01e2051540100c0c0903a44210340ca00c10200080b4000c0c802583c0080e20b4101c0c0041001100a40203404200c5e200352950fa401024144030000d41017200c00440c00d0b24607564550f009079981c0d2102256100d941850b000041713a14090b00607a0003e006000c114804d40c2d2809401d58010480c0541c0e001d41c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 388761564 1250 388760314 388760327
    0x7080c06070c1508190c08070503061201050906060a06110c19090516121503240f06060206010509090703080a0c06091220120306061c0515090c0a 64
    0x441d680800c50b800059280b0a10100070401d0500d0b0300c07202c2803490b0024031284012842c4800300280c0c1d1400402c00711141d0702030502d0b50300a00b5802c106a503521010006294030758941c0a440e055801c0208000c101e40f404641e4600520064030100d444544802e0199121520340b412025207500141034115986031a040390142d284035034922040c61519800c1c80d1082c0c880840d0b00900c107596003501c4201c4503502020b140043c1a031680c040090301000541c0c030300014420b100240941d504589881c0c010200d8084000020200000030880b0000707507800400a45141d00c20301002d40999400003515080144070709100781d880d4000b5020b0305042d9540c80690ba08181403210801030100c2c03d4200156451140310074460080d4000d2840801c0f26500925000c12040880c80c07415482c564609503000004030b1090841b40b55401907240d40c0c4450200340300380a040c10400b240804495109102000382c1c1c000e43c0101511000e03092604000002d010306400c0c1610308500c5483d003003207101840ca120300d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 388762814 1250 388761564 388761577
    0x130206070b040c03020909070501120b092710050114030c0310050901150b1206100f08041106120a0e012a0c0b1602060a0b0a05091b030f15010207080c06 67
    0x16103d002403526500171071040c180440e03d00804c1e61003400113100640c1c000e00302e1000b000d54000280700c40e9031504081413580034080c10440803102c0b40ca0040860100c0180c4908504860310225450500e8405074203018000a00c01d071541400c0c608200070050a000c20201e0304c0d80c02c0036009084688211078000d008200003003025015558412003a803c040360610900d0003010a018a186c51340c54008a90409100142c49c480c03140c050038685005498001d11710604101c0b8906141c48140d5850408003250502140c0d03a540c454400100319a081e400300b5480f0380220360344942080341d03401601c07419007211202400d90b26581000c040e07803403000e90741941d41030080015280c0b800388045143d882ca02c202100f5075440e074600000c8002080300c07950400c04a54014205402405151040c1c4045a1000718502546001e00d0000c0d000a804108190b5400303052404084020f907246030134031a4204150741a00c505003507400c804105900f6600c00610f280035030340c103c00549016035030070f0100103441e401107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 388764064 1250 388762814 388762823
    0x150c080d020f04030f0506180c010f050d230a06061403071106070809121612050708040e0417031902030603010b060c0f060f04030203030f150d03021005130206070b04 73
    0x800c40b42804110b100c024100540c440c820303503407418005213400ca04155006210b4252020000071242001c280020081240d400a0900e00c00c408003c400c02c54540c841c20050341c0b031090400d80d01c02c6081c1c40d400000c280f80c0c1400b85003851f450715090304403025504144103203030003d8501c1c07080e043c5140c1101d0086421152034146081c1c403145100307011342440401c4403c0004a0202c50401c80e0b15202807000c940c03068905451140f6100062401c5818580780040182c50059050345807000340323015104842407d80c00014080c5c980c2d0350340011184401007290308a841030400c0c1c0c031201041c00204140e80c0038007104c3c0307030300450f001803444410025000140159455902c540e030714034040e212303a8020701104071044050001400c1048040d458100068070b0344107190601801c20000c2a40401a250000e0680219035100e4490150301c6d502c0c0882d91510644c0164541003240030180c00142d204042c0500344800e0001d640c4034403100d580191400d0000c1e4010780100280c40000d00021000d03607005102c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 388765314 1250 388764064 388764067
    0x4150605041505030d09050102061906121b09021804150b070501020d110313060b03030f040902030a05010906210f0f0302060f060603041226160306150c080d02 70
    0x440300020180c4200419120b0180c0e0026000d000f5420140201da04071002801c0c003c0e90703e880c0600003540c03200010002c2c119445055403185c80d00100340c001c60000c0040c020120900c2c402c41c24072034005402e41c0d02a80800c045058002240c440c1802034625540100d200c5007121100b900c141f0010740440800520746d200070400c023180914401c07010341783e841c0c0078000050322030701020070700300444e10810b000e089007400620401944004d104100b02c04194403040210300b115120010030b10b18010f4400c10441c44030003190206215230a68051031142803039907801c1c0001c2e41d0b1035084908540d00b9006901140e02400d841c89403e5090f10341801c0d06601c5007804100020032a1100214000c000c101200160032003402e00010a0b0708492564001e10111101e503e503042558815000c0c5803450f0200060100d0b820300f5410990345028441c4081d100c0c020300c061680750200b008801d02e007014441d5804030b40741ca100400e04000012640c1f1000000e900c9030024518551581c81d4290000a584ca0301e00780c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 388766564 1250 388765314 388765319
    0x301060f020709060b04030209150f15041a0705012315030a08040305011b0912140a02030a06061802041802070507030501091a090f0705011b020d082808041506 70
    0x51442840300030311030405c80c25255411441080340c0c07620060007074581c00961010141c42c80d550100d018100f00b804894a01c5125443c503510039060146a002c0d40002c1d4803002c071103e0603414900188105d6204800811020301e0701046406c1d000a040c101c890424110030025003101c180c10074540101d0402002c59050140550b180c46455100307400c103c3d0265140d014038116102c0780140c1c11510052403c04071515410310407030144540716840040d00c4030071042040e001340c000c1072006c0702200ba000340607a00c601c5c0c0c2c030703040c214054001c0380b141c11803003040f44200c0100040f0714802d903010b40c0c00e840d02136920402da114000c0081e402400090324a401140350010001c0d00074410444013510032500f4041ca204e003c81d000e407039504024059101d0b9007090904101e10b01c00030400d01c00313440b403d080400c0020341d01c2d5660f0031780300b6954a009400802d08030340d4030180403516014040c1c190384001d015040b552654908114101500d03080720201c1d40b000d01140003d200c2c05080c204480e010137001803500d6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 388767814 1250 388766564 388766579
    0x61002070f09060906060230070f121103120f06011106041a0105060a0c0f230109050c1816020a12030203042a03020d05010608031207230301060f0207 66
    0x8401c2d489202080d40c0c40310100702008103409010028a010f00140c580354450300c00101c405c09403041180811991030945210411440d01030703640c0c2c1a0030490f07101d841c5115150004900032522400300200700c1c08070000009070800001c40b842c10300b100e25800d240391604130b845021960b029210b58188000406900c19450707080180c140705034040c0c031101045043c40070945c1c43c1440d06800c11801b0b10802c1148260480c1c1002d14070b611580d00590703d0025034664100001110440101d942080e041240c920070030325815008034840ba8061002e903060a0400400c1001c0c54030910503c4500000700c400103440108135050301b002d00070140c0181c0f8000034640d030319010802c150b001e000010a5000c402c0c0018807a440000100e5410161003402c008013113165881102a02484002d103d40540f400802c01c021081d08044000d25510007203903102e0100b0703d103003601030070300b100c034240001d015291158001c00040f4504001c1002e510307296185900b850b0b400ca540b0107a00c1d00c0c10096100d5800002400c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 388769064 1250 388767814 388767839
    0x2090a2601022a06060607080d15230402040f050907050c06010f0e09010905100213090609020307140f0301030f1a07050a030c0203121f0e040c0302130e0606100207 72
    0x4000c5810a40315030500d41c41c0e0581c01d151946480303800782c0d101e0001c1150584030881111f1005410446070b58807080802034480207010807207107144c0c17503104645000411000350400c822150206a405034880b6030b02c071003404101e000f98402d6500740355019400300035904024191540040c664030700603181c46e41d40030000740742100a030300104913040d40c4807007040b007104900706098100b100a0300900c89000141c03696955490590b42030701169500254102c184078102c21424000c0544000c00d00105543d440b07000000d40084a12902007000354088511143d404402c0f203c4041c0c62020940c210390079600e076500d4503001071804407040102c1024a0340d1040d10541110320400b030583c0c0c0e403035031030303800d204010300b6941c1ca01c10400c00e541c030600609000007007080710243c2c82a003640414402d4103400ca403580f01282c0981c424000340001005000510866a08a02c1070360f00a964800002078441152000c4a0070b03041c01c211540c00c04000f04404d85041201c031307400d80c0ca0714030454981d1521240320b507014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 388770314 1250 388769064 388769077
    0x1107110310060f170109050a030f090e0108100b01020304120b151e01030b0d020109181103090304031a01050d03140f0c060a0f0c05030f34080a02090a260102 69
    0x200d0954a200304130f401512104071541004004c024007461b80290703034190342c0e2181c4403401401d2001e1640c80001e40c03442429040300a010b0800002c0b8035503074601400b5261244140803000c0d85c1e04114444e40d103540000116001c44682c40030305d40704851f0603203c2e0f1000351000781030001b07400f0b0076107071040c41760b52039030141c204410b00e0005594100030745400260844e0a5451040d0140c62203941800150381c100100c081147c0c03680c80703400300d2a101d40c1d4290004081daa0900e50b60345102005004203403030004050030690340309680c101c011204481c0544180c541c00d208052340000c4a80a03400000e103d10448841e044100d1101410200200c072600c0301900b0211210003c0d038486030030090782504a01032003220000110041200c143c03035182c003c00030310000f07021040441490000c6900c03079450f00700041030041d0030700466661079120401107034140608800c220000b501000842d002003880c0c82200c58011005001c54507842c90034905080d070f111148801c0c0040700070720702c40e00801102030008085 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 388771564 1250 388770314 388770329
    0x712060212250507060f02040303090815010b04090906090b091f05040201050403240c0c021305071e050906070615061704022e09140301110711031006 66
    0x2214401c0c800d04140078030000340007607050501c00c207442c0c603401d58081050724240c1c2d45140190f622005420054050181008011000c9100040c00401d143e030240102055601c10340c00e46562042d5920072641c803000178040c0301c0602400f04420004242581d10101c51148950700c0824149102e07103660340000822140300e88282c114213100c0c44103030440d40343e0300007458121400300f10904058000034058000c900004006620520b01034112184210151034000c10307044041c003210210306002410141240300407030241c040480c041c502902e050203102c0c072402181d42c4503000d030084801c1c03100010340b112040c10f013440000c003c260039030b4680034000e0070b00d14003038807000c154004008030701c203001c880c00c0d80480100030340301c1c03203400490301042d0340c05800ca501194001414801c0612105884015404809100e5022040151545d07040410801110103031106c6404201c1c1c1002414240c4005410921603000200035040008903078411141d040c04000d412500b040d080c035113051048a490341c10615 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 388772814 1250 388771564 388771567
    0x3020a051506100908060402010f120603030e040c020102090d120507050708060106090e090723061207260c030c0f03010306090c0f050609040f0b0301020d05010819020303030106030e07120602 84
    0x1602d07041c82940040c1d0303100b561810082182c5050b54030703500d5040241000741005550b032070700e20000c0d1184041c21031400012008000660340e91502400c42c2c14468082409542400b00301007400e8010f109541c1c5481d17010f801d12807040803c8d0740f011040c00f6042002401e02000303000341e00204008109010250440c2d030002d0209506181020304002c5080d0320554080c011032b01040241c41c8003041490071100f10380c1c0d50904e820324850a4200d52100f102d802900140042500c1170944190380100d0f004400302d440fa0101d0803110541c45080e03a0205400098460240010419100c010340c003c517803040d80a0340c1c0c1400c150724240d241c046a4402c1e442565440d0302c54481e20240869103c1761001401c129203c01c440341e02e40304c0071030914007403c0d158603c0303140e4801b01c2484404603134021000d1500020001c6548010100001c4010003081c040c01c00c0622070000d42c03401e00186081d6960380207400030000c50440c0c1c80e250044025000d00301c0d0718003c1e03014985002403544803100d1440c540c10b00c03940740035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 388774064 1250 388772814 388772821
    0x3030206040c05090c0a0e030102160303050417130e0c160c03120801060c0f0f1e15060b09060d0e150f1303050a0c1b0314060a05040b01050d03020a0515 67
    0x1410781c041641c002d80d03c02e4142c0703001d000d1480300e41400c80b56a10039038280b8601036154600089e009000e0b001640b007922a0300116201055407541c07105220354821004500c1503070701c16001c0d02d400d00581544001c402501e003002d00000d0b89200701c0941c072505105040d8681510f8801c1e000c00da01028070220380c40c1c03000c4901401046094030880540c1c206500d0701c07100720740c54038200800c500241c8501400c5e0507200c2c502c1c0002d00030303114004030720190400b9200c9820341040b0030200110310449001d450900034803160743c120201d5806550122588050b079203040c504100c0030404103a00c00b001c0d0307042040e038956082d00c0169081c00650307462040202c0310041840c00805a5554039002440040c000304002ca0020000303800c442a941c401c206442c2595603000145803022140c00305012504040c1c9086000000700000d10307440003449039500041d140140c0b600c0d410340b0184d9000340c81c02004003804100601c030b0390030000c140c0c606290191046a5041e81c6640f129414000c40303001c103400b002000740c2007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 388775314 1250 388774064 388774073
    0x2a020a06050c060928050f161e030203030403020108090f07090b0108070e10030f290411070b010306051e0a14010f0b0d02030c040b0a0f020c060408060f09030f040303020604 76
    0xa503805142e0304090003440f84681c0117a100c00e40700d48800e4441d18107030a54402885410000017051003030181c1143c2c1c641900075844c0126900d40c1c807807400145520305502e10311403111207114044a0b405030085060506550040d144c1403402410451603109003a54004058000c011400c014000007500180010800c00018a0b201c001051401484084015020b041d1a0840209080b10180c87c0000b03003110510300e21400b0788039802c424280e8100c088007140e402e107540950a480614129810403101110400c0c0f000907001c0c01902508680d01c0c000104007260141d000b599006011a50a0900b20040311404207003100a03900d00029a179908402d00d5150f840e440b06602600d820080803081a280900d42c2d0321a04c150b400034512950044049221801203d060750050541404a162500030010009000c69254038541d4014450344003450b0300313401c00500701e07001d50700f845018000359607807517540c08220340c409030110b030261100304120701c2d140301400040c00c060761207580608140e040070b051 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 388776564 1250 388775314 388775323
    0x50c040f02130e0103110a15030b0307050d08091311070f02040b04020301030b09070b03060310270b09121c0903141809090c03060621100f05090d2a020a06050c 70
    0x51b040c020b412030741013803007001c0f0140b4503003112085615010880001f0900440d00b090f05550206410882601401d001c101c075080c043c2507103010503152894030f1200c1004060944a14002692003400c0030840308000c51024090b14010300c1c000750010035001a10000700b001c99200360320546200b0001403d0003541c440c144403001c01050104000780c29820030700000b035103400411005014140e80c400c1410f24100342c1c03945242ca004808220f1140e114514203010400141c00c031806210b60246584000440a0b108140e50955051111411090b510481000003c4c100a00140e0070710420208244100c240b10303000f00318000e201490b421084000c00d0522108001c06000d11000e45c100b0030510301c441d2400a03159074041070071039014001d02071030004513881d003031003c1285000b0700803c3c04082e0750911507000b002d240040f09808015564822000b16128007400080800007552600204d039410311552503200c1c0d40500c00128442007010b0350010703107000102c1c0d04c030101107440850311205801c024003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 388777814 1250 388776564 388776593
    0x90e0a1b030c031b14090f03060406330314011d0309010201061d041b0305010c1d09070206010911041d0a0501170606061b0307030806030c01030603050c040f02130e0103 74
    0x42d0107031141120004d002d402403003d820103102c122404200340500b40c0d07440e41c4503141454043d064500c281803e0030b000c005868064603545d070940216500c2d040d01074141485903190070b90a150544510706642c2c40702d8800c0e0a00c4604980c0b5074070361984648014059105d40705070f00755070000b550b030351065a00290035214990310003015803200520b034500c124940104240d000e07622201a4071107100c01200340f40c000b03030143c001801d6586040301c14414190044052642c48080050142402c000c00080041d6100102c4014005070081401040003200a0304900e9142100010b42814507445004484c030072140340720343d020b08454000510103807090710300c9914050300d0030001d103030741c0b521040007842e0791000d0141c1130602170580000e00c000198104401407542e15020420750703590b400f85050003401400150340d014480d0141607502c030640d60180c0304120403a42d01c20041c00200211608000081000360304000007a5000c000c40110104c4120700c5401801101c45101000d505504103440c00d0359401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 388779064 1250 388777814 388777841
    0x50103060602030f070f0501021921020a020d0f1e02011e090f0308130c080f060106021f180209040308010e010605070308150d1e11090403090e0a1b030c03 68
    0x100304c05820a80e0080882d00365642102d030a04030a4483e1a01038024801c0c220114550103450413030f0b95001c0c0e8003060040070000c512000441501c0c49001120492203282c81410241c1e001007091241c1600515001441201c9820074035084103030b03000c081d00903032468084400180d40d1110011013a0044250388220000c0740d803020044180c80382e4501c0781051410101400b407000460001d14030724450700010381d600b07500c25505034102d41e4641200b83d40c0d841100003500343c0e004070000820391901c00290f4000d00d051132106152190980d1901c071008068050781d50b806944d092000c00f015071240310100e402144291b0718480b2070361500c038403a00000780680002c0e0803c801086071502190340441c2642d080000f0001c0c00300151340c2c10000405a41d070180e0010f14200e400032800c0000c0b482180300c2e0305068003d10001e18841c46000030002040c504131030080c007080043c0418800b22038240509039112004901c00612520403011648681c50703640380321170001c2d8031100440381a503454000c0c0c003501c2e00301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 388780314 1250 388779064 388779067
    0x2030f07030b0601141c0605040506040504170901030b120f0708120403080a030e010e0c1014040b070f0c12110d0b0a050c160c050a051c03050708121005010306060203 73
    0x7159920032800c00c014203143e0412200400c0a00155881011220301d03070410040329924640d03481070900608606e1141134407030342c030b80f4000800034204ad0061a01c00c0c0e90100c200046e0700072402641780a40c2024141a040590f5070b84e10b404240c4500da0f503a2095910f81d40141002500024103a1070205547c00414003900b080c84019984503030340c810786040ea94400c0d1103a46500700410304400030006030040314040d60811101d449007000108072034041200035074006401460005040c1c40d144c070ba844141d81e2148003003100300003503640780c0f000d1318101d4400d40c1c0705e041c0c0400d0b0740c9a0036800d0070540c00c1098030241600345071080100c4954251051b290070703600c1c08241d02d500c0d182c0d00c0c00e9110080000b0030094607000014006000c0d001104d401100c840d41080c4400828240341510780301c2400f03014056401788502003118a00324a40701681021a884a074181c012954221035541124000300c9110b6002e001c005e00e41d90040b805d80e0301c40c90100f080043d015141400043c141c2e051640241d095410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 388781564 1250 388780314 388780319
    0x315010903030c030804060b091f051c02060a020c0909010b0405130b0a0c050c0d080f01080102040305070b18150d1a010207060e0604240f020c0a091509021602030f07 73
    0x10000d80100d00741350182441d400355904c030306203080980064440342d544140281c00308041c04880303106c548911421100c0004440c0e84a00c14000108054502444d212000a901100515040c0010003c1c01103030301c103440c2c0410340713107010034250720302542d06030807503511200200111b05007403023800e41c0700d00400190307680d080054a4000729440007910305100c80c1c1d21100c103640d4140c0a14212400658841d0807a108002c00c0d400040444d1070a4402c42100c003a074400014003034005000351402e403a000005003400b03a140000769245640700707604c284911021028400844d950301001914501c641c0c030b081a030788000c14080300e0119841c038100400302c10714007900d03900181d0340060a034050701c040d81403038205400c01c400094194051603124802c0288003c84145450080000078440480d103a00c8015103814590000c4c0d032202c6102c41a60b420801c1500c0c00c0160903601e800400c4081003000a607890380d41c41d0021201030340d0111001480700d21800301f201c0c0440c202040341c0d0030710101c01009088050b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 388782814 1250 388781564 388781567
    0x932150d1401060512090c120102130515040b0a020a020402040924080c120c0d05150702030f0f07030c02030d031505060408070b030601110a0506012d0b0a05041802031501090303 78
    0x500c8140190030100c0030000b0305140c2e0810881b0147c50303000302400c00704400016614040d41c0b02c0000501c48140704a00040d003400c02280029507080031100007400c0c14100020020150003a44010b011840b03400450030140c0c0340ca20091010340120040443e000c1040b00352055048406080c1003803030036580d0010800344002080300c03100000100e403000c10300c07000703180c1d50b030300e008002d4091560002e48949200104000051044956403580b011103020752f884443c01d907103e0144d20f21310120030404000300510713900190000c10b1098403030b060044814403260042842c09000200d0000401d56a0404a401810700c1080030000e000c03c032009460300781044034054640380240b0500e280c4000c044003284d5180c0c003400b010460f02c141201112400001c500784699502d0083c42007042d00040010b07200942117581d0b005074141c504c1031031006c004914180d85209144d111050a100b0401c040c4400314162140c2c406d82d84180300404e0016032a424100c510b448451040d08100e030502c00300d40420400203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 388784064 1250 388782814 388782817
    0x30b1305070e0a0908040f0501080106080705030703090c1e0e16090e060a0302100e090705090f010e01110f0609070e010e0406021602041b030b010932150d14010605 72
    0x60364655041c030102e881e020180c00207000c45000c0101682c45c04034000c10114003c0074040d0490f4400d90341c108903a44e941d401500d400105960346800500c041000030f003402c0c0640c01000e1f50b6445052804c4020b6515002e030070b40c0c002104c2c14135a0401e00c00c0820440740140b44445034005c100e01d00f0f40071080410003000f80100b2a940700c1d10703084d0f092007000520190340d040c5540c001142c0180904c580c040070715100400c1109041041c40c03040002d500414901c41c82841038908199024008003c288a80b100540b0076180081c0e40d01e04220290600311a545c40511406040d0712038000105000c1c2003c8080c2401c3c5030351504044039804a4a00401840c1d050126403030b000740e00440d005135101001584071580303103081000a0b401c44e0601c10522542d01581c0340602e03900d22655020051018180011034450409200d020072020707500d03074844504142a881500321030084410004d2074000d21002c959400c1c5000351281620300c000c25030310409500c3e405040e07051040008072840c1d540c10840003410700d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 388785314 1250 388784064 388784069
    0x102060910050924010905010e0c0405040509120a09030227060d0303230604050a0516050d06081213091e020a02030c072601050c07020402070203070f0f030b130507 72
    0x1a102c002042c2800b20030b00c20300c20001c03402c0748503003401490000300c3c80800b0f000303203c3c1006081c5003c000080000c51200c040c3e0080542d5000139150928103c10000509005800b20940c3e0042c9402c0e0200c2c09240f0004018010300307911203554461a5004001001c60181400c04290803004c2520200540559000741c2c400f004071081c0144010608084004095070754143c003000120682c071394203c0329104d104a108903402c9405000c142d6400c0218015a5030580b201c2d2040d89400c4603502c541401040600001811200d00060407507403040614644917006134460075a000c001210200c070090441e40d20042c01012106111701c0418020280c46a48000c1044070342540c007041e81c0764000d10030b000f1036141a8100085a0350b0b140c4804c0c0706040e502150000f098003031440c081d030007503100041c01800e208a9001c2500c0d82001c00c00c0d000d1001951066100700da15025002c0b021916116401c1d42ca4042c04048a00b034010704d085280202ca05035015040b80c44180001400c90005280040c03901c06 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 388786564 1250 388785314 388785343
    0x20109020f090c0c0d1e0e1e0f0901090911030f0d0e0109171612020a031e05031803190f0f150204080f01230a050709171b01020609 58
    0x30301d56a8011200316409014542240c038091614880a002d40c060f104117484001d406070629801408141500c40d140e55954162300041080c60300310003441683c07000c1154a4001d0518841003184000103903044d1401d030030050560703664034944024003900a00e0340c0d12105040d001000646825038540d681c4030031078480314007003111400380210281d20920000300240358044414215120b5459456200d05007000c0f04165000d400e0400030304c030072280c0c001200c40751f000b402900125045448003071610201b4056008098180201d100020f40c0400c010148580c00c42407030354134403168404141c00d203504d0701080c00d203054099804802140810440039040c2c2d40c007c5100300308680918241c10b01400b80043c000c0c55030f10118000580c92004500f0000d100c0090001f0462a500581001d102400c101c40c004442e420382c00004807000801d03482203070400b081c1d00300542c0304d513500c40c400003001c07800d50031340509030b049003000b005007011000e85100204006d0026105901c1e124800c179594142c1740c0200f01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 388787814 1250 388786564 388786579
    0x40807020303070c080606130c0f0302090307152705010e1c020301110717030106020d11070305010c17090a0809100c02060304061508030f300103110102010606020109020f 75
    0x1046541c00c000b250190359205034190a042e544075252622160b0803502d05010725a204441c80044403a403050614001300f60305c0f21060b5442d6400100c1c001d40004070032030b07050b00c114079004c60080f00842e00c0000048003a541c03513008440340078030110239851469094443c03448030001400203a810007154502a6801c2e1600444c050333025030450112003503a8030103034065180214040080a008000b04085401080109450000e08140708124842440b44000580044107011481446100c21517942c41c0040101d4007002d0716621070a003100d420130310350000305040c130880904190060742410751055400001d010030000c682c4581030103101c0d6445052242c0c2c3c0d24001542c8440c0202c100e120b1594010308401d41303c2c941450410000c0681e40c004403022082520000b441d09000800c890140000e242180c0c00e101c1420b100e5084003c107001082c0c8a20350961008554083e484007090082d4025150401c040c060324002908484094003d2411079040a440d4005611803404080d01d0310070a95620 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 388789064 1250 388787814 388787827
    0x50607080f160507051809070312091d0601110313050603060a0909060c03062c0c16050a1506030309051306120606090c0f0206240406090609050c04030b0408 69
    0x18401d40c8203521409a55284103541e40003400800103154058800546080b0a5064200051140480200d0707048800f98000b40e024000180e040414421400c600e00306661110740703d03104c83d94000811325080524500c001c080106940e4030010441408000340c0c0550324080c6c8800a0800c40c400a01440380240400000310300291111030315200100f030288800c10030500c0c02d14103040a41141400342c000a814540b010070801c4080003030003500c0407038150504903038001100c40c0c203080038000d0429400301802e202050070301c40480101c0c20054482da024000801862520b20020407003035020503046881c1079400d04c002608000e440090320030403540800180203001100340034050940280e0b046264503600082004501d800c504181c1e09200d00034800203160346412604400c0d00408034005a211001203078442d02910780c00e5881189010700c040c0d07a1032242011800b601e440d40d004c80007556179402d0411400e803c0d4860381e504000302d114400d0ad0149503807500b00821001810203000c0f402c0c0050f40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 388790314 1250 388789064 388789087
    0x501080702032704020c0c0423010e0907031a0907060503091b0d1b0e0f0f07050912070605070c050d080a351e060307150e030102030408090a09020405060708 69
    0x80d090f05900140199a81c0c131081741c4070b03034682c80c2c4540200c3c0100c0c286a050000032042c18030140e400d02c07015a600d85d0603841c140ba1610000400340c40c5a20301e0040e00307804000700d403400300000703005980402c1100360f508050010701e1900c645039004004100c2c061080c070500e14008940041158440032092404100060000c0d00003000400000c0001003604559811240c22426000844a440260400940e5484411151105c4c22110301c0c020541680004481c180660041d0580031005007000031402c05128656280001360f401c01c0f00801c0d000b18801c4108400e05003c0b0003c1e1a0a0b507084040340340c255a0300354039000e00c91040050100c49207c80d1520305034a042090b0710303507a8134414542c82402c4d00c14411444020707110007007000100f091b114011503440c0c54944c01844050000c02c5080c0c50040980c650416840f240c03001c01800c40c85854943d5424009540038a0140c620a99201c1602081000b0024183c1c04110000c0c01400100311581d542d200307494105801041065070340750142c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 388791564 1250 388790314 388790377
    0xc120702030c0a1410090f15110105040b0601110a0b0114030c01110a1412031312030b0a0e0702010216080d200f0322030807020105100f03020f0d1416050108070203 72
    0x2c40d880789002c10340007078441e41c14555070a482100da03c1b442702400742d070303503607542030340e400b00c1d000f0302a5201000480d500754419180651100004c1c802d4845143c45580c65500a43c1e0aa004401da09000d02000c041842c0902041d88070004c2420310440819034000010388441d00188003a003000f5201403446000030052011540076240611515500e15102d0380440c0103607002d02c82607516060b5808841074a41c02842110380b480ba00030111504545010072241c40644c00514010440d5000e04c100030003601a00380381d0703a900d480b070100b580c1c071503408803d400112464003000000410311030603a42904900c0004842007002841c0c10281d076640c44421107040c0d40e004c034000008185888107070000b456032000c403460007171304180e000b40550303112880303401d8048103140184041c045589070100010f15000c0844280c85c2000b0740707900c0884207103031290800c23004505207038501500311a07502d03040c0c1140c1110400180c10309080101d05418824402950b9024600107481c040070301035074075214840c1100317 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 388792814 1250 388791564 388791569
    0xa0909050a14031903020a1d15070b0414010902010f08060d0812180105060102030a0e13020319140411040504031815080c040b09150c120702030c0a141009 68
    0x50200200c942c100e0207035503a480120740784600e0b4904907202c04030510038022030302919003542e28110030001d000304510181c00082c40c1d076544286a0400305640c100210003901d2241e00034801d2a40e80d186c14180003040a40d41c6400c05090391400345030100507a00f000780091f80700e4140c6000180c69481102043d40342e0030000e4003922200010520291464072031140720322808141201c0031106c1419a00e00303080c0c0d04150340c041c0c00350b04103000401c0fa45100d807107070006105c0c006081040d1101d101248004a80c01500d84c0300403121010700308240000b0324083ca00302c0c0c901001c00c0d0706072460b2544842c86a503070240022071150f03440d480824141803140702080d28003550261540f10213983c03190304a01e823010000071000415000380000e51240c46140079a000c481030344c908a86407103000b00810642e4424142940c602c0e0405002e420210f2408104070356096101c80c030150303034a0056004042c540004510700500c01c2c0b414010904c8118954040003050708026580200c03110341d040c000381c80c64822034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 388794064 1250 388792814 388792823
    0x605180301020f09030d0c02060910050d0e0a050d0503010303121119050d06122001021908040518190209010c02030f0703110a06020d140c010c0c06050907050a0909050a 74
    0x10866003a0540c098000344813400044040301e254400d02c050994207031081c600d005e94011001d00030700d01c1904001e04460400405854038516100c4c4080099045a4a00c018240030b90b21103044002000400c108030005c0c01c50b5030404908541c034641d8014411303501e076100d8465143e01d82600440500071007065072140a1f030500400764104403010020050f0704a80f1546820030b00301000000c50450f0f036002c900540c0d4101124401e4400b0010102c1e80300c51002464604600c40e01c000701e41c802c5c21003a000e40300540f0030400e05980f289088104205080880b000e502a22403107018481410410001004043d1100303901584030310003000182c1e86140040c501a41600502c0c21820411402060150035240704446e445030380c00d440c030240300c0402014056400540e014008800e0900d0055400c0780007041c031280c0240c03820700d0100140c0d007950718060442004ca08241d0b040c00421845007d000d0744118040c00601c450781c604000500b41c0620392050407162640c0d910355805001c0e0521500303032480d030007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 388795314 1250 388794064 388794067
    0x32d010915120605061003020c0c0409020f0310061d090a0201080a1806020415020312040303240e071d030a020d0809120718090b15190f081006080601060518030102 72
    0x360700b08100070b040d04a924620a164806d240c1c406036005e8400d940b111130044000300802d401075424400248003411041c6e0784001c070114402e003980d400708074107603000040380008240f45181c004c030010918041442c0109400b04d00c0200071030780300300040c2015042c2e024039014005468030394803400241030f000d106030666070440d5080411b0100f6600180300b140c014200b10000318092000480c1c8070300070b990441c40324042400204000c0b80c030a8003d00200840d0503003056400c4114144546e0000c2c0e00e500c1018401080c03002c21804030b03000256804070901038500110101d2503100040d45070701282000922840300340030308009100c00c034401d0302e581a1000d0b00400c0007401e1000082e42d1001a44603040340d415070384140b5091203402e07000f008070b041d91048141c104d41c0c58031200082a0340b03d418400da049101c0011860001031040321920051450192040e5028141070303402d4180a10007003641c400d5401d246080107070540004000741103642c64581641c8402208030540e4a060010024945c150700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 388796564 1250 388795314 388795349
    0xd060b090a020a0806030c0a030f32060f1614040512060103020a0909020306010303031e090311150103050c04020f0f04030b010e011212120b03010908032d010915 71
    0x250740d8020009140c1d20703215203030f495a038641059600c400000c41282c0102d0810350420001d2441030040740b0291140d4201d400600944400d035009091b00c10700c400904032000383d05800403200384501c40e08582200e640c84500e107010703d006a851080c05840c00108480200419024070341d00090350080c180c0140303100140d8a05030344041d5907040030700041c1c1c0300f20f14446000880749164801c0b00700d080e901a003d4207881c1c0c61034406038014003684c03900c0722500c60707866400103040c0c0c00d03071081c000194860740350005031154060b80d86152910b081c042d43d03058001c0000610100e20001454510345e070b8100c0d070150f03448284100c51542030041c00400c1c0c82072580400c001c020000021a40d81c141e03040c40032100e00301e03aa182c5110041101d40f0311701420340c050142210503ca0b10806559504c00c50b00080803585a40e60008603003140d841103401da68000001c010b2150855010501390300381000d032002407984400d08500c0801000040c031507140030380d9032400c8040140c40061a50030050040d441c0d2401002e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 388797814 1250 388796564 388796581
    0xc0f03070b07110304270b0607050d0807020a030206011a090904060203091204180923030c01140609190f02030c070201030b0a06020714030307061d060702060402010e0d060b09 77
    0x7505559140c0442c6480c035002050070800001d4400712076036030b0103030300700050114848080490000b1007504070a840300055000c580320743d401070070300b103108400414440454010040402c9000303445034045411401d45e200100c1e60004429055422a00130a50011a140103529441c415007203850382090b0340c902000140500d030fa000c0d62050310990151040954030340351030070151040f40503095075403181521034203c1d500c00c2e5004401c9a0305c1805400001c202a40201064240350b84640040358000100c03034a1000e003c2c014040b103030740300d900c2404260a0007000603903101c0c4020300300d0651044850541c001f47d051394011441d0003410500c1150759090048010500754400c46059010900700480605a828108024030440e40b07541d0152100c0740c1400d10900d4051002041c2d45d42c188400e20400d00403840500c03031000b030a510184100d0b00c1c000045420350800c3d00003440d083c20354021904000c0980d8002280004001d001ca420b0f0120800d80c0c5001030081540880701038020695808021f03048 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 388799064 1250 388797814 388797833
    0x30105190b09062d040f150e130b0705070f0605010501111b041a0a06030518010e060c2a2401120f05120a05031014030a02060c0f0307 59
    0xc200c04414050388500c1000d1040d04003054444940181070848111000c03110301c1081142102c0a41000d804440098005829a1041c0c03046000311941e82e0744810200040c500717858001c1c50010240806842d0038460b01c541101e01050160070307444118009000648a14100c07441f25500282d00b102c26003040c14204000e0609001c1e46d0f012480001603a01d1300040040c8000281304480c42c0324540645c2c035003d200143c42000d910380341c1305007d09000c010035920900344002820250343d00241d0346c6092051041103801008002000e6454900c00c510050004116a68440f0404070420b84e074250102c10000c0d800e000085003040e071084400b03250404c2c1c2010400e00c000006086000c401c5a074076002c0703c400c41c030b401c1c03041250b580c0750302c40071800040401440c90003c0f4020380c03d403140008403524641c0e07198019000480002c10000800c246080d00142020150200d4001841107420900119a0300c681d0144043c0c403c100209a80a6941c41005203030051a40d00e800d6030745402907481c090070079 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 388800314 1250 388799064 388799101
    0x1505072d0b01050f090a0c02070b0d1a01050c100c05071203241215060e0109050105010207060e010509040506130f090b0f071704080909071d060307091a09030105 71
    0x1801d0364800006040c0c5484000601c5a120040101c00c10751101c004050040c0807a9103c0020b600602c407000a445541c54060302c80400d8100300801c074401521503e1031a0080340307030b8050600105205110901d4000036408000302200100010780c280000b00a954600501e4002000911010840100700741e050300102d42194140040e04004403620b500030103001c03413600441658905071121700e808a070803101c540c802c0c0303034015000064541d151046a00e282c18241c000b030603221b44400c0100311075641088001300404c51480e2036014085804002460b43c418403000030311440c2c80d0801b140059440d50603125240404110400070041810041d4000c0c200e132440a45a070440c1600144070340102c8040d81e0710800d501c0e620201000c001000f00e07541c0b00c502400079503514205008401035a1100c901035802140c06441c0c8018a041c102e1340040000c402200c140d000b85000c2c818095080d070410000b80984220b0340700480d0301440008000380754040c0031407055056017040107008000d818100b43c00103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 388801564 1250 388800314 388800323
    0x60d1211070b21010501090b0f090616050601080d02060c09010c060b10030b040f020301050108010e0a0608070f170c01210e15090f03030601020c010f02150c0d0609061505072d 77
    0x4680c0d1703074030056510301024440c440c6045010807039044440584001043e0110004014600340032403500c0c25100403112400440311548020300520281070104070030100c0341100d2009002c24607107083c5800c120f00034000350b076040c45644242d20381000041d8020984d00d0318060000311640900a40084c041c110740c44c0a580654075003156040482880e00841c0d041c1c41c41a1034030310540c0d18010b460f50a601004100c44480343c0c3d14003010407005000d100c2d65008101841d8944900e50900b1008060600c402c0c500a106a0019420744240c0e41c002008030a04200400403821078481c1401d4030014105d00c0a4111180c000c88040c0e00c00302d45540c84090003035500c001110400c00c0c071107440d5650780c8015203045000d60301c50329404d83c50b984680071f4400c000702c4034416074002000908852441d04070036a8001e805107c04990080300d01d83e0b03841800e0080c007d2000031300200745814542c0d00d1000c44604610b0402000003128014040300f110100807a1107445020310401580301c921224a400c100000c50f0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 388802814 1250 388801564 388801627
    0x40b0604150503060708070c0506011805130f0209060a18090302191a190914010f0c08061e060304051606032307021002160209060d1211070b 62
    0x210001601c10700381d007034030300c040c000303000c41e0312420710986007004e00030048001c00c01d10b10441c50000340305000450003400d00054441c0600d50032002c110580781c0c01410b88910501d50204d07100820b0007048600c1d003440e0140c07124881a1106c801040c0e410000d500b110805200d180000440400c20703906c05550710f07000f03238281e0b400450000d0b125055a203420390b000e0980005603a411003003103d0f4268103600031621441c08403540010706116410381d1081c00d410360b5041e00c07005004c00703000000c1c0030744001e07031030a402c00b0001c40012000260180601410190103083d4802907071000c80c0e81c80384107603c603c0008226540360720b400d1034480c3d900c442007000f46561480368600003a07128040c1c0540d208102105400107041c8420307401101ca4142e00418400c2103200e20390400d46005141d1006100c24030040f824480210618010b01c02d0700000a052503020316640c54500700070039221803114a4965143c9040c0100b1030f60341603098030307041007600b042901c8500000c40580a241a00c40d00460f400a1803489 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 388804064 1250 388802814 388802831
    0xc1407110a0e040308010603020f0d060b1308030a05040905040f231b1507050c040c030f060b0306090f070c0803250e0105040527040c0602060906060303070f021206040b0604 76
    0x2e02540815a00100410394120041c0002070194014040c001000c2042e2400e2034150058803040d54101c3d40803c15503e4000785040180300b010140d031010303202c031100031494034507070001c01401c40c801c621540103c0ba54410101d0100113480d8160701e801500000784251004009080b10820a00f0705100803e511a00340018085060002d00d10300c8064014a000b0b8041d0402c1800c182c2607010b0b000844084c012601ea040490341c41e440380079001c1e900f941d0002500f46419100d00b08440d41c80e04496815602401046003541d25400c1f001d07400240318100c0d8665440300003043c3c070321924031040100404804001c00280d0b0104d442041c25407100c41c18900e100074022402075580551840500707001036803c00040c02203082c08134902d10410700d00d00814503207071851010340c0e0302082c081d074040724032940125040290603410044603400401000140100d42840c10010340c0e00d200d6038100030315000750445a14150340c1c1d8600c1b8002c0c4585420309407112440d19107080c00d503451040310207a1243e845e04140c1c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 388805314 1250 388804064 388804079
    0x305120307020f01060e0f190f020306040b0a080a060b031504030e040f0b090f090f010f020d0b031b0d020f0603040606030c1409180703080406050306031912030c1407110a 75
    0x303003021202c00746d40704049500e034100c200b103401e00300800b0482d890401e0f0300ca201c010820f5200320403015464000050712410140104010344940d030f100d5030710134501d02c034003441000b0011541520040d0301c90302c00102c014407240480e0501404e90504ca0f1100110020003003450380028208902d00403c540c200405048420304004503030203c009560014000c1e4000341d00f90181d40d80d8640c0001ca440c080780e043ca60001d03030403400c0d0703000800c6403809141c02280c489411959070040c1641110203c01034a80780c0520402c2004101010a0042c85050b40699007403d40d1621010407407400400f800c00350752440c081c104880a00054402240c0100784c0002c001484560300c00310121003400140195950703211040981c800710200040043c003030264207000000100140e00400003003006841315030322031400000705824060702000c41c030b002081ca80b2802d800600c14215648165806080024900305200c7c07084802800041c507482400c500051081d051002441071903000c0c0d403003100d028000c00d884018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 388806564 1250 388805314 388805321
    0x51b030903070b040206131d010f0602101817070203071a0f0705121c050109050106171905010f090b03010902060a0c05030d020d1406010c0803070311040305120307020f01 75
    0xd40c80c1060300140718030000107a9580046400c07030700040041c1d013040c07001424619a000307503600c0041a125424549050300510440c054010309590b035035110194988400a52645030075100a0b5545586040f04400807060b00b150308441e42d000442007550f45513409221150364020714041e8840d2080f003100144a03045c0a5202c0c13200c049007401981499480c01e8a01c041e908210401c5901e405450101142018490040d001d1241e80c100030001c12104c00d10b540013150303010703003281150a083c600144001c98200000c1c06907003052582d6000780f80c1d6007071400c0b00f65522420102401d1414000001094066000d99006413020301408000c081c208008240c22039044850080d04824140500c1c480180a81550104940110140c030309c1c001000a4081c101da00c51610003050a91f40c1d82c00c0c40243c18140341d00707940000e0a0800266030b81458950401da404020503403803c1545a5014000002241c0d090318021340d40042215240781241400200343c0c2c00842d2400010703c00c603161010400e03070500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 388807814 1250 388806564 388806571
    0x1062102040611011a0f010e0406090528090c06050c010209090901020a110703020915010c1403071109090a06110c0a06020a0e180f0402041d010c08010b0f0906071a010603051b03 78
    0x38945582010040019145844d182d1b0304561b000ba91003500054001142c051148a43c1e0003000070de40842911403074160308624108d00c1ea00962800b001c00d0f00023162941c41c002030b00c120303041194440f0382c8081d44602a1040c0c000c10380e000312810060110741d000c150050b1100840d03544030b5000034000d04090316501c1c085c601c406035001c0199004940900b00c16200103c10007410716000d00d490201e03458199042c14850100040c80e44005051018440740c0720780c0728030004003100e2542150604004003550707040a180301908461756018040c82613045001103580749015070050721641c3c0510300701440250080b1035210080759420f400003405140405c400460060707440315040094550100e00320264a00401c101d81041c0c0c3c0e10b08071071031810216204c144404460001007644010444020900034040e0302480705501e040c0550210381030000300352440b1075400c1d6411601c401c41c1e401c2003140300743e107019079140c05001c0100100d0318503416000581b007051078440080c884845a900c0010610045 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 388809064 1250 388807814 388807819
    0x20a05120903100b01020f030301030809130902010512070201150303021507080402010207031104020702041103180d0249030506030307030905040903111902150304020901062102040611011a 83
    0x80303c4411501050364071802c10480107104888290f04881c0100c0d20719403007a042692211404030308410075240c06296480d0181101400b401031a480d41d00180c414003ca0380a400499004800070742002d00c01d43c00341f40c80000c401c401100b420741d2410045e40b120542001003081003100c40001ea040f90207286101d004032b41c180d004012407451030301c40380342d0520410b000c6580503808000240240c2d4481c018140b480756010043c0303580703044c000315992015205035407060061b0400035000701200e801240d042500c0755000b48030746a000119030203080342c2c84038a5910000c04a0007402d10010001800420032003604c0d0b45040080b0b494210425a8030f0050944c010000342240c2070900c16410b1541020258511074140461002e0302e14078918106480015244884421074a0f040c0c1589426840580701c0c2c1d4010380300500d9400c1c1600480d4805c50140100c2c01441042d540c0b410075500e4100075041461000300c4210b40f070ba9150100203180401e00c0c01450b21960074038203074204400f0f100030000c0242100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 388810314 1250 388809064 388809073
    0x10305091b060315090705091306030c0b0903120a05070c06020316120c02041b12050408030609180a06050403080603030307090e061210020714030406090501030b04090f03020a05120903 81
    0x1032104200460340f00405115a06180d0b504000d1283c6840130708900400c2c0030b40316a600c40c80c0000900545140c80c800390070f40c071410190708001089412180c0030550b003826011641d60040d0002080c980210038103501030b440f13400243c1c030703106e55403302c0a0105c0c94401c04500b407007160b031a4812a0750f40901e00403409901c4180c0d07594000210907003039055100c21a8202115100c0a80e000181200c090b41544a00c52440c20076140c10285c0c0f043e101072640c52242000c00171828a83c855086601008008900409081002c00c241c403071700b510705040c01c1c089a803ca8142100ea490844d01419082d0381c200c0208406031301250302450040156482115180c0d11244180e141001603040303c10040c143d00e0708a41500010007074900d080c4804040166041409a0345581c01d1401103507212448618001030703082400240411039001c81108201c0d403091a001c0b50380a40840010002e059424008110081c403607200400c05402291300a941030180302903454844220f0b00c00540c0344240c0440e00c2d8140c20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 388811564 1250 388810314 388810363
    0x5030706080c0d091e03030e071a0306040908070602121b0307031109280501020106030201020604120e060a030c110c2101062d0506090604062601120201030509 70
    0x210502420b001c1d201e810300400d58a80d5a1109801c0e20080582d021201102c00d017410203164041c000c400b082c44140000340310345454980030041c10224580700520200000001c54401c0d500d0740c10010001d5007001d41103684010a25003500294403240342001c44618900009081d81d201c0c1400c1030507004440c148078903607038070001d04400811a043c9061111103041c040b400d400c1d100c2c001c2c40507007540150f0503840b500c248400c1584a450341540918116814803c0600040c1d901245094216074420400d48541240340429109105420402074000303c2c003113115400154990891010300c240c0c0e40310382c4419000e0581080c0c950040b030344400c0e0000c2c03155803030b0002412001020030113012b11100014146456500726041540c809003001c408003000c10140c1c84005044002d807009180071680e0038138210000c0d001c9982c2c1e001d1441075000f404400c90104111314001e1703004003c400b1501d90341840d650785800f107071075550040341010b0b40001c0c9407038002030b801c800000301010078021a039800400d030b45 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 388812814 1250 388811564 388811581
    0x5010b191b06022a030c0606060910080903070618030e3f030c070e010e040506070c080c0d02060a20220314102405040209060708040902040f0503070608 67
    0x40c05148141c4500d0352000510121528801c0c035042c445803901c01450340e8a0401d1050703487c002000d040b15118100401105d021965030b040900c401ca01e82c0e082c82806551088085415809810000b4210b00c0c01c0c03181c0380b2112101b241062040b14443d80310644084144000d21a0307800e41c1c0b9501d0360020810203c030b80401841038500010540810350601040b070388070441682580c02030554a50b0580c0840824040100341c041ca1602402180e00c0c1d0101c58607190329255031740e54000d44080305021201c070000303081c0110782003260308064a01c0100d4a0310050340707030020760741c0300101c4504d01414176220707003184c0000302001030113152400800325500b0800c143d13015507044030311040d5404001c07014410020001c1c02902e0003500426484000d020082d1a502c0d500e401d84900c0411130a03c50380035068000080e1844c405c44090320010398005031034240617400b00300030b40300e00c22020342607910124000400768900e40091007940ca08060f90510b4a07500c03403d243d95402e46000304000308081500259445 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 388814064 1250 388812814 388812817
    0x102130b0c12120f01060c030e0f0a03020d0b01060e0d0203100b06091903031b0308070c0203120f040503010f02130e06030715110c01090f030f051005010b191b0602 72
    0x19007041a6020012a00410030391540300508069140c010102040408245401014010940d5052180040c00550b030018640c6840046480c4211407500461381ca5844076003400c0b02440c1e014000422a25041c20003003940b040034070071500060291a42c0745084d041020b403240d100c40c0e000d4010107991030080001300107419006801500000d00780091184c0d0b68600300d0b414810102400b00c44c05560071810001c200c60f41100f0400824041165000c0c0040d900c4243e0340c0e8080550324041c1d0b0070b50403500c00642840c07000c0010130600c00001c02c40701201c0b20064000e00446100320005c0000c01c0d480241041030307001e404c9130000c0308217550808000000380204500e50001000f4180c43c6815218081040d801c070460040c1c10000d01070a08400d212401008518842d141c04d00b00a5400d51400001c0700e905403450000030000c40610800c281041800c004800200c0e407540b100340040d6840380f10603080380c0c0050b4040c1d107180ca4081e409000942c02a980d51980c0300580309051403115143c0c42d1034000c6d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 388815314 1250 388814064 388814077
    0x50a1a0903070f06020d03150504021602100e0108091203130512031e090109051e0705030601270e0d0f120c081905060607121e0f030e0102130b 63
    0x9442004400015034080c025140602981c00d0030541a6082c808003d01d40210f0b98621818540750001e0107981511603004a01151070440e409640e442c5900900300ca25100543e0003900b000f00b186c55040e170141c000300c0b4010400c10070781c1c40da14a0750391441c65559a0030000340a03e05080b040012903903045e0010000c04850f8043d00450321007402e40803040c142c5d503200f1075442140d51034040e0024820a034500d90290031040c1c00300280481107841d142d5940300e00108100c905060012800c0082030705c1c1c28482d200062100070141c0d4010369440586000c19001800b20b504417a45600c0018009a05403003128140508a00140740d2201c031074100f03490011000d40007100b80080c1c6100c50130444d015000f00088054183d60b01c20b00c0d03003800da0840c521988542c10072007a0070f0401c020000c4640f1404280d07030145400c4070810000020340c0e24240c0e80d0016500240c0b01e120543c00180075516085142000820210307a001c000b05503484503001e08034002e13070559054040c542b071410400c0c403450b1800740a4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 388816564 1250 388815314 388815359
    0x3030e011b06020a030507020c0307091e020c01020c190b041203290a061b0807020d0b0108010504020307090903020a0f030905030102040315060803040b0417100e010f060f050a 77
    0x8848a450700d840071440d4100c0040300c025800298030312902d0b40c5801090f802c800140000c04605e58080f001079201c0800b8041c00382480d035104022240c800c0001135280601c0b404000866a0314010301410303010f0f41c81a114505548204c0309520909415401e411003034980100300a45162150380d113000111004e1020f05040540f00e02c640380b207403103020034100c000000c508011803186946500780484009a0b9004505004180d030700200e50309e142c8044480c04035880400280d660150340b00141f6002c818082c00341070344100d1000400c4c050015800342d0700440c0200c08554080f50740341b04a50680f614000010300580054a003807001543d0100900616403290603e4441c00ea100c81c0400e007203821644c001d0311248031882000503440002d201e0351020340400006945014105440b04200d4861440f843e02100142200084221000d222801c0b0481c6555000e1018a91000c6854042c10041000284140c40c24000080000780800c9080413688042c000c3c05030b0078580240c8018007070889000d030f41c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 388817814 1250 388816564 388816577
    0x6020901030902120d111c0804020406030b04200f0a030204050a0603120504180209031e0c09420607060e06040503070c09050106090e0627010602012403030e01 70
    0x100594070300c1c2c0c0c0503003682c4039213004200300c03aa00000180340f400104040001a008040c0b0080c0072544003d0070326100d01c907800c210116868910100b002003250342e2015000161200a00040001a05202039030017080c0414103004030014080080c80c02180302907592008501d0b004000600b81608110b600001d40d400c0026090381d20784420005483e8a0041301c005880060144440d14110002d81203010718400c0845c28071102101083c1c0e1a20508200d40c401050041200380b900410800c4608000e00030700010003d0810541400311217405010b040b420440c00d4580f078100000c1000c954490102e41c02007900c03100b420005000d5503610102003910303010345481d032000c0c1955042142c5400f0340d103d40000c55803034030799007441c0c0340502c8183c00000c10701d82480010440140d00039603142c140d0f2012102034020b5261440007882490401c201040c400e030344819201010700c80751103104e040381c8980d0024003481503490b0006001050403c40d11011551108007030010070b20034000c1440c2e1450605004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 388819064 1250 388817814 388817831
    0x9251202190312020f07031e140124060309020a0603050a0e0a051e191b08010f090b011505030a02090102070317130510050307080c040b0a05040302030d09120602090103 74
    0x184030303030610390300240c0b03100fa0380e110310400e0369030304000c6a00d09800d0384024120003821941c03024031035143c0d180922542c04280b4110b40910036284d602613001c0380888003c10070a0080000e41842804881c0c820104226410380000d0844c06030140f05102035000f40b40610603410900c0a4004100c0a06502a0503136200c1d8400f075000070401500c0301c1140198010300006420084101241035200d02c10748280d0000583c41e100074062000a00d0300c50340c000c521084504071a100a80c4d075140740c5c1d01200741503091107100110034803140d100400c1c00d4002d4a120180f82e0b220701540880302c102503400c1340011401c01c002845407401d640a08650070b07051058500c0913549480708043c000800300001841c010002e400300c000f188504904004040607224640301c40c1000401034044d01000700080d0074401040005600c22206800302c60107080500382203600d03026520b10040082e046408102d0003841410714092041c0c2c0903039200000c4808016204a41c0100e070750314031020750845036480c2e040c99140d1005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 388820314 1250 388819064 388819099
    0xa0b19180b0703020105040b1003050d0e2706030d14040b070c0308070804080607030b060901121e061403010e0c01111f092604210c06050309251202 65
    0x200b00c11030003a8004074032800d082c14003c0e441c00c0e000c0c2120b581c4080d045c3e01000000c8010410240c2c200d83c0342031004980b0891000b01d1200c56a0403152007400d96a4000e4072034201000c500680541c0c004d80c102c0e142e07080c402c503058490314240b512654041c1c40610041010240c0b02c030081c0543ca12038a110000070707540c0e688424061300026011603180b0b0b40410184001d07202041103952065041c80c09200130300c00b54000c02c01511074900d0306030400501480600b210340885d0030603248100d84070390083c140f8154021000013030003a401280950384024550441615050041d813080041400c041c11303c90740c004006442051015500c280240510f000000910031007051f0203000c010004c00c04038000b203142c07a00030303a001e0300010340e0300d80d802009031540360214020041d0b60a43e2200c5602100c00540e1800340c10901041240090103c5100300c40400c02c035030b000c805036018515150403550f60391080100b00c01c50b500c45071511141e041c014502080805003a160104480340007500c44030400048244 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 388821564 1250 388820314 388820317
    0x512010f02030c07120e090604090f0203070305030a0e041b03270c050103060603050f0f0a023013053c21070506060d0317040606050a0b19180b 63
    0x340180075502c04a03501061000b842d00d04c00178583c2d540380c00182e480714a00000c1c2032a1014284c0c1c0d002d0740d5650142001c11200006140078190020308035902c0c7d07070341d9240c046c5c1c0e240c2c04400340500180030015040c5040c00c00e405022000070b01085a0740000314002011001440600c42401d2098800c018080307059511030014841319018001c0e410486040c40009010303541c2c03540c091010146410300f003003800a1030041a0380c0100310075030218115191030742064082d028800d80604030b0784042c000e41407205030840c07070640b0400d1502d500e2440f9940e00440c2d45008500983e02801d10740281c0b0131044e0001003030f40184a204500c1d07042044012250015140d144044001200140c0c8000d48c2d01040456030302159040d880c108140313915105165503801e4541d08003070714003030040707080840030003c041c01610b05404114040d0b00b140780c01d01d8582000b038040e00f000c0c03081d240100c210210101e407844c00380d012203100e22042c1e44000f881c2e4160181c00c44850000101b0311281c0e03d5140404031f080c0e83d404e030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 388822814 1250 388821564 388821571
    0x609120305070f1b0608160f140a08061503060310020a03061505370c060908070516060c030804030807020c03010e0705190321050d02130305060604090209010512010f0203 75
    0x28810400d412941030700b4840313010300d0740100090183d500100025400c1400d0180340b6100a45400720020f4001e03071042e01c000d4450000c80d01420b501003002d00080d80d00085140c4101e1080b02c4a0084040080200d065417009480c0740d03030140c110004040703454201d60024928400546400a902942c80c08108481703822404039100144000a2602100070a052941a1082c0b045242080f64940002c44144110440c00840605c1481c104003400d101d102e0b031249030f0564004400079554ad50340d1030f00e42d0701c410540c1d2070a03400d60405207010030b0319032241f240045610d030b0540310320240da21030703071410b8a0506004000104500c43c010714003807203480a006034490340581c000104a400d080108003da003240c1c107100e4101074060440100003041a106c9034a5248000c50300e03014030011403000c2141c6611a2000e0101060700010740c02c841d07034207002002021a401035003658015140d01c010001a80d07a6140c000c1e5001070350500601145c0b030404180f1002c18103140000508480f5a2181000e0381c2048 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 388824064 1250 388822814 388822823
    0x50618120f09090a110405010c030e0301060323060c090f0d150227060a0e06041502100513200d15060807050a030c0605030a090203062a040609120305070f 68
    0x41128000c40c10548800e64119072403003c1030140d00c0717810300214040e0040303114280c1000b41d03a65880301403600504e81c601d5030b004090028010607480703040614000503004403140c002072030f8420043c90303500d0100d640b0b40a8941c2e81405490a030824040000c81600461034580c0700b0300010080001400400404003100300a00001d81c494080807070503c0c0e072120882586c4170f00d0740800b80000d81c0d55640e0080710007880035420074450000300d20000c2840fa0042d500300584605103011071485a80d000103048000c0c41090000340902d989074000c2d807844400648000b0811014075482141d4040c2d00d1600c001c16036405410803401e004079480b0100e40c844140c45241d4890350342c3ca41400f12081c14440c150142806985156425245607070340490000c0c180300b00401c014000c804034041c8a15a048a0900f580060031640300f41030000021042d401010019030203030440e990b0100300c0300414010b61f02101e800c1e0f20340349020703450305a5038070b80101450b50450420404100c007400103400e5800058900340034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 388825314 1250 388824064 388824067
    0xb16060906020c06100f050a0b030a1d0303040b09060106140d090813030f110906090f04030513080f0706030c0f1d03010501030803010e0f061f1202030712110304050618120f 76
    0x40000411140143e904548c1c0280c010306418081035510000312034110700b083c0c10000c0e0900350038900c0c0c030050440d10030030b180302c1c0400428802803108804241d4001c0307100d00b0589213182d81e1994140d0380c4501d0412044440c0109028000d08510103500c44e5031520b0040c01d600c0c0c500b901200c504a28480031341c1003110718640c140e58006c11700c84146200020300400380c960404e076041190000f0419000240008080c11300c420010341094418000c1c3e4204003001034403604210345820355661038184a10a1071040d124115000552501c640510000085180c42d2101072810040c03044071100c40b07860311800c0d0404234094083d202d4400b403041c00c1c000c600030144292a941008501c581050700900141e800da20f0b0303081403054903514240c3c200c40a143c003007407041420350107500681d0300c0041c50b01c0340c550031840402040315958001e4411946184200390400441150603071415440c001500c4c064041d40c895400120b00c10054146040c0c10060b81d0704403112000443c480d020107034002451659a03000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 388826564 1250 388825314 388825319
    0x71407080a0507140901030f0507050612090d09061d031e06040308011e0506090103090b0a1b0c050c0405070504030f0f03120513020913061103040c0b16060906020c0610 74
    0x2c24003a8502074403103280c22601007004140026000401800064080032600d009041004410803048009281c040c00064544000c0b803a003400c82e84044400180c0ba005401e039030411075100712991016249a41c80b04141d405500103000c4110b5402c04c880c075094894080c420200d082081440078041f026400200428901450001d044100603030260f540c240c5403c0d0f510607919280c901d880140d074825100b2644801541c80100e000d48200788010740318111410600c40b90380c00c1c542181c500c03100301850042950702c83c981c007180c90f803854000180c0179400001c1442c40304c1c0b421f0340207140c005030540340c40340c149500d80e01c0c0c10194002121088800d00202c040710810560040c2c1021000c0040706020400e40c58907511001141c0c00d44040248662511000100a4980514010440ca130041020000640140480c103800c2d0300a8500342d41c010308070300c1c0016112035440c1c1210007480c01c46400810f220f403031380e541601801070440100c95040d000c0c41122140c03101000050f105003800c2c030740d810100d403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 388827814 1250 388826564 388826573
    0x601120b0f0306131209060909050c072111030f04050f0a17010506100f0c111f03051905041e061409030a0e040608030a2f0a150c080a02071407080a 65
    0x211703030b4850301c0f003070040e5240d01b0050030360007050803012120b20010218044d0b490088840d45442000c0d8028542c0122a0140d03842007001c1850a101541355200c3e5035800040f424110f03a00d01400c1405515003404110034000c40c20440b01a4627a00303005010005500d1f2500c4c00c0b44035800c0b100c26109070b40d81d034400810003a4a03100d0b130300c41580040e03400c2c21851580d25140080c1720070088080582000028001d10804d80c40b18590003030008940c07070b588004400c280344010007815055030081d01c0c6c1e4181c1c0d06001c1016078248141030155900072030038150000c84101041c441c40c031171442a240d0340d546506508000810314002840b6029080246aa8042d483c8002d03081840c0c5104090140b450424180203c460010456514113054100b105d45c1d2004400101352140440381d1350b150350b40044102d000700d46000140055000d11880000c2845112407032680c0440d400812090002550f0320b000c00e032800b400354000c0240d58050341c0e01284c85000514224034003441c0f64400805940001044824013 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 388829064 1250 388827814 388827833
    0x9040503272107031e0c05040509070e19021207170f0a0f2912030c03070b060102030702090f0921041703121f0e0601120b0f030613 58
    0x824064a07031840a024950225254040d01d41e103881440026401000d448201040041d0045a00c149800c9121800a41c1070742050f0000108032044954550007054510345800ba607845400101d004000300c0f850201050186807000d0074a9036038448549000d2668200b9000505000205c101301e402d0504055000801c1c00881c807200600c409400c90900443c00d44400d01d085d0020543d40010a10241b1400c034200284080b9002c040b00e64124500c2c2c60500440c22000042c00f4401c07501035507003200c82905603450307100e6020a050310360400c104910000301161001c0740c1284d010700c102c80c10700074250f0106520030b9050710998180741d02c1004010050200b0051001c3d40c8802c104a4480043c0c0c071228030700b1900940c01400161248030300110242d0f00104191000d00e01c14030b46902c1c0070700b00600f8009143c0c141652020b40280da88002003030200e440c020b114001c0304181e4440c0115580e41003540e005250691070540d1001243c025180300e683c0410485000b55141610494400b8407407500d1b4825 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 388830314 1250 388829064 388829107
    0x21050f0601031a010e010e060d1a0a030506010e25090e0702010213051315090b041404020315040213060612060503060405060f04061b0f0311030c0702040b0f09040503 73
    0x40500b0010b840700d10081043c68103032030040070b0030122500d00d401030060380d0340354440103016009400407a0056401c0440d8001c0c29007403083d045603180307107440700741800345100c11800090416408880104560600c0d2035441d41e02401d8207420300c7c9200c9142c401a030204104000d1074002441c0e107003080c05001d500321440c0c1d030400c0c1c5600017140703041c252007083e00d81c840652240710320507a400959411590b07142c0c0c0140b44148110001ca8181039101c54403d4020300000036003038003940c03425071002c001c1e000c3e03840c003140515001002810803142c0c984450700b11000080080307030040c0342079144002c3c1e01550301902000e01002e8641400710340051441c4c2088407001d0b4050f42c800c0e0300040621001c2200420101d4021040d189484080e940c1c904203070020b40000b01c1d40d000108004101003610950110303404188d0802e0340d9081c040c90796000014581c501054440c4800a00108510801490b05038414166100c000c1c05a06031541c0450002e080c40c030040350262859000064118910039040307100104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 388831564 1250 388830314 388830317
    0xc2307050a0308223204060e070f0207060909020c0a1403041701020909040b0a06150905031006150c0f020d080915030c07140c0901080d09060509060f030721050f0601 73
    0x20303e0080170340b610002103d01d0300600f22000041030042a41241c096a4003c00a081800515a170301c608205c1d2a4003200c840300090040b00c503c0c2c00caa440414188101c0701caa5840d803034641d0030608407500a6000d1140208103216140000000a032042d001c030000800e407030040d5860b245400c100410300f240c03000700040240d00c10860300301e103a540d4081a6030001d400c004408142c1d035039600144020300040d040001840310f861401b40f541540311015800f0794100750261a130b495070604800c7e040d28800d00458440440d001c5040e00b43c03902c503c1011041f60701034802c9000691040e00458141c4000c01c1090701c0ca02e0001a07081c1d1a400c16010850710030308074203501f138550315001d402503100c3d02076140d0080103e4804101c1031440fa0301000758a0301c6000c020036000003941c1d00d0680a81d03032842074600301d010803c031550004030036020340107032001c4410180400d0300d8682c00c507030b81171410360000307050b031040c048100c915402c0802d1104000b1040803503c4000505400c01c9404624074082c02411f050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 388832814 1250 388831564 388831627
    0x10c0302040503030d020f0c1006060e0409020d02100c0605010b030106110303041e0804090c210b03060c0c12030403050c0c09190b220506100c2307050a0308 69
    0x200a0f1000000c8507000b4001800050b203030200c04404d020b071031003551580c600c10320a00b540c4a00c400c030f0b55400300c821140342e902c41c4c081050b201024401034410b8005c020394408070048a000250610f156503003c1d007000e1b80390072030148880e940c9403011901c080e0001440f4000100040c080c0039004962002c019071700500030740c10741c074041d580c10075280c0c940d0710008100b00d4500303203490400a5440560300501101e00040c0021b01e50840c0c014000c030b8194115241640d0b40d134810325441d00c803d214400060030054080c0c005da9880c0c079141c081d65446818441c465118095215410107860409140640e00c02c2d82c0741662a13526800440c545003641298500c03804441d818040d8400030259654905420b61030b010030000025000101c045c0d80d496079148022411814140c500c0c5481e511803441110202c58140d5068804030003165a8040d030380000300904489034003900904020b2004040807600c80003103514079621075002c83d61580c0103074000c4030714210108080700c00035114403120110074200302400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 388834064 1250 388832814 388832819
    0x60201020f03010b0906130b09091602070302060906040905040302060118020a0503041b0f0b2104081c060302130207140f100902010c17040f090b01050307030e1905060108010c030204 80
    0x41c00684018402c440c2d0704000028400040e84900c42551030b03040c07425921042c030720342c3d41505080c0c1d07500000700c81d489152900700060040000400b1a03400018a030f0040464a0665007404a2035115815140e4001c1d0140300020303421041d0b00645200f60300ca68003078151549059459503240a01008030540680144041400250b10205690f8000d810890b041042107001071a0380809115400c106500580000041001c41d0210003c0c803050301042c9140710401100c502c0020000e2040d5402882c008003088190443c82ca4224000141a18000009041c0369a580004d58a000d00010019510b80200b424014007007480a007200c0340d040800600400b444500110752500210000355003034030341d25503090055904c5084600451544001c0014000d0246000407826400902c100011501c40303101c00f04010b18a802048a0000e042c0c50382402c41c0c4030001c0a402411040c07410a0b058461428104c0080d03c0c81c608440c03400380114080c2c58103504294242d425207080100c400103250040004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 388835314 1250 388834064 388834087
    0x105070f05031e16020708030301030203070306050402060c0a050d09120c061d040908070605060307030812150d06050912070b1b04081203060f04060510210204030309080706020102 79
    0x2152609406190480e56a0f0340d811902000c2c80f016034007035080103415010401000d1098007040e1066515400f02d074581a52103200d103513640b02c2404000c0d055085442c0030000500de5400c10b0390058070040560741401c4804410520b010820741040e50154001680400354030342100f0040094124500b6507240d000444d00c52107101487d5104640402c5409082c070a03248140741d102c4001690000c00070b100020317240c101b05200e0f40203880103072003907032409000c9031044c5400a0440c00b12507200c411a81801c1001c060000c0b100c030001e00b03510300d80c0860183d030f01c00d541e6100a0125454810324000a0f94184504403e25105103480c540c42008000c00c18400400c0c4143e00d1079911219100d12078a50084800202160b0b001e517a002d05494810910841c3d4590f400078040e40c0714100585090403040f0360413017003206848403071060359001030440d03009041451007607200c06044010801403c030000c011421a8080b640650b001f9400601c494000340200031049c8030711001051a132000350b0504035402c09 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 388836564 1250 388835314 388835327
    0xd11040e06010c05032710050a0c030e03030405090c03151e060d14071d0118030209101e08011409061f0302040207060e0c03010c051e0c0a03110d02010507 68
    0x141e814444145808020440300b003045440011806400c4040207503c40140480d6210301c500b420300c11070b035a196004201e4072510554109185941d650f41e1400c055480980d00d40340c0709000076030180400c010202c2c5c20f480d0a00c0a901420315032880990b2803402032080203044130510a1640301b42c043c0e1082d001482c1c1d40040010ac6d80400300d175030036590010b00c0c0c0d5080060444080349000e24404108002682e9081a020043c14803541500d1a41c52000001124480c15a441020650001c0301060000d41031600b00741303a104510390342030300d0340c0380c0c90b0260b040b5a4440c80e090540c500c0550001480180c500f0f006941009840094090040c1450006140c07501030003080c20140b091002084c00c04074409400c441e004540103482150399480c24101032014140a40000520340710311890300445080500c507d603a2071600f60b80d80c604000c50305595030383c1120440590306008000740500ca21000042c804007030303264820344440d00058540c14101d82880341c2e0421f0002907909d00301c200002d01d9000301 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 388837814 1250 388836564 388836571
    0x10b040905030a030f06090e0d0f0c030c0b0910050901020414090606031501120f050a060b090d11040f0e03092e0c0204090f050c0102071203140904110f0d11040e 71
    0x41c0170807645c44121503031004001a902c400482400d00c90510007410340450b122011469a44c2d03004d0910500b9441a507100e2040300d40100010010f540c10000308041070140360300051018161195044c440c68880161003080e00d11402c50395001404214a403c1141240c0c00b102c81a41c0c1c41885150050000d803082c00000c1185480044010803035050780e07c68210300e0780302c00f590b61041090b1080c0041820081104072003181e44145004004942040c0101c140d13090707404000c008140404103551010083c0c0817009802c0d4010352038502c000c01c24826401244d080d144075400445c2c841c41030400b000380d149603109402d941101d04d41c4c03021076803a181c0d901486c0d5040e010f040a115403156440031900802c1440c6000e00454035207000a020400701103255461554240e00319803846440e0244d0011201d041d400003008a01241070b04000c2c20750960203811a02c0c0001e0000403000300040c814011b581c0041000201020009080c80000c422840f0f64031120010100e4241001d0501f2101e402c0104082c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 388839064 1250 388837814 388837817
    0x28180509042303030103150506090420121002120601110a060c021603050f0105010e1005041802120303091603020108040b0a0b0604060306030605090d090e07050408060c0705010b040905030a 83
    0xb400052111840d410280c1407019002ca075500c2da90b900348210844070b4200c0f500c40103420003000c150030780b800502507030003650030100c00c0095294000c0102d40242031030140340d130032242c08404c005580c2c10908c010350000c510100050f94800c046c428842000c3d20007490581403103000c0038a285000e0000440c4114030740c2c0300c500045c0e00a615a01640b510902180c0364506041150012003080004110b00799100c40c541c0003400030f641c031511083c1049000300c030030841000302c00e4010401464140c000c20080324005c1c90036028556076402040d20312100c0300c9411004d82c000020700060680030003807070071554002664240c0a03411507000a0002d60b0180001e40994203803004603040c81c01c10f5221b420903030b400401d0556a2903403041c2c00f40140c41c40740300503180c061414001072803e0745d0103d01001c1001031075480500c0c16040c0b510808802c0405401c110400400b0311010942c0442000350f54060608401c1c2652110040d1034050300392220143e0040c026410565184002200042510320a051030b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 388840314 1250 388839064 388839083
    0x90712171e0a0e030d1b110303030408090a08030c102c07060306060302040f030303180813170109030e1c02041806050105090c0301050f04022818050904 67
    0x109035034a40140180e512007100c1a28a0034140340c499481c100820841c0c09a07107560303a00c03000020070551109410200040410444040c011103080040b12408a541c8250a01c0d0051020031000c41d00d590012542250840313000100d10300780e0314200c030400000f02506030086d4540314090b03001070f8442c2250740c44c0c2c40da11621441007411000c104204042074042030f20300080030079050b103076560b03036500305115441c042860500c011400e01c0c4030b4001c40b01a1007801c5d42c400149440e60742d0840091441c0d510f040c3d0b2003810211214000740c135090050144144406040502c1c03400d005008101d82c1202c15006842e03850030080c0c1c0d0019810072200050b2500881e440213846405910404041400c0d0310003c4d0300c40e1510700c03e003441c801c0590f06030003002c0c0a004100140c2ea2510140302c03034040140e03032661300c981e0148010089440c0807103807403201000c082c00141c241509505c0c0703484120707070070b10034800c80500340c80c030300c646150340701c3c00341c80d48144180c0c04449140d180601003503046002070400343c05c1c1c200313 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 388841564 1250 388840314 388840343
    0x1060c031b050d0201060e180318030a17070203011b02061f08010e0715090b0f030a060b0708030a0506011803260a02060108010e01050105010e0904050f0106060f0305090712 76
    0x81000307408005500a8241c0703801c040e244100a0081c0345900035080b0480b01c0300003045001c9848507160344c00f6036081000310701d88001402c404085001445500f680751062580320000600001246144c003049a504582c459504d84100740c2075894000000c8240e64040d0400d05403a907000580c1a044600815202d123107401640c0d22400e004841c0e00b100845609189a240290034001a0041160006441c074a00c00f000014219074404052090a40e03800e010b1090800d461000002107421030048200052095038810880c00e0b56000014156001e400c04820010030f0511801001ea101c42c00f460320a000003800d00804840c2c0501e0700024150b500240041800a5040760100c000307002d030041a95141c64a00c04000c0d900d5609000e008890f500780020b00040113414000c0307d060311416103500c01c4003003112050000d1500c0041040e80c840c403c00c0340500e054a820f01c0b8490241c103441c2e8508001408100002c6c0a450001e4580049507001b505c1c208141b598000301c0250580d4000c0e0719658204 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 388842814 1250 388841564 388841597
    0x30c0201112506180b0115020a08180a06030905010b01030e0706030e0f160303021e030f09010e0405010602160b04030f03080c0c0601080a0b0f06010f0e01090f03200901060c03 77
    0x601200003d12051405000c0001c0c1000861102c000354030071100002160f8a440240b15142c3c50010203c001d07901030f50200000400355030141c0710515801680b134100071614000118140d170b6030790007840802d0f0303950905000c1c42800c1c0141c0024117800e080910201e0004806569200f1591241c0010981e81d04888094540148041c0c1401c1c0218030489a00950b0054541102c0c242840224054801d40700c9602d640040c1000caa05080d80c404041c0d8240b0640b03035020005607001843c814100440da604907e034070780c4c0d00c0c840e030381c06004658014070521414480183ca02080c5403c480c0c07004000340001c2000903201c200044a0a0781484d2014050b00c8504032104070740610340010ba264042e0320000303e82e0407000591140424054407c1c07009a0710f545078100e0001074140c66050000b540781c045003680e01d0007030100c042013410615110741d105560340700d8800c421145820456042812041e4003084013141020012081c50403551b6000c994585100680901170f4507000034248a1040705400340c45 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 388844064 1250 388842814 388842877
    0xc01050a090b07050f010c1b0209060d0f0308010906080c030c040c0e09130b0a06050f01210f0203041502120118021c0203040302060f0c0a03150909050706030c020111 73
    0x10b203070510b030207034880c03401c1e152280c2c03034010781100211290701e0404c01e04c4a843c4180b00c860b00307403542520492841030f1241c0031b01c024000c004000c1a0818103580034900002c01c100555a4058000c0d034070425154141402401981d150381d0100101c5da1120440040d40e1398041000f941101c4121000038084d81c04034400c2c0c0e500c0b962412030702d500c902181d04200c80e11201c80e2423034420070320401300384801e507544484090440d025806610b81003c3c51080410840d40a03240302888011f01042c1c40f17004403003000f045c80030398400ea0303070080c0d19503004001d000c204100090306480d102c038051019401c05220722100114910305100c1c0340700320714100d4410b4480e070200b136044481841d00c0e0141c0e2903005004064040c0694400d84085005110741c50000d40c1070000354400724001c01c05480701c146855a924000c4014000010301c540300128202030020340113a240c811a1100d5200b07401406066180c500041c0445071460025400d42e410454807070209809901140d40300202800c500305070140e00c00c04003645 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 388845314 1250 388844064 388844069
    0x2090a0807120314030f01060c110310240317211302010e041103160207092406031b200a03051903090503071e0b0a0609061202030c01050a09 62
    0x240a604030102d401102d4a040c1e1030468000e0320f4200051400040007012403204485480e21010850010310466115280d180c400d24090142036050700e04410001c0c0c10101c10010160700f403035a503619030308660060114564040e000e0f0380468402c40c9151504c8440c049502900d400c940f8001408403120842c219603542c03440c2c5160b1042c122441d141805100603a20b00d607041e03001c1102038110a2480c80c0a00923140328802e5191183c0c01c5407a6014201c0c8000c0714000300c03078258011003c2c040385441c0c5501c1151502c41034520510344184070309034146072611054202c0004c041c1414000d902c040801c800044a06401d8a482c2081c0000d28030750820030703038940b1001c0205004d00400e9034107065000c130140805d01484503c1c40c41d500703101c20341501110604100140a600180101c1d00491461788001c0355030807609a042c6076852141c0da400400d002c0480d0300d0f00b2041d64594003030010030a90300c50f41002d804040a9404445100d030006a0b944003e407501c50304003d00050144c9030030b846a00c10100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 388846564 1250 388845314 388845329
    0x30b1806160e1c06021b0f01020702040c08010e04030804020a03120c030207080a03090b03180a0305030a050a05061f030e01020417010506030a1a04020102011815050907050105040902090a 82
    0x3090038000d54400e41441004081d40000e01c0d408114480d515052598404100045038840e91018840d07481d1000f9401103080c4821143d4558041000070005105400045d100c41e00010303502c00c058810442101d41c8400d402c0208445080140041240418040c4d080364050420310a15591440010b5607040325400041000761155502505280c0101d080114244071313400341c84a00380c50700c45156030740200400103030000341e210100b04000075003000110b800180b119a1185045100304a03145001c1055608400064000003002480100d40c41416000181107400380454101000016404d01c2a654105000c440c107084081d1103034081e1b8040022941d40800a540740c59440d0742c14403688004205003c155420000010400c1c90007103400c0b041039600000d0440c5403144010a51407072000100202d0566603914010003107075403003130301c044c10642c4120404801c04141340031200a030380014003010306690040c10144100e82e008002d82d030603201c0c12140140c0702e07500d000c00a888948a03921111 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 388847814 1250 388846564 388846573
    0x71a0a0207060c1709011b0e0d050a1a0c07021e040b030d020c150306060f0c07030204060311100e060a0c300809030c0703030309051005090106140108060a030b18 71
    0x20400341e00b03c2c00304100c68444400b00380341640e401e88810300f80c070080a8500746c041487e031043c284450081d006c1c10401a80900080c120b61181d90b03c16142c04003150065807003602c508083c05092b11904640c0b03a002c0c0c0c4000c03015050692941c042030714001141d10481c0d0b83d4a503c041c038451b50315039234480058900d000b411030b286d20103001e00c081d4072102c1020315180500800704140600d003c00400322400384101510261604100b80c401d080603402c400d0021006000ba0b880000260741c0724000c10300514002c1c01440681c804020401003503022455900c0b050000e4444203c1c01a501c40d03080e02d001300e106007400350070840f061a0030b58600c119503549802c6c042c2c181b0300d4070709030a01401a000b0758130302d9925411815160042c1d6a592400381100c0440694000c400c107000080c03080c0c101c00c60940c400c00450300704c14124a0044c013030301c80031580b050b00d0745e540d007070100a500020001600942400c0c01e0500381e070f003403000104500188a01028100740551004100806000900e60444c0d024100c181c8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 388848920 1106 388847814 388847831
    0xf12030f1503210c0c080d0314040b0109050c0408071d0907030b04023a05010501091401150c0f0f0302061b0712050d1103040203060c071a0a020706 65
    0x200030004c00d003008078001050078405d0303009031a11502602142c1c030383c0140182116150011f800c40c4148003414040030800114681d03054500300c030008a4140c5d1068408207a0744100e40c4074540c2482403950004012000240f16030405003a10803455503501c804009c1980d514440c013014060b0680039020234014030708030300d4210012003a0782c80c64a500a0341c45000180d440ba07000886114040900344108102081c0f00e11805044110707420801d039101c150281d8441d0344140610340e0325a03030814059010302e014402209001d039104c18141c81d49109460000902c0e10b03d694200d007d880f030302d80480c1400007109600148100048030781420443c242e00e41e400f20b0410021401d06224080121490042c2c0c03e0140011a1243c601700c66600e0500344145440c0c04d000400c02c10b00321600b80060000601452141c2082d03156810440b00941c8400c41040c0091096000091900c0d280c210345 = true := by decide +kernel

theorem cover : BRFrame.Cov 388669064 388848920 := by
  have h0 := BRFrame.cov_init 388669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 388669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 388669064 ≤ n) (h2 : n < 388848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
