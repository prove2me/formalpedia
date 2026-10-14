-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0769
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:40:52.53799+00:00
-- url     : https://prove2.me/submissions/f161c6c7-2c22-4816-9b8a-9a661e86432f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 138129496 ≤ n < 138309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 138130746 1250 138129496 138129499
    0x3070b0f0c03300108060708060f150d05040203060705030709030803070e0612100605070f020f0418030c120507031d120d020a0c050603070f1110060303021006290702 73
    0x28800144002c0101c1600c20944040410a51030000760003000034040c0410303000503119031b100c4000c000c6c40c542c0015586800080844409820400305000176040c0707481e560501142d5031012440002d190343c1a0440d9002d079100301e055841940c0c800900b1a03140c00110b4244001801e48030040000c43c039114000c603080280ea03c0e00345015002007000c5189540102c00da0010000d20b801041500240c0c00e50f100080e284d5468190b01d80b498540700c0420347c2081810103407141001c00701c0300c80303141c0d0f46501c04c01d0741181000f02e00c1081030042c1009000e0624440c0e00740c980328103032042850a18400c400321070201c1d0b4151a01e86c1c042681909502c03111103402c0d18a134020000c03a0701041008020091303c80c03107045039402482c103010140341040846110764030003400740c0030902c00c2c0825a03403c10034048203411107140030303580e952880c481146041034110800203014a0300c48003006056010034424100042030009000c2c0b070343e5503881400354604010301c103a441290013502c804c040c4c40110080108600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 138131996 1250 138130746 138130753
    0x612050d0e04180818030f0c0405061801080d030501060e0109140d05010509030a0207050604030b010e0c040b0711041404030206070c140708031902010204050607020405090a0c03030809010b03070b0f0c 88
    0x28a501c2c0c00c000c0d400c4000064641c00301c0403171001006a050100043c00a01c164041c000148082c02c0ca40e507101e5801060920a07511000028466243e0349480c00e803913180071000e007126596641401d40c0356040d006030720001a003404004201203014054521400d1010380d2a182c216280c19202080c1ca41000c003810341c0012500c0c0104e000c02ca00340244c50081100300e015541d124100c0e18007a180150580c0a14010b01052004102040c180241079045030b4000c95020519074524100c01103511440d001a202c40c035001c50038000740840c04103000030014003654204a01c01c040880380002e079900701c40050060b8040400240342c01e12075400542114843c54030b010016000a02d49403c010898105800c294000724006050a1000e40400d441c08000c0c00214689810640070481e14400c1980203400759440c3c0000c6208c05004010488813242c0241002208684a250007400d0540989594100350700302080340b182860003044880c01c94501041241c50300409042501480c1c1205030302991901 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 138133246 1250 138131996 138132011
    0x306050604050d0f1704050418020d08090d05010204031109010504020c0616030e0102031303020c01080702030307140d150306050901060f090c030209150706060e0705031519090f0612050d0e04 84
    0xe045c1c40d6074240d000c8190190584840c10704090000319200701c1c103410740301d146800c04c0c440076032144c003000b0640303d400c40c0c507103035540f04c6400c0890000c500c4800d000309a5840041c000040c0300301c4030081800e42c642122050003999881d0104001c5e400f0303101c800e00040d04802c001c52109504407011203107088142c100410841459200301d030032600f00b20b600b040d01543c86c000304030070142c0c10b20007548803060900f89440f05041907103000b580c2c2d000c0103181c2004e01038000e1003285044090750039180146d050780c005020441500740e18000c100018401220325030304040114402c8101801641d003611940f20314090326a1510b41c000c0c015003405011034007459420008804151200036090240d801549a426603030b4001e458400212a5142e110b401d9184070503050103401c0d41e0020859400002c804052180d400e401c0300001c00444a920310f400da0a40c182e50001242c0d04160055101100000c42c1001000c1c1d0750103d550b280d0000181c02016604251003140c01d85016402072489408094030002d9541d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 138134496 1250 138133246 138133253
    0x506090402030d12060f0b030907060203071a1003060908090a1703090108060d0804030b0114010c0f030e01031d010f1103130305180603040303020c010f0c0503060d060b040f0209030d0306050604050d0f 88
    0x5042504031f070007020700006c01c1001d1000f00b0070998006025500c029450225580c4030003083c400140c2104442205490100c0c2e20796a400c2c0c0440044d6800403000c20540c2951711345001c01d43c0c02032000c20f0042c0c00d1003000103298000d9660900465a154000e0341c50201d4900046661040c010325596018124240c4071001c52010405480910706c1071814203003035410b202d808041d907100c9d450341c00e04101c4a01242000200582e007408640c070b925091140c1841007050041c0c0181030302c10308241c06455000c468000143c015042468a645504000c021410702d11030114003900c001c451003803000c189092601c001a1143e001040d1468400700a25480307000c0d400040d200e0760007520240c0010740c0209108038403170300038803500942001500080021900d03090b405000ea0100074500703031140705641000418007031075030008504048000c004024031102120903034000d420160005010b4455507400b07404641c040e100715800e9a100505450401c1d150604000b0b10002004e8102d504c200003600c0507000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 138135746 1250 138134496 138134519
    0xe030106170f060c18010e0303070f03030605180108030405010c0c090c02150f090a12030b030604050a0303060f0e0406110c0a060506090c04030809060a27090506090402030d1206 78
    0x4189001030900240700b80416031400c480940f9020602078208a0148045045009445109428200040d02e01c41c4000080e08600032076102030802a03610340107108250b411380c0b00780d0a44400b11502409107400c0c055012100b04240669000c680c007c1000f4000340d0300034802d1345406031280070b10b101d4503912804148140c0368020343d00b50260740b20140c10030000451100b00ca40c40800344406041030725041e0030f0b959a071070b5003400103003a030350113a441400003e00c60b0304091504200502240c40318141480d080d980d4400d0080168002844c0541c081030588181170a5401ca07901444982c3e0030740caa5441c0e0034000c2013050b480c3c40d01d646040020010710032040c800421203c0c01024009014074140041c04038204005020140f800d01c1003100b440090701c3e420945400b40c0042c1c440c1900c0b10314414040c0c43e88183e52060450b0703500440b10440348807001c0e217004002d54402c01790510007a1904410300802139001d8070005c2d8590444c51080d04618420032581c1c000052252000c42e10307560307500400a5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 138136996 1250 138135746 138135779
    0xf03090501120209012106080d05030a05070201291809010207020a0506040510030e0705120a140109080a030906060902030a0b0103110f070b040303020c011a01080603070f060e030106 80
    0x8109020000c200d29a0010704051140c429944150300c0e0000350b50000308100300101c0a03c0c62017100300d0f4044021440c507804440540003401c11600c2c4ca01402002902c21b400c00c841450311103040c107000520b101c0c41030050004c01068a036091a0300581e0600e03403154002166801c1ea0422000003090426280b040446406440300303c1c001a6680407500510442d141075402860144070300704001c02660b241d800f0210700d20b600c28078000030148903040b5500d0401c0455404250701440741100b1051082c1d02059047d5110312505183d00280c00b580e44130f03801c1e500d201c0d801034500c00c4107101070070b20359019400200b020b40c4200320006d5480e88175507280049801c02e0710f40030080342d902d61500e00c2958040c1700d641d070f200c1ca004c0c030307030a04100c00700380c09052500c01c0900c000d05504583c0041000c060103901074901001e484000ce0100f1420020002101010700c2c2e680ca001951507004a07001d401c01040341c0d4150340e0303a0200260f5145c10400151695171860024a80541d43c2d0a00001e8224503c610111b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 138138246 1250 138136996 138137003
    0xd110a060c02090601032009030709090506070815090601050c0a0606031220030304030c021909020d1d060402040506030f0303100807061803032609060a0f0216060b0a030f 75
    0x408070205006204030400f0040000381458540403004000101e46001807101034940100503a40e40d00002c08a8101551684030805507420134100c1410400c0c00315410340b0840c85550345100c0c565582d01c250074210802c0b600d10390080c0380440400e14a502c40c000030048203c0b4030044030080c001542e60002102d0180e030042d1802c2d620461203121080d4410085a01210750300c821541d0060040309891316480054401418040c40056403011912102a1400300c0200200c800898940d0341c0c4240380a9409040c2401c1c0007442c1020310440459008003842000c690480100f0340c503500c6500b0700004140103400641d0500c00ca00c2c44c0012140c0400086110b118280c0e1120241450442440e19210180c0c0090b028484400d000b1090881c0f00110003003103c2d003601c0c2ca0004090010201d18107401e6810a40866540c84020411107001c0029140d00655070480b080100f2281d4100110890091660422a02140385082d80100e5080e1f00440c050300001041c80c01c116650703070f1722400010b40c044c03001c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 138139496 1250 138138246 138138257
    0x5091501080603030a0206180a20010915050901030b0f0301020403080d05060906130222060e01090803131205010f0e1b03060606070605100308040605090a0914060d110a06 75
    0x405095912041c550703044402a0f00031410100c200001940302d550003007000300f4045000000400054081192100d05a08503180f903207171015840981022089102041d404a030b4440f100240148240c02d02c04841c01d055940c0d1404d103100c180c011000303451010005580545e42e00c0d46240300341d50030300c000d0006510079003110740c0d104a01d10494040d02c2c8020079141c07146210000b04803590300e411a201d1100d03419050016035900085050042c10420308840440074a80290041640b60304010a82d910720401d80300c0d4000c480e030f01c140881d030f2489334140482200768018010014811120030102d80d0307512640000c1076807a031030781e03481c1c003144e84a52615420303601c105404a500b03d020860303240901c40139000703425a4640f910109142d1310603000c004052507034500025440204605158005c0c1d58080452a03803541e032020014241d4101d0a031003849401b81440000d412981403241c40ca44540398105120607a0f9004100400a0300015040d82c12419400c42c0c3e8110703540740c2e280e180c00341031aa21003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 138140746 1250 138139496 138139531
    0x10b0a110d120605030604050303040b07090e0f180106050a0504020d180804150804030507030c0f150c1101020c0d110703080c060f070203070c150c05120909101202060a090509 77
    0x70311050f00c00baa4480350190300000c0601001c074070007104596200b50031621007855525444411242c46034140c0c4008107007865001407024480ca04210f06010f40a1030440d180e0698090540c0350072203505202d0140e002d02c0404003000b00707040503000f0705281540c10750700080c400302c02c50101c030f90725684450494100c4030016041c840c1070201981217003512000c0c0760084661500c1e0390041c01501c01c07a0805800c0c0706040343c001080104104441101d10b40c0b000b1039400140902146501030003d4200e07080100c2c160340c001c110080303030510a8a1a80720100300400c0c0b040c0c01c840050305e043c111580c4900c4503018240c40800882c0d411801885180c2c07095004206510b045140300c1260314000c0c06810441d0000c11820010403081e85000c001d480c0384404174007803071000300c009417103200c10f03200003c0c00c03070140744c40412074008071001503c0c119000340e44d01ea07816506c1c01004004042c50340940a48050b800c0300b400c02500b481d4005c3d068102c03070341c185140303d04e441c1c5d80040c1c90f4510450318000b000711501e64 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 138141996 1250 138140746 138140777
    0x2120105100e1f1206110a050a0503060d05010c02010509010507020a03020604062408030418020a050315120d020105060f24160c0b1908060a0905130606030308010617010e010b0a110d 80
    0x140035003801006c480c3c070703081000d4210010400d11469102c0f80c00c010004c404240595162224202c440d90b0040003007120458042020b4041c0c801194203034060351804001800c02400481e800c27024640c590b0207003140760348a603100390007081c260315204024000384482031080d10391302c2e4028018018882c001d54585107480307042c0344034031043c0b42901e00c0b0a0042c000b640d0240d80150aa030303048480c011a10420b40d041c0c0d404100346020000c803540c981d02ca1460502c105580642c40a401114141d131200d00b800445401c1c0044204140501803900c1c090300055041202d089014041c4480f0a500307075200981e241d101d400c450340c002d800203a000380000070032598081d6400c4260300700348500d040c1004240792260000301284880e21039600c2594881001445400610406220060340050100425512800c000340142001d0050b100814404081000c4079450170700d61504803262803c110110340e081442100007a04070214403802d201c1300c80d0152008002c00d11040300341c0120790762000400c0302e0210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 138143246 1250 138141996 138142001
    0x4090c0305060a14041103010902040c180b0406020a03050304060605030703030314090610050d0c050603010b03040b070c020d02010c031704060506040c09030506040210050d0906060302120105100e1f1206 89
    0x41000c044146040c0b004e012201c00c4140d00c640c015001070b0712008880894021034050204100700960081c0703010121345202da00240e1960302400d01800ca600ba01d5260030000301c03d403196006070070160b8440002080000c4c841d2004503480b81c49401c2c003150159a03500840e00d01580e582040b00880e4580380c1c0d0200c0701c910007040d20f90051202c002003045003000091820343d81081d0141c80c2c01b80c42034002110522900100c5840280b1000c0d00d45070796580d413100b01c200c140d001980d04a402d2b00c030300307030116030034030b01c0f40800341c604d030744c008008644020300390b801901c9442000d00c04609100b12406800c21501030100c005200c0da001d40e0300460b451a18400304411900f403030041e0000d01041160510129234000364090340550705450170f00745501d40b02810b580c10b00811512b40e040605207044e440800050342c2101003203901c00c0c0c884010748241002410f090300c804030b50800d40494030041c1040a40d401541907604070340d038502032007481034601500c0c14942c0c2c000e0b000080b80342c06580d82c0100300603051 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 138144496 1250 138143246 138143251
    0x307060207030822350403050c09010e070905060d110a0306060201060803040305030f0307020109081902071a160204021303050618030403150903050d060806040b0606161b0504090c030506 82
    0x4071301e44450700140b540d400e168000035102d01c0c007100007402c1c541000c0601d101e008640c007400c0343c4000b6480d2030782ca24009584405100045025184640c000180c0d07842d403201c041d0140c0311075110181424145014061160002810340f80c026881d02d0844420442c04001070203044800e6034081503007030a05074003038251491075001942503442000200081750f0048140c1c1d9018502002d165034949501c5400c81c0541030001c00035000076000911080ca020300303401820006411a020b683c1c0a5030f8920079810081e43c901034143d54807004200c00e04c03801d07941d540d400c2c0c84188000e20050600c48001c81c0b82c104e0036015001180d0b617920620034030400c610302508015000c0c0c6084021480e09045503203045485003010341c21280c5607103450114007094011026902072008041007081241c0e0355045680d0b440ba070945090b1544041c3c0c001040d85404e080007201c03500707410290000c0005a241d03036044403018450184840d19008100c005ca031a03602e82c0603040f40980102042e1200c00c0c15401c0c91230401801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 138145746 1250 138144496 138144541
    0xc030905060f16120b030d02060a06060203041d04020d060f062103020c090903041520070303020606150c030403050d120605030a0201080606130b1903090203030d02070503070602070308 81
    0x71082040702000c643c034070800342c0c40d03c03a15000090005010043e805030450b14403840e454007954070702d070300364980c001076051040584100a000c1c0c41c1d9901d005031f849100700d01075108100d1101040c5880c480c64904415001480036190107011501501e4140445050900e0410800d4441c0000c114100c03100661110780c03000080c41c01882c0c0d24a6802a54550380482c283d402404c0400c00501c0410083c0180e0380101a659180703040c605a2840043c0b68490140310487c00300303107840c803003502d440001030040103403070f8184c00800d140d0311342c0c00c20884c51803498104c2055440082108481041050001e040194480e4004180030300501d0b4001d0005075400314200f91092030a001040540e0b0300090b01b0000035028249019242c4801c03010170843c5c803500c1103103070000500c0780000407840c440000410702c4410301c0000c0d601034081904203e0503210081c2c0042d6060f441480300d201c00114a038000e00c2c046114408603031a000040e95070310166080744009602044a09041010020500c801d41924a01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 138146996 1250 138145746 138145771
    0x60712060b030c03040f1403070308040209280e030705070b0910080c0706050a020f2706070c050f01030b0d03030504060f06031208070e0406030b240d0f03030f0c03090506 75
    0x9010300000444d02004002810441c08074512400340b0070405040340c44003c145081d01c0e5580748508025002c00c0c01600c0c102d004504200005240c0002c07014000c15800310610a03150f2109500c1c21803002d001e01e02c900540c05e0004000307080006c1d800304800303030041c02540c1240340c0fa21241d4042103451031180c000325091114040c00c101091070746c20b088031062035201c9000203150703d6404040d0000d001e40340108d0210072000514515483d012a038004018124040307500e8140499810300c1070502420b10010841802c00750300f40082d20708a40c0b0840c180c4010315000441249100000b80480402102600800e035110288003c1c400c5500a030b03104601021000d00c0003a1440c0c3d070750307105c003c43d41412104014608021440740b51003424042e603200700040c0184021a143c3c1000101c4072804c1d1240f00446000c80000242c003010207201c3c0d4801c45008140c1004008541c60340c081802c00440c08070101a40c4401d5000089020701c1094030180c266640001c100d4401e1404034500310026281240690 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 138148246 1250 138146996 138147001
    0x90306050c0306130513020d050303060306090102090d03081f180c0e0a1503090204050108010e0f0a0b01060f03020f03010e01060f03290609090a150e060a0303031d060712060b03 78
    0x440300c54104e292101640c400044640c1d13100007074606146507800080d40300d410070b044181402000800ba5000d544105e0078ce41c1161520301c185400c038400c6600041d004010118480d010030f0081600c107500880703048030f9611807104d445074050080050703000304880c0781b5184443d05212407a0b2048900302c540c0c90910300d00c42c01c03514000501401c103512401040b80c042052464809100b45c0255010b541e0180051201d540c650b11640d000e080390790071303070381c454401c1c220124025240000d03503415180d04000510b031141d08080084a110000c080302e0820303d80c00b0071038504101c1d4460001c40c020450040400c5c030360350404c000244652a000b602c0c9042508250101c0520300014882c0c01e8a40383c03000603240d00081400109910340070780e440c8164440402e5040007001d00160f0805041c0001504680c40016250261205004410386045030051602001800064040da02002d0001e0010386165144910f21040c1d51614004840d07a00000d40f45540508a02078140203100140c10071510301c2c2d0030f61 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 138149496 1250 138148246 138148249
    0x30e16090906060e25080f01030b180d0206010602010b0613031713060f0e24090d050a1101080c071208040812100608070f1e0c0b0408090a090b0d02010c02040e0706090306050c0306 79
    0x7c28180000b0f44561141c0000c2410310000d00c0381404e409880c401903425000d09040c0c080c2d01d42a00b407041ca405542030044a8034075103040801c41d003400787c200039030102203801e41d01c03410401001d5103041c42c50000c04204d20580c5804800c2460010300695481c012000300f880c2000b0104986200400e000e140c8141d40ca603410074601d04260030302042007030140d4841c1e030b0342c2000420f04142c7c030360060300f01e000708031061b414400c40c030302c101c00c1040007030321148242d440e5000c0320a0203100e00000602085030200c4200c1c1483e200c0d02840340c115014075030f200c0c1801c404002c080c6100e9002c3d00c41031400c068140c01048032a4001050300c0e07200880c1d0030440d141d200c200c01301500111841c0204040c0c1c1910011904503140600041700500ea04450707140d40a15191038192000d501000265204103000360300004d81c10481c0c00703080d14a0401406c4a00080c1407940103503a24034061001726817242d00c403400c0110b8024200700c030200400141c2c0e81e0340701c0c580c0785003000f0046500103000030186000070800c20113107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 138150746 1250 138149496 138149521
    0x7020f0f061611040c08250203030a0506010e060d09060f02041401180801060b0403060614010f1d060307030c170c0427050103080406030e16090906060e2508 69
    0x4040c201c0b0303071084660312500c0d01c41d40852807510440d500502d05044034044076448030205215103071b00d80103100c4865195181071a0309040081000040c0d00800016640c2c0910360051a0000010306040200c405440001540da41141c1038024040341c0e02c80401c2d06001d224010480200500c0c4001c5203082d0401c0118400b0900d09125141813107041b0701c2d61a15014110b409400400342840200720041e2030b05031004980c0d119110a5401d5408c0260100b0059841c080d003918050058441b0100a8802101a41d200341e40c0c0108001c00440c2840d86005500c9100c025441a1660b0f0790024400c1a101c174013421800d80150b01090300c50340c04081100507118001242c0649850400800400d840c152100d01c1c42e1034002c205000303181c2004000803c000c100b00c05001910210307203050045044040d4010350390b244214803d0011185040100400b03880c50348000c940600a00f40490610703102c500288202e001034904944101540c2c05c2500c10002c084d1344050b91412629001202e41007000340040c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 138151996 1250 138150746 138150757
    0x606040b0a1110090b0115121e050405010b010306090902060403080705070801060803130e09060a0216020603010b0c010b0a1805131407030b09030913090f0b010b07020f0f06 76
    0x410080014003101e88a00800c8286a5212818221100d070f050740d88100d000303001940300480710803004800205140d100300440b03035410703262540c41c0743c240322090032000080e2030110b03040410740024441020006100307001d032b42d01c142c1c0640008180400d0140004046400369489240c00c9850f040c1484010780d00d10084034212030f000325a007500e40410b0309185040c1034540d0b024074490761a00c080055204000320192000380c145007d0443c41380c1d03454461070040c0e20704035010348554010f04001198140d056024203901c0c1381602c3c00001102050780410b41391703402038100c030030940b5000c80d011a800384240224103266100faa40b44c0b45140c0703003495420180ea0041c0361800d07081c0d01c810014044080d076289141e405074021040c0b450070285001c140341c85440b80c1c04195000c440c25400214000000421100040c074090803000c88a604400c8410040c000d55104480791244000b80360080b48010240034068407108240d260381d00402d20410a00088098516014030350350030b0209001d41c0c55105542 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 138153246 1250 138151996 138152009
    0x402040602071a160b090114040b04240e031e0901090303050c01020910030c0906020601151805030a05100b1e060c01060510020a020307080a0503040b0f0d181a060604 73
    0xc1c03001c00b450400d24500d008100071611034030003000b103940c107200d1170040103401035000000801c031a00c001c1240c1034048008840c0904030008800c04900058820710320181282a9900280062aa006580740170346d07000b5045400c180d8804100005046003014600031341c1a0302104192404403c3c40010b01070800a100250a00c10081a403d002440c20b404588148000030300713009409843c044090001d011107a800d00002d040c0607008242070b0b00000d0030724140c840c2d180c0d0540c200c00c2201d0045401c00c2002205c0b01d004083d00600041c0e58804004818155201c0d0025240820080407950b040314140c0344410720030781d8502c248400c6180220105011a0403c0c2e492a944074405811980984929400f0365001495180d521544680c0410003124140c800c50542d51400e84c0c5081e030355541e8502100140032500100000c1005600c841d006022000780144030b0388c14031061441260031035616032025010b44801c01041020442201d4840034401d003e481da80b101c40c02c10b1070204100d4001e601801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 138154496 1250 138153246 138153269
    0xf03021f08060907051e04090b03010911100507060608030705060901020906180d20040c020c0906120f03040305031902190b07020a0b010906080c010f0e0f01121d0606040204060207 79
    0x4404c00e1140e012258130050356011018030100e50f001510305640148141c030f000c0e510307040d0345a0440c0303410302500130703002d4100c4c6142c1c4140566900300090342140595000a10008029400005044c1c1c0608002018904040c640390301e46d03070410500303180c4000e1007113515901c10801c3d88101d58545003541d1941300130308910406071240001045114440000c0580b40c00c640607485d500752171400200c0d41c12240700755000e106070f40322680180d07a584420451190f01261001c0082c41ea828440d0008119000650440f5680c14a00010781c1c1541d001d0380ac20b44907a00001110100491205446480c55200c1e00c000c092013021200c40c3c8400c3c0c060354000804032220000401c000d0b9108002e110750490f00002d6000700da50391100d400d0020811841001814054401c0300c001d158021901104000c1050f01d4200303440c11a0820098081c43c500b1000781484080100140c0004692180004c800034228800840e49541960140342800c010b04561207580108018001700e0390110700441159600e00c0c40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 138155746 1250 138154496 138154501
    0x40305060c090604030519030e010f050301031b0b03040503030405150402010e090c0c0d0915020d0818011409060601170105061c020f0a0804170906040605160b010f03021f080609 78
    0x3419501c0f41d85c2c00585184500503d03c1c04a40c01a070440c05154401d4840040724106100195020082000c0483c08988180010000710380000c0026001c8030320b50040003061616040c1030a2250026101928a0f80c400310400041050030848114244048440c1481d9031a0550000740546c01005420f07000da81c480b008541001c001c00f0649441040000540390540b40d4260300406a1390280301d240303441c0c001c40126018050003c586004130300c240b07030350f441461b5540c0e04002c00c2e4001d048050246070340d070f501076100302c41c42141185070164581002504007410400300041120080108106035203400302d0040105030b480404030f030080070008085000e81041649004000c0c00341c92405d1002000025000706901d5101603003a12461240c4901001914600f881c1c20b010301600102d1608540b0401041c440940904090049100c850003042203008843e40c80e86103044007a8041c40f034440d4208810b1086280000303480b40141c020b0b10008a2051105a0040c440c290251800b401049400003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 138156996 1250 138155746 138155749
    0x207030c2106090c080106060e0102060f16050711030115031b050112180210090303080c0702010c030e19080102040501030e01020f09040b06040e0903040510020102070512340314040305060c09 84
    0x4c0b5000030304081008210349542c60002034503020b8801c128500501a8030000760803a02c00b00d074024024100b4000a0354032020342d500980f01c0b42d020b000180d6640310700f042c5100782581e00340a400248200c6c6044010040d00e1440c000c5101c10b520340c00b00703110241501c0b050080340d0b840f40300c106c0d28042c4a0000b09542c200d04000203422451008083d4104102c03e101c0b0320125000354040044038403075503a00509540e219061481400790301002400205804902e0303000c40e108500400703a40000401104c07140000940301540c0c00b103c1d40c0410704503500854108107940e054403c110002101ca4025441e14a035002c185180b0310420440511a40c0d6840d99a501d64840384199006001c0c40400b40c41181082101d15030359410134410b1301c0c4510340e400042c1a0292040c000e44110503400f03c01004499090158886960844030000300719644507021981c204564005500540000d84c2c4002c500d0b40c8503003401000c4c0704c0c07651840003044001304000c2001a200140040d0300c654860750540e21200c2c440c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 138158246 1250 138156996 138157013
    0x10807020c012a0809030606032b0e040207060b040c020d0503040213020c0f03130501140304060b12150603100b0d0b0601020a02060315091f0905060301020412030207030c210609 78
    0x400c070f190402d10b408501080013a000000e00140f40114104c9101755260b00406989107105000390140d1071903980004c44103900c0b00240e0352015081d0410503002051580410100c0c2c0003207105440041d00d88040038501d09042c8583c030f4910348144058980c01010500141046c40040c4c00240a54500000300800c5c0b84a941502e81d003000001c251007180c00b02d4039140355281c0007880030541c1c0d00d108010004680d8005c1d0320701c0284190840d0f41c5421907803203403a020001c2c120040b8164015200c030b6414050f4003000c0c07008112a010038800440c032801e0900903d8600751080281d1070041e03144c1403c0e00740aa41b51007044d0502c951000b02128540c1e11080100d00740740e0a80c1d4025004a07001c01444a198032041c055404820f003503076a6503581d40c64000705d903402c03100345200300394104d0306100a02c50078a05410050780120007800252405a0710109a803034a591400c01b500146c1045005104204060707401c84001d0032901195001440307404101c1d0303600c119a0314001c008990f50002c1c4800c00a909 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 138159496 1250 138158246 138158297
    0x90706090b0d09230606030d0806010e040e06090102070b16210209060d02070b150901210f0507180204030506151f120b0904110d030512010f05040b010807020c01 71
    0x4e5408803010b038400308030820350300c210060601c00e13028010004141c0e0400040d42005200e15a4840d00180c49203401520440300100c00340384c20544030491007400c150200196030155240d00e000581d0b49109040800c04110090300c4001c218a48950241c18168400501050070040c1d414560201500c14a520001e12805014641246010445c0c4118030901d90103004103500800280340d603070380ca041c010001280320480169100c0014001449140c1504521102c00d42c0210329180000d4003603202c92500d502603510490f046e6000d00301c2401401004100c90201114829042d402c00b0300359510113884041c01007400030748200f0564070040319910103014502c0c2d9400080c50b0411003100c1c0f03400500000307405000104440c00c1c480001510305290b0796081c8519005001060602040c00030001d1449070044e0a03010031809000e100c1041c01c6c82c00505009280400f41d40c40e82501c2c000c244000e031b4011005240c10700400104200c0c8440d0003007607413107070440b0034a00004402a03082c0526081480b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 138160746 1250 138159496 138159503
    0x70f18020c0f160e01060e010917030c0a0602090301140c04140604120b010504052d0a1103090105010503210d0c021608010609050a0c050a030c2006070305090706090b0d09 75
    0x2c60180210300360750000e80c4400c1d18107580e607240c072686e01c900058940c8002c0314141e078002022800100805000300319400500841841503a1a0424040c00d162900755070b00000c2e100280e00180300350b41c5240c24447c0401c55412203007070084900c0d100c001c2103201c1c000d03072290340102040c412662149070f80780300403500503081d15200303d002050f10341050356100200b4090306002d1850003020030145056005e041c000342000445c03003460441d05116085148030041c180424690b192a41d1181c4207070306034091407040403400c0000843c1e40c5000c0825107804480c03040042d4a070a9035070f4400300c0070f034480c089401541049801040395a140b40c000c1740750140700c40d03010048160320031003c1101001900194122002410140400d441b9a40e0140c11214410010800b00d00200080e0004074000d030080054104035041c140c4074405902c0000e207180d45d40b803603001900d422a40030800c0c0c3c9501440790702e40180c00000104001810304801400100207800344004080c2d010400b03050300d92031a000110740c15032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 138161996 1250 138160746 138160753
    0x1303080307030504030e0108060a0506070804090608100b06030f1f0e01080106090f0c02030301061803050d030204150804240906020c03030106021011070209090307020d050c0102070f18020c0f 84
    0x41071800200240710030b96089001500a41b9400d65a6105d5500640241001070840200d5072401003000316651203003500b00c3c2c544030f003031200040714801ca10440009180c1d40026086000c00809244102c070340798030210f44212001c0c81805902d031031940015a1110060010408104401400000c1e51155034804c00c100350081c00041208030301908401c0c21950f0480003070211b03000703901c4003809039140300d04d6490041c1d0050004010983c4104200c10a41031980540c00783d0310b490362561814010403211090110703800180401c00240070004100e0f03141800d00d8003a60600301039896202d0404040e40c80f1181c4820851000840c11856001c840002e1b403113007045540b180e8405206407640c00c00d10442003d40a000720011094a1900408203c0781600c040c00d0700e080c0c0640e08000c0c030101d001d010907049110510120005031100003000181501407070041110b030125900083ca03041a0b604010309a2401001c03c115215400c11264581e01174094050b0f252184812401d24180c15503c0740c001a11 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 138163246 1250 138161996 138162001
    0x1110d02032707050f03071d06060d0603060207020108061f35011502150c0a0302040b0307020114060a05010c0803040503090d03112103060d110621070c020d0813030803 74
    0x102c0002e9040125101903035110041c2d4010701c10952103071100c0c4140f0384003004100d0261500c01c132295400340e10100080a180c04c0540700b000071000c548d00381e04226101c0354002801020340d07800c05a444d5100070100e5a100040f01c0c0801c07105070b0020000000001e00284a600400e098500d240c00c9802c100700700044d0510b141c002c810140e000700c0a11030082c0103080302d81c021032800d00c081100720521402c1b44a052294964410403252a440401c001042507402e00020560503d9000150f00a800540c00800c01c40780107450442c41c42e10103003c003449189817600420159810540142c04603030449c1d48284c0703036a2f0754144541144903e49046a011582c0200da000b0550003851507070040e00c03180211161504000104200055241104046810300f40002a09850a80240d4250510501c407000c0401c00802c08a00550807141c011407200f0820704402e4107440305285070503401b50903442c04103240310351a00443c000c0720712000c025040050010b1602200701041c248030f0000d40e80031103080e07540e1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 138164496 1250 138163246 138163321
    0x30507051c09020f090921120a05070f02192003060106050408012415021623100807080a020c07030b06120601030209070f1b060e060901110d0203 64
    0x2012802d01c00c030710501d0480310400090801c12082481194008014607444540c841e50b034450030100010108481020800401c880d12808030147c050300c3c4d40213021490342402c0340042c1034a2050000356003103520000c2d4403080c004041c044007180640000800301d01c2420702c2c1c14a009031000005282e01841440c00000d07007694000018001ca80381100208001000c12080404000c00001021503018000f1010310a03244000000d00c08070701c00340100c0341c051070350a15440c528010740d40301c207a1250180366900c80e055103102c089510840d00300c400441d20209080054121038010700400c0c10480b002c40000e100000650441d51034050070b00c103c4050507940e10f02890800021655603000d01c92400403204c801c2c100007110b9060b65402440403845580e140000ca8441da00300300301404100f040091200fa4040007040321031010300424001c10a60701641d400ca24104c0302078596101a807400b0b070a200380084c0001074401c5070510100142c0e4030349610b42c0c0175002340e0011000d103a204644120001c0361 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 138165746 1250 138164496 138164501
    0xd0c060c0308010b0304050c040218100f020706030e19051009110103110304050606040b060403062309191b0302030322081f05071704030807030b1c03030507051c 71
    0x869120b6038844110b0f070f880382046076840c002907a000745643e1042d4480700d00f904d499005070080820605112600c1d940203070000d00004503092603000030404081e07101e5451035040c802c0b440540b80c1030800b800381d510030140240d80c0301c0107441c0e1000748003c3c901c00c19080180c1440a40300040450310103011281007030401002c90300c402008903010a241c00740100300c3c180c82400b524412900840a08000d03910079080c4000350004c480d54a034000070400002c80050307154410602c0d52030810342c0064210b182c01c0a599607926028102000316032020120110160004490304040342d07010000d0036120b140109400c040d151990030095050101040740c51904d9014804010710000407040c508501d90780f84109511149002c100c50441001311600c0d8440c5a001d401c602d0b00b01c021440e003603d8580e803402090030b001e4011340303080f40050245030902107420707454040c00310030783ca04403844d460704d1042045842042d0703000741000f418580c8500c005841240240c003a03555821200d20710825100210380003400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 138166996 1250 138165746 138165767
    0x405090a05030c060709091107060c09180204051503041e150204060e03011a030a02040203060613150f020105010609170111370504030219091a030d08070503010605090d0c06 76
    0x5003080000036200c1f101c1d0240741f115500c4410000d14150ba0350305d0308005011009011014040c10510000341000c0102510300c2404220781c0041e116810312003004070141034401c48503601d0400340305001c0420740a2400840845c011291140742c02c2d880d15000d402e9100c241c90504c1907034804100007451a400519244400c0e030114001c11510b003205800e414656000703001503070941e200d24084001414540d0003141c026a00400c058203007000901c846880c0120343e008104466500c5a01e480b182d0741103c585002d51403d40000e0010b03604001c0b000b85602e80e40d228a05001d960300441e1580b801007944180e03050f40748032041c0ba944640d02101002d1030704061442c6400007510843d0040701d100241501e080d07882c0c460380c82c0c51800c0c1c0745030200a420324811886400794442400c0004504480c0d104801500417040c4c8010014a00441014203200341c5640c1d41d000c0c003804c403040140340d550180499065400b01e05200c0d131600c442c480800c100c003542100007081402400b80101d030b959000324a80f00d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 138168246 1250 138166996 138167011
    0x27090c030212120301060c0c0f09022a0a03050304390b130603110c06190c0203160b1f08010203010807060c240f090c0f05060a0e0405090a05030c06 65
    0x60ba1401c210a07160395500d10b4008612010307a0900061081610a070350400009005e4441d4601d16526411240c041d0003499205484156000801d6415131000c9c194401c3c905c2030f05405440e00d86003c900050311880301000080c108003000001038204550f0301d040c1c4c3d0b110000356020481c11903880701040c926040e0b541c0c04410141400070002a101d030136004481c42c01100c42c035801425860100f06030083c205001c0e5030300404105002070210358000b000319501c00d14100004108a141c0703560808100c400c900241320454100b00a01000042d0040d01c2a60880e0300c1010007089654020030710711a00c6104a04000842078a140024158030540185042c2d60f0a201601e4000b65103080c144c4001d0b4001400904000415030004142114070030841d408500180012800424050085044403202c2104441c0c4c3c0c080307100144501540c1c000c013507015003019980031f0314107031051101911034095140c50b284101e1b07d038400100c100005110f43e1a04a42c400112501d503040d50b510251241412511038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 138169496 1250 138168246 138168259
    0x3030507180501170405150f060109170604020d0c08030f091008041a070302040b040602160503071a0310051503040308060d080703051e0c010c031404020a27090c0302 73
    0x949900607100c51880440304161a24031000030700c0c0000c801030704401807007514940681a241100c1039100400d05100d1b1f0560300e01401d41e46801c50000d03003c03002d5600020b120760700501400c80302131000907101e40c203d501101c1c469050102860a6448070f540790b040b6158500020484148130403184010b00040030045517983c0700d03500c02e4081100e226908490280001c4102400d90030ba0089220900790818240d14002d0310380754881401c82c0f095801584020016800703400c070201003070b1130341008102800b0100c1c081c02c02e0364503002c07480e801c160030b160851600603800004584400496441c0070000d181c082c10102d485d00c0e9040c2c14607800c0d00211010360200350603c00151f800e20303041203403500140c3d01040e07060400780b07603840440d0540c010b400e07685156103a00000c91454003040014007001545e810010034000c60f610402025205195052801c001d40442440010b0b81e45032101e02c01c0e01e650282880a0100180c00e1001c1c5020f440c8070100c7e81b0707292100d41410700c0030940700e001c242c0e402601d1a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 138170746 1250 138169496 138169517
    0x30204030606050d0f030804030c0c06080901200a05090d02090103060b0306071b0f060902090a0204080f03090f010f12020301090c0e031507082a040806010b130515070602030403030507 81
    0x34042c00190b13000000b002c07021550200340001c6c0c080e00e01c83d03130064080d1820b030031400c0850b40c070200d07181044d410020100300f6010030400810780c24040c95078051030303d035054250020561402200303800384594030004e111010039681401c0c0c481c08051041e039a0020a84112565207081a034000d10218888602074050080041c019900894191480d454200c03e0004000c00035141c604580c600804101e94903a116545070300541c1d00c01c13500764050303400e0ac0c000690b02c40c40c00c0c0e4194a095480561005181c106200c0314616550380141d2002c1c088086c2040c502440a095040b25403540704c4540340300b02440400042490348103a4414905540e5a8550500d1440c09038101a40c0d200e000b502c034110280c0e250009452a4813034095143c01854840b095850410f00035440d81d4124550704034a41440008941007186010400a13180102500b0040780d00c0c005d01c60300034082403c0c0f6801503900500352881c0b03502240300040d045034070550b00b0030307011502d0b820b1914006000e48429200140000c40c50b461 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 138171996 1250 138170746 138170749
    0xf0103050106170307030806040204090f0506040b030109020a090504080c0609011a090606190327020315060603010603110702040c050702011d0d2009270a15021e0a03020403060605 79
    0x207110f6200e040c0d00f07001310700f015059a0700f192003410003080d55401c103409010010b0150b11b030303008032410305007441000304844c600303807007400203c0b504160014460fa040c014a00c0150b12200f03040b1040d5010041d020032240e45908203240e00703108400000382c05200740c08c10015100300650000880b100290320b0400d10408080403c00c0c0b860054540e69404407040003c0140280d211108802e000507a00b000300e0400d1005040034070450780319080d0401081d18100340e03421450144440d090010504044902600b4468085007160105004050078035646540310f00b445c041d0902a503252603402007050041d420130000003000c50b044040101d01040e0650742407500080600000c0c000410058540f00480040303407a20700261460301a10502269120700351000ea45841c075600d0303c0352802040c1c0c85000e0340030349000403001800300382003560394010400c40e000180030100c00c500085850400507071244202c180d41529100c041846241c01c407400181145a5500b40d0081c1048a000740020002d0613074400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 138173246 1250 138171996 138172019
    0x70c150501060e0409020d06020a180806070e10020a050a060c08131104020901030b090c090102071208190e0406030b0106020708011a062a0109020907020c0d080d090503030f0103050106 81
    0x14407000c038501ca00d0b050a0b60a29034017596070640028249982803903591610b1080380c1c001650303d00090341904000303201420001981e0300402002008000d1440c100300010f0883d000300000034840c4105035040018144204500f80b0759640090a458400d41e185c50903a00500d501910540424084070008006102501c203003c10781c0d80240d842c103054151001004001d50052845d10705040c0d132014000215200c5425262081c410452100d56581d43d1000180c40c15401d540507100c00748000000f200000d440300e050322a103060200e0060f8405990314030994a07100903a0000380c00c0b600d0420000144100100c2507812101141c003651401e03900c074201c01c0d007a11890b040182040301c444445006034100b0100030701c40040381c40440c00c021403000c41c0112301c0ca1304450020000d80e445d43c2456095151003074416802c05038900050402600100120344800c140c80405040800041400301c2d4115107604121000e507413002c217982d624a817112000150300303400e00099034103600e0039401050030307054032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 138174496 1250 138173246 138173249
    0x806040b0f07080f0a18050109060501051c080d06080316060501122a0519150e0f01030e1204030c080c03030f030a05090111040e04031101060605070206070203070e070c150501 77
    0x155205990f603a19084000d00b40400980013505075969195011581048560201440d911030f8001042c00c0d219070601c58291001a080f241c4900111030b1804000c2d055074a0458145502040198503035901c00e11080042026a211880502002030315200600041040000b411f20501042295988565001260300c0c0343c0034008000c000c020301f0420014900fa1440f06411340c24080d8080341c251180041001200300c0344081c3e0902c09280c41c284041504000b202009100d03034500302090349020300c00210710301103e02a06050542d1552140c50041c02848841800c03030b14036200d150340720ba80f0700e404650f52410344150300142c042d02e0544c104c6c170310f8048121b0700c14100c46821582940c03500550a40107001c081d1902c00c0315982d03019000c0003511100050401072820503084050744c0f6282c14081c0c046045a1481d900c1d83e458031009100791f54008080d11142c43d0196220382d110510780c40440c1c982003040c1c111011580ea0b42003004500c0c0da00044003500c903841004181c108880b0040d452040c2c2c3c00a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 138175746 1250 138174496 138174511
    0x8030a0e07083a0c030e0603190b240703020c040203103003111605100f0311030103050705010f0f09030f08071502091e060d0504020312040806040b0f 66
    0x4481030380b180340071120000300f0204141040084022410003a000e0810b26501200c0108040c007829409040d0000c0700200b40410559a0610310300c2e0051071225201a02d4084500c201e9803003401d1003154654951101c83c01d02e858900c618689410764500100e904030a00440c0103204200a4441ca41050300a59003d40c00c40c0c0c094005031070809105101e0003040000c030021000100d015921300b5049070760300c190740714026101c02d42044444403445040140d0500701c0802801151000c110316254502e06481002c3c0c1440d0129641d540384500300c02502150044118050700400040b0504c50042548821100242c07298044000c082d28140e90300f00f42c0c5030040000c1000d00300e041002c074030321800541e2403c1c414070985140010b25074512072034a40c1c00d010788030340035404902c0fa045400e0818502c0d108aa038220281006901c00000405600c03844407844001c0d520380000c40c0840d142001003562407203100101c140c5641d282d1503000d60f64402100d06403a0038540c04042a0440410880c09004081 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 138176996 1250 138175746 138175753
    0x90807052709030c030a08160f0c060e12040f0503190b0c07170c010b01081f0b07080405100201020a03110c061308092814130903020106050d08030a0e0708 68
    0x30784024100701444010910724403800100000b10f5486020300c020504441a0b03100c18026003480c200c14044610b81d810340000344206480c0d404e20700358001c1e031514040d6900000200300e0042d041115404c2c0590b030284002c06840100d000302d02c1c0c0a510001405440060781150407150b080d50500c40b40c1d91004a001c1c01046415000c100081d45500080c8611405101c240e007003808400700840751036006d070300301d0b0384565511602d04060b982d20090300c0da0414800710400b00c1c412600f094000c1002c0e650f1042e140c0d002c00008090040000c071b034040d03400800e00201a019884040c940c003034080c0d44507528050010345000b40910b543e03c0c5000c250740c10b0b042100003c01e103036601c031000140c1a0061315800c2d191000300740300c181c01566a0f01068a100c0c3c0f1001c14400740003454018948450150303812400500f040d100c81c056480c0c0b20302c2500841e40c0201d10b40400c43c0d4295040503401060715801050700308107050754800038000c0b050700641c081ca1003400100000c450600c00192500802e01036440d880c0c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 138178246 1250 138176996 138177049
    0x3010609140301060e040807060501053f06011503050618070c0f02030d020f010510120b0408070b0708070210050106020d0e13020a020105090717060c0d020d060609080705 75
    0x860441e03600e00c0440040c0000807a243c4441500805000c00c0324100d41741900045c440003044194000c5500400b410354640c44241480443c0014ad402400048642c881c0003861031400c0304400080c4540100095040e6070203540c54412a1140000c0c8020020102c4d04180101e040c90800c944e00580c090810040da4599444640003210080d08040054407548201d501d800d02682d0184590a2090a260001e03c101c28a10002501b0f54200604160085140507004c100034440150b8030700600c4d91244a80805540d43d2030300b1034507400341d024003402800c50344003044405034100c009640181201d4080380e000c1d080100a01c0b007500d03800d024040040c1c002400c4440e0660041d0191000601c00402c000c6000031160074002c12038100c001d082006030344500030311460800501000c8040c2500d00b903040310b000d150310719040d950707080980707100801c090010b10524248015030595035550754800062010079510f820080c151107590050361007600901c040050b280c60b02c074008040d015145010b103070964 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 138179496 1250 138178246 138178259
    0x121c080112140f1204140402070804050d080f040609062c010807170c0a0305090a0b0408030a0e0604031110140a0e0a1506090609091109070e0a030b0108010b0603010609 74
    0x2d03007001d03520510501c82e0440c40c0e44a15401d100700100344a00340d14082c0c42d1032800b4480782030620b10390449801140704200705004076a24504542c2a580103888450b0403440300d1800400501c9824490522404081008181a0b034051550001c03545e0550b0b07448a41180c4880707400c07005040c041c10182070811184416003070b50003800b145034460010309003400360100b00302d008a82c001045510700c6801500003102001250140310381a0003a5485004284800341c503691002c0303000d00a4005401c00d607002c40041c0c452410398102826400c900d0090b510075050929005d4100070141c103400081d400703840304108403038209104019070710b03032508d0840905e41c0311011210300074405004a01001e0144620f60800306c6c41000041d005041b021400080051070002030301d0484034560030509081d800c0001d40300c0130500f140424401010100c41015840e04e41d0002580c9a10039079607501d8000800e4000001400300b0141a2812607014000a0001044d440c0c100149031100340554004500f4200007801030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 138180746 1250 138179496 138179513
    0x120601030b1c08040e1602101e2f03070e010e060f0a05041703070b010612090506090307062f130801060f060f0e091f05121c080112 58
    0x200d80c1c09041e004040303900701c00c0501a5045201d0644403010b000804011328907100038600c4c0e1040b45941d2800d00301a103014025114466040c491080c26140d04401406071405c015500f071228100d10304000000c0316038001d1100f8503102e031040d0391300f43da903c400c520180c0078101141e2140440d0b036220341044a194005442e030544201025810503000d000c000c414000da0703001022082e481e900da9944135031402c1e9900146c0e61010b14201d09981080c403540300000c15085010303040d101a03040400e03811040c44c086900400c01c00300d029003184155418820a51404001032002d00d0041005009000c002070b031091300c2e240151010b2142d0444191402740c29265040503100070005141c91a07000c42d61801905c0c00d4440039000010342c0e080c20345040026940203403411001a00c070f806c22410000b0b00100080c2000304c0149045441e8900c0740c501400844035a40e80000f405000745042c414600c01011203681300519540d46500200c0041024500790082c2a258104c0740503060b583d0300b01400c1d0356503102 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 138181996 1250 138180746 138180761
    0xa0e0d0f050c0303010e09060907030c09050c0d0f061a0301080c12030c07152d050a030b030109060b090705190302340302010b010c0f02120304031b180212060103 71
    0x800005101e052001c0b40b05000550003010301c07403034030350f400d05110001d01c1c20b014029164040940c801d140c10000a00849030341c6003128280d66001949a0301c602c000704561140304005031f08c4c1403500e00f80121070300fa00e6002c5001d4503c0741501e142c00c0440c2c0720b4130400c10b2000b0701172104141c0c000407000300035280840e10f8560862891054904080302d0080c420b14000581d0803494001c194a055040002ea10140540341d225400e00010000c041a03035201011540002100703080100c00609682114020f400150480302c024008118046080c1000b50042500c040c9491103031060001003402d4504c902e058809032a141031501c803035071a1041083d002940401d60f045020800c0300c41e401080035065000c1c4c45580700360704408404903017900c0c000707003119043c801581c1481041041c4070040b543c008003d1001a03410766a1031200c1c035039005014910b01a60f44014101072a100c464504001130f480410119465034003d1240981000c9200041c0e0060115150300002d240000502c42d40c800d411545 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 138183246 1250 138181996 138182027
    0x120305030c1806031005030c0a05010f080a110c03030612030306061c1103190605120a0308191d192d080d02040302090c0406050301061d06180301050a0e0d 68
    0x181402da503101041142c2c0044503091001c0c20080301c100124201070162a24551003210040a80360401c00042c1500e07801d44c60880030000c501d0300080050002e540f12004030340790f100050f0703203400c041c032038447e62640700f02c071524000e0a40000001c1244000000c0e03d014000092155003405151004400d001a8040b07604030210b031100145085c0c16500c10041d0300444c8409000e05402e0105e504103070590b42c60f54009c901816005403010b0210300041031141140fa4503140c070711b07001e0322400c2080d0765100380c6027400100d45192244504040354951569000c500700e900c10b840c0103411104041d04424120300c405480181030700d14000c4d8080302c803591800210b0400c028050300300e52545452410f40c0000c135018880d65800130b814000d40c5003030201541d0040c2152030240c609428600000c206003c107100e6002484600f9500003203108011044814145010381042e032138440c0c0440650314000c8201c40a40694600b5021035240c4425005600180110f4030007889048116407041381c51000a41659 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 138184496 1250 138183246 138183277
    0x4020c031617030a02030f100324020c07080f1e030315060d05070e0a0b071e0212031911010207031421040503030403020706080709090504020a08060a15120305030c 72
    0x800715070b80c503880030314025558104016100e1403e000044903c0c4806009041c2050915004000052030000d0503018a02801da4190061710170f501c1c01c80190045c01d084009900500001140c40080000d1020800d02e1410883e46100481c400180c0c06505c0b00c1c6100c0216081007001512554a6841d107885002010b0001440e00704226003030b40c21220161400c0002075400f0950f04050f140c0340219001500741d840c619485c050755607450807070b0030420040140303c00c0312900111080d50384021503801318000c040152070340d458582100c900e200da0060860008125031180d034411a00051003910a21941501c56050101803400d02400c01e030050207003201910854140c5441c00000204410b0159219100454a03400c140c03501a0074418284c200741c0420800c1001c00516a50002c0755004442403030400165903203940c000b00f11a0f4409030402006c900c1034909100707000392681d0009e031b100308801002c42c1c15541c0310f00361181c44441c0e684002d80001c0301440402d500d02c24041c0200091419848107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 138185746 1250 138184496 138184523
    0xc03050a0c2f010509010c0b1803040b1309060503030702040e0f030a03020c0705010e010c080309030d090f0b01080c0105040e0901060906061e0302070b150f0a2304020c0316 76
    0x5082c640210804024000b85801442c21020084100c00150354582424007504114801d00001d0800300308601c0540318249400124002c05204e4084100b060507041c02ea80e40ca50f1a10a0041107038041c484000c03030b0307407261100001c5540b90380c45a08261b501c0200a14a0b0203196000c00c0003501c0d5083d01d024250040c8042d14900000400041c00c220503070303481c0941c44201c0782c041142072840640c00107060040744801105140e0f4010350720081c1991042039180c81781c40320700c40189140544c440c8012090710300114007040c030403074402e070069941c481c41076900240c2e00c0c1c0210580b40e001500d0314a011070400d10003440703854418800c55902c000f44100004030030381d80b541c1100580300f081c1c0c80b20307000c500c00740d44502129403000000e40406103182400d45c87c0400c070b60385042c0002d40050100301913801400e841b03c90f6540354000d20b844040010304448400b900d40c02c400e29800d0b1070040305a80c1c0500c1210740300b4241084d0007540c61200c00038000c1c2d81030204c00d0300c00d901c542c601c00310200c4000150844 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 138186996 1250 138185746 138185753
    0x105090a050411090702070f08010510120809030304030f02030c01020705060a11010b06030c130806070210020a0201020d0e03032e030f050f010507080f0703021305040f022b1401060c03050a0c 84
    0x605442040d00398020581c5514180f02340303101101c46d811088569040400300002e0581e03000e9103504481a00c0c9640d01a8103050500686d10f0003080055036060000180c00010701601c5501d0b11a4240228103880040400d1401666280440c0c8211500039100303001103103003e80203e00300720010241c600046000d441820024a05e40d00460b18142302d05004520200300000c00c0041d04081d15032400242064140580d000c1d50ba4840c010280e00d41e04d4002030041016803003901540e001d0b250850341800300400c1b009800d6160f80080300c0b041d10542c90324051010111400c02c000d6614624112140c8405003103444401c0031a06103030041d0b6941c41a00351042c8010024441c2c0b500c181d4066503011214100200c022503071660140c039a108042c01030108010700c1d880540080102d8400719000940d090011070107101a0040254600d00c102d200c0607400d09050b0721041c1e1002c5502d120b02e0030000c14120304584104c900c82800f420b000a048600c5ca032000034002c60080640c4801c504210b03945032035959 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 138188246 1250 138186996 138187009
    0xf0a05030a050102030f071407080708040b03040303060312020706090e060625050601060c39060e0907170a0203061801080c090a06060f0e040e120a0e03060105090a050411 75
    0x40884a81e07500000301b1041a60f9a0359040e00f04181d4a40840d44911840c00329500d80100c010242c1090000100c550800c0100c1c41250000d00c40e040c0165203034545820003500a02461005a0725200720810005500348041000019107405444040e1090b0030013800c02c0c58901e00401250300700074100040801442200001c200c00c8000002940513140309150840c10003006a1007070b814032141d00d40020001d0000d0024114051205001c540d044100b0940c2003600c0c1148000d8444a40c9140300215100fa881a03e9800002c003c1d11003c1d40741c3ca494404545012500420003811220f5202154074544241c005581211000348140b58460303801d800d0b1414840203038422a800e03880344080340d04c00d081403104107a01c401c1039030b001c110f0f50745401c3d03002d40011550030510003003200910302c10405503550380c0034050b118010403c0782c40c0a02440000c69280e4413000014010034280310320700150f440e000030344c60b0684034040c08a9446e0b4403070b1454040a48000390007101d5164521124005986801 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 138189496 1250 138188246 138188263
    0x20303040f03140303010b0703030203060a0b030924091c030609021204020f011d120708010c0e01021b0109180902090a020d0e150c0318100614040c0c020f0a0503 71
    0x8101d240500d1803424841c020040120542d41d07810900042040707a4620003600c40c0c282d014100542d0369a0313005d000408001007504560039001010061140700c003030000b04444404606184149540552585030b01c000c20200d804916591100310303451380483c41030609480c42003083c00d001c40d00c20344030f409a03c185e0300300c00466405904480200720039864074480381c00003200c0a080040a40f1035071200d001039400308501580c010203a03c3c841c50000c5208002c4007000b004c14030000c02030f4180c241002407502401c440000d0041c8508500a65400000c1c0814200e0b154140c5504421910300340c44103024408403040c0401d05a92120f200c805600d4212800c0e03c910108000180e854010300906000c80c0c2c00d11f07002c0c403020745c481148540610444004240c20003a072141554403030b80c603210f5055481900d01d041341c0c0300c0c5c05008160320035074030a40c100005075000c290038002081c2400c024001102c081101b0f02c40041e9000070982c0150921a440c003640c0580540900186030312480482d2902c1010f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 138190746 1250 138189496 138189509
    0x607030915050703080721021b010e03030a0605010908030a0f03060b0a02070f060309050604082209050609070c11120f0106081509010603020a090f02070609050a17040513090602040302030304 84
    0x950741c003050382c015030f020341c0302d220390a20392890001c85c81c001f03a031115440244280c0a0b400191444c0c1c950214955500c0510400001d000c0c20f454006a140c981d0010348114070a00d082a401040c61b41c00342110740269044d407402141003080782e0034120f920407c403003403410034180d855a01107401f030315920040c45803148030740042c2501442c00700404110703002035100303004061500c070900c4c0004001240c15500103800c07943d0035444400780b00c1d000d0200040001c003940c40385000da0740028204181e4002d00d10904046a84001035500c00c5816161900394500050103500080c83c1880140780ca007001041440c2c0210450b101c1c201d01400c1b00e42103507042d030050802139000c2c0e0202c1303102080040b030a6911204550090180303a1869021035641e000c2c9019680c1c03034944600c50b100381040c40364199481a90030810070b110b8054982007880d02e0782c0c00210144c0d0800300c00740242c2d9011051800315022184054128208000e00311041c500414200c442111496020000080540c2c1c2c1000039101038840c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 138191996 1250 138190746 138190757
    0xb1302031006021603030e0a050a0e040b09010209010f0309390f0b0304020136081006061d061e1c0b09070e0f030106090209041404020904020607030915 67
    0x100003000350705444a41d44100c04652200070031032002040107105800b02c0f981b6050803800340301c0303900c0011080995a0070240c0c000340704000020364241099002806207014440b1420b03d91145600d1500f80d1244414031400718814003400443c0300c2c03095102d018428010008032400c410180c03140c20801d0840c5991082c00c541c601e04c0280782d65090600c0705c005011891104001ea807524107240001d0000500103410300c001d000e9010440740c40c40030550f0041e0398901189088115400e4030220b080202d024030030062144808018032021039124140545039161190004100c1262005110041d00079004ac2c01c4002804800c02982417107982c6000b580c41000015210f0040c000e40308c140702038200f14001005c0c10100460940e445d180d070b00710741007042407038181a41640c0304041000800c0d40c9180f00d405619200d0300003a800410b5020340010002124144002d00d01820403511801090b2070107035022300082d001c6001440c04800078a001c0340310342080c0000a60310005801034840c0d000903075021a1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 138193246 1250 138191996 138192001
    0x30b030d021606170a05090a0f030203340b0919061b08040b0f0406020403020907030501060e10050f070507080f06010303140c1b01020c060f040801060b120c0d0b130203 74
    0x8a00b1070440001d009a0f10382580040301000202582440c01382000040d50b90359804558560014480031045230380100c0511107181092070001c1d40c03981f0401e818040c081600c00c07136404460600050310112000d50341d4102280100d500c40c0010310902404100251146a681c0a4514099203883d050f8038000d14000584040000743c000111642080c020700304110f03002000006911625134580204203198002c110faa26460303c48028840c5400295001d1080020011038a5160b040300381618031903a101c102d0300c40501e06121506469010340740c045082480700d0b02101400710003918906005400f16210b46a80e44400c2d420001003041420640d00264014818180c00210400222003042c0300c0500d820040e100c25034559031121800120412800700f1071025030320030004811010402844d1540d6001646a0f401480d0300c80c4c410b076115942000c3c40011401041c1d025030b0407010b024010008580d075000000003e40d4407501c0f90310311a03503660f0320b4881e1503203407074540300c03101000751400590320b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 138194496 1250 138193246 138193273
    0x2030a051302010c030c150204031104060b1608030606071202070305010b060304120503090f0712110604080604080f0706060312080f2502030f19120c050712030b030d02 74
    0x4980c0241450304a00403a012540140d9101800440030317034061900204001321440c0c6040009040c20441c07100318000310b000700900c11961032003200754804036810000a560380a1400d0766004400707100c42035810400c8041c010030442c2c402150b01040080495142c40000d40d200d5440528456514005a00528040c410032400748688800c4020451b00907084d40b51a56132214425640c1039a44200407000c8007140800a041142c82d03003007180c02043d5020340f512810b07012824035440e5400d850340c901c004106130650420604903001d0b10086c802a080390345e01c94851042907072145003541c1c00f40804002d19804a545442000091407241d2542d5400d0303014058020084503010700301006d000144002d0100344c88140d50900e07440c4070f6040d8034180c3d444903500309a00b03601603c1000c04003100002141e548204904d60340700c0e0034000350f403079110107017030340010040031914507291420101d142080810041003130403224502c000060b10703003c00c1c09018000824184980301500001590040d90070103541d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 138195746 1250 138194496 138194501
    0x70803090310090c090c0c02040e061b03011d040c080601060503010501110105090703060b03190807020a1a07030e060c0318120109081c06030b04140706030209031c051b0102030a 78
    0xa4003110001c0c00f1141c501d8070b0303003a02c101d11031142c3c482080d40c0d2600100c0b01d40c094503c0d1010150001c00c05c008440d0000321440d00c44004a90000640441c00000780d2101c4161040e02e0513200c01c81c0f030310701d1711070310214462910120241007582c0c000400140000c070442c00304211800303010207a1b0b400c0d031294035000000d000300da5121901501a414003082008404000034000c08807608410049000450007010906000c0304c018404508000f480d07100c001d2040d004000c011243c0700383e484071001c0c3e41d108201d484040040400c81d4114400300f240801003842108041100b410040410b898041c0726080782e46141e204140c0380220b00c130501c80c1c40499103407003039410b03450300345140003440058015559174040b88281c1c0e0400f4142c6410300d0b4055110311091b8400300255621422022107030419007071540806541601e005d016105810011a24503c01c1c000c0d00d1003104090000c1149100324103444081e03000c910005002c0001c20321100c18103c0400160000c6a0240c8000690700e04285029006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 138196996 1250 138195746 138195763
    0x8070b12060a180c030615020303010509060d05120a171602070e0714031012032d050703110c04020d0b01020106210210050d09060605040e07060807030b0f030708030903 74
    0x200740320b04202041001016078900c291142d10301800104400c90b04000c0d8001c1100e031b085820075903d0407aa000005400100443c1a20411a09041d0340d9440d6001c211000951200080242e0428405082620301042c0580401d558078200030b901c07a5181c000c24980801c00720744990465008855480b0b03010740512104014161568000406203419000544411210781d00c2d0220842c000000491131200c440019028200403c1010340e40c0810b410300411805a0542840300440540c0404a8241c0082d100b41d07040d0185c0e03150381d4109403071a1403d0702c1502d01948400d07981d01940050003907596842c402415030702c501a10000d1007a990741d000908403402d0b50003040c20204604003c0b02c0e03459040800c408500e504580491030020030310750458282c01903900c60306040742441000300400202d600182c007a18402e980c02c0004400ca407000655a50042c410800400d40300000320b0758241c420f810403c005035000e0250f1500310785202c0468a480d0165012100341e810118100c585403505010300c0c070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 138198246 1250 138196996 138196999
    0xa020d0c0513090302060c09040e06040308010f0f03030207030210020a020d050d0315050f04150306020409050a1802090601180b1201080f06070509010c02010905090f0f0a0e030412020a08070b1206 86
    0xc040450f0f583c000c0e6440c03001519240601d00081120b510b207554907003102c24604002000d40300a0300b041d2070003a0645400b0b004016038004008004148c0c000c108501e04107ca030164001c040c201e2454091144d150b00031341c0000214001c080203480076868038030b0710800b4203224000a042080398000d009045562451a1203510b0b00080010403007580e80c104280c0482d0300c203c030300207102e084080c41050500125403004248500210700000d11600b0ba50001c0d2181d01c20200c01e1210500d101c44c4400d14034250300c4001d40c4100c0c5140440c2c9154450348003403008410840132200c091703449240c8207006800810b44080306c1ca846000501c5050340a02c03c8005a901050003081c4508080340058035601070b00c0f48860402c04030056110135603200b416200004c12001c1e10f80031841c03c1c100c4101c0d206940440701090114901c0d801f00311028043d2003200d42840000c40032f981801c1c104558150340403408034090380d1101c1861400310342e00605100f240001d00e41c103400c4503a5411101048000c02c0401841039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 138199496 1250 138198246 138198251
    0x50702100509210903011508030322020d0b0a02040b07051c0801030c0e0c0d2c1b0409050102070206030c0307020111070b07112503050c0d170c0a020d0c0513 69
    0x10b901d0b915002814051030048498655140d440002c0402d004040987c62844122400100014151404402140114400000c01000e0030b42180300c6644651030600003134003e03500240c1000802d90107203c4a4006184400246c07501d9510309010034207030001c49054580390000c108003501c2041403900340302c5103100d50030000303031962640d22014542030103032144240c419036440c0040c150708125412160082403a680c2004072824523880e00314207020851100c004250600701107920920001500c00406500ca1120302041d0101340c10b200240503a100c0440340b643d000d000100041c1d503030750003841c8220035912005840f807500140c000d003900d074404051015800100106001306141144803507010030207003404540c5010088001d4a4207910003005a1440b00020800712031103101c20804080724080c104440942546c1e1080000c1603104000007001140c6031200c840350409200090000444520b040d81c1c01c50364150003103401c48200b00700031030f0043c1e4800381c02d000314039103a400b40c0144d03007148404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 138200746 1250 138199496 138199513
    0x13150509090a030507030e0a0b04090c0921050f03070b0609010b040506030423060403120b0402031006030b180f060103060801090201020c040506030f01060311010809030f0901030b0a09050702100509 87
    0x10b52a03007032100c809810001c00190300c009140c09030035060070180002d407a1010b8950348015410940c0c0181c0600d5603800d0420013050f04c0240708001400a40d91004a030401c980895001c5070307000311101c4811150b500541010030072206041c80034056003802940c41d440185006000c011a03094160080c040c40314090200b80007a8950754140e0b54890307030181d04440c04540c815a0102c02c00c62804104005200c0e02c0b04200c101a40b203801e14060340907803a818031200c1940c5080000b6070008807469401000e4a0301c003000424461f4200841411001e0a0f4081d42070002040c940000fa0440f603c9481c0032890045c04660b5030305215140050161500801031500c0e50341c0000d485174031660301c15101d6034803000810403590303040c08441030006940c0003c201c01c1c0d54928008118418400c1c011b40402c0074400041d41002012044800c40d0103960145450320748100300540003018006406500b01c0184040851104607501c183c50141c1031071f40082038a0841c019400b0282c402c02080e40b107407074100010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 138201996 1250 138200746 138200761
    0x6080705032a06030a090609110405060d0206071719020d081b07200607060b0a0501050a170a09060f0504060b121203040f0605040309031202070b0f07030e13150509 72
    0x4400d80e942c60103c9640341d481c2c0314042000b01a0402510203043d5514110015040214801680c402c1020a0350184141c0d500c80b0200901030a8114000e50003400030441c0c0f600142d80c100c54001e115aa155915080c50f00c004204540d13400d01180c02009130b80111826005503400c817800b00ea0200c0c403501d140007080d640810303d402074090320a006040e200007030291000100a48001c0c00240c41c0030780411388071106030804101410010b00ca03140600300f00c074800b1850394458000c40308650882c1d240d8403100003080440c0c101c8120010b041e5a41541d507854050000341d207034020010342c000440c1c00403c9904080c14030404a032a03404c50b4920030b10191107582072446011800042504410f01c43c640c03240d4036030402c20241c0e80c241400800040c9040d04101c01c041d000b00d441c00541b4000d520100c1c20086500b810b980e0303078110340130303031041c0e0f500500501105640a00007021401c0c400c1c94541c0305600128045443e03c00840c1c14a480d50781c480a00d00004031444880400a10044481c8060790a0204 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 138203246 1250 138201996 138202063
    0x106090b0306280510031d0a0308040b150a06080f1609090906090c0b0316020f100e160b0903010b03070e04031b3309170306010309060608070503 64
    0x240c0d041d030a81ca40c412804900f10425849002450701500700c40000d50201001070081001c0c0750020300c02c0c07040f030845081d614400600300c0000c99050711040c80a403100d445001c445200103000014001903155a002c107501d41c01002002800b25403602c0015090643c1e034000c0050005045444111144080108155001d03a1980850b40011400140e0010311f08148020781004400074201c224610800034924260100641c0304018030001002d009640352022600d800c0c404484c0206580440098544a00c15030302c840548404d46049441d4007110a100d031466040c55400b0742d44203400802c00302c0c281d040a0045404010040340600441400c0074500445108040d0024040017014200b412880e00c580f00d510403840d070040301c042ca4204680c1541d004e699540001c8100c201c00c0280346840000540c052045816030090768030003000c3d4503400169450b00010451410581c035000580f0114101e4410440544002c0300a060b40e80d0608080c5445c1030441c0082d113601d550400750340d01c200c04228 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 138204496 1250 138203246 138203269
    0x2511010e01020d110c06040b040306060e010e19020405040c0305040308011706191107080405010207060c050a0b060102010209040608010b090603070608070e0d120c0b01140a0b030901230106090b0306 87
    0x40c11310310280740810407054a0480d40282e400d400000004012980303400b908080c0080740d101d40d5050050f9a01c4075088100036100380f00b2850b00c000e455010440f00ca0002c0010340203050708890041c1030a0f0f4540001c0c6c19101074100035030100f9a140b040c08141944241c03aa40549030017112a0b1a0303d2010141d1907523040300601000107100c105001480040840c0c105100b0441e0741c4901c2c07502c0b00740505182072150300a10619025200c0c1031000a500c6000300106140c00d40c010000d46400d06182c0c5500400c030800030130050440d54200a945096604c5108000c05005104000622480030509003d24000080c1090344290300c90720082040c2036000d25016400718070340c6880e48100d001c01011480300705101400800003005c5000d04060700b0b0380f00b05801c0030240102c0c804085a42c1c0d4a0742c0300010314440c0c010b01c0c1c00208664050000092220042d0b8206d00b2400c0001603005c815052040c22507211034540c2113203410340700100013190f4054040c401511211442030302c1e6013410b03400250080c421 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 138205746 1250 138204496 138204523
    0x2706030b06100504080a08090d140601060f020c01090e09010b1309020420090d050a080703030507080703060b09010c150218100305010e13020123130b0304020918032511010e0102 78
    0xb09070074649c844035030411040b54131680c03605698070308480048d1100c01c00d005240001e108862584143c92000903600c040d240182c444250503070400d4860000b40070020001c0805640f03d0001c0e40f895261858400043c09a03110005010fa0709481000152100c40c20030748003041d1800e0300d41006492000c2190003150080f0b4001c0b620049a01d031603070611824990192003580003203a480245078050708038610071242d030343d03030200380d681c034058103404480142c05201c1803080c0030300c05684194010b4043e40c18040c0a43c0360307803504031b918104030b038141d0f406014102c12040c4001800c16440c2007038a400c294441840c18284090760400c4210000044010240507620161580c083d081d6405030f803070310b6170b6030307103001c100e01558081102460800da001000f80c02c0004e4441000045040211082d2402a94024410802c40e115410044950444c0c50345807003081c0010010041d003c0c03200259043d4802c0116000c4510b0324050502074220000c901e10700741071101c00780005074960703808078000c0e003030070344 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 138206996 1250 138205746 138205763
    0xc03020702330703080a0c1b03080a0b06070809041401080a02010309030e060c0105040c1215090305090d0506060a0e040f030807121e050903132706030b06100504080a 73
    0xb00042024060700101445982c510005140004d140e03114000a10a0360340340c205101e020035000d003c440c40c000030300c0411a1144d0101c2c2080000f40318050940d0485550540481c813072045200054142d4400320045604820000390010542054003640c415003080c4d10304000c2c2580351040c0340b501d07428485030090401d9038030b030020703010540102451512204050b2440783c8800814000c039009080030f440a448103c08a90002100306d40800c5400c0c100d0341c0714508001c1c0c0030150040101400000d84124140107043c03146c02440d880d203591110354103000f01c004000c0c034205002804003010054014541e41c058110402000c56502110690425890b20342030805a5601404130341844090001118050802016500034200c1011401035654510003c001c0c0f030300d5003454580e90f84030345203203e000300c61444d500b0040e0100c112140000e8400c0310315440114060f42c18030360f0032110075800c1140d09a8198003072125504100e10401d16038400c40c207101d840c141c10001d00b2a500d403010070005280c0034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 138208246 1250 138206996 138207049
    0x192102030406030e12030c0a0905030606030a030e06040509040c060810060e060d0608030f0a0305181e03041d090c090103111e030f030910080f0c18030d120c03020702 73
    0x208111143c20a00c0715003241b522030034031001401050344104201c2c00064400000401c46140104000340549801002400500d206036001d496490340071811941c070450601000680751030320364030548100c0c400c0210416150500f58080c00e0103a000c1c0c4039503602240c20750180103041d005443c0240f0500111001511885070b8070f40d40c80035001d030b174204204500000c0b42442680743c1c611f011784512420398600f40943c3d607456074040390042042c00d85006540c4084c03101c800d1641c2e806503038000c0b089a00203030303403605840303581d0104640c0310f0035402c00c2c1e02e02554041291004d01440102da8504003120034038220351464a0340010403000c0d10a4901c256182242080740250111001c0c0ca9880f001d003e039400b8401d41d1506603169040800303440e0090034174061466419105604d914801c0e6182024000c454480c0310702c030701103a00715144001040d60001c01d0b900450346c0c100040003c1d40c90903070b9200240d00895241c801074907002094074007450300600c143d20043c0d960740c0750b42d14012819a1001c0046 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 138209496 1250 138208246 138208271
    0xb120c0d06090e071d0106030c02100e0d17040b06040507020304030c231c0b06010c0f12030e160b0901090f090203090705090c0d0c1119210203040603 66
    0x51054000c0d011a45240200005505050350000301181280e90f0a54915660701c0c038904612211414a85408071244001406154000c3d800810054114412940072941c2d103900c45044800035000d81000d98091709002040030743c400104408041d13120844440707428182d951200007040600603510454950001582c042c0c42041610029504500c001004558440c00da40d040170400d84d9006c2110b0481040c1161030810191041008881c0c004800c14110b454071000f00d0b800c0041c280b54100034007404281c01283e0244078000070140078070603186010309654400350480c0c954003007164036a000401e10146000054030010201c0c1c0c00010400d0343c3d4100384004807070b100c2c400e07082180240311382c000126000105a000e140328403c410102c8507040e44a10070006001003c9809010170601000b201c1040c42040e00f04d034441d080d040c2041e56456101000303150804442003841c25100c2c110100c040280940e061242d20084940039499040001c7c001000b5243d04c564015201859201c0445d42c410 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 138210746 1250 138209496 138209521
    0xa0e1903020309130e06060103021201120204200d0b010906020a0b06061902030406020106050307030c03081c0e010b090a0501030201050702100e041a09090d1d0a030605040b0103031103040b12 84
    0x98002000c100c1c84c07080701c062000003002d03400d014a0b40c91240d40c0020b10341d035000b80300b160702c4040c5581c000d004580ca0194480d08071240e0704401c0340c000c2d403680044007441c4c40050914901400c03280d465a220b5030040061411a00d5902c5401d0400502c00810420715801055504130260010031202da50b59510b004182d251041403681103040c83d90325500c210315079010002c0d20980f00307030f83e0081c4019692401056a640e04902025140c001c08130001c00c00a802e5030020050f106020040e0340c400b2249554000481c0d011418030003103a5120b01c182011440e1601001da80140b83e118100100d50464000070214040c5a000034052605072400c0d500302402081c0002c403078080100700340030020781001000545190041250300906401010441c00c0c0710100d81013041c0c0800e0741d00c040c0d5050000c00d4520400c07840804440e08420384480c040082801801b5070f504c03a40c01011500f01652440c07070020040322040d541d1a450341c10a120a01c1803034840c104031200c0e42030a410290307039510b0b40500c0084 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 138211996 1250 138210746 138210757
    0x8030109020708070c1410020d02070902031e04050c0f030708030a0f171e0106020105060f010e0105041a03010e010501020303041a040611130e060409050c040504030c021203040e0a0e19030203 84
    0xc01404858000348014071b04010801800054540c0308007802c0c200310690382c50b180aa80d180250b048400203000c4038145901031680000e0524000c206248a900c160b0400403064030280c03803580000c0c2c0701a107981081ca0428015110036001022410302d4081c800c1d45070b0042005241c01c00c00c84515400240d441044000c0b00a117030b098403c1e0031414410100514600001d0314078615220070340002890303a006208480c481d60001d4145000e4036010001151402c40e41d1048505121092202055680c041ca04542e4030300b00842e81c0319503c2d4149100050048030590010341158010401c00c40002c08250007100036280900d201c0c2c2d0681c44078541400504100002816090b0740032698112103814080c07030800f2140e2035104d4840c039450b6103050100780d4250070009071043d07200b0180d108142c00d00d6131049a109020b40b81c512824850b07070303001030340381140c0000b04400c961022800340035030115901c1e15a005410200104a0610102c100b40c0e110350804140111b440241c110010a041c028001c480c4d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 138213246 1250 138211996 138212003
    0xc01090f0504330306050f010305251d040c050f0607062c0c0907030b010c0206031b0301030f120e0a091802030d090914060d080a0905030109060b010e0d0803010902070807 75
    0x541070f12400d5009520b60040c0c84280c416508000c0402c240800040f41d01d8140d82d000006081154007903003419020041e8070413011540011400d00190f08550580000903d9851000b050141d090134141600b10032196002184614294403c040c0c2070354840086a803010385c842c03404101d60034210704002524110846500c00704030300c440310000140e00070460640380141110644241c0d221002c0490031581d8222026000c0340000d50007102510f060005194006c6141d04090982504200700040640007a801110000d4090380c854081105d00b215540700781c0d22500c2c081d0400500c010011f1788024551099013041960b81c0100c035031403540645008e0003250080d08440f11145421802882c3c00080d1140380c06443c03501e0400081c8a1010304024001c54000b01074003000121901d4030755051b80080b5018003401000c0c8000a03094a00780240300d02c0e180106030024602a160380090580143d9410b5a442070b40c020000d540040c405c0307000d40303042d43e20319000180c44500901d0b00086505c030f1450040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 138214496 1250 138213246 138213311
    0x1a130905061e0601121b090302130c020303182a0312030c161401141905010b0a03021b0601031a0609090d120f05090f0705100c03140415020105090c01090f0504 70
    0x7440d4031074001f40250708807803080d00c0b607030030f80701544006208076031909010b040180c104102081040800e410384a0000e140c82007074400780d0703082000809280d040c12201c0c48100c2c40c001c100a40c9492309005602d44000010f84452a6103840f00340d107642c5203d0340030309501038260007020302c01b44510f005c40d101d03000b1141d000801103038072241d11603401840121513601ca01201902d550484501a02581d81215240d2000c81e0404c001a05c00364081d40020301c004140070407601a2000a040c1004501e00942c010307078a090300210040101e40b4240001044113010300b060320b00f8400360000000711203082801c0c0c0d2804609004404031984080d1040c0c400c40a081c03401c0c00c060121082000c50703040c20082d0710a04807002d8030baa41090016000c00030f01c400e4007080803990400082402440134000d00c1200b20711240c42c2c06c0d00e0700c0300d00001e551002041d41c0181e5495040000c51602000381d8a40354100342020b5100a01d010414108c49059001d068019a182e074440e10f1104c100c10307020005040b030341404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 138215746 1250 138214496 138214541
    0xa0603140a020a090c050d020f130909020a1a0a0c06020d0914070503010606050f0705120c0a0b010e09100e2404030905011701091a130905061e060112 66
    0x1841d40c1d0380c03100d10040c0c2c0708a660f440005402c1d5040d00c1100c801c0c0400d03407203c40c10320208407010b8000750013043c201d401c451802c11064030b011003448110800f0308214640000c090605005010020802d034100301c82103d880c510340032481c140801690301941807440c1914011985141a8020f8098191100303241402c02c480307901001080000b1050780c00703034001141c2409965400705800e90308680300c4c250114101300207091000c4074240027081910301401c00c5a10f200100c0c540c8020981c4074640c0d0701d456400a00b0b500c01041008440c80d4014015840340c00041d081840e41a6220200c0c008596840c83d52400d864444450030701c5011842e040551f501c0240707601d0000d420103082c0702210128005401d581b0b01182c903601807030004108080e4142710f628940e0038510010002c103402e01c0c481c0c000d03c070130400c001c416950300001d4034003001a0442c0032500c0c407c0d51905c0703072400f08090076044a0300c071552415260071081a000c603034810001d180001951480400f901d0041c4980484405118200c038030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 138216996 1250 138215746 138215783
    0x6070204091e020114120402120712060b040c111906110301060c0506010f03050a11011701350303070f050c010507030209100e1302090112060305060a0c08090c090a0603 74
    0xb400c1225900070b880b942500c4070b8120011640d4841d100c03041901c0d002c10404280581032542d014074003040c45404a84200d510b881d00400b515484010880340107459001040c0541000c0c003984020486a00301684c1822010b480c5a8a1340d00d0b00c02c0c0c00d1502c541e82c0038290203211460700511010152480c2142c0d90356140c400041414a4114065075144540000020a0800c480d482e1040b03a41020180c900300c03a080da11209404600030f0164100160240c240c01400e101580d02c9000f0410781b10903440e1411b102d2000399142040d4890040340900b02e015480c4101400f1080b01c1c0e0200030740c58642d1940b01d0b144d505030384501a80101110a40c600b404001400e03426034000c200918040340c0507a86c07200e0207081182c4035507101034074070b411441030b014601801107541c0203400d02440c141011141003100c2c0c00b144c0d04650a950003a11540c3c4810107000084285100f004280c0380d451401c01d010b40b41c02811903554a140d103414600604070040061386034141a40f044028517842040d980f89002d1009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 138218246 1250 138216996 138217043
    0xb1b0f0315010206070c08031306020408030c0c040e12040e06060c0f0a021f0c060f02040812030411012c0105120109091103160605090d021206010f0504020304110607020409 76
    0x207a03140584120404208a28000c008100503542d02c2096a49140c4c0c0342815050030051009013220f2003078080c040400d450f607007070010303240382c2d000c00c0d006240c0100810200011b0f00c922140c1c81606030019401c10040c0e11105040300d040d2405c0e2803100e01350761144d8012070b145101d800a01c4859000328400d03c550b0a1300800e422003540d0007103e00310200c0c3d1103400c9180c5a01140c000020128155100e0000014004d81101842c0c0c0090728005081c42d83e5155a981000030b40400062084000070030003007000b424000b4a14018000e2900c40c41d8100b80018100c2c05d81203290000500034690307055801d090384034030100c03099140300c828060300559641c0c80d41da024022a0000721429580c8840030942820001045400c4000b06148402610b241100607120f17503008501043d040f8011070402c001507202c541000c84424044001008150724016122805a0550f000309124500410500010a82c4624459504030301140e402d43d82d04001c0c4009801450280c0005025550b062909041483c554 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 138219496 1250 138218246 138218281
    0x10f1407050a1b06030501050d1103010912020a03080c0403050a021e0402040b09130b0a21020402030103031806050906090405130c0e1b130303050702210109030f0c0b1b0f03 76
    0x70803010403001e0f282d04c402e4080c0e03002402110380041e240c200e480049603400b002290100f50180000580080b292502c1c01d0b03040c0940b0300000568004031000d001c165021603820303030008090140c1400d00341141c2e141912400c0700003010303120b04500390805071019916005246c070f100c1c0c000e0007155507aa0366a81d1b060340e5044002464400c050b2446c80110308040390017008448540141405002030030107807072800c10b002004941c5440701001107444010785540c40114007950281e180d90740c507107040030040101513405800a100300801400380124507140c042c10f6640940086501207101c0e0b03204142d132030b61440c60300e10207422040801000158114010a010b01404201c1e4008802e02ca0b2a1325032411481401d401c0354001601c000e00b00701192040015100d0184002d24900300d41c680d10300d0f4200d00c00028030135003104d65580c6140360101600004015400b041a080401a2208546a20080650080c2415076000c40b0400c0c15082d501010100c40d03110b0380c040b01c480d071241014074180c2c0c0300c8a4031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 138220746 1250 138219496 138219533
    0x518010b0f190909060504090b010e090f01021810020f3a0e0103050a09052113090c090501110d08190204091512080d150509011403060a0b010f1407050a 67
    0x5c2000215490600e0300880080c160080c0c0c00a4159291841811400d180100903042c10301a1000c1d10818602c28002003250380031854248544109410420141c0d00110689909540c00b140d08421010000b00c0ca80c401c00a20480d6003283d02e228800c0011100e001e08580c1840c0e454800c84808826040200808040004e913010040c41daa05020b00d01118030101e00501194041d500c00d0300e9034201d4500080e510502141c91500b031803030304c00404810360a80e80181003011348a0050003c000e44c0900d860004180900e04015400841c0e08656203a1920211601c10000b8500000d0714611070101001c901082e154411590340f6928450b25006200c001e2070446050a4a000010403078520140d120849400841d5207103072440c0000c1d040000c00c682c9a0400038008001c800103455602c45900a0080c035000000f0000c00301400c0030503086c202c0050a5581c00340c41c1100101d001c1e648009041e4038405542030501320355005000c642024018000005c1c507621819401804022007142003143c1e0b4001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 138221996 1250 138220746 138220751
    0x2070b010501030e0c04050c0409021306020c09040b01030609030c0b09011d03040806010b130b030f090c03010515120a12050901020d0507030c031215080c01090518010b0f190909 78
    0x200c8000450540d481c0810440080d0700c1710b0986400c0b85072030341c882604140d940302c81c0e80c50180e0714125070060760001a00042c1c4403d624004010036a014010110700c840c01712030740300d6941391a61340c0030105c040601001d449039540b08911402c1600030318030500150b801c8404040c003454100d0401307010300350510100b080000121000c21003000000103641c00d5404920190000360f01f0040b030b00442d0381104076940c0080d620071400007840900c880066000c1c26490205031000d1604e1045545803400794100343c0e000b0703850807081120b000c69130340854104010803142c0c14482046030312010b01c0c248460a000c0c10340a9031651612030143c000703004191040080e000e480000d088000c041d900d9006203880a0007207106071ba1840000b0b03100f280f08001708800c0f01000200c0c980183d202801d0100d0540040e28181d0200204003050741c2c0190450303000380300c112a0074401504030701d41307100300038410b100300740240d00f000c01c00c180e0749803203141512081e22103100429422080e0f518010301c2000584602e200062 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 138223246 1250 138221996 138221999
    0x80a0f0f0f05370b03100912080718061b020621071809020304060e0d0801050f0409150c050403121205010f060c020f01030b0409080301031101090806180a020603090102070b01 77
    0xb03544129030306201000100001071160000f1644000d1306600c01d041e540b60140607107405e8656454421079280c0d43c01000002c919941c0240094041c90028040c8814003499165015040c0341d49500c2c102612000e240a184000e840d00210120460703810300207503c0100424440c83e1480b071810074029031f008281012409032500001070311140105500e0981c428002e40090140304030a8008603046485041d00041386528011428204284514000006117155004100718507001c0c01070a10900c04690800074140580da90020607898411040d102d40c0c0c582c5044090716000e04142d400850300403500644002e0001c02c01000d541e0440c0c0804021490500046800d101c14110300060b0350751030700c07002c00d142c1c05a000c102080c250902c0c0a070400da25810001d18640b00c90143c000344620070701e41107450f07504629100c0d45c0c0c4c036a2050210304200b071a85d001c00038900002005600302240722082d840c001e600c61041801d01d0b504850194004400006200c00c0020540c01003040c28042c04180003181d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 138224496 1250 138223246 138223291
    0x1514130311030114060d030c170a050c1204050f19080d02030301030303050702031e0304021909020c011a0a0b071a0c070303050a061a282d080a0f0f0f05 67
    0x210b13003a1200c0390007003501118180001c0c010300311401518000c500141d1601002c070300e00b40d45903004000b1600044c00c04902c1c114840e00401c0040400110000d25174100745c10000400d440d076030360794a458400c0c10a000040e80c04112800300c040a00171076400c3c0c6070704004045020759203910a01c0200c0000345000002010f061010090b50300040440c1111600752a002682c503200b900003600980c0c0c451200402c071040686c035079807030304001c06800d4009a19441400d22035802c55204583c4a10820809651841541d0360a0a5402500d0305035920b02e0303c540303840c14056120340313041d04070a103509454414802c414400c40d0203090410700c00da405102a5540c282c01405560a6104001944a1405001e040e03603045101920980303081d42c80841101c1c0c800039840214940c0070048801069951720023880c40000c000082c0ba0f0014050f07280448404450002040d010005042403e941d5a858054002210680100f032429040701002d1001d811100d00380390041209558080800309400c82c4158075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 138225746 1250 138224496 138224531
    0xc150305040b0403031a180718030503030609220f060f020c0601030308070201090f0c0503121309270c090b030d020a060c03150905100b0415141303110301 68
    0x1d82c0c0e126442c0c10305515240c0e000e8026100640300083d4049242100034100d0300c1d80642480600c450704c100100c24140307a030020f00443e090b1745440c1046481801c091002c40d80000031207400040944140300180c0c0c5519200300704a251024961590000c131030b0003c02c1c03244c00d29500c0b039294000c80d420480d045010480108034440ca620222480d08010300400c00301e806654270301e500821900010440044990b0381c0c040c03042ea909000c84180700c0041003800306082c00c129401d040080c0503d014907240c03a950401d0345e81c010501c2580c011075207807413405034036081c24618410700840742072010a484143e0701c0c0c080440300503030041000c0d01c0d150803250702c3c103031070005140721440007a82c01918501700d89496210180032169030900501d0344444260009401c1240e000c00141a2003000151504040301040d40c0090303540e0104011100602042c4640b03031030203515082a001ea41802e001071440b280504550380548903060315000405440081401402201400c00d000110020803440004007032190b43c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 138226996 1250 138225746 138225751
    0x30201020a03080414010e100b09070917030f0a0305090d0206010b0a23030c07050d0e091906090606020c0102070b03040b010e0c0702091e13020102120a05070204090c150305 76
    0x1603006852000c0442d0041e003d9942160203560342d1480a0705440c2110309448a5140031583c503804800c441504920703d100c5c081700f18074112228115030900c00720042140c8014054a07003900c48214210891800420032208051010051b1903240c0a480b100034008210807103140103a03005591192415a1010440078169900140154101103a981c0704413940a81d807840d00d10600e0080f89440018503d10000d903200c2d042a06039070360303501014505603040c00800601c1100b07211220621124680d20100c03e01c0d408204451200d00802414131200060325070346c1d05c600b04e080e281160200b800390303000ca07091012840c07c0c1c007100e10f81342d07a80c0c1000e2801d00c41201c000e04600c1c05100103000c40d10317001c0d0210350040d034a03000d001d003006050703000141104170aa40c5100da0114801c1c02c0441501400510355111f500e0206c0c3c100b0300d07203454001070740342d0034850b46414000c1800109810b201c0d01031b00c282d4024940190007084181d09030324011601c2483d6025009000402018420209100e17000d0a407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 138228246 1250 138226996 138226999
    0x14032a100e030a050702040f050a02030601090b03040201020601060e0d0b07020c011d0609010f02100f051023100912050d02060f0705040522020c010b01080115020a0b061503010305010e160302 84
    0x10303d01460500f0488040c1c100c50b0080307921035200c0360040ca8119617409007900901c14240010703941c1c20400c00140482490360700c020043c44040c0308100260713030003181090440d1240c0c2030055104002800003640c081485c8001000311803003030144200d007540011001c000800a0300c484907a4001001400d603981c10700300607140e01c040c080102c03541d81d501c100244181c0c0001401141c1040021005c140151206001e59961060b640d03030030000c24591031680880208900008141c020201303414a841c031075038155095014400e0b1504400720141b0503c0004014513106501104049880c9000b03900d6669101ca502c00611a54000c120400d00d01c0582c54001c582035241c082c50540b901c010301021940b82d40c207e9000c40c203010802800796000c4d000500e204c141903400025000300d00c9001505040040e00806552581000c040d45080c0c0c0000b02d500c2d0294010318481001d0360b07418000781c1d08905403242d140e01503d01000000c100081504100c900c045c0c07410a41d8080c802280b54075031004020b11019 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 138229496 1250 138228246 138228253
    0xa050903040e040f0501060e160e0114031f0b0f18040b0109151b0f0203100b0a0513110712020c0f0d0803130c12030206010b1614032a100e 61
    0x3d0004644880b2800e0052040b00007065013a59400c00104801040f0341d100903d0854005c482c10f03d9500a030890040c40090070404443c154006d00800b09006c002c00780d004000324404021032024204050f01d0082a687c0c0c1c072030b07a84040720b030480c2c8419004045494601c07585601d0304800d61400c0d000d0304442a106964800d1004d00c0c042e040c595011240e03051000340300c000012180340300d40d030b410030400503030181c1000382c0c141d90709105240c50500303111150700229250174101c441950364041010b080307800403189003802481004d1050001c011002c50640c107030368002401ea0411840820b0140703420525025075400c08000070610881540c1510415406001154200e0000d0f4500000d1a00420300d603000101c654000c0d80c1300c03442c40082d40c01c107121020803e00e203181019030421a16015224052246040c16607002480b15503450220700100054405001c07820729020802c10395090b0030154403800300720a641e40d030f8421109924442d0000b6400f4648200c0c400300c8803070152804013616003000703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 138230746 1250 138229496 138229501
    0xf05060402040326040321020f010608190804080303011d010608061f03090c08070f081b010804021302030f04020411030601090527040c05012705150c0a05060a050903040e 75
    0xb07942110301311800ca66140144004400f18012400080140c060f10b00121030070000c44001030b04d00300d20440d00c0c1c5581c2e81410014000450041007034400c0084100040218010384d141c9200540200d400042c0302d031001100001e46800708a00e05069085032946501c12030b62581021030704004211100c1e0b4018540112450000c044e000320a521542d1920700003c030081e080d516000c0924140d40001c509a01001c0180941502c8100c0c1c5002080309100502c1205441440c9076820140948a541804002800202035490f1a0b203064441a0b000307600315681d14050b64003409084041d103041c0e02a03440c14840d4003851000604403400750b03005844003031171546058104a24903d10380680d0103042c860000318281074100d620020b00a41c4107241c4400c0c00d03810b00000410751480b00c41d42100d0900804c0018010b20003000044040c1e8500390742412000c0c6010f0306004a9115040248829100d410040340c24444040307166401406242024440c0c0e40f6400e42c107540c0c81c0a00e004a003e5241e92a01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 138231996 1250 138230746 138230783
    0x200a0527041422020d02030303040b2e1205010b2d06040509060d03020f010f0e010b06030c18010e280504020f0a0309050a02120f0d0302041809060b12010f050604020403 74
    0x810072544e20080841c110610243d0110741160001c2c1c500f207a2000703002d010b0014424510034404031710603050707212044644408510140641640c4500c182299895416501f03000b801c0d046403140708006802c091307035091110188c0701c4c04901000400c1d500700d02209007035003d14082c412070b811204000c0400546881c0c0604108184048507011020340c401d012095410a0081c010700303080c0300e2403800001d4039400c01122182941d0100303682d10f110b8602001000780d04108001920300404407005440500309181d40103940304074030011030541c81f454640344808524100052415000c1c40d1512a40358070b03940b18140416400b4031101da2426210600c104128584694844581c15000d00112001c00c8150380200354002d221b03004092054015290500000c40100004280440c0314601180303010b1816502c40d030a50100745108640325101d50360175013880040d400c010300000000b090710100500500c4030600801d01c504100300c4403818000068000e19161007540c003107a40010801c41c0b1415105d4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 138233246 1250 138231996 138232051
    0x20910050c0c0312040807120302030a0c0c0e10140907050d020708070219080613030f030905030910120e0a05070905060d0c03080a030f200a05270414 66
    0xd200220791041c07950b0488155010403101e10900344200341c041c0d985040c184d01320306082c030325006010a0054a845c40c80000d50010489042801611f040d09800116203092581180180e02c00b910300c2280c2c50078016240301d001080303c01c94903000c611000d642a01c0040c4252000704864460104da0b09101390101d201040c0c00420b040b40c0316405103440e205007640080e00040200c0040703c41d03900008014001e5070410082e50760440d210040c0540c581c0358642c0c0003026200ba90401608043d115541241002000c006580c2c0c03141004201400040720920003c00b40d440840e100220745003083c0c48281480004102c82104d1a00036000c3c1000504280b0801d0103000040d20203900311a00f14142c40105000041c22000785214000c1e507903a8060300c1000038143c0b183c44440d2080c0c140743c00c034068516400103400d40d0201c2c041420711522610b004100343c070a4011601c0c0301c000c00e12848406141000300e0103041c4241c0f07404480c2002144c0f08005941905402240d103504a0080d0500003180d107450030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 138234496 1250 138233246 138233257
    0xf060402030a0b0603010801020705010c090311040209062a0705011115100b040305160e130b0c0903010614031204030b07050d0b0a06050d050610050d020304060209030a05030705010c0302091005 85
    0x401d010820f038814001180c6150300907800000b90707941c00302d240010010280522480808070f40f428242e4242980c550303094808289844a00c01c5178001400030700e940f10700064130030301c046c004110f81210301c07805011800841001d04495042c054020041f403158011666140610016002003c0d4501120748541e000e400261100261074404c480000e80700c803424004002462145001d8058030200000c00c1251681c950001d42841e900d0108024030003003001244040e8603040344480f244c42d2940c100c602d406114010465405d5400e0500108200104440301940c07050260200e900002b10328555500b5809140802000c1c4c034541b0010514051190001c0c0842d1000040002081d0420900082c04070040d43c1c0300394046540420542c42001007031141590010040e24035001d0b0304a5600300a125224880392a0b00c1c140d4080080b5040c440355605580940c48054200c4200c2489030070041e40d41d400c0030300210b440790b007416078500c2c1030b0740700b8025504a00005072544000e001c01c5001990180c108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 138235746 1250 138234496 138234511
    0x1909080d050d0b06031006030e010b13020304111e0319080910050f0304030e120d0e060d0b04020304080705100b0a06080c0c010c0801061404030c030803100f0602060711060f06040203 80
    0x50382c003ca440c5070741e213800450084980080780304210340f8000002c1d065640420a01d410b070b900d401c489908980b160407060b940d400400100580d07070342d12403800e1140c0302e00449800d81c10400d02c81d0a1802c01d00f118040000c1c040d000ca00700d07200c00011072a0707240100144031004180d500203200c80031040c1002010f440e007081e4581005400c150602c515485180c20880b0180e0000d1b40c00010b5440e2400d01074040400c02002e2005020030b410b141e80301402c03421460102d40e0280324001a8074140000c40e51164801c0c80c030061080d5a642064146401c0c00d40061000f59824003c4280c0128184c009125070149000040c00c8081d50314a480f809076100b440050080c10041c0341040394000d00b8000703200390704052280f078580c4000b5504000004180a801540307030a0707450000c10003400480d2402d4540f83c1125445880584d503541c3c0d440d5400a640b0090b4032042003610402c0000c5a103540100e04541b03d8842d6650309100a0503000c1c41603580d00e820303104000350100384000320f0b100f810260003c44d4003456 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 138236996 1250 138235746 138235751
    0x30c040b0d020607080f0304030507031103130b1602040207150b06070f030e0111030d06030314131e0f080604060b0a050108041103030412050604051506031c091a1909080d050d 77
    0x49461b49980d60b910031074080f8005940000c4000805400c03040d0701c400e44421900071402c250305002c0403509240b2900961309181408242400c1c03031806042a9081654084c000350749840151403d01848150040303140b207454204a0148d01a05000041d924055008103090b0b00b6121261426542800940c00084c1089000241034050010401c018084548420070001d2518075508004001001d0380072001700626040054581090b40180c151040d21602d80308280c650290000388003980c0310650115120705030103800003030250000b00c1c080d403043d40120400c1c8600d070307080b504108144945000d0325010655040100e40804c60359100f2450030240038048038601500c48042113a0020710003070032900c582c00b810030002000800e00070200919024504034800c0e061210001e515501e4968082501000b000c400e582d00ca8820040d400040c49d91010351030302186203051425941c1d1000d031402d4001e541c0484421802403085132a10101c40e90100541781d4108071040443d07035640080e1090804a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 138238246 1250 138236996 138237007
    0xc0b04080d09050a02090603120a1407021009080105060f060f0d0e06090c0f04090c0506070501060915091503020a0b070602120705091009050d03080405010e0607030b030c040b0d02060708 82
    0x41c05441031101e614010401002009403e1041100300840280f84034000d0304000ca9495100300d121080d5100c140540c100b06103c0460804144c6041c02108400b82d03100d1483d112015a054101195805855800d030003800103507620018003051a00c404e4078a034000008120034014056000b0241822001c6d0341d0340800c40122545905140c048107940c00547d5030002800404945440c0803000701820040e2000d010948040c1c80d6000801c1d204e12845000d4000011000d041200079030003100609101d5004002c1907038003400380405a071150146940542c90850141040c165100413a400c50b903000303203950015400c2601044107034028017022100e6680902020030425220008144103402903038415407520414020803084001d00130342038003840b155480a11060300d8039540030000d6030305410038102ca40c40c6c601d842401800d9120840c1083e008900a109149500d6023011000b00812021140c031201810204000c079a4039a1300d4a51081c0c1804884005081010142c0002070040c2403590825 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 138239496 1250 138238246 138238267
    0xf09030c010903020c04060603110d0c2006040b010503340b04090207020405010f060507170c0f0d030e030c07090f090b0a0603060f050f060f040b10051306030c0c0b0408 74
    0x102d601e003100303c0160b0402d42201184d801e0a03c502401400c45240601ca003030720f03000d070b428054440d001038103000a840e45460001d0700d005400d0008458120b2242211540b0243c00c6140c42c4d0009a070100c2d0045070010002415180024402c0191600c08a200e016030050503030b624400c2e84c1c00d40090046012005001401d003803048064070041080080142c1d64003200e204000442e80140c000c8803a05480e0501030084583c03060988020540c04014000071500000c01a5007a0046034603480652007034801d030980c0d040000c01c082541c01d055803814881c14103042161078581c02070102101050384080400c22440c81d0035017040b191402403080008513491240c96800e0301090171140354074110303100c0104004001013031043d40c00d5a0580d51040045051000303405006d400c0c040d02c0d05103d00c40c40400845c26903501c1d070008003040c0004000034210301d80c049000d04903030820455a001c640c03044000180c540d001780100b9004210030b1303440e003492554031f0740c2e103842c840c601038412340b86000144070504e400c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 138240746 1250 138239496 138239501
    0x70816090911030906090109170307030f060603020d32040c08060112030905090f04020f030c04050114091f12030e04110d05130b0105100e13090302070b0f030f09030c01 74
    0x701c11000d98043d41ea49402266149040c1d0064441c180d81c0e0715040950001ca00007001b40308031065101d1003c0d941e40c441c41000c4001d0000940e2003c0043e181801c001602500350340103280e0070030312400900000d51941015040d40f8144010090740002101086448058a103420f0740d015100316818a0f40580b036035031151030f0080c00d0f000b914030b50101003001d20034160040b03d440002d103c00c90348440549040242200012800381c0700034020400d528035000e25503414005029a01c0014000304810341c0e50356581d04201e044400c00030f01071245d40d0082101800100b0200200054040c440b2890328034100126602050040c804c0d0100704541c072904255961341d00030b0314243c07a078503e801c40d2510750b6112803004403a006480e0614010142008400286168407c14110750080b103400381e0401d00360f207080e105075403203082a550120014080004004456101d9104107009500302d8001c1074988200785001d106280c3c061000207002c0c40012031841001c01d209900c1000e260079281401415241c550a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 138241996 1250 138240746 138240761
    0xd031b030806090108010606020d030209030a0b0907090e01020f16020d0c0b030f1e0106030e01020706060e0907080d0507080904110324040612080903070b030f0603060c030708160909 80
    0x1001e6009009041c41c2c07a40c20365014201d410000c0065500d0301e00060b580b01c0d4002c206030145030300826020030310794041c400c8000503071b08501841980d02d4900a01c07510307182640116012503250901d5003020400520136a0790250540c114a480c1022103500482008991a81280c0c4112808210f00000d81d02c0c0020500070110f07100c4880c1c03030f4245460105403001d0002c000e010404491440c64038400b1104000c1411500395040c001400320514200d1400383c030402c40c020b06001c0c28002c0001e400740c10501460300ca50314030003c1e51602d6031105042c0c1d4481d000c050900c0001030041c00441e0200b20190700034004010001e0001450499818013409550803c42d06079600131520a03004148969104805000f01011581042081d06001c1c014030410300004021303081e0744020421090700c0d1420800c45001d002c461050a4403450425002c100010301103417414000e000d414041360a131400c64050302d0145c609a240c150342a956140c40220100041c4940d0080000c4a800001d2603082441201c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 138243246 1250 138241996 138242003
    0x110403080a0507120503223906171b1207020105041a07051b07050d080c010c020115090b0102071e050f030705010c0b0901020d0c050a170103110d031b 66
    0x640b11011820204900e016496444c0c050100400c200302c22800740c41c2d8541c450841c0d20310f514010f043c0c80d003481000a400c0c0751601d01c0c1010403650b00758070506108103000c0c42c038901c0091880c1807a02c51204441035184814843c080c50040404151054100002400300340864540d4030308106050b90700390140081520300c000582d40d50801e00091240c10000030390a0100d203251301402d0b05040d0170050280c413988401e0a900100000ca04080c1201802401c004041c020030071910340e025400e2001d600d03440110803907503541c07818140301c1c481030042c018804081e10389441c20718050f181a07049000f8080c107140030b5046008400700442c6007002c0440481e84c019001040540040c00d10042c4500840d80082c024440d51185404001603a402030203280b10300e501411203003850725800d50050190240c18410b00a090601c0140c88080d54018003a09200300c1c036a581048204007269124800102030002401c00c142c944c5a0405500f41101400e141c144070b072800c0940344c1c19102545103198450340045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 138244496 1250 138243246 138243257
    0x60c0501150b0d050a060302030601150e1005030711010606080c210a1e09020619110613120503160e06090a030c031101050a08011a0904051e011413110403080a 70
    0xf902016a2403040ca5031003601311004101c09825134000941d02e04051107079201c4104964468046503110b446241d4540a028141c0034503a0130456001c1c1c1207400807100940043c0740d2240c54240000140501d03000c48030319461310403c0c1e894042894100d070b4000017440d40061082e00c03004008994030860302e0300c00e10201c40c0c00546100d4000410220841c10441807070b46500f418180c0e00503a0ba407030216160b000d0044070054001d0701d280e005507005100c1c1c3c44521424042e20f020860703009030901220109900c515610540c040a1100558984c0000d031104e000010080c0b101680c8035008107441c4400d010014415401c00c114400004c003019545d410031282c440040b5000c00400c4006800c004000600342000d906000c8a51002010a2014494035a80140c2c074480c80b691842c00744200c0380350300b2000c0c10901452400c40d90741c40d12080c48041c1d142c2541484000042e10052071039280389100e100910321108006040051400b4154500e0340c1c01d000003080200000003001d040c0200a81c42c05c541ba407 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 138245746 1250 138244496 138244507
    0x10140a08150d1509050111071a01051c0f03020f1911010206070507061a040e06060a0f0b0d051f1d01060c0f0803090c03010f140c0406020601060c0501150b 68
    0x480d1001000400ea03030b010707180030384034240041d07a02c040b600c00c16a030f01a8000b1300d8200d81c0c1051409010320502284100d20009201418042400c15440b45000c0310301f5a40400d90b0ba40f401d00000303100c0040803100c884001c000c080001000b070814450001c4c02841180c40e0340c840c140815060440342c1c9040204506806015002c01c8040141c00d240d50200340058540ca14040c0005840e600c0b03504401010581e440b900b54280380c6903003d021035100805030041040314189615580c0c0e070401518400d20409142000040c08441c07141980250b80380030f50310381d041003204000302000d8400a042d402004101c1205102c211030b0404d034083c014042c0d040c0302d480c41c944c03110b54070005e0081070b004401000401c02070100420b1300313074040d031305041e502000c110769a50782c4211160604592160103607042d420480520072584140d0460404807515000902c3c15846540711501503104a125400258200f4001009261b016011100c0304902410022482e02800f0084219418298101000254000c00c6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 138246996 1250 138245746 138245761
    0xe030a0305100803031305120703050301031a091e07050d060207030801140d080711130b04180f0b0714130f05061806030703021c0603022d10140a08 65
    0x1e942d001800402858101400c003054952a4803009102510721032421110f6420030004000000000030014001900c0d9149841c00408d0760340207100503284082228100206000800007440c007615290000f044980c1c040208200e0340f150400c8a84024082c03110b0000e0702d9102e4504a03060301c4d1080c0d0005950305000d00c1c02410028060304403418000b040300d403803d0261200004001030a8201041544940462802c15080b1107282403107908000c082c426a8690f040e550400750507400102d13400e0101c00e0059440c0305104000d1030014146000e5500c120012804450410750000224039000b0a0b4200210005440d644030440088410080b62003c004200414405001820341240c80c3c13807800300f06070720002620f01010300030391060000001280507140254121043e0094a1900851860042c4030907002894240b01c240d0041400c082aa910785a1214070425801001c010907500b824100d0700784042140c0700b501340411300010741d030402030352520100074102c144c602340d4600e440c2d0b2a0105 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 138248246 1250 138246996 138247001
    0xc040905060a151406070c080d020705101803020d030c021c02090f09060a050606090d1119080d030903020a0b040b1006050f0912010f0905031305030304052107090e030a03 75
    0x40054800b00c0c81c020302c010704114040300c141c150b0481d5096119012030031f0043c0d180c6083c0d400303840e00d40714071301100c468550042485d20843c0c03001c8400c034840012a200c1039640068644800e0807441c152241032005150043e20518042d02070700d89410844040d0f804a01c0c051540c0b8074036400e1001c0041c0020461520b00f28441e0300420301540c20310769042088100d42c0ea480058094560251200000344007a2600c0c82910305400d402030010051a8035420b11110004500c060140170382d203149540903114948a01c8201100c03d000010304000c9041c03a0214014962a8011400c500a0107031000228400000041c081c60140c1810f40b5682080401410b40c03158030340c02082030010178884103421400300e200741d50307000c5003d552003d203141100010900420050301910311851030140144180000040a0003a89410312a01003030262260700309540da008603c903040d88041000c0c0000e114030303610160980c02c0d04080b0100c0d17400c0b945907801c020580d400310030611000da10101d045241c0580c1030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 138249496 1250 138248246 138248261
    0x712060b0d1407060c0f02100309020319051501050a030209090109080f0306101403073506030609010605090c0f19032007020901050910090c090f170a140c040905060a 73
    0x241010185c495055540369944003000802912034103400089981003070298110b0300681d980101079544440c2603907540c03000c840000d28195101e00c074044008103200071a48409041c0e82c401440310303809501d5582000051000105155959522141d00c6400500410080d00704036103001300c6a501d902e415018000f114020103400820030110070018160341c03a143e012660400842c0c07400c81407010344201c101c0ba100000d01d0f01403090115852401200c0f05607606242d0041c1c40440980d4455152854050f09a50329402380c15840800034020408580045e001000f5801c40d001a40d07091002c807454582083c92a025640e01003915034800d41210038022008101030300395100620300f05002c80d008a1050001405420b018000c0a404140c454062002c60801080c81150904c268000c240c001401a505e40c03080001140c42e0030b6003c100f2843d121041845551068000c18a40300140c550b0b40c0801e82c000b00403800c0e03001d01d01d01c9042d15145d5000b110403950040000b0403007803c020107603000710346030b8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 138250746 1250 138249496 138249509
    0xf4c050a0915020c0102070b0910060e04050303071206032109090e100504020d02090106020106050901061403070c080f0d1d03030412121517010c0206090712060b0d1407 74
    0x24410090300240003100d40d0014021000c9005844d0b418450b5054020304c20090054202e1003da010001100720000300758240302009081403141d04e0351907400e0760254500341c2d4000d0068106100040c87c0c01c6c03183c4e121101404410b800401d0344c903520386580c480b000300d420b0a00c141c2c4201c00c1d80314260720340121000d40140140382041084180110340d654480260f05010300380c060303c40c0003203002c2d5569039180d0744449400800c0c8040c1542e4507040a8001c0285200d003600400c0308100008102c3d00442d51440c0303040d49a080c40d45550703a540300403a40042d40b244110b5403c01d090240d10300b000b400c58050708041c0140c102c002101a112011311020005000b43c8030002c2e4400c1041000044100010b85011809800e007440d4811880e4850300203415030101d2071100d10085940081e00600e003071034001c10010302c03800800001a64071000c0741c40303150032944050194840541001031880b90a0b01c140000e008050016a4802100000340d507045540003d030380748030162040e00180c00d000c4c442e49005005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 138251996 1250 138250746 138250751
    0x111c0b0f090c0117040206130b0c01050a09030801060f09170d020709111611040504030807030c0815060d06090e0a14030c0c060d1524020f4c050a 64
    0x242c00c0c00080454140400301002d11131100045002c6490304003c0c0e03104040c000e00d11480150301e0305503e00c01a0405010100c4942c00c041c003050282c50035100e004c0941d81c042d611818186c0c00d0030000c3c0c1d14400d5071050300e800c01a0410300000e00388803801a5015051101029040e81c10307810100030310b003840507009421414076044017003015140781c4040f10100307161780d600c894620070340b810084040390720900d4054015003440c04000425130700408007442820691420000d008602d082219024021107074a251505062a043d080c0c0c80c002d805404001c11090001c0380246d01c444010f0107881c54101e0083d407540c450b01c01a0100011101442d8030303802d0080c011405c0052070301c3d00c56500c3e911950547e004203800101c0d4055801c030f9811500701c246100e44c510302d0480e520012203001c990021a500c102556120f5181d007120300c042000034042080320300814148104401200c01c1d06000c00c0c548100343e8299801724044002210340c4503140391080c0c040d145058030380e8940020707200010240b480c620b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 138253246 1250 138251996 138252013
    0x20307020706181512090b0105100513050103020d02221703031005040c0c050d0e040e03040303080408031008070609050316050603041106040f0b18100c111c0b0f09 72
    0xb46a040f07120222241e00003103401e00c00d070941c0140c5240340300d100803050a80c20204104240f00c092200c59048030001d80d1041d49170210b01300d0807211405841070b403c1140c40031a600700042d40c42138016121240c004032005250000c14000e0b45007410381c2303032480460f9843d100c1301040a2410900c1c4000103c42c10f00c09541b9501d050803a003441d50350240500740c03155036a01d0a031445548100200202154401c1c1162855070008601401c05c0e0005210b49210f5401d1079a8284052404400c0c0c50850f44e145d281c1e160385454950718040e443d040206180380f003000d000400100f545040006d040100226103481c4000e81c1010185070410121803416401d064120404100c692240380842c2d074001d400c04503420282d9a45000241d95210f990700500c007110400d0404102c034030030007004111101d10303110311503d07801809060240601030301c01000c1c0030882c040c4140001c1041c0d510b8402c0039007401020350010760180b15107150b01101c82041030b103c1c00c19103020024444410000030b5004001a1300500101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 138254496 1250 138253246 138253277
    0x1009210501140f070f200102030a05090715030f0b040c050a021903090608093903060103020307030221010203160305061203031609080a140d0f0e0607020d0510020307020706 76
    0xc04000d07001504000c1ca9031a081801d030310074600703000da0901078054050251441b0010f076020b0f40040d04ca42c01c511b07192102040f85000001004000c5070064280c5905400025000341d00500d50700c24038000454690300440d5441e610782c803a400c1c0324415900c0305d68441135212402450402d010382d010980c2c0c40d000824401194200440d00e003142c0c03441c6442415540c030144142e00780303c050250b02c91b00110000002054a802d8404911007500e81500c00c6005000d0004040c0c1c0c9110a1002a4040d04501c80038005810461042110221405a04100040d480e18500d0880c3e200311117640300d031807103c00c1c400825a03160203920703041503040300c2c0c0304030300010300180c0d03510b84c84054842c803441c0b2041c2a0170b10f6400d008410603c001c1078102c0642e09000d14606017203070610440c1541454030301802c80801c0d2940e0003003005000729a00b030303a81e903102e009502041c401d841d44003d0f01030b80d00500042c8070310b0004c0d20420480e0075000c042c840c0546c41c0d0a041c80040e1401c141504910b040c01a402031407543c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 138255746 1250 138254496 138254521
    0x6050f091309061a0112090c06080c0403120201090b131518020405090d230a0e0f0d060f150501021b1507060614040902030309100921050114 62
    0x2080120341080d441110261444002c18101d44010005030078010303a02100424905005180c030001e072070301c039900d0040c1d1214400311007a00740003c0c40c19000180034030990f4031421402e036100161703c038101e103030079141e480704550715958481d401d0040c1e45840600f010809803100c0385401c19292403440c0d072106d0300c60b5280a1380070f54280340d05086903a60403184010701e210b100c0154040783c018100308041c0c113200e1809615003d2045030400402d42d0100080751041e0170707800f606020b184080745c0a08003403421808130f03032a11a440320741e68000108010f25a096a03400c800c0c2c40c41c10b100701000649030300ca0011410a480090305183d41d02c1003401d0080205980105003820b00c0c0100e00003640d0002c150000090701c040285c5501010f40401040440400c00340342d21880548585448814580b8011420002610010321740203405400a101e0705001d4280040007240306406c606020a55545604400560341d45403207510b455461085904000c0c8402803140c12681d0300d20070300c2261145428201c0054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 138256996 1250 138255746 138255757
    0x209030c04091b06050d0e070302030a1101050d0e010e010c050c07090b0d05010501060503090f01200304140111130e04080702060c150703060501170f070509130603030f020706050f 79
    0x6a488603140b50030801da010a81581c0508120400c1205441e294024503a411181035031142600e001d41e1425100e50000c0d22800b102e42c010020710320101c5540d1041645625a1105414440240050034401c0c0d040d01a08203080b0070303c000020b040e0950321142e400d50b090a03203501c003441000c21034000c03020008540700042e20122180802c06518040c0464030b2215910405480d0723510301000401c550342d12100850141c4c240004444c0e041d40104141c500703e49800341090030040c0b61284400124051502460b8094001c01400f019042c1200c4203500791000c110b120f842500000404010344945622114081c25801103d0f1003d450107555066591198100280c4034172404240304460103001c1001440071042080e410145003450000900680f41034000d050125110314400030301c0300305801c0c80d030b4400c0e10481d1210000d03403103441c801d0b0340540c4030141d01030300089090081e409902e202c0c00350100941c843c1d03981c413031044120000203080c000c0d240c215004000301002200c64004103002904d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 138258246 1250 138256996 138256999
    0x370c1e11040e1213050a0803160b0402031e06010f06030506370609090c02030a020c011b020d050d030b06030123010e040f1d0f071514030a0c0e01030209030c 69
    0x14648200d1601c5a1800f903a02c6480d648503000020064a07080d2a8440c07203080b107030191580c0b005251070780095600d80c003c03000d02c0f5107503510002c03a540104000c02c20445d0017074009802d07240c90b40c4258420084803200d1007800c07c1c01d94006401041a6514085c4c070f100200b0481c60200001e050510020300701560110304111000c041c41c40ca425031102d68a42052001502035018144aa50302c8000d0304510b510f101d03030740a003440c04c4000d411007800842210b2003c24564040d01ea00101a8010b481592506c90000921145004048010388800e0b401c03481242c0244014a540710304100c0080544012a46680c000d41b801e000400c8441200b0100703200c1034060000010032040b207980100c515111402840d5030103400c08d20320810320700e80e9034042299130728091641c10a495500030496a02c03140c42c00b0340184ca6020081c1003081c017880d03c1900e8498444e0380341c02050304070804c0702919640c0069504007900fa955094086160390030120b0f0003401c0a007800c00354100040070780000d840704aa003011300d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 138259496 1250 138258246 138258251
    0x317090a050d0507230102070510080601080c041a0903100c35040f0c050103020a050d18080310061e1e0903050f03090306010b030903370c1e1104 64
    0x410080140884405407042d05c0843d100d1800324004100034400c04040280503005130300d008a00d50900e41107294407a41a504c1e02c2819031200300045661882c01050242c2c464000d1001060310320302841403115050000da1060340340c580366030415080202116001801c3d520b000c00d04070416030042030000e004102e14201d24664410b600d001e100752401c4c11010580e220038601003000704544101c50f80a15402805a045103d4682d00154120300c1485524008210188044d0251661542140045140d40e2100001405203a030300c084107900141c0721040d00c3ea0604c1018040c86a100d40e418100c0c00c2c0005018500410071180a80905440400c00320210180501c2c9d00b00607008408203001540c2c82011545405690340185880760410407545110340210000049e0208021090f41d0107545100301a500e00f85103d102d501940c94960102d4a00c2240701e840612948615800d4641c01e012036203840250790400d14100480201c4103126225040c04a00000040f6030620709841c039504041c0c800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 138260746 1250 138259496 138259519
    0x8010b070305190816032903010902060304030809060c030106050a050a110a0803090c0d050d030b210304090b03010504031d0609030106080304091508060f04020604030614010317090a05 81
    0x11505845042038011a160803c141e070442c080e40254024411600c0745005803030142c400030b00f2403c4d102c18514680080549180c12180f11015038505803c20400400002c0c048682d64003044168004a80560104908070100241c0c40024850641d0242c0c10780b02c02e40c50343d03042100c050418003403801400c04012000c954912003502030b01d0081450101841182d80300202403400d140681c0c8103c1d546130319801201103800ca80d0521100c41402e482d031104c00b5010030761041038218000c1c01213621181e8020b010094011109d803070801d0b03400904170a14041c1d90f44604204100c07043e203079001d8403540283e01d00810040030940c0703d61000c013171801200b0000f140102d8100000c13680d02032502150b500d9403a102000a4980e0b001008104541d140d280c244920300000d010055180e585200340289070700910700003001e410b180b10390242d01500c014460740c01c00b41c0303e4561400b12400141d80c90008550000140300b40400c018405400680d88400d083c82d105090380072680b1074000d072040d40c0c082c141d090305 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 138261996 1250 138260746 138260753
    0x402060403050105090604060c020a030519050f03010311030111041202041e0212010e01120203120d230405011109221103040c030c05041a10090806150414060108010b07 74
    0x1100c0c02140c01000038021400d00c0a0703204d80303440742a6400c440d07040c030388000301030340700d001003880c0007400d0b0940c54440c1010f5204901610091a6951900c200700341046440404000d00c0d020b14065130140c07039210004415070041c5401c40f215825600c4650300140f0080142030f150240c5000d102c5e81c1a9404556a801c45104203000f0842e41152180a0300101c1c0030754820b85411002c90403580c10f06911007141e40d90b109613a482100211029400d40c00844080c04140400d4000b0140006031302e8000508170b08d10344a0a04405413140b525420131410402e00003484024050f003d400b01302000917910709817900d03002420b0700800b5100e1004083c8000801c00f4904c00950200304151b49407a01c0568928140c50000703c10341d1503000856030403200c0c1e440840c1d681814403503410040c68002c09521300240340c0080080c0a10101811802c00c0108000071911138028000d81d8002d6450000c90124080c0c1e0808110580d005c22609090080d100c04c00c0001583c0d200c0801811101d5042c00e00e95074595604 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 138263246 1250 138261996 138262009
    0x4020f0f040c05091903050a030c051c0c03030c02070f1a12160f08040506010608150d030905030111070807080307090f06090905070e010c080d060e1312091208030402 73
    0x2180c198441c0c505000d04076100e41000040132900021903041d504525608484030a4222074003018042d540710340b882d540000e0003840b42d00d501c80d000300704854201900340002c540030001f03452180e0004444008900401d90140152908003140740060301505042c4035090045d094135118103240380043c008000c046201b840110b603015013030000400f00c00e01e01000b06800306040302c0e444000280c0000d100400162280010601843d40b05001e40f0480e440d00c3d0007143c04410142000005121031500e0202d15a11800d041a01034480e44410070b100386130104050855508060303040143e08100308138000a5120002c035421a607000150549130307100c0c010102c40d01586904880c3c4001d8604d074010071200d401ca40d42070101d89850f0305c1440745c2d59030f1700d40480d020902a0305981c0070580c2e0010000010345a0b90192244059070200010b0080da52100200c00700019522034000c0c44030b00c4100020b026003800c002d0303000c064904000d0721082c6808040c0c110b0340307007061006c2d049680c040b010508640c5c030311 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 138264496 1250 138263246 138263269
    0x4020d021302091c0b070203031b031506120103020a14030303161404060302030105130b130f020c0a03200d02060f150d0605060f1020010603020a0303171e04020f 71
    0x2410f04010008004c1c141c94291040030303415901d1020f40800030b40080d2000044a22400b4081090107910748400c40030802c0390005080001a5482d40030120a83d03100c0d0400341885144442111103207526500520a50100c147c010f540b848491640d120700c1a05c0000449400088200d00034042071304184044502016150301d05290b160006000510580d05401a5058038030854031240768010b81401d0404603185420619009444111a184403c107643c0c00400c5440c610300c070152a01003a4803525003840850f100403004162005118501e043c0103540004201c2200c000902d00742c0c402d1100030b50789420040054246000800000d61001c9440c0041131100e100601511400705035450040c0c0948001c84009000f42510340e68441d50345400a0864552006074540070174040001e00d81040406d2a01106001503480b80000401600c1c1c07444054000c0d0300a980d50780030742d42e8030075000400320400b82015912400c1d00b90341e44d2000004c0d103181500f0039812038800745401c1c03515011a00510b4032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 138265746 1250 138264496 138264499
    0x1b060f020c1e100f021b012a06020318120306031c090305070b03060436060e0604050d120b030d0e0310060b03091002180f03030c0d170f04020d02130209 67
    0x70208000c03494004e40c040e410048143c00782c8654644840d130392142c0b02d1010b104540000d0003020303105100c0501491840d43c030038402c4404400b0801035122802a0780c8282e41d16041003451418145004109000c1124031008945240d859820101c1c0001c0e030314a40c0e41869042c40d03a9040c0304008140c010a005c600540c0d0040075100034aa803843d030b0102c503402c101d41c01405181480811918804440515200c21425544445008103114803c5401800d052001c90b40c0541c1c07100d0390b81202c40100945071196204070014045030306408002800c2c0c43e0175007154030809042c00c1190701a540e010031007400c5103803e85044800040520002803804903641440029580381c4003020810b9000c610041d48140440c42c11114400003045019040b445010595110f81c01d05c09d0740780ba0305150017255840b4200d00101280d040a02c03400000d030400e80403040c110045030b10256000c2a50314940d083c5a40300040d8900300d0114036007500410035100b42c80c18001e100780f204c00704603840082d40340e047d01c2407101d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 138266996 1250 138265746 138265759
    0x18060d0510140708071e021e070303031d0606010302072102010c020c010216051306030c06030902011e020a11031e0304050a1a1e0706091b060f020c1e 66
    0x100e00840350020304030b0001c004000300b8510002002d150250070014050000e540d1a10419040e114105907200000700b90803007140182001103c0c032110b41160503a80100c050081d040e02407440c5000b400b00c44403051038008144044940907071000b400701d1010b502c0b000a0801503a150807503e4082c4840d0100184090f94800b81c4040c0205c00e40c0c15405800c2c91907564003110500c108110040ea03650402030602c1e0203d420100f010312040c103120103072182490001c080401e04c240c607540e543c643d03081c071a0450000260742c0c504400c1990383c0611040881c580b05582440079940c005030007525500c8440010300181c1d8941e0414401e900c0800000d40070402a110307044100d1640c010350b40d2244d02510a07039102e000031640c0811598a40b0034491014003000c0d01082c508010003940b240e0b401000a800c1c080b0b8001481400c4c0070031068098103582074414090070320703200307181e600c1c0004400d02a084081008225407100b03610341d40004881034810f20845542d00c0140310310306a9540d000c0a0165a9003091 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 138268246 1250 138266996 138267013
    0x30a02090906090c03010b1c020a090e0f061608010e100e01170f01140708040302070305100903121a0409020406050d06023106050a030209040c021e070518060d05 71
    0x1102050540c002c03c11401039650501545041500384e408a0803441d074091841680d0440354002d101802c128144080d0401c0701080e528000b4030100c42a01000c40d43d150030090210504250500c44036034081c500c0345540341200080580184040e0f01409829000ca40e00c83c00301f0013048018241e0001000007042d580d15645e150a10444210a981d400c11294801c0c400d01e0018044180203183c1400c0c0c1c82d00c0d104075540d407004011548024042d0080d0194001c961010000c0f03402440b81510700c1c120303000c0119104240d4074004241c0c1c140c4038400f0268a140401c51000000044184180d014089030f010a42c80d9050001500074983c4c0d41c05140c1c05062030251104000c81500940005000d450032260000c029000d9002c0b8500700f00c091440700000c40d04240142070040b4082d011181c028a001410804904045412154502498000360b0302448421014600b205c46c148607000100029210291410b00412070a44c00d0607002400342440c032000a4850b1502e030300c110b0440b80c201c0221050341c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 138269496 1250 138268246 138268261
    0x70203010f060801060e0f2a03070305070e0301140f07141303060b060c0c10050c010e0c040e070b0702100c020d060f15060807030e16091406010201060602030703030b030a0209 77
    0x180b280b446480055400d082c80021407001c05810780e44a4103900c4900e000702c5d940c4403e505483e131500c00411500110342140e401e86040790030041d40c8100c0c00d0703442c0002d090074203242c05021203c1c2c14030503038800e0f0704060300360001800b00b00301c4903089141404004056203800c00c058516021035010b940c0c160b903011a40e04110070048500d501241e0003040c0401c9202c10380c0303051060300d100c3c808808296a0003420b9210007405c1c0200600f24030b100c0342c903049042100b03520003507007541c6800344a540290f0064485040074a418442c410144000000814840f8548050718200380a142c0c8041c2c07060244008407102e09000701e0040705416802001c0402d06000c6e4503001c2c0c0104030303240c0380010341032400d084c286109250100384410b032503541e2a0500035503510f04080300901295400c6821a00410300d00300425580035507405d000c0e00c080d00c40419070004902004040c110010a90f60440e8101101040090740200031148429014600400c0da110541d0201e858890480700c000d400c01c000400b00a0300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 138270746 1250 138269496 138269501
    0x6060c0d0909060902092407020607061407051e030c0c12041d0618040c0e15040510030308071808100902090a0605011202090424030203121306030c0203070203010f 72
    0x82e584248801c001058880d58000100d0040b11101904400700c0b61180a500c801c510900428220070303000189001040e034013266854000200c21075200d5150b00365004070060b550042a07100798945000317401c026030122545402055030350b9100350100b0020210300c494400c0000c44018840350001c9543e544186030541d00658014400e00c0403880a40e540d42c840c0c501c6070b02500c0c0c015840240200341d059901c1050807061080500300310b5900d4190200021010201850184603130400c030b60381401c030b541000034002519402410001d4004030300c3d07070520000c2c0e00152015080800c0c3d103000c0c141c0042c8003851102250369604a0030261044060f96800e00050b50040c1c2010307403080d103050005071280f807805001d41f035483c0500da0201e0200c480b558040306241d0702038040c2d0740740184089002003070310700c18140c485061580712400405014041c81541000c02240d5010740d40c074a441d40c41d10500340701001c5010400c0c014981010b8603404140501ca05c00c1050b26041134008008100b410f400c1240b1800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 138271996 1250 138270746 138270749
    0xc010e06010806090d0e01030507030e060708010603140408030a09031b0809040c02030c120901020309220c050f0f0901031e05101505120c040b03010f030b220b06060c0d09 75
    0x2e881558009040b100300460f0145910340c540c5c64100e2820940300066003d003000a24607804c26135030311004400400d08210407402a4001d4441c480e055061800040540314412803003485420450140400241602d040300c0e80b00300c940308009040143ca18040350300031245219010b05c0040381c28400140641000140360707a00040b030741001041603940301661680980e444900705908920205c5065030789200007050b00a80502c10780e07141090791400104103c1c0f200f0307108080724000404203840079041c3c1c8241c10a00c1d4007410042d050503801c0c10741c12102d214500c0c0340e1484040110b00030010342d0081c0c1002c1014501c00c022000448c01c01c481d0000102400c0b25020741c19452110001040300c007913014000b031221a0f941c1c5070302d04034510000194803100540014003c040c03c120002c0d0901d40c0f1005140a00707820b21010051520f941000e40540301c02901c6001905c8400c1000030300d000105040440540c3d005011705081c1e034130840000d4080c0212036400c2d4050045007134401c21103506c07642100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 138273246 1250 138271996 138272009
    0x30206090d0e0d42060603050906010b0918040f030e15090d110301060807090b0405100905070201060306050c0c07080c032d0a06020306010e040e0304060c05030c010e0601 75
    0x18404148014200e0b640002c4100c241d030415283c0b107091010580610303c0f0a2501c04509120a44a80031000c084814030009020740400400043d80d5203858420300800300200854581481107003410190755444040c18410b11030780810009100e070594440d90084414100942284002407425090648003075445160860000e0354801e6000030525210103501c0803612040300e4030b41064501e01c28000508a850340a89001c0071a202c6140c4965007401100080c1603124060143c01346040f004106580703030107003160311a604004c10490012915001d080885002200208a640315000182d0040a09400182c20241801304001030208007000038969030000e0f20441c0e000b20b42d500c00c00c0e80c4407480ca11183c0d505401a040441c6041c114000d502440c5860300403034040408405581c614282c40c61000315001500442000340540e0044d0010310410f40c19035042c01a10640303010540c4134807480c0035000510445d18525002d001040050b1411001003030000c02c51161508450b6548500902c03640713 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 138274496 1250 138273246 138273253
    0xc03020c03150f0f040b0a0e0f0618070e06010e060702010e190f0b16141e0105041a090705090a0603020604080c030f0a050a02040c0c0f0624060e040b010c080703020609 74
    0x44d0103141c12006541c440e0340c1206030035056450351410341d4040c00f1000071003a4103108602080240a1050001500440b0b1800402c41e00403ea01005801c007840d035030140e60354a130440200091079070418000c194901044400c560f81c0e051500c0142c8562880d0821150400c5201e90140261100c070807000d01a0350b00c80e171012091560b507501c1c0b011244074038000c00c103010100418049c00a051410058482103a03130302640d00c5400c012450442100d48100403032856912101480184020900c0c64003070007100c070151302c1d41490f1041d041a0307280c082d8030860b0f0150342034400148403d40c190b03000d440596030080ca05540c959840d180070340c0d1506214025840780c081c41c1000201da9100186000c40b00d40d02c0b2010b040c41c00107070b0b02000010100b0700700401c00d101d00c10501c1c0c0c00088242c6c051034922803042e14002401c200250080030700600071080040a000300c01428041c580c0c11242c18141e030002120041240c00358240102e80714002e00344010100f140124494042540200d001031044000d1400c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 138275746 1250 138274496 138274501
    0x3080c010518030403020d02060c031224100e0d111215010f030b0103080903010b0d03050711100507080d02070c060c110114042309151302190c03020c03150f 69
    0x940704e21952100941c00403208504000500b09540a025441110019a4148100d008034200120005c81d25000c19641c84440307401c41c0300b140e090400000d0ae0a0798903410501400001030260300303011103004c1c131070380b001440c1034100a840080091804005030115504400316a0301650320340c400c1c030086850204031400070440d1079130a424001260780046a1a80991031500d9081d02d0342c0c130a403c110307015500c42c400703c0d41d19151582a010b0385442541d03801d07622106810900002603001c0d03995441206422603c0200b1a8011300792203c50740c100c131029950389491100c0000034842d00390000c0c446070b1041000a46140c100605440490040d40903a000c00c410b400110b640304843c8100700801841480103000c2c010320508420303200c0300742040101c02c10040c06e000030100c41d0210703940c07a0388542000031451142130600456203c200c0303045095080540100d10200000716111011f0108030b60140f02509040c8204100c55070003030080c1c29070b1514030650015440c500c0c000c903140403d09103030b80c02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 138276996 1250 138275746 138275791
    0x1e0515032e03020310052a0f040b0d0b120c300d08090102130b0702010c0b010306020a170603060f040c0905040501050604111810030608010204080606010305071d0f0a03080c0105 78
    0x60b00c4c896010368041f0000711a00c1c41000350303c0c0c4601d1600c50350000c000e000791340c0740c50604001030016080d00c000d280e03110405ea01103041900c2c4010350082c00b5540c41840343c001c10000140d0792122040c111f42c1c4081c1801e910866141009240e044403010781071508611001c1d41c00850101842c2c0103d40d650480744d0794090300c5500b40d200d0003c2e5001c49a000140030460000c4c41805404070b0751051500741400ca2507034603040c0b000202030708190b812650000e1300341c007400d42064101d058000e010b81088442d18244000a45036140203000d60105a010f900241c00c0285082901014041203841007000d4102810624001c0ca01120800d010340d2038405034501d00700c402002e032840da00c14501070031400a814010b2111541c0459201000d16445940c04920301070280081c0c805000c2401c000c02c1c840ca130180c00181955400f4000b441440100d80c0c044c0b449000000f0000848001950b072008030541100106045401035800074040703000101b4580c040880640000b4020540c50300000c002c4640c190 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 138278246 1250 138276996 138277001
    0xe0403030c020d050901031e230106021b0d02030a0b0c0c06010e04201507050a020310090b010e041506030f030e01090b090112021308071e0515032e03020310 69
    0x211580702103032045c4441c0300958400d400c180201b203004c41000c02400c03450544481560b0180d0042c59820382c000c0350280015020b490043d0060610b840242000c0c224034142c10800c1c8a40315603035001c1c0b0009400c10f0103644080007800302079580014402010700e80340990080030313040a01086c015004040c0002500085501d07114081ca400021084808210b402c076040107118051400d41c01c0a4001c401220041511000e400f42030b004a02170514441544101401d01c042d803682e50300c80c03501d04030039000410850208907042d280c08900340300c0c044c0c603070f8101002005c400c400c0607541141040000301c10030040f0307064816240d2003912040c0b00c1405404c0151070240660113031103107000d02484817881662150241e0085010050001032901023540d090380c114103403036004044d0503070021604000030407080d0300c4541c0c40c600d50340030a6826030500e00050101010701c203140c2da07000800b00128200507282d03110320071000d0b400a4000304100d6610740d411050640c0f840160300c28019003000b10310340c11290 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 138279496 1250 138278246 138278263
    0x1d0f07020a08030f09010902090c31033c050606100e220c09050307080c100c0201030b040501090f0b0906150a05040b040909060b040b0a0303140c070e0403030c02 71
    0x150440e6140020310b140700b0130080a0064943d280c100b160b000d81ca9440b4614001e13503031682000e036204589261100c0d242183e800c00c014101d02940400c0d8425807400c5400180c90f40700c40c680c0c4803075090803040e07440e0252640e40b040d01c01d00b2501c1441c0078543c1081d1801d203081d100304141c0b401681c078181003208240b90076104c200842c0103c640c22009240c10402030340070b0460003400311000303900d04144000b280d02e0900104049104848240003900d81080b1141c02040b0b450028042084c0d0301021401e4020090700030401e2003100d400c030b002168061f030403c540c021405882041135613998001d5501801c24081e59080306841c004d80702009081c068061072140c50083d06111480209a030350744501e80c89a4060323010001d0030704c004101412081e0091004150009001c2160300403420034030100c038050f0301c00030711640c50a580b040c9591240070515048a4150504845a004100782da420314456950046424014903101090544a021200e0302a500079030f010080e516800005030b0350381081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 138280746 1250 138279496 138279503
    0x80d051f092d0e0109050601050307050a060f03050a0209030d081017190317041209090204031e020109051c11060306090a1a040507020a02030d08060105160c1d0f07020a 74
    0x25035400c0394607202d1401d841d0900041c0e180d40001d8520500361040c0c04c48403001c1049a00340c21102c01001607250420040024100c22500c000f4807a1038050041c1c0040121081c4406050312440000da84e1461030b41902c00344140901034400d524039081d0010040b070012204071051014440d004503c0320b20047e4103029500c80e4100415484410511b0550506020790b821020040d1007803040040302c482c40e42a502032842001c40e04001009440c001d0104e11107a0071003660a0f10602041001c60700e9000306030380d00c400d58240508448042d000495031071030903421442e000181e54030800740358804d9100000301d141c043d00c1d9011542e01d130081002031038482510550790024100010818402c1194030148901c01180040c03400750001030045802c0e1941214150007503040515040d00798202403000380c0c0b401c192454000c070302e46801e20001c1c1c001c0c0030b4800358440713003000983c55404000a0f00201c0c00a0302c11488442c44004004507000b008000442c1c01c0483d00c050b09003c08c400d0380c00041c0c1990701c07560 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 138281996 1250 138280746 138280781
    0xd110703080705010f18140a0206040e07020705030601061106061009031509050706050301030b06030a0209150607080408010207120201060e0a020304051f05090c090103080a030207080d051f09 84
    0x40c507150340140e0740003010240e600c0e560740c080d11310010800d8401c01c040c6c0d110401241c4d516411307a0074a110103400003040101580c11140303041c0b0040c3d17105411101602c1c483c14080c5019218424103c2c41c0008035080f02e500f611800002040d2590481c0010100f070002030203c401e160b5401c005c1c40345010030141460085a640300003880003c444400ca03c500b0240c0c20310026004809132540307445d00c20f03140c2c0001d001c110000014401c0c0f000003c1c0c034951000d02903000304151a03195000c51008400200440400300010740c4100c0940da03010700300c545035034025086130b40b40c2d5101c14989000303500c00e00d402c07200b10f805034091088543c018050041102c18014190042e0b50314040000c0103035000400407580d0f8043d14942c003c3c800c2c2c100d0071100300c02180c140005214034110100394908844a0101881380301c10000401c000b901c1902101c1c500c02d518a009030711070740540b41000b0240a5448290b8002d41007800700b150101088200074041260002d0b55074009035160700700ca08460a60545440290 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 138283246 1250 138281996 138281999
    0x1b120307050307231206040902090f0a0209030307110118080c01140d02130314120d11070209130302070614160521130905090d0e03010603020a030609050d1107 70
    0x1030003070000e1940040300d820a050034410400092031060b810b11415044808082480c1c500003000d01c250561100040c0c0e020080248560005012004018001d000c40a120740014441a1064050350760a91014046985490246c981005101180c0c032410b800620348900440c40d200000303845108840d160005400907100032401161000c081c818800b4080d48100407001d03403480c2a20040000e20561028240098214a0700031000f5405500000e5160701400c0d20b00042d0035080b048030105850490300040c4c23035514024004050040c1c24002c0c1d403080c070100c03c00c0309050341040c0942606101340d0907680a00c0d00da000035144003120610100300c0020a002c48800c0001e41c00707104a0b050301410490703400c1400041e807000c06850381210010301c1200410481014030007030139100301400c2944801d0000d49814941d01e996002d5a40390602000040c450814064400303603c00809141c002d003c9101403a22802d00728060400c4a10449480c40303800520318145220300444030440390340201408200707 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 138284496 1250 138283246 138283261
    0x8090f030c0a06080c16030509090105040c091412030c030a0809070609120302011506030b04110a021f0e0303010311010809070f060c0c050604080c0102060705120a1e050403051b1203 80
    0x144c0010304808013a0760800805682000d850189682d482c420307a00d0f10b58415001c070030302141600684c081806182400d80e03c1500e16004120181500c9114000c18070415525001440c1c05604410700c03e403074000000c040400d408040014011001d072910b801210391150114a541d45805208500001c0e6560b5024411001e58003c1d60004900901c00840c2042c103042c0e5140e40d400c1d85900c080b0100e60340e15200c0045042c6802a07030200c1142943c010f0030004003d01c00f82d00c0b0124102c1301003c08080180910001080740d00c140000e4040c0d100305c94072983c41b46850102d03a01200300d420b011400b11000248010b100144c0301050f9000c03210340e0b440252070100c0560b24510207a10840b020b0100b1500426591548805003000304104001130220034080f0001a0800001030079075000c100c0f04010030f0302140c80c0e0200c440e400c03900c0c0090005894645a90b640c80041846810004003400d10040c0824154050060048460301943da102408101024183c0c1c60099201c070b100015014000a4106c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 138285746 1250 138284496 138284507
    0x106052803120507141c030905060c0a05120406150b0903070e060609030114010512070602070b07030c06051305010605060a080f0402040e0f0d02210d05150d08090f030c0a06 76
    0x40e0980b80c14000d007421401c2d92415007003060b0850a8206a012008030400200c5180c1880a50942401c1c00c110b84d80c110b440385602c441005082c110300c18000507241070340364864800c65441291420200c8135074145403402c00040e0410018429440003600f201003000e40e00302c0d0464030324400003401052000c0c40d1078110315003940300400c01c550005041c45400d0740c1e91028000c214000348101c120390740c40c0d0b05107020403a01c0700c00701c070960700240c0c0020005e110007900010718801391101080c1c0c1581f60001c600e000c807002d50240380010910350402050180c584604015002101c1c440d400a00c49240c403501408090f0142410020004a200000c5410141c0107840c0075005030024002150b45000f150500d45800700c0c032111100d166210400491402d5030501ca6440e203050042c6c0700e14100804004141c0c4e460080d002d07207015855844002c40d107261030007039080701b80a4024203607203641c1d000c40c00e009540d5080a14258000d002c400981d0040c0c5c42d000c55039668080c03009240c042201d0030724404654 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 138286996 1250 138285746 138285773
    0x10080402041505040204030501060915051c0f0c0b0a090504050c0a05030a0608060c131d0403031d06070309050c04050f040b070e040513030e030f030a1202040f06020106052803 77
    0x10784403200101183c0740e1503a0004002640c0200c00100d1030f0ba240440c1c1d01d0446044009803c00c8100f003200c280090b07618030440d01034800651040c0d01c40580a4149444205550300c402003107403684040006a02d80d4480207000714080f65201c0c108125a40c0f410702080d64802c0f00e019500e80c0c010042410700038050809550407800303680c1e0000e00d940c3ca40480e1031a009003652130403607000700462401c0740d501c0c03900107013400342c0000500026104011442c1e600c500310040c1008040c035850310300c000340c000352004ca1081d801f8000b03011508581030480000d00180ba6080e03099520b4051805801d025081c40c4c081c0c0c5009640d00121500240d842d03440d007400c0d03c24080c00b49410012100d16010b030310303552030003500d00480e0146c400c80388000c894078026201802c440049030080e04001410b05c03400d4408030544040240300d042c5045a1011581800002d200d160045c0006201d00d020103d06141d05600030403c3d00c00c1a60700e441048000c1d05003034a40c255a4842201001c1d4501040c400520500300044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 138288246 1250 138286996 138287021
    0x9060219030207080d051b01020703050702040f0b102c0916090803030f0609010602061504020a0903020901090905060105120705010c020d0f05010f0c03020708072909010b0f1008040204 81
    0x315041d03220300d1045e041281c4102c8400014002068000084054018002d0140403000c021880c0c0700b841c0d13401803ca4007500718041d00c1540d03a621001803440c03090b006254512001080040c8c20300321036002030724120304030b0f02c04841141d1000c2c4c070040103000708841d0821a04001c24419850741c2d080744200090500f40301c580204002844002003640c8200041c50043c404821900704500d4400e0602078143d10517031048045505c00304c148501c0c0e01e01c007010000803200680f40035070f4503060000d056901e00750b5a80b0094200481c2c1380000341c261601d40c083e0801e05c2c45507080d601c107030b42d9036000c0047c031203d40341406000e44c22440c0308005d070750b02801004803114406841117040540948031070014406c005420340300e994403012449908240d9119104201e800f6042c11401c2100a0711529450b0041440060182c0c144144010540c2d2220104140040004d207c2e107007249400c500305400791015200302c41c0200c0c00c04000d00031500c2c1010f1041c110659556407070351075075519001c200141019001e20b5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 138289496 1250 138288246 138288253
    0x1050a0e0c0906060f0a050414091608100f03060504020a080c03100e0c06030c09030607050421050f03160b0c03061806040e01020409060509010b1204030503090c1003050f0601090602190302 83
    0x2102540c04c0170702916070381007a0384900303888610340400586a0800100040d1180080300c04001074241c90400ca60300405c00ca2410381c01940c0c850021940509950b00612030b02c0503400400410401d568010f0b40c4158030075207960060741d0380ca06c1255600c14610000d154141c0102c000c05e1910495076200c00118003c407000c680600a92101046243e8001c2d10403d8a80100141c542c1d80c50504010a54016541e85080c52800b4070341188080b045400c0d04120621060a030092001c0c003004100c0e407480c84410206a070b80c2c888464080510801d0781020032220562001c00044241810b681964403d44001c0d040003a2243d0300100b02001e408002c0ca070341d62280e61108052541d0101344090000341254050000b02c0e10700300410840c0c0360030140e014038042401003046081403e074111150b0303003041d0f050410603205e0712000320090038442d0840c9000d401009080301a20f050f41d140d00814025200c002d4500c105807224001100c80b15242c0c05007002603401030000c41c0c4c1c64500024000406ca0207413040c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 138290746 1250 138289496 138289507
    0x312030f050103030c03180608010b070606050a06090f090608030306010507051c0f0e0a150e061605060703110703020c010e0d1407090c050a021c120e07030501050a0e0c090606 77
    0x10300440300283c001360700254103a42008201600f04050940321542840142d84041c0340401c01804500c050048641e18a00420b8002c20014140c000b2400b41000404d44440207031180d030010061401c80c8985410b0030440080010313011150700c00e903000d42d417014029600e50380da050015540355010000440d101e03c201420103101c0c07000c208100c452200b079507aa40e0510300214500806915400703c2061240349500780801c13030440613500340440800c0742e0a0121a402076180099043d000e501100d681003140c1d09100420407401107841480fa201e00c0d10104001d800c6010051850b008080d80100541e01c00c07008541d0540c0101f03400000410300134100c01581803030340e5034803409214481e50700c0140d17401044144400d154a01948211940500c0e015041a81d42a07001307640314003070443c40000c8000000e804036414802d240345201d0b90341c5641d050040d07282107100190b440000784404e07540d41d4645408600c5c186042d00036410240e84100003000b555460104012060743c024180d542d12010401c207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 138291996 1250 138290746 138290771
    0x1110403151a0d2015070b1503070801020903010c0f0804020f03240a060b070510020a0c061805060604051512100e0a150c050d0216081c110301050a031203 68
    0x76007801c614440d940181c5241007148014484c02c0d02908428031821800c064030a000e200c02e800e61310396582103019641580c9850031880140c00314030f03407410780500900c040407a03005015001009a098241d0081040c95444041254034040041d4550f00162020b4041009440d007402e1400716098004c2c00c1d0342010428100505060100e81c1c0e4017400401c4150401400300c0d0f051242c4401007030003003411803038034045589081d01e80d40a06140041e080d80865041003c0e40304501d040c0744039a1043c1d0030815038090304e015103684580070341c04850303501c50080045e1860819000d0307540152460643c0300302d25040881000b8614195a4440d4807030b210360000c186100e44540106c1360200001400740103460001d0801c000b401c01c401c1e40203074035241010802c204070303540300e01101c900c02801c0d400140c849a0400c0c038840100451100600485070109061b01000ca000c661001901c0d071640c81000100400426940c903400244a040e40c80650144208040385000f40c0000045109142c0003c52f50315404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 138293246 1250 138291996 138292009
    0x3060b01090510201203060910031e0b0a271703040b07140901090311030316030801150201090507030611120109050105011412010b0901051e090301110403151a 70
    0x2d2140d00000c044540000c99080e0350383c0340c581e11503481381c040e1030360780304140801581d40701c0540094081c11101c4002000d00d001111104c0c095640000903800c9440d04601801544648880070740c0c01258080100d40010014842c0001c0007584582003610544080e42e02c6000ea5550ba1050b100140a441441d056800080c011031156104d0a1250344c98109003d004100b80310900c0c0030701c2c00250801a00c94160b0300507a010003140ea00c462401108490f560101e400e50290220020241c0503a8044508154106003554113071807449414100110070717450300302c5c00c0c0ea03d00701c0054016023141e0400c0c0003140b0650410404101c2e100305181c0b400000300940410144244c4c88500190358486c0184115a40180c00d800c1030920581d03224244034008c500481c00300700c10300c51001110800940c2650030390269064400d120000072a8041e403070041704000c146644a1540ba40c429446d02da4500c0c1314641000070b9034152030700b0900941118030103070385000040c0354202e040038030003413040c0c0300e80c00aa0701da0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 138294496 1250 138293246 138293269
    0x30c13150f0812070c0b03060a03060c020a0605060109120b060d0213020c160e24060703090302031203040305120a0f060801141501020c0d02060903010c02031201150903060b010905 79
    0x14844030780424a00440d450a152620704181182d140420013079010071007040b000402e507141e0a400c2c80d600e840b001c00203204090f9030360008102e2410400041a025004107100940c1c5000362010310013a50b44d800111041001e41c007031902030705107440102012809a6104070b60242001c1c003050102551900041c00080d1181d17441c04103503800251049008400b0701c00e4013000030301d0a0350840158240b03664032158820040c21110794400c1910810322403100241e000f60110009000d240c2d40d45000d0a004140b03120301e0005a01901c6142e0319880d184620340e08892256401d50f075a035090503000384050390092005031105400741d442c1c2a0204d800245441400001d1a114000040a6000003000001480000c020100c0100c513141e40342226600452010340703044d400c860140308036105100040072405807101260b019841e01e1418480240c000006080800d000301001820f07a03030382d0701c4408400c403d403a000f40001d18804400c0001800580124043d1074050401c804280d40f104089501340060 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 138295746 1250 138294496 138294509
    0xd0b0603090703031b020d030305100b0c010903030b0d050309010813020a090f0b0102011b0509130203070509030f0706020703140a050609010605100c08030103020904140703150501060c02030c1315 86
    0x101c40c03c000b0190032400a03040b02c065011100007910003500094600e4598040140501d41c4850005201910700c000900c0507000040440781c0310050103c0007402000141812070200b8600400c2040c54601883c060dc48554000003c516006a07800110741d04030010304a402d58040000481c4016031b28194410080e00603844006443d1007030654180c183c42c8240301c098150b92512680c96409054044000032076007250414640c0d07105e01e03c01040001c1040c1019aa45502c04001d010303039a54024003c100d2140b048049075201d06945914588560091141c01c0c00b5900030341c420800030301d0722055101c0d0590b1060542d40c05002e00c0d1144c606100040b501c003141c50b5510403003071003989000d1100483c4280c491400b007081040079900d1400c640300601000e0310503c001e400040c01c0200c07428080017505241000d4a280d43c1d503a00d000894001044c900c800410b04043c00401c00a21907400701a91540040042c5090f030804424080080300040c0c40c1910103489180240f445542201c00310b004220 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 138296996 1250 138295746 138295753
    0xa05210114160c020109030b0601050403140a020f221d0a030201060e0c0a17040602130303030b0a0b0307230d060f0302090a0c020a060e070515090f0609010f050d0b060309 75
    0x9003801000b0340c2005080209042c00b91011007280980d80c048941820740e40e02035440d21481e10340c00c00580d020700440e03200411a00207007411160a20b070100d030f107025451007030b10140c100f075000d07070308011003602c0b030683d80071201c0407030034070001c0001d40c1e85c01851a0382075042008104072038002c216400c04e4020030b01640580c2d1540002c03c940440c1d4405240d0003a00505400d0625924110080c540b1480f800044007494035a0003180500c20140d040321491454030381c2d003480c0c2542d070346005409821607001c510322070003048800141d9004608100e0b0b200b5556a42c031103115588100c0300c40c0d210405010720b402400018050443c138001c1d54401d04020301200b0303c0383c885061444c4100000404010f110b418021b0420320700c1441980c0001c4c6184229070b10000116208100c100010320b003030050344c80a130b840758003801121900341c400c0c1c00078800068141e0300e100e17802d45d0318403d100c00340c800c00c0c44441c00110101c6010704410320500c0a041810382c881d001241207403e01d0000365054006071081c000380e42 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 138298246 1250 138296996 138297001
    0x30306030206031e010e0c090111250e070f0e09070903020a120b1006020c090a090c0e04050d0905010e04110d020a1106010e04050307080309030d09061b030b0a05210114 74
    0x107130f01c1074550040100c5072000c0c6152500c540908218040d0b140514140500c080295400c500e062141030301131074080100b50f009500c40b042c0200240003030f01c202040c40c442000070548c1a0b22460000d0f1030142e4644030b03c0482012030b018000c1c01c580c02071259042119050f80400140e840d61071010040001031100c107601d807158280b4180101c0041d00038403450b51000750400c40c503900851840304291040ba0100c58654030030410402038894820010205e41c0780342401305000c00140209406140038070107c50444400440548516880d030003031a000c1810b003031191003107290542090382d0360385c1122640c0c0c0c104148021400166049408482c000c9060207040e54850041001807600401c0c0790558000d841c01c2c5034642da0307224451044050b12000d80000000d500c02010001c6550150080328104815505030038060000d100c02003018220040d8040b0403413502d842402020741704407005000c405864070f400c080011030581c07020101151014030051114591080c400c0160b1950002091060f03071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 138299496 1250 138298246 138298291
    0x6012c03010f201207050703110105070f080618010b0f090a030804031b120b040c0302100f030c090506090d020d020607060504170a0507030f020f030705150108061b030403030603020603 81
    0xe811201c1510060000b40413000c401880000480e40080041c102a039031281d59060446258404c0c83c4012510340c202000d0050711613000020410ba1b040903501c1412a4541c401041581008a00401d41e005899001030041104500c024900810b4003404c642c58019900e000c2880f101c030b158010396901c900401c0070000d0096050358007a282c4a0000c200034907604281d19500c81e074131484406410204d920002908005a000244024cd600108818041c4180300f50041000009000400c00a428200c5007003c2c140151510710540c1c00040c9414208a59642445100107e007807007641d010302d1030110080543c83e0b4030003c0c06514090840860b0b149000e0401c840a08081007210f9000a400c100b0410b04030340c00019034140c1981450f240401001d842d4080745490054020450301303007c0040d0705820080002008854003081a513201c002d43e03600c00a498a079041150a00340e50819040340f0b0b101401400021648035100342000500d480e00c0b40c01003642d503003045440c2c02c2850820185403254 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 138300746 1250 138299496 138299531
    0x80a05031b01020403080706090c0504020f0a0f0f1d03101b020712080327030a05090111060c0301060f0207080d110c030d0e0402070602070b0f1b0306012c03010f 71
    0x40000101c0254501032450740e4a0840d40b01d03841c00601001d540310205001c200394140c45900600b00100195112410100c682100381c0c007043e0342002240700310061202042c000c009010303500009032110794034160385188800c8011002d284495050090405444c400503142c452520f50f00205802e480686516010180c60030220f40c0015041d5588010f0060005061000300c03584040b5804404111000890071109020f121034941c1900340008180c4082150b4400d02802200c40d0990340d20240c08840d14000e601d410f4141c030f00c0302c0540070070001032080c940038078500342400c1941d1048410f656031b41c09009060090f00c1c00c0100019400c0001582c0c1d00504100d01b0b41001800c4010f00120b800410b00603001020100080340100c1d0003140b401c041c084242d054811080c1c001001c0b9115150001f18809018800c484000c0320900c10180700e101900210241c92003000180c444d0300e990340b0300c3c5086c00250000441044103488811903100c2c441e807028040d4125001c60582c020590703002c4803542406 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 138301996 1250 138300746 138300787
    0x603020a0e040b070c23030d060f0b0405040c05040801060e07080f060307170106030b010b030405070b1e090d020607060e01060b09010203040e07020109080c03040503060106140304110307080a0503 86
    0x2481c190600038400820001491950011190f003000c0400b243d144c98009134020b0008501c000300d8080407005512114080300414040b24002401c004982c2c54540202034001f841c041d6136600c1c0720a010a00850400754840c90a0590700d04145081691b0341074002d00359500c5403c100407402d48101400651078021050702e4100e00f40b0054040145480004039582e0000c511a0801048084040038144042035012a01850304148002e05070340e100c0400d180c1a52058504503800d00c04c3c3c2100107644030000c01070340c0050b01c010940f980340d410421030346600d9401040000754000141d04c0c40800607a10100201002403103a05c011501c80e0134050700c02e0031545140d106030040181041006826039000c03084405a450021a000d8aa212034000305d00400040c030f8010100310000500010188001015000316803040301221103a07a00c0b41001c5076681c4400d542c100810100340041000686c4a16400003001c40c00b0b01110f000995400e096441d02d4a048400e0740c040d00f0000c0d1070051980301c14038484 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 138303246 1250 138301996 138302009
    0x1203030b032a0906040e150103020f01091a030a1b021b030105060a030201030906151d06060403030e2e0507030e240d020f040b0306090601030b060315031c030603020a 73
    0x40d400c070102c885200102c000345041403088201d80001041a0ba480d40041055040d200441c1c0040c0c2d482e4440c0c0c00000420300060344509104694038035150711406400f402d403007851070100e43e03e606c1c10000007642c0d00060720001410781c540984800d0b0a0049250810101450f8001c0460342c01d81d003241e413034520035060490f000c0e0741000100b100030740307034130b40400e013140e90a10380011078001070300f0210010800300701265002555840006a0894000724007100e9505c0b0786015143c584031641003112910552200401240ac480f0030030301c6c0d0b49000c5d2172034200c802d42c07000d00c00a28503103010080c00d443e04041c00741000c5800130500c0000c0c158819402d410300740007550380c0b600000001701165a0808c0503120f40351008000a40c042c50140c050f010b0740c0c800c294082c00541c40d6500c807050860680c001b12401402070b0f211100058143d8440c0c000c54000c8180501100d20350b841e0709a200d4410580ca41000303405102d41c00054281c05112079800446c18445d41d00000c2c42400c510420408412946c00b20 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 138304496 1250 138303246 138303283
    0x4050402100c03050919051002060105300106091a030304050d110102120309013306030f0207080c01020705150c03130317040b010f0801020c030d020703091203030b03 73
    0x401600c1c0c01c0844691914070b418542811506032901300c8079031007040d0b107071500107660031400b00c2664400d049820641340c0c200c44111581201805c201c4c2e58080c24850b042d40101915095640d00d0380b40c0c4001b4021a44032a51205138140c0100e030385003560020303408901826a00d021114850720002a00e03039030740404401030352415241c0f600241c415070807560082c01f00d00d500070b210500c1d03a00802c410300c640c00c1d4848445460b490280d070528005d0050b21803001102207010310560460944507095a16415164603d12000341820720440040c000202407200c41a42001400003150344400a002c1301c603000000544c0c0e81001d4038016040440740c80810520035504001d200110000c001600d601c819103100c2040f001c1d042c2c2c1002c46074028501c2ca4101604408400d00c020b001c0d403511640e061700d601e00c45c1d484003a95280d8029080784659601c01007603803c00c3c460010b48400b541c0080c04204d0007840e0210440b43c548941070300c0c05842c90004c0b40400d50366400c04500c0d080502032000075020780d6480303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 138305746 1250 138304496 138304501
    0x816020c060904051e070e0f090108150a0204090f09110613030b0a1d0c0414010503070303050c0c060c100c0c08040b0a031b09030c0b030403050417030d140f060405 72
    0x2060341406002d040c0c501c02c54440d00000ca40c0d8004400d80504101d4010000c0e1550412030009803500942000907406000e490081000b1410328112040c100e03018100107001203603603404001d80400f4080c0c40b030b1554580810001441ca1080d014007058a100500001072000942ca40034160304484038a040c0181d41c02c1c40544098106482c1800840740c10541d0310425584202044000f03041700c0a00040c40d201008500c00050b400288140440c042610200078010b45440fa84515007002d104256165108103818000a48100003510b05082200c0840b400b07200b120380016040c7d001410803006660141100d502070352181d00602400038841c3c103004922414540350f21680c0e1055024001000400080c40d040403482a4013071035100a00302c09074050509a04402413204000384000d40c0e03102c01307031000403d08040c007200b00d0740102c4c0e141c0c40b41d505d403521f4154901e00304601042000d9450106000c0c4500d0400540581c0d0346102042c001c0c0c84440c5049400d41c80c046002409036401549007108 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 138306996 1250 138305746 138305749
    0x70617060904030c05010603020603040c0513050402130b010e06030c1207081603020a020313030606050102150618070c06020f031006110a061e06080106080d050a090605091503070816020c 82
    0x70540d070001d8051804540c0843d07541005400740150f0b40c00203420450000801c401c0c0300550914606548013243e00c1c1109245c1d00d011442944c1d010780d00079602010207504940740b401164800c5030051810306184060050100001c1d0343c6070021600380709603181c00500d054580401c00ca801d644080ca0381000f04581c141243c0c0103041010044a034014580c1c00184240c510f4020025603a61008141c030903060945c50f4644000500001d104a90241c414240703010b03c500e880c030600d94810000a81072a07510404040072481409024041e00305004500160401103941c41c00100703404200020901d6503811718603c4c50b000a107041d40608208158005002480403000c640f42c88010b80140c008294050000700052070079001d0702c014580c552a000002800400640082d822944180140e0384d500c8070481081d60284a80c2198034001607044200384900d0340503c0c09003822341c0001d4205011000b0104a95907168000c5c5e0704400410301e500100507221070780000d080b055030080d10242c07006580110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 138308246 1250 138306996 138307009
    0x4080a03061d07052104030f090b09090a09020f0d050303040c060503160e04060b0a0c0b0c040503101e020315030c030304150813020901120303050108060705030a090507080d0207061706 81
    0xa140101300030300055420100616143c0580c1d28840e585500555420607190141c1010507c00d12140420b1403160001070710a2540161100700c04003400000183c0e5940392107000409292800f2a40300c1001d0000d001c680e11008070b00007e40e40324800843da2820b1a003085c200300c80040d0300220402c001001040052460030b02002a202082e0502c19100b1070b001c000140640703000c1c0c100203400a27000c10041d00c0a81d1001660460b0f07070107100e4400082e207030185480000d1099014440d0158001102810682c031140e102282040c0c06c2c105c207840614601600100fa41d00565040342413510749018054586010720181001c110218000c51400d46070034680304c01c2d13024000c19041030ac900d21002a100c00702e0f054030500720135030042000780d982da10340601d1030100c2074400050740020710b0703c0004030301204000341c0c41380140d40584844d401c0d03940d040c0c1c010001c0c20285904540502a0f8800059448000c11003c1080407031034024100c854249880141a08101c800e043c0840148100384a401e03203444 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 138309352 1106 138308246 138308251
    0xc0618031203100e160e01080703020d0612030e040e0705010c030e06030702030c0d09060206010302090604090b04081b0c1e190e101502070e060f0904080a03061d 71
    0x6844000ca20b0060f4501d420200311088546d1030150302980d01c480d03001c500b0345000740c0390281141c0d620081e42c41c1503010840c0c81d00a17004d0b0300105900031381c1c0d0501910017550100300c41d00010107001c0c1d44040900c103182c1030000701c076444000c0c180320703060144040c3d0340603103102d40c0c2e13003400d0030b00958170361003410689903500580144113589481021610102e0b409940140580d9080d5004c01103424400b401c1a0350187c2c0d900c00220008905010341446280103608a03602e03031040900a4212400001c2002c0050300541140d4010756600d503500040640385040b040031404104011401c40b800e403004d103580a810704100042c0100c150f644046c03081c6066014060f030103503100891066030400350000405a000400203010191094044552001c00140458400d003407a5011031300000e41524261821580001d4600c030041c1c25004250046c110011000207034503140b2811006020003 = true := by decide +kernel

theorem cover : BRFrame.Cov 138129496 138309352 := by
  have h0 := BRFrame.cov_init 138129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 138129496 ≤ n) (h2 : n < 138309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
