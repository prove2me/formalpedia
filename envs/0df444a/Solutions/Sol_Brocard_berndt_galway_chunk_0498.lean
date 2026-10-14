-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0498
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:06:55.726359+00:00
-- url     : https://prove2.me/submissions/512d1edc-8ffa-47d4-a2c5-48bb740f5b74

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 89388490 ≤ n < 89568346 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 89389740 1250 89388490 89388571
    0x61202010509130c02011b020307030e060f16060e15040b0109051b270607080715090b0403080615121504200d050105010309081e07060204060c02031203 67
    0x2ca943c1025061003600c06060940d000020687caa4881c0c003810541841040400c551040000e000081d0340300664201c42e11303050f9695900c88600c5640d1210a0045001070405650961001c00034460150850b640c1c400302103081d50321340744608a5211550b141120060300d040c1c0076500411035112140d1249510403c14070440c0c00d0000b20340075211555202117100885001030289030103410000310301014a002c000c450a514062480c0e94103c49805a0100900908001891110122441d8000c5500c01e0381c440f91280041c6400d280240c00b4810682d003a6004250300501220441983c900315450441d0b207a03c07044040d913882003100383c3c1c3d0300400e2003a5042a1510000010092002448629032544e03416864030b032030300c0c0c5241a00b200d105a0080b8101403c203282c10f00413501c031004031000c919200311420401705c42c5c044039012a200c0c880004080c0b500c00203000031140d5014503d1118a4421026036444a1916015882c41d001c01d0f02d8941c0c100d05c04007003c00f00029100202000d403140c010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 89390990 1250 89389740 89389759
    0xc030c12070e03010c030b0d08070212010603260906090d031106010b180f0d0b0c07020d060603021c0305030a0903020a02040908090a06030c09050904030c060e010c0e04061202010509 80
    0x14000111105480707000c0450030400308620245420700a025180c1098542007150715800340008100d0812010042c0003803100103555415900d40e850044036510110009020b641e0303503403510068003820180c03a0740701c2000f804103844e00010f1040445080384d030000d0109090a80d5181008601e96048008609010400503100c6d50a0014403856000b0302c90101525102d607078110254a00c94145400e25100e529000c15144603a40c03805042d0348525044600b00f002640d41e0050402540f051000195100c0c015105079002c109484d040001640d01c00e44080500d540304d000c107020011030303030080200821010300025500703c0e6964460204980248100c40c1040280c0e00030804072400d07420f0a99140c40c0014400885040620b0b400000300b4841c41c0410041d00140c4c0c00800340001405200c0c8260403501c082424148211900c0b402c964004504000042400d10320600906c04500740c00040740700d00c1806800761038603129a50803244000d06a40d507241a640c0115a0741c1d201c045110350108100703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 89392240 1250 89390990 89391007
    0x50f13060608090c010c080406050a1101060b1306020d1e030b0411070c0b030106020607031812020604110d020904300c0c0b07051906020d0e03090a0803030f0c030c 72
    0x20300454000384015161141103040403840a4140200c03102680d044c0102240e0301c1c400510f2100c115411176001e0306c1c2c910344074450b1000407150702d001d0324455100c40d0f0074580d01060000f4410018503420b40c9003100b201a180e5a204143d0700c1e40c148949031404034030a00d510303e220f0440e506500c00852840d18002810442c054001011581c021070076880c401000308030002003003000080d03103000e0224103807801e04540c5071142c000d50340c58000700144105a212b1a10202d00070091654150090380101c2c082210044808001d50700d0341c003107800f544c100035103401c0000241440300251001640162140b0000e47d10768448900160218000300460f0603c2c4951682c003601b0540c2c8411100c10a40e6020385019041c01c1040303400c1882d070810b0940001c1000003400040d0001401501e1050840c2e01c070f40300c01007070f0030410001e004405a08950711708003d28600c502c98044001d2208141c11100582c0c1680c0305c8104541e240400c4409000c9001d0600105145d900840051035002004225191600300344 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 89393490 1250 89392240 89392279
    0xc0503041a09040b04090803040f020301091a070f05090d02270108060106020709050f070c050a08030109021c060e0c03101206020408010e0a1106090d06020412120804020604050f 78
    0x6075180c49807110008201402c50b072401e0b004200000c01c04031800e02c03d0a805032910281c034800948014482100b4100c04021518290019403c9035001202418a010001451a03401204443e980c5c0024100004101618002c006482c80050064030400d50308030154240540340a1203403410540c0700711060400c403034a0010400901a00c800405844903501d0101d01920740b80840d00500c00180c240010080343c0f10401092540c04180d0f440c0c207050088480c1009820505202c2c0f016080050000021480c182c0c15001422400d1341c007005952841d007000350318003c480c2e050003113031017690400c0041524100c41c41b001d19009009142c10f40315283da101d804501c2c014a80800322081500418100f224650a03c030348030000c107080c1e02500301c0b94102c1e45c8032285171808440442c032500000ca0110425119610700e00d01040d40300004654841c1c40c0e49058046030020141100d21462421906400500c0b074003510340919800740040e8201814001008240b5a4500006402070007902c0d034020102103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 89394740 1250 89393490 89393519
    0x82d2a01020a050c070b0306011d011b0b090c060f0f09060f160201120b030703030f12021201031b0608010b0315100c02010e030c06040b03060307030203070312080106140306010c050304 81
    0x50b81d4482907a03c00030803d6517400c101d1a03910280d0414018401c21030540d07000b000c204e002c4c810a68100008415010060b1552103002e2090a400d034501c4040b41d0800c00103a1407a401100d0f4201100daa2158210401c101d03441001100e08054009002c00301000e1005009404400e4004044030300b4118003111400c0c150b00414240b5514100c03000540c4251350308212120034000c0a0101482500c4403003021a541e080d41d84001410000c5800705140c5e01441509440000d00389014159a100e241c00680742010b503083c0400e4035003407842011005000f801000307100032561a511031703200680c038128403103146030030003400601640c3c2052005805542c90600380c0350b80038411340314030000040074000100001e071008466806130381315030546201079499105a6003112040c1701c0e241da8a6a4490100781800c1c1c42c0e500080d058410b00c90040300f044140400394410210765070345c01c05181e980d51001c8401c04c0f10403080c0d4030516410804a07800b5441000c15440c103c0c013800840385400c0d521f1590510154 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 89395990 1250 89394740 89394757
    0x2011803020604110108010305150606160605040213022a070b0c0313060509030a080d0e03190f2d09030c0b0c010b06040806011806080307082d2a0102 66
    0x2c000300108010040418114150340d1001e1928a60030340c103540d100c6a45900064039914042c01c200300141d4075a5800046a0b041c2c0d006190421000300640313082d40240c00140d408038400c1e4494003c4189016151082d01c922505201c0d120581d115040c90001c11080070780e100c0398450040d0000800d039451240014150756850314003d5a5610f60026440210a0300c0d8000070100032041000980ca560b002400f2120706410081c2c072030b0b40c0c6a909105500415443e041030702e131400081244060806251418110f2640f02c0d240d500c4800200c0720f003102c0c01d44403800d14182d4564804114560001c2d81003180b90070070064141101065129103400e1040707581070f8450140c4040009150f442c0394800e01914001076400e84121342410b051450031034440070140124115016520006074118980d1741185000340341070415680e03074401a04051100b58454518510011980501d80340000c4d030300035046494004415803142004104001c01d0007540c86c5042c03800102041c00c010415004c8284010452030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 89397240 1250 89395990 89395993
    0x109020612151f051308120c0d0305100b2a0705030c1509040b030703060908030f01080f060105011b0b0c0c01050c0415050d020c0d200102070f02100201180302 70
    0x2e203050000410740c2058030280c14010802c083d03a1021079038405803501c03554101410701c0c0391100700503031402c1d81d222441e41c1308041c0b91041020400d614691003009240d0240481c054075039050212500360300341d070710a64041c1e81d960725a020801501880e000a00560718001598480f000e03000039a88090081600d01003000303810105040109203010006104200f0f01621441641d1085c1540c0c803101d8054090701e14021600c912540d0b803a503905000d0000a1540b00b031041098401d0b178140074501e0342040326400c040319406400802c100c00c0001304074244510460007804107a080100468034100c08584030140a0741d40f18850001030300b4403032030030f00c9003084400041e161202c41030400d09440c806011121884c0c0100010300c5403102d61101c1c0240c404050805681c0c820401814000910801c0c14050260081c4002e08840c01ea104a00c5038001a00401e0803401540801d840e6081348a81480103000402894810005052000d000414400940000142110040b1016042030001902140103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 89398490 1250 89397240 89397277
    0x24080606010e0303030f040206070b040305091302040e0415021c090605071106070806010915030c02150705040306110903010603030f020d0c150203190f02070c0510080402100201090206 81
    0x15040108695903002409180c45507200e01c0c0704011946911002d081002c003501e998001070b05544685044030762403a80300414845515150400078015003021681500c030b608480c40d01c0e02510a2402500c040d21805000c42215854941d00d08034003100c54941404c2c5d480e020f000544030415612602c1c0c60140b000100411084102d10305074044801c003d002c501401110300bc40340c140000011499803020b06030a00c440241c0340d40c80169030528403680441040c400c03141d808242146d0503000014008101d0b021981450301600d40a0503800c03088070b8800000d04180b0080020488039084002c0d51492481607034600035800380460f003542c0d465041038001c1000d00e111a14940c2e0f04104521b0b04103002d11f400c24960481e640c6404905010450713041e1225000300101c2d0a107141050317080c01c003803110f05003080100c00c5019460080e4000c454296401d90384503000040500305807480c4103244090ba500c00d203190341d4070703801c221f840d10030310000c2d1045650b90369a600050312600300403e0041c1c07840024405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 89399740 1250 89398490 89398499
    0x4090e070906080d141e3910090503030a0b19080c0a090c021e01020c01150501020d09150f09030f0614010602010207030206160e090a021e07050a0609020424 69
    0x42c4100100d81700c40304801c104102014007203108034030780c2000d142c102c001c0c1e90b0f10103000b040300404411b4110560b6940f909244449505082d5102c00c04410542007035400030304120300f10000f110094000039049400070000101e01ca00583e001c000d10160040010070043d06c41e061011244804c1c0e00414801d60000c41403e62a1800e007000750010100207505111520b0318842c0207440d21400c1000242e105500d40c3c403604182c80a4040d1130394401c00c0c40c0200809846403d0380d1640c1c2445102c0e141c09802404100c2d800fa274852076030b400684042640351000386814003400c13074550105510f02c00400c80742c0000800007400240740e443c00d46014107030216860000c8401091000d4040c0d1000085d0b80c81001843d00190300840c00942c03054404216002c400c0c2c41c0001a070720142d05040c11907200742c04038200100606103074050305111400c0381243e0701d810035448403000d5510460030050110b030321000d01440019030329013041e0a454405400407030100f51032240346a0201c1c40d120010b840c20341e2400c0070301 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 89400990 1250 89399740 89399747
    0x120307030b0a0308270301140402120703031409010c0b01062706020c091f0303031d070303050415050409020408010c0f090f0306050c09030d0804060b09040804090e070906080d 77
    0x400c01e012a21a240a03185542e00d40c242e1250403404c220001d142c1940210110b50072803502c81640b005402030001e4850907848184aa000311070480c0309000507022040800000181c00307080d40d0380741c5c440040041500c3d070003c2d000e81100c049241004021041c07840042c3d4524007403070007402161075032490325081030441c134100600110341d5040002d9a401c10400c044d40003402290320030381510600d4242d140d89040440710315030151840c4000f0b1400c03000008040e455804402e1607a03c0405d9140c6102444070038a44403c107501c03010700028400c0c4000e01003051108040c2c0160401e80c00d189285c20391300c040c94030030b03030304181e103c880c0c1655141c100040300340d0020701c041d8024a0625211813418105070404807000c0c1d81e4040500300f01c0e0355100142c580341e002012240340c8400142161020500d105004110313010440c0d0494416007040e114141d02d003011780c1c44a000c0c0340d01c501900d0400c1d0a1501d00710062852592641543c481c0345000113203001503202e9440945900750182060001840016 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 89402240 1250 89400990 89401001
    0x9060408071d040804050904060b0319030e04150501050f0c0105012c06010f0c030201090f0c1d16081e0106030614010804080d05040201050d060e040b010501050a0f080903070512030703 81
    0xb4452441c00d0410403000a0303d030b104a8003a00e404032048132198503103062900050880c520311581500c62020790390140e01c0c5400819860b01d03c00c0c3c0d6485d081e241c07070205000c151a20680d10b0404c40d1082c2c2002d00080d8000d50141000503c501001400e02d01d24118440c2903400c282e000e04442c80440e08000b50a1541c02c03d996003c0c0204008241c203401d21400080510a071403260108003e0390070f50450405100390080360302681c006d0003a01d0f620031a8213007841186564805e5216040042c05140603080a9521080c41581040507060460b20782032401d85901d1002411156444d004841c1800c1d20b1010b0300f140743c0070340101d580c005216410a000c4140382e12902e04014107101c02e01c400c0000245848080b6401d240c0c1d1044003244540300e03880107903190b00130178917044400d41c01d110b13000c1405035410301d00510480c0224405600b590342c0f5001951140300c2e000e00300c40003c4414a00c0da40c200d0007600c40c140c00040c81d0b0202c070316048807038461a007054038072b0020200b00200042444001075141c0542e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 89403490 1250 89402240 89402279
    0x8030a06090506060c06011403010e0f06220302070311040b061206190e06061b060a0b01090e0402060d09030e03010e060a05060a08061501050d060b0913050c0a050706020906040807 79
    0xb840c5807100380c0c01d0540d501c980501c5610216230b428402d04442e92001e4209485021419084807040440c107844140c41c0c01007150040811b0340ca6030009007021022050b42603819401d6000340c5003150440d207485840313414010049400c01e45800c0b6510740d0341c0b1007070000c0618651f11b0f04611841e082c40001c0190503030514242c80340b01d0203240028495100c4080c5a0341e08600c04542c020b5950300c2040115004001341080d03100715008400402c02584100d8000c90184e0038241e0304c0074140d40d1038481110b0008800e44010303400800511000d05110010f03405010f50750b000c0d0070841d80000700040020700390303145214207001c160024424804580941e02920b50050803c4800d11180c0c1e0a20303d480d03136030b40740007840003003000315890800103683d0094049401c202c1d03c6810600078291501031a11640e0301c10440e5500850320f542c2003500c110800e101c0c00d8003444000242c18038001e8603c90032a950f8114000503034030700d0781c20004142d060340c500c1c0041c001480c0c040b0151601c103180c030050b01c240711000c0a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 89404740 1250 89403490 89403499
    0x10050304060b2403041109070203030f160504140102010902040c03090209060a1508180a120f0807050409090c0906030f0b1305070302040519060303020106080c120c1c08030a06090506 80
    0xc00783d084a44141c0041da003141083c448a4880e519420074142d6400c0b510902030308184118244000641c0c044029440303182a0075044480d500e4101c00843d070a1002255a000920144824080605e004034114081481480007142000081e00081c08035544000c1d4907005c60340d101003441c21810844106540100f040741c540340130501d401c004a803542d60040d17000c0100074110b4009027205c588020070914034002101180d201214a11b4410001092030022601189a640401c40824071400113548218410750310107092074a0034044c03001074459000103c80d941c207100c20128419000340b08600095000300e0310380103100628100850010400341c600d1960b010760310600300114900181100880342e0560300000c0a50318031801032070914074904559000d13402c284000050543c1500483d0070703649680242c41581182c1e10404c68074480c4034405140d59003000b52030344018034103044440241c20700640c0d0405900e40d1a80c905003c0d0b0b000f1605010303010381e80d00040c000c1744c005102d482d83c0101c0c10744 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 89405990 1250 89404740 89404759
    0x90801020408031e0712020105040b010e04021008070e03030d0b0906010215010b0d09020d06060503010c1115090111040f06030c03020304020d060903020c030a06091b1805060a0510050304060b 84
    0x1406161a4824610b0304d00c4601c07280d941442e8200c00c3c803012540364a03000401382c1440c07085104001c1c080c1070195000d54816004800108110710031031601c90080e50b0080c15640540c2244209481040c401403a110500410910f21801624140014209196107038400648840643d0401aa4090140140341154016002c0c0c0b001c1e075030303058503180c1503480203102035840308158103200f40a45941c0c0e4009410400406640301080300c0d0781c01000c01d440b400c80c028042c001d40311600f2910500740d42500e84640d8400c4400b099a5048804c8458210080b031002003200c022040030320b401e9a201c0d900404460f20380c001304100f0039074984681110703d0318520f01946141055000906030b60070480c0090041c3d9960320811081600800c580302c2c600c400941a103240105c113007001c800030070984505880444485000c1d0904880880040099412500c0d07220681d0800e1001c1000400e001042d4940182c1c0520740864036a641d40804800314000f5a61669240b50602e4002c00303542c5174082590142e036598 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 89407240 1250 89405990 89405999
    0x10050702011b0c022809110f0d02120703050601020c040914071503050f01050a031119090e070b03062d060d0b040b040911010c030c0f0308180a030e0105030702030c060c0a0908010204 80
    0x1010742c0d00c111b071920000400c840c004921013403407034440d45280b041c0e1b02c0030020300020034607040e07000341000701050552411650358041080d0280d81003200c2140c0181c20a01c49400540b6044c1e1060043c64060a1051110b00c1c04044a03458220240c00800c129584560000c8029070b142c010540d2013480500e03010b110703514100215030b07120100d000082000300500d2060302c00791165590702c0e5445500c45040d43c4456600d240060081c01c0c4940c280c0981e0040d0040420b1104699089078081c410160180c5500c15030a07442c002910075040248800010f00d501605080d5904805001004103c8100041c0c5141d90800c100440c1c101001490049041ca1500004507a0002940a401d47e00b130a140502603540d2604503083c802c2d00100074543c0c00b0880001007030651001c512842132600d00c6020b90702d0081441c0032940c039000328000800103580c180900302503503c10000b071a0807100303031b0040300d09285031030a40e80d084c000d04948030950024041000d00105030320215040040144070021454030341003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 89408490 1250 89407240 89407309
    0xf08030708030403180b0903070602061005040e12070b150d0201140310080f01090c05090f0705070206091c1511042c090102040e0a0e10050702011b0c02 67
    0xa0580141070000c0100c001002d05010303d2400c4084010401c15070a1103448038008000382c0c000903882800b130311a40030040b40b458000550305001c1c5005000c2d0803501842d2100b000007400c0e0071001d94900e401688060105061804040c100052081c8100300b004c1c80c00808202d5030788500c10016211f14914020100941d801c105219601c000c4191030359542d55540c591884c0e50701d9150300581540c410200d44070700105c81035221030780c40c600c91401c6440341941d072005c00c0403008003a1490040c5021400c0465141030084008198092000c0c000c01d0811a5440c0000c0c0041d0504207c43c54180302850b00104005c004c18045541007440e44042256401110155904c2d000720300441c2c100c0c0c070b040754919200c2c107944461400e00344290202d8080a251000e48103010307400c031784103545986103081d000c02c956581c41d004049140c06901e00424200e82d45601c03420103410003801c030100f903542c1e5450a2042c210b440c014003c50003d503403140945842d00e8814800c0d8941040c002101106c41c8030482c001c0c0c25030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 89409740 1250 89408490 89408497
    0xa050f040b01090515070b060108040203030a0509030109060204080f010524010c1110020706030608070b030703020315030303010b04050f0a120b041a07090503010c08060603130c09050f04020a0f0803 87
    0x1003038400080d940307a441e0058460303c00710740040b40d2003031180d4220002a92084000c002e01445060030540507100c210041d550481e05640095258000340464202644184003900c1d080780d0003000400c0380c6000761a501d003203030710541006a49801c46400610752101c02d008891f08900741010300800c40038403000403500f0700d0307801141070304204400c0d52810034072503107003001c04003040020310341c1075140c6d482c501c0655689000d101d2100880d040120004581d800465008110382c100d074a50362940c2d851160440082d80002c1034040e40f01043c2800d040315407000c0002d18060400d200c01c090341c41b4104400c100001040183d498418074207400d05100d0169907030403026800d0360041c881002a00e59140011092000d80345660a4221000420003d26402041801141c500ba8000c21103401c079810b04a0700b070700c02222a990008400c2000c51042d42152501c690180e000d10310301884141c492160009a68054030024411500352081c00198540004c551700244044040c4c40000b924024501d0f44032f00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 89410990 1250 89409740 89409769
    0xf020c1905040f090602160c21060c0203160305030901060e04080403060b03121201060906031a130603050609030306150a0210020702012706030e010b01021009030201021312050105060a05 82
    0x41c0c0303d402007244000c203904030300304a650017170003035458010009482281c0e901d800b8094540c44000a40006c2e035038880c6040d040120320001031454070580740d8550381701410a500e41e040862004010340b001d8030010031404610644a40c1e5525a2400e010340351600b0741c1e00c10b4018280710001a07040c040010f09030001c0343c0450b0740c040c9010511980030300000342044001102c1208854001440350b110742080e50007241651215110b4481164954200700d04407000100491a000001920300d0140e140c9400680d0100218101c04980301c1c0c1c480e603c49003449425143d03e25075900c04000c0c42518600742a12400b490300320b25200d030a001c003d130002551007642a012068240d800200b000559100e400d080e0300792540781304003a540c0300035070046002ca14070b60301c80c3c0c000107031404032180c2c1d1020040c024080103400580c0101010210300c21040010206000118103666081010300f405244c00e8071743c00003d1581e10503814412a1608045003903481c000c03d42e51241138030003800c0c4030a03955031141a6884 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 89412240 1250 89410990 89410999
    0x4150b0d020907090b120103021f0c02010c050c03030d050f16080a11070206040602030a02121806090a150804051204210515011715040305030103020904150c0f020c1905 74
    0x5407581030042e03030a0138203908a03100403000000c3c0d0000304400050346604030317803003601c25040c507114403100c01d0004040d000080c0001000070b000600036611544211501320f000c1c0c400e4070000045100080e1442d0700081c1441042510760007049650f141c410754883c2c1c0500340d6a60402c0040c480100246101d00c0103201c260f1799903460041d0a000482038007540d00007030b4040c0c240c5035516101c95019541e47c20607551200140f040038045142c561440c1e082c0c541107406011840400e401001c10889207400610516400000d00000007c0c152180c883c541c001c40140d86a0404604160a10707504140104588400c440d20400c001c020b1750950104c002800c0d002243c3c1100501c0341c501d001820040507500d0b00b601c00d070002002165010900c4140024403400b01d048544946031448105400c1404450180120300306000410244c102881d40c9075105104010505061045200070001c48088201200000c2d8942c0d202ca207015130100510410098102d071140c142120620015500f210300340100c40c000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 89413490 1250 89412240 89412259
    0x1401050f0d020f040605091017070c0f060203131202010501080303010501030905030705070e0a0e06010e04060b01020a051209090f1506130302090a0b0907080c070f020a080a0b04150b0d02 82
    0x40d070003030360305491140c0341500380d0703503603465844000500c0c9802611625115245882c0318028413401034180354054420300d00c0b203203e541d4400701c0540d80000460710503034a0411103c074960001e11030744003c5100b884401d20780c2c0c40d02c00341c0d400d220503a01c10f2a0300c0e00c130a681c074210052100550000541381111001d19000c07464000307130b1070130b1401c6000300d00c0c006200e031051806c081800c400c02d11340984a034200b440b0170000202104240ca5951000303100740c402070050307a00424007040080c1c01103c1004010700440c1c00d403001c2a40c0782882e11080c005a000802e4022911090740d241140e04107404c2800780f011241c03203042081140c0b51140c504030003248074480000792180c03044006a000c41c01150005d00c0d02c0141d03d4100310640c044d100900c0722521580088002500c098020340080d4000d401c4240076601f00500e030380c0d68000711441c20344281d0344024840700000b01c01004000000c4424030540a5000c0f40c1840d20300300e070b0400e10b0f440201c0304480c1441051500c1c2c1e2580c0c54075080d541d4044422141d1b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 89414740 1250 89413490 89413507
    0x11107052107020904050c0909010c0804260f030f07080f07120e010c080a06090504050706030b040906020c010b013915090302030a0909090b0a0c090512010c02071401050f 75
    0x201e4403803444025048400c0c03104100901c0310220f2101c405041c01d6450b0941981d50156080c220703003030780110364007154422010034042804200340840030118219011114040d49028544030307080030b4281a44d201000040000058110111070340001c01420a0026414050301d0310415010040840c400c004103103c20503900711082d040504000c11a1008104a204101000b01884022222040014140b2000052210503440783c10310590f0440090000c2505000085020344a104502035120b903d076298a801325526200414220001c000006455180c120000d0f160240b9010052030100e6919201291140c000181140304c0c6500c8140381e00c20895881d00c80d81400782c07503160381482440d00c1c4064040580010081010081d1a125051a1a601c8400d0016030f440d14600500484c0c4c801d02207240c2c070b003650700500000c404508010000584840108070742d00103040e4034640320307074540d2a03170002c16805000b41c1026162445003902071f00131000000e42540709030f5000c40c4081c0c1d80060303200c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 89415990 1250 89414740 89414803
    0x41b0f08190e0c1017060d050712030908030a030902040e06220620030105090f0112150207120e0a0e041a0403110a030f03050106051c050915010b07030201110705 71
    0x2503c80001081200c1c40018150020540780484400080681081c00070500518001c1044084942c1c00f20040161a00b00781c40014801460304049051010044000c030309440c090002e0b0400f421a55030018022646004200c1034402e02280c160003604060f040c00541031000034a0024561040e00e01c0003040d1142c940703c03004011040c80024061002c60580304d0018000b401581221421941d07034059484070280701c1c04e84036080c1329900034240004031038000241c07811409081c50020410050400075146c5600b02c2044003905c1c072400185104651000918042061001401d0708180400c9503161540c1c0e02d4107140c0840500300040c80c1d2010006003014421000300030200302b14026200000d6403850080c040c40800c1000d000481c0c146000454118810025920289040101702c0c0c3c004004150b10380007080e0161280100d23000b200c5000d0070120107041c0c0782e0f00820308101c20580e100d019060003030850f04200142c900c1c1c2c11080100401103070300001c42e031804001600410303010240ca81e1400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 89417240 1250 89415990 89416003
    0xf0c170705010207051b01090e01051005270a0602011e020c0705130506100806030a060e010f020c03040f0501030606090e070903021201020d061415090a05041b0f08190e 74
    0x400c02d40c00010604100600407800101c2204984500f0100d05525801540c5c0000340d401405803012030100108803514054a510f074888035542000e034542041c280e42911644240c42200301c90030f01c0c81822a00b00e040980510008000034802000101c149001240218800381700400d01260042680c03402d48074184005001010000c1031210000008481d09000d05800c64880e80f044d000d00c0020b10341103008204d0b00d4400c0c00c0090103080c080d6082e175560001002c0d840c0c60004150369441d00e80710b8010305880240120144040210749591802012044c1c103419138028a04150900c0c0c01003090700d4111442c6d41c00d6410105009609903940201190643d0303450340089e40c059404c0c00b0036005510194018200b00c148102c05210407a1582e03e940450010003004980104034001c0a0045148003809000ca14200074901d00c500c83d600c0c80090180d90502d15894019403140080003000c0750050112524091141810480344c94500310014068104041000000c1c0d01c42d55000d0800b1000d1111 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 89418490 1250 89417240 89417243
    0xb16140f0c06010e07081f09050a240f080106050604180e010203010b03090f070305030d09020307030213020c1b010905010c020409150203090708062e0902040605190f0c1707 76
    0xc8455a40c4d654110100e030b40e0741915560003050000010480224a201e40081203a804001440007107280121420060a00620045d200340d0754042942407005080d11101000117081c900381300c3e040c10308180011070001c641c0403000c0340c1c3c9442020031240d00d484041c3ca04a070258016800030008560003607024100c11114600320303520002c004180c080984010314002c0c51600110b8840d00d0109605558902940c08003400c603030700c14010742e0034801003a00081d100600c05010348000d907940b41c0c00708540e0a11035856640e8260003203050000c40d24104004007070004a2000c2e100402544e10010703100340124007455040101b001c04480654441b50001d00150b0ba1003510000c44003126400ca100a400030b030b4204626000f803000c00605000c001078568000c00e40302a81c40c107120005130f50303495212100800000c141c1c010b84000540d1000307500c094002031400d92202540c0381c07204010301034844100300d000ba0034021921488000c0342d80c0100040f4403168044000780c0b01c1c0104010500ba9402a50b20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 89419740 1250 89418490 89418493
    0x1090305070b13211a0f0f090705031906180b060603042a06091505041203020c0d06050105010e0607030c0b062202040806060a12030e010c06020c01090b16140f0c 71
    0x1500240d03401c107003013001d402c502404041c0078000c400603c0030580c00d0203030b64a448041030840414440400c1d10070341d54020b555181240c290f140d48102003800d00c40c07103941d040342c40820b9180f10814003980d8000c1c400160b49140341f403240080c4690300c15410100c0905001d0042002000140c01c00c04445074404408100711101524031050356414003c00da80350123402c002400c0e2200c0026501445441038040d0083c40d00c400d41001c4c10420200c1c5041c8664000f90304502c550041c24865031220241025a103016100101d04d82d0b0501002429060304c4c0f90b80310307008940811006000c01e034006049585e00da48040000e610742c81e6440050b041c600d00080d800120341022608884204070b507070007032007143c00540545110743c0c1d0398010004175800d42c0c8505e0040c5004500c0240000b840386044101004050410545050701c54076070070201d070802300482415a64074000785092080c65401194040076a15542011001c80000100080c50340110440035110200e0030b8000481d0240c15582e00070f41c4c800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 89420990 1250 89419740 89419769
    0x30f0f0c080313060201020408031c0b041103040c05090601080f0703060302060c030a02010b0301020406020d05071a0a0605040e0111090f0a0b03160f1b020f010e0d0305031501090305070b13 83
    0x1e80603450b54800d94911002403d28000042d0460040c000d840868081001950602c5980c9000303d40901c404804104126950f9111700c0203540d4611030744801400d00d0080c513490345840d207409212080709070070903446400c281c000c0110b10703a40400741a0340b00c003210001c40401d46540a0540c00307490580c0009600481c04110140c0040000026040c03d011540c000e105458000c0141800c0348140e000303080050300803c0480d4080c600410080c29250310503506141d05c10448098544582400d0b2240e011480d10b40508119500e058050321041d880300c90b0007000f0341c810144028403240b0510014500401c591031200340207a585c40c1c5e0081c0200b050041882d580d250101d42c40300c1e840f00c4a046100411001882c2044862143c840906040c0e030452801c04000700540820440d031100b04001c3e810050a4844040310340c98920242450b203101c0c0c1c1721583c030303414040081994914020003a50400414031020404640d0000f101d200301e403c00c800d465594480402912142c4140e5000b8034000b10034203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 89422240 1250 89420990 89420999
    0x312070f230a120906030501030f0219090e010209040516091e030609050102070b070f08042301091406061c0b04051216050d0c030e040509100f0605040612050304030f0f0c 75
    0xb81103d14a000b01c0e9910000196100d440c1a01103a00a0002418410101003a2401410001e80f02d0b101c9010503a2524407035503840e000841541d403185041025a5000308904005003098000d040e04100e41010010030700c01102c0004000e51603a200d0b181105401c44c3c503007a242020041c806c0050b5401240034003c42c1054100680031b5405280c0489540344034100003034146e44100f03800306403615a582d07000c0090700c079502d8080030010109402441100016081c0f134a2201c24800c00d00d149114102045400c0c10384c0e0a494204800204150300410000ca074070150150507450203c900381d807000d5a502181c4480c1060762409079003080c0919540740000d406002031010840c0102002e02c6541100c1c01c6117440a01260b40200c803010050200700300c4100b040c102d02d0f183e004540d201400d0022075491a03d45e68500007910352b0044207a6283d1340e9030000b806142494019640502040800a02084007650f201581c92145100281c14400e1044c503c50801407a1004142600c1e0041c4021443e00e454 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 89423490 1250 89422240 89422253
    0x1050d030315210c06030603150e120417070506040602120c0703020a08060f07030c0f0c02030c041e060803070302070e040c0504020a05180a0501090605090420090312070f230a 77
    0x882c041d613128400f40c500142191003401441d080e258040d411014004020500034003420300559079000500908006a00751041d81e40640024003001c05400c000071140c0003002d081c4141c43e0426402034a08020a210036030700050b160b0000c9035442c540e00c0d40c2c1d1080d0030807e41010f8907500029030100120b0302c00101c02c41c0020340709001d15201421400142c8034001e080c0c00b201e00e501060004141d071849195095402161000701440c00903040d5040241484005070849071144140e51101240c3c22101207024460320a0001928202004500c0d0050507240a507807584144a0400794040c03070070005013042804201100200000b600540d1248203414002d41141c02140d020160462800100035107885c295544108403441a1140314486080000032500c0d0380c04600c0700340c1c002da1100041640b01c65001074507107010118851003521850903800301810010018007035198403e050041001091054030340003445503016034162a14600e6102c59071109249810345d9410380285034800f03040c4000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 89424740 1250 89423490 89423549
    0x30408030c0f33091f0507030612050303042a0644090114131205071515030209090706030b030d0819090209090a0303110301050d030315 60
    0xc2c04410b03240909480c1600c4855085200d00d480807501146085102442403e0307116a0001c4031941660791010100d0381c0c03051440c80303400682018941e200c0410454560521880d40602080c807a840031316800c50306d03099034078000580040c4c0390117075821b4101c800003400d203030030010a44070201031003d05070707079070400f600c04900240840407500e49070381101148800c0381541c0c4195003500c2100d8039040c1415048251410004100b2002996150710201c40c5220250070a4071884148540c4070405900d4a0300907a440f0448c413601040c041c00b8004040014038003c1d4842c0e00603403020700001c401d25546618030043e54280d102075005500401031100c42c081c003160b07a1056039025103040c03129889903003e00d035449902640d10b034009034010740800c1c4c0301c071030914044500150310103012800e8280c58001503041401502d88001c140c0c001d6440c441019014012a011180354078649400c661521010400500861100500705581c2d40c4071882d0124a07001d005d0060301d81e075004030681701c5811469150415 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 89425990 1250 89424740 89424763
    0x40c1e0608180a0213200f12040309090608011a0301050f070f09030209010b0306010f09050a0302010305060a0b04060c0b090a03090311120111071103010902030312040503070b041a070801050603010501050a02030408030c 96
    0x1a00741181d0301c00348102508072900c080030101028230340002c10700764200341a0068402c804000750705800080b0300c210342c0a00d401404400c800000c0404d5601c04422840c3c88440301e80740640d041104114004403c0099158810402c0c02c20041989000c107003281c1080c0baa410080d80540ca15001240b01014074015510804007a240d44182c442044010340307107050302d03104440e03001040e085d0038030055201e43c011750b4000001078244034104d5203600e011030309034100750080800140c2c400001c2041c07004000d04140c1000030035014000303090041d00e00500720000782c00058500d4403000840100c0d03803030340c9000214048100307008003c2c070f450202410300503510480c0160380311a03650400015510b01807081e2540280d0060086142c00314003030361106400c1d0000c00a580c980030a2011001003807240c0306c4503125510600015410040358140c04110a2024040404104a03180144000d03182c6100700d9042d01c00c2420300ca51220311842c0c0480c510b1040c0d0b0444c05c4c075030202268484031011300142c4d010100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 89427240 1250 89425990 89426021
    0x6020c01050c0d1404021e0a080a060b010f09050d0b060f030d2001020f0a140c031c0e010207020321090301150521032703010203040c1e0608180a0213 66
    0x84000132051201181518040c1d840940d82110f4440d0f41c804005281400f00b010b440c03840c2069072178061500340100001c0580d8625202d2070641e82035a4040b0130100a4440c03420952402814100801d255189200c00100f464080c080400c3d19959080c10000484200404840c11030b000705000420450354003500c07124008501075040104881802520146000580b10030308208400c02c00b00c1d5034001d540d55941c0d691008100006200c0814801029903035060460106201c1504010320304603080e4040090706644148200d00c010303913001c24404624594501e071081441c1d61820b9a0140303210b29483d080d4190300e80f811900c0b07640008010309044800071280700300880c43c0d0082060b04144104958007054008100e6a10014509403052000088d01c02c0380f00d4011034002d010034226441550301703035140075010f001086442c01c4c034100d0031401e0b211850701e580b91506d420000782c06044050070382140d064900701d0000f000030040010049160b00204107100700152891030b04000c000f002d0038000319 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 89428490 1250 89427240 89427251
    0x91805011107050613140a030801050a0909110906040f020705100e010207020a0b0d06180f1a012109050303070815030111070b0406110d0f05060a030807080706020c01050c0d 76
    0x24480e00010340e015903420001524450751000c0190392410303500b1004407401102110314804031b0f1010840001498441d0f11020915410320b001c020b424070a03030380300c90a45405c1241c0c0100144201800000c44c020a8a01740349648035540001c001d05031800340302045900c0800d0b20707028000002008000807910060401810743d8a10b9124203038491440302030340100000300308210302c181d00c0340240000020404001880d54490007a244403c0e04c104590400c60b0300c0e100b154901c4030562040c090703481b0000d031095a482d800000043d00c0000910040c01032441e802000a80301c80e1140c00075407101f907001c41940e59900c2c0228010300780c070005a0b1040b043c1c0e413000030600364905052249460000400b9041401c000e00c550303031240300103c002d008551250311080444c3d8000261409000c885039a41008180a10107038040c100701c034001403c591244061101c1040030070b4003941114041900b10070316580e103a19508152010344211030032041d040d841c103000c0002030b603502c6000c2c16a90080c0b6005115 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 89429740 1250 89428490 89428511
    0x20706061409040b130605010e0403020c09070801050411090d030306030b130b01030204110d0603111002030909070302070c0e0a020304020a0b07021e01020f060901020414011b081309180501 83
    0x7a001e41804803500001000701140204940314501503003c0c0104500031040f0b44150307100d009541c82a407004146c0d184020a00c820582c0600c00c0002041055462040300d01d080d034002080004180f059038012a80d5a06104502c0c80388822100001d41c0503000d49800c6016290090042902c0d201c00c1d01d481d0300540114134291401315490b901f84d90440f24085c1c0c0d0742d086800700f00080640c1e048010340003004205402803000384d800340c0d000450041d040c2181901030001880841c8800703d000c0030864100300122401a5a60f81d5055084981441c0c01a1030b212030389420b082c001d00e0b50700651000c00c240700c20404100c185400562083e4420380d9041c9100c2d43e1400da008180c080c40200030740c00241d014094a00d048811701e088403880b014030440f0340b12001884003e0801606858407083c50b500000d061169001541102d0044c807001c0c84c16036461401243d0603901c182c16010700400161002805180e030402036032050028054a50013000200c0550400c03810b111100306c801c484a5081020415 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 89430990 1250 89429740 89429759
    0x6010801050111120f04030b070f02010c11070e09150c0304030314040209070e04020f0c0102092b06050c040e090c01030501060302030c0f16050118030207080c150a020f0f0102070606 80
    0x2102515403c000704942c002c620021001030700001c8190030700d4035080c480000460045d600c02801380f0400d865007180c1e040410002070035555050070840910512110344c120b204000030f0440e00b01d5000b2440d154050b1034080c030460509000c0300c02c001182800106101c6d0100b40f0b4401503020f14030070744040040b41c00c8504690300c00402140d020394012001000100e00034007a47c01c003421041c0040006182c851001030054160b0000e281450310360b980890310341d0150400c1d201251002003060301020391000320400c2e260902c82180710043c030b4940c403500458480700e022415140505081d24001402c2d2610900003591296000c2d82d031360000c0c1c00c000c00024428001d04c00c0341d000d40782c065102840c00342c0c100c40c2aa01c642c4001151012030080c3e941c00c4c80850b00a03c1004650613100e143c40701c1030a038904000303207001450303045060175400450100b4240d03610341900d194211a400019034072221111000e0b4280801c1a20300c0728a0300903038001c0c1d01050300640c01010103520594041048035251008030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 89432240 1250 89430990 89431007
    0xd0810080a030e12010902060408070513020f031306020405090717070f09150e04060e160e0303030402040c03090210090602010c090807050d080f04030b010609140d230a0803060108010501 82
    0x680840c6001c07071890407506001402d492011412030020540a038251f0100f001035200f07030f0080c5a50b81003101c00340458609401c0c0a002d100c440d220039030414003034104c1c401c0c0c40d1002410680c105d078a02e8034014100416501618010040101240071074074140001400303480b0036181416049011000280c5131034000c545038030941041c1eaa48031003c0382008000d581800c40c008901c0107110004138110880d81e11401110017622240d01001c45a0403d00c950640145102d0740d00700a000b0154a41c41541d14000700380ea50007a0119000300c1c0040101e40c080c1c000b025118806504030886049040000741c02008903400c4442660007005441441e01046604142c00c3c042e000954001ea00e040040345010326010780d4050103218038510b001134024030042c0c291310540c4125504052240101703c00b98000d01c01304020441c03090034003609888000091161000d40380d00800c00204000171584140302301c500f0040c101c9452040320351010b07090401140541040b40e60343d000511090002c00e0035407007481c00d07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 89433490 1250 89432240 89432243
    0x90c0e010b0304150e0a170d18030e01090e04030e0f03010f09021e0d0206030a150f0608010504050c03040605090319090503010b010915030b030a02060a0c02010e0604080307080c0a050d0810080a 85
    0x11b00400716951b90366103a01405070142e062201002e001a000400c0140310300c10301004070240403240c588407480d01030000e5400c0c5070010705108440d03104001c2c810360098a554402d0303240c6851b090700e6144800084803588010045501586030550300041c501d403590010608600807103180d64950714000c40c00000303001040f4001e400c862540e1a1030010300b8008091900040c008001090482d0071030841d000d407428690040990410420b410006140c1002180e8050030003500c0511452800d4207454000780b002402c000d080356500c400241e01e205041c02a0b9003001c4007030810310411003002030028800c1e681d501034507200e5440d10103095a40c0d8000c000090442c0e45106c13008003840c0c00d404c4164000e100358203056415000d80d020000060b907a81004211a0820f501ca00e007241e6114000140341d00c1840c0360060141c20100414000325100009a9011076801342c091a41d50002c01d11003410250b4005000f05a0301c02c0b8015403d01d540c00943d00c0344980c0e500031500700030700ea0f141d030380702d50f82d1024500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 89434740 1250 89433490 89433493
    0x50105010f1b021503100b0f03040807050c04020a030905070801090f020d0314070807051e0c060a0c08072f10030506011e180b1309090c0e010b0304150e 67
    0x4a401d4180c000c0403907000207030110812855048442e0049401034107020f1200d070340c840001040000c2c21200b6010302c1c02510688040c02d0412205000041c9544070190000d440580013007010f0341002010001c00913006d001400540d124461401c0190203800c2c590f0301254580201ca0010800e034205124003410301c7e07085241c959803088150240300c044146403009a080000c510003c16181100f40002e160207481014420f81e940044e06005082680e0480d80c0400345241d0384103600aa1030000b0746400300d44040321240e0751043c04030815150810900320003020034102007400c07401e1114411081007104130800e4400c903040c10904078040c22003500e1500662202154140c42809882540090b510540604062400108840443c00d014080c0da040c030000681441d0070800d04800d41c072818004110419645080000369400460001d015014541500e9034070012002488060000440106131083c2001441e58490342c000359154402c85055460310321084000c0d242c1c910510561807004403550 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 89435990 1250 89434740 89434757
    0xb040b2d0607050613030914010e01050d180804051504060801030b04030311030406050901061a0301210f080705011808161401020406020601050f0102070e010e04080409090308040b01050405010501 86
    0x10030110002080c011068108000b4800400002d4007003000c40d026103030541c442e03104201c240c07030000c002d440300e90080041034411710141000360340c102051041044003400c0c0380d80c440301c0c2030110710010710000400030303132409100d0b20140038000842d009100380e40040d9000e510f00c0344945007035a4144594454540003c030800010404a4042440182c129101780b40101d02c007000010001c1307030703900142d4040e05d07081d68074001c0c0701001809105080085c24400941105903907a041240d105000500ca10341c04011b2554a40300b05800d01c2c5218401c0c0c50740b1034180030b00d000203030601200e5a0800c00e4222603e40c600b86250380c82140030701700300355940d0344641e6061500b8071048005030341c42251281150b460a00a0b1050082d00c02800600f0140071145e0003080f8540c540410082d9902d000c1c80c0490554003c0e100900508117220f004906517105500510000d03140c7e403501c00454440c95022030140761401000004056000c3c40c43c0340198014503406119036202d0040000b120420b10419010541c01e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 89437240 1250 89435990 89436049
    0x10212041103030d0609020d0522030c0501110c06041202030301050d1410060b0a030b0d0f0b0705070210031406011e21050a060815061809100e010b040b 67
    0x900d4801d00e008000d001e4074140824102c121007a6131180d040508000d0300491001c100040a1058662003002c0703901c0d44c95010001300307082d00c0c080038200d4080e0401400241c1d4a00344213094010880704800c0c4841c196440c09400c00c090740310302c01914100c9101c191325440d040460b20000c2640d050700c0c070003031420083c4041030365a0701103c101542c802d001c6010700050360001110314031941d17000f4401481c2c0305690300c0c0c1ea0b0070000c08403100c3c1014140320b804020421004200c0180d0945051070307001c0309a980039141c1503002ea500c0d0091202c02580001d8511681e17910903859007050b0b0346160010b80f19034060300c8640041d00c03110304800b24070195522948864400701d10505d05406545181010720010159211224003130340c00c03c46425000726110282080b403010100300b0b014924012441c0c2d8100c504100c0002451141003960160b00305200c60301280402d507052240b02c5070064620f00401c400400070001a02030400e40380319034841c5191038403550f160304040030003110321030364411800b0402480 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 89438490 1250 89437240 89437253
    0x60609151106040c05040609090f0b040c0315090308090a02030d030f150b030403080112080a080402040b0301050703090c06022803020304050303070303141501080711030c07030f060e01021204 84
    0x19030098a08110794115600c415040c24001980101e0081280d484000d043c2001d101c15200554840302c2c0e06480c0c40803207404500d5020f50584096403000098800340c03990b040c10044500c4941001d00100c0403000182c0e40c0011b164048003030a80f0a03103410703207180d4039a0340980d256405a8001703500741d003103554444085842903008000c03208000070002001d040d484c6807a101c40d109500003500c00754000040c04207040c0c0000c045401085600740c64080d9560954800f01075000b40030240342805210300215003150313a80d4002a40030000680208603a1600380c000130003906080005076581c24000902081c02840402d0351003400840c44000026203116100398075100d5406082a82180014400826903035402d0001709601c5003c5d580100c1c6150f003c42030010348440192400b031504640358041191030343c0180900e644290a418804022120400c070700c0d040d032047d80000321140c040c1c80d002004015154114dc14901d001d25400c110385044503005500304d1048001d01c1507111014000100000c0707c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 89439740 1250 89438490 89438519
    0x60b060a050909060a0b0f0304051204060c080c12071a0703050c070201210509070e13020a090207030c02060a02210307080f070c050706030c0e0102060c0f07080705060406051801060609 81
    0x3000c5c0131030035825600d8182000d150095413950004180000a10083c010100901081d08089544461030302d07142c03d030003802c2407000703600007406100b0101c0e408800780340600500c1400c0010441c003980d00c3c05185002c00450412881c0e0110783c4204070040350040784644201c620801c0f0107071002c1c7c0380c2105900107685403107845034200c0104c0d070707030f4806006964590300420b4003403510b00c0001c2044e01c2c1000b00d0001100030050101002481c0740e2400e00c0582e0b140807003c42101e5400c0c3c401a950300c04c0d1f040466030800c1e8600c01035008500083d01810160303000522710700b80701d50305540020500f09030f10740540e00e11042d43d031100016038001c045807802c04080741030b981000044c02e1041d0700f602c01d607070790500340041e03a0b00900c0426656180110038942155007074580ba80d003407000d00214500310a50407001e0255100340c02404030b022401130100002d000031038854542020840c3e40d140380c5850715801600d022030344074200c041c542845007081c04050042405031607068941e62032090500c003480305e0094 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 89440990 1250 89439740 89439751
    0x2091e01170f03070507050901140a14040905070e01050109060306141512090a14030a0207060f12060807090b10121806091203050702070620030c0712060b060a050909 73
    0x1800751201c1e0b00c2c400070002801001c0c07060024022a03442c000030444c411005034004222901d01c0203158a0300d940d4400303440103613904a03091103003103401c0b0404035004045426005203d0701c101140814124855030707203107040301c000343e03941465540c940d07a04a040e21414400c00d0440448507012b00403526024100e020080005602203092041c0d590850126843c00d0310011525003000d504a41030003ea0107124004c000001c00851030074510f840c000395951410710416040041481c8507086403480b511002d480e054890b8400e004181d154006c03031351905294419800c10b2440d11a42c0c4030f90b410b140c40de4604020799500e5004200101e917819034050003240910300203028805e894a40010001e00c942d0010714040d660f0301d00c40f030100450140c21900040e01350415540660f0040214030b900c861541c9112504d0318146840c201546401072441c0203010300c10f005030085030380c042085021131180c03191080c0a00e40c140190030301388040c41024401c0c040528009901040700f940c0703c1c00c10002594005c2e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 89442240 1250 89440990 89440993
    0x1401050d05060f310207050d030c11070b040f082e0603020904050303071d2808030a050a0f050301030b0403030510081e0c091303120b0d0f02091e0117 66
    0x1680c1e0000340034200c00748940041c9404400720360164200c90101c5180413894440440c0f4240441d15083d54400449032007008040d140c0c0340c4280c08034031990200d604d011880b021501c0b0b80303895840c01d81040d0858094030481880f0102c000842620003d240030418a070140080a458038190f01c0f04034030308401090503107854556400100586400214604c100e00403c040c0d901d07410424001002603082141d00c204035881c02c1540f02580e9141030883d680b5401d040e20311481c00d05007000c28100040160301c01420390001180e42c0074a076800c40024804101d9690b61200e100141c084141e03014002030002030f061406103000600001d000e0303402990480c16681d030810342107540304c01982c9046d2128081c446001c0240051015900c000c00410003500400c80e00c0001d5131420240204107408081d00140400c840c150f00705685140550000c181c07007038042c010322403001c01030904840c02000d5032001c03405034400c9030000d0500d4408180500805810f102200f0160f40703003640c44550900c1c1c0c1007548501c1d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 89443490 1250 89442240 89442259
    0x60f070b07091a040503010b150d0906090803150306070207060e15070f051b03010e0c090c0409060e0105180f0c0901090e01090506120d05090105070611160c1401050d0506 75
    0x401031802c030700d800071080000d690f605d04040902d802d40e08200c2e40107008210050003034581810b00801d0303980300c4e5040320000441088078100100940300c2d442010700200e5000041c001d5950340e861620b100313800c098041300c14949544208903540c48440c4030f010300180e207102030110140343c44030440c5080301d6864481814148a03845201c180c046c90769040b43d0079403114019500c1024080c0210000c441c1c2100200911400030503c03035160f00324291101d00c9280f0000c005080341403503900b9a00906440181041400c0e10342c441c08a915100317008076403040b045c00c408040754020f0240340da4803030540c20a044010f1388031440e0410729500065001c80c1400350800303011841900a0a2a41c02000c86d00404612400c1041c01c0c840d18188540001145030014510441c00903004000c54030300050038a88640d0f0360b891400c069000b0406405124020f04000814601640080000124542c020700d41d04641e5540e070040c40e841000034210301c0380818814030102003910001d601240d8815030240c046c2c2803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 89444740 1250 89443490 89443499
    0xb0c15060f030d110c0f03100203130803010314060a021801120609020d2301050607150b1c0b0631020c010501060c061a090c0c0c03010c02010c0e060f070b0709 70
    0xb081c041c00f402d0800600380101340d01c61640104407001a40e041a92580342140c200808a0b403124540b00308001c0c80381c0c000010036510f030910601411a607400c900d5007516540c403485d180c5040d8a010340071051a219540108280100f140b08840344030808941595818041d84010744030301c420702d17030200c82da1580c0b09400292120303e40020310104144520024801d1120756060200078940095101005030f0100148000d464200850b02d256400c540c40c50a401e0341e00f03540c50b0140c442042040d41040c041a03441c500c0342182e90440d43d2240c0b00300e10b0000c01d9647d003001c4c0440594803c0c030054480c03134944010041c1e50314001c04540182030100000d4a098105180c1609460703083e8810f00004014182050900800e407103248448801101c80c0b01020041600182c80e0799809404070b1000040080e029552140800030840c640d80e0150003405a00b007040780190003404200c42d0500400c00502c0c90000c0d83c603240089502045030300a500b818030102da2205100d456004080005215400c0000304 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 89445990 1250 89444740 89444743
    0x1003150e060a0b280b07081306080a1a060906181002330402040209040e0a060b0415081c0c05031309180f03110a02120304050a0b0c15060f03 62
    0x3882404442d0000c2080c5040b031082c070010f100c0342d01c2402441810400b20100c011003191050381260301c40c1e00c15a49450031404d01c07840a00c01c0040200c100c000014002a00541204145120b1a081d150810184602e844141454000a85169840369040000401a140000180c141c40141c4000040c6000c0d075200419142c8918203415405a4000440000c8191000203203c04040200c0b000410100304080225004078000e00002e10907500483d00800c1ca40b1594410f80038080d20070210742150b2840e0400c02e000700b1075802424000c50030034407980d18040a080d0540100c440e05402400d5a44413aa0800001e00176906201c00b04a58000f00d080401c004201600c1c0c10708000c0ac0000449140a00b00c0c0c04503503885444508044c45402594003042075811607410558040c10700d010442441c1c243c0c0c60502c041494002d60000100b001c1c41203609002010340155401501c103264090384401240982c2d000c1c1070000000d95000070300310b80c801c0b080c51603401c3c0c001c1409410075083c1da07185c00009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 89447240 1250 89445990 89446003
    0x1305070f051f0206450d020d0930080c0601150f11030c01020a09030b01121e060f0903030219050c07030b1305010204060503090111031003150e 63
    0xa840c011a01202030140d442e0081c400040c40300e10341180302c40704000700d50294852100600722103920520b41c100d03510f4001c0500e141c0307040c021900710802400d0242d4850701040c00e083c03103250003580b003222140409035000044000b049400342c0c440440e21450000b14080d00d01307651411800300002c98941c0318601c020100c0c01c000c000d2060741026194204000c40c0b41c0b40400507442104107800780545000752075005808490285000c1c03031700d480030303c074008034552940c400c8540c0c0c1c2200707620001c1d448403416801642e00060380c1c80303070000130002e90342c4140000c98000c100074003402c0114100c990340802115010345241151003084080b0f6560320448410b022980340c454240e000c2600007a140d003145400c414110354800007406c01508003000c040c504e9650b00003e00005090181c0c0c400032900502040e24980000c0394000300070b565840d26614010074075001681c07128450342c24040790f41d03055846078040d00d2051100454a46409255440d0300303201780c100c21402485c00d40d88440016100c2000c1c00724 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 89448490 1250 89447240 89447249
    0x1806120b03100e03040e0a05010f0605090a05031e01060b0a021c090503060103030804020907020a050c04090f05030a05070c060503011a030c0d2a021b0906150a020106180b0906010305130507 83
    0x1130740d00d5900d00800300c240e01500603c110b880f24038041c010b106510300490342e01c06413074079494283e0b01d40c0d83d1031005c41c41c0d00c00c80303400c099818031450803102031035901c5005154072040701200910880b035480403284264050019041c0250f00501e00010504203d40701c40c00501b412454030302c06482d039540110b03041c000281c100f6030000300080100f20560500c82c90040c0c0182e02440203108524154540c40d0b05c500007040420b1041c1e44490360358003440b0070f01c0b903601035041e0031400750b9070786103180d010280c074039030200c20b085540a074020b000081c154011820b0760b040301c0740c5414102c036803000c111300148982c1c03005100f01a1110248452000c0349518851044000c2d07503076102c0c0c000842025100c60110840340710350421035204a0445050241c0c101403c4000303c4155844522520307100001028484c003640009404000810184c20301c0d41c0c1500404100d0b0410176a1980b2045c003060b005041d030382c4a20b521504a8000380c0421a554400d43c400d69028101c0c100603100d0021540c0c40d90b04040c1161701c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 89449740 1250 89448490 89448493
    0x306011a07060609200a090302120a0204051302030601120305040e10170d02010e011109040f0e0d0e010e09090a030807020106050607060902041802030a030309020d020604151806120b03100e 83
    0x3000104207200e84e01000c028016070117101e00300020340704020320070070007800024081d03804050309100c0c03210100001e41e80694000c0081c8a5407500400d484445000404103034801e220300800002d07031a0305003140064864144da10309140500700400c2c19002400a0408010398180100009046880c201606403581003807014042c80090090b00900f5992140b0b114a61645844a001402a019411107803040d60645020511311200e1103070000901e1002543d103528000e550440e84503550064113401e180b40244c8940424041410600804d03803001c0711070700380b958042c1045801181c0903500c1e07954481e51510000c1025a11400402c2054101d030070101d8003075440d8542e41c021454035001e034584c051482c03030b0004409083c9800213942caa0200f0009010316070b40c0c3e40d80c00b00b95100c81101c075131801c0d00507100d02d5840307941d4aa596607000035400010f001a108407006210000c842c409c40f03048030f2580daa803e0040d40e0350944600100010305406a01d0b125079136402041440134001e01507820346120 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 89450990 1250 89449740 89449751
    0x1002030307090b090f0409020324010807060503130609051c17060303090307230a0e0a05070e090a1104080a050c01020f0f0a030e041e0b0f010e0306011a07060609 71
    0x11020b00486016000280302400900030300340e26844028000b851010215804564943e0a0000c01d003040414580c0c0b80700104e112105558145842c810141222200001c8984d00365680c10116800d00082e91804609a04012840c02091541e0444580f40d40914159030040c20140303140742d0000c072040d4541000c11b25a69050740140710114001c0c0e8010819000755103081c4014000a4640007070380900c00280100d1501d0080c0850071030392401d017100020700700801d184c1c0c54244060008200b110031956550402002643c0a41315407681e11f01044051318014403520303003420f400d002d09038203030008002480510000602c0182001000091405440a890504032080009003801c0d5440c0007003070a6400920f01c140e2074400050102c0c1820b805191203641c0e0484480000d0141500c4007041c04280960118041c3e042401c0d4840311003020300321440c04a4455141c0155030100c02a00c0d4558541c000600400442d00d0446041300ba503030320348401ca80350030160794a1504480e000e40100c0c45255130340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 89452240 1250 89450990 89451001
    0xc083a0c0c05030a030c02100207060b0f01020a0b04020405060310050a14070503100905070302070818010e0414010902070f02090f04030206010b04240306080a1b0b040f0905040302030910020303 85
    0x14469004005030918011003400c0d02529810342d00d100300440c0310201592140711401c410710034002c0248400070840150341d90042408d058020b003c1c41f03442e140c840d50784400c0d0083e15600005800c124103500010340e0300301e0369070340e003c00000345002001e09416014000070300400f50311903c50340748110b420010010b81c000b0200c0c00b0020003c0c00030109006c1c000304005005510a103401d00034100e40c00c440000c200d55494010031000b038080d03840000d10052020070302012004841603440d49c401020382e2222401d0700b0311420401561948000024005502c07801804130740798540040042c14001c0c0808424110741d0b0740803c0151008030741d40030201c1e401000340301c100755042c0f0403103004003140d61465041c181803201030141c104003060f5040d04202ca98060402d0f40b802504003c004040c60340035a408401c69040814864146010301d2154001e10140070900c040000162400e850a40031b00340100b03814000360000500002e0b005600303602c010f100003201035070b50010041d1840b4042d400b0759180c0c01d22 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 89453490 1250 89452240 89452357
    0x10f0506030603030706021315050a0201150b07030e0d02180412020102130510140408030901030608010207080306060d022a06070201090512090402250201090807060c08 74
    0x15000144610340c10414404a0f90b000400e49510f2600000700590310440107005100c3c00202c1e030303c140c803407114010607071041c60380020280081003032035002803081d040b5418140c2c200046c540650440d00b0b0040c8040c0011a01c980c0e0449214200a0004080385046400080d0b0741001c007a50141c0d44c8007040100010031010321034021140da4140000e50604811603804408044035010302c3c1d0044080308110748540340314010344030242e14244401946c070340c6c82c0c0448507143c0e8846072500d03011a08149000a41c0c01051003228103043c2c002c0704a80c110780f40c1204200300d9a002c0a5580310558007030060510f00300e01e014240650b00c251040d03000c00a028004036500740180141307001706691400e600e402c086000803803030031202081c030300915079924000c2e030000e00240144641d880744225140c4035203588480300480054198000d8940d51070300b5540305895650765905014081c0005c40003d01c0d000000c1c0940d0260002d08600c150b17035015450b4500b0907040001c80414600700c0c0041d00850184000c08 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 89454740 1250 89453490 89453519
    0x81917030601120b181816030c0b09060d060801060608130f030f05160b0405150912030c1605070504110708041503020c2401060801150e0103020d1401 66
    0x6a504003421440d2140001e00320b034001082000380039896110591841d62005441030046809182c1400ca034145082543d5111220b14884070107072094201e04032030900c0c40b014003812640c0c45080d0800990500e500d0001d90740280340e1031a00008188500078040440b0b000d90406130640d00e00015565143c00301c02804401d000d401c5e4910700d942e00d102040420a44a9420041c64060504000081c0b4010045072140310f255011100c120041c0c0b0480100a4030206903805180114125951880414800300802806a50b40b61503070784500c0d003440c141898900a0750744189120b0003141040d201640c0c80b01e907920043d01c11281a04501c80500042ca4584107405e10702c0c101c2c060250802400341e9802100d4030841c0a132440c0401d03031140b4100c06d90720980440d800c821009082c0c80d0b1404203425210640e0040450002809000800210f1410701c5500400d040743c00c070079514848081e0318042500d0b449150105c05040640800c8403031800180e0b8010aa0540d51a0015040542c58100c840d0500312 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 89455990 1250 89454740 89454773
    0x20f0a0b0a05060f030d0c020604170303100803090102031801050d05040308100b0c101d0d05040306230f04030201110c0703051504020f130b041d0d0201050105010909150819 76
    0x4829695241920000780c0b0305c000e500d20b1f00b0b260344043d01c47d0000489a00544d404642610020a059084000d01202840c02002c1000711110360685880c89185c0328000c0207107007401640309101843c034030078142c0c8041c0c3d609031042c107085142c0200380c0140710948100f00c0b4281c0200c0c0a071020b1150142901345048010000540d4250811030408041070711500980700303c85107140c694140c280203048c000124407072a8048000c41d06402d012603001761039a00315100c2616264a03001406111080d07040320001d040c8092290b402c0207603609051441941c074082c00c150119075840c800c044030207180702c1c01130400e42442e1005003042e44c80c0d843c1c040d00c0c049200612442020340c000c10b207c0140c90714010b21a03149004ca90104001d2000e88902d0000c0c0400f0581940c0701d4101b103000110101c0030a8040c407201c0c0ca4406032074242410030300036820f891082c4121800501c00003801c000481280e80f101071140000103070722070310310340d1020071921701312102480d03000b0040526450820843c148841c1c55294 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 89457240 1250 89455990 89455999
    0x1308060907030206030106030f0e0109030305060913020a170f0a0501050108070902121618060824010c11010309020a1814010b0a0c1406040309031e020607060c020f0a0b0a0506 77
    0x240c02c50740825401e00040c03040d0300616072034034901c0001c081c182d000008251035442c0204801d0714103080c014050072081d00e42c140580035800200f51000d1a03600300c00d826030303006480c2c3c031b8004c0e181400803600d084207601c08058600400c000c040a071a0240130360340c0309034094000407810f9414403d100d414400584e000742c1055204012484050031001402d65000383c40c884411107640e0ba80358140c500b02c0d85045181b5407a44040c50203d80540c1241e616800b0304806040110122200541e100800320b03010f45241c0071401c2800740d400005d4036561115140708041c94041080c1002394081748000d03403141c11400c4028490303a0f681c480400c40344629841b041111165429035490680703045018400c1d4030b07108082043d80d1070658148098401060210148002250b40300c0c07402c0d04005004000d40d0004541440142c0c800c64400303800108192500e07500148414a0480785651311030040a02402c444254024001400f54203034003488070526150250310850303034510f0200034410031103600910441c0320b0b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 89458490 1250 89457240 89457253
    0x30201022514030705090103050304090506010c020310050a0e0304090501170703030801030807030203041a0a0908030a020d20010504030c050606010c03050a0507050c09010801060807050d020f06130b13080609 91
    0x1d012203240d02007290b001e10199260816604042402d00e04e00b60080d80c0c100006000010421034000010070449460141c10002c030344540004440c401a0307400d029600d5400044140f03101090380d84141d42205104000103210420b950106055030400d1f40315011503503596004100e22402c0010700002c62201c0c00141007014155500540f074800d040c0009450707540d001c1212810035000b00200c0d00540f100188803649412010740360b0400381e0020001c42e00240180d6000581120004259250380003260080c140c111100c0008540840c00305c0f00b81024035001c8060a1180d80003841340740c1c0250302035a58400c551000f401c000740b400700b000c0d103a68100540c05c04540d01007580041603500d026028944155101c51908101e4900504028040e03800f03100c540c00040c40c40c905510180481d0306020a451a403541d95003040042144042c01070f400c01e140c42c942507154980403005202e15501e45480d004e8441d01c480310404a40c110800100d10410038800c1880008403c010b0700f40c0c080d5407003009094 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 89459740 1250 89458490 89458543
    0xf0503100504150f0e01080d12020f07060912020105010803090d1127010f0602100c050c0d0503061806060327030d0b04050a200904061e0906050303070305180d020d0c03020102 77
    0x12354400d80306500c0104448075400303507490760003901202d50781503203480d05a88509035814203e000b0302c110001103401500031400844268010b00a40b07048070068005503013000c050109105085601c80c1c0110b942c424000a021030755541c80c0500d440410300c200b07a4503c408000c0d48492110001a000031640c03003403000d0304000c8258000384010501da01e4003000305107614170310006d8034103008018449202d07014404920400c581d01001451195604031600500144200c0312180301c11380c251000c41d0064001c000081c82120524407503410388000c40094030040044021a030b095030400041e070b4400036180c00041c04141b529004203500507450580400107600258401c06801e020600305040108012502103d113a54a0380200b00501c5110284c41c40e0b0540506c52110924881c050b400d0114034042020409060001c2521915645a142c03d4601003030000c214802c9420f40e4801e95211000340c0d441c00c0140c40f00007024101910540030f038a00682984006820140c03041d00000240001580030003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 89460990 1250 89459740 89459743
    0x3161403040303110c150f07090807031103030705070602011b080c0306010804060b0a0b0c07060804050601030f150603030c0b060603060a030803100b03190c0806010f0503100504150f0e0108 83
    0xa8000b903042c00c0010b05440b20450072032140c000c82d182010640502c03c0320000c05262801c60034421810030301940d0281c0e494542c01e80742403a150140254a912840060002940e0380070310300a0030310014101c900b401e070f855440b140380c45926004a00140d440c1d8244010844024201e61480f010504001c40350f443d1000361200da60100400e69410021154042014030416078454000910060200110952038100c4002140e0012a0000719803084080028100d07200c0c0f005a400303240e022004d04410b902c0c42c0c845010720404884d042da080c0e00381c0c44418844130843c1c862500118440d031101e51120030242040030703205000806290003000b007007007000078903940c07082800e041e40e0748a20b0b402d8480c0c03205803021030b007095150044902402c000041c4601124013000420b03131103807100e100388400705c40444221207101c8169000ca0110b503040200c00c510320b0080004c1c65112a1a991482d2003e94500006c0d0650b4451211005402e0081d0001e0200000045070440a00245840274060303502d0720030f07102d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 89462240 1250 89460990 89460997
    0xc0303100807080d0f0e0d02060406030c09091109060a02010b04090c09242c0c03060306090102040e0a0f1b050301060905031f020f070b160305090a0f02040b0f0d0602031614 76
    0x404012203000303401000c7c0c0d505079180b80c841d6006051070b5151031303c3c0c40d07003d0001e003503902044011800d0302c00b002842820b0381c050406108030300e010040c1410490b005104464121080c41c805554842c16800c03001c0c1c03210700c28035100d140140e00040d0010710b8801464100e84410400b255039190004071a09040550f00b400b01c1211190f00d103818841140800040205080481030710f001c41c07400302031100b0018140d002e54054642102911f003140c8030752a400c0c0c01c07440b903445082404e40140d000100390000c01e6200c01c801d107020204c08549218905100800d004a400000c0c01150004c070050103d0b80d0310010b00400351000f94010b001000380c0800368007030943d041074903d034501d80020b060034032a0306c0076060b21040c5501003c0000329050100c1c1d1030b4003403035100c407082c0c0002c1c0c500000902144000109074080700d4110807400302d000c810340c0034440607184d0840001e42001c500000f02c4815203810005d20103440c020b580040e200d0034640c0d1020b01d80c901d00f0400c80200060109c03404800d203400d0046 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 89463490 1250 89462240 89462267
    0x100f08010605030a090b0c130e0417090409061e150302060d15150201020a02010c0c020108040b0703020c100b180f07050c10060b0a030b04051b0f0c0303100807080d 72
    0x420340302e940c0c44c000140a4409000010a440444401d0003030410054001e00702c48502002c180d0611900c3c0c800c424107100c81250f0182c40c0341d00745112006601c5e8110018610020058404a0600850340303991041e07520b181d04010407141200b035450751010140c40381804040b4008000c0f20b03106d00c0e54001403001c2c015074100620160b43c074000f0102c24003950030040001d24041d4034100701103a000401900075041440500b000d0350a040cac6841702903214400a098140d0705071645921074035540c50300c1d440f4040003803c41c410f050342001a510480410050652032804020012a005180d0070910061100c0c02962440003800e03030060000140d00c020289900100f546000c64031010440d0050b85008058611500658a40a004034051548500801900f039040d101440150407410601044034000c0740c1074a02d0030754074180003c42d014400002c2c148100040886410300315844105400c5600030355280420307070301000040088420070302c114002441d545d0003502460b64a420080c0407078014858 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 89464740 1250 89463490 89463497
    0x6031b090a02070c08031902010605060d020c01141311030a0b0613090f2a03081801020a06050a06150309020306010501081f150e060405030703080708070b1302100f080106 75
    0x1820714901035069401e0240c04c0f0a481c0200c681d1381d240740791240c2c003180021855030740c55004644a0350050180c1c100700c440140040b403510558011000080d0032141006550355200e030422900e1540112015006100d80030210007280030380c0c6814925001d150810380e002c2e811180c1e480001c0b88007214000d0b423204096030400c040b582c1407a8668000c001001000304190400c086234014060300c01d16852140c201900c0b00e029088221003901c00b811903e1200805c0741c0c0041190800780d80e01c0410100d0150018011241d08034007595883c400d4400450b600c52a8a5592400704215840906502c4c0c051107141010881851550046500da15050007418140a500804030701c480800510050101c1c003d9a04c40e0612912500906401040d2141442c0010054a0106110316101c0200c40071243d0040040090916554801c10355070425081510049400d0000001041c0c1c0d2000150ac2800c034032203d1000ca0140b031041000203146007004c8404c00c610103a50a54083d003007202c40341540c22504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 89465990 1250 89464740 89464759
    0x32110090b03160305060a051f3f0c41060703020703020a0506090a141c060c0206010e04080a0320040801051914070315052706031b 58
    0x10220349001e0f01000780f070581c00d0520400005104000c101c05002d00c021000a00190b1280c0c034664010713a09400c1000340d40e40f04d102c0200f100c1001e813201c490b0f400058103080c81d12a003c000c90046141940c10210700701c0000800c407171041221034501c0344003601e0b4011041c60350b05c82032040d46102e04000d18041520f003050b18035008074910380c034000c011141d80051003140c0d2136001d450000d40327130110b910040340203d50b03141020409161903000d80d4040c0d50090040244a0b10b40207060094074400450190040207070a044008550211000f07041d05006150204180011000092074210164003200f0b0001d0001c0c180030014442204407800ca400610b00424645150441d100040c003514010000c4554002400248008190421441050419008810084001001c90646000c40307100480b03000c9100001743d410340245c0c0900c41354980e4980c42200d007912040400c0c00c04000b5a841400308801a1a9190900060030301c0da078400701c181c5c06080b4002401010348039180c1c441e4045031240b145038 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 89467240 1250 89465990 89466011
    0x5010819020105070b190b0a050310020d06030206040816050105090d0305031506030a0b0a0902090102030a0c0c0e010f080f0d02031608090d0c0303020d05070b040f03030e060903211009 81
    0x441c10754200c29005948694141001400703d0402c14174601d144c00706c0c508020110342280383c01914081290f5018000c0d020914164164000a52182da80409d04680e90040400561900c00c050009040c1c000020b00340890190102c4140012592003541004010001143c003901c0e00d0255402550703050811340d80301c1d1140014103511000d141c0d01c29070003100c040100200c2003031980014103031241c00d903180710359075440340000f10581c851483d019000d0b070b0081001b002050b103d90750141c0114050700d008920b01f51074988400c41c12000303070301060f8024800401402005002e108103c012280b5a0081050b8110300718081c0d200d0141c80c3d8003d2021500d41e00f0310051040000464203540c10082028089090f580740030900d03004540009e41c01480b13185045d401240c0110110384107a5044820758829a4480d0303560100340d0300c0058101c08268844180e5003200307a0411015018001150285440b60b0130404640e1800300b02c020441102d0351080d05006802080346082419a035000311f0108441000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 89468490 1250 89467240 89467247
    0x1e0d030e03120403030b0f060f040e04021c03050315030c01120507020a0f060911010908030405040b13050a05012108030f04060e0601030c0617010e070806040b0d0311010f050108190201 81
    0x4403480200744402d204104410503034503900612221908444403030710706029000744002030003a2968850342c1c040c10001801a44070881540750f00c0f40c4010002012511005150341c03001c41201d50803000b042022003841340c00008103520317425a903000d90050800c2103c9030b00080188441c110500d40c0b0954440208aa461003480031311071103500814103002c448050b1030304100401c41c400b0195035540a031b002e0314200d5885400c2c40021503420768003e41c14103041200b004002c20701c502500781e08c45194000d00d44031030326a000c3c5920030b21002c00001140c0d0714140070640c420325040000584503c00d069542d00003610740094a80054003a0b007103000740c1e5134500d440d00060611301e031101301d6846500f0001041101440e004000c0e00c05a6444a0300c11a480b2440030740940e0a001707200003100288000f90780c0c14882c1c1034156002e03d00074804203c507401300b401b00b95100c041c041c00f030f0001950340c101c4a00b503e1090003000d9080c04090400c000640c503103003005817101d20454001d40701e000d82030800025a0310 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 89469740 1250 89468490 89468497
    0xa0207050d0c0230070501020c0d03081e010e04030909020a0504030b09030f0f0c010e0313050f0117070e010315050f060a0302120703050a0e010614062208030304051e0d030e03 77
    0xb4018005100705002e141c51030304c403e1503607402c08070b5208032507010030594408122140c6011010b01240821050341d0390996284800419448442250f13100403800c04c1462445030f0300a010810034482c2908060800901d111307420b40218461600410441100940c841c04036003c50303070404000c0130991940c00d0028158171500b4032003855040c0205203001d00e8041c4e82c0040504405160080140200400700c80780c890081d0760640d06a400140707410400c604103400b0070000301c1c00514141030324602001c2c0740128040e081d140030703000640c1040c0c071102d00d58051013003c40446c42ca084910703500c1d03c1c24001440e0220303012543c0e8041c0c4004a440700c075081c080e4042d50744c0b400310705a019580c0c2c94a084010001e1004a44564081b4145540540d414806126080c2a900140c1c080408107000800340034180c1d1000710201001860810005019402d002c4104080c00d81c003000f03540c4d03c2c20a800c0441c0b6006021005283c4256100746901c480980052540345499450802250321101420010305500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 89470990 1250 89469740 89469769
    0x1a0906150f030f0d030c090608010e0a0b0103020c010606081006030902100302340308060d030807030b060c06040c1403060906070c08070b070f110d05070f0816060204030b0a0207050d0c02 82
    0x110703601424441d85c0e0076800c41c1d02208456500c6802850765000d048440000030b200d11b0810300c41e041301044454606801038030030080181030140c540301480b0441400c41e00150705c0b1400081300801400768010341c2c02c503100e000345290720b0305009044c3c5a0b000280c007805043c440c4024150b00060940922107087c003c1c10012403407510071b0200b021700c00c59449140c51802c100300d00161a400000e0b5603840c00580a400c00364255998804036614403505600401d103030034205501203010b00400c201d001c01086500e2080d07203e40300340112249046501942c00c90a40d0045101c1d07001074007040320349280040c4166020020b4900001015040d0508034680d2242c51009001150302c1000c0080d9140c22102c03030480700c019030743c4124884880f203016035112171410b4809000542c042000d13002094030f090480350014091002c9600c0c0109041ea0300015098082c81100c600750041070800600c080ba07040140c0c031010498080d480e0841d0356581a80b40e60b4409454030501c426907100e00295100c08000c3e09550 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 89472240 1250 89470990 89470993
    0xb130c0b2d03061f021b0102070f08011a040b03060a0b0d020607050a0b070504080a1b0807170d020d090e040c03050d110709060e06130e06041a0906150f030f 69
    0x41035810441d428035401154103c0c022a5101a0b400f445058503031240d6000456901601d002030712800181c4d80440c8004246046204120b00400e0148074407103010020440000002000303038001d0aa02c1c41c0807082e15a8070b100c1d514010743d5200c01c5d24041440303940401270000005a02c0000c0c00010b0031185240b401942156002c80c1001c20803900184c4448004c3c0144003d0020369a05ea10840741c2e4400c1c3c0c002c0000c0307900544101c0700012012118a2640e03a05552001101910749038014a04261540070464080342d5044890301e04405000d0b40490598a1016007096400c00e1000790060b4000e118414030a9584c20008007400904401803001d07513484020740b02d240e205801d0080c084000c8043c029190f000d84d080000d80340c500344c07082d00201c80e0303160702610190341c4000c1005031b10b0303002103002002c0300c0c0c07111517030f401e035550901c40c40780f2840c4502840c40c85040c88030f4029a80d03404c0100701c0750981e409101805080c40c1c1e1580001744401d82221403070890080710011a0070807061241d1141603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 89473490 1250 89472240 89472307
    0x315060302030c0d11010c020d02040203100e10150c020102010e15060a05091005190e0c0403060c032a090b0d0f05160f0507060b060310030b130c0b 65
    0x1005515000541203074002c50803141c810301294100310703ca071128500282a51840044001c4079400360003d41312443c001011190030320000c0d0081010f0780c1c41182d03030506004c40d041090102c9400300052641141c038803440c1d06031040c20000102030402019001c0c2c0c05000314180e100c81161702c00d4104403800d0030303042c040d15200081c0c68108941000283e6556220300000034011070b2508005a42600c240081c0c001d0f100e500c0d160809001310340c45280f00e9090b540042800124006128945050203030142401a5036100c0c07940c10900111340c0203103d6032080509011314a8181b03103200203a9041003c5403603814a00d20104c2506071034104043d80900d0394103001041c11075070380c440303684003084006030a40203210507036641703c1c9180034150401d40040840c40724a01d101d0414491405403410030702c1a40e0002c1d00c21258400100320350412125080050b40021080c010484100017060700100110500d4a0f154000d698005a07481d9900a8022011004c5904079000c100c5802c200e603500c080c19845000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 89474740 1250 89473490 89473523
    0x70e0c0906120612190f0f020907050306010806060304030e10030608100911030a02060f130e09100615020a140705090c04090513020a05060c0f0f0f010e030a051c0603 73
    0x2a400320840f64035100d0384113110481e42c41400894043c2c0c3d80c02c400062000400d22030741e261300b2000007008040c0c490050f440c40250050310342004207400307982d10303403101516807900314001003001034001d061600402c001d00a00001030703004080c2c90440e1404607111501c24651182c120018041c070340c0010801c0c425008240d140750581d038010392000f801a020513651441a00074180d99410700d560094000000300001c0d11028071500113400751907070300203065540903500c202615081206480c601c0c0c090300064010121054544909001042d40084447d072300520074a02035250743d501d540c05042d56001ea10701c4a51400d00703001030700141c0401801d074003403420114a81000740c1c100d4042d01b141180340c0b40124408404980150566540c010036003485141007500f4007800b500f141080c0f00c00b512645e03991941081050018080e6002420014036010324035403103050035102446003241132500208181803696038000d044400680419a002400e42100e00301000104000e510180c004c03000b00c840d110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 89475990 1250 89474740 89474767
    0x30d090501020f010203010b0f0a0203040906030305041e0b040501030209181006120513030e0409020907030f110408030306060c0703080a0c12020f07150203090a030510050117070e0c0906 82
    0x2515030a9003101c1692040300250360807444280103045088070b003406600340700b02c1c00c1401420960064810f8904041d6582c00300d000369a015041140400c1c00410203011489030a4060345082a840b4a034504451600107500802d10940c090300d0304041c1c0008090080b92a404154003400e0405101545246000008000382c3d9855000d4040002d1240d01c00d465840103a00030b0602501940e1311910f03c01100c2c1e54107072900f81c0030b104003540281e103d08004c80540e84001400e441108561030100782c0c03007003025030300c0e00704d401c409001c1342102c1c0140410f00174040c3c0001035a81c0078000741e0b140c56403000a1050240740a00f0b0303500050a65800080010049600c1403103118040d204007030364164641000401d81c0c56842d140d0700805940c2c4104170402c0809000701e03082c113181c119401520b1900090202117440c1c010183c10a4825901c030400072440c42c100c03031013140c2c018080d50186400c0c2481012800c0d844101511803c8160014a0041054001803100303c0b00c2c0e41400078081039940035410480d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 89477240 1250 89475990 89476007
    0xf040b04030b1305070501080711010e060a060504020c070b130f0303051809162304090b0a2c0402060405180f07080705070b0c1b060a06060507021509010c02030d 71
    0xb220540e4040000c41e10210310070700030580c06580007018261003410302004640d403010041001c07080015000c20b1414030344080c41800309001d500030182100c1d29200c028117068880765070040b4003d500c10000882d081c1d0700480c0c06c2c41521029900107a6821428803244410030103034020054030103199000004264001004220a824401108030264180b400300140c904086429003d19080320103940191481038003004004038071000c20042c40301b00b0007012400c5070001c1e000b030001e0a51300c400a918504d01000c010005101c2e24141588074500280d490408011003000c2c8010046003002240440d030b243c80580b400390402030110580c84401c43e80c24254500142d03003170007090303103010701048000703100e03001c034030b110300c5068450625158003035580c50807882008080a250305018894034044194a542ca030881c120020300910040c00c24040740c5003240e806a03c60020b1160030441a0300603154051f5840c40c01d00800d4200d80c40b43c0b880c4005a5000025510096040c01039400c1c00d0740103604203110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 89478490 1250 89477240 89477243
    0x2070203030409110717030105010905010f022b090905150613030501020d0212070c03021b0f03031b0d0c1a04061401080303070201060e04021c08070f05030306100f0c0303020904020f040b0403 84
    0x101e260710506c242040455103c217000b0385000504032030080c0710355405404d841c400c2d866948100c490f84035130007405402040b07542c1c20580c00a803820104030940c6511001c400050102e85a042145040241c080c030000801e0710700c001c0c0200004074110803060419010b1b44000d50300300000750b41c0d40d44c0100c1038800030b61000d280d01a000061034003194240d0702c00d0b40f03031415156164008101200b80d168541507807001000c001c550107202c1c068810000d032014006484003014840081c401e000600d540d1504200c100240d1b03c0030040101182400b00b03041c0c1c950b010701000e0221090582d92100d041910282c1f210211030f041c0440b00c0d0000295802001005501c035011130b6008211045d1500c4406454141c19500070398088a41d2500e0344400b000f2840240039580f19a401c01c0c504003c503600d40c1c008080000d410347e10303500044200803150034984a060000d0350649003040c0f0004403407601410a9808080c0a000c160380841e0040042e100d030f90440383c40c0d880e0340a016441e80c0e901c0c91084c240d580103000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 89479740 1250 89478490 89478503
    0xd18060e030315040509010207060207051e120406030507030e010207050d02060105010306060e10020304030b09101503020d2a03050615180f25110706081009020702030304091107 78
    0x2500d000068003000b624041c0a0001c42c0980b210040010040581000b900d0280155400c0100c0c0000a130076100504034984154040e0400000c0800d1300382188910040c001c28582009036040017507030080341101c05850032400d00040c3c80e02d078904118000d120b902640c400540c4001210000e1080005410014001c55400c41c3c0302a030702c0b440110180c40603031090b440031900d202c0c0c14240d246413184021100c2150780c4100c07801c16650351114030352400261b030240b00e0354100040e4100420194041c0380800315000c1980041c0b107203180d001c15a0190100009015203100c0b510780f03002c152114844c21034070180c4012003002d2540b20304241e5150303c000d480c09000da0f000c4149411007410704070380160b130b0b1705842f507103000c00c999400a1b00d102d03d51005041d2140e40028103a40700c5104407007134505904000b10b42d100c0d0492910324400e94908092504203a050240b1041044845400e514819007698910030740540c459816202080c918000c641120761018142046000c0c052038103005085c500b4007942 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 89480990 1250 89479740 89479751
    0x405010603020901020a03050d020f160b060102151602010b09091501170c01050d0906050a0f0c1e0f05040509040501200712050f0d090309060e0910050d080d1806 71
    0x940491085103c0c0f20302603080800040c010070300a6024040f01540c10001515286c49510a00e200e58000500081e03030303154040703d00e4144280c4400090b4010401c0c0010145a10303101419224490014051004520400302510005100303401c008080c5c0c1c00502644410705000d07500c141c03554007110302030000c004082c00000b185400d07010144507016002002c0d00030070031080d004442d103a00c80d03803000c4c010319181c0d08180700140d0a4401c0510400401c80000361407610400c1400135a05803014071005c10600f51010300b0a41c00f9800d1213150b941160800c40c0f00000504015106405941d000540c4851035004000500ca41074102c18084560144040c21807403101e21a5617040c000d012010b809440c811180480c1c490003440240401c0c031136010014200710380c410405080d15648442280000c0710001c003045020340000031514a007078111480f0b0b049140180441800c0c0b0748503c501303840381e45100385903414810500125040b000395000300b40001e50080f207403802000b6039048100c440c0b03482d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 89482240 1250 89480990 89480999
    0x9040e2a090c03060108071103070501020405100e010801170f01050f0a0e0f1b040e0f0a030206010506040513050705120405061b030403051e0906070318122102010b0405040b06040501 80
    0x450300c24442c000c0380a00c581540c459000455101c0c0c802080d21003408503107840054032040070030181c01c4840c4140c002581d1142000184504406490322103000d2248001b209852680c100e4800c0c0d041d20306003075040c46401e4851415500d40f800d02c110203081075181c5028001c910355a0181140301d40300d660001c3c01066a21030074295030360311904110110341c20141510ac00e611000f0414504a08010000300312920368100c1c89040641194822104c0d0b4002000c0008158050241a0040400b101c18608161034600810410304040c500205001d07541c000040c442c40c0120180c030040e2440000269482ca018644141c1c5c1301015a0000c01e00d404041042c01010380000071644207503810b0b03172501d003070180b0002c08208110492240700303203020302030160382c036541c8400c409011034500a41d5803d94031080410101d4500c1d2450b00081e04040f08a03904a0200b4003800000c01c0c5e04076062806250310401c0712049006008010302c5075400350400082c0000e00404440507805008221000c00c0187daa6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 89483490 1250 89482240 89482249
    0x120219051008060a0506030f1605030610050918041a2805070903020316090e0a050601030206070c050a030305030403110604020319020303040b030a061a04030503030c09040e2a 77
    0x140c0c41141d50110880c000c080c0c1803880ba0a8480d0031007405080c0c2101c0c251602d00140407131b0000c440580071100300104126007048035a5902110030400d00780b46145003011000300cbd0104141d00350350018440c000070300d8040da459580074500da01c24030814030b40d0b05051030f00d0131070303441c1d940201c0c207010140040000ca4068849680c0d40f00c42d2011800c0c0e41c5580240c43c3c55070802070440200080306200b0381000c0040540c50501402c4080c075a0b00b8450060141031031050301c01c03222061a10103250b4059602c42c0001800000c0680c15a0340403035001c1c0d11403010b441c080c981400903030450f503000702151900100f0940c0010196000d030b4481d8a0b1111040075080286686881c11200698964030075a001c0911801c00b00c50b0040301d0f8000780c252460241c9680c0590300c0f550040d1102191a030b07507101e00304140340000902c04440500c000000d40b50510315210f8036030301c0c0800790045801c2c80c0001003600550340d50703074009600104040b050391242420f41c600c01e5a40104234402405054401321321854030b140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 89484740 1250 89483490 89483539
    0x6021f0506091302270631020906040914100e041109090a061d060609010f1406040e09070303030509030a12020702010201020c06090a0309060f080a0f060b041202 71
    0x41c054100e01c1c0e851081039901000650f100340c0e00400d504000c0e02c4000020032404100d0410440b60001c40d0910000744000561514500014050b64100300400034011400713503400548030f2003025848000e03400018119103c0c4c2e03881192006c0c500f001c800703024040582807901c903140e5603590301c85840c2c1e505030035071203104202c5c4c0080400d060f1080601c0d02c1c1c80c0512a03070740c104241604442c4804170f6584e812040725a1030403c00710203840721359100b070500000c002c2140e100c0f8060342d255241e5498111110001c5034580030b410154040080d124109032031700402d9030000c19440701101c805003440da1030704d07840744030502060300001c4c01c003400110310741e0001085503404065569003a210110454403503000b508809e00490465408002e146c40461003004024000c0c602040a45a40c0c0498640501007400c51340c0030000b0f00c000e000e000b0200c0341c0c000c04010f07030150500c030340410940c1008249000405498201098040020401040380c1c00301000303c400700c0f413095423a48148482c0c21b001000910 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 89485990 1250 89484740 89484751
    0x501060c020102030d0f021b030c07090b0604140f211605010c020103050a0f0507020618070f05060d0603051f0f0204050328020603010306021c0c02030313080405090106021f05 77
    0x91081082c0c1c5d81c1101c481d400810020140701c0010b0904e1420121049010403000c10f02c812507102103a00c0c01c1040c010700c050070040100c220204980040d480c0814004c1c080c034426055044800340c05050030391624a240d185203100208441c05042c804040c4407080482c4036242c82051050800b51400500d01940c010140c80050315043c0980c41183d0045001e08001415111030070f8803881a900d00d44628005c0600801b0700fa00a0541d5180460b20706120400c5019100c15944c0106010482e600c1c43c048540292401516031940d50103005540c0740140115074001032051280b40400307000a041055400c9640720000c83c10321982c032942c40340000740d0140b03014107a41a04041000c66038007500420032224400e020480c00019000c0b900040c140750804d074001e40349203800254030b10145440302c401169102e5900000c21081854660003950317800010045e01310915a05221000c0c0441c10342514000c000c024400c200c0d668441c0340082d254400001c6e2101d8440c05281001075071900d03402914800d6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 89487240 1250 89485990 89485993
    0x51504030c060c082a04150c0213020f0412210e01090b0309280c0e0402120102070b07030c050d240b0c120a111005040506070e0303030406150b0a030f0501060c020102 73
    0x50818801030141e800324400d00340c6401c90800c8006154010007c070741c42c1402d019110046d07603c002d8010b0041d00482c0d417012115051040101740d11000c030607816a401d6440320441505118150b140a81c140e40c000c0c003404650700c4480481ca20a01d51085054401c1042a0303942109035903901d00400c182d0005450341111768000303160309800000b600355a0000c203400340c4030400380c543c00e80d1200c5010135a1a0484500c0460040c200402d5041c22206503034032441100003140b40480c251500c4807200070280042e005c0640740c51007000c001e4403500680e405004601c1c4104150807003080500608410210f1208010442c031500240d07811020702174803017038613060000d00360202090640440683c401a12031080c0444450300407001d8104100c054414040441c000800e0305180c101545031150040c19501002089004082c1c0c0340c80110070f0b0b03030f0404e500c0038001c180170b03103d40c80015641201d5040405282c401081080206605410222020b01440000c00203a40c0300c00c003c548141000d60041d016 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 89488490 1250 89487240 89487271
    0xa0605040e1903090e070503011e03030516140f0714100207060509030a062d020405010504030323031e06031501060507030e040f06060306050f010912051504030c060c08 74
    0xd000400c1c1c40b600520038a00003030104d40710745100d5504541903400800184000c401031019002401481020b0b00b221081022914555600108507100c1d040b050000e440c014100c002c10001a2080c080c1e03d4000ba8040d00d03601036000d030b0309556900e1a8801c5407140c040e0300038407203031504252855044040c15640500749490408000b034400750300c1201482c1d01840354400d2040401d010340b0590419501203001120021080c01c40c65012408111001c101a44108410441c50380c104088508881d81424200c0e01c0c40701d082c05454a58002c06043e0b05100030000030011300302c07003942c4148511b422119480580740c40300d034145607546040c04444013801c138984005025140c000c401a0142c00d1003450b000c041400030303101141c141da0300070b58801d1007192603400a005107601409058054041034030320365000045800004e103640840c0c815205c400146021306000d0017014049654043c0090801d036400342054900200030b42d41d09201650f0051910070f081403031507c43c0840034010114100d24206 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 89489740 1250 89488490 89488513
    0x14010f0f0e150c0706060303030c0f2c130504050105040c090c020c0904050f0106180c0809030711120d080f010608040533091506010503040819090504020c060a0605040e 74
    0x40c4004098140f10343c40f1400d100000005d4042c3c090706010b18801da0b03020440d0080a5005060b55090404240c14001004031610003503401c611490741e1811801074905916011001060680403183d2101084505020030003051050540009001e2445080200d1449a51316101c00855055520b400e0043c1c00c41c4400032003074035040f404543c04c0350250b0190b80c00451110402800c6a8003a4040d0000c1038800016911035201c600c200f440411701801c09104c1703441c02191070341d101e02c11004c005044041545070b0240b903480e100100d1110340c410404031401c04c0002100070380401e904661101c0108410000880c0e42845913840b00d009076804001080b184180714034441134a4046a10301001006081c50360741600e110340304050040ca400e102602c00b00c0c0456030003005000b001803007181446010018003000a5018081780d551031075180c9108000000c88900b181c54031210b50016500500109030130841c180c000c100b0900652004804100b6265070703006000596107015406130f0035400c032140290 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 89490990 1250 89489740 89489773
    0x702030a0221040b07030f0e010513030212030c1005090c0604050d03031a030a080d140603060a0c0e040207060e010b15041404020412050604120c1502090a0314010f0f0e 74
    0x200800c00704582c01e07080903210840c8503656040070a040e030000c1c4071001c46111140e000400742000500030700c3c01501d4241c10714407040340001a480000e0060440180e9110080014400d03107080c2c030f61010a40d0308080407041030310054841a40c5800c6d0074000e030f600345052032800008841c11a00c015002c081a0186914154020420400e1403041443c0c042a1080c250340c09008840c406445445d000303844031100103844045400d00a00c404078504960240400b075640001c2050340805c050a020448405a1008645081d0080005600326001090710000c115098008080004049000308120200c0388100b0003000038440070042400c0c8200000c1c4404030203143c6c200d01000000e07001520301659201e0368034020b9102841070710542c0291b007d02040081e000c00c0d10a01083da0b00e0907420482c060348940d900020801840b0955550014880c1603588030300c0d4644000f9070700074001221940d0b03003034403940c0603000d00b40a5404c4280f60090780000d01c2d43c00d101d5444078945640c0244030071100d102225 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 89492240 1250 89490990 89491033
    0x503010e060d020a0e0109091112030f0c030706140105180c030703020a0212121e0702030913090203070f1503061202120a21080c030f0708181e060702030a02 69
    0x50b60811015880403445c0c07290b126400340282404080040c440348141403112149400c8808603200e284400101401064004180c0d220b5240d510001540e58105a4441d072039481501e2008100d40d0030710041085481590840a0484070700391003561010200c01810070b0450411294898103180c1400070854203840303540505120752103401120441802000354051540011005041c403540150800050dc402420000b0848102030700c03505190610b00c0e4041c0d01da001c3c0460341c500642040419003107500c1540c2002d000c2d550040c00750740744203464680920754015940100341e18200103140485421344a44070704c00840c2d014903988019001e0590802ca5a04141100340095204040444022501282d0540303602003651440a045000f030150107400c10074010301ca1002c1c02c805004008500d410196125030080d100c2c60202c9540d90303400a610307411965a60f000d00c09201e0703030784811a450081782590b5120424441220559640d2020481c0e40e4421841e034500140c10440e220030292400c40202d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 89493490 1250 89492240 89492243
    0x30801030b0c0418020304030e0901030b060d02040b060a0e0307060f0203071203021b010c0e010813120203160c0f0f080a03030b01030609020c100c03200702040b040204080d0f0503010e060d 83
    0x700389000e0f40d0306082c01030805404c01000308950700109220803d0f1304007080c28032041080d2081030040d0302d15154403054410080010b801101529100780c2196940c0d03103e041d030b2503001000b803500da2900d6040240b88505089001e8013038840c2d0700c80850014040c0341103001d4045103500035407070140c40d650350303144c2c405109500740d0038141c00b03028050442c0d90b044c0710300c1e99401456000180340c07031280320010441d041c0c2c0b4034030b58180034202043c00380b00c446558824403065041100c1003288003050038220310710b118140c1c448020403481c1c0d83c460304010f6032009401c02c8580d146080400291640984c215002e0325109121075a8400d14000d8000f0340644c100d061200d005050000e03009603212122010b1764000c20781c21405810840c603402064401e88294460924513180401400d904418500510a0109a841c1e41543d000c2001c9086554641050304400805041592680d030356070384180d941c0e145880b05001107600158102080c42c440e00c2540d04032038060f00d030b40710300e0b0301c4003000c0c45400c1160200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 89494740 1250 89493490 89493511
    0x80f0c0d050c0a03030c05060708010e01090b01180f030b0a050601020a122a030219111912060c14130303031a030a080307180302060f0f0412030201020a0f03020304030801030b 77
    0x102c00495560343d9103107002540030f03407140c603092030080c0b401d40d050410041403801071290001c0144200c80c126034071941901d65405001a94003002c0005a400d0394240c2c0c04024180c01070b641c046081c418200705036044902c1101e0540d00ca48600d40c0c40c105603070341104c103e80180d1203c0c58150100315841c0c0c43c1c0e845c03403a05040c5a00864008a001c3e00a03001e07030100700703410500d0381d03240104065040042a01c00300c0c00c02401382044440395161008140310464052203100f48150502c0c04403a106061130040080d2101298900b402c1c0c42d20b0806001d510303400501003845250b00000e0103c485045840050703000c40c4035a036250031680d050b0000c00401903129131640020300c09085036181003044040842c0540725640d00c07880d080400030119400034180304e0305452403250820050300d941c001d8400604c2000300d00b50300c40002c846808414001c03640400201c085600e0203000385901907005107018035090f45c4400c40b10310110019001c0c0c4c030083d20001c00144c00c0382c00401c00301d2410307142103400009820 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 89495990 1250 89494740 89494753
    0x8060412210903030b0906010201090203060402042003041211060106050906070305070602030f0a1b0210020d0e031914070b150102241501020601061b02040b060c010b0a080f0c0d05 79
    0x7441c0c0403aa440c1c0070803004a40e4864029038035141c5019159400300003440240700108641c0c0c04031b5200c20000d0f01c0240a43c1c0c5903001700c000c407016080c40c07114000d41503818640320302d058203290036040b0701c00b0050f01c045007071030030001402000031900d141a1031290b100c00d40340c00b017180241f0070306a00550044d000c02c03a0502046001400702e000460044da003000080b680d41c100080c02d4070840380340641c4520408046030820b23142540115141c0d281003800540103803508500c0d5a5200589400340403000c082c040010855011652003145410007507080d40c030030640a84180c020240c51140100142956000400045c48090404200300e402081807042d519220100300d44006400315200d800129410b02004120a41e0f0340c00380f40c40102d403000d02c0180750b05c0d490401c019010302444001403d05201102c010f1055440d5074102c0c502090000d023565035211140082140280705030855248641c982c08000240210001040003c1d44103010250000540010412040c1e009081c0c04480310300880 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 89497240 1250 89495990 89496047
    0xe0711010209150d0e010501081b0f030d02030711040b01090909060b1f022506080705040b21060f0112020904060506130e0f01030b0103170c06180708060412 69
    0x403420080900f01c1c41896854501004800003039406405407072816a00d84001001055000a41c00030a508115004a4520402d0000c500e044226180c4542c2502c206a0320595065000008100c140d018002c3c2c10b0b4000c010004000c10350f0342c000401c82c0011441c90050120304015445400c01d80e20034080000d003043d11001050010710200708040c038070080301501403002501440600b85044c0c02030400046082a110006003140b114001c0c00b01b0002003000040401d401b800c103c1d006005140c4a094980340c42410401e0094254449e040c84061481c0101d00141040c00070354500030360585a907442c00c0c441e010418020340102036215482500d03143d00041d551207040003080501c2186406101890510350307000c000f190003410200581000c10700400c0030454030842c0b54103681c0e000ca41169020a0141c00101500075019808070501443c01400441d0b02c4180c0e130a0111103542040d038844076030b01d501954544100f2180500902c901000c00140c1c0c610441070604c1d0300c0c078240c0e1070341c4641044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 89498490 1250 89497240 89497249
    0x80a051c0e040c030c030605031203180718020405011e080109150b07050109020120060112030507020301050a0b030d09030503041203051603020c092203030905010b0d0b061203040e0711010209 84
    0x83d42e001c0843d548080d45c11141d0351500035980603110903001000c511002900d2000175210090104407419420b805500508405001c20801800c412280404201145080e9802540107120722808644158006034120f010100c0d5005103a0385501c40f095182e1800e03144002030140d9444824240d101c04802103012005280684040c0380100000260407001e4070000d0903542c044940e0140100c0580c5d498a003001c00001c0d00303419140155100c02480c4032600c0d0075034140c001c0d0300c1c0095065091038104480c00c0000d0b4080840c1200032001c4038180300d6240b8003510a2003070340c04090004d1304100f105011281aa62000f10305c14401c2c988545461854005a6401144854100d00503004103541d104c40e49070120380c031a04116200858441d150303c0c503e80c40c0360204102d60080525807554205400e118082d481800403510180618992902c9032801104111048414078403560800100c8105803c000050381c081c2da0102c0c9001c4c0a80c7c41d82002503840011146840c14259000c00c2003c540740c84c3c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 89499740 1250 89498490 89498501
    0x5030a0c0e0705130303050c010617010f0f11070b1005042a0504050a050d03180b070203060f062404030602040b0318010902091302040605060a051201080a051c0e04 72
    0xe0880845101c0c1003603007404a5400140202007040f1003801082581d82001c0d070241d080b680e0600340599201481c400302409840f00b030f03001101542c244030030501801390641000c182d0589035600ac1220300f11022501d42190262001032603906c0c82072102031b000541d4040c0340c0b5001256503c03030700c02e07440d82e80740000c042e0f96003e100b503600d0880c88000c0000c4c0702860407043e2240c00e02410414206400c1c5404222a94518400c0510809410f1140010f040c0140072101010303880080032284aa2103141ca14000da20030541280244588000a4200108070b03010901a00c401004d44143c2111a0350b0440d00500c1c0107032070040035104001c00030002d100351004100400d0100f40c0306445e803614200d580a8050a0701000d0a0f5904141158006030b03550792500358001c40c0661103145103100307400820010031590300a11307081200000c20f0400c03e40c102d4050281052985d91214103a82c0342c1d070010b41c42d537841000080180d44240c4d007490030141001d03101d0102c2c030054900b054040d0040c4c00003e007540c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 89500990 1250 89499740 89499743
    0xb01110610030b090319080a09020a090203100e09060f071e020601061b1101030e0a0602130905060303040311100302160c050907111002130b03010603050a05060f0102030a0c02030705030a 82
    0x20011072007001007000d4403110b00e51107162000030358140f00c81904110481c9403414282c8082209803c00245036000b00ea005d03482007031700a002c54107426190690f10009610035107014545c4480c503840002d007180d801040c10710030070740380c000b5000545814801c1c0220400181040c0203000001c000040c00c42040e071030044100d24254024801949881c40c040c21408001c44150501c181007441c03240403401c3d00100c006d4a840a1030002060052401c0550030030b07086034001810076000051400c182c142000521060b01c0002400704000e0302c0390001c140c0d8070312540c400204811a001440e030441c0c645044400105c554604025240c461008440301c030100090108503081c281c002d40501040c18103408040d444911410a05496120501d855a440303503000c0c07040503a5500000e0224640700d0041042d801043c40c02d10305612561220300180281c0000c4804800041c94440011242d14200c1c15458041c101a0055490540388840c101d403180c00040040c0e80520845d41d0024240d00d00300b0800d00240d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 89502240 1250 89500990 89501011
    0x2130b0c01021305060a020a30020601050a0815040b040201050d06031211072d030b180f01051009020310051e01090503010501140613180209010809150a0b011106 71
    0x1e0020a0140f5a09207403a08514002e050500c04244459000901d5081d5030b40c00180310050702c583c0f4441412082d8001103905200e0340b9038600c011801c0d4000601505880c801c840c403c14454480f0405603584401d21248503c1c480c620000c1000b280c10094030b035401034010314216103448407940182c020385106906c00c980700740c81d014600440070b038000744004201c3d103d50060480d091520f0306144451001a002c51984c40c10710b140071082d24200d400c817800541e84a03606290510b80b40c0c4401c2070b03081940a480d045802000101e022034a01886070500c90788400c554020b00c030303042c024604001d400043c0100c480714540034000c221940c40107070304000e021382a03404c103440c141e210000400c004040d0380302902070303814880144001c0140b1210448101415984140c503040344041c00d02d81c4850760713030121098000b6003080700c0c0c8440640d0028480e01038203890361030880e00c41c0600983e842061841500d0300d41ca0032070101e10b0005058000010790034052502100360380142010609120047d1403c4d07504 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 89503490 1250 89502240 89502247
    0x60e0102040819020d1403041a09210d0302160b0403031b030204060207060c0203100603051608060c03130201092403060605120106110f0105130501060b0319020304030c15050106120903020703020402130b0c0102 92
    0x7c2d8600115030185a80102c084be02214901e10304071036403600b40f12088814150003040c56a070f40440f08a00a8090b0780113240442d00d400c2038100a401443c24000c00e03254102c52002c0e51000078028001ca604844160b0700030701c07070780f4540f6604071038038940c40c2c504070b925010f207282040044c0700500a4002441c001c0001d042079201071080f0350008102c81c0d01c8411590400d004000c00e8010b10420303a94040c221312105038000c1c0341c3d07100403a462180b40e00016100303104442100e508542d2003201c40d0048505d038a0401045844290589450081e0407800c150700e100e540051040500c500b04542e8281c0540040b1082011104440c6007914001c40e03848014852074034203002482424003904000b000040c2880b4554201903100c3c010a00c3c10404d003079015500040403030100340c41107112440454100c0024060b241c5215205c1c0702502c0288036140002da80706102c40c108501c1d038841c00010b03030760680041c80300518607424040650007484000b860718003408000031b4030516800c000d141800c42c40000594 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 89504740 1250 89503490 89503507
    0x151314010f050306011a070b0a020d0510050d12022e0b0d0816080714030702040e010501080a02040e03040e18010e070b12090a060e0102040819020d1403041a 69
    0x102050141d1000c0d002110600d000c1169403000f0441a055500e40c43c00200300d00d00c01130030b16031144680f40d00205220100e10030408401d181ea0301070a88010b8182003404182c982318200e203822000d50041d00d41c17200401da2003200084840060b00003600d41401540c3c14071041e519402000a4100d000c10b00c900707501000080f02042d54850707005440070460301031409001c1d54880d5070310f600034051145011183c0e940c946007405a01c905566500c0c0d403026008000b1140d10a0b001e880c0d0704900c6049000c0d40c10720407100e40544060045905031549040103020040e202e07005c000c040c1c85041150f440f036020802003c00c4c0b030111080d00d544a1f91a031300b8411008014a83c290b402c41d21054038024013070300040d00610094542c0d40480384000e1000780d8030000d41d00c40d804040d007400385440c80240000c2c9840c6c1c04030484103041d0060300868440340c1c182c550401012036040c6100c200d90f2002036010781050b420b5000155000a520003c02142c01200c8c14207850308040c110042c0d1200c0220800000400c1c2e285 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 89505990 1250 89504740 89504771
    0x6010807031707031b030207050919050a0c0e010e0604170606100302040b0729043203070f170301030302100605010c050d0f031806050a050903030910051513 69
    0xa10494a42c07403e00d060b0141e1401001c03011001882c20400844107005824544200000000b504009002032814100548131800c05040c8890150301d0b00c1c14540002c01c1c0e03080034810b481d1010119183d9984169220b0700443c1c1c010101000d03158040c90600000c15030700c241074005a4140c82d240014044c2d0b0034440104052204155801010580108400d0101c440c03034a0544240c0c0b0307400710740261498001064400700f038001840c143d2070401d0801c01c01091140d900c03800c00a22031100c050310304001d5542001d100d1918118400b070b00a41c07081043c0300008190410486d0070b240a450030000202c03900c05915102e91081c0d00560059204845000b60707001148104002400242018803a4002e25903889407101038101034003050140c25a401c4272018041d400c27941d55007018045541180155280c031200418081d1240d9a0382441c001c00903141c410000300b00e074000c0840000510384070010200c180041c05c4024403864480c43c407100006d071192203080b908450041c03230b00804103d801141c100c50707 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 89507240 1250 89505990 89506013
    0x60409150b1801060e010804150e16060507020607020d020f0d0506060901121109070926010e01090308040f0807080a110111030105062a1905010c1419110601080703 72
    0x265142902d640042100c07030703005510000005002e007040c14403540d03242002d0350004201c40312003080c5800d1010741045800e000c41c0321842a041512071942998480104503054010880d00941100b006c00082c0058608141d469054030310041c081c080d001851400f01d01e1000b07179084101c48a90101c01840910302c0e04128542c058005809030807042002c40e1146440180e0440f0003601035000e400110719a00d00c02d07810070004c3c11602124810409000c0f8032106c1040040e0a216025440d01120890b9505c0c180580640e9503015a0b0303c84aa80b00d40e1202410301400c6603089403585020840d180000d40003402408000c08140c9071581c4543e411400d05080d1100311400e80000e01c030030401401207951760001d130f5105026111155003d0100e035481e09001c0480712001c2081c6104007101000710074600101c00d038995120350003d00039404c05004c02c0d00c80e41480c02c0b0040d03d0520034091428410b00c00001509080c4840c44c5c1a880f8406480143c0d04010081e0080112500b00020071300510900c0401c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 89508490 1250 89507240 89507269
    0x60a080709090504020d06020a03150b0c0f0601150f020c090a0515030109021f26040510051501081302090103051e0309060703180b0406030b0406140901030b060409150b 74
    0x3e010f24502540001c4482c0300030304000301070650100d61b044400307200350f200132044100e90400e84e0505072104034090140c2c0005800400d03d200705143e4662820001c01c4403030480d20705140c0503169400d6041c0030780352096410220740440c4030301c2510020700d60b59204940e00540780e0b40300008084c00c001030440c036540c500c01d5801c0d00a82c10600050010303100c0e800c030381001c0e807015842c0d00400518180103c41190010300c0031811b16141021112a145050007002d000314455421160500407042c1e44c0c8082c0d4800f110a9442000702e00b00340e5246501130100d040e8000d420150040c0041000d500040301c1440c00c0e001514a40d0010702485a01c41c001112900c0c10700c1c3e060001c5051450750000202a881070700303801410000307040d1551384001482c0e048035018115042e4070580b00d0742ca40b90010020042d4408041c440c0e0305103078000500c80c040f1809015620405002002075a0a41d200c1c00041400901040d800c41d0b03503106918007098000a0480002c21000b10115012030104108051044071048 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 89509740 1250 89508490 89508509
    0xf13090e0606060904090c0311010305100b04050607060b09070207030c050307050f040b060408030304060e06070e030a140f0a050a0b0c03060901060c0516061e03020f0a030911060a080709 82
    0x1110540d424000a0169100b04100d0b01160340301d0251012501811595200404000708080702008220b040e00c05141a01c500b0781c0c00f00b00b203a0701c1011526175a54540310b1850a003a0400003480181001402056200e010ba000810040988400f10f241400103c50080041e00041000c0c010401100344050043c0006c0300245080c90400001a8075150f4140a0900c110740d03c80c08414152100d03005e460003800e01d2001e9075105e2809040c03d402130a0111100802801100000340485010304600742240c0c0340a001080e201850355a040814034050b502400c40388150240c0c0c0d5114502000480c0b0441c2c840d401500e0201000d02e001d0140141c0a4061007040c582402000040e4485490080c111161860100202c2d802800c1c02410040d0001070034155000c079400c045400f98120030310400c03c082e450b6412154070a121811400ca0240180040d6003110400049210034400e0b08090341881c0100c580327901c80120007002560603840f00d8a041c02180d2a0010055010b4108181178003c141114 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 89510990 1250 89509740 89509751
    0xa141e070b09040b0d0804230a06080403180803040603020715051b180405042301050c09101107030b1602010209150a05070c180c020307120c03020307080f1309 70
    0xc03611106400b400055a000d07036601c034034403440390340c036030346078240940c0c002d600b050b580c42d01c5895000c1520300d0750144611500c1c0c10003240b85281080408001102e80542d01c01c192604d80c0d550403a420100307958010b0041d4000e0001084441003807004000814803510b0040c0d40d80c2141c41c00a107211030158402d4552440c1200f0082d41086200070341030a8000e0702c03411941d80803074010703119801340c000c6852900207242800300130800c000261200707488001d0700340015030107904404040c00d035031046a0100a0550a0001c04c1c40c0d13080c400d40d1101000340134200110003415550390307603150031441d41c4280c80c02d050381c0d8140f0400c6c000040000c010b4900c244000e40c900030408003c039110f410078036200c0380c50030340c00241640d0b414442c0050354580c4d03620442d841d450075a5a41130300300c0c0816048441001501e0103580c1700304580000201c40304c1d41d91104c005c0703034040307070115041d2102822500d0a0f0300390b000400050300000c0b84d03030005200790b0880c60400b94644502044102c0c64001c6038100045962400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 89512240 1250 89510990 89510999
    0xf010f0513121202030a060e06060a0909020d020d0e0c01030c05120123060705010606030b0a050f130b03030d0c021c0e3006061c0b0103080304050a141e07 68
    0x21103181c44802c0e00503212000d000c803951401c0310f0308501c00211024080c030120511644031040e0b04820221410032030403000d151119010000640b113200c40c1325000c0303440c0140c204000700094010f45203402c2c2c60b800040c1403080080303004c0155441b49010381c45070b400044012201d981c052080700204900391505c50f04040030800e07031903104501801a1506003500da044c09000440c05070701c204141d5030140c44035455012604d4a075002c0d005500074034000c00d09000e1080500d0406091900403135000070a80a210120031080c8a06408517145c1d400c2d003039491f420a00d4068608000414019150b59070000301c4810010b002810320915410070704602940600000005a0103070604680d07400854040780c0900400920607009003605400c583c40304030116101044003c042010b62103400c0641d9243c0000c102040000b445040d0440000c10340c3c207081d030051002c510000055584240701e082211009241500c038000e1940c105100500d16500c0308044261a283c20010b1640b11400d01008000e0035090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 89513490 1250 89512240 89512261
    0x6050c0f0706080c070c170f060106050903030a03050a0f05010b071101050a082403010f0f050a0c021f020903030310060e01031406010c03050d05100303110d02030703030207021906020f010f05 84
    0x240200340613440c0855103e051064034402400101b01003180030341501120704580c3d458540c0c83c22020314a009590001030514018002c58429040c000c02a5142000514081d80144006040301826540d601c164180c020b0b140d120307190107418202c1551340c44e0700d03440c030301040003101403180641042814048652610780105c6981d801400b0b02180c50005104903003c0114042c01901d070303a5056080001b502a4209143d01001802e10081d800344655900e024681c81996146c3c403000b00164007040050000c100c00a414803110000c2c0440546410000000280b03103401c1034512440101000c0020405185c20001040341c101c42800d080c03000306590700306000d0105004100505001c10180c01004051144040740ea8541c00d0101c100590b0401c44000b50260046003c1240850801400d808481000194201007407000c5c3c0d00440c0780240c035603411806500041c4040703820118042551402c0c3c03841d841da41010341410342c0101356200c2e0240c42d481c2510f01910075000482c4c82c090a02854518 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 89514740 1250 89513490 89513507
    0x90a0b1c09110402070203030d0f020301060e0a03020a1a0c0a0303020913050402150a1416020906191413020a03140a0603030e09090703020916090b042d0503010606050c0f0706 77
    0xf01c2d001070700ca414a0002c28118461030960111052400c034030040707512080d0703000e5410b80d0005d0303482c010b09412074003d000ca00100c03408060341c840b2401000704a020b03042d894003800110810420b034205015141201c0c6480901e01040300800d8000c01e9070f0550b420507070030000b20720000300c2e01030200781056000b04580a80207151200100d03c0003036000c0d404c0780038401c10100b00546034445030f0b60300e040d900780f01105c3d41c140360102d109090f0100401c0b10f034039282e202074815800540f210170540f440c2c070030107241002001c00d546421000726402000c0400c3c0b144043e086020a5490100300300c4940c0c03000d079040f21801844000e89529003403050001c2940008100514202607851070410303100d102d026031501d0801e81c40290b000c0540001c01061035010075a10b986040b09031140c5c00010344900e40200f4a01890041500d000440c400e0111003032016a0002d0b2402101491004d50a884001003400e40b08283c0104011030300014815107100f40401000517844415005420428180200104602da = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 89515990 1250 89514740 89514773
    0x30120090f0607054b071809110108090304060f020a02060403030f03050c0c250e0c0a0e0a0e06090612060a0b0f19060c0c08010c0f02060703050108060c0f090a0b1c09 73
    0xd4021900d05c0d443d003000440090078003140400b400c0401c0302208000703032a81c0a022282600c4014410000754000c03030486000b0303041c104c003940c00c190a00c0001c48901d010780c0d0682c400c51082d080200c0140e05c481d0000c00143d03010b035955061115001902030709803003018114800e125010054440014000321b101c014840304403d00c17614203d61002e0042e000c110f1604900d01032958142441610b00c0100010020a0000d0f200c030007035017540104108002d5580d10400c8070402031200040d4003445c0c402410b070751228000b0118425503807030520040c0350043c1141d51030000307a911601d50906103802c00e0103010101d004c0303690342e0705c4090389504174071108000e02c1510144500c0041c2001085840301400000d007810000802505580c20f00040030102d00740b80321b5001d40100000316004922070b00a640c140c0d80640000c11441d2583c9076480382d036070302603007141e54492401e200424041e81d0f42d8200100800103035140b25120b41000c021301201015103410030b00d05a180407a51400620903231919517111 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 89517240 1250 89515990 89516113
    0x120405061503031c020c0d050702180415050703090b040b10080a05030a0302030403020307050a05030306040501050303070c0b09010e09010b07060516020c130207060c03060e06030120090f060705 85
    0x113001c00c20501c0041c3c02040c411114a0150720242c072a13069000c406421303107074022a22079100c402c0a02880d07007410402e90b009440d188410400101c8005035800c040d401102926002851403880c0d1503901044100ba54100d403518043c0007803000c1d0f0135640c41d03200c1c0034120600203461000919550565248580c1d03220405040e0040001402d141c003e00075200c08940110644540308000d06d403090312a4000c480c540e2044d840e20002040ea410004180e4040b6584080c400001ca8106800a452504410101c0d41000084855405681c60f160060f134000c0036590150794480c1d10502c2c210b010f031540140b000920494411b014280551b001803240c240c4030054501c04e00c0094007401a070082e201d400350191400382031031040002d26502d64009812592101555102901d0704000c03d826510440c842400140040b00700c0207008149900401c0300700c0c40148001e0000c5289004103881d90052002605d0580090910b99805507406a40c61404400340505000780904d50007014086d1720313400d050340b00a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 89518490 1250 89517240 89517277
    0x60c0709051e0106020609010f020703020309040902060d0207050703060b030f15070c061b110105060307030303050901090f150f1112100504061518030804170106030812040506150303 80
    0x4a2070b00c03401d1141198050041000641e120400039644800c1920710400962824030028403c022a20a4450160f03242e8043c41c50200080c0800c00034001ca041c007030364020070420005014045920041403083d01c80e0f40a4041c00d4554280b120440780f680c1c3c0c0c968003a8000f16010380100702d01094220180030b03c4100e001a9848540c011219030303c0c0c11600400d40742c504106601507031f00c901d0a00c106071a03299203640c0b410701945e031458240c40040d101075070942e00881043c000240207822559021114000020751085240c0b03404d48041c599882c1604c901c1615812045010414080d46507041e40484050200410150780302a040c41034011540101000c40045910706952104c00001004010428042191901107020030540b8646c9024080744000d440035000142c114100000c4a41002c401030500e0302d0038089171107e41e04181c8003900355603580d001000144028000c0c1c4100107180003d140075141614255261080151025028412400450206580c00000c4403c40007544540641 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 89519740 1250 89518490 89518501
    0x405010f021204030f050f071a0d0b030a03030903091d040807020102011803080601020d0801142112090f03031e09010c17030f0606040f0e06010c150b0906060c070905 73
    0x92042c1d0650034507401d0000100001071000d07216181014074000d8040e101d040030380486060380c80c030580c4a80520070700301e542c3c1c0300742c0800c07164054000c0d003088680216031400c0e084002030402c55840801c03000700342da844d003d4081c5035011403508003078210708000b00058415030003241c82c07100c0018030042164000184880c1103900c01e400c290000201d02d102e00c0c00d0b0420510b8003401c1c030700048074444d0040c86001e02200e1028442c01004d4100c643d0110301c090b121906c002480281801c12104e000d07859104100a01060820000342d8003400b51480e0540e100c81c240310402c00300c0008031215612940c014096400c003010000030540f01250010385c1d035980c50700c0c0c8200503079030100c800303070080e000703102041d00f000c50220080011403003400314203486261540c0b03a02c10846240141d00951100500c1c4400c2401544000307082107401c41414101001031100a6a468400c0d2000800115040c0d07250f02c042e19450804101b240d400c2403084070030b6400c0c034002603802640e42400d80b04580c803040c3c07100c01144 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 89520990 1250 89519740 89519743
    0x6010312030b0913020f010c0209040b0a1104060507060b0a0b0901120b1c020405060a060c0b07031401030503120702121c0e060906042a140109080f0d03140c0405010f02 74
    0x30120b2001d89001201e10349220901106240140b082e800307007010b00304003102036119030180000198010013121140c0c445403240a040b0b00010300c070046160740d030560080c0360303e03403003001d00000c0c041980e5035907462081d0301d0000c059641103c51140035214a441c103021224402098401d145028a049400684040407010103483c140c3c81e190740040e40740700e0031003d4a041044900d15079000391001c1c8403079218a01400400849842041c001881e280025400640303001e5403180c010000d071034007107015020174000e901741507420b9208071205e5000003400700000d0803550046a0040050000d800580040349107402c503841107a14103440090040452007091016034019408101c06200f2a205071400d088200e330303a11000e45083d1061107900200d0524905070980d0803070103d100f150f1400500c0e24140400220140c9548424140301000401091404040014017200d01c0440000d0a100103421005000c032480281c00302c11801c1450104580301c40000d0448044400030300c3c2c066511001c80000301e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 89522240 1250 89520990 89521001
    0x51f030209040f020d060501030e06040503040b1303060c050901020f060606040512160b13080d020d0e0409120503070f08010b0414010c06060e0f070503040309060e0d05100609060609080601031203 86
    0xf40c61641c4049880403054240e41d004c101600d40a0305c003004035480d2401829034407042104d00820f59807040200b40000d4141501910085601000c010003094680e5200c0055801503241400003c0717012030080c0d041c2da41005041c04252410000c4c18107410050003042c200e1285015681c000ca614030030180c1a40010003c207044010041088040540c403410f4070065640a0702c80c801242c1c402c5800450303011070104007505400d101d0340003007c0b09200c194050754406804c03141150b1190352488202e0100f810a00071001a08032a501c0540e0783c5030801010781080c2c100400d110400c8600d90061129000550072201070b980751a00f0700490075920b0740100e840710a181d000a00090038240005081030040c030f40180540312664002195984541c021100c50008490103400142008010050355000700c19682c070483c00070b0800c50300520300743c07030301031510254820600c4620380d2040d0410040c0300d41d11440020b81524945032410038908041d003a502c140600010309030611a00740502c129000307600c030b03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 89523490 1250 89522240 89522261
    0x2010e0d0b0f0610050408060703150b0d0b04060f0501230c0d020f010606030b010c0f03030e0a0308060405090c03070303051305041a01020c0a180509030c03040f0807051f03020904 79
    0x1000e10b107481c2486003035a9006481d0540181010038160110030700480035079043d10400401884540e49101c001c402074124030901c00d59512410501041180c003001c02001c1e10300a541c004118001c8280600080380c4551703000c0318400741070036400d0103282e074000410010711102007149000464945c06141c0984130380b0801c41d0413440340444124040303801048440702d400a42c802002010ba84110540a8440030802280080c0074441c4000000741c0c6098505141402803031f0020b501d003140410725280451000c030a40108a464040141c07a14141c05440d41c450202c8001d042400d1050012035070300c610b2804002c09001c03001c1001114074a10100d44401000001c1c414400c14a000d0400603840000c0c00c1454010300900650400c0750400781410750499600d004001d00244180368401c0c01010050103828040c0410846c180c140b4000300b002d403028100c0c803840303501006e1808200d2031610f02981d0001c1d020f40c1020400000452440344106d020702d42074200943c2d1003100307100140060003071511 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 89524740 1250 89523490 89523503
    0x90f1401030c0807090501050627030613020901090b0f1e09040c03050f010504031407050c1503010e0f04051b180a050a0f09020d0609080c100f0506010503040f02010e0d 74
    0x1c2400100340082040b0b0340f041003601c0302c0700e403900e1044044d20805d01034140c210070304200700310017001c012296507503051840440701c2c0f4407031410300004c3c03d240c000e4505d008401d203560414415854034043c261b0040444401c100002070f00d180204521440d4a04c600c3d00c5802d898129035295010710004c001008002028510189001c0c9000c10360121700f80020f80c1c1510410300d102d444a8030511480d4003e07a0141c41e5011980400707030245e000c0383e0103a5000ca480d80101d003858421038686c40311640006005200058580d81884018034408600401030788007401c00c00c0500020500100354012221411000d04185a8207000803640d60f241e0300100f95200e4003060100009030020b03501c5140070311000030051004090340100c000650b060004007035030060012081c03000082095010190042c840d0b00f020741001d046090990900c1c40c1481003542039500c0d64000c0c582d00c0d401c0e109c0d940d40110242040760440c00d05807540a580d00080c0402414080d12703120001050350362007031910042c1e60215 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 89525990 1250 89524740 89524781
    0x6130204030b100e0709032a030602040501020607170105040b0a03050f0c100c03080f060319080406020c0604032003030f07030306030519050d030c050f040b1c0e0304090f 75
    0x24040300b10707010845100c20b61841007203000c10500d42460320180501000d84c1c801c81c2d0b060941e1601c8101041c0c65030324660049a540c0310762503e01800100c1e20046018200040e2103a141c18000781c103009000703203004100171807c2c802881c4401c5801400d415a0802c2d2000543c01414001250340b01d03449400142c19881058000180c145000030381e1003200300240d8640c602051848403e481148a02900401060403500010080d18114030895842038005088440c407a0852041c01d914a41180e82510100d200150611060760100035005400000f61000740c03400d845c5864031114415094030300c60806802d001c0600340d42e582001601d0316080414405136554041e494003500518a0744000c84460240303847c8003940c40b400a007090040c90308507014022103612032004034020701c28020141c0038050103100ba002d98510820281c030140140e010341e03656448140484082c5e03509030400c40202e1034104000c0341c080301004000e5808032840180086214949400e020003d440700c2c003c452800d03c2d814 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 89527240 1250 89525990 89525993
    0x10e06160c0204290105090d02040509070e0c03090c060301050a05100210061e050405070207030308130b0109050108100905030a0e0a0902070b01030201080c25051e0607090b030f0705030613020403 86
    0x1e044240744c041c8004003162800f58032000650709809030310381d0540d000c240621090b016084c26081103a0189407401035a4919440f003455a4400c0c0050b901e00036a54004001c000209000f000049080c103002c9030f4941c110340c0345c900051a0800b4034002c07a4001e00c46000c0c0c90300010f00070042000042c11801d4140080e548504055521620b07103549180e8203440d911001880d400e003842550f01411060b0f01400c0e0060451f2015600300d10050580c4080810518004c00442d1042d544c0c103001c3c09507201c1c00b0a255140c04c0025142c00c0002d01400e4841c0c1c0b03402002c0f000107074000102c83c4801d8913400e000072100343d0800024000300710b950210b4035560000603000c2c1005140e000d4581070b0303407003600d400140c0d03100c54180c4101c0e0700840e0f081e125480c554010120307001a21544500300d80b48648105d075007003800c41e400021412081c00341440150f00920501052640244280003d4401400c0c280d09620303040d08906a400070240003c010700c040040821038170344514500200341c80e0030000035955184e8a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 89528490 1250 89527240 89527271
    0x81014040e1c1101201801050f070521030702070608090718050f0714070b061c03020604030e01020114010b030421050703031a03100c09080106080c040608010e06160c0204 75
    0x3e02141c003215442c1141005020078062038080d0110401140141007000e95401d5050308100c0e6881c8506022041c41901044404a8000e002107813180e4041d220010026501c9503401e2250b030412801c102c4184204002203a002030b04a08031802031030020311710b44030303941058244036168100e009000000d41d0104890740c0310b034002500030700385800364040b9503403903450840b05040340100c1c50b412141c04000da540810300d4548540c1d007000c0300400c1e60340d03204c2404610308103481e40c01c0d4089000d138004034200414180c210380b0b085d116507801c1c002403054000c50048094160414028203155034030110102e01030010300c0c0320b800c05404a41007905045023018101400a400481044000a00f01181140c028242d907009441044019000b4004031003410014000307000d440400e00b0410102040028407658240280c01c0180103000c09403400321009030500041d2640b54204840f01d038140b0001d141520000280306510812548001502054051044580b42c01e4003001a6101381071148107120000c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 89529740 1250 89528490 89528507
    0x62604060b1c11010c021c02030312090a050f0c0a0618051203120115050301060c11031f0b030102040617040501021e0301180b0f01030e070305030301060e01081014040e1c 75
    0x1583d088541c49010001103441c0000110001c0d001080c00451040c200c2c8254044148148001d054074204005046801040c034011511188a0307130104c40e284c1e01b40038003407080e0f100c0030940802400303400610001040401450748503003030821003164039404480020780700c01d130050840144a807084034041d1036016031b8ae8211505c4900c40c040b060000180f1044207404c01c00f0101020740310340c0c2c2180e01e0950203440d02c45413018203035207080072034480c0c040c40d40d818840d4002480790042c1e03001001d1110b5003110102c6280706070403402a84104000d000c0280c100d443c007455041034442458240d0b4541c40d040340039004503c402c1c60004c0d071003441040c491075050044c0d41170b00d1002c0c21601e40303a85001603803800c0c0c40c40c140030183c001c0b11045800d201540700b5004007004403011811100119074a5440610715402640420000390103001c6880c032560748007040039040302c0741d608541d41450600c4c81150311844100c0031140318658910700041c104505104c2c104030580c00800315003030a001018064107011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 89530990 1250 89529740 89529743
    0x2060f0316090b0304050a080f0714010f140f040209060111190212061009020307050408100606110d0f030f0626061b040b0a030b06030403050d06062604060b1c 70
    0x501030803000c5051030310705051340c1c443c0b40c000f8000c1049907130503140c0745140e500107105014081020000100441c1071107881d64104a1028000581c03410003402207404c5568510369066508145010b008001c0c08501007589c0240d012115076484d03884040041e2100d1083c40305800c01805440408030087c86042c5000800e00c0c0255042c002d035201b6040381d241c49410440b40111156080074061282c02e6069029503031200050801a01d480d4551a050349460410440902800d450302800c0c010264005000c0d401c800c0140020a42002406400752003001580d40312400c05548140030f003800e0400d508010001c0040055103504100039881d1443c101c4000318540c00345200303950124602c00000c81c203840c00703000403081d8103040a09141e10000f003030b8000034001c81050384400340c0c61200c4c3d840030003c41c01207120f078070b8142e035aa10503910318040c0e840ea5440300050040c2c220f070582c080c0191482e0190072010000702005d0581c0c903450410020900b124105420a82440c216100030040380f00d440c2d44507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 89532240 1250 89530990 89530997
    0x102090a150507110f0406030507051e0315070302040b04080f0d0503060102071206110a120b0303041d04020a0305010c050a0e03060709050909150403050d050f01031e02060f0316 78
    0x5507161191010954488a0341800044082251401188400d400001d621100900f107610b075800c1d003030015003950b00e039800c2601d081c0c000641c1040545032880f68010169440b200e162441d400701c00000380c80390741000c20b000d0092080000111624481d50450307000d01061107200f80c4039522919216a104a40400d41050744298405080583c1c040d00c282e9100301e03030590040030b1050800c440c41c5540d01c41c0500407903410f0785546004015412800140c4001083e42d903d030040f0711406e652503003d460010342d20314000e402c03c00082c041d88a0f803d17200020b640792411407240070780f594800b248030115954000340582d440e00c104064240d03030000043c00c4080c480da51791517041c100c0e001010b40b9107200b40d81c14000b09514003802c02045c01c00b404903980c84030001040d40d01c81c1100e00d10441103140c0c102c80c00c400244000440d40d030b40c41d1040c81210380141c94041c428016604542d29203501591181128160301e00030901c0c04110360360042241c026819110020b83c80e4104108101440c861246980022 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 89533490 1250 89532240 89532259
    0x50a030503070210111803120c010504020901060c110d0219060905040b0405010b04090926030106030501091b05250f0203210f0d0603120f020c01030605030c15040f0305010209 77
    0x14011341d0302407030f820600010303200e52402c100c620040342c440340740031030940d0180201850440318001980c05070400034078640c004a00752900b031040140c0200c0c144c016009000e03a090705100880d40d20380b084249200e082c2c2d40c0141002d06c80c000502042215007000c0f0784114940d50100e0003a901080e101c00b01c030002d80f130600c000c00100080006650090150040e4640207000030088118690440d08215001d0039041c0d0047c45540e040400300140e030548000043c0d0008010428164184511801800c48090030400341244803880d00000120f08440c03020800086140014007559100011120401307040d07400c1d80c01c500d40b8151040c0c00c00c03100282c0c420301404040050044410010108602c21490064a082c1c0700e0741581c642d50b0002826010743c295140004800209111a460946d0b01251036140041040e14402460030200c13600c640e04040c1070007000c0110351400a42c80130785080032074601c039441c2c10007440035005000710390004003016101d541c00400e0002c10350041040507800d4810124 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 89534740 1250 89533490 89533513
    0xe03060a0c0e04090201090f0b12060924031e01060305011107030c0f080f0c0f010501081b0d11030304030807140303133f020606030f030316030207050a0305030702 72
    0x864014800c0c50000c42c0103003040c8103281c0740907400302c81c21510506080d8100c0d601d8070081c01640205401c0704040410004403100506224040c240e44910226940591751418880c0c1c000a02c1203541a64501448480e8104581ea0280700d8844461070250b1403640802a01c01903902a1090f40b105079010f500c1d101c803a00c265a504000c6030701041c1c05444000110f17070075603034070200051000c0099618200c00d00030740d0f4003044848020240c64001c0700082c10404e468105450850704181c0c00300320203074071107901e0168501c20070340c078503461403002c03a0a654580140d0030804400e26041683c42c2d454000058040200880034002d008100d0290303045154180c50141070b2541d0b80b0054801d0b600c0ca0305240d8040300010007445852480c0d0402c51514036210068481c88040607006a19501008444031510a40315a0420100d64064801c0f0018048070303070002c41d4581c072480054502d0030340b0519032000d488483d0090301110003060b80700d0200c443e0100300f03040041c0340f40c0040d140d100050140491410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 89535990 1250 89534740 89534761
    0x40809010e031c2318060307110d0306050108100305120703030b0a030807051203091e010b030109150c1d0f01020708060a0c08070f1e0c0b100510080403020304050405070908030a0e0306 81
    0x422174000030155070415466003042001c81e400060810741045090300c000807010b00c06016040107203102e0b880101c5c00707905060015003150b0000346410301c1201b990b0010000f241d800103104075010901aa541d94510060030100d02030241e600809410440e0b0200000030082458010000700d8010342c1900c80c06030200b041510b02d0300c01aa103640269004030380d13840070031080081000242e16002c000066600607000824250317286d40105480c441e80c4100d102c0311500c040d02590804400341d141203011007002889603c0500804030b123490041c60611142034041c4d00802c120005021440215a00c0c1d01d0840c1c240806091084042e2002901e900c0200315490b0049000402d01800798448800b8003e0b0240031101d0030384285440800c1050310003498010481e028880ca0081811180545456040c2001d0010212126032070104100d0308074100b001080e800710944058071011035020400b9214107204503007400340c0360011141400300255810035580c00c42094602414281c0690b80641d58240400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 89537240 1250 89535990 89535997
    0x1715090d080408030c0c3009031b03010e0a05010c09050d0b07080c13080102251e030c06240f18020f070606030803010603050f040809010e031c23 64
    0x52010640c41c034046000070f0b2401010f0350380522810308441c1051400303c141e40c80c0001d052a031480c00030a0398903200c40807000407498803200d4040d0403028548008000841d6940e200d801c207151071840e5a808002c920342e030a41113454020030550403566500d0803410990300820121604501051040f03d0024844c107040343c80410341c5421210352820307665900341c01c0c5c40e507100007041144190700c200060541144421590f074050030442d4001031716801781c520800048100c00105082d101070f540314001c0007030322005e050024001c3c1b24685110810251500356402c4a60403001003103036040070101708100d592010040d2686550f41000c10040b41e9610300140011030b02c0c0500d0203031030701840050340d4841e0560010200800340200043c81c200032500c80000311034050b0001c503400c2c6000001001026414003845801c009034041d101600e0410b6a12201240b252180c0103040c06101c04151841d079409105d07070f2100c280e900108503003525603510010300c80e2010400a40c1000c0401202d99003950741d48003039 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 89538490 1250 89537240 89537263
    0x2b090f0c140312030a050403020a050105010803070507140d03050d0e010f020304200303160c0803030106020307030906020609070501080a09020d08040602010c140901030b1c03020d0e011b080901030204171509 91
    0x141d285485505c0020058003004206400b548900082840028824400c05000f80440006542c5501d0a4540a400d00c00c0b2903104d5640c0040c1d000850125658509400f0f10066050815940c2c070300707a1000d180064050301c000c00301c055207400300c603094048003034005600c00c3c1c1c455140c03425074400c581040c4c40e000c0942c0a51540551060000001e4010b0398440800b40314040e01500e030032a607490214a203107501c260410300050b003000c01c02c117040503006800710016100078000780605140004d04940c0d68003841c8512410000350b0350101e120050030350700c05000a60098a4400d030340d00d07641801d243c103070b10034826140190719106001c808103100e540010040d140040800d442c1c00b25070001100078060200d00c2543c00390005c0301030403a1060b09120144814441c0e00540b9502c0d07401d00c2c001d480c40d02c0200c00d45061000c00d010100c42c50038140424031200754044200b82e00c80091000413402805540c0000525089a0b1101c210806001401490003482e1401c14502d03a82d4040480ba102d8444084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 89539740 1250 89538490 89538523
    0xf03090507050111102405011b03230307020f07050307050a0e0405011103070c060b06070503070327030302150a060b040b090d080a0305060102060a022b090f0c1403 72
    0x18140410b40c480c040c00e911056840d012174220b903561550a81c1103600c564154040c20400e000001c0d140b0100a080360020700c5d01342040d4581300c06e0a6000701c1407641e0380c0e0005040080321480c40e4030f03900e45054118054050524902e44916280d07001030b40da4401ea1051201500c10540000f65038034000071954240e8a02810028169143c9180b0b01c80d0fa90000e041140c8075504d81700000c20741d00c1034001461007051035903a2a82d05803d03d0400b04d00b19941c90301710f40d000315000c0001c240400c2000003100c904960520381215032210b100007040c801a602100e0b418507450300d1700f001051590004800440c81c14021b400d80c0b5075150702c104179007191580e00c20f03202e1035102404200840b51814010380341000020b046500c40d51002d64424440e030380003c20f0700c00402d548400313204465a04011295012081410840c5080600481c0d00442e0b9042e001c4d03280508040356041001c0c003d46e0300441a81d41e030007015445106034070b152074280d0700c1c254059a002001d40c42851940c80c41c0c00501303203814440401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 89540990 1250 89539740 89539753
    0x60e0c0d0f06050102190f05061003200904020d03090f0b0409060918030804031215090b10020c0f010c020603010902030f0a06060507020f0d1203050114041b0e27070f030905 76
    0x2006c0b040440b10412080d9201c1c1440c10300c1d640462000d01585100d1458183e0140406046140a04507419400c008145864000e081c0000640703508080c076030002c0d0100d804e040d80c9021498103c40141c83c0b034119402004243e840080e0070700c00b410241003542d00c62442480401e0b2501040c102302c2c1c100d0703a00d00405051300030500010034001c42985c0d4020303000b80341c81c00c03048610541013401c0d900415440c21015002c0e40013084440b03d10b2050b451852011110008103c800c61002036940c100320101c0c0e403044000f00454a20350f070040d2056801a5800f511058480d03944002940081d0011140c0c81400c4070501700007081c1e5a014401c580070b0340d000f920303540d0030401590241700c250395203842415003000d40114040d0104128204c1c3c407a0903500c0e660007042d03540c101800101c006110400d10b40c0900d08203c03030900c18080d000c483c081010a1464005c1216001c01d0000743c80c00c400c450b018980e440d070107010038000601c0c0100380748244821307100e540c02d660502c40110300310341c02140060019000f14 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 89542240 1250 89540990 89541013
    0x1b02030a020d0804090203041211010203190510081e06010b03010b0f0a05040b1303060606090b0301090207050a0b0a09030806060f0a0f12020d090b01050d08070303050901060e0c0d0f06050102 84
    0x10071050402e10b000d03001c040d06207038403030014008030390040d6003d641d040058099000e24030b5202c050410440078000c002c1d811401c0c070b80e41030704c0c00c4200f800182d90ba183d190400950201c0300d480c940704c0144641c1045130603020101e52404e4038080020740c0301e107207401100000306030100c69034110b904850604004614081d0004c00d03800880d0000132820341000010400080c03507601800103040c100d0200744a002c0c9061952600f5001ca40d05607203c08140100380c1e504102645814013501e04607640000c0150b519400c1e80f410311b0808580300c60042070300760240d041c02941d40056100e14807291003030b1225120340e1101c0c1e00b005054058011044410801005652002881010f100b4000005400d1800d59948400121001da802075015242d06c960340f40041010310403500c01030b0b40140001d644050f554096902d41663f14480c0100280925031203101090b08141c0944c400c40043c1086101050036041004003210251700080c0c000b0580c504040005030300c840716100b0341e001c5400c142c00800881004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 89543490 1250 89542240 89542249
    0x408120709050a0924060e0603040c050402120406050c070c0302011b0b09030a0801170a02060307090f141801050108070e0d08032d0717060d02030a03030b011b02030a02 74
    0x30300d1001007181006000800f0745880380300c84080c044240d408075440d0b085c1c44000d54512008541c8402e0411203a10401101b034000e8043e0781c0498040d5a803d40d40d42e02d904008410611982c407054105100149103128400161041400b592181c1014031841c0c950042d0300b8524000c00340050403004107100d0400046d03004a031502490142d886021989121548400c000c0c0c05007103c54070b505410002300040182d80c82018140900049035030900145045541c0599500428038028098480040481c5181d03000e420500d005001c2002c14900141d01c420620403118120b0740014007540c00c206140a090041041d200c3c103071a0b040c0d6030300b44a070360f40d0401100c05003100c964142c2c00c02850042c4a001c522080b0041d03205014441c0c8901c022403850550038183e4407011654070360b000703103c418000f1056126203100c0e9030745040c5088614507192100080c3d042030883d40001c0d41803040001e0f410070141c058011030002d80003600c69280240c10a40c403a40117010041c0020342c50f410102e01c1ca401440c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 89544740 1250 89543490 89543527
    0xa0504050114090708011508071401090803130509060d020f0f0402130f08060903070302150a0209091005040506100e1e0a030302101112040f1e0f0b0105090408 70
    0x2a4004618804602440441d800b003d0703911000f541c000003414807128809006481940c0130b90501c1845840c600b90700d403034030740025000d602400b02c0e801d0004615130f842002c00d20044c0c5200700643c0d039554284241c26403038010903c41c507406491240c0000b807580c982000b02c1c00c0c41c150054144c082d140309080801141020500d5000ea00543c01d001b00c2c9061140580104054000c0e984440c214509003c800d03440c2034001840070816500410809001941c0403a0324041000c2260650000d0b4640348031060180c0039074440c041c0c100408204102840e0781030f1080c2c10851f04250340800c69921502c0a101c40c2c40d0003403000307034041181c007180c1c0004d41c20110303101101098090b56051480046600050041000b5401540160f202c1d285100140403c1d01c60040002100260980707804c86401c1001c1210400034001b9084140c044072090520070002ea0000d012081111100040ba00c1803901100a44c11000c0070b0340d280e2118030022465081c000c15032802117030840000343c00c184065010403240e68 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 89545990 1250 89544740 89544743
    0x20d03051308092b062a09090519091b060f02030906070f0203120304030206071b02010f03060305160303120603021c0501020c0303070507051924020f0304032106030b0a0504 76
    0x280300e00514000c12440074400000c140c403507170012950054a10440190880084d0380c01d58072803d00181c0400d182c0c00c082c140c000c807444080c010030596640140381c0280c49005001c18120307401d0104880400080740116411740480d040c1c80c10342c8070b40b2808111840c03039201c1050b0740981d20403c00994075143c4040906102ca02c81c5d14108424442580400d0070103c1c5d1000700c803901200801440300b019014404c07554840c0c0076141c444a10f552003900c80c1d0740e81c00c076000040d05003c0f590342508225407080d080f820242d5040812240300e076084440004c2e2982d4a8442138000a40d04000c020010241d401000f007140d400400c100603104401c541c0c400c8026001c90111403a650811003050b4040e42031010f0340c440d6206072219502e90241e810321506040784800b1242030400c28000040018004100c1c003010001501080440c0c038880e803450400038852689000b0300054040100002c0561041404103a081342d1249040545442e05103041907a009010060000f0415400910f01090b2544a83d40c0035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 89547240 1250 89545990 89546029
    0x221b0c0326180a05030c0601050a06031517031210050f01050c25031208060901080c010f03051e18161a1e120402030c2b0c0f06020d0305130809 63
    0x343c0c0310340c0c0d224550303401300d460f02c0d0080d0841c5004108504d004008035000780a1803c0510072000c02220207891600540600b845028004490042c245420000d44506001c104044441c5040200103051015050710906228040c00c0700d20b107845501c1141500d0281410381c00500d80c0c0f060f5881c01c000c211601d0074044080c0f11008400101203a08a4031039064245903880f0110710781010824402c074090142c00c01c0c041640060300c0d00ca002c0e64440001d4100801618000035151518001c3c0810302c4041501e41c1203515580f0240541550004001900348860100f120101c4002d1200002404c2070391240544c003d216a005880d80b07807110004240440b0b08244625640c40c4040c1c0303020161304542c08001d68400c40030104021070600b04200b20034410b00316903010031000c1c0c01900c1d49848051301901030f1250310100b003401c200030300480100048d203041010b00c620307107071200c0000f5070315240f1582030b0b00040d042002182c1c0c10b00c0c155482440d02a0001c00c100e00d0080041c1c10320071140101d000c5520384 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 89548490 1250 89547240 89547253
    0x303090a0920030705250f0b04030909020d0b03011407090303050d06030b010602010905100506060403080f0706020316030b0a05060a03020304170f04030c14221b0c032618 75
    0x100b00c901c01c02107225a4064503029150100700304003500a41b450424001800480500c900205030052906201154032442e001c0c0a0754451500b190204807541c0b14444940c000302c1c4802018100d1303005200c02131b4040d00200300c2000417054500420310b00350741400c00b04111030b90500c0843d10400007848103140190740401d215036207a5404085a030b0076400b903070050f50b580f01c3c0007007040420300c180304050000c00403e0000b42010710000304580703e10b100c01054204c002072103d103400580c8041c0d424140d04403a003103441740303042803110a007914482c0000c00080d15141028000d80b030b00c24603501c1581c1c0d020b0300982c00c0107620300b4250020342c0080c10699003158540b03202203000300d01c50020420701007158001512245075140501c260085902300300070380724020000100071f0b1210307149200070881c250701c00550090440e441070014103001495150880e11420b444180c030790080380c4000070a01c01d548414907504050008000301d5400301c102c20204604502050403c101d0043c0aa8003a5100c41610312 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 89549740 1250 89548490 89548541
    0x80705011811010206091b0111070f03081e0a08010b0a121517010209300d0504030c080606090420090f0f06061918170a0c050303090a09 60
    0x18000004030040b1114910a807402d641c0c1d590501c200380d00415180000c2041c80c5204c0390700e50070900c031ba00702981003000000251084000805c5410002d1090f8003580704070a480381421b81c2e031a40304444402031000d0300c100110800d20301e28112004501550b849030066400d1414486282e070000740c11504010580e010020707072000d00d124400c1e8100c2030309134254000e440e0074108140c100590784206082d9205101c10350407901c07810009902c421a1852200d24840c042c03d0103188200c902403041c00c11f12480482840c0145c0200c004e1084d02c1c003402c941d00300c0c1c95481040568654044504e16044072808010030005003d800c1504a050b0354001c3c107101c502c464070007040351624100c078000000b1680d5014064145e40001106400840c1924071510301a4800039050705814050151410064280f8100319420b44603203030140585462140c0c08418910710b0611580c8454411003601c0c0500250f00c00240c0d89400401c6460030365000e014413a0292503c0c1404005201c081016000201e0b6982d42c400e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 89550990 1250 89549740 89549771
    0xf071202030f040308100e04021002030f1207090f06170c0904090f140601030803010b0c15090f0105090712022b031d01021f020d06030210030e10060509010308070501 73
    0x40c4101d440004542d403d18050400a00c601d0018209074202010180c081c00501003580c2c241b079006030151000304020084640032881c511900c0480d180ca003401261200441c2c4101581c24000d00080e6128485151a1040340046140c030b4130035400031800784c0500303c14216401c50060f5100382c03815902030400c81d40f440490180ca6101200700c5200080401543c00c01002507031802c8240410b07001001c156041d561036403030500c818003413140140004943c0350074680d010840842e641c054201000ea4504141c44180c0e44c1d05603000181e8280e509080c00500300a00c0001c4110031582c401340442c40404194003031100c1024000f000310070050040c845082c0c41c0304421030150388140300ba40c4240d8020510210504169600d05819045402010020003100348804441e0005040c5080041e0340341c801608050042400b603100940105080e218240080e41581c000c1c140c00740908262075500740f1944e881d104407105401825070100100d001400420405000b8101941c46a00000b031841070011490 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 89552240 1250 89550990 89550997
    0x11103090106030618050307141c09092f090604050a0f05030f1c1d09100602010e06041203110f18040c0f0905040b0102190501060e07050703080f071202 67
    0x301107607446a004004100e900d100c1c02030940c04501050180075600d9550070703204d110b41d230070280c40e0a44c00c1c003180030050410b209884246001ea0360480001e02400d0001c2d0284640748102c058081c07420f207001040300c001c80d004d1102e0441c01d05050a58526030000da52594000d2100c2d0b0fa048507040c0008030361622030b604030401a14510204a18082c0b60204240ca424500c2c9049001904291038800c6082d1100a4084403640642443d50f5540072000d0001c0c05648000120340c0c0c00710341074050000d00300d20701e000c51080d10301075402800001d0a03123003e00e9540c0c0c3c05440c01020388940c41030100210384030390b10403d2905030303002e21149001040c1e07400006540250b0340c007404002c550b0f40c00c0310051400b449110f002c0c10050610485105500d00054070000071449201d0095403180c4502065a00c00d108001c401c031803545008003028600d0a1147c02401540140d40c9607000000105018030700410564081e00d5150380ca01c0322076980c08045040c441d00141582003803114641d030400c542d95090015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 89553490 1250 89552240 89552251
    0x503071106010e0a20091c150c0f031104030206031005030a0305090a090902091504110703020109121e1107030f030804050c2d030c04151418070c0203011103 69
    0x42040d1402c101015804950080b0b4110900d804030094104441001105590070b41c40c00701c1f00155003040e1462201b401810407913009000c0700380300300e000b011405980d001c21800651903640c0e01c1c52242d2408154129a40e4180038641502d060000300f00605d0301d600150b5001c0241e05580800c0f40d658004245080d0038508110f0100340b010540c2d582c10b04200704408010240b10300c0503c048040c0340c01007031028030050800034440603001c04c00c08464481c3e401011007404080324081d51100c01d400e00034000c00007540d0803144092100c20b18132003c1e01c00e503d8210182c00c3d0208064980188070710a40d214510584203407202d01550034004040f5440d10800b5a41f1802a120494280b0b0305280490070b091403454141c2c450054501c40442da111043e520040c00302942240c0300c011440400000c0c50b00e42d011802a078024100208010040900c00464003141d50b5007000c0c0904881d00020040c0f119003030010301c28244081c0300020b1901d80f0078551804224005000014185000300f428040da920440c1d8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 89554740 1250 89553490 89553509
    0x60603011d06190b0408060c1215010c050d09091503031407170d020a0e030a03020705040207020f04050a0603020306070206070c030c08070b15030f0a020604031211010906090308070201150501050307110601 90
    0x2020080e0400c203100070340d40701d41403108d013501d0b15444002d07003102c03000c0141401c0d2a0f800030b1052507000780d0103850043c0e034040c0c226003190018003260000800540850292030106410203802c410007a00300c079001b506803945a25200c1003d01c401c2006450741d000240141c41c070301104000a04a00790b0403000f080740e0714200c030740940c0d5420040360107800c0c4406020040e009a011075521004203a020804605503076003243d002d660b035041400020103249564106a1b8491b142c0b00c1030212600495100c00102c9200303030f013519005c2c2c1d1807030020303621020121040804a800e030035280700000d11035108030303154504c10b291260074110310b525800d0340883e08492618010f8000d072800451442c0401840e20b680410340000c1c15920084d501182c1e15000b45d10005004242c3c282c50043d195010310845100b9100b924001c01909505040ca180900300104058000c1020700c4080340805106000300c105c440800314840700d4080c98000111080e520050001c030400c80c000400d0392180205001190080003100f5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 89555990 1250 89554740 89554747
    0x30f0706020d0c020a03090302060d0b030106092412020904020a1d0405070b1c0203090c030f1605010306080a030807020f0a050c03060115020d0c03032003040308060603011d06190b 79
    0x50b8000102e480d034500d22019035020510010000398403034041415a58141c41c00e075202d2444100c00d1006d001c000381001d40c194241540807032488000c0c1c2c0308184030f00c9190035050600002c8001c480a07810140251803c140245511300c001d41006192a9040fa2025002c0f48220395964081915005c0300040c0c980d0040b010020300091000070844103015240716101ca42c035180e400095407989201a801070389005402100144900c1c070305010742109031202401783d0743c000c00462003543d1a61000787c040d404d01100404041201d5100b4070906080e115040000c14880710681c074261b03070500d80200000e085114a1190703042403041800404001e610039070007091132929010815041c508160800e502030300140700c60300b07607403a800242d40145162500700b6824201080c203084001e024049020300f44030300100120610392101d20003c40c4201d010340d951440d15100c0004210b1948400c0c400e08254030007112048282d5415807891541117000140070f204038429107810f45107109255403086c041800b010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 89557240 1250 89555990 89556007
    0x40b03010603021803060601020d030b031504030207080105010f061205090c0402040f06030e030306010519020a02030607210605060d0f1d011b08010503060c0c010f06081011040b031503030f070602 86
    0x307901e0058484c22805402c4901e0500f0000756615210302c420001c00d500c6015a0741c003918284401c481204120403098a41c1c501410003941d9654588a0045590b20704400054281203003410340003039444d1950350383c9061040f0307d114001b4103800b40903414240076122601a1555407440240000c001c1d184413009110f00e07049014040b9400200031380b4064004000b04401c0340c0c0d028080711440c8000c10300d00b10200200043c100e1422550050080d0148034980c1405055a004001d0140b581c250800d662604001c0c441c48809a9230030340701b01904a00c06102c0e41940103020380100706602d1a88500080e40c0c03000252003070740358204c07070b1210809943d0b078040030303407441c0240c3e001d1181480c1034204418607516043c00700e5625000205034001d1b0120220f2214000d010039003010220140c541d00a00c001030b00c0d100b00725100c0106040c0180020720f0600056000c011880555048651030703021a800d42c0e0b2103020582c8031105c807542c1381f541030004000d41d20300c00d03c2190141400e00d028000061700d854a4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 89558490 1250 89557240 89557267
    0x160f03020d0b21010b040b0d420605100206010b090f03010f020d0501051e100e0402120601020607170a0b18040804051306081f02040f0605030405010f060501080103060c05040b0301060302 82
    0x542d1080b401241880e00248164032000500c4020580c01010b038047d45070320030b0007141c000c005240d501d110102c66501144c841c13a6102604400d1488503441000b940b690744c0c00b0331100341c00250030f850142c1c014500400140030450064806154040e04407104202070341c00003400c4503090905800115404a44064400c14900c5500e015002c1617642e0b600e8403840d2914607007030070038840c026031003401902d030b040d000ba034401c81d010400c0120141040d5140c13080a851644940d0342140c0c0b550051107100e000440441c070660402005c4032401c5480d011680700c15003031001400c0d41314541600b00d8101007208046d1845103484521450107281c600c1e40f25070a0104006075091501c5586012506040c0c00f403210b03c401140d02004040611003008400243c4802c001c0a0f010b1070740000c800c8001c9130000640030b40c000006612039840b65008010300c01c0b1040528007200c0a070700031a40012240c80050002a207150700031215920706040150034030340e4400c441907155100340c03c00400250089100b089407082c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 89559740 1250 89558490 89558501
    0x3020715030627090c1203141804090507030209010806150102010b010801230405100801050c031302060c07030b0c0d0b0108010605031f051305070206160f03020d0b2101 74
    0xc00346000e000c03080c43c10501c5001540301c6416110344000702c80d03588051241507030041c000c03280d00402c0c00318016500c05c0031212143d0030003c01c0d004075a040070303a604001650400c0b65000f14003840007a5a203021202808001c2080d01411501d6200305d810200250755654601c6009181c4c0700000c000340d252082400c40382005982d4824103680c184039045032300f80e80095890303054a000c0303a4501c810203d51090b48010444040751680c00c14981001e2050000484001c407054410100082c026926407055000303451008072002600c0900c0307aa195001480c0180040040c600e0b0242100c03030300c40d281d03203030b0300c040010545800c103030090001803107600b1800c0c9002e4600341001c2400c200c105507251000203410303880002c01281441d03140c40da01d0080030b1490340540c0041d101c058100b00100000081c0306004100030b403803c40140c480d0000140c00b1b03076401a810003039141c9542d58980400303400c10703058020f900910014020162034a10030101c0d6166200300d103458026940c660340a81d0f040035007143c01c540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 89560990 1250 89559740 89559779
    0x50a020409060e25031e0c3002090a020304030c0c08061006170703050601030603060e06010f0812090d020a0306090b040c06020d0c110402041503050105130203060f01030515030a030207 81
    0x1409104602c1540185201d25044a801250802c07140c141601b0442c1c00c810200d00080600518910104200c040301502040703454026401505404548004185215500e040294003000071400100c20b44401d03005940c001d4884d040c104060320050b6a40750038242d0a4000700b005500a00400c4150105170649074001c00c0c00341000d5114500c00308084a046000070007840a15440300c0204a060340300740d101c44010b540012040180342d09036014691200001c2c442c103070303101219003000310308040302043c58004020f65681c854a0b184c0380c2410b00811181415040e42e102c050201c000020403c1740c060b80f0522886265058a14a0603151903c5605400c2c3c01c100110740c004807240c03c0c00790f0440303011041c0c1d0360400b803603480160007200028060700c9039030007480c0e5a0310f881922500068154200340c2c1070b03030011161520054660910faa00300d0004990407075002d080390740c1000d4194001c2d84400c2d00a20015a2555140030300c101091a121560300200c0c010ba012140030011200307906070a070100d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 89562240 1250 89560990 89561023
    0x40204050a0903020a023309030d03020903100507170405031b0309030705010818070b07060b03030a0f120b2101060801050f0c031f0f0311030703031407050a020409060e 74
    0x2c001d50b4a00075610500e200e4001d0180c6050800c0312010070311401e5010207801c0c49410740c044d08000c2900d07184c494020410b854042d22613109450008ae01030b000762400110301034000d0480c0c40c1400b1150300a810060240c0c0c0500440b12841ca40310385a071200036104d240100700440c1c1d02c142a0702917003124910340285000c160000d11660310301b564007080c0c07141103400918250f00d194075400c200c00f007240d001c0d080341c1002d4803880d171000800038520005800560b000e05d10401000c2d0039a41456240c0c89018004000180c011210744542401042c0e018031410715902d000942032540004203111f00582076800d0b019900300305501c0500002402880042c0000300300a11050504d0407a00320a2600540303c2054036101000042d00800c1071440e40100035180d030b00716004182e84640d2001c203130303185010513100c0c00c02a48515040c0e050000d125009c990b4155a501e40d413003d024508021904012405c07a0701d0301511603034002598070750089081c400e0003070000181c0c4070b0780746400c20f150210084050911 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 89563490 1250 89562240 89562251
    0x90c0a03080301090e031303050a170301060806060307020a06050a061a0711010302072d03030c02010b0904110109090212090d170703180503030a1d010b0303041e0506040e040204050a 80
    0x1607010001da03070441d00010070110f4221014600c4504502805460b11400485042c001081c8a000250000d8440c0541008210a15804c40300d251a2000340120b202040c1c811000c14000d091450045070f00000b644143c5801c48210342d50141643da098820380038803902e0b83d8003801345840c58015100c580340d8400c1d02c0d40c40c2456030b540c0c0742603101091070680e040c10f030f0100f401e42c14015082e41c02450400d004400002d01c5030182440310501406620a0300040d1410040b81c1481c5e00500c52404441c8004200c683c05540b90395824074404403420215040000c111000512214240040c00e201c8c218405480320929048606604c0c1c100300048c60f03002c11038a201e800d009841990002501300006240100d0b041d0444500003070480d5140000404502c4004200520030200e980608408403d03081100e0b00d901d640e8520509a17906003880c0d642c0758200f04000c10040030503181d00d1219440740001244565501d50000302141c02c154004240540100100011441d282c8101c2c3d500105d60081000b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 89564740 1250 89563490 89563493
    0x50403020d03050c041a030406090c03030903030f0309020d02090604020c0304080604110301060308071704150201020924120a0e01020406050c060a11090f0102010e0d0c0308100617150d0b090c0a03 86
    0x207403840c2da1b0305809025040040031505200141d0840441c140d0001c541c201e6070356aa180040517039613107120550025903040048945c45110b40034480c101070300104030020701100c030b4007042010540588005d500580c00c01c10315259540c14005000242800e00240a0034a8039081042a145101c010544240d01d02001800080d60308810740d8500c0f03421030402406001c2c9600101114441e80e0401a090840145404140c9074150010300380347d40107031500303855503403104800454000c1d5010018150b15051250410f90f003150840c40f17910001035080800d030b406250410b1801c81c3d105030807030700004000068291000c0405c2100d42d81240c480d680800c9040c61400b1121040e009941302c0b02e01c2030440d4060007065038401d421022000d0200c2e0b003a00c0d8490407180300078100411000045020030420340005510711074030503120b011034055886400b01402ca00f01442d281800003011071410b42411070720700702c081d103c0d00c5080c0400c0b03104000c4a0018209400d005140000d441078162045248440c10310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 89565990 1250 89564740 89564759
    0x7050c101815050c0a1b08072d030504050402070204090204180201021e0c01030209031c03051605031b031b0d021308031303020f0a1208041d07020c0906060706050403020d03050c04 79
    0x10212520341c81c01b1119404d01001c1c0d014101360941c0068042040420045c0502a40001c9250060910780800e1544d404000125040105060024020800c248800c00083c2099002090303141d00c000c0c40001ca46100d030340011700315904014154240c46201c6e0b01c0c041196010001c4203c00c25040f8508202100c003100f400d5a5641d000031400c0c10507401081d090f030503440c10807840708030789044076500c0c4029150890003001404102d5011a4074003d43e4625010310340a6001c030303030090b401610450b040e40c05a04088501d54006814841424100314080c0800300c03030b540140045006e4003902503510304400ca1030183e1020b00b900f00c11000c0d0420050503450b9012003940d10100c1f541620018810340038200000c45101c1c0561045026840b512640340c00c01c00b01078010b005a5841c0845c1c02a10012074000d900d46510450340300000d6808001c60715004d01e0002900340e0300c44002020350703117008155902c480584506540c00c90141c0d0000fa1158002509401044e505c0000741c01d1483c00c0c2480c00002c035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 89567240 1250 89565990 89565997
    0x9060b121207060f05070c050c0d020102060a1d060106020d09090c0c0b0c0c0a0510060e010e0103061503150207060608031c0e0c040e0f0105100e07050c101815050c 72
    0x10341245001661a080240c142c120b103804c4403004100f0000c1349050f40014007100c80140d401c8603107000c0d030040038626203482004c418065170103a008180319522189144020f2031100c0c00360411820101d11b0036a103480800240c0d020f407002c0d9000c3c01c05040360a101802410150b00103464880c14040e0652189a11100401d40c442d0400c0c0074001b05e440e2081c0080451195883d0030b44980645034015003407180024204029604d030b001e00b0410240e4801c051340c030302c070000c3c094803032010003806c0100081081600b2a00c80780c180e105220031415502d40d140c14107041480403010302c240d000300301c140c00d00c84244580c5000305030920180d4949001c521001c100140c1990f011042150303200801d002c02d00080281920100340548200002984000702517a6102d000d90a8448ca60810000840503116101040300b119080d058901030b030303101d80d002612203800c18604440248126440701c0040007960040808451445003040a4040c2c41e040207909076080400d03082d481070514040c4281c035054413044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 89568346 1106 89567240 89567263
    0x5090c040612060b070f0503131403100606020616110604050a0b070e0f060a021005010315180f020f01020703060e0d03051515031302040207050109060b12 68
    0x250903612a402001c0c4c80c1d04051040100145001d0490141c40e4401c1c416a42410440c2d011284603c2e80e541c414880010030f0b81000b9124241400403800441e102d480c1800b0050900340040e607a1040904440181130070f5030904008144030300421a60130b00300c902602c90a0511782001c0b583c075940765000b41c843c512400301107070a4500a402900090302e000d0005001c61f150358040101c55044002d03400c00350300070403c49250040180c0300302c6029502c0b90400300b07880b040513107171082203540d01c0000c00408003203414001d01140c80c0400c1d07002413960403242104e4500749000100d0800b11143e000410160820900d4054010b0102e0061413001c481d1340d04000300d65542d42c0c02141c1d5404201c40b55000004091504001000c00000310790018603c160741038003180da5400f103012030f84490b40c29101a5034600000d020040301e40245804080111501c5402204002e4255104d1001044 = true := by decide +kernel

theorem cover : BRFrame.Cov 89388490 89568346 := by
  have h0 := BRFrame.cov_init 89388490
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89388490 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 89388490 ≤ n) (h2 : n < 89568346) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
