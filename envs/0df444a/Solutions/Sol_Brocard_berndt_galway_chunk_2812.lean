-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2812
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:49:05.288656+00:00
-- url     : https://prove2.me/submissions/ad9ba526-d534-4308-bc51-0492fd6cbe10

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 505575539 ≤ n < 505755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 505576789 1250 505575539 505575557
    0x3040509010e0415050106080412090b0a051c0504080c1005040f231e0606090103020a050d0602040504060e0a050a0515010f0923030706050906030406090f062d0e0d 72
    0x42c8460704c1860450840b0010745054004951503511a5202d4403980c01004040481000b90f902124a001d00784510809030405121100c0b120784607000130000d02c020380c1c90000c6a2412008602d040354000d481c200d42c2a1400202107204003004e0010000d00c0312958020801d91920340c90743c6c0c450100c1168004c2c02c03190082020343d00500c8080945448034805c40071907401440c2d441380c0351840d400c80390021100f07100d179a0009001e407810f4003050341601e9020782281c00c03603440d0009102c8240d0340d071081200c55039000c0c400400c10761201d01c9181d004290120001c029400c221280b103044460103012481e8050a0500b005420050040b040f642420300b0321740b2a10f42081c0e15011035426509030820030000012800701e0120003880e91504948260440550302140d942d98010359880c410f8145260308118140002400719003d0380c4140540e90180441c00154015a51508101c6030840048101b0841104c241c2e15071070304035044c0d07080b2001042003c2103c588401d640580d2890700303610070804c100343c01c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 505578039 1250 505576789 505576793
    0x3150203060604170328030e010b060708130b0f090f010804021806030c04020c030c1204080a03120902030109150609110405040f02090a0905010815041e050f0708010203040b060303040509010e04 85
    0x8840c0c00e172241440c0c42c100c1000804800c6c011030044040400040c0c2803c1d2400700d400c3d818410490200c0b40100124501401d0390b480c1d00c0540c010401d9104156420400001c0195484000b018100007240c003c1e03a45002600400c20440c01d003070456810404070000300401601c800081d00206040006c900030240d40f005c00081c0b07003109142955400600100c0c01030050343e0000302415044000502f50f0301c0e0018807441e10041806580303e190f40b1a800002d000001c6406060240d821441050b004100b2406c41c0d004217081d00c1e01d8120840c0c070090081d81300c039111074117440780308054030b01804148420300b06805c15808502850044510440d41d801d4105038150081e41110140c4401500c150b80c1c00e0790703440c41e008c0106024450101d85008034070b80116002010340078940300d02d50001d20446201240030380c04c2c61078018403000300c58a200d030030303c0d0301040c100c1080b409000301000400135940c0d00c0c1c1480e0408803244050f00b40e034000d510600043c401c5070b440b810406d0640700300d141c1c0b00d08255554 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 505579289 1250 505578039 505578043
    0x8040204110c01020406050c100509030d0203070c0b01030f050d030e0d08131a0a0b03030316030b0102150907060914010203091c12030903110c0a12050307060e070315020306060417 79
    0x701989503243d620000d00002c48940090281202104002c1070b00d505ca0124254a0280c40c2d040b6903040450f0010003001440e510640d001d940c01840501d000d0345035040070790324540108000e030000c1d103c9580e070240c88000c1080402640c4900e050904d400c0c0b280d18003a00b812a0340e80c0e00ca0b8034200c10700180f0f00c0042c500083c8981910b5130140c001c2c80c491042c40c001c03020000111401d0b20010340d500d08021510703109040020407079008400304c014502c660080080c0803401082e00181c55411402090708101c40c040d080c028681c0124504409441c01a160076805042e20b6081d9200c07064241400005042c61780c0c003c0b05442840700c0a60700d5803251090789034600141c07505080700614600c440302004450b00d40c10342c417004c030f40c034030a0f12041c41e000e480862560f0707110892004a07034440310300b4074103010141d48480650300941c818801c0302e00348940355450360261441000510f82a034019074041091001d1a00b0010b04850320300c0c011442c40c00c00002181c3e144c422402540310101d00055280000034007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 505580539 1250 505579289 505579297
    0x1110607210c051e120c09181611071a0306150a080121020306160201021324050703050301061407050102190306080d0e0d051501030503031006030b010804020411 71
    0x1402003041c0341d2441d1010b031840e001134040745100202e0100da42c400c0e00c0e011040310304c000120481000d40b5a68442c804010b98005510302e50400740c10345004941c9001d1500380d41c012a8001003064001c103601000400140c4240d0301e0362111780c80700c441000580c061715190104c410040d81c49a640303030380742408030b0841c640c4060820b4130b00b00d0000f1074085180e070002c84e890503581403111584080c802e03400103000846200f840694142c1217140854003140301e00c00c0c141050034583c0000340c00e15611143c003040407a00b650100c0160010001c01802202c03010b02040e40c06e03c000d007003403401d080864600030668001401100f05200b555440c0304401520001a6442154483d0007035558101ca400c26007250a0140c20701d90129040440106545001182c407104e110015682d201c1100c8400e0100007800d50010801e50742da00411202d070074406c0440150038045c5000300000e581c1e80c02c0c410b4044030032651351341c0030300d080515201d1401000d0303911880c07054000d0b8040b40e0104d41804110480c9440d485 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 505581789 1250 505580539 505580597
    0x120702040b030a140a330c2610060f1b0201021507051201140303120613140708060a050d02130f050a1a060a0f05220e1501110607 57
    0x4061002c200e4001204814144202d5a03280c80c8800d03c440b1405801c80842610b00008006d1541400c14007168056841e4585d030740b500300559030f1b00c141850001d42c01c3c0707190240030901c514100400c80786441442c500500d00c925202c542c90544840c002d0402c01101030901494400440d00005e582c420420352500c03203d10001801c40d4104041e003d010b65114a0a02a00050f501d0000441010380d01c00968100c070081e018600d00801c01c3c458036442c0e107000f083c0a6001340f24641c00c0a0500d80c84c404d401d6120083c4008258600f460300001e010194014141c1c0e20403460032030140010f484282d90003445641c10345102d580c01d84c0112944010708806c03054905554604410848081100d0b0450a8120b140c00c0c41903020524900c02e00500d481091380c0203020441e0000700c0c1b000380303104800a016041000304031110b0515101c00c04200701c002139200381c0c1000c002006002c0f1304405100c2e1880f03021000d0800c0e400d150400c0c10b80d15200c00c1c00400706820300901e10741e5490201c40d00380d41c1c010f800e5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 505583039 1250 505581789 505581803
    0x182103140a050a18051b0607051b0a0b07021005030414060f18032d0d02030406140a050f0a0f02090a0b1e0c070306090c05060a030e0f120702040b030a 66
    0x201e032822040340149411110300001e241058109140f0359420340d83c81a8043c0c110003c0c2003221a8000d65141c1389840342e624540008081043c08042003007880016000c404410002c5560310000341002030f00051900a018072110800228005030b4642c60132041d041600e05020fa180d545504004c03650345004040c0158074040e0408101d80c20600424452161241d0349090303111182d020050f96590145800030021030300d02929415888000000c60450042c510000924040c41c11044500380c2e0000d440440f000c686980301c1e400d240da840800300d0750004900d2010006031810007180420070101412459000703a6681540715400503d404546100d0005009400da036503031001484210b500c000c2d506035400648610004d007007000d00c82155003041e07840000f400c1c09815921400001c10340d613142120307002c241c85000583c0d515950041c01c0c94040c0d6880000e13800f214080c1d03560806180c502e1002080d0021003c05111060400c26188140d8044c0c400042c0d198029010030f1400c0f0706000d0280c100c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 505584289 1250 505583039 505583041
    0x3602011202041d0115030c0504261516030b010f031a041103060405070504050108010b030601020a120e130e070311040b04020408100b19092301090209030118210314 72
    0x75080d41428100e45c1000c800b0118031544407012011101417250120004004104c1049805040304140d21055401c40820070f004c46d000c0303103042c900400c02c91034901c0c5281100411503002d034a0011141c10000c1c908051200c5209600001c1c1a800100411418141ea072450302046c8100c80c4000c51100e10090310420084000c10380c8504160800c0b80c020740f00b1410302001500b218490b0b400d880864006841e003410f16402d05030302c9100b40d003000b01100e04601c10b4040d9100821a0361030012020061a02c42c0003d140c90304c000d02000c0303090110708891250604040302d03041007000614070300701c1c1c0e00145010402d4076184c0000f000f92408004240c2d20900101c0e01060b40e150124a0702100d1714102d1040004032040010b0190150b82c00c00320310031101c06110300700100c00454100d034600d141103825011000112146100602c0e03800e80010b8015076010aa02606003400d03c280200d080c2d1001007101c18400d986c0c0d40000703024410682c907054100c0341d000e401c1814000e401c8007640c0f00d0610410145 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 505585539 1250 505584289 505584329
    0x121c09170d06050a0b120711010930090b090103020c07060f1706060f0307020a050715020f03270102030c0102030109050402040c1d060901020c0d06360201120204 71
    0x410740061046020391490203800003070781d01d40100180c0071181c24001090901d202d034030550030090401800d03803040c003010030040c03081e07400207110700d0b0601c904c41da40090750310310302800740c5080c851a198083c1e00c040c3c0c07001c0c0c0c40341419000307402002110b10415103150359091002c0101c020340240e09003841c0922034148086074003504464504180d05d8a5a6416000c6003004140b9880983c15600c07903800ca40c041000881c110011001113174000710070700440c0d0350900709a5501d4906121584201c044015820040f64100c0c7e05110490500c00080d00442c1000e040c040051950304280740ba03841c03214101c949888544e4024415603002d003280780c00131516907940d09510700141074121003c85c42245418000840a030113040c0c0162091101802460800307030b92410710117a0341c4144d034003d055100340d42c8070091a5482407810f0030224840c640100e074419100d40e24803220a202c2684c3c421210140201c80d07041800e000541401c6602440d00c2e11383c1c076400700720100080c41a03070045803040c45200d9803204 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 505586789 1250 505585539 505585583
    0xe0919050309120312010605031b1602031036050609070609050901270209062a0c090406051509010308070c14062209022a121c09 57
    0x448241c2030b0394118804030341424251310780c42200c220b2419154060018002144140c0c05140e2002c61041051414000381c042e40d41d141d041450b22400400c40401c540c0c00310b050901080045452251b4140040700b00103011180c440d0003030200038146400d04441c4a041c02d1400b29001311a9040f0040c0e400509003511003503100d01843c081c0102140718404c0018589c200807009504850300c20142020315501d0901856086103d03604402c884c3d030b020311800b40c9640c0c81c48010000c0c51854015111100072200100320b03c0c1406809141d0341d600030401000b034a44440d22615801648003500040a0b910b104120281c00f806c4980789801004580001c420440000004c00030503029035200c500865641c14540c482451100300365030455000d00c40700580d4009003900d40000303403281e003920348069100d000f503100301c3e0480d0400300c3c0401c44080f103c40590001242d0070000c082c0030006840b0050011070120100e206141c842c0c4c40105039040c0722030f41c000241d4003180803544c0c0000040d1500e20218500340c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 505588039 1250 505586789 505586797
    0xa020d09080307110405040c090c050409050105040c08070513030c121407080c12030f03070905090a0b100509120607030507090f21020a120501020301030c0510090e09190503 76
    0x110114040440100d0910350002c150b40d0100d52000705854280c41c41000d05c805441c02910460721003c43d1070b00451400603e005200d100103480d5509038035986008050b5050302d10617400140510318014812080580c00341c0c0da140e1004003070500d260b07641030394902042040d2855001030066504800081140d00d592451002403c1c0030f01c030941840038021001d9600c1d0200c038810110280d03c022000411401e1200d050508018a201500d052201c01e403502c40e0654801c8485e100000c030142c80c10301043c0340c414181900065400c204002c02d402c05c1c400310329a0100600004240f00000c41d1942c8a0340d41c840400074503100312810350301070382041c0f28081c01070801918050b0100300304a00108245140081a44c01c07603101c81c140c81c2103a461200c0e000b05000c80c804050741c00c030542400115503c1c1d1a01c03900d801031172081e00010327a40d41c0344d070805441c0d805481d045144580c440c00f201c0c10031180d21601c02010f0754065642402e69898114107130340740c4405089501c4052801090000502c1301c040050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 505589289 1250 505588039 505588063
    0x90d050114010e06010e011d041410031209120f08161b05010e180a02040b1801030c05030c1215040906050412050304020a1e32010e030a02041a060a02 66
    0x300d0b001da02c410740151480700354844e1050010f14010620003401c1d045254032002301d4800351001900280100e15090708510032110741e2001412900200100b24040030365000502c1203140030b801080c02c1c008161105400c0b02c00c0901004450800c050500c400a002c503040440c000d441c3c0c07440040781d4038003401d117448034414010144180c4100090b841d40a60311039000d04030020405289001000c020000301c1e10080c2c00c0210050342400081080203040c8000c01d4041041401d0044001140c0001400d50f41c580100c60100102031043c04000c00c0401c09450080407850440c600303e40e22400044041580c188619505c28104001d14003440000c2c2c0c00b0301e0040b8003911203501e103104c1e009410386880c0302c1550000d40103080b1a408001c0000b92b102c1000f4001c40300341c0f035210000d540b06440841d0254004000c04442e030503441a10703a8118115401941c94820f090154000140f100080d894031020360000e070103181c440160300c0107901510203250b000c82c401003074252181200e80d40207545482c1000b0b9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 505590539 1250 505589289 505589309
    0xd230702010b090a05070f0c08070501052e05090126030a050d0b091b1303020d240e190303090209010e0708011208090f0105160b150103091205090d05011401 69
    0x102d81013260714041d840c8201d580740c4a098910511800032a00d1b84056403082d5013124092040400196085c0116805100c03401102d440130002600880d515030300c08c0716144241180c9142c04c2202c1d4503404482c07411110403540d5071104d02c61180d0b800b80b910310100c81c0d950003030200060407518560044003503c2c0801942c001001003038924014080391440980d65410b05030b03100490500c113010820010b14640750640050f401595503a80811264041102e04450244200a8160551a81d003016007d4030300480e40c28810401064a4a80c582c1458441041d682414042c03410906000744c02040b5820340c06400c00f4040c0d07030755078034280740480705880040000d400d21000064500c0c3d00b03044107805030b030420000b0340703814141c20400c08286a250301e00c1d818070130b040c045601c7c800b0349000340d8000e0500400c644031151901c0c440f820301010140e031440b0705052805c0b24440c085180300c460f508200d21141082a80c1d21311200016043c0341c1c5c5d41100401641c03d0181608251780d03140c42c3c1e00d04030341510607 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 505591789 1250 505590539 505590541
    0x1b03020a030e03040807030b04050a0b091b031606050f1e0702010201050708190209010c1a0402042f090d02120c030c120c09060415090e0607090b0d230702010b09 71
    0x30b8054482c400e52040100b50380c044001031001c28028800c4a4106114004444000d40a0b65074240d10800481e0910440e03000001092480204107a4001d15100c084001d0900319026001c0750f070310192280180030400802241000511080904444451502250760b41d01408440c200a0300d0b0352245000b240103500742004113040e00e01400001d030081c0c1585941c21060700681d1840c00c000c0d040f6107529070400040302030010202d00034001d213850b072035222400d103170403842c0038018401590b8494150319801ea0000c8030f030348110382e0300c034080441e81039044102c1681c0f00c028100040f0350400350a0f020398003030807019803ea1100d100060095810009409580c0d0b0441d0300d10802034030a00f9080d803803401307800c01030030080186800010107500a00080000410041c0403180320310b200200c0e048495499650310b8000c0d445501082001d07481334561401200c01400c0c06d20142182c0607140b000400652074a00e400203441d0701098144483d111002228910703c1e0000000f4040d10581d44400d0180785040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 505593039 1250 505591789 505591811
    0x30708061b03090a03050a09031205030a0c020601060f0e030a1202070303030f020f0708030415020c070501080a020f07260a1706030a050705060d020f12071d0a031103011b03020a03 79
    0x11080ea0f1080a0a5010b0881040d098500f550f5951282c924207003046103400b004000142000e2014000e11555515140c480c42c21248010440703d0541c026015903100d1401040190f90007508a0000c0e840361400301125403582000c60302d0140381c058020007420251200ca5107085e0f000070300350102c0703019550500c145141151690100d04c98031605402144081000e00c010400c90070043d600107104050759030390240103174101c80807600000900460b503040240b041000d0b607800303080c845c0c000c1d140520461070915011042c0031a80720790b0500921169044070303482801100c400600004044140c0d11507621604c946004105001d07654008100d40a80000310380e2074103001450300030160380030004050f0507091000300b00c256046014800080b030380800041000126010103080d41b0080c13404c841d06141071540c000303044064070f0110160300c50315030f000d0b0031280d0751103441010450b5007000118510f52a404007090250500c9000340f440058003650031364842e6415401060b00c1c0d911a6020801f912000d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 505594289 1250 505593039 505593091
    0x15030f020307140604050907021510090b09010e01150c0f051507020f06070e121c020705010c0803040602070618120e03012c1606020a02190b2703070806 67
    0xc00c1c00644c2020042c0014807240c2040141039402c0142c5004a541400107040c10180710502100c1303581d0070b40a05076040109001a004051b0715903801c8074100443e41c14a0000502c0d0744051062100c10408510358482050241c00205119508242c007a0f1501d001c074108660b580314880e134562000c4062000044000b84007140191440b842c0c00080c150a84030340e54200d030a008217071071a641c00b210181541e24074a0b020052444031018412080101d2041c070000a400d211165001c42d062042000c100c0001800b050b048a90083c0c0c4130400580b1401d050070141c000305030b442403020407650003982d0541070000704c07110001031a46660b43c0b42e03010301c80c01040c5800d13121940044020011220f04000728950110404190002c030304084607c0407040710040145c0c2e1009030701070303c0580c0100440100350700309054019a9600505081d0301001e180011802051044100803250303110202410b1010f4a00a0a49465540000c0444442645600c000c9448800c1034a2003442c0320b00c2452901840011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 505595539 1250 505594289 505594319
    0xa080d08150603090a11120a060f06060503070c0609060b060301080303190b0d030806030a0602210c04030c091a040608010e15040209010512100c050307021e0607030f15030f020307 79
    0x4e56000d80780c603030f0b0180d840754001d0881c1030360264481c5c01c814010300d041000f009625a0f890140320041010301151a00c0e44c12a00e507508888200034080003003080d140c3d00308007510112a406980000c4c07065881c10040010000e5184941c1d000b900000000f401303100020103140a003158844040400e100084408100d6440503100354200e4100c1e001c0402082c0940500d0f644a240582a100c400e141030b60f0310803c03644001184007040c01600031360040a0b403058042c5a010b440c010809140604603154603044803a1440307606911500d4a0740040910b551036645495000c000d041804880d8582400c04c0c0a802ca45000301068840c1207000d00d002466100038a000316009000100e40e81d007050280045480c55800c2c0303c0c41d81c4600d42c00e905031b100c200e101711003500c5016520185c480c01d01140090501e580a083d04c4030560010301c1041401c40f0104000360072116034100022a450b0620028010301442c0c510f40c000c24907401c4000042c0700220310381604040c4220151203005841e880540540c540d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 505596789 1250 505595539 505595551
    0x70303140f06211207031806090320031e0118080301050f03030c0a0b06011220090301110f18061920060711071415090a080d08150603 59
    0x10222011a440307003814407040c1d02d14024032030031141e015010700703c0781e00e0301c0c040301400070401c000080c2c00c41c1810350015014550102c0d00c030034031480c0c500e000d1000b00102c0460201801041c0100e00d801404c007615913208100c01d10140986094140118014007a54228a4820080e50810403c4e84451a4002600c0300c500ea020100c0350940c1d0800c020301040500800b41150584010402c4000850f41004060707420782c40381c2c0c80600940340440004001d418000750318804a8185841510392040d0f0242c1d5500d0349646c84030a0303883e600300c0c80009004d0700e00c44001c08902080050860425080d0078002c1100009410581c1c09403800320741440b000b0300c20700c2880321500c3c00501d418040355101d40d42d4003251b018494103c001a85c11002c01c213060041c140c0b20b00c030200300716510b500400035051251a004205904503140c1c010384400209000c106400c4210200c1032000070010b03460358450104030050181c4104803400004001d40c060a41c0c2c0c0140d500c07054a034540801c189981c58080100e030312402c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 505598039 1250 505596789 505596811
    0xf1008030702221107060b10030b03060a0b060405040e011407090e040803060a0b030a0c11012003181e120307051812010e100b0d080a0f020304091107030314 69
    0x1003030300103400f4420751030107809442900c1c0c2c2000082041c01c0d4016001c81801240002000190031040243d10240a25140c00381800c1055911032a41c0108009034440d60429011603a43d4401c800100c0c40c1c8900d400066002c3d10700311201041400542c0001003000c00c4490980142e101c800003520781c0314051180c800300400000010700098000805180c00c0304014107080111611031807881031031780044920038400d542d0341c40000d10b00390303015804092148140740200700c0d19100740d4008000241301c0d80005404400040402c1d04004d811891000078014482038030340000d4104800b008400107181089141d11551424410001103141201d00951441c0c45035450f0400e5050103e0300c54050140c0c0c16800155280e03213488407442030040130030880c1d05030082c0c825030204104035000c441480c08124060154032580c0c10015801c41c0403a21200b0207070402c400c1c03824004401704e1030352096400c95108941800f082541c0a12810090191684a0346080c4503102120822010341e18048504010031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 505599289 1250 505598039 505598059
    0xf080307050d1808030a05071e050d03020703050d0905011508032803090f08031e01210813080604020108180c010e0a05091005040e0715260f1008030702 67
    0x500400183c80006280f0740e041ca5215501d07207485007541c10503000d800100310002103a50400c5100d40b103881c10709010451418101015403a0359641b02c010400c034034141580010f61030706240c010300583d0a480130300c103003c2c032140d0792501e061806400c41f64044000d24400d00c1e40802e02500210030b407240d403040000c2c420356486030030191000f103101200c45c0d1410315031b030b40d039005000c41c58038082c4100550150300c00c1070350b074203000031700785542e861404072260301c80da1140060090048a1905101025540300719003040d142c0c0c0e09103251984030304188000b052404420000c1c80303107004241e40744110f000741c8414110355114242a8040901c5080010441e0050311215940398015002002214005031094204a0f1a1808a00d1080b819200240c440e4800c000c200003030700d403030702491200d4444075015001041c40c0c11003171503405124039013050500c01130604401000320424030040311841181660040b9003094150b00074441d0060380c84928030000c00c6804260a6800011a1801603004c0c00607852 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 505600539 1250 505599289 505599313
    0x905090717070905060703090e0c040e060f1801030c0303080f390a030f06050316030b04050c06031306060e011203050304081204050f0106050907051b1c03060f08030705 74
    0x140d50700082840302440300b10070010540740c45400250030f0480c841d894600d201c0c2d00b0710581d500700d204000e20000705081c0402040c0404c4101b203240071340041055607180307800552240003c2003c072003490b4003a64080780400020910180c41d5001085900a4582034000e80340c2d5031003540180001c888110b18520310008a41d14040b80c14030903070001c0040d2403d052a200580c009044613417151800d9070000b52550705d220904203c0c1d01c1004014403040300242a00e00d0300300d8800c020003609101c050714140c040703000101130010500c02948582401030440e5502d02d007405a503401000580420703580c007441e00001155a44184048031f05803481101246586401c076a01202c81e684000d20460711000d09204110f40b4200c020b41ca54080c034481c0015040d800722a088407402c4588550003540326040000074001d04940080840b410410700020181040b003903ca10146044c0b082240f4600c0c1344100542892507651580c0320030150f4280000408000e035580c0d0386039030f99016004018007103421210f60140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 505601789 1250 505600539 505600577
    0x4020604060e03010b06030709063507020102040b160b13210504050405010806041a010501050702130e070906053606030f1014090f1b06040b0301080106050109050907 73
    0x18000702c0040020503444644404285190425030305003011035815402409096082843e0245d03006807911800c99204e15080c0b54066222941c016070074a080c450701162800b80700390101d4010f4030700740840e503568444544129001544006058802c10801ea002c221011401031107007481c0c54002c480070401100e01d15109456030380c10b1000b0701c248902084000342d2620b4901569000700100001380c402032906080441080c6030304103141000361014001484180e070040191031040c0e0f01510f10040001561791a100201a001580c400e6072161000c0003480382e0a64203e1001d0b04e4007605c15202d01541143c0b160050071a400583d405501020480717001c041d04882d2403030717000720000c2c100c0c0d524050303080340c1310b00342500c940a4080303e0f41ca5004901c0b90040742c40fa07960300861004002c00c100e001c80644240c603000c01c1201402e501020181822090b070b550403da03070180041100865880d6941c00d0094001d00251081c140440c1d1101000600e500d0440da00e1440b03685561164195000d400000340 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 505603039 1250 505601789 505601807
    0x6040c24090b03150306040b061c0b0c0d140a0b01030f02040f12171603170105090f0411041a3a0302010207200108060316032015210402060406 63
    0x260f120380c18504d00e01030079076040202d940a00d01460000500c0c0c2408402c0c0a104e41407850607940c0d544a2210410006e05268039646d402180c02c4000307500d403a0840c00315400351405441c041e0326890141c1c2441802d500c20380c0403403038075034007604c04101c21040c285c00b12069000e00e00c5028a840c016a8003049156000582000013520480c1384103a207400705984584107401095030070b0310788208146004201504490400046480c003c00c44601d03600d044002114081c00034200144100c201c004a0300300009085c1c0c03500f101038000e009202032602c501180c18101d031107140140c400c0899610514072550061580440f48072840c01004520b00b001c4442c3c192894140c0c030440071507608200000101d030140842c1614480885c1980369142c2c540000180350200190503a0310940000e4400000c101061400c4000c0f01c1e440301450070301c07417106050240405d0060102a820003d2242c44110703800d100c40c000d109520480c0344c81d00c811001101054400d10041314000e4001008010a02080d400344540c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 505604289 1250 505603039 505603051
    0xa030e06071103090d0f1704090f0203010e060607210e0a240c1b030606031208092805250806190e1009080903010c110304120201050c06040c24090b03 66
    0x30302d50046c5035507a0204a2003c0700058020020041000c3c080c160041c040c0003c001045d040640c15541801e83e054058180501880d00c00c1d2030004451041089554107101107081102c141010768000c940040c0c0810807804030b0320b1040c0b98020012602ca1025010050060038052500445000c00740c8184c0f03141c0d008078000c1d200089058450764030000c000300d1900145120340c202040161035442c1003000c0700c2e60001180709000c0f5460170451141c2c00010400da0601a0001d8540101c0010074400f10344503600750084d0580c002c0c0344000010300d4803551840081c0f0840300540c200b05903924000d41d19103006540d490f030360205c1c000c02c0c503c6038406500507038090784905091f200c4c1d028849183d501140e0070700408072283c020205841d40c451a00380306402d6005d0086c00d224601e51400d40760503480b0f2256015940d0b141c6c5040c0d0b0400306591180d401c0d2031031010103c0444030103081ca41014101c112581c801c000740540079450030300080a844450040000032501c4007c0118101245e5900c2c3760002800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 505605539 1250 505604289 505604303
    0x10c02010513120c0b07030c0f02011a01140f0c0312010f0602030f030a060801151502070311090907030b040b0405010b100203070b07140403030e0321030106230a030e06071103090d 79
    0x341300085600a200c0034020380f01520300060200030700d0310242400025114500a592409900402d1000349010b603400c071000034a0420001d050802c1e03000014051403041018254000c1110500d1038000030003044130303001504924250380c3c0d844d841404010708034018100141c20a0100820144055002e90b03000702001c900841c10076110031410b4211906480981c0c643c4a9140e010040c1d40366072403e44007401410320141000c2e17411a25004000380b203540f0100d001d45851030028000c01c1c001d0180e6400b035507004c1d002021900741750034080c0c500141680c0c243c0e610352030b01c254807202c0d10300b8150980071040c00d41c018505045c110745446050000042540e030a110000c1c0d0015503540445000b400903610a0700e81c0000a0500c0051502d00850601b0034032a480c6000d402c0c0402c2c1c0f00e40000d0320704459092038440703d1100662000f800c00003910803d09020300380450329006064250b000029690180c404842466070741c000c007101eaa400703004100001d074101b004544070340d06102d105640002c0c05091 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 505606789 1250 505605539 505605557
    0x8010915020901030b0d080703030e0c06070809040b0621070804030c0807211701050a031e060f060306050f06012d1806080612030f0901030902121c02010c0201051312 73
    0x10680c2150700751012503407c13400103028400c0542511403080c1c1162844001d195030400071011403030340c1c8100c0350301074803520022803600d90907911508001c0f0403850140603142c0351144680c1c036100240e00701c0f5520003014600c00000d00b503140b00f85a40b078403613a055034800500130f80984510102e17505c414400d071213808411501c0115400001201500441c2d1640c6002c42c201800c12101c403030007010380080d0712a41004c401080815002c500c5d0398404c12281c80001300c10f449500e010300c024959240010780b014241240041400420f5218511034242159030303000655070000110f808112000020f161426009250100f55440560f007c1c0b1000490030401c035002000b000c151030300802c80d80700b80c00043d04141008041e0a10404204100d000c0c900114140421845410000c1c080c8140380c504240e5070789040d40540d6224003808241c90080010350b1f00e018903451840c030140301681284405903003484c1c1c0d6507821920500c1214401e1100d080c40008030003655640d0340c062042c481d03600b0b0070004041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 505608039 1250 505606789 505606811
    0x22200d050d020d020c0103090b0105090712111305191a070602030c040303090f06081f05040f052403072c09060702160b0a030e011d070f0801091502090103 68
    0x844040c0d5810b80080c10b4075036200c00c0c000d2070014032051031410107040c03610100009102410300c2d41518811270369051141e0f50060300315183c0c843c1211031030140e410440c6026101c00c001c0b000301018019601116981c03074445050000b400c0900c00105842102104200004540030070f001c2d040d0503203c41007602d00401600c9104c180c2e0420b5560358084000000e04100701504031007994001c002003010464020b24114015194000c02030540a2800b40050108001031040c000b48002c0c0400800800182c21144549001010100c6005000601c961101c034400b2440220b0030007952402002030440030304004288048007150502070002c1200aa04a00b03c4001c04d601c543c8600c40041c028591451720110007440c01072407140008604106040a0042c0c1100c0d1040f108440c0300d134180800c25011950310340380104840c0300034148200941078010102c00740032402d141296000743c20340d0390b03c2e52107140e118222000d00c00b0041c000480303079030320880c2020740e50060701c0d40311014107000400c1580d00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 505609289 1250 505608039 505608043
    0x1508060f0a0f060801150903080a080907030c0303021b030708030d0e0304050a03080304030f1b0209130b0106090810231308030c03060301050a091205160c0e22200d05 73
    0x55041030001c82c4c0200c0051103e40340c00620904c0a034000c0c40d00c503104502d1502c8925043c400c4d03000c0f190400840031b00141201d0820024200151b078040d4103c08001e039207040007505c5d40b125582c0c003101003840c011070203c1c6150001c4c1ea001039850400c043d40c6040041d00501c8000d00d004080c0140d1404103000025103681da850581001758010a5056601c0c90a480c0091105188001a000380318144684107801e22035003507040c41d03c55058600350303c25141c000c1c600c45020701d80d04c1c004141e0340a04c4004035606030b000c82540101c0b5240e108903291507161040a1083d2030a900359104150811141c0d440342c1c042d5000341d607400401700c440c00321412001c0c0c0c40c0c4102ea83e2040300c88001e844400070501410341000d22a607640500454010844050070b43d0300d039000d003146a4a540c2c1088004500d00840013181c204000543e6840360154115a9441400c040621030494225400c40540c0c1041031071400022480c2c80c140c1e40c0043d800301c102d610707091032000c6400110f09080d0852004040a40000c1c42 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 505610539 1250 505609289 505609319
    0x122a05010e0f0303010f03060908160303020c0d0203120412051c0c0e01031517010e070306050117060114100509090708060a120b040807021f0e0a1508060f0a 69
    0x900001c101041c81d1403200380703040c540d01c0d4100d10b982d00800c010003003403c95210903c1900e6014402142005d030900f0300f85600e02807400f0394211030140d24040d00c101500340d4024803904440c4001d9582d0001400c1040c0c2c1c0b070b40a40964001440719440000e0000764810600410030705103420110705208141480f4901115804207003401c0b40d0781d804103401c9403600000b00182c00c5100746030901c24a4003c1685c3c12a503d240c2c071483c9904c4011080c28689048203402031000182200103c0c2d400740e94030300f84480548002c1c0306e10403950601e6500c1134400c580200d03400341654543c507452b050a907007500520102c03580e00c0492000304003050140c000590b03161010740e030040400f43d03a03018a0342403500401c400c41003ea4000300c155059103440b100015032142c01d03c1c4d4000d810101c0d0b19221042c600114030a440a188136001464003041741c0d45405808c01690301d00440280c85600c421038580e030900958000c1c40c0f0400b4040703071103c0000ba2241c074107021802c1c2c03c0d031005001c01c001c007545c603180400c60280d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 505611789 1250 505610539 505610543
    0xa020907140409020d050a0204051f120e0a02040e0307030c0f1a011502010e0d0219080903030318010e060105010c11030703081912110405131e09150603122a 69
    0x40c0001724003c0000c91401800d8001642020071880c01b841d2030009148000c01198240042910004243d8610b0107a0100389580450300401d0000720001041d094884090020403840b441c0f4107a081d001440000007074500195158450150702081c0f61a4600d041900100854074450100026150064074031852402044070404449051001403406802d40b0190801d20055030b01110b0700e600c1040e40011080b05400343c001c00300310070200e241042c120520030300c41d40c80d8040c4400802d1040003e055501c0040d0b01c41c001c0020414901c070809180c0d207c4900b8400d82d40024205901640800c100741d07006c2032607240040c1100e4103141d03030766600122900514020f5410709003981c070f44040145c202d000030440c80c00c0c400781001454400401a2214042c1c0d0140c9400f0b032403510760b80404107009078025403200482868500d10b007a41c000064000e0080d401d000c80da2111081d00c41e03070340d00c0c42034020113060748d6008000702e025001c01c07801181d4403120124440d01110b1500040b542c007201301c200144040d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 505613039 1250 505611789 505611791
    0x21c021903031b03230c1204060f1e030e030d0f1e021e03131a060103061d0403050f04030b040819020d080118020c010f05010801050a0e0a020907140409 67
    0x64510300b006031841c01032075581c3e03903184100d1841d0b50000c0d83c0120144d814401d4000c800c140034a22554445039800313003180d2002c0c0d612030b60303260012004005002e8000c5a00c16503981000e95003040c0c04440381c0c0f001145010041c0400501d1011440c025000b400782e03500004112401c11b43c2c0b401101041e10170036041d01c1b654580e03555540001c6880d816814840006041d000c0d880d1200a034076400202ca480300d5000344151011010400328900c144c969181540c02141c201c0610300c1d10400b04010880c15103807280820324010b00020801840c0361000740c81e103c880c00462595469407019070f2a46c1c44480800703202c1c9020000480002c920442d850300907801952855255031764991021405205031400f80c00b90740c45903542c01c2403039138000319960548a816003250300041b00b10380100301074019040b00030b07060b50901b40d2141003922298803c0c1e0484071a1002803007251203818240007124082c0d400700c0d105800ca031200c4009800c1031040c080c1c201c1813600d40041004510241006640c009400c005485 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 505614289 1250 505613039 505613089
    0x30f0302160618202112070309050112090506130c05030d03020409050709080a08160b13050c0907021509030403060203010b0304031e0504150e0301020406031d19021c02 74
    0x48030202c030a0160501220040d0002030701c0410000b0f260421000c42d0541c2c440d000620045410814055452104c401b280e1490301c0b1001483e01403c80b04490060741e0010302c0880b0001180c6e801402410b66050708032019240980794a04041e0120503400c405441c5400408000a010b481c1040200c03001c0134540d4005858034201a50681a00c2001d07000c2020408403410510043d0b0300840c0383c540107640030071581d0395200c141c02c06040b6000a010b01900481170101003103083c1100401840601d80310308151030001c459003080105014040d00e0380e5006911403c004c0010559403440186c11403500002c81e0b0a05a40b40d882034166403098000e800501c0f00803040c00100b540001e100192121540315a415490102c05c005205004034410b5008103c001001c06001c80c0c01100803910458001c0d00035991941c40703e00250240802800c400d581a030f5109030090084004541c4150301c414090b00c480d10310040c0d0b0208030090482d00c080c035240124100d03400c8016507c890220b10340841f200032603051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 505615539 1250 505614289 505614293
    0xd02010f050a0b030c2407032d05180f040501140901170a0f03110f03090a08030f0417070905010608061c021f03060308040b1b0a030f0302160618 64
    0x30381d03401800407040c00e81026012890f640d03010800419488042e10a418445a441c4800204041c8074080c6264184001112010304d944110f299001030000d00040c00d0030815159128921242c0d04a0440003030420702c0324401920000c070680110000082101d80e10851110000d008c5a10aa00c9000c1c26034000e0a010030034242141c404e4010300750f81da04203150504c2c0c100d0b1207486105280e4020120500c01c0d01740c00c2094040e6071940318401800c000c071079040c00c00c0840c0595aa108903a030074460080d031100058031000010031290300e070300046002c908081c40c0490900f020101d41e03a40c1071590040c0b19000c511111075114683c0241241ea568004d031341400014070031000d0f403203c01000703c20750016614002d6104d42e89208407041081c001a52142400740c001c41c0141041d820040440800080005440740e009000e044003402529454468688d003c110556864541c41c00401140151904100160095019118020400189103698540390756074804807441e42228031034400f907030082081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 505616789 1250 505615539 505615541
    0x1050913060e07091203050706090b07031d010b0a0e0405010e030f041503090b06090405240a0506010e0d060e0106050a0801020a02010b01030c1202030c0712050301150801050901090e0f0d02010f 85
    0x9003203c110b0602500c1075041c48a9000e40c804520000390a01c007000a0000800225521003030300d040d08001000000d080100005010340f020307008942140000404604a442c0180b20307001911200810300e164007860604c3c518070701c4034003c1003603c041d507941c0f0101c0c0111206000502c2c214206080c0c1316921406c00840c148022058500701081600d00f1000ba00020200d00000340c00131401c8800100c941c1e41d80c5020f500c1c0c0900325400c003400e82e80c0da10b080303a8031120f05a09140034401c00402440700c2d544030001191380501043d58150312180d04080c40c00440c1c5680d1204070242100400890060348800c0807904e07805861780041c420783e60000340c220250360b0a00c51049040e0007468123000100381440b009140d4101c5c2005001035a90000101d46150000c00854404541c401d4800f0b45c08103640d030014209420920a80002c03c05499450704d040d44a601d405050b9213000742000081d90800c01c138500240202a0580f106100fa050303100d984440c1000052400c14441c3d002003084821090550 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 505618039 1250 505616789 505616791
    0xf1b03031707200c120d030f09050c0904080c160302012c06090d020d06061d010803160f05060a0f060e25020304091b0e0906010f0e01050913060e 64
    0x30109640072000e000c40d55500a00244140d18001e84124040032003040316400c003122200c10760352020410406046851021584210a05040d1020041e080350400c44400b55420038200030115040310b1461000f42c84e02d030398002d800c503000d140d032541403401c00d030f03c1c0d9454414221010020f10010100c00c00c21980c0c449107401301303020780c41078900e04c07000003c4240849001d4911060f02c00d00022030901915152074500b680c001384c00400c001c1c15141913050000c0144864080c25954946072013031160a500900d850314100d60070b2000451a04d015055004007011b502e10080300c408080a8100010a40070022680113010300900012001f4541d01c100d0103c4006600520030628420200048100703000d0030390030340c80314240300c80f01d9031400444128118440c9801114560780707001c5a1390701d10301310441616001051031701c2e00c03040460a01e0400034001c008543c1d0b20700003800312114076a80351150508250301201030400b103040080003000140301c11902031000f0034403a0394040400c00e0140f030f40151 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 505619289 1250 505618039 505618067
    0x1412090102072108010501050d09050303011701200a181205100609091e0c050a0b0a0801050d111003060914090d080f0a1e0204030302151810090f1b0303 67
    0xc022a0f0348141024240303002c1481001d0511902190302c0a150410350004440300f0340c0803055a50f079603100c01c080c035011020301c070100700030b50b18001c800e02400f0700000341840c50440c501a03140c205025038070102c1e5003c10904d200003000e200440c0028503c190410500c5615100d50040c1ca1031404002c0d05c038003194840d03409070340c0036030404080001080036401b903200c001003103000128842100d410820821030f401d81c01030340c20018480c400685942c42802504034101690341e185001e076030358000c200120b600c201000d0b0001c11084061406480c08482d10744144505080100b4015a41e26a003802c4030440c5034554903010b21b140800050740420310401a0750725050400d4030f80303410071032504a2440b400a140b00c0207103070b075481010f28900321001e00c4088201c4003a01596110b48901d0005d4841c401014401d08608407100410110701100f150902110b900000a141415960032520083c1c141a20300b03507032910380c0c1c0410300c0225100c2c410a000d07100440c2480da100754a5413030300411949070b10342d170 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 505620539 1250 505619289 505619333
    0xd21030b10050a031505120d020607080601080112061103071218030e1c0f081209071406090a09050a02040611030304080a111e060702010b0a08070501141209010207 72
    0xc200ea55a03004030a81c0c0c03d0400c0e0780f60000d1300c0313006007006007500300d0183c00c500d0b401801c01102d21440b80000035044080d500941c20f40300b258076500c5c000c1c1c480609c1a260136000c1a620341c01484494a40f102501c49203019031000300e184d0314102c1c4009034540c0140e0380d11001a004814210409241c0d0041c101070008a0030760010325419500e0040c68100803480507031055403455a414928151780007540012600300701c400078548828904000554800c840e00101c8140d10000034074010004140d032021550500201040040381008100555018070790310781d8818940e51340800c00581e58828284540d0344000300590b070b0703030a20002508240f0710030030821540e4800c00800002951030700603220041c020b41024822046005001fa08120040c2007604007024410180c035a60440004c00c10f0242c41e49400801009403501d0900c00f0003015070080c20b1480c0d100000c104080e5100c0d00d00105012429190305040000040ca00550494242c03680f100750f0b90041050b80a000e0044c82450b000324031504 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 505621789 1250 505620539 505620559
    0x406050904021c0c082a010f0f11010f0f0c0206060306040f0b1902031014012d05160f170405100c02030f160e0601080c03010b0304020d21030b 63
    0x20000310b0b45002c0c246408a940f01c2000301200704032065207000081d1260000b9100346629803a54402401c00c4019070700202c00c2c0d1000c1c404980d501502c0da40c070040b0500d80d40d101e50364010001c1505c0305c11241c01212806c3d0350f03650041d000c42c0d1142c45054005c0361104000726141702801d0300245030180c05032685201c0d800aa00340400103c01c0c41341c048203190301c002801002c0d9640e03011810031404150f6682002400002005150107090461800391403000081c9046140c105c4c00444140d00b100b1401c4a01144d40b00f400c1c0c50340c0124140480b0b00551a1038030720300e480c034400780b00c8160384c4007035104a54401140d0020000c0101800009100e07010b800209410301d841c1000050361280289185014800c403010f01c002036460a000d00014100d418048810000348403190f044000198490a6900a040d401044443d840b0b03100310341c0505000102c3e141981d0030031001c441c680d03001170b00490780702ca66940c2150015150706860141c250a003030280b248036902c0c10000e81920130000c00342e4468003203c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 505623039 1250 505621789 505621793
    0xc05040b1e0d33081b0a0f080312220204020a030603080c0d0801090b031510050d11101106150607020d0b1f210516060503060406050904 60
    0x19680700e11442038024110480400c0e21808500c6551407a07a55a42041c8201100a4407169010400549843d40c41c03400b4464030880b40c4412402d0058290b51717003101e030710003007200b51000041e5005580246a6800c040d80c800c010448040c40da80000041c1d0008100c03424650382511103542d2084000d41e40f4008807080c200c800a42c1c2000010003445141c2c049074118030b46209a2280703000e158090000e660303c0300d04d82c001c965101824804440022140740001c643d4403014000e04103103a001400601c4043c3c4858100100043d0003041c41850341d25440c00084e859540a00011409002e05003c60505a5403018410396910390110034003030010030000001050000168240d000074846410310300c00e20200006111881500c9002e0350101c00661800180310302c2071061402250001d22203440b000428075151b00d5880a0320801c0c0000302e2030b09054000303c40c0e01801112541c030520540d2132081c000d80060501c100a83c018500040011007045202d00300b81c810b01d8081c080c03c0300c404070589465 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 505624289 1250 505623039 505623059
    0x10612060b18040f060c031427030414120f0307030e0a06020a05150603030c0a0602180d0b04080306011101090c031103011e0b03030c0d02030d11070203030d05060a050409150c0504 79
    0x283c0b40081015582c1c07004591b40358400c0c5c0c48804103c030300300040101810845c00a030381d0040b4010000d1902903c400e85980c070141c0020440341212480d059103580701e81081c04108070742540c10700b8250f20703004a00c1304600c0c545042c4001c0005503c42e4490300751201c8a801801100340d22034220074159030002d01c0700e01c08500c001420030001030044909520658540c40841c0c00d40c000c50075419841d01c61085c0140c2084131640282000c101460b488092402080041000140c0d4180001c1c01400c41e4030003080c0458a65002182d100300c040c1400ca51120a41d9013040c01c442a00d282a15090110030050080002030040c80102c41d904074002c0c4039a0380504512040d15170407101e9004110340da804803080589050050b03540007007881060384e84001d5000d001075120b60000030303d03002c0b091802c118030340c1c41da400c001560703289034000e0700643c10100d02c0f2040b40000c10b0080c10641d44508001c00000729580e8602800c10304603c0b1341c401d00c40022219400905583c2130628103c2072007418071080c4508401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 505625539 1250 505624289 505624313
    0x905030c0d05011b080103050f01020304030c030c02012114010602010c0f18091409060702030f030f040f05120403050c0906030c0105070c030b070504060e0f01120e010612060b1804 79
    0x112007114440c855860308900400c00390040c01e20251084954807040394000c000f0318101c0c0e0150342a11821442d10740a14201e02c82210020f0104122480c0c0c000070a00c40c0b0a440070551060510030340c188211180b90341008410301001140c1d60701d540030940b550b100054401d0042c88240001d105200c0d10400c0941200220b0940300c040025000703c00c03003100c00b149003010081906107410841441e400a000d200c80c4c004492a0189101c0d100c00301d034a00b4800001c60700c503400e1111226003036803165041e28110035405002528955031240d014000b0400078042c400c0c00d01980b4002c2503a5600e03500e81319046c2030354008014400c3c070030203041105944001c90b049042000c24a0311940d0384041c1d16042030035103074603003000c1d0901002504005095421000400503602252103039145043c140c4200104600f40414460001d050f401044507140c1940c0c20582c00c2e50070000002c10125101c10240c020010080402e03101c2c140c846000e1f4500382421881044402e07031400c050801071405071a0000d900303107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 505626789 1250 505625539 505625563
    0xc0e01030c061d130e0309090702030a08090c0904110613080615010306260f160f12150b011106100905010803072a08151006051806071b09020316090503 67
    0x42c07117032981d04079442c0500468070074040091201000e0300303140350300075902c1d000391001c40f01189855022580c12171001034154048200103041c400155100e0b6500c2d940c40c1c0f100501c0301d410460601040703000510108060024002c1503000380810300e055007103100002103034600b4906052520350140020616000c01c0d110070061049400a8100c101c0210351510903205a91007803070003140d8015881d00440e410350402c88440c408042400d0340c4138543c0b000401c01d503090081164210290917100201c1c0e81c3c11035140e0b2034050604219510fa00f0008501700b420440364240304c003515400038446e002103842118090f040100045042c0000c035520b10a0412300200554411201030070664655800c00d4981800b13007406205548489464500d00741c1d0544080e1118a000c1f02c030b00402080b03c41c8944141d4400301070016038040051006006e00a880d1301440d42500c9210210705904085040b502c1c025004060a8200503035038602050340c3e0740d1840f03014201c4010040314103401c010555001807d0302e500c2c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 505628039 1250 505626789 505626791
    0x90b040f030801090e0a08360301060608070c1410022206020d050a030b0a0f09050703050f13080c0313060903030207050409020109140f1203090a150203160c0e01030c061d13 76
    0x12004d4011801c4402605001000000c2e1840c419481280380d803232070340183c40a500038072070980c5034503041e0303400601220284c0c00a4850504400428100594045c03031049000aa411042d00c0c1451b040030f0380c1c0502d41c00b05000c0c1c250111094814140480348004005510103003068412000000700140b10b8083c11808050320341c0c11504040c1e07500292a0002d0a07107018000d160b80d91001414003400d021148140840d1408002500e02c2c000400703a50b110b601d064101c20104103031039484030a01d4000d601d5001d200d00c400d001513042c6586034480c3c1406000d4540b201c00c0c150b0b103949402403420140c0c0d0880d602450070685a0300060341c01021a00c2074955028000c0b104018240106240e120842d0300d0562094854895064504010004000494040e120300301526282d091b4044505c1c5c00146080060748104550070b003280880c0519002144184c3d80b0002c07080d5a64a00658004282c1050310100900e0700100b041030303007120001e600c22071a42a400601540c0070009000300900f045050345807 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 505629289 1250 505628039 505628047
    0x303070c1514180424150c020306011409240105030901021c061a0306031009140706020d0f0e1020011e0c1d0103020706090b040f030801090e0a08 64
    0x3203000340e640d102c0b498803100c2034986802000e40d10200040030410310501a502d04455034040e4140e291a2020310010310b9845c0300c1680c94500141d0101140200440400032034101e0a401a541400410300820342545d90b01036103510300707003041944030380501150440c090030310480d500da1015070aa095884002d0030959103ea960003841c601a2003404042c400001f001c404d550910182035020030241c0b0840168022012410850300c4088d02c400c0d20156032691107000746560705082500011040c6210f203184598608207091290701d4401c4039002070700580c2040754101d0300280c1c014140c1e0805504c514090006038041000300b142c5220700c000a00400c16829401d40f070220080729080380c1d0809170f1008010411f140c00030561800e81c1402d001c0322443c20f010030000c0e1140300384106020403c0e6480468201c001c08030043d402540096421038405d502e0383c2c4610017041c0350310081c5225034095111031783e42d03890074074009204060507080200e80900c0c01da40064000c20000380d918003582d0101e101070791 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 505630539 1250 505629289 505629329
    0x30c02040b0d0501050a1b170a1a1903060b010905090f06010519020a1b0f061b0c090b04050a061d100b03010f08151e3606060303070c 59
    0x10002d110316001d032442d0b00305010304c4516841540070904100c446001e4108403640a02c003150585a401e4003220170b20048400700b001481298042421101d18060010340f0059020100d00c0c805401c4100704d85030781e0554400c10500c46140508600c218007407074041415410700000414500020303022078000f08402e00060360320f074062000c9501c0301d8042090390b030752007180d01402036888100040444042c002e0f010010b90000089600806803000b02c01c0b08a05181441e01c1112080503101804a502914102c0213004c150407109541c081d180c040030110340500524140000c0e039501900500710545840d000708401c0128030390711148500512078461080d201d100e4000310207101500514a0800004000558070040c0c0303503007000700c84e440c0041e40c40c0d8034035190004178005012501c454024020f04507000c0040c0700d04406551148039503264a020164040c0d516040e0710342041ca202000040962201070303a4020071016134881c108500035440e08440b0b54601d01c0c003428912032500c1c100036000c41424 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 505631789 1250 505630539 505630549
    0x3060d08071103070923070f0f0905101706150a0f0207081905070602010507050403020112150f08012901031805031c0501050d0c15030f0f02070605070c030c02040b 72
    0x9104000b0200c41030b2944036508403005000e44200344504980301b4003c1c4a4010810341a40d05c01e201a454002103075000100c286ca500414400c4c6904104242d00041016030f100f00d042e200300011039586002c0d030304000a40c0300428001078442807003020318a241c00a01701d41c54049a004c01c04e149400c4240c8605103a05030314101c09a00007104034081c00c140c002c5940d01103002c01903000d025004842e6655a100030a0b401c03a0300c107840003c00039104000034070165010b110740c02074141c0041400505100640000d0108003480d40140c1d003030f070400e001c04116601d030902801c0340040000260ba5920300c1805916601ca92311458094140b549400c01000d858a41011311100180c120040da90350794120761076540000400824a04124500300010407d410000d40740b086407a0702840e001e04450811000003958400030411b0403c150300c815000480e01d41a004180a000d401c05025880f12a00d25151099881c020203101c1040400c1d904203020030f40c0202c00c01d00040c1c0648001030308000301804a5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 505633039 1250 505631789 505631813
    0xa0207022211191b030206010506070c03050f010623010503011701060b0c0c0315191d1906110f07140a12181509170109050a0506010e070503060d0807 66
    0x7405403402060158207407001d003088601002495031007528507031800d03440750441081501d021700164800801032143e82030402c01041c601d4090404e80c00e104c0c2d9207685041c03801807503140096181e51588000c00a06401ea1070a0010b80d0110300e1031810310170341e0700c0001c185000502c62055409070456580110034000c0d4007a80142440403410b594a1240c517442542d84c0071b400b40941e010b4819510042034030307560b64101d180141e1100300b0420b203035610300003014082d00c142d510032914140c9003111030140c01c0041120803003100c04244244520401e0b8103000c01181c030030032280c0d52030a0f410404d01c603000d07004a0403203c00d158880701510f441d88150041c01d140c1402035000501842c60340d0582d50003103420440070080c012440c104040c441e40c507607006800301c20056041c04082805120280700c40001020070844001c1088000254041390f52996403402c1c5400701d050b00d21350000030043c0407400050501545c8015203040141c40c6040040201f10700781c608400281c00508082842002c00031400440307 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 505634289 1250 505633039 505633061
    0x7020604030c0f060e0402070b010909050c10090608090c011b170d0f0507020f0615031c0302071203051515090a0e09010b15070b07140a02060604050a02070222 70
    0x8625120b845043d071035008035207030240101003014100e040e1038914050080702c04242e4481c40c0b5017801e91911011402404400d4011607990180710a44107490b110080032019503030007561404281840d1030740240081714050207859180d080f41400300b13a243d800c448440800a20a8020700c00c1420b10308044911541c401f41101c880c5400003540504044107401c04111082e10306001c124586a00303070282d07500c0b540780b072904405410420014610031100801800b9805020f17055440c06c184001c620480000800c62500109074085655820701c02c441905520041850404001c103080c88a50900565522080988100c03d5035512080c280c0920041d9104c2d03003c068480a211901e0301081e050a12044806034410f41c80c00342107214610f82800c132055411400b840c0c8920b0140e00351034000380c5240040c9800e0600010300188a0303c80f481c50018042e248495024200a0805c60100003e0351030203003481d41c500d4014081303000540d80340c000b800d07081d0340f6020810401c140c0320100d55016003a09240 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 505635539 1250 505634289 505634303
    0x30708010f05060a05040b100e0a05041803030c1119110d2409110f030c150306090114030d08091c0c06050f040c060f0c06020c010c0e040c0e060702060403 68
    0xc03101e403a074940c11081c082c1c2030031151100c1213500c403001e0000b1503034452100b6520010452078108980e000300c20ba81064034001c0d0140e41391546940c040341c2996000a2a100761503100c404074000c0c19070510a44100c1840c40c41c004400305015400c140e40d50180e9210b10340b0310050210450100101035003034281001c40034002041072400ba04154015a03090002d0710001c12002c404101e508180b84030384034240343d00182c880f00015885081c0415501c00e006030036014401c01c6110507140d50740700c8881c0c080788144507045941c2c0c41c0c158207000f2145010b078800741001c0e501d0048150305a9000c901520744a9a0b4941101e0940d5a030f00c1c1d052901c2c1040c040095620400e80d08407a07550390080038210310354040c85040c0440d0310380001075940c000084a01a0403020401814480703a807040104480c1c004a40c90b1071140840703603490300c03412a0b1018900c00c20320380d90b84594044413078104102d6008424100d9003040300751400314000d05254135080600d44a0640080c3d81e000f190f5440c0180c40182d500000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 505636789 1250 505635539 505635551
    0x2d120c090a090c0816050a1b020a050603042a21020f100302040305120702060a2105010f0501022418210913060501020c010f03091b06120905150603070801 68
    0x1000c0e11a58003502d0712981e40c03c0700000c48400078003803401c81f450003801303a03201d0348030b07036800d4658030480000204101d0b484a02410f00081d15581d05014600481c000c1d0200c18040a480e100c2240345150203c6da01e200003070002d410000e19039220020b01d0340c01c0c10030015070f0b0301031b04910004040c9028202d600d540b004040c1d0008000d00d034998060002d4a01c51002c07102032030840d041508480c0550308000398000010800da0b012980300c0c0c460b20b0b10f9401c0301c002c4504114040800041a079400340c0200b0004a1484420061583c0c100041e1695609a640c00d0440109155101e0603400d4000c21807000d03182c105a40b40920042004401c84841031081003003240e001d406085406640141000d030b11801a942e00e2003841c01046c4204021140160001c069000c2940010340c1e100d0100780d606400d00d036a4807401c10106401c0c048a0f0012044400e40400103070500101170030a100c04850024200c0c41d1104107800504000340c2000152060b40100c00300d42e41e0880040c0c500410b642004001e9401c1c25 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 505638039 1250 505636789 505636811
    0x15020d0e04140f06120a0b04060c090b070807060c0302180405060d060513120801060c1704170601050307090e030702091f0e01050906010c03050a0807050c032d120c090a09 75
    0x80855402268105e4419484003001c00a45541e80300032000500030001d90743c040f0b07000512682c80f040c20384210741001640c2d256a40d000039895041751000f560360354000110802082190300ca240c03139640e0281411401e1007071440d0030858009001c050580140d039240045187c0c0d80d100500c410003103500080c24001c42c07030014003004074400014811240a4910001e07104110f015402c600c0c181d50050303036068066030103615000f445260781e00318041580d200300800301e5200ba1209880e03404240c0340c00240041d501d8403042c1868841c1682c001940c0078503115402da0102070201c21108030790f4040310107a11a455814801c40e0031820400202c14914202c00c002030440406010b2a040300d008a92a4615503550001540c0100d00080000d00040d000c00024009600030b5420b80d40051a0380761190400d15240c080502e5980301c08110240183c61b03d1031a0b91804a0100509100c0440b0408038140681040100c01c0003501a01d140004100807402200544611032080002c0103200014081e0341040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 505639289 1250 505638039 505638061
    0x30316030b031609061202010813020a0e0f2e050906040b0d0c080106081f182a05060a0f05031b161b030201020712080408070602011515020d0e0414 65
    0x140c844c0840203030410100250007903480700c16004c0703160180c403007880950741c03140e4000031449204412030380010302c91004200c030340402600500c80d4803180d18100003828001140405c41540100c2c4454500050840ca1a20031206110b04100c4406407042596038559000180181191818054018100103440c4081c400701c90800021074071180d000708643d80c0c0300da800c0c070340301e15980446298500b11047c2c0c0840f040a04c2c0d100c003450b41c6c0d0240c60300e058459183c0e01d9203065480d0480f1009003586000401e244c008800345028000d10b02160006d1030a11141d07406010310b5800c00c0c0600510101000040d94070940442d20484a10244616580c6a2070b8524202c10350402c06e00030344040c0c200704000241501003004103003e482d016002000480d180c22480d4200107102c40c8100d030001e006000c001032020382006080064a0b054001003007a04107610040d8041050340d200ca80ca00f00070f000c410240c01d4010906000010403032409500c00860a000b2034090450610324400c1d002c001384c1040812400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 505640539 1250 505639289 505639333
    0x604030e0a0b0909060d0f020d05010b180402090c16050a0b100b0715020a0507060e1c021f0c030b090403082401140a02070e0f1017030316030b03 64
    0x421a00d40e40c0e01a100da00002c070902811903900c1d00b0009900114a951608495114000c0d200e0089000c541c200d07540030880f03680c03074120201d49580d1202c4040056181541088051422a4403448014901a000a03e00d40006041038101031400103038003550070385403c4080b414640220445000d5105454501c0c07211b00c080f0788000d456461261301003042c026030000c469810703400c04000d180741c00d0092007880096000d10351001c18800204030281c0054810300070f001841d04d004025060b45040e031400c0c08940c0642940381011074105241d68242440c044401900380019000d000480c05458034068006161000441d43e20a03860320400040544c00518180b20701c00c91143c01c1d141c8000c4880714070000480e08800f0303011546076401c680105042c08082c1c10030096620444071070a5445902105402003624000e61302004507013004401c5070b00405000007808d902c6c034808500521200c2c15034807070102811640604062800d040d82d500d100380c21600310380d01e0003010ba52031301612000401807008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 505641789 1250 505640539 505640567
    0x703062105070e061305061315080705032b0c1505090c0a1a0304080d06121a0123030a08160201020c03070f0303120e0613031b020a060507060e060403 66
    0x20030b02901207544000b20010f02d02802c0d0103016003030f01035101240c520161600800c0b007508200e184413030f440840154050800711410340700d15410382e60300b021907035401c107455900402d010f5402051340146404400141640007100c000c0800017000c0c20401c11644600d1054015050342c0117100705c959031041681c0601d000c1c403002021182c1c07060880050080314102803060800d0600780c2600c4080e200740b40001540c1c86841420f40f0340c0340c04820200f030f40c1210b0031034204014158a0721003001c20401c8230245860340c0214842010f0142d0f16110700f0540f060344034100383d10002c56611a0141a44040040000726503101e24038a0b00d6016080000e811101d800d001130780103116a04155002d810089608800d407801001440c4007a429a2802c3d540a90b03040030a501c82e0386e8414245580d001c080c00028003904010720703540b40742c95032414002c09503001c0603900000e5101000c3d80ca00160381310042541286c9103403c2480c6c540c1c0340ca0404100400c41c0c030005d031440340207501c1040308150f44180c8a0007003071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 505643039 1250 505641789 505641793
    0x60305030d1d070303080a0b01020a15060e0c0c19021c0605061504030b0105042c0705012706080a091e06060618051329150a02150703062105 62
    0x68502c2494550342d80e054031002d03021480a5010440104482c3c010714071a039010300460b02c10b0721881c4c0d2070840c048580c42c104c070507443e030b03a02052140100c4001c0007504081169111418100448a40b5455883c0011010503c08906180f9400c646a1b240c030040d400880c44103909800b400b50034807001030101100e42030f01c260b4980e03034034003031048505007a03800b07a07500b06030528407a03802d020a000060008520801d003010202d41c19041e00c2c0514074221100c042a10007608802e454000003416144110042082d000085180c6100390b81e000029582180c0e071a107001301c925100c5201400c020b200c2a04007605040d0300aa01d070440c0074030100c000c0c00d8030f4415003003000b4031a41c4110403241c6a03c00e030020000300040d10003c00c41440c100c40941c1c410854030310006076030a55080c018410f281501a954140e00b02c001d5200182d190146514041c14002440d262800322048802520f0b00c0e2920592040c0354050808586490303c40c2d071168014261146172001080e0000101c04180301211104540754 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 505644289 1250 505643039 505643081
    0x1260a0f051311010c05060114011b0804140f0108060d15020703030e101b0806031606031506180e10030506011e1d06040e0f06011d06030d0c02060d060305030d 70
    0x3d5441400304ca40f0041e0400064175050b400c0c14060f10f003150814040c4c40c100030f403220005c00f80054400c03a140080c1d100d41c4105607507904d4202c4000e40c7d510080143d5100e03c110f00b50203101a60458845a4051021650207150344001e103414000805041c544014107031002c80d02d1410550150303c901941d0f0410011211200e0100c000001a07500240140e86041d101400385a4020702600c1e40d650400001000d98455803c0494051120740c55680207000094072001c0616420068121901c003034008d500d45200c4c20003003d49041d4441e40720b4070607884001e00501c000741d040420780c00844051640401a2049969110110184e442c2e13244108428000740440016503c013090516032640540d460307a5140039aaa002044014218084042880d001c0c07800558810038040c02500d010b000103110b543d00141c4503180031000007000400d0740e4020b030700242c55003402e16004002001d8156045400654031240b041c0b611028000ea40d100400c1444040b5411004c05400d03004022915550b94490b00b032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 505645539 1250 505644289 505644323
    0x50f0a06270828050d0b0a050f0607080f07320c0f03011404081c020702010f140c0106030507060f03020c0307020409030203070b04150e1902040510030b0408030702010b01260a0f0513 80
    0x120801f9224080c0d2101d1039041014403800d040e005402102e0040c94602d0800c00710307295180441d80481001c40d0300010000e032140d5140201e101d030f07440311220340003100807a40140c48515503d04031141038034421400ca144802c03c940e13094000800f9410001c0c0741c1d070268101840d1000d4242c000c090465860110000a003050240305d02c2541c5100741c05131b50b82400104803510075145034400000482c1258001c01600010755001d0080b40000c602c504010f001080c504080141781c02070304a268803c00d0f004101504c02030350001300360790286404403000140381d90940b40603851840b83c076000502c0d280411b000c00c41407041c44500d084104002100c107000207440440c6158892034840c00103080110188440409806c01da801190701c40e40040c201520581c070b98482001c40c2c0000c0324103c4400200008014110780e080c0a9404811004e00f030280c1c0c18a042c0640700c0030203483d41c6c4d06010f40c1041c4e400280c1c000303007075811402c0c0f4044107401c200700303e040181d41040d0824081005403040401024000d032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 505646789 1250 505645539 505645549
    0x3030f09100c1707020103140906150103180809060c070806010305100c050a14160f2006030a0e030d111207020c010504170703050f0a06270828050d0b 66
    0xd0952000341c1c22141074031040480103031340000b03100340d0406030754030a200f80f040c400303a410601904450f00280391034501070000c901250106244a410182805102d81401c02910b242640741503010581a8442070107001140d418010348000190354485d6007800148031001050560590303010300c4c1507400b1181cbc00f1000500703440d024103d420000303100b08032103030501d403040450b002003c84021160745019121210720484001000382078072090702c00240d0b901004180400020340510302d002280705c00b105000054018000185aa0700c0152101914070303031598240103d030203084210004000c4d088040120038035642200e100c03207048156000104050500001c2c80740d400000595405250a0420540e048030744600500e0426500c03a401c40400003800900c00c144007800d40c0c000820001203a0304140055403c0000402010310541c0c00c3e070004104005c2501e04100c2d003008400d556502ca01449080c620300d911640c211600489582c040129406401404031a900340010301c071483c60102005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 505648039 1250 505646789 505646807
    0xa0c030f110a0b0928060f1e020a14071d010821041203020703060908091507320f060a0b010e0d0b060a0e09070515070c1e030203030f0910 61
    0x181103c20301151800d80303001d10488006003085001510560340300d10003607044441d580c0000010980907401507589136400380183c0c0c035103060303100c0b00000140c0e0144065181d43c01c1c0c4201806414550340c910401003400c01044000703240749411020a02c5401000c1d940e600000e0096040b14041c010411001043d00412210a0a03001c901d092a01d46004140c5984014070b05c0110300398002c0f10000000f04e015407080400084c001c17094695241c0d8180300b040304581120010545c5007800f404213401140c0f82402060111080700300e8802420b204039403480201508005540d0240702d21446289030307520206459004040500040c040c00c03440000651782400301c18226504101b00481400228000042c0217412910180503100c0c81915031250040c0c640040340c00d00002d6004020030010ba0801003103000710304141401281c18001550707214004610f10340306a5080c080e48a185283e18500304203614001d6600401f140c1d40c480701d2664040d0160824400b452113045400c2d003414555000312284 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 505649289 1250 505648039 505648049
    0x61815040923160f18171603030c1b0e091005061c0609030302090d050124060c06110d0c090512030a05070b1306090f0506060613060c02030a0c030f110a 67
    0x4108120701c000116986513500c4242c0e410400c964207100e074022034040b200e070058a455645e0089600c0c84140041c601040b8003181e050014130400c0c1000804e5000901868007503200d00e481400c24100b030007083c01d001d219007054040c6028130052008a4100042441e04c042c0c02c06400d2041d0fa0f1032034200100c1e55801054030030155004843d600025000e40e104d9000340d442404e0040c20062000c0c0865500000c001040320709079591030f00b00c68035046403040c0d5042c83d074542d54484003e50621900505000c540f03100141900d4489049031101202d2105072800d000f0f80403c100218001c9034002440c0210610406002d030841d989002c030165408000c40e0407000c51521014906078041e682d901880c0e01c0207205000210b1185103403400030b00240555a2924011000030500361030900b01107040c8040a00600d00c00d80d000c100528507030b10032a80c140704443c0c0c1e9081c03200600c0c015001081c24507825000c000c062041c004001300400c0712080e5034040075401003003030003100c840003000d0041110080c090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 505650539 1250 505649289 505649311
    0x30a03060e1012060e010509060108060c0307051b010b06030c070204050108010e0319140d0903030e07050a17280c060309020d12021608010f1a061815040923 69
    0x18054141a070a50203110b41c424440001c081c4d1741000341c0ca0850340c003a2094501900b102d4010000790b401004015045444a60014a541001c0001070442d101e080d800300c1c054920030801e8005d100c003e50240c200c10038060095541d9213410b03080001c035076018603401c034400c3e0710305000843d00e404144144102555090003c501e4610100e1040c1724500c0604481020460f8921140080c007540801030b141c00013418601103080d900c42d150146c01d81d51092482d1041341c1c05010704200c40c0c1e80f134105d10012a6900c200c0000390b5004010114100404120404c01c1c0d10a4200815a401000312660603894007031905c01e100a525641c04130140e541142c4080e6000600c4004500130569035090100d060025004541030f000b1000c40c05615000103030300444060b5500c0088400c02a0f0342d000e500300e0060509008141d440a407070000303240d405040c00c55502c01c91f48405040c11521240002c3c600b04000c884c096842c0c603950152440038009622041280d26074440c2c000c4011041c4000b000e0040c070500785 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 505651789 1250 505650539 505650571
    0xe0a1514040b0a0902071203050610021e070803030c04050a0807030f110f030f0a0203070b0f0d0c0c0c1719050d0c170d0e060610081303030605040608030a03060e 71
    0x30401010740307001d0203901da200f840c2c02e00c0010031012900c002c1850a1192484100e40084010302070115030004007054051203190040c11f85065003c0381e150382101d00c2c500c64182042400d00c00030700c1d01082e13070020b0070144400424010349032442005481141c02c00c03030700d00c414940c0702c080160720b031082d0303110091041e10300d08880c00004802c650000c09150010700356481000c443c4000920300b40c0021800c4600b904810303d42e000b5800c007131151901130495200024038040c4084a03140c00c0b40303c0c80000d111100d50b1034070480141441040409601d03034000c01c035a80070710303211a5040550030100200c500c0f940f0640070045a80307003001008062503038000e405041e40d14845138040d28002d030024000c0352000b040700e80d420b25100313050f00540301c0036501120010b04505c900b15100c3c64a540a01094460030000320041c09082e40900d0150340f20490a801d9070758103480f403400790f003c0d1035681c000070f40c454109000814410780001c050010328007942c3c3c06001440d903501d1800c03607070f98064034290140e024040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 505653039 1250 505651789 505651829
    0x90c03111b0a0f030c02030f010506061213020306010b0a030b100c0308040620042c04230307030302090102010b240a05040b0a0203040e0a05130f020102160e0a15 71
    0x500000701012481042e03400b28049541c2e540100d0004240c220042107407a8907800070340c24100106440c401610008010500301000021068018440030491107001c000c00a042d0758250343d141d404030755000d02150f01e60f5848041100c01e40d002040c0000000b407603c0d1030f140203454007a04000c400b0301151030386000d54030583c4003184c0d80c52000b40156005519100c9000c14488140c40d02820b01400d8440c1c2a15a8241464003050480500881100c1c450642400c0d90070000c03a010a60480e901420300b240112600d40e00c20400e48050320b1000135400040341880c2030640540003002a031800364000c02c82e080180081028089245007206506200c1f02203045250b00108010408075940c0d003445070403c1c1da120000c5080c0e5008041041c0181c20200341002507000d040c440304e4000441041c10b1003a4a4800428030110141c0e44001c4c01c0d0f0100088004196402802100480c3c948155110f16643d101c9510f0b042100c0d09890010840d498070b6405001c500b0324640c1f00094492032110002c07a52440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 505654289 1250 505653039 505653067
    0x1210060903171e0d0609020304020928020307020a0b0c07030206041205090312090a06081b0a0e0405070c0c0f0b03150a0b03070804020a090504080702091f0b04090c0311 74
    0xd40015038046000b00b10b50820062100c55000d0703905100646544e844840700c1c0d40200b5925554071803242d0394014000c0c880181d4480344080c0c2d018016245003092a00c111202d00b00312511103a400010070300c00424441059404210f100059014482050940c0c0311003101d10198410842d010b0016045a0041000500e540b252481c000c1c1c00e5117845030511041034002030030101c40300301c03e09903d200041c3c1040c06050112040004260078109041940b5003c807031000c000d0703e0044140c201690004a90344c00c180905071100c40080090800c0020b490588405031000e80d46245c01c1d152170b11075220000b030383c290000d0302c0390903aa01406c5150030742d00c032400501402c980c680c4480b588001c0c1e100f40450405608400f40d07104107066600e0304500d060600510511892503040312135554100f0082201080b24101140c1c000d40d8150342d0049150307510b074045000f0349403105c5aa882074140810010b0364841e039002501c1590005001081a00079180c000d808803204011841400d000c2446035814841d04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 505655539 1250 505654289 505654313
    0x1806040b04230609010f0504050a0f0602040f030f0201021b132003090601060807090f0e070309020406080a151401050907020f01050109020316021b0d020d02060f1210060903 76
    0x204002d01d21400c04021122240d403200303030308441d22540c007010800542143c00d000302180340740560b808000c035003410303119171b9215044660060a401140300900c1c0c02c200d52581111300402c1d000d500300009503101d02d0403000d200c1c401d0070280e00521030789519071840700208151a805460040840c0803201041811a016000d20a401c050804601d01118103001d1180c00951190130380c0d0015000300c2d81443e40150002402600c0c81081160b01001441003c4042104000380d4000c1010424035076560b035002c0303020f0a50044002d41103405e010307001843c0301d4000f031114400e40c482c4240c10440307440000d110045405040844145400300b100402035411b0100c0e005800c05490720698404002400b021425200c2c283e104140705a800010041c0e002c00c0040368501521032407018217103a0b010344080300c490f881c104001c144030b41d00d101826800c41d91440820582598040c25098a4007400307441c410440e0001c5034059000040d10740050307000380d008c220034010381d43d2076103c60f1600741c1503454140c02801 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 505656789 1250 505655539 505655543
    0x60601032d110304050a1b18020c0f0708010606140903060c0a26040308070f0210240305060403090b0a02150a09061a03120405011209020f22051806040b04 68
    0x2654a071002c9418100c000203620880c05400181500307407051174107600c01000040040d0508090303a0042c00646400b000764101c3e1030060170301503142c490001c030142c180720151503e060a48109100090414419008081200d0413521600031008406072940054400c0c49181036164002400040310ba014a002400b086000762400806002e1074a07a4005500c00c0e8900b100400d2110300100001c066202c84d106500000741e02d45840413940d90709000e90360b443c0d4605040400c0d901c5070500000f40040400482c00003200d080c0c403000c6681d8900b8080e4131200c080d03505800041440724046407034501c0701c08642600300568000e01202c5c0c6401d0a05610180240c9990b0110f80c4566010010420070f00818611024800309646016010002c040c90030407070f00280346000d102408100410380e049005151400140031021680034003901c00070f00080401954a5072040369680400c0000d20408001c1d000620050b404102503110140460042c00805203903003842d0b4040c00000c0c0c0060740c0b89044a4000e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 505658039 1250 505656789 505656791
    0x60207060e0f10140301090b0f0402091f050f1803012003010b16170306040b030606031509031e071101021218130606051c0e0d0f270305060601032d 65
    0x160f80000080b13402d42c000e82c040100d441e00c44c2103902c080c0c601248110241e07041201c0841c44d203582900401d00c2c01040020001c0300610002011720030500a4040702c40b10300f944424aa030766440d00540340e40d0034140c0d1007810f000e58a00030142c4950328074442124009145086110708503880c0141c040b5542d8081c002ca40d00000190314510001045540b03240d012001c15440d59490349002000e000031113054229040c400d1303000905000302c507200400d200404840410300d200e250b50b120080d00d0300c1d5105008500c8444440458041010022440540040c9214800550000b000d0f2030049944801d6424020b1594004003d440e1714013940300d90382a980300001d8590780082a4000c1030300b048900c55401000441c4c2d0000390b0459400c0e48000e040358002c4010070400440b007201e484a03079079489001080d4140107489a9040050740900050140d84007004400c800c4000112565940c104003440100c950f4401e40010031060b41c081c8c02200c0407401c003c4c3c40400301c070039482c1600c481841d40b0079210581d5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 505659289 1250 505658039 505658057
    0x190c1a041e090212041a0f010605180d030206010501080708091009060b0d0615081b010e060c010903020a0c150c030e06040504090b041101050c060a0914030c0106060207060e0f10 78
    0x60300150168141c811304a000624103424a918075541c01c20b20110b4602c500c00800a40360f141080c03e50544070700789049500c4400d40c6100c1b0804130105540c6590102040105504041c2d00258580c180c03042a038034100380b0b0719400b005456100082d00c100c0302c140c0103981c48020701d84650b401542c1d00c83c05910003280750fa4007200450004404910217844594a4011004200031101c0c42403004120f101c0041444a00c111300040340344242c00091410000a68280c2c80340da52040d007550360505035a0020015108107160103562141c1c204402c9a003003c1d5407a00040d001c1e0310350b50310b9000d45242d403281d601481280c0c0d81190808100c0400c650701c07990900c408038054459228000c8814440c01c6140c4a90900d81030005003820300390042410050100b1109114503804500543c10840c091404592260b40d40341154040d904a82c01016921010550021454054201e0f40480d0034bd9003e6a44140e103c250840d101c2448502d9140c0200507502c6804080c24064180b802c0a06245030000c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 505660539 1250 505659289 505659299
    0x10121107060c0f0e060906040306052701060e0708010e16140a080105151e090303070f1b061805010c0c1a0c0c01090303080a020307020c03190c1a041e 66
    0x200e502d049180307800152200e04052441e504404044e020000c2140d940381000901c10009540b0311607400b00420050312140410f56200c0100204c0d0090038028500c01070100002c04628024004c4d446039a80c811001008110030901890300340741600c0c0209400c584541e40c0320f03241030003094501c50f41010401d04403000c1c01140171040181c0392801c3c1a030346005940d4902800c02c2261098400318501008007000302c81651202003010b026041c804080300e40d1940c05907000071b403e5018945010700501442151003003000300b42002c110040c000c070340e8001c2203281c4903801101c982820558a618038102400306005543c0030360300c0b2540d82882011417080e0320f9213584c0303049042420032554540c00e80b00400c10181c1d100381031180445050007171170101007461440c0c800510401015041e201c2e01a07000000c190001c0c42841020000c4202904803002502054284034104807094000c0d20a0005c9420101c1d10b0840a80315441454079215490b04242c1040d5103201490000100581d4040f210000012 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 505661789 1250 505660539 505660541
    0xb1204111207080f060f011205070801051e13020306190204050a06052d04060c060e060f0a1503020f060a1b060f050f101406070b130c051012110706 65
    0x101007400d5000d0a0300300d01c0c2c00046494032a041800803038640104003000140c00358000918115520400041c81709070060800a0500300305400c000346650900c010040744280c68a412104c0e00c0f841750982c04160703136201e02400340c400d500100941c187c003c1008112640c04410101680107814200103150030b0b0340307400052030058950301140216002160b4402c401d03072801e040e48034080368a55107085000001d58410326502c1580195414400d0120000091050540c03091400c0c48c0c039201119050b0030082401e603003c000483d13000000b141010312560391441c0003100030003180c0c0d000d41452000982c0e0800c0007115000b5003c0e24040080d0038840507000f080100d0008541d500a0078002041000300c1c40c02002c1e140e0041c610004035940c030091185c907403034026a982c2110407400915242c041328100245043c812810090003038040c01041c065110244030408114911030301c03644098555030030511050700040c5490102040c407071404420341c1180742e0401100660342000300351030f000090381d07a44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 505663039 1250 505661789 505661809
    0x30b0604080106050913110d031101141f06050405040203310302010507030501060503040605100b0a0215150108040b0a020d020a02030910080112031d06070b040c09060b120411 77
    0x100440c0c3d100c2d18204054248244079a03007156410140c5489144242c984495890003181e000e405010909082c03018107100d4591102d60b941904021700202810880c01c000b06802500c091b01c0e10014594000104c0c202211032100300c81503522500e00f0300d480c0c4010030009400043c601c000b61951040000319003202c0c06036500d071000008100c24201140d40c100282181e00050500c0c090525110050110300d80100982c2c0d4010703440b0001090f1503a80302003441e0109865401081c000c00d000ca4503da22a80200e80303032a698840d0440b107020349e134540000c07007001103414000d02c0c00b19001c94041004180c1c01d1403181d501c4030144002500d402046003511089a0002c800c500060304003059a84661030081c00c1601c5020705441c140c1029414004034400b842c80d0f8110007414029505034250b410715074480f140c2580c0318020001d03034898189003050038001008840482c3c007000540c5001c24054030078442c1070291010b99103802d00b001d080b001040441c10000c1d005450b00500145100001d95840402c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 505664289 1250 505663039 505663049
    0x21209210a03030506090708060d060e060702030703120204050607020d06020f07061a041e0902010e03060f010312030504080d180b04061508010209030c04091b140a12020d0210030b0604 81
    0x1d081a0805040c01811540042c0c009031048180400784104281c0c40042907801c010111103080c1028400e24212000701f61480340c44015002c0c1c4400c2000854001c0090101c150003510f8500d070031062401524100c6c800c0b07000302c59001c0820b01c0800094108030b0440130200c6e00ca12001450030010740180401c5822582044607401e8441440d148070340c4046000310042e0900707030b0b0180309010035140003c1c0090f08518000b010243d541807c002903a102d8000052002d0b070207419915941006020004c032a1400d01055a808440840f2456903078420312034a4440e170740100700300b414100400d20b414090840c0414468041c0404e0703401b070b8082035010b0342c0c2d203006910845000404031b90703242c060965020039901c45a4580d106000c0107071140c0340072900010fa160220785c001503104061500040f52132018240702045c414080001c154071111030f803400c0015008440c4003580d84e54581c142c007000000ba0b000290005241900e19005081130703583c490341a005402c1c04282c6094a0012075401d1304260300c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 505665539 1250 505664289 505664293
    0xb042003070f0b09063f06031b1512060108100308030105063f0a0209010509040b1507060b150f2a0f030415050408031207050d022a03030702120921 65
    0x101b801e1403800c8007400e243d800f2078200458051402c48000703500d941a02d040705806410307000b10b55035181e035a8144c000f42c10803040c05c104d0b243c1d51003d04110100350111402c902041000c0c02049280e45076007243d500b1250301c011040e01d160300700003c0c0105c581201400c951003c560340030443c100f03108803c400034003042540d0003204400042102d01601c40014040c12000c0b0b104000004903039912000f150341d0742c4810340d00850102001c2020030b8101c0c00c0001c00100700300d0302182520410199030401031014004031184150702c14107054a4080f845904078401c03406100300302044900d1192002407504041304110220944044840c0d1b070304260600746940b84642000030180101308a82010002114591403c0d0382080d080201180d924462038030702c1ca0141c8007042c00140010304c1179049407200c8803141010341d00d03601505402200035240d40180010386046010508120300c0000641c0e2240409900500468030700c134680c584585e021807051a0449022104c0180703110034051844d900d14030542c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 505666789 1250 505665539 505665607
    0xa21050c0307020105010f0f090207080705390105030f060d051014090706020d0507081e300a09150501060503060a060504060905040c03090b042003070f0b0906 70
    0x1000078212217058105100317900362200c0900c420323119000c3c1d40040c0d034603a400040c2d4401450800d07000a004081c4001c046110302c0304090711b0902c010071201c00185a9184900f9003106010840310358600c2040b85500040007400002c110b4100300365401d4006101600341010720407107440d50350400070200c0c1c007204601e8072104442034800e0440c580c10b60000915014004450410a0007034540010321018400c0007000304036402402210800c032891121900b0756042d80d0049800040726541155032010201501211030f40c652951241c0f0080d14207c5446210801e603442582202c01090f40b400282c5109050549240101c1c0b0503110b940c0c060621a25a42d4980c503010080044c0001d480e0018401c1000910040004030f41040803481502c200f04d9001c9010700358410218010b212615001d85032100e0001408207000145d616050070042112100700c03101940800d050707460401d8410207048030889001000800e0400b4060718800400900741450407049005107140c1c0ea1001032401101543c2c45 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 505668039 1250 505666789 505666801
    0xb040e0f062a04030f2a150503060a05221503060507050c07030303110d09031805061309020a0e0306090c0901061d0d020609030a060b0411030c0a21050c03 68
    0x115a402c038814075011444901040780a40d04650050b884014441002d41c0382c0c01d000c100c10f250020014141c286000b2180c0c4800304920a10250140b01d0b0070004003846240c0c40f1641d100e0022207108a801403c5030301507600c1d0205000500403009040c4c1c2088140049800d0b40364600c0c0031301c0c40340d44052a4001c142500754100710089940150003201440810005e0b80b181e2000420345004880d01403d000400d280901c01400451041d048a4030038249800501010542c115030b00380d4800d6a0000001d696640329428840c40c0c1c4640c0150a056215485080141c1400da400601c52a0020b2a12401c1000c024011a203404001c0d640c1000c143c11114425804c2c0c240302e00e80d04c0c0107007002c1c83d00c8500c0c1c098800390101e40800caa19414041c23030000d000c140c155120076003280d40480d0081c0403202100c0c1c2c03a0074010020280700f01071601c55814050014581c8080c01c00b528001c014074000b1528100001c9420b0f90b40d408000101000e106189082e805a07454501c1024494090400c003a40d130380c9001c07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 505669289 1250 505668039 505668061
    0xd020a0905090901181104090b04050a12030c14090406031a1e06010c1e05120d060b0f04151205040c031101030501080c060c070e0c0703120b030c01030b040e0f06 71
    0x3000152a41e14004092035140a4010456100d6811150104030521b010021402414522001038444141c507000c0c801009030000c0c6140280c0d00560004003c0907000070121f00f6078045142d442c00044044480c80c8120710036070300a226025005000064040c0e072a503d000d521401c41c80c210400905407010482e8081002601401400302842c140c0c6091a081c1e0029000b40c3c41781e10050009940d105180040b18000f0124001d9550080110b8200c2d80c4070503010f5100340d00540c08140414240310f4001025405002a03814115185011074200340c24100031818041c4400c66400810402c0400d800306100785100e002c0c0140e01680c803000440781142050074170002c03c640d519042600d0000100b0034110041138000d00702400b1626950380e0069454000d1922046401c001440b0101001b4440e400074510001c01001d0322030340316154144803902c0441c00b2521340a0b00c05ea09600400c0001080390712070750014000301030040000078041102540907140000086c61111180c0c00031090281c2c0c2102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 505670539 1250 505669289 505669291
    0x106060f09090501030f060c0302120405010b0a0e06090708341b020a260319090806040816140f060f0a060b0d0f090b0f271b04020d020a090509 63
    0x502c5009200e59499981d43c0032003a0030284d4041c04007a996103036502c1d02c42c425012104540511198400c2c88e00781428614002c001c40301c03880f0710602240c000000c80e00e0f072058030203125081c010f0090302ca6903640302e416038205000030400341130030f214030400b043e41030707242c041c01035407255014035a10210003003460203071610480c00658049084e01081560060b512190b8400c2a036100804100001c5070110240c00541610502e00301d441c00040340c2c441c941146030640305c248600c6640c407860039955941400d91144800e170350140c44203030200001c7e00e03050400c8a1001c000b61007442d1005903843e06807151818203070140f00d080c0513900480c09009403a0010100c0642200480c40c040001c07501d86001401036218003481d114429480307401e006290200e941c03191070480d130058030408061070012901040420101c0d041c1da01d90351074140c2c18500308014505e40e00b101320300c10010a606544003a03400d42c1c290040380280d9029800700a90345000312140060850003600d41c0311100030608201c20002c100c44 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 505671789 1250 505670539 505670549
    0x70b090106050406080c101418040b06090102060711030d05070314090f0a1b05030a0305070618120c02240703020f010b0904150204270c0e030c10020309030106060f09 73
    0x104113002400f80c10404621102030000441d10281c080381015015196024843d0840c0c00b81400450b4004680d024400e07502580c680490b820032550908504010441c0140350120f401607104c00c0016001d1801020118400581d01045a0900070600d0308001515021100c00300003c0d110328000c0e5032001c80300416504600c1b11005040104e0072100e0007695142e0700c201c040d10124140c101a1002401d910b00311000e032902034160b490010090a000d003403644915000c403000352410013800000f448002401004607880307013060a0824507498100c444998460040ea40700790145001c569200e41240c81032021500005519290302e10350401a04203054000408202e9041c104005110340e1541f104d194410361120791450340b10341d081c0d907003802405290001c401c0e445001c40381007544c1200ca4901c40c0100c0030010b0911a04800303580440b031034807450190a800d035200c0489180d0703914003510203d020f400c2504c1241d0a14620707200090071f6500c04d900200104031560000c0d60815807010300c42c1d0141c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 505673039 1250 505671789 505671791
    0x60510090303050f1e0a020705031603080306010f020f060106020f1504080f0a0908060a0623010e010e011718061006091a0403060923070501051207020c06070b0901060504 75
    0x51440d02c010b010341c811928009252040020540c02c070942d00c800c111380e80c2190f4905a902d404070301034065981c03c01805050b2191160040340e120314540d406001c401c0e00d9000707540c0c03400d6449030b000555503c00119500c105601030010210314100c01001214003d00301340c1d00514440307a1a003c802c1c105884031207008070ba07003007100801c40403581207002c544446a462000661340c41d04428100d902c0d07030a030781005800e80a42400d03c903003600b0b00d401c1401036588400740a1003408010400090045000c1040d80c04200d0004405099600a285801d51501c042c1800d80c0b0f80a8000c3c07031134080710b40444103c080c282c541001c2d420b0a1504020703030307a4083c4850000d107000c136051a001600036441413041900f00302c240318030701d0000d640ca40181d03401075511003824884205149030003d461013080c0100102c5074160540318402480005005003255010b0f15003618209220340794000b407070402400b1000307601c200050550340c3e40b0b4440040c400700f40184040e030014104aa10305d8203407400d0340d101c0c2d8865 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 505674289 1250 505673039 505673057
    0xc071401020a1a090c03030406090807060c1a0a0b0a03080325140d022b0e0304140103150b0a2607050a08090c09090a0b0c0307080c1813060510 63
    0x40030841240d40f040040c0004840c3e41d0b98600300540f030040fa000119030180070214001a0f2188c105a02109441c440b2042d900b2440d100d5804451443c0100d5000e03110440704c0d0a230f00c0345482c1509038180c210f00803000c0400c000d40013402061a80d840d950080b14080da0000410020320345030f07505c3d801e0800307060b40c3c41c4100d100b2207076000744900c0030100b80e05242c06000444e0800307038840e5412283c010240c8400101400290303100c03450201603080b90128141d090940d0600a808007000306c0d015034040d8005a401d0045820045008281680100c1030b0390021140208612001e01c1c00741c4541c0c1076907614150303000060f0701d8192180c0d50102e030182c0094619820302c214180c1203010380300503494602d8503004507a2510001460520351090007604401000180500000003088103100c0d079004035882d401d00d40342c7c0103a104103407104a41c000c00242002011642a10501b80181500011080b0b80c48601d10702c000024054801c0c2c0420030041d9580b15004c00c0305040c84200f0001c2d544503420b00d4000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 505675539 1250 505674289 505674293
    0x19030215130b03070e0406030f0b090a0b0c0d0f02030406020406121e02070615170706050f032a0f07150207110609010c15090302160b0711010905060c071401020a 71
    0xc40107540506a0012008070005020501c56081d041e500d94005205100280d96800c05014040b0041c01c01d680b801440c1d800107030450000506400c0481d4490b440c404103940d4507a0410702a044210700390b81607030300d61089018510050000d0344c01a0b0150000595440c03601c007024210342e0a4000c0100100c0c100f082e850143c0d008030f41c040c2d4002140c0c40000d40e4a66180c0b03010f00c000c020f5904c0c6011400800356001c10f20081c1e0054525074a6207400440f4a0a51688800d80da2801882008011040c00304002048003122202140c4042c40000340c2d0310319249103151b60052a044200c000c030000c0d901040716000d00c1003200f00c81c05031010410f421031411821f40c95265401001210440c01002c0006d442d9005910031030140000039001003ca034095440354000f84064800004144c00601c101a031310480706030078210803021203601c05081ca107044a40e60307070004084c0141907611306211180780e00040c51348171fa000800241c229040070b4080d10707040c00d400d00301030884252070038119400780b031000c80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 505676789 1250 505675539 505675567
    0x806100b070611070206031311032e02070b01060302031014060a030504170c010209040b0406061e03140108030909010608010515160f03080703060e3319030215 70
    0x1c449810690114200391101c01043c641e00c07035020000c0d0450000820801140303c0140b0b000d00700c03803040c011045810403032010550384000c00c1d1461598688149111105c51010b00704008003240d0014002d41841035030b407509414407500340d010001003a0000104070044240e002200090809014070050345441003003c1151030103105001003d06507210b001c04c00b0b2000805280311139030a81e6031442d540300e0340034500b00d010390090407540d400b0368103045003c2024540750240600f65026561b038090940032604a0440054001d4043c406043d92040c11545c19454003000c507003e081e2000082d6511001401841614401648030404108a00c4010301565481211021114140f2003401f911340c103845503014214240060300400c106056400001015000003034548900b446440410805590710802c00002408446c00c400540ca060994841180359030035000d07400001c0d07015440999411008a05141c0046003401c20f0070030400c81c00c10852401da6034000d40d814800700c03190700f00951000304039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 505678039 1250 505676789 505676797
    0x9050402040f06030c210b0a05030a0321020702030d261012080f04090608062a21070320190804050a080d0b04241401020a0506100806100b 61
    0x3020540c4405d10348030071512841503a1810122141d461280580d60b040e104001d00002c802e5500403458890001040d01c0d02140491850b07415446181c0c10100201484400a03680c25124031010750074481c0b00e0258504102c03071000010030b03840340d00445400101c00c4411940d11900b0220800c44e40040010340504090b2303102c2110001114841c0c40d40302441d0480b410b0207040340c159510701c00804c000841180c0380e0031240c121000002980d20540711304644002200c40d07070388900303000043d088907028039080a01c0142031815200c005001d40340a2044401d034150015100700b40041e0302e45484040e50300b400c2c03014984081c8000711f00c034038007009040c2c40c1905c403d240c0c2c10002804850f40018082c85000d00c06074a145030b009200303a6555003080c00c008028441040500d00451900002c1c10707003813a05051503490b1070441085804024545420103280648060860b81140a001c02c1040060703010001a4055021040c441203d141071000c82450078000034140c146000d9424400c00c0310312190030482d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 505679289 1250 505678039 505678049
    0x80f090715030e030f1806070b07081306020a021509010e06060d1103160609140f0d0203100e0a0b07020c0d061802060a03020a0207050928181209050402040f 69
    0x8580780a092000540c001d024010055446000020f41d0709010070088000b0041140368041c0034002e000078101341b04442c0101c142c02081001500007050080d4000c40d007490348000c407950403032040700440c2e0300e11042c0d8011000b414007682c0081d01c45600c00490040c03541e8012040c0f4000c207c0d050584900b507541d2103000d409907008082032020142805401c0c1307242c02c1007540103003c44002c2800907125441c0d6510710301c510000100300703000c04502d07007400a41110b00c40303400a110511a40e0000300308010000458801caa05106000003030341c00c201180035100303012108401801c0060018140303500d01004c018a10f41c115001030100214641d0303030740480319605030001c0c4002781c7d00c500d1204e1100e20245014000c0d6002c04081400d15401d03600d900201404409a4240c4082c543c0d00d80910541440030f8a1061007905141000050201541654440319803519400b02d607540074a01c40c00e042d005507401c29103001c01107442505019400803541001000113460031031074980303480500030700c1007003a00074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 505680539 1250 505679289 505679309
    0xc030f07050f060f090f0d090324290d020d03050a180b0712090b04090207030242090a03080402030f15100902041d06010908030304030807080f0907 65
    0x2203203090010801c410161114820704643c0907040000602c135403003404841c0c01040b8402d07085242e501e080301058810100240d525240744d41c90030342c1d50744101c82c006085c0d1100d6801c100001c1d00380c40c401c180541d442d0f00e08003508074003a024000c0210708000c0079000c0d9207401060340c84c02d0200162034441800402c80d4242c40d0154403603c0003203046415006105001040340c280300d1001c2032082100740200040ca20900501841c0d28035000c0988080401d4410101080d2090108005000c501c1e001089194403034810340342c080c41c44418980c0504c0c2c040d101c1c031340b42d003613810700e4082e44500000010201c410941d400d20998940b0240c00c0d6a2210040f800404002c1a0f101003011500c1c108a0490003098182c03e4031124541c3c6134014211100c00c0b80c80c141c2910410303c002441c0e00c846d208540580d025080b440d20480500c40944262401c0030704400d0420090a0000900002c20700103135004500c0390340d0b20303174160400c010024803400001d000400902c100c90140003c12000003140c9044a0508035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 505681789 1250 505680539 505680547
    0x7050c0111070b0a02011a180117070b1803010501080a1707030912060902150403201c080c010510050f13020c070e1f0308030714040b071a010b0c030f 66
    0x781c500340034256200c0d51411401003580103020303406400a900c500c01d510000010603410804000c00c0381889a50aa22454400c0061244241b00e0140741701d001d110030212000303d43e65501c0441c0c958000c010100020702c4860b4235060518003030041c070740108a0f800007080007004c29100c815910001c910041003d0b07400145580805000e145650001d001d603800028480b00c103800e10b4405094500c004034403541c00d0040601400c907020003586c00382e0303030000c02e40200100d11701001081c2081c01c0d1180ea40c4401c1070603140120440c00d000900e00f891040040320340f10a4001e103000d0a590000e0b02d5940c01d81c61018040c801a21398800c0c04c41c4401044a030307450f1422091100500038882c81e81551050b020f40017000c02d0513a4412522406400f42c03083c1c03840c0107501300d411b400d65108107010040002d40200081201030f0f10414880f210103c80e04609850b103540d50140c1085940701c098202d40f08051000901062a03200c06002d00500c40350801a00c1c05083c03010b0030b42c4038407030b00051300e0813903402003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 505683039 1250 505681789 505681817
    0x301061a03011518090e060a23150a0b0a02120702150a12180515130f1e060506130b060a050706060806071707020d0801050f0301091703150607050c01 66
    0x40030250304e100d500300403030b20100d0310b400c0c022000d0000d0b01410603403442004080f813035a003c6880390100705880002d079001e5080c220004031070b86400251040100b1100705040080715921004c06200410201c105155030301d28602010303044c03082e64540500c0002090040d030380035860704080340b2210629500c109a5400c0480e2066034090640003a000e04140340c6440c203001084001c001401140c0900100c680ca5441166058040c0004880b510b100000030004200002c2c01e95280c1c0c0500c903c01c0c0c8000d464045c9144d88020715640704581070b1460f64036102031010900700701c1d00010080e000301d8805d01a800040001c03038003510406044d402080750003d420703000d010703069020001030110a400d8583d40d00700000010700448506840c0800c034441031022986090001600c103000c18442d8443d04002d0707107418100010741d00e88022180d050354a03400854005165150001100e448030307100961242004101c0500418103d28002d0251108000000105400143d0600d01400910701011101905 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 505684289 1250 505683039 505683047
    0x1915110607080a090618060209040f1811030f0a0b010302010e06270604121a01061b0809011b0606170f03032a0324090402090a0902010504150e0301061a030115 70
    0x86c8814000c0714240d030b00040100c29002408403942c200c41c10700a2100c8024100c08507160a2000003c0c0b0161201e140300040142d0090010018028195104102c06400b29401d10b448070004503009060707500144210742e04040e03d24041e07101a9003807070a1120300e14416140d181c05140c0401d0351038002c0c0ba41c10712035846208440c05401861139007190403170980340040740f64404041c261014403541b800801e0361441083c040001106046144c2d000050540360840d459119060f01810010800802d69060450458041d0064820b400c001a2035261800111030803072280f441c0581030308552269003402800000fa00d4004411311980b8900183c0320300003460210350403403c001c158001000300902040c02c6842411790301100fa22885001c4010780c2040a01d074000c44009510603941c80124182c22041d5100e80d00141c41070400a1620382c8458201c0900c5000f4024070001640c14100c66503181401c0c0210001001d002618910708101030078404501c2c0014098586401105298031710340c41d00ca = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 505685539 1250 505684289 505684301
    0x10c090e04030c050f0d020a05010b01020c0d0305030405010902040501140901080102130303081302091e0c09100305280c030e03031003080703050d11070302010e060402030705010c021915110607080a0906 89
    0x102c100322078400d001b0030000794668184540039502c5500e04103070303402254000b1a40080d4400300800b11034400100b598144c0d17013038002030010b4485640c0c6054843c01a00c2d036100301c6020300380c604c03100014101080c2c2001030700c00301600310203080d90040c0a40880d0b01000714401c004d495150038072101c40d80e10303205c045240d404504c2c0702030b501810b0701d010300a040d814a4802550f468500c16441c581f582d0304840211684034040007550070608580300307016441e01c20b81c0501d401a4054412100d41c7c21800c40e0148607040036081901101e075949074000780d01d0741601c644603c0707000e0314001d103045141101241c0500035072840b0240070060000340b003008041c41036045a010b00d400442c20421011000503900712038000880c210003540ca04185125650710000380385214680c002c0086c51100d0038400119505081c00000b2600054070074070110340d010a44450401412454012040010414034001c004200e000c020344c0d02a0040d0702445102070303110301c4d995405114040c022074030780121b252510080103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 505686789 1250 505685539 505685563
    0x6040b0d05060a061e080d080703180b060a0515040e0c0d0e071701150b13090e030a09120f030333030201120605030c150903100509010c090e04030c05 66
    0x100020400c50307400e907600c01000e490303205c205205030000001e100005014180102485a400717250010b454601c102c100641c02145403802040002d0003680b150b0740e84200280840742ca503503603020891039082c01d1000e14014041203507181040d42d4140c5011886105500034260400f0300070b0005117940c100f58044948071034600e40100407c1d0300b01c840d856100c194500400b191604210703010303c020b9505000301058a1600341c4d0080041d490b0603400049503100c2c1c82403016070515020005284002841100302c0810902e001e140e499801180c0140303007032040d030410200030b50119503680100340a0081ca030281d990600300060942d00d140a410740d94260710300c0300c6400e540803d000548110030b203d5a00100c134801e0b2075070500f052131000c50f10141c0340280120f98156000120100d128036050404038803608a1544880c40d10b1917500c0440e0411598030030b11040207407a5014814001800d125050a03112145001c4402c1424603203000b03483d00c0082d10140401c1519484482804024403444503550 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 505688039 1250 505686789 505686793
    0x109030602031f120b01230d0c0b04080102030a0c02010204081011161101020c1f0c0206280909020702090a153204180f03050409020d090501180b06040b0d05 69
    0x144da1000703c6107500d9004034044a40140c00b000005044000c040c80c0e0400110b0524921444a40d02c0107004080f040d10405540c0c010140c0000105c50031020020310291030000c0015170b40c0d03d400000c08040c4c40c0100011001c6a1040100704a60038001c07402c40032500d60a003011078800c0400580d8409802620065051a40600e03240410400080884115600d013a02652980c903000310030060309100401d130403900426500d1006000e64414034006c0c61161008014034141500c02e070610721610040080180522404500a50256000104500101405102986088541d5010500311030020b00507001c1d0b03984413021502d00307040081c0f0240c05420801180100300001d03507122400d0304c504152540740ca9411840303588440c1403a008111788065a00c0080489034195239a0700380d007200d4910142c08000c010710000c643c3c05514001880303090166000400c90f040707103040141c2182d06051000c1e052800d00e00c5a000051131820720b40d0745c03001084400090324843c88022804021040d44010424 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 505689289 1250 505688039 505688101
    0x7260102091c030806041103070e010309081204140303090309100528110303010f030816050609070905150a03060e01020f0d0f110a0507060f380f010903060203 70
    0xb81612002a24030a406641c41c0416929103100b40012110402d446030702d0794008000060901e0700a000d031a100101c10300d4002565805900d42d00c8007a0414580d0364071110500040c070044c0091303203500c590000c02d000083d61070f60070107400a559030f12803840c0f904d00904190404001260090065680010840c1c128130380980d0a500f544614221501c00000444c01c18404449070700c5000050324140c54043c51130804e22030450319002c03075503046400200c8003c460709092000066040c00040d014154600040040900b00b0b4501c0c030580e07100400d001d100c00407100c4035000d00c1e91000c000741d04076030f00702c00002415001c2e121628060b102d0b04801c00f030880782c0043e01d4007003109241c2c8000103c42180e44104003003030300450b12554038414039000000050b800c0c4083c8012440d5507201d4212032048a40001c3c0c90551281110b20480407548940e40c1c01c10a50140c15524400c140c0c902c01d40c01046454181404070030740007900d05c0c20a07000240c1100e0340400013800045280000d04018440c140c124456 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 505690539 1250 505689289 505689319
    0x8032d090f0a030605150301110a050301090b1f05040602120a0c03230a020309180105090f060d0c062001060515030c13080d02010f02040b1909030803090a11030726010209 75
    0x140d180d1b18050280a0741c078017030074281b54048007070944100c02030b11790b04d60340780d0b9181c81075800107030052441c42d40e80041400c0d005040c0014003e0003109a41041d281c5030303110b9240a80c06802c200b40c1070b410074020442003207511800ca60001c1409403003941420100e140c0c0d100d607808141c03442d20545640c0c0c401c1c9130016406400c5d0b900080646400341c1c040b5170340c07040f0f003820301440903010b00203200e040d80000003c0080341d078806007020000e502110150150017500040d85801c0342407101c7d68004000b292500704580c013010810302c6249496802e080013031080501e4140442d00f480e0418180c5900c1107404004208888525000c0300c42600400a4035010551103040751030300c85071040400b402641ca00502862480400c0c001e44045624210640707080ca0321511020210b011503031a0102000065103010000598000185006500c208002c015141d003a00d02200301d0303140000300e9446a80094010081e1900502440d851803040c005800c0c12103030081d003058068024041402d074401503000310210 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 505691789 1250 505690539 505690561
    0x706091412250509090703030207060503190c05040321090b07020307080706020c0a15020a1101050c012a02060906040f17040902071509050c040b0604090608032d090f0a030605 77
    0x816200200d644502c2505c0e14003480f552216180b0004015812080040000e1070150b00a142e0080303288540c005049510900c40089401c0e049940e00824404101802440007060b81400c4010100c4900001c4062054026009041c1841140e00c07184000a0f2101151028880100244070100464401c180c4405019469001200071280544101d0701c000600d01d8180d080750200c0c1e02d241d0050100707101039440d00c6244002403204203041c04002c000c010400e0500344520003c0d150b07500690700c0c0e00400d090b46900a2904949140f0440d48040203001075040c010560581066002e01c409009581c00d19080c1041200342072091403410000c5800954076405400030b00c58140b0840c031445141d48800e08a000f02e400440010384180d00c07a04019540d8142940b004440b80c20040103541040d545082240540300103800078515500040351501c3d040f8844042d01c0c1d40a1058410f494070f80c07a0044e001b0300b90340076142000d8843c20046002d50420389031f18006001940d04598140b01c6441e1414940c2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 505693039 1250 505691789 505691863
    0x1a060a170f2509060e040e030c100b0a03050316060e0609010e0c010903080316020f07031112010c05071509021c03090605031608062701080706091412 66
    0x900c09038000000801450041ca0030319460002c240c80381c0c60558207291003204d100010210168029030394013020300d0030020030000b806407480780c500101862540c006004096450340036281c0d0040d014541c0500003e034011090b684420991000d189041013541004000750015417800d13000c42c02854207201e000d10040d00200c42c205009000c407030381005000c0c01114240c6c80743c400540030300341c00d2000c178444002c0400784d440d03841c44920443c0c10074107980401500386003150748100c4048503c688026928142210440501c1c9103800081000f01410030000e17006d4400c06a006100020b900d060907070541c0180e00c080302c0c940e0042d00000d0b00b031508076641c5141c075140f80000e50104003241000a07034540f1820032a0300ca400070600d01003410008010548801c0b1001e00740b154010003214050900342d41c00ca07012a0002c08000481899514012050341044403a170000341c200f00b20041e052110b010900c0701c50206d00e4080c0e0b03d40c500590090851820181441c0300e0f0143d43e0008400c00c440d80440030522 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 505694289 1250 505693039 505693051
    0xc0a08070b0103110a05011d0f10052206020c1311030406140f151c17070b010608060f1c0c1818021c0f0b010803030703050a1a060a170f 60
    0x10b5a100e80b03130200300400400381d4403c5c0f9000132500d00d0320303072034640080640b102100c4001e81580008a00000020712114000c42030400085020440200c140700441d804441c503000c40c04d004001504001c402515000021039490042100c54803c0720120070384c0c3e020071286243c044550ba12401d03d880c0100c05485404904010311003e0000300d4a80240c40d1840ea0040814002030b00014030a5014004420701710105401070715010b8040702d0100301c5150f022004487c00213940c0d0781d20549880c000e59006010381200301003100910800c05903407985004202100821100c4561024941da0184110002d420004020700d004e201d001528004c14252110619840101840605015840039400c94007030b02010b5805803c5800c481041c02100c00c14286081c021400321854000588614180180030784c40041e141c1e00010400094a40c90b10440b504514028000d0100f918200c043c00204046615014403034a0006075215280c5d020303440f0341c0c181a01d124100d030094a428000100780710300032a24 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 505695539 1250 505694289 505694303
    0x120201210b1302070c03142b1e020709050c091f09120507050409140109030c0b010503031309090c031217070f080a15090603060b03061008060c0309010f090f02011101020f09060c0a08070b0103 84
    0x300c00f00702000a200c4012141d10ad60040805501d0040321b8009407101030703e03445410004003c0da8030340d0380f0b403001c114101088140d102441c803111084010030101c0164001105414002c40c0c1d80006000850854101d07007003200c011420030320740e042800ca404c5602d401d003503031980791030301a1041640000041062070f005020001c550782c0d8800503d502c034410075840c20004070b038402c410b0015840a520650502c2e0040364511826900ca40d00c880c244121801294080f8101008007090840b001c00c41603403110300c0c0e18140120f001c245501400c0c0d200081c1165a0545d120201c070701000241c040f0603401042b55075014080d550b80c034140440105074603108507019004000009441c0b04416480804441100c4014100340d0384a48c80303214507400c00b5005240c2c0795220713842e8982160705030013800f01013030280c07940120076030844c0300141410316542d51a1072141d0043c00440c100740d06c4507041e140c0200042d02c10030f540d518444030a9042c1981c14400030307d4a03602041c1c0e041401503072001c0906aa1080700703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 505696789 1250 505695539 505695557
    0x3070302091f080901021c021c14010f08120d0b03011e0e1b06070b07030b0415210203030a0e19032406050307120201210b1302070c03142b 61
    0x402c1d00b40c7c401c2d02c2d0121010031202144e4200c070350b0035034000c00b110120401181c100318514403d6074240d42c01400707080180000c2000501180032010380000091030031800a25480a000b4190429400b59a00b02004181e45002a4009407400e421101e403880c0c03000900358420f402c07012420000c2004400781d000900c00d10002c104900e440d12160790700800002c180301e08000380c5923160300c00003070f004010ba010944c130349002c0c0c20345031501c1c01421094020340c90a418030608005059001c1036001c046120400ca00702164405030302c02202316601d200484c50548019140000482d4003680c8040385000000e45500b0000180151050403003e000d40b049610200480509120b10030b440c00e500a80340c0c160400340003001070701c0002c03041002951060402c2026009990102c807000d50800a840c0892a111f400000715454440d03420190144808001c60070a00c0a413182c690b01c28603404000c01840c540071b0301302d04e1000708010361020301a941880c1c0c141800d103582115200e450f07841c0300e038011440c6d01c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 505698039 1250 505696789 505696801
    0x2180109050604052101021303030e0405070e060c0c090a0207020f0a0807180b10090503060703270f0b01080d0207121a0402010e060403030c150504030504090203070302091f08 77
    0x14025003101c4000b4550350400d42410f0421400202640d403458050400b28200e840405c001c1c0090400300580401441d102c0c1d245013000b0b8040d003007402e0400d1103640340008100c00c698001100701003100040d141030761182d0814000c2890166180c5130580d01065013020850301d41c400350001c0001c24800d07138a20001907403110034002860054020310130346402003031080c0032003818904803078441d5000d100c02161001038000807030080f40c1c0c0c400c110000103030404070901c0241010010346421895a26041003409450110654444181880120002c00c50354082c82400006c2690380e130a01e40000e000c1029580d9080c9281d5030302602114680540146c16002445030341001201410395082011614042008a281010001e00a00407030610505030040407407a213a100c09080554402d4803070f51143c180500b411a03c81d0102003442c4901400d010812000aa2020a581c1103904c1c040000d43c40c0d0701c07000001d0380640a0b420045800000d03030000c3c41d110040740c0740c1c01483e80341141c45203809500e6034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 505699289 1250 505698039 505698047
    0x1020c0a0e01090b04090305031515030c0c060603030315010e0a1d010801140f072115090e2e020c0d080403080703052a040305010501140112021812011e021801 70
    0x84021f00842e009000003201c070104d804e545007605800500040c2446803400300c0d90051341003910740806800c4c010410342c00c18541000880d4100c0d204800541c1103240082064822141c071a2003181001700c0d40740f0050298031035001c888003628007801e105e05c02c200d00c840401e251b0482403082c80c0e010b60a2642e40509000c6882049019480e02140386400d503030380c69030940e21145060541045003906d00d000410240b0b582c031038202120700d1082d1050800d8604115030b410b5842c1c0c071003079000d0790f0401080030000c001420800001802414052000c540384032000724024051560427400c580944403090400a0f4800f1086100310f10a480c0c040c0c0c02c5c0c440900031012907604440b2070300b0045840300300010119044800c2c00710b52840e994410714150700da988042c2510003c0c1e202c1c0c400c0400000c2d04040359030308034041030358035481004110306114034401c0c000445104e40d05c1a9008945911a0b20800207080d049422825400404440c1030260041600002e5000d02d60180071600791500140866102e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 505700539 1250 505699289 505699301
    0x30e1902010e0409030507020301110408010606020c091f03080c0a0308130b0c09130615090e15360105040609021e0d150321030507081501020c0a0e01090b04 69
    0x181d4070309128040791010f000081074440000e0341401824010300d801031b0340c01d0050880541403010200e84851404003000e003900c85540020096400240120034a501c074911103d81c040c0100062408840010803032441d80c4c0051342001d00b400a000480301030703441002620040c0700d8800c0e5103d215a07511484241d404d2061540e00810040d000c50104120780ea28001a100f0240b00400008060001544e03c0702110142c0e030000500d02c003984c402d1101180c11010b070390020300070260b2400062504800c03407603520600351841403050515031041030a8081c0004140c240441180101108a0071003140c1d082c03c0300e00344102072103141041c5e80032422040b5802a139400b42031200c0030b00450040a034552030795400254038541d2080d036070f0034020440c81c140d60b1075400440c0910030100750704078982c0b51001c9801000d03051030281820882404905603001c06080c0d07001011004011580d410000102e091458010b00d459001007000c8021518a4401060504072040f000040200444550610090b181 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 505701789 1250 505700539 505700543
    0x2010e0a08060712060810090611072001030e0618070f0e0916150e060d140906070503011410111605030f12071b0f0e0901140f0c070c05060406030e19 66
    0x8040313401007804d525001019158450f01d00841c64284074000780700300b07401c20bc0040d12107200d48402041e400c40d17100d084000b908e200b8a4140284034958840580d00c2c01c01030555011040b65140b051400c01d400e1181201602c501004084103640d1307080c84c1042800180e4101c1e1460142c211030614903104048001c0c04c40d0016013000c0011101c1d07803019260340c1043c2c014590092810814103042d030b05948038010480041d51009103040c03d00410092506000610704003d10000300014800314000068010000c4000c41e01182c1c4080c61a10842d0001c0780c0407007004842c03080740700500c40f08414014040030382d081982150f440c00340c0d00501950f9001089620104440300304582c0b004211507941e10f800480c0244070f150110350340d4000b160a88105c991050307600d00608800c0c886c80300000e01940d030384445040100c20700c0d400d080100303020304080640302d400c2c2c14800113005000c20580c03072968401004010001c1d0345031035032241c3c0503010f001d041c07007109400c2c0914000008210602c0c5541c0e0140d40e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 505703039 1250 505701789 505701793
    0x80f060f0705090d050703050a17030603060105040b0607020306180c1f030b010908070b0d0e0610090506011211030402010908030a0c1e02030307060e010c1b02090402010e0a080607120608 82
    0x38071100d005031010307440000850b070032081514000010650400c840c030011480b8034010100b0307a480d41065003202d010841c07003c17542c48040003030011554002604c1c80c1550300403240050407502403000603032035204c0c04c0402501405200104080c240404908089052410040d214400258800c10141403000a40c5a45039221840034022061203644108801c62040c10304501061b10b0f000d030a481e00f01c66901c944c1d90901c0005040000d142c55018007800c1a10510003095a41061101c85200c0b154a00600390716950f0307540000c51683c4105072241020302012410418000c0c4403503080004c0d40112010703070105551003800140b501c00041122403190fa95a68402640440c0d5204581382c1031103192501c8a0400840340030250350240014444a44552070005658228205240c00d482c10b6210010a002d03001580d00030711300c0e41d50b05400c0160341c1160400c110b81c0d039a10040e110101c0d03a0601c0c0b034100e01e581e140840c2c0350700c0009000d4004c60076903c40004c00c402c0142d003602943c2c030354000c55030301d9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 505704289 1250 505703039 505703041
    0x130312020c19020a0e09030306010f03060308120709090c0e190812030405011d030901090b03100302010e2b0c0509041203091a070201020a08061504030f110303070c080f060f 76
    0x200c80d036003452850b4280300400c40c6200076522518400c0318001590311000e036400000a021381981c0080352000d01624034201800740700c1c40e507118035001d030040c205503203008203490002455407442001200c0140c5200041040b880e52200001440706501c00000e034040d041c801e00b1081031860200300031084808400003840101d8103000c585149800141045910359202c9044402045800b04488892023840004580f500402000140260700707035480001e04444c2041448000100e22610009591702070810800c100c0c0c90b4030100c5c2e4040b0900c094400c40c0e00c001d045aa200041081521032414021103e25141c603441d4030400460240070340d0001d02d566401c11721000078034040c1c2c00c0000d056010300c1880105044a91001d1818101110000300603540022104c209680000348690001c40986450a80421400c0e84068600c0b581c0800303080c2c0c24605040d41c08000e0803000081504001402340da4481d0118a80020307a200c40d8012041c5a000d400207010f0f142d0030000c3c0b401c0c40341c0001c1e0300600203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 505705539 1250 505704289 505704313
    0x6090504120f05270306061e011d040c08010f0f0b03060111031b03041521020f0d0213030b0a0207120806031e03040f0f03030c080d0b09130312020c 65
    0x741103525a1182d052010510641259041441e402c20224a4130740c0b48000075600722041604003a0003d0100d4480c0300d028800c1809003140c14050a80070f0703001c0c00d084403600d0300c100941d00c0d9032440208070355010741085000709800380d20000302412035015071000b46030301e612501500c0094041d4000c10600442c2400011980c3d8032441c880304900403000142e91600300d114101007032070b4007451411003495000060400c00c1e080b8035005410500c2951510120004031000900d00c68102c44124035449500400e814070700601000c1110205011900215600c0c403141d0b074040d220f186244410780b1208150340005030364400c41c0c021580d1590340000d0340c22444007100d10688440c10b026040f5501845490b6481c0007260a140c000c1198014450046403191300d000c071141d4020a050b0008600b00a40d84030800001e0303045a1140022035201030311603142d06840090a0040c4902244207034046414000d0158111041142031038045c02540d80000f500d011402c50403da10454128420540c041040519 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 505706789 1250 505705539 505705547
    0x901080601030e1009150e0717030c0601090c09051c061104181406010903020307091a060706020918011d18030a020d031404031e020a02030d0507060609050412 70
    0x5030010341410b00242110702071004510748511803503441000b65503007162800340205086003c0e00b902c00b2003000e211001903000010b407508154840c402030710b00080d203d0100c1d00014810b881d1141804022241e15613034400c80c52010b45881c2040c3d401140b80804042120305082040b03110411074125a052403402656490000b01f81203020700001c204180b10104222880d150640c00f50b40c038021010551007a14403040c964014094101070511207400300410041c4c5010a0000c215005103000050b54220303007820400159031840d915034480c400217104400c00c0400d9010f45510f200640d0340c041000c00018030421038450a000b16480d601b454150064030880001d98942c1c02140342d0030a00444400d00300603031442d04441c6240300540c1015070921012641842280c913a00820000c0b4001030034980c5029110601144509065038014101a90110b008110024881c1d0707026003241c0c1c20041c8410000c01341d0f04840000c95100d420034130009240c03d2240640b5010b203800030b580c40c01a007203410003a1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 505708039 1250 505706789 505706791
    0x80f1b0a0c030c12020c01030f0b09010506130305010635060c13030206042405090612040f050f060106031109030715090e010e07110307210903081308070812090108 72
    0x40c104103c60710010006001c02034000080805600104010100384002505503061240c200b42414580803001c201c641c1c5a00358141100d20a80d50250344070314800808601000e42e4002402c190b003807500000f13115407089540b16001450380c082091003845909a00e84944422400d550154040320102300050113200050401c1c4c11000701000d0304030b50384d40c04a9115003180c0d0111100004030001000f0000300c1c140420400d204500e441c61400d0341f00030010381e80740226088a2855810040050104a9210003030191035400200720355070340707940940f2a581c803e404d016510000b414024115980c0f00a45c05441400c6001805490480c0c03c0000c4c0b06d1107524250b004004104080400090000501c03100300e001c3c11608111510304d140804014106407014210051f0f651b008018030000700300c0c2c45500b04204001c7c203800550340e406608003201c044030745800280290a0001d800160ba06101b159001254100b00645101d59907420282d03858a56004001d146100c041010060661080d050b02d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 505709289 1250 505708039 505708043
    0x1050d0906060b04091b05120c040305011805010e010c0c06050a110703031406060403022107091104080d0206040209010e0a0609090305030618010f03031b05030307080f1b0a0c 77
    0x1425019545079842074407907aa015005a202c00030b020700c02001280102c040c5007a0340709801012a041c040010100d1103a4200450500c0314403011600c03031031103001110700031504140240181980b0711054440c2c480a201b081b11698685800d08600c010b043c0610b5040c688245c968084005264880c038014080081070071100c01e0740c4e450910082481e42e8080c0040300e0003540c00281c0f102003001200c02064024004912418003400f04100581d02c0d43d54003110802690b1901c1c000e82103013910240f40c0030b2141c0049425604140140900381000c038040c00c00c0f112540102c84940d85000c1040c0d8443d04161400781d0082429001441410b040200c1207400001340c0c2d400003400f56a914502003241c05102c011400a0720000038404c00e0300d003e4101c1c205c0000442e0150400703504d8114100d5078000140300040030f200a11404900f01e1380720442a1800540041c150796407482d1103031006086240c202c44200c0c407504200c021420a0100c9275001505441c100a030b84d00c1e00c404101c06488400302c00e03500b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 505710539 1250 505709289 505709291
    0x150501030f1413030207090501120807020a0b0307032316050c25090b030f031b1006090605120c010e280906050a0b1201030303090305070b07020714090f0601050d 71
    0x90150700082c03000030607110320840184803030200030720726000382481c2c150b61040080f03904000060005001d18140013281c298840c8040e9560405840841ca1061150307114a5010201008012501d501074001b140d0703008142c214614511182d40c0b1440000c07405a40a000003040000c00011a80c025130090201c01034510489645280a0b401019441c1050040194101c1c00e00d1082003500024050a0381c5124201c000c0c0c45082d141001d01a62406040c1c440440c14294044080818405100801c2191079607070050010940341e64569014040502c40c407030141c054418180c407040404036501d003901005a507090000b04030442004181c5200344000c2280400d9006992819503003031428200600c0c5084011441610b0602003000c100c0450b0700c14090350000f00401c80c11704051103100f505503039150400041030080d41c00c0484550044220041900d6096810b01103240c1c0c0018010045903404070010700031240a80901c0001c2c40203032042004035402502040d03496005001a00c0c43c0c180e0b0700c0c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 505711789 1250 505710539 505710551
    0xc0803012105011a120c01320301292503090815220c1703040b16110d050c0d060e010f090c0b0408030a0f050403151e150501030f 57
    0xba09402c4544040c5501c50385080000c50403ca801d000750302e02440c10307094000e00704070040e40300040c0201c0c1403044000c103c1c4c808440d180d041010030203040e8425125140b0308944a68507010410100510201003e202084005000142c05400c0c401c0f5030328074508440d480a014049016a00d404414000c1142800010000461888820000c18444501c003040c266400e080c0407100110a400b002000c60416015a10400214041c0c1915100700e8052660381640301c0c10700310030b4900314011a041707440f0f0900300045404030458010040c2484a02800e0301c14500c4860104000d662a00440c0090035600042008285032070152803050b8070030300841011a070111002c0ca9182100e59202490035040e079141c0002d000d20501800c440040c0c04030f128018039040c2040c802c103a50f8000d0010820820220003d0b07003403011300c1a0159402142d0003002d0101d40e0505030440030180c0b0107140d072010749410045040c40400810b0041c92100e042180d030141c9402d00f8a401117002c1c001101e480d20703855890340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 505713039 1250 505711789 505711793
    0x304230315040f021906050a050306040603020d030c060506031906050405150c0a0e0d0804050904080423120c10030213170a0b070e0915010210060b09030d0c08030121 73
    0x14041c900ca14881c103007214400c5140e1041114107100d0b880012409002500140b081e142c02004032016080c2508000b52a651042c00143c083c00050700f0094103d815154858105504040c2401125204160900155898805250fa9480d40721070a511130100c0502041c01b0914503030005400c14003480944e05c40e0100d041d403011410074141c450904c0c0310350004081c0b00440e07000006010301c120480b130420f0b804486072030b91030841c000d60203018803c144400c00301e410001403404850041524060100380700d82c0944844503004140e45826000e15014250050001c01c08580b1600c1c1540c001c08041d45c55413206000c8000390003020264030304011141000c40c030b0031011030100143c0d0b2050310050220046030f1420a1326010003401d40b809124034101d401d8041e80d18034908603440039000a402800556102c0102e14040002c5a03421040b8902680410040c59010060001200c21340031500303400b078414400c440c00c000c0588003410501c0140014044101c0c801a003581590b0040d024080000e525 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 505714289 1250 505713039 505713073
    0x20f010c14060702160f050d170d0f15061809200408162403020a030216050609120f030c030a0204050a09050703060e0601020309100516080705070803042303 69
    0x1075a039503002d079002002100e05154010b00c0b10000c1e151002c0030b0b91003d451f01004c544c5691800c00d00608412401d1514001749a405040c1c903040352043c10b0034030000780c1d4078121200034029480c892a0030640018042041d60240101800454405400651261901030340b40c004000c02c1082c070100ea40088000b400340c07060040540083e040402c090700b400c260b442615100c1c4515648403084184407040c984001c500300f1340f0104116035003410056510150341000314028030802100d01600070181407103005100000400318894083d24045a802c495101125112030040d0100c0e01c5015104100144403075101c00c010f507130091646540582015100c40000b4801e10f00c170340107003030100d03590800c1207542903260144800030040340443c40ea05003480c00000751a0710a089486000d40c2c0030504852102c0d21580881c0c408101c81d604943d8580903510717103510030350b02002d415110391140400c04a80088003008903800c96524000000c1c0c0d6859030381210112101100c0e81644c903015201d140e051510385 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 505715539 1250 505714289 505714291
    0x31a1005030a0b040506010912110d050f06180304050111100c0203030a060b0f040b03060f0907020c130221040309031a07030c0c0203030322051207140a020f010c1406 73
    0x180e448168aa25180e00382030122955424003511640c10901400305e03a903081021001902c041100c1012a08450f041c150301c0100c0401c201504102c20040030410303c8408108888813504407070030f507611901e60020080d045007140300b405003290001c003c20042c035030003804448c82d02c40442094911300b400d030031102d404036060718081c440076030030000030001c007881c4230700c12240605171a0413070340e0801c450501070301f6030380c042d0380100034a0b1080003010848035540c0d18120301102600621074940c44c901450000d464485c1c0020035406202000448541c8200d02e000703031100b003107000109040070750000c001c0d0110072801030f0041c0e061042140c0040b000c20000f0a8284084003501c0f403011450500071001000c5561051b02c150810030381c804000c00582c0c010044980040c600941540c02240c1980904030744044503000510350b104594211004014460140001c140070745101c43d034080443d8001904c1d820983d2000303600c1400842c45e87e41e01e600030000c13a403c2e00c2c01031a000f00c903440e180c26a07070f10f803001c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 505716789 1250 505715539 505715569
    0x102030906060325060806030f0f031e0906070f03120903180b0c060a0e2404030e06070c03020d331109010206060609040207050a0c080d0903050d031a 66
    0x601e081100c181410081c1c2a0344000344070315144d204008000b60307000d00384280902010010360102003003d5903400c110000c0c201341c0d02400d8a1000892030348584d565404a1000150b18244015020800c600e50042d40c0c1ca07100068881031800c000c96450313205611100c2821001c0c401540d414480458085c40340b600868445c0c1c84d202003240c101460302c02c6000140d880002c500400f00039010f403900c0c02103501d68100c03c401c100800c40030361031040b2900f007013030402c010301070f5402c03d000c003c085d400e00705c1115000b64000d45581c010944070b60140407042c410510090300e101502d00741040103040c030b4810149594051550000c5841c3c0712801c1461044441d82003c42c020001150601c00d01440d2140c54800b10846515a00d04803d290001c1e440b0480140000d1195401050440f015201c40c0c04848000e544601904d8244140c1d02d030001d82d4824900481c41c072481050071032700019015516220035a5005002402c4c240a40b40c07013103001d428650b1510303030020021a03150100742c580c580d035003803215 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 505718039 1250 505716789 505716793
    0x1021c020904050c0307021009080c01021201170a020306071202160b040210300603080a27051302280201090201030b04050f060105030705040806070507020424090e0f01020309 77
    0x1c08a00c00300300c1652406007001803002003c0060201043d0005080f00c0c40300d03a40704010072200c404d0705020049000d44000e050441d40001000e40013a402c07000c005040e00e0000da2010040180020055a20100184000d4059116002003102503004001e00c1c01143d80c490400351811090f01c0c541080c020284000f21014014842440300b1840d0001072528521924035000d0441441c0300040418101d4071550100e15010001e0542451a05900f018002e136410450740d566402d07901c40010703d810840f03089ca814070503043c055034200d055221420801c44400030031441a5031001c04102000b5840f555092460012842055684c15489248822203814603000029000f020f4000074040d0307074800161038410340c81c08007000022000f075940b03150401420319020b5125030346d8080649071442650481440c52180700c040116082d4810014200144280c40030b005440544080050750031840316500c08003030b03515009218284544d8000e00180c0700710401c4555200300358000908907803064030540700366 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 505719289 1250 505718039 505718047
    0xc07120303051e0405030405040b06120f1603020f0a0806060d0e010b13050c040e04021c0b0a06091a10090f2c04110103020d06050619090b1e0304020301021c02 70
    0x141280700c1e580c2d003a0599103070091036854136907142a141d20840c000c0b00c0c03250b641c0d5800b04200352600010780710542e900c0074004a02e81800c003800d5041c0e6004403403800c42e0000c104542d4903254480d00070b0b1014a41d19146850800440c0c0c41c003605e0410f00140100c0d0040001d0200d080d00842da802040e0b02044200000201499141e060010180b0000541c00141c0d05140c18406610400000c85048a48103000d04000c1d407a0361000482070303454511005162003070044031030280810701c2e400c18092010715034108002c503a242034603030680e4455050300310188240200440c00341006c4d03013042c51140c0103181201d8119110580e4100008950300654541100c1034586520880142011391540303040310710380601850156030f501e0b80c45d0001e0036043d04050700861580001321054111f04090300c4c00400442d140c0d0340c1062411280d9114100987c0000c0000c00300083d00c030651400c032003001d04614000480f211400038811050780c0040d10887c3c0542d401c00541e0030074850403181c0c5004c840c80c8040035903a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 505720539 1250 505719289 505719301
    0x304061a060403110f150301030c06030b010908061503120a020304030501060504150603020705121602090612030d1a0307080f010e03090a050d051543050c0712030305 73
    0x403400c00c80d84468041c810030041403000c1030054001250504040f03c40d00c000c03040340c0d008201c0000c0c246e040381406020200001c0104092086400706941050b03800300030030f610690044509086621414106400c1800894000d1101b030345520b09110014048030710096180801703540c1d542c400050780c001608041400d10421070b0078050341e001000e0445003841075280d07130041400304282500c1114145030b400503205003000000e02440f002c417286038001c540c0f150703443d03001d0850036500290201c0c4190040000203119140c140350410080740508001c5040c8070100c08240010680015003004104101086000b00c0d41e080082c1006003d01c0c4000d0450326052114a41c2514803003030030b00d10903401c2441400c8094642003100012110102d5034000002054145141441c0c0340c0c1c050202002c20b0310f0b040041400403c150b00c86a480c03524617102052000025000010044154031801100401803c0840a03c00e00282030284114070030360ba00f4668a2101860007a0140002c4001c03075181c100b0401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 505721789 1250 505720539 505720571
    0x1c02060a170604020408031b160905040201110a050601150c060c020d120c051917101a03090a020d170a0215091c112401171203012702030406 62
    0x70b00b02c6000c0c0c50940c142810002e00c0c0d520307401060360f9480c0404110781c041004850422030600c40d00c0c0218007180c1115140c00104015210031a0164041508008042c1d144040016030104079074005003d882d41c1d07401c00181559080e980006541000801c0c0d000d02c0c0400d000d4425000e00c0380d140e40042010411840010340324880070303c00344086c0c502c1d20f51105200d5401c10211084402810300030105807000c021b003a10300c3c02d10b240c0c0100d1400220b40400c62400c06244003241601c1d03081194440741c41500d048030f41e25100c2150204a09d400042d00f480041c2480401014617a01c201300c80f52180c0c100b4400c2d1489034000c090003000590108141e4035594038040f600390b40201c0984050150400c05040820544800b100f130407080107460055241da0307030340030f02140d840600601d041c3c0e00f01c460b80c0507002c450203000b0300801d0300340302c968800e540d2690310000b00c0c1880400c10ba05060f046038604119891151074060908224506503012103000880a20046100b40d1003858000341700d0002c040311f02 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 505723039 1250 505721789 505721791
    0xf08010204090b010f0f0e0a0306020d09020a090c1b06090b040503190905030c010804060e0a080c0d09030b010b0a12090f030f0212040315060b0403030f0e09151c02060a17 75
    0x160500009250b17404100743e01c5120140c84c00c0352401c1925140c4103040104000b0340745a840500428030210350142202200d402144116008480508205031903031091800c45010b001d110b00820441e400b40c1c2c00d0a205c440440c04000e000c1d4800007200041910b0703403040b2100c11501156150000203821100d4050914074400b2201d061501480c2c003401c08010950303e200004480341441340f07002c0020304000c02034101e450a14070020507184ca49000f4501100ba6411a90106c0502d00072003c031852101c3c4a422100b049035040f002c02099a482c2142a0801d03078002c04004080000c0580035079801c445600444002c00c1c4102d0b0400d20012490a004000303074101704400045401c803444070701403800014117031015281c000c207041c3c140741c91810b03810f802050f00781d020414800010030000305040d0820403081c0d0038001602e6920b09801240100320058a044400c1e44c191040b42e1180c00c0c00742005240b414041d0841c10b848901d560746500041d040e0307041040504001541d02e2514107060302401905 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 505724289 1250 505723039 505723061
    0xb0d050c31080111040902090307051507021f1b03030f090f020910080c040c02011b02060118020910081f030803090d03050903030a0506060409141b0c06041106040f0801020409 77
    0x1c100c1804d461007035200074840c034841d603903807181c010030b02c0350f41d9580522508000305801420005058400b010421407604241e409a2040c440c0e0200d9546048008148000d006019942e504683d401075030400038104170f060054040542d240860714100c3c405206000480c0c0c01103480100c1e040381ca104200190300000d107414036400e040b6004215280d80004c400c050501c00711000b0500c4c400d12a812401440480480026440c240429000c001d0300810708605840a045401807201480d20303030300c403d84c805c006100740c01049000041c001c5900c070310030b41c23500901c1d841041c44104d02030f4080c040c584d2069030400c1c1c0340304200000f40507038418104120407200445080600c2586440c04003d03849000c001d01040b030241e01c13500052460740ea200b003154040c05280301c1c01c201c100c24480801050704000c0f01c1c0c41c02d40300091036018903c1d410303200554405c0d800d190300424241e9104d40c1c40c0710070104007a50880d04410180b0002c40d20031a80700703651014000761800140c84502e0100c003901692201c0a513 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 505725539 1250 505724289 505724291
    0x8041508060f04091511130b180913080a0302121906083903030309011a0a15031109030312060f04050105030d030203040503070b01120308090303010b0d050c310801 72
    0x2e07400140191700c0c400104400e584001481d2441c62040d1040c51080849103c3c0070b540c01d4001060301110500034101c1e051481c3d41c040d04c012680380c248230481d0000e480020f2100300340015040062020300042800c00047e1030054107100d09913964001040d01611103900b18181200440b50b401c001b84101002402f00c1401401c14a000202e84955a00051145243e1500440007400b00c4500e03040d40d01606c54001d4110b83d40c900c0c140d0038003070007040030079a60316680c15180ca1049040c503014000e6000e80d44400c84451a25010b800d054004110f5003141004035201800084080ea8050015100c003181003501d00215107800000c1024125214256034480c9240000510050320001015080141c0500300140d40b612117040c664a9070084441c001e016182c079070300205100402d41403800b5100d1103520b483c8029200c1107090358a90009002d2010024814040074030780d1204d6400440d00f00303005070480c1d8901030401e01c80c140b41c1c005042c100301c8240080008040000c0008181000034408200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 505726789 1250 505725539 505725551
    0x30e010f02011506030b03073314030a0c0315121a0c0901050c011806020723300703030605030f07080d3b13060503060f0408041508060f04 61
    0x43d041d9840e8140c05010b0400d80d89000a00d40c41c2c50801c4040098005140107030500c0440103076a2048080c1d8003d07081700880c002204214407401800145424851030388654116611a000140200030600c821801c15444051682c02404500c8000c0041c00f0011002c05c1d2891a03410700d000111841c01c000b141010741078040009400880058404880c0246030003507484084814040c00740020716000c141918140380190700304840b9500401c2c01512440e05a034440402000e58503002a00b0008a030040e0031031402c0b81e600020f910044200d5003118040c62524603400c10299880b5002404106d0200c0d80d01c0e0420b002074603003004003403201880c650061840c213003403261301703034079106404001428882d00c1c4c0c4540f020482816580141001d03142d89443d45c51800c040c04454020000c0341c003a001e08490741c03618141b6001402400141c3d003000c0d000700003544840b600803020341001001a51800e4081c4000308051880c42e82d03000c0640b07580e61741c5607018104402001182642c034440c41e0f1085141070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 505728039 1250 505726789 505726811
    0x31b041d1c0e0d1713080705040f020310050f01050706020d050f090a0c14220603020f0f090c0f190207141e010c06060515040f09020c070911120103030e010f0201 71
    0xb114000f60190700042d07150280d482c40c0c581c80c41e02d000703208030742501c2441910086020030300000c0d01d0040350800c0310140189902420601c0480c48161450703141404d0040080c071540c10f10b2182c0c010010018500586020301c41c1c1c68010882c2c2140e000303094072540f110240151040d055a6540e08441a0341c040c0450800e9503807081c01104081c81010f401c1410b50380faa0100d50f035210384810312500010541c41386081518080c0d07004042d18082244107484c462201c14040c1403100b41a2080d070030203000c1c4001a01c91100c01c02c8680c2241c100706204240c104001c4043d511000034041500b007054004040c518180f11b000f11600c640300d0b02c0d00f4003841d2411813040d15440e139001d0305200400b003800e2101440040d420321002400c0b0a81006030420041340c60710501000080c010400c98541d41e841c0f110b12515210510164801d410340072000354130125050003d40c03656031110b400103ca10403042c0c03902c034080901d2179071203000f40e0054000c201348050700011940c00c00c2c21502852980d20003000f07410404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 505729289 1250 505728039 505728049
    0x6030b0112050604140405060a06080706050418020717041809030c060c0e0405090d0320071b08011d06070903120f030f0f0e0f030405031b041d1c0e 65
    0x1d0004040c456480380007084080e2103139401040035012040005441e0f00e0241040da603a1001030300e400440364580640007640340c6020440300306480c80340d52181d02e418035001c1c038000c0040486d42d486103c1c80d800c200e40b03030010346031800314080d4101864a26440da8500300245205941c0706003040710b15810704494000081d440760100c105140d10448c0058081c041e83c2d02141c00c84994140c3c41e07003103460541030200011001030290400c1c546650b041c0800c401c1d10340100c465400401c80703031801c00410b104e0320700020300080104491640b444481e03010281d0b54800c41c0d027960540300d80822605003441464143e064103001c40707603000d801c41c1003000c00c2510710b658600d10381c101c424051080210302510280c90342d1090b00b1161050061038001d204142c0700718120002040c08000300c41051042010079402e000e004015241103440003000b601203040e0800100e004104603001c0c00d84c1c41a5244c0d401c8002101130340e80d070700c094044c0741c00400c0c030305061456245012407404400c4003400ba800c07140980325520 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 505730539 1250 505729289 505729307
    0x305030c07051c110c3a06140105010806010507020f01110f01020304060b03060117060609060609040c1d0d0503040b13080a0b07090e06031c11011a030706030b01 71
    0x20204103603860403282052030034030580c038004005550045000c0076100d5031082d824964914010140d40d6195031060030404406e01190a82600100907002900400c02c0044003420340f024440c00305841240315070b07581c0300311000c140c1100c01c10fa4080c0010f1200b940c3c0000056440f007403c0c02c0252600c4c07200d03000940000c40d400700e220304111002000f0341a400041c0841030f09066404002e645030b05043c5481c0000d4141114500e0003803150360000600e07445440f6400d40030751811300203011542ca815041c010061801000250000c00420100c4030780d8941c0c0c4100102d08030256070b88544088240410494500c0030103070984540c80000270f20001c00c80c04803c45045605e0000f1181e0380c2c07084d0900320b80d043c031000e91010070316026440d894000e01611195840c800e0100d40e0790b0050040e00c40b03454000c4ca00c815109075405900030314560301c4508501040740120b522604203c5015444550403d094410528547d10381c0c109400c07502009050401c4604003a00e800e0409000811503100000d20201c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 505731789 1250 505730539 505730551
    0x1060507020315040c050a09061401030506090411060910030c020706142506020a1d0405130318090501090b0315060d0201140c03070308040b0a0b06030106140f0d0b011803030503 78
    0x10f03c000c041010070149640040040c600505141080c03592448010010101880752056004500000525941c40382c4601031143c02c0050071907400707441c3c0c3d860b80c0306d00c5040c0c4482c0507002031f001c00541ca02a5980c0c00c0e104001c24844e40c0100c0d008a00c0d1100904012003540000c6c02c0c00b801c20882ca5260b8881419030790178881c0300c030f090521055048062140d00c6880c0c0405421103100050b1400307115484a0060425007401c0140703030b540f5220302d052108454003252001c040d401c1e0094500c0000340300f408844050844000d04800450302c5145180072603070203070311102c0040d95600b0b1032030320303400c081c40304940701800481004118603100e0040365a800c9140300007810003070030031840c51b000302c44603058440320444401120b485a00b40c2c0340140a484054506480307200c403040000304164080d01580218a2015100905503480d0031801c0e102d0658051404103030359002d02040b01031030100801307001525214007012850344840800502088003a1039800703000c2000300e00c10310110380c0200842c0c1d0040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 505733039 1250 505731789 505731823
    0x7080d180c1701060f080c0910050f210610140103050c04091e0c0c170304050c0f06041208130e010e0103032d0309050d0c02130f1103091005010605070203 68
    0x4180200c0b0240100260303000386104000064001c60890000034455640d890140c41110700340d210b40b2003900740207007680302e080d5206041902030252424414403450200f405410701c0310200e10301e0b4a0007802d2000440d80310000d4013148000300011620038100c04171940c000e0800704502c0c20110f1040d01c1610590040c0c041c820703142e046982d942c4441034440302001c021000c08100c802d01140004011011104003a1040414410043d6071810180c040301e018545c000c005159505260046c40300080302501000e5129000348000224114160084d2072014458005140d46404031000115166590f81014580e51200c40051144280c20314480e8152909030a1840704001407010031001000c041c600d010001e0085114040c43c983c040e001130400c1d81c4204292074071543c0710802111810284880030350311000c41d80c0c0c451107103380c991044d2a10991160b001c030301100300d07003004005640203031041e41c9160300c0301c407441d24010720910071640035040600d490343c0740c201c1c0750700003d68844055020080300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 505734289 1250 505733039 505733069
    0x10902091f090c090b0403120818060a0b06040f08010b100302030709180f0c021605040e0a0b0a090503040305030a0905090118052502030409060e06011704110607080d180c 75
    0xf00d40a21500d00050019981841c2d6a0ba04d03032070124282000c1018000108281102284044407904448a0260f82e0b22009200a58601d00404041c011105240da0031402c00c100104000380c04500c0100075100540c00130400c01941c03014807203403a0a40e100d040815105005118815910929090332203c0c2d2244501d0b01005142d03001000300078501461688514107115241e07c150003040344192540d50410141c0d5003980d030003e00c01914441540076800741c01090601002806064103943c1026018600040d203410669501e45150701540050b942584085220407035240e01084e100c001c2e1206032003000031035141c50040c00c2d0700380311028421704031034403080001c60360020300321140b83c040c100840801d07a007030309180c0107501c0303601502840702c0b00303030910401054111100700110701450b010b95070024084103c000b1040c480c40301400403990f5000c4004050442c2e65114080c2c6802800b6050761583c40171280030003402c94804400801c1072a44540565011810018214007103c81c001107034200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 505735539 1250 505734289 505734311
    0x906011101020d050406141003080d021e2a01020a08160509030a031e14070204180501060f050a08010b01020a03030b010e0a080114070c0512070201050d0905010902091f09 75
    0xa03019003c00809034a01d0f00c8100b1050080302d402400c041e90312240018415202c804003034006c001c650102a00409003001110301c150001c0d40208004460041e400080e0f040301d50f4920026031120103075500e501400408034443c0703046140100d900650303c000861910a18203405070500b00001c0500030580c3c00c00740f07485001c0e8021800c4a0351a0340003000da03056610f680c0b034090181400703240c0300d4502030f414602c101c100078007a000e07000d0400c0040e50403072f0601034140c0c2003201403c0314650f91680300420807403440006e682402110043c0290340321007402c190808040c400c040d01d0340c1e40419a00da041140f0507030981d8010443c464050b407d8500841c807121040010f0302c007000c0203102d1b02d8001d003444c500008e040c5011b5118450039000d0001c4510561181c1104803050b403080030011b440ca420003048000139000030402010118410b0500c14107101c0440021b20441d035002505403010b07519480014110f01c2c1080e0400e501a0b50303150781d0f584c01400180d248098501a000d40c951059880c424190 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 505736789 1250 505735539 505735541
    0x115080c10050f070302010609180b0408130b03010b0a0201110a05090906041506030f0c17011701060509180d030203190e030f0705070303090605070206180109050307091a0d020906011101 82
    0x31543c010303240c0c00da503203a0451400a000388011700c160042c00c1d1410401401e03408140010b22003182e0011025102521542c59007260303030348420854540b442000c8000507400740b40101031070007400000c0c0f91a4590032002c030042c3c00c4d5100034050b592985d804000c2d0041d01f40d000815259071030b900343c034090010b640f05404100105402050324101a01d000e03000100243d043c1c001d001c2e64500200d0501c481d002c0044141d5119180c46070013245546004010707c03094403400c03c0d40e100301c00403800200e0303c01d5483d000b10300301d003905070340085408113490242d0340109010481e03a075151869107401c6140d07140070103080011205001340d02c2c001c0b646a020090303413110100140c0d940c40282d07040c4d141d52a1140d1a01540d036120b03c0c801180821214400050a039000720140e03072031160040c2100b0329008900790800545016103c115050000309440409d154801300801c2c2d003d001c0d003c10020702d040032542d40405d03651071100304c1d61284480903800c20058403032541c0b5039004402820030110128654026034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 505738039 1250 505736789 505736797
    0x909070f120317061219060608071508040302010f090b040201171605070819030b030d0305090309060706090c0f06121a01030b0a090f060608090f1b0d0804030507080115080c1005 78
    0x580281706d2141c0541200204000058101e40301c4e58040012079502c0b0075a03522001c852003503181040751415002c000324011940079501a110348000244041000b01800c1240d10b440415202f40c4403840c01c000c11542c000101c60080d28012404042d1031078182440c44501d0030030301242c8104540464140100411076080c1c42d01d0b00c1210f0004248040900b03030080c003c000340c01d0001d10911030748a616240e07602a210f44d82c0a41c01c144040c52400c4212420300c200e03036100481c00c441c3d6035030701c00803103003c1840c0040c02c1001e05002050011185c2c908203000700400d40b900c14499a40340b4000c00703041c8001004d904070300702803400c1c20042820041c081c0020700703941c6250b114400c3d940c2000303091034412200380d0000c030544104e525204800d4840c80304030340d991404019071070001d5001c00001e401c181505060207619100050144442c1041591180c1c000c0e00b20354000c40782507101500501100e1030a0060300d04003a812444015161710b4140c806540b804594a1907000f40121034465541604c580120303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 505739289 1250 505738039 505738069
    0x1030b01020a0b011e0e0f0a150305061b2803050105010e06030105090403030204170109120806011d030c0303070b0f01060f0504060509060d2306010311270909070f12031706 76
    0x800d401c0c03030f10f42881f6040382000c4030403030100391a090303900e4803e102952051041c0c1380c000d0000c142030b2740c4044075045d441d4884c1815400000061041034802c01c03080d0082c800c140690719003c0000004020050191003040c0c0150341400000e000114542c1c90b82004d580c1103d104441c5801c1c1c3d6111420141d00900c1503800009a08110304101d5144d814150001c1d20035500c19503280c109038120b8041203c0c8008141c8441307002400090610b00090401c14403d010510000d003555100303143e0b000080c4c41c50340b1180089903e594400700300103250300c00610b41d80c0109aa4205201c00502c410340c018030300d04ca03902541c02441700102d56150340c0e860b50710079204140002141007042e107001d01c00d810010806582c3d04599203010000107001c5500c240a40120032044000c8141008000758644482400152520600c100d184004000d16554004414040c2990f0b002411911781042c1e01d900320a44540c10a0130082e40341010131b80003d600103903025a40030039060404103903c074003000039070f490449801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 505740539 1250 505739289 505739309
    0x270617190908040305280201050901020f01150f0f14101103070b090c010f0e040c0c0b13030207090b0109170309100207140a12110d170901030b01020a0b011e 69
    0x1c15030420594038002d200703417400707082141c1d02c0740841c2a90342044241d2402c00c1c0d810540c1440800010f5000c2c0d03000d01005e00d814015110301d051a007400500311413141050303c400500b00742e010004a158400c004029010000c1c1742500075081800000c0d00100c001d0146016107900315034080714622030001a02a8640030050326035441c0542003240501d40c0070b603885045030040d0086081035601608803040b84408684600c803003c105402040001c0195050050074006000c00b510700080020740490311035821915422510025810700030325000c1d068000000992515612004a86c0c1041141003203802c0f1800300c4200c81c03161200d4908501a010040341c2001d010032101c02c5607900495400161000751059030604891030041244401c050312031600d0000043c825007001c12102e4040340500000903107821030600c0e0305d542d461070668880c014402040e10100b960092036074107004040d520031092004000440b5030741c9070f201c0d052038180315298440d141d0010f1504607801054030f9a0043c41d1b4240c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 505741789 1250 505740539 505740551
    0x40513060803120606160b0703060608040b01030b0c0c03070f0303050903030112020f01050702060a020c09090a03080f070504030c03030906080f04240f020705012408070b130e010627061719 83
    0x151600310fa5038140e5102d0040782c01c000010641c6486108cd0070b1141d900400d80c5a526482e60311000ba003200060419002000d04101ca415601d90030001041c4440c0300d9030841d0350181060400408444000e040841e040e00308000410108171140141c005086d011102c4240c40039180005076414070134504000d4202e08045518088160007003054503404505440303011103543c8007080640c682c0400007000300444c60201c0403403c2401c07500c06a9a002009050080c50203440c4c1d00c0c0c410038440c0ca0350003100050350039202442525440201c050308403440380007000103401c080e0ba824824240301c41070381911400300d40c1da0f981d00d50f600d6004400c0300c036039182c801c5590715601c1c18a18040c06e0104d04251003030103040700c0c021070b2044c1143c2d5003046074504c0f0090035040d0f06001c008040b50780203601001444580160102e02c0700700101c1c92034000c011a8480781c03881d00c83d01c40c0c80040c290454030f0032116021450030402545400c6446441038003800e0010b011240e550480c848410104a0740d04183ca0b85404 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 505743039 1250 505741789 505741793
    0x90a09090818120a0303020706090507080304030c1e03030c02030a02090a06080111070c060f02070515120601020c060301060c020d1401090515060307050603090f011104051306080312060616 83
    0x110081c800c400301648244050320b8100140710205044040e91040c0e54852400240401e210b54040d0030f59602c01c40010074800060f071551407508a0329040420540c00024042040028100746000104a60042c010700b02c80241c02c4446074001d64030019042c00740c0d4104e030108542c0c06120803040258000c281e10784d03034100801c18800070805030240b003890b0742c60100c443d211904c2000c1035698040d8403101c903400305400d00310225030b5094052038100c20b61003000c1010600f40da5420b080c0111148a08690361110306800c2c81c03881016015003103d040d500720800130f40240e203403601264150340c2c0a04004100185034070105081070f10220b409040e0b1100214082c100940640103240c141d4010000c0303500031105090480e442c060180d4019034542c1c01900708000504101c00a5580300d030a0300c00765039440c0b8022002500752295203160701d541300780010701440030b450b0a1194000d201c5441d2000c11225040910382c0355203120b124048040c140c0740c000040c15503a5420104c40d003031400080d40150b10b00c828 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 505744289 1250 505743039 505743053
    0x210060b090a0504180204091502180906190e0601050d02040803030a050117071526090607030603030e04092a030204110306010f11030d09080705060a021905090a0909 73
    0x51a240b2400b600e100005591405000c1c140c44184c2070107400c8a03c0000d5401c020061242c07a0742210705056004145490201c43d101420380d465501145180903000481000503080c001486240b149175061102880103001d07054010035a204508041160f40350751005882314010b10005000d414000030f8081444c40c4044095800b40700100780900c0076907280d040f440480e9001012529140e400204100144c1000c4414061715061030b0516074103d046039890351140b0341c5046401804841c1003400e104458004100403944180c00e85020071050703007141c0e8002c00b2070000002807072080781c441c5900d1013441141040c0c9005142d10907001c1003481124450414200498401a0320a510b44003c412481502904581c031515050355a8100c07502580300940d10f0000444441c2072a01c028405022290b80d1407003140c0702c250007075280c0ca444044034076001c3d1500d40010030300c4c5010360040c40b283d00d01926003403080504200c1418800e880305510004603040c00f1195216046aa060800c400300703000d09 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 505745539 1250 505744289 505744297
    0x905030a060f0b011b030309060b041a210a2a0602151b03060d2609150703020d0f020a06051501030c1416020a0b031807140a05060a0210060b 62
    0x1a079181031002e0500480151000c0b1032401769040024002582d10002038403940c48800110f2140000144050808001c0390440c2c03e8a103903d441d0741c0d100303245a1903a29050180300c2030585210700901d4901a000c000702c0c0c4850500380001d04407119202440c001d400e846054407801c91164103001c209a41c1d60314020341e6480c10107402c00010128002107248042c3d1002c101d2600307012811054695160a8103020309000717403141c242d801002c0382422441301592048a6080302c101d43c8a00c0361201c1110f020440310b10b02c03110400c42d0800040140000094002c80d01c02c00301d041d18108130281008080b0300f68140080807100620301460030040041c0d2a0120040590741d07078082c1c1c0c1c20020006000d200b620b40f42a0341d19946143c210a20450f104e10401029500d0310910280c8003c10856403817903140302075081074030320302d69202c0c0940c0c6030881c0c43c204004000080c07c5400a1410b00391030301011a1100c1090b00074117004007000500d00210038002c00c840c0a001d000d0510030004e1981e6010380d42d00e2900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 505746789 1250 505745539 505745561
    0x50d0c060809060106050307050f1308010c0e0103060f06050c0a141e0303190e0a05100b0f030a0c180b090709060807090803030a0f110406030f051e070309030905030a06 74
    0x7021404a0030180001403d241a2400d07916114610307200c15078151001d4125000080d041d1004000d082d0940c1028081c0400400c000c50000c150700e085060f002d0310b20720000e201c590404d840e0000c20040c9510380d0407203200b00c462600307055603101c00020036141000354920015041407400141c807200d2a8000500d801d100744502c48110340003501c0e081c21500e0384800c0e103180c0c4580b46580c0d468815500c460b484100110301c0b5000700da08103851962a1801c2c00f047c000004680c0c0e44c4d58030019200d0800b0203a1138125182103002c0e0105031001c4e5199808103846004030702030030303207044a864040c40582c1e202d60804500100581154600030381d0081c59072310640aa4130010b503404011580707107030003409510180d80026000c2d40c1141d69500650f0300405121b803401400d2611058103481d08018107009201400322540d002c15103d044403a0b0105544024001c0c10754205a18440380080c250741203042c0d00300115140105010302103080c00c84071004290070055050080f2600c150811101e0b9120401801e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 505748039 1250 505746789 505746797
    0x6170a06050a09050a06050601020f0d05040e01080a021f140403080c0111091503060321040918020117040f0b090a0c0e130f060e010614030f060403090b13050d0c06 72
    0x390b40d00d001c40080d2405103200070842c1d4001061640050b002c0c6d0007407a440368062040325003810044100500d416180c0d0444008144005000c1c0315409281c0c4055001d040010028030b80c4072095400305841c01c40c807696031060009448044800c040c404d0075080300b801c012441c03590300e031612070900309410760180811001d20b62824008907101c0301315009840006034020544100d441c0074494688042e4001818254540102c1e0703003a030040b50810110580790075500c00e409880781d09240d92381007160344400b100500c440d90078030300c040180e9103d4810b084110348200000c0b45500c80b454441801e900205005021014035410400109000a02080703031700c0c02010500051540d45600c00345410302541d40221a900700c07501c4070080741e80d4030f8170354402620413540018030b0010498803c1c01c403681500043c21840500d4039041c3d080c03508000d104180e104400140059082a98001e0090310f624410040010b20200c2e24907809182158880c0050001134a444000b0b0510311b4a41c8000900b406060041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 505749289 1250 505748039 505748041
    0x180a05061509060c01110d0e0d0c170705030c0601090213050603160305061305040c0302041b080121050a0b0907230d11100c0624170106170a0605 64
    0x940360100d4116041c0341004603140c903103082d5405200035988280303001d80e6650f4852800000d6a00070788010400a000300c5000141c1c6c00402e11403a050250b5151250100003440c0404070110304d00407200580c0f9013040115070740d0b60280d40340c40c0c0d0450041800748019402070000005024640350020560042c02064081c01640c83e00100a860700052307903011800719442009004043c003e9001d981c001c00000e080c800340d40c084120486c103580c402ca80445840011b00d0080023141058003510100b201820b1100310f9a40300e81c07000074446401442080300050403c0d401300600102c80903030fa4140c2c0e41100c151840209241030280c1c482809450488640c03196075000600104e13640540804101034400414911411004021407a030310b454041e5800309103401c8007100d542e100600b0319a4504291030b40780a414441c104502100c006a01142c9108407204220341000c1050b8182d5090300c1c03000400c17410819650f40101d00405c400c1c2c10412241000006080044c1000200e11010781d203e0303801442a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 505750539 1250 505749289 505749301
    0x904170705010c03060824040c0e18011503030e190f0e100f050102030406032301060c1214040611030d0216200603040212150a0608070e0c0403031b02180a05 69
    0x25407001044144007604504031040d000702d02808100b81c100c2d02849c1c559201544030604a81000d0054481401c401090311703010100c240f080c0a50f41c0405061040e204010b40b46072805007000c0f00c1e2840503803080758200b1604580c104601142e2020f800703160280e04100d5120801e4808043c4240c0d4a01e60030700c400c1600094440301d10310354000b40c0320180e020b0340c1410700c1d280d0158007a21180006111041113008a01c00b040c02070f1129038020481955500305400d440e081020029410a032034270708100c140302d1520341040300501120200e844601c0c0081d03d0240c510600750460240c00703605040c007400000d11190300d07440c1090205c00d540c0200c444148003801d100720000d04001000000b6044401400041c02501c0d01445215251401d08140c2e46a020700340d0500907607a030100d921032040b5680b200d081c000e420041281e24043c1404200c10340a80c04e12034090042d900843c48000d041192401403900d04400c526403222640b40d0281500c0740a1302401e141d0480040200c0d40d54008520301303000224 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 505751789 1250 505750539 505750543
    0x10e04020406021504050307020d0b0609090a03020c15120705040503070f0608040f0201020f070303030509070b07020d06020717070b461d2103070206060904170705010c030608 77
    0x2110300c107030000c2069003401d0f02c07682c40c6007138024000d030740500050042d0000350726050744442c41e480c85032500507883c0c40c08100b0414400300103010300165901600744400041e8000441e4001c2101c1210820105108100311100d144501e0000e40480340c140320600c100300c1c1d00100508107441088082c2d516940d207076528440941d00c80c1c4603010028011502290118402d6000c1c07044850042c030545003800d51804070ba629000103a802100002e0361138003007014a1505000d800d0140c0b01003450b0500d8500d498002078940c48e150b0303c015000660001c4c04c4000c20030800c0030042500c0a02c1550f07503c61100e400c280046900407a10030f00303011401ea601811380030fa12141c414101107001200d847c1207013001d420500c0e400d4408800340080b6983c0c1c4182640104400051180c004090010260a250035080c49103452641c0724501c0c1c1c04400340180700f070709500400c160b607100034180e8070121030b0742d11820000a0500ca0020003900c1400000300d0b60140241074220f550b10300c41d641c4051024980e0f5640c115 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 505753039 1250 505751789 505751797
    0x51302072a120c081e010615020a1704051806031902060a0c14010e01020c010b0303090a1203050d0507180b030c0a03020309010605150406091a030609060d06060f0302010e0402 77
    0x418002078048003884071030000182040914010a580100e1a88403803582d86800f842c3c0d88510b600c000075510504580c8002d000d210040e1a00b440454090140000065038a606210740180f58004222440c0f000400c00301c03c0e10010f02006060644000350902c0c40c40c2079a00649515010340614410b0310804d11030b0100310b010360f560240c0300c1032a03e405140708540c0e80884280031950142c1000710045810001d001c1c21043c1d60340b0b40300041e60346503412541800c440c01a0300442c069001440000c015648400510301103c2c0b08003907c80c1429503d25084859100381c0c100000410314003001d000c1120342c010011070032802c6c410a407080041d25400c400845000484c0c0e5120403100810a1003c8907102e5009103400183c1f803c00450002c0d1903000007502d010106803024400380c4007140810109034460601d600412461117030405542104500100c14400100643e0040584030045102c648a20701d90110940d0841410402d480d1a5007444400705560322080e40080c0e4800d020030100d04d001d01c211 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 505754289 1250 505753039 505753103
    0x60b04030c0e0601030e010c2601080712080412211706010f0e12061b03090d050c1615020f0c0f010305090a062313151505130207 57
    0xc20012490030b54001c0101000074000d0381019190303201c5511105007401410312014217610b40300381f11044442e40804e140c0d00799000c02211511b050041102c01c8000c2090300c16030b454190400523141240c24000303001c2c0706542c4007c0c1104440c9001c1c005001d8440324080ca076103010307081000013005c4048111003400c0440229080500e844000c5102c3e0341c019154032213008024203140001404040015206001041c20464160040010040d90003180c0d418440e000c90010791b1203046060480449a5640c100880c010601c20f00081c0102c0a881c108416450b060598640c04840c58440e0b020001055a01c2a03410151207000c401d82c81028000c2a000c05502001d030401003412000d02c01100074080c0500040e10502038948220082011030003070340700100c03581c0505099a1245004c00d8911800100240c046a04e400b50142c001001c8a100295407401ca02c0081002c0009004810b5134100e950701596001050b444a0044884950003a02805004800340c0081031510000e07400e0f100c41428403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 505755395 1106 505754289 505754303
    0x270210091d01050f271e15012d05130e04060b0405010801090807060b040e0607050301050906090c18040b181911040e0a0b040501080619020a0207050d020d0506010612060b0403 77
    0x15169042c050844811800d034201c6406680f5444510301c0540ac0100c00141841d014142d1012040900203401d03400c1501d003007900d00b00000741610110740b8055401c0100018003000d06109021000340c0000042d0726000c66540c60800a00100c0d081c90b80c059a1025880f00b80503042000511400454442c0c60341c07541044208030711103c00070001c034030603640174003001600c1c03801e103099400d04240c1004140c5104103c0700050040e00118045682001140c0c001131701410f04440d80600480192080010241000d0481e0003640c032032002c0031100304010001003003401c40e9684a03a6001c420004c0015200003424001000d481c000c0c0d104000c42c0c0d0101d4184100e030f50000c8200300007626100011858480400c074042e40b110790034410944985885000c40081d521100741c0780410070340c0142590125a11660b001d00140c40007003001300c00034a0308001003030052101007114166600041 = true := by decide +kernel

theorem cover : BRFrame.Cov 505575539 505755395 := by
  have h0 := BRFrame.cov_init 505575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 505575539 ≤ n) (h2 : n < 505755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
