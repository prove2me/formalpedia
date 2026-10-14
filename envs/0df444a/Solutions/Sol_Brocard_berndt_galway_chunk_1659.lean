-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1659
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:05:53.823673+00:00
-- url     : https://prove2.me/submissions/3e6803cb-f2d3-4ee3-813a-89bc789534d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 298201438 ≤ n < 298381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 298202688 1250 298201438 298201451
    0x40f031b02100c0203031c0507300b01022505030d021203060d140105010b0712030903020c150c0105090601050a0f0605040e1003080d0c0e0409020604051504050a080f0c04 75
    0x41e260203600320300b902001d14103c50100c420b48002802d600c103080f0030f4050446440281004080c0c0c40d482607000f1006911000983e09801c82c040740d00100c100020003100035900d07500082142c05130082a440d00c0144180c030982080d002740189110100940b0706480d01c0034200a02c003a040401c0001032440300d40c00140746101560010020b85c2c44002c0519001d1201807004100f00080900800488131300c07800240b11030b44e1100c00b1000c0e560005101503810071502c8119410f018080c0c41403440440d010b6002c0d000614004041c45a0b03004404440151500104600392040c0b0083c4107607070089002c0006410b1759450f1030304000321840c9682112600c0e80032101c0420060360417104443c21a0342d140785a001d1503803010b80301102a01242d00151401c980014441c00901050740588540081901c900418001c10b006220450f906440000d4200ca000c000038490362510a001a1205d209800307090301d42902e500c08920356002c59401504194003d2080c10a040b2061001d00c0d075059040d901000380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 298203938 1250 298202688 298202693
    0x708060c040806041202010e030703120b040504020d030f1b0f17030c1803120304051006081603020d140f07030507152a05031c0608030738040f031b 65
    0x102c0034058001812070807005e00c04105a4000e401405210b4000320560351a000c2d6410054411912501d074480080d00d404001c3d0f409203854072480340520b8024207440da920165a0f02a01c0d042c80350f824180500c01d4030020240904405142c0040e214404c100356007845800e4500401c03d0812000031541650052007081000814001561060820840d0000801c8000c00c042818041e00d2080d00030070280010400050150000d8010103d1070400302c00c210b1980e680c00c0c160b8076902c3c4140d0503070152402d0b01c0c003000946400c082c030111550044c1c070b10144041c40826500d1a080c1810005403e5402180042007401000c0c0305040080c045105031021545450100620241811824040c3c4115000c171520910090900141c21264005c0813030340d56894081d6030800162401e402c280341503003046804140300d8801f20a441c0ca0580c4050024854200170308030520610801451519215418550807541560064401d02481c0101030030001040182001807610080000d48485c0700c00c8410304000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 298205188 1250 298203938 298203943
    0x60308040b0703030506092208070b0103030305011e0305070519050a0e07020f0120070323040f050a08030307032a0309060e0c1807030e0f10060f0b07080d0f0903020708060c0408 78
    0xc5d0708803155485045080c285009e610b10f024049c0054425244200040704040e01540070a0580300c90510580b1100307000c491101c0c1c40455030000a1a90f04184d03401c012504142c002d0040c082403101c40e040f50207482e0300218040c0d108540c04902c19485000c14040080e8041c4401504604004020700190123442144d4150028480c14003280700720004e8000d041c0342c0302d5070b80d000d111184e00c6410503882d800e0306000c49070307034000b8040d401711400d000200140364a4074900b800c045034030324009181540e60303240d000d40c014555480e107a01e10004030000084448100001c00c601032645460001d091441400e0032021507110551550316a40131400c04d04c015501d00c1070021510391080c021071516910414100c003e481502401041442440304018540700041502e41451170b10490401c01541d0f66152103030440303424070035503044240800070070010400c400010069000682408180c9c01d60840d28a42203074540300c4290016040f08a051003a0702d028402e058111200c250b5035428039040401e1580c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 298206438 1250 298205188 298205221
    0x9041104151407060f05091606020c0d08040f08010c1b021f1206030524010f15140d0212060a08030a03090203070506040f0612200a0201060308040b070303050609 71
    0x40502280080b40e10070010540221081c9650007101440040d1041d5140301c05070009840e401c6440c0564450351249120fa5041c050443d1050b6005243d01600c3d942482203500641800b6a162403080001040700022111464001e001300c10000613211b4090b6002010342c44140040d082c130390401c1040001580c2d072030f82905401c1d030402c24004480c005422042c0d81100000d544800c213107040c0340700007092100110705007001e80d00b48507680c0328202110707512841e803120900613662840140c031b000b0f104803000f40e49140d85080c03643c02d00500382003038070025440c42e81144490104454001480b003e180000d151a07a420000a540c100e12480c208042d1315180c1c001c001c1170800b0556a01805425550200460001000c018210715550b07500e40c000c4130410740302c50003008081003420141c01510740e101e00c50301c5884100382079103a80b40560203140f80310700d51181005504541d00e420001c400705181c480180001c1c002406156940c4406250203020303103400070480351040b0700f68000c001c2c0910349505002c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 298207688 1250 298206438 298206479
    0x60306141012151401020609070806071103041d060102010f140c0702030c0402030112030801061d10050904061e21020918030d09030813120f200309041104 68
    0x52051041c02e0500800800554400c00c1000001d4000007078620010615101114004e80c2512015620f9a1403150341b02840e11400405600c110f000440042c03180d0100310031040c02c44190380c0f51170f03038406401411001c608461241c0702640000e002c1c0c3ca680900c40c5400c0001525000d012000070040c0164148000a00e112a00c04000a01108550741407107032440e0340400810841d100c0d6141ca003040d611220070401200843d03131500001c2481c40c02244150110001400c0c0782c2585515041800360401147c030003c1d05205007032000c0c0e10b0555890095a018264001e07900c0400701042080c04840085030f4800c25401f003810420301c040c0c0c20141c21026580e40c05035552101a216424421118204401d89004a0001040502c0c0200b043d4002081250080d070302c80c2075541b200d0180700001c050002c4000c0102030b0014484c1e810034054005400585228204645c100e90040c081c0344e00c10274400705102c100d07040050310202c01d2505200b210344901d0244811418a03003400240c1d9800d18048210 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 298208938 1250 298207688 298207697
    0xa080a030e0f0112060e0612150c0a090302040c0f1808120c03190c06140c07020d0201031d0307060c030e120c011518061a04030219051203040603061410 67
    0xc100d03103a4001c2c2c950780a00032055208100c241c6d550300b00c40454440035140244541c20180c0707036001d10f1000081400c1c03c0b0340c0d400f004600039119000002d905910007107160062008005000001d69194441e851816030070b41c460200160100c3c100501424041042504910305890309000c0701c400051259028608070840950307030151007054501d5406183d000310300185d104890641d071240e105141d00304d40d81c030480741072014500e0030b10b0049002008031414103507600240001e2026140c800030412030140181030014041d210700c1881610300061740101c012a5000089080030042c561242c070381c4400300e0b0f1508010300d10288003055100d0f00c0c03501e031002800a001c6000f40086200f9170180111541004403a07040683d42d41c02844035013804109180094a0700b0300001e0381050301c21041401c18140c2291a00c0d207402c550800242c408665880c0d41a548501404280c81e12804402c59900e51110300458507640341810040503503940f5044801e21402007400030307010ba01c41c02c4405216040c60f080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 298210188 1250 298208938 298208959
    0x111c030810030c1701200a031a102c060901080903301003081e0d0c02060906130b16050d06030308060f01030509120306060c06070e0a080a030e 63
    0x10036102010642024000d480b0340080040c94150781d52000703180a41d082c00034400a2841208800035802e401c00102c5044c00c200095001d0301c1c80b0350309c8507680d20006054110000701a0000c150a44090700ca58030110324030081500d50000920850030171b01341401050001d540620020840a004a13006c06061042c400c02140c0f48540600964500c400d5000c03000b8000c0402952880c18640e5030400164280d0908010071211400e8101c07030000c0da50445007952401a44003200110408001083c03a1070f450140302c0540701066602034800544280d80c020080c86c10551802814640040d0144800d40950303164900080c04103440d075035000c8184103000300707005004402038446110b010310306000d192510102000301500580c605018280940c0c1200c20482c40320010340c01c481054400304c0055011031480011004054021644280d01800907410000a40d00107483c128095602001082c0e4842e0214910304050201000406d43ea00c0101000101500c001c4c18120301c500b481800b4441c00c06 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 298211438 1250 298210188 298210201
    0x6030c020328200a03210513140f0a080913060b0d050606120c0a030e10050403020106060e01050912150a0c0e0103112a0a0b0604060f0609061d060406030504111c0308 73
    0x5007640b1000d00781d48203110072320b00b12510000342240c00c001140c211444608080c2c00001c000380e00024000c0600c01070031542081d4a039100c00d60459042540d02c1645a24101c20501c06401100c00034860402075988580e0080760110a40340300508040c02008144407ca2162843c00002354210502d1030034030356901c0c0c03817031030403800740100c0740010340e4600c03a550858004a94a034803252040703000790b0080100030780f9088210341c8407000d07140e510f00290007400356070440e00d030414031542c00000010803540b44040030007800302e04c03884c121641e84040b0350700d004800394241c202c4450304c41c00d4400d1900700300404800d07072102d4413801164203c221900407080959a12001c1548000b101100001128141304880c034091030307035217000c44a4600460130b02000003080b00c2c0c200d801205503191038845a40240c02c19800316041c50306a4a82e4100b0480a85d0011084d120b11004001801c100e9402088034506820440c3c0001705205146000c1ca1042e0840c0583c08404500e10740a90b506140140e4140c03601d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 298212688 1250 298211438 298211477
    0x3071107090203070f0f09080307081315020a1106040f12020f04020d02040303090f05060a05030709030606030b0610080f0a0b040e100c0f02010507080106030c020328200a03 76
    0x7904801c01161002040c051104e800000c1007510501c1e81e500d4a0003880035210440e4070402c14030403030110350300500c10400000da080300a0301284115801407084590303101d070606000c819410040003d82c03c00da061800344240040c40541025040d5059480c0c5481d095003400c00441a1007500c000d5400f00c20814110f40d200c148271541c03640001e00542d240c00d03403410503e0080d1f000e8482280850906d01001841c69000442d01e0304a940003000d081c10b114404105403415440108813070304101d60240040001152032181c5005103001d00c0c40ba502520344141404000071207540f1140070300034100c00300901800010840c03540b09480f10710200d0101c1404001c503019003140200d0040d20f00540c00403030b0160481d64445110f0270950344d1110703545801c030b1105a080754400d48023000098040401400b009001e07401451003414140b044910b01400000000c08001c1c40f461b48540e004c40200c280401c1d103074891003a044104141800c040d2860700c4800c9641d41d56036400b0024144200100419802e4800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 298213938 1250 298212688 298212703
    0x6010303120209090c030a0b0d1e050703120305010f08010e1c0909060801020c150f06010e0604090207060624091806080d170a09050a0321020a0c26030711 68
    0x280003d0b884e8100b01c54440800c0c2c100311040c00046152034080704107440c250100035600d6405c07144050400729400c1260034103d030000d42c1952584a041d80c000005038811010848007452941c1c0090346504049048050841a500c82da0941c1e040450b24211084046800c10720502c03142110501c1c60350507641074035060b4807548001c2c2214503294001030f10110640007030a03074601d0082034541200700d040c00e4410b2641d050314404024000100040c0b86035014018031400c01c01d0080246051558500d09601079034814542141c40703d445690400114017840118240d4402130040341407550800b01d0014407a0f1810b2103101404c00403004160310031a9642d10000c003402d104020b8480c00c001a0902501e01d00d00d00540316180d042d03200020300d0303541d0300e03115940525500c800948055403070780c0c13821521034048180d40c07003440443d0200b441304640c541c402000d904945459213401d0b94003d041c8000c024400c21524a501c10101d580c1d6981c500c1c440040f2907001c0c10605242c2c400b15615801c2c946403580 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 298215188 1250 298213938 298213957
    0x190b030d020a11100c1e080333030a0b2a0a121401090f140108160803180607080d0f05040b1005010207170102121005030d020609060103031202 63
    0x640241039202a40403500a41c080e01a19503622402101014800803000141e40301c00000c1c1d81008280016003203003150a01180c2e000340c0700d841503055840e881d825074810784103840c150400d0608102c02c1600100040d800220545045c0c5e6818a24000b082d11082042c0c4010051040c071070028060200d000e07030010700311400c1d510b40b5450710403803440c40420340e0050b001d10000c10508004008158898095000c4400b0342d540c42e010f06910f041b0002000d4115802075071252070319480c505482848403003419000304501c000500c8a00454603040c0e010700b00d141c00445054108004484c040100710050030321558080d2503e56a502c0b85003080051801030f407030206201400c051050f40c1d10701050304100d0082d801410140c0d016140d210b0340c2810503035140704072070168100d450100b1007000f0702401e840304e00f030f170b00b0001500d880c48100e480c0c04180011150002000d04c092020312403414200409480b50b001400100101c2c14011060b076690801403000034204a0000703a1401c0400503038040c0d441c0c0c4034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 298216438 1250 298215188 298215193
    0x80d02161502071703011802030403021f0f1103091b01091a030601090801090309050f04020c030d06061b0507150507120c060f0b090a0e2406090a060608190b03 70
    0xc03900742103480654003000d411385820405440c4030f0051160700c400c981c121100341c101094080d1002011001941004000b903095015030344a1013450340c1c0c0b49504450400200500140b074000036078107001100c41203002040002c0d4203104000e0002e0000804424092400d0440e4800000f030b0300c012601c2c901c0c1c58124610550181110b032020440c0e107000b840c01507900362a500700181c1c071500340508031b500307480c1c0107000a9003200c400c0040b4141400141400e41000e0000351a10100c14442460b42c0e00446440c01c60726a030340810414103a201e00c8259942d003406400c010092155120340740e03201c01d0b038056a51180c0a001444a100c0c1c0034004451056030b000004a031441e202140c00340041c200f042e81620520b062000c25094440c00303208079a0f070b0000080000005403203030465800103115244401c030a03482603a407001740050b01000e06c180d82c844120b0f03485d06903260181c2030240c02e12000d04900010741c02e00c0c009000841d00000aa42c0c401c0e02a0350810118150010360f02c094000f5002d05034150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 298217688 1250 298216438 298216463
    0x6030417070303050403090e160e0301290f0f0603073510060207150e030709060b031f2319060917030406050702060c010608070f0806060d080d0216 65
    0x2d50036420581c80b42c1d00a46503c020507075242030070780b8175000031591a1501043c2c05418120070380104d500c0c02031020b0240c0002414415098031001c84c8444840d640982200b0f07645051042c5000074412200710026070714118440c2128020422602001d05440d0078072000071480584801d02c0318000709082d0041d51100a1103040c96000101d4610a55411440c954031b07400c0401c410780002110700c2284e001a90901c441e03010404c048030b55602038442c656250107000c60001c0e10450600492000c3d281085c06580c1c1d9007003070041b5a0629004030600080540010410000000c0707802014003144415a0302c85108205000041d0307103d095030003039140130b10390380c1c1000c114940c7c441030035070035514585880920782121034401c903503901a51181c00002001000508010700300040030317018800c030a00000c61490386641903541010300b940c01000740308020070700070800b20a08010103608410280d84004002c0b080391189101480b80c0c404580c49160006000b01d040d9a9141c4a401820341001182006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 298218938 1250 298217688 298217693
    0x5070312020d050414120901030b0d15020310090b010f0f03020c010c030b01030b03060f27010606020102090f0405060a06030e0a0c081e06090a060c05250c080102040302010c020603041707 82
    0x82c4415101a41c6009011603083c03c1443d0004050036001c00781b16a0508240000d00110050855070340301c1c6410004d540b04210000341c045810203854202c038a800f60300d9140c0041004c260f2407560740036001c0d003030a240320805103036007000101c0c2d4040c00500c1d0010020581d0700c0190060312400b020340d440b175841e243c92030120795819030065a070098244c0c0c00307102160b101800c2558801040e2a1854400b981e10003040740a0005142c095010b544c3e00780034081c034005203074070a085800c0c541c4007401507500011300318600e240000d10000130100407903040010f81403076400f14881950760300660341815030b0b460745e562505904000c140c6109600410504020343c4462405440c2c02e24204d01c111045101c1c00d6985007545d0208085d40b0404038800104102a075644458000d0008800184180102008009a8070000c0c103407840e0207040320715001018a6003490090340b003642c40c1d40050f01c1644180b20510040c2ea102600310240c0d42c04540b02c6403a900d0301e041003d040c0d0616440c00764003030700010382c8004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 298220188 1250 298218938 298218941
    0xb0703020106080d110705090403031506021b0411030f040804120813080d02062e0308130b091c08040b1204110904022d0a181b020a0305070312020d 65
    0x43c0c480c2d41d000d864400070039001c00d42d60705165850300225904000380034416400c01a88003030b8003501905e00403034a841c1c0802074102102031078203c980141c00034086440c1d15004c04031201a8240140c40c204240354407221404001d0101030494070f0381541c0030010500340300c03c0c0e0003590082c001c044620180d00b040c070300d0010460350010510752500f00da0305500103a60030000c540c540784468190060a01a501d0012488400701d0981418441c0b54142464060324400064550007070b621078203206940384d00300c0c0103120200300207600c695a180303020810300b0071985440d0f207031032019480e0a20200082130545041e499a0040c0d0304021494400802c0b440342c2c13903030080c1d403090240303001c0d00c10b00581c0062a010b02a140c40b0859010b07411140b8040784068522101a00220407608840112641c0414000042c2011407940c000813104200862001c4220154031460f581e8900d6401030341e204c4240201c000e9201d5201950103010b010340072030040c0525018164200040c129413008540da901c080c1035420 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 298221438 1250 298220188 298220201
    0x1e020310060806030f1903031503030f0e03070807050f030109060203092107030e011b0f060c11070e0109020f0c0d050a080705090d0204050603100504050d020d0f0c060203100b07030201 81
    0x3000556440c000c20306500b004107005c0c0c00c0000310b4018000107080742481d80e22194214404400301542c5038048200079481c5480600a107200c3c0c1c1d1100403064240740010901158007840c40e100c1d0f00485010046a03200080d10402c41e0410b40d0a42d540c0710070b440c0002e00414013007501500c900d000008000014030007003644421540781072556000e6400010712181c05001c1c8440080101d0000d400d40d160940c00341c2520455841680002040b880c2c0590342c00c0201e060f0103904417016138480e121800143e801030101108030500c94003e102d0340f803500e10600704042043c410901890750000708032189082810854441d03032040011542240030401c00201907510150841e4001121040890192881181124489200140a03a512829580030440202409801d05c3e40c14405c60509417860110380c014181b03c0c6001d40b000d00403249140001904107120383c50307601c040000351300312180041e0704071030419071560b0807400040c2c4a95440c0c64503c2c035490650088549140041075480805a0540041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 298222688 1250 298221438 298221449
    0xf030e0109051c020d1202180418030e030c0a1202030c0a06020f0d030b03030702040e0c0d0609060b0105030f041e08030a0f06060302030628030f0b04120216091e020310 74
    0x288100f1100000300d8481c0c6000b0400b00c00501410b04400e2104411b401030060314400142c1d6000c100d1b00500004c00f00c0d65012244d411405465054809154102c2140705040308250040c00c650024040007503c001694040c8480718214100769405540b01080b801d503400c8006400c1d000d0094076104080c1d0b4555104004090a01c105070400342990b00c01d025011101e5400b400640c02c3c00040d9007004040c1810039101c000c82d02c01c50491010b903031780381070f80070012900904002030040340c1c1d8180380056502101a8505000e01041880b1042d0b103140d42c10750f480350f04600801015100a0007074074084007201009080b0400100c10700106103640c0c0d02030b107201c07042400100021359850000780d0690004849171940081d2584801085da1040e25012001d8288101000780090301c070750f44c85840818101e0292607402d0003408000400407411030b4820f148406000604026141c4a01b080d2800114050301d4049034960051610000140f00f001d540c800500c0030564492a01c0b00300c00c00c6100d403e2044 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 298223938 1250 298222688 298222723
    0xd120f140108060c0403020a05240a180503070e180c0d03030212060a0602030301151403041124190e100f020d0509060301030b061f0504060f030e0c010f030e010905 72
    0xc1444400b5413000c54044940c09032491540915250030007200d8010400300d405801003041020b0581140f410090006e684d49450f2103031500050f851000040c42c0ea50030003070103a0b0010303074141310054028603406d40c446107005000300941c0c62024628200882400708071380200c03540040300300701901030300901510140080c9000d05550790314100110b019282c4290340c0942c00420040c041c112008280b480c2c40c0d07090f4100300b00c1c454020001082c0c41d610440e000d85a00c8241e010700100d0740703802801c0003050345070034005581582da880f86007101da2003129642c65031001201031043c1d846009401801c00010f004211080c280346540740074089940844180d0010f0150503090444030f4041c80c165050010003900031400c0d603003990707500461000040e05681c2d01c4070007154402c0884400d48024103041030242d03a0251218a0004080d24030300c80d60311601e051600303004c1b0a030500003000452984211092030681181c0c02d1446056004125110300910903500300750415042c05000078400500710b060401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 298225188 1250 298223938 298223941
    0xb0117070806091e071202070b1306060e010b0f09280323060604020c0a020306040311070f12030f031107060203090705010201051608040507170d200d120f14010806 72
    0x42d07180c11a20080c10710070881c40344c008144824841e04181d01200c000f00307001440c00550740c41e4841401d0089603001c00c0c1d90070040b42c020400400e80036020060640f44c2600b0a43e5040480110540c02a101000400702d408603103600c0c556521082d400918880b41005d54403909025640014a40e4038001580d18138250078103031750b00e043d0307060852008000341c0380500401d8170790310f01b00006507104101d84001481024454030143c0d4042c0035450103148282c40f0607034a00d800042d40c0c0c2c200400d0394400a031380c6610000030404c10b00c0000150039029810301d0301c83c014203409442500280035181038554070391000b00f140000c102c8958011401100700f80c08030b40700c00395107400483c240d032021030341030b840441e40f01900c5e042c41d03025000312608a4030400c02d4031042c684800100440008043c1d0a2030298002c403031213100d080d00890300c5c40d80505182e00c060040142c481c800b541c0c9032a4141c0e1401040205089244261916801490040da0381402480301400000c81004030440c28068150540101e00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 298226438 1250 298225188 298225201
    0xc1c05011511060c0d1a06030c22030305030f1018020417010c0c02120109020303270306040506070f030209030f07050907031506050a0c12031d0601180b011707080609 73
    0xa80500c80e203140c0c881c4030b28003006001e100b4043d004c0c078003a21b004511145100311032940c48002462046404031005916003c4005a060155540440c101c0620450b14001c0c00070036402000c89600500300d11241034183c43d03908034028094081c3c1d104134402000300803040c904640710b80003802201d501081920034413200125072400c88114209410100c7c1d040141000181401b100c00e0819104c154000141142250003090951340800b00c000681c50a0303032951819000002d00c0000b00840580081c2481e01e02541c4181d40e4070030141440c802d004810440d11b01a0f0701c01c0c0c0440c1c0200038060141c03007103903608000141d5500c1b690300416200b44424000202031600c60302c00c00c015400007110103141685080d2003500d05500074108541002000a58400415031128045501c0d01141d80c00103510542071408542d0441221800680da41001c00100704a030110070000d039a40000c1d40c40001c103003000000688a0080715608c400d4040d00740e400300459980c000048a101d035205548051030390f42c81c1c9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 298227688 1250 298226438 298226443
    0x1103010510032c0a15020d0606020309011430040c1205030706090201170f040b130201080a1104050a030803060a0b09091303090906090b030d02030a080c1c05011511 72
    0x2081c02e40821110100151000a554040500020441019100049013076110072000b141007200100d007258001403032001e001000d208000080280344040c508044460b000200a1106034804214404002c140001402592505540d20000c01c080c1c0c0105403004a500c0600e0100c210b909458815040c80c0000d00002180100007040c0d42c80805107140c1021562907074000d1180c0c0c0c900380d040144040051015035102c00b2501e00800400754101401e24251070940500c10000780340b4014804012161401030340c10000711600561600c101050400910f0700a002c1070249511140d07103c6002000003090100c010000e5000b030b070007507540080440d1100244403081c410403d209030458074200c00510382e00e0100c90403c0046100746050f1110f269511003400541e00e0b19000000b03042d0342c560b40c000040c64100880401c090550010b07500b41400144040d12180005103c07207541d00740098000c00030300318100c40502c212000e410412042d40c440360551b04881582210758040381c8201402410340000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 298228938 1250 298227688 298227701
    0x60720030d05040e0c090a031103010b040209011706040906020f04060801080712060b0a0512030d1406090402090a14040c14150405130e010606230a0804080a0c0204110301051003 78
    0x342e403665840c03c1d142c082c03451401d0000030401a1210f50501c0010100e41e2221404001103015860175100100010300309405c4031a0044420b10440c0304200c520321503600074000550560340360742001c10b103944180104c0d010303100c40c40000700114800203680d0701c13054a610140059911b66a511a401c0e1f8aa0104960300d01c2240260a501c0182d0103680f070024020313400542d002d1401508280c4050f580b1008146038202d50b8003400e8050300081120011101284900407440c1c256012400281c14040c0100b03481c1c4a0241c000307030080c01100000303000603030700380c1150222940303140950400385494140300000708014054180481c10100102c001843d041c6940c402e502c1420f00b040d03191034509801c01068142c0b10480c5c0e9480d0f80c981c9400d41c0415001e2003400001d08180e1618254558106103101c1f0619130881000d41c454410b0084034200c42d48803e040c1d134055071001000e544c85482d05002c0c0d801410301840250b009080141e040354141031503002d54100d44054070b01f40c0c0740c1c0ca0001c07819400c8e03600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 298230188 1250 298228938 298228963
    0xb03060f2715060414040c0801360320060105040c020a0b0a150302150901080702190f0c08010c02010f0b010207080a021915020102031605040305030313020f06072003 73
    0xc520918441c4001081e4901d40003e0b00800000302e4411040804801c100100e6003601ca6a8010303a0030017907402c0a004001c0420043c1e048581001c40c070100c4100041ca02000c00040d41440d074010f00304250003004184e40c3c445040703194400c00e5003e07034007042c0e0f5101c0034001c250280b41000074240740d5074000a10f0011096121082004030707581c0c0300f0403400502c5012560303c0c0c40b0b58484c80c0000981c407200001c1e0070707129856181681d100ba200300098440c080c080c02c850704547c48140070f080c1d5589000c40981c001c551007143c000700000a03040c032005084e0345420080072135190100000c040f9405520030202c0b203100300c10501080c0b011305c0042e42c640a40e803140302e4042d08480031790b10061800003800f101d0045d6445014500544070b110f030803000c3d03a10180201c0135070350010500c110394110140d007028034402803400503c3c050443d9661034580c0005403810402030303014403086007155a52150401507203000392446c0d8a030941410404100344800550b81403e031901001c9123098200403c08800944 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 298231438 1250 298230188 298230193
    0x405130501062c1c110901050603042612040605150f040209040f020712110d14070c080111070c0b0c0712062003240a05130b03060f27 59
    0x3508a06418030944611607020f0503d050914030806030703140ea10500d5400c41c0a610a040301d08603207410398407440460341c0036104825850040040703039100c508403540305600141d0301d54404640d031050f913484000341d4440b86401901250402c0d10000e032000580c401d500807801800039440e800301c1481c0902081c030703d041d0000045801c20b1040d04040c0c0080c00d0802000e44005a0107c040c600c0008a80000b001114840700750800e15500300d41c81180d41060020b088098003500914a0026004e410741c46a0b014094101142003c20f11242101001c0140384400003840452505121641c40340e2200d0310880b00140800d01c00705107075406506031001449504014024103050258406884034075100841d00b080d1512089400c1c212118810f81c01c003040000c0030b40e280d04003010440034501d2402c01004500c203012070b00200075601d0210583c00c8840a035200c0b01e01d25580480b48001d04442004150035100b4030302840024200241c01034880c2040d803092014014600c8032072000920300e0203400c02d095 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 298232688 1250 298231438 298231457
    0x8071b080d082a18010e0d0609170a0912050c0310050601020106080c060301060503040f050d0504092406230414041535100e100b0d06111c02040513050106 68
    0x1860020212510105040c5240769106e2080020070801c841c0004071b56583c0c680c801c550400441d2542c0c5101424440d80c214104150450001c08a0b04141304001c0c00c681c010030340c4401c0c0001884a540ca405000d010303103101500a0b01400c018000c1920840e00542c600880002c0408020130304003d0380000070301003032559282c14003c840a81016009030b4004c4104900040010307010801c11b20072080c2511001d40319031038590000c04542065241e44010343c0d05401400c020070381800400141c0d40107042c489000701d4941c40c0080d1200e54060181c0744650b0005001c06c05008203080005001c03c102d40c140554500c3c88600c100d4003555100d400c250000d010070310400c0103286404003030b48822a50f40900c51200c81c5d4000b500d040c281918450b0182d43d00c203004415800e0500007071107000c6412a0621010003520040b0b0f035014041d4030040c10741580c0d041419801440d400488c0c03a1507040b01000103507aa81003500c900250302030300c102403241d00601200000c5281c540100d6040310940c0d02c65200e807 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 298233938 1250 298232688 298232707
    0xa0b0307123c0b0a0f06030803040209070e03030d0b150705120c030720040f181e0b01031a1e070c03020703020a0611070e0408071b080d082a 62
    0x49203000b500d00040300282014200b5210640000391200500a04403180701c2d08011528808403031080e401c1c1c45c0d400d0304050f010f0010541420403030360400d5040d01c48880302d40d104041203603c154600c080e03135031500000a0621f05441c1c01e4203d241601e10494050051400100c8000301c02e00c510180201540c01c9400500c00b04001000601030003040101603030b00d40304050341c030319200e800b01020303580e40c00e03000243c0d1a5080c1400d01c1004018029000c1c10080d100301e50440d04005010440001c1c544000d00c110041c40001405545c00034643c044400c07821940c5074a86401c182c0f60840c0358007002960800042c1044403006017a4a040740410440c009540398003600701d41daa00044400c1d010342c42041c1c0c0c004016100c0300c02c0103006090340d5a4600074030320f656212031300303010103030748039102030911001070002061010b012595210341c0b09001410302c2c81300c152290380034425588440114010a060207680c10b80101000b8031610400d8014041c802071459441c0d07030011010580800044180f224065 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 298235188 1250 298233938 298233983
    0x4051201182a15020f0d050d0b0a080d020604120306140603060402130905070909060302060301091e0603050d080703090312050c0903030d090218041106160203060a0b030712 76
    0xa1010300c200c00d40c50b00000441e41281810400d520660842c0341d08018030ba1a00d506200800c90b600d8000c001d00b0000c07252410091040c010140a40d0f4501e550741c1c0d12840d960355403a080380007011464241d581c1d405008202075141e0b0403c480c1500e01400440c0001c4010703110384500790994552175642614014100c051108540004224540207a42003061081007a043c0070840c0082a44683c041010324001d2070040008a01741d008000c0e0318203040301800103940b45001e40703054900120340000c4046101d220301d10701c2e1095121401d055171418a0100602c0300124000b030400e995a119014135071102c3d60110103d4400d0040a000500050f018000710003035a0072407508000a4074255080c0504400024203540c4007074034040c07841e80d817000350104504090100c2c032401043c075a0f0400240ca82034491039102011151164421280003072400b264411a041c01d540c481d4010703040b184d4900c0c04843d440c004040441d00c05109124807580001c1d2015200400280c9a500021001d00e00f09407100103070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 298236438 1250 298235188 298235213
    0xb0307080604180605010515040807090e010b1302070b01050609010512100f08071517041101020106120b0f010509071b060e030a0c1a04210e06040b0405120118 70
    0x26031041c1c5840981c18200c082d8031500d003d09014510010b80341d45007004100e4004031100b88802e201c40d0503c02049140408a1103000322800701502007070113110050b8990044c880d0f507000d2a8005241409000c0e1600550302501c080c510584048400b41d89031000c0080a000d50008c241c0080c90800021031102e001e09002a00004111015400d050302c0c3cae021052408219048240300b94454082008038035030502904201d00d0403414440d0800384e02141c0d07412003040042010b02413181121030b80140342d2007540150020203801c40c288801108034506144448801d858204405802000200d86464030f1140640611200d848101100280d40c101d400c2034174640501765083c40e0ba0f502010a40072090000303041c0030107103543e00c000f1070000703140022151510001c5c0045c2240070108203c001030740100544590f9504884003d105905840100c58182c005864180c01200100e0001420940407020304159a41103810b0707007403c2d40d100c00b201d00300c5021207980141c4501658480010500425804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 298237688 1250 298236438 298236451
    0x313380c07180f1a10090506030c0c060a0902030607260f15040638070311100c020c01111009030e0307080604020609040b06040803031302090c031003030e030106050a0b030106021203010b030708 85
    0x103024441d51540040d9898001310fa4194ae05800010866143c8400380060b41c0d22a1b1130000401005c0c1c0d258010940d1950b000340a58140400785640451604076203846000b00311240101e0070041c03901d40d0140846003170070740342c509104442986140c100d103080c1c0142d9007501c80203403070116030154104001031041c601c2000e4000e14042d036080881c11114600c000c00c07200d402912050f0203083c3c5c001c01c46240031181c0288880043ca41031041c64215800308000316070700800d207000d0081650080c000781c181003003403d03480442441c0204e40010944c200464442041c01101901d02071030303568840380d4407544d088400a502c21010070154046203400e900408a244001d440a8105500c5a40d090f285600039603004200d2940c0031001d80461410345080b60344044010b480e10b0550900d440654101d01140c040202440a0800c021600743c030300354019001000c000300b40d000110317a21651610300c0d510030b00036180140545010400d070103140a0480f8101c400d00c50322185550744412007182d00303c0c009402d2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 298238938 1250 298237688 298237697
    0x90606031b030a020d020705030a091509060302030601201c02070819140a060b0301180b070809190c030b09011518020d0e0313380c07180f1a10 63
    0x5125001703a04e00c05030081d01e1083c8010f560729440318002901c10030342c81e48081c21090382418814800c40e8024242c200b10b852904015845c2e8603107100503205060481009502010b0500d00225a00000102ca81541c2c1c2c5034245180d0342005004102d88410050043e1030f15584480c03070710700241000f0b1180a252ba40100c20305468428080c00d251f0412050f4401610a180c880c000c190562500784a01c528050031000b10600ca00041da0340c84040c040f0040c1220b00780310034040010500002400440385d450703d0101904130a5500d49000444440b09000684100c0d0200c40000e4598a051190070212811a100c10f00380078034101104450072070021000e40b1280c0c0a0101d510003100c6802072440d0000064003844d1114490410700e444002c0660007000701003030301082c85001002450102c07091400103102202d54400e2902a0b4005104d1280309100c1485401c2c400503410b003401c04210000d40c19404240902c442000300304058490240101002e500c20142036921464105003050f80d000e43ca090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 298240188 1250 298238938 298238947
    0x402031b070c1e03060b01050301060f080603010615120b040e06010506070c0810020c060f06130e0309100305040b070e090c0a0c020301060303112109010c0827090606031b030a02 78
    0x40414810040c0d400c04502248420b02130017046800c0c001d040112100380b906a09640c500400180b8003000315201130148164400451160784082d0000f030f029146c030307801a40310381000036002031540000314082c8481a00d0500443c105180600454154241050082441c0e900744030400940740d02c0001e040302d4913128420000340303491003480481c61050b03220341d0042c4c0721140f000f400342c10454000c02106440080004202c03260340c82c021150000781c00004000784414098a0b0306255100e618510b55100407849040507419525030009d80c4100d00c264030701c900355100c4410070340f4510018030070290f01c514100e0020303008d59034241c050007041340149000d2680000030b401084c01c5800320380040d40021141003480f04003500422000ca01e00c1d0000c4482c0c00107001d5161149013500403c02051304220107840d01c441800100c805603034402d0920075503418444003807401c060052504001e110b0058141d04009503582c980142940c4c46045145c540701d40c4601c120140c44490b50005149241c0c0035400e01 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 298241438 1250 298240188 298240199
    0x4020f1207140901090b03060a02091804230303070f0c0f0f030c05070b09013608060108011416032f0408060c040305030d180f200402031b070c 63
    0x428107004081d1104462850101c210a100c00ca65050b041083e200381002101d42480d1000242d40f6030081c00880700589030341220000603194140700a0345401040b8280030312050206150300c80c07104200c1c4000c0801071040000c02c664590200303c030004046924041548405c50003103440c448402c0c405c51661001c00c0780e43c1d540f01d0311382030300190070703800074411841420810004120304000f91801451050400303012000003021494400c90f0b00ca081015040c404840c21807a1410400c001018481350500c1c0c0c0d1900c01e07640c0d640e00d00f4403400307182350f0170404a000080b01075071015024905400300c0c5151988510025406414100000302806020b0142d081031210140d07450603a585000d90016034030351410603481d00e40305000d0004035034244104002c0000603c000b00319a104112604049503031041803c0d600c03071541d0f5810f00a054a50080150410880814011082064640b8024040d07002034003d1204034002200d000c10002c1500303480c0c0a55074800c00c0541802032103080c20003046512907 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 298242688 1250 298241438 298241443
    0x408040906080f0705031f0f0b030a08130b04030f06020a110f241006081306110405010f030905030901030f0f090f0308072303090a0c03050304050a05030f030304020f12 74
    0x90b4040816600007401c411281d000c00d03c2540700405048000f400300002d484078403004405119a4404140d07035911114a4283d42c0380c000d4210200001c09581c0c0381070b25801c0202c0300e40d1010080528541c0a41e0380803c00d91060010b0342e003a2a0416540e0218540717941d1004001e5011044174410f10264544405030280104505550940e6141c00382009a000140708805622074001d02074800b2001400c000c0c01c89603a074101c0701212014a40000517803200b681c219022514590050900703070038594121558400d21340100221070382a6141106040c10b040b08404035400d00344010042d410401c06000070b036200c2d41100b0a89444444005948508036211904071614400104e80151407941c415050540100c02254803615508106100700c04030b0700680001c08d65140d403069401d2011001c5224034000700030451403d076010240e0000c05407039003040c2d0307500e420510400c0d02c9400c2d844004240c0d41001315280b1051440c1e4802182180c59a42c02c03c06111901c00130150000e00c014000d44140008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 298243938 1250 298242688 298242701
    0x140f03131e0c2903060d0215040f060801091806110d14040302120c060a0c0e060c012a0c110402220501350406020c03040b04290a030504080409 63
    0x40c0000504043c82c01900b400c881c0440c1820440d40b40400c8001c00c1c0800f111000c40b83d01c198210b90001e031136540c43c400a516400302c202c048402c14004170f0042841009001401e0030b0f20419246c1c04940d81c1c1c1d440c0e1a0040d02c102c013201c0c0c2401d007000030244000980c0350300320196441600f0b1a040c28005003611280407286407034000c035401d0820340284014550180700b4220744141000000d03180c80304d2940b02507910080a00001c181c00d50b586040c0203124490325204418200007440c40781c2e19802d150103a806080c81131070103003042414503c0c10051a4940e902d10341081e00c26165806036030003c2e1144170091024800d0783d50065020000c50b100b50101e0a00690b1040b101000c0e082580c0c10400010800186801d0100040028050704000807490188404450a00740e201c04850745c3c0d64a0450040d020b10706149415102c0410042003150701c3d0f0700a8025205078041004c40e00b22044001a40e2008031020f041088034104452400c3c24407e07004254098094200d4a24242d0703107041000480e0030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 298245188 1250 298243938 298243943
    0xe151c020403020f0114030c03040317090c040b06091503060f0604080601080d03062114011d19032a020904030807180b0904021804090309030201140f03131e 69
    0x14000707000e00031481e244800c891050802c0c82e007031155180380542540b041c4005020002c1d2090080002001c00d80704d00342c10300d41e1a80141440d822424034000d10380e0b4401314080303103a2280b070804c2c21484881c1041c0068804100000b0101860100c40581e942c08582c005090150442c00c056509001d0b51658401007004107130b101c004045540c035250110742000e44130002c43d0105411f200301081404c8000c0c11544540089450900401e0014580000d14136590b400000325135013002c4003a800f41e8204813020001780c100e04203860100c0b1303400d00000c81014180038000c000c1040b00340030105c28403102e01000001da41060a0310300c50314440d000201550000c48048000480c040308000d130099010a0300104c0102c00d44031000fa09007040c05010050007080020303801240e0200c4c01680405180c007581d01c000030090003c10000c00582801040002c003400264080f410160744803900c4441c98040b2155011101d00503030840d12a1640d940c21a0711440302603800e00c032188041c01c0c500103050f2a01e03e8162 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 298246438 1250 298245188 298245191
    0x106051020070303140309010f0504050105010501020f06100e1308030405030d11180108071209060b01080f01060e060a17090607030b01030e030909130b0705090913030e151c 76
    0x1036010300d20324002004040c16000e80003402c041000030740105044d004203650444030307a129602c201050340105003031544070480c9820b140500c410b000040d031000741030701c030b00780c0c255041d1040200c501aa00d24042d5296907005500e80410001d084452221981001191104807410700c0c090302d4003029500207a0342a540c5420000308000184080d200300250744903000700c018180300d002d4104a030f05640c44803103d81400703c06000196164407030b82030f00c02801c410071010030440c0c1caa41400300041541d01e0105000c207018001040305010010b40d40ba04803029507540031071070722124040c46810740060b280407090002c004e684480100e801d40350907208407854801401e851503c584010103480344413084e5030502d85090542e2045a01c0481200d400744820b42e10308605461b044000c0b05280c10506000d40005120001c1c000790b10740c040c2c014100e8090440c2d402c8190b0320b4449007c050301c0d00182c1c00801060802640340c0e19800c00400f02d00b05600003a1000c1d060281e503040d000c001071038a008607001b80b03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 298247688 1250 298246438 298246457
    0x70b070b0f07030b152a0a0b1807090b10050301030c061b080d0e060c030709170c040903120609020f03010e100e0c04091b0c0f050307050304170606010c03020606040b010201060510 79
    0x701c0c81c180400c0004001e0308003a0306d500c607400c1019a105c4d0180100540f940d4407030400103c000d00c5100b241d24020344600103c80b40b41d65207071000d00c001c3c107005032600c2c461416035504001c3c0354414000c3d41d0603290058907017140940f4103c41a94203a0f100440f0a04006110040d00c0120744000094400c500c0d515001044d0450726039165030504500501400d0446414028040349550100244043d10702d10003642ca603141c0f4446240d403510720403190440d80070341442c00113400c1580c40140d040903406000ba0510240d80c4485200c0f05034000e803800c44615045c28801000741c04481b20900342c00c4802207281003403545d2210709110003036800316141c00102d03500280c20850807080c0c3c402d004c0b000c031841d40251209818008024900007002d400078010481c091001e206005040c404c23143d00c1076004045960303442d50b645440045d240c1850072181d050007080f000032000e50103003440e0003603036a01d680075040a03524841004000c04010340f4182c1191b583d800e0200d10381c0c03070304182e042c1e2000303c544079004034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 298248938 1250 298247688 298247707
    0x1b05010906021c2004090b0d0b04110306130206070314070b0405061b04050a03140709060807090e030a0c0b090a020324060109060801030803071707090602070b070b0f07030b15 77
    0x1130701e40c501034400a100e2084081104083c992043c0e03400c2c1c80607030b080820703030008410005010380e15a4a0140c02e80420324144000c22030400280088842e05900391040b5603a20000440d200d01c140d90083c1d00401d00308082e0000034494820341652140e003003042802e010003901c9080004400711001c8440340d000d80705216003c403104000418500c441d0703241514040c20715001c02d401c0c0207540b00c0204418041ca0029030b0a640a1041901130543d4040800119650b940f0715070f0342e101a4170a9650443ca080d228035814000401250302d569400c0d00c4400444505940f500d5211000030400e094034010202403600613503003070001c1c83c509160741d40c01070044012444d911103208d001420f00c4d8107008055404205540d0040649811260040003003600d039a11008282c410154600c11040b201b0f2351003042121030b642184c00780c0c0c1034400c2ca50846003215110110324480d482403c4000d0260040c4200148281e01d580c005542d016005150208045083c0310214100c142071a40c90a1840c00101d8903411 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 298250188 1250 298248938 298248941
    0xb0402010e0f06090d02030a021903022d010c02040f020f04091d0d050f071e05010f15120f020301060b04030b0703060b03061207030b01060c03030f0203071b05010906021c 75
    0xa0074282118503400d5000a4400502148244802d103800303240303610030720400e40d90300707000300402036070080e2a4440e500c6185900c0604003000e40801c030301c509802002c080e036284405105a0b1100040345862000c10103c00041d11102c11200c0100d80c8580c6030b071080240c4004034005011044070751814241c440b070604184e030003070b0742c40b45602c8034080d110301d4041345180200051010082e0483c2c100550380c1e0b5183c6006090610401c40080c010003c0700e8664503881100300c0e070700c0034414001c100821140300341070951801d548107051006040d0341c20400a01904070358401c920708440c4074009100101a10350b011a0958400b50311200904030041810020b1080e135550130ba6008881e4503080055a040200c1c11220303000c00740141f400740ca0b0428a4540341b00702002240007554000c00d403003119694030b50000b8400002d10800324002410003042d03018146a07402900e00400c1c0a8a0701c01e2691140c00d104900040c8091081c1e51664039080081c0c0459614401410f00504003595a000460240340440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 298251438 1250 298250188 298250207
    0x30a030b0102012a0503040323040504050906070806101205090102040f0605090306041e170d2d15180c030e150a020c071a090f0102060f070305180a0b040201 69
    0x1070440d01015044d01032904110001c074030610f4a0f04000c0d8803522207080031603000703145400c101c546404000803165024034003070191040381e000300d50902c699074894041c0ba4644005071591000300304210040784841c98481e00c008011301d10762800c44010700d40441628203a42d400e54281a0995001070140854601c0703915400142c625428041d00c4c1881035000709588400051029055003c1d02c0d4984c80c26908a1002ea61050f8000b4054030f8008141c240f00052940007210340300ca4586401c41e002c0b01c514100c01c41001c2e00c3c2e45080308280c0e41c000305022030081c000000800000c410074a90214140564411003141110507200000341d200c175100c03021f4110303030494036010103583c4196403100c01080d00c004076942c0030341500c50240e100c1c4c0a40e03010380d2503c861a0005540c004c56802030b185680a180090507828100701e8100c0191002e0308010390b1500c8051702c55402c401d2103034000039021070107500802d801c1600054242042140303d500c840c180006580203e030250b55040502041d980d1264408 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 298252688 1250 298251438 298251461
    0x2205060726071b0821030604020304020a030b0a0c030b030f0307080307020a1209230303090d020307050d0b04120302040b1204050a0c03120801090e070314070302120618031204060504020a08030a030b010201 90
    0x205c2c04220810790b030f24030300004120070b1180f40c00100050440d161182160300071b50713015001c00110700f8819030b0301000d08003030002600064500040c0c0c004910b400500b11040708505c00145103025100c3d2203489140e4001442402548510413228001515009030403842c0d514a554403460a42000029085003550b1707004400e100006604a900d265000300031220401012101840740c0c4209201080c10611240c0c00940e001043c085294180560070b00c98503c1640f10b1990f44246000800c1d0070780032401603001c2c8007400d8000703100819000e0007003a0340390740223801402160303030190319580e6581d140701d480d0300100c4200c0b031201000c42c0740301d402600d514050004218207011032000c01107104da0b01c812901c03001e00700f241b0482c2e50601c02d80c0240041c0014540203001110070f02c20204c2641e40e525800d9580c210113400c5034070b0380d40501340b0100c203907034101d0030341d141540c0755880b540c91b4030025000140060743d0000c01d811000500e50030030401401104080d49002c180c0b290410b0001e401c50310040b020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 298253938 1250 298252688 298252723
    0xb0108010e0f070315060306090e0604030c02011d0a091b0c02030d0507031403130209240f03010216050106080127080f07082205060726071b08 63
    0x18401a180240800d0740400c0d08907100c500c568035818104e002d01401d841400001044880200c1c0c070070783c560481400d40c0c21401007800703410310701c90030300c0d40c2e07000c04a40c040c3c0014180465903005610840301d0170742901401d0a07045e00900841e0001e26a0541e0342d218035032132662620340c80c4000c0006030701801440824140035203884400c0c0c010989580050056408000d00001d1000c101400760805c41800300c9803080e959201c1c5450001c85414200310312050f4032078007440e00081d0310450b07410101038200d102010144aa900100e003842412100351125542c1035400f40080391080c2d546480c91417480707000714000f1454608e040b04247c00c6442d800111a6044203006481d440c014088a412502c5940400340d50381c2d80344400c80c0940707107000e0352000401c0b5403400500707007110314901c40700131155880e2000c082520315650307020011280700e800001007002c00402c441d400542281c01c40564600c00d414821485e244a40d030b5402c000394130702130300708265980d40d0301e06000f983c1c410080c100c48040401003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 298255188 1250 298253938 298253941
    0x105060312090117130c170d0f03090609030e0909010b011d0409082113211206090e010501090b060403170405040e03030f06150d02090d05030403030f030b0108 70
    0x400d0311055001003490a03520002541180350f4411803400141c4c40e4800c02003c2c0d00c1c1021410b0200350b003401842680c02d41c0882801283c1070f8126043c80300070030178002c020500680045030a48803c0c0c440d80441c1c05041e622032260001c182c03180176082d420f600c0383d03542000565601080050b071071400790000e80e45a15180740310310241d812201d05072704050140c004800c10340d52403001070b014116480c0000d012810120346450781120100104c1038840d003d803503085403542c0364600c0d8103102c6010350380900f1000703e8203140440a003407101d126046080318a806401914400404030a4a01980c0013180090b0746000c60f2003208000c0c03190038050542101c0078420030b100385000a940d4001ca01020b82288c0b040700c8524060001d00b02124020140a0014401d000c81c1103402900d9400481d5101c0c2c00900300e50014426142c5861302c09014000821170600700101018054003c0d0450b400e2181c1001402200e840401c0041026000462207656880400c60600b24000c05560000e0040343c1032041200 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 298256438 1250 298255188 298255201
    0x70318080c010c0c0f0602030c151501080415020a0e03010f181707060c170601090302090c0c03070804080c100c0b040807050a0c03060606020f0609121303060c1701080105 75
    0x26800110910910f010004500c50342400300300c8100342e0b4824010300d0360001c00020b8040c0c000c405025112003007400d83c1c41280380c1c0c00e400107041504a41d0910960000c1c2d440031030647c09240603682040c0160941d10940c0c001010710802ca0b4400448280480c107035081e82241032170240940c0b04410303402e030b10a2041201c2000c4034034030008100c10007060208100c1c60001980c807100192981540c104005010208003064042c083c04603206017919250094030010310594015103600080740d034042d00a044986e101040d0340c000da0425501901c0300d001c00c100403400710b400c0c0400380014201c02c401801000f4044400c0222a6211800c40010321617090460800724040c10100d030340c441c0d003028215544190340d207405410203000f01002460101c41c0440403091100541c80b082c01d80701150212201000414141603a80404541c0c031102684003002d0303510310101d40005081028464003194000c82c1e1079944030700680740c0c03400d810000102143e11501100346c8000e0341a00401002008010070708159 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 298257688 1250 298256438 298256443
    0x10303030207050a0503130f08011b0f020a1a18060702030d0504030909020313060f29210606030c0a05010c06051b07111201060e3907031808 62
    0x5100140500d580800c2e040c043c40410b00c10510080c3d44281a66500c2a048003ca500701c2c041d4015020388515500000c18101d005104121200d0303007960564000c9950030301c084401d0412072840d941103008000010001070601000001000105000c4c080141740c1094000d0070b1060201840d00d81e680014144010203402000700c61134a28042c0001c50150303150b0030705580d00c500310b030701c46001c00d0301c00410807101d0880120081182446100c090110920b112100015070302c0150812100485030b07103441f1010400017040020303101d0060220756a150725140c01c0310851107801ca0b0a007403508284108540b5250a100704510340b001218000d01b158208800205612504200100501e5503030021a42030641d10259205211302005519648c0d0600e28120f8a11680b10304500e0044202500201c840941800764005968a00280380410354440641444807420281403220650358200c45c84110707044c0c014650109003c07a034200b9034440305441c0050040c420880550050011050203020700c3d50301 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 298258938 1250 298257688 298257691
    0x70b03220f03050703031815060803181909051969060f150c081c0507080f0103050618010e01050a14010e01030f0f391d 53
    0x10720f050b81e2185160320302980101448114030304e4030355484000c03204008410000500c581110312051024982d01c641e010740e28000c80c40e0450410a680e000c0140c90b0608002031142c2d4110204850a2581d5402d25001203c40988048030384a0468005052000c5075000d201159600380700510410703a03481281d064030743c000b01000710000d03848400c3e0045903140c0c00510b0645646d940c0c160018015140d010034400d030300841c551151a4107092000a15804c21042c0c130048070b41c488000549419a45411140c9114a650880d052103042c01041d50358101059814210401810b0014103414401c3c000f5040c82c030003c0001c1c035007104c080014800034902040140c1c006141e40704403006403806d030740141c0c094103002115000e00d42c6003608000c5c40c00600e4010804404100d01d4280d41031341c854018040b03600b003d01025101c41c100380c68600000306001c0c10020071b14007409a50f5074007200d006c040c0030b4000710f00f1081e1001e80f154075600f0700d82260072480000140901c050a584004480c034500c00702d10380 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 298260188 1250 298258938 298258943
    0x705030411190f0f0308040b07030c0606080304030212010e1b030a02180609010803040e22051902030c030d08010b09030f0d0c050c0402030c09041508070b03220f 71
    0x110109003000300007000303800c103204002c25610b0865409015180c54810034451000c5400c03043c440041c4056042406000b903a0b0040c0d181443d090808034410402d0b80a80300c04c4080014a503804000304002d4460700b0007610502015641e11403550040025980344031a080030300c0e03498100c09003101080028000489001103020344071541000000904103140100082c1d0032070000c850612540301d090000610501c022202c070364459884000301940e90242c1e0140362480d1019101280c3c0d0742c1807901c09142080031240701d01a43c06844d0703480724101184000b000f084900400b002c4000c620382408040015801a0002d103018215032800400c1c00c032040c421400b8002c00012446000d031028400e803404028584121032010310751110003001904170083c1a2528015000042554038141c02268001c000444010341044480c0040000900320ba054103d8000a042800103c40c0c7c4c0600c0403c00501c1c09265041e228503008201240070701d40e5030007280e00071011031801e50000b07100c06030b109051074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 298261438 1250 298260188 298260197
    0x52206050705190302030a0e060112060203061c0f050d050c0a030e0625050d020a110f01030b03011b030f05040201140a27031a060109050f01140a09081203070807 71
    0x40301e4000c107031a980719056401c0c5001800140340c00010b90541c00850280b4141481007000c030211801a6440300c01c280600100300e03858085100200b50250007864007e1002481da0280000358095403c0c18030f03a0310800c03128520741209050900a050040d075a10410340d0402910700300f0811a1262641c1d2075a400405124800150560684035407003034034141d00b4071034001018401c0c0140e01d2609a9480c0804540314800c40ca1050b44283c40461034001ca10762140c01e114041c0b486404100d02100340340002410036941e10764034112580d0034007501d1003a002c0d00d0401012059101c0c4010140c40445d607072000d40604101c05d1000503603000100012000c0d08031840d544505521000b00c0f401e6010b070381e0801c01641601d2502d5007a211102041048902c9a444402c500c071800a0708420700c24125440b5000c101d0407001006a03040c2124182c2c00b050052504040c000b07400c01220845401180e2003070000f4244080038080d9841c10030401c000760000c142041e08500d01043d00038000d1400802d15020803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 298262688 1250 298261438 298261441
    0x103020f0f0403061401090e0628050a0f0c0c110f13020304051b120d110709021804060b04150c080d14040c120b040f0804050603090a0605220605 64
    0x2290200d05689018503880c000581e6243d407410b2440c05002c036000600a101032940c00080c05518a10030f0405a8420b00050151552050382e08a04c5401c244102d4090f0100040402d030300c010b2a114092180b89201c1000640385040300e41c28007214881041081448064103c110114000c0702511104400071106100508120780201301ca01031200c08032180c960010050008000f400300303a030b1049002d007100780d1389840d5891042020340078a000080e54181c000c0003407250810f01c41c5e8806003c40904c0401c40380b44036583c0b00040100da020024400700144844a15510703454180100d90007070141c01142800c01d8104a030b22611014220784030070921102d182104c08000403002655a00c401110301040580b001809040030300100300c4e4200c988880d03d420114042c2d0115540c03a00058010000581c0355440303035598880c1d1294001d05a0f0400d50034400055a55947d60080d0710032640e070406001d11450515008007075401c003520b900f02c15440d18000c8211140c801961a4440350084000b00e0f59 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 298263938 1250 298262688 298262707
    0x40c060c0f0b090a0c060203030405061021081b010b0a090501150e010909140f0610020304090207051c051b010c0c0201050d060905070e030f010e03070b0a060b160501180809010302 79
    0x9254013054002c1c02040460b800192458001c000742d84142e000d1011b40b83d045c6d1312514070200007581c60140d9507410070703400649150000c038404030451440c801c1110a11300120286004502c10446600b0581691102949a154280030b8020001440041030901665044c0607141030855051a020010480c043d510700420b61b01c20107841c0d006008090080014110407c50100228421102c414038a02510040380d03660408513216608100399901070b604141c21700c81210003940c001072081c1c6440c0700390f882004654620301211a140585619a580c0e114400c8001121882901d1400c10103640b51020381504c01e5013004400c9092642407800390383c0c4503a0b040b0080028595600000d40701403a000400515a03040900b406000800304c088034041e08200c40001e099419441c13044125800520085000888a0413195048038090a01040c3c5607151000c0c81256005502c050300d80c007209001d00c02c140306080c4510300521069464200021040303445100c0d040c400c12030305a04040e03000035200da9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 298265188 1250 298263938 298263943
    0x1504030204050106030501060305091219030608030325030902030c0909100e0f0f0705030a1b03140a0308070e0f0625120923040903090503030a020105040c060c0f0b09 73
    0x5140d00420401095840b184c1c0100140024011000032a15000114800010002d00070340000003100f08a4a480c50111a0b000345042441d081424151200c10104a0203002d01c0914070903030840000407180340c01c810144018200c038045050500d03180c6a190030140c2c4000c10781c1b015214044d50640100d88640c00114a041ca1444100305402d2400e050544d0b2554085902c030908010b080855080003004104191a400c20b8440c00f54543d100c48130490005889031a201c1c2424452052a0344c8940d4079180c04500300600da880000e42d0300603d001c0c80416400c0064503401500ca40742080d5200020341c0418000c00302401428410800411003400c1c002d02100c0005805207003d0f183c031141182440c01c151070f8100c0094000102d0f68501d0b003ca1070b00e481802e824820b100800e5100001c41510382840001c00400f581601000f410b50f10104103510b0410061410410a500010300340c580380c03d00d8540215203400c0001004001c1c80401c0210b4841c145025600f900404110455243d001070302c0c4c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 298266438 1250 298265188 298265197
    0x1081b030c180d051c050f0d0c1404080102091504140f1c03020a0b090d08011503091707021302030105010509010305090f16091a0607140a150c0905030a03020c15 71
    0x950003c18801c0c2c02080002c08100940310f000c241403021131100c00480140c072203025000340c81040c81414054141d20788003603005007031443c02ca405c0c00e030b580034000451703042c02e40d2194011140030b031b400141e010300c1e82c00c0165107003807940f404034502c034149802c0550840300540400003da01c1054401250280c80d6620040c001180c1c92202950420080d6403034065202c0398400000c1d0b44d000100700000d1050240854003c100c510780b5036440e2381c581c1c203020400a00e4030540c00d0030410165103030342840000b00c0d891400d209586046c0700f41600d540d00c1d4410030020540380d00a02039240d005100422071079030000c1c180c900e40b44090901003002d0303403442d241500d80f4480c2c135507041841c801d40c0c6188440070104004601a0390710070038103001c0103625050380c468030410641a290070030010442c2e100400c00c0c03010921001c941c2c1d801a200000e10303503113404400c1452124107003880c5580d800c00303a1403c1d82003041c0000500c0c0c260060048000e19441c065242d27801441801d00030000a6420761018142d141100d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 298267688 1250 298266438 298266487
    0x606100e042415030b090103030903080c0307081206041b05030c07021302070b1905090d030911030d0201231504021303080d020403120203070b0109110d060305010b01081b030c 77
    0x196a00c2d603a03400030298243c881d03032080c008a4a081043d40704c40c20f04c0700005058035007645904c51030070701d541c0d55400607502101c0780b200c282c003007130044c0750016440500a201400c5d07880d01c1080a0b04011080008482040101c86021603514504c038040d04c1e0844141c942c070031610010252580c01d0740c0089854007a050300040c01ca1440068804200120400300034019480002940b007044110515501200c0080d1000300c072a511141301c0d500041c5c4203812040d1500d1050300380220480915010034070b00440030440202517512035101c882580c624042000c1c2c0040c1d44401c9140d00d003030800c5a00806d20100030094001d58000034030343d14404201c41914015644954115660100c50803030000940060104441e02c0a40015621000340700009403864280c208103008016460009050000e10b8003190282007a031313082c8902d480000e401e1050740c00842c000c1c00045000038080000604030000102681d9602501c0309501c030070316a0941c181c1c1c0c0c2c4845264800c0b039641040d00c612110603814140c50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 298268938 1250 298267688 298267751
    0x906040308070b060a0303050f13080f100e0c060301031704031a0f070905060a030c030e0703030507170309072327070503070c03030b120607050301080606100e04 71
    0x30030049040c00a00040f0700418040502e0344842040052802562001070300041c0144803600c1c4c1d0b030a03040002d1240c00e00542220742195a03440c00341d403c181c0003244a0240340c0001c1080300400f001d60081a05a00031400540540c242501c0050082d000c180070281c189201c200c00e02290000c0304088901a50b01b00c81c2c2c0e101c03544546009014490011903021240580d000b010642e454000d090300c03419200024003003424202055000c40040c2a01da4140701010f4407880303420b192050510440000d58083d0360349940d07030825414501e00317002172000002d0500c0d10070000c108542c5008130b0540142c441620318424032002c040265803011184805013548541c001d8050460104d03070850104415110410402259846941c00d980500044402e04045040000000e0000c1e01c02d500842c0302a070700614a21b540041c5122044c40d104040341d8074008154008018065100c0810060368060703001c032a03031603621110920081207a14401d480074019074503a0712812103204015a40f96207450075807413 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 298270188 1250 298268938 298268947
    0x303010f030507050306040c0303080a06050405070302090a0f03080301060c030e090114010f0201090206091c05060720031c0b01110d02030414090108191b1d0609091e030906 76
    0x8120320a40d905210440d10340c49440b100203100d0a01180261081e900101003042c1e5910b551001e07a40c141c40202445055940e0350404100395035580b04150044040d0703540182ca4020401c01d02c9442002c3da00007010320380460300704100081940741268151241441d120900c84040d140660310301c2021554194000c94810001c5409026034459401c042d0090740c03440002e507002c06d016400c031400208041d402c484200034091542c100040900058098036071501c200142c2c030b49a2a0030a1000d580c618009203c0c41e00c030100e042da0038a060151800801d028507d0209401c000c000c0c002540000c241545455140c0c2114a030b003ea801c02c807020007420b040c2e80c01e0301c011940007502c03035000307000350442c0151022845107182031101d04941640d280600415101c1c01c5481a45012039104408903500c0d900c008510f2001d00d52200310b4001400800c8403031071241550170f03d1200d46140288018044c0100100f00100d5640c0041c0d0042c2c036019080c2c0340e00340e640c0c2c260b4146040d4030074a40e14079002180000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 298271438 1250 298270188 298270199
    0x70e0a0e040803040b0106051306030209060f030a050609010503060906040f020f030d08090118020607171b010f061a1602060c012f0405030d050f0d061d07020c0a0e0901060305030301 80
    0x10000c504ca644510782c5018580c2e222403055400c0d000e0740032601001000b0030410302c04a03010342e009003403c142c02001507041550030810200158011030f42800c40c5500c1c0c5060040c181058040301d03014202c210003506481c5401620075541c1c0b080200054852a80304500700203644800d03050340e544000190035160303450311703000b000340c0700442c2510350200f950b00c1c04108480303c114082058034074690041000e440c2c00300b55100e0f0030100b1801d0007803c520803400c011078100600c0060034070f080e10f190345d000841d04400c8201190100c400329807145040c55107205451465441d91030407641c142c06058400c9a404502c0c1c00810381c03a00a40200c28199842c0c03001403000e54101845046101107450605400c0101c00e60b2204401e005030300c241d6400d0391091500546250052010301300311301d0900042c0b81042e82c04142c01042e03594680c01810803034903011141030841c00c0744010942c05201c07070000b080500c001c0d0300030405d402c441e4403d034070208400c0d41c041140e998083d0802c80045412030304890700c95840c3c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 298272688 1250 298271438 298271453
    0x110403030c120305070c15020f27010906050415090302090907090b1f0f0c0203030708070605100e151807260c040b0d0213141c020306070e0a0e04 64
    0x103503000c0c2d401c04041a100300c0340d0781c401c0c0181c61007140556180c0856090359035607107049054003040c00075103035020b0108140640348280078101a040e44c8107544c4152404950711614102c40ca400c06040001c0000d0901410342c00c00d0844041310390403800c8820324104110f048a0324103550b00000e600c50090018085010300000e02c40094034181e4404101844c403110800c2281b0104811003100c20440040540b0b285000e28080311181c0303000d0411100f00c808a50009007182d104000450b200c620105002042c880d00c2d2141070b50040c41c0b01c440d03140c443d0511000c010b408c140105014402207040060110540b03400c1c023524034201101c05011442d041414018002810311194200400c1529004041d109088409640a8101030400c1440c050400349000300640c086052400400c1e020449404000704500e007070030007045a0780362081c030000700b0010041c0034084900750744008400d03110900b01598001c1080754100d00c80d424410f410483d048040b40040007640d2150100c1d007015002c110511001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 298273938 1250 298272688 298272707
    0xb0d0b0a320d02091b070501021c0c0917010b1201060509130b040b060d02030f060603060702151918030f0f0503040f1b0b04080703020315061005030a11040303 70
    0x1406542410500002154840384880c40c1640840d2030b01c594005414005101c0c0e400c2018800641000c210000f0004003035400543c1c11503513a90b0000ea00c01000130440451030401006450130711203844c03002d00052400181d0f00420f08011180260340089100940c0411480c03034000c0c010049184402c542a4001c02e6144105d43c003441002d40021000c0b0b041c01c0001e8582540b056070300c12140c545440d58120204000d00440d04640540005000740e5005c0040740c2c4086140c00c02404140f03040400e15082850180500e0195030050102040c1c1781740c00c40c00b0b20f6100400b084040d0380d0340c00301c178042c1000e015800803820301982c441c115401490303808202602c2c8042680c807070782c1c0c0204608030111803a120131a03001c0c00d618044000c200c0000c8828000c480540004032207918100d8941852100643c49680b0002c0e50742d00c034410400440c101800070015000000341610101d180c0030010a0f0880318090392002007002c0000050206441940101c945c40c08524025407503d423a8900940007032039 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 298275188 1250 298273938 298273979
    0x7060306050909010203071209051f150806060102211306020a06050f0f010e061216030b060a0e01150909090b0708160e060c0307020d080301051201020c070b0d0b0a 72
    0x2c85100081403800140201da01450180d034402d40c41c03c4031b640c8102c0c024003d200c41256540101c1c4810b4102c0c1c4c004e9540c105d5800080600026030203106e05452030200b0003503000b881550405410002c20b83c0c3c01040e04041e0f00890140700e541d0040300115407025108884d2034844003060b082001c41d100e0b600141d08400c0f10b04c1000200b20795110050800410001201c0b10201c242ca150018420364041030140e54002401a01d802500650300443c6420a49606410201038541020400521010494440e0000e20580d080745020f41006001038102c0414000e020241c080c0144030213240c0c0c400d40e101001410380020401a04130bc0d840d190b05610001e42c6c281c00003c0c1c1d003a01040980d9401c0d84054141e6620342c42e00064062000c081c000c1c01e40044a01c24054001442440007607102c0e068440100c0c1c1c130a000041d07407981050100400c1c006041071600051784180908000b90034002403641c255002800c43c0b64440e60090040030140400c3c3e0407090700107625400010ba401d2850122030032485 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 298276438 1250 298275188 298275199
    0x705030a090b0403020a2102151305150702040e1002030411010e010318060c200706020f061e04020d060c0f021002090f0f1c0807050d0e030d031104080706030605 71
    0x40d514001e800b01405940400395111011100c104164440034247c140a45280745008081b0318482e00010a1740c049011400b07200340e000031302d03228131300c40030351801d40031b804111050030b541080c00c04001c03100d00030384d4402801a43d036000c00030700083d001c03c504402010030840c103541d0b074038280c45c080000310340c61132035907002c141c490f01c404210b580607002d10404202d4081052000d9540c54072410080c04074140e40c0c0041c4801e03004981c020103803a0f0b0704800c080c20704000a018007864050001d140c607241a425810580001040c0001182508089441c407210511100119266400001c180c044445402010a40380801580801c0d400600301d4188001c29020344000400c2c07010800140c0c46000c2082d64041c10300038483c082403400244403581c0c000083c2174406104001d5020382055170303607540c00303030341c294004903045040180c10003080701210054600030303c401c001900429030341e9500d18a200f09050701d8000317132280503010400b543c0081a0362400c031081d0550b600e2020b4000c08242c040c1301c1c003c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 298277688 1250 298276438 298276457
    0x209100312050c030d4704090f03031e06080606010206010801060b0a0815040203090313050a0e060105070311010c0918110405061e04171006140d170705030a 69
    0x300d0045050b80c03400600c503c0a50700c1c0200103004900200801d4003050449900f050070385101c0342c0d108a484600000c3c1050003400083e00840f040f003401003c00c05503210b503007040618400501901642c0c2566a4503050108101a9608104034060700d01a050035019252100000390f00d07000003455405245c1c2a02940c0301a40c9031070500d03080e58601c1c001c07000404020000c8891031032044401d907030b01c0140086c2452481e031403d0001801d1760310580300e000080d440440c05803584441141d4401c020a003c0361440305181c50b000051080700d80040000d4103015010512000340360081e00d0074081d10f02524020058814100700140100403039004a10000302c54100c035422103c40d510800c0c0c2c4484c08604c6160800d40380c50200003a03a48103444000221b40d440181d081c490903014054006012590401d0b1403911402c02601d1a0002d803480100c0c070542000d00401c01144040d1240041d010207444004440c5030760308207201240c50450451840b080001491003d000011011303104c13041c241c0d42c840004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 298278938 1250 298277688 298277723
    0x70210020c0a1a040509010603050f01080a050627072402010b03072d06030207030311090a0302090a09140609070e040803010504091112100609060303051207050702091003 75
    0x403074004a45498012030030781c00500a40c459a0600e518909002841c240352a49400201d42d0076182030b03018201003511a028080400f50b121503007805020841d0040a50501c01d480702562610f010701240d10100d8a410714504c822410180619040b007003c04032026607030b960f540081904042c040b9040441180d00c0022640e0744103024414100c81c00400400e0400d0405a505840b61070a04c0340320b95113140401d007000003450b10224840184019180103032504600e04010301070b60004c1854000c2007070b00300003040703080d507032100ca10090b6a0191080000c550390b0821081c001c054841010f411080c60040380080c1d1000040c01511401c650340c10f0b980410390310800e15004400545006001c0b01d0113000600c120705080d40001003550066002c210405804070100e10040e80c54070b08003d0340d40140d03580c940042081d0160070028000c0b0b490412003d4619100200340c1d0181185c0b202540300d00c3d1010810040c4108140e45d0131940081c144550b9040500451410080ca031004a0b001074508900700710 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 298280188 1250 298278938 298278943
    0x41404110612150d02090f01060905010809030a03110408010612060f050106080a020f0d06030b1e06010c14032a0c060913151502010608070902090d0305070c0b0304060207021002 78
    0x100801540340745906450b1843c404403050314110507a900612424510000340e070b500c0002c240181180c0785034041e65410040d0061034400503030030139410f120010381800042c000c0001125028003051400080d10340240c0c0d90000e0754800d9501445280d0f0034414007182c04001020000c00640c42180100001e02260704080c054034024420070300401c3d00c2200282c20608245c009005c803101c21484079141030300c018585411544650021360f0724a210608001800d401c10801422240e440318104030940303000d400003401c4e440469401865010f080d9a83c4103410400c005035907030a58201100b4010006420581c11038080001c04441c4511840700c4400e4281400421203422380b07000f0305070840c0441c0d0001544081c2002c03403610f50a5080c5090000352a900401c00400c0e0000d00f0390012400e9450711060900e090480e42103030403d1441001080d040d65681c400001d16036074541032064a5840905000810080c290300c94664203c0c00000c10081242c1680140030080c0b084540180b0b4485009003240d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 298281438 1250 298280188 298280197
    0x6100803040302060307090305060f06030606010309120c21020d0f09030c0608090a0c060513091e110d0f0f18031202090607060908030708010e04030c1509020414041106 74
    0x524642040000b880541480002180e0203d07007401e007129400c1e56580e80c640b80900803150039400001400c00c0c040f20386010301a00380c0105c0c003441c00b400110b07a152101c0640001d000d400d6004e011004e10010200a0003902018020343d030102058050703050440c001c0e4441c451466110002030410200031412405411601c040d00e4010340e00d01102410b201c410f07589800090010ba036244200c4103004005000043c0c1e020182000d982d540740c072084103017900308150946812400820b401e05444401000405c2c0c902e8035800031022000c1026114011a1011485000074205a06040140a6451003510f800401311740c444128100184482c08020200d00c607100240180041e95001d18000b004041d42c01802010781c005065034a0300c0d003295500c204440d02000c1c110360000d8007104110110790080300203130042c141e4180308005407074183d400a20046090740001c00d022080c20030a04c1020041c2e114800d07103980034000b0800880061201341c00c410b07080318126440400e00e080c125003130a014041d80c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 298282688 1250 298281438 298281449
    0x316080304050d030c150b0f030304081203180a03020f120f090d0213020a03051009091211070b0d02130b0a020a0204050910050c040f08010b01051603090305120c0610 73
    0x35800e0a040000f04542030301d10803015010002c0c80b074000d80100c0d20002d526241c00c103400c440050400c0d1024144501020071901c2c191081e08184030400c440b10703011800d401e0000303005c80d00940c0c036900d4a45a01300108003081da02a940708880150041603000503407150580140011124114900769007102948501002001103000502c03d001050404080c00c8942d184003c1264000e04549020001243c00c1280e1110010740c0ba001030003481c910710480f16001e0244071b181400180c100c2e84601481c82400d082c076030200000d44c41c10b0321407040700340070040c0544024801c0e983e450700195002c80107500045101a01c000c030164000614000703a1048400d80d46044d00a04555a966003c01008000050511419000d880f46050340c50f1480e2003414460070380d011000382c580e400e00c07e00110203101030f040381c1c1690703160840c02d80d2680c0e0031400f6520012415461250140300502d821101d0080e90340c4010400e125020750985030380c4a20004c3c3c00282c000e04111855603841070310741070714401144241c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 298283938 1250 298282688 298282693
    0x3b0f0c030709060c05121c0b030109020307030213090507060806040e060106020c010f03060f03140609030a1e1b0b0105010e030307020d030e01050f160c0b0c0705040c03111206031608 80
    0x10803c4034011441d1a80d2540264140e074641803140d080d0003400d9000ca0a40650072512075848100d00006101d400c191041c2030b4020042d00c4840d03800719503501c03801e01003c1d20950b003500c411300d81d0f4031194101581156104040c0c540d6590389a0003c0e000440c1980c2c0c0c1c92040e818a1061101c01400080440c100c580941c010401012a00d005540380c9610b40e0313180041503180c0401241ca00c105440700e0000310f00c50a11011030407088618107041ca54054080174440c0c0007001000c4140d603006955201801c0703c1117020007111500070040d205d00c003146a403905030841b82090b08041c01100401c5504132002130703d400d03c6400c40442010b4903440713080c038000d40c00403400c150680403e214001740ca1560906040083ca82800000042547d03089445070600f503001c11810b22041110700d9034100e00400f08c851016050000a45205443c1e0040e0300034240102e560381d505088140c0700e500009441a603212145551715070340c1d08041d05120084034078600138460b0340b88514151000b00b80e1030341150040401b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 298285188 1250 298283938 298283957
    0x120d090c1514090d1b06090f230a05030109030e030c0102030c1005090c1207090c09060c110418060504120e0307090b030c04050c030613020a05043b0f0c0307 69
    0x1c0c02e0125402588410350040315015035540018580c4085c2e1120901071401480d10514000c40180401100e0300503041c03030301c51104100322801a03103800014403410141410000c4c65608003264408555502041d85582461025410700d038204014601440c0c0960070b68045021010042e40d4912900000160540c008504401c030220103034082038024000c80b0a6503010311350b24000400707154482600b0310072500412000c101984062040c082c04601ca803c00c110701c0d503e04603011300880706810014181c4d604c40701003101140d565610607a000500449010080c500300c1c2810b00003460704403800c039591810780080040283c02848420f040c004010002e1044906226001c405070001114850b054440c40c804080d80b950786004031403003020400003094481c84d1242c00c000101c0707100480c04c09081d02c10070002c000c00c0d42c8502281d050301d4001e9840b9645c0060888a0f8080d080300960714500c0703003044043c0d05030307c4960140c0a8040e0709689039850f416201d82904581e684800e0310000041464081e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 298286438 1250 298285188 298285217
    0x11104051e040e0d030e01051303030c090b0408070807050a0b03040f060603052407112a030304060302072f010804060b09010e070f090305060106030e120d090c15 71
    0x81d103812a51a21194124014462000c142910307072203114a039080e00300428603010143c0c54443c50b010280306000074403450030040d5a078800c607049184094109074881c00d180080600400504c0001c0c0080c1310242c0d40d95513130ba1840f540300c4d17486018240886c05424030008013458204010015201c04070442072440c0c03170f03a42d07507003801c6121541c04590007030710340300000f02040040c8055101c07081d0720284a081e94022481040140380c1c002c002c1401d2284141c11600700e01c0c03001460410f070f00d09001ca4075484155115100002c00b58004285605110004004c43c4e01039140c1c000c6d00d1014400c140410400020889041c5c1c0071256001c083c00c0116040751b600090340c40740c118940c05c28000e62000034241c04140102c1d015201c00d030046080488441e0030300181d0f03603210b1124070381000103242c0411000d080d0368030103440d44e10604c44c42c030405445411055802d9811301261000140000150340c1e1012202007440150a0003d006d46e0180d1000c3d2000822a0603100d12070000c8031160703502c0c00680705c03c6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 298287688 1250 298286438 298286449
    0x409060b120c091903080d0507020d08040b060a03050703080d05070507030c2d05060601021b03100e0c0a0303170c09010c06110408030706050402040c050702090c09010210020d0c020d0201110405 85
    0xf04101e0b481080801d8180180e860142d815010b58004d90310740e070340c0e0a1400f0401081d11405031001c0119442641d1940d041c6520040c419001036000000b075074252210f500280c103500c0c1c1e940000e8040d004138000001003001d1355004111070302116005000c01c0d5511082501c0c9401140c5e0043d011600000c6014000740c203903840c00d00440224192348400307412042e2030b2111240c608604803450350056050103e15a010480051f19803880c1d8803140c0880490000700b42c480600040d41408103441e0307040050386402c11320854120200c0502003601260356806c00501202e00541100300d0741c0745144c04a440d10380181e044400c0a01d040c0c4402c210780c0c0c115681c01700280306881c08144407942c14080890b0f81c3d2001e0008004032030080801003141d0802d07004204c01ca480104045007071210400c44180162950501c203607014000c40f02c0982ca5441580c0140c2c02e18180c2d00c46100b2040c4006140810300076075522250b0310f0083c650848200b02c034044802c1e0308a40500e8010a2000c0c0b041c0802c00841c50030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 298288938 1250 298287688 298287697
    0x606030106051c03050309161707090c05040b031909051005100b0a0f020a060c0f0201140405070b030405030d0204092c1f14070e01120501050603010b0c030705070b0409060b120c 78
    0x10001c440403078005140042d04008c0d250020b03a08003200d402240700c0d03100104042e501902c6403e50803c0484c0080d10050079a00c03681c82908d05240c0084000b903c80c02e0008180040d01c1446501401240e0301072516035154218044c941151914000c049402e80c4880c0c1d100350280c42c0003114161030244044415200203095031005800c43c401d65841d00001143c07030141c4a401100ca48808c81018546d01e4040d007943c485025442c200500d240030080460300020360304007201c004a40c100c1d966101d13401c1103411441807913984003000d0700010f40010303144169400349100c0c0c0f44545500c034042c20b840903124038104000d034040d038159210030900c03102c41008030032000c2504038282e40020404c030031999a030f03000751342101d05101103000e2858004a5503007010f240b240300740c240c400070000c560421002910324001801280c0350312101040d080a2214200115154550041d04403680c0c80d503500d00100c016845401070303807803840c241200040e40f04108410b46100200c141841d208075a151007546605400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 298290188 1250 298288938 298288951
    0x10022109030a020a0e1006020111070f080f0304050d090e130201080c09030a06060618080303011a040e04061d031303290c03060f120a020f130e0606030106051c030503 73
    0x1942503440300507504c510204000b08202034900446250031004100380c070440390b00034415a41403d01c64134280508078200c41046520009194082a00e0304048041740100390881d10400000001d000900000040d100840c003c00e903603e10720720b40c840140f240190390543e8105002c00920002c1801980540c045aa00011340d079030072420204200c00003031a002461710282d64003951405c0c00c1c00a01d5010818424000c41090000a030030301c2e005c106541e80c4014881c003034039035010201513494006298100e500070280c80718011200d05082c106000107100300801580703440d820140d548000e03407011054403010700450800048c9507103185c271202d0307103800b0803c84a43c4184c1c1c0e288180240202444a00d40a88185500c00342c5030b113400c0c81404600c500d400c03038883c81082c1d031080c540c05c65403001498245081d41610b11100c1d010100740030500c00080003404510171810076961070201100003c0482c40350728103c00a00400b0f07a518148640080c840b84914040300f0700f03040030300c00310340240015034210f030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 298291438 1250 298290188 298290193
    0x3015100e24030d03050f010b04060503160c02040e061f0506182b030e0312090d020118080307020a0b0901080c1c09080304061515030b0109051c021002210903 69
    0x400a030000e0704190a0700f142c0c0000c00d54480c02e001240c0031181150740500140b0145600e02810301d4805030a90000401c1c003050606804e8903000c0c4c541c402d00d903011556a001d4410301444c658900c0203071b103440080321038041a11010008408040200c10801c045840240999103058600044440160b0100300c001703420107030665114140d111089900c54100c0b24020f40d08480b00c1032864020820048083d0040c4250702c401040c110400098040780c2d04070000702c4002c0201100c6100617500221904080c2d032904020780e00018181c4004001172010300e2007242e040f031010341c031006441d850340206402c0d6400100c802e00025101c00c81304006000310803020030030303600bd603c5c240f0302c000558008031421100e41c5004030a00040001c0d50044c005484501c610055800b410316a640407626100755020781059103c030100c00450f4040c1420b403014200c042c0c0b0f00c2c1e00401000c4a440c0701c46614400817401901e03a250742c101254400301e505040c02028001c40107010402e203100f140300d9000a1807503903050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 298292688 1250 298291438 298291501
    0x1150f0513031a0903070203070501200a06020a09050a0e0705090a080a03090323060718091b0e1005030105040b060d050411030c0109030305093015100e 67
    0x1072400c05180c07402944180d4054031101d50021243c3e20021018003c40000d61040c4007140050741d010640030145d0b507080c40c03c840203c00d80d0340001c001c201d1001e0301501d00d00505a003882480500e400514440c01c00391110201c1564a800b48413614046100d0000c403140ba080100b490144590000d0400c0c03400100216411038480c80c0c00307070a2482c400300840101d20000300420800c501000003914001401e81c1409071b0300e0b041c81d04036450b100c005007070404001445090500001c4003884c00c5000d08032400c000c010340c008503001f1090321040803408070089406410182c035140340103c1c5050304081659581d42c11f5900c3c20052001070445895651351081040c00310010304041407140a200d0b50260136499810654101890706081c07101904504000c0072040a0010a400004032075000105854064044261164050399501c2e59192030055184c05441d521000e04002411107131031440020794841520307440700b01c0351181111710800540c1c01d640c00000b100d000c4002c00f0911001404140311051 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 298293938 1250 298292688 298292707
    0x5030d05060a1a040311060403021c080d0f051807081e0102070f12032007080c010603020405070207150806091303031410030c0b0a0c0209040606030f1a07030501150f05 74
    0x21035211264030f90501c4041401c01c1030001001c0700302d65041007960744a19060a64001c00c0381c3d20f501d440e1100f045055030140300c0c2040512812217200e88840d9100b003002c04000c0a80034040d04050f102c3c40352001c020410980d440720045810001c071000e0f04001e105d43c03504a01001c420440c601e40241065500740880f001050340900074651300b5100c7e0b0000c04210720100c0002c0d044880c15281e003005903880c140ad1800c1c0214000c11070b41d03850342011440e0344410080c1801400342c45103820094010741040c0c1803100e03e82e000501d040c20744100080801d03188410714012540c1c40d030112110b91384405070f03201082103035642500050806000c1c0ca004110000c42d02c00d00c5400c200155403074034900d0b201000030024800040d6503800030788101800185400c070320305801001c0790b6045a001e4840c1041001040800c40c00381e100174021640161001e40b03010040c104001103440d00000c81440390051000110107a202c1d00c226410385d0783d41541000c240c110f900d012909103c0212001d8140907017004840103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 298295188 1250 298293938 298293959
    0x50a020f041a0d02030c03061e1c02040e070906030215030603060118140108071a070503041e0e010306020a091401120f02040801090f140a03120507030f1d060106090305030d05060a 79
    0x1103240d000784a00c3c0d03a8180302e0188207116014154903c0c2d0900500b940c81c0c840d6841011012b9140e40c002100039411000380001402000720400704080f603c1a0840019070314181d811042c1240e0007268840d6003d103011194401c2440100e60095040d04040d0060141000062000c1800f0443e1540011500719240e1413882d1240207810000480d48101001c000b00c007006041c100f02d04818414003804e00c2c82e56955550380c0c0c043c6000d180c020790144010410801c0d00340c00c08000a2000030030740c40b4a0350396030400c10001e51060018000003116504003007401d5000b000307128222a01a95801001d800c12040d20300240f10303540c22942d42c10740800c000030b4114400d0080000075402a08107411040f83ca2500d2510075181c00c9502c034080d0000d80820300403e401c82d0320310100002c440c0d800701d895035501000314020100c10540012641c909055820024901c00c0c0800b4044c1c0544221002030362140c0090300d0340c0c0106c0c84010403a03882001507001c14016500950f8102c80003038140802a1349803a01600e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 298296438 1250 298295188 298295191
    0x1051608030c0705150405161a0a0e0303030f011e231c030e0910050112151a03150102061b07020d0f2f01090905280c03050a020f041a0d0203 62
    0x1809000300010303c800d101f414043c00591510b0590000b011505d0100700285130303c481400041041c20100300341c1d00c103601444501c000c0722001000e982c3c1c3c0e8a89008864000902801103100b0002c540905030460082e03280813400343c1d8a0081d5290010b10002c13205134008902200840d04a0b40d80d480c0000d43d01500003020f00c51328401e4940b40c042d5080401413110104006044003003450303402c881013150b643c22551905000241800c0458030000c112040516100380780e1049101d9042244415a04082080614020481503020403100380030780004a0766040d00796051405115a0450380d01031461810040c202d00f807003e801d18201e0303201900c2d5503500b0301d074540050300d411a02c90345140d010702a6848800c4149814011502c1d03040b41500001e1083c1910f020702041180d5420103c1ca03100d4083c0300e90701d00412060100500503401c040400007610004806801007410000490f501c81c00500039282c0030049003403064145480d0028851541e403881c0d580b1140394000700080080040180000c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 298297688 1250 298296438 298296463
    0x405180f1b03030403021807050f0d020901110c0604050d0c05040608030a09060804030f081e150102010c030501030f022b111206060a0605030612161401051608030c0705 74
    0x41008a00600c1c04000704125182103921940007000b0a1005a0b1081c1c0c0501a644803026005140e40c4c0e00e04040e201c40c4500340e48009031200219150f00e03501441c0d00200440030080c0d80710744a1304030703160440740c1d04e8030204c2442d031b0700103410b12092180303081c0719007040b81081c051120301c1c0703e0650319408903040315107503045003856410009000e80341c11b4000712014000d20040c82d01c0110b03441c1030b40b001800700c06101078010810100c103000c07480800101c8410405000c500d410f221250918031421151000000174560265007003290740e031b56441c064800c00381201e0308002ca01100b55034540c00c0010052024000300d480e01400c0c160040c12505020740586c00303501c5140d800c1601071021040024a40c00483c3c080d0041c0c2c450000c00910352590740c1ba2100326101820200d07100d07211000001c0446905041c43d408500c07600c4e050740d610030342c00c00c0c802044134034074802c00303201652600045410b88100290685138015a141003400a200d080003141d11014030040303503090044075507642d4100300100c40e15 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 298298938 1250 298297688 298297693
    0x1050d15030503040303090b1e0f041e080f1f090204060b0d050f0c0403050c0f03071706220c060e010210061203090501110c0f0a090203040305040f0501020d0e0405180f 74
    0x780b003050703004099a00940230301c0070a075040c0103804910074116100340101011002d404038440c400c070010170003607030040c03d0034002807030205402d01c28409049842c1c0c49900030764452021000c0500e000800e159182c01c41003540050310300b4030183c20b00e016000c1d800f004c03604195180380c00141694598050309c0216031100b004a01c50900020740160554090000c80b1240810003081000030f8000079440c0c0041401d4032244030740007803913000909002440c1d026261130005070300304091440c0003042483c811000d05908059640047c10310400b2900092401410709940b45000d100140c050070b03050b0640c020520447e607488a03c0003101060b80c2c0d8652000312008454003181e800c154010301c401000d06400e1800e4001d00300d1440d00160345403c280002070140c85a40c80e201f10a88400ca001c402070440524250350728101407400500a43c4984142544645414000704043d0305c0444c1c079041154070b5986000c0f40c1d03d07142e41084000d0402405004628146a4005000740c170244086001003100902 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 298300188 1250 298298938 298298947
    0x120406020703050f01050f040b0612030a030b130e0a02060d1107030f030c08060a0b07080919170703020a06030525031e0509070b2208010c0e12070501050d15030503 72
    0xc003d85031065800c0f00b04180c2e414007042002c91000131150039801600b005541d585900c0d10408030761005002100000b0b203010014040c95801e070160480741020000703890580b40d24203660501d43c02c840c520030b158822500b04004c0c01025187c204058400c035a0f202800080a2581c10041c800c140c0c084001180031034002c0c00c0c010b20740c0d82c040c8241c1e0079002309401c050105142541c00a02607200c5070140703050a84d804100c42c000d0106400a81d604904060922040349080418251051416102d11540c43d01c02c2109001c3d003e0000c55204200ea46c00340000c500241001b80c15406084010020507031000744c2c1c04103111108601d0403556088802d52030009140c2e400345080c2c1205010408514412405d03c010311008240005440c0d04692010480c00d44079610801078191100500440905008200c18080395044040d8426003001150b5156124219032580910132148110004031025802c100380c10005940110020104062410303000540340c1040c00030a01400c1d0a90800d542d40e601c04034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 298301438 1250 298300188 298300193
    0xa0e0f0303220e0103030f0906030e07090c020708120c01180b0408030a140a0f0b150414061201080304210203030702010822150b06040b0406140f0417010515010207060e03120406020703 81
    0x89030b0360241007d441c0600c2030bc8140c005032a030340c5007144142050940da80034060112482401604050300011080d26030116034001c3e001d080b60031840040c0c4180d403815072100c0700401c182e10810b85180e400007000c6c0c03107a42c45496440c1c031900001d101d00303142901c580c00340299290103100700d40301d01c0c01e101c80010101c2c00c00c00b0f400220b0b091082c1d420b006041030340030b5094962a540940707040707501a41511340c43e1104900032802a004040c0124024050b01001145180c4084094015110300070602e0b08000300c6408001a100104000690540c10402040001d0751007001941d6100780000400401e0a0302040641c2e00607404040a44000d054000c1002d1000d207103020300d5600c82b03400c5801c241001c0c01c148103c0507910a51080800780714914040480201c0050b080da00e080c42001c2e4003a8030303960785111050001103596420481e0b5482e000008551104031004814540c1c0c040c0d00401d001d9003840c900703540110034103541d1503041c45130001d4080c54080c17803070040c0043c2800741c4c0580156807552 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 298302688 1250 298301438 298301447
    0x216140114150a09020c03040e0c07110d110f011709030a02060906060a15110a08040e06090f01060e04020904060801140106090308090f040b1002030a0e0f0303220e0103030f 76
    0x203820342e040e21807210440315540d0395982c1c4040a0301c545103001662058030034907a9145100da40c0c080c0309403209510800c8043d543c020058034040c0d005044c1040c0048048040100d4554a0200140a101e8540000140c0e04203441d0346141c00b00181000354003030401800d00741c82c18070100c030302001c264400200d90005a80c14025581c01944c0c0314003c3c40c407403c0110000d1886a524050540070110010100c1006d44c41520002c5a04090320143d503206c0001e4200150340e0390082c0201d681ea07503044408075080e0305007085240c0c800d00c1980c100c011642d00f0500225081c10401c02c44c0c80d4069001d01c02d1440c243d9a611a1a000b0841c290000806200094070003a00e03200c144c0c441c1080c0520a0810404100e04001320340b1540d20445281300e5a1001b24002030007441642c1c002038100e06c416020019241d00040106840c95045d210500709082ca042004020440114031507016041400101e0f4072030f002c002180250344115400340c00e030948a8500164400c0b003680140c0000708800764004481d03400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 298303938 1250 298302688 298302691
    0x60a151106180705040e060a02070203070e011e052d06041a09010206130f0209040804120c06091203020a0b07050c100b040b0402090d0312060b0a0206100503010c02100216140114 78
    0xa17101880403446020150340c0b9408003e00d041402c680000b200b204555040c40390202810a0f6690106996158605807880c0002c0e494001a00b11210398049103501c0c1881d0005107201c8103c0070300d00441507041d03010301c8508210100b0b5402080074040407c0c2d40e00e00240c0d10003141082c8030103035110311011000900c3c2520251207d0382e244118401480480d1180d100c1d200466015540300230180c4440c5030045e09446251710841980041407000410081c031050440c3c101d9a0980e643c2030000c0c1c41d1407105400072180c10300240035030310200c4000f001861104000b54400314a081550800702c42c404400d0500172100c0101030071554548100b0024500b078840c40c801840300341c804604201511021940c80301c0c01080203400d000522554240640310307508844040c081c0d13541890b0301e5000700b08c000303540c4502c182d03400400e04074010740218090805100d00011100380c0c0e0b009151045000001400079441502040c1406180f0349400c0c0104d18512040c10781c0810487c00014909106801c0e88080d007030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 298305188 1250 298303938 298303949
    0x60b27030d033c0902310e0d02071701020c01090804090c080c09120a020a08010c08090a05120703020f03030106080403030b0a05010503070f020a0605090604140105060a1511061807 79
    0x4560f690504200b030340d00345040014140c00000030300440702d800064a81810a03800c0d0119620325412141c2d1690200d0120300003185480c414804154003281c00c03a11000048214001039000d200204002c2030601e4101d0700c3c5014503400180350a1842c0000e90a59540e08015104418001410480c01d904c44c8110b242d4894039181a0203242880f11184e003480c0701c0c00b0314041c072440940142c403005041c1480b4946030158010040988a69100040717030290078402d201c24041072203e00010761166000c41d46d540120750140c05005060a01174500c6296001144260214420107414440196040006501a10054460741e10b80c2c6070510300203040c0c4206164844c0605201c290400141c5d8000090769000916801c1c402c00e14901c2c500104e00c1c00949581c083d081c2d509200a220f00b601011803128003843c0100102c96440b032980c0441c03030a0f100c05407100c80c0c000031032005c204020300c000b0119203103004061a02c40124160701800c1440d1803001d50310000041c3c00b2071270f160329108041010a00500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 298306438 1250 298305188 298305251
    0x13020a020607030c050d0c05131401030b040207020f04110d020a03050105090901090b010e0a0f0204030f0302061f06080402010309141c1b06020304050307020303031501080a060b27030d03 82
    0x1c000300c0000e000d4006c0d5920460100d0b21502001a0140581d045d1500c42c081a420350340e045658081008007c0c580300132981c00f00f0301c0c260680300c240c2440d008903800b551700a044d01110045000c1440010203d20807012141e0388180000010300c15940003c2c40d90900e547d4001c1401d50400f010082c1108000d850000c00303a2401c2e4112000943d4140d1490448041c1c0900348000d603101148030b800b50000c03034440383c074861000801004001400c000b0203440d50280e42100c0060380d800741682e0010450304801405522220000c001d00f900c0b401d60b20b580240b040c500411282e40d1a5100040c9041c02000d4081c0c40c0c0129540084400b4401c041600040c064a408015124094050b8201030800d01d0003504e460303000000030b002d01c0410400c03100d4960340035084035503903c1e00c0441008420440d00c80c190001e0008030100f8803002540c042d00f0140c0701d20352911441c02e00c0052007905c00b072101b4403062608120410615505660a0105000b28002034501007599415002c0e900461035200d00c100d040a07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 298307688 1250 298306438 298306451
    0x528030b091312031808130905091c14120636040c03020a06090f08030a0e010c210905030f06130305070f02060a09170105062d13020a02060703 63
    0x80158000d0000b8194104150b08522250810101c1c05404100f00c10f0710a5161441e00c40200500da1008010304d0034180040d050380340d26209480c0503140305982010441c0d00403c03102d685410701c4900d110701d9803c1e6003440c90710070b000b601c0d06e0100c0790088408500441448030400000d810700803001089100b08000c14041440711a9000000141882c002e00036202d1260000e0708104641c4842d20295800500106031540eaa4030010314000250192a0769070344a03120005d800b00001058400c610b07410b0b00c50800520012004480301b030440641513a000354099041203003203010442c501031925069541c0111103007000c05261500d51101802101503000c502040039140300700801d0001a85e0616249a44001905108001c2220f9020203580050006042007005810407a03a1080b60108c0500054014140d810507080765412501240c0080400e910300040c100e00e8080e900c19140801d1141e0302c00511500400d0500c241305000007180c65000030001d64454041245030740c0400c0c54178050190 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 298308938 1250 298307688 298307701
    0xf0d020316030210020403060219091406160b04060e010e03070b061210020a0f110f0c12150103201c290a0c030b0612160528030b09 58
    0x4078400c0e440310903001c0c85810040d4080602c00c0c0210140c488004806540303480e10707801c0c02c000a6010110059200001e6055503001d1800f425180b812250f00c0400c0b00120902e8009120855002d1044040805403020380c420006500b03a60b003e020324001c2c100050401207690030b090031030b02004c0400e444d642c0140b01c850009200b500520f07900000a4994180c2840e03c041c00078038042c4440c20369255a03001180d130140796035021152824114642c0d0f2881e8840f8503a00010b84c44620300c840860f1781743c2203240612424140140d00c08031350740d228004c44602184070f04030584c01174020307001110200300300d600481e10742d048800344d001b02442c1103c010b00701000310080c10040b00c020780c0000385101d0800141c100304690000781c00003c0c0d042621940500d260880d80640241880806030003c00d03c0d1041d01d1103642031a01c2641c41c0742c0760040b810401d5031280780d2020400944c0701c0141c42001410001e00704500c44202d03201e81d50010140715a80c00c407403042c1c40502600c0c0742602a6018409441c2000311 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 298310188 1250 298308938 298308943
    0x14010510091e0e0118030e01020c09010e0609150a030f1406060a06081e010b0a0f03060b0a11070f0f18050f0a020702030c060a05040f09060b0f030703020403150203010501020f0d02 79
    0x14820780c0c81c800000c900f1582c0b45454050045c14402d489800c0506000b0400e0540299900326800800d90903101480e20850400034405030038080d012904d11008002211030600d0560940c2040d030601b032040410421b030740001c4205070b09410442d80d13082c0b034800800c00c001c0c8a910301c0e284d289880001d03003800d190520104650506520414080040e908003250759580c282c01520891048448101803641c4c4a5104a025610841410001450610001c0b400078030900c1f4104c25a040111f165140c5041141c08980990310b03003140c0c04040c02038080c005051a181036100c00101041c404a01d451031401007081090160b41e021001f072a4100030070040c845181c2c20115034007444d09140182c940c162800400d02c1d1800001c00c01e500700000241010310240c200000c1c20131505421103c0c42c0c69511240541c1c00d0f2990b6200306040310301c007441074915100364040515400030041c9001400c06640780c40e4540078050b101000c084403a1b0010052229503410f10281d604014400020440240c413400d000f507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 298311438 1250 298310188 298310231
    0x21605120d08040321050105100e1509030f0607020a0320030a050d0e07090b030705150a14130f030c080a2301200c19030206070305060105071401051009 67
    0x1041101070030006082501401200328417010b10090100c0081d42c070071425000700b00a0007a01d2140c0700c130b000094116403003002420300500010307142c4983c40e203032182c00d4001900501c0c1075a81c18020208d290100c0041000760740c2c030922841d4010f0484201d03e05014241c000d15030300c03000c4004440d00007031765205000421170707172600c40c00e20705540c0c0d41e1300c01d105030001082a0114a00c8600481070000340501e0940c1046401600840540d551103554100b008489003030300d42180880a0b050004d054030501410781034000b440307580300143c503001030000d103625804102e800544501120700410f105116542a07010007070004480245107240107500d4942c045000c0d6515074a21000c483d0107038205032029005400010784500e41075042090070a410348141d00000c505090607c1001d842d40c85114402510803c03203034050b000303050aa02d402030f0850241038000c04403414483c040046100288802d542c00080080d207000001d000c2c105000300c0d051418140c1c1c452a10203040648c00c0d00d00a85041400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 298312688 1250 298311438 298311463
    0xa0902280501180308030403080601030513020108010e10080d0f02011a010206060d15110309150705030c030919050f0d05030618060a0308040f0608060108071209020111030a02160512 80
    0x2640c42d100f01c2100341c0303a604107500000c04440f030100a1004050700b040d0203e00452007600c00780710304d540d120705202d00215000c0d40039001030300c40d10040240362500c52040c0c1d005600030703c03201d41e060384139030041e0320345109424440d00040c1448102001d1550a1042d8142e00c5a01040c2c2021040c260700000d64440010740254400e6039010064000c02c450807807600210200c3c4030007800458908150408650006c03035200c0c0380341c003d1b0107070f13600401c210302d1040c1d21440898442904680300c064558210b0b4200410f08000c51103a084d44060074072203070f0489003120784641d00800c03c1108aa4203a824604880048001e1150900c00d0091a81d55000c0d11000c080c0300ca40d6003034580d0344034070003d031403640300703510142859030005000b041080d440f515041c280ea60503110142252552801140c010804480302c0c0d00095080c090703010190181e4000e2a400c5005151001e0105910920319041d0781c0101c05000160b4003071000304685901d0013600c4001032200b10350315140c140c110500280c5034180d84105 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 298313938 1250 298312688 298312697
    0x11060606162307180b0303030103020604121b0e0613060f090e0309090c04031407050a050d02040222090c0e0306071407140106051810030b0a02090402030a0902280501 73
    0x22807210820340b140c08082003100d1003200d031030540d104031410fa01001d843c0307440510f0381001055001c0e410000201c90480703601900580c505480d00e80400c000c0d481c44041201d07204150301c020506560143e5840300604010094140b03d81801401c2010a204c4030540300a41c0e420404100f140d801c48a0b000c9048950081e8085000440d912009081d8070549000e00d5010401700244007015482a01030b1098a02c61808100528050651541d5440c1d82d40304031a130016154009205904050b11861602440a03001505008400c180749030460051b0301d8800740100d41d158100312401c0140151040001c5c54207104000b00001c0e40480d444280041201092280c4c40039214400e00350901111003140c0c000c05190755500314410b03100c0c0a03022030704c1020703c294001000c0500c1d0351413400690303026640c3d400f18a500140b941c1c0d6440082035001b4460a00a58203200280c00ca49032070005610441108100141c0c0000074810004001480714080300700b01c4c60007401c6011044200d10041c15120f003400d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 298315188 1250 298313938 298313963
    0x70c06020a0903021c03081b09010f120207061b050f0f09120d05120f01060f0f0311120f0106030b0307170a0f0809010f020c0609010806040204090c1106060616 70
    0x41c152003440b81544000e400c00b182030400c5080800c0c00c65070040c8540320ba6038215190700d0351481206409800070101901c48800c2114076141d60003031241030300f0b1014a083c50303851001800c03201030403a003049405440c425128064289000001410001c95550340d0a01e2400d10b440c00f070703d0341481d0064041c01c0303801041c005060555507803001459000035601c207088811030040040010b1485c2c100400110101c0300322004144203250b5084050305a0351300f07603a801030b01c141c0f40700100c0d1b41c200d80d00c07112024581e44030740c82120810600c005040a01460302101880e043c8401c0c1c4212414050b0b02c070004052610420103065079020606000b101c0d040b642d600c011080d651003450802403806401820010303c83c02080810201002602e40d400c0b09072509081085025030590701c42c0071410810351f11250400400d1419805402c1d0720340c0000c0e01800050411b9203c1040104440101c050f20001c0b40880600040c01442085999413026040d1070050800f0404a505499096078140c010304201d440301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 298316438 1250 298315188 298315207
    0xc0305030c0f0304031206050f090f190204080304080709060b0306130f0c030b01020d0e132c0708071d010e0a022110090203010323071e09050f070c0602 67
    0x1078641c51280b206000e9a01e042034030703004d403200d05c0c1d081c1d601403901e0421000044030300e0600034103002240080c00000301559041d980340700200c0c00901d03a4461010015074608070021601c098005001d101d0025070b0b9450070010070625003d05640420200c0341082010320480041f20107903500f004054400070500188881102d0144c00c410300d640154518001c10040042c3c0e0540250525030001e80944400010751441140c09101700c04107a500602e891141c5528239246074049513003003107118000302c90f03c19234815402d0001c0d8098040840e56000c10b40034028120701707001980042c80400510b0702042c071008910104008148074045c0e545180b040040c0000c0c1c101e404941c1070200f07408004100d000803111074088581d080d2841103000180302070200b400e00d92482168140c035048403d4004081003000c1004143d564191030038070340d0142d00d8000a100c054103142103905100e0059010b1460b003040d00355021200000d1a04000081741c0041c0f040f81c45c1c000c0280700c0c4554200802598840f00d22 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 298317688 1250 298316438 298316461
    0x1a0301150c02063f060306041e050303010906060e2704020406091b03050105010311030f070504050a08010b01030f0c05090d020f1c051c090b090a0314060915070c030503 74
    0x2425001c8846030071000380c690740b03d0380c08403211560708610f0300d0304c10110400311151030080c0d04036038203901613100d81b0108012030700e2140c111020300300c1c0a122401c030316056610780e820340d00700b81d10001030f007526018103004003600001c41c1d0080706130603075041d1405005002c81240604c100d0003001000185100420103648407608901e0140080d04800d101d80c80207107000e00c00d41482d1191580000c3e00e0400082540c0d0312038018a04071005204000703017035448207411043d41000181c0000c0a0000c10400000c058030f80105000041c4005070002a480794913000240640b015030041034205031400030035400c000d812409407800c0100681c0c2c0301c682501a88003290034800040460b039400380c0000d1420366083d90750410358941600c2402924a11220200c8000d441540b40f41d400000c600401c405004a0240301c02905181800a020072003040e07a0b920762460340400030075208010340159041003840039041040e1304007a4a080010300706031030450030050601c0c5090a00504001002010460700d2584 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 298318938 1250 298317688 298317697
    0x1603050412050c010f03050709261e0607090605190c05010f0905070504020705030a11032502090702061009110c0f0604031d0a0302010c15090c1a0301150c0206 70
    0x146184003540ca0050b0030002d40d10b0322190348090000700c5040d91040c02c18400c0c0600d03401f503907154550f98071981c1001c0010700c0c481d40603083c02060050f400c0060520140800c00d6001c1030741468200b4500400180d240760819000804038018040a110200541d95000e400c841c0928142412800140010340e002c88100d01200c1d0007a103950f0030580521020180395114030003961052048408055644041c030060303000d4440051b1040d0004c0c09901c00d401d000e000b10748802d28007181503c3ca001802c00c01d250300c0c02c1001140310300c0514902000c03821410b0811400f0b4004040c0d00081055140041c6103026000040c05030600242e00c5403d1892400c0d882015a030303012074039005a401128400301e02e1561000121410740000e80e41c08a400020b90b4104036000442402803e420303505401d5400644609039814400c0b03d800f44040d104400b4001c2600c10030300740a209030b080c101c02500d44105a40100d00110030421610400c01c01040051004680e0600704070300c900700104400740c9400042c08070b008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 298320188 1250 298318938 298318949
    0xe15011e031407050a021614010c020a090509060402040605220b030a050106140307060f27050607150e010605011704020d0507140a09090302060f09030d0e1501080c0616030504 77
    0x400b1414400c01a070481c0c0a00381090555080320324050404d01200c0801110f88500c440c401286c50141009510881c4404413090000d011412440d685045410132180101c500c0c1944d50068018441146018007810000340b03800c0707aa50407507046424280007409440d0400c3c042c0c03d0394a265045003a00c0911090b01c1d165000b5008008040d69030200c3c2d0702480b08020000e00c01e002d124404101c030342c090a6071001d10840d0b5a580c0d40e6064220320b208003005207051a1030460b88000000041d40ea4841009005540c8142075116034418440b001c00c054030480c07440003174148d0600100384011b0342d0207411550b486032801d041300381d6510f990020460754101c1001c080c000d40200600417460040840c100240e402c403c0d201d2100343d580d2002b0083c00c8030010304005006070410008109060200c1e0122900072403050162841c0c0b10144080d242162401d040d00c2c8810740104c50a4070030840324104407801415101c1c003a110b14803200002941c0e0b4460401600e0410359413040d150181841030050700c0103000f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 298321438 1250 298320188 298320221
    0x5091207030804020a06110d08060f10030e0c010801051e040b0a0806100806041109090c031911101707021018050d030c1b050114010f0e15011e03 64
    0x301542801485800c1c220380c1a4014203405600080b0213104680c80d006910b41500a05032002442d0360480e0161070140c102c95018444c21441c41c0503542e45024840152100d0701c00240701c06084c00e086050400f0300090b141400328030001001a6181c00351100e0400c480c469580032518136190025005081c2481201e80100031001c000c2440d9800080c9540034422968070241c0d03d65545402e03c0e950f80d800c0b500244a01c01502600da400d08184242c070343c0095100d0305603110382d1070445c0400c2c90041c4516000781c401c1d00c0120400c0a00c4410b130300319000401c00769503610010f08809006004080030409940003442c801c000160070b2842801041c020203c825001d000c1c440d8402041ca2000580c190103607941c3c010112a0b01c83e00e4024030984010701c1c1144c941d1070302c6c800d0500104400303050302c60054a05540b5058008a45030591050038082c2510403003034001e903400d00100340c1380760368018201c10b900c1c10081289441d0760b030007548c9459550300001800c01000b4403040c4c11009802095030381070159 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 298322688 1250 298321438 298321447
    0x703170a0227360f04031707050a08040201020f0a060f0c090503030a1b0605010602060403080a020a080402090601170903040812030408160c03020409050d0206100e01030f03020c0306090a03031803080604050912 92
    0x44400c404d001c3d0049020b0380d00c461440070510f014500703010041c1d4000c000b0030810800003c686000d90030f039030350190050050703641008440c1456801e0218111045520741c0e51200010224500ca1040c83d003403020070300d8049103e906040100b6501c1c41341482000600c41d01e03516001c0058a0500daa015107135001c80b040c0709559503000013944d40e44055030100c3c00300c1e00800c001004074400e842aa040c01d4510390303a00d0880d4540e038090018502024040360304000800448002c61000c480120b401107107510000c42d5264604130400b8241040c403460792482a03410403c1c030020440c0542035403001040003095032504203032460620006641ea60000f074005040c0003594040c004081001500150f154080e0780844d900c001d000c44411499000701a04564214018404100360500c160380461003401140d591451040000307240420440b00d00c0d8556005821407803c041d03060140203642410301d10f500540b40e00a42d800340020700300400003406150340e04c00090340000100010132aa0f9a0701d410340d9500c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 298323938 1250 298322688 298322701
    0x2090d1506030204050c0f0d0c111506100206040506011401020106050a03030e04110306030703150603241104060503180c040c030207060b090601050f0703170a022736 73
    0x240c00d480c0b009922440c506000a01d480c0c0c081c0c01182d40d8040d10035446450700742d0028041c0000c003003400e4008100070700c41d01c18080c5010b04001040c001c41410070850403901d408030420083e00420000e4000310b4015405001c009100010f04605466030fa5282c08108002400100d0041c00180e02c0316621941c0c50200000b81504558030403215801910103000c0301a001a60b081075101c140d80c2c42e60143d110000c10001314a0f2071031110055401550089010f40c0d40c1c3d12821200c43e61441c0411011002110b00c050501492041c4000c54030b00412090511f881c0c107c0283c2513000c000c000b010203601c011421088200107002117101100024010850401c010354020001d40140e50111201860100c04104514064104d40d2246e08147e50b1240313880b0080c442c0502a8105072021003c0c0308492240e44403103010441581e01c108005400162160103100c030720407014540c039200d07c51701c07090751843e809151549062101c880d1038a825103c1005500c1c00c0300c0210036881c0741c05030f5040c200c1100b400745 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 298325188 1250 298323938 298323941
    0x5030906040f0e130213020a05040b030412080a050403020d0c02010203190e030d02210f07050d03050604051e0106050c030913020406030b1017042109060f021f02090d15 74
    0x80d40c3c0c45510b442c1955440a0354003084040c049400f0750b000b414840c81d003480c1c0c0c3c0f580d0000c1070042d117140f415505007036884a841904d42c00543c0c00b01c070a800140070400c1c1085e40701900f10ba208914100911040c181500c029444000c0d014450080143c44114001564005c0086580100200d6403402034484085030060454210a400610074001c100740101c0035840002c800751140c103911820380c28803001010001850340715072000c3c43c005000780840004208240503040c50081d8503280800d941c48d01d603042004031003004203000319041441c0010301306481c83c06241415150103043c056954600030144510310301420f24801d5010700341d842c1e0f68542d602e0903000b0f0401c03508035440520807404d88004024075291940680400110f00b1480c60250060000c5150307045400340800f1045050b0204810b54440f0b48006604040781000104221140d48038a0200e003842151000d01401d140d041c9500f00c005c1102040c02c02002c0d00401d00e000745035603c20008501a80c4140b000c10800002c070300250 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 298326438 1250 298325188 298325219
    0x50a0216061b02030703050d050403030902030a030e0411030c030714040f08150f0106081906151e0518120c060c06040c0506030c04030609110604180e0102090612040503090604 77
    0x1212080700c0282c40700c142d4000410360b00b00c0355042e01c0c2c9509080c008640383e4000c03c0000c00560415842d24401409070700c040c410086114000e0f6620102c0c403164000348415142e4a1008645203a000c04c100107042c1e01c85015aa0031050604d4a001d000039100c0f0000014042c6400040ac00c2c1042c0030f0000e010b00c4000360580c507200301d140c00486940e554407409803603142c00f44035040200307840e04006002842e080070340843c0486262800036030300d0f4550112100c03c52150403804042021203010701c404151000503041c0d03c00103483c003189825400c560003012444440d1545d030241c0c003003000001d82c1000910103040590f8018000c01c0d00d074000a11074030750740c100940301907440c60070b248008221401c2020449101d040140e075414502071440d90741400802c103105056034051000040c078030b4643d541c10001d10042907403d1002c034081e60800e00c501c046512a41180020341e10410481100c0d0704d44600780d4184c2000890000d00c169182c1c18410304510800080c03943c032800008000c0b5180164030481c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 298327688 1250 298326438 298326461
    0x706052a0a02101a12120a030b0f03010b0a17010905012a140316020f010603030201020c07052215080f01151502070e06010e1c0512030f0a050a021606 66
    0x1902c100e81491999021500300c010f07948500080c014406501e4202108250204040c02c001c440601b00c14118402543c1c12462090000948858100d4041d240c00d64507880305a00880c000c02c042c0c0030000000c2c0300c10406228002e26000c0645094080780820b500c5000c0702c0c1c0c2c010000f840407044e000f0010000f24042d514840e90b0045101c20b240039540310300600e000031a81440340070700e1521800280030012820000400c118400d0f070202e016494420b01171500250703c02d400145c1c5680350801800c2c140034682e00b040e4080c151070341c04245114010b8045160306040030300001044010808d170303120310400355081002180300c0c40c03002040600c015840754545101c00008003c3e484d40700d10103045140801481f00c1d00590103a10b044c001050480300a036048001414030380724801400c80801c1c42c030010003e080b80c070681381c85102e8043c40030500030702c0b60421852041d5855490141c824108802018217000d80392039136200091150f1100b41e0440e5000d000c005a080d01110304d51a05402030010003409 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 298328938 1250 298327688 298327693
    0xc040608060702071806080d090306110a02030702040b011812050c040204031505090c1324050d06020d09021201020901030e0105131113020705070f0b07080706052a0a02 74
    0x403065000300d10280034080b2076010f414141e25101c0368018098000b05030035802c6903a8403000501c04e00401c14410f00607101e403121046ca44c40c43c00c1034022104202031416003010704001d00540940c1c044110b8520315030403038000415031384020049031398800028201070900703440080494058016450b99200303034824021100454070250a1005030f0045202c0200341c4500b8072040c82c442c81c0b050304170381c0c0c2c0014400c084480f42414600020540f0b00c00e0000303c005540d0fa44e113601c0004d46a5103841c0002080c07403000b641201c1c5000c02117407015140700300237001154085101d42e05000d40c0c1d00300d1512070340c000340800032400044100500035403003402440e02003450655805040381d4180202c51240c0c036611000200043d40da00d40c0c411140c204180c66510a00308104058000d5091000e0b0040a0084c00101109818002031000c60348550b000686491001c0c011000000d03031030012074103842e6111002064580b80d000c484034007110b51003a110a0000c64a0404884092920282c00402d901c0c2c0d08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 298330188 1250 298328938 298328951
    0x20c0613090e0f0c0f0d0602030a0f0c032a05040522021b0c03070e0a090204021b0a0c0806270a15020c010b01090f0909020312030a050117011b030b0f040501080c04 72
    0x30006804030185e1070070340200c072000f0450082801a8051a4403c40072100800c07142400ca180d80101c030b0088040c0c901080ea594004908080321940b803003220a1039100843c1e0f104440075025049008510030305200d95181c080003032560440f600500b00075403081ca0f042d5150030541d40c00a28002da0369510f10040c1c03081d044c07403031214600040c0c490229003500c81d601126807038000c000301c050301c003020b02640c0054082104c40c0e07400b19850b4a80076a03946a00181c643c070000e500d0011040c0302c1e0382d480454582d00c100c09001c044544c5a01c5e07081c0740142e400c0b07a6070402416480300c0e41003106001004d4513100300d0f01510250b2043c65001030044200510080000804440c01501d04035003601440840342c100c080d043c48040000c1e440840e0040c0002e00720fa401004031032034081168030031116981d501e5110720040007424104420039a138114554001c1c44188250300005051700c0203034288404143e191610340c0e445844204400d441780002070b10500140d038440713440c40e03944c3e440c43d004a4040d500c4d140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 298331438 1250 298330188 298330213
    0x115050909010203070c02010e180103080306180103051002031308070c060806030118080f1e090916020303070c02061608130603110304030309080f07210906020c0613090e0f 76
    0x4204c91140c4120303103030f0180d1001d054004580101a40801c90341084d04000ca0140b280690396004e80250310411003070b0703a2440d01d030050107034100381200301d007840d0582540140005107011405083d113481d0700b100141c8036922107902010f40b00182e20098140b500020320b02d42400301e00c0c0c5070766080c1c5501b92504d616580f500020701d4200c880070706680c5c48007500d00e204100026804030090110030046040e0904010849003001a4102c032130000c021080d00001340601d90341080e600c2c25911000344811130b440d20900141c0652a8840108030300300b0080c03d04490800c55a0382c205850408400d404c0f418030300103842c901024954820000c20700c90b0050010b00050b0b1500c00e02a049554070380d0a00b0303a055403166941035000d4081070744116510b200c28448807a0042c0701c04042c0542a01501281c48e030a2589048020000507540d540003c2141e103050620103141c0002e13071184400c5040e01c14954524510010150100c25034114205080c100f29241d85040c0303000841940140c0e5034003e40b0050285907 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 298332688 1250 298331438 298331441
    0x6040b0906060f01080901020903030316080a050f010b030405010e160e131208070e030d0e01031409120703110f06071413050f1c05030a030f091104020a0c05011505090901 75
    0x80360415801a0044114140f81d441214103580240925001504101122000031700350f8000701c641c0714044400e0f0780c0d040041a0310607121500301321031003420003050820302c80e0816000014000d00c0b8400800101140422500358000881da100150584d50b041c0c4000e11502c1070303d200ca129005c003050401001c07070403101c000509100e80e964000b00c00501c4200401003940c00500c0107103490140200510740c1d40c4103072400c2c0141043c1006030380d2582c000614200002d01201d401d020044400e40c4102d003009403550002030000300c0c031401503d03012384402040c6412218a080c5503d1642c40d805000c10480c3c9001000070030a00805107511507142d10100000c03000018010000740d03031140392002404009500303010203414010680039010b840290b050390004d20002c00c141c0c10441e5a944001246200300361706208074035000c0e100c1078042c005c014903511041000c2001118080c4626400900748050600031044a5406a40301c0b00030710020601c80e0815800740706900c222070103160800002030079060107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 298333938 1250 298332688 298332691
    0x605090d03060b03132303120f040302150c09120a1103030a0e04090c1203081005030f0a060c030605030610030201080618070c0305040b040810060b0f070f0807080a0206040b0906 78
    0x2290f01aa0841c0d4560b844038604d070140840c142d540003443c1101401c0d20104d03000c00020b14806000442d6220101e040c0c141042600520001c0001c0b004014000003d501113400810b00045551601c05611500c0c028180c7d4496131900d181d01c100c0000d0110700801e0081840d60b02103020f180d6120390f400100040c50340740d10540900302c00241001e100c0001600d070540c40300719010f00507280d04508603154201c0e10401c0c3c86a80c416008a03100f50200300002d0510420503001c0d11081d00580651260071144940d10303103913040c008058944401010820038460340c030030700c010900103003220014201110f07081000703a030b5400283c1c009101a0001801400c184144404c0d03160345013014a0f1135510711170101d60310148102c084082041c20030000440954120140018000c0c1d007015115828034056002c0840e01d03154800aa940b90a0000015200b40c00054401113904140e0741301109405280000750340c4a1502d0081c00c40030007183c618041d55001074080d11442c400d00108405c1c1c0c0741c40c002c0541d02d440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 298335188 1250 298333938 298333949
    0x8030703050f301506040f032d0b0f060402030402090403030f0902091e09070f0501050d150e04151406190302090f06100512040f0f020307030605090d0306 68
    0x3040200c0d0002c2402c070091140740c58860301c00802c824400006541e001c0075402481d0001400418440ca80702e1141c1a81d10300360b0226040c620b002c0c50f00d0000fa140e9045d034800649504103207004042c48040904115005a6590041c904419554034105003254402d44040e084d68090301c002564a013014422039000356002032078a00607650742d68084018120003400d01d24442c0d1031f45038410068440103081d90007494031001d0801c0c10140350165182c0c0d2031006000801d103a00810041105020b00c003031036000e480003841c2107942e6480c2d0305500341c0609807090f0744c842110707031245001911881a0030700a000714452245e124120055914000644040c80c071024440c1e848080403074454a4000c1e1844100000f07401a400c0790b580da40c00042200b50102ca20034426903481c800c1005918040701d03068103450040c00c0480c02d10203101304d03c40c19010b000300002c00c07c034070201003282441316001d10940e1169008081340d4080c1e1700d81c585140985019211000035201308000800c402d4040d01881040c2c82c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 298336438 1250 298335188 298335197
    0x30403020a0f020310150920030a05071404030309060f030209100509011407050a060506090412050a030627060f0b07080304080910020d260f0a150303030603020a08030703 75
    0x21151100c42404100042c22a4940300c1d070200070750003403d103015204004e402d0005150807203140242c108188c400b944105d26004030010840709000918401780ea07040141c0040004160703988800c1a115810020f81030f0140200101e400020150b01008020a541840d5140c511103074031441c055040c0c3c020580101c1d03001d240040485c0000d4440d0300035080e0540145064440c1d2034554945001603801035005880a1704181e0201050001034010a500094281e4069456181c2500c50030b091261401d055000c1000008804000c58883d41090001e8802d00c01e040d6000c028181000f084510861440440c040c2800e4000941124280c0441e04039001c06604600e09040d60303039110210f900c020000c40d510346041c025200562504000c1103581c07005900104000d600308503010f03101c07a2103007500e80e08080c442c1403140001a04210801c0c6c0207040200b60210341e407200404d800c0600b900e10902c00400d4640c003800418550f01d50012001c0300d00070341d041c104064580407155128410b04a001c0c012a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 298337688 1250 298336438 298336453
    0x1c080112060506010210060801062108040e13080a020a0203070906141302040306051609120819020c042309030a020a0f050f060a0501030b0601020606010f2d170c03040302 75
    0x58140c2c1040c0d41c0441c051054401205002c0b200c44225190390b0401c5065072340d102c2c1d06202016809601c044c00484d02c4d0711080403580c4a82e2007a10300c0c8a1405580e19a041c5034002c034840d00e50003503410320780c3d0340c0c403603d00d43d10b910750300c0c0c0001e68411000c03000b644603104464000900481500c1030794141d51000420050059600003404440c2554442440115074204000004078886119250081c02d00c2a4000e85d0f41c80402e0300107200d1001c0d0303044441900072000015001903103030070403246c1510200641000102e60b920087c3e00b8031103d10b5074503801c64103001401203110092440b00035844850516681b55441b2101d5641d903e00454540e0320250748141c091f5004181920400d011f800d00c02c1085428542003940030905000c02175411450554482e130060080080b4442c0881d4442428030003085145401000200019070a540710010b01414124280342004d0942e59407240d8842640751503040309403058010102d10721000d4900c410305158001c01d400c0402542140e000356015401807102 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 298338938 1250 298337688 298337693
    0x6090f070207231203033106050a0f0c09080d020105010e04020d080c07080c100c0b0a0203100509010e0a0b031f050712050901141b04030b0c07050f1c080112 69
    0x4207405a18840c0c5580465003a01da15955100091100d0403510300911b88a060083d00d00e0180d15280103800d03401040050003110107200344500702c4006400a4000c955900c980c40360000804003018010955400c1551200c081c80d0031081d03460071038501004407000441620b030304074200c510070f00030034000020780310104001d0f18008112401c020f004514991900c440f8004a5180201030f901201c0c0fa030700180e20400003490b02102c11010011705041101550005555207140c00300000d0035207200c02c0d0301101107211507900940300006400043e080d840340703586032048507000100840c1d4800c00b10f42400215803030780c1000714402015201018289107000c0018403080c029041c0141264100a2040d41e0340480060b94000c0c107028516600c000106840c80c0000d4104a4800601c4c401c02e074040f031060042880500c2007281c0450b90010b40341206d680321071100101c14402c5107006025031243d29440c81c401d03500840c00805095003501d240d8101060f00c00183c0717500d4030174440c292120000303c200703a02 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 298340188 1250 298338938 298338959
    0x250b090a050d020102010e0f06190c08070810080a060207060f0605090a050705250203100204060c0f060902030313140103091101050703020124030501060f030c0303050c07050603010e06090f070207 86
    0x482c80d1050002090100104c5500d40c03406d014001d121000d6071028042c000000500310402d0b288e40e04040c418000009201c0d805403c106011340b07524100413604000500c1e909449060340b0141070924140c0c0e00070381603410491701941010400765449031410101241241c1036104200490300041c010260341e554518441c0000e0a000344803809020f810012011215908401a80c1c50116166810000040c1d4014540f400ca06030598040c850301c100310600c4810b80000300303008119400000707284810010301d80700d000b8091000e002501880003044010040055002841c2510b05034140d6000070400d0ba00114180c1c0d200b0f2202401a580301c1034614025441000101030a50081c0000300d2181c0d00708503100c0910380c403514240701001c2c2c091028404c203c400e000d0369000740151704802e00c1c00784c00e5448030351480c2c80070702c40101842000521290540b1040c05035100510000340101d45a603560390f0303d40c5103484200c0d400e80c807640b50b48001034141d041c01d078005801401c503070780202815410b000c0f0526 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 298341438 1250 298340188 298340209
    0x15132402190f0c170c24070f060c020c18011508041e0b0a06050d08031f09020703020102040906051e0907050705030c07090e0303010b0d0b040b03250b090a05 69
    0x2912529151810000f103240c0036040c1e0001d020803003c0700a52101c441410b400c10310014400d42c0318013440040d00c0324811140424010624807074030b2a40d44c46609103070007001c03201c10365001803900341000e4800e020150003081e4941540f909603507a4021491030801d0410300c1e00d0074018008900e84880000c030506121301e10443d8001c1c415201202c00281c100d84462103840101c000319402c01500c030801030010100c1c0613420080506540041c03d47d681e95403446801d000040c82c1020060741840e01000030128550300070300600704000110364842150800030702075030250058003001400c01c54002000d0805074050800d10701148040302d003540e1b211003000980c840103002401004401d00042c000b085d418002000c9104e001001003040b01c2c03620094000340c40100858804503003040c4010004402001c0849002442d4041e00040d90001000050028031041d001180c26108180d50340101c0d000c4022180f51800007102100145942c074081ea00c04d07071084010a50b0070008881e010451800d1100011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 298342688 1250 298341438 298341443
    0x1202060c0a05031506030f0a060f050a05091e09060708010f26030408150a0b061603050304020a121a0a05070507060f1103040f060e0102091e1513240219 67
    0x1008052590009200c0b5001038551f0b0540c02000301c02c3c462403184a01c125002801005480141d0300c2c6460001542e1101d42e01c1200d019000c400001170b00210384144d102c00441c0900300240c41814100344040e81c8940c05c50710200460f81c0f00b070021407281041c80084086800d400801c1e101c0c40428001d00344039045c0d2500d138102510040c040842c07100010301024007010071100450f20b40c2d241540011043e45c54013003c0c0e5001c0c1800b00826034590001e030990111982c1c15007401b5030b40e5103c510115181c203225601c034641000501202c182041408190204260000168003030551101c00d0b040c1c04941701a6440030114200f0000d01c40040d07500e0b04000a40c9010f41400580c007001c000351450700368007c80c1c00b1509000b01104c40c40c1040800c2c4695509603110b20021410310050002041c106c1d01e9420f1511050740c91703d010341c2c3e40c0e40c5d00d40c100c9000180041c0c0c0b00c552121002c602220a08955014242e80e1501d05028900d0059640e1040015050fa43d8014030600040803561401540d594106 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 298343938 1250 298342688 298342711
    0x7030e03181011100b04060e010302060405012106061110060b0910030f11040812040513180f03050a1103160627030c021c020a0b0c0c0301060905041202060c0a0503 72
    0x41c607a103140a03c404000901101c401180b401741c02c00401080714040d030000407800c00d041005001580712013054a09903282824035960f104850a42c5015413a0b00e07002c5c0304849401c0410204050b84e1040f130001c3c000081d10304070340355501c03145421015500c541c007600d05401ea0030721540d2602e280940c182401c403440d9050018808a2030100030080d03410001034034128a000103010810324004200f105035660a1402c824205414000091040784040a1701b0031901d440e403076000c4450071001c10512240d5889128141d0401c240d05e800f07042900605100700102e85050300c2400303100301c048100c95403000d820f004400358852035a80c4200600148602452a031501d0f101c840d50031040321101c400850180d10b80784941484d510411003c0380c050b0900140241c80c201d15403006868654860056420000c54240ca031604c0c844000d1a001049840c16419801d240000802401d9540107500660140c025154030550300302040e81d403400141c4481000900c204012a8140d02c074034050b6803c103100716017 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 298345188 1250 298343938 298343957
    0x9060111010e0c1807020a060b0a0b0a0903050c0d050c09040f1203060807150c0b150a14030606041512020109030206040305010f0605032404080f040b0307030e031810 73
    0x109084601414400c2c006500c0f05048148620300900058004526148411241c2c030706514006e4845810484c000c00154407481601540d99070004264060f1540d088004d407113181000f001030149101d07100030755803802440f24aa03030341e04101c50068802c80d0028000c0004590410a10506000080007612000321451440d40000e50340001d00d6100d50040d600440c2050400a07043d00780b01c0c160784010600407a0031445440c807600702c80729507800e1f50040e00c003140d169200d000458688003501c000581c85180031070003080d8031000b01940f1480c80d00507001c940c0141d541c0c506100c205c0c1c07883e0516143d5505106003c200d941c006019000030144185016241e071656907000ca18107402581048a142e51110540041d5030f100d841071100a0204400400314040e029201d810041041c02c506031030150300344001000d00000c8400c4034044400212080d54885e90b5101080d0203400584141d40000e0070844c014070b14800010544404c0201000600020782d121000c000032028903000c0b0b181440406d50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 298346438 1250 298345188 298345217
    0x110d1407060f2405041506030c030608010e0312010503060105011e0309050a0605010303170415020c190809011b111012150612020705060a050912030703021e07020d02090601 76
    0x110641c20b155100708200f41c1e02d0700c940c80035010f941500b00c4c40c0141d00d010740343c889034515002e106040b40c18238180015511452041240903200c0b642054080b503091600443c087c83e0000b0050100b01e040c400e01c600943d0721358080584464080c421180000d40c10b5100c401d14288800d1064ad406082d42400154420700796289070400f02d50b0b2030280d501070303650705c0100306050304040d0345641062003d0b00c001681c90107aa5141713220000c0740c0b00f24103199012444900d691340802801c41c05900703034080d001e8010500d242908503544003041c002d00044e04a0000c6114140070b100d0742d6404c1d544400300068a50241c8244024801445880707800c014400d1462014480d06200790301082c0004681584414200000500f0f2001c0c905036011031030348104007003030110300c1c040742c0a500007009040c0460075441700c11a041c45c141428840381516080042800f40081e00b42d0f0082c01005c100c850045c01842d1400ba06074814024420042c1d002014001204c00520b00018555071200050400c11404541d64 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 298347688 1250 298346438 298346441
    0x40e0615120c09040627151a03070e1f1202040302040516020c0d030207030b060a0302061b0705040905061906090f0204080f06090d080606070b1303110d1407060f 71
    0x2682c15004901d00022015900d040c207000d1213000e020000340004a04107058018910b50007004801e10405590320340c5119555424042000109604420b05840314a044074201d03040d8820f48284011595034555a09282051154100800c00d8501954815030401405603030b1410200542440103508000c007000503231b25442620f000340512001100c0c1c3d1890104083c1c50442000c1415110700c401041e0074000a50020f41c0700141c0c0d07484410980d85440340707000314001c2c000d5070704002d42c040740104d0802c1c018030091010541c07044840c0308032409a590394051008448040d203001e880c81c1c0080c00056070841c00da10317264800501c0180009002c1d5036500c05d40040311944245c1010301c0307800203020032808234100403d40300d041070040a84540d003413002c0510340c1c030b20914034080e003800704113030005045aa401042d90b80054111000720001e18040e40100c080c00560407084011502001080300b07110f00010f04515a00125120544244020701c641c035101c0e000000219607954a170100d19200d107815 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 298348938 1250 298347688 298347691
    0x105060406050d03110c040e0a030e01090b041a04030b0403081e06011d0d0c17010f11090d0807050a03030c1b11240408010b132007030c0212031905040e061512 70
    0x604040d01d4252702c0da181c0248803c02c01e07407101d410000780401c01c0c489000e0500c204c90032512003020450391441a40d80394140c0b80566800641240d9254080100307240c2c001d400d580c0700d0a882c1c03608005803035103540500003501040e08c015001480542d140100c0415101100810240042101601a41a0ba1511a4401190012907401300d141c0790400c000c130300034007034450003e044080600001c15205042070503406101290307445001805e6101c014040345008450746a5041400c0d25501358050501801400540403204009205049030b60039070301d480f40300e1014095000f005404941500d00802c035004000349000a15002d40c41c190318480324038400148010440c09001240200d140001c11035074114031491021840e00b8030480c0100c242c40200b441e20720f220502010741e2122503600341111000d5000900039044100361300704800921000015110f141224043c05006204418007201d29014603c03c0402203129080450341c54902690794a100380340285000e030401a9451404420240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 298350188 1250 298348938 298348961
    0x30b010309022e05030c0f0915190f2c060d06090c0807020d08130812090c0405130218070201020c032701030e031803070807080606030105060406050d03110c04 70
    0x40c808841c00d2040c8038000b001048071403420304c141189040700c0c3e601c078a8490180801210300c000910142e075655822625030705401031003469601c549040d68105210010303100c480003c0340d816485110000e205031078089580c80d2494550700002c003240e1410311404a071300032607a0b02030740520200c1f8103080240301d40002869500c0c0c000c10001c0d01800043d0928101406a10071900f1101e001d00d400c0350451081a0400c120403808015001e060401c0009801020400d40303d802d4000706100e00d000c000244803000501c221020086500c481d141d020140380c1c0780c0c20080d048071640d209400340310300751f0b00001c0e8840d80e5800054034105820040d01d0541d448508030004032121148034401c03110242140325078038070080c24200404c4464040700c0d80d49000c3c01940301c030350b00e01c00060004c180d00c040c0140401002c10908a892107510b40d82d006480d042c0480b4aa40a0340c6064001050351915002e810300b106d002070001c0d10000255201181c0e01401082c81024901c20313048001e00c1a110b900c41e201104a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 298351438 1250 298350188 298350229
    0xb010909090305090f03070302010807050a0c02040c11010605061603050c030903030c0601030308060d0809040f0e0607020a14010b0a03020108040609050d050301060201050702070e010605160b150901090219030b01030902 96
    0x504000410074404aa00b821718002e6014141c2440140d82014103550000300a040040d152400b880702240c41d8220384000035005030030603004101e40c0703411034000308100768410000d02401b600e440500200d80a070541d541009255000703940301280c010300051403d054000d0a8074604000315012914640c40307140308203540d03803000004006065014202c65080013007114100034040c15500c03800300034080d0804180c0315540e5015805500040c0b6404401010026030030380e0308034500b40c50301a444408d0b412043c1c0d210401c0c90101065070806101c1c140000078010304004183e030a54004440750744000708100e414650721510000850344c10030810226418030380c1c0e40e5a0301c2d8100f42c3c000f402d64002030001c4003590f0100c102417018404241000381941d215240540e04c4501003880760f6815030b85100050100148481484022903500540c134900c08c00648a00da2180d0303131402888224841c8020308806c1c04590301c004580360f0322981061280b11014500400da03e00650001116084003103151100003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 298352688 1250 298351438 298351447
    0x60717040302090f1329070905040e01150e0601112d150402010f05041a04150f0503040605043020070b070c0b0a0c0515070c060b010909090305 63
    0x1481c2091440e0f5002d40040c06045a5082000f81481e00d1760303038200000c00c9101c403d408403213941201e10200c40c00034030840701c1e5030f418100440003500c4c06201d4014a80558203169030346481c99414003a080c00722080c0c0c00c0018015103000b810303502d80c0c18080e0205041006082e401da100150401c080304420071040b0b00011010700700d0b184001c01c0345141c0e518054903084072906480740030701c080070305a1054080c00c0c0036007a000500c00c112500c0c81150410000c5910580500026600e40005001501e45409002480c00d581d40c0058a0100702c03d0300d500d00183d030402c00100080c1080c0c00c0303035400900c203005051803040110710040b403019001c07114904081401300507055641e0b102401c15080b400c5602c0c0000035201820001b602e0b02c0180c044d915041c0000070740c810030000680c984000030900421941e072500103000b00100500b4090801b5149449514540f10b4030440c2c4441040c018801600c4140600d41c4640e5100007622504000300d0501100d079038005825402da010704030a480c0720742e864541d43d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 298353938 1250 298352688 298352693
    0x20405060f090f01080f13140a0302070f1d0726040b0a05180304050114040806071107060203090901120303110f0d0f140606032802070b06040e07060e0607170403 71
    0x81070b40c1d032006070400c4010030501606c440b000d201c898005d01252020400221641445000c403802a05051030500c900b0325076500f80b640c0402d070b200503104810004041e035a55200d011481950300c52242110710204c9000c01d1605020303036001d030a0740026211460f0305446a2414884040e0210b40c2924006000780403c4420070032441401c0d4001503000d101202c86c41501286540c0303000fa4001c1505201003101501700c0e41c2d0389541541c1c000c0c2500c40c121000b502d08100000e001100000000d40d8920507401d021664074004016030b01144000390900d0000c2e881d00c2d2400f402c2d030350014401e50070f2544c0c480407902c450740000d00820301400c0b040c4105a603008130568110840740310707203203580015240c0800180040158912141c02c0031084400585988400301d1511000015007007030700c40c200c8250303030000c0c602c1166000b0f42512402801c0454159640200740300944d00b1800344070303500c1e82240e83c4c240105809180c4450742141c2c054185803d10fa8540d8440860403100d504560203400086000c004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 298355188 1250 298353938 298353949
    0x12012042402011116020d0209010b07140105010e0c071b060503070e040207020d0206071a0109050f0711060711010e06010801020c011b2a05060a241a0d020405060f09 73
    0x303035982540700070410031550040a44c8240a01c03074006000428940c00001995200d00300c0007111034000b0114001541d40c0c11140c2074170b603c0958104c0300d40e500e118081d801d030b807010310070380d4125450024003100ca0b90b15548246481d078171004080b0340c0186503181d4240d0309141c08036808054495900c8555903810211030140004900c0c142c2c03e44254010030450005840e014084118140d05680050300c1c0d840e645001c0e002c02100a00005400502d203000140014a6800c01405280e420b41e0704000758485200c11994902c0400d501400d0b0743c0f00e840441d8040c0c2c41104ca50001e4901500005080000b50b41410b0406000303030b1011040742e401003080704440100388150000c289903040f1551140c5803180005d0b0942c041c47c0100640d1180d103c18541401039503468580e903450780300301518803074588010904010b15881440bc0d110b100c5c0b111080c0c624a20703003000034040d83d0140e003101c054000c03a0603010070240e20071041820302c00c2c0c0074007001420b0348540f0086c204601c842045103032108604d000703104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 298356438 1250 298355188 298355249
    0x3030b1f030b0f10091406190914090103050303041b05040c0c050106060e030601151713050c09070228081204060f050105150c12040801021c0b01201204 67
    0x144610129415046225042040b110482c0c84070f40f401005420301000040e1f01d4060404200b10703110410740711600c03099001d8040015030f011003500c0d6404e5030700a410722403003d10900008256030b004101060100787c0080054002c0e200c3c203a44004a25103035004907041e50340390707011200407a002c0c0706d00c9002c00c84280603c00c003400341803412260f20034850001960701c24043c49a41243d007200b0b04c1040d4000d11480121080080400b0030481c141070802d120200b0281c0e400042d02c25000700d1440c4012464411043c9006030100e500070406420b4030510b201c2c07004003032046801c0503884035100e039001074101009054100c1c840c500f0a00d0910b420b08040d416501e81c800101c03110f610700340040c007003a655514180b440780700d10075155482d0000368039024904040325000344840f1001050000e42da090540051251024001e8044c0180055841c400709861030300071554003042010b110461014150588c105100049404481141e84181c07102c900c0740d0301641192014840300000590421072500c03100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 298357688 1250 298356438 298356469
    0x2040906020a0f0e06090f0d0f05010624090803030118021c090b0901150e0a0f060902040f0503010603170705101e0e061006080901020904060e150a0b0703030b1f030b 73
    0x1440e00040706d0000743e080c0b0603071110b1407291408012640501c0b1a400750301c401994884000c2209544030451523040b2580e5207442c039504c84850450b1200c845c070409803035080301c280900079829a4200301d14800c520b61100c40b250782059086c414032091040c0610f14148a0880c0c03640001e06849a04044a080c40001c20140c4541c1c100140782d0f01c0c840d0f06a2152040b500045052a8251a18040b42c6c02510b5030310908983d02d0f042000200f06890781d40c2c014000c540030340c00126603035a030f120241402c0e201d440c03102608905c2c081c00c00f0901002a00000d091407803103141929542c0031210080011241c40c202c04440204017521101c00b090083c3c070408201a40050080071076203091103c454035100745008060800c249000440c84207482501030300c0200200070400e005030391302d80c6030725100320004440d040100c1415a50115250414428a10654050b20901480e00d012514150050681d02a140b81c200c0e041c91114000c502010705c0b10040781c0120f81e00403400703a030040100a60b149032030404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 298358938 1250 298357688 298357699
    0xe030c0307240504030206180c0105180d0b01120c0603050c0d0e01150305150601030605060a08040507211a060105090d0203030d020a021e030414090402040906020a0f0e 74
    0x541414840003054a803400d61204103501c644014056a801040d20406031000150815003804101600440c03076500c0760072160024402c2410035441290f0302e40b541200c450204200704000075100081c0c0c4000f000845016180e20f1044840355110b01156400364000844070142c0000d281c20404584005e20013002c55280521031424182d6101d1102e01c111100017259964507601d03078030600b00a4025140118080c3c072070806080e03032401d12617114250302e03046402c0540d016000500542c0244595410783d0f40c00352403141811010103040d200100c001e04240d4092042a1000904002050090340e41c02000102d5403040d070722500c0d0100c41160041e90b450581c03034203041009920390f8084160303818881c0c201d448268051740380c000300e41148201c01d21140078600010703204616070f070001207840e8004020b12140d00b543c80d002e49526164082c9010311350340c480d203068000c0358914081030b2407900300e400180000740400059076440b080b80d11480e88903007c80c2c2d1410107158166044071050b403074038006454 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 298360188 1250 298358938 298358947
    0x40f1e0b030612010e0d030b121504080c0f0a080a0f0e130b0a12030906091208040b0a11150603070603060f03060c12150312032f0906030408030a0e03 66
    0x200c034050100812290040e641c1c60070030b43c1c030703904250064803c02889005966100a541c28014081d210300710800b4054010b51b48a0035900e6400950090701c822140803400103526140e440382c50a038880c030b00107442d600c20002c5131034580b401444032002c030921481c0d003540d554000400203003802c0c0100045105001c440e0808041c80d03103072048140c0103003c8081002030700c01405400101c048100d80c225140d0700c450690700004158224444409231440da40b03d013419142d503460240c2e01e10445d4000148002c5e01400204564814074000c1c00f0718070080d0a2015050444401e01890007228502d0011000100e001b88846801c0c10b000304000303820035180234440c1d281080c40b02d41d9142100e1000401803a91550b505100e0707841080d8020822005c0607050010510306151a0320f00741c5540809c0e90510526019408058001c0c49481203043d1034010f07941540d8006002a4040a101070b0030a00701081008001d0360740e55500e000b140305030300c24512251641030135082202110603403048481d15510400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 298361438 1250 298360188 298360199
    0x8030c070501030f0612060b090108071805040c030209090a030807140f0307170103060501030201080c032203090816090b10090911040504020a030b030f1b0904020411040f1e 76
    0xc0c84000e9500070300b0003280448214010700c00078106a480300202d501d041c3c40e141d04020326904031041101c811100030410ba40c0310104076444011074401c1e01c0641d40c500c0c0004200c000340783c002941c012300402054507100d60b01c0e0007007600c540f0112001c5406400c411030074010950046070391074001d68207203441d104211008001440c0c80c8600001d103e9025000b04c006a84507102d00e0035488281c04202d000080f95a6a140c007a01802c2e01b800201d010480c014001203401400c40b068910940c2c2c031071210303410840b12003002e64005c8849441a4100940a9408100f5240c104019103900320842c1142c203006181038815800ca621103040c0030f12618075040d0403000258082541e506a4546100024001d40d00c40140710444c0b0450307020942003400481e034a944160946d00c01c6200340c0381902500c2c81072550031481525102000c8014a00150007000e0502904001900f80e5101d07102070400140c020624840150030b411a45c0305a04110894a0611501902c089043c0c040b4210301c0700d5042d441d0811 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 298362688 1250 298361438 298361443
    0x6080f0d030c020c01051317030a02010509150f090106170c030f0d020303010b0a0e0d030305040203010c03050c03011502030f0c0a030f030c020c060705100603050304060314040209060d0807060606170108030c 91
    0xc103541001030200c0d81140035075450084000901c001903a001e21401e160344141d407290000d2b1108005546400c0020300540000300e905608007403011010b02003039603440a100741c10b00f0064640350075036503501d0010504845041c103100601100720000d0502c0b80c2120308040c03600700000c0f0100c000b0b40090200b00181500001aa81554024408070341c4648411804413403024440c81c0b060351040c90006140d0134140c1541c4464050750094000307112804113100181c09460003a68540d2001c01e003080104031496020380c14800c0c00c901441500d1910800300d1065078950480b00c03031034120350462030315801056000b1046076400211070405000c0880f10343d6002c1d454010441606009200c00604541000f200b4003202d40d49400c1c000e02002030316224100181d03280c0080c02294003092a001d0005005a454140c0701d100d80d60052801e806603880006010a00444040840b81c500c0b050000000045c42030164001030000f560b41c50b0104c51081042c07041011040e0f21001d0b89030010001c0c08080c4102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 298363938 1250 298362688 298362703
    0x130e07061e0e0111120a140703090501080a060314060106020601151704020a0305010903020709050c12061e06030a1a040228020f07060507110a05060a2106080f0d030c02 74
    0x102e040040660726040700586011121308807003c5a40141c1c26040c022003c01000340c92801c01c00d035031300d40c4014501d40c01ca0945114800e0040d000c5800000c00300025031040341d072994017120210f0003007200d03130781c9589100d05030b040c030100707034440e1b40040c80180004e03541002002e00400003205601003d280c000300207400945e42a007440354204a402c001411f549894220700000d645c0100200030618003070400035210a042c0c0180c0810b10b091a0100b4107100d4610f058440d800401a810300c96a286c080802044038400074000c00c11902410900c3e90940e11000038603c11442c1120104015141cbc01116940510344c603072480c402ca03c18010509401c003590b1405140026200c110600b001c580c0009074600041f8030302c401c40720b04c5003400200c0c031694030101a0044603c2030400610b189034040802580030b10354000c0e590050001d21058410702e1049512950401c41b1220b0681d01c1c01044100c0030540b4003941000d890b0350300c80108054004405c11030410300c4c50052804001700c00400703400940302c111 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 298365188 1250 298363938 298363997
    0x17090a030602090103060b0c010905060f0601050d0b2403040b06010903111011070603060807050603070f0822030801050f0f01050d1d1615020303070c080c0c130e0706 73
    0x5010512a40c142d001b50306c1a4040d000200314251990940c6e03c60310301804144c030044034940640b00104208180200c00782d03008034030503121641005901c0300301000502441000d1940403200d1100106048001c4108a04c500c1c95850f0041d03492a05e400c000c044d9190180425041154a40c001c10101b55120000c960f03800040711006c4902100c0c010813190300060b50b00003402406148000941944c050780008219030908003602c00495403001007040600007180c08101003100c016003910401d100d40c6596030311070300c00318454a1040807404007003005400800d003240842d50950040c0840d10b4032541850020303c0031100c4046560308200000c0880c041d11822102c41074036032261780c0010b84510080c2112594090440b00d44d500c1d0f880055514603120321600c40c01c1505214245403561021088910620184d00c5540510309541d4401100340e1104ca00042540030b90f080b2981e5517030320710b000400400c945002c040b40200d0440160741c101440c4d030380010300307014410003000e1186647e040004030514 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 298366438 1250 298365188 298365191
    0xc042115050604021e040503071215050405160303030213093b0f03030f0c18090c0c0102030709031101030218040905030705030708122d07030209061617090a0306 71
    0x80b5402c0208001e40248619074408030205440790320500b222002900484008904403807040b0350b254403c0e41c2045103a0303806800490490f039203041c0c098080c0c0025412920a408683c0007412542c0320700710390029500110700107031b00054007191b241040349240c0d0160503288000c0184a01801f03550440f500e15280d000e4000f00f80d401c250801103d0201e01028200100c0d060364905603c5101d5262250300446d40c403481300300c0c04c401049800340c0440641b07004110303104107403401280200400c010140c000f0004002e03101d0400c11003200850a0005d9409a40e2a4403a40c2184d415850404054880041c3e102c0c101441444610022000300c9175122038000180c0f400160800d00e030402d40d04602c6a403101800c540300004102c02080f01f00d9005202034500c1c0568400d0f0750b01c9c1c2c0250501c051103058007071410b1f9144102249543c40300b009510b508901503090040c5480c50200128125400c445401c1440b030802107540e0041c824054103510380c0024a40c0c03143d1910482c000003421030300803800041c0025 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 298367688 1250 298366438 298366441
    0x2061012170d060b031605090d0609020f0d0308090c1e0d02040207080708030a050901050408030a1d0610030212010c020303010b1318050603103e030c04211505 70
    0xd40808200c0b200e031140c01d07500340303c002d8075140804c070180d0094070403604100944440700c3c04c40d0701c2201640c02c4844002c0078a0513031400c50302c69901070001010166400000c84403264400d075100341e0001c401c14801d4490540300d01c1c05030210f50412060b418060b000b024842d51040001c0c1800c0c00b40c0300c05210484101000491074000706c0c00030b0050040003044418001581c4c0d0a201030b4001940c030a03c0c0c01031041c41141d8030796000c1c0e420784c0e1040d03800a050f1001800420500003481c0c114201c50340402002828103200d031105286001800c1d6102c400c1d154a0075002e00039801c15803e00819454410001d0161000c0050003d5407407105100e602101c0300040342c414041c40e410040079008094030100d052154600c015007e004010070f4882c03510910580400010880740b501503001600230032300d031043e44c0d07103024200c1820307550910015000c1c41500888c0f01c0d10002da104050f50241d003008400d25103403170800007001100301850a1404040d031400c05071000068182813400c006880e80000810903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 298368938 1250 298367688 298367723
    0xc0f0609010f02030909011e0603090b01030807110907031a060415080709090c0f0e040e070b03090a081b0106063011030a0f061508040f0c0506160302061012 69
    0x2d5001d0210f1705ca910010140001a000c01401e01481c6c514550b07036000f00d4916903408081e81101d0b9043d01c02000c00c200c400c0104041429040a010024041d0318450301e03030b144540004508010868035000030a94804148002e02815210448066016108240340c2824040d4803d04401d000d22710400704240b01001820070b61240030f180008010040301400344060000000d40701e43d6603800070b100050303001c10510119203000d004800e1385081500c09441458280340700c6035125440100000118480c4803000400100e1400040c40d890403e071100c184200c40d284011401d4a0040d40703c50200210740303080d90103010301d2180c41018095100d9400c4034aa0101c02034102406601c4032880c0c10702d07404420802844c50325000f100c044404460100b002e1034541e1840300c654101312045800140c0150001400181c0c181703503030b5100c1402400300381030180d41c03000080c07032540c0442c2c54030080c0c07505c440c454001c245e01040420b820181030100c001c500f0f4100300e0141d03070031070044001400e00b841c0400c1c3c2000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 298370188 1250 298368938 298368943
    0xf1002030c0a0605090c0a0303080f0c09060a02160902040305030301121112150f091e010908030112110d03080a0911091314060411120c090114030c0f0609010f02 71
    0x91240080250b9221007401e08161005140464034503c2034050141141058505010818141d9a144e200ea40751f40d1034441120701c640c40024064600c6100401015407181d440102030030403042141e00410012000010b610f4411446900816981340144000e100198000c0144d90640b002c0a0f003c3d10410070a003815081000315412280d00402c034540480e00458011814811009400048403040e0302c0d40281c081c030342070381203802c0800c5400442c031220009140020046102c3d01840c00418040c02ca034a034451f46900c207038056441c000910307040030100040050710f40c2c43c1c2c9504440c2c0c00715404241e2030140ca1813800a01e000c4296603100203400800400c001015101480580602554a00a04121a01788110100391076290481b0108a104440064a0b51055030300404245440f041541442032002540e001c209081c00303010304a104a07141d41c5203e50081c0010030000d4915400ca03414113062800350a50f07207000b01743c100d803101e1140d2690811070703208070b4080c030700040c8014441d1400ca0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 298371438 1250 298370188 298370197
    0x60a0306030c0609060e01080709060c0303060b03130507121208340210060b0712020f03130e220219030f060203040b2805100b1b0115050f100203 64
    0x90035a4110324020940c035034001340030003c1d60301589030307403100711401c13001941c403107904075a01c9000034504581448124401c1d0000d20712103110f41000b044454170340a065446800c01c43c1c03007151019041c2e14440502c04200311078401860414411103216681e40c80d0492132540c0c141441d4180035049011601000401e8184500d0f002003004580901100710083c01c10f8040a0744040010320030098100015519441900e04951262000d149000b07000c5d81ca10405c207080000d66800e50190703840e4044200003e00c010480d01c9503000320344907254145002944c00400180400740c04420110f50108800c1b614101000700640445141ea541440420340003880d040799040280043c1900554008001c0c01d40c0180d40200d00c90443c43d82103640d032030034003040b002e01041a50540c410340098903110b4600303544065040303a14040c001c403290b501c404a1031296803206400b959041d44007030142c2081c40d030a02c5068012009041d0700040c640c502000180345a044d418458800c0c11a070b104c08c11500e0081084030b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 298372688 1250 298371438 298371443
    0x7020c10050412050c0f06271912060c11101d03040e040b010806070507030c1109070f110c03070605160f0503040e061c030f110f070602010f0c02060105060a030603 72
    0x1108508110b1034415181c92010801e10300a01700702800010031b1410200380da9001e03491900105010b801c0d004120132008e00752040b44d0b000000740300440d00540b448600f07031004c1e050344004000f00718002e241040455813405101001c021029051002c5110046034030510203000d41000f04000e2080d0000e4407481c2040c01030729605210000e0000b418a0000040a115a00800301407603d681d0381c100e1a03807074010803100c03000050400c0140c040021b00034070100310b181c0d018441c4140e00010000205681400070b0350700c8008942e42e112009100ea520142101e45042428003814211071041c0104c1e40d070301c1c911301488080c007201084c266810030071215040300359500200c0e55000b241d1a0b080c15a181d902c680111031094103920700060080c00c01d01452110f00182a03044011070b10261002c442d4110005185c3d800c0005029101860755000c0180c000e084849030080c1010034a001360282c2191355911a0120a906000c4ad000102c1e401050060444406483c0281c1ea110800d00c05c038010322054000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 298373938 1250 298372688 298372709
    0x140105090a0906080106050f03030c03041e090c050714010c050301170c06040603021213080301030f050109050a0c050102190209010b030601180902070c05090f0604020d090b150f060307020c100504 86
    0x284e40d0015004101142c2d002e07100f00041c46000400d2580303900c00d403c200c0c49280e1042000300145c421840803600c006240d25011600c48e501c50f1301c1c01e0700360343c40c02c3d0600f00054800300d0460f040c44060500304509031560002004802c0c224100504603000500c52010b2a0300000200c3d000c3c0f40781400b00070364040d4010300d0941d0361500e80b040034000b90000082a070414040307800003000c03074a074200c80709a82a0400101415a0b28542d0707140320590f40c205045486540b949002c0f130000d1010172400c48928468000d0500050610000a2520b01d580e00c090743c00c01e404100c200f0168603000324203410364900c07201580d40d80e03035068010794600c4580c225180d0300c000c002c0030010b00690581d024060301c0340f003541c0300301800344d9440810448400503210051941842408102e0516003680100a01541c640c0080348040142c0c98410903880100d89990051120003240c045030300e4158401180510704446850070350502c00b100a5a40360b80c0040c0702d018400c0d00003c01185070044080d82c0080c00f11409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 298375188 1250 298373938 298373951
    0x3071803140706050a090b090a0e040c0e090106210309080703080301060e0f180a4d070b0702030904240b1801051804090302060403020c010801140105090a09 69
    0x400800d20468510070750442d0144a502207016482441211840c500c15519183e0140c2004201641907110180d11a4020070f940300000d02c500d0a95400c40c07265014a11402c045450125100f004010003481407510307901d040014402080040c0f078030300704079040541e50b02e5220404e02d0140c441142c04c0c1c00644003441940300001c20000488025411b032501a47c6a501002c500414040b0a8042440c10744d4006801201014090440301400d540061944000b1031845100f96500046252100900d00300590011426032000d121491010b8402ca0368100c0000c8203072a01e190794100e0064002c0202074202c0d40000c500c4c0305108000792256000014804c004a00441c1d4601c44031000700e45070103141003200b6000090381c5c01050140c0700c0c501a1200c23203154080c90800110b505074090040d1808841c0d10004170b5905485d940708422089200b0f4004211506141c20064501a802c00f0414100983c050040c0f05113951800c181c205401d0130300300a900c5003090000105040d07040d03003091040a24211 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 298376438 1250 298375188 298375193
    0x302041b02010e01060302010905100909150e10030803040b0901020c100c0f020d14161209230607020f04090f1119030b0f0402010903080a0504050108090f0d0503071803 74
    0x101080040d61a002000b01e242204129402da81403031001134080703503501404000d241850204540325a03a10f1030706420a80e1a10340c410121595884c81c1e00c4000300c400020f0200c840308655843c2c22805070414a022280303156249000c030b01c00140010040c400a40228034080b40940640c1c7c001012141a00d1400001c100c0f00c80c001c00d10301e00003034005104c20002c03090082c00807500c1c8235403511550340d0310640b1b0b000106444d8030f603021106100d8440c842410b41c1020905107000c42c030140c1ea60740e540303140e450b282c06041243d403404900d020154030340c0252520030641d00d910880754000e81c107540d2004406918000507009081148001e040c1449544400703041000c0d40c82a4441c05100311340141d2881020030500191001d64000100407035000004581038042120400d91701c00c0c414549680e12315240d0b628403640d60812900c2602240d40850b00b84125a0815881ca922611002c0188070000e405002c260b62040079401034414048004041102948280070140006000c1a007045482c3d5903407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 298377688 1250 298376438 298376471
    0xe461b09091a0708040201111905100510080715090b070b0f090a0f06051f0902120105040c12091e03050c010c03060e0f070c1505100605040f091104030204 68
    0xc41103800180001c0821188894440c4140c01072405a403259044d540351b50065449015118441036a40300e4500216486801c060005201ca489803000d881401c2c0d500e80c0e418142c0d40e01400d84004041001070621181d100041c0c50000c94a039003100b0003410007030742e00907940b41e10990094110034200103803200901c01554107040c0141d1007103070902d4007035030f41d203004c0342c1c45950104000b0300c075082000b84030012891941000341c0100503000718050788038038034020701d00c41c42d42a80103148050700804c5200c0032121255000f40100b000799000d01c0000c0c50020010018041940780301e515070b540d1040c2c481070080d8420066040c185254121195002d2810050500c0e04100040c000d40e6080c05090007105102c0e0054504841c0e458011310407a8a400710451040c4000510080c02c2180072008400802e51210320b03090200007101000441e800c10044050802e80d00b0b400920900400f0001040f00764aa6604041181c030f256100140d0b04401041c1c0050510840c1d1000c0c2d4043d0510f548000c0c0c00c1501f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 298378938 1250 298377688 298377701
    0x304031b051e0303061c06020c031b010c0c020a0e1801060909260702060d0b09130209090a050c011d0301050412080108060105010815060c010e461b09 66
    0xe10241040302c141c00c090f682e02c82110840e4003d04c4000c0644030410300ba08881c1c0b0014880c210140c108210b16a00c20b14640115455100310300303c4210070452000e083c4583e005000c09441c001c81c512515401190703001a03244a04400424110001052048050f1180103402c080000030b00035aa07841480e803020f0702c2c8000d000e03200d290443c086010140005d900c03907051442070b03080c1e81c0c1c01e003441502004600e41098054101140c0c4880d100c0150b50307180544288144c0c00c03010740280001b201d00510000380402010103071168807220964000c00c1001841c40c050308003d02e40f104148220203c17050714403000c0048103415600b400e0600c01000071144001812680b240c4c0e8000d030580c0da0b50600750ba940d8082c420940802d105070f01150341c020004a003200100405011503180050f01c1c68590700f1110f02884005c5541c0240b02401101400b4198100454a031001e6866408a000701c1601300d4100c5110714880340e5028250302c408200da24034201da249400c008810102d1907640c101c480c041d054 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 298380188 1250 298378938 298378963
    0xd06050a0c050301080a1722061403100512070801050c0315100507080306010504030b13110303040e0105060a0903080d060f0501030c08060f03070803070305070506071110020304031b05 81
    0x401850030003041c842d40550f8101c2d045a40200104c4401d5182d9804102c071521704004940070402c9010034060605000c860010f08252503103111514001c0000d01183e40d039404404524810004e000054240d86042c04c2910b90880784041c0c1c0c9103005004528013482360340403070f0703c6508000070420a0f41948010710b109207482e140e0480c40c4d40540082010310f0300a00c10303480c045001400302c1404544c03c000a550300c810181480c514054490b01d441d06103e030100c034031901e82c0c02d20344440c42c10020002d0610420310340942c0103500745070902c40d8840600005014030f9003d40f101040d00f6692620070740d00c9400540c0c21080c8243d4030301800c41c054001d00441d001d070210440c00d100000449500c2441030f01a000c41f2070b52800f6a54407050108141c10ba8100181540341c4520f84011980410070700040821610948800703584202a03d0280d040040c014040380074000b00820f0041c411030045104150002c50b0000160750b50703514a025595600280c01c0032000d102c0fa08060b40c00c01100181c031641d2000d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 298381294 1106 298380188 298380191
    0x120a050a030f0e0a0801020918010b0901050c0a0c0f06021615030b0109030b0c210903070b04050102070b0403091d070f0f142a0a050604030c02030a020d06050a 70
    0x1044d60040b00d00c036540003030710700400d103059a100c00c110500010001e01c2036241c031040c00032500424020a0503c000041c10b0305044a052100c0200658041001000340d074584280201520f0345000c1e80000d44900b140b03482802104110000403103500b4081c07035480000b03201003103014107154070345141071200c904030220000d1010b56081e84195803101c8015211491107a41200f6111240320580c1000c500409002ea40c18001c01194196a0003801801c039540b07076807800500a2103148006010301000c803050200301640009041c04595100b004125003011840340031a00002c00d442e80c00c081a6401c2942502d580902c01962524040c0c0c14400e90410301d0682100c00c0350b010804418242030b503404060801c0c00c160a4002c02c80310080e00401801e405503a6560b03413084045c0010b014041140c200c50304540e002c00881c11000c2e40940b074002c00c4959854060050a006c0e210703c0c6085 = true := by decide +kernel

theorem cover : BRFrame.Cov 298201438 298381294 := by
  have h0 := BRFrame.cov_init 298201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 298201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 298201438 ≤ n) (h2 : n < 298381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
