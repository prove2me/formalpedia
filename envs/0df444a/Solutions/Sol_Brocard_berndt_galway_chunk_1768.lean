-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1768
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:36:17.165442+00:00
-- url     : https://prove2.me/submissions/dd792300-b2a5-4fd2-8824-d14114f5f0eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 317805755 ≤ n < 317985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 317807005 1250 317805755 317805757
    0x2a0501030519020d11040b0703020609072301051b010c0905040c17070e0907030203240d0308040c0f0603020c060903030906010b0d020d1d0f011a04050408210a050714 73
    0x402e98400c00c0d000181c0048100c01980302c01c0103000b80c001e00e0354444e074aa42840c501d5500c40c0e00142c0051060001003031100c0710108240f0211540c080d81605500300f00044091500f0a0741c9000e8107201c0b042c02110801e00d24450049030f56a403d2000041c007174005040540101c256800c4640038514000c00c6103415600072100080c1049110080b5000b035940c40c0044840e4500c800c00c16030040c10b640c0c04d100000c0e4141d000344d40212044078040c240782d2413601184d40c1040c07039803006d039a01502c0d414a01d00424024000c443c0c129020fa010034490545800318400c4000c1c460b0700000010b80c0c0000c145024402c02e01ca05508095620065803541c104040b0090b40e900041c05914950100010480300d1184580c2c100c4401e00e02c2004207020021040c07822212500349452848d00c035000300c0c811140020018400c0e0314900c07d2500c0070300b05041c0310009110061200902c1140e0311581001101c540c03001145a218544450703008211143c0792030303c510400e5440180c1400140b0110040180e1042c0c0c60320 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 317808255 1250 317807005 317807041
    0x61b320708030405010f0905030d0606020607050315120d0509031002040305070b0315030106140108090105010b0a1103040509090303100e010501050d1e140702011d07060c030c2a05010305 82
    0x407985840c3d4a4a003000750050459800c0100c42d549001084010004080050151009240410020720ba5628400d9880d000c0844a00c030000e041040001c208e1603080384c001e6040040500348412620001c0d00c0303903280840740e89103000421004a80810a45010404d03034500e610800c80a60500d450f55440c00c0d912480c5008091507160013100049440040107591686800010000e00c6104e0b0b072410f08900310500b0407a500d0005000c140040d05120301405220304803841500c01c18036040309841c04039107074040101030300c0c0365010402c07000406550b01800c280c003503039038000a10f590f810300510701d0b40704440660100403d41948001000a40c0e0401d090310f880c070806110204803010f14021a040003000c24040c200010324010100240c1d15491030b0a5202d0300316600204141c1250081100420f0840c0b0980c4100340e0105100303200303491040d919801428460f040040c0d1201b81c503901d501d28021481d410000c11150301320032102d054058801100244401e00b405c115034140341108030811420301d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 317809505 1250 317808255 317808263
    0x2040929060729040c082a06092e0903030207050103151509080c0a050a1406130902090a05040905031e04080304080115090605060304030309061b3207 66
    0x12900b107081c080c031402a8004201c0c42c4000e01820304001100900325041542d040c1c0d550100c00b5804a0050390016110194880e144464016640e0898940350300d26003094005805c01e03418468046544c0b80c40030764492140f5010140328200b9290f1601c03041003074600a281c01004500e0700100042900494500295213013032801160590340c0702c604d0b0349241d84c83c0c1d000418001e80002c0c000ba9a940c808814000c0e200081300b40d443d203860b031030100000740186014465124680312010454203d0201007000d042c400609000d090114000918034003407c298400128540c0004d000c0703004e0720b080125840901011101041501c409858065036401020b181040052070034500e00304202d400c101341d400070070181c8100c07940e03280c0307822109000e44200c9841110080035000041043c0e040e0780500800c1e0ba00240403d811690342e900d04a014010071081a54402d95606400000551003424100d004540b512000b8060700700c10a910151aa00508019046625003010480e40c0750700e0f04880f8000e0300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 317810755 1250 317809505 317809507
    0x20a150b0102210a020d03020405130e0a1209030c0e010e0a020307110609070513050f0c0d0b0406030b0601020f0f0d0f1103040303081e0f0a0507030b0901090204092906 74
    0x146400603490f01c8120034581c0303d40520481d203e140010070100806641c1155406d60780001148035041c2c059002d64000c10f42e00c891400d00e08002c8c02c101e5448140e0109102e000c84444412588891800c0a1060510000503820031002d00034451b40b04419070080c18182004400ba616041d5000640302c4080c02078041c1c180c002000c58505485a04801c40014048050b100e0314144100c8041d0390b00c280b44a1540201d414400500070255144606445481c02e070042039030654420f010b914860b400560b03a0603890380d5607201d82040381c556210b128041d6109103101c070900c0c1049000039140542142880e05968002c0704005c8120002003400e06140855040407240312200680640c4d4200c00f039090f20f002c0c0e1102282c004145980b0000312030103407211413540007411400131180c4c4121041154846022107a901c04120b03080215840158840b0310303440d00003404440b50700000c0c01401c0c00c0e440340340c0d0190081070922201c0014400e103680c410002c250314016280080c0c048442641ca016000e01c1070b00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 317812005 1250 317810755 317810771
    0x1a0304030f020a120908010f0905280f051b123c0307031e0801120c082a03010e0c09040c050613060f0f0503060f03010f1812020a15 58
    0x4001c004418030f0a5002d201100c10250750080102010501c0c42010320303941c00c080c2c04a6003004a4824402c031030750080c0c060000c40f0f95407550740b4180c10702c03072080244c280c0d004101c040200b00c500304c42c035164902c2003024080759015982401f213244003502c041881110f10071003131a1030010000700c2a14005000c0c405412603414032090f114000e1200a94101d00c8a012285400400001c8001d01091b03200c2e484010300400400102c44841c4425003828021030800401403006020381000004128492000f25451649840440d03003403014602e84494480c625482c0840c01113180340201700501c00a8000300018401c441c0c03da65078031410700303115008400300c8000c101849280b80030389014110107411150342e8200f502065400181c9449000700040b042030415198030321511581414a18950712603007035440d800200182030101d6010913500d03660320300302c00c80f2040c80b41c010428040b400610400004e116810200400225580d2110864000000340030000300030319488040310500c0c2c1d000040540c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 317813255 1250 317812005 317812007
    0x30c020103020d0e0c0a0806040b07031802040e01091401020f1b0a020d1a091b04020c0c13020d061403030a0534050c010309050c060c03070b010801060f1a0304030f 72
    0x22150600480400c4d09003002c400b200d61001035100301a04080d1458140250f0300c034046505c640041d14010f01c11407013580440c540610a4000210310007090341e90000410855000030121640744c084540c46035107074030f040018401d0307588105064130300c0722000390700d400074082000700740781304403400303001c82c1038505031980d0024804000c0411083d6020384101000079550400307204200c2c07406694100c440c2c14030005140312030003103000300790498807001030900e940e507010400c40603401001000c02540300300c0303180d81007070354881217940ca1000a001300160f5440c00140080c2c15121035030846000d8503052004a0500c1e02c0001c01c0b42e210301011716001d52148420340320400706188010385200160300c900d49000240c580e1344018a40d2920400c00c031000100384c2c20040d03003a40c0345507c3c094201d42103a00c0c40100c07814510001c001926000341036910b0303c002541d600366489800e8001c01d032242c1d900c10080c0f100f4120500d8a20190522202040c8914045900641c2c0e038403000308014104140300d9108640d40b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 317814505 1250 317813255 317813257
    0xb100207050a0b0d0b062a0307020a03030f05120f0702150c03040609020a0b0408030a1e09030605180303100801052404090804030f060c020d090305030d0203060a05030f010e010b060412030c02010302 87
    0x760fa0300400d06647c480c0d4010000c8414121542d001500400f041100107602c02d00100316a520365028106020b1249152015510301e80101800b10502004221800d6821280089107104180d8000036000c00d081000000345801c40c2581d070304a60008102c2488020b50300700d030a495009038032035004070f100c0d640c42c40400c102c3d849039401828040300c04500420b141c00f001c8080d000d420015641c407882404025000f004106050000c4404540303050002e0021410039040107a00100030700792001840c1404184515550007103038800d4007084401024040303000b080c090150800301062047e110f8105180701c1e03a25517022120400c0c4140e9613880c42004200e440c0094600440e00440b10701030000203414110081d0020b07143e00b8005002e00c000101e60240503412180642c0c0c1c1200046081c0200c2c411148001d501c00f810b82a8842890030000816503402c00004040608050006c240c05180c20201c0e42510104814544208070511040c0540394003000e05c0180a501842e0941c0308910a00050f402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 317815755 1250 317814505 317814521
    0x15020d14040b04060f050403080f06060c1f050108070803041413020f03040c06020f12090409020616061a1c030c060510050a051005070b09031c0b100207050a0b0d 71
    0x100c000080304000600c00a20005407007140900d0341401010581712201c012518105e90080100c1c2884001c101c170280824a12684020f01400c800e207413903d00900145007400c0c1d07244030b074402000400482001580c2d030155a00400b003880040c01c181d402c0071801c80e240c0c081c4d40202c881301c0c01100d4010f0741c5943d51804052041c0310004045545402d552408411503100711816510742440c29400113407588001210003030303018664043c18000340780c0b0100c000690f0051038903d900545803a22000540d5401c001080100707510704406050602925104041d00c0e000c0c95142c00d22400380d11038580700e468a68148101003142c8034416140001450103403502c0505000c050840361404007049281140300c4001c600b59070040b03030210140c658074010003903100c0b092106d034000240280319900000b00303125402030300221440700f52030030603480084411000c501d548103940c0441c2c42c0c0c03034040c1c000e043c00d420b0700c5c20410440c800390803418100400f00c0c4003044548525810600000382032180030440342e00000c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 317817005 1250 317815755 317815781
    0x10e060c0a171207030606031a09180109200109120f06020d24080c0303160206030702031b060a1407020a140a0204020d06080c06041401080a180b01030c060c15020d 72
    0x184c10501c40c024010100ca0080002080c070b02458902c00c400191070568520f0720003846003042da07a4805142001c01200b0090803242d40d03c40d0300703010014800034920710942e041640c001400c614568001080203031958403000707a00068500000201d94802841c00c074003034000c140542d9946031185120002e1201040d0f0684203010341e07180b038030b00224413031070f8004481e00d40d02110b0300c29004100701034403807080701c1120000c05083c10088006007000d501540d4441c0890040d40d081c04480318030030004401083c0e152010b50000130401c5500300c442c0c0300b08043c3c08030310290500280303045500030350f5500c3d0204024200100d07094900030420000c004c54100c1a40c081d1055444e00608000d200c050310720b0b40221610741c0908071032160241040e030299011140c03040c1250040080110040d41d400601824180c0c54a0704c4050b143d18041d4050150b078890b500c00e142155070340d8503605003445680c5060304494204040541102d0100c2c001c00600e140000e08503000507910036500d44946c005110180c2d80403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 317818255 1250 317817005 317817037
    0x2060a0504231f0b030a060b010201023a0522140a06020705010606030506130f02070b1501030605010302130905060a03020315070f0c0210081305030f040302010e060c0a17 75
    0x10100340ca0102d00b2448410399000c81d03465040020076a041540c8141e20313600e8060f8011030310f0b04003007041c0390410080c160f4180001403400000101183e480c04246450707000c0240304070f51100c0c1750041803024403454140c449040101c0e05044500e05032442d400c802090310400501018000e0240800502100d1842e803c1203079070b100424a000c9020350840c130810380e45035280a03800150a8040d0284600c2a80300820214980c080008400f0060401864440b20980d090160340001081c035000c05000e0b94800d501c42e0041c42002000505a40154108904060042c0600c503040c01011001e20241c0c3e80422010449544890103c0c3d0840e189a03c041c0d8103100b01a211004c40484d540003a0003440309990716a455103540b2410781e403408182c18003d401046a8094401c054815241190003440314140b2081c2d00c6116107800d0b29641201580c21403540000404104642c1c1064540102d0b03001030780c00d5401c0c40c2241102a44688a1440142c00c00c12403400c004030304003030070080300d283c0315074035280c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 317819505 1250 317818255 317818313
    0x10020a020a031d0a1205010b0a0308071b053d08010501020d0912080306190303020606190b1e0d090b1b030f1810060b03040b06090702060a0504 63
    0x2507594000400540200d000c00711650010644185103820b2158040c1c4204951842c042514100104000065581c2d540c1c84d00c1181050740c84411070b82c0210f02413415262120014202005071880701603000076402280401089103417210145008200880142c071103000d00c0b44042044201192403a0011004201c0c102d40e0640c0e070032614180c10b8030001c0e4215003100c00402c905441311052401460441c0b512b030100c0e10300003900d000080d980400003901420762a0f440e036064030039190303032a002140960403220030030140d1308110f00785002c44206000725500747d51508907040c0c2c2ca440b689000e20300d48a40e40e01e056440920300012105110200d820400c441c203030130708254401100076074184281c1c203c51a00d0906d0b4130070302c40c1628064001e601011280380c40388080c2c9607104901030049e5555004c0d8203100000d00300f079072042e940100810003505a0b68641403034809145c2d02e000300b00c0e611509891081c4011590b00051456110303500300d00019103610b031810000c80031059108041c4100d041e400315 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 317820755 1250 317819505 317819507
    0x2100c030b090a151715070e0607032a0f0f1b0b0a031a010e04150f0305030c01060807030f08030c07060906020c0f190206030a02041706092103071110020a 68
    0x40b030040d40c0c0a0300001135a403601d0300c20f2103d8002c0c8285a0280326809003070920b41e0340c4980704074290415103900380280b41203a290702150311034010002c00d50214091490351000c00f0315250245a45061070110a0417408a41c1d541c0b807121400d0700c50240542024070b10315001c01a1290303400311100900d00003828287c1c1e85490041c01980451040d030002410b01c511541c55180c41d0701c4120301d00c10141c41e804585000002400001e0548003c0081c03215044e0000003034510307585169030040c5002d54080e50352036507002003950035a880d5602108130790303110080800100d050405003d0700c181e407045609c2d03030b07940b20b0500d00e1006024001d4040c0003140741c03142040802841d507005081900040041e100001d01c0c5070911500c0d50301b483d42115440880039900c1c0b00521b020340046a2103615540d006040035210500e01340d80c40c0800400d22415840740b014080c2a00d410802404001541710b8614850301d0740142c2d03418140400350040b41404100c00114200c2e600071700020a40d150131840440d141e859102c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 317822005 1250 317820755 317820761
    0x30905100203040c060e0303090906090a0603080f04060809030403170c03091809010c0c020a14010309200111070b0405040903021f022a060c09210a0b0c030702100c030b090a 76
    0x401e05000c01c0e04c2000d141c106c2e09011040c0d032080341005054114a640791418480b04c402c4c000d140400c0c450781c800303011000034080400381c44a1030040301170945a0341080300141c4039040c081e103071141950040c8010000200c02c400c00000d196980c036805034443c400500c00d0f501d140a41030310241e000c000305e282d101003511303192000762042000b03070300034400003940c90019182a08000b0010b034110f54481000c3c02206c001408034482c548061600003491400c9441e4045a1208040a180860003a1000c0d00182d81c1c095804000505688080c2101c0b40c5040c40c0e007156441648130b2030340500d4031102c40c5010f060003400381d428a008503110648c11504014442e42c0254050298404010004420840044401d503a00c07035140740c038040280020f4071004440a403540211902c968003802e8180842c410124601e0310100f1182284000e020320f2482c3d00d08940c561000812004d0300c01018410014281c0d80020f4400e40c2c49105a000104800040f10403000380910440c0c07a50400040414000e407800c10f03074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 317823255 1250 317822005 317822009
    0x16080307020a03030c1b02010f020a0803090a0201080f070215060d0602120603010c110a0818060a03020d11120624160c060302030601170606070f08031e16030905100203040c 76
    0x5036041000703001920080d501c00c1a14400031141c0746d116818040154040d22915030040c5990046400d01240d5036503046040d8001c0b50131004a4008400710421941c00500301c5070018815102c140b214030740240c0003035803007055030b01807902c000480000c20030640300d011561020b59003001c4250750703400c03111503c041c002c9004e1320007038003940c0317420300003800e403440350301d8407010002d000016240e800342d681c80e00181c0360402e1001e4420302072081e018104c2c40e65000014050300d02691000361700c401d44000b40108036454020300103000141000380c120812502d5140580c0000b003111050b0164220030a136000704e0085610059010000190b0030040035041c075244080548a03a409038401d50302c9100032000c1e40010b6800c20302041a07400d5410180c5803100c420f5510003400f6208a0610300c494444260f035400000042d201100c0002c28000f400d5550368544a68445503c407a1109040c0180320012400400d0503040805985101c600304016050103030606100620206549a080505040841c20054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 317824505 1250 317823255 317823257
    0x51e2b050f0114030a1401060b0a0804050d090510031e0e0703020f061306080c07050106090b120c01050901030e1603052d0307030e030307020307170d0e03030d0216080307020a03 78
    0x1038000180c543c0da004036100c2a120058003602000005a44036400401e418005400c255200c07000880c070050440c02400420034207680303003505400e107030900c01c2c01c00403201916410842a5441400181c882c02601010041540340010b8410b00c0011840b81b483c0050a40000d1039062001c0c0f914a52800207400d020f61340200d407000703440e03440d50b000c1010b0752154881c40000d03034071101001c014640c000c03030100358020800407006240c40da031a42d40608460458100803000c0d99100c0c0ca041081c1130690303c030800d80000000902c04460000e0001c3c0c014011150590704264581d5099950004180615456400851841d4007015220303e025a118021081181c00b504205074513505010781001410600321488000f852030001c40f61012550302c2e0302e2040542e0544810802d0000685040018000820a2140490f480102d02c82c109080c104d0142514007082460f0042c0d641d5a540401101c6d0708058110005070f803040c0c00c200c00041e024030404007800607403010080000300360300840c0410b14940320b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 317825755 1250 317824505 317824531
    0x40f0204050a151d07030c0203040305030c1c020f0c090a0f0f02030402010e0a0f3b011404090c0e040c05060703050705070906140909012019051e2b05 66
    0x11121003c0d01e103600813400440458142c2c011548650003640041140310440c816286030984036211945181c0c010103640350075074400090203609480040c0403000c09105440500340c180d56118103180d80d0f0780070300300d00c07445603811b040420b540c2d43c0f80740d0000000750b402440505c41c0e070464008950007904221803c1c1d01003024031040490915014050b4003d0310f03460300e49100b5490801e504003040ca012401d5601e04032021b61070140b0038010b9200c40348454401b070b540d000020740c18281a407545501600725140a2803c0c058140c3c0024003d00300c2100b17842c1400342c60b100175510f60918400019443d48550b400c0003001400400f030591000c01000464012010ad80d42c1940d6140c009040350150320666009000089403c001407801a0b10380c1c0e0491641c4001040074144204ea1823071211441c18454122840040c1c60b44d584402c41d80241c80300c0780b503414803a042c0280206120754060445001c5000440000740240c0405131204840e8141101e40c003891a2422000302c15400401090341e0035089490 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 317827005 1250 317825755 317825759
    0x90b09010b0706020c12040806070207150509040b15190e0915010305060a030524150306010b2101060809060a060b1c0b10030c08010e060303040e040f0204050a15 71
    0x1442041141214294070040746002401d4940400a4000d024041564003800840b802c1c61a640000b810141140c04040c25071401c1c44c5002900c0e00580780c0c03111a8143d151108a101c4a81080660700641002d940110380d00b00030000107001c214000c030030034401800204502100c800c40300c288958054080c2c4882c58082c0851003082181102141c05030500811401c8400751940300c3d41220707801c02000b62090211396141e5072201c0c140454140c20203c507180ca10789003150003003880d0019030085a26501182031403140c0002c241c07980e0b01400b4650704840d0005804810010b000054204000030a05468281d6141c02c80186901000d0341c0140d250311414000c83c8080d0700621881045420b95180c1e0b0f4038220035000700d9800301002102684006546040150701529208003940284e88955800504046200700c06004098103800041100031580c00b00441510000125425a00074000020550381c031898100e00044a140c4005c0d00141844148040605250007064940f898801c20001c0b80e0b03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 317828255 1250 317827005 317827009
    0x31207090e0127090f0f140c04090c1a0403060f06090c0509030709110c0105040f06142a2b180b060402030a09021503090706090806070f110d02030301090b 68
    0x620280030802d250002c60b60300e08102640c07013004030034030680f0a030702408103a071a909480e5400a900761216040340803441d2401c001031240c1520040d00f110108030340840b58842171004ca030140128030b9260001c1c0722000c5084803090a03a0f008540c4a0030a003c520307029400308002c3d001c1e034402d9903003c50803c42d0381c414503401281a074491240160080002c0c1c2d1425000d100079155107081c04103014030070008194a28000e001e054401e070302400e00b00c90703080e1349850b24004650003560b00f011171060090500114a01c072420310007014107050810740031a0941c87d074000b075610074004008802c4403802c20034900400c0b840b14211445800d25010403200b4000c2002040e40e1004c51401402c0200420004540b07140c507502940d085015010005820318440c0d0110b0860641e0360303074500007120003104112222000b000400c000d092079180060406d803030710040980d1a903002d00a81c0c1800070b14001c40540c1d6220310018015800350500321824200f00324030103501c80d40f00f0f001c1c43c02d100e814403003440d4030f40c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 317829505 1250 317828255 317828279
    0x6031e06101b02040b120a1a040210050a0329010807050a0c060f0b0402071a01060302090f011b05030a05040612020a091701020715050105040b040902100e0102031207090e01 76
    0x121009484101100e000004200100c81c2d00c800100c2e4000e541315448480c0b6105c82c82e0f1030611060a50082c040385442e810f041c4841d0781064030203507041402408200041c0c40e6007410103044042c07814082e48a071811402a405010480e00030150500060981e49811004500b0198104000c0c0c03030702c0551b42c440b4282100d85105014030303400401c0d0a218644009011070340702680514200300000350040680c00054203a1b03000f520141c03005003e0344100c2e41d0101c0c000603024010405800d0440c6014240c40100f074503280703890340f11810b10403450900010b64140c07002d02102d09520106507a5108008500503009810501401c400078603803040011011245108540c030185a54039200842490001306504c80e10050b0309104080d5000d21202000800902c920086010b18610208140d070405080c8001c40303958046452050b82050324030800341e01c8903126400580701c0d516103040e00908000060b881c3d80314003550a5540c10840b410007040c1c5038068140c0c8155081f0042d503038841d07680c4601070010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 317830755 1250 317829505 317829529
    0x1b090312020706080c0f130b0307120506090406240b03150102012f130801020405011d010e100302120901020d39110a0303050703050a1802090402030a0206031e06 71
    0x1c5494400415036514099000e080e100c41743e1b030070291a1050700070744032a00c01140e5210717400e400004000d0040d0640c121200600d00340d0141c40030049480d01d00001506810045d002034105907448483c1d80d40b00071900406820515203d8000c00c19540c2c507000d07855194000c8030911b14101001981030a150b2060103190300d50043d0201c400c0340040c585548402842e0fa40c6030017404460108036410002c020048194020505030340010b84845c6818005000d6440781005540000241e0704c0600842c2c1c0c1145c040e0747ca1210656802c3d902d4a035006040c1c009102e5941d0f54800c903054502002150700e01500104000d01007581d0501c2071461045000401d81503130307500c0c075416240c1d24950503101e03030b100c10702840c0000d50346c5481c1c942c140d902c3e00740c2424509806800d0b400a41c84104201c2d405805000d2a9080f2080510804c11407074030280c2c140c0f0f0764000307420091181016401140c01c1d9541003001048883c0c0041620f913880c20461a41d030101e44200c803641c16002c41e40000a01d4520305400385c041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 317832005 1250 317830755 317830757
    0xf09260412080c15091015080a15060f030b041101050702060a0c020a0b07031707020705060702090a0609050c18010e010e21030d24050a06050307031b090312020706 72
    0x1c40140d581d40300c0744107421111860806204648158507000c03003840c0b0407130045d0030781e1000d0100341449100d40b00940308091501c5d4400c0a007200100031a4000184801d40a038000c0e52601d8031020041c01d94018003045c0d4000005017207017036000700500c03801c269068082c03403090860b1842210f000300103460303070300a040d000303940801d0600242428038021081d80902c5072008121801c0983c0381c080c0c00b0700c1504080c2c0c040d000140307005079038103100807400815a00b0410500041207614070700800500b6511616074020b0159000c5004118246055001000600441d1406014501d0804074840c1c01d500140c080b103810b000c001589002d19401103101160707520301a51140100300c264001c0c030458400304400100005001e10710b1142c01d8900b40701402411829000c0401c4046103a1f00e05020913001c4e00c0003141c0c24494107400c011a54aa02d25003040301c500d820f142d502c0782d50b0500d0507002803150f410f00210311102403002101250b400860482902d101c0e4003440c2050305090b2040fa541c0c406402150 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 317833255 1250 317832005 317832029
    0x60807030206030106110f070b190c05030d0222060f0207090209010e04110c0a05070f0b03060d0605100f12021518040b040b0301240e07020615040f092604 68
    0x5c010a40b00c0d0700c010000203041012601e00d007a01150035807400c030030b44d40004400000801d50201c250500070600b034071880b0300e00e007120920310142c40740c036124032407155142181540095400421800010a0b800740600b034000864041c0d9249409440400f21707005240c014010804085170004980c4280d0340340340810b81d81d140010149600744030090004201d00042d580c8180502ea122540c10011800c006200b000540507484c0b504c02c3d450390002142c0c02c6100389203814820821a92902032442903580d0300f107400403855840701f98508401c480d468020500550400502040d13101c0c000844600b0584241d0b01c1d8000401144540c400700d004040c501954407030400214142443c2603006812100c03c0208001100c000c0e090001382145e03803101003801c01c2000071107240040fa1a0611820040094500d280a80c0c13521081c020748450300100441c44102442961a4003a100ca40c01141401c089140c10000140320b030400d060480c2e40e4248800010f540904254003101e070480c152001ca0f02c41000030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 317834505 1250 317833255 317833259
    0xd180e04030e0f030102070f060b061c05070918090b15010c020d020307051206090d0f0906030c2309131b050306060d180615030308150307090f020d0608070302060301 73
    0x12180810b000700001c0d404445007481c000655030070310050240600c42c400b5203402c8070040c90400151a510381c00c4502c904820304c1502030520011070440007020001c40000303026030b9540000e94003401540c008086101d02038000c6045403549900440b5010b000740c290144545d510a10300c030401600035400c0d0f000a1400800c0d40060401d1910714a0088c8001e058441c5640c5801c04141070105400d81d20140b0f40c400d00134030034404018801459211aa8540b20f4a1001c40000141c210000381c4140b0080568a2a4404407d407048690440e0404c40c0b0a603280506032030034440c0c0b585d8001c0d1002621480901003000301441442c49204a0501c907800e06076881d5540240c1903c803504000c051300d801c203c040205d020358604511070310002e412082800c103150304050501c8000c030340e035981501224103103980301440480e0704035a030160700120109449060f81000030209043c00815408a101e003400c215184451000b00d0300a090001c11a400800440d82d0fa810002d6507841140320182d0065010801 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 317835755 1250 317834505 317834507
    0x6120b09100608180d020709050603010b060318070b27090f011802040512010903120b0913110306041101021603120c0507080303040f0c0b090f0603070e040e0d180e0403 74
    0x3c560790182036107070300b110075900510841c0e05012400c084880140c22008052000c00701d14842c0d0340d00103405a008120310b54840000c1600340c400508030300e501c5d081009078480741200410250001d07040c020781e0306448400440741e40c621006480003501402003014460300c4242440c44c0120b20a80742040ca109441e441d280486507400c41100469240301e07020000070072291500d41c240c031000c0a07040300001e9081c00341c4c240149085c0c00c0e89500724090b4105101c81ca0320380c1c3d64a030700c9900480d40d0400760007003280e14a040504610b05040741500341c00303150100300c2030200c2e0400403030027840f0a800346d0315000c1c485030300c1802d450b2503800300a0040d81624501c5c1880c510425000600354072403012101034688031009149150400c0300e003192030b4050000e104c001c004560b88840001c0c6580c0341000e0030303c01c803180003032041c0307017040c0d8683e008120100000d107007284504851401d001001c4e00c1041480e021000041d02d0350701035a601170100d940307040340c0000d00001c07a15005c111401030801d0000c1c1e4496941c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 317837005 1250 317835755 317835767
    0x90302061f05060c030c060c030403051207171311010309020105070b0c041a0301060f140d050408130b0d0b0f010f11030d1a100801140d050f0706120b091006 69
    0x1084940d4582511001c5030300c3e01c0314030040c20070f201a00021038803002c0d0362038180d02d0100020054840202c041c018030000030741000982e2410403200d01c8041d1280d0301c41e40708840d10400110060800240402031240070501004a00c0b0b0103405100801d07212154200103505a03402100000d0014008202c1100400c10b1510079603000944003070a1450503030340b182004043d20b00c4000002d80d0610010040020640282d088060400c2d07508000200c154245a0482c0310f00680302c02400d45a01e9034000f4082041c00c0c41201c1418081c100107900103925400381c0800c0c0c3d081040251201e40ca0b00f0031011452404d0718641016003816560101c100d0a0840c04940084002654040a210510a000110800c0d001c2d018060159006070701c19020b01d41c081140d80c461943c00c0d603040c80203541c0180003980341e4042c08501070030140d440c400301100520f080d034549207294048060314000c1240101d1440da00c83c440030707030026141d00b003440102c544c2020861072103003d41e4081410891604200843d0340a50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 317838255 1250 317837005 317837041
    0x902030a020402030702060702160303050301060e120d030204030c0905090c10050d05160f080702120c0705060408150a0213060807110d020f0f010b0d06021b030403110a050409030206 80
    0x642524014040e5901003010380e00140c030700c00d025070001020041c10702c0c3e04120010a101032090039082641c035545016010b80b106005150070420f1602441c4600d40303900030f4111002500c001100d0342410040c1c1c008009402500045650321108100050400c076640200e80c000d0f01c40c44090840c10304040200b0080b90021400d40051240c10300290800c81e01c05c1c80f0700b0b8840c054450780304500081c141c80c001c14141d10300c0241800d1002402c01e00c43d4a5600081165915070030091042d600c4d008546031500e441c00b41d601c055404500064080b85108000c51400c08061a084035252980c440c010118240e001c1d250803562004010402001094802c00400c0d0300004a800c3c0710f0490200070048a0808140700742d40b101591140210341c1e8000c004000b000040f000100080020b611540005241c0101505010300303401d0300882c0748250b070061301841071480b001e040110380e500d603520300c2d04400300640031860b144240135007070300010b440c14140113055a90b68164044c001c1991010f41c56100300d5004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 317839505 1250 317838255 317838259
    0x3111b0a06060e040b0105100c030e01020703080d061403030f030403120b060a02010b10110636070303030f0c020a140f010f0b0306070f020a03080a0b041109040501080316060902 78
    0x380368000c01141a900c580d4015100d041036600042c038182c02c003116403580c10b90000340151585d0028401281d032140c1d00d1a00f96601d032410b0705154440000407813a269241c0c0000d03041840c00105020500855404030080311220050920840340e08820076403030f4041e4110b541c005610400005000a21070210186003101107c1d000603044042004107440d500000e080d1000750b03540746148546490f011038000070091a03458102d00703070000360203200d4442802502c0500103011104004900b056035051806000c40800440b01c030311883d0345120790740c5841600c01034001c81e1a0081c201e00c090282e00038115400016001803241080d91b80d5801d8031002c0f1182c020b007035805800c4407514589000e000d00480c0c03070220000031a1520811041508054015041c901804030703500c1c000e04090b030045901d80820750141031001032036a6244240c00601128035003964080d10705010300f0080c100c204080e0035995000c0e50100580d0384c0350400c0c940c1d28440c01c1c617611602400b0019805c001100382c0c0000001501c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 317840755 1250 317839505 317839513
    0x2406040f0e01180b070903081c090f0524190504080c0303041b0b0708090f0d0c0b1c0c1b0c031a1806010b030c0a021005070801051002011b0302030901150f090c03111b 73
    0x102d40321804807034090134040390330303400c40c2d01031112824580e1034500304096444080740007820111100d074010001041d80c2d020480c2c40d00f0000c0c051021400c29a20060b071349100b41c03952841e091518903210104444803940000c16100e02141055100007600c01340c1d5440402c281c60180407204008141c0d070b44e050070130b6100d140b4400083c001180404404020203a03042c0d00b60719222448458003210104848440352a4901140c20030703419404158403018003c180b150710290003241c10003501c00c1d1aaa04003400a283c085400100c2c034003a603d02c0c611510380c400e0200c005169040c1c0503600e0b880e0030710070030b0840402070000c510441e071020002c0c203d000030b90049030401c80c98803020000362042201c0080c0824070038801003005080c90215a02c4941303c6100030402e070030924900c0c1e043c80b0700703000648017055408400078003162000d43c0540700c020803412003014072603a18034011140c003803603001d00440541001c8240088502a002d81c1a5040b800385c07120f801c040e8075074070101d1170318052450030201d80711b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 317842005 1250 317840755 317840771
    0x40b040e1303200c0a0306050115020a0c090917040e06040e0312060609010203041a0403110d08040b07110d060504030e040614060d02120c0c2406040f0e01180b070903081c 75
    0x41e428603040006e5201d60f00c00306880d85007030303004416416527075104415500081e20050008d406e45041c131080d54a035a50004d000784a41c00d04170740064019895000c4030100040c04500181c400c600c59201d580c081b60b061284031039500065480b4061241e4000c0442c1640340490420b14242016241d4030300180704803401c099688541400d1045042074011503060001400d2052006182c01c50700d441c90266401c071180c11040c1e48031541441070703100d4000d4001020a03154100820703a0003003900e448009000744c55601886c140307680200025201180410f940a00040d418103150003400222031068030302c001d80c12020700500101c0d070311100c81e9000c038075800c02481300440302000229010300d002e49031040d100c00c40c0d42500d130300d0103020b118064a1440e50b00f8150300d00700c0d0143c0e180c030350004050b9008200131290141e480064058142580a55400c0c5440280c00c4840b241d0319000e420301a50191541e41c84400082c4c0b820b8000d030201900310001042021607880c283c69001041582c49440010245 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 317843255 1250 317842005 317842009
    0xa08030703031a04060e0415020406080106050a0c0602031e1b1605030c190314030105090c0a0306081b04060e1303050304050a020a0f0611010b010906031e02040b040e1303200c 77
    0x40b0a0b0b000002c0d803505040c1448244008c40c0044285192138260131031415080810240502e03074148240b4041190020b85c0001d09031040132807401c1e80d03a0100c07007952203081050503214403e007041900b51202400354000740005820710041d000015071800c0c0580340419a450344070b1101c800c030f0801d545d00d20041207000b00360707801000840750440c1e044c00100440d00442c9802403034111000000345da000340a00c0180328a540d410b05041d040f10040034540d6407000e2880c000d4010340380a90080384580036200c0016800340038082014410a0b08450400c42c290721500107000941d0140c0381100c401c000f403060303030300024000d000458103d4050300440e08505a254001210340c07405e50080d001d4010405d200300a01c58004030101a2410501c00038000c070245040001e244010500c00c07001015202d202081c004140c000d601d00707a0515803602503590315103610560710141d10600c0f03414207030700303042000904404200440003007960389036640100c28807141508040c1082d4410440c501c5000b88080c101c16a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 317844505 1250 317843255 317843261
    0x60f0408060703020702190e010e130606180623010509031509100612030c08031803040824100302060a05090d0c06030b0609091602030702030a140106050a08030703031a04 75
    0x60000c990f00580e4038529481840000e5904000241c1501c2540005020010410034558155042e040883c0441d580b1a454030351402c004c00d02c00b4001a02d003480204600b085800e186003054030084d420303c540303556035202c8200c01402c00300030004007050b050401c55540c4680000e25a00301d0050440341c8000d10240da491075103a0075107442040b0307803000c034000e0040c4186020f40340050000c541000080411520090070401c1ca50030000d082a00000c0021601c1c03402141100c1c9180700002102d4a076034603618116540d031f6410070501aa264010b44d54000c0310808203030140704e4403000d03200d40c101500e56800c3c4406900710340b00c1e1100f8080d0500025080fa185e800c242c04881e80540c00c940311051034a1405001ca600d88101d4900400c4200f01c0ca01086d1150009617410807000d010708012001da1490480c103500a1010084d0305026a190240c18084810300b4901110b810400030030416a42e0420056884440d1149600701e40051042c1c8000c240641e121403499861500940400f116440004080b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 317845755 1250 317844505 317844511
    0x1c0503040909030305010e01030206090907021e16080304060219030c17030a05060603011511010e120304050f070617042d1a09060f0c190e04050601030605010509060f040806 76
    0x3003907642c0200d0390a05626008090040003101e1115540d5411a00810281d1045001443c021210100450311031482040124048004050309002d100b403451001600c030b003002c8041c0c50071148420404182c00c00e01200319002c696864001703040149085030b5402e00c0822040c0154140803814001c00080307030b0040700006c158030b60381c042540c1d81d180c07800a440895038050f110758050807050006200910122811000f100380c14201141100340e120030a5002d01070a5140d10f400d4000d165500c415202c0d4071000e10f014500c200160703543c1007610b00300b00c0c0c2d403002c17940b080000089030720640c21801041111500d800501441c101090350310140c0d041c0c43d10890904640310401c800116850910440641d00850164a240305034030604080c400c0325600d071009850042e1580400f408100c4e101c100c0e070200d400320101d1041d1007018600c01440074005000000105000c0c034103000c0024400e603c40e124113001d42e50140c55440c102100381c42407000304c1c2c001d40d0840c51a400c0400c000719104d1001c1106903c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 317847005 1250 317845755 317845769
    0x206010501121b0c1b0506030c1309060e06120a0b280606050c010f020306090a1503050607030203011d040c03030f0207050a0b090a171207030e120a051213051c050304 73
    0x7480200c1c615000d17003240d90141d944c030707500e0407950024401e941c0ea010480380c101c6100781c140364403a14400340d2041501e12591220710150f10b40b000c0026142a400c803070a00c09e40f4110303400f0070b21a1404a80036100c90051078000c103000305034400140310220300d0407d10f411051010000703000e0080404984200e80c1030750040780101e4000b0821180402d424001c84510198001d010740c150700b4154045031058001500c01c01c2e80075110504500740542901e0072100075504002216490300300907001a000790710a0151b100b030300d400388801e4900d01c440701400c907014a500c040c01c031034610b2640c1c40803207104ac40003105a045002f00d510014046d95845414400f9054805006940306552810040d6000c0c0ca544400030b61146010600700c4218041036241007804c1c040d2226584042c0c2d4070382199900d0590700c070b1940c0705044088000768401700041c0320f4944c2d44580100c0d100c0344540303441002c00340180c2c070000c04241560380c810300043c20488802c06804c05581e070300700c1401600da51100c3c116001504404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 317848255 1250 317847005 317847017
    0x11091008060901060635280c080718120b0108010f0b0a0b0f120423010e0a0f0c030203060118060b0405131d07080a1703070206010501121b 61
    0x1000c003440500501c1c0e0045480402000010314240f000341c04600d0301c0800c0140e80209400c02c0f007403c10191030501c0c07003920600c1018107070318050800d1400c442c0c2a0400302e0031052480c0c40003c541440d840b5a95004040761100341e155664410103c0d41141e02c40f00d0146007101408000401010740d0742c607101ca551144490301000d41c144840c00b801c46d00c05001200390f460406640300c0c0e050311911015400e45002d101103c3e9a040078078079034802440703001c4103111250008000c2205000702d44941c116500d1150b4480583d10040b100c805090710486407484a0b10741005494038000f640317016500e500180b060702010100d40d525000a810800268000b40c8508103d8a021035441d0581c4150300107060304000392410a401e10021a000300140840c07151980d43e684401e1102c00d8044c4203a640c0c1078407010489114035156844035840e58a030030f108039409990b034581e26501c0c1c5070010643c1c1c400d50755030b0300400d46a840c00004448041848103c00c60096964022000a07841100c074031041c0082c0b62118 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 317849505 1250 317848255 317848259
    0x1a0315030714120c0109050d0c080d0e04052404021b0d0e0109061701170a060f0b1305040f0f0819030b1807090b180d050105070e03070f12110910 64
    0x8001e500d503800c0c00503c0b96400c130b50704a40c1182e8002c4444d80c1900c0041c2c8000c0490354152034401c4040c0181e801c59005846041e1a4119055005c08494480c0d60261014002c9171590311031a1941c001040c1d480140307040091641c42c103424294050801c50050700c0d8450b410300c0000e14102e0822401100e00c2d0700281400b0a00e541d503507000f4400300003c1c95640740141c000341d1604250b00f00c210040c0200100c00201000c03580034588208584040390ba0445010031440c0754144450b0020003060900301d004054007401c9102c030174402d1003010310468010001c1d0040b10170742d9130f40c00804200842c04a50165041c004040412540741d0345121048154400040c0c6038030480c00c101c0d44035030304260030020400d607800700210543c0c40031601c030032905010401e0b500c440031841115100c09174990110303000030510318000e0600805401c03031800740c001510340c220750a201d102415180c0800307005005001010800401200e00c482105154860284405000390721080000072400701041d640740c580a0500c04003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 317850755 1250 317849505 317849509
    0xe150301060b030408031f03080c060106020c06070515060303040e01030c0f090207050a030e13111e040503030a120f0509010c020d0203130b2a030703090801061a0315030714 76
    0x5800e0141082c02c41c16802d51601e1343c0c840e4000e2000503c0007510060340c13100100513251402c81000a15030000c0400e0702d40e6034880c1c0c0155551000d10414005200e8400030600d103040c9002114000f0390442c02420b8007451a6211414000004d0715036034140c881000001140691807405502840c0b05201c88048980342c954840c010088642140400314410020817000038800644d03401c0c85541400c00c0e00307600895074000348507004000c40040f152030034050620303050f141d843c0c000c106072043c00a40c581e4194106842c1000e41c0a9809041d4045e4001c000c1c2603d203070302564846010060710040414108541e0000d0344c141c5a094401032002d0791200c2c02501600c0e0144018510390390700c0d00c01103041210450243c0344012591154588050300003540d0501540d20039066a5407030740d01034607032550b0714151850707507500c0d1310210068000411810010a4021042c000c0a01325451041c3c103800102032200c81000943c40600800c9031901c03141044800ca0701d0a202e01c0703000f40541c0100700650028001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 317852005 1250 317850755 317850761
    0x408070b060307120f020d020411070c0b04030302251206050601020c09060603060111010e0a0308041a0c0414031c12062108090310092f031b04060e150301 68
    0x4038242c800e0704856814002a542c6214141002d50491350b20408004c49001040c01100400780194000307003411003d52000d40c40d0030007007000d940b1900404c48015640c1c3c0054000e40905d000040040e00082c0c083c01c440218681170652061007817400c03401c003954500328084010007400701103484a4680007080140c0da011310040d9180c0c0000e40780040c15180030030000c0d01620008000300c1c18080070000641e065030013580404209020f240860f40500d03510b08000d0007841e000c6604455643c09980061240f08240c0a11070043c244056802d00b80360402459002500c0c60750039958152140c2641c01800289102c0c0e298559402d0342c03a04e035629110b401502e030a0301c0702500041a51500d51406800c00c442201c00c90500540040c0003a41303520785040001c3c20b01c07424081c09003866051840c920b00b8042a01588c06510900b54902007045c3c03009000c400e0500e1459040545c1900725043e44140c008504106901c21800104002400f03030f160124650308003c1901e40c80620000302d000ca81960400f44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 317853255 1250 317852005 317852011
    0x1801061d0105130e070207120606030b0603120a0815030102031602060601030c020a020f180108030406031b0206060d06020c0d020a0c1d01060309081e0d1419020715050408070b 77
    0x1c0b070180d01d0442d1114034400710290034032a81c08185a0400002c40003403003400b0300d901800031089a00920403240c207100c0701521040c001610307030b03400610108400d8070b40010b80000308042d01c00c0a9040c01c480c2e050a580c0708900500019060002420050713160f5000c0c0b004500c40c00b16079030451200e0070004030007460404000d04040c1458504102241200c2d000143d0790505c0307504441416503900032101140711500018042c1901d0720081001240c1e025000c070142c0b040c0c1d03606075010011450201003000e00080c1440700440540c0200c80400d0450401507007086805001c1d0348050703d01559407000b9458283c80145500040c1c0002000e0410411a81016002464000411032002544043c0510206410702c074403000d040c0c1d1340e070050b8108658241a2104018251080a1900c8004d040320340c0590011024100b0b01c3d02d404400703140c0c9120544010301505401c42200140180b0891510080d4804603068488a921056a41d0003a00382e0203040d22452096684540390440d514100035002405 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 317854505 1250 317853255 317853257
    0x15030e1b010c060203130615180603080a0309051606020706180b0901050d060b1c0513080d0c11010e0a120806060a0e0f04050c0310050618010305061801061d01 70
    0x1a0a414000e03a900c55441a0182d401480044c0d80351109801050451100300f002448241041000c0c0f240c0c1107440f02e403030111103035900ca50301000c40c01400d02c4101c400c40e0000401e0004103101140c1c0140c400d0f4000700c22140b0800c12503a181101011762050782c0307842c0e0303c070a0050b441000248221584600c0001e000a10200c11400381d905000125038203001d802030081c1044000300c1c3d039096105980d0000e4000f006000c1d40d041d540e403041401c5121581011080b115003a04180204400701c0d046011540440d0b0401001c600380f046d13088100e8080c00480102c0001c02580240894040c1d80a01c03c40000340c140d08000c06072906149020046d40110788409002e10a40340208403040e11a01c0444018102c0c03032609429584003800042e50340c805c07859040341c00510f413004005100300c50200a40c0200f0100314190390203a80c43d01009501e201e40b800040c113900d01c1405802c4a94002d400103500070000820410031080c014180d8440100261311150009019140c803441c1001150f84000e51f180c82 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 317855755 1250 317854505 317854543
    0x9061b02060c07120513092007030e060f1b150705040e01060f0306090e060105012003040519030203030708121303020c09040c080d021608070e1f15030e 67
    0x801c400d071210034010043d0151403101621500148184a1005c589004600c2d000340c000032916480c2c800c00800c0e0320a800a08600e6844110000c03841c020241c4081c2d9031b0640e50583c0070a00340051081503004900c4041182c00144440c1d020210f11039010071492413080000e201021203003640328042c202c058400320900c18100300038412100141085819100c1a0030030b904040100c06084004240301c0d44034141031860b00c42d0080741803a020650341d040f22800d99501507071801000480341d0484a101c00140e15a00400040006044c0503940c0c1c2080b004012280d039420380d50b40c0100303003541c2c002c01d0104c80e50100007920340321001900003565005800d454129450103201d50f0042d5481d1100c0443d2481681500700203001c0080c400e00c8003000d410940c054a0403d41c083c50082d5031110b0703a00141d01510755a62011661301d01c002000b40881e03d0714008000c417521980c990540d1130690311504040700070040320214114510384402c10700c4003a250350005060504100090600001c044d51609a0714 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 317857005 1250 317855755 317855761
    0xa0e0609030d1e080f0f0903250c08300c2d06040b190e070609050102010e01020c03070807060b0306151206061516020901120308090304030c0b0d0f09061b0206 70
    0x8852001d6076131249001b00c120420b40c503400c07106842c5024903003c0300c94004035103000907840c40c280094490202c0c403811010307007140c0d00c46500c9030305c55181c1c0c041d41c082c941204800310726501d0151400c0303070b895114000700f83c41c0ca142d1162a81c185294404201010072100c80e00c9400841e5462403180c0d01103a042c040c0071a8182581c590815540240803404600b0b841c44400c002c40c4007607404042444440411900440ea84123005092152603120b5207016508c0c08445403120351060089803001400800a176251441c035a6a07100703a5002120165001ca540f1391041203540c904001c4140121003103980048020740d0071003000038203c00d01200450300c1d0000d0041c0403091302c444003903800c4442d0040d0000d84404081c002d50509100341e90000e544910103c0001840708040810303181e4040c000d83d40c445045c0d81e40542550f0702e200b03502c002400c20710f0000c0c08104031042d10f40a020404680d00e40490a40d4107284e8440c2614005203007940d01c41d0b82c0318042c802d07500000c9004961005d40c0d00181420707113 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 317858255 1250 317857005 317857021
    0xb012307111f020105150f090c070c1502010603020a061706281508010f0e07211a0906030106031515150c0b010b0306060a0e0609030d1e08 61
    0x40200c00d4024a41e008a5018070080d544010b1000c6059601003482c14038498008002406840152050b5600d2614240d00d4400c600780350081c11a1f141000e001070f0b0700b6480d8017406120581c40a14242d6400e5003046002c26040c810883c0c4040007146540049036039811401045038461a642c08003060210640048082070000d10342c80b5403003032007182c8029040342000c100100d00d8000004003480a114013402040c9440540c110301221842641c9001d110f070303212241d1150803420741c015402e0b0a00b0500c00126414800e09600c0440d01480c010b4413400d00c1c140120306c040d03400001070b0b0b40f060b004210560303019060100c03400e68800000c4000f8444140b454071307443c1c5000c0c0d02c48000150300340c0300c0780124100d180d40c0e04824010710000305806144000f50300020600709030803008a410408200001510214480c00d40b4000c580041601c1d1a00c21000c2d8292042c400c41060103412140921030041c8a035014021060501c0494641c80001e0391400302c402c4200601c141824140f0520b001440410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 317859505 1250 317858255 317858257
    0x81207030e12100207030903061d0a1407030c06050717091e0d0f0f06060b09060a050a030905030a09060806040c050403022206090204181a040b010908100b0123 70
    0x950a4030601100a404000b042c01d0084400c11420510b0001464804042d80103085c82c0482e4000c4404010b080d100362010302c440090711079201c80652010158401250514020000c0051060104d4580316500d54681039241d2041d8000c0021030030200e00748050043e400820802e107801515407500c0d09a0800005450908809517055102003504600070302d0346900001d40c0c1cbd41c42d040305140c003045140785800003920041040844d20281000b00c00102403100005444425000511701c0d0305008010204488035000000a1000c05485980b41c50102c1c0c1c1c1800204014885a41c0d800012070410320050300d1404050b11040c011460580540b5140c0c0d130180035101039035411150322076440007006441d4080120224500015440c00e100000d1090150f4014000c841c0c1100c0011144020b1801e9501241d5481920f036480814a040f07007030b040c1c6016840610041c5050401900554403460b41910304404548003115540d030303901465030691707041400c1c903818901f524401d01c0e010014641c44015 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 317860755 1250 317859505 317859527
    0x50c0103052a370203040305030d1a1011010b0a0803030c0304140706020c01030c031a060c03040e0411040608030703050406050a03021b0106032a03110d0510050108120703 75
    0xc150b4404000c084450320b40001c40d03190299a01c840c4034241c01e055192401c050703103503040380054081140d06034246800881650200e94202000c0c6040c8102040503402810140f02d01c81003121842241c00f400f981c1760a40407012010070f940d500e05200488280508654002c80540c3c070440744120308100000e00007049a900194580c0010b44a484030700d80240b00322190320900d405030240d43e0001c9902d95000601d43d000c040c0c00d071b034240072404445e1000e0702119040010280843e01010084440d818084020007411084504481c0781c45c0c0d80b038090015021040c2c608644540810107543d480b07250502440d005807580c42d0256141084a960185c214810351044e00309000703003c00e20042280c000e90568084202108202c08880f02c65900729000300040e00080f00ca4100d0251201c0c49a601c00203100461031003502101c58090454940b00b021035064aa410340c8410030b01104c800107481030180b04184100b40c4c1d40810345504024840b410708600c1040204c4d5048207101d40d4010a40c0f00e2450742e8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 317862005 1250 317860755 317860801
    0x504062412020607021903031e140316110d0302090301050106020321070e060714100b010f030f0221070f030207020d03030b0d0c1d0604020405010c080f070519050c010305 75
    0x40e82c0c0044d403000c101c00c0010f02e0b0080f9110b418540c030000c2450340090115400c81d042e00301102c50102211800d031140c82e030540324000e950005100181c032004600310440c210440500303142601c42c5000110b6440c1100c940f01303140c0043d40115610b6504d00b000d0055602600c0240007a600340001e030440d44004845046401d421000102e0214141d00e0180b00c203050540d0025081998071001401c0030101042c0e0b000a41384588500070030032184d100c00303204d1588118816521150f0001d0b03007500403009012002c4404c4a40c0d50300f04441d045400315412103000110403040c0080c81490705441c007801043d0400990024540100521801a510142c2c664111680750400040030101c640c0890084041c88034010010a6518000300b001c01010005a603c0703402100040816562401400260f00951045c1c90204100043e441c00050303c02d03020b0b04c50200388001e44d50034601c003034848601d07041c0c642d504114080011080d000a009040c80140c3c074a84084c2400c1c40a4180791440381b00d42c80c0d904440d58 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 317863255 1250 317862005 317862007
    0x1701060b0406360b07030e03010510091e0c02010605010f0813080a0507051f11070b0c0309120708031009140a0b04091b150c03080115050c0105040624120206 69
    0x14003090a450f540c8852440980903a00d0300640316405442030f40c1c440b6505a01003011300746108201d280502903a0301c1181c117905808021880d00c0b20880241c164800b881082110403810901410b0491058038010402e42d400410f660f40b41070005007611082010440170801824104908840c00012034000682c9c05104a40c0e5008181000c541a00500c4401804c80c0100500e500707010b040032403900c0004048003420050700030441c1031000070f44034000300102103042c4e41e4002160243d01102859001c0350441c240c407414001c0841240d8550f01915040b01c1550002c01800760f050036007040c0c14050b01c1d8039007040054440c100760500d0014001410b01000503141c05071040c0365156074004060130b81d442085400300c40344112003d541000d05006d0f039030310744900c1502d641410344a400b0f0045250b8054503011b4090f401c181120401d480f010600006012003044400c600715024401c541c810f41c0140070000b01003007411040d000c5050007400d200c4070180450028803074142500c10b01c40c0f645a040f2101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 317864505 1250 317863255 317863307
    0x70804080d32010902040e190b031501060201060603061d070e04020c0c030105060306130308070e060c012a0e043204060506040c0e010f1202041701060b0406 69
    0x100c0040c004032100d50490960440b00c5081035245003201400ca003a4070011001c60341e0301d50a818089014034404c00800d501c0d20004245541b01018101014542e440c4d000b240c3d0000b0000868900705c040d0100d40c80181090004200d02c80c0d080c401c0001810507450103110851500000115031407030501d00d048802e40d0b050100c0c01e580d0080c44c5013001144060025500e6903c078120450300c4004030500359020354200380005899142c003042e55442606a0040c039041020b090f2000c441c0c1890080c1480280905824442da20342d54007000381c40031603440d400101b12405d0b100d014107002a02c03083d1004c04800f034808001c2c0c01c290401e071100c01c100c030305440001e1003d66000c03082c01c000c4d00740d1030500c20304060070841941c80c000420300704d4810f60080c1d805108940303c02061004a0b035010059000190044038042125072180940139036903605490074104d90412000080d040360b00c240d01403402028040b6840d02151070078003a240081a0140d81a03090514008000e00b581100b03049014000d90040300c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 317865755 1250 317864505 317864527
    0x20a0e04060602030405040609021228140601031b0504061206030c03120206010e04020901090515100e0109050409050613170c3702010e04020d0e06040210050307080408 74
    0x21591a1000090041c00700c6995a030000c1c0d243c1d80940034050045051404c08504010507000b16040c0e80145070115806075658009660740310b15440001138410780c01c43c0c4003c820b07041c60013180059030040d1010012410042e001500b1140c41c60404c5800020550196480d0f6400c401660115010f50500d00000d007214031000000b020290001000109a03550200a00c5454207412800c900d00d0740072a441030b601c9a284408171f4078103d030001c1d80004014014068179210f45c103e00d070481864402448029101c20014142cac0e03040b00701c103a000603541c407411000d43da80b01c3c20f890028003055404000007465038407010b4941b80c1c010140748203040407020711003c100c1c3c1050031200d009182030310359071034882018009489a10a100014201035103c01c0785a0700116400a00c1c2d5100c072141403c5002c900c90303801520009007084985510030f90074004d0119640040c0200e20180710040c01030300c0b0724509807041010750341980100404102c01401003202e520f400180c1c046e0003d4010380c030541c43c0d5031000c0c0c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 317867005 1250 317865755 317865767
    0x1508150907030e061026190317040f0605061507020d050307050a080c0606100c0605070e0a09020d11070201091202061e0a020106081209061b01060303021f0908040603020a 75
    0x303c21564492101041824001d02c0b0f01c10003600c100200c0350203415061180c0c1d981000c0c2e20880100540c200e1f001242031007200b0300300c0401561190400c0c41d4070340131445401c1841e000482d02500c48400d0002d0103800c000c2c0368465582e00000803901c1d114400c204070034041003070117191002801030704942c44031070034454104156500285d00800b1034452031501d00c0c202d03070b5039005002803542c10b1050078085007075032412604e000c0f2112402c1d41e43d000c40c240710b9101c1c01c0c05400041e080d00c0c240315081d41c842040b07440d44080100600640302001d607403040c024181310101c6402d41041000e1400511040006030303401500002181e1207410070490b00285800000d91b42d00c80c2d240d40300c00c01c0100c0205041c0c0560300a01801603d1034903002044030547c0e035104140c48000302d40114005090410000101d803420078040c05c02c41e807001d0309075810014410041d5003101c00d03a42042c0c0150b13100440486500c001007a0700e4000c1414100c05200c40b110555405150380a64001e603428190003040d61800c481c4990 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 317868255 1250 317867005 317867021
    0x12010527010609051e090c1f0309020a080321130b0c0c19021c050705040f02120406090b100f090207020619091a0c030a030c0212040906150815090703 66
    0x90f10410031810302c0303882498000003051800c0d5121000c440020382c901004130b050003240001510002c0380b40780c41c070041e11822840d40c44800c00c0c165541071250158803000900005002100021030392440f080202c2d1585403500c02140d65003404000030001144110034038a03000310307441542c0c00c1440c0c844915400c0c0074068003542c07804074400c0340d4401c109842e441801d801c260b8000c5d15010b4260a5510500340c6000d500c1030b001d002507101e0001000281059401f041009003a0742c4014204224940c051110318410703101512a00e4451152500b8003542401c12174214002d5034007118480e1502007144418003040c03280c21061540860410f0039034031401e08460300224000300816509144200c00f034050655802082c1118060446500e00307002484211422025040002d5080c00e41001045018005000c02c81086000f0300d030031500e441480c5005030000d01070b80c10010481034100b44c60b649010002c0d100803401c004181c02404003c11154113031152946040c0c518210300d544004090307000d040a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 317869505 1250 317868255 317868269
    0x3030e03041a03010609080c030d1b0606090e010c051303030509010e030607021c0f21141302010e06040303120f0b0d0b0a0b04050402010f11072102120105270106 71
    0x200502d05090b0003941d00441c141e0307465840e581c4100c2d8039018113a55540040300e03101d400d640700c0c0b00d50f0004c0394040c03884151340c2e0840040e100278407540355584100384d84640c0e20021040d030f200e9084a50490084c0601c00225400c1d2426900b40300303c14010260f00140c500c0080c00348040060b8011050b44100186198080080c00312085801c21000081d03481d400001c0c5440b40044501d000c910103032046207904410496070780c030b01d14a00340c48001405007070304044104298550b940100703440700c9a803403901403180ca084480502401b4003800007424594084100f24880c4208100a000094101d07400c071243c0359240c0d5001807440d804400240c0101a032004856020301c140e40001c003006600c00c52188103e040c20070034002c0c0307038050082c041522070554009001c506850011101148a05400c10745805000304031030352a69a20640e058100c55615095a5040c040c145442581880390f440e8821400150081005251801c0c038541c50100700c90b40361808468145600c0c00d416401d40040001d4088 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 317870755 1250 317869505 317869529
    0x30307030e030d020a0c1703130b06040b210706180b0304020102010f1107020109150c0803090c0d03080406141b07021201060605032208030f0406090b0103152703030e0304 75
    0x5208000c6e1000071100307021500c240568224100d4000c0f108142c074019403000c0b40c003403c1c400f125600c0d15441e000040c079882d00700307036030700c0c8150a05c1d40c81038507500c81c602824000720742185440500c5401c180050700007409001c000140c2c1c204400400c03a44108550820080e561a07464901c0100d015190003482041110f040910382001040200c0050804030300c00d0700c0fa24075581c1c0d20010340ca610280c2c2c14a410103d8240d021000225101070010741d071044821041d1074140882c040042c800382003041301030b00022401000c010400c689845450940072440030342100900d000504807850740c0016004081452011a40c80c0c110344420800340c20040c0c82e40000e011161300d800300140644c10864184584840240c10b803000a9208440f02d0629908118146e10f183c2d582c2c0a04105404040c00c2120700d103a9031010706011440903040640a14072584042900b40c3d004003545041d03032000c01c09000c0e001c5158140d2100300400d5142003210036810305010602c802482405400c2d07000d20380c418520414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 317872005 1250 317870755 317870767
    0x804151109040e12030c07020d06020708120a05040215090a0306021207021504080d0506150d05090f0f0304150203040b0a0c0615260f0a06140f0405030307030e030d02 73
    0x160102500721030809540c02c0203c001c6810000e0760350b040001d0366622603034040001c156400118001400018005080300100c010b8a40d80d4400701d920520b4182e440d03100104102c0404a000da106603000000c1240600c80744c00c00b078000400007410100a006c2103540002c140501e500d4200b0b409000719000101151205081c9210b079035040e1080b5078203030060280d50300c81c2d41038607401442280a01e03001851207050422102c1000f0040201401150380721b050300820101902e82c242c020007032555801d4000c520360070240040c5143c810301e024111150b4100f00d2600120480010540c0c1c00c58045060f03460b80a10380c10411b03420340c03250341c201d1000910300040c01c2c4046a0803408058002c0d1003050304001c051900700284000c2a024014120444180340035601a007400c40352600171b1203500c0c0305a9010b07001e061486c919203080c4410403165070342c4844002820180c01750309a5031156500c01103040e185081d6a41a843e8880100644245075940f0981207500508000350b40401004480440d079501d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 317873255 1250 317872005 317872031
    0x151305060306010b04030b0f0601140c032206020c040203040606080708070e07030228030e2409010606080c0313020d2003010603150f0906060f031208070f080415 71
    0x601240c0d418081c2c801c00000044400c203900c1290b04617030700081c4842c41a212070100d1801c448002c2d04090411000815050034110410020326520300000001c55444004000410138003202d02c01ea500c00d10a80701d0308015440c0c01140b4005800070031103005a40c2e03039643c502680182040d0300311990380c2c45900c202060f040b8000991506890021104031100e554581c0210181e01c2020302c003040d8007081409405001c071603003031a507401401c2801c002c104094004d84107440c003804140d0883c1401030f41340c1c54400c1c44814030380c200e41146140c8000c0c062141850000b500b000780281c2410b00021001001a1201c48807142d1513100c50383c01030502003e1516030038400901c1a544006030111080f242503580e240c42d0510840301129030006851143c0d004982d6000c0061200784020300c00c554882081200084040c418a000741070b62244c80c22103035042d824505205c0c1c80c050040810f0046c2003040c403c2098104600d008800403606d0130780c00d03559032440c1142110072040300c0001c159051140b200841 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 317874505 1250 317873255 317873261
    0x12100908071506051201021303020d021f1d01020f120f0d02030a0c0801050d05120c010e03160c1a0f130503010e01051617160908190605060f06030f1513 67
    0x10354040b916104030b030f190303003807091b00f00d1051150720000218420300400c01802c0c64801000c103140014000b01c03824a020103200250f0b04505451300000307112120543c0b44d5810b14540c507005041c20310040a00c0350140c80c05656904e00c0600100030014003050041c82600e460f0b080320111900d8500c299101d0030544041c0024000300f00160700032074019400032940341841c841c44810150080020a01c0c6000004a80d07c3e030381c080d44c4246859520b603d501c2e83c0118003040201550001c41c040008404854100914502044d4100504102e05945001100861303801500d4000740d41038807859480c814034001d00d420055651200b43c065003008144841d44006500c520311842c4001488400e102056400300c40100503240018201072584001c00e104410f002084a042c0800e81000b109641c1c45041c000c1c644040b0000e00c11002d01e44850000810482d802580d402c141e054803000d81c180101130014005001c0140038808070f102003000500a00c001464100c00c0745401360640001001e042d5010000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 317875755 1250 317874505 317874509
    0x9050d081902030702040b0d1110020102040f060c050105070e0105030a021c11070b010b0408031c060f0816051512040312020c0106050405132a0e07090504050612100908071506 77
    0x2c06c2c1c1c07504885920340d0030090300c4103e80c541c0c050f04030f1101c049a84100110011000c0d03082e0119035081c00302080c503100036900310300074003002d449e28500c0c0c0c0703502e1800d24217441d8001d205000f04030140c001015266040340c280c3e904080d10303000158680d00c001040d10000024203c5007007901c0d091034081502c0390030990007460490b00034601d09009a0325141c10308079a1040c0d20903030802d03078400c2102c4065000079110620b0740d01150f07503000c40c0c101e603921415011604075420000c041c0e04158040e4083c03203903801c00303000104030070344140d0746100c014042d00d40c00d4020000003800c0440706c5000102014454194109072480c1c0e0781e011912035052100340d074000d1540b030040b14051440c190104007040c0c840c101716100e450340400b0b00003512241e2000907034007004002c404000300103201c0c40401d401041c2030880c4c0c450300541e03075011412864002000191200030780413500541503420400c40d00300001c24003c410140800f40418210000c0c500350a15200b100c078081c10040500c40754150390601c41d000481 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 317877005 1250 317875755 317875759
    0xc070b071103070b0a0209031009020f0d02030307140d09121203050a020c060405010b131107080a2a02040c0c05060f0606130b2109032704090b060102060907030309050d081902030702 80
    0xe400741c0c0c1a181c0b02b26521038170042c1d400f40c08401d52030505c0c5031001100c0902c41c8040e09403070400c040395554803040c002c010101c502c5504240204541c8a60000c064001854022004400c01c0c0c02511640081088890070038105600c0d0000116140c9064040b40c4481d01c08808a480d503140c10f09000e030090100c600282c0c8510303c606111001f040540c0140e00c1410144000d0714a404406d0356510304a5001c1c000240600c4440c0b00e108450000b41d00008848040d1302c0d8244105030f80a20410046445040d0701c0c500741b101140500c4042680000c0c010f80c40f07001c2074030030b150a8890100191440c020000890001c08080c2c1c40410000404005880d0394890102d40c5090410b2038542140e14070811540c00300140d00511003005441204001d0f407101d0f00702600c81c011003035114808502074812262056521489440c180011075a04219280e403000701d080140100d1415590000c0142000d44115441a506050f2110501c040758080b00c88040140281c2d000030140c09402a440ba00409802c0c2c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 317878255 1250 317877005 317877013
    0x5100e090a020c1903090302090717060409050c0103202a0f100b0105040509040b07080f16081801021209011811011206090c020309090c070b071103070b0a020903 71
    0x40c88020a50007910143e01c444006410a281ca03d007003e010100056000d41c00c0011656001025882d15500b0790f00820144da00e0810205549142d00c1007580040c00c1d90b170155141031540b0b0049400800c152240708002d01e004100c522b0020340e000201030290314003c81d0708200154403210800540c00c0700d206650f4880c031034803a20707541c03450442c0c581c0000c44e6424243e411402241115a10541c000c030700c1020141851030515480e0030104402c0d20303007290100c800f4929031060004454004803a0307603011200669140d210324001440258201c0a03040060512505c040854580400c5480c800d0500b0340c0d0400854a41c5010307401c000c00200d0589140c2495444d100004040040034640d00c61820f030413080500c00420541c00454144404880500005607601004107a0000034040c002486da210781c0215100d941020400002d800c001d0002080c0c52802c006280009401407481d542c014454149041031143c210406401d6206154004000c00009000c0010313405aa50280000c0c032010b030122 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 317879505 1250 317878255 317878261
    0x9060c112e1b05210418020a17010513021c020a0203190203030606071e020d08031f03170f0d060e010f06020a0b0a05060402090d0506011e140d06020405100e09 70
    0x418034550003604043d0580c0c00001200c150707280000e0383c16150210181516191656502c002c0c1540c090205280c003401d070300003450007034465208050006052380b603c100040c9514050004411080b074a0b42c2d0044a600400c0b096011f03a05032403a0310542405500656031020300d160025105d5001001c04142e0780c0300340411109040c400800c1e24802d41003d0911032800300582c82d20006000d08000307a19644641401040068030b4240105581ca4850b446054803806c014141c280b103034049440000d082d501800c000c0010501042412040143e203054643d41c0d4030b200c1810000a100342500d40301c00351300386400002d089642c44200c81c12510081c3d008078085803150130890b06d90f0395000010f01003000e50703800b00d124044a03034003054004e10000c0c8018a40780ea036502107480c2d03a1410740c003a10150441f000402ca0501d8815502c0820906000b02034400307403c0052541c041811143c820740103003008000d10042200c1d40d030480b03000e40380003450f214141000041c0280b00d42044400a40900c01034004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 317880755 1250 317879505 317879537
    0x320100503040b06040515031504030311070203070b0d060b1201080d050c030307080c21090d02070305060403050a090b030a2301060207051302040306060e1609060c112e 74
    0x1924051680f04a406402e0780307a00702080043d000c082c02c90041c0b080040d101d080c3c942c1d010003039120010012541c480f01c1d46020300300502200c114401d0f83d01640300c10415540142d4000c10749200360352000360740d41d455641d1820cd68001b008582c0255121030b500281512421064107005070484550034110b40c50042e2080044a003409205805040c03580300f8001f040555000d102d84c242d02000c104880350501201ca5403240d1103491081d104000d1400b004c0c00d0102e8400c0600001e5401051400104422495551080c0d550040100058100800401c40400681c40b0f021107100a102c8880110f8803400d0001401d001408000d0302d03090072204217440040090102c0010038129a090b402410311646401d044c40400000e56085011a6500304004030000702c80f8407620f00600185100b1400515103203800e0024081081210014400f0700a803c00940d0780c0007103e840b40b9a40710010488080641001c500a5141e5101200c2d00e101030340c07492200e0001c0c030044030390710392141d540b000801c50f40005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 317882005 1250 317880755 317880757
    0x1509080708120706091a0703150503030a05031b0705031306030f090506240a27110406030c0e03070608101d010b03130b010f0e011e03030e0a03201005 66
    0x5080302624400f44000004500940e001d0b0f90882d008000b1101d0300d44500e201501189800c94000d40400e80c0c0da5000310000b08800c4403940500f00c242c00543c035001600d40044c01c14000100350303662080703950f00030740704d0100350100b90b421050703016003125141c1c0031100c0180103500300b50144e600007034504102605066000d0040340c0255070088040c2919484a50b081000e0365a070401c44d16140c02d11032041076168403009021801402036002900d034400da144c0209440038a5070a00d030a285051400b55600141008102c40883c1c48a08000030b11200041c0280d4220820040035540740c02507210000e0701c0b64104840c18420030000c1c1d00340f00b200c7c2d200d60780d92103820954400401121144001400b1344e15001c40210b81004101c0c1540341440f50b40d641d6505004426086514690300143d41000303c466200d81041c09001491102c0d150164440050b401c000b885204c00f404010f090301252225880b190700c0d40c1d010315000741107404601d500115140c84451a4260203026016101001c00382d20f100b40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 317883255 1250 317882005 317882023
    0x210108100e0a0f1401061212030e12180a09090b090c0103020f0301120303090b090a03080f09060f0604150b1305030d02100e0330060f03251509080708 66
    0x1c100c81441550340c440c551188864241110740e5946e805001c610074003c8a00c24200b5032090041100c034012144004007a40c2c20900e980e1210b5220b1961050b40107800410b4841000d6660880d44100c0555400a2035400960340514881031926996400340012101404c3c07144000c034003103401a1103080011812481000389c210003841060005000e6802c0b203041d45681d403070003845d020405543c1601c400c01c2100055600e040940c0c00784209804168001d280c1d19801080d00f148000c0c0c902c2e00142032a01d8840c001c11a000e4a0900c0c40022076680c0c680d400b8654040b000d940c0f18050640395002c110045e03000c6080010b4005c09110001100e19002444040c1e8200c1340c2e0241000e0341101e54080040c111040e00600c43c2c0c00f091006855802a002d100450354288403000c0300c842114151921401c580505006d00404520301e07080d44c03a88001a00d0f412201c00228000740c0c01d0380c1580103500758450741c1c1001e9030f2006d0450309000c400d6408868402500c52000503034001c0d50b55010780b42d5440e40c05c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 317884505 1250 317883255 317883263
    0xa02030403180f061224090b09010308250b0a09110d03020316050304051305190606090501051b010c0503090607080106020703080a0c0204060e150d1502210108100e0a 73
    0x10f2410f104162040d888144841e00110012a182540c00114200c602400300f0040d5105428442044258142c2c05940781051003921003609650454540008502c40c0300708070810340740701d020005800301c2c5c01c124044c3d031540c00c0050807417142803c500359005840c800708152011031030124046180d01d0811200d803420341e8160020362070701400c50310b42180b00f00700010641c0c0c20300041c00000f5081d10b940c2d41980e01402044030014141c0740c008160b2194103860055101e110b40380030340502001e50800030302c0c401d44400342010742e202c86c02400b00d54220301401d51052559400d00030a12a4560840c0145024800c1003040e500c09c0d554440040300c2890b000d104d250016401020b04001284401c1c2c01401c554401d842c2010260005401240070382c0d00c4c0703501c90b40c074104005080003001d000311244110f055034119283c21408150791103201c40b00c502111b2140c1080e03800901ca28051a001f20071401e11180d1080c64104e0350b0352101c41301d4a40c80c0078807024003140d062402c881d8441c0c4011032600b140981c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 317885755 1250 317884505 317884529
    0x6020f15041703070503060a09150b090f0310060501030e0d021c0309050f16091a120f06040b0f07140a110708030c1605030a0309090b040902090a0203040318 69
    0x440545038400c050810b07a03452182c0450102d205080d103004504c01c0c08191502c0782e41c1c0c02e026041c400101030f2544014500c03450900104804603c140310b5000f11601050603d84451105000981c04441d45c0c450690600c944444045a010950000c4c022102c00740c800700940c04c9540252621b480141c1c400c4801a00450320390b00100b40212120500040b962030000b511403070994500c0c1c0303020055a9541510f50210140708521042c120350301010300442801448204103440032190129110b07946184200044151080340d4042040800070041c4c2d041e088440600b401d060050110710181c07150a02c0300300603000180028025060355022032269a60b040ca05144104110348210300e0000c1c0d45035501076100005208030003000a4542500e04801521a120314010070b0903084840d94401c03406900043d82142c0401d03003280e04107040301c196076404250300c0d00e440300160080181090003980311458400b80115031240e68091403040c2d00c2030300e541d50300c4a410f10f0b000e4001c4000b44503e0021800b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 317887005 1250 317885755 317885773
    0x110a050f030607050c01140a0506150c0d05031305030f2508030408070c032003070f050a0501050a020a020a030b0109201b12030103050604030909060b09060f12010b1306020f 76
    0x8410340080062003045800080d08002000c00c7c101200c8042d5030100318a910381c8141301007803603c7e000c403a41d29400000c2d000c0c900704007081440d03205c141010000007801404400208000340c04203110241544c0078060701da59165000007514150000b913041a0030850461844003100503810b00220241e4104c50001d04640e200e646400c000d6001364012510844102c0d00040022815610090580d0354049110b81c1001c3c681c0600d894141c1580c03090b512010114030411540e03c03a0408181903c00a2a00d0399440f000041c044c1d2900012200c0203400c59030f40d803400002d121030011400e060b11502a4240f00c1440102c155642c201036111510f100d43d0010040240083d64030b501072507400d910681500c00c041e00c0d1904a40c91078000b64021b4416812000410041550180c90341000d804054000c002440c2040145c0e0b080c0e0007020020b034014000010010b600c1c01c0b80005640c0440da034401e092940d90b840d40c2454400340c10405018900d4640700e0404501640081040002400b405009180c200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 317888255 1250 317887005 317887007
    0xc0f1b060914100501080f06040b06010c020307031202011b030c0207060e130608010b0f10051c0f020c0109030e0a1404051003120f02071401020d030506040b030a110a050f030607 78
    0x1032180380c111100b10304019032052075001801101501e10200f000000d156151407003540c01c003d19561090680d400c54420800080e4480c00301640110003880c1011442c3d0440c4042441c0c204a500090b104242c0d01c451240b050380d054010484141c44040e040300c1202c15071b407065065030181007403200540c01c0b908003882b08074410800000c841c2e400511503e41a0007089059080381c0d55070304a510780c0d9440c2c00340c406940c2400b40e2480c00c3c41c42d09444140002c0d041950081140c0120128256500c1e588803d42c1418107c1d500541825090004115a500c01c103002140c001c05000004078041482c0f0340464500349840a040340485005a040c11a9030300c41200700b200030030340103088000b00c1d800c80c20044007080700522414080c40030307034881c00181d008480c4041c4c07034a50303503a002c0c016110545080444607603000c030701804580f6450801107002d03161540000e0160031442070725a014440c2c400b01d0010b000039401d201d006c08505459180e411502c800500036140d80c40510950554041c0d00400d50031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 317889505 1250 317888255 317888261
    0x602030a0e0402130b0d05060d020117060f150703020105151c050a06020708120606091003020c0a020613091410030213110316121a0d030203040b0d0c0f1b06 69
    0x100c0c1c0010401032515400c10240e402c01074140d004840401d00206100300302002510a03d90003440c11030b940101c0b013201d03030700081210155000f04140300c2e2000300410031940315031554144401000781101e058198000d13a824240c4c1000744154019801e01c0e000c50323001454400c00030901c40016009007000d041c0003410724405d03091303045d089501d48035030315a100120300305202400030144140d85403076a51300d01c191700c6ca83d1850090071040c8610020001d01c060b40d92410607070040400d90341400b60b2610044100d0300d0403c0f400e803002a4002d0400151480341c11000d01414088d5036800300b04001c00d1040e91108142080112480d0002d4801202d0500140c43c15821040362100e140b100450300b00300c0504031500b42d81040e9a43d0440c01480c6140e10740c41600140c214141d1340c3d94040070070440d660451405019814604054019000b1480d00c1d02814801e0007101c0140c0940d9405c0ca0b91800c0c00340c03014000b4000b0781880d4000170825083c0f01c240d5407141000101c860f43c90501000904000c1e2564130003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 317890755 1250 317889505 317889527
    0x1050607140f0a0218070206060915030106060810080715110709091505151509060d09050a030306080f070b0d2409060639050312011508010602030a 65
    0x140d2031048807060305400200104882050b80101600c038606443c4107202c4541c074640c2c5001c1010901c2000c001c80d60343e0008102e83e2201c400c403220110798580500042484a0782c03003c0c260507500341130740480c0c12604000c07814017400d010840010200d90f510b401c4c0744c51f111a8007503a0550000c68682d03004c0f9902c111803270303460507900714166148507640e012000108c45210030111034021643c095003c040d100740c840c0c240c0c810501070f0b40781e0350914280c1c001001040e40c1e103190500c842010911030000e8840704207580c1c3c14250a0310800021a650070300c0303640d5484034081100000d06080e4046000700c004103d508480101c031005144030703420120154065000301c00ea85440566541e0707200306c86803040301440c2564002c440346a440900b044004000d032076194124209001d2500008242244020702e100072804d50341240b180805000c01d160b6007184100740c005450785c070011030016405c1008881060484040340d4041c4100b10fa00001641c0800007407248401503001031000c101e0306805190513001d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 317892005 1250 317890755 317890763
    0x100f121e0302190339020123040603050105040b0604180e16060c031404060e2b0803090f1605040e0a060f021c02091f09030b070507110901050901050607 67
    0x10000f001d0b40b0300b043e16580a0003060700052803419104080790100030001402000e02d980600d00942d880040d41d0003403000f81002810040d06c01c0002c10349003090f044a030b81c09286503407040d50b150340c1c5060090203003600780a6244154601040c0c25628a0510115400c444000240160204103c0780e4a8014186007600b41628007070386401d14003e41c02030341c3c2300020701000e0f04d540281c03d40a06000b428801d031596040d00a20302004203010154108010099100d001c440d1180080043c00c100040c14000d102c500464680c05903c81041084403005140305140c201c00f140c103601c03500c0419696580300701098134000d8224003018099802c198200f0800081d202080f214029090f1740e5031000c039001d8649500c0c6003540070035403003214450460407181c16003d8810950602480c640001c8118522900c484040f1565401161585001d1b151020007150410828481443c2491000c0e02da6444082c04403a101480c0030310b80d409207401802c040c160b40d40a40201100c1c0e007000300b030003169402030509507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 317893255 1250 317892005 317892013
    0x602070501050a02030a1404080f070302010b040f020a080f040f0b060d150204080f070305060a0e0a1203091a0f04031d060c010603050c0108040519140105100f121e0302 74
    0x28045282406814000c5050000043c2c1d280b500f00b90400c101d50942c8040100d0f801000b090102048142c1700703884600c03e005031140c0d034825051070f003640105180e694098105003408040e025041d21a809481c1000040c1c540c1d500d10f81d21205501900d9808580003800d50f40300d400d402c8040352203144020344c44180540040c4e8401a1900c0d240c2d10b0000c4803c0b01002c454000031300340844101402108030008611006015903030030340e55140c0d2900d40080c030b01c001c0d02369215074207914003100304a45003a0a400c142407820415020384010054000c0740d034107644210720103185120b11001a52598440c2c207003000048015125039030304071400726692800030390031500c03401e501d125503446400400f4000d11036800020201c0c90341c80d10504001161440c42d050101c00c0041101040c40401c1010600c4a850201c0b03600d04117600d400950590780c030005600c07540c6000d040210380d005101c850010303250b05103540d0103030581d034039440da82d085280d1500610000c5042c22500144103040d1170800300038800c1c01a1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 317894505 1250 317893255 317893267
    0xd0503010b1309020d05390702010306030803041a0106080105101d2709060c0412230c09060402160204020d02090603040f0303150302100f171005040b0406030b130602 73
    0x103c03081c2c0e00500d40c5c0c40c03400355855042c0121155528904404600d011042a00e03801801120368401403641d01100c042440015a110440e80302c0e40c01000034551004520723440781090304010201860f0590024414050000042200c6014450f07450403500018003541c248940100115043d901c4e00e0340c4416605450188171100c0d94400d4070340b4680c10640b0b101365400f49164600300c20072840280060f40b50740c00480600c100c100b081070407902911351508100d00d00c04000c0c58451070440900c0106000b0351a5010300742412031012490440c60305c0c0c02c890700e01c4a5143c400c1007000300d00c111900014400d0194880d0310042c2042c1e000381500044800c4014146540300303000c03490b998001c8808540102401000c8010982c05100b816803081002d65003804a50450380421071040358207294006000044842081c0a4414848070080d1042d030007201c007070b90804284000c11644203001c0c443c0b05505040c034040c071906080c403030a001c1340e810050008603a140d4001503490340c02c40c520203664640e020040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 317895755 1250 317894505 317894519
    0x80a03060504020313060f093203030a0b03010b01021f0f0f0e010203100b04120212010b0a0e0106020f01020310050d050a0b090c011205090d0525050715020d0503010b13 74
    0x13a52081d40001e00560307401080789041411100c40740e04001143e480c2c2054400825404a004064407407005141107a10f07030001000c3d8101d43d81c0c05c00711405407000104002c81d510050300500c03408001a0024420440407000590303c81141a8203480d13402415882e018205116402c091044141480e0014026103200c01881c02d481c80c0c200b00c104070360740010a100d4200e520b400d1203001081c9a62015080c14101045803816000300c20000e4031802d1540703001c002880c800e41c4503990100d4010025851290717240c6104240b01c00911903000940140000c443d180007041c001c070307882007074100540c90000d800c007410420300c000c4600b000c0d40c2d00c0c4600f40781c1e000000e0030100c82d00d00820024008005071404040010f10610710703581c00149040c18042401b03190701001442010302000760a0072605c80d49885950081d640c0820131400200791403410840510102041802c00d9403050340000310760080114050707a507507016003208400540104010840105944007400ea100c01c0c0d000e004010316035440c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 317897005 1250 317895755 317895757
    0x1140d0b0a030f0516060c020402090a0e1608070509030316050307050d030f0c090608191107060911331207030e010c031e02090a03080c0a05060708040807080a0306050402 75
    0x2c21941c0e0710010004400303106040007184109034410800c2e5200a0030100020403e110440009010f00d801285000d91580c8440801700503119504d0f04071000d10307041c0003d8000ea504182000d0210300b030000800c0c801c9202c0d808860130301c58090011345c5060b024907102c860003c0b04040c1503400e800144415000900c062003021210071145d500850744c03e01c3c074444003040310001908001070185d85d0030208a11600041c40540c464002d1201c0d107810107a40030031f0703c00340c080b0300c0e84007084100c001018010445a80e01c100400740c01900300c41800b60928041c400c15088960a0700c80140c91302d071100510408185001c2c1d40c603104c01c602207081280904620990b8041a82c1c2500400c0c0c4619904407600c0c03013407087e03000f04641c40c68107201c1c41d190040d031003005035000c01c070502415400148041440d00e6022200008682c00020320395034000b40c4519540b1007004550444039400358a0118400030f02c5100c00c0c50090b5000b4400705d141c900f0750307510110503910085071441416100c0c000043e01d503131184 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 317898255 1250 317897005 317897009
    0xf08160803010801151a090307081c120e0309100215040c0e0a15090c18090c1209030212091207030b06040c030218060f160303090213090201140d0b0a 66
    0x44180341e100d504095040c1c0c03d54810010b85007024041078820070100146102509007451040380455942448101182c03d000c40d982004499220b440f9062203041c0201e10110301906c42030341d410040801007100c21055800500304030754180d00501c1300728184d1800240f00000f01d00f20740101e425a80303c0303114100c4403010860341038a80c9240f00c10104900c203074003c41203034468243c880800080444040e041c0c0c5041181c0616411a55100c000340c03034440c0606c400920300081c04040c04040d944d9400008050500f0003845000141000d130040304040341805150219039150f0050407100000351215038aa801c41c0707038402d03408401008070030061242405040c01850040c50400c1032490100e081c0300a442000c0010410148104003280b44062070002c8040110f00880e4076507641c07103203528a1002c9000700740c1c0000b12000c800104034205034041e80407261641c400c0d1101182c05e0a10030507107044074801e010103070200d5410031414000041c104000e0101c0001c3d814002030607406400032460050b055 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 317899505 1250 317898255 317898263
    0x90c020a0c09050115021f0b0d0501090b010801180f060c030216120e010504060e090702150712060b0306060a0c0501110c0606030606090c070b09030412080a0f1b0f0816 74
    0x1d4401070289641c85c000544c10078071180010200c0003c4400f003c030b00c44103120003c3c102d6640e03d24240a1a58500b210382c164a50094000d200c80400d40c00c0030340c1907100c2031081100755031034800d1102d5400a124541072980d900551703c444a0741664541c2000303410021800c40070580c0c01c011102407204484007a90780700f800790710440303420503841d0b00203081c032a2019941814002c052008120242d4040700754a01ca6a042c8e407002d003552100c850507458940156020104000c41c0420401c0b01503100080352190b1800e000240405036a850710401d4600c07003900c085810003000c02032003280c280515030746c2c085a84134900001e8800300c0d0101441c40d0780c012a40c2e0b1000da400070300034815589400c02c84260401001c88550403982092001e0020502c5548002410004050000b540050047c000d443c02040c4180c681c81d82c2041b5031034000500d9210262020206404944580c0c80301e20805021803a1031448170100d141301c6864864002003500c4810480d5003000802c00030202c08001c00d20034a00900c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 317900755 1250 317899505 317899511
    0x109050c16060209040c110c2404080604170703050a0c0f05061914060a0302011103090307060804060f06080d030f020403080d200f030f04020f090403090f0608010f090c020a0c09 78
    0x401c2c10801031b0748420305e5503010460a81440f103076071000450105021442202c81c5200501c0341c0100000c02800c40300c43e103c1080022030001642d4a0201e0034610407442858444210b6041651a801a010345900500010000d0101090540c012600c540055001d00f41800b01c2080550700d4502c0c001d02100d502c012800243e030b4602c004202402074074101100150000324070701d132400104524000c2c52202a04226030181401041e5400780300b165811b00c00901030300d40301c50f104e5002502c55441075034115091807800307440340b040c1e004030f1182c8019140f4600262484007443c500c11400b9281481080003119800c010000014014200408034080031101c08901c000840b012034000f5030301a0005031a034041080b1079417654658074200e07540007034440c104003400e881e640003085080441041440e0803100340f10500c03060641007015041201e022400040c601511188116030303e200030300c0780c403150301407a01003800541e426400c40040607100348101e0303c18140c03a4071040030195859200d64141d5136 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 317902005 1250 317900755 317900767
    0xf0801091511120405072115021e040905070e120d050912030408070303020d020d02030d051b03090604020901060e1f020f07060e0307060804020d0f03020709090501052d0109050c160602 81
    0x503c024040c82480045d4885480724006516010503c002523008000300300c0e40001c180c40120040c803820450245d01030a2952500e46444a2030001c01c0280d80003000b040d208820030906140685054140e40c8111015200f80070501500740c4664100340b4015038801c82100100140e204204081d00007414100020328080346182806410060112450341c11504080480150960000121600380034000303000622680d0314410101c0300d051a203420161b29030004148001201d0000c0c4450156000b12a0320010fa42d95100a0301c1f010851f031002a04500c0094240400840e141108060904140159440701c00c054200c207040c1000e039003081e4045007410002c10724a040800000d0050320742130800c03144504041c1c0004800c421403803401001c05c014441c100c1c040610a00c11000204610b480601c240304503440d1944c081c213000ca4568100c2644420901660784098152010840442c811070f6510f074208400c440c0900350091500100031410400c2d5140d500381080300c8440c4901510700140c8800b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 317903255 1250 317902005 317902019
    0xc03091210090c1e0815040507050d0302010b0a051f0c0606050919060603050c0403020d02030111030705270117040609080d060e0a05190b0d02060f03010f080109151112040507 77
    0x80c008040c100fa0007030011130a02001100050760f0384c4078000d09815500756640c500d8464035113182500f20640000c03546170040e0400d6015048600c01c01001c64002108035103e40c1030200c0541d030481a2854400b081035002c400600034480038810b0341c0201c00c0400c9068440d808100a0001591008884c000290001e44280c402d8450746018100038074080c0724505141801410310300940c08003901c00d03801d9079258401c42d0b8003503000c681003148040c142a10392030000c4d405855504015460400380714101c00d000b10215480c00c0c40080604145c50356440c80c24007150102c45190002d004440d03681e81c424012011842a1000e0070200c61410705c0411a00c0c142068221010800741981c54054107280c1444030178000c0c0b000c7c12100303651002d03001400300c002c0ca002504000340007501079000741c0009404c08030010518000d50607100103070044031403d50381c0c20965088643d0640d0207030000a14885064a11100c3d0308503c01e108040001241000c030800401c024941061304e0864180c0c0c44208108824 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 317904505 1250 317903255 317903279
    0x1a04140102040e2d09010605010314041203110d1109010f02010c0c02240304050703020420091c0203031b070501021609050703061503090302120c03091210090c 70
    0x1401002000758142480e09058258484024142400e0440c8021000b00c2407480d8100e006402611034030880440c5c00d144a009001740400e0045500090810ba0503060a001000041d801140c0c08011030318548481e820440003016000010300703914004001c2c0300b03000c080324007914140010014109958901c0c880024020301070014007401564100740e0b1040c5001e410402e1008026016240303035500c844c0041961410025400c24004d0052010081c4018003000040203410382e882914108045658401c0d01210101540d449000d03a210800240c0801d00741502c11480c80083c640b01c28030b042010740e001a096810140c2002031f44641807500c490075003401c0044000400742800948000f002540d18220945030074024501801d849101003074015109070b110100410844048411040315404010041c20742107005400610801e648445120000e40455840300301d110300a600e0311748010107104407a1001d0a021a40340101d4bc00500019414019000140c0c07003801c101c4100341c10200d0315158 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 317905755 1250 317904505 317904533
    0x30a03030f05010e070824040617010e0c130f02040b0f0304050606040c021510030506010b1809010f050108040302070e10031a040b180705040603030e0418050303060d020d1a04 77
    0x8185000c117100c2d000b44c110440740d40040d5420104401e08201024024026005540030758100d441c110000031800d0f410080f1a182859010081c461118114500d076590000c2d4080d10798880455543c1c4105c20f200e584c0702c2260010414009420966550b10702800c1e074114941c69044404004104410014140702041c0e220504031010000d03a590400c00954076003e0741c0411030002c3c00c0e000403a0003642417800740e900950340007081341e580c0e60315410030084030f41017180011a04211155070070700a14040f41000d06030f61040d2004800246400011240c4034006130050707040d4080d080d0040b845e003010f40340247c4503040e18003108040d140b452030080f104500356501d0b00d5031464248184070001f6a00d2020710b0b003254003e001082d0205100c2c4a05007071910715440f9030341c4030381303002c0d40002016000407005801c000c08650070451b80900402600c0c4a03440c05900810317a40040001410528140d9604000c1c680064200142071115584041c01302001048080d00350002d5020042000024082260 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 317907005 1250 317905755 317905769
    0x4032706121406010c0606150302090102070905060d0303091b03030216050114030f090f03070b0601080105010c0c0e0a0b0a090f0b0a030c0605070807020306160216030b16030b030a03030f0501 84
    0x2c80504818580300b01c0d0030015014a0400c55241c440c00180040ca802030742c09041d80024107942e0b6490210007a000f5804800d0960140c00307078079800148074440d88541441800007030149450b250f1541d030304800800707241000f01c03204041d05a400300d0310b0310390300c40d0500554400d800400c0030480c0001c0d40e88002e40c02c1e52050b07040000c28544d0340b01c0c0041c3e0345c0c03d40e504200c0412101c5816110110607905014590a10b0741041c440440c0303041c14801809600d5000310801e0701c411720320b41d8031500111601510007130007404544c40d0110030083c0814804403240c3c0521750650008500140d800000d580100380da01040055031a000d40c0c603a103028034807540403071140803a10200024619070f60724603510f50900c80e5005201011406c10180a54002102c0d4041d5000b002e8480030301d4400c1c0c0b1032120039051500381c00148990f401001564a482c2c00c0b000507250840c80310707529a0303111035030030380d003403014400c030104042d01c4824840558800300400301d982442074030080341c91111100c200041381d4059000c16 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 317908255 1250 317907005 317907011
    0x9030415270533160821070309030c02090a1d030409110301060221090405011e0905062d0d05100c0201090b15040912020f0c0a030c06080403270612 65
    0x50100f07164010800b0305011152401d0780741d02c901c0d042140c02131360006001d4000c003000030b01807400602004400f07040000c440d910024a0300ea5440032412030340100d10040c00b0569154101007d41350401e449a41b00303806600100d440a00104a001446062600020140e0003c1021320003500b031402407420a001c1c4545207401c561601500955a80d0690718241e00d164400d0450385555a10340700315146e10314090401c1c06156035524041e110020002045050030b00d01c0d40e0b01260380c008600406008a000400760032266003010300b40301451a04540d005900c901c2c0c1002d441040d1076404030031580703c1c001c9015201c4000220300400c19281e00e01465011645421454000281d5403070340725070000010502207250b400e420004c076004001e14800507100c1c85415850032030090340020541046580d0000b580c543c003070040c003800038520745404028400448800d045c04100c0c070030705031280d01c81d0080c68855800307a1022401404004a6600b404d1401d80e401000e018498000342d4071032880d58550810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 317909505 1250 317908255 317908309
    0x20415080c042f030a060801060312020d0f0914010c06090f02011701050603040308062d130902030604081c050403020c270f070203070602120103020a0e090304152705 73
    0x15412140307201c03003e952258404008542070b00c10785c0d4012006040034030000c003d12522401c0c500c50343c00d1003030145001441001404202c5e0f034821301140c02c0049890315016030b81d42c14800042a05060168145e0400c0000d00c20032000c64198020104954080c0c10020207609071800010810440204480300d80004e101c010041503e942044a6200d034051030065501c0d00e40900041140201100c1c102016494020f40f504481c07100408840c2140210303038011070031085421b604141e494024010758580c009400250103d14881d00408001258902c2010000d150203d24012164161410780c0142d000784a46580ca007450b4900c03074114010500d15441708100a240c410f042c5100034012400c0d01c1485001c20780e40748c020800c0d1800507130b200724150349520b011881440c8841d0b0906c03050344120701d100710002d00c00c40701e01240350007060002c0141d460a03041004091003015500941410001015030754103075002000c1402108030700c3c02802454480c90041040302414000c280300b0020802e500f10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 317910755 1250 317909505 317909561
    0x702030a0e0103060e070f08090703150c020c13150506121305030f0a080f0c07020306010e0601050f0d05070e041b21111e070b010b07020415080c04 65
    0x140d890019091030080c1a40c1c0030798004078083c2007154403041203001e8103002c3c0071019070001e04a0140c40c0c015900c01126070b076004403007540c03890b0901c405001c182861001204e01204c580060100c1a050f00446c1c0c014041d00b004540d07030384604648040341c03d40d9000082100010440424014a011986103003803007404c0345400c01c5403001411b41814500100100d50411074140142c48850400306291b0b61945040d0101078201181280d181200c2c0030413000064201240314280c0d800c0035000350090105030f0a004618009401c080c02d6141440000c1c4600342020302490005c100b03214100d81c010030107040030780000e0940700c404000540b007a81080c0c062545090340f04d0a004502d0f48900c0c110440c0d407800c60b015080e08025100c3e001c400c40c00e02d01805a400c245200501c010a0b0a607008620f2130300b00b05084540d400340070002000c0d941b22070010401c411500014150407400108001071038801c695440352a88100d902260003600444030078441441d05219176140e0b010076114103100b18412840c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 317912005 1250 317910755 317910757
    0x605060123030405250603110c071503380108060f0f0f090a0608161805190509100e1b01030c090806090c21070303031e050f09070e070203 61
    0x40c101605007400b000240c2031103010407410782030440c40404070420b011450b03050180c00c80240108030101e414125109001c14440341240e52140910010f00229424000d40a510580c480104420103440300340d2010030190400c1803905141d00040c01280c00c0c405082107003030680c0d040002c0c07414000d10000b0081c65440d08050301e0340d2031008417070013810b035881c400002d0440146a01d140750841020000c10090000c45c0d4080810303a91032404540d11192024184a40c5503414041d501c1100e4034505442c00510303843d0003454010000c0c01d1441004500403803044100c1e182168101480d502000645802e56158130841000c0d03c1303000d0140c01141c400d0b1030b040e80c101e14481d440303904040e40c0d01d80300354206114680b00e40c05401c400b002d45200f41003401134550390301c9000e1041d501c03c404060b10307410000703282004200b40c00d0114002d00010780c81d58801350300500b030441460345a200381d0482c000c00b030b107000e104061142112b2030194819007041035929141a0035130b00a40b54800c5490b061080c1150000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 317913255 1250 317912005 317912057
    0x171306110a0c060503060102160312090b070f020906010509030a061b030c0203031308070c03060e060703180212120f19050a080a020f070c0e15011803140c0303030106050706050601 79
    0x41080c9a0300d07100c1b0780040f840d080c0070380d00d0401c296110200110821003030802040c4924225035030840303856140c5503403d880b440ba82e02c2c0100280380d06900d08005091468005074401c0d8141084c03424040860701181c1030103019441190055030310001d8501c41942c010561a81d54241c2ca01040307217500400001c0c0d6280b1010b0300642d00940c0000c1c1c48010480d02c0390459200d10b600184030407079540d0360700e01500a803c02c0c901c610010f006240c00240703028480e228040e051419000b2080d0300c003080760280840011540400c4000d400780b03120b01394040c8010801040c8050148408a41e6042981e4000d5850502660102d04002c4200610140e0740d6206a01e103821100c1807000590b01c8480704620301082c424650020b1030814511000280007003602102c6101e400c0300c00380440a01e0140b030044955240c0740b00245500f00002d14240046180b1003120609109804201d13002130350f2000c0081c0c555002640050001080025080100003060003035941100c42801c207028031200c40186094412426 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 317914505 1250 317913255 317913257
    0x30903031b070518010f23040b030a120e01080a14010e0c04031707110f030303071214010f06021c05030406020d1509051e04050c0409171306110a0c06 66
    0x70141244906100440c010040101462140369207402038030f10202c000d11a001c0c15118600000928101401c04a90780065102c2040c02e0007500d0300801004002003203009805108040022002440c081d46191806403281c5980c03012401c403000041c45250020515040d45003020454807030401a071039014103541d074500c24811665140701d80020f15006035407000c1c091080d00c4650702c1c0c07020120740003804114068926219000c01900a02052001540e045501a03204100041c40d03544500000601081c437007001140d54262140c41842d030141c280c1120740243d181030801c000e1030340c04101c0e00440c0800c0e00701c0d003040d1191a40300505103010042000c0d003540d80003e82010b00c03548550001c90242600080070952540750740081000740001c480d211a807481d160312075007100603100350b098451903002c0c000700400912042804041c1001c2c14045505c001240c110003018400300000d403104000141c0c01c1c0180b580380c031304010601d18120700621243e4010b0300180000c24251442e100c1600c1e02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 317915755 1250 317914505 317914537
    0xf011812020d240b01030c020c130e03030f0a05101d060d08160501180f060b1503090c040b010e010f030504050c031b0306060105040b34050d03050903090303 69
    0x441c004256101c0101034018400410403104980d240800722194010881c16070080054018010041d022140820312500250f440301e031f101d001c58540350102c941801031f805004143c445074400d03c0c41c03464005817000102009600c0401070a11458460305030301429004032131191a26103544080101c000c00e41040d90400c01400140c0f40d503c43c540c502504c0d80d400600203990346c4906070722142000100d00c0440f165405d011550b080140143c00741030065402841e4034880042d40e50700c15000b001013400c590b410a20414004c010008400040d40c4502e407548042c1c0388009482c2d08000407581c01090316030522485018a0985980c41480401d09510500703000420b503c0e41e041461410900b00d1825134180f240642c0e1110414000c3c02640300340205908990b19500d40707400655141c05513005414001c070303003400f410305070300b4112090206280020301000460030011201c008030240306481038810f5400704e000c1000750780d41841410740c001c040401560809140000081c2c580c81102440502525 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 317917005 1250 317915755 317915789
    0x1504030f060c0315030f0209010f081207050a06052805010b2a07060207030212070627080607050903060a0b030303062806090305070602010915380f0118 67
    0x3002c0d5104400f03e4407400d00742c10100343c5d213141c5a607030402c074208100c0c09603200710300018107800100354040698080601a0104080034624100c032500000c00036511445030030b54180c0442c52900c503060050196034a03c56800452111414034012070803400141d452070500100102080501519000110650801601c891040203420700700c0c4041409646030080d086c00184483e00020480100ca2003038941045600c1c1d00980725484d050320f48181c1000c10410400502c2c542e0688801004040c1000c1c42d1f224906d480303d404070b07d413100848842002c10f00018000703c40d450304109039503118014203410b102e204001c5c3d000c281c4901000e000c0d91f00419001d802ca810850a02c0c080c15400704240641c1e00d441076403002c006215558620007698140941d46004c07400c5481070160201c0c05800c00c00400000c2803070000e4030020702c0503415680c0180305201910341c01d00c000504031004d502000034582c1c1200403280801c424030303061610203814054240140c4905401d5010540c0864100c9045251085 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 317918255 1250 317917005 317917007
    0xb04081207060e07240215070507050a17040914101e09110901032306061c05130c14010c060905121308010b060c060a0509030412060b1504030f060c 65
    0x864483c1e080514003c281000c586844064484412007400c06403840030f001a2030781c1a80c6802c80400c0350b032205201040003a00c80c5010f88010206940b0480880c0c01c031b040a80c41d144076081e4408410b4101400000e01000602414000d20120100036901d0b89054180341c8100d1054241c140700c2c1c41c01c03121400701c0043c1400300012908004104a48042c09070250501c4c202c0307101d07031002805c28042880c144a035a6820344250841c051f403455490390403415201d41c0104a40707070b04022880c0c0e0601d0806400c203000141580101c1d8007404422124028541036441d1448002c0c130746030820f01408803c1a0b001210743c1e070240c009030381160042000070381054242031540c00c140342080c00750b41c41d9000090080309640c21801c41d0040301c0b203010003000441a00002c00140380704a01e01010240d11601c041a42a60701758040313038000e490030048038602603a400f080e62042000031402d440644c2d59031410030160402d00c800382007900c03403c2404d600d45030469681d1a100d0061000203000710b50740d00051a661 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 317919505 1250 317918255 317918261
    0x40506010302040b04090501180b01050409020309190b1017030a030209030f0607050409060b12060f03010e120a0207050d02150a03111204020102190302190c1e0806010b0408120706 79
    0x1c1c011114131a41d866885e0300b1840080c05080c0300785080701060001c50f8040c81d010f8454411450700507510b892415141a00640c041c0d0030203414982e441c020003522110036503a908049506030301c110010b1545d49001900030002d58003543c014042c080080083d60119a070100440d40d0030810b03400c2c0143c8524148012030302c0d02d2005c40e141d010030300c00c05050109507038004001d0021108061001c1c441d09407903030340e0340700c460054507035880a003002d01000c608946810941680303240000b40001405c00c490302852441c0485040c0c0034941da82c400584031103841c0d410f020350b03000342005070b5080d90055085c0c2c0c0485e00070980601544804034021411004461098008030b401d07000c0500c40c2511031f501e8105c0042c030000e069400324050b2040d03c0240c0034104401009020381501500940088000c10710f5418034031120704030071105042040800701e0000c40c3c0302c4507100881075182c030300c0307150a042442e25454a83e060308403840c40e51003440200301407100042d03c03c03403440501074034070745030045442c01d4406 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 317920755 1250 317919505 317919509
    0x120106031506030c0605191101020d09030305070e0901080d051b03040612060e040b0a0f0e010e01020c0705030f0303070302090a17010c021e0a0f050a0c1403120a020c04050601030204 80
    0x1076000c0e40600000c1c400d0301d42024080e2805440d54103d00c56070350710195014030510310140005c0004030074108490b4062840c203088603d22400141ca01118080c1410407075051003012400301e41d403041402051a0b01c04d0090111384016038008149504001202e0b40c0c80d02c1e0b145880c020003500090100006245031207006182070700b101120b4403107460781009081c80d841e81300f11b51030340d52a0000004110040440640c000c680084501045840304070a04d009020280e88010540c0d8480420820f038040034441d000101008400050315468a09540d03401c1113aa03600161207a40181c44080d280c0c1c002004890300200d2074140182e441280201055800d00d0f00da2282c0a06600200b41548c1c855040d00b21511000f046e0742560861140b2582d90b14103000f0142c903821080d8801e20440001030030380010442c0890103281203c450440507554007610325116000001c440712400c6118241c2e04040003881c00840d20314800d03e06205640318000d5550740d2002040341b0454443c00460482c1e40a0f50440700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 317922005 1250 317920755 317920763
    0x20a110601030b0108061b03060d020109121a0a0b01021c03060f0801090302060f10030f050a0b16030501060c020f0f0d0c08010212010f0e011217030403200c030c12010603 75
    0x180c07503a40381088614240240f040400c540034080003d1400000b480419407005000e182450464403494140501030b030020000b02c1c180256603102003010b10300f4440c0620752a01c00d18554007203d000126000c0d085001410501c1c0250070f04043c280d09a0300461509901f661880901e580c05035110f200304c0c0a40819030140003100701e011004140d1400c190044c01026009400700d502c9600c41900000900504642c8000c100041403030510008401081d03e030311280c0103000701c801d40d01c0280c45003d100542503c081d032141c030184501d40405a054040e60340146403500f00356855442640103c4d48603042002220b10403030360040006c8940e40da401c3c8204200e50400000314a030f54840000070300030740c405c1c0030403101c440c2030200000740c0d8180650250b040c0c0d400380760740000691804018010039a40000d0481c0d000c0717888a1440318240340040510700c1607000761750b01ba20162940e4290700c10352000c50700c0d0110390b40119000e80902d84001401460000c0299807a58648010050141c010501c640000b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 317923255 1250 317922005 317922013
    0x105070c121202160f180e060a0b01020706030c0917151815010b040303050327061e0f0f07110703060b0108070f020705040209010302090405040b0414030405030709020a11 75
    0x401404600e00700d160300031442e502201c03400501c080310020050800c1c49071a6410310307040003e102e0b10300101040c030009900c0c120045404601d1589150a01c0e004480b00d580c9240c1d0f070310740201c0b9581e04000601c010455400c0422040d15070400c028031120712402440008024150f45072144941003104498258007030320301070300c1d50900c1151441c91412070710340704030f40d40f041100c414185c2c0ca07004100f504a40c100d23008540b0705483c50340c065400c0d0300010b080040c03d01c2c1c1101d00958503007402001c1c0d0403402c5140060070803031500783c4903240c4902d01d201c03031040a185ca803810041d040c140381039910303004800384150050540d101101280c07141c0028410782c115010b054000001c01280d40c200e028810001d07242c0d4000c2d80c1d2805000c4902e5625070b1313118001a4461902002203041a9000f0522650b0600d80542b4010724a400300d403e885064070110b903014800300401080c4142a5000d6020a1846000d10b2801d4a0a40007955600c61b0b40101c054060b0300080c901031840c05080300ba64007821500c21f42e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 317924505 1250 317923255 317923289
    0x20117150406050301110319060503031c0c0801030f031d1215060916030c05130602030d05090d0e012a030215060a030c0b0a0c0501060801060611030c07050105070c 72
    0x1040311060322200315018504001000c1084d25060050794440720441c4200d0381140c2d5982e204030710002d20484440c03104d80d911800401e040c0c0303080c402400300303011080c5080c85000316012224101c07005051400d0401054034014400a01d0032801164520740610b0704050181c0804d07540b640d901607032055554000c400c002c569029100200700c80b920202c04c002603c0c080e640e01010700070740701c808484800c055038150500d0160305000394015500461545002342c100110040b603100b8042680d0401009680003103040d61416810340503442e4050141405803121080d034200103403000245c20821030501084000b815043d24071410410b4a0f0104080d16068510309030070043e48810b1111130141809100e640007030158200103240a00301ca5002d249808264a0486244100d0f0824641d600c02c001841c921140841c000740549800346c0422400040e24034908200580a2854078200840c00d41041c42644064040490040102d230003c2c00c1c501d039180c0c007501c1c1c54034081106420185c130102c425049 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 317925755 1250 317924505 317924521
    0x50909010903140f09190305011d06330102010209150a140f030a090201200105191e1d010e0303040308010506090d03050c01090507182a0c020117 64
    0x2004a1442c003a46907000312102c20840700303415109070101039925071005c001614103070800381c1e05c0d520000210381c000e4030625100c1c0e540c942915410038600d43c0010822a030f280b03510702d083c80f180340c0044a41501131045220014604040e048008400701d680303505e40072001c07141e4002e404540010100801c4036441144883c00364245030000080e0100040f203140e00303d02c0790744104007216640a04030034601e0840e0750f0540d040000e04011070080341002050743c41c2c00d40c008181c0f03000c480f0359031a920000c20107162800700282c0c14a090400340d0401307800d0400c90220129011030900804020340004139550110a40c1d40c03816200340700f07491525603e41034480382044008405103000340e20a07955464183d0741c0d8020414103020305141181d0048a88103a400080d001e03e0003007014082010020403610855101c46081107085c0d481000c001c2103d07910344c03408140340c2c4501481006503000c82d0420529014074a40c002101040c0c003010b100c01d010b29001560300131203100d50100302220041d0814a400c0c40c0d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 317927005 1250 317925755 317925761
    0x10c030c08130f03080417120f09040f020711010e0114040302040c050f03040c0e01050a0e13110a08030405030d03051b0307020106030b19060807080a080310080f0a140619021305090901 81
    0x70400b0043c40d80160300c02603601c1c2c081000420724600c5444181850849d10781c5075403d90100e5046980b082e598010400351100c903001a185170750150100c20311a080c000005009107132502003082c10056400705800004035041e0075102075035016503002074000c6003c0829600c51090041e03000208130040100020000100a03100580b802c01c1003400c81644d07140248200380b0402d003d075080c020410b0000501c3d0440c00188910080e02400c507265010410201281c81010700341c1041915170000542400241020003100c11a9961440d04102d2841e041e890340342c0d8801422004598042c0c0000403a400c00c0c800d400c10f20186030803150903041400c08940701c0103030030750840c0360421060030644005020f40000c1401030071200d000002d010b1000c207607a02e58400342d0006045107003441100c4004100f402e4200711605070f90100304000d108070213542c20b18010403010340e8160001a4048410041100200e401c0e20030500701b040000f58440240e8009a40403410703a402c03c03600b014281d800c02c124448150 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 317928255 1250 317927005 317927009
    0x60908030c0414090c04030b0907050a090603030206011a07080313061503021f140912030d0914030403030e04020a1106040b010627062007060815010c030c08130f030804 74
    0xf56020b00000181c07414030411103011181d0115180040c8400c0000ca151680107940c0a448201990100360700e540005a255035560001810036540345402d10405804000803809480c0340412080c041c0c0500c0c100030a28403483c035006080040100114a40c41100e907801c1c44030a0b8002c40034813541042c68040c100840e072070710043c0d01c6803201c1141c8103483c1111091418801543d40e0760158150406000c1e0481a80130030000340d00f119524011b0070008105102405404e1911000441d05030f540703042c1020713001381c185c001c1c4002d80c108200410010744c221079141d0365000305580250b281c0050210070362b18078518400888483c0640d000b00001c11464156082c1039540540780c1c00404654035950344a0316210340101341c9610803500c000e04c0317031078000c00e012071050b403060b00701d065000310a80e119070500060754415030100d0710450a2205407458030a1101c2211001e2a08031007000842d100105200c0b00e13a030000c1d0680d81c00281340380c946000240081d028218640c0c1c510803141e40c03407801c2a40c80d4454 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 317929505 1250 317928255 317928269
    0x8010209090f040b010509180307050102031023090c0405032409010b210a1719030e102c10050f07091a12071701060302040f0b0304060908030c04 64
    0x160000348040e8a0310400b18001d903042012940168204002e0140c40304001e8401401e0764405440c8500000c003c00042000c0391007600096120b041290000c40902901e03000100e15080300d002d0100c89a0076410404618042100c810321103490b60784c41c2415511503608a250503005011a0044070440c02c104600d2005201c901c20034141c0d100443c15080340c2000041c190301129890a0141466142c2d5003110780343c000c081a40c1d14000c841e0340d1141405405541e4000c42c060210310044400c0883e400300c0080d03401800e0510000c50090a05034880740c4800050001a5440c1e45001d0301c414280218420480004141030b08480d584424a544002210180a0365401d020009da43c0508104000d4050212900d80c0480c007410710881c1001da80c002004410003c0382804468840c012642455000302c045407604c90b00d228100e01c08800001b016080242410700420080101c0c007a00400d602c21aa51115101d8880e26a860400040c02d03120b180a0841c04022051041800c8100c2c001e0046890b1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 317930755 1250 317929505 317929519
    0x2091c0809033f0d060f0806060102120d05040c031403120a0204050a03030f0507060504030c03020d090602101a0a0303031e06050904080d1e02030108011113030f02010909050108010209 81
    0x4000000340c0c18800303d40c00011030100c2650012820b100c01e0307940c00c00f0420a0ba03191802e00304405901400c81c0c070720394052951000f140c01d040207941824080315400c0642840903028840d0146150107445c46072104032203400e80d8400004040c440c4090200002e15030122110302e0366002552510341d03036006074001c10746d607981c054040b03200c082e440d1080318101d07940600950551407442d202518500c00d00c081c0e560510008224150018005102c5c0a118900c20384400415050604000b40340c28468101070090000c034500c18040300340c0001c2c1130042c00940800100d2680c006020840c0f80da42c0219800d0340203078140c1400b2081542541100e020101c44600001070701079014490070541d0340078403800b80c000d5185c0c00414040b0308480001c10001ca00454042002100d80c0401c410008844a101d0a207580c08001401001d00078094080078000203560319003014441149003004040d02c2c40300405c5110600401310459001d40303240303001440e40c1c900030480340d80d41d0031855020750b00c111030707251140e94 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 317932005 1250 317930755 317930773
    0x102010606020a050d05090a030606060906030509010c0c0b0903130e041e150515061204050628051b030903040614040311040902121218100c030302091c080903 70
    0x440020003c240e503402c80c00521114a0043d02501c01e5408541d6a98005411100210119010380a010000e001c142e650689280c03400400030700320b540240c4500070907414180003001079a4001ca41c840c2060708410060300c29214100c0403451449001012449254a20000940407a0130034045110314000e5002030090000d41f0064180701011010060401200140c90022800e00c1c3e440281d00600402d01078070500d000e000046e000e5081111ba03200c1e1603c4000810042017000e000441e04207444071404042503540010000c0142040146804655500d0000410042d801c0e1000001c0040b81d030841c41c1d40e401d01d4601c1c1c2d5281d0788940200d00100310b290b541401746c5d48510040b50122908030005050790506e02c3c0c00c010142120f0041030340c0c018050180b82521910602c8500d00c54210700c3c0701c45980740c4030f64200c480d1051450341128071036401d08900d0650945c00c2180c90002d81e078180750041c0c0e01e03121000091782c010380c0c43c009801c168410b2548081004042c0004202c00101242140c103004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 317933255 1250 317932005 317932007
    0x2220512010e0304120510050a0906060e0105060d0b0a0e01080a141b0103020d0e01020a050c07080a0317040f0804030b221e11090a0204150527030c030115050102010606 74
    0x1940e428000340740f07074010001040b0b410502880b07910303910f10910a4a00400c5040c03110790a4580070b4070ba000503e546c0e1800ca004021072403041e540208664803500c01d040d0f02d0400054000c0c098141c2d0303124101c6e2508a98621651000c50440203420700c0c800040c1c06507107580005a40d02000c0d5011101610180071100e000ea0002665171041c0302100d00c40300001d1a050300441c0650003001000407807544401c91551401c0d02800503098081540d601d59444d003034000031030b916141c03c69110100c00d40210307200c200400d501080350103c14400444090f45605d4501d06034058115050000d17040c66808034000c0b0800061b01002802611801c0d112007040266240c140b01d0180d4281c0c00030045074264500000c0790181440f83c01c421405a823185029000c030801007100004105e40d060581c0e0350006040c007440c00004840c1b2102d480f6442c6c101e0500310f0008108445444201600f8007045000136030400594082018254501026000f03200c1111849010925911030f8081c2e0b901650a09001250403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 317934505 1250 317933255 317933261
    0x14070c020312090a180f0f15050406030c0512070305060a05070f03050f0f19020415140a050304020f040e010c080402010e010c0f06020f04150207030501140103080d05060102010222051201 82
    0x70b0f0390003403c40c1c034081d2420724410f500d10f609190880c4101e4498800800b203412510a900000d418070f00d01080181100c95181d00a910740d40105e40705518100c01031000c0b5262100300c1082e50b4040c0c2d0720f0030b15031044203c16440e0900d16400244188106020400c0c280e509822160003441d850702d6a81c40c02280340d5069003698002c840c19211031910300d0004103084525048a0303000303c85c1603401c2c0c00700ea0300c00d0f01ca8810380c0d110fa044282c0c0724103203030320042065500c10000e00410800d01c0c100ca0400c007411400800502c00588042d115601010010089544d00d5001c81140d4040380d00030490008521703c02340807014120390990100c2c40200804009502a0044d100141d82c0311003a071042000c90360b00e0000941200c600384000150038030000c601c6903070110301d90b1603602254008001c1c00b495890700a0a4484040d1580700710050f82c1d00401c0016546402d030341003100100804130701c580c3c45800413402806507284010040b8103040e00a80e419443c000928107070745055614101510403040f4540c01e07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 317935755 1250 317934505 317934517
    0xa0c0605061f0e04020d090302060108060a0b06040303030f060509071214090a0b04050a0503070311072c04051002030c07052a091506070c08061006020705011214070c020312 76
    0x4030240c00d080d1014414400c003202c66843c41d00030801402c000343c1010f03003011036602e0813040f0090b82c80100140101c0d00108101c0307610081c1c05405002a00704900070a4650066102c002c0a15480306010802004160040d00243c440074094035850f19165074000d0010b030700c0319005100b4505d0680012810505454420311030704d0800c00400b0840c0007550380041e5a03c0081040ea081d000c1c681ba01c3c00015401d100418803540079507a49802081e007041620300303041c1c240e4010301d080b1300c103079035072408858442c4860480819056910301b980d613294242075007030924154112114510000130803030f91101000c09454458082c1044580c0310740411401d1000740d0350352164500070303408003002400328989140b08542c0601c4400c01d40c249110180e002c100380d50458030b000c490343e4201003424013000200300a15031b44440c00d440384400543c9401707006510354415000313a90402c460141048500315281c0c100c1c480079007500c488800d040c50021801481c1c105403817822842030040c034032004881c0a1040035540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 317937005 1250 317935755 317935789
    0x204150302190e0f011107030807060c080f15010815150c0c06120103120c0803070302181822050a0c06090614090409060b09100e0702070803090d08040b0a0c060506 72
    0x131941c2c0300c032401034a6922110302807003018030540b140032000460120182007032a20400002c1040b400110b0040d20344c2c000108501040d0380160104141101c0355010001459000c0c20001300980318084004280041712203e1034203c80724800c012141441040142110078140003a102203800002c10400b0303d114508980308400d0209005001003070000340c40c44803180300e45c1044500341c00c155849000d5504100c034590046a40402c100703501c11004d090300c00714038404540c648250558480156143c0c0e5020f004455042190060a401e0f002545480c4111940200c11222060725603d00070b5010701140c0103100000341120300c00a002d9008181010001d100c00361881c0c1055040c10900006005d05401a0390494403510141c07810b44a2031116406818666000c10006040c00e0001548440c0682400c007150300450301002040e001106540050904882c0744034240d00760f087c0002d9902981d0403044540d100001d55800440d00300900c1c9080504c01c0d801408655a880b040040c0301c86205845c2c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 317938255 1250 317937005 317937019
    0xf050904060b06130303050705060a09120e0109080708010f0b0405091c1211190e100c080f041d100b03010905060a0806100302031605030d0804060204150302190e 71
    0x500001d426402c10301d00c0c04000b4240c24103000b400d402e28034010080354000c1e000703e1000202c00003888003e212507031380014400c2e0180035458150b5280850108500d1142c001c110780e0b07000008a980c46003007900001c040307500490b440742d51107805113402071000340c3d5904901441d01005848034240360085a229060b0309018107000400f04400c0c00c1107991014501c0100800c0c007180300941030701c43c0b00390411000e12400d650740b03490080d4103c22911040300c030071105000190300010080d40c0d0b01d000050240030686450606002d0740d14042505000b8020b00c0601100046000720b4080310301c100404213410b840d0540c590b907031110548090003601d5030003415100320f004c000501100f581a084160001c5000c3e140b44609a0b885201c50305190b0190742c01144080c0040081041d4582005503415903010300380d0702800b113840c25000940d2260841740100600c5100343c002402d020341541503d006201800d900c4403000300d601002002076104200440100760f01040410709030344541510450408050088 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 317939505 1250 317938255 317938261
    0x1506030c0f01180f12030f0801140d080c060901020a0f0c0b150f130f060e09071202011106040c0e37060f030b0a060b0307020703060b010e03011407090f0509 69
    0x450740d0b40710110f80b0743d128440804000400001c8000301400800307003045600c40900140c40d004000500c18880d04c410040050014003c0b04040311004c00440011101100ca82074145032242131402098400b88031401950100400c02c8410340080002840c83da456203019000100113031160200d07188040c00c0c051034040040d0f82d841d8001d450541040b0b0081004804003801c10010b5601d4a06411200c0b250303840e48851590314007035028902c058120300a080702d05141000a49036103e00620071281000003860b05001035902aa031040a860449025a07000e858281082020810103104040d2260000c60005034001425252100d540d0b51001071355509181410780e210f003620200e440e0010075035a03102c00150403425500018000e512800001240745000ca00000441e1029445949081c00c104100704820ba400305080041c0ca40c00107001509400700d800490f01ca043d1100002c0e055072805c02d1866048001c1c07984a8850302044c0e50340100780351911032242c0e204d80d407445150f402040c44004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 317940755 1250 317939505 317939507
    0x308030f06040e030d140c0405030316260316030209010c031107080d03050f0a060b0706020a090b0d09020f01021b0d080d0c1112040b0909100504020c1506030c0f01 72
    0x14181c0c0044004002203024006104140e045510401121005546d100f051340c401c0d401c00c8112503803011115101c14149441d04d0040f81d22813140480e41c911184c14180210104007060300cac0f40c5440c8041031402840068085500041c0d644150340320081c03001040b802e10324a901c6802101d4805c81c2c181c1d1000d00403911950300f500c130700e50b00a10035001400b4401003c0303292401007051210800260f507000c07860341041005030f80403000c042d0001e20030342d08003041480242c025004803021940c0c40700340142d075030041100407a0740100d0740d0016078914a00061030150140c103038001c1c80c4120700859040c0e8010801c070005907038510401c8400300b64200800200b0304189010841102000d015500062500062044001c101c42d1314103100c80c0469490251380d99420b40410501ca41d0203180e0000a1509082015441c40ba002d07640c07034144a1301e10000082d11507100301c0410001410050415529500e4500404e03417102c50090b0483e0810a0030000103810345000142c5103048280a0301c407000c40b41401c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 317942005 1250 317940755 317940781
    0x9050607020a0308130512070e0f1003240f020d050f04110103202206020706120b010512040b060112021201050111210702010824120a050a06050103021207030803 71
    0x280303a103c02603020800a01516060440e00200f0040e001604071207013032049c2c5c001050030280904100131050020800001a030702c800c0700541e5000ba44140940c00f6040c004000c484039400c607614107906202d44410001e07510b402600314107084007800d0001d03a595042079144c0b0281103074050304500f5010202226540a5031100c4600c0403030102e103d605000480660703502d540b09010390303c0061185e6000d851031540c01e0030010003411441c03000e04051807900a00404c0c170710358646020070705a41c6407a8214240e0080085038603941080e40100450b290504099040c0042224600c2c082802c0c1590f40c2e849490034802c0b2043c0c0c0c0c450800f50903441e401c01d4011203c0c2180402003110318801e52004040d8035201c90700c2000e985041c207120590780c0d8414070004000a0020344880b000c084007003803a0143c031410781603e9903100001d4441c0410305080e4102c042c43c2c00c124450251441c00342080b11001c1c05050340050341030760b0090340d0000001e11161581540e440d2207102c0580b0b000c03014004201c0085000c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 317943255 1250 317942005 317942017
    0x402090f040e030703140703080402040c0c05160602010b0111060109230a02071b150806240403050c181506070828032c030c01050c070309050607020a0308 68
    0xa000440c400d14480041021a075072041011201d910101d0228105a4030440e0600380800f0100a02e0801d003065074003030701049001e48001d2080361600b02c44e0400502c1040340c42c4089410078101d41c19103d07608008544022036000c0c540046d400c1458032080d950082a180351000a00c0d00200400da280128010082003140784001c11194500c1020213510010321b01d49002c1c0242c4000142e54a0203460181c0d002d1507107040405554075445070401401d85e0303040880d5001c40311070034407030015659003000a841e110f004104140d0161002030303403804605100c001c1d0082e603114408403880c040e2100c040004010f09403e240e5191181c450008903800c0d0422640c1035455805030405040000c9070307946540720340107100705100c0702808072554000400c601c844042182441c0c00d0400004202c003512080c110f40d81c0c03040d8a030a6410742000c1d100014100b0440b211582000000c00c41e42c14801c1100c8490341c441401640000d40c410b8003c60189841c2044403001903001b00742070344061941e540c41500390000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 317944505 1250 317943255 317943259
    0x306110d020a0504181103010b03070212040f14040603110607080c0d050d1a060316090e0103050a0302160e04110402071a0105041103090c01080919121b030c02040209 73
    0x50064105280050001d012849115211940c0340c9003010401c605c40312121254142c000c0c209074210003842e03d8032080300c0c10f6420450005a6030b0760b482c0310680c5001d500e040880320900b40007400040c40f0300c103003102c02c0c280c0f44000c1130111540055020031066619500001d0305100000914446510308003000300000e51060218034144807031001202d0811b0850300030800030590001c0c0c0c80c16510224420042002c40305400e0349084080000400c219010007404890020783d0050ba40c242e01d401078060704014400c0840c1c010840d1703143c0c6400c94076455900e0b42107016105828070310184039191050384080d20141d0f401b10445540b43d89454555011201c40d641d0060b0303080024401003805160000c0c0d40308004c0c010303414103502d04003d110455281c2181800c50200510034045d1110000c2840d482d00380003443c00003426107510070818141501da807140321407282900f080c0000c0000a10a000e03c40d409074984205619a044a03160506183e040040024030070900280c0180303080c0d4003030410b036500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 317945755 1250 317944505 317944507
    0xb090402030705010e0a0b03010603050708010501110709051005090c040e0903070302060f130602130602070503010b0603010b0708040f03060912080c0d0c05090a06050910020705090a0911041a0108011707030611 92
    0x500c1e4002d81f102d6200f03822100000c5c0d02c0d2410061a5170300207840d507005060038070f8411003603541004060384038809400b680119070b1311100407034400790048400c1740c050200201281898103000e54146040e921910400310440042000104001c5000c0b0940b60442d8154028000980c0d4200b40c100071070170b009143c0d42c8039114668211022030485d10281c030010a01400c2c810341c40d824048064a4032a0642c400740c441d0303041444111389500c41d00145c80c1100e43e0013800070740703940d503d1600049500a039003203884c40c440c2401001013407041c00d801c1140858001c07400002c04d200c00035411a0308400480d501d01c0604403c11406500b0f42c40b907400300c03002480500d0807500f086034090000b450091079038024000958007280200462410034408c440303030f0441b4001090306500e030401140e0028030043c10420050f680300405000e01c209480c08140c074001c000d104010040300380d40d070130039034440712407049002032501400070451440341d0030181c120344051001405014a96605c450140502e60010301403108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 317947005 1250 317945755 317945759
    0x40b010e040f0614150429211b1f0507020102010603051606030f141803071208160c051c0c0503041511010204060f0305060d14060108010b090402030705010e0a 70
    0xd48600d0300034403002003c050044c1811550a03000030440c02d00e4900c514030b0031100d10840383c107100c2c1d038102000ba101c2520305c9070102040000d441c0e40d41d403241008e4007851214040c00003940802c074040d00300c0c070308003a680c0d845071081c0c140a440e180184140580d50b9a04410b101240e009001905400307105200118041d601c0e90355150400c20150600c00e11040c04001c10321090741c140c02903907000c00d1500001c0010311141024200042c1000e0301d001c640103d1010182c0096005100303c0b410300d90088810080b01000300e500030800c40c400c48240f5000200844400003a510800d41d28020316044001804258a141104080404480004e1040c00007041c018400142c0070710261000340783d076003c1080c5940808101414002c940000f0420903441007005011141c2c102c40103041d14080743c0340010380382c0d445c070002c01c049000104c2d018182c0f001c1400c02c081d0746040022641d06a0752210000d000c0d480c1d21406001c0000c00580e8020340c140c21030501840300c0d511842c8000c089070401041900d0541e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 317948255 1250 317947005 317947013
    0x20c031f180b06040e010e070b0901110f07050f0f01021b04020d0504050c040b0a0308043606090e03070c051014030a0c17010e1605040515071a040b010e040f 69
    0x1208450803240b005029040181514052083e46141c90a400080c0300502c0740c005950f03102c903118066000d000001260720711050744908085400c09a40b40121a000c1c1007641069603101c0d95845528411103d01d0307140c14060414414802c2101e8042e0014266005402c1012000700c054040f86504680d0074884010740c8113050141c140203500410141615043c02010b0005440042e00943d0290103803080030000146504102d808440d05000340c0c600841071030400c2e0102044206d5620141040b00e01c03806500c8000358880030894443d2481003011417080340516889015964001e0020001101d00700901d00f00f0f030828800401543c034115142400d19190130b40e080d041500c7c118100c03075480c0d851542c003507008240000740c000004007004040d803400707010b0610b44070024100d00c144401c000c103007401d01d40140b080d81c028080061104800c2c64410104039090303040002c0607158017410940002e003005500052a0299170030802c884800e07070a1408460030148060b00c1203820103042070802001c1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 317949505 1250 317948255 317948291
    0x120c110d17090606060307050a030b04091101020d02010c020c0d150903080a15031203020711060d140109020a200c06040906060206070215150f0d03030c0f020c031f 72
    0x340c440d512490380c111001400394521060041421019038082e8040c000c01c0d0380c580c01070703903400762251520315654090010200c015124040510380c2013801c0072401d0041060a281c41c3c0f5002c0401e0303084801000510314101d00b40c4202004035405078004284845407030800b6001042008d0040d840c171445a8400600d080807603c000d8015030008200c803090080311803a5004160741e00c426107821014450131501c410408800c504220004d040e4006011001c0215212000d440004028101c3d9101c40ba031000304005450900c007080e188a007000c00100f00c440c0c051013520580e0000b6600c041c1802000282e9611421221030b1020b510311905c103010b04140da0301402000606040e034400300d40d1030316002d4064905400035103a402075411020101880140c0a03502c1c0364082001d6101d051251005400704404041c0345c03150320b4000c00c030303030901c40d05068058001c4818510282d40e54003070120500b40c101c3c0c0307541d007034813011342d150708040e9010344100c84101482c0b544450400b00001d403440306000c19402 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 317950755 1250 317949505 317949523
    0x90201020c0130091b0315020a08010b0c150c0c07210803070908030f0406090b0315060d0e0102160b01050108070207031b050414010501020606060708030a020c0c0a030f020a0b0a120c11 81
    0x405c2d0301401c09000300044d02040d000d44100340081542840703288000500440014014404d80302000b040c090707007107a0108000d602450b010359140030380d801c040341c01501135881a40c85411500c1f464000150119903842c4843c208030760f00940300ea00380c4256071050708650004c0c1002c0b00308103c000002ca406142400200700d22402400f00f107968501e049005014900340b584040000c2c2400e01c02c004e80f8070301e07042020424a000310b031015941d00c028010b02000348903803d0050340303d43c40801c2821140c0e075010028003070395004504821040c1e80c0c0300011140444110358550042c1c010355000c0002409901d170780601c0604094640c0c040940700d0340486e080b54545090147c00c02800c0f00108200d51f010b200c0a40c0140e8191070141c600b007881d072102ca04510001c0e01e05140a0303400940801d402c3c409103c00031140c1001000317503003515a00c0c01c1080102082c400240d00c85c040b010030004e00d461820b41243c60f100b20a0f101c0005c440d00c0001c80c80c004103403082007542801154a01d11260210030301849032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 317952005 1250 317950755 317950793
    0x2030607020708011b0e13020d060609090e0a050312070942050a1214090601031101030912030504050c04020f0c0106301113090201020c013009 63
    0x20340d03075251014032820348a181004112403905d12030090b51306a48509a40f04000c0c0560382d0700411849540000002d214408450100c3e81c581200070614540c008080e50031510345078020f010004c0a90803481e26034000f0107005000c0d5001b044441448010794420340c2d40310300e80d82403103150b0719030740c0a08030700740762815200750300220880d01141300031098011028030030140c10700c10f110240c4150710060311502c00d020800707042c440c038050500f0340c00306241c100e04171045030300420700200c0c105500c606a540c0c8080c0400c0340e0b846400411480c0c9540300c0d100e505e03802a085072900189480f00841035004010181050340c0c203003d50250b00e0355607169400106040d6104121203944d0b100b0f4090341e903007111255006200210001d1589280107081180030b40c2c42c00c0d039801c2d130038109480d0130314007000b848070b0703145501d0381205050580120315030041d80001101030003a02541c000800a000440742c1100d180f01c1d07528070300c128451031500c5669030b2210700648400040000780007016900c6c1d11540c010490542c0c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 317953255 1250 317952005 317952013
    0x1e040f0203060a2d15080a02090901110d05070302070b0708100501090b070813120804030201140c06160c08070606060e0907090e040f14010b011107120209040f0203060702 75
    0x601141420001940d000429200411903d031550901c0340f9800402d03549128100c0d4410341c8042c0d0b40c030017a40012105c55040c140c1c480d50f40d41e0303541030544400c40400f09074425103a0a00040580d201805042c9400e80300d102c00c10320f0724000c020342c40010800a441002010b900380880d80001d248090201d0285140c0d85900c0c802e817504038100d006900c90703500b06d80d0403c071089d441044003440400585d0803941d40803062170788519044810a0310480031f035120240c8120320610b07240520404100400a40b03000f0707070315220140d0100d414004644a1411000b185520440001d08294900c80d4401d100c40031502d0905401c02171501c2e40c4513180c00c000c0c0140e541035a141c2d0100f00268106214440030311007a94002d0f900d141000c0e0140c280c011603c00e6040031000400090100841d84601410842d8840d0b648042041c43c40304490003045100030352804144040005101d01d440004e48804a8403c5400445112020b0382880038101c0c01800460f42c200c0360200c0100140e60910425120703a07401d80c010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 317954505 1250 317953255 317953283
    0x715020a1d040b0303090607140703031115060102210d060e0a0e010903051801020c0915010806030c0a0612021b0d021510120c0b160201030608010b0a06081e04 70
    0x214032840459811a202e1490080c0c141d5050f1008415030305580342c100d03105030f00d4815a080504041c07a00d410007101ca4056544088101030b001141400c0381c0352540c0c00c0300c00c640480d04142084d6074040d03400e03501581c0012070301c8445c81c4c20060b1038034660a5503c1810f00b41701e0170043c0e00096400c0b90700850708420300001080049031940c4900c04602440e00c1c001d025a81450b100640640b198040c2001054542c0ca41441c40341d000300020600a6009480c0304241d00e452443c040820824040c03a900050031480411060300e00010302c1402c20200400d5804401d01d0300000b6203406600d0b01d140611103800344195040d1442241d480c400d481175072400303004600040c1400a0400307401d140e402c900d00d00040c061051446c1c24108003c1910559a81000d100e21241001c2442c2020780e488225021000640c01d03010310f003042210000cac2c502c02c5c1c03400c1c01881e403180c40050036502d010322442d4201d0319201c001c0000d54441d01980fa085900120301c0c18002c1c5844410241c081811981500d0002800d40c41e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 317955755 1250 317954505 317954537
    0xe0408030a1a060d0c0813170a0203040806070305010801140709230a03030305070f1b08090d05010504050106060f080108030306060306011403040606050a090e100e07080f0c0406061b080715020a 85
    0xc1c4035170010740558481c1f241100303a501d4100d000900b18007101c21000100d20032880c01c2c020800c03034000e401203001f19541441c2c11000140645000d01a8040359400c180d041c20750256404521030041c402502c583c1202400c2414031900c0d038010602c0005502000203c0c010a42c4801c1001d0014500a42e804900d51404181c00762840c808100c201c000c2022140518842d40c004002940545502ca103943e980c501614000074000404044041e00f01d5190070203000c02c100055004004482c01030f150404401302c0c0100c15110050248180003107a002040000c0303c520b010b1000711390000c2c05060040001c482c40c55055840e401c1241c003110a05d6840000740700381d00e49030300044001c1c110360005007c1441c3e04010180c5a00e2915410f018282e107450003c1d0704400e09100e04006002c1402c1103e2103030121603521583cac3ca035030103011802103142c5440422250312030300c034001046550a00001c8807010030b988041c0035500c0301e00d081d17070b41244284214441e81c0c2c03180003d104c45861a610000faa450345c445c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 317957005 1250 317955755 317955767
    0x1602190501021b0a1203090305090619230d0504080415020709061512050613090803011d07230f0301080a030f020606101b0b0c03100e0408030a1a060d0c 67
    0xa09030950b0344034043c44c40c0003c0319191a80c0d4002c3d0207280c0801d074002145019074040c0a07008030303d5072022020418100c10042d01064140c841002d58074a407026050300d40c00d4006041708494450380384010480755400e44c01c95084160000d1050604501d415600c646140c9031a9804640c03000580040c0020482144280125009010f140742e4a0b0203203044000c0c050306503086116505100703603c8200140965075152051112100301c031000317121403092881c1161035680b0900484182c0350f64800c0000a9400155070349100d0401a1034501c80344280340d0380c01d8884a038501249480d00300c200700701c40039107100d140658020704000005105650f150b01c3c000c0d050240c07004c07448045610203020040980e54440c20044d8001840c1070108071750042c03c040b03080308000301c540904209500c0c0e052104c082c01103c000d602c544104100c40c590b15440741005d0050340401d83e000b4081c10810b001080321500c80c2c0e0700c2800c81a11041c0c010301c005410102094041c0c100d0552403040640c0d820740b650426070028 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 317958255 1250 317957005 317957047
    0x1b030a03050c03060a170115090b031501050625061811091614040506160b0109020903120d020c0f030301051504050a120215030a020d0c050a08160219050102 69
    0x103050381140b400c0c4020803201c051702d2040104200900c5000d01143e02c0a510002601c1815454414116210240308000d0048029114020b01c21959004000600c65007542d0503910001c103020f26203100ba0074003209865103e400c481c42d40100c001600001030b01c61042d000600c0610522070000401400c0c00b203405c0310117611440c00b86045504102d01009035032812070001c4010709020801000000300c002c030f01d020340c0c0c2005420900008840c840301c1640003000741983c2c8610034481d0144c0e2240e0000c0203a014124402d50168404a105c00b60300c1d04440c003600c05900100030040c01c04002c402c0142c60702c2e5200c00500c141c0e410000042c022810204154807080d9010503009240510700004581d0308a000c0c401c40c00d111050781c40719011543c50852145011503c41200c036101e05211000d4030081d0320100c40a0807040c40c1100140030940140c06441000510f07855100c2d180d80c400024030707203107880300350918210f00400403868041800c0c8444a04a24011400181c41e02c1590300420b040740000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 317959505 1250 317958255 317958271
    0x7050c040b06071a090304180b030105060604030c0b0a050702041812090806010b03040c03080307050a02010b0406060c0204051b0c0f0601050409081e0d020a0e10030203061e061b030a0305 82
    0xc1142d20041400d803189400700c0d0600c1130b02c80c2c0c950364540000b10b00350300031034019040c0b44412038902140c02c0c4054202c1c204690044000300710fa80c45500811030340348200c0c800280184005002000000b40c0b000203055400c5150030301e01d01c0d003901680000c00321340c001600407200001030002c080a02c010440400311002450911400840c2132283c075540d41e13030701403041900e100e05c000001810052180004001981d11010054aa061400d4007a0882e00004416001586445520611841c10b4018101101c50300d480301c1e003000f0a0788e02408003038032000b03160020500e02017004000c10007444c07004080c00c014183c09440c201c252002e07441c1c144901079000e2032246003049410781c0450078034021101007220304c200e2005c50700c201c2d5510400c00e00490100903082071000c031f6520516900004150341d6a003084402c1f416980003d04258128001a42e140744c1202041c0399070002c0342800d0401c00b403515001003402c0d007840310240522a403e909007100c149203800c0400c0f91b10b91709406000390754016079130b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 317960755 1250 317959505 317959507
    0x20406111213031104090203010e0a1202030f09040c18080102040f0f0f230d1101030f0509061303020304030606090615020601081009030e0d03020106060f230f0f07050c040b06 77
    0x240c0042d0351941030240000742044100f148000c01c81d50307641d440340a607651f010740284280d182d003968540c0c44101c0c480040e101142403d000d440d40364404000c458081d101c4a5038a81000c4002051000034024602d1240038028003e0302e01081442e20140350b40201801c0c070000da511030400148101088103a80001305c1000d00e048284114441c0c20201020344001c1031020b0003480740e0042110205501c3e1020b82d40007907503011250203102001051980c1c2020a883c144040590f103141d0808540c000c50b140450707030300801c02180d20314006124030141c0a000e0310440e410141c80c1e40b54403084a000340d10403d41250703240c7c82048210038180100d0038110b1b050016181e0f543c50100c0d4240ca46030b0040303c9524042d91084c5500c1014041d1600f92900342e0050301c00388540c102441c01031f0007403549004070300c045103405595400461050012070024070300c003072030036010b2503407078040101c2504640000044140300717024901c0020007440140082d10b000310020101250400180400c460030b000d040c0340602d41c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 317962005 1250 317960755 317960767
    0x260109200708030a1e020309010203071b11010e0310020408060a0b01050a0c1e053703050f03040309080303090c1903030e101110020702040b030319030b040f0204061112 74
    0x2c403805803580503001070000b0617905c440300024445102e0b02c684802c0c2843c4007006022104005501451141c0d200b034a03011400c88013207802d54030b45040400001d009007121205120294480c100d48100d1030300c0601100c408a56140e41042aa001500242095417002c0100300d155692805804d00100081c2481c5c1d24048001c030005002c048008405400c801164059190107504903034410b448a402c1000e8030310004582d61601428810409001602821310b0072162090f8200100050100e40c1900d540c2d01d0041d102c1385075081500001c000b03406020400d040081c1c609024401180b060211031701801c000c1d601001003010440c403202c10b04a12281c0d01805000180d0451309400000104694910300c01301032040494071000344c500704da14030340a500c0c2544c40501c4541c02404129200f12020301040c0f50441c00c0c150b582c00781d03221400900c41c1c0d0b00304d00346131180030f58820740d161071014101090891480c5048001d0382d00907400f1400081403c8030060548030248280c00030400c9584465280c04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 317963255 1250 317962005 317962013
    0x21005030405100e0c10030c1119020d0602090a080d27140d1b0e1e041b03080f19020a080d0c020a171201061e2601092007 54
    0x2070390810f00c80d854903610702c0f282c040404200100c03002c0b100c0040c80d43d448203008410050207411001945030200e0315150400c081840040381c55034031001001c00c443c02074850b40d000c07c04079110303e08064030a203a00f00320b2620345032100551000545411002401101c1e815200289292055060300145440c1c0d80b01500016900d002c41c10200c55112460284490001c000140c4c4511100d000500860140c1b040c40c08880910b4003c0307007103884100303400c4100d0365404010711441400043d0b90781919402c80000300011b00c0d2202e041090004414100c0030161250765854180c0c0c000c1d000308151140c0030036a120a0740b140b0401328001604c5201802801da07141d610a0310718003910021481050310b40ca0300e16a09442004520f00c4c81e038114281c10404540300f41d0102d06548802c08401d800c00b1700c10700114415016040301c1e00c1c0d50f00c52141d03c2109a19030003044401c01141d5403032120201c055400d110b0760003840020140039101c0d1090014440120950348078600660b000a040140030500500001c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 317964505 1250 317963255 317963263
    0x40807050d02040e0106320901060315030b0708060405070c020d03050a02030d060f050a050307120b06040204050d120e010f080f09070f14043c0b100c021005030405 72
    0xd40003541c07500c002038002d200080150112503942c4420b58a800b10015105d00101e503c85840c00d56160b604511031541d583d800b000a85090409404c809040010040d0902c00d51080711000340551090300800e4481d520403040482c01e403043c00c0000e6a420900003140350511945401424504280e02c0400300742d800318003188071100f40901489008500001058024030450341c0f250300c0c6901c1040040d840d000c1c45c0c403812142c0d0013428041c10f115003000c5500d040008110054680c8910300201089141c4e030b9100c00c0700001014903030825000d00c000961a1100451201d006c0e00c1707107101034100d10f0340c44c82c0240203e049055460404c803203501084016070704154101e401c107a03e1500408155200003110340f6080b0503601080d20303084e01d420002171090501e51500314080003128144217003d4200110454501101c801258001d00f11041c010030301440080340c24210602c10703004c5244190000025802d10140d445034011544030440301c411807a1880600081e440a400c01908605180d00c510380d031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 317965755 1250 317964505 317964509
    0x3060f0a03150c030b190306050a020901080118090b180115050d080705010b0603010b031f060509220f0b01020705041413030908010219120e03090f06250314040807 72
    0x9483d68910801c00d229100e9000150103200250882048a1241c030494200e09020321040c1c7e21240f41001048002045000b11102c019050351503019590800307010b5851410203c2c1c0902d641695001c0c0360000400074807090384a6041c0082645654410016880c00d56281115290561203001801e1104c1c1d95481c2c54000f06a070800a60350b214110361070300d1801010201e000c982c5c802ca0200000400d0706400c1c000754480c1d000301c2e8003960311500c80810001059500d0180c1d5001ca80140710f0741c0c00c02d007402c1c1c00c003800f2880300c0c00c46007140517204a12601140c10b280d850060032916511151041d580400c0341100501090ba4200095413442c111001884005400d400000b2000718080051520500f509030160031085c000719665201c0035051807002521640040100b10007002d088003203480351266102010030390002e5072400d250001046030078001e00022990100c001d2005285500c1a0068030851180d04110310031703d00760a04000c2d000c0c0e0920050344c0440c400402050011034004070346401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 317967005 1250 317965755 317965793
    0xf0a0309060c110a0b0306030717100e011407020709060b0702061b0a12020d1b05060c1b01090c0603050c1c05040816060506010809070305120c070e0c03060f0a03 71
    0x700203805483c10345007040c800c80c0e8031984100c00410102c1e0303124100c0001c3d4080c01c400c1b011546150350700c0d6200d02c02c907030310070a407080c164000700d070f4840018016401c03512920001600009400303000341c1c0d52000f40481640c8650060307205100c00d004d03a80f20740c45082c01400c807213140302c1d003442c1c05980001c07010312500040b41c075040c40ca000703010001c10703041000d003046c81c5d408000c080301b041c100072000713555110b0941c0942c0042c039100c0400c1103000d00312403080e89035034100303020f029140e0b030745009401207a00c01010764149808000b40c10311700603000e120b0461030701c1c42180080840d85c83c0c03140090070b075040508400581c04013040031254420030392000d030011201601c404a43d42c0d9513828020407900900b402000d40c100031101140c100400c43d0303c03240c46000262500303034241c0c950074180d81c0d0b43d5885002c000c1113a8030030318049000c404490064054000f0403c200c404c543d41700c1c0d5141c02c3e0b00000b62000743c60070b030740030043c0700c03551809894840303038090103a500036516440e42e2569400f14500007001c4c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 317968255 1250 317967005 317967017
    0x616090b07170c06040602210c03070c02121e060702010b0102100c0509040504060f05070201110a0e030f03040609091b0f03021303080415030b060a0905090a0f050106030204080f0a030906 82
    0x10800c1e0300a40196402d41e420141511030720301c0d10381030506c0039520000611040c50301c58459184880c503468503050042c04464525420350380d1781c0c00700b03841c1c1000822099900c0200f51a0222a1001c1000bc0682c420002d80140f41e1400807021405d280c881c019001e5400d69042540300005a640010b186096a442d06008280b851b0161800d480a100c0d2440e0305130810300b080200000c0c845150000c15500988900800c035556807140200d0886803c0d84160900e06030400c410401244100c104000c000d40060a45103155080f034410341c903603403090b4400c501080351403c08101c2d070001c03881090220050400c1c511262050100700415540186c036040007415404103d900b4001e000301100d4000d154400108e03030307403661900040c80d5424048001c0f8400a07052035403400c0709050000c03d40700706a5240d15511580d0b42000200070051900030300d00215a540c460220010701c180d400703001c2c020031003600d00580e9541400744540c01c05211a0410174244d010400b13110001ea03003d0400021640146009 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 317969505 1250 317968255 317968283
    0x60301140601080c1c020c0f010506061602010e040212060a062d030f0614041503080301050d02030a08070615090c0206010b030606040b070804050a080d02100f0b030d020616090b07 79
    0x11341020300032107140205203004100400314034185a40100032480c001012550211058102182a600101c4203190420b800f803000300398405290b06691000c610504040e4403210f80c100210b000c036005030811706041c520b100c050100505090804401420580c640304440821201054401c41000b100c074503400420000c0c0765610b14425840b441603480003078030500182d80c2d5007940d84444880d40d070101e4816071030510705400f02e100e001c0c512021694402110350460380303404100300004031981c0081e03130540618645400010105002009940d115001c00640d100d40780c811070802034442e400c00d031f01c003514080d00340a01c40e4001800504403010700007016034a944041c0070951314084c5034000d40d94a030004c0703200c0c4100a64039001d4019900240d40c0c283c82c150391405956681c04480480d2009038115030901c00a00e03800c0e410007030442011a001059480c0c201c40441d140c0381e54060b2110041c0c101d98144a4604200c400d421051070840ca05205980d0078100000c0300743c414600b00402100c60940e40d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 317970755 1250 317969505 317969521
    0xe070e0f0d02030303070c060501050a0612110f031306050106110604060902120f0303090c0409020a030b151003021810020d1b14100b090115110709060603020d0506030114060108 78
    0x22540c4259400f50a41c3d49a0400c039101600024200104444840c1003100101d074034100203403d481200c0440da680001d540102c0407c000626981a404500d10001c000600302c04602c6001103000c2c0c151081c0360343c3c19204c141401c004591041c1c0001040001120120b0000e110014032213811640140001484000600c0000d00c14a04180d150481d8010100716540c00c90020000c0d611524940341514590b03040d038403c00040b1440170760300a501c84070055007030000c00c1d642d20f2600c2d0b01582d140c1807aa41e41001e800000c07450308110001100094002800100c0300c003040a881d00c1e03690040c3c0e204481da001680e0080d403218107210341c00c01000200b0f06c205000704210081401e0090704000d40c4142c0c60051010145c840001440400e00c2d2411720301c1e0601e036410003680b0305040f114080c19800c40f0008250f003c543c044421040c07454240718442c03000c1031034a4148240401400d00307031001696061205000003e9940c01008103101ea40f40c400214408450200d416030300c65824a0400b99958500d50 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 317972005 1250 317970755 317970769
    0x2150307020a1b1d06010807051e27040e19150606080f010b0f190309060c080106030f0207021305040201020703050a0f230703080c070816030c0e070e0f 67
    0x802a191155164110041e100b8680d401416255074070b2008a149071502007564600c0ca00745e03603050020b04a0400104140d2054000d004400202e00c0384c001084007500d100d0711590040720701460000284444841c016030a070f0b04607903407040c0c151000d00418207c0c2d440c079504d404d004110300e00c100c3d140c54400c0d000c00000b01003003045041d041204100154807940010480d280c11110900c011031008000b1034810784000650b640405454081c52520b05032004403520112911580d00a0544955814001508074010307118081400d80d11b481d450340c03410074001d05454440394054242c0344100183c1e009a121041020030150007054041860b88031840101e00e003911941c405049806911300308010007000740d9043ca505030280c03075240e12048194811402c1c41724030a040004660140e501040018000c0b4041c101c5d030207600d016241503640d504040740c10a50302088000c08900c0031902801002442451040640024070362010035151480d0b014054140010401d07220f1081e000c6000c074241d0341d00e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 317973255 1250 317972005 317972023
    0x50a08090402070209010906090c0c0c26060a0b090a0603022d06040611060c0322060e0709020417070305030301061b060e0c0f03120403150608030705030d06050604030215030702 78
    0x117030514044d0369480c50420002d04840c020490306601744203040e0f1041c0d22501700e10880030740007079031040d406162282c00d2084070200110380c00945c0c0c0d0040c905c08400000c3c4036082c45031504050101360303207015000b0005502e4005048240382440c041081c0056200c2d00f24018400d060fa03042140800d851741420701e00c4a80605255a00190008004c030340c0c43d921002d100020030703030102214515110202e00311540e0008882000305900c4040f50500001050a414006030340103200004071001c000403078030b05003087e1b40c00079081c2980000307040183c60341030041d00c8100300d205805000180c0c11a501c40da07ca100600c605010072480c0c502c010006c1c82c445040c8862540d0121040003c0104a0452600ca42035003a43e035105034240d450502d0356082c0861484007989a0f154864540f40c11942d40380c85440070344859140f0740d6903802c0049401d28040005000c1c0031f014100850f2600ba405801c0c00503203200e41c00481c002c4409010810068940d142c01d1202c0c81e42e40184182c581d0b07180e82c1c00b20304e0704e0210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 317974505 1250 317973255 317973259
    0x209010e0112060b03250303020d0e0913061e0e0c030601030c12141605042313030e040e0c0a08030a0507060b010509030d030204151409010f170705030a18050a080904020702 76
    0x6c404640f0700c4454280c2c403241224802d03000e440d010301e0352a1041c0c82840100c0d030040d400410210019010000100c0c1524a1510440700060b84065000c141c8143c00040d25006d46d000340c5d29140e6100c1000100841311b403003001200200307107540c150355035042140e0051142036041100f5030284010001017811000f40c9809440c1150081e000c003040541ca0744000d80301d11030280d840d011900c00180005180080d140301c1c513100780c1c611600c0c0c201d8155403214400c5001e404010310b803041044165964000d00e058003c0303520081c0501c0c0c40c280100174540b01030707611884081c2d20810502038000d41020079200019000300d00024000465001a125031003080755181e03050107560a200d00c00d030f416a02910030703100722802020401303000450030340d842149007403103503a03a01e01440070881a42c8952150b144100b030518081c0c211085203850104c0ea51400d41340b11010490100030082d00004610540c0b8480c100071940d000b52090a86440d902c9040c080c1c03000d00444e000184941e000d0301c176078048615190340 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 317975755 1250 317974505 317974543
    0xc03060c030b0a0801020a0905060d0b0406030809030609030c0a11040905060f01090e0a0b06040b0303190c11010c1211070b0703020106081002040b030f0702010603080f070209010e0112060b03 84
    0x100c400080081c2207a6842e00d10898025070086010841403098031502d1081d40c89420341141807034100308407500055100c240103510340d03120140a84580c020b1500540c810455141c640702050101401c22400030803031003a69106010030f1640c200c2c0022042c1155410000303c82400c40700c43c1c04600603203011000540300344541d0341400091b496641c8842d0484c4d6007a4010450031300814501d907150390765500060802000d04002c14260b140030b50212541150040840c3d25000204041c0d00342901040c00719800700301c90030311090500c035a19400d082c80309400d18118080040503561030240704280c00a110030480c3c81c40c010401c82404001d003c0c041c1c0b840c40d000030784801807490024003070701c1640903c0805018480c013112141e0b00340c9c002e50301603c404400076410b6550345c0849400c1947c00a042604641d00c070440080410b90780c0c1300400e103841171810209e544201da4014446003580c10390000c02007000315801004040c094032490b20b4920780c80340d00800e0124040c0300080c44c241c5141880400c2d881c1d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 317977005 1250 317975755 317975771
    0x80a0507090212180c102d091406090a0e040b060a050603040605060a03050111071a06010804030f050706060f1e03080912071701050f0f01120201081f1e0e04080d090c0306 75
    0x81c000070102160f582d50134030110101c02002c21001c221042025081c042030023000140640c1407072156200d10240040c006a0034880240e00107140307595145d000345018640300d01804180500c3d940c036a5885041514140752284c60f000c08510706101c01040600741030750399404145d460707031202081801550880300a100c0d180040071b141925a01c88802121015102235146c120b007510101c010380b1402058450102540e9141c609980b445044601201004410014000056403620980380034014100043c0341042c01c0c09140d0800c02c00d4900440c4c240d500411701040010003103011940106402d80f0942540080b40141034588941a0020101c0710049040c900042905500040c42040c40d4034142503075840720800401c56040a010b00d03142640c80164050143d4051032945420024644c5490070b04400b1100aa5034010981c010309111441d444024050803400ac011074080c0103200c82e040e00c02c1c2400d070b8071a8014451601083c840c0c40d180c45e140c07018030050b14510401540c004030240f2501c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 317978255 1250 317977005 317977007
    0x3102705010c030b03161202010203070b070801060306080313170a020301050109141008030f070c05060d09060e0c091303050705100212011406030a0b030c0604080a0507090212180c10 80
    0x1446000b01d10029140144400d0245000500407854001c40400f405c06c403030070302d0300000034040c03400c0d416810352000b00039460004100c2c01185100718440d03642c0100c95410a0360040c1500d01075841450740b039005018042e0000804c0c001c400448010041070000240c1081d9524100040113102941c0365203003000018043c0440d42100d141640c1e2003000f58880e0b511848148082001801440711550007400b00c10054002100100112800761400c24030103603885000a03125448803041030075540d100c0742e00c60204403490080d10300305103040c1d0142c1014011000441c0307207124010400500a00030459400900d0f00034011580219040020781b400c0b008007608520180d4815a030030000c1c0449000001100f9803081d805404040f0020f14080c90f6854402c2d0540291013034000180c1d0500a8100b80e40250703460100800040814002410694486003045410112a03a0104404900420840096a0700040e44550143c03021021070b01106441d100189404d5010441c145c0000c403480b4442e07221 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 317979505 1250 317978255 317978261
    0x13020a0b180f0603010f1503090609260f0d09110301020a050301170316060c02010b0916030609020a02030702060c012c210a0e12061e090a020310270501 67
    0xa1182618080b0803505824107101c02848244038030303107021188480610445040c810010740c01880c920b00800c000702c03140ca40c0000c0b05d0440c542141c5000c40800d240345030301e0351080d158075400391000c0c9250a0900310240311800707100f00c0811480e0903a80740c03468010441559080c01903400d02900071502c5680100024005a10a028000030300740c0f600b205801e51040002164000400c043e0248405d0866640c1e040c091301102d00c2e500c041d552100c0c00c4a02640303c1d01101d80c4919012101621649003140010b0100d90f4140c001080c010300400821701490b400108603122503134103860a540ea030a10485c0709004024401100c0b068101c00d451001d4052030641803848021410800d5500002480803803450901c2884850050355109110b2095014081c541010036203602403d09200c1c0d442c860f038400e04240040b681c02c0495000300039020310141d01d031404140d0111030030009014030345564000035613a200d5a0f08954003580ca0701c4c00016264419040c00d41d9003076a003c44542d00c10042d00d451806 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 317980755 1250 317979505 317979547
    0xb24070c060c02130c0512040f050f1b010c020d0321180b070c02011e0215160809060405070b09060c01020c01050609100515030a020f0a031e020a050313020a0b 70
    0x200e01076410000d9207140325441804d821105c65260145800001c12208000500080081c0c07410302c512440703140481e40520081810380446806050003650904210403940b00f48104241000b500030340441c01611034031360007542550141890008210028071415100607142890a281410070103120b80c00e445198140f481c840c030400c5009202d5072103600c1298001031100029000030f40141d00c0c800e885002400322200c0389140c0c4180c1c0c804801d955171142c810402a640400c0c03000c40a868203002030350000286410001060107002d80d4103003a01c640b9655042c5004040c9681c50000d03101d80e0550b20070b021104411560700080d516560010b80c8035000304000c840b810b0007403030740f400000c140b14804a507500566000506003498085091404411608003d200401d903541c00c01504201101440c05450401c81954000c1805d54101d2610314071048080b241141721307401400a050000d8001d0b05581e0700480d95012842c061510340000b454409455000c103000b44c000007042d607040c8038107640701c0203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 317982005 1250 317980755 317980759
    0x1b03051f0507050c100b030708160306050c030115050d0605090702060a0608010510030f0f1e1e02100e0a0e100603050c07020307050d0809031e010f0b24070c060c02 72
    0x7042e52454020341d40c9110750b030344440840c3c12a20948000c403500354480500c011001d0102c800ba140ca480c052441d02c8061208200010410b55042040000740d00603580e1021161804505552500d001c00d06080c0e021071903101404404544030220b04040d620810050100501d8000341d42031015002e503c035034080d41c402501c01e0130f02e040403c641030140900d500444454413110501031842e210454002e4044008071070109110380880041810302d14142c43c0119034100c011103c0c0854500080032461040300c0e50384200c604468480980d403601c041015110040c10b12415060144d800550b41c840160084416000c40fa001e0182e0380c501e2041580a4484a0318100300070385401100492901410f503000b5855403003c00140070604201000152040c46200e015080a4040e000642440721a05001c010700c0c148616541410009000340c2c20341c17082000c01004040c1200c400324040854480442d0b00c030447c4900102c0308803200c1382c00c4070074440e0048041405280c903014000c0400002d60030030380c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 317983255 1250 317982005 317982011
    0x31101081005060a050a0e030102030a02120f0705030c030402010c050615030d0905062a15040204111206060c0a0b10030201140310050f150c011e1401031b03051f 71
    0x2032150902041c0391054550040c0064102904110211515403103540442c0c02c001e00c901031a1001e44090000c0c501880e0481c00241e1203000e019141081c0702402410341c040c103850002800041500300c4100c80d00900505a207aa80743e4480c00180c400070b00310b40005065105003000c100d2500c02c44c0c41c00c3c80840600b14151051452001411190f10300c03140034843d07000600b003140090360b8460360050030714900e440a04004020948802c282041401000c101c11044030204003c00c40c94688550039115032040b0170309003440100031265849500080182c0d019500c00140808003480c100100451585e02184540b000c3c070301709400e0b400010084c03000301c2c04181d26114500e01400001300762403280c140c01c0c4000001900d00020052a04984455541c2004d00280f104852110240040c07161402507800401d0b903052440d0840d8100070030740e000b802d0b141c0c98805d850711180541250381e030449401a84600025609000e4401d8151141c0d100400302d10541514400900440d03124940819401c42d00b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 317984505 1250 317983255 317983261
    0xf11060403031e020a050f0102130f081e2104210506072106080c031006050303120a1107030818150402090405070305120c1b060715020906030103110108 67
    0x110855014500004000c290003416190b0b44510101c0328071650b241a1040301d4419005480c0c560074a41c100b180b48405940000e80411040c00740b04401c00100118100708913140d103000b00c1301da19010640301c803691070840320241010110040200da480f20b02800d80d600c0c000510041c03c04960b41c40361141035009a15480078502d241d0b05201147c40c415003050240c5045da03143ca07030854a8564008200c3c005905081d1040074a400910548015040310300050079283d80000805144c000c5400800c400281405002d22241d10080141c1e03082d1008040c00c0c0c5015110314681401030f00e4000f00400d001040031881605240e446240f0382c1c001c0d240740400089100c10507215035203e201d0040d4a0120311140404140141803444030a688503018105550300c840c3c60f555030f103003040702215580310300c00c402146c004884903052150a04110070040324012143e81c00300452000d00940790040e1100c015401c1e2410030306050b4045541055005101a5032036859142c50030512640d03e903424000b840c00d03000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 317985611 1106 317984505 317984509
    0x160b03131410020702041406031b060702030a03090e0705031e0c0c06010e0114030a0506061005071203140a0c170601020f0604052112061c050a0f11 65
    0xf40c0e45419600400082d02c0303450444031040c0c1400c0040c012142d07000030f40000010a010040c2400c00c00010024094bc001c4107806501400707080640f004055010340620305407a422030070050342e6129144101c426000071205c841150a0500203420302000c509a560b81c007142d880d20360362070620001e420300d050200070f030b00134119403031303500300601c00d03110107031910340f0040b0b4241c0c01030140404c591035481d652200500454003407588212001d074068891002c903090a5040700000d00c00c15210700740200104a5070000f89400c000d1000417483c00f09641c090300700d84206598600c6a041d28040c030740c1207000c0c805007500d415032103492041c0700c40f510140080c621490192003d4038000c1c610707800c014001200c408141386d00400030404a003580384d000d5102c54004200355400080580c0c03143d242c3d043c50705c3c0d41e000685240700300b440040810a0b000e0249102074030402d8081c0100f948082 = true := by decide +kernel

theorem cover : BRFrame.Cov 317805755 317985611 := by
  have h0 := BRFrame.cov_init 317805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 317805755 ≤ n) (h2 : n < 317985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
