-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4706
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:28:47.709136+00:00
-- url     : https://prove2.me/submissions/fa5d3229-ab40-4ac8-b686-e613e46f544b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 846223021 ≤ n < 846402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 846224271 1250 846223021 846223031
    0x90819140a1401090c050f0d1209180609060e01150302070602070b040302060921090603061521100b19110703031115010f03061e02210c0f1606 63
    0xd15107842c611010050401982d555000b80801d00030038030196405420301744c441c2c3c003d144010010564443d603962002d4803102174440443d80c110310540580004010741d0502d84040340f03240c0c0021000344076511800109074a8203000141c000c0b91490300700d0485400813002400152207020a44c00703503120a20840e12154204200c20002e000da50560b03002d58000d9000741020300c2c019040e14034000c1484070110002d60320104e0842000515400c503840070405454054a035260000031840000c0c2c009502d522428000c11100d4241c400386680c062a80c00d0350440ba1126200c0aa00e4400c0d2003c038040e14034151020130052080b1b261480d02002000f8142ca0100710017032400c2e41d4a0700300003481e041100080c6016003006829031042151150380c0c0500c201c1080c0c1540740406d40001404a480000d20032901c0303413401da04c0c03500325008041d440da10000080d0b58525200415501c1c04a681117100c000511210200e4800c0c29403100307507003050030300301c001500d80707420800c007a80042403000c8111111600c42d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 846225521 1250 846224271 846224273
    0x90918152d020c0105010b180d020a0e040515130b0a0207020a0503010c030b01020c061912141005180402060f090307030206190f02060c1902010b031c090819140a 71
    0x71aa25109003604014010b844507000c3c5100b6094074030603400594919030a008101d07032040c1c2d61135071040018040700c049a0040c860700c0411420f04e459806010000006820002402800703d41c48041c84800d0361040c8203540d8092803810211410b4202034115610702c40041d103100c84943c003d0500900050011038904d6031000007a0a6500607070107140042d4071f6107a91281944c042080d014a4070f002c40f516802c01d40c1544c007811401070031103a040d080215508007504024070300c2d80b104100c50840c0d03801001c1440c1803100e0100f207043c14440c81c1d000c0d00d08038449202060400c40100d00031540100f09628040104618608076088856210b600d4064100000010f03581c0c3d4005280382002e13034110101e403010242c0013904504500d803a1340f0541d0887e07c00c010078034100078100c1e2121030788030b048102616520300080707004010300b261060301071140069000169107042a281c001820f540e881c0c0803a241c1300c0d41c8240c0c603044901200002a01e40c84680360003c1d0b80442c158140010070000c1340d44146c05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 846226771 1250 846225521 846225581
    0x1170f070e041806201207080403050d09030c030809030a0215070210060f0e16090608041a040c03061109031b1c2d050c0111070b0a09091815 62
    0x3110490713281d50f0728450700c0300200082c80ca00e664042082140350404e64600500c0d4118400100080d041003c43c0d800074003050300803002c1e603902c07207503100080291044c0c62030060301c1220504c0c0140d02080080d00029601c40d000011600c40344540d601420040002c020240d900200240010302507005019013103100984504c0745070014401c00545162175480d121002c0100070000d4030004080c0795032000c0c0a00d2580105d640000c172340d0740c1c0c9024030240d0307210308003401400450140301c00810f040c04140700a0105070b01c07142050b2806120704100c441c0c10100884224481ca08030341c4c6d0190426030513900d894000300110b4480e40409054507500d580156040817010901d100100d50081800510a1100b1100751440500c003074607402881540d0425140c0942e51705124024034100051964000d01010062140100600c2d1a40c100e80c0c07219035929001d0201c40c0140190315800d4601510040c002c4800f0700f800078126000003600880011080300e06000e0800041120108604191400385140d6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 846228021 1250 846226771 846226811
    0xf100309141f05070903031d06040308120603060619060c060204031713080c0d3c02040b030a080a050a020309090103210e01051611030a060b01170f070e04 68
    0x20081401c1014601504040341220030152500c0c0401c128800144001f0760007a41d40360041c1400c1200c400a0004407001403542c0c80380b50401498500d01244101210059440b07403800380c0d4084080e10201e030b41f5402400006d2003c4641b06c01b0740e4459103000c210250207222002038040c00b581006d0b141989948480d1140956182c4080e04482c000544d104903201402c1c1000c05458400050300c10110700301d000441e84032074400082c1c0f00d89a1040658541d8000304100f0354500000100605141d100c16001c0300d000042650030b134012801e00445450b58035000ca440e82c02c0c964405a01802c2440900c4101d40035040000c2010a503c000c2098500f165100d501c524004c61040e00c600e185604071040c0c601f004a95000d02c4810b20a000802c01c4103030380c1040586140f10040214006c0d503000d5030801c0c0c00082c0c10400300c1c540600842c0584070600400303030880311180900b1f0b02e8081505490414009280100311180b03d403c0086801088285205442c035507500070000b0804205004074689901d0801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 846229271 1250 846228021 846228043
    0xf1011010e0a0203100606090510050c0714011101090c0e060d05070b13090c0c1b03150f061d0a050a0905160e0112051203041a150f0f10030914 63
    0x1074841202c400440c42d0810241c00c141d06662402e0240501d416000303000c00a032800707594460701c491511046078600c1001560154044c28081711034040c3e5411081040043e0a103e55000512038171a844117a5414002d600003d0750001c1d03030000300da26143c19102030050240807641d111800030002e20200300200610400b414003203070555600d413200c0c00300344406501036109001d000d090030f04182a05030400c0d8000f0305281c000402032450b0f48080f251a0b1141c415070002880914501020000246241e000c41000a103490082110640b200c07141c2d0800d18400c3c02c45ea4050b00b411000442141968000380d0304407450402c081080c040a81d903071803c02c2c5108401400603c100e0b4000c016400c44000c4450040c0b48100f400da14075000341e251240c85860440501000300800000308041080e190024644544501c114107c5410300407161071740c10034018140c0380b1500c4c40600248903480e00420320035043c00d000302481150002e00600307a015040880c0c0c1611030b00e00d04944078049c3c0009200d0040c3e21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 846230521 1250 846229271 846229273
    0x9120a050c010e01080108061302130e0102091302030f1305210a1707050d09050c090403051c0b091311040c02030901110a0206030705161a160309020f1011010e 70
    0x38500400010b081c0c3d8000300006042210110041000100100d410354100032105081c044462141c00030030b030f031080c840d544100903616000401a001c5010b60103080c0440d01210425000d05511160006900054a0100000c111480403078004880c0e203100d404414452029601440c03002e10082c074903682011242c0c5100e010000d00030070855030000b02400e805103081800551400c000400810600900211804c059510116901807100410441011840041a096952070103103170041c02a0030040028a121145440142a2203940e001c1d4294091000d848411940d0f1102000d00f02d440e00741e44107881401d61100280b1080e1603602403800410200d4000f165510340d07220004010003281550561079410000c803d400507618901125002055441c000c1d4988001e80c48080403100d012a000700310402d030100c851000612004044d110b0691410318a8541c45140d03c203409035009844000e500244014021f4030a16000c94481d00d0940107141902280001c003240a007100e03801c041103409 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 846231771 1250 846230521 846230533
    0x2090906011a031e0a140603011a1e040c1808030a020a02041a090403030509120301030f080310170a03080606030603071e031505101e1412031201050102100b1509120a05 74
    0x101146c03650341181c2000c801d800800614132541e218042c410b00c0c0058041c420380c5500803081805d800380300b0302015410000c1c02040030389066417020300030481d850b03242c3d180c42483c800300080141010042d69070b0100303550094000300409500308070080410b664440000801da000c04601503e4000b03000d8401e0b84203440004190800c4260180340608001203118580410401480021011213032680410341c442007894883d20340302000884454a9001107062041d01041204161000035410050b05d0203a00d5545158803901c1c207210691000b15890380d0144c0c08800700f00b0503600303080c1c045440b83c1100441000e44584035074800000f68103108404603072a032a10244213505081c0148403004100d02c010800c0c50310b8480403058a038036400d104030962003040402d0084152100d19001c030342500701d8801c0c0c81d66081095210103200000380508d5005224824200c540700a841c4981d4500b5503004180300240140f05402c406a03900c007207d081e8014484045141c05054204000803860b4444c1001d491 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 846233021 1250 846231771 846231791
    0x6011412100c020f0d0c020f060c03210109051509100b0f13080a020109030b0a1e050414031c0f0b0d05100c050909010905071806020a02090906011a031e0a 68
    0xf14103d0521034922894005a0300001740d41d4000006503011903060b1840b0882e0151780001900d6400b4965040125000c00034208810011050414004110070034204500d6625940001d044890032a100b6000c890018100300701c1c2d16042404c07a61107400b004841c844c103912030b051580140c20450f844050040c01045088240390080510001f9041c03070700007010803046540009240f0103940c1300280141980740046000301e0b040f40c0242e9802c10310740305a14140408072500d04010700c0e040340c05554019075419058010781e030100c21100a01c0b041e0000545601c00d0315011001000307182d0450a0182d5941e0070701a880e04e6080198207264042e201420441400041c460255035174043d80b242001302c10400100b10340c5e2481c01d6141507541036a030005541c0c1c0c45846c103441e00000d038000d504503254890360000e4071541c001143d44001d4401e0b903184503151240505955150707000e01400156516822000266110503009541d020707104901040240c0c2c0140c55040705d1540c02c0c4c404c2c1511a4840c114a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 846234271 1250 846233021 846233023
    0x23030706091802090a1205030d110304060e210a0e1908070905011a090402160b071202070b04020405070c0609050105161d060d09020a080a020108070207030506011412100c02 76
    0x7240d5040c1440c010340c6400c401c80009417040086000359400c10041102920a0140400c1540d0800341030350030030003010011426191042c0c008503422640d180c140b410f60fa50002d00440c03180d82e00d9000e03910403441c00c80c55140602d125080708280600b0420981e042403003d07a121180020303100c40411158012500303181c10a4108842d58004409190800004000c814440c480000b44c7d500103c040a4840740403000050191041c0140088250b22612801017440404840d2900511b0300780c0340c40c194075030507020200503030064600207002420344900107405401c2c41d0300305544c001d00a20f09418031211aaa5110071103140d80c106940c5ca0b0365a82c20001c0481c1001d44a401141c05810300501c04000c0e030380404040900b07124000d01030300020404441c4da01c002d8004e0b0350b440ea80207001070f9460381c64040700c2c3d56401c1110b038186c1c001080c09000c2580c15002143c56019250040d01500d03c1d030382840c2c070140c905a540a15039030084013a201c40110380c5018406007a112031040408208022100e00003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 846235521 1250 846234271 846234299
    0x140301060f0b07020402030a1d07050f0f09041709101e0905060a0e040204170a05071d0a05130209070f0806010f0f0804210207031e08042303070609 65
    0x40c0c0803a40340c003090041c1120b95094030051035044030050f0b0741ea03950009a1014252075881284140c03900c0e80050828031002c1034240c19500700303a614068002a110070800c640101062940d0002842c3c1c01241c01300b81c00e8a140c0c07800c2c10009002600c1c2c40385403000308a10f01015118000040c07047c0c03501d60180800c6001051118040d4544109601d0400300010b0882c4241800001802221100e0201c0f94903280c05035002442c0019502201030352078220705480303401945040301e940c014460013280700410010044244006001203016503518402081c0003030001504075000c41ca0f00001d6000103a0b07407961060322a810f10790352802c411000c05e42c083c2811340080c0003a418010304160110384544d00480400751400d05241400d0f1035251400e03e401c0c074001c03c0d080700400040303583d0322038145500082e194084a215080d510742d04a2140000d10041da4954401444640100320821119801138408404426801455005900c5110009140c080503a0005002c9030551104008508480c801d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 846236771 1250 846235521 846235529
    0x30f090706030606050f0c1204060216090c050412030302070204060b071a0603061303090302060a0201050f0717040206090f0915040f0605031216080a0816030903020d08090c030714030106 82
    0x41401a9802c20138041e01501840e241402d5a0300b000c034204210b900d040044140928504020307980e501e403111f40094a070a444281e241d14200c2203080020704d41001d2090066108195850038241401c0100100114101c42401e804042d020701c50040940c2d514424a8001c0c0703a410b0602e036a0310300500e4400180a451001030607018017507004c00081d03441c0402c50903805a0081c0344406102c4c0384d40303800e840341c2c0441d0700041c0d00400f000c0303108000160151700490241c06000e040c401d4581e203000d400c440600150050310a80030f4198003003801410f0a1000d07210030b00c8024064040c0c0550000864201d42c03003210608280b44041544090301d0030503110b81d0280501d120014000d86003084003081d5603840d4803240c4a140c000002e0410b0300400e00c0b07168214800d034428a00c90351181441001010500203460800a21000700741c000041400792048500f0194076070043c101c0f500d400c0000360b55441000340080510b02030b0701c0161507103607404d0080d5005401e0319900d0352001503042007850700312112030300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 846238021 1250 846236771 846236777
    0x503060448050306040f060b030304030516060905060c03041505091c030f050909060f011e0c030207240807050d0f06090b030a0c090905190b181906090203030f030f090706 75
    0x428403011034408000072080715084000450000d1805000c00c0c4ae6100e564009000d074020055041000701c1c2d020b07100c40880312107555520403d1f80310010080c1d00c0c8a07501805030980e2040000700315030301c040112052190343c5414aa81041084400300309112030f00280e025003c5c1600c842201090381001c44029251401d2800034246494200840c00031000030300703a580b040c9010031503490300d60300c07900c026500f41d40190386002c0700000c050070261641c821000110094020901c0210311b41c0191140c20341e1654000d410304120504001d030603201d8410151448041000401c00132505c903c5030700840c90700c07107109d6000060107482d0128450860780c9a111451003030b044586505e0101d03a0705100d0000b0386468510006590110307180c4180307001e03001c176500c0385047c1c581814141481075204565208400c048004080307214081d00319500e4211041810b0041000118581c0110f2030b1540038002c030510250440b03140c4802030085d510746800c1116000548400f0780c04000003032009102d02c40091170542 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 846239271 1250 846238021 846238033
    0x3031e050c04060c0501060b0c0d1403060f0111071e06090f15211508010f09020306070c030507081801090602030f0904020c2e0c0905030604480503 65
    0xe050562144640e10880c41007001043c0302d40148042940880b0003003459010708e07565a601303001c0a54031000c184003103001280041080d8131000c4020760441e0701c03c01d802070500700d107084100015602007501001c90038640c4619580131403c0450204c151010010000d400001e1a191076001000b01c011a00000c01d100100c00d0b0400221000161035012446681006401c0120300c0d100001d90f10255150250075505280800c0072036040c2030021020f50f1104002806403144031031034241968042180250594441d1000a05442c428201001c510740719140c05803901c1100d842d001040d8000c49020f103039a00184021001ca986c10142040007488140091402c00000c184510560702032022103902554000511071000c4a050046260007021450901c0130b495401280c6a030b085a4420524083c5280c007400c41d1001d4041e03a5024200c81004004002666807680c1c0c1210280c41c01c401d0b038103000100c0041020408580c02041c0414020150f03180301000600300ca09144030065101c54065040300c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 846240521 1250 846239271 846239281
    0xd0c020313140303070807060c270302151c05060109080703050c040b0607060510091802030a060e01090209010e0a0c0f020604021e04020d051e06031c1b03031e05 71
    0x8402045400320b8101c086045003020100b81184120f04000303108040015000f81044156400032040507040d0355070b0f4141c01021803040000c407990789034181d40580d005004200628119589802d0300110071046410402c03074020300c100c03440040702c145036401d468004100e0340356848034561000b082c0e00c0005001c4245507407115034640b865444040e000302c2d2541115840d940700c800844481c2944150104031503c1e1644d10b00e000307c0c4d2140601c4c00c8903800c007500940d58040244005c00043e4009014090701705c90b9644050090a40c00740300d05c159521468642c0c0541d0700c07108120f00801800c850101c6600d82201340b0720031549142448410301510501030301c0940da00040050b8410b6050f9503510701c085141008902107401c000e00d450b4007500008011020b0803890b04198041c052811400231194648000711130782c54012a21940c041e03006ca81302c0111160380c98502000d5115a040481b002100341c0b011310015152100c2c15400f0030340302c014201041d10018401944041c071702c40c0402183c03c0c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 846241771 1250 846240521 846240547
    0x30705100212070c03180e15010e0f0919230a021602310903031d0c090c0d06030f020306090607081f08030406020c1002070f0909111201020d0c0203 65
    0x8040d1043d403c111502810200709070040244240040381510040c04c100d42c0c5981d070725480340d001c940091840c064445c5900c60b55001c2c210b55441d0703901c0100385000380c3d8640c0040c0002000014018080c0c00e00141d0401503e802e14814450a000d081015103014007002481d225078100140034800c40e17610400c49a0f5184010b070b942e24802d0755046070314152030702059040304034010040224038070b805d101b114103a41ca440b00342e00601e06184680c800740004c0d00c0091020750720a80f00100040c10350400210040350b45412074580b0350001e00c2c003030098204152100041c0031500e040e0811078040903c02c000c0815458100012903000100c0c1c001428545440c1800502c00380010b0700803a5051544800d0380b00c141158884070340038142d018120b1ba225a0f407240e00a50f42c0080020b020302400c0394007081011144045042030580b060b49a00454140c0340000e035000810b520b40c41a184208141031084040e6102030300700d4548502d000000da12804a0507003d01110703c422900000d55000304194103100c0c103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 846243021 1250 846241771 846241807
    0x305061017070509061f090f05030318060c0a1e02010822380117030c060103020607060e010f0f0c1b0b0921030a0606050f1204230307051002 62
    0x500380c550b140262128000724102802c83c41d0780c1508080441e544043ca03039440300e41c01f0704440350003c40d60388060b07503182031644034815900d07281d034030007550031500f0b40a0811400414082240c003044031400c41c0d568440d10a00914032046eaa500c92140d0b207400d0a6680c0410102e4002011604040802d0b840c01c074184035a6040500080c07104019000c83d90300340d46075070704103000000006180c02c94640716092403403003c3d809008107941c0200007400d03880300b5000041900e20b802e481070010f0010340d085408124094105210440e41e003519401300c0000e0302d000b0700808280b0280c2d008003290005021480300e055030b50420354801081030074058048c142403030404002075203802010401042d103914902608040d8030411180110600588603504901c881e40194890b0042d0f40e020803410741c4500b0100c81320310038580034a41e1514180960901900d69480041d0001c3c801c40b000e0550b140381d16404007000310a0300b00c1c03107002e40011800d0000c2c464284a101a10035015408615000d080034140e120782c0c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 846244271 1250 846243021 846243029
    0x60e0604080a0f140a030201020c010c0801210213020f0a09062f1507050a0806031504240f02090f040504020a151103310e0c0c0a0606030506101707 65
    0x1604140d000010b00160110f84c40c4544200e005546070980b180c28068003035030000b85c0b540480c0d0710b4220600d4200740300c2e04a140c1130707400c011225a075641c0929244441408503804c02d980c04400b41d0101c54010400744018803108990614458499810080245c01400294040300901c800c40802d003101d14003001200340c01411306e5203000065040081c400b4a07001c0c0007412121403405010078010134a030800301906a0300303207540d1280c0494dd100741c05c1c580c991001404180041860304085400900008015410f01100c00004104c44881420b400d042c0c489040d02d01c15000e600081e20351070340c03c14400624844a040d103041c49503043c0380d4003060382001d03030340726515461b648102c41c0d4820718428500c04000c10081d10480e500da444160302801c80c0242e43c503030100c04074044060f05005450303086170001107070351001c0710a410341c3e62003c003e001e552002c3d03004030507030080707021b0200014558440e01d80590b0090005103114540040c00c0c003c040c1198010450100f002f0014640781d820003d2014240c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 846245521 1250 846244271 846244283
    0xf031b1905030d03060e09010209100e0103020c250603150506090d151506210e0c1c030801050901151416120e2706030a0f0606060e0604080a 62
    0x4452004030290350a1040e04801d505005030002101d0059240d04401d00752201300001040d15110081101e08074895541c1c000d8001030041d04101c412406034110405541040c14050720b0200710300e4043e82080262841c00d42c24405200c2e1400c3d4803440e0120600c0605800d003410880e001d0b40c040124070004080c455180700c0c443c002015211501d403205c0d242221580600c019031b201448001c040082c15a41d01c0d0b0036480c0000b01d00000f1918410f00ca04401c114270704110301d202d10000d425481c003425912a038040184150000030099840c0e4000709102805040b101140f04105442d0050807158181d026510481807040180400380360580d0307400319072002d0300b04a40d146054501107130050066040505540030100203100610154a008010039295a6601008100e64904200c24201c203c450f1007542d26042d04140c03101c0148050b00c48e04038a009003110240600c0341c0d9803c0711155650b404440c1292949800c101d20b0740c2141c400452001c00301d921130f003400d0410032516900c200c0c0300805408 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 846246771 1250 846245521 846245539
    0xb16030f0c0804080d111b1203060f0f240310120519030207090c11010c02010c1407060e0a0804030b06060304022d3703081e0903060f01050f031b 64
    0x501c005ea4840c0a40c40b80c52000309445100c0050911242040d85010f01c00500030101b200f10024207050440b0700c1880000c003800c0e414071005052052030580d1428036a00420b000d028030414108020b18002e040950103070840e9079203480300640016110983c082194251200d0782580050000708440c480c440c454043c5c4000f00c011410224a0045550300c085195490807604082c040d6204011b0010400c41e100280003003442144100d08841f13a040115000507400d500d20100c40c80310074002c0501c1c0f4010031002c81c0c01c0421510443c101044d2030300440d1651000a0100200444000015440307001149c81700d0552130b042d00440c08031001d42a4a0080e0b00c0d481c3c4841844403484d2401000014010300300004a1100020411000740101c007901c010b011040e1220184040d40c0e41d00030140d9a104c4005401c220119110b443c2d030350065114030345089000c2c00020301c1610300300416031080c1d088441c210015454501880010050003c666000c3d8201c05810f43c0200c081504006590006440c2048 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 846248021 1250 846246771 846246787
    0x90204050d031404031209090e062202030c150702091305030f160f030801080c06091806010c0812160206090a030806030a05060c030f06010903030c0308060d0b16030f0c080408 77
    0x400c130310894100030081e14202940030740c00d40e80050300320140c0d0ba950f081006105440f0601d00ea0b5041c04954540d5418502c9000c3d0b6145110620403a017618030240031241c14440c0360000441d144907580c5444401c402c040f814000b58a4500300080c2c00100040000c0048009521516181e21500c800d84914240000303001103081821080c0d5081d890304080940d01d102494036004015207800c0c8220113003803003800310304001d074500b041c00c0328a444002045410400b40d20388030b181220400078412814440c9610a1b400800c403801c00420b10321041c40070740354103441c004099201c40300032042448110f5010340200100a01c001520b160000d40500701120503a4603000042d241c41803010005000e40603240c184030712203104001560003900c048a280110360b54601c0110ba10090502c400b40c00074042040e020080ba000303640304c40e0445c001601031a440301c116110140c800009072400c0b40306200364080d0401e441d605102e00344403000c034a5401d01c5078000000c0002e185c07901c00740000d0a00b241c0056054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 846249271 1250 846248021 846248057
    0x90e0a1e0317060604050612060f0f0906270a020d060902040b03040f06060510020c090702030307080403080c0f040b0c010506010801120b0a0f09050a12410412030306090204050d03 79
    0x45c004040c0180120790750000180504110041590410302802e001004209107207400440e281c0c5669001d030819080380e40e480c0c00c110030702007070110414020101040101a920365145020320518100a0159844500070800c10440e003050b0700513104c0c184180000d00c24000032800716504140c11441c02e1a0030005800c24400034241580515817080303426030945001c0b500031840380207040c1c049503d80443d039240d2805903200e1004889040001d0148400540080e00a8510075040290110440c0c10300c21001d5682d070172640300d500b040010002c04502c10f10141d50034003c2e282d020800380303803240203940342000001c0f0a045c1030200802c400044800a1460744099214a01d2015000301c00d00c2490301c0d5051482e1507000348070f02a00d03c15a104040581c1034010404012150503600c810002c420205900fa698000001c02c4004401003008050034040e03460409000a4048a8022048006c0710724002c0c04650300c40e80102c5032540140f0081000d5a20300900140090b00f504000c04807c07900e4100d6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 846250521 1250 846249271 846249277
    0x6010c03030e061801140121030c020d060509010b010c030905040209061e040612050405060a0c181509091b0c230309091509150604090e0a1e03170606 66
    0xb014940c8121020400c1c00e1000d010b03031401c2400d01000812103a05100c00c85a4040000d02407604d000c0551040000d12010b130a0b08954111700030300d08050b0242d03059000030740080c50448241e030700c144c50340244084144280301d01403000386e090074402ca40710b50b159001b4111801611560f40301e141d001c10364092540703c40d400c03101c1c00c44d04500701c026092140c1110000542082c01a00b0000e481201c082400c48207900c43d40b0300480e00840104110707a5149210707000b4040710b0740068100000c010004404c00c01521000c8050038459100081030703174007244001c1c0030000d16130182d01c40d00d0400e01c00309038159907000100301c2107455150060340c5074010708040420244690103509404c0180041d80185400400034050542c800c8480e80100d8403100d284175060040c00001540c81076a900100301988000340c481c1400a0004d00107a05260380c441d42c10b0300325405140c442030304c0d400c0f105119040050401004035004d01044541d10700700c4a07610000d01c0c00d00c2d544030914400d400384001c40c0e81684c4400035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 846251771 1250 846250521 846250541
    0x90c080606030c151b07030309120807080f040506070f1106040303120b0d02120d020d0804200f19030c0b19030506030709090318080607050a0815030f0a12031406010c0303 75
    0x5c1c4810900103030311581d1004988000e03070001d0540780300400c10010f03218611041d00d4104d00c01d541410843d40719506142d020101301c2000c002d082000068913116003014045480c002d200d00c5c80d40517258248502404c05400203184180400c00092000940091000c0040c0d41c50150005503504a138000c1030b0341c10318025020f98070205112240301d23098000074074000701414039403e0b40d80c3c460014506642c0450140d030300400103250748050400a03c0f0301e078a03003044501c0060003280c64007030b01404591880d2001000e4243d0040b5044248148140f145c1180020030020004030b00d0700d180d402105608440882c41c9104164460780030410a50b402c211120141030b42c4c3c00c0810890100749030242c1030280345180d104526001410002c0c02c2040419024410101600ca5502d03010081d40100e4459000034140030000158001d14503564804000403442c0c5020340000380310092607130030f0020000540900200c109810200d000b00c01203080c01e54541c10503000e00380500703800054903050703002d00302200c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 846253021 1250 846251771 846251797
    0x120b09010b011409030f0f160e040c0303030b0a17010c1b0b0720031305040c020c101b050304060206010509151005030a200d060f080d0e0a080304060201090c080606030c15 75
    0xa2007c0c18890205103120b030740440480782c0801d07942e150407179081c0c81e00440c0c016083c000c09080c1080400e003e43c21000c52014014a5604010b440360f0140c07544440d101c46284881c1e54030749030300d01080d4005043e8810510900c1c03031104811503035901c00e40d503414018421000c2045e030040b00c603132540503044003040e072a81c0c403006d60f41c6031a1164521f1045850500c5103611990401441e03540050020131ba243e480c0d580988004001003503240142e030440400c0d002c00c2654140ca158070008524140050009844280c0c0540f019514060030055001c4001e04000912284003600c0b00455683c0e030041e065010300e50070041e459950350b52541d401031605074000d1940d5441e0440c0022015610030040c0400e001c081002c100c043d880d0b0000080d004001c1c0100d444a50060321855800760041e000404803440041c15001c0da03175180d10751035045402030303489440541c2d103c48001c030402070005000c1001d8840400100024904000003950351401d440c101e070f00905202e12440100c1e01108225000c41070904 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 846254271 1250 846253021 846253033
    0x20c0f0a03081501050a02100507052703070b040e0f060d081b07090603082a03070309030c0b180904062004150e0102030f0c0c0901120b09010b011409030f 68
    0x42005000304504a035088900c0503c8048601158003031000e90f64001d81d1a801000700c40d4100f6240c200902002e4080002d00909101c21902d4185410014039000404075102410352500b07018186401c00580194103d200148414040402c1209001d80d01000c05100020243c031088017140d40c0c1c9030300803405041124005001410b504160402c40c5005060000f200c1945a0f81c0c034090045131054040208501c4c0100000000d0150000c007004881103580c800c80070380f1022083d40c0d460341e40126011004500301140400a1015404000b4010000e02c01c1c0b01d03251200135003002c4580c010f0100341e60710410191000c5000d02c111075114840c0511041c41c8000c48203200b128a02054100d4401e207024200700d290031a407251311850880216003010380055003001c0e9441512043d0342c0103050f60200030310548030041895130340c1071042e134028030030b004c000300845400742048400302c03c0091904050b68108154202d03541da010b0a0901c07101c01050310181c0320790010300042c0c2004000300035954030348500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 846255521 1250 846254271 846254273
    0x305160201030b0616020f1f140f071203050c04030c060f030608010213090b0604030b040209091c1d0a0b040512070b030702030c240103063b0705031b04020c0f0a 71
    0x55001c11030b0070700841e803650b142d09404042221490044c2100308c8060368000310400100d0082c0c001420f83d00b4484400c604101104200400d40e820561080e61100310320f401d9440c1d01505842080e4016072103c10a900d49411619010800b9005200d0070003040061151501d000344207620030009840315100035507a0306c0703170040698070206060042120180c03030701035810f00614200046508495100c0003240781c5079201d0b004c04c0041c502c0140880301d9030090b401140c10000e198002400d118050b80c032490800c190b40200782c94030b2607030305000501405000d00c05020740c244c1041580c080700c2003140c251080490350283d0a04000d4261300200489201006000010b90040b000e007003411209011150454840f040400302d0700c1c05582d0b00b114510a03800107102241840d0411181c2d1080c2c80741100e410407a03240c0300030020b11404900c0e03002800001c103a0344040024000c1c2402090210300a1001400700701074254454004403c0303900c5654002220003e074030b030070f001d681c403016100402d4600901007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 846256771 1250 846255521 846255547
    0xc030a020702040f0b1c1728030603030806010c05060a1805060a0209120a0f08031005030f0a030906051315171305010501090c050702010c03091e170105040305160201030b06 76
    0x1a0340303541440b406c04803540c0b402c20040c08260011807a0482c60ba440c2c40c9003007510200441c0e0004400c0503003d07482a598a0420100c07d4408002ca1016500001d4a1b80b0310f040061900f04007400c03d07410408001c0032640403a20010301160888440d140010782c01c0514020740010700e0104d00f004180b0b0040718100442003010b90301400d41e8540503111140104051018641c88860b144401071019040640d04400300354598043c5911010300e0001001182d129030001c1e15212025050407010b5000c0404807080503032040822004000da401d095003424031120b0101c90720003060042502c00080d01c90398074450b501c00c07920010010754401c484002801d0851021302460f201c5001607503a0760a10f0000511310110f8810004503010b40c3d03903141d080c6001c6c0d500446681c4400e50040d01003055942d0085480e1039071b01422081c42c0894403190725641d10781040d000709840340282582040e4908030400002c2500103048402012180003c0410041c4900c01079009203c2521455000100800e0219440311 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 846258021 1250 846256771 846256781
    0x30c06090d020118180203190b030d030b0f04050901200315060706060b030c0307110309060313061e09021c0b060d081201120501150b09060703030b04050f220206030c030a020702040f 80
    0x2032075843c4030103c230301d01c030f0301702815036000d042210b401d6841070b0b80205890303100b50710461000400408a00c1800b01003000102507440130390b01c540301655180036038403115070043c41007010701c102c007101e050440c60050300d04000100d552501c64040d44000592800300f148075840440a044100320541c0c881c1000e1819078029003044420307801160321002ca01c0b58154001050721a00c0d00c0084c10580341d640c2d8624024a0798117a08401c448182e25070010640a60400202034a00305d5088000103041c4900d00400050390704601911100082c4c14400c0c1c0003150604580c580d0001041c6d50300c607881c010511b0814041d20442c071000e02c5c3c0c2d0750308000125805000000d030f03001081c01200280091040c101010985424074817072400b880c0420820800c050a104020304200c900a00340001c407400042d01182c01e441c012116203840d40cac0340350100b04a0904008441c0740b20600040ea1004051841e400701707401c0e101c01340016006c001c003c4001f6850354029011aa081070707001e007040c850301c003520f04a480945 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 846259271 1250 846258021 846258031
    0x70b07020d080411041a130c1803020a090209060d090506100b03070906110a080d05060307060503090d18080d0906030c0509030a0b0402030a17030105030c06090d020118180203 77
    0x2009455400290710322882840c0e01464005070000402c801d030504000c02040003a41d4400d0030701c4002042e040595909144001f05410390102041c41107000c0c01c010400040344442000600840b0300034009038940895240544904a03001a9aa003400c0c001440c140941303082498618100804201003100204a49008807805003240b241c481e00e50081016601044807e11300050303200d2001c021440c07141c079955032960b511106a92500e481c0391180419503102004840e0300c00c0d2a41d003030100c94102045083c0048c80300e450101d0650502c40c4a1940701c0300d4101d1144200030082d2008104034841d481d1b2074004008050489105001203440984034440902c030301c1000c81d00e0a040b064400c2d000300e04907100c00000402800d14030407169a00030040c800a001a41c03d840b80c08542c000040c041c3c01700151207010040142d86035898076080615003028046818000c60040c000864141c80740c41041c00c00d80e6090902018400106ca0103114040c0d4a600c0180341d8000106403941011541d40214020707 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 846260521 1250 846259271 846259273
    0x3231e07050d1103010302091519330c0312021201080a03110c030703020108090c100504080c0d0209160c0b150111122a1006050405060108100b0c0a0503070b0702 71
    0xc1840201508a0000344006508038150400081040981c403c001c0b41c04840104461712400408105c1000303000d0f10703084160f8800740c512f1204210140d0f00c84808403004500c0108012031103c050041503a0f80f0161b008044c081d805001818084880d0155481109841110011983e40f00030307181e81c498a9800640214121325805841154003160071a000c43d4040e00402c101071465004694485000f4240c0700781f030081800c5590075540303000b200000c041281d5950368540e030421007002e09280c40c040b10341d03101c2c1000c080c52900586402004d140c2c801c844144d048110882241d09541c2800c1000000b024034601d181040015800e140b81c5220500007a60ba40c2210089085140d03038070701c00113011701c8142c40c3c18071100c8500e00c0390983c1035000c591340088241c6944071801c1c40c0340c9060408280c0440080e2a101e09202d2410b2a10415910a00910301300c1c82c0d0b4282484107514012840c040d402000340e000600006d241070800500f00d80c3c1c1d50041c100da0b03840c01039003090002884203444001c01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 846261771 1250 846260521 846260531
    0x70309020f030c0102070b1c05090c010207240c140601030605190b060315180a0f110a1d010917161a040e06010e04092103231e07050d 59
    0x200b401c000500c071540c0041a0014030290f4240b107513141d8550013200418080035581001000301c01c8490091501590100b0000d202e885120000a0b09002003504000c50040d00f240c1d26101c103c620500840002c0d8060900407c44400e03030801c18124100c4042e40d01113482180000010485035501c8688244d40004003020100803101d4040d055038600c0070304d42c1e407082c01403010901403043c02c03a01e40c011150003003441b00c110070313180c11456481ca0220f540119550792071242000090560040c402d9000c11086014501000b1341809080801e01003000c824915641d841c070111744c1d0040460b0005030a03d0041001010500361404e999070340130016500e00716031480301c0014001d282c184e6021401e901c00d00c00a0030141002074000001d0001000141041280540802c45882da481280c11050040180c01002c6100c240301c414003100204049042500d098521034081991180741010720042e1440007404d5150100c0d00600c0f50030709880b40001d000400c06202601703801c80002c00d4a142801400c0c41 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 846263021 1250 846261771 846261799
    0x300103121b02061810080a1a18090106080313030c2c06010201021e18030303011d090102070210050a0e0916030207051612020102191e081207030902 65
    0xd444451021584080042281e41e04010f18200c0003400d022901d000200d40c002c203000000030381c2005079000e110f0104003e80244081d40c08680580045040c2525031120307454010008202c0904d0450400341d50400798001048441034290001d200a0040100b2207483d0619009460006100d600c001c60300c0815900c0300045501000004007460318403c0700304000140c0c011110103102100030980c43c11554208011524116180d554402d90805030018940340c800340c12641e0340c0d109515204034421f6005000400216103040803a420092101c15103030003545070007001a0180c001c48030020351080101340d41007000c80e8804041c164680156584d0055816098107100c3d005505480300741e070021f000a990301c2c030a030290f0020521300340310307408451141d118140a82021030752500a4540e14016288a4055681c100b01d0b42268002c440c5852011005171354031107480f54015008803601ca11008411010b0000c4002922405102400c10b0b420034503107104010018a40001c00320700c5003040c080021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 846264271 1250 846263021 846263027
    0x303181e0a0612152601110708030405010c0c020f28090c080a091230050712020313030c030903080d0605100203090d030e0406031401090303050916030830010312 71
    0x412100c1381460040b4900c1c6000c1601707601940342c40503503829921052040d002c0003049000788501d03401a000b0607102d0405207411402c0d50503500405003003040e011861000f581d10100c000141c1e030000c8030400d01c241e414042e0701440340301081201980136480500041c8503001ca40041d41202001e0b550800300343c2ea0050030408481c0500d41c041c0c00d49200c0c1c01d0041c0e0b003d006501c1240300a0074144445103001c50f40c0c103070050100341c40b214003103419142e005000302c807a0000001c90712100800000c1d411803030402c460001c4035a00e5040034003007144030740c126410b050180c10920042d5400ca010207075212004041c101c094a464890140555502d4454000c00d910120645a030741d00024030700c05402d10039443c02c450343e8280003034555125546110000004160840300181c0b108020004501215070f0f04002c1c0407030300006e040180d60b42084a840c5000f010f04001d0320300b640c0d486032016031a03021481c403030441040081030440f03140c01c0029100c0c0343c2e084010303030070382c100c03489030340001f210450041c011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 846265521 1250 846264271 846264311
    0x80c090609041e1a0a0f06060201090b04170705030c06012103020619021b0c0f0f0901061209020406090e071505040b0c101107110303181e0a0612 64
    0x150a036a240c00c444100c0d48801c2c040c4181e903500030000c44d03c0c803020104140c500d04d24140d030489000d0340d4540380800c21032490f00500d0000e214500003001194003e8460440c40103009000510507002c40200c0e005030440c00301910b007242e800400300c036240c0c2c2100800c982c0ea0503080c09503020202c0804031a0510040f5407031080b280d194103501a01c126107810940314100c092840a0203203007034081c0886815107118103d602890405200205050038594040c0807400b680004214011440d202c00c2020035281c4014040c1100c425207032120070b2441000118004001e07030600254014140540090b030182107400c07500c514008001920b0042c1c0e81c41c0c402c04503a403400348004000c0b0390140070422688a0b80c4020380b00c1c0f0300311a016200a0491640c0c2310017121001c40030a80c2c0b5100c0825140c0c107100c10540d0810403c1c2c001d4005525001c10f0110140444000d201c0f80e0784115074250314401c101000c506107103001d10002c1c0c030a90302c007901c450f0f014002c807400180103403040785080c04a0401180c04140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 846266771 1250 846265521 846265523
    0x21020619050c331513091104020901170406090b180d0f02210408010e0303010806160c020607020609100305180a0209010e070507080a0c060e0d0905060c16080c09060904 74
    0x115112250040400e40f50b101c00040c05040d40501e00c2402d0542911824500e016501d00103a0004445160b80b500040f0a001d040600b8015403040c0810315481c0d0b0000c51281055031410040b0009a49501d00000584000f29008042c10380ca102031107250010340448040e00e032460340980e518203c156a00301c90008411802e0070050703210101c103040d002c0042c055481c0140d00c0314412442d0584034008035094070340c01300c03590085a2002004010340e0301b0a0000035001500e203024804140c094a0008000e80d80c0840003910651000a03c3d00c115905c040840d01d0416010f003202c400f0100400004e0f000781411144c0220b042c00c1c10b5045901d004011034840340c0c0d580d000b0000c00701a424051b01801e8130b00000c100a0034081c0030001c1030041030820700a4581c072080c0c0c0d55005403d109525140e400e175000850f55900d1980008100d040d240d4012042ea0140c880c02d82e00383c1c2e101c0c0a038080c09071521301c448110407082120501d000c90b003000041801480c1c1d40301070f10120555114401440058581118 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 846268021 1250 846266771 846266833
    0x709020a11060f1b07020301050906010302180705120a090f050c0a0b0c1c0507141c0309030518060d020a0c060e0a020913020105041520060121020619050c 68
    0x100044210300104d03030150440c01401c1d0010300303100c000d601003800c581d03068440400c82c0d07110600400441c038280c3c6070304030380811692201100e8101040301030002c0c013038210401a1111083e000030907514096201e01c0c3d8880e000700e8850306100850038107a49841009000034080d54000002103980c010740000c131480310b03071075030014440440f4840514040c2602e048550040240400105011504400180380d425440390082d10010b00308141c0764440c1c0c68a4005e40041c942012004008683c106054454041c90602c0c295818041040040c800744940482c1d4110700d40701080e03006056500000c188040c0f03100d420208020300c80c4a10f41d40e0340320340d03200300250b02055010001d03090351441101515250310606096003016103400b001001d406d0100031240000300c2c1001c0c52441c4840c0c55180c0c401c503221500c05040d581d41401c0c00640740010b460340c1c00303940b20186143c130b904546444045501007400d82281c9030148090b80c100400691012a841202c0e11507c10000d8a010b51004500c1800441e50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 846269271 1250 846268021 846268051
    0x80601080d05180406150305060f061204050703060e010c020f01020906043011010219021507170409060f0f0e070311070512030604061a09061b0709020a1106 69
    0x900442e4607501ca9042c0c0110000948031001c3d050316107004507409400d608442e02c0711100c4440e0010100d038401001140300b0220148030764019201c0720121000c5160381c10407541c00da41c0d2420802e02c0c00e80700343e100416051502c1c03c3e0b23500041c810b42c071018120074a42d0035105101ca01481c00d0b070a0380100d4024542c40f02040004016800e0340d400d002885410f00c01c81e4000484042c0d2a040c10207544074010f483c043c0c404491100c02e5070303060103900d194110b1182104001c810580106011501b404c0e001c440c0070704001028010b019072040042e80032248282d07156915602c8000000141240c0c0c4502104501c176035034045001c050064496080e154078104920701c550310f10904801405100000303150b513010410104011a6003030101000502d8544101550303400e02e501400304490312a880445501d800280c00915504204c0881d29004d03022150343e5143c0c4081c40082412002160004080348102c0d80006892070305900600314440f11a2140203441415a03416500e40d4011103600660700c55403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 846270521 1250 846269271 846269293
    0x908060a020306190605180108090a060c0302090619141207030209010e061614010902060d02030414150103020103140f0402150f0d0504141504030e04151e08060108 72
    0x15038090740d80888010207500c4607400c4c0c245043c500c10010b07040200080e40000746d1340480c0c0b09004145440002c2844c180003603207010a0910b13120104020010072032900c4003c0340240e10320a4042d04c068840c02440142d07101c1c1e452000350804440341d11640081828011891920b940f4203041d02e00d440306d502100100e0ba0f5611208400a41c8800c0002d810302c2030900000c201a140d00014095803400340b410001e4103186410042c40300700c004081b8000300e0b030403c1c61308001070701c40c801641c01884001402503140d44031442d210740701038400d5043c000b9520036011040400b4400f4011581201c2c000c2e2400c0182c1180d0340395100d00d2120885a8040150019020400504186240c00d5003400c290102504040041340c12060507442002548c000c540c1720270600003844000b54107540801c041100403c82c0b40000307010000e5205000f0000360170302503801807421f2681c903143c0100c2c24510f41c030030440b60b2154503028406620714044e00b00783d1802440c403d000c00c0d000340c0010340c1c1d81a120360000806102c440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 846271771 1250 846270521 846270541
    0x6010f08040314040e1f1a0906070b0403050d1401050a05061b2a03030901020a030c110307030b1e0405061305010f050703091716121e110c01090806 65
    0x8054400c904100d102e00c43c80e0905040318002d81301a100c0141012003e00b080681d8108041383c446071511409544003041002c20f0700300c2e05990b0681280940705446a415900246d01400307030010241952503280100300825610400a1a1141161004114086c401110b4200990090142c66004860701c40c042c4610f1408030081c141040c00b0300b6024201940081c05241012149030404090241c90f04a138503510702d20f4043e2440300b81e816001541400c4e02440001d65506030010007406001801051100b402890100541a141c000d41113621705603591a141204410850303401481e54491422200151310302110f080c0944c0d0414010441515802c3c481c0864040003101281c45658408000400b0100742c001c0038814043c035140043c0c1c1c6800c0781003401c6420410010101c66000c2000540c0c152441e00c20f501c1c0080390000c4200041c4030f14581c0507548940c89010303401d20038044441300000d069200c0d00e0344181a0551013980d0310707802d480d80155014425030113000d0a80c0c011000203015014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 846273021 1250 846271771 846271787
    0x12170904090218150301090803010902031e151809060103240e0d080117030a12230411042310050a03061406060f120406020d0e101406010f 61
    0x100030000103140900c1d600240100320941110b8443d1590b4408000202d03540380c44042c01e0343c00aa000344110141c03070751500500d200c1401000d0040c1d50120109841c5098404401000350700e11200c00310900f050450300320419502d0307003014402c1c01000c2d220200000d081e81e40c94002c025000040c2526404e60b0303079408590740c15803100b071041007804110f21a5194540503414840c801c81700a010340d4800360100516051058000e00741704140e4402c09081c480001084845810395407402403991703a800300058007e020b1505031107480f13480d144181c000ca0446403245601440c072549250b1400a9094140015940d00340390840300c606c0241100808540e8080310300f41c0c400024621420100e440304009000d009050700b0907100701c3d90350070144404260000c08641c0000b4119444c604020381d41c0b29002c1ca501c100b90028002c1600407002c141040b044e50180e4416001c2200244481c0604201c1141d881500e00207005049040800205404c174841071007600540d0181d480240c3c9180f00e42c004d442d040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 846274271 1250 846273021 846273037
    0x803040e01331e050903060f04020307180609110c33040809060c0f06010806040f080d141503150c07021e040203070e10080f071101090f06050906011217 67
    0x42070700c0c08150f072901c04143c2110780590380c9840b40c41d15040140d0a052806000038400300c01e200454040c000035a8002503000c1c2150f00388801d42c0040d00c0584006c001403c900d0f409058014103000b04606404d000034098100e4011400032607030b04566401c10100c0b4006200300200300340040d0501644e94041c51034016a11601603c1104d05d42351864020603102e40c0202150300680c1c02100c01121070907824400d05004026410090032182000e490f03510400b945032400500406000600e480c00e50411740000d071708060001041280351038890740c5862080e03518821640310703010341031501d03242540c0c0c01081c5020b00380e11011142050306907400e211487c0c07460318500d0743d904411520a20301c0e0380cdc2c0340002c42c42100542e80344103205030208148181902062682018400c8031800c010449180d45155030b4030241d10303d000b000d202c1255420038014065028094200c01152403940140840c54004034046d090010031030354913a0b42e901d4030b24070b40002a0402020310128011200d4100200b4015000070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 846275521 1250 846274271 846274277
    0x15010f05120f03030f0f010e01030c061218031e03060f031101121104032310020d0b1504030c08070b0708070c0504091110030c080a240803040e0133 65
    0x107000c03100c059038659001145c0d002103c148020400910320030900e42e80c0d00500542c45120303019410b41d903600010380c855005020802c0603010041d5010300907031300300e04030743c1c1d1f02e103410011900c0305810000c00d0036403000c98404803c01609244000c0300c3c801d201d600202c6d22001c8241c40702500350b681c1d420144409031401410040208400103444d411485401c00701da28201ca01941e443ca10b00d056061106400c4219203881e0b1031084404840201003030a080e04141d0000051f0b0b101480900b60000303211041c0c03059002041c020040b5504000800200141c1c1e0041220440441d625640709607915005d00802200000501c43e400c0040d03880ca01900005200f410b48068458841c4041821204034103000d84418010340c0c0090b040c0d040c14095050214054541840703003c003004000707040785402410030210f06d66104400031180901c440b100298040d4480d802840c04d503560013440c1d40790030602883c0340443d041000050461035405d81196a140c00445002c895800000e5181800310400070b01418 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 846276771 1250 846275521 846275533
    0x4021002030f0d1e02040302130f0204090e100518074211010b011710150914010207050d030302090a09020a0c0c05040b060702090901090c0e060315010f0512 69
    0x4154441c074007030104141840300004a521310313000e80c1218602d0648201070218070400c01403000da211000c00740b90031b4138400008918140c60303040d400024459544144032a510300400c481014a01240341c0310b071500ca07004180155215008c1854000d506040901d0300c81d40166010480000c20502c1801d080d00c1d0403549c94101c1201240c00245468a240382c000300b502c16001c5201619000400d903118020340c40001c0090341c0700400041c0600422196030306400145c9400100d0070180b8445490113004c203080342940c0807400d218060110b1425005d030326000034140c07a101645500c0028a1811603100070700e5800c013124145c9044d402940040609074100410300b2000c43e0815081c0014048895039130b07a110414105400c080305003171200e80115115506110b03e1250070f9983d40c05a80007160103c2d58030019445100026006241c01c2200a040300e0f64020b001035808200702072544200e9044d4150f030286121102140e1550100740164108180848024441c908007442840840400c0707004841c1c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 846278021 1250 846276771 846276787
    0x1509141f0302071b060f02010506091506041a0c1207020d080d14010602070602010c02010509031909180c030507030b030714060d0204030b0106110708070509041e0b04060e0d080402100203 82
    0xc90301c0204e83d86180c81d900f0310002007210f030742d11032280001c04440348001c202a0620324000b511010b80582111050b000c1d50124826035924507003100c008020700c00310010840348803103000748940c010250810560091003000007000c010f03042152040d81c2c0c01803051405401c15510000c0d2500071908900d10b45541d1400003101d0f805c40d881c202e0107420b240e0000d040321450310000a007904c42400c60481164189002e01c04a807074008259030080f0301801c02c0c010400f806500840b04500942d2264995862032800b094905000d075104500d0ba035800d0350148820f5403103100c254190f60000c5040c0790154130800c0c0c20448804810fa4401c1c20941c010140391908a00355058016078209070000d46544400c040108440c40d0054004040c1c0c1e0b8410014203101c07072428400c0e1b921000648105401a00000d00240c100b083c3c1c10f004a51900000b81d14480d81e10f500c0c1400f80c880380b02200d0407100c0c2850140c0c180c010181c000b4284800b0038055444c400583e030f0325401d21101c601c11511803070941c4402d00c13580d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 846279271 1250 846278021 846278033
    0x9120813030203101b0315051002150a061a0405090402100e060c1b0306010605191b060902100e13021606091217042102070306061509141f030207 64
    0x90100e101340345002c225402d2420a0340c8404500c444500241850840c031b6851019071a480041250402c8501c0703804015610010ba007012269500c0c5008844108101310320845a507004100b556408140000f624100e02040c05445c0302d03078083c040d03100e554940002c0040c035100c0702c1c1da00c0b0701c8218944808030240080204195802640b164001a0080c0241810702c55502c003025001810450061000f549854006030103446610000302840c02505900024180940c0c00c078541310200d82c03080141c003503540c1455002443c1c4150101c0c4220a165080d4002074460400d00c202c0040050000911500750041d030002584055000144003600d04100b1010480c00d204030710515000c0e00d130216801c08500d10040c5981d001d4208010190b2100d014800404c600d9140e44510100703403000041c0c0070304107900981c40c14203250300c010308903410305c1d40c007068048a001900e02032003c03036104d07802c4054489001d005017041d0558195001541c5080070f18070340b4902d0302c20710740122090500624042c540c0d1104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 846280521 1250 846279271 846279283
    0x1060b030705040e160e1201090206030109021804050105060409180c0e060901060311040303030518010c050a120618050c120408040e060402070c0e070210140103110109120813030203 80
    0x1c400b040002c28200020540703110039035444042c540c8484034003110070070040c1542d840060f0040c0035800c4003131240000b20003580701c074210f5600100065201e680d124803a002a52054000994105800c0e520428908180c000c95041e20401032030395003000c1c10403401c84001c00c0300103500000081d2141155000c1011174800302c002d0408002c4c084458a014000d00018500c1a480f44080515040003920078118038003c0da415a5414540804c8a032111340301a070ba030840c1d0002110b482c0d4038082624541541200080c1148a042c2d110301c42d1548580f07130448121940c910903032503c41040b10405152000c55440351340d0200442400c10704061000e83d0034940c0700342c101e500312855040003034107005102c43c0d2104a035106000b26000d5151110540c0c174003002c10034502ca1154007900d0000450700c1d00d4004c0c000351040c85c2c0703048400c000003203440744103110518003840b06681c00464084595020b510803440399098402c81a092902002140e072400e540d81d100f810400c043e54402040400107039014421 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 846281771 1250 846280521 846280531
    0x309090a021b06010b1602121507030c05090901031b080d170a09080d0903021e0c0a0b130612090210230a0c0f080903070609030b07020106230301060b03 67
    0x41e114407040b9400e2181c06107060310a071603580300303100401885108a04403008840341c0780c0401d0355003940348003042044c0b07c40143d4001c18000c0300000804a004584210710980450f0b806111103404101c094840c2c0c400d0342072482c0c02001c203500600120f6680511761440c8100d105070925001d0303940140d45e0400610000d0f02c0c00040098800c0c110107015480300ca07400005807001080051519510102c051150700348000d4000d07110041c1ca411700d8024040d5600b42003081040c2202c800c51741c01c185490b6680c041c0380034424540d4107400300b05e01c2403240c2540e00c211660142c2c150704504101081e9020342c4102c400c540400d03111320000c001030b211b24a6642c42d0021a88400d1900d074501c2c9000c200c01c0c0c80001205051040a0011350b204690122580c03011581106c0c040008003840d061014043c401c04040d036415118041c400541c84d41c0c0824580100c0e03028801d042070a0b100c94400301e00b603078a544290b000f800301c0d42046640a50780108045400318004000003800303a40e03040d0f4074489800880d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 846283021 1250 846281771 846281791
    0x30616020d0e120d0f0207060e0a090b010e090c070c0b0313020d0f0503071a151509010306030b090307030f0807080613330605040503060703110c060103080702040f05070807080702030909 82
    0x5c2011416a01045080094440b0741440c500c0700c40038078003090a00c06588290041c854840c00340c081264018844000d07040c0019000103003a203460b10080005510250045544204080000540ca0b4121041c2c1c2d0003260030000e0b481d4040d0142d02042060a100d08041d42d48034415400000015010001040c1c00741c441c64124411b4240380000c0582c0800c010704100700e02450201c15222035946000041c0c124103500b404c1625204000c00490060506800c0248203c10450520450a00c000042e00c41544299036407540032060800454103440141c44d950040394491001c22824901000c0040c1464040500003880d05882d04841b0810320310321000501c0304408241484e01c7c041c0840d80b20002e49a20300704213150925100200ea85c441004100404140d034480008a1900002084074034080403d4102da4003075031241032010340744c0c4c00010100d21403071070686019080b01c51805020b10500702d5448424131941d4003102074541213070041c008002c602040050102940c0c44015035409000000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 846284271 1250 846283021 846283037
    0x251208120a050f0c070c1e0807030c05040507090e0a05070e090703060e060307210206070c06050a03060509012402031608030f0a0b060409110d09030e030616020d0e120d 74
    0x72010101c0340009016401c009008000e45c10100b1303006d40d045402c586120100d40d0150f03026401402d00304220380c000060601900500009020007040b0901c107454084034100802c1c2c86111082d1070741c0d05580b0925811060100001c0d000380c04aa020540c0607030b045c140084821404000038041d2070f01100c1e1840405d5403400207010103090000019840701d000d03801043c0007030503c44090244105295469412004580040210b417251010307100025402411048040e80f1014080d05680000000c1d500203881c01e48006481d1408024030b42c1243d02c42015840550540042d000e2a420781568050640c8410070420004108240401615038043c4840c5030303c0e400e100181030000c00e00505561034450408415120b02e80d11081100c046851100001540604e2010030411f640030f003e500e5440c0130f1501d80d102c0c0170305801001c0400310326421000d4030183da850024110140311030484400050380154200c0240034001c5031140c40080c0010401d10341402c0c40b4030303c14035045d419003d11000424407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 846285521 1250 846284271 846284281
    0x40f09151a0715020a0c110d050109121b120509010927050a0b030c010c03020106030501050a021809160c11030109061506030e120706020c0618251208120a05 69
    0x100f291810042d026044d8509145001e0040100003802000742032144e088007500c1083d65000940c030704a5500900900c07400da4141008020700300e100d800c07040411080005c3c05140c01e441440f00700c4080d8010b04e03160039814550400c0702ca5811882640d418000c0400c804100030004036071604140c0d4110700c0035050740e040a540c0f03a00303688000c0c000c803102c0c070b00300208083e0680d00440c50506a2a0a28114540072110b007812400341c0056070001c0c1855281c8401c0c050020000d030000e0201c0182031240101211400040c001c00b08030846070410806026600170701c0c007a00c141ca2444425000f41910001010020002030849603028421240f07242d540069142e10002c100d0500010006c42c2001c00550110b280900c1d200c08001400308030b08600001c000703080004030760554003081c500c08201d500da460115200044403a1403040c2031074910584210501c072080000554905009510640740f440b450001690710100110004584003541840300c561003410751080340c1e00c60042c68002107600d04003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 846286771 1250 846285521 846285533
    0xf0506100501140d3314011806031d121809010602060a0902010306090c0e040f0b03070320030a03030b1f050726040905011a040f09151a07 61
    0x1940c8103505000c3d600340b9000f240c030316000c02d41c0d0913208803040110b12581240e1300446840c02c0c4900c0841c40c5502d40d800d0300010000000c2610513500d8110410418035402d2006490311504442c05035080043c001e02401498030981002d28071314003d41000c003403a030344960883e0619900311140e00d90508045881484c00c1e0750719101801d114001e440d80c89180d41055802525180020600f41c80245c481d1654421648258024001001000c0007000082044d02004010118081403148201e09140e00d104400b2514440d0301103480000b001420454a0b550702c030300c512601c004c2c008402650b02d80704182281c6080c000f1200a6200b5030780050a4600c003010040e0912050600003925404620003400c0c041d004000c440010303800100d00b64101c0d0000d1009a644804118080310780440840d0008821240b0382003241a01c500101d9084007000d240c10304000c034040e80c8641c10380d00c004000d04001107500b45c3c0c000005001c0f8500701200365501c95405001070314081411400c030001c0000c60b407081c000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 846288021 1250 846286771 846286801
    0xc0115050d080304060c09150507020306060a060e0d06020f040f1508070f1d040606020a0c05040b0d02060f040915140109030b0117070509090d110604020603010603180f0506 76
    0x68200c07810011405607484010103030000400003483c2c05d075500440d1309504d000e11494801000e0b0014400c4e200460100e008200d46c00491040307020348500c1012800520f03008440384160ba59540d100c5141140320000c01902c440441d4003541c10a82c2084002c20707802c0000c000b0300240200010501c8211715050b0200c00076000341841400f00540d02e014459111341c81000341d01c9101c03403490a039142940c08214030712a0003840c0c03d620361240c5000350006100c0e40100300c8094140c00341c145500d01c29501c1040c4800e4544c41c5a482c0c0e84081c60a55020040c0740141c0a001940324800340c640c00e058503038082038121401d003600000082da220908201c1114450b0300c42d646c050702031070855540d900e15660051054018002c1f4403155609440350404513000b00149001000300401c5c2c410345081042e2480d032a403900000c902c00050b8015042c0703107200300000d5414010b60b03010788200c0c5560b113041000c07401401c0480c0e4902800c503200c2c03280000f04030710001c0029018082d90181c05141440c01d440080c0ea9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 846289271 1250 846288021 846288029
    0x1b0f04151107150c05030c2a0f09070c080403061802100e0904020f01020f0111030f0705030705121005030303070f020708070b0904050714040801020414010e060307110708030c0115 79
    0x5030000e030050040d903001020551100140c0e0030503136a004102e04d0858114004c3c80f007006042d110700c003550f44202c4100344103c42214412240c654150b800c000078031183e907584452842e0040c1c40b080201c3c541e140b00703412544155004100d100e045c00d48966880c01928031041e600b50001e0b5403040c0d91029458102010032035a442400d100f02000a0a004507c03011002003001e4800c4044501c4650f559000b07001c203540002c105402001035540704458030754160800e0b100c0640c03070034021001071071160141c01224050803480d210581001d1502c0808200a103004100400b40001d103840000c80e902d0400140d8052841798403a022084001040207103403408990004400c0d901c9901d0820200502c54100c070080b21058030f010480303568480c3c0a80d07400360003d00e141c0444400050020300408c043d07001d08140e44004e0346091607035240034011603160307e14081195103c541000450303815405104a21072450440c02a5408141e4580c009030071500246442e2015035109c1041040e4403003041c040d6030140c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 846290521 1250 846289271 846289273
    0x913140703150b10180b0412060b0d0203030f2203200319080d140c0c0c0103051905060a03060507050c060906040c182703080f0c031b0f041511 63
    0x41400c03000007070303403400030140144c060040d003005c511a00e40e00742c18450080d2000b128902d680b03c0d42d9030108400e401a480c403d4501c4c0d841c0807081006864038592080351035400400035420207051036100c080c20740c030103510340c1c5964500804188c082124488050700a40c0555800b40f240c1200c43d031040481c58104c0b44051190f0032400c01b070b18542e850181000d04d4181c001d00c00f141c0760110450101c0080c90074050841d800c0d1190030420050102d030030000c12207035003d0310645d03a407000120015020381c0e4041d15042c02d100b100d40e2032240c00c46108d6000542c82400202049200c42e9203440c0c0004850040e101c41c00050400900f55040039010842c00d50012504030040515251640314030241c1751441c0180d1800c031925090031260390059070004d2041100444145100081c4034082c034080107414030044010446200001e580000701c00d0502e4801e05000c401949140d071030418410803000400c40d56008103500303008090b02152502d01400203032648803000940141002c03009081202610445686 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 846291771 1250 846290521 846290531
    0xa091a04050106140c07051f11010e031801020a0b0a060f0b19111e06070318050d030c05070c0902030108010b2b0c08010c030c030c05040b0702091314070315 69
    0xc4640c41840c908a1244584200c1d0b01c0c1c5d4500285c840c04c0c00351507840250701c035070700985d100703504407901c101d248041840c2e88454039000509424a4265466108802100c5d001403245900e00e41804600c0c50001b98140305031204c1009940d2010105c00040e034001c412a079480605000017a840210a000350400205090509840c0f0642003101491204403600304807508510781c030b803403134104250403034800e10000d080c070740c902071040d03980d554a41161808002810040c0d10407a040e070084940c1d9029400078054403082200769000d40191095001010401504104c3d0310007082c101e4240501802c4415400340c1e99516203141c0b03509441040700f40c0f903c10030154514a0720322184003e5403410740c41070302444082c3c189609080034100900d90101d0507550034400c404450355816801444036031020b0b202042103a07600380e8100c0b082e0007680101070f8103c3c0c003000b43d880036142c80000a035102106a00503900041c0c60340e1110118034025600708507552102c00305000704010341e1a008980882c440f01001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 846293021 1250 846291771 846291779
    0xa0504020f030f03180d0f03180f0e07031a10020304081002090105070f02060d0513030807020705210c03010c0c0c0b0f0409051b0a02070303080a06030c0b0d02090a091a040501 77
    0x740720b100e82854100d12000485c250700e00340c0c030b0b000e100310006074110107440318101c05030401502d4080102081c280245400c0b01c04070303411180c000504181d80e1100704c0340c40b00355112a01170700141044441d0310b0a920411240344d070107a50f400400d80d201825940a10b46462811030000d1818041e001801e00360b0b030040c441619281d03881401c2d100c1c1c66030412004001e0901600102e26a031040201c030248043c2020b0800024605416040c10030510a82e1054499664118100d0700c824a50042e43d9206000000100503100b2044248140c0b0b0040b0b420385040954030300c0068210384d071400fa2400800c02c90001107052220b1201c00300000c0030f2610f001450f04521030340c3d00e071040c840c500890035019610741c003040510302c0c4080c64040c205003039000d45588910714800a50380b603006200c1140020500800540802c3c058041e0b002100e40c001820607900341440280c07012600000140301d0156400d100700085581c4090300300004118941c800140755a0307a808007003120001c038400c0c038021810840108 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 846294271 1250 846293021 846293023
    0x201091b09111206150408070e060906011e230a0f080c0708070803070c0c0f05031027030215070e0405060103200904020c0106080706020f07030b010513060308030a0504020f030f 78
    0x581d01000495031045c400b0303026008800e960040c2e0300143c10a00c5a148040754840940d580f55009400446680c0c00715904d82d001101c99403840c40202032102901c1e442010010b01501540700d1082c40300d04003141e000c40c60381808841e9000203c50100096240720088000c94202c50116040001d021195180000940700c68060f889940c40042818500000080e82c0b01d204c3c801014426030f01c0801c01c550255140c04400d14000c0303a0140c94402d005002c1d0150241c0494800c4501d48800c40c03034840040c03100c1807504400c00c00c10200950644c00b46650b00d0721a8a482c00c0400d11648494441c62080c0150b0340038030007100c400814071814145041c040c0c407a88010545002d841d42030000c1c105a135450f0083c003107002303800390895280080d800c0c00004540c220000c44e01c0710070740d04550b0854401d0110380110a540c0d0000e48005484810550014051810403450018440281c0325003c6030301d9569a540c1241c55108880c0007080caa503480c144021890306448a42c0120030880050000da66414000c0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 846295521 1250 846294271 846294307
    0x100927060b0d17030708060d0c1208160f120f14090604030503070b01091d0615060903011401080105060901150305041109130c15020d05031909030504030606050a140609010201091b0911 81
    0x2b200c00e200c04030b500c02007048500c01c480c4402d00e0503200101701441450141c01d86084420100d0340f10103481d1408031210b03ca554107400c880c00c03581d507240c43d0f03034804860110340d50f1002c075499030040810440440410820002031440303c0c450302c680141580742c410f01c001100c002410040094012002c1040e5103030000809542202190030000c070b86040210019085100c0c8406094055091092080301454146000390484400704e0081c405540e88a0030014031840901900a0f00a01e680318840814070175032260703903c2441381c1800f000c61300300c3c840000c0b90250200c40840da040c0b04842030000300100b001c070700002030800c4105115001416075000c0d44611040b0038520410002200140c8084140e0301501c92039100880100703d104000d04008003680d2080c081a0b41460800fa400213241c202107000e1030441e190580c4001041c6446000c010003039001003034040c1150740701c030001d034003084c802c046207a140500c040800803a9443c0c405481c0a4488080b200b01018030180701f240e020002c1e01c41c2c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 846296771 1250 846295521 846295529
    0x20c0906010e041506050a0e030703050a20150703020d0807090515120106020606090702030c10050c2107030e0303060a12020303040e100927060b0d17030708060d0c 72
    0x2103482c0c14100c64002c50010214600c0107014940f8203c40002c850381c1100051950542664a44050710368402c24540d030b5201c1444018126403045444002047c84034440d42e95008999400345202c6810000180d4a68020b424138060078000041c10400c058040001001640380c50400107194038203c603028040b84868461035010f5200000c441c02e100001e90211103d40c402008120311a5031602d43c025076a03102110700c6030207000e0150125603c00d0000090361040100c030402891003040990385440038000144c03000c902e0007820301005000180032100c0303804011a83c404400729162040c03006080c0d400c40c40c80911a900f0800038000e060700c80050120a4607004254095061801d01c0031a107944503690000d209041c0300c0c42442140c450456501c42204d000700d2080c8041b1074541840000007e84400a001d00b15040581100040f142e411451480c030300285130311081c5140d51640030070b00001c130141e240c07c50000001c004945030030645094004a0645408001211582c0d4000d242909406 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 846298021 1250 846296771 846296777
    0x71815030b060d1a091608060718031401050a0f0b150c1212010f090c0206191808070221122d190f020304120503040e010303080a0507020c090601 64
    0x28607980f182600d0301600d80d4000031050b1600f03100c0760009240130301030b40e071604c060080c480912030002c048009041911040d40c0a1310180e1142142507503107500010060400d60446179001010410301d00656a00c0c031001c80000c9264a4819411401c40e00134280b01ca61180c40c4c1490b42042c1d40744d4100344684400d00282e104e070340700c10303803410a4600001440b40403218a000503420030128a40c0503003504841c022000340b18039580701d20b0090300781e8001800c4000181d002000040714039002514214070104422000200c2010340902904035421980c8151054800040d910701141441d004510b141c21014141031100d1804050181c1c880b4081c0000c00a0340c1c00104000e88071070709541c0c3d8124000810070700d01c0c04503001e0304402c0420741c00c000c4c1103005480042003141c0c40710380280f000800e448602d50165150600700f941802c4042c0b2050400e03203140c0b0007030001244010035900014065030081e01c4554481c074284804405454008165108640043c604442c0c84e8682c584200c1d0410030900f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 846299271 1250 846298021 846298043
    0x10061a07110d0f0507080f0a110d030c0209090f0c0a12030f0302090a0609060f17180a2a140f040b1201061404061707052b0507181503 59
    0x1200007040b2909401000c1d00b401086041c1000700100080c5240484800b01d055441c03266810842e01e403190b41d510009000a01e0714010212940781041004521500c80d04000d4402812a00420000107080f10030403125440440340500c803441c1007200301c4007800200c400701809401d0480000d0303005005c02d0000c0c207001c603441c000c0310a607009030140e840f20400501042201590b90030010031f4065039105090104000507510544036102d2841c081028081c444400910f8171340800c3c0b00311055109605151601a50500c0c0d00020602c550742c803505207502c10300c41200c2084421b1400300d0461603120110b260004101a1840d48482c140030114100c100c7e00046c2e41c140c10008200208119017002c0003d51804c100410701e40d00082c00310a1900b410b4071308000c480d89079003082851613081d26041c204e41d8044102005240340c62020243c03140b415134030b0545200c80f001c9201644601031401161580c21507401402050703001d542c068000000c2c0c1c181440004520040e00900203024000039240c0c001c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 846300521 1250 846299271 846299303
    0xb18040311150c0d052208090103060e160e0112050108011b0c0b160507080a02011a0f060904020f04030b0108060a0507030c1224030606090c0f020d0e01030b1210061a07 74
    0x80480ca41c01c6d14010b2003007802914884c44d140c2410b034030041d0114007007850f0020200300141c003408854030520221100c1e140c0300c1c004001c00ea07034400313101000504000300211003401c0303d41c4900855000342121000803132503050035101c101444032a82200c1c2c0030414035000a8000c161101034182c0c00500b00145a44111441c010444143c41990790140011400040001c4190303415807101c1d0358500c2e601000c1c50000d0343c81d4104004050200c91603a80030b02d040c0404011442d00d80d00424030346020a01c0186019501e03230781c802e5a6a000d9100b0f08440e08990100181140b1500505a001c4124a020820708e0290b050141c0805c0e40c03480c0c000038890b519808854040000750640c21000030082e042c4521035986e243c50342c050000c1d402002c50321130038410700c1030160f070140c4442022002e841d0042c0103403c21402c0111010045044054105612100c03498440d840d9547d845030044807500141c610104050754841c1501c0341680502240c020641810031610420410340750b2043d030106100400c0040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 846301771 1250 846300521 846300541
    0x20a05030c03060420091f05040204181109030d050318012022171005060105070f051609090506060d0c06140c0f0307151802040b18040311150c0d05 65
    0xe0445e1260002120b505112a400c80e0304420074030303440c103e8081a101034590040c030050f0301403441a8040c500d01c00c070440700701b410160050b4281281440c811403c00039440e000038a00520f030400c43c008580c0010a000581030b100008003e2120f0200082c810b10900c44010001d180340740e00c500c1c00c400d501140001042c43c8424021100b1908a407000445035241c1e42503000c0c900d502030307016200d0710544200e402c1d00482801103910401d030585415040c03000b50f842d14001422040801c44d002d01540c0302c90300d5600140400c42002c0e00240d1000910a81c0b00d1815525284000d85881c1c4240403e05610000800c48a0031a064507500e103030040c081c080d4020041d505000b01c0c2103500050080d454040c940700000006000c10346e00842d03070703190549a60140001151422581407500484501d00310016041070707085050842e00140010f4121031a4540c403420740d070400e59040f40001e441d500030101e030050400210b1400d540c031200b05413041c01c0415500c025031041c1e1039003640e01d030b84490001310045a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 846303021 1250 846301771 846301823
    0x50c0a06060602060907061e030902060409050c03100b0310030201050901090e0c12011a0409020702062214061c1d030409050a050f07020c040e0c0a0909020a05030c030604 75
    0x98041418460180c8551003e502c994003154081024407130030f0000070744a4850303968086e0700d03804004040c0d00f032900c0d2003040300034040881c3c080c0e800000030040003c61200911599100c0e1224500c0c0301d442c0d0610400b4030602e1b886c5ca41c01088400c0e0180b040c03041400040400408903942402c2080d51409118010380b51b20a9591150700241c8216081050444c40c400080144180c6c02c41490150b030f0300c3c1c01c05c0a00d42e9087e0202c042d00d80b90b0500040c0140000382e4000d141140c00107003d10706218541010b007142c11812008042044402c540402c441405002003c80000c02220a94184445504640002d02440110300c4501c6c0d12a4141205051070321045a00390348941c0903a661151164140c0c00540019150030a81c54607140006209000200f8007038021490b503409000704110340c40810000d419041c01c4e2040c60700940c00507414540d2448400002049207000209160700030380100300c0c10450315480035000c3d13040a5459500c0d0389e000300303000d03a00a5001c10b05002001c108031031303050612 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 846304271 1250 846303021 846303023
    0x71404030501020414060703140a0315080c1801150503040606170d11070605030402060a030615020f10091e0c0e040b151f03021615140c04030f0201050c0a 68
    0x4100080100c18080190001e01c240c404403140b0800304e445520610070540325000b00580010f20291401418442d03480060441d00c089140c0420b521441500e40a6514101d40c002107403940071101c1448a41828620b542c44407007074800102071980761808010200c1c400c2a040b2003000303070010000c1e0400c0302c160300c01c00241c0035508484039144820190b2554070640281902c000c030303040030380407909070b04004dc81005071106580c07072a08540b5aa8240800307a0040d06080080c161966000720b00c1c103120790740c4008101c00c164028504400c0c00d100050400c1400000542002d00345140340b404580b488280c0910050040d20200c406005810040024807c42d003080c1502803003081400180282c074a68103000d000c85209000107440030000700090410290360040d04505140c0c1c160b0202030003640906203c0300c490303007050b2400039141d5403820880d40c011a03000ea416514100c0c020004040b40c42c265100b1194020035140078159162440071281c2000f00074104400003412316450241480200019 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 846305521 1250 846304271 846304307
    0x809012714150417070f021017070806040e060c09060c03040914010e01081b191d0411030a0314030402040f1b080604020901051206060c0a050d0e0d02060a0807 70
    0xc0c00259000c1203202c1003e03103060783c0f0403c800d2030749002c1090100448000651000508414403059403e000e8120700c40305194080c402001f01c2d02444100c00e01c0f503140b00741c41c3e03641d41003480d14160042000700c0b254201d1b506c0f80341d0b010108000c440c6071104216458241c086420390307140c44645000354a584103c2c0c10108841d403c0c19102020032606584407410390794141c00e030030416a00d822040d03560350b11a81c000c8002c45100450072206040280360404103c003003541d021041e64854000400c45006480c0c001341c011841c404000500004020800d103a030000c4018158503007091320010030800e180f0030350070404174002012608540d80c56000e031403d5500c042003400680540c1c030351b00030481c20407901c603800f25201314001a43d600e01442180c800c204142c50751030405070a80030018410800030185601314071700f0000d5801c0c109041102003021031240005101011030060010f0140c1701100c05140152800f40a02005a851406072030384e0741210318003444203690720501169448080910340c025 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 846306771 1250 846305521 846305533
    0x70504051e03010e1515041a040e01060503031b0616050d05101203020a050c06031911040b2709010501080c221202150906030f0714030a0c0809012714 66
    0x9803a44030b48030b01c1c1b2030000080742c28190b01000d41404140e442c020224117901403491081542071800358800d9604407044400094020781382d001081c95680100301c8050069035542015040710300400400b5031241c00e04c01c51103d00d030001c08014100d0300616510b810b40703d841d10000350074070100c40f010800a0004c07240464080b219800d010b500d400070380006075298080e40340c140940d0700382042124003903071100303040c1c20600c00f00d400700c2700082c090014407400381c9800300000102c82107600c0140c042c0e81d0485460211600b81e42032104a1a0224842d260141e4000001040940e8000050a50180856005e580d03522620120001d4400c40c003110048107610060020130a10006c400d84611544281d070307840080152805030107918003a01d4801da174010020400500f0340c1142c40d20454008280303090a1912500859000b01140c1044a085981c1c27030b600e4007442c0e0075660100c54a50000c072490020403c10410f1048070b800d4480b002044c500030b0825086000410030300d2008004501141015100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 846308021 1250 846306771 846306793
    0x10c290c0a0818100c030b0a0f0f0f050117090118030f030c03050c090f0102120c0a060f05060307051e1e270a09140a05060708070504051e03010e 64
    0x103101c0c0c100d075a8400020b0010b100180b000c641400341c540c0d101142d8001416201e0758030507900c0180c04680d220b10f00309521004600410388800359441702401600484005848c203140c0242c000030016440900044642c0b0300411072660400032003400004e0b240d012260360342e90307103241d540503145002254502c0005a41c00d00c060581c44001d983c1d01c80000e5506129015004404406860b0241c0700301d0885501086242c1c40d615101d581d14030030b00c2d818010b50b108040039030050011600030203291445508105168010040c1c54415449503400c8c102080005040880103c1e171341e400f40b802464016004501806800b82d40308201404030b03078004040742c0e0040000b0352462903000c1460902c034000c4c000400c0b2140d00203054091302200d0781030581000540e9980880750340140180540c06d0310b4142c40e5a1074528020410700c1b089580a000d08024071060421740d10040415400030a00070070088144814003103942d51601440d20310041d081c2900c035483e444e400080c0103000408143e0410300c1905400c078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 846309271 1250 846308021 846308041
    0x9200307121e0b01080907060210050901110301090e010b01050a120c111e01061401050a0315091b0215010f050906210d0e03010204062c0901060512090705010c29 71
    0x110710343c2e083c0d0703c00300d042d282e140e62150307281171a00510300540c00441c040d113401c0c403c0b90b1050b070340005402c0012030090388480201c04180e000781c001c0580c2c141c0765816411045002d010f020441502845c003180741003c1d044008043c80d1001c0402a2245e03140d20100400301d100c0c1c003c0c2d0154104850030384884c1440314040d180c071160401403010007035090400001f1028402c0d40004401c0e801078442c2c0e441c001c1c0005e02140184441510401440303683d10021075920703a1031146042c0306038583c81100c903a8840304000b074542060700c00704005840668005104044101c4030210454070140c603a691a07450768400101e007101c0495100040070039a14108500100004540f4000d03240c80d01c8035240941600281805d0b841240540301c0400e09540802144d40c2680e0f2902c80008401c01f0071400a400010004043c50000c0e40188009203000c1280c034144220f079201c461b00a4036403002820310502d003400180a0b151701e0703200504290810a550166102c40b28421100cc1c0042d030070310100e0b490515407071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 846310521 1250 846309271 846309281
    0x80c01120c024201060f180305060c03042006160507031406100803030402012a050109120e1906080705070506040c06110f06150406170709200307121e 66
    0x540400743c0045915a52441c07044100e040c0d0f0280c1d51142c190140b820425100c4010811000c15442803440c400030210700107029550290150642d03469990a15007080d001e40c405091550036100349480f411411540c1d00c0d0115154100c010320040b948049600781207081c0b0016030f2025100d58004900c45003c15008208503214501d41c00300c0586036034641d448203980303010444d40240815000c0314a103818403040c2c1212a10380d03880301680c080703950065a90b603080d5200020301300c500d182d8145846031042e402008400781810241c40405e81e031410340c0c0c1120303040740c1d140c490182030001403008144968440c03001ca60040b0342103c1250440c0c2010b03c0c2114580c0824441c0d0780014040b81e562141c1c006021801c100003040c094024100d9450340d070603c41180c0320f0060f00030b03070182e5220b5002400800891024022079404009842001d00e032045800603100300420b0703a09403a10560030100b48803828003e0f42d400201903d00b5880780a1a900000010700b0351500d0103500c0310300140340c46e58860b295000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 846311771 1250 846310521 846310603
    0xb1b040f050a15050906030a18030c030e03120f0c0106171005010605030103080711131a030d0203040e0f040204060308040902130b0c0304050904110406030c0f080c01120c02 76
    0x441e180590300c4800e40115400850a24000381c4d040286400c18500080610380150a801d00050510042e5094003d42c021440040700443e4414541c030050540000302d24010a00c190080c0146041141404489100303c0d505181c6e9400085070040c41c5e02001d6002c030b80a400b0382481c081c00711072720041055603041030465012405e420b04002042003481407054034100c9502c0060075040955070750310b88546540d00f5800c2d80e082842c8007e8000301403160701a28400903c00031003180f00e07a00c90014142040d800340000002d40d44104410032144410188a90b8004181c1c400e8102985492000501a00450b840a07082035004100414164540d500501e0b22507400c40780350605c0380c0d0300c8051000900031100d2a00080d04284000c02081c1040a80d0a60051082c081c4200041c00800014100c607207503013003070b41d082e5504502803000c4088002e2840c0a0034030a0024550b4061500c0002c10090540e0b60280d50b06413201000c0070f146008200301e21000c0d4401c0340c0c0d080c918903a803189590203081114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 846313021 1250 846311771 846311779
    0xa0507120905190c03151a0607031206150324030b10080109030801080c0d0302100f09080307211505130207050f03091008010315020f07050f0604060c0305130b1b040f05 74
    0x41c00c0e0420382c640340b01c1d15847c5030300c6004100c403410b60001040130304d4020410541c00d02c0711641000103420160311480c40501103081c5013144030240540028200d42c058002201c2c41c004111880341560703030340c00c50082200d9000740140c40641d10200610780000580d0301c038204540c20007041c18101900301b0b108605903a503000031101c00b01150400c00c01c3d901e410040140160304401740d402400056500100241c81c041e103004a0001c045640301c0c4420f42c000c0340c0c010700190743d0032005540310305013890b50700c56075400c18410701c00032006c1a80450540654499244100b6040b1403800d035001381074040d030b5900d0750043c00380c0f0041a4407481564580d8010740c2c1d840d100d101c000c02400f440741d006424890517aa0000500000b0420210f000343c000c1d40b1060300d4001803035081c8180c0c00013400401c00902c4025500c4060001400c0910380081514a44074a80341410b0414081002c02074801e504442200e0b001203000c0c0c4251622514131012034480710501d07001d062b00003000f05169125400e4001101d005036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 846314271 1250 846313021 846313043
    0x4030909050c031b090a0e07030e071e050d0b2d13020a05011119110303030c0706150608070c060605043206031902010302040b071401050a0507120905190c03 69
    0x510301d00d05c145010b0720380c41800c040040c403400c80100c00d00c0742c0c45112405c0008102c81d02901c40c03032030605503034030100070020070311080345030401c2c400301f014002d0105482122441c3c00940c0d940041520003001c2040c0c040d000c00104452051429030785002d00b00c00b0091540ca41001000c0151400074240107034002c0d410841c00040f25445801da1030403e64004001d80301144111800d40e4104480060903644880540d04101c0d8540d0140029400f40024160703944d0b86044914004040d038507003601d81e0000302802082000001d800c000002d500004510340044448480d261100c02441c003500615001442c05429112402d00002040d40f007180c1807035213000c100140c6000c7c000d180002c8075a0350f050b401000c4074031f50607949040b55401052050401504107911030340316084e203800144056a0707d5112080491000c0c000384610380d00010740c04024003082c0752982c0007500768182c2d40c004410142c0c1c6c4400410a0000611191101d441031118010400f562414440d0449255000650740c07a0010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 846315521 1250 846314271 846314311
    0xc05090a05090f28052d010e0102040b07230105090a0201020f070f0e0c0f0d0522031407050a0605070302090a060912020d240c23070b04030909050c03 66
    0x181c0c4580502d40c102e00003e01604901290007400c04c0004104c0d503d21403a040024050040002902c418600c1c0d070100c41c564241040c45800d55000265018090340704000500200c0350540c01c40d036495400400741e5145810005100100361481110003806520b402c0078402c2d030400100711840b59034002da00715986255184403d64880903140f1400310500c070000401c02c403020a4402c2550f0000081c1e030502c1c1003421420700c2000380ea00075004450415528010081d03010001e1084055001c0f0300031890100c80710951700508080364801845c04049004540e54040003020484110310710380c801002e00017401c2405014001e50802c50742a44a02ea00301c0d804106184200803420896200040315043c4003225001e10280c2503c10106540310495040e0500007510034020351b1080341300c650300c0002c1c6804081340003020b206a04004040d5514442ca20f589801000c40a0b54101c40d0440071510141d205c919080d5100c8510b0ba101245960030141000b01580c42d003409907110780c0300b80d11000c06640700 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 846316771 1250 846315521 846315523
    0x3020c01030b0a0e0106141306020601030c172a0d0c03060b030a08040e0601030f05070f0305070e0d06181208040c0504050402091609051c060c0201050c070308040c05090a05090f 78
    0x168004c85240741c403400c004120680c85064050002d42c25441850300e803411003046000c968002c1c2d007200e00982d0010b0b00400400c17022213030b090001c00080380440b00203845c29400c50703115600c0001046804000154002c50480c2d010104041e121004110540b8000b1514209030224511311080d1881890408202e02c0342c140800c1001040d81e1040034149031904091005601c1c4030080d100d10b0401d0740d104c40343c801914081c494507004114136162003500380034a020080c2900c00c0141214104030480b495059aa00e800a003c1c81466012002041c03440c00110950200c0d10b0305400034000743d070302030014140c10b900b15408600850180000c002280d8441e01400295142502c1c001d4008a00c04001054203031001140c032404415031400c1004560f680c00025002c088103200e4003000000422000100303c1c41c1e11541d43c561078240002e00107858501064141802842c5015040c4804c0c0400a02000039951608002d00002468078644e410207103003180003000112600712240c0315000c50380c421144 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 846318021 1250 846316771 846316789
    0x6010905120114161b08092e03020a2003070606120611040303050723061f05151c0e060a140a09080d1121060a0b0c0d270303020c01030b 60
    0x2010f5200c02407000998217032140c00981041c001e8588003401d0046030129a1905005030101e400c81e4000d4154800e5201d00b04001c1c0c0c0304181d038005251042003241185a00301e107200c5010020b811000404900e0100c00e00d0852081d444020600c9151980100c0d02281549441400ca402030004000025032420b074000c50b03125078000a8041607040c411103000580104004100c503582900010b804080100c0b050f00c0e100c0d0584811f488062031821880a910320050040f0041c007040350701191010311402203d03505d02c00c03c2400f040181e800c1c00150300c22100d40c0c0061403000f18136000c41d0018074210f030320742005140b80e04071110111905004070f01d42c4125401140324aa400156240c5441217002c50750b0020300141e00d80c000714403003d11002c031403960198004071070048500c0b4001a00c0c0350010422581c03207843e0308420100c0109100e01d940c810301c00201c4811002590030080103800316074000b10703000b501d40103019a1007540c01c07101000309980450081d0300f480082c2c9050000e101002c0030450218 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 846319271 1250 846318021 846318061
    0x515010806100e07050d060f1802040e0109020f1605030a0807020309030606040b0406081005010f171504030309050f1507030207020d0224070b0f0a05060d0b06010905120114 76
    0x40380003906001c1c0000f190046034001c5a14100903161864569006094514940c4040152641d180b410130080380400e000850549a440085291600380603291850b080706010391101213034003189030305d103c101d0790381200c07070003078604540d916203103640d01d025a80c1e82d1043c07038120001070300c20001c110010b00010507201c6040c8005c001e049596248000e000041800300240c9511588407880000d5550040c440504001c0c000c0d04086403070b42c14120341c901c05400c0c60b4401c03460122880c185000e049c0011885203404620307000c03580b8040d21107045c00c5014251581c2c015000d8080c0c80e1245003a6030b03002030b00402000d0110075115441d6074289003a0300320702851001a41281112005500514100d01c54039520001501c40281070700d5040440071075908010f004850b041020014006c041c0d00c485215540456900028401c914000d004541920034000c1d000709401110004250700e680115503006c040c01d005807501174403600140b0914060b244425400c942120903002041201551702d008410b10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 846320521 1250 846319271 846319291
    0x9010b011202031311150d0b040c051611040b090a05100602010e070302131104031b0905010b160203010b1210140603120d090c140913120c11030102070515010806 71
    0x1c10610341759030306003144440d1000c2d030019100c1c56003a00140f01c2e00c085d128444c180000024030394140018072017140e810006a5085c40030a10414a060000040b2600301a5004000625490382c0d0008980070300380c142001030b44082110100b000030381459108500c11100c5248550303034075a42c2d40702a403c86a4507072000915030042001400582811401c01007110b00c41140000c50040805030300740301b500a500b088600e402001d496403817083d20026654064400000c080009500d0450262041e104940b904d2095030080452841559400e41c40091404009001c02486080706814252200009809015058a030180c2a0a600380c681da000b4468240a002404211219441c2280c1904800742d522541c1c0c0d102c0e403126000a0941d4100c0c0000d00c18403826650024000d81000300704e640051010003a0407002900601040000c1400b032a9a001d50412107480d0720a81007400e6940040034540d80c0560001071020104480050f51070803a150b00c014003000c42c0d0325900e9898482e0710a4402040c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 846321771 1250 846320521 846320551
    0xf1103371d0a0e0c0a021621080c060c1308010b0303160c17061014010c0803060307030209010f14060c031813051602060603030f161a09010b01120203 66
    0x2032080c101c1c1e1151a0000c0040550391415510310460a5000040301c200441c00404504100d200d6010058000d400030982040142c003401c02000c0c0c04000800001c0e08421541420840180003000f0220740408108805a518600d4817a4101075141d10540031002c40c0744120400003480c11041c4034404446d8401000f40d40742c4050343c0c00401c103010b0100410b80e00c000075240001180e410201000d20304a0504014003040e1504142101d00b10440d5400114116131103032101002c0d0b079000350709580d03096002140c0d0340c40b5211100820b1078090542c0000350030200e034000210300310082d94100c1044802003820100120441420f0105900800320032001c0c560007845040021501c401003002d030b40f0742c0500000c80700c40031002d1042c207451007501c100200301d02202c16814800d034184401c0c0e0740f22006800452400f900303841041001e02c2900401075820100c0e40800c401c212000300614049440459001e0303060074401c3c03800b402003200748855800f2982e9a07414140398210350007034910840c143d401c40743e2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 846323021 1250 846321771 846321797
    0xd081807052409060c0a05011503120809030d060909050c0105090d110f0414150609060403141c020303090c0f0f10120c11070506190f110337 62
    0x200e803000c02108080b40da071043c0b1542509407104009024610310719001000161001d04000342107558a6844110540c030b80031090011803642992403440b0301c03040c5001030045d603030721044500310700a041c50141030a01700b040c00100700c034141c0c0107030f2400d42c0074100751415040d0401c0151118462250210b4000c6400006a008507000c0c400011030f40c10051300654800240303400050441d8800810080300e51a00c0052002d410314400c0c0c401c0e0164425282c4501d89105400011a1030141e4407000f0400316403500b18443c651000d1050002c0d003105104c81301d98030039558401035202e8004444580b0640700314509100d0918041c4404500d00307001824070b0b1a060181c030140648000300309661024402400c03c8007900ca04280314170810580d00c4d550b03c01c031700002d1944883c02d1407042d40c400c51080700c003070045044012242d41c41040c1c0d8503040c03d00607151441240155000c0c815802c030f01d00030b404086101429042c0da4281201c0803482083c508801840f1a8519804c00300b80384050310004140146d207071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 846324271 1250 846323021 846323059
    0x12070608010f050d021c0501023015040207060608030a090608091f0207030309151d060c0a0f140304060b01090605160201050d060504050c281e0309050d08180705 71
    0x6020000e03100351b0080000940b1141d00f039910102422490703018080c0f440d004d4040c00e044007203180981001c0300076a4182507280b010420118402d061241e540020f203402080800e0340440c0c008c0c251501501c4e114400540080c282012324860b0001044010000070012680030884010036072003000a9900d81d00304440f020000e4010311011802e05549450b08008591035081824405100e610007041c01003803940201503041058400258030b9018106120406442c1415215260060302d002c051101d000d03c401c4941c2c0e03400900d10f1068080001c14401400600c0c0c0091038010000e80743e985420340d42c1c04003107940d48a031043c0c00c0c420505100344c240042d8410300040c1448480f900c00818081c1e11100020200c41c4c0c243c1e20910300990000b044105280018520500318900d4041352141182552016206440d5400c8901014003000f101c82041d500950103203c116401c40101c9042d04410f0708007418215043c2c40100b50f0403160350b0003038807c040001e2448103550010308442c83e501b002403061 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 846325521 1250 846324271 846324289
    0x9023a1103011a040c0309110d060b060307050c1e1f0f020d0e0c0103020909011502010207120809070f2607090504081e0301060e0f030c12070608010f050d02 69
    0x4488403201214880d00d240d809005032410764581d241840c0c0c098080c1001c01040307484204441e0f0a16003800e03e500d000ca54110b40090300350071300341c0d0249040040703032902c580200125204160f2150011082c0702e101d0b41c0c4100900502103000013200c00b6200d259085980440e80b0022031415944400444950f40d044c110500320308810307524000c180ca91140112100307a811000d04803c200d0f40e524101d840400d001c100306c046000e82801e0071460503003004042201100c3c14000c1078203440301c001220485503c04d41c125031441e50840f608045e081d41c40c410041687c44280c44001c1d0500c01c64102041248451240c5008c65074401506801c10048811035812081c45255a800078010090000386c051014098248a40d20440724145e40340e20071110005c00c1d0120018100314620140700512003282c1049156621034822100320a5062100c00040c1c903084146040c0358024000312840c4001140018610084d40d4960303c1d55038842c0e0b218104022a04a24481e250740300e099a40d1305005814943d00e2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 846326771 1250 846325521 846325523
    0x41d0115050d0f0201180603240f0e040c1d0105182205030403050706080f090705030601050d110a0603020a031802090609100b03070e180708010e06030a0506040609023a 74
    0x17011407040c04103104421b425009621480120b510342181d4014030703001c41c0d808600a0340300803c1e42c00d81401c244900081d07480300e0050486d10b114100101e400d1102c000c8400c4010705800c5401e290003149010b84541460b001c0c8a1030703001e5101d813450075206c03c0094041e10300c1750002840560031101c40040019981080000c01c0d030381030000b084044041082030044001034099502c401c046402c0c07150b4840c07400c0710003cbc0740f05441d81014030305004079074011509604440c000c035070902c00002a4105a242212140c10041d4000b000030700004181c0e4058000d0f00c2100510780701000210007124a1540701c4941c0c03c0004e46c42000c050001d0481e00e030005140c0d401c508140c2000c0c8040d81c40744000c401c03551054440d4800305080d14103100d50307450300c1404031003806d18661460106090601c005030101e10107010b021810075080000441e0307a201000358140fa07541040880f0814180303810400014010048140c0c00b030515402c40c00900000e203440445030212094048026808aa100020060344504 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 846328021 1250 846326771 846326777
    0x6120308041b08061303020706080c12060f040c031a010908060604110f031323150a1b080612010902011e021504030f0810060c031805041d0115050d0f0201 68
    0x103001c26100010414140300300002d41c1d003090481e05c1d5080203450404194013800c1041442010032541030641000e40f40381c0070300c211041e0120384170400000c205526148440c0e82152804c01d100c085654140c0200284c8140c1c88025050301d41c540d4011140318100c0d008a098a62084004c1400ea0400360701c030490b050014503003503040841c0d0031194101c942c001d85a26034404e542040c00c40912030000c100fa24018034403402042c42450300400980c59944135020104403008000004500c0b02071a00a172030b100754440001c0c04044075424000e0114401a901240500645582c0e01d11b0b42505103e010f801540585503503030307011011030403619403481e110340c7d26007140920a03035079102c900d15080082c0240d109840e00910350942041c01032041c00c004000300c8008004200030070000b0b4201c3c42528809070945010f0324054100d580c10704100c1011303032105421a150107403007107030b00000408046005e49414001e11180328100380480f811344642c050a035000b0700488040c0002644c4050203207580d84181 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 846329271 1250 846328021 846328073
    0x112a190f0804091103090105130309050913061d01060b0703050322020301320f06210601170708011b08090f120c0114010e07080403140f0d0612030804 66
    0x60400280d4003000c80600d078140005c000c1c06a100000e004541d0b00c0203041350400c00315003081e10020182c4d00541700c1c01d4007546c540c80c04a81d42002102c03109115503080300080c000d5410b061448001c0c02d2220000065552030a0008500c003550300c6c00725076185826036a80790170740d01c884201c40e0310444003101c207180c41e08100e0011001a1402c4c080c1403800f86d22140400c0d202c008600c50500e000442000785114080c0711000c110352030008000464100d4070603214800403954044048188030f032800ea82d0003161250700300014420091594403800d80e5210803d440c2071554440d0703850b0036a01600c2a04450715000006400028469401d0f242d0210500003101c03400502c0716482c07030800d0050340f42800c0050000400c12689142400340120200d000407003490f8030361400c1b100640c4641e01401c00070800070380c00042414184105101301080381403201365582c03400b912448809942c032440c6132858241c10900005451941490900c1d40c06230103440e008155902d643d200910b0704e9001c40c401840354449 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 846330521 1250 846329271 846329279
    0x111030403241b0e091b0319020301121703070503010b030c1c06061b0c090504020a030215090310020906160c120804030c15120b04112a190f0804 64
    0x80c02003d03d2040030900c0d000b03285810f0000103200c401c0441500340540d010109100e00004030041c04400c00721100c00c4030ba00ea03101d0f4814505a4140c9820b42d04900c1d002000200701c8821921605040c14800c0e40816030905582044100500040b174485000c0b513014401000034032a0900210380c03114443c401c0a1038104070791703c1442c40c9580d26141402d00d036a5864207001c481e4110a1013911880302c2e04001c880300082d59202540c290301401880701c01901c980105e8210b4a0707900001b0080d41d8010034100114842d80c19862040c0c00c0f5880280c8640300340c101d2505003044510856401140c050012031404034540440070b1064805403084851354803803e000541050600150a034542c032500f001613659245042c520035551260b0030040724a04400706040d9180e03000b90040c1010b4000307640201d0500380b4180044c000b00503640c10498140f40008483d075a44040112250040f6180300301d01004d000703d980c0130781e51403400110702c1450052400a01c00411546000c00304040d201c1c4804034a001e0325 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 846331771 1250 846330521 846330593
    0x1b14070204140604050121020609060d02030f04031407030f08090f030c0a06200913020d06180c090503100e0304050d050a050d02120904050603011b0f0e0111030403 72
    0x40c80300080b9981980106004641c078040c003a0750f004040181013500031f075042492506407050914402031080100040c4010b05440300c1c000c1d41c5d803401c0c20b904219100e02c1d141000d001301000449048002914410824105501d10b60681d8002901560b4822002a180c102550700c3c80016180410300c0c8614000c0a4500e032041008209100590014025980c180d18100003622103203911012074908070f420499440280380d060300c03009070080310480c45004004103000c0c024842c004000c034031030742000000300c3c50700f01c540701e201882c0b15481c0c010410b503100700b101244c2c0110300d40280d6506030001e141c0203600a02759044004407540040603680340540c0c0318000fa0b210441020102c4440c0c00c007808000910000303004252640a0300d002500060002c1c8204130500e102d034238001c9114035581c40120710241c900f5846280c480105048191821041420151006450507100000142c4070712441e00039521480d8a80c11031040c0000440c2498115500c0b005126030500c65072080e481024106110450 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 846333021 1250 846331771 846331781
    0xf020919090c06020d14301e060603130303050c090442180902040c17090c060d050a15060c1502030705090405100b0f03010503101b14070204 62
    0x101c03900202030ba4910301034000c2e040c400580ea08005005040c5008103035881d01e036048030000c40588a07600920780f2220320036290702c06403500c11504050494104400c10020000e004c2c00703540c8031361011032035554400030401148801c82e802e0b007803490b40300840c400103030007500103581041c144504a41000c003103c0120741215038001d4100303e600030040020003500e1060b4042181500c4403025030340c441c48040c4099048040341c0c03103030501016010100890700c1705258048160301e54024010310100c520100001d005801d10310110410703403045000300d40000400140da007501c40f406407196091803440c44600000b040001c22042105480d0250f900c070348141c401e00c60018150315140c024070f520300d6003850602240c50706140c0d00c0c0584104240003503941c200040d5a401001203c0c0800c09a0320103003c0700040003e0780c000741e0b40500104104007a141c0b488080c46c162078040d01150500448000c0803010354070980005201542c4000c1c5119149100300000b02d01e01882e4800a46040865808601110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 846334271 1250 846333021 846333023
    0x80310180b1309020a09020f071a0912030a02040b04090b01020f03030709050d050316290103020d0b0403110d05040302090f04080324091305010b010e0307140415030501020405011202070f02091909 86
    0x2303e8002418410014844076140b50041555071428542c54030040d507030b030352310643c17004030300316040110005032818001c1e0103d070040c0400401c040c0c5c5590343c03885200040c184c041001c50140c00365041140807031000105072441120982e46042c842c0740351509010080d03104450598150004000008600004004802e04280319641130003017081e4a0000c1480140009180172402d6401c0c00100096918070542880881d00b1119041c1a91a14542550040711040040416006500300c00300a80c0d00720020b001141e00aa4410f881d65031040c82d05400d41c1b508613002000c514050010aa450303c80c203c064689210701c0f1901150104d42d04c0c00602c0400c411111a0581c0000d0501d03201040428000c49909050030b0801c403044104032000252a02414040c078800006050b00141c8142c0c0d841e0046c030040e4103c1a5440030f42601c80c20442d02075807041c0100d502062010b0a000fa0030545807013256000c0d50452031920100c081c0b81d0800c400103801806522819a01009420b00c45a49200c1c0449803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 846335521 1250 846334271 846334297
    0x50409030e120613020906040b09010b030a0c020f0a03030209010c06050112060b03030c1e070e1f1a0a0e060f030a09060b0f1e0d080310180b1309020a0902 68
    0x4000c0d01041184442802d68800100e4000c00c0502c540e401c4161508044039070304607119507851b0355910100d8024068040d82e03a9110043c14000a140c07446100194021400307510140600564000d09a81e0750780d0810100c401c0b80e001c071400b0400310b072003035001d8588104145000008a10390340c440e042680d60a03009810000c03e8100010100700991103070b003105107010f90203582130450340c040d400d845034160b840b860b400c40440700c0d050b401c14a061151901500c620140c0c22164182500e400c0d003840740810030102041540d0902069581e290842a010f803a140c0030f0f002e01e0600442c500300c400c1d1041d041040e8020744240708018074948c560b005036120f0881d99100142851060034041c0c01e40d44208034840c040c60000c08800d41c180c580c4031421000304d0032a4045984003240c03901003484039040180c0601030507070220a01ca058203290000004540082e401e02090900c032408410443d00d4070450164400c101d2182010300c40c109822645c4024001490740c0b50942d907a5039000c041e80d010750821480c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 846336771 1250 846335521 846335537
    0x518040f0c0e070306141e0a0b04030605090c01030b0a060c050106210b07050421020f030f030406110606010f080a0902030706050c011109060f16061505030c0328050705040903 77
    0x12184e0510503103000782620300c0b503070f040b001e40c0101044001094030702d0103c1654048244440d10745404410600418002600f586c1d11275807418000028034003903612a4803800344180800b407640c03180c0a915052000180800701c907900d48a020386280d0310800d8219842d540314040001d2068041c4581e00907203100c7d080c5408801014601909014001401d10f0281b01d0140010b1148454001c55400195060b13a8003c10302503107400090042ca034220110703a410312a01da84103501c070001001510444030a1b0322400842241c04441d141c50b003504031855400601e1031200907019900c07030f40300031b900100040d100042e01e0000f030700881e05000c102c0d00301d030700810310005034114011070074451720b070500840c016602d08003012200040ca83c0d1180d1400d031011080c0115900305010980008154036540c01441080701c18092034221000203094400c640c400e025491819900381404981a54040c082000c00c43c1d81224000000111021005003034410b07224401c8082343c0c60300c862081010a901a0700c0b1104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 846338021 1250 846336771 846336781
    0xf07110a0f080f011a0402090609030604031e0309080d1d0709060f0f030c03030f02120316030b0906090f2d010e07020d09060f17040b0601030c090518040f0c0e 70
    0x483c100704164004000e80c5815204590703d0b510401e0b5101201088a01503aa8120140020411f00030703243d41c10f50601400060104154003c684080709041c0c0840c3c004008100007000d80450740e01a9028100c58400c000d10102058079504c80401c180c01c54203518108101d070072074249081c0032504540816540d85106000da00620507028004250708403188245c04e040d9030326408002c0941c8401024400d4083c0840c00280c000d0000154040310388280320f440c0d240c10302503404114040ca062001191804000c04e0981c00e20070700581c810710002c7c3c001300e260f0300c41114140602000414090031655407500c0112603000c01c0b403411024249496200c0190750501004540c0f0f40c0b0080d025009540c0001003041e0400e4210f102c400440c6c0481c20151054000d080c1d055640f0020f0388101d00d004501c1808000402141c404071314004e0303400303a0b42000155458042503800003c01e0050710741c00700100240c0140004103182d15684144030b1052072095003200d170380d00705c45442c40b900403444021584013042 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 846339271 1250 846338021 846338023
    0x9050a0f05060d1b022b02030409020f040b0304030c0b0703020a081506221502070501021b01030f0f0f0c1409220203070c1b0f1e081c090506030106050f07110a0f08 72
    0x46c041e034079403500c0d005803414100070b03541c0d01c2540700700c10266030007081c0308442406a000780c0780100003001c01d0a541386024a00100b00c80b00100b001c9a0070002c403000b14040074401c0c42598100252034072481002d4a840780c41055003201d281102e60f01207010481c0040c00f101509100075402c1d0810300501d041410018110151000341442104660041204011aa03400110b1851404400c010b02d040645403100480c050500d60b0305005406040030000b400700651907229a86034051481d040203003540b4a07004482c55a03654091504064040c0000500307890300c0f995640ea4424440039014190200030420020ba0b001252100d0120300100c0b1000248105604021915040d42c0f01c1050098145100286450704074000d030401800d9184070400c003210840e41d1000034008080484030443d40800d84c20411805054000300000c0800070002498144501907a05a9006489050510401c855418155000082c0c252002000d08501c5020781c1c854a014102a00c1030f00f400d088a141020512 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 846340521 1250 846339271 846339313
    0x15020909090a0302060403081509040c0303120903051b2416030b013e010605041d0703030f0512070806010f0206091f06210309050a0f05060d1b02 64
    0xa803640100c0ca070b400c00260b01040740c59126038107003804134050b2119582070003010074400c501d41c0c01c02002e00038401440b548003d080101c1e482603590303a9070b1300c418000401c04e8503080c10005011800c14410310601503a024040c02c40002040101c07000c80340c00380000d10030b03840b100c8201c94219a08105215200e8000312000e140e2800314181481000700c5840001c22030200c2d00017820b4844054150300c4404400103210200240000403441802c200300141180241000d10800c1e11851414080101c4803a050840b214400000f1015003a04c070728540b0309698541c100b1000c2400c00070101b007200c981c9201c1d02c28040c040d031203982d40c101039132901e880050205885d603c4000c0540d4030040c20404c92010000754146120207403c90107c4410441d5030210162210b90010711005903640840c0e500000e070b503e6000c0c00a4041d94600d44042d9640301800961190360040120100c00e0401c20b02c02414108001c00361400c03200fa0002c0c184405000c0e6581c43c00c850802180141c102c00c9207000c0c88221000d107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 846341771 1250 846340521 846340531
    0x18020405100f030609020109080f0c030c030a03120213050a0b04080c012a08090607030c0b0f0106140703020c0909010c0e0f010509040906060f06050714011401170a15020909 76
    0x12000265041c240b90580194a80c8002080030303440e1076a0b01d0443e4400c1c81c1c980000e100520880d9801c0c14881447c0da190000300d45520f010f0b10030080e52040780d14002403010491038040e102c0c0c00880e02c54543c800701039400004450156072280a002819071501c100741c40080c207201340c0b0240c5035400c114400b4144a4102089810440c6c0d001a148a099069174030b41c903d041c080c818501c0304030081c6448039481c000d18404582c0503401007046814150400308080d80f2511030a800034080e80c4010280c070b20110280203940004041c0480c014a0000500007030090794042e0040702c14000c802c4001071903511045070100b400e81d44614160311131a0301701001c100ca03240110f40b040d1a000401e40020a28011880ea0078801d0361510302c00130078410168400806864088921f80c8101e44600d009405a40511403c40d000c00e001e64075091f0103201031007580c1400b1010365910034580d02e002d06070284040404803201c6240100d02c03100c4005049101c0300300e4600310000d0050786400c1d00300304000da034103c0248 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 846343021 1250 846341771 846341791
    0x121501120b06040c12091a2403162705010b04060e03010b010e0607030c05010e010606120203010509010302120f06010e0a0e0a0b01380d0f09240f18020405 68
    0x2d030118074243c0040c040f0304085c030900400140c04180e4202500c41039604e0030301c1d0b821841c8180a02160600307a01e0f505c0a8070100311030820743c064400081c90b0343c0e012036000d060f6a008000320280710141d040343c5840060074182c005220440d40c000400c4088440030303801055603000001c0c0400c00da90700100c10805010040300200112841000080c003200100c5010b503201c0c1c10005910410140650f050b0307400c1907086002000940c0a092100303000700320500600700407812000300480240610f0007140c0c1a100d02800351107042c0d10350303828411700000c02c8140303e2650123548406d030f51000d4100412030080500c0034140081e4203154580c082114204081c4080c250001445040403c000c00c45890441c0c04401d4050380f034604206200300d089008005240b003070407406110f040c82c540e900d0040c100d448401c0ea010040500303c860500101e441850000780003025003000c0344602d580c8040600080c40c4d940c0320209803200c0768200341045401c03016400e464904c0300c01021056040030720841d81c0c0920102 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 846344271 1250 846343021 846343031
    0x80d0b0a080a0f17070f060209010e06070c050108131e11040e0c0f04020c0316020924040b060d060611100e070326040b210c0702121501120b0604 64
    0x28480b600d08200145018040c031600c84518104a4001310480d0401500051201030810382c61070001c0203035000000142c0090308111100b01d5070300c1d24108841c64203520250940b0902c1c50b2100641d408040140b004641c2050650342202161741c845405142048400740b00c00340d2207191602e00d80030080216080c1c004c0e0303d05030a8075980d080002e01c075405100c0890b04164401203036400038005c0c5c4155400705100307000200310b100c52240300b0f4000009151003207030210311030f5403090b5002851400c104c2e81051741707a0340504044500d05055000ca0012a00544164a40310000c40890165101541b08100054820380d40601108003400302c207048400c0c405041c02100c030521006583c4141901011305500b10404040f02c1021340d0304040c189103100300003120381780c41d540c071424051600049c01c800c0840c20088918003800c201489411703c1544286415402c02460350240140d542c00101c00200306d100c0d00da0301e81004149050028001e081000c504c10444483c4d140c4044d403500050020b50180e4101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 846345521 1250 846344271 846344273
    0x7050a0c081204090b0307090915050109140f0615130504050a09020a180f060e1f06050409150503150402120604030c02010507030e0a03050c0109080604020609060313080d0b0a080a 79
    0x4030f0702140c00d91000400c0c20003405000070300b05511a4040d6210390f203004000c0381000004d04202c0300d50a80c001d03040125070b0340e501014041d07030000c400300d58100c0180e2000a4006500c0c281e20740d00482d000d00000b1480080c0b000a86199201140d5080c0c0785803441e60420881c0350502480b6805520410301744800309055010510303030591030090803c0d40070054041000860389921201400b030504a0502580d90f651031103004280d0141c80d00c0311901000600d40d011012034603003000840d06a1341e00c03d0302e4185480d80300802000c441e0880f004400b0840c00000d000d507810006c0ac0f01c407404031100844203007810700c10000c0c01050b1015000302c942000c0c003084003203900100c41517440384c1c0a080c40340c2d9078041d5150407282d203180440081d5101e40000340100074058001142600c0440a80311596042e8641d40280d95601044030300a600505c03c0208114a0403c00301070354100a0340c4848480319000c5503a549502d8015995030085e042c0c2c2c13140829210324041c2c501000034111741380070740056556 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 846346771 1250 846345521 846345553
    0x3091401051b1611011e1806020d0e1c0b040b07031d0304090c1205070c0318082503020d060b0f040b0f010f140a0804050c03070b0a0806060f07050a0c08 67
    0x14900031300503011403081900c1c240d010b4501001403d80002d0324003082421000003500d4000c0b10342103800f065000610110b14280001603035420f481154503a41140c841d004d08102c80c00c40c0100c41e4194800100010344005115000360034007640c8900a10031441c82c0c2044010100c488130382219070320320700c2c0069042d04c1d1000842100c1c255000190041049107406005507004442003d0091140d8502010444442d51040500000b14400e9680004035411030301800310104d081e019032034254000a203d0511900b41c0d03d0500c140ca0760800035040560f90781e40001e1046001a10151092030310341c40100802d1a0035400a229220222000c03c50724a0f5200402c0a14150880c140d050040700d010800181d402950f9400d81c0c488201c008940d0b840310001c0040412005072000ca4452041800741e03007003464007207861130542d54401c0246040c120f140764122038001014102581060307040244c1d00041014100500405004a00910030f0704001c0c5000081d4010395400b0015035002003181a1103034003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 846348021 1250 846346771 846346807
    0x10207080a030c030605060703020c090606180906190806010306140c0d020705010b040501090230041203020c01051302100206070e1002030904090302010e120c0709020a03091401051b 80
    0x56140000380c100320f208007540104213640000b0741c040b50111fa44002c0541c000359004000e101640d00c1c2d59240c681a09103d0a40240d01a507400d0000180d5180d1030340c1825003c950740204020700c0b54490707a040d00d125141022041e001421107400040040c028401980660341e00c019280c0c048101525202c8130085090284800c80b80040c0e40001c1c40708180031003500003a5030007800070820070280d40d50303a802da0029800241494040740f400074002c3c1402d0050b0400004a001c0d00d035020301c15a0721a81c8002d04000341341d0514040c1642840051809102481070600c03401115141040c4281c55004000b030320031841d503921b01107501c0724081000d4981d00c02011a0300c035800391422444041d00c001e02383e0a40c000d40080f140c05c40d16043c45071040c541e0540010413581c0f2004199158480c00240c103804610035004c9001540d0304c0001c0c10840f00b50a035000340718a50314ad250003e0812642e95544100c03200058981c03e8a07034650082c0304410410300d0310718405a045c40c200a00d82260ba0711141c0101c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 846349271 1250 846348021 846348037
    0x40e01232203080a05070e180a0e01020c1c0219051e011b0e04230402240a201509060a060807051311041d010501110604120e060d06140301020708 64
    0x540b03407004030f0596401340c00701a480350001401c0d50a02e01d00c55512000d00423048036400e06860400002008040c1d041c030071901c0f07513510729000d0b160a01c0d009551780213407668444000d0440c8141103240c4c2c0c017620b6003040c040026111344040c0150056400030407071070b50940645140076901d052104020070008035409025600c403800c051002822590000740140328110b000c2a28049002112540440c00103885115600c01c50300ca00902c45072412002e104061a0010440024200031411070540140843e6018502c402e008000d840c600000c03c40c00c0419240307101d00685020414012800f500b071106545c400c0201c1405c115062402d40540d07510709c650b00c101d5018020303000315010500c80d80c1d0009075000e510301894941e51591954109d0805141461280c2c08028180010036a503204200319203442840c000104042c1e111030300c80082c0c141c03120002d00203200070383c241c0c0c0c08a40c8903807024010450320301c100019560f1400c80038002d15006180c0c000e110b640704100d254002001c04054a0141d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 846350521 1250 846349271 846349291
    0x901030305032d3601060911090d0f0213020a020a0b070e0303220b280c03090513090516090509030c0d0810050a0e07030b0a0311040e0123220308 64
    0x49034480004012103802049134082e1101c008444508203c0150011000c84455180030014a94403c5101406000f42d85919030301007214903550001c1a0a00c03c0c094900b40010000c088002c41c042112007240e100c0660721005d80c001514200600054200b8554041038909004a0844078000003945922a6040c0f10ba44482c203880704040400005c80414068101e140c0d10aa40e00303010f0b020841c4450380c07240c0c140c1381e01100801c44079000388110200b072007403075054960320049403d050401948001a80d004141703250307580081804104200100900301e0030703545400070070a0a00b020401955801021284140d00401110010510000d07440c0c04503007592620301201d45a0b4041080b6214a9900150f0321401a41003c21801c60317008080c0e00481082d1800c2081900a0b0140071651220f840302030f0101402900b66203560900ea00032108242c84c40000180d80c00c0000c5040325280000d0180781c0000c5010b204000d900e219070f20780c43c0f14660aa41c4080c01010007030b5401449140e0080c00940c031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 846351771 1250 846350521 846350551
    0x30a05271216061433010c0f020409031211031311120703080d0b0103050702100b1809010b040c051206040c0909050708090d1b0206030c04050901030305032d 69
    0x41080d40000c02c0e00d0380030700240070400d8040f491445514040c0d84818022600d5415000301c920301155800c1c80c8040703031120000c0c3c1c1042c1d400540d68201071000075901c3e15405058000144e8480c80b402c04020710a84440307480340481c015260032a5018050306100c0070f01001401241c0d44c494070004000755000d183c80d150982070201180d007280a40300404010700c52a0004000c01c40e1900241c40405200e03102044450401c0004409883d0140c0d009009030300f1100d85007019050b5904641c0342c5070805450716003040207039a40e0391500070040b1907130107069665411170841fa161a0280400c0d0a44602c0d105044c500781c0007440a82b0000074010324412981d4500155006010b030104030028481100700708030030329080d040648089030490f0030245034051703003401d00c21041c0128508201c0503a0480ca070400101c141e400d10610340c1c03000d00310041c1004144400102c070398440f801d05010b14465030350b05807039061203c41c0346420340e4040d950702005103540d0350903003035100d4024503160300c40b41700c0007030b112 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 846353021 1250 846351771 846351787
    0x9030308150d1a09104802031903060e15030c0d1b0608011a091f0f120506060304020f040f06060c0b0604020f0405010f05040b030a052712 61
    0x341d10845480080c504000390350f12194120074800524803900305602605e60719071041e0040000c6404052251180d04440a41810030284103500c01c0300aa05501040f00066041203240391000c0e0034540c0340700180c0c8002540b03030014170070304480300107901c09080a000041c140110a0360000c00141308201c141030031180d003851980c4c1003021112119019003003001002e420f04060400c00b080505200c1d00711486c94000035191b02c5080300c54100c5181d0064848030b00c0c80111440c070141e024070b030899408940400c80b00703e903c12403881d01c44a00030548031b80c210b0280303400015000d4081c480400c0c1029140ca01080040c0c0c0359034007220382c01a811100c4402d0794254074001401420303541340d1000e99a152100100b02e507a000050110918090303203405c2560340c0c403c1f00b000143c0c42080c001d10b503032071024072041050313500806040b40c00703010504080342001c3e110079104460340c000b156420340150701d910611036202e0544400b012400792813401e640c0d40c3c4039500200d582e111400520300320003c0002071400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 846354271 1250 846353021 846353029
    0xe03010e0f160e0f22120503042f04090507030c080321041109190603060209030705040e1504030c060c0302131203360b070b060102030304122006160f0903030815 71
    0x11700c00d65404080031004000760040289070b90411102152541003080c03411242c0700811040c010503a89034292240c4901c420b03800c3c4000350405000403500e0784511710b404000500c100d040d44020b031a803c030065031030b807110300d115540742e01c0000340040c2c000c154501400041045d0491484010005460280a0380c483c440c64641c110208210800c1c0203181c51808010442e445d0010000c808044040f0303103610380c5403c00c200803595102003000e1035501c254035043c20243c5124405521074000d013020624102c081d12181c0568161a68100c002640020760740c09084100c5100009014516826019815150b0f40901140b41e6020009003032070684400040c880c0000c00d212400c00f820b459407542081d5540a0728134150840700040f0f80d00c603061000206203500c004183d0f0b114541082860400341d200d5042665007103800d55030024501052000302da0000d40c10000d0707030301484401c1c0703150021a18030440104407800d205991000c01803258420000300c1e038080702064001040880b80744890610360001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 846355521 1250 846354271 846354331
    0x60d080a0c03120f0f062c06010e090c03250f0809010608010609140606120103031b020901060c260904020c0102040504060803070c090c0f0e03010e0f160e0f 69
    0x840d02c43d905180c0d91a4443c0d01c20303000300120b081080c0b02486441d132038400c8a08841c001c00280c8040c2450b180c4209581d0f1803c1a03259081801070404072601890500854480101214000200f001c000140412054183c0850380c0c0c0c0c20105140000040c0708180062090802d01a9481005003880108000c00341c298011801000600001c01040f527a8400000140c2080d404200c403030004000041c1c1c0f0b5052501c1280d000c903014180408880e03085039020344d90300000f18021b4901340305c0c003c400b000580391b41080e0b40c042c000b90f0b01e613600545428034110650306141618a007608003240f00e11008610040191851000c0c11900540c845590070415402401149d00203580142410720000c0c0d20200400100034031406401c03544907441c3ca40d01c0c20700540311240103200004148038410036201e449500143c0c0749a20080011419928603801585401d00300c038110641c640040d04403803400700912181400400c039084184216140c580c1c00c1c071b0800b203001081244180c900311001c0064210340030607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 846356771 1250 846355521 846355547
    0x512040501170a06181416050a050a03020f041d060103090b130f0803160207060c0c050d02041424180c0703110f070611150403050c03090406120b060d080a0c03 70
    0x20300c109035516460304102801c4094040c0307036445002c00c0818400e0141f1400310088401c00c1d100c851a101000204480c198001010a03041503400d100d4104c81c10070f090020401017034005613002d410034a6030486e09007294042c000c03505051030400b4040c0001c804600f540e07840020b400305c2ea44d0711592420140c10014040c5001090520004104403030f10020500045000b170aa41c01c40d01380c162034880c00d4482052500003c2c002105030b140c10002c0d860020940100d080c809003000c202c1c88141480244004002da0300d14400580170f124070100400b00c500c2607200307808219411032501c101191075030340103000904030811641001801809046c0500015002c0a10700c1e811140c81284062040e40c071800d503401403d00003500c141e03040d00070b51000242c6403819080036000c2c4020381c540c0c0c3e0702651554080200d804243c0018007a0b040c190ba80d80c82000000c001c2c010f15081c840d441454841048000103094a00c580f1380029044041814032050310303540c1030030741440308041e042e60400f0343d207000c04070b09 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 846358021 1250 846356771 846356789
    0x207060908040e010e28090203030d0506030105060f13021806040303090e0109050123270415140a090204020412150e0309061c0207020303040f030512040501170a06 72
    0x1140810001c0200003402241e000e00071415069890703030740008035240d00365800a644048504814a00489140c42a913602c8156100064130344141d4086070940c0c100b40e62275008542d680041000302d0a00780107241e40140f0460f01e08440801100c000b0302e14500400001080d1580410380e4800412030180030640180300900c11313a140c039682e15004105034054011f2014100c1070303a0000420804034080c80d81aa0340c0688060030409a01c0f05280c04c00c520380d801d5680c041c0f00c101540c6c050751008402ea40c40e415118a4271420b5103028281041071068450026484c2c510302843c921000c09610b104c1c1d500f00400f403001081a50450001801a0040e0f403c2410824444a41002041038050b410561010700c1d03e401c0c4007a0042d07884445e02d90042000280c0c0103031040000340700d0f03440c0b0646585210344900f0001420850306030042031031a000368200304046164480d0520038442c0801c0500640b40b10004028602428240000d101e1035207031201c9201000c0d084049114039401d0b41000707018104480b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 846359271 1250 846358021 846358031
    0xc0a0c08040915150216050405060a050a1427070507060b031006061b020f0120011d070905100b0702030f0105070e0120030906070519030c060b01020312011503020706 73
    0xc10350003d20140c52260149041c5081e1a10006500101e902e03508501c0421261a43c640361400740302c0035041c02009580d101641e0000401c0035a1513480f100080c00403800c4a96a03c585841070140359080a000d06d41981245841601c48000380c0038955406189840c1054a5455503c5d020020b440c010f403209a05001e80e07802c0d00a08082070340b01500311186039a072041565022319000e01040540fa0019401c0010703002d44000c00d501895405000c0b66050000d0b17075030448000080350071240208940d00b28400245813803d12104200102030242c02007000410150500050b04142150184280058000041003407015581d00340002080903081c90300038001c901d0250f4004102c10f20303045c1c503140410301c1c0503200616110751021424101001038015880c000c503c00c1042401d80010b5000c07074561281c82800c40118032080c45540406110ba1100c5c184401d0519190083c1d07600c0b41d907264115801800745c81008090140c03000d044071a44e0100240b00c0705511011000391080909c081d000c103040c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 846360521 1250 846359271 846359291
    0x90e070815270d03021b0304030f0201090b03010605160f0b19180f0b040c050d140d050c03030a0b01140a0c050601170a0602090f1f0f02060c0a0c080409 67
    0x34081503031160340c2040380c200c0551050001c0c2c0e05540c1c11051190800c2c2e110182680e1568000d900429249048000300040a41c4541600d46198403035001221460001d0561200b10350300300c10a100074094800c0131509542c10600018098042e0350200060041a9810102030264007081900c1a981299090a80d451b040d1070020161f080340000c2c1002920300008450185101003094016030b500008880c0410390751380340c003100c41c0d80140082c0c0c0c03088041c480028040d6904092422401e00c140c100404010412100c01d040c1014040c0c188240041040101d49002c40881120743c0b0041d103c10011f01c4411900040303a019400f83c6074801080070001d0608100c68000c2c10905490388074008580ca52381e00c5902001c3c0c840c031805010080c5610207100728000650b25005000821406420400841d44000025104001c4d8800d03603203a045924100e22995030b8001908804d800d100e000501003810540582e001d90701c02d122141c02080103c00c0207900f040780c4901264001c280703c0c2c000340140e11389 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 846361771 1250 846360521 846360553
    0xb0403080a020d0e01120b0604090c020a14060f060121020a030225020108070c060902030d0305070206070207050622050301050c0a1b030909052212110a0c090e0708 72
    0x1109803070143c81501d5a85201c14480e1403003110f0810107941d040c9444c0d0080004402800304031f80b0580d4072000a1202003002100c6120b184219912a07000300f180450354201404d00c0c0356070040708109600007404000303103803034458141a040602841c05002001582849403104080440450081400000d048210961503005090414000c0d5120f4000c0c6810303204460085150f00c0e0000c1c0852000700004801c28000c00380c68810038010f01c03000c222000107a0000e41008088101e10010941d103d040c040b240c3c0c1e0400c54540d100320036000401c10681094001000c500400e58003201260701e14113440620411000e191008007400340007401241410002015036800c0100001c00140c0300c191100804182c074100713001c8450b0103413524500b041c18082c21300040d101c0100601c404502ea4003540302621280d007002c80e0080d014810aa07440240601b000345005110481c20384260702c1aa001e10204900d07604070012111002000244907401162403810f0043c154448040c40c001c2c0c684c440520a5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 846363021 1250 846361771 846361777
    0x1c0b030f0715050c0c0409030207080a15050906060102100c02071e0501030e03130b090d02090a051f03031d041803050703020c01050c031b19081207020a0b04060b06040b040308 77
    0x24030300b141602000c0c85004102c82a00030048400b40c19400001441240d0409500103840c40b40a8415a4212604c1d81600f41c50464560002c40395140b01046280350f040f00c0b40309a07500310580c0300181c80070b4100500000c0d980c400d08800f17000000c2c0d07100b0040000500810400300288201c028601407040403d1100c50480b0083c4101404242420b4501c58000c80c08000c550111900028100750281802e0108001c4d800c50229582c0143c148042c145c00360b540d042c0c005206400c8140c010441e450490740e04541c41c00070080c3d48440448058007400020303042582ea5400b5080000141d0b601c114003c001006030405801808012450314084424907500400034044240281c0841c1d982102140044071903108100307454045400501c0b440803c0200e2081500c611540f00f4107d5055588000900010101c4014201c1d0314490000c3c014000e0030a42e4441e65000095001a051091498940740790045005100814007603958502c103005584140070b1b00c1c081c0c528000e0013512a5124078180503158 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 846364271 1250 846363021 846363029
    0x6090e0703150905070611010906110702040c090602030a1d060f1314150a170c130801050609040b130b0709090b0306270106080f0a150e031c0b030f07 66
    0x180b405900d00e2500d0154041d506010394094000d10b899807a04008442c1000c1007503e040041d52280700640100b10f450148103584907201600c242c0d55510b40c81008110340d00c070b8003e181805103012081082c140c011003035480c001054202400d0800030640714000d009005811a540002c1c0819189551016100030b02030151400702c03450181515010445003080c5003000042d440018516403000030f00c80b50026015404941c20f10716203024030701905c1412120112681c0b04a008086400b040d0f04100c075059000404141c4020406410410049407200038010000f903c5580b108002c59008000c0100e8540441c1c4c2040c890b04880c24464002070a00282d4070406814504210340c0345011300d80810f049004400e1443d4422025144e00d01610f110748030032001d01015561108009280d00050142c0d81010912001401c000000740c5800809402201c0170100c0c05460001001c1402000108440c18000d08044800b0740a10700090b803c00317800c2602220790035000d0300380c5492541d0301c0011207500b61 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 846365521 1250 846364271 846364283
    0x203031b0703021c1211011b21020c0303150d0c0b04030b09010b0d1b081609060609080c19171f0908030f040f0803040b0907050d030203031906090e0703 67
    0x410403031842603400b141c0d41c44d014000d84d401400d4600018010540c0f0760a40c851040040b9029846190f90858020044440340204040c0e11461080540d602103e0030380354440a0218141141c001055a407804004c1c00c0c0c8448090070003c0c00c50740e580e14003500d400194000302c03450055444036480102c40d00144401c070341c40815500803400c0b00406003c0c5100c0640064500201c103509030300e500082da00301c3c0c28000c040d88010345c0041030600c010b008158902d103803504200c12491400c050a81103403841e5002408000d001441404074620103e40c100914004030307540d00d15030000c80e0328000c2100141d4810540a143c081441a2114020491100460340c00021840921100d03802e1410317214681070040002e1070400c000342c0283c0788420b0b4903811078028030360046004100c1d0344201c5140d1055a09640d10313030f485001c12101a1082001c01c001d440c05440000003007601e40c0e0041c2d81c03400b0180184e041c00f86080b0300391030707202010b0b4001c40c0104181c56091204000b00d07031486860b16100d00080d159 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 846366771 1250 846365521 846365539
    0x4080106060503090d2d030b030c040b0a090f0605060a0c05100515210607180602030a120c0e030d050405090a02070f030c060b10081905090303070c0203031b070302 72
    0x2400b0300035810fa80c40741c0b6825000e41884403101e0f0040700c220064010410404441c10381480a02c015820481003604854800082c0c0d03044136030805182000d501d030054440d90805400310a140c4450140b1800c442c942417000c9075140040400d0005004079170006500031801240c22004075901c0101455502c2c0503406503502d0700980031400064850807141c11908001307040031504642441c950100c404402c00424044580400b200203003441c0041e5070703000c000b4803c001d03a16444145900c01500504032030006510b0b00100080c041d00d994128102d100800c6d640d0b81c4070340016402034017200c004078002420303144904d80142c400707000d136006801000d015048072000600240c0ca03620031182d01c1a00034a0780d8401c0c2c91595012580ea4601c07020854003951100b512020700d0311021a10800c4a2550319076000341d02e0200400e201000b02c85401806003420481400b0064070003108907038004503249031850001c40b040c004030b07203175114088201c8502e8120003211505c000001c82d00c00203680c400c44140b16 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 846368021 1250 846366771 846366779
    0xc060e0106060e10030b06040e1b03040b0c0c0a021518031f021e070809040e010c1d0303092e0903051f0e03070b1803180f030307150204080106 63
    0x2080315039602030003011640d040c3c449003081c0f8201001111400382840d000c00c48003111004104d464019a1100d9000c20080e000c0c04000b412810000d007031040c50810680c21854a80c0f600700c0e000801911940d110880024074030382e00d540920140e901141c014180d1484000812460b860302ea200e401007520703103200e01080400b1441c0c003203a5510603244416801502621810100c4000d52080400c00c002c0351120b41c54400b4111890081c0038414003541080d501d840c035610621040e9a0f480007400e480364941280200c2194100508580c4048811041c1034150396440103c3c0c5944141c0c903996074041804102e40c00361503e4000c800401040c00c0306407409002103040207641141050100500c075030000d610084035081881c0c82d0504010320b980300400c40c48204500d8604580c040202036070000e1058080002004003651f1032070406180d200214505144400326003658903924002501c9252044e01020081d5010000c3d07030303172058001085650340d6441c0c20405009501031722030321606500b4000001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 846369271 1250 846368021 846368023
    0x6121506080d02060402060a090509040c031707021c060b13020306040c09030302030a0e0d150b09060901210602070524060105040e0a0e0a150c0840020904030c060e 72
    0x1294582943e00100307515183c99007002640c0c0c00c03511342c2c0c07820000d4540c4001140d079105035545014034055494444840d003503003003c07049202d94a8540002c8d410130400707400161281c00d00e030a440b800541080b44d18092a241003401b07030120900c0c2503032120384058400e891164a90086020701011182003002140036501607032601c07064440940542c006009201c85640240f070300740440c810090001c800e0071070a9440c0110050104409004183d4500029401d810420101038021104407904405503143c020010b0800e00d550f00104507242c036111401041080701e405440f42a80e0000903503641100c0c9807015040c90400c05200c440061001c0c1c04100399501407800c990650705c1410009040d65507080b100c41c060102211a000d80c1d10070b1074214404a5804480c031140c0c0c071003000c0081075031491120018a407601c0600b28181070000100890812038800410740c0c5046c0c01e1058084e004429000c00f12030b1400c200402a400004120402041681c030040a6480d00c0c81250204000308542c1502 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 846370521 1250 846369271 846369283
    0x31b070e090319030b06030a02040306151a070f080403050c01120203130b04020d02030d110c012a03180b0703320c160e01090e061302130612150608 65
    0x26038210b030010050911816004145144901d1560070042943c410340c1e00480c00c50f0340304481010311140d01140500070000b5600841410380218903444140d64103014424840102d010700b00f407088000000c4d0a8200a0740d200040a49500981c14a4465a590408503207900710021000e000441141010101400d83e1081e48d01a01e8030078180b03039404406940d4400c00c01d10190040e81e000011030030440c010380e010040030700c0400c1c240da225071010060340c405a19150030321040074144030780010002c1100f48800004d000d20742102549003d1106142801d54140c100141400003080319a1001b0032041c145400074030342c1c1486507031203a0204030148082042412002c804490500d198000c656050013030002401d0800e941c2425034141d100048080d0350741d0f10480d4000d00a040614004212510484c826842d0300d1040c031000e010540342021090611905202000f0310860b8440c504000309051548502c015103490b2040304440280c606052a10550300e83e40c200c40103040a10102d8003120100c0c0b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 846371771 1250 846370521 846370531
    0x1030e0307170307111c081308190c020d03050306030c0109080d142a120a050a080a06270f06060207050409052b03060f0506040303031805031b070e 65
    0x20001c0c0d8148100c18035150f0028049500300240342e03a000840c1035040c0040d003502080011400c5030a16078840c0980440b00c010002107490114402c010081141a000c81ea040910300b100799040c402c80200a442c00c626202020f03400c600c0882c154801c2580000c021401848102d00310703602c40e82140e0044400c0c3c480350040108a4120342c1d160440203000342042d81c600c07482c0c408000e0509951080c480c1c841c029022401f4420500740011201060701401000300103c1c0100c401447d00da10300c4405080e61245114140401c1181c4000440c214550741c09030b40a0200c400c001400c00b030b2040e45c030800c0350652980e1000c0091a0001240c02c82d02140b1841d02200c9140d00500021032603c070421008010b0301d03105441c20b000d903419209a4600207c04485005003100c40f07203c80300420b0300300404994482e000554071340c0803010284040c0d03450300e054400f266814070b00415160f07041020141c5104503000f00510070711000c640351040c040380b09001065410380c802181d0f51641d0b04d464003c6076000c1528 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 846373021 1250 846371771 846371783
    0x206100f03020607030905042301084201090515010903020f0409020406120803040510020702090408310501020d1809110c060a0b09060d03020c010807020c13020901030e0307 76
    0x1400c000500f03042002e84041802401d0407107910f0399900204040d9102a440c94402d0544903402481c45201c0c0340d28540548002402018182c4a030151755540301d4070844a082407480d4900030b002001424580601240269524003100c4d50f075881862000c1d04040e00c1c001101050090703522043d501c00d901c110100c903002000320307541c09003410601000f4042d910044c1d800c640c40350000319411001c1e0b540440c40520510959580f8502410003070b0070b200341102c850050030f00401180000d6540c00104a40007a00850600d640b139586508052044441902c2042c0c01c0d07482402e211030586201d40c04600b1910283c00b50381040d129a042104c5030301002e8410600700026031410702a115555224000c00d940e901030107403500c40321091040c0382090845020410945403910070141c4c0c148500b034690803032804c0c0ca01c03500602e51603034041c0d1102401a0207130304200569001458091003080301408045020b8000b000c6124550800c0d800395014540340e40c0464140f418501d00b240d400412600040e030440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 846374271 1250 846373021 846373049
    0x31305211201061b14010603210212041206020d02070f120e10080c0304020d0b1f1202010206040b150d0f051b060d02181e120c01021b0d080415020610 66
    0x17a4454404012081d4001d1983d0350355540880003448040740d003083c00c1403540c00c0055031400004001d240582505412090510601080142c8590402c05800c0c241e4084000b50f190340710715040400a01a441003d8051001407010200f840703100010180701401603614081c07100b4021f070900c42000384000c0b03840002007280300043d0302c210901c03028640081c4010101e817610002c41e00c0c1d400410380162030020020000c00c07200c00c0c1000d010a02d80303006010700000766480e1581a00082d40301c90700240017812204240b400110307001d5003000e00f0440c005009107181c5480d000703400c100300d500380000400c0300e070b610800c030440c002c0c80e0f0042a80d418a00c8020081440c01005034a0080a5003103200750f00082ca0500034048a56940c4180d0110440c0001104200b858005c90410054038450340344c40c00c058104180d40c0355166030201c0c00105120381d41d4840211541c8034008510240c3d501138004e40b060a01140c04600d954000e49501042c450640c00c82d8000c1d207581144502d020564803070440155420 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 846375521 1250 846374271 846374273
    0x705150603150402061306110120030403080415060801090215030402031f1b1115040203210906040e04230307060905011e06050a08030906031305211201061b 69
    0xb4014541c494809400181825030410303154117800c11070340262020030b4880c9120000ca01d403d10030b124500342c400c040b54042c40c0c04481102c11502c0301802c09010841e550001800340b1206034222283d8517074920003001a1a900d10440e030081141c0e280c128810701007000308010340b1492909a9001da40c0041c00f43c00f07030140b07014400700e2034a00c1c600c1c006501900e8240709481400681c0300c40984280310746503146e0054082d46d200307040100d43c000040002092201340b00250301d000940c000d1540503c1103221588140100001d9039008450159038450000039020400b5801e40c2034141c003075845405000602000308451003211a29149207840ba544103000c2400811a80c1d0488407089004070000100c81c003104010400012880101c00403941d01c0c0e007020450341c18020f80340030003805008059400c01c003424002030300a10000e4403511031010008441c40034042d007800504e0301468071030310403111481035050249594000c07801c2890150501800015860f00500305130700e17515030104030b0410b0401e42e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 846376771 1250 846375521 846375553
    0x50c010f170a0b0102340506031501050c07030c0f1e121704051906120b0307090b03030f0307080f0a0b010203090108100f0b040e1f0e04170409020705150603 69
    0x701083c00e045100301d0136480002c080610b41c20300107058100c0c00050381c407500c40c02e11401c50307945c0c1c0c019401032800700b0030003103082ca01c2c0c1503044400400346411680c59201c409807518005858102a082000030140084c005400140400442d14140c1c030203208070356114000901c00036548035416070020071140180000b07010003c8150180c01c2c7c07805003070030300f0b890354042190010b00ca800c0240000d1414014446075801c195252542da005290521035031382080082901c2d00301c0c9205201805460b114103445540d024400c2c0c80303000955004c1e990b22803800d0800101000810349941040b4015440030401550150145d13400031241030300118981b440300c400456846a004010000101d084036003c24000000b255200003014040559621070b42003c0e20408040d20181c041051a880136100a411050483c03000e0220b48401c0c3d00300300c0554030750400c444a070b50f00c04000c0b13080500c0000d011442c51b44036405090654011012910f522130044250004064141d401c0350749a8068aa006450301d8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 846378021 1250 846376771 846376781
    0x24130b090405010b0f0708090103060306020a08180105150d052e0c02240402130c0e0a0f05090712020f160b09060709090f140c1e04030c060e0f030a050c010f170a 71
    0x1104ac0340010313415980f80c440707004981040c540900041e00e0f21041c4207001a402203408010a43c3c1d1008215900313005444c028007505041c0824021400f030440b99061000600c41c00c0c54501c000f00c51030b00d40c40d13006004c91800301e6903146040d40c40d501d040b90201c01544001b0b0342030129200000c08000007481d410040d040200c0040040341d214414bc0f1182c45100001c1c061074855440c40d4854444420300203040140983d025044481c440c49500c3c41040280d0340d0310141a04021039040208a14240d01c0d030703003806031040c000e03207484034040052001c0c90079891103400001180107180c00348041e1100030307a103a11580c05640f0b41c0009002c1c0780f020300540010758002051100d1043c40098084903080707080f6129202121080c00079071005c2884110304490454a0b40000b0000d10b9461402c2d08507a600300515001e070050310104180d1040c1504652660006004400d2006040b01c01c3c51209241050751960525840360024841d90740c400a01c5000d440d82410400400c1309031a0540d80304104035000b04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 846379271 1250 846378021 846378037
    0x9060f0c121f140a050607020f010e030304030b3c01060f0207121b0b12040b04020a05060c0a050c0109050a0509040f0f0b06010e01080624130b090405010b0f0708 71
    0x24280d076001000b40c1c48030601c00c00200440303428400e03015021020000200040c1d170200b802004200410001640c2d600c401d411245024206400201c500b1070102c0c0c40c41c01150402000c0810220902052600114019000c20004030140012102c0c010105040001d02188001c0c41e07a000f10050152038050300e0403e01c2c84010380704550146549245a4101900f0001c081c2c0741410702d4080b11032582a1004228007800e140310045117004001c003040050b07480d000f0400351221071010041411580d4072600351008007801130003036490710340c40a80107460381d55412048510384030394100644554002c0c0e0030881200c0b0010f0030f07000120700e4602800344c00400208110340342900e1940803000180c551241190072406102218660300d0b2220024085c508000d01503814007004400300711031603075404500b40d08018403040600b828101071b0302d81e09080c01004a800f04015544101151511415010b0003200380e046400340000e90385c1d6212100c061240400210b0382e80c02c1080b540b8042403070340000b8a407503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 846380521 1250 846379271 846379291
    0x90f01030b1c14010f0203041205070f06200316030e01150905181603031202071106070302072105012307211b031515032c0609060f0c12 60
    0x9443e41c000780f800c403110703c600c510b01640c4c0072017070009000c0c4400000311002c110341030a919020140d229030441c0c07900054010b00b0240c56641d02e04900140100c00200b44000c540c1003a20313401d1400c5c68813944241d0003120070009180c00903080e50614140030f2081079254401d1703052011410000c0d900050440108065071001c40c0141030120310b40304210380c1400c1e101a00340c0c1454a82140740062030070703e60003c0c802205005024080c04070300f0704440c0031700c49082220056034444031131070141d0400060f60311480d00034031114401003607010255501458588124000c00003103041405014117185c00301c001c44041030101e0001b0b1081c034081d8403814141c41041c51480c0042e02200d200e00305541c50341540c0c46e150718902d166541507580500898101410b189921414542007050228244084c04001e808040d291200d0f035041b1000b400c400ca84642c400c1801c811844c4c0c40301002039a81d00162403c0282d8416080007403c5c0906500d1600e008440c40c0494614180450030095500b600190241c4c2c50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 846381771 1250 846380521 846380543
    0x41b050f040f030f0b090706090b0c390612070c140d05070b06060c21130b04050306071103271f0806041401091104030b0a02090f01030b1c 61
    0x111000c45030b80c03100218403580da882c0e220116450134800c0d0364809040f0a6103544004828001503403c0102442600c0c80300800544034440100e4003441c0604003d403011610701c000c0c5401c03061405080a030314400c010326030b0183c1460390f440c041c0170072841000c05242c0082042e5001c12107151140e440420954000c040f1111120410110b49050220b00c50300480801c01c0060358404000d108002940d01c640304172211414203000c000c215886104a80b20341014a601c001c1101d1184907203004d4958012b55019040100381d11100c441950b640503000380d40c401e104e03250028903030b6481005200e007000c1504001e90306242608060a5404001c1101d030103841900c101481060380703542d4000c4585c4401e103100708020059048001d0140360005d480c81d8001c1d41003100810164092613001811036074507402c009401c045602a0041e140100c2e00000c1c078a90904040c812030400e190040c1039040390803514401c040d009040107400f21000c1c003080641060007540d152100f422002c1300c14a07540c0c0142e0943c02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 846383021 1250 846381771 846381779
    0xb1e060f041d090c040501030f0311031306120516090e100e040501020307090608011d092407080606071104020307140c390904060f0c0518041b050f04 66
    0x245462060110106881400b41040050f050070031682c420501e058608002e00e50460301d4120610101c1e0002a043c441c868603448400071041003150000300c0005100400582c9030a802401c40c259186d103d6402070400d404241505000c031103040c1200110344400441900e00065012500320051034a100608850400604000400d42e03c0b071241c2d00c1030000598902c1c06c40409000d05030240c206204022000c0010300034046d441c1e40020144203980a010301c16548c44200d0383c50522035000035100d240d10b04d4141e100e65401080c4c0b00b4041e5640b5100e030241c0d5543c40d410300446008807403003e801c070040d920103007006040a90003560043c0782c0d458103071803444079000d40c03401316031110f08180025409000c041e4110095880c2c0c410282c1e5503c170001508501e22845400d0000b1100300d4503100c3c508400104080001c1984801d2400281010600048000d02c2010340310b4ac011400d262011100e0654a144a14040c0308079610b07441d25881102d051031000c9012035194000400c001d80402e02004082 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 846384271 1250 846383021 846383039
    0x1709240c040302011b080a0323040302031c11040f03121b0b04030522061103031005040b1f08010f05041b03110d050406020a030e15010e0402061b010f0b1e060f04 71
    0x800700c5a8140c40210303441c0000c601e0200b400c485031807043e200f140c039401803100103038cc00f0040361400e400904c10015980d00151024009150700c04000c40540b80009001810009814410b41204d00800681085140f510740c01c0e0b0321825007403500d048950003500d481002032081d03000c80f5042406460010b04160030303a03c2130506642a0040c001680e04500c100b0082e656103e0412200b80340d0540c00307103046003007580c1d61078180459402000c0c4220345030702d00b10045e42c40380d004405190b02c900c022003061050705440a4a820310a0050030b601c4125014081002e007454080e54982c403000d1a040f0380310203201c00089006010120700420f03d0a410042c100c001d28507402403a0165020707a000590341c0390180c8024044414005040d941d0380c0100c8028015103015007100c0c1e0441d000308500030302e6a50381c0c0c8000381142c46021008403503c2042460500b01c2441588a9800722000403801c003c0e810001d4100000d6000030400c000450640981c1111141401d4003d0996121180100c50400f51280845 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 846385521 1250 846384271 846384277
    0x7110303071421180622240804170d0f0501091d03030103200405040609020a06050408190206070618030305060f0a030609031709240c040302011b08 65
    0x703030b41c00d14942481c1900220180700184840480152451851404000c002d000e80104a9400f649900d40c10102c03030981c8504085441041c0314502444000d203030452203083c00c40003805603149200444064a03035407030031710620840c84002c90310303401000d0b0b4070b6980d80b0898418004502c45983c2c0c081c0542061920a0301814600030425403000c20b003503050003070300400c4550300801c5101644d8100749140e883d002c0401124152070f0882c1d450140b404841004648148400d1582504186044104001e0010036071140d03400f54801c0303c103840c000d5a90781c4100c400340a14054940c003034211140040321102e0028a0410045c4054100740c14010700b40c507228101c41c9070500d100146034124468204159040c460b60b45d004100f22030b0341d030100e02e01d00301103012619103010050001da52000a9001e01d4003582c1480d03030000110031403078000d00c0c0205405448070324011030f12a03e41010329284285071921104144602c40400e152403c080c5103400440d0b8004001050841003078a05861901040540c0c0007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 846386771 1250 846385521 846385523
    0x50603040b1b160b061e060309160b04060e030c030303060d150c050301080607050406020601092a09180b030c0d02010903080a2a20130216020a0501090305030f0711030307 75
    0x141043c030408600b40004040c400810152242d05295100f2280808950b59600ea12000b660b4503522940c4886071a0f02e0180c02410312018003880a0000902c00c50a0006000740e911560314a070303221903000107156a400d0301240899141d0418030001d602400d15100b81c0503014002d00729034003e40d55404d424030440e13111100401c0043c40000060020100820840303070006590b14003140342c40d2520f44001d48469041c0950b052040e20760300e0408005840550741a8481000c8030120780405181e003024081070b0851203410040292486c9a081141e020f10808221910150140000c20b0380300b0108503005600210880c14040301040100206441c0c074043c00c00034106864000180d11411008440c40740318032000c402c00e41c242c80505001030916004100c1c4000304a1281a0710b0a0342c500081131007140078032025410f48003140c0e0b0403a1a03132184901c82400d00070364900c580b0603154001141d1820a038000940954002c110084220060000415030f050003000132000081e0007000003030441c0c0c42400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 846388021 1250 846386771 846386797
    0x40b311d010f061e0303052803050105150c07030602071a010905060108010f06120f11070302011d0102040f03030e030106090c0210050702010c090618150c0b0702010204050603040b1b 80
    0x182c110701e5a0a00c1140c0c05009100d16400c1540e0480300360346a068804c2c0001000c100300442d155101201901c113002d4008803c4000740300310300e66a54001c005210900c5550320480100700c007008251034040c1203c4096041d100542411800c544603000654088201280c141c041813420241501c2c00701c40060103070103a410081841e00b032903400107002c0c40c4183c1198082e00c5111200b0440c668214110b400c022100d0500810680650170180c4002e1040380e00000c030242c2c0002d40b42d0304050b4198820000310061200b20403d4280d486822401c1307015034000d44840450400050005c00d008030400ca5001c10700600100301c0f60b0701c6d16084003e4900c64003201d00075a000c0380521040400c0ba00a06074032507180d1000304081507070b41900400d402028030888083c80800c4a800701010000c00c001009070000b8840468000c0c403030307800100040c4518000f665000040341c01310340c4032881802201c00b181d200903c03032811901c0ba034680218441e030181040c0c85c9030ba2244861680c642c243c002508820711222 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 846389271 1250 846388021 846388031
    0xb04020a02031e1e1e0f301005011404030209040b040c030804030c05121513050a0b0916060c0b070809030702090403050a200a0f0c080708010902040b311d01 69
    0x4000d103005d4544024100681c550140280701c140c60545007074500e003004034002c100c1503046098034000300d11300d580d400119160150040181c40700003500321608580082c0d132000d44008160b88003200340d0040380002580606010045000b00394038920240d0002c0c060382c410090b9aa580e41d80c09880e5002d94412512244280020403903072906000d0820503c0100303002d800b4500c140c107811004150014401304041d00d180c005003043c0141081424802540000b0016607800c14592055898082030211581c08200120101c1d20b80d01c61103030304e450180e0004402c0b00f0758503a2030081c0d0316010001c4c2441120322051113044090383d103400c40d5a000e203000740c031101c2c0e0300c00800340300910201064003d2181d186e010581592185000a000c1c0f007210b07004440b81007000c81030315001c050501154031188103841068004964200f0662180c800c40340308031001c0000154a0041c1b12010300c04044903401c440d0174500215810145140d8180300a108410000e0b225130004bc8851841c111060300c802103a540d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 846390521 1250 846389271 846389287
    0x10b03180d080105150c150a0b0618090c0a0e040c0c0b071d030d080411060c0f160e090c041505030106030305120f060303160f0c09050702010b04020a02031e1e 70
    0x2148010310342095440003541b40c18280c3c0740716035980081140c1d04105926140004180705440d6000c1c08500a004204540d52050200d8202c0103041c0101c00610420350311020a00c2c5a0100088810801c01911382c00788141189042200030840514090103000d030001032080050344043d1018842ca030641c41d84113008a0340840558280c180a1540e8000d5016801c1482059004802143c3c866806440b218071001000301041c01801070101c0f0341d038203102d850b603c640450300203d1501d15100501ba580d40c0c112b641d4880ba0f0849100990782d0480c1c58015220704403681c1001c1d0414100c4140d060223034080789640d403020900b1215036078810740001e5408a4a40068216a0107080d04580103200408050403c400000e40b01d2181880c0b00d5071000c107500380c070030401202822911050f82c0180010850580d0703414004003a00040f140040154601000002c0c04c0c0307440d2099540141e2541e0045041009140545036030701da1411905400d89801d02c1500c00c4425a808a800107100203100b407502c981c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 846391771 1250 846390521 846390529
    0x60d0e1e0316140601061110090b070809070b031006020708070609050d06150b0c0f06091f020d0603030c140604020f04020d1803180506030f010b03180d080105 70
    0x921940008a2141845003014040c8000151210810803489150202d2600d150041c51a0f0b0402d42076016802440700004815400c485003800d500840f41c00c0c2d40413207020100c01c00440b0300b12a00180115504400b08030f6861050007215030000150080f90011511a520081c00317400460300c5c0c0200c00002c40f814000e907681800380100600f01e45000f020342c2820306074094000309943c000c03c0c0c05144c810900c1002d22000c2c4d0800140c607600c00e440241595202c000c221807641c04940c1185c0144a201210301400400043c46c1e8417842c90035002d040d00c52211040031717000d0f0944c00a4510115024891910003c0d224800c01c00154443d4640180c02002454840d400385407442c0c000b415034014a0800015889098400c88440700444005079150004100c0d01e00610309040101004c04940e0011000c1581154008600b044400060321260381e0f5202000603030710003100d036000d8844144004101e0480d644000d103410002101944078601e4210000300c0c54000c004441e880000c400300010821410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 846393021 1250 846391771 846391783
    0x30604050d11010501080c060304170f0a1e120203071101140708091b01051303061a121f02090d02100c0b010905010b09010e0103020d0e01050a060503011404031d060d0e 74
    0x2e40320b0020300c90341d803610302280d403200b00301151140508000000070301084801041031403400c8081141e41d440300441c0c1410141d0350010000c5130040f42550114030800401800c003102c5c030881940c0d0380d148920b401c0c81801c000c0c3d00047c0180c01403120450811513515420701079004000d5802e004540c280ca08200002c08050b0050a030601e02e400c1200e4a002c1c0f61006186501d030000203007085660f0b5510f80c850307900540340d903074005071016143c100c1c481c200d00c00c0c00e010307a05c0703440e001c0381c030707401031416815110381c4441901c0c07144c08080440381c0002005086580180c0b04003800240760001a06940d000300b914104420800c200140c0c04017005010000b0811019015141d00401044158145400d10302c02d84944181c6c503050100d0380318200f40c160b109030119502c0f11851b80040c0000e60390041d24601900d030a84022070814102540481d050030144501030030542901d03e400f4103511151419988151070030302240c4407440629603480c1c542ca030100140a5038004010010782c8440101d0141d0800c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 846394271 1250 846393021 846393047
    0x12604050c0d0b04240606080a0c050c070509060d02060403030f0f032013091a091b120408090301050f0a050f010b1801090812030106120e0303011203030902030604050d 74
    0x190801d00c2c07078086000343d030ba110390069001d4600011610711049404583c500c401d0b10724011420030001090542d4001c5107035004241c2e180301132101100000041e0703014082c0d0780b41020b0582c0410410840b900d44801e441ba0484000b420311b41d203061044e00032544a610980055003c10000284101410f51000100c00c0240044c84d04101203102004031701120001c5449124180d2030100d002401d110f1154035050007032414140400540241a0900301d0340e110800c3c510340b0070641c0b1030024200f14000c0030880e4a466061011500c0d041c00382e14213000000000c0c0050310010f00c2404490341c1030710b09200d01d6001342c890b00646581c51414100000a80300c2c0200388010003265600100450b48011003643c80c41100030342c01c810300710340c080c0c01250040042e81c010a040c0c030561184e6500b041a810081d410390700c4c40e030b480c10b03a496111070741641900c0326821100025070081004001d41c80c55000f4200703259100e8030b070220304108203800017842c1040940d81500c1580100200000b100c0d017164002c0c03000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 846395521 1250 846394271 846394279
    0x3220b0a02031e0c0d0e010b0a0f08010606081b0a050408031201150e010c03030c02160906080c030f03040b07062a08060d02240708040603050a0b040204140f012604050c 74
    0x2526050000c0ca61301d020ba007002003600340c0c032003084000d010400e4203c14160300300a03002c0d0b6107450b80c600001c10316004034410b48850f540f0f07102d0f0100d48d4034131a4440c98406c068403248a0240ca000000080e45603120445d482c0030803a003480003040d007020034001012036200944a1080340c0d414210301802c001200c241c0c000c20300a003030f0207101d510790b0049500610141c00d403c00242d13811254105a0402c82551200305140c240c0700f9021904c2001980700d003003075074003c01c21a480340c0081801e2541d5071450001140880e4000d1204114110b400e5000304206841241c010502c0940c0c011841c6082c04030a0003000807024ad01440c42d04030358459040390340301070b0884401e02003080d69008121101d1b2030b0022080714029074060b5030040d24a000c1214842644030804036601d555860004004000540304044440e080500a15042c5494001c0c3d03425100c8402d14840c08198410030041d544a41180305414070194116070325541c17080040d6500810102c2e22450003e141502d00f06e4106031a01c02d0251103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 846396771 1250 846395521 846395581
    0xf0b09010e090a0f0f020d05070e06030f0c040e01030503070512030c12340305100e1501020c03030c07050a0509040b070c0501090c120b06010306030803220b0a0203 72
    0x26a800403200756055000e4a6118458407402410b40c094508200009161401c0c06030646502c1107641c000c002904004c10300300116140d04408031000604d10700f9441e0700c10400d00101d248030071485001ca800449400005d80b5007941c0b421b10044241d02684181d400350004a0550180b020070f00040562001e5248810728624001c4440b50b628003800400b5640d8a084000007601d10108200c2e1000c2d62041400384a105040541c0030340803204c0d00c0220000007401d00e070110740038200003240001600c40d0203086072615619080c40f41616041c10301c526045100780344140e1100d44041c40148002d40c095005070000c181404180840d10110b0361000340075400c4541008041015040e2007604842a454440352400c034a08009000d8070030042c1c013510142420300c0000c5c54505c0c80c0203d81c102071044024500716075403000190704882981c4400350040c40c04100140c4101d01c02c0071950300380f4110748081d0582c5007064580e00812007040320094005507000081c009801c4007250618100128500c0720a6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 846398021 1250 846396771 846396787
    0x506040b0c21040318061e1209060b0a12030c0209041a0a0204090c020a0c06080c0708030c0a081320061303051e0a1a040309090e07231e032103010f0b 66
    0x4030300a51855550010103042030b5800c562207508d00190440c0d1020080c820140316052510040c440140aa40b2400b82c040000980c81c03148816032404a400d5102c404948000360207110400c94014801ca40c0e0321015000541040f510b80741942c00f840c405500107803a04c0c1040100c9049800c0d0729007441c291344c008c4c007400c1d00044109289105444807403800304040d4a9224042c0c4c02802004801408808048200700c1c88515540c0500320760036a41d070f1041019101d0761002d200030300035448080c000402d180e258806048881c0000400440c000d0001341ca000d4a0480d0a220100c0c640c2049a05800ca040c3c2e5811880492846842c0c641410026220418603581c0d4003040460107403203502e004c812132000a05250041e00c20340300070324810ba0140b00d10030b64542d400b034407225940a01241c3c0343c4420414031802e540b800d5000e1010202808240b040f0400c41400d011010b21b2402c201e506100c1c05030f02401c0c244c0028032070306c410448100c6e442d85950412130072000103020b03604101c51749101804068 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 846399271 1250 846398021 846398027
    0x6050603010621061103090c1e3a060b0f030c1f02011506021606080c0d0e01020f070c080c011e08060f0306070504060306120506040b0c2104031806 65
    0x183c48801c0481c1a0052445601c2e1a00241440d180180320401001c802c10034040ea0100358001686030032198440c52818003488406c6031500950b0300b9070407084c400d178103e5407013030764002c0d5100220344100c1090313424542c50389400c02000341240494125446622035000c03410101141440000110042c24039800c00c0c0340407442d206100c800d12080c400741d2030310f400d003458000e40c00b101882d08892100010b40d0748404019645800c0c0032000d919580350040c2c0003a18a00c030744001c900130264030038054604401c100012024011b61042d06000c0c0d5800c119619100da82200207040380303072045002580c3e00380b43c100d00c2414039038100c81e1623040c00a414202003d0000071088040c2d600080c1c1041ca4190711110080f038030290021004540510031601484840b5401c10080c00441c7e03036a41d01885059202c2d907031640c2035000200010100d0340440c0200d00060b805100280d0700c014031060090070a4a4001e6520144070120030103076800c0e00139414801816031264498031039402c00d148022486240080c01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 846400521 1250 846399271 846399299
    0x5180d080708031315020319060305030f073212030613090f0b0c03060a0614160f080703090e2a0309070b04150e0a030f022416060506030106 62
    0x30401a40000021310700483d0b252000c0100e500002c3c1220340c01044450140258815600303d00c100c0c3d4050502039211000740901c0e401e1340c1e1b00c100a1410441e16505840103504114800c9030b01d171800018201c202040044a940c0004c0f803003209205019440440b641858180060000e01880400810215445440482c0e1156180c8940010714104505020028100d491401441c1d19a90f00c18400e10412010181d8040c007822500c0281d07240e40c1d82825103c202451245e21020311090151964100100011040e81c0e400344e59049103018240c1da40303000b550311400044020400c0c5900030f0110360b540c45900c42e44680c61900400386480b000024011103101090251030030800000001c40c1300c0024001c00e0010103c601000f0384640d09c5803186ea010f0026031a0080004859825105d150314000c0101000c980e0001250482a85580c0910940b00c41041c02c07140302c03030a8802041032940070388008005082c84040b80f005100268685841641d102524042c42681024030900c9025114501 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 846401771 1250 846400521 846400523
    0xf15060316182309010e0c150a09170d021e031806090d030306031110051e040b12070908011a12011401030804080d1403010504090317010605180d0807 66
    0x24a1980b82c0040c2101014044034420510075980014903181e012080b400703641c2c0601c900e03000910050032041150b07035407010f000890782d078070002c41e1514103240454900182910b155030701d000c54461703451305002a6a800590301e0350039241d1000c45001c2e049075050000d10108000000c0d985442110b80403caa0340380550039201e000c01000a40c4640340e5a90001142c28900d40030744180244102401c018004112900c0203580192100743c1440b403d01d004015544034095036154203041038102002d10740c6000b4203550b0300300000b030300301301c00b03c1d8032410f160180041c2190101c0100480c07801220040285c20741d54080b140503810503000300030204a0302c5140d070b108441501c101d02c0d0030406410311405015001c02c04006110f52100102c00d11248400500c03da03018001200d401078000030301100d0311007041c07880150542042c070040c80b05203420b0b0440000140a8603040c400031b000340c070b14a80b10314404ea05c00c1c00444e04c005a0600103215880c400c0c840700004482c0c4527040202034482618a00c10070710 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 846402877 1106 846401771 846401789
    0xa02010f120621030201051b042306030f01090b0d080906090d0818100207080a11030a12080a180807030e030f030a1206050f01020c12030405030f15060316 68
    0x2104480c1c4002e1084c229180c245030000300d0909907919540e000ac000b02e00004081d0716030340c0301d001e1740c003076886035002c42010b5141c0182c90701200c1a1400c11405603c40070864000300790024107032030504109a65843d9912580e01c005400c4080c544001000c80c84081340f0f103000c284803101483c14900b41608c658075605e19002c0140c0c3d5413440b510491046030700140b03040c00001c20f440c0040c5504000513040781c011010680d201503800046000d03610020b80d00000b0000d81c510076010710300a000c1c0408250031a1401900d4051342403049840140901c0b120200318029038404010700c213440740c00041038903161040c44100415045c00e00003803090003403c0c1040480d052800d0404a00351540507001070110416040c144606650090b40303900742400103120010303043d142031000d41001d40b01c1c4805011249500348154124820107021280254450074041c0c0b62103a41d0b1100d0b03804e4403840a = true := by decide +kernel

theorem cover : BRFrame.Cov 846223021 846402877 := by
  have h0 := BRFrame.cov_init 846223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 846223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 846223021 ≤ n) (h2 : n < 846402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
