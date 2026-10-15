-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5441
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:52:38.429361+00:00
-- url     : https://prove2.me/submissions/015d4f9f-a9b9-44a3-806d-fb73d69152ad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 978417266 ≤ n < 978597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 978418516 1250 978417266 978417287
    0x20f060c0709020d0b0a03050610120506070302030403171303090f080705040906060503030301090e0c0117180118031106150d0f0f0606090930030e070302030a030915 73
    0x65940048001c109074140e030760013020a41a0a580011074134042400180d2803401c1b9803007920558002810f220800402c20b034803038020f02c110000c020400110740d0303483e80c035601300a121070185640407001800b4140255030100b071030103603660040c2d210301e46680d10013070362460308005500040310301d000404c90310b0480802c0d5081d240114014840c42d450081000045c010864046801d42d898102c001203035141040918041c240349100480d9030940f03803ea40b8035080512115034100400308403a1010060568002354009604501110f070042d114182c1d80e0150500d0110190010700200801080c10782c0085012030150850342695510349444c0c600410000003903500b25880704d1068509030004080d5500c4071040c1c0d10500490440c9521a1101801c5800315409410702945401c01d260070844c10940000c100340d40d08107800c911102045409954000c01824001410341c0c0310b5003511124020010180203640c02811121100304500d80102240d03114800c52940c0000c00a0840c036850040c0a082c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 978419766 1250 978418516 978418537
    0x1f051e0903071215050c0a031109010c3c03080a0902060901080702070e010b1c0501030c090b010c0503210907060215180a0b091605060f030705190309020f06 69
    0x5a00f410011020000c20240c0d4003180c80705820004091342c1c4d80d0b00e0140c01d11540121501503200c640c41100503055074180001d4201042c41001301c03c0d0242c0c1c0210103140d110740c200c1001c1c001e010008a0820b05404201001c0e5181d680c3c3d90550700c081102454580d00d210710a680f2503440b078403050b01e00000c1d5644600c0007503214800f80510b02d40c95100700301c4181e101d0220320440703140c2907842c81800f007450802e0704041c10324500042d05000b03514030504035100d10040b1040400c42589140c0b43c4110380021805044609516040c80c180140e2040803110364003900141603995800003400401034406940c401d00810600d9600091142c04011881d00101c070110f402a0000c00d101c500080708005008000814500035040d500512030410030900c101e00d4803588104a0500b4080003092070140c0b6480041241c0480f03032018803440d25400159040145583d50300b40d00c0352070b02d40d4280c48074000e50026140762030b4601828000150300d074104060f80b074006e175000001c50102c02e0a1085a10030166442c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 978421016 1250 978419766 978419773
    0x51e04060b040b0321280206040308010618031e02130509010506030708030f030a181b210b0403170a0207060f0b0d020f19030b091603201f051e0903 65
    0x710104d60880000c00d044803440f05840c058151b82d041c1d00c118961006040e80041e0310250401c400c1540000029000d00705604165680f9001426172040746211408001c1490312114042450150342c10140c01100c0d5004001032600200c3d00c1102001380740490f000e030120760901000ca400c9003808148a41a20098400303075240c1030140040911a600c01741119680c0e40d9030f00401a42c3c81a0080402c01c55403180d1411107607413010310151960702182d40c00c54070340140c0c2c25204010390520254041d400e0750384040401015039407030030107441d1074411141c1000007040b01420040b00c0701983e03000b4000c2d03a1240340c08001c0d1100c80ca00040484481d11800c80e00003c0c044034510162802c408c684010290040542251604040b2048405034a41c0e004450a1145d1002c0c441d1420061107102822440101c0d41c01c00c0c245940c130799003000c103901c044e40078440301c0c0c00c1c0031045070740c6034000054400721007854000417a80746000c0041240d4003079025030310100900140c5011a4a03003908442c1a01ca000303004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 978422266 1250 978421016 978421063
    0x207020310021806070b0402030f1606030906060506160312110d2c01090309080c0105040b1605030f18040501080c01031d06070c0b0a0204080d03051e04060b040b03 72
    0x10740300a5001c1d0880a9510202d0101d1440e9691400001c02c1c04a05c43c00f009580382c01c4c01d2050520f485d140103402005504140c0040e0070b00308503045d0350f00c2203c0541c03901280ca414603040200042c01140c1041d6040040010403014401003501d41c010854801c1e5514030813104501c40e80e03021103080c60940100130740c00b00300d610103044440c0c02540310850307031118282821510b1101007103240c8111160428503511210040706041c0c01c91894802040e030311015001610244000030202d1260780600c2080d1480441e1f030410f8040002001d030742070b51703120003146d07a1540a5031817110150080b10741c0700032400880d0380302c003d582001d000c4c003070482c0c80c031100410055507a1001500078041e0340d4445044261110442c94941c50300704403145c05142a42c07641e03210304815040568400400401c3c5040c0c103801040200b000a000047c12006031503145400112521f42d00700b500c520340c030380381441d941c4004c480c014030050094941c8000d08120342120108852131107003041c0342d240c0003e01c0d81c083d1901c6070b510300b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 978423516 1250 978422266 978422293
    0x70f090c02150411040b0103050f0402010c050a140303160216210c090614090708160c022d010f05030a150803040e010503060a1415031608011e02070203 67
    0x4000000c0d45607006442564080c4600c154661108a4080d60b41048021800706242458401c00d46404000e1a051003a440d01e91500084410041c000038100076410300080180f00083c401e8019550b0b0115030080c40c400000005903490700151350746070260300800f01e6488a640006188007010074a51103d6a82918054121386d00c02130b1070886001d5284400d25140002d0079140091010b0504600000343d06400c2244800c1015004201140580301c11021b002e40190051010342c0c0c004007880070010000c121610445011281c084001e4201020401c542c0b00b80b02400300307080100341d000c094064810740340e000448480c410b844601d00807070002c102195003c61150040d014459036402060703011036449500c2461a4000e501602400582000601031440c05000d496048082c6401c01d1051015a40c1c18031008e17000075020b0040359049044c516510346040c08002a1132011381804007640e95101c0c80c042c041c0809000d2842c2e810210102241c001f0710520a440800750080c2c02041c0214041a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 978424766 1250 978423516 978423521
    0x1026010b2e050c2a0f010525080a020109050606030d090b030a0207050a031701270218060d0b0f09011d04060b0a150305130b06010f0306030f030f11070f09 68
    0x41070001006002c10607441c203002c04000f0910004089259400201000221061580048400c0502c035240c140084801ea03a0320805480e0741e07080740c802064030a1401e1110064a50f04500020105032020a00001558040d440b80803c02d000300c09440217030380e44a04058460303002841840101d0017190b8140f042c03400340000785621807d0903500615101464560514248082c1411070014007400d11a103101e505914403a40103001070441006011800d0500902038044e1950420380c0c56408141a02681c4407584181c205036030250186a40d580300c442410060400d102d2194011481110300b0203a9040c0b414503036041301d2001307150072210400501d401c407000f44050400d403290b41c5c841410074200e0340e03079001c100000c100303d664150255403400f0000d001d450000701003903220664a074031035002c1600505420350100c0246404070402001e10003d400900c03485e007024003030111094962042540014040f101010140c5441260180209015544540c1401542450158050704101640098 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 978426016 1250 978424766 978424849
    0x1e0607141611211603050709050705070f26030c1204030903080301080c0906010203070b071407081c1103100621020a1e0302211026010b 60
    0x80604884405440c4000389180000a019010103039600d102c00b44a0002000b6661309000b60341d5000446901d1610341e01d803100820701c42c00400ca034403000060382461140c402c444030b5991103c1c003400c6102c15800d0640c100c02c0440d4014a00f1400d0603c200c8640b2040d0701a28410f0a040019070328103002d52200d18048000a40110180441c800b804400903107064083d5007e4000c04000b030800542400c100f00381488060141410354100300031280c041542b4100450344500d40d420040c011504c0740107103003c240704a80700a0040c04012900f0012480c050743c00031110514414180003d01203010321642070702c825656900c030011030b2542001a5801220700c2c4041d5182141403092030501d40c11308000340d81c0500e1301203001581c07819502d00c2c2c9140c1440c1c28030046041d803504500744040a103558070000c411141d03010410000398009030a45084140413001f40044161220300b040340810080444002c4c807101102030350030800c8110700c038140a0000310360039032310b0303042c4810034034110107225541c1000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 978427266 1250 978426016 978426023
    0xf0f1202041b020d08010e0103030210110c120d0c0e09011809060f1d010608120903030409020f120a0903090302010e120d090f0e0c032202031e06071416 67
    0x4800481c4000801c0000744403055040350090b00150000031001003108205812164850080c0390060002c680e000401c8501141e80040002e0302c3c040c08840808540600c008012052158000506012502c030014002102d00140c040c4184104721006031307001184002d0598200100c0070040103454105800d6607864504680c000030f251420f0740fa9041564542d100d2020f500d500c8003050001d6201c0314200b8044401c02c1d10080141d02e040852441c0c8480b0000c0e80040f040304042a43c8009a41c1801118000c00c0c01d90b1003103660788030003440300d107c1c0d80000b44419102c540c8000002c04d00700450040000440e85503442101840c150307030043d5900d001c0301047d1500900400e41508414400300304030300003007080ba00c0700b80c86640780244030041e00d0100c0d0010a81e8504050902054001c4181540e400c1810701842c0d01c503500d801d2076517000e40c5161180107581413040c019000344008000050080c00c800b1441a203456a4841900b0380d00c0303003010518010095001c02180c0424824207203412240c1d4030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 978428516 1250 978427266 978427271
    0x70219030602031302030613210e0d031709030405060a052a0c042304030e01021f061a0306011d030f01020d0b040b03190609060e0313080105010f0f120204 68
    0xc0300e440e5081240c20890303090302551031484c030000c25450100038955010b41c031544c584401d1070266951440500c0007441005003400c0040b5000040b50107080d1070000c00c1d4010740b03290300400003824024548064218079a0544e0000c001041c1c0000c4044215000c1e210003811241c46e203016503404541680c810034000100500da4010402c0c502d00414416000c016000010400080c4640800084503643d0b01010144195103064048080e000c07803040d070788150907081a0300400002c3d030060381410f850400170000e901030440c040014030341030f070303c08400c0e60f00401c20056610074102c0440b1161000361076460100300c1500700850a00781080e000403030800098240c07505441074801d45402c0e60041140c00d0900c80d2210304c0d42003982454402c1041501d8120000c100b02204030345ca231008903ca1070030141c541078a555000c800d002ca1343c1c201140c10341e1200e007225a80c2840c0f0b150060700940c1402050101e500340000010a540c003c40010107444050825102903440c4c84d003c203511204032a003c90700b107074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 978429766 1250 978428516 978428519
    0x10b091f14040e011d070f1208070201030b060301080f0d03270c1203120f0506010f11031b0604150605030d030906110724060e0a0905070f0902071a0c070219 69
    0x43d00707010b003054401401165003050038142d140d8030b0401d60544c005030710728142c5a90803c10382c0c0c250115100c1040c2c02a181c1940d516150004034040e00303000c0d4200342c22a030b0002c0002400c0e200003407103030320009802065564900c1c90140c11000c2d901c1d00e8524150321001c01810100f506090104021020311079000f4902c4256240408024030601c140c0075001315126103030b500e28400090155221007a080d40003000640340440019200610100d005420050111405104503c081084886404901c0c0c0038640d2003681d800056542c01013290100d41c101400315125100301f00340d0260741d0540c0c030014041d2071041808401140240911401521400e0f00c5070100e141040980703008100f8607018003140125103280c1034201c118012100380c2450000d250500c2040702c003420050175904000307000c00118041c003044c140146001c4458200252070801a00000f4610002c1d60081110b940311340a80c11140a8140c2c0c0304088010031550550b065004010400042c46e00800c00910a80503030344e42180103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 978431016 1250 978429766 978429791
    0x10b090601122d0b090a060f0e040602040f141c03021209030a0c0f170d0e011421100501140304020402210a02120f04110405060102031605010b091f1404 67
    0x19440b03800a1070005136a0500c032422801c00c844001c5e80417040d1842884028500500589181c409110b0800403010100c0460100030540d011680202003044294481c1501c500313100309204504032030544a480b03e1022451649100700100d015940c058010341100c0c601c000e2070441d56403042ca5900e0b80f50049510b442c00203401c46c8c02d000c01034072500014100352070404901e2242c01400300307814407050f406031044206241e40041042200002841e111501110f031241e2403004e0300540044030141d445030103d60071310020003c43c041c41108881229111142d80300c0c010343e5100038200e800c0d00540000c0001802500301500249a00c0c1450410646803112007052521280790660781203200036000075200c500031203000b12041d0001010306810a450a0650380d0341c5140c02e5903100e15025540f01d50000d05240c0c02030003940c5900141a40d41001d050030751809500901050154502c2160f07818045040900581e0403031040d5031141468041a44c00c200140c0d20401034010383e00e51040d03c03040420b140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 978432266 1250 978431016 978431081
    0xc160501050a06030b010f08071a190c030305060604080c100c050706020d0306150c140102091806040f0b0d0803061c0b07080f090a0803090709180302010b09060112 72
    0x35074011440000c00f00d00b507207014080040d06a202c2c9200e00e00d90003051004180c042071803401c03600309010002c04401c40c41c101640c0360052082800c40e55411208806105810040704a0894800e9400b00001e64039402044114000d5014510741e0b940596600040c41c18040c0c1001807200305410046070000c1c580d99218540031660300300ca00160041400081c40c190580508400307898002040034220700c1d11174005060f185c1e0b8080240910224182240c1c0086007035045682c5504054460442c680f04040705c4442440280d900714001c91408407503d400081c10f1203020b2072035100401942d1528116140c41c074594101405d1103030301001b52460005210180e003400c1e258544134200201e0309181500c030280486400034415940351500e401081940403000c0b40c05070359a5405685240c480e240d00584d140307403202c19006000d0162504541036a1484920303034203211148254001d102800c030b40420702040080075204c0741e000c03901100548101d0040c5400c44400c40c844160015404a00000e03085030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 978433516 1250 978432266 978432271
    0x60d06080106061d0d02010f0c0f141e0105060d0308250819090308011a0903030c0f0f03041d0a0f1407030e0a1a06061b01050a0c030e060c16050105 65
    0x40313103050b800741c240060703003903e6450b20301ea04a4200f010501d6680019080500c201c0c9040c080069140481c410401850322101415401c9445130301c2c500c60300018180e80c0c01c5100e000da0700c200407443c121070f40040c05004241c070840300585240c0717004c000c56400f6951120003910f8840c0b29140e40c42120100501285490090701036a0f0340c1c0005414860200101c000048407a610305c1e0342450fa0030008030741c00100440c1100c020352104428080c08142c0a80140102080d06500d400005906629000b0001e0740210004c0040161080784a0075542039550703109520894244414902c10658800318644043e94010700001c4049401c80c01c0784100c6080303418001c99907807100000da040c002c1c1c107545403103101c0741c2c044070100500d40650583c40703405983d0a4850342c030003111081e1000822588512090715200440c0348240800342041d200094080c0c80c045405e0701e102840e00342840c007000d03c20301450f0b5120725181c000d4809508e17040e87d002c0300e6034004072401a103642c4415440700061300900c00c051 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 978434766 1250 978433516 978433529
    0x230603010807060f05391603031b060905060f0c0301060906050a0302041e030605090d02060402040c1e0203070b13030c0209040219030c03020f0d02030d180e270d0c02060d06080106 79
    0x80105034000e080c511b20100c3c07140f003603007030b0740144040301c0146e407461401c4003640d070941480b960086d2442c036414a028403403080206103904200d4000304114000070701c03d0251801c840702c40210355504100304400d010900c14200011a4039030100800c0f4002e80c00ac001900c498a070151030907031a94030300203094120311100b819001b12013004200307103c410300c901604001d80c01c02a2000e0341000030029a00c10f00580064440c2d070381c1c1e00c040100d0340d00564031034031040407a00b400001e90272141030280d1030b60001c89043d14400074040000f2030398503c2c10111075032260301d9200c442c1156056024421a0403004100300d030011415400c42c00b482c844040a140110302c41c1c44821841c50442c0706104a0945400341c0380d0140804001c118016500454044240950b914114040e005132821a481c440c0039a8000d030002d188a00610405260320a04a05c030811030203900078216090039207959940300c1415112001548034981d180062a00c0801050380c0c40f101e100124000b9201c954082c03c50311150300c1034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 978436016 1250 978434766 978434827
    0x150705040f180c02010209010c031d0301050702030a0224010e041104022209060528030b0a0c0f090503030d0209010c052b1d0d050f0106230603010807060f05 69
    0xd10b40049401103101c1c046003440290304006000002821500301c20b00001c0600501100c0440c0e4050395126200c800c080003402440281085d03c0080d450f68402c0c90b900c0014002ca00b444810f45210314401b0084c0c81c12582210966032900064a209204c003500440c0c0459034000030b03216030f07039481c005044070804460602c0380c401070702d51018441030b46650042c0c0c0d0361401d009007048540d455041902c0d40715601c100d400c803000e000320000d480d0009075805c014134000854080c003203240301c20b50141a00d048152200705080f221704405581d03182480c420958580c1c004c000c416048245a0090940b00310107052003d2448459038030207092525410900469801826960b85d0310016049010028001da051244006131841402c1c0030712200784482134041c00e0340c5c030000d20070800f080205d40e02003141007008101468903018580c0403040845025042c40c030034800c0204451401c281264102d81c0000000c1404070300e03084040d1103c0002444407004d0060621581c1c25215260105a00c600d03000310300c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 978437266 1250 978436016 978436049
    0x3160c0512160909031e05070c06030209090712142e15050a0e040216060b0111060f06010c020a0609090c05040b0a2316050c03060603150705040f 64
    0xa1008140034034288048980c07149526558400b4054030340d40c20384075803d034081103120399401d0984e1840030070982c08051007102081091081d42c07000c0945a0b00348501d5504c00c2160b9510412410390140c004002d03440321404d0003180750702703004110200e00a90090300225a5800b100d84880014004441802c2c85000d106d080140f50480a000014406000061114400d040441107141400504501d409100c000600c1d90b07605405075444148000008100355510342e00150b141c082030395013107004c42d0b285041a041042e103600900500214444282c01011a031b500c40f40c0c1c1218074a006002c05051000e800106005a203c14040002616a540b240310307450b441d10000c00c080703640f50101007081080c2032205103c511408421a500707101ca500c0e080720492a2110107000544400a420849060014a03e0b00207400c1d9002d0b240300c2c0e40205e0544007071105c00d801b4107480b4001115100c1d03043d045940080030289500e40301e660000c80c140351090605840b1002c0c0e1503082c0803a00000095000d0004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 978438516 1250 978437266 978437269
    0x9090308041a0c0a0309030e06030a1401050603060d0f0602210106020f06010f030b100906080f1006031a0c09040f0522081b03120408030709080d0c0209060303160c05 73
    0x1890241c02400310200380392603c1d120964950082403410030800d80c54060360001d1520070440040103c0000340502c3d0340381080051240106110010410700b0502d140c0001220f19103003099038400c040140c0103410000740c50742c038181408400c0300c080f243d05a01380101583e4103542d608101580240c80030003146941003210180c41c209089030811a80c0c1c9c0706030300501c2801000a038080859a01454400c0b4a483d0381d504100c2180c60b40c0c02c400c205a142c0000012020400603034459071240c0c039003d9810381e0032103880d80c4003030307600c28003000e80001c0b51110801450810001000e41c09030450000e641042440d5002030196018640840302c01d40e01c80c0d090110081c01c030002c2510300120a140440505040e40e148212401460f208000c400309440d03610040e00d80c244116188402c4403182c150700c52030f152801c10902e070025111403001801c02e60003c910420000307503c015181c80c90700e608031a800160b0030003040c3d90005107001e4140c001882107640b5030050000381f80c6038901c101d640d034180509020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 978439766 1250 978438516 978438533
    0x1170f0303010810020307031d060a060506040f0b31090b04051015050c0f06091207110609060702030a030201291e0402071505060411030405060f09070909030804 71
    0x250024050300200010044140002111002c8401c5400c000d6201c1d42e07194030a50003231110f09410720520010503040c010019001c50090b100b03400ca4201003110304d0f16101881801e00990080c03084031000c921042c8020032041c0058450041c249128622001048150400d250320b0f441a402c1c4958250409004400250180602a450680b010810707031030145004501c00307001d440380d42c4005100d464034145113840f6604880c1c90200010843e480920061140c0307a5510b8111000d505c43d0042072003a0940c0c90a1200302c0c0c1c0da060300030b030149010a0b081c0080240310b40c09881704540c010002c00c000c10060300c080c01303003102e1203001c1d400000d500a1170304100030f0400f2055208101e1408600b811440986d40c1109a00d032021040c84121303e049006008100280b069000c081c0600001c4030841c41c0c65085600000c0c070490060310148801203181340c443c0b000740010f640003000e0b50002400540e2001401d41d0250b840351550044070300c020354845802e404c0350301038a01500044d0b010400c200c00e008054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 978441016 1250 978439766 978439783
    0x5070c332a0309110d11120304121b060e060a270e040b0a0516030b031203090f070614040e0601020c1c021509010c0210030b041802040e0f06060103020715050117 71
    0x940d01c2c20700340c103007646e51010418908400030703102c1c24207540040041c0e03d0070070955014054298604040401c0b40c2031000402003609040740c41d40400d02004242113100700c4070305858400292510b82081c2d0780000940c0c0984900c2c56141a41a0341c0c40c03507181400100e01d990f401001184620381d1030b82080c0c14412903502009000c022154102001d02c40e80300321090b40000303091140e01d03000800d030500e2000642000c102c058030351070186c0c002c000d01ca1021030110303030b010302c045880d41201c1c159540e40c0c0b419101582540f0f01c0352000c0e08280403c10a03015840303134443d0701c25014410740d2030a603a1400010800014500040984a903800d424000c50030200828040303090394040740c6043c0441d900000386219032040009004044584180715064040d42140e0a11000108103014880007000e080054000001c000e0344170f1802c1c0f81c01c82012180110302c1042818102c80648826030f1100010b6010350301c2020704803100c10030380e100d04540440901ca4140685000c544e01008014801c8040c1e00c0c1c051072 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 978442266 1250 978441016 978441019
    0x10b0102061015050f0d150e04050c041d0703050303060a08031e0a05070b150f09070807080603030c01060e040317070503060114090405070c332a030911 67
    0x1400380c2180c803610b448048800c0140152100703807954004a40318000c908807281608004140c140c070310411a001405103040c1e11440030043c55a650030882500c0303054034090f000380c1240407003456074140398010381050421000d13820740702c0640e607003002d15042c2d19074820380d01071b003011040c48a2450511b08010081292900031400c1403040c60b80c9645600c00c0300c030b48a090010009800c00800d00500648200039000850800c0d1440e015140c40b400b840c07a01c040c1803156828500306c503e18a0704255150040d450760780c0d452100c1ea50f00740709071005440507283c95071500c4180003c4807811030034013403038020b004443c00e44072090600e441c01810a0b400801502c3c1c0842d500020000c2280d441400d42c0d034800b00c2442c000007d030441440010261054281c040e41050406041003078164101d00303482003080c422201010000c2e031248401c400c2c84c450b100b0040d56443c1980c00314546401c19009080144000c440c1154441381030341c84595a21400c50080d000300ea282d80c0c48a080c842d10484c0ea0703001810 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 978443516 1250 978442266 978442273
    0x3020406080d09090c020c030d09030309050607050a0209061306030c0e100602060c0d09020406081506060306010207182715050105100c1b260309060313170304030c05010b0102 77
    0x148140500310601501404d80510390395401e07401054800c00103403011282c00384c181c0e803021202c01001000c0e07101c540400c0d400b0500031040012541003407000c54114641002c040c207002c0b1150b900f0400059400b0300100da10171564801012031001c04e1042d90b00840c810f802d030400d42c6140001c104000c00008040c140d02d0401c100342004a550080351040e07011480c5150b203036a513402c10382da410040c4010240a908246480c1020038007610014042e5011600c615921105584000400100d4401142ca49006030042e150800c10a40880300d01400da8418100109080d0020982d80ca5981c405042141e80407040d03a115009000349032200f034125905e0003400303001c15818040842d0741d0084143c410003c100051a0030018041d80c600700c0301c0112040d010300304125039101c1d41c2142850103200c500501c2080281403030f400f440000102e50b02004068003545c00c694542c0003060200e850010195020511048032102c0c0846170402141b0840c03103600e9101841e02c043c289107003103410000c0c1d42810f40d031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 978444766 1250 978443516 978443533
    0x906090903040e1b0d050109150501020d030c090b030429270a0c090e100209030d0302031e01090c030c030c0c0210030e060115030b0a030f0204050c120906010302040608 74
    0x400c0071044905a450b080303035a100540b5415079210038507002c6248403d001102003901200c1c54119080a4122106044280441c044609884404490074450175000d079121204221246002e5081443d46002906150903510307682c1e02c1910a82d072048800711181003045607001440c1e03280c4071112004224100640030145032010403040340324400b0031102070141c604440004110310804c05c00180940c000e5281501d04c4d5183c9110001d80b81d04075440c8054059907181c010790805070b20940e0b66980c801401440f00382482d032001d600035800a0300102d00034060749a5450390210b039840740e50081448000c0060103001c00304c2c00504560900d0a40c0d401c00d8140700c44411107503403007219586a1901140c0348401f00f01580c1094000341007640380c2a19600039070000091000c0d40503003d2081c001541ca05100907a4084100641c0081a01000385144182980540542450341c00241c4c8040c10142607807a143c0c1c10002c100700120b0484501400f40d20800c014000c5003020f02a100080145000600201c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 978446016 1250 978444766 978444781
    0x9023001061d030307050f0607050c0601050d0c030b01060e040b061c0c03020d0903050405030f0601080604080c1501030629010c2d0308041b060c031b0209090c090609 73
    0x2800107100710410428040d103000100c141402c501035408078001c0449941c1c502c1880c180da2158079034040f0171424082d610004031014020011902c00315074103400b030100c5a080030f04101841500f11001d441c0c40b40a600d0120001d2780c10040f66001e88041d0316410f5401c01d01e4401c00050350408000613009150078045c42188140c00c1107444076451840c46c011603122400b140072070090140c01071118405042460000c1407540102c01401601c00035000d940b00704007207102440e43e48400b071041107001da20610001c1c0c04604444040c002021082096a241c1d00440326110303580742080e042030740e04135500c83d07402400b03031000318410081c10390303441ca0001c00c60311000010f0010028400094900402800000001d00f14a82807148588052845088a0b0414140108128001c1320f0071a0700c00b004900b00c800700030000600d0000c9980564885000304620f0341c003201c075100d1102d04844440c0c2c00d1502c1100581d50714003000c2c400c419450003050351007201d4041140425004d801c050007100840c1c14008203 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 978447266 1250 978446016 978446107
    0xf060a050d230102040b090411120609250f1209020f120106050d11011101110f0715050108011a090609061005040909050705010f05120103030e040e070902 68
    0x10b030404070b62040d00c2d0561180550300b09001069070841d500c0060041545500700001d0444460203640c00c000380c072094134085009104244031220754040140002e40d4910304019180da00281028610a0340c0010a45501e43d804130081f484020079290700100d01819407000403210f407029905000d106510f216000b00340b4014900c9041030003251915203104d02c9000940150005020207011040c0015107400e0400420001090903070000710a09418040d021050042d0a4110202c19500d460000100142c47c0da43d400544101d550316101c96112a07500b80c00e04c501d034024410303c40049402c0700011604d90b0045541d0707406a200314070f554280000e6480d40e505095120a0940310120000c0c03010500369054016948401d1000d410a0208010018040f42140c22a80300b0b884030840c60038011025134081c024000d16401c415072004c010808248550090f904d07542c0040c07c00222140a009042c2c00d041241c0c111219090700014600c3c8801c0c007004c903060914001010307802030038030b00c1034070690b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 978448516 1250 978447266 978447289
    0x200102030c19111f0315271506020c06090d0204090510061a07020f030703050307030e130e0c010309020a050d030c05070609031707020a09020301030b2e0620150f060a05 74
    0x20159034104024211b04118a03c90161194400c4410b0290035019020050442c0c81e02d100010b908004c0d00450b20080324481d0425030302c06030060420004030000744040c50708200c02156000141c049440c0c0580c40724031501e180c00b80900c02502c102840d21000c80b040d10802d43c0000b201d40070790b0140000c417500d40c0c82510030840e41168680f101c00c03c4180083d281550a40000e4a0f601002919404164111442c800e5a0b40d040d603525415505e803102680448911480d085800d07040301e11440032070341c8a544a041201d200a282413181358556000c035012000348401107000c24007003040303141031042c00c20907680201b00c10f18001c06c015055569410180b0008550b11929940c0851141c045503101c1c01458098a140d03c421500e1750f075070b41403100141c0016101940c440106903400f03c02c3e43c0e003407660300c542441124040d1402c0380c500103080340c0b060f0300342008002e054145942074040e03403014849405070681180848003142440310ba0b5401074480980300714850030518104100c0740c0ca030a141000c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 978449766 1250 978448516 978448579
    0x1505030c01080907261b15090d150902030705030d0c020910121104390201110a0e100c0c0608131b0918200102030c1911 53
    0x841c0c0d0785a01208520380b900395000317210318158581703441c03070b66018201d61004008800c0040390061170741309041e20742140c0d078500320340e0b04503849044820885228100070b0103445005042c000d500821500c60064040c02d8607043c0e6410f98030350225609602d02045440c024020072405000302c03d1092001808540455100030b0007204154009407074080d40c2c07010400202036078034201c0c610100504d0084001c000030080544528036120004034850103054982c0326903001c0c1c118803161407001c3c0381602c2c40380c41c00b410740108540d00c55a6601c28001c8a0003c0c0020144a071145044100110304101c44c200c04030141004002c1d000c1a010049a00180203104550b01c0e41400c0c0300076100c042e40b9440c2c0c40e68281d030103400c2107003c0b18404c10006a0301844030841d44ca003901007042c0c22007002098016080c0c0000940b00040b50400045c03205083d880064040d5030500447c0d1600b554400360700e0501e40103c817200c101000c2501e41c00c060100b07244030010b541d41c0031198170303100001e205028144c008034000841d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 978451016 1250 978449766 978449777
    0x12050603032a010c1806020610180b030114011412032217060708100302030a021002031e04030201091d040f03050912010e07060c020603010e100306020c03030a1505030c01 75
    0x340b0101502c140a20380c40d1002d9002070091140c06080a005a043c11420700310f0303a1038600380002c0b01031001c6289400b80c200d01c8160341d6154903101c4c0c0311081d02d850b01e0021101554071340728064640c0c1e003407080007540b20034568540f42d07a6242580059229070190b10540c014400e0f00d1006013415008004c03140c0d41410502049880700c0c03080380b072212028042e005568005040f0f2208500c08400040c441e10803540b80c0d54103401340ea680100d031f040005252100a40641c0054440401880c4c00941003001840700c0c4110b9003012010722040100240c480516000342000040a0040d56030268019028002100c1039803001081c0c09020700c00420003c10140c051680300340044201072146045074044a4010254540c179003d03080740300d000f86007040143c80d00340301b0f041c40003a41a00030102c45c0e44d80c0d0f400034882c5096a203880d00310003203240020034640b0300c200c4000000c0005249880a400c51620300d0000b15164036100000c0012a020728008082d1000608401c0115940010700710780d8010080c0b80a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 978452266 1250 978451016 978451057
    0xb04050a240606091a0c161205010507020109080409051302061b011a310906020a0f080603031603020a0b0403020a05060c040b040909081b07061205060303 68
    0x10604084032080014800481c107080c00305040a6100d601200141c58030040000070b82d281c009072180c00c01407182840d041c1542d11261418000700c3d021300f80d14410f500a41d203407150032504090740c14010760401035079001c5245c60301007800024400c1d1584081c060000300a48442501c0d194001c2c010b6200e5401e0040e222400182251003842c00c00c4442d6902a01082d00c580e80d40158008195100c0070b921000c2d8a80240240c160200d11680080d15202805c2e9121820841c42002041c07800d1741210b403408920050041202041b40c45042100d5029917001a01c40b0140b050080c80c040c1e40510410802024105222103075502108036003036801402c01d04214007003c0c1c41c0030703811322a5000c0054a241a002d04000500d500400e145082600c2401900e01603610150101d826004600500000c441c4c240700500c8900602e034130080c01540104000c508290040c1404000102d520261035829000b80c1c9080090681200d14203104001d184414842840c1c200042662806040640f1101c03100042d80d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 978453516 1250 978452266 978452273
    0x20c1207140136061518060b070b1324050609090d08090c060310050f0d03050307081e180d111b1504090203010302030d0c02010e10030f020418060806040f0b04 70
    0x210b0070714540c456420301c00141c405c40211500f041c0c61042600303613400405034082914181c07007402e09450400118a0038036105031034410081d0402081e200400c0c15031080e400210340105003010203025540c2c841254038000540f42c100b640d0000d442103000e1004a010f010b8031034002b040040100d0360740d01d0242c240359100e111540c5032804400d0000c3d0000000010302c90041001e00220302a0b5200b0303501c2d1500307a90441c0c00c3c0b21482011003030150001c1c0e01400428402d0b4031a025864000c0c0303004440904402070172078003150202040d00e007209140e850f055110001c039814094440c1010407420100100241c241016031980d2214540042d506000b0001020b0b40d03480c4140724441d031424402c9203071a06d45800c0240c009500a01007a13110340f00320034981700c4162042801e840520741c1030792070084801002041c81110b80e0140038070341c140354a49056180c1c50805d480944001d0200d00e030020700c40ca917482540d80403540e80c2d82005c981c5030003000400c40801d044001d51444643c0c400f040b82025642c070309 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 978454766 1250 978453516 978453611
    0x504120f140a03020d110301051804050a0209090109140607091406042115021c020a0c05060907030b0a0504050c010c060905152401021b04020c12071401 67
    0x10480900703400116414038203a5060303010b8a101c41500b001084141c451000c45000e40c0024402c040e80488800c450760418400419019000b510a60480750712003c280e0000351140c00440e60103299a654000130010702c080d4103000001165598060240c1d4107040310010300c014110b00650046802c92201640d240e01d80e8001c440051515002c54a070b0f140a580c507040f02d40410402c00e64285c0721a09244c0c190024500c22102001c0050b1819254184a904180080c0d004072800d0340902c454010340d035001c16030600a4502c5252080701174a01d2a0562500981c1c112014080c802c01502c4c1404002c00030344006036141110409003403e9004210610b000c00240c81c1c000f1008200d4050349c00402c0c0c40401c04007660b80910340d032000058501019502e01080b41001c80e000700e005074042c001c05440c07041d86c646000703440b060140007d031502151941b038910304408851280004500081c444091103039101009174241c0804000b07100c4040007003c46445080020781c3c8600001d0b115400458203040030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 978456016 1250 978454766 978454787
    0x4020a051213210c0c03032d050912030d06150f08090606040506030a05150a0b190e221103010c050406090b09120f0a12020a02010c0b040507051503190504120f 70
    0x50305c0a1003c0d120b24004100c86d80c0c40e204001d0100c4004540322540b00c2c0b040b1401c0e555800c65031414200103100c0c1c104a41645141080040c0380400c101c490658042c6005500143c113418807a0008200300c0706009100240b40302c0170b03c04020626060180408010803010b4210310308071004101c0351940400281040c1c4000c400030602e210310729210050f659040b200078401d021941c410410080aa401e1282604401e815201c59a03001da01c20722101002d001d075207400103000d00e5181c031300000c50360040c0300d4441c1445080d40c404172440d04410a078a02409520740342951407a00f142064982000507007030380700e9030141c2c40300002d001c50a14119241c600525215204c0c00c0b088a010894403050b00b03488407034405007681c0c8400c202500035282c600000d050717884130b83e06030b4805440c044070340c403424100300019004441d180114840000c0742d640d01c0311640480c01c42002c5040e6642080c281c00c4000700d50708251a543c1508080130800400c81010643c89084000d00304074070000000c01046904a261 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 978457266 1250 978456016 978456023
    0x1080118060906140a0f180f0b070e03030d020310121203020c1f0923031c1b020d0305010504050c18040b10050d050c25050c04020a051213210c 63
    0xd01005003080303030b9411400000b02911001c002941c609080018010b402d091f011b030071500e20704a07400006d800d510880768085418904041d05200c0c00002904680c000070386400f031140c0201c18060310241890700c01b070007840340c2e02c4001c0130541180da41e803201010321034a80c001d041d80441d0034a80654140300707043d00007040810444a01080c00e008030700070208804103540003041c01440b4521440d01548150070305484400075402c11040d80300302c50001440d03400c10b00105444140003c40d4014021080c0010100b5402512010f0704c2c885000b002c41798144e000a00c903030b0514060200c2c2103140021108104013103010888071561400100700509040e00407140c00140d540040741e10b01e5441805022442d5414405100c6600c4503560300e2800e025206492180781e00396401203a280001e000584041d9111300140c420f03205e643c3d07000400f242c100c88070940c04204c0018500300020306441070180d01c58185d0400d440c1014880d1511152400d842514105006c012440d030300c4070034041c0c0080c052a950 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 978458516 1250 978457266 978457301
    0x30a0807030c08070c1805091b03070503010c02010617030f0f0306040b1e040c091d0424050a0c050a020606012007030f062007080304140a0606060801080118060906 72
    0x28601c0d00000040c200d114000604106448000b612034450041f5402411b0a02c000d010006083e80d4101551031410002603140c420031100150585081c041d54034018999000085c5c02407600d2410a000f210b07080007075126402c100420908004510161440445901c074115180d0366040c0100f001805054410355000a80501c101c1503c0301c1d600004020401c01c0d5000e10000340c0800040d682e6808030f004030321120100c0360042095171011000380d40d01c5401501c0c0c1520b50a0b03c41c1d4110aa0750413000001c0c00c031600c4008200089c0403034000c441c0349094031700c1c20a20703140d2040340080d251038010300701604210b03d80400c0c0141c440d240405208801804007074030205603491030000c641500340c00b0704480c1f03d41000020007120b151f10742c8519846044d03220305882c0074074568904180ba8401841100c80102c3c03140d00c0151190702304100a480f612424000942505044005d820710300c4c16032121500d0380c1003000071944c0001c900d000004056200340040390440075490094050090100320440151 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 978459766 1250 978458516 978458527
    0x1504020705060a060605090310050901140103030c020a051f030f060504140406140c04031e1406091c050f0d0b0409240c0c12031509060806090c030a0807030c08 70
    0x300c00b082503409a01e049004010250f552107080d645d9000c2c0d00c000310340c1504031007545040029207130000307588074032500000601100c0103981101c004500780c0060340006c0c0f1351003011046003041e0080720003500c0700f2070300610040e441c81007039600b201041c9042e07000c060701c0381c0c03200c80c0c2c400d0103800050180030000c02c28040d4004240c40212403030030443c0e0948015042240c030080d009000700b0030a000e00382c0382401602e040d003161201e910b5444400120302e40300030303071200860110380e86072620f600030100d10020300034500749400b94a02c0c1a82d580031455036242c0000350180c19a8001c002c451f04003491100c4a62103062044a0790f00401c49800c090350800d050034514410070000001c200342e061038500d800400810044c419400301c0c0e100001d1900491038207120a0042080030481d10f0b81c101e0107280110b810311401d65288400c054a51000f224141ca40340c00380300f034020a1114590004d12280180040880800040d03650382204501a0000400090010a02d840341401c500c90301c1c0c1105116640e00d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 978461016 1250 978459766 978459773
    0x309020f04061401030b0a0302030604020114072111070f210506070306060f030618090827280303180f180b01020a030c060203090c04052d1e15040207 66
    0x3c041000c2c140000d2520040f104280362039410f803020b50780c0203401450680d84580c0191803940000302645800d40c03087c464a800507005110340280488a55010181c640b0864805803820f003000a490850390007010040c05240410300c0303180102ca1440740700c507284a005000c14081c110700d40102401d613000d040108400750f50184c00c04021207486689075110700701c50f520b0490480340d83d8041d001c4480310891201c64610380036000f104005005e5504549000c003400c0d402140e4410840d0032454404401c0da0b41845440c0216802d03d0030074080d454907003e406200b014401b00091030000070140007400140f031000c03048000c2a40090b005511801500720b46400c0009112040b10b040892494101f028648480d4030100301e401c1c070141d150f01d908032030f03590903918035002e07400041031f0140903c90304c3c1486a01f691140110341c080c12241e07442c240300701041103548102c80d43c01072000c2e480c81c41000500090500d04103018584403101d44902d070440d1605256885080b01e50b10341e265005001140700d4040c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 978462266 1250 978461016 978461039
    0xd0f05040b0f090d050d02120f0a1b020618011401030804151d010e03100c0e04050901090b040803040f120f090602010b0f01050c03070f0c09050f15010309020f0406 72
    0x1540120091907096072046100300d00b100c81140d105100741c1001405000c814003402c0038013500900018094140241261801d06000741200d10303010100031b080521601d10740d98800c00b5000c00c0c0c0344501608104003950f0203982c0d000081c0140f0b40844529034165041003080d400005101a40c2c4d4041c0c446503541d044c5030509810501840c8150244200c11016290088003030144142179000742100360070b4007100560322070b010401500d130036000d498016030320780085200d40300c031001042c0c44001011b4540d80c140700441c0c40051081c0e03402d83c5020111804a00394002546c1d2041d0b0000c19207a99580e5031034103140c01c0c0d9600c440100b050980b01e29190380a5001840500308140f240d940324a0710396100d001324280c81c50164282c0c0c00c60804002c40155503c51401420b2541d00d5400b02d902d01503450350f0314003111b01c040358190b0f0b03070903403955050011408078012141c108038848801034060901040d1441c141c2c01102045050580d50607444045440d04415002641c500400c10066140d039180750104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 978463516 1250 978462266 978462271
    0x70c0806070f0212040f0302060307032a020c06071a0406021912053103030e0d0302040602071e090203040321050105030d0c05030f090a180c14070b16050d0f05 70
    0x54014010311030401e540c030005890443c1c01a134289006d081c81d41d000e1100b0390b4405441c1c80c04058407081501d0401c1c0d40007c078036409078040069494491508040207007000598405036104045c10402d80002c500102c1038002d134004141d4111803151928075002e40244556984039541401d43c01d8206034642d00b003984007001d06680074080c0a00d581e55040719019100b1810035114071f4800c00505070fa05c0c036158211035031403442410002003440440e00558a81a041814080020b030005824001c0a60500141c030080203946821005900c440c44520134541c3da60160202c0940c1c0400000c0078944591700005c840180d00c0c0d40d20800d00e214440400281900340a0140240300d004455060305209800000107a80c00001443c203007802c041c82c501e155070148200130760020b580b01d00410070215061040400c0d071846500003a80c1e00b04584041c1442c81c9003c0100302001c002d001000101c0d150409030780c0e1089542502e50440b890552095810340603440d624030080303141c01c01c00c10480045500060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 978464766 1250 978463516 978463547
    0x71703071b0f1a13060f060515210f22080d0603050120030411010905130e010c0507150b0102030d1a0f09190c0509300c0312070c080607 60
    0x2070741d00110030450f441c0d10400390381c001e28261030a4003420200d401d59000c030f5203a5401040100d01c40c0d68620008516086000c00614041000203440e050414520310b20305880c1d10764610750301ca5140640000d0b211072402402607092521840c00404505082d900c81c0c2242c551207014a41c580b200100440002e013000d007c111204d43c60080003804a00361203507900309021400030766500e035569668403020185039010286050010030580482c0c0c90f59001580500b88032500800078802c1c650020003800d541d140070310102405000c100690100b00e445005071200100f01c8800306028a203200101d255203d40603945403000c0c501154150048c7c030140104001071411102481d6291855013000f403012401c0d2084501880034401c1e62486295981040e0902e0000d410518240382c504000316003d42e5081c0b001d40c8501e1903060140d80344604584594003281c0c80321004010015111002c07a690710083c036209480e02e400420000100411404290082e08907101901d4590408440151010b129035580c41d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 978466016 1250 978464766 978464783
    0x60c060c050c030a0513030512030708130201080106051c230a0501060806090a0605060708040e0f10300303150603020304020609100507140c0a0b071703071b0f 70
    0x203003003461045069440c0d00036414042c41c81d1808840081e101039110130305250710100c2c0c507038002020910a001c05000707200c3c0100d00c0c0e0765a180c4440c004008045c0200340c1070500d0a040407010150364011241c80c10f442e140e041c0940e44003420070192069401003401214803038203052029103a0326540d801809002c0c43e510764010a51140100c610540300300b4003401000501c80b0000500b03610b0540d1401d50000f801400010f05161200c0104003550700445003500e006800080404c01752008412440d070021241407403285a0800c88048041c541251140c2007181c00351303a04005500c15103170b030795881001c802c090f45100c503115881c000e40a00195602c10507218000c20002500324000d0003103902c038a500500f05450010880300300b0aa4501199600c001c00c84144288800104650f80e0340801808400060071540845800c02001c0c881e5900104e50780901400383c48001490900020502c070b8220b40c2068403507581000c2181c1d584075800401c04d48040c0898128207000e1601c5001c0c04c124011003d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 978467266 1250 978466016 978466031
    0x90b0403020c131a040b1815090105030c010c060b01020c1f0f0216031712040f0c0b07081b03160b0709090207262b0b01030c0f0e0d060204060c06 64
    0x20f0600303e404242c94101000d5071080c010740c1d1440c0c643e000e443c8410b001028490545210200100b84c4001202c0008640944565000361498181e5648e0300405048000713000a0000f5400242148140c1c10300900243c0c681c0301c041000d030f000740401820004080c0c030310390b4440c401e403140b41840f404692400001c179900301c1d41c06010030b1020a0000e0380c002d00c0662a011103240d65a4006c0b4142820038007201d44000b03110b4155141100b455a50180b409080c2420500c403403801d2807800c10b20591311400daa010100710400000702001b003a201d0360212504051101030300114440e09620903d4915030701031006103014020081c45034141801070320383e580c481ca619174a90242d102244100503014050740d24800b100c1c400034408140c04541103030344224040c00e00915030f1121254101c4040810070340c090a00d2000051901c03071003510b000d00b20074039090151041025020b000d103150b80e4102c208000b40e0b920046030588035400041612507104400b1540c4650310080101b034441079120032191070b41018038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 978468516 1250 978467266 978467299
    0x315030705101d0a060e01030b030303130f020a080613060b0d0213020903010b1009090b04090809241614060f0c130f0f0501110607020d03020706090b0403020c 70
    0x65410695401400707079212044510020f60301034281600c0150342c0219190700e00203685903640c40034014242d035240c64803000c81010000d0140c1b505001c8050203030b03200384200015801c2038000400d038107810a01e03050500b0154008140d003c0745603040890316204540030700288944408030303041201d00480b400c010100200c03017007280f65082c02e10081d41c0401881028040345115900411040324000c000084040c0d80e00c0200c0c100407284031680d404142c190700708020340c5446010381d95035078100b20b40403c004261951003e4040c061011810b010b50404e485854800c150400341c440b0f8030b0a41ea0390a40c54500051901c070f842c03030300c6250841d01c0302d5141e4074020070444001082409402121f80e400080e660b6110180c10541080f84c404140340e070302da0310025094804248035805802c7c8024458181030078440003412004926800165592000c010002403641c04101e418030542c03149400350b520102828080003a01c0000e001070041d04407001840209a000109140104e005889108498002d080b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 978469766 1250 978468516 978468523
    0x1050c1210030b0a230703020a0f02030918190906020a09050906030723040501090e0c100203030103060504020402070b07020606040c02070317070303060b0c06040512030903070b04080d0c0203031503 87
    0x20004001c000d456010403c4d07020944c00c4203114103460b040c000d0700c80440000c08151048291004004243e00068103d00305911072180c14000c801c6000461414026001085400c105014080d0700300c100400820103582c038501c1100130b4400e100c07405000100103030a0500081d48066901ca0214107001000605414000d8a0b1ba00c140801009040318916042801c81c2c4420400d406119038420002e15400d03c0d6610311a050283c41107140010707032139a0185003146807030416822035114111203088410700903130000031030707040d287d20500105084d00c0c1c9201003800b0740110080203182c05500020080c500c1d500041c514801c5408841c140001c001266050381c85a5441c00040d100d100e4511000d02c100346d1906c018542f843c840c2c50000766140da18449101241c00526402c0c40d030b60488020303c003e0000400a04000180302042d1919500384011159a01d2151200082c4415160000281440380c1c1030141d0310b401007050030070707c14050529030007903d0354401c03034501b0004250352418040e80d04002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 978471016 1250 978469766 978469769
    0x1a011e1a120c04050109150c0f020f1216061106040809220207060507090503120c0c06040f060806060a0905040906110d06032a063e0f0105070207050d1401050c1210 72
    0x242c0f12100d40c130046071078900c27003950010010b80e08414038980c2485c90b620340d02c1031682403505d1100907040a854601820f040d00385a0350010301004040c100c0e00108200c0490400d030440d0303019507119078a1401c0300120b0348624111032041e003000c191014094548c0610380040c5121441b41800b08200e595030802aa0b0101d01c5005494050f804001c1304142e40100c1c500600e12125080210343d00240e01d0340000b0360b20340c09900003c1c509100d007c3c003084580d0b002051913400203800c603032450408219600040c80640c10780301c1d252085488448800601280390b0259400030300f01c4403860f40c1e508805100d8009044148400c407488040442d4070400c00c0f9034080c01403000080d1201c00b07c0d40510b010412141082080318030200c40d00303010500c0c0d00c05030340c0450407001d8000b05d0ac960360911100642d0310b0308100e101403090020764101000c00c112158082103110903668220b078030143c1c155080c180303500340045000301c2c1c8000e5031804080c01165180100981040c2e1542140044156a911200350040344e05 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 978472266 1250 978471016 978471059
    0x140304060212311704140a060e130c110616260601031d160e0c072102030705031216021501050906040e0303041a011e1a120c04050109 59
    0xb0101070100200d020901c034001030242030780360301e606080c82030090301d50302c9a444006e10309118030b502c444c1c81c2800f0121400a00080c10114901e00c540310100705c1444030300250f52102035407000994140d5001c0c00b08070100080c81c0f021981185010404128802c0b02c0710b03140f00c0441d05108201e400707074070000314607009040408003914a070b80b109801900a00043c030500c8800c41c0e507403800301c00c1c62107081280c0c400c0c3c0411640140503844c500b128030004020060302e81e001740c00c070402001012540083c3d034407410301b003840c00d003140c05046607000f00e04600950300020b02c0380c0800103015860380302e8000c3c600d02610700c81c882d010500c613802e4416079070b903030740e00040b030032126a0100100060b01e00000c82c0341d440a0068804542c8080718810a4150351044600300c5100010000c40040c5e80305240807030f405011041d5400388200203510b01105480d519100c0d01941003400301000d01d1505040c0150382e10840202d0320540c2c2c0d814903041d00034503a003103800380364001008240c0008000142d0b4840c100c4070600c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 978473516 1250 978472266 978472321
    0xa0209012111060412030c020f010504121410180b09070e0f061c03030c270b0d09020d080c0d03020301140f01140a030e010518030901050a140304060212 67
    0x280d680b81080c07458010a41980400e091000003003580c4003c0301c0c0c41c42d05100760388407d52882c0b64070401503251400303420241000b200b4401440030482d40120070074a50b81145070042200d030310340c3e203076403504001c030105075040b600f070201641507000ea42d003401c001c0d9841101da2001c1d6590740e001c1140d0701c1203248122050b5014100c0800c01c0004202c119503000803018114801241d01101c0c94141d0b60b050b50402c500090341d5071080d90820780d00007004000307001134005030040014006d40c1c0041070742c0240030300094040e0024507401c0c40550742e0f110b1143c555025005402a00d041c0c14003440d96048072107007c1e0385015910740c0d500110311078802c40e810ba90b8600c01c101141102f0788248035040681841c56030621500119200b0b02494482c081c01009103039903004544d0031425490b4609681c0054040c0801d000074901050700200040f050b5030440c4820301c5e101d0380b00c0705020011282258409015681e8003000001d01081c0641900140800c105092948040d034070381c01e1110811070584001c0118018 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 978474766 1250 978473516 978473579
    0x1a030106050337080304031d010201110d020a051b01050106110a03020d050a030e01060905070f030b1305100b0a0302030f090f07050121050c04140303120a05070903140a020901 77
    0x603a408901c0021009881080b01240055038440381345910941e000d6011441d0240080a907440700c401c9020414003c0c4000d000b5103170482207a500c940a031a503200f40c92600840c4050041d44144250707003a955007501d500398042c00c101e06042c004c00c8280106000110900e4a8181c43c18001801002951b4940d00601052500311406c03605030304100329076000c15441c2c010f4200d2400090041c1c4016000650340000c550a118201401803030091001b4014107051145145c025a00c003002002420750100c4049119501d24039014042107040d080310206140c0404c4503001241e05901951045c0080126100ea6459540c4907964a04100700108042c0d0b02500b030a00044d4887d01d40c1c034071844115000c4203a0301441940840980e141110b031522030040208041001491040100c44580c10582c0510703e040c64500b28511682e5000b4010b042c1181c40d840070403106071158070080d00450300b01c0c2c107401036110101145504c61718002c3d420b9108000c600d0010440c2e03052040c40707209008210401441e2740 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 978476016 1250 978474766 978474823
    0xd0222060801230f03100c0216030b01050f04020405180103031d13110c010e030304021f0c11130207060b0405010e0105010518040e0d05030405010e06040827041a0301060503 76
    0x41d0104810f030740e000003425841d003081ea1800c1004030a0840c05800200e20f20440b520000e18012240200040311070b42c01c07a0400100b0750b00c1d00d085041d00d5040ea02e030705400d0b8902d00414044c2c400e66001a4008221480c7c40300030005040d0040c2c180c2e44681c0e5403240071722038058103001d12105048090351100307510820100c0c1e0440c552001c0212603400403854100030751031382c00508581e90f0703012903030460304000f08100440c902150726482089025001c0986103051500080440b0740c801c0c0b0042c16840016204200e51307071907074008000c22580701c0302555a640c1500c2c2c1400a04100c4c0703044e5000d20300307050001c146203030401d0303650b4140ca006a6403a030130014400c08512014a5086901d45c119688a0f1341ca078120406004204c0e0010090f01d0b01c40daa810180781041c00c48140300c1c010040c03500400306202c000390b03480c0100c401045160908900c1d0009003103034142030042000f95254094580b01e886103030f40c80400c55113503046808034003c100ca207648406068072180c0503180d420b181e1102c80200c0c40d12 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 978477266 1250 978476016 978476069
    0x1615050d06090f0e160303020601060c03050d06090b0f0d0203280206210703110a03020307021f0c1d150304150f060306110a080415020d0222060801 65
    0x80201400041078065503091040c0032a8003003c1180c40c0b00c1d407540d0000c4402c020030000b080040c0008a0440981e0303103540c0b40252154018000c18003042201c81100e014907118070300352542c070b611001c0100025650740a10f44000e003150030341d0a016681c11403e070b200d94038204140f01c07200c031b40241c0070700100102c84000b14030b241200c060480e00d00600d1400c10015032110b1014100104504c6c2005001c104400308030301010301c00420301c8041605080c80007403000440d90035102244104d050150701c1e600d54041c260304006440701c2c10a080c6040750021004401c00d90099042026103407240508603c83d100d00e80004841003402c0c41d0808002c2076034101e212001801164001d01480d0000c10b0355150510180989009809158486440301d1082c0117004080c032606142c61111007000340341403401800074200c00360052028004440585100b0f174082c005404568040e01c1030a021992050304110381d03145120b8180300c980582d00400000300d880f501904449060380c20421000c210620290203030b80d403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 978478516 1250 978477266 978477277
    0x9010b161506031112071a0c0609030405010905030f0a030c08311406250c030605010f0b0a0c030818100504060501121e15062301020615120c12060108161505 69
    0x106404104600746201c230040c0a840d01a15aa030041c43c0d0b181e1400000400c840b08940203a84250001800703d03040510000c2ca07031080d5540750601c1d0000e121103040024040c0621504051006820b50491140503240e000140202804580c282540d640782c00d01080c2020105243e6500200c04004210024114000e05094134844244000703408e011a0346203014400f984e03204940c440d459400511401510fa60702c0b0015003c203125450030722800020040804058010103001e101d402c40214082036500100c404030115544c00f210a00c5070b10a10f402c3c010402120150f440c00d1600b070000c1021601451400009600201300c1401c0d010841b502c1d640c100d10034001200c1d0b011151101000424490007010020800c400428011155040c5841c274000b2030310314102d0441d041781c4208031903241c1c44651141038a070305032003d00b403004203a0215490203407000c004550040d5609d0b910304c184c00f00010068184c6168005032016008811108c110124440c0a10398003002c0304141c1341040c0c2d02c41d002800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 978479766 1250 978478516 978478559
    0xb09030408030a0f02010606170402010e12010c0c20030309060a0909051303020c1027030512091005090d080d090f05010515060909010b16150603111207 67
    0x9160507551422580385030300009004020408a615140e20550203102e500010141c50034026064154000072001c0c1c2d5200404c020306000070b441c031131101626507084c46010040040300030070400c0c4141c3d0b00501541c144020072214841c2c20402c881e5248244072b00c4c0c50031030030701500850501800804008180c0c0000e0a40d6080055120700000c40c3c0d900c501505009071309072004201030a1140c1402400d15608420580c0180010440f6003003143c0e1014a0030304c4450504101b480c03c14051114080c0f110391340d80050301500c5482c003003585114410700100081074048402d1072031a44d202c40c0c1076803680030341021103a1018200e219980412a510003d00d132402e280b40e00051000119610144c5130700240600f551140e55440800c501548107602402d1360690864066007000b02480015051000500401e10310a07404104502400c040200302240c20b54001101410405500341000c02805544810f40b105512001c900a860620140000800e20220040d2240c1e074204a0078140d0700040007842c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 978481016 1250 978479766 978479773
    0x15050d02030c013617151801020f0403061a090f0c07140609010f0e0703170c01090c0806060102070510020604030f02100204060e0906030f03190c0204020304030c0209070305130b09 79
    0x441d40611450104072075590711222080b1241c18001d02c0c0c4030340340300360544c0180e1b58071000291060b000c54000c403560155210717107442c2d9100700d140402806800b9540e03001c80c5140001c00c01004000654010301e441500329060030300030903282e03010890300d03120a45001030102000300c01319101d41c05840040500c03500801000219441072103205242c42411a41088183d55854210822800d00d00401c600101c0b900c004208090a54641810050294904031001c05001942d000b11010a4100711055a003203c070200c0030310380c0d421116443ea40111303040307801801500000b042519000b0b0300384201c00c403181e008101c0340d503496400707541c1940340031100c00641c8100a04852011240d000900c040c08499031140d54009414090120112021b0820f0303100f60010700d0b404140d101c0000695120002c220f5050400d0101600d041c0c07001d6007a4038020350000e0001042005154000e220880d09a00c01c0e103d00801e644c076020114112403095686042980c21295441b0104107078000035900003400b142035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 978482266 1250 978481016 978481067
    0xb030103290a020a08010e06130911030a050f0601061713060b030615041a061e0405181e06090703020706020d1406190612110c1015050d02030c01 64
    0x70800601c04665034201c20b03400294074031940d03610070b40d024018800d000250480d0304002000038000da000200308a0f4166035001e280c828000009080c286030540641a81d00c0f40f055410405d4a0b000140501c44461146400004656105550440c090500302007190850745851480040c3c0f1041da4400b80e034004c2d146c41c0d80c2c0c803c03942d041c000603020341c0352621040590000c480a20040d51070640410030011800c4641d403802e501c802c412580b0403a000c0500c8c48160003150300050b158000c0b030700a61b0300b05064540c141142c1e40b0703500032540281c102d1035a00c0c80411b8190040c44ca414012121560031511000205504c103000303402612103c0e10407032025041030302041404007110346020380d01b20790501070014006035051108181c0344040d01644c2c04c6134941d003441c1c0083c0c500248a49419801c958030086401121b17401c6043e5007070341400100380c0c0d04480e1280045406001c0307900010642256208002416162044106441c15806800713020344080321401510711002940b511034203520304015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 978483516 1250 978482266 978482333
    0x1d04050c03011a040b07082b020d110c07181118040501080a111903061a040b0a08100507030e03040303081501080603062a040906090f05010b030103 65
    0x140a1046203010310903a125854002c2d4008495a4505030070901d410401060001d000c0803004c80c0e80241e00119001d40d030301c0c0104101820100c90940d112013030145005a0081072519400400b04054645000d0103c81c03599134501d40303a0b228200c40d65025910200c0b08128500c41c01190f15042a20703a0400a4081d4080700d03070882c154045608078215840d100415030040c81d01d4422640541101ca0042098503010383e52411080040448140320310500f6840303002c80c0d000140804061503100d40240048186051890340005080d0901d511942c10900741d15240e08000d80d0342070455007600014181a00076400300030080a002c0c003003008060300e452134015030010400041004502ca651400c0043c030304010080d1035500080c40207810481c9250034801255000580150045001c030707a4a02074804080f1071140e2820020030707a041440d004500002c0d80c0c10164441c408075490000c00717110510750191a44200c079424050f95645140501c010320224100c2404027040070005034560058100310070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 978484766 1250 978483516 978483521
    0xa0b0604030501020405030f0a0f06091110020303070809191e0f0b010306110f0909150405010602072d0b1e1911010e0d050904060f060507030206091c1d04 68
    0xc000ba00c10340c0d00010200000d00f01049251002c1c551030003c3d0201e48125550600c1100c600c910241400d40c076504203005001d40703030780c488400e0f0200034016990000c030100041e4032604215155030106404100203034400c0404520143c2101806180e00c544090f02e5407015502803c40d41070044a0040c04401c80001300844d5075801582e00600c50b240c407540c51b5292a8094902e0042000d11540050041c41103520009041d1078080e941190400d20b0740d079441ca01d09640751705158004d588a0704240c000111542c0101e89036081c0d41c1d04c0028103640f6001c038101c50a030380007000c1000d00f51034500b0604004080341c540141c107610410440c0f010600490310031a8000d0740018102e198990b500d901d4407035101e50414001c0d155017139458003d10441e130590005a448000003010607003845400200200e065803658072400150601003c220a000d40721b0500405580117014200c01601c1501e0101d410a003000602c1e0700c2d40c08480d040602200c60341c080c00c85a205905050398105030a40f4108030300c03a6903070f0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 978486016 1250 978484766 978484769
    0x2e081002030423120f071a0a060614040608061809010b040b010318060b060c06090a0b070915140c030313060b0d15091e290105030c090a0b0604 63
    0x5100160322030030310b0308081c807800c242d950400614070151481c3c3e0354900300119240701c114075241142602c1d070200d641d10071254820540e0080c4a40300c0d5044e03c41c91210f01c24280c0b0302540c2c10100070070416807a02d030251001c56124203c5000c1550a1108016461288440a40c054070242c20080300600d40484000d030100c058820046c0f9035104c00000c042c500f00740c40b908070100c40034641800840e0010001000102d00e07074901070304084e20340010300d00b140c50301000c64a001150404607899880c043d0340751038854100701d80450b201c00b49d600200710440c0c4500e04080c10b50b007945009002c002140b01003507505250764000c03031120744828002c1103015902840558424040902c0e90b401d40f80c92440c240003210b01c0740c00201e202e448030b826810f01007400c60060740c0910580000008041c1410f08045507c285100400340301c6207180c20707040007000443d0500080041d58440040c40d1500c80c80d0452400090034001c0c0c0d50958442c406038031240c41d00402080e040802c0480000303007072070b444000ca201c9a129 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 978487266 1250 978486016 978486043
    0x120a020a03020d0801051e061b07051e0612041b030605063f0f071805130b0a0b0d05010c0c0c15020606060706020904021201080c0102062e08 62
    0x1560204007403503014041c03030070320700b0709490206000c1d810310b00020529500c80400c505040c03514880d0490382c5e1980e50440d002102c0c155807040740d90007600002551444039001c1d00703015451f4618900300055040550070282840140880d05246003107826003c141401070003a00e80091a8450a55428680a50382c0296000e0b038404600c902d092024803104100d0300901c0d10301c0317070900110591488551554903602c0b050030305400d11100c82103090b007483c00f0f540030001c5496002d0000b00207121000445408080481c542c420b00c0696200300d0200038407401c605010740180d5580f030018029450303540c841c20036980c00402541000030641c40e07040c216100910b0103c003048505240006000040c10050018441030550910a05210100170b40394880540700070f01405001c20032904005041c1c040d076481040c041e100310f440c0c0d048122514814842031291442134011a114490b030740d480440d1003807080c00c6143c25084e900c101c0c45103102c0401c4624040b1002c40c3c02100c008164000d0901031f02845041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 978488516 1250 978487266 978487273
    0x31407270b09040305090f180702010b15191b060c030204140306010f06050306060d0c030501051008071418040906020a1106040c0308030a0f1506030b2709120a02 71
    0x6000200021200c02040040c80b84848000300f0000980c044121410f01005494606101c8100e50105484910300c1c2c50b152904011401048000c941c150f00400442030102c5013004842c02c1e20040c4044c40c450456803101d05182e150300210f40c1ea008403644861801d00300030700310000741a0303116401100c0094100c1000242c0000c3c080005000e42240c5030100081200034240b694035112245030321300601e2007400700303200d00807001501c16a80d0350305544071541c000300d09001a503100c42e002002000c00340652481400c14202e43c003692032207011079a10842054a800d0f000758410702091105800c240f15619080050900c0e41420b51118024642200e00c1102c02685a1070104000307861005e01800701c4405030b11101c100f01c04034401c07801c0c08085a8001d03501c05d5072900d038079481e03602521070919251103c9080200304071103204070a0440d4100c600320f070b904000300d40110080101d8a500c100c0d000d9034140ca04180014507411030040380350400c031900220f50040e1440021411507070070504100c00540c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 978489766 1250 978488516 978488579
    0x60e15071e11030c0a1704080615012001090b0109020301181505040204120b0109020c031b010b040c0c0308010602010501080c0103180c061e080105090a09030201060b130906080606030304031407 85
    0xb0f9803070741b450910350f0b01040030340c102420b11800a6880d4401003111000f04400c20f00c80d0307034a90145521541c3d00f01c8804880c41144d8403041c1403030281c85482c0302100e03012482000060105594803d403410f0b07904944888000c546051402005001d40a041c400400785075000012543e44030301c01000100314840b241c0c003201d101810000c41004059111458141c0104448154408044112480141c40403400c50302442c070041c0d000d004000840074035411624110200003e0354010aa08a4803486503a4030034507030b030704c52070b049003078400030300c200c0d6586d500800c5240d42a6000741c00a000103050f80030b1500c0d0041c1c0507100c101912803268000e03000328280c0d420340921410000701007a1b402089003420f07510740d49420045400c8000052807100c032540d46a00c2c400c2054400e41000008254051800d611241c01c5080c0c41481d0303a05200d840c51035480e01d14005003d0310301284c000e01c0307814000c020b90708041c65602d80c09500007003800d51821502801b240880c0e000c0a0014000d0b18841017204076035042e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 978491016 1250 978489766 978489773
    0x30c32101b0203040509101a1b010e0c0f0d06020328050103021806060705072c0103020a05101b030c0605070314010302040f110304060e15071e11030c0a 67
    0x1980c005148501d102180c0010109103034000085504072281501d810a0603541c0b03c00c1c40110030b0a83e0002c14000220744c82e619000d43d144030240c154011101603500f40e884030058014201c6040c4d8801c178070175400118441070246000402c2100303101001d0448004045140c1d100c030300700e03401220b444a41d8a58552a843c02d179486040301c01900c6644501040350f94116000960310040c43d030b60030080c518484002071003139200d1708241c60503283d0110440d100507403940d041c65040781244402410100003050008486549032860b14100d98024206802d03150412017131091880c1c1e4240d00405100104814606008440d8440d6941600079500d6500e1700e5454a00381c415140040c142c08201400c0001200041100d40002811250f04590004e1400102d5110001800f90b11050aa882801004110070b00245410112040620100759101c2c4203007001e1240105805550560014041c0410301d4141c584c02c4c801c0350340c4042e4904044c040210b42901461550340080005800c942012a202081 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 978492266 1250 978491016 978491021
    0x62c0303130e09060606030403051608161113200c1612061406010219061e060e0615190c020d08130501020111180a032913030c3210 58
    0x46003044a1b030a20718142a2001041401500780d042902c24041004000b00504d0b4401c032001100c0d4a80349800f40400e03070031719a0b41c070910302c01e0741405280741c0c0104650300c036618440c400201a5104d00b203560040036a10305d6500b5080303204003144c10703c511141c1c82290070a03010807a008245100345840c0c01022303032504031f0a130785150014028655080d0705001813a0303000f00d442010594103034140303e403013079140c02c0000240051030341541029400002820820880350080c03800d8801c1c0d80181c1c0d83e280c940005011249680b200c800011103001c1c04032407085e841c044c2d44170803110018a403104520000e44c000803040308880004072401000014031040600750320721380800070300003400200304000c496101d58610342324419158003164681d4000701c00e180e99901190011f190000c00e0307400c0590108440e850b41a440700340c1c02e0030140f01140050045d1005105504006500d80d032203000740c8003165904080c02480540c9140000c48050754a0040060040d040c503150342c0801c003c0c0601340e0010001d804 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 978493516 1250 978492266 978492271
    0xc0b030925120c0317040521031b070819030f080402010206070c240c110724020f0a032a0b0106050c07080304060203070c062c0303130e0906 62
    0x1501c0e0a11800080010714000300412a622032450303076101a01c0b890058180e0080d44c00040800558040d0300221130f00e8080644251141a0342c0340c55038012902d41c1d45078a1814a4141003203a10030403640c07280b81e40241c2c0000c9104500c0e400c8628103603d402183c1e06020404400c40d0300b01c00c06d2808007080c1a4020340c5c4401020310f600b006525810640c00003510390300014403040c00d0165052541041008030420740b51458101603100c840300c1e1003500d00001070448440540002091000c60301e65030f04c40072900b0b80444540007482d0441c5001d041c00584000403002e04002540a800341d004010350051006078807452183e47c0b0401105525501004e000f40155200101713080580e010900080207a51b4003070540e401400c01c01d489a041104251600c05150008480c50001080008071541c001001d0015284a02502d15400707869440c115100c0240504140f10815429808120140000919050f640025081d00d10740304807144040c0040c002ca5110b114424010020400720407010320117980c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 978494766 1250 978493516 978493543
    0x301151806051812060c0f040504050c0301090606170121050303151906080c2802011b0c050a030806010e220609020a17070912080306030106052407020d0c0b0309 71
    0x3450038039020986641c5d041c010004218807100041002c0340f82c1030f06065900604006005000c40c0c9031501c0c501c081d0350030078421703001d05078207080c030200f10349028140803540b680c14082101216841d000717407404c0a035075090a00454840c400352a03000b0800600085100c0d2256900000c0080548014003010f2030044142c050380007407140c0280040b99114510940050440c0e44141c0c85507020b080c40c00c5400040740c8120841304088802a14040d01904080384120625241000a50000000740c1d1a004c0c041340c020442d03080140d5810000340240c80e10754009806140110340703100a000810781e1161200d0200c807001c039246035121504c80c4c003030240402512443c0d4041d4101a00d010b0050f104e54405000c1c058000602000034501c5881040c19400400f0307140391041c913802c1181008001030b4010784415001e07500f0120302045a0400441d001c1005680b1000781140310784490b031018450b00b09484c00c80c3d1000400c0269008140701400440140c0101d0000560700e00701950614900074a6003540c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 978496016 1250 978494766 978494779
    0x6031612141518011a09041404050f0d02150f0a0f051e0606131502010e06040f05150f01060f02010e0a0c0602150c0f1b070602070602101103011518060518 68
    0x10311079614019041c1e1441c0e0303129000240c0321b8100d000024003030141036024000c451284000c010030310000188000f0189046001c2d10040402d615080b40c481d03501c0c9552081080700d280109001c1c0c01e40055003a4030181000000030b40c1528080c40c0ca06803003096078aa20800799036044807032040500d010a03900800c007120600d10700340160b0b050016025840c8038540f824803803ca65100e04500039040103201c510704406445091525140868039106031140540d81845610514040407403031103c00d0b0700840c80e50310854070507031800030f00300e0301000f65490b0f283c119501c480450140100800c191031481d441403006444103410300320300902d440c0c0320103c1070764041c0c52003060040d02492030084400c0300c044d40c264140c0d911201a00105002000c03400400300b4401da0800046140d4081014400c1e501c0c6942514180106c0c80c1c102c80544080001400d00404100010880c48041e403222042c6c2c040c644c10b01106000190b90000e00c505441d5001ca40407c5000454108416442000c041010004c4802 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 978497266 1250 978496016 978496019
    0x30f0624032508030d020d0606021b100309020607120e0d120c0f140c01081806161e0207080706030c0e0904060f15140603161214151801 60
    0xc0d80c1c58107204425040d6944010b40544642d10b0705103001c000d002078000302c07a60782e207444140400942c4000c4503c0c1200b450180b000c01c59038404155071207106803604680124800c001c003004a043d1600100700203140e980d54903000140c0b07507040644203090150384489801c020440c00606440c0c0b400c02036070300c21400701d058540010300741d0210b1092400c0501c4c0200d080715907494000c0406143d00005010400600c2895288900000f500032a003142a42ca40341d181c0c030365010407007000e441c034000740c00c035038002c030001a0000325190401c00c26030009281007a44488251905107070150283d80c40710050708040300038000040304100c4000100140c0c901000b507041076410007010540101c5020b4403804604021909121903604280f88655440c0001c10640541512040d10f842c45e6105d8580700340b048202580a520b030020641c0c3c4034a031072074a41d410010020504031610744822a07604070780d659a030b07460000001444a0a449100203d460403102241d64080108022400818164000c0ca0000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 978498516 1250 978497266 978497269
    0x6110304120809040f02070218010f03060209130519180b010905070c141f050609060904050325050c0a14040b0607020d050c1c0b0106120b030f0624 65
    0x1103804a644218030060302400a10302040300d4442e800c600740c3d0050401410701400301d02c40d4010204107108070303040c407858201d00400e4800081c0901c500415010014009c20218078160010102c5007030041104804118090464040b42ca00791182000040c2007054520080901d10400c000750102e009480c003400a242c1d510308034400140107844c2d0741c948510100342850b016400710140c01d070b40200d200e40440b080c602c50329942c03090520109600e4164100c1520210800c2c46000d00403d8040c048072681d45d1506c0500011640103002114284030400001c907818103180c0700110102d4010408071a001c00d0783c00c16a1900040c505440e2154801c00c1c02040300c41c00e1500d8540b0124010f07078000c980d0035007200c0002c80b00e000740440613401503007808501c8204040481e08903084c88084408040c4444103501004183c00142c4005104001d480018000e42c1e0241c0d04004060100d100701050498100c0042400c0c0808003c0303514551340401e0900c40011220103a2070030f241030003902d82d1111b00c000d10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 978499766 1250 978498516 978498523
    0x1f1e060317030108100207050a0b090d02071e090207051504120f08060a0302010818161509121704090c0f1412180111040608010f090204060c0b0907050d060212010611 73
    0x8140d000740c1c5d540000c122042103000d210b112140c0740c0000044569141054000307440303280040120740180100100400c1c003105080c13600e400200c80c0400004201c0c106000301e8000d5014503401d60300c40c4030726644414980c0c00c0d00c9406104911540a0701010f01070b400d40075010910b148520002d001c09002040800c0c4c80380c00c3d03801c049071b4091800381d4017a11501074500c5240c030b1850b900d584601072005041440c2903044101022500807203010070080d05002001c41c0c1480c002d0241e503044202840340300b40815411212509141c038019181490240d43d1031400089840c01040c00020881400390004074a8104281440c0c81340100482407900070000140c1400010082c850281501c84103e0715000c07030400d41c4480b40040e6000801940d99886e0b000213010f940302413042c1145080a140d002c201d80315940295001c9032099145e00101d0038060740c1d000e01f401802000e01a96201d007400025040d943c81252a845500800005075540211021104040b070142c00078801e000080070031020340070000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 978501016 1250 978499766 978499783
    0x30609060302220f090b040b060102030304020d06020307141b07090608030a03020315030d0207150306060f05030601020a080d06050112180f030e150c100606021f1e060317030108 78
    0x9aa408190b660f030b460402000308144045a0b0350b99140c01003403001c00c1802405c841c020340c0203030010440c9560b80d50049a4038070044800035001010541e401c0c0005074280c001e15000f110074200000200400180034444e90841c9400d1030600035034403846440d0303030b905018007005804100c1060202509002c001680d922500301000201640000015419414907218222504005060304c4c4c3c0210309440080d40c3d0903850107980c104001c00c04a034500c95000c1e10030724080b1061030b11481200341010406403142c1c0c1006107058154000c00c1041e0001504603001031a42d0700c0080400160941030500052100d00b0880301c4407103561070102442061507190f070000307002030340c0912241c00b84082c500e0110368501002d18042c0e08040c0075a001206c1840d010050120140b6800c1143d500a444240c103406480d030511802016030440e1034030b81d003050030114000d850400002c50200d0540e100340045208800314010709145c0130780e154024800c106e18406400b00118001040314159418503d1345500c91480c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 978502266 1250 978501016 978501049
    0x109060e030c0402070c060f020d0806010c08090a030501020406261f0b04030f0314070b07080612070b0322030509040b0a21110103060605030a15051f030609060302 72
    0x411118448075039040000790545500504155241d62051a100c82c800d540d90041ca00891140203040c6010f61001842c10111107060391880c1c0c81c1c0d11403c0c015070340d1a08401d0706444c2c004c000c2000c551583c0ba001481c1c401184101c0c0016a00d0f4035201d0000c16014080324503a100b80c149030101e81500b040350060a07004501210601c04c40e591440c024042a80035034041c020300000800c001082c01f03404682078100d10701944030030003000801e10700110300d4070500d4001417110700c03000d02185d0281d1141c2c1a6984c0000058400001c0062401420349440307103550150580039000000c2001905414040c0f014005410302546040185075501800d64018a051140115907410115059554480906008000807081071040c205041d15000714a12003038410755628001d6540a500d85d4481d12507001110141d503202415529900c00c560050030026a0034040c0e02c0c0c0d60800800c00d40e4507418009000e820f00703084595402031120014007501c0c41036021120252070000100050b03103602c242c900600d01c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 978503516 1250 978502266 978502277
    0x3090609060215090f0d030605270423100e151e0a0207120f03140723130f0810021c0e070806011d060d050d050a0e0303030703061404060302010906 65
    0x210140064a03205e1a1481c03081903100795101d4204141c1c155000c0c2c2c01b034a4090325540c40c500003c044c55001140c9218969a2000c00c2c200002e000c145c5d07105001d50030359900d040e01038000105801c0d4901e090803080d0300e000d40a82d603c0e000031501a04001020b007680d140600014285401410003000d82c1c002001c2002e5403c00b079001801807640c1c1d5040f900100c1d44519600c1c9444055100109082d90400e107650102c2c0ca404040352100701050116403155880c1d65800060440c00e04040044060f6482c9a9010341130a114480c030400c0d01c148004090301888054004051070030802603e0601c0e4401d014218910411030200102c030412200c4501c010320400202d190a4550106490702c4032561001d10140100320000c1030000c030461156001c0b00b40000d007401161540e10070440c034054403c0005000d03500c810556070300c082c050000b610709003c42d400d0014002101a001c2070035580704aa0040019503215028004044581098602c0308426201040345d03a085500182c9541090f010b500306001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 978504766 1250 978503516 978503521
    0x1e13020a0302100504030c0635060d0609020307120201080709050d022718070f21051203070e0a082d031303110114071509150e060403090609060215 65
    0x84c0074030121001160f0184c04076100d00d40c1c46ca001400c58242103ca40e01e03003260741c1600860003080c4110f80762495810021400240c60716001c0152666010700304440c1603403281a040b002d650244003010040002d40d83d007400700c14040c0700062214400070b1084c0309004007503405003c0b948620048100d41076055840d0245542c0182c42c156020006034103880a801d402000c2058031020404800910081c85045a403155103801e0303c80940482401a84003d400d8003203e161020100764829407000d000e00c0540300d80c06011030320b02c60180e108403081c0f40840c0f00e0002190881c14440010401800b186000d850301420722400e514040400c5440a03010000100e0100d40324803041c0102c59a00307206d2404003031042c0e034a181100d0f103001114940d9001c00c804250856881007840c044034051365000740b441c0d0f483d08404050303100a00c4e02401c01e803500b4005480c0c00303c40804a20a0f1145000384a004004500d46440d00800702502e50300640c0410814034420800b20380c0000340c0303880401c0015079000007507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 978506016 1250 978504766 978504799
    0x5090409020301020a0917011416090b0d060f0510050a1409120f15130f0804050a120c050307080a080d2421020a05010309030e04051e13020a0302 64
    0x1480c8020300607615500c0010b0300c904403900004a4811510080d0b4014126458614032608980e03c901100c2e00c400c003444e0000f121000d000700400307a54255418502c3d002074032440001002d4000d88042d01e00a60745010900160310f05501d07c10040c01c04456840c450750140c04010f001c0c0c055010610117008040d130300c01500020000c151480400003401f01c0c1c0000d803410400c1e0b80d5600711212541003c1c0601a16101001e200f4603a4078866059460b001c2800c006a50341c249000c00c2120042d00c948200f44804a181e0384e4500410005000032a070349503c68069041c25520b401c00395200ba03110354400401048103d00116201600c90341254145444140d165001c80103048004074140360341806028407254a0701105580c02030b14a844004d401a01900225050040042e00d0195100a00320020890b13580300c1c1d005409007901ca464100d100c416042c010400b41c0d03d09a42070700300c1c1201286030070b10304003000baa81580016495100303152201c458000c55628105804068020341d0707080581c5858 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 978507266 1250 978506016 978506021
    0x71d100e0d080d2301050a030b0901060b030c04090c022805100903180603060608043306050f2403072a0218070207090b040f091419050706050904 64
    0x40503049000c1c40d40e981d9000309210010300c3e404007100411902c1c6604d40414202c8008135a040c0c6002505503c80c150a44d200c0150008008100b55401d41d222080400d61069a50255008018241056444608145080046c0d03a41100070b401158413182508030651003204031600344c45400303c01034001d000700d03082103810b00c41c0950309180010700740340091080552100f8881c5070b81034a02071040220751568001c900b500d0b09807142c50700280842010901090740d18055542e8102c20303505400b950140900902182d814403409010400ea4032201007282d414009042c1d8001da400303c80b410101e080560603014607000751790800c01d44038004800189814041c00c4110210705d042c8581145861044100000c0e042020000303d004880d1a07034011034566100365603070700447c0c80f0380140125a041c51060002045240b250991180d01c404c59982d04c0d18140c4290981c05010740c010306c0c8240121114180b4100441003284d803100354990f082e1001c070343c1c085869010f4072514505580e5500354140014007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 978508516 1250 978507266 978507289
    0x3020c030c03041409010305100221041208011a030c0c071a03190606021c03150602010e1204060f0522080625021908040b12071d100e 59
    0x2a8400001c10384010700000010f0011915855040343e501262002030103403440081c80000c2c070617442108050454035154003d0035000c101480c491480307003828400e8180345201036900b641c5460b518600300401d26841004113014100c4410812090300c100c4085801d076100081c8080d62126011070035159030b03c010b000620041855080307440e101c8540200341ca403161701c183c03011029180c001d51341240000403170190304100c45158000c0d000c0c01c10a88003030211062105100000c06503545414040030b405094907002900c101d0780000f8480b0b0013040c800c2e00c0c00145458005407080e041c44100034882d031040d0003132034201080c980285c841c0c55131803809040107030541086a1401c1900d901044000c400070340305224943c811003d10303001e100b01c5115000480000341002c016008210000c3c5ca566200d402d207a059441140d80902e001c0e5501c2255030b068001100c58104581e0080034454171130b07407151200b2981c0c0e2081e8441710500b1103940c0040c0c02d80f610f10403104244210442c00b215980d071030040180c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 978509766 1250 978508516 978508537
    0x7110c12073c0e0a051e01080d1d0901030f14240a06030339061d1504030e0303091801050109170705121e0601150809060601050a0302 59
    0x155000c00e01404440c1c110194070300c0e6503509000d0b42010074030950181c5040100c1c2d103d030b148040161903100510f00542401041c0840e420120032600340545140906c00317000f4140e1102404c001c92403680014560301e08031800507001c00c001400e00b8003a6940130b20081c1140c0d07005400d14240c0d00e6030301d0042d50609580603000800e000d8900031440b94070038410821800d040003035081d0f085548860001003100c0c0c140c0006400101003030350704003403819500018408881308400001240015031140e440c0f002060a0882e225601c4211000320741c0d4041c01182041c0914102504840880300030a044159005001031f003081011101c90341d032510184115070b5166070180c0703a03420005000e0341c07205058000b8800c49001074a03104000410103121000b2600ca00300c3c0740054074883d4903001c02c010a2004241c5040d189004841e03009025410f1402600814081e03100603082541c500809070020a44001c001000d0041c00d004011f12000c011511036030200342402c0c02d13034450800e00411070007802541c4640c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 978511016 1250 978509766 978509789
    0xc0906080a0614090604020f0607020a1e0602030c0d0e01030b060703080f0601030207020a23090a0b040f0b280b1201090506060a050a0e010302070f0f020907110c1207 73
    0x4141204081507025001c0e02900d0240040600c00d42c2c003410703a24040310000020741058001c41c0040c030703182228100342c1c0c100810650170b265040c2c0016a4a954a600170101e080c08040c80c20580304a00200c98020046800511300b0401c0300001140c484040140c1c02007040100c003041e188580c0250301034400c00c0c8010b4021034581a40385030280a145003507070b41d14205202c60300003481c10f61080c002c40e50401d074040c002441140c0f030b00e0101c81c0c140c1341d561040400440c1c00d44030048245c49146a5902c112904240802c14482c01814407040f114440b6100344c165003004000021601e507100400c003100d000d0200810092200c0f11110f400700d60680201303202c42c500044001c1034008082505043e00d90f250020840c40e1a800204038080c801c14102c0800724030103104a03075142d030086403107d81e40799040c1809481d060150383c48510350042c0d44006c8580d1240c0c202440305600b4400c1c84250f01082c20705014147c1d81448045640c2c400d500e0b0041c170704c05d515901c0250192801800100001e085141d02c0c1e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 978512266 1250 978511016 978511019
    0x70503122a06060307090c050f1b0a0507031e08070803090106090e01060812130b030a0b030109060c030b12120a0c0804060e030d02030f030f070c0f1b0905040803060d0c0906 76
    0x70070b80328807041d03a00900c80c0c40b41c0c10001c03c60140c1441154a00050b40c0c4070b607882c200da0115255284e8106c0b0182c0440c42050054001c80400240440054a449200038102c900d055150555040034641081c0030101a500038480004119508031806190803250031b41d01c95551125140c05042d40f9046440941d0800603142005441500309000365a0502c0954036101c606101251160207501400d101c08912914208600b0724590015a04069201400b06031142c900c0042400c1d1505c451b000c464160361340b010048000d5251003080e0000c4411600c03100100b005040306039451541521940d0089000150032030841c3c007d03403060201690210035035841d0342e55490054000d940076a407080c040e00652101600441c4003000b150544507105442c1401d64480c114403240700403000b003c16050007040c0b1400c00201d4840800c404a0b41d2003400300c403803c01c1c01d08000a005003496402100c1d100e0409040c00000303035141058030362096041d54580c58490207428800e02c141c0c402d40c40500a145407510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 978513516 1250 978512266 978512347
    0xe1c05090f01020c061207140c060f010e1506091309150e12040905040213020c0c0a05041103010e15090f09060c160212100c020a02030d0207050312 65
    0x58200c69900311551500321103048016621001c540d41140c2d400b020810100d8101038004c12a0b03608400380e07142c1115960082c40d103961582e0b2205988034031075440a020440200c1c0c61500981c09005d54403a8030f08079007454403202d240d078035908060921911021a08210070745820780358401c900368071001801102c010742800070b170400c0c200200c07403900ca040120b180d81d400400070710f440511544850b201c2c6001c0c901000d940003080c0141c07003240d2250b001c4041c00b85003136844c00501444401c890242c103019080a0810506d100c107680503e020724102642d1400600111041d039044915141d0700501d541c0d80e0304000090348072038207500703a4081d4500040c00f040054500d4464030880300c420032610280c840d1800c0030b1860144042c490b81004005480318010f003000c1080d03c0d11442d052086801c2c2e410245040340551360040854170040e40008014812740c50100180003e0104600181035407074240340c0480d8550503c40160100c004000038016031211000300c1281110341c0545500c2003600d08000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 978514766 1250 978513516 978513527
    0x10f0c09080d0906080a0207050a06140a060509010b07030e03070b04060203070309050f0d23030a02010b13050408030112110d03052d1801090302031506012d030e1c 72
    0x10000544189000b85403801d02400c1e00d8010340300c00740c5071040140da0340301e04540a580310364400c84007401200d0801d030000b001402030b11400e407000002e00d10039281407004002100c0c8640e201d103100d4402a4010030115203ca021034007003980520b005641025040080791900340c0503404249039100000300001c150b40c0c0800a8040c152180d600d2202c0380e665002001018140740c4103c5074010b5011155900142d50024180e203000e81030351001442e0881000c003603065400c01441100542d445010142440c600248407454518271000201318505180d00c80c80581e00050041d100c0c1038400c0044c0750240080c2d04088542c06d00000d00802e16800300e880c00a040303400501100c5183c2495030400f140300000d14220100d040c0b501100f80d82031108400a00d001d94401104060501c102c03410040b003d42c405101c21885501401e10f5501582494000140080c9006440c402964120440c031f10342c2c88000710340c0040d088001d2402003281c0049210050400f58800800c02030803115032901803d10303402c170 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 978516016 1250 978514766 978514769
    0x503010e0703060b04170a0c0801050601020d020613060903170103080d110703121109030109060203270c09040c260c0d0c0513090503070f05100614040905010f0c09 72
    0x5800c40309844001c4140c09540090040314080c003014070084c07100c00c1e0b6443c0403d52000e001c40481e25007072069210b40e104140150490301c1c680e510b80003000000c0d60108100400800c1510007030000f4a071421020200801300d030002006030780c6070f03900c01c018980324000c00703000c80f8002c3c1c000c0d02c01c9584d20320b0700e6030b51980300703000c903a8000d41094203464210340d80c0700a8441580c4c041d16600881d280940080300144008114504140b00030b02c00700a103510240316298040341b003940c00503501d003440e1602180072420814190107071b441080d110441c01201240060204106641c0c0c142c80d0b8580b4680656031205541120b0401d1186444201c5a1506030401c502d500103242d064030042c000d40b00511404c400c5030003001e0030888109000308154201300d41c902ca105801c1355000034025400760380e1941180d100c0c41041c2d4646072519180414884180f103203061007901d031901042220b207456580b0515000785c54809200f2071303a4031103040a11a0a40154810100c0104100038509000e0780242940c1403d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 978517266 1250 978516016 978516029
    0x31a010e010e041208091603060605031009240b130b01081f050d050102070b0c041701060f050f01120615181a0a1806030506090702012c0a12050301 65
    0xc000001e800301d81801c0701d0f40220780084180e6011041840e054521170f1010702a844c0302d2180584041307002142032080f01c09144140300104009103040205851300030b0309013602501303502d011010400201065105042c5034440282a61a414404c00000043c02c10a500360303048a010030070521041140c0d4401e000c089002d0f00c0e118041d84417025442e9044040184410400000b5030b0180428a010303040d00310711501c10400903160159660340c601c03181d0303401c1d00c070a0300341180820f050000002d290340141303003404000020004c0e00e20700004c003207240010348103144c00341824080f9100309074420700300c1e104800c3c0d9865060016070381d544004241e140c4500c4d4035800040c444480302518151040058080350700e10811010a45610040c41034950f11440210042c000e8140e0070700200b0b80c42014040c020205030320001620314290050141ea00e800804813011a45089042902144580320726440001d120503154900350401c8206031500002000141503c504205405107030b0b90302c00b0086040c0d601 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 978518516 1250 978517266 978517289
    0x10b0403031b02010203041a091504060207120305030c0d180809040b0303090306012c010b0418020c0601170a0f0501050603071205070506130909030c050606010203160b090106031a01 80
    0x201203001010703061042c00024010381003088100b1000500030f20300d0215844540c0d8852514034070300000341e55100152000d05105002040c104081c40c0c040c00180c1c01042245c03008000c544083c3c2e0003e2551000070036454034448045194030703840b00c1d1540108051000c105298040da00b06041c108051740100d030304070b0321542c180458002030b03082c04004d8404041c4050010500f80e42072440030300c00100b0b0131100d04403042d21054414082c0f48540f000038000c0c2201074801d40d881d070602403d141640744082c059516035004010850a6400c0001c03598110b4070b00041c211011110041d5990400105440c06495640c4002c244030070b000b01035002900624044040781c00b440d942d90791892130041c0c070300000b03003050704142000c0006050038402888101d01c0714268058440c0c071100034508a50780d012080c0c0c0099081040b100801070200704040e00301c2070034001141400707100c0f0302001d1641140d00c4001d10020180f80852141c40c0c0035040703400919407140c1d849100305200c04a80756004400d01c219082440c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 978519766 1250 978518516 978518537
    0xc04090e15070908070b030417190e1e04150f09051806130b041e05030c120f0a140403052506050f09060a0e061c0f061427010b040303 59
    0x24041c007aa0b10890341c0c61005414170703502c0c1c515010b00c2c5800041060314904c0d100600444000c80d04002000e96241401400003072140c0170308000c2100b1042d51105000784884018010403547da040d055046940460700401d8100d070301d008007a841006940034001d0189034100114070314440b500603a00c40c5075400124903a8104281031941d840b41d0688d640034801c0c680e880c40001103029941c0d03907030380a4015110040c0c202d64550029101c407040c048180c8188e0008a03080601060a2055440d0820842c040c40c0c1400e43e41305420310315200340d62035102403185018070981409951000c0c0e500968014091301d88603822100c1c02c0039031920343c0c03890f02c112070350420700403c03c1c40c09401624108882103032544e00b44a001d070180615540000341400520110224612040c3d44101c000c1188801c8140c02c01807801c2182502d10a5031212004100198240b00061000300d1845d882080c02d0401112800301b1810300305240340806000d0704800074140c41c08000402c0001d8200002c1040701c0c865501d864504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 978521016 1250 978519766 978519781
    0xe010509010b1f17010608070806040b03070b0d110307050c0f030c10050c0c01050c0c07080a0f0b0c0d05070f110d0905241b15070f080c04090e15 64
    0x203a52151096030702c00501007a0488104a00f0a2070318100325500b46020280780ba450030090f8140300760700040000c0d00b5102002001c643c40300c0c1460b0440b1043d0303002d0140280b0342d80000c1d1070704642d000700c2002c507801107480b49100e4201c0d04002c0c1e41c1481000410358a007441e600040156200c40c5c507420941c45810090194030b42e0000850b860070300100e010b44031400050b1080300151402a02c45a00d5040911140c0ca9415080c0306541c0a444040705103580c1d03e02001040b403d04016600440b5136401c011090340100d4044c2091405807640322075103500e60741e40c441400c0d0762800384001c040c0b6030340c1c9404d0809c90482c4c3c000b500030501c0d6844d62551700c0c048444400d0380e070756072002281541c0003d035043c008201074200804070040d182c1031040740d42c041c0000703c0000c140c1504070428142c100041199041544031003840000c50303016001a4401040c07909844c050000880300980f4800c10607400001092041300c01e0540300030300388842e4140301c40b241c881c030700703a5403030300104041010f800b490340118140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 978522266 1250 978521016 978521021
    0x60103240e27012414190803030a0c0e0303130911040317030106020127030e0a0506070803040b100501051c140708070201050901061d04020604032306071d040e0c12010e01050901 78
    0x8880c03246174503030106801c800a10402c034820f220140e204000750b281c0401c900302d0a0026500c1b070038000340005100503100c44010a442442c2d01c00130301a400410000c81c40c5101c40099200340c640d40000071a840030111040300e81449150300180c40080c0e5500d01c800c010102c00021030485003c0c0e4001d000704207401d001103200010544a05075010300d50310350f0800180c080c1150010300e80d0000c1400300c020b40d072500491340e603038002201245d044000000300030400202d003c01036000a9050f214102050404001034401c0c41100e0070400c00303040909800780f090300c0c643c200041c2c0c05910000d207400ca08007048003404966007a9461300c01365003000001901040144654401c448c4070605031b0003100380c00c403110710801d800544140d070880e00411012000c42c401c58078540460182d03088468900489011140c18000301900310000c2280421064228080c610a08401c3d4001190009400421018154603240c180721206030000300c40f5142107002035065008070284580007009200d0340d5a900700e01401c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 978523516 1250 978522266 978522269
    0x80906060a060822150c02010e030c03030c0d0b3a080d02130905070c0507060e0a030209060d150f150806270106090203060103240e270124 61
    0x255000d00060110b0b12800f0b859510900e1400944e004079065071a1008030071017081039454000e03150940704102c150309100d00340c040d400c81800385043c40f801080041d20b07031201030010300644030007281b02641080315910490306034200070039a40042400440250705100050003a03001e90300f220b8865042503c00c2145144850381c0003a100d4a4089950301000094001c1500d80d02c024078034440c045245045403058a010707848a8031806c043e89414a042881c2910a40007441000801460110140c5510380d9002c1a2681103506100c07a80c0c0791f40100e070051314500805030500c8048003c03040515034540c010901c1105829003801044c0c03c03000742c500d80382510320030b468480d0308c108001801c05086c40e00000c5c0a02001d109000c0b02c2a28426050030340e401500400f40c100e9001041c07069035a054800d0b9000340d002000300800b40801c1907006001e4900611440740001608000512482e10030044400006418845520840b0345e040c02c040c002c0c40540c240b010199007110710024030041e448150310 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 978524766 1250 978523516 978523529
    0x10050c0309070315020702120a0204061719030c120306050f0117060f180f090c1005161511030a06060507050703030f02152a18060f1306080906060a 65
    0x151151650b540c80341da01030748131002400954240032150042e41c80f68801c1c260f017299000140b1005100b40100821212107030704c81c9482221840b40701ca6502c1c2c0200d034240d18119240c28440209d40e05040a4443d060052401012402c0c8c501000070540d0b05a84038509442003900e0607910041c90701c0065a255000030068503510f40c41d00c00080307051910001074405a98050720300c15a454881e0b079170b5000d0762003d442d4403005201190030410400f41c10480c04107510022628150407060410000c0e01d0380c0715044144040300e040141c8132081c0400007245920000a4900801c941190b0b180c0010f07041d00151820203045040038800141c0c0d500c00d00581d80303c0e0b908540580301061440e0b03000c2e202c003100c40406405500031840c603203c603c81c3c0c4c420710910030604440c00304207001480280b030700a111b50144810125105220408415880d03031856166800c1c165001d5542d182e001c50202143e0264603580e03801189007510126030280d010002d48e00400c070200468946840b80e80400c2500502e500420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 978526016 1250 978524766 978524773
    0x110c0d09080607171b0403051507080402090f0711030c070303030b0d020109120c03021807020d0212030c0c0f07082514041a090907081603110d02060c03030910050c0309 74
    0x181400c1044d02c1c0e41d8001c2e540c20310407414080c00c590a0039040e00b00381d20a840c140c10040c0ca007542100001b40c2c25500403224034000803649400c3d40054080c80f00178000b070081d41002e1000690480c00b40d19400390220221013200d4945803069181680d40d54203010440002c1e040180650301401c101e5410400294142c6400301c1e614100500c0200408280c00d094030f4505010b040000543c8414200c1c1c080c0c10450140801d4501d400c210280c58860281003c00440d80000c7e0740ea2010305480007560b420090700e1510f40e41d601010942207140400c1020076010034052007400213900302000450006801511142070f04942d1130030351301c200580e001d00c59104140d14181e00e2180d580b42c80c0d4440148001055400c00142910b2008105034030011565036815a01501c07051015620420216041502e90310381c004080d815681d6004603070119000e50b60240c0c504500b440210340c6d03104183e5008031441d404482e100d1428a40103542c0d6180024400445403030030011480700d6625004032840b450902c0d001307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 978527266 1250 978526016 978526037
    0x1082a10031e110d182307081e01050601080c0702060715150602060108010903120e070308030c090109051804030e0a050a17012319110c0d09080607 65
    0x1940a001c0c12860090351a40d6503203050b0a0903100e1080350020b807a0b0b9009241c980700071018410441d1042c042d814a60500f40407842c2c00256801440701d44102c4001d1762850010050714036500e459071641000840d4024550900306043d040c03603041119101110092055844441c015190400142d6550701901340820105025040810082114510440d030020031030703030500090012180b00b84010b005147e200c0c00104039080e41041941c0c0035050501c002c02c50600d6540d00070700300ba82200142e001d09529800c42c20740404060005000464000c50b00c02d90b01d181040c000b40c06548810141400718550010105050070600070815400e911044d05902640b0b4944003a40c21006480096900809003100810a0b460f180d2041e40101200041442d24040f8081c01e94295070702001180c0c504540390381e0044110011110b81c503002008145104a07400e8004c680d40c0c003806564650b20010000015440a0b504000980c10010081a076480d1034807a10380024a494040507152000011410540c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 978528516 1250 978527266 978527299
    0x510080703141c02010b0102010e0123151011210a0e03070305031c050109050606120a27110102060106091a0903010510031703040203150403030f0501082a 68
    0xa00d0050b802898200d98400c03420b191800d420000e18401000140d445004914844d40c090080d420b120008000901038540f81019902c00004940c50419100c000c0d04007040c454030802c3e00d21001c1c000003518403c5c200c0303200701d000350441940c030020803000d210346100b080c008007460f01c03010f00b00c0010418407445c00046100440d20007a0b100b50869140c0a01c000c0040064001c0008003090b07a5411030100052200740701180c01c9400580c031101c0051700300310410150780c0d0b03000c003140c1c0086001401080117403901950240100720403442c100700c2d840e01c00c400d0355181040420749541c41c1d100f55005050116100c00490f2542428418200032940d105400d22807080f40386e02c080c000d40d0302c00c41d0f640d003420802c000007400e41d00141d5104404144200052041c002c02c107200c1c3d050310000a00c00c61941c100390340803a54608015207000140b0710803601050030540306c1d800558010482c50003d00c0556108c4d41e1032511000b0445800c0d00c107018003138914580c0302c0759101195900c18001d1103105041c10710071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 978529766 1250 978528516 978528533
    0x1207050325140a0e0d0b191b0c0f0c140405070c020a09051f03060228020c06070807052a010e01080402120f06090604060b04020309030d150f0902030a0510080703 71
    0x400d584103000c00340054089545445c0c180c40b002a01600f8489a0b50a001a0b240007000420b070b165801103040c903124420a8241852005205416141580c5c1021181c10112013541400c5001800c0e01e04000c030005000d265000c0806e11888101e90803c4030752104402a035079100003803030094102003450000c0003a0103c55010581c00559424080b00804124400f014180c3e4260000c5030020380c0899241c41800f18010001828010405107000f07030004a480650b80301c0928003260b00c0755034002008810005100261280268081c01300e9a06900e1304000078040c04080c0c03c2c011413041000d56122440d07109101d5000103540684601844d62150f40034442c011406569041d918801ca810000b4010000c1013454480d4580d603001e41203d090502c1c100040d00c04008945210b5401401402400c02c004004c5440116806000041030b840e950b0000ea01180c0340e90100070340441c083c0000030007400c030303070000c503c00d5001440410040ea0303020101c4200304510301503094180e1050409100003000b14 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 978531016 1250 978529766 978529777
    0x90c0720030f010e030301090b1c080c0a08180f04060f030209060616030f170708150a0f1509053f01060b04150f08060f06120705032514 60
    0x180546400030342d071010041c00e4440654500c011548000010130251103d4031a004c143e00c001c82d6902c01c11014480c1035108924400c5c406000325400260800780090100131020903903511244031503c4070030300301d581d00d143d008980520780982c01241d201c0c0039030f01d09032180340162590704800219090940d024800c000030000d0032645c01c00c01c00c0001e40f800c83c000d0410400001e200b9aa640320240b40701c1e1004255002b013101144207441c10f00d0a0044030354000c0d0040e540242c40c4142e01c0c5080d1105400507240c00120750001e50450034044011806841c42d000c0c001030320a240c1c0b0f582c0b0049503150144444491007038019955549030540c50707003c0303184c01f200c0a090031050002d64010f800700d1220603802c5920b56070000d24046800501000542440308100ad0310507081c0c2030210b519888607801a2032068000c08052285482c2c3c1c17460642aa610019554000c89003a04034803035151416020f020356100780c482d4203001d0b41200c03010603000c2060b80402c1d0075500a50714030300040e41142d15498540c011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 978532266 1250 978531016 978531019
    0x5070f0e0310050a0207031412010302010c05101505040606020a02060901030c050d020a121d070b03060301061e0801060509040305040605031306141f082a060c010902090c0720 77
    0x101e1000b0701d001c0010f07004040c0611003039803006958281c589000b07050030440c2d508101d080c0700300b8004a00343c0e454195485044903020300740000619860315242c0d0030142c0002080c10814603180041e00000a45000340b02a5801542c2c1008220740700e0030184d82d183c0f00b12000a5006400700010001d9500c0780d0442da84848132400e01e2814548888160010b0760410807250b40041d030303800020b660940b4940a400342c00c000c0d105030842003004c020303004e5455090b1070041160614001001c507002d92000d502400040070f0300b107003007a0405107100310081c6000e011312580115600300700300401e1524040c258103001d5681601d605180500e0454203445039000140005061015504184003088030360086c0035101c1449000d51140d482c110303400142c0d00170a280300d0900d41d04000c1041c469034100184449680d855100d9407400551400c50a40c03070400195001a000a408100d105460f60150005e06015108885080759566640902e90b41400303a14000750480211b40302880c0c0b03560742d084104120410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 978533516 1250 978532266 978532273
    0x9051e0a0503070603050402180f0402010c170703030e0d0f08130215031501121e0f09060e0703031103030f2415040305010608010608060c160c0902190305070f0e03 72
    0x241c450009041058952040001c00e80761001c002c00c61501c0c000c0044403c0a01801e8011030402e00e50308041e000300240000d05000d024103c0c102070118000c910044641000305855071500c0038070f4018080d0105072003281c4a0b00c10b074010702a141d4041d00f0b52203512000da0340c03000001c0e0f56850030f0314180b280e84a403c0c1e070002040009042d00f1a881030056220310184001d8440c5044001b00045c4403e404443e8407400300d26001416140d00020f00030715500144948002c0781c2c28450389002c00090420020007030046d840e00d40310014514001c200c0504036402a101d55104a1b8070803000c5071244030403158082d0f404110700c0024074203800324100e121003c5001981b1180f44030508082a0590000c20310555550004102001000001d0040d5070260132103c0007808000d180000c3d05070740b12800343c0014403c140c081030311000560090b42c40b4100c15008114109225038981c000c40080d80030600658880702c081000d0401a4024008c185c001e04080c1d6420700d00358401d4030700b22102603842821651501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 978534766 1250 978533516 978533519
    0x50d02030a0b0c041a0414010c0203060c09011812031115180a2004110f07020d0213110a0e03010902010c06051b0d0c090602070b0d0531020901050109051e0a 69
    0x1050071451402003d4600a083c0c0d1b01d505000d40c4c20740ca4a120103095041014000842c8010707100030860641041c00c0d2100c2c1e540302c544041c01070300c0b40259007501d0036440400c00c00000d009a0102c41c80700002e0301a4441504514506100948a1921f01d088058906906021500d2204034010503098203001500355200048941d443c0300b0051090388146400b920140c3c00b0590340e282c5441402000309542074100d141c4030a14030681d4030b078000ca900103407007a143c04a210003552076600c1c13004026003080c0400c0085103040c01720f69005811814442c00004c03130303e41c00d038980ca050503c512514250140c446403102403455917510301401005015011030038185030300700451556540131b484241c102d00004103c1c0c2c039101c200141014965844001150f1205030104107681c1400111106403402d2407000c61a940ca5006600c441d0001c8451029442075004910300d0204024800300e080c03078421103008405980e95801119240d0b80d600615500c100b482c03003c41360051070b0180015025001074803203400603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 978536016 1250 978534766 978534779
    0xb070e0f0913110a031716050d08010603111204241d0607210e07050604090b030705030606060a08130b0f10061d06030709030c120c050d02030a0b0c04 66
    0x11007a502d0080440c1030310098410040c415600c10500042501c2d0002d2252842d101c010f01d01c0c200d104100482100020092510082c5080001e0419001411104071507205500141092401d101d0807000a00d4120b40d0002250700d10111118001d8196400030f583c1c8450b218015070580074003840500030003a1800c110205c00780d0045c0c0b0454001c1034400180f0350320003200311781030a4006001c10100880c11000100c1d00b03140b80d68901c52030440e40c3d00050703503040c0003450902e408080d402a81d8001e0010a00241050b550740002e624440d0641c1a2030480c4d640e1024942d0340c18083e22035035070190041c0507001c812131003000d0b1f146d440040e071a21010f6182aa495030710900401b0b40700c1020103030142081051508030060828014140d5180400c3e080350041c06001a0080a03807940340700e4000007020403140c621440026002d95000400e1001e520f5881c1409103a504020700c044400031a24180040c0f1840c01c5003000c20700b01e4010700075150450956880c00079901000b040090301c2101400003007200c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 978537266 1250 978536016 978536029
    0x103090b0106021e0d020604031206090510080c0108010602100905031306031b0804030903020d050c130e010c03060b0f0912030d0504140606210703020d1a01120b070e0f 74
    0x3804030340c000c1e0100c2410290282c009805032400101300340d0061850b44501c41d4009465507101d034141c0350184561007801030840140c8019880b2142e55030401c800d00c0351480c28854041e0480f102101100c41103195070005480e507680074400c107009a008040103a018001d517400c0003030032a01c95000d1b21f14100f542148030302d2040d00c1740c00060000f03980f2417111604803140b00482c0c2c8003040301c2c1400303d040d2038641d0b0000d0442003140030007030056a02c3e01c420b60400c802000044c0070b04d44020b00440b04002400c2d1080002c100f5800b9440e890740c01d00c468660454003d10403a4203889025004038a07045112829000076880004103070342000c0840e0100480840c14805070128490034100855141000c2c01c00008040307190120684a40145040c003131303a961007070700144010782c1c5041c00640046032400d4003410022503500c06508030900c40c108108201c1e42400891034894030014154080c1d0b00c51441c1c20300d40d1460350000300302c029142e0200780ea02e030003001030100c41c187c014440c42c8001e900b007021800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 978538516 1250 978537266 978537269
    0x15060f042009040506091603090201120c0807022406041a090c030a1a100e0a05030a050640080417010921020c041a041b110d090506090103090b01 64
    0x89001d00030900102038500f5018182d04110304889002d03a07420842880c0d0182041c002c90b02050540e1210828116401016400000c40d2004001c000b07003e00c0c803501801241e41152900014010740e0203995640040c88048100e5540039072454540d0f0307503aa0306210050400350b007200d00c2102c4e031035440b191030342d200000350b4411010030208070303100e080c2166044207541003504080b60000f085803c2c9078047e00c9900485010648600c2c110030750b4186000400c1e0890342c0d503003016070180076030b0f600d240c10b00c0000600680102403100580850740d1a14828076100c01d04641c0c03074007210700600010031005410080099496004800003031401d50b840c0011908142514607010459440304055020310906421380000e51680003120045004201002500c4281c00b1198521540c0d0310242d030196040c0d680c040b030f0741910025000300130610303590240022091440b1000c1c00000c03c0c48441885910010903005940d07001a11143d40c201e0800c030801031a904003041c801d0401d07548003803003800314500c02c00090 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 978539766 1250 978538516 978538571
    0x406091a0d15030311010c050f0319050c181206190615120e0601052107030803070903021c0210030e03070c150f0e0303040311150a021501050315060f04 67
    0x181c081d481c0d4500a400c2a48645c1d580300c2c10303450820700b071080c00e42207000c8a407400300c610061a43e030355805803e41c0c1203400f1400035240c43c528200401041e500803000500b000200170b20781080c00c80d07003041000321007440001c486072140c00000108480d1481d0401d443c4010405640100303189445940c0542c0383e0030074004040001706c140d01c1e0012503400d80c1c403807102d02c001c529010380700c0c541c106404950740c0190341c0800520082038202040800d076040c04101701542d0b1003000295282482d05005043d62501e001c2a48a80341c01030700b5200034500b658052100650103008130f038841600078825001043c10240780b8000340010014007000441c0300761400043e05224800d4003d0140c0b00600605018846100c58203005424040b00015075000041c0e81c1201d60048080a0030441600807442d10380d40d078001440d032100041011210990003040320682e0440b00311109041342c0e40c0e0000c2583d595400707035910310380198000210f401400c06060b81210b41c0400390020078020340b25506508906040a15403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 978541016 1250 978539766 978539801
    0x12030c03120b030a02010e030a0b011211010206070c020d031b05060108010501170a06020906120f0a18021f09050a09020903010605040e19020a15120b04020406091a0d 73
    0x15000c150700801c0380c1016128001c0104524504000881d650740912003011b814030054159100d01a5400c100e11030881da4004000d61681d42e640b002440042c40e50041120003111031a0f520505510002e50580b10b19125aa91802502650240700300a800500b0070390420010340002904001c8180d07000c20315521a4000742407944c9007843d00ca08480d01038100752070070001100c1001248200140c55400c1503000040143d07580c80381d00000d07550f4070803d03e034068276603511410091841e189000947c80741c51681018000a5154020706c078602a15120096000e272251543e01e40a0b2075071151400c01051034148102d504d034440e030000e680c8068076440a42000d80010f02021141000e00070710b0014001540d00348140d8500d10081500c589a074001d00e0b4030b1240c415980c0c029992803041000080180310b484d15103100c0b240600511042c401c606050301c5a0400c203220159007010300c01c58007100c00c1607442c0c00ea0103040c41d80070009030100e80800c054a603800d204e000c0b00305006101c0c8086441c4c600f001b1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 978542266 1250 978541016 978541037
    0x100314160e2a090103020f0405031f0c0507020a15110f0d11030a080c0d180602121513020d02070204060e0403021006060509010c080d052a13060c05071203 68
    0x8030704080750705a64010500000951007042c40344003a0680300401001d00300940c403004044a8a0103502a0707a015540c18855000003a50b480040c0e400e06420114002c41840742548412055030349108090000f904074044200030030002071200d440c0c000d4062789262060102c6100000e03545000a80780500384103821031a21445443e8100182c01d10041c8032030040d509004004001426414004000a06100c1e0018503080381441c19407000e412020070350520401c02101d403c0603002508081070311a80ca50200011814040d089000d0300b07070220000f00071100800c100c80101c80650000740c80d81c0041078080c844140165501d0041201620380c20f07034243d49600c3d01d0305000345000142e0b10040440c618017001408810b501a04450b40b0290a0801d520070000924000d0014407a1504141e00320749800140320303006c110340c4840c0c0c00e00c1c42c2e441d0b03c00104d8010f1821000c1d0612a5050301c1300080749007001003001500074074a01c80158050415645030b141d84514207080c08071031000c104d0008203100364 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 978543516 1250 978542266 978542281
    0x6022503091e08030a08130b0103050a0c08030316032c030304021c081e072102100c0815060412080405041107050c130e0d0e0301060e100314160e 64
    0x40700d064600102c203902030396a250419007a01d0f8459624058200722201c400140c22840c80a0060300d81c541c00b0b054400b01d9a502d0038030507110550303000c04440740c40010400040040000055a001d0324400d8000e011212902d4015030051419070740412a40003075000c0d50380b8501d00c00f01c0d50403000451038050340da40e1400d481007086400b6000b039490030140200610302c010600400a82e608840122660454140102c420042d10b009800005258041d42d50280190307400340034288528a5542d002c5980303400001e40031038207440c921060403000405d1400001e8100f100c881d181e15501c0001344c0164501512811030000d404000702d816500c0440002e0300300264145442260710080640a5071400c0510640e83c1649950052800f90304c9003003511440c1c07011503140e911601500a181e001c032000300c0b07140500900f004101441041c429440c1150001d130750501101d0540c03140300703845541c00b085415507582c110f10320181c0c40d4a441e64030442046440307041c4081a0703a005403042c02c0c01e0703d102d440c1044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 978544766 1250 978543516 978543539
    0x2010f0b09130807080f0705030a0206060a270905150403080f1513150f051c0c060507061b05041e0b180415060c151401030602250309 59
    0x2040c00340070303686100030800e804000c28441c020306503101c03226954136001414201410300a201a042c01c1da078001031140208600080200081c660715000d0314038950301c103030410500c5e40c44c91044061218413901050a080c0041800c0350100d219440d001410b0012500d90b145070113000010010400940e405100a0580100c0d91a5000a030290090580e01d411846401d0404100888a0040c50b00585c141258003941e00212288842441c800e8095583c071401450303440010720234903004d1a0301020b0340c44899240e040354a56640c0005040e08214a0301500b19502e60015034181c40302c9940700d2000300140c0104000c11f55803020390b42e85039111810480b00c00880707100e95100c401e076001c2c0c452301003190701d14840c20790342c0651801e94115900c50008010602030190480040d2004010940201e000b40d00714075000c0601d40500d840454200c42c207044c0104480d81044c581005903000d200420003d51590010641c52404000c044000c54100d01c4c0740c00d400403200c1c001c401091301c0780418407071406400d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 978546016 1250 978544766 978544781
    0xf09060303090b0c030d09021809010f06080f07050d0206070f061a10021c0504171b010503011a0a0c0615030203160b03010506090604052e0305010e0f1f0602010f 71
    0x5400c1902e8001c1010f0f003c5e98a100e040c2441101580f510381000640d80d40b501d140d04d80405c0354040107114508160042c0c0241011621540b040c2d150610100703060030006200a5805a620010a481801c2908009070350981d42e00072031344800304002181c002492403070000e114900c640b202085a40c3c0724110070800f01180c800c0207004042400e42c81d88605e50015071001800800010000703030301d40c085021a40c9204c0c903080040d80890780480411001c1002664600342c600c0035281e2043c8030320483c01140c09110a100c0d40101c0503900c5d044580e47c0141c44010980700b509820b10512410090351200192650030104000f803c0c5401e40820a604061080c81c0745156024500c0610314107206441c03030540010b0051a005480c00b0420500584603841200c001e0280180020076642c0324548a140381612100d40c80710120109510380c0d8194020700602d41600d032900d4496400e980c96010031180d207400149203019010204a200c4010702e204400c2001600f40e41d80081031103c0207007074031000c2d00e0f81c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 978547266 1250 978546016 978546029
    0x3020d052803020c10080a050601030e01090b0901110c03040e09030d1b090f06050f0f0d020c0303150f090705180a06050c010509060601091502030d0c09050319020609040f060f0906030309 82
    0x21481014030b0781b54011072103a401802800d000600740c4440c001200104015100300c050341d807810000c04180710a110095100f544030070000e20200c000c070b001e030540380c2c010480003801d15401480103000144074801041e60101900c1c0c02c072802c003400400103d00f0780781e0745890000c1200ba04003130000e617903a01400a201030880001001c521514007032000740648102294001000c00c0807403500d0342e40c448042150743d1800c0b43d0030155222060754001d20384952058a903188040b48c010403480d580d00b003072280c001d1095002008e22005503511801036901c3d5201c82001f10701c2c0701a101d080c3c1d85a58a081840001d420181e035400c0d00c03444810038090840d5009441e900465004001708520b40c2c0e8000343d1107042d07070701003400d8410b00090074205078614003c1c030398010406800c18403e80301040c0e00000c0300c0c04030303802182201c20440c4000300c10a03c298000801030342000d0100047c07101401c0c19080f038108404600030003d40725540ba40900c030003d000da0456410710b900c40c1e0301001855803000416018050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 978548516 1250 978547266 978547279
    0x3070615120312110409020901081b0a1413080705120109020306060105070204021207020609012415090b04080105242103090d050f15010f060f030b130f1505090103020d052803020c 79
    0xbd2500030310203601030804058104043c00782980c0d04042001c00303842511801c0100d00c0025a00d03074403003076190030180c0100340c001c0d143d0040000c03101741c0500450301e1098028000d013036262103038801190540c0c00040c060703800603001c2210481080c030b007100040c441c00748c03507000d0700980c10410300903400d449120000c400c4004c841c03109100d040c06d502c3d55502c01c984a20b4219114071350078080603030b9031702c290798082540000040340024810006401c0740d07209588601c6994550401e41c00c440c04400c01d07811100343c21409150000c521110589080300c90f044650084034140286000040c418160300c175421101600482610500b00f00c2c1088080b8002003610007a82656040280300e64400d1100d1007040c003045038106e203000c4240d010341d04c4640c005c94050020b03c03202480103041006440c2c245081d5180700c0c0340814034465107810222000c00d4500042c1510b42d43d9285800f04003011440304800e072114040c0f088a5605494004c8005200ea0204941d580303901206d818041d05100061061901468 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 978549766 1250 978548516 978548551
    0xc030207021309020d0b09150601050418050702011509320a050a1427030405060a0c0516120605010b041401030f0e07080307061512031211040902090108 67
    0x296070781c0390001c00700002100020f11408900015182d140c0c0031401a0070180002c042c40010a80401d900b841400c1001d400001c50300c0b09030045481c3d104900c28007100d110504d0012191101c550850358000006200200e001c140c6c80b414000e0f0915142e20180ca140d6039030078034844500349040022669150a0038801350700700c900d11544194003000b00380c100600d075147d00103003054445900021082010070310b45910351401442070303250b000c41c4111802d05402c1c2e00c060201c00010000480d4140c9002a2080c0e0801c14041800e4aa410000204580d98058485059440c8041d103040a0082051062010751580641002412164181c2042e091241c0400c02809008100144840581c40a290000340204200016002071101031008003150003103a00004010340004003902425008100c10420740b2440c400c4080c14081c0c40c4522402e0702e44550b403113000301e80030381c0c80010b8840e03060502107070480c02c401611244c8c0d403154003c0040c0a50218900d41ca55030301003005a8004003462009510308c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 978551016 1250 978549766 978549769
    0x2070b0a0203030103030503071106072006042a0b0a1e11060f041e21170f1008010e0102071a061e01030b090c0403050606100804111f0f030c03020702 66
    0x83c071050102500340900000403800c81031080d400c4a100318190401d459280c04e05000061028408610b22a040c0b66407070082032410201040e0300303000c2e40d8030240d0725030216010b00030009100d900c98034000541c01990340c0020b0700070101c1c0c014100c803240e0756112203080c480c1c400c0d5142c09140c182200410441004191251a100014040e42010700d6100c001000d0303986241910700100008401c8840d80090303ca003a0401504034504108000c215103090f4080e02c040b13004456138950040d015000c045488040307071103003600b1184c41d6013000c440046002410f448060443c2035070990b01e0021210303035000800c6800c1c041c002c40301c180346403c100861041814001c00091070001044581502400320100403003250307000340e02c00d111401c3c01611070641c616101256000c1c5820510003591300f4003802000030707081d00e0002a40d0202050719124214642c4031501c411110315104060b4907040400c202080f10001034515030500000101e65843c440d462400303030005d05a0b20604e010f40241170050100302d005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 978552266 1250 978551016 978551023
    0x1106010815160f032a020607030b03030f34050c030615011224030309090c140a030c021f020a0f1d0d060605060f030a0605090c0405010e0d05060a020a02070b0a02 71
    0x6014140c0340208150741c0003401c5840ea2200e0750200c5c091000c100345200c0c001c54000c20081c0c4640680d403420080d1231003250505890b48079002446180c010100b1800c020f440d06014030300ca44030800e041c90b02d5a03203403124000d000103528110644182e4805200030310185002c2045580c400c0380240b448603001c40035400a000e408060a0400580d0744600800c1c0e800c1425031510b13444041c503081010340442e501c0c200a002c0c8038160007040082420801c03210445405003146180011030401c500d4604a11644110000c020601000c0b04501035110305441000c1c521030401c000e400da650006035151070700c14016081c0d1645030402c0742442104141e0401c804605041c20244400c1541d00700c2d040c08451400c03e0050003540c0160754888400b00e5252004503032000038500ca40711400c01006030586400401051a10448908084020070002800203500c6040d4160300345001501c1160700c0c4402e0390315181407460807110000c840b035000c90400c0c92154100010b90043c00302c9448141b0344031941c00025203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 978553516 1250 978552266 978552287
    0x50606010c0b130f1502070c0b040302090408180301020a0f020f0c0622150f08070309020901031101110d030b1905030a0b220b010302042a030b01110601081516 70
    0x40ca208480fa0030040c010680e46440741250b0010003000c6445e07040440c100250090041a691f08100a2011459030003980131030301920740081215810b69100d584101d9550302192110000280105110500340c034240050400c0c40c43c9526102c43c00501610000d2030046845208112903001e41003c5965498420884080304d4a078500000031002d0303800c0e1199001034a80c40340031103c01c0041c4107c1e0741940000c0e2100c0003074040d030726410b594568003400c90542e03001c01406540111a9030040000441001c424405d0301c006041c040c02021864041c24103140381c0804283c04a619403100c808285401424050481b1583c0f8070b911340c42d42403002180d03a44c00e007840000c120503800c13804200101420321181c940f44411400a000c032150600c0c090700d9081c03081c48102d008506007013401c08028021498501e44214907c0c0040c2c5c009007200f400c8001c0c1c41c0c010030080c107000c060403132070240517400d0010320301801c00301005212071f241c00c20509440140040070600403011071424201e04d00c2e4010f02464 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 978554766 1250 978553516 978553531
    0x51509010b0a05072a15140d06032f030a150b120a050106030c14220f140115020321060a0b030103121103040506041802040306050f04050606010c0b 65
    0x54a5100c50001603600b40300c2c601c0c0143c099040b17004130b400c5285074502c2c0e009140c1c25030140c1c085a160f488480191b0001c4212022000c20640301c12001c4e501d00b074001421050300c0203480840e001c1e6594440046004202032803104107900340c00e4069403090300700d25004c48681c080c5c000344070389611500e074241d4020800000d15200c0d900c440b20f80e500d680e0340c1241440c0301c0c5040000e446c058180740c54030703d000f802c441c4000c80b55079411880004030440758005e0742640c42005410300000c9259001c040d540310071001c110080c3c60365101e0682e40600d1282c4169080b40c0003200700000d2a504042d10141c080d007949015104550041100c080190503030380003c201441540d14000d0203441e030200003000d698091300027285405000c0000410b0200c01c01803468030f11182c0e140c0c0d000a20141c02c1064580c801c0b03014a90304208104010014544083c01000b41114007a0005003055282d40d5014141c0d1426140110f100e94503c1c1440144003040c0080c9401000900307007000309802c903544800c81c4010003055803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 978556016 1250 978554766 978554789
    0xa0b032a0f0408031c050c0904050907080304060903031106010311060a050d0c03141b030c0c0a0c0803070201021e06010504020d0f050424140f13050a05030d05150901 73
    0x40e9150600c107072081902100100740d10340e5110070302035680f600710100300100303420030003080340402d42c1d50b104641c0a1040e6600c0c0624007290b4000b800701501000d01800d01521a07001d000a03a040140080e1024040036918901d0251030360a005194141a01501d0103d4102c040104001005454504031a5109843c44da448404400d025a1180511510340310071034180580c0112007549544901040312101c10010000d480b441500d04101840e03032048005950100017245500c0154000341c110040030b0002c5881d08007895a55180703410300340e444209250300200b5010304641c0c042c0501394490450b9824140c4d0462900c003119130b2020184125400703181c1c005100404100b26401041900d0141c50301880755041c24a000200f00c44850300c01030042036403020349540c1c1c040038022150b40c800c3c00b02c5280c0241e103803051350401400002d400850026202041503001480502010008901940c017554841c84450300f45000e944000f4011075008400740012550fa9460010386030550340f2034405c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 978557266 1250 978556016 978556081
    0x6160203031201060c12050c0d180503030c1005060607050c22020c0a020f0f450105090106031e050a0209151b01090f080703050d14060a0b03 62
    0x4281540b24014986034a051940b0003c6086600f0500d80201c4a100b100030640c07200f1220002c4580c0c0c01000040c0086070000314180f4500b034450009603c80100044003003a850342d0301d01c0080d20b5540190b100765015005580e425542103d00d11569501030002d44000e8940a91740e901e44c0d0310b41084001071031081941580c4048505180d03c1c0302140d0b40340d860811176071156090201a0f45440000d0200d22640c0b240c00030360601d0504203055151020090f0070a40c060a904040501c10180c80312891405010a0305c1a000011103071030f0078803071080c1400d02c4232155040030140100310704140c2110043c981401c07a91403070041c503a101d1580b05110ba1600180b0303034543c25290700191040000e860761000c202144078900c401070800074280200b188034543c41c800040b41250b42682c50700340002e0407030700c00f10740c1714004902c4a5000305138144c0309180031482d201e0301000d5101200c1d000c1010800a540940030006581480c5003614050010140e50604615046070100c400c610f43d51507030f52100b401c140c071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 978558516 1250 978557266 978557269
    0x1206030f24090c0102121e0703050c0714060f0705192607020d080d06090f0c02190b061e04060306050106021014071407020303030c0a120212070c050a060e061e06061602 74
    0x12000741c00d8075100d4155235686850b040041c4590860781c1006c0d168080e4820018145a150042c0070003148090000e40c10101c440780900e010780c000c50002c1c6e4650082c20146010300d04c804149070002481007020034a42d2074402100045440385040304c0c04520400c100501c00741e80c030a140e041301c0a500c413a40c80c0c0da0340007480411014001c25800300da401070911035031980c44070580d00500790048050b4201c46803510b000240510fa0004120050b1510f5110800725604d810321402c4400c200c0c408150405040028202003400c0310403581c002e95006584d8401800220740c144005590320035142000d00030031350038500002c16504007802c01c3d014020400d03801000440c11800f0b43d0303840c0360010f058907222318164003c51600d03480740a6401c0001e43c004680140a40c2610036505082c91900c1200c10690783d4090650b4881c03142d220959851060b121801e000400358011245410b01c200094403590034010142c1040101c1a0060b0688142001c00c10106403a01e9080d84d14004e860024000c01c03080c1d500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 978559766 1250 978558516 978558547
    0x6090b09121c080714090d03110312090303040303060b070c050103180602040807051002070b0405040c1229100c0206090a0e010602030a090b040501051206030f24090c010212 76
    0x140740c210659001c500785003043c3e0401d05142c4a0481521100c032810414410840544a9440360540c8029010a6080824414200c0010005403082103d02e421440300341c000399428100c0702041d46520002c100300c20580e05016001c01000503212040c203001041c0c3e182120340a2a004060406548080540407018020320700a09142c1141d000c554960319880e0440c2c44100502807d0300400340540c003040c09520004c0c40d00100ca0f100400e81d41094180340c1040081c0c0180381c0c0c4042040a2410192049155445102c44104030503150809040038200003940c041820070b6001c0c410b0802c06122800a90443c0355441c06070fa0468a06951741c00200000d030924450350882c141400c41c580000c205240c00000400c2c0040141e00c80e00411507486084840b144510b006060000d40c052008a08401d10141d2705604002c00600f0345495008a41032f06103441c90703008881c2c001182024108411800c01c02c40d080e000f901c00030141401c0804440041d643d10001d400ea407548901c002207400407041c040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 978561016 1250 978559766 978559783
    0x501020409110d061502071a0d0608010f0501170d08130503030907080c1504140f100e0f0307080d050307020309190806090d0912050a06050109051006090b0912 70
    0x90100100504541540040c0d08440d00d03c148540c40e00e00c02041904450112175884506503000b080098100aa00341440310300b0401f0850514041c030001c0b22403c4507002c0d01c0041d06042f0000100381a4406081d0180c80c2c069024950100c4510a205000040880c1c00c00ea40c12150078540c8180c2c82d00034a020b0a0b2030070001c081c00c98000031050101510011442404651412080382c0d9040c2a0408004240c0d4400f000d244403114108400c001c0440b0312401030010300001007001c185202c01e48041075a00415541d2680081d032010050708003890f2040d0003449901040d0018865582000f034180e90320f40d1603103440f50074082d0100000b04c0d02d034420401c64602e480b003d0302c4000c645031944184000300c41cac40e0040c211140075090018402250026203819400b1055840d45009890488207400d215022001503c00d4015011064040750407806400c2c0201000310b8005604d103000d288000e1050a1038004c41c0404c1282d42c02004944440800c2d01c1302000c00311407203407241e9222044546443c200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 978562266 1250 978561016 978561029
    0x7210c05160c05130b0a060f181e09090b01050904020a030609050c04050c070f110103060801141501261e090c010905010c080301090e15240f0d0f05010204 68
    0x200001d541001040c11038041102d20075110001000d4480358040c05030340b15920907680040c0040010042d240c4101000b09000da401c0c1070406071085c1c907520f000070f0614075800465818003985e590800b214001070903000182080c907002c1003c02d9140d668880340c03000600c01e180c4030b0350540300450b0544d65044403600003142c0c01101080700c0a01850466140c0000815842c811450800064a110700100803152007070b40c85211456004600e682d0546280701071890f55040503178030200882d18400074071400003041031680d80740f41e46180c2024040080080a00c15904000000d150403082c9601e080d1000e03440000d490285207191f41d03640400101036500750002c032861405d4014000b507140d020640414185082c2d940103030450300e071001903e982040071070050000c0d00400c010803070001a50300c980c210000b04800e8480d640c40e0704038a0440040c0607120341d0327100380d100001414a42c00101c0f0400300184281e812002070400000000c815221807600071705401000b40340c01c81084029070498010306503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 978563516 1250 978562266 978562297
    0x30a06020a110d0f09050603010b0d0504031b030306140102031e0904090b0f061302090f0409060f0e060708071d0f0f03070603061701091212060b03010306050f07210c05 74
    0x14618070040440d410a11104c000c1585040c000c100c0d4181142282c0c1606d81032642c03a45030941036a100e0780200401441a802c1018902d580c20701203980c01c80c9446905c1c066078001c111181406d0f0281c4403490307808001c80c19580f0800422003d508034600d4900d420000c02c1446032240c0100b00840c0c0a491240c6000b0001c8416400304808541b18200076800f4020035218103409100e2500408124401d40490542c40145e400e4051b01f80d151a42188141034482c09000c100d401e44400c65005444c109a600d03030050308103004000700154400d16031a40070407549000d6421200a41c141101001c007041d1040c090035000d02411030584508084080039900901126962980c6030350082c0200b40c10701503c440191007610410808505000c0c1e144000c0e004129903098000c41082070321202c6041c5a904400c0c1e032a110006541468840591b0003140542d80120391807030700043c95005000700404907818041910000f030a803280d443d40300305200c6498140000c03c8405148151401e01994125488003030703 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 978564766 1250 978563516 978563533
    0x60303050301140a0302030330040501090308070801120327090c0e0a0305030d1806020f1218150a0f0612141f020a050909040c03050607020c030a06020a11 68
    0x140d00c00c0046048810070300c1c01c0d4906508020821145442601c00690b05900500c22000c3d8128400b107015224440c1d5820056040451141407003089000c949c181c4050b55201d4156040c180c011821a0384801e10f0b2400c01859030500103104d90000311518003408101e107000003105860100903038040141c10411000382155501d007260300c09044e0115000d00040d40d411814401820300d00b800e601542e82c003c0c069804d1260540003280108600d0701c051091121880d0428042200c501c001c099000e69060019901c0000381c1c1c089a40726000340403504c012484000b026070a800210314071010708110780328400140c0702c800021024290680000c8030080c5000d00000b03283c20480520002644210241000d14040d441219155018140c284644d080704180f0540355100d41d90003803042d00101e0600d00e00b8001588045a00080110350484410b00c1c004003e00c280101000001d40c8044030384000c10052208c040443e45500c0c44007001420590045a06203205014520021404400c00110750004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 978566016 1250 978564766 978564773
    0x303050f0d090c0f0801020711090c04030b0405061e010305030d0c0e03120d06060509010f1101061a0c01060e0606160c030503030c031008070f12060609020310030302070806090d08090f010603 84
    0x302001d00c11342c83c100015030301c005a412010700075140082d4112101e5000070020105016400354010040400d01e0010007011000a4000d0080c600650040d0004e28240c600000000440c01d000c00141c22410083d400400c0080c03400400c90303012100088000c80d80740405d142c25644002d00c7c00003a0b86c14015003c0300c0d904441c2a2001d0510155444d105000c203d547d1a0251000d1260345691400685040c8120301d407140524035150045000800000d907096036900c8a0b2810034044000c50132240740010800d00c07805090240402811145201000604024000420034403418400024108100c3c4a00d4180200414403070000c54014080d00c0eaa490100e40719445a44125000e28103c0030a40d40440c100c400000d001050305e0820640d0403000f420f000040d40400a00181202e01d1a101c1d00046800180e07400918058400001580c03a05401c3d403901a050110681200321168401d0081240d643c1e070005520450f00c045041022494031602481400c040c2c00d00300c01511036003060ba000040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 978567266 1250 978566016 978566033
    0x3170702010c02100b09220501050a020c0c010806060406120f06030f0515090a0f0809030703060209040f0203041a0405030c01320f1503070f1d0f0108070303050f0d09 73
    0x60381e145600740d490600c4540e00c1c0c18115400c445d0001d4003c10365100047c6201c0148101031800d040040d002208501607564141c25a5011200009100e4001c1203000b03a64100b0081c0607038070381090070180841d2418401240ea1405035124090070050050300580c0700c4007007580701d121942010203003441120b4aa061004400c0c011120484c1c040c41540c581003281c21714107800501800c01000a00001c9149480d80e0900408980c403d03140700004200304a032545d0b040015078001c5100e031001503141c1c2c1040040008403444000d2000030ad600420401c40007546000d01c0c403c0500707010b81807a0b00ca80395810002c0c03860203440011105036103003043d103e8202414511030310341c0e840608104108941c081a04450341401034407220f0222001d4000300d00c02c11259141740c800c0300740160445a80c5c6684e0802c2140310030340d40d13120200301ca91040340180601c03181d000c1141d002e202a08910b215515002e600781c3d5031420b52001500300100070440b081840b14100407905850206c02082c003410b050350400343c01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 978568516 1250 978567266 978567281
    0xd08220209090a140a050d0804060204051807081005060702060f1e040e0a062103180e1806130314070f110906010216091107050106080706020c2b0317070201 69
    0x61520305020500130b444400103103615942d03031000161068007100c00d0241c1d8a0600600101c0c1c03266003d110108541c0c850f020300141138007210140d0307e40e03401c0088000e0a00100503007003d075040140f40c024001602c81500b112070907a8140e4089944200c90032030350031580140ca041ca084000d0b0140c0c0c4216030340c00603021308296801e60541d00069155180c0342400c996552048450100c0d84600803940c80b410b84990560303540c000e061004480f440d10400c41c810381180d0b004074940d0307600f007024480c01503000701e8101940702d40c15000b0141070811503d2440b41e4084120001d0402180d411109000101c0c50150345a09501070140d40b458603c0d0f01c0d00041c2c900003880ba082c05a1106e0f80002c8039580700185810600400b1000884002c2c02e1029800107481103152049200d0000c0000f03000080003441503400a224060192041c1400e0a01c000c0c1070100490fa0300307218001400101541407902d040e00000110400c2200c0d9595041f0300d01520b4a181c020840355940040760104040c040d019084001d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 978569766 1250 978568516 978568523
    0x1908070501060f1e0e01120609020402221e17030408010c0c0b090705130e030c0a06060302090705031b0c1c0302041a030f0f19020c011d0d08220209090a 67
    0xd10a0001c1d0700340007040c184030320038440307020903d0004000b0461f002010000c802e00500f03003c00c411082e500401d007a0f0344000c03501040010300740020307200e440040c00004007804030f03003143c00050b4604c14580408401c060081901c4005466009180e07140108110350062480030002e1006110454002e414509d214100362540e0844400061080710003260000139907100a100450440b1000b00703940090602090301e20151008000100554208210020850b8450040410b14be81148117110900c0000b4010301c0070300c882801442440f0040e003100400d9210303e2600d1546410b0300ca584280741c84100d4800700d1584403a001411403140d8980c0040007900e0540c0f51080e0303450410070900b04c0740d12085420004c52985500840d69a040d030b821010b40100003415010340c01ca415030201c2c0708a07440a804640d00d695500b4640350b0031070600c541d108004580f90041c5ca0f82d803050000c0039000b0440240b9a0404820102d130385034482040700001251282c0180400d051407900345980d950b41e46400d01c054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 978571016 1250 978569766 978569789
    0x15060909020a3203040c15050c0307081303021008090106050a03050c10171609170d030506060d06060e090c1e1315050d0f0507021908070501060f 64
    0x1040c0c034003260003241c540381001c0e0380300004840c0040c00d1041c01641ca02c400110304880c0c068620900e0002c03409180101d00079450300026915091810340c00c044d034080b50205002007403002d841e10303140100c162910607402072052507440b0b10301003006842e20880e402c02540002c40c84800c2c4131555004451603c1342c01408000c006098503402004600031141c172000344558058461110359041c068103003c01401a410304000454842c1c402040342c2c403088540d1001c0c65800052140c000ea840b02c520380060048000b280414610780f021240c035009005040d10a00d505c40c00415520f80340d4904076212082c11540411200382c0f1100003c1040380d0420300c0d584684030740c20206002e45074003421164100c071000c2e00a002050004800700709a0084030011241441e0081c0000782d20611940110919440350744071170f5500c414414501c2281c145945600c00c0528103400c101103980c000032880d00e40108c80042100046803032030f00041c1031044c450b0083c602e509044c5c0000d2406ca00344d0311042640da010f00752 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 978572266 1250 978571016 978571019
    0x20901060e0f15040504060303050c0c181f050303030702070801050f01080d0f090b1c1a0913170d0c02070b0c0d030c0e030a0b0a060b03010b07081b01150609 69
    0x22503034454290718156100b1501010800c0310701d080d00c0c0106101c01641d010710306141e81c6900007022243d29a1007580828800286d5254542c03050101c83c0305500e04850204074041408000d501548d03000b4034011107000750702c8043c55181c0c3c42a4001d13005003401400c50b5500d1420400094885a152240c01003c0d82000041582030110501e0b8030706840714000100400700092000b111118443e02c80718092148000000c0354a030186802840a919001540b20254802c0d0001d01c0c222200d503560840c00440c8000380c26015038603081f50700e03040f441c03c42d1601ca9402d03480c140b1060700020b0810800041d00c000030f65160608036500002000d18560302660b804958643d1083d11500c6030030100da503260800f102c903100c118042d03800100e8881003464071000d00c9034401c010900e8207280b402e0555220280b0810007001c1c0ba05800b6646c0030340640b04080381103502d40412810240103a60008280420101d2079401d03c0350010303118529018648028004c01154403103041181040d802400e0001e80c51510 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 978573516 1250 978572266 978572279
    0x20d051020190305071e03020a0806031b0402030901060f0906050102121918180e060612060a0b010c1203140709030302190501060b0d02030603280b060d080309010504020901 76
    0xa8401c0c400045604103840501c0c003108074024900140317a401072007144441108100f955550595a201c0192401a0340720302da1030b400b1744514001891244a907010041130720b03410b000390025884035402a074001d601e90701e4106c070083c00b52074142c1020103015000d0b200010751a03e282c01ca00c00b2a0401c1e002d896000400205e20300da0b40c485c1c1e01610288400e045417802181d03104105c00303480c942d182000180065100d002c10552030541400c0b40c400541c842c180008c0b9443c1c1402529005542194a0880702c004108403944800c0024140346c0c405590f40026805640101c2c0010000c0da0b20244a0245a00f0413001800615807202815003002000e000500260b02961001c402e0b40d0305a002894000c0c04072070510a410001a0221525501c1e480e00041603031045002e48008600e0740c40c0903850789020002d1529000c036450071a01c800d0030728414034400e0246a0841000a50031003810440d0f44e031041d0101d20480d0380440001c03c98040041001036048041d448030f0301840c821914481543d81e079a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 978574766 1250 978573516 978573581
    0x12130311060f0f0f04121a07020304050121180f050d1701090203040219060e1c3f030507080610120c0e15030f0c0406050a0c020d0510 59
    0x5440b00c0c06a0070814201890a00006049080e43c41c0c03004620382a21403086203980e200b184811240300c0c60b280105009521600b8401d640714540740f00079814546400d0000f0f20076141241c0c1a062040603030514242c0d161107030403c05181c2c41c80700c2c0c0075000301d620340b808150401440c50140c81e94000c0311028000e81d03200b14251001001720059248050342882c41110095102800c00c0740d01800484985d2541196144071000910464840091042c141d00c00c0c441c1540c01200b03d41c0c50802c5a0003100000303004401d520400a8000c00300345c0032461582030400f0221054009020114000e0300194141c0f64960022446074035603640c0d812a0382c81e1078040c040d81030008410040490b50350f0825841b083c2c3c2c19440001280c0031813034034101c0b0001d004042020031060010030950350f4000010800d4a0542844058102d1980c2c82c0103032070189026001000c9000f40030400c010480349a00001c15542c500c00b105034400c0d0070ac4260751a0b08503159560340201440000680a200d43c0e8803103160390807014 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 978576016 1250 978574766 978574777
    0x1206050d230d09030212010b1503090705040b0d06050619180b040c0806090a0b040203010e0103030201152301142d042303010615020a0c090903020a141213031106 71
    0x20f84803003880d0750950342041a0241c06120100c480d6507642000052070b903a220b0618a110381c4103046596900b0081ca210741820501d030801da000b1030070000da442e0951140002031003230580200c80000e181e1505000141500c2010740130345040f400d88200801c4882d842d0782c552902002500007013141082000030300003079940080455020941d09000200507040c03000704154044405138002070192072240004080360420b8026040c5400b2000041c820943c0900c204901d68154088180030a4078080c007100c04e0040380102c1c0b142c031071b03504500c1c0050760b402a00c01203400900c00311056126104e143c0740c4c1303c5641c50003103150200d0006010709900800c240c0200c80c15142100544904c1100d240311203061249d21102080c1c1540d602c03c000108400c100c00c4840303814884c3d44c09030401121a0508043d008110303040003084900e84556180020303000601640c01c2303075125106100b00c0207400c0003e400c107034800c45044e500c5080041c0002070300318486400c1c420b89114528000d5450598002d000711402070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 978577266 1250 978576016 978576043
    0xb091c1401051e191506020105090c1503180312070c050607090b041703220e060312030402010813050d020717060c160503040b040b040305100c08071206050d23 70
    0xc83c08207100d01030701100c164881042620108130344403030b003540d81900d450035801500141d42d52401d2050011040c424a000404112a010201442c142607841a81300c00b0303040800c03145803c008000500410b209607482c075141044d191900703142203080a001003000c8641110f2034080c40c00003c902030b001d04240015a210715401500305410010511610207003811140341d28841840390500c5020319a081c040507805105a0340006450700c902c3e20000a0090486440317038110010308000898403005681d409602460405083d4840c06200d992006003030101404601600740c420426540004040c412074061103000c1e1020042c41c0d880d60707200d000035202d6540c1d06500700981140143e41020450381c180c018003d80340342c03a81c0c0b4418000d680e40190300100e95424007082c108180030080c44038010b164200d02041c40b41c809503890082040c50002d1800003442041c05001e61051055440003014010150610007000c849080980c0402807484000b8001c46440400d2072000501103182e050700b205 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 978578516 1250 978577266 978577321
    0x220b1b241803070204020712080106110d08060d0210020309130203220309170705100509030a06020d0f0513060c140a120b040207110406080d090b091c140105 69
    0x26090506041c05601e11080c0c01144000d01c02600540e54510003001e442d48903160b07400c46c1001c03020740504004016803000e400e20440c06080007081c0004102074001080626145029580e0a00003e040305022040603420120070198448015000001886059411949107814001c1d10040d4404e81c40100c480502d03c002c203085003140c2c0648070700001c210a02c00d040045030035032507080e4500d0358001208003611a038800d01e001c02c0103041903640030602c4d0342c13540f82891405140c0400300303654146585009010603400100f4102405980d0322a100e072421541c02030180d42800c0c0f185401003180040251030a500e800c90341310a080c0203c083ca050101c1c05d00d603441c106422588141c68503000c6038104900142c5440e0701354080d0750f441c4001c02030701d0f1007186c2d00c5008215290030300080313418a8200c1010b6520981d0151000f0360842c4550b022202c81613922560340090801140c2c91034003000149000c051501c03107281c20400440072640f514160207000308515501c048260303d448103c2e5508950040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 978579766 1250 978578516 978578521
    0x12100b070c03020f0402091e270f060f0301060602031e04030302060a051504050c0705010c2a1e0b150402040b0703030527240606220b1b24 61
    0x14400c041444d8038200500040c1001804008904521104915204e42c44044003082c6024940f034070b03003d4521200d640509045145422685941e40c078080c1c180300c404c142200c0012000e954602c89142e40310f8000d0004d200242c0e036228065a03035009083c1102c1501c000c911010107940d141806e0382c0841e50158010400342d11041003a02c001d00700981061a0726a072001790020b280c0711801355074040d401e40c1c40c50940d11095070a1003400c444501450404001e4415000a08080d1038200d0002c0200c0400d0000414102481c040c00418100c2c6401d0b0180c030801c01c040020f000141c003401e4403c8070049421751403081b007d01013004904c81d600881c0044802030101c400401c0c0b02e0f0380031913404607142640ae40300c8141e80792884195081c25500c5042507001c01980074980c0c403012500c50079007611f41c00780140c905210f00040d40e20300402518001405402c030b0900714001183c0071200003400c01c0d00302c2c00d903a5454203020000c0f01143c21f8415080e4400c0008900081c050003c0e001070001c03402540640c0c64 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 978581016 1250 978579766 978579769
    0x3060f081c0c06090206040f031a042006070507080d1704030909111c1b020708060106030203190606120506010e0108150d060e06010e060d0b040318090212100b070c0302 74
    0x18101d2880507910f866590f2440340058403148000c0c8080c3c0104c240b003061842c650b00d0400d60b0100c1c00b003603030f140890034139050100084040c0395200d5000c01800da031007008042d14000c10101c1c003822801415500c1510000243c80c000400c2059007038010303541d211030820744860344040011080d00e0040002d000032804008071704407a4401d80b9004441c3c0c0081d0710b000030303440035149040000c0d4000e5203007560381d190950720500100100e55507960300e4005070940c40e05c0c0202c0c1540b00c0d07405120351014180c0000008460880d140b08000b50301007100b17010000d1684600e0000c082d85403051921800e5450000130803140d40c024958082000d40c16901d000c07040d0394000c07804802005100b401c0d50400c03814449000068614041c203005004100300030001d56160072100c9094602c0600ba043c040c1c0941e04010700410300c101c150643c02a0103040010b8131003601c6021100c2802c1e298480101140b01142d8001c40b02548004240141c0c1c1c00301030300907001d496141c264181c1c811894010031103142441d041006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 978582266 1250 978581016 978581027
    0x180b0a031a030105090607110a02030c040b010207050d080c010518101104080d121d1002031513050a0b010e060d0b030a020a1712090f040e07051003060f081c 69
    0x66541c00e200080c1e90001c2002c00d09440341900d000c64243c0124040040041c7d0006025860f515400d0003000e4212a075004240c4500c41c04160702d000e035440340494041c1d41d00800c40000207040c0513120341b007080d181f0b0034110b045420072030001c0341035401c14011483d48070b0400e840d800d0011510b0042c280901c240d04a030402002c0700c2a0a9000710014000080c20f660b091101140450030742d11060b448040541701c4504580281d42c0162a01c1101c080d01002140001040701c100c900391240141e40340c03124099200d034416102c1d4116806030400640c03107040c03130103074000c103000d1240c94005008090040c001510081a8070f482140c01c05814042c0e03401c20030050f00030039105080901500c2d0035209640224904074191341100b1005120020201d80074903040000826414503107415508241c01080000c0182c1e80e0101000d12940d241d00e19141e4510080c44054000c0200400740880201e001401034090078041c4150a107a02c150003000400300004142c9040052112800010032941c2d584150380 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 978583516 1250 978582266 978582281
    0x30314091302031f1a09090a0906020315102a0c0b0a0e03370201031404050c1008040b1605040312210e0c09061519180b0a03 55
    0x80c400034501d400c0c00d4856442c4000c40c000c0041d20714210003561491a00b4155400507401180542d207103031050341010b60301c0c6080e01c40303043c0d0407640030300755440300d10103580a0882001c002c0c203c1031001046c003001d03900816a002410301d040e500084c00039440b24050b10f02e40d17180b441049420b10807084444c143c01080018a801c14801d25100070082d49882c000d031200d411004110010440610b41c00020f89010000c0c100790030511160307884103101d481c2d15281128403240c036010412801900c64011603010750001e6100b018640e16040c4030b8602130502540d030b1000c1d040d00304d0081040c0d207080044035200d510818825500316209180c951204070714000c4c135213081a242c008200044c04080005501c0c2081e610040301daa68500306e0300f44c0b511038998114020b0303100494085140070880f00d018200840c0d010210302c0211456585aa03503e130111300e035030542c401302c0c1540a02c0003c0c610044020b07400342c0c0d1422001590741541400c3c429980c000d08408502485041000502600d454a4460381100d907 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 978584766 1250 978583516 978583519
    0x1030b030c01020d11150405061807060e0411070b07030b09060423151c0501060609030f2d06022505070e0402031006061d01032d1103040c030b1003031409 68
    0x151b07001d0040400e4800d0010540b000c55150700200103002644103055100780802ca43c000c050104c0c00d15110014000d00201801c80b40110b8030b03035044840d02aa804261014941c2004400d122032400402c010014021602058072448401c4045030b514101403041104910400304940d000c11072440e02c2e0b0b0200e52004040292801704200c2d800410303101e00440e154a18588000310400d42c010345083c07420f540c510f410035800c00031044400c00200b151075094902007604400014241101440302c2000860402102440301c00061004410400076034000c007041540005c0c1290290000e20008140c807201d03601c0500141d0045c2e109128070200c5181654200c0d03c024100d615101d280c01720882940c1040c4c0c80880031562006d460100106600201401240246400c1045040210030900fa40e8100100c29044480004482c02400100d90203101c41176a0807003400c3d140d1803c0d18165689030b180340422112800081c01203000e0076140c0000307009483c1d143c2c0350b00c1401006000b02003515000700310010b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 978586016 1250 978584766 978584773
    0x12070b0a110c03011419050f0705070c0e0106110609060402011707270806090a1709130e01020c1b0d0b0619090e120c0d0e030a0b1501030b030c01020d11 67
    0x542d900d507424030035442801054010342400d403400620003050040c2c016a690055802d2008110401c2040d00101d81d209a40d424010f0b2585014203052914410941010003207031544800465103030340182c5840e07101010303a402c451880c3e03618404180c54890070382d0028081031000742d6031400c05d810300c225258080f000d4900b14a2040d490161550310310201c0c4669101d0386c10840c414813640005010071980251404010142c1c041150340d0301e42c0c0d140d01140400b006000105e210300300c030b0740d51100041091031001c109100900120081c0c3d0300030740c000c0c00b00c4001c82c46510b408041140919420140c0340e40000c0461004040b141c581d10310960300203203074503401840410038000013492894400040c1955000000e01000e1220b4050f142001c10500e50008040500c180e40c04404002a151122030141c035203404e0411104001c07a14203802c0080080510f910351f4100904085400443c1c1c041032401d0340c09000c0c071903005d0f05040e07c5a0b2640355060050b0080d050f0103000303078041d480c02d51214504404a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 978587266 1250 978586016 978586033
    0xe0406021b0a0305070c14010f11190501060f060f0509040903200619020c0601140a0b070303020c010c110c0409020621041403090a06320912070b0a11 66
    0x6802d000d00800101c01003840861604188014030382d00c48090f2039103194031000c042110b80081c0008520f1244002044140c0c007541c50203c01c140321103000d600d4504100700802005162550107000280100c406190b01d003e800070b20580700b0890000300070400d803a400e2521070743c00c0c103200240100d09410782c1404100301c080c1070200c0c0c01d28506040e0240c0740000e00b0302070802e014040008144d000c10320640038018040c69421690124860741110000107030706030007000303140100f0601505070f4005007801401280c41028540c05030000d200d9050084020021010341080503628698407105245040e404809001d0300340c1810350002d0388031030004103440d05021168900041e0740880001210041504506100030400c2c0c40d400444048003d1003c0d6080c80701070004210350703180074403940d0100302081440d00211860341c40c013241212500ba80c0c004190058610850b820f0b07200c0310380e26002d514080450400300001159840c180d92100004501d849043c1604540c1c14800d84014107050140c00304 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 978588516 1250 978587266 978587317
    0xc06030203150904030309152319050c07330b01020a12020106030219030f030c060f021b0d0801030809040b0a0e0708010612060509040303050a02071b15090e040602 72
    0x181c64401c5101c0d03a004140c00c082d5103070041c0c9407400d08e80c803010034505003241c500c2207045500030302c145041200d5200b000703940c82c40444c01b1009052440c0c40c0190345880140301e2405582e800401405004842656100c6140840c0c1d44880c0b503c01c024061000104d0800003100046da044600b0050051044440021a03501c0c2ca0051104007640303400543e64640c0c042045040c22000040140001040603031031900d507407500c62912003100d00090401c00182c1c011001c00c1201e0340804030600700c0d000110340703d24408406000c4d80020310200c440314032402c2c0307405118610079a08141666801480b081c10300c1d1061051001514900c40e0955007ca49001d02103a24808140c003d4801d00880d43d0310401540b5120015020800185008005070300380001445542c4603210915049641860002619a030f40450440240501800200f9503d00c080007019038107400c450701c0041d2400b4040d800c1080001c0d29041e10301d2413840c429200c1d110078000010303001c0343c0c5540c0644450242a11001c688154451 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 978589766 1250 978588516 978588529
    0x20f01030f14010611280f0206040e0a1505040c021018060f02120108071217091207030209090a020a030f0602120c0a1d031f020f070524040c0603020315 67
    0xc02240014511020f03000820780104070006c1042c0314000e040d011603207101a0040054040b9902806020082c0798410031501d42e00101e40042c0810321006078035084c44a031110140c01c030b40c59441080c0d10030702004a03071403416219400d43d410f0b01e60014440040340035a1000500401c40d401050384074480f0880001c00c230680036401203440301440060351a1a280d28050508070180c116500980c000e1000780241c0721084244c051254209944d031100082c081102e00461182c3c0d131450b5040314021078a000c5080c0001078100a591003100c104000b9520416103d40d102c010406c06540401003c0040000c54903241a06000c0c5000d102e0242c6420000d100031040300d00c081d140c80b40c0c40e140010b0301c042202c0d0b011340e401460005410342800160050400a0f603204120201c81d43d08840302100c480f4044940c0d8116103556000c680e800d61509072030b040a035191942c0c8841561080c01001540c80b03c020000e05207840359511054184005003003607411402500014281d81410005903120806030b41d801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 978591016 1250 978589766 978589769
    0x20a170112060e0118060b0907090501020a0308100b0f031915091a040c02060f0604050420031c050d0609020c0706110a02090c030403230f07030516032a020f01030f1401 74
    0x2004041100c001544c02c0c0002354500509440800100707400c00d10040c2e0303020900c0c000e00c58051070a00310070f031680c0020311509002a80121440c500018201c1c0c01c408884025610404004183c000d248150b10320410550f42c0140d024010300300d040b4024042c000c203562040080340c1d5214a00740c440c201c2c3c0c10105044844040d46040036902030010864045001071280d94000420f071014031003414107030349090714004c00010f104201200e4074022015078800b08240d40110b1070213185540c0c0c5004180b00501164032a8044202403410820301060b001014001c0310602d20101d402418400d14140d822900f0f01c564403d001028040c004004015980341c080315801000048201030340da042c1440c010b00309411780781d401c00c07207682d520021000192070b5009031040d031024042c85030b0b40c1d904145012141031041070020182070100019400506a00c48241211540380754080b504843d20300314001000c034585580298040e6040d807100101c0c1d4030a0704840c8807190700d0300020450312002c00d0200180c0009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 978592266 1250 978591016 978591023
    0x9010b2b080c01050123030303070c08070c0e0a0e070b3007090e33040f180201030e1b060f07021008330d0c05090703020a170112060e0118 61
    0x183c40046c0421490425041c184200700e0490081390b1300040301003500c81c0002820326041c001c000080d4014000701104581260380e102801800c10340d21600f41c0c01c01c01c001520301070302540c5044130481c0c0842e00051408255075101c01181c0c10540600d01c059001e20342c504500e4800c0a000754078691107013142c0d030024041d05640c2c690401c11410900c2c0040404070040c003114002c984103002141405034540d075043c4c0c240c4d0b10290448a10000c0c000324014120760b603820000146070103180440381c0350399042d40c0e011904c00d0f80d0502013084400c3d800c0d640c401d65101031681c00d02e81211286210320b4168001c19420580300d216500b008002d800058030a00d202070b40c1c00204d6217110070002204444001d116500c0c3c44550190840722b04108150142e040141c030072030160b00d2183c5000c040c401100c2180001340fa0091101c1c1c028036081c64000c000e074015011910100311254070580311100e00001e0141612501c11145000c00c0c0544c80ea1700160000061a9401755620541e800c104c81ca140000c00c0c1d510700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 978593516 1250 978592266 978592271
    0x60305101a12241906180c0c0206070807030e03060c090111030409051602010e0c010816112406060301080c060a0306180c02010509010b2b080c01 64
    0x5182001810605103480032040645045184086042451038091000d00180d50300a5801851614207150034003540d00d00e005100500250100c41c528602071600c20355200e401c12600008403200b900c10354080e4014050003130118103039240c40c09440c1c2d0007004150030500d007010350303180d01d50042846503201c00801c0d205501c0000356141415082074015140383c0003a80101030310300d4990980e20301e134010a0705440c1040710120707a40b462a801001603030003900d20b40608110f6828048800140d9900d43c6038224095400c01e1000d150100303000c030b40c0040303c55041c0c46108280e640e4901c04e05494a0304014101440341c1508210300c2543e08004a40f58100d55041880200522000350301c42e0300c000420031441004100010301c120003012854951402c0240c0d030194841e000d2003025800341505400c000c1503c2e200c410920b11503141038000860b0031880da0020022a254458810309841180018903001581080d4002800c01401d45201d003401c00006903a542c60195607410100380d00c1500804844da4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 978594766 1250 978593516 978593519
    0x41415070f110d0e0409020604030206040f1a18120109060f050106200307030507050703240f05060d1205040503030c03040504230606130b2a030c100c0309051006 71
    0x1600882c01101e100310700c1c401811103510124004001c6046808040d0069460f00c0000085481e00005c1d14003440d40180150b0f200c0362030f1510111045140e11039500c40b015202c0007030100048007801c55404d8039100b02c4c80c40d2400075001c14083c981e482c00054080035076851014101040c0ca900c01c60a8500055101080b50b501d00800146a01c0c40c50090040e4514440b0380b10b0300001c8004210f408260389410001d032a000b6608080c2d0425071294805002c00d152540035002d200100354601046881415081081c0001e0345032000448004541480d00428494400e0380403c5c0d4420413490005507610380946047d4640c0c000c2402c40d00103002c0002039900100d41401107180500078070085141c000042403000301a030034200504a005015240590b00002d030110401f80b04204040c00303880e0034925941d4072a03420744103100740100380110b443c1d0500070b160a808030b070b40d000c001c0398205400e420080c0980100154840010080a000031003417681d40c02e00d120009000703025015111440410000e0604d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 978596016 1250 978594766 978594797
    0x304020616150903090603020a05181f020106030c090c022e0603030905030d0806030709090305190c05010623010806030a020d0f050c06031003030f091a0a200604141507 74
    0x4482c5d039000001454014085014210381c4403054800c1425054117001d907901022021601004c059854000001000401ca0100381d030150003040803030b8422400b0994180d40c170540181143d500c11518401a0000004054002c80c200b907207451001c5054030012051000d40702e0301044800c1c4c2d80c011000b10320440010030841c601403006c035007007035407508264880c0d00d0000e000a4413070101e4000c50640035514100b000505100f8002d41da0801360b0300c1c0494001c10840200608440300310b140496066082800228107002d80b100035040d46019032469a1501d021840151415980285019054802e550580c000760391425081d904e00c074041c0003108445a00340c208281001e55022450703000348010002e00c1f9254000a00900c106c980518010054042961003198541d4075a8002d0b0204001d61100d9a025200700d40107103201d10083d125901c0303030804401440794143c9038021120a13a040b4100040c0411542c146000503901c100041e2000c116000b0a800da012600b0784154000407204c0c0e5026606 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 978597122 1106 978596016 978596027
    0x60409020a12030306180e0c040b06030109020f250201021915050415060915120b0117030f270303070b01090f0f020c030c070e0c0304020616150903 65
    0x6041101080c100a0100c00b147d05401c0d008081d0200014a0144900d0b880590701415007401c684c80c0c41c191500941019a4942000000300410000784101d500340700c04481c40340d000c880d9009206c1c0002440c1100c0c4000141c1039128a9000d1400316490002103000019040300103c4e0980c0e907891710036200d142d44000d080c011801c003070001c219002c0c1508034000d00781d111402d407800f055540c140d807014003001c5003010301680101001401418004850701124400d0582128070300b85400b41c036024598410344004446446603980c181d4203d5400d0003541560307008070002c504040d00d907220442d01c0b00061240c0385921b0343da03025149542580340c20940140301c240301c085442d041c01c822025120760000f190320110303015403c000f02e180421024068002c1c42c41d00c00b0b00381035a40325030030701c00586e0100e0000c01c45125a4000c3d040050044000c02c4008030340c101300415640214600a050b = true := by decide +kernel

theorem cover : BRFrame.Cov 978417266 978597122 := by
  have h0 := BRFrame.cov_init 978417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 978417266 ≤ n) (h2 : n < 978597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
