-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2586
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:08:58.588237+00:00
-- url     : https://prove2.me/submissions/bc8791e5-c67d-43ef-9e62-05f63bc156ad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 464928057 ≤ n < 465107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 464929307 1250 464928057 464928071
    0x1e0d11070f030e032806090f08030f0106020d1e02160801050a1107020315060604031a0a110910050a11060f1510090324020a030905010501050415170111030901 70
    0xc1e000758403084445000e6003210000d5a010f00095806170300c4134000a8401d54101c25510b4018002c0c111038000520000d0764020840038001810b001e5407140140c15001c44071030340c0f541c0050f65241444030225001a0500c0b03600582584800010b440c2400203004403002c42800c0e403110f441400250708064542e07036558040115881c05400741f00d10030303240210164a000901d0300401d03182c01903a50084100140200403440d030351a4042150021074000d05c8e07c074140403160307040031122002912104003103410041003410054a40c41207541c00702004010390389902d400402510075130024004001401518a00050543c005011262040020042c2c980329460007030707040a1546801c8500d11b0084009008111115400880000559400040d2419000d03000840f000c1280b04038881e41f07150034001728001d800e554040d0444800355109800078000740c0e80350700a01c41100c00c5100340b4090009414420050741c07004207401d407075010a107000460030304001d2084140d180e10541e0010f40c070b80e5450307030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 464930557 1250 464929307 464929313
    0xc1a0306060a0c35042d18150e010b0d091b030302070305070801020c070905060a03020604030515090303062209050d0c061b0903030f0905220506061e0d11070f 70
    0x1a5100b908010303a0003140c00c5c40d0410000701101c0704000c214030384001c0c2800030202942040794031100149070045010980418642020019048480e01400c90950b00e01002c50302c401501d4001d07050b1515100400c1c10b001030420b020000d82001d040941c4c8007400100d1080c541c102840384080a5402500148102850743c6441c80c50a03106034400d00090b4030506c500d81c800403000c101d810031110302800100d29a10f03528005099050a03a01c000d61105000800100b003210200d001c0741d03041c013030081c5d4014607030b64400b03440c1d00c80c841201d4160744403980c1c1101d0040020549200103400f90341190019820700706a44007803400c80603810900100b0201040c4104101036401114001700e100451081c03021a0010b002c1d01d00310a601004051054203800d11021522403903500008160007003856408121903c0c14500d01c51142c030303529000a0030200040c0380fa080c14002c0716040804070800d01500c032031095a5030310540001004140c00343d1502a01d0060014000c040c2c084a4040c8500d080c800c00b440ca = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 464931807 1250 464930557 464930633
    0x503071709070f170c210d0e130905030f0a18030503031602030c06010513090501060609080d11030405221406040507030e0d050a0306080601080a0c1a0306060a0c 71
    0x103481080d13180600402c60304450000706841440440a40b444618003440c0101103c910303841c510003840c280700381d261416070030340c3c8038404001c0010240e0350300400f0441104128141c0781002d9003d0b04035032042109a800c2101140203003082052494104210013000944040300111a40103850030f0f800401444800c00c094881802c1060140c0025880c0c024408007041d1500b10500c6454415176480c81d0716007882e15260042d229503940400200101904e84002520310001c3d801075040c01d21412202050143c003c004d0804031042c50001035050528040400240c0740580010045200a0600c4941c2101e4180102500d20031100f40203041840c101c81400301b20359000304110101401c0c040c8000f108040800c1c041d00581c060324010b030703850651640c15400ba01180d4014250f91195400000d050800400d010005920a4600c407007840d035a42e52802c060024010840040c41080010501e585401001046424242c0c14084d410030700c0d6032070b6101022280329040c0c0c01c0c103104021000d61403440f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 464933057 1250 464931807 464931809
    0x6090e01020405040c080f040b060103091b0602070b0f0d020d0b030a0614160c031d1c050d0e01050a05160b0c0d1b0203072d05070e011a0a0503071709070f 68
    0x40c4c545400d03607181094840d10362640141000c1e003010b0954000c659a2f0b44aa00151101c0d41c000910400d140074444a9081040c0f05102d0b000c01401200c03001700b09514203804076041480310240e06400c18241d010340d01c0083d031041d90404240b554070303003500c000c42d24180303d12412107000c1d100000d4191180c03811030101001c01042c0d003a042c0c56000c480c0c860203800c01d2000140c1e541501d45102402c3d140204803038031983c8d0200642e072201094464a010035104001280e242c2e1042d001e84007150108801900c14081010000f40031880600c0001203007846000a09070411032032200e64a0b1001c55100e9040c0702c0402e484102c02d8010000356081d002506000701959400f0400c180d0390030403d1241c0007500d80c02071500060508907040040071944031003508a4180540d4903607640341030740982c6021a84e0f444544214005600c202c07000003511b00c80001020320800800090390320300014820202c80caa800280349100b400072800180104d0711640b107038644248001070040c40c806040100d081214411 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 464934307 1250 464933057 464933081
    0xe070801150f0b0a0f0c030c140a05120301120209090703060c0509120c090c07060209090c12010f0f2c0108010b01141314060d050a050f06010e150d06090e0102040504 73
    0x4c10240c0d0400d54000407403032000d0040e283c40f980c014414503044402031007813400604461242065404501404a0442c401f10b114108071340708880020144207441c0401d12541d014090400050b00c0076040a050702072380120307400c060380e0895440780c0d9044202e50181d580c58001580120b14194241403c02c0fa4400c079030024401040c03800c0300e800014094107c005d08464002c0c1010600a04000c2550180e038a207a200400d02811450b2001c82c82c0c090303400159000e503207040080700001c1c40c3c8082c0c0c9081019203501c0495480482d09040c0d8500e210704168110340e0b0300e40e070101240d0880c0c005490303409000c2d2004400209403204800001004202a40c040300000031081142c0107000307a503004088c04884001483c01d2121020a00040712400b610450354600c905100801494264640c0180e12079607006200113a1a02c807040112600400390380d0a54001030401d14800341811100040e0003030900e401008a1510b07204c0181c10282c800140c10203c950390081800d01051034203000f25810000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 464935557 1250 464934307 464934329
    0x40b060d0222091a060d090f1a100305070e07052109060c090d11030f07090504021003020403083c031503060405070e1f03080c07050103050603100e070801150f 70
    0x120b82e4400030070402e60b00c1c4013900c00c580000340311401c440079800204505801110300c03a1044810704006440d200a0b20b4410100c00350306000a10400c03800d00190103480d0440001c0400606122108030b5285020f01030005121003800000c0c1ca4801042d4207119601c00074102028608112005d14501080903104020045082c0074130915502c0d000c0c0d0401c2d056030844941409c140d506000700f0304024003115028030030301404901054145041e08090700070b0b4826207040008a0026101b10100c7c001c0340801003010000304071045108c0311410b400c495141e083c89110f408800310065100304c51100d00c400d280c0e01c0038084100122800c100300c2c04030008205070b024209926056a6050315900c01d40510251801201c0c0450040951080008001002e180c40d80705d030035480c1e08240e035003a040304084012501c41c64001052070351281c0a22030091202800820f2200c030860b410601400d80000264581e104080b000103a041d42400340701d0340d90b0201c440c0d54800500b0301c11400c03018451608800d512007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 464936807 1250 464935557 464935571
    0x10905030c0f130c1e080f1828051902060306060319020d0b090a0c1b0203190c050907050408070632090102010c03090b06040b060d022209 61
    0x51004550408400000c60ba41d106610310140007600554100c040703520300b14540441c04840c59044401c0000c2d594101507601d14030404801c00f1035040900322032080c00500310a020801e4000035000c000300502c1d01c40192012080d0081c030f400708071543c0da4a0400340107445079019040c41001e00c10140d020481d601b0088200d1544d8012482e0303440043c012a00801c40040083c044204981c1e050000540a0070b0079907031032034400c07044c1d005041c2d9003060511a01c01c44000c105a039090b07104420710483d8545400c11800c0503101d0400361040340703507001d07070b0140248070f814074a062103680325038178051250300303446882030408003805174200d40105004248001080213218981c0c00081e00382c202c1c2c1581c43c140825590200b0169910211100d03c080780d00c00000320b5000ca0140b40300a40042c00c420780c02041f50f18203008045003554242c03040030b040f100501020800504060b001982c0c501c201074290391400c40c0c04a4010220b9000d0000c00742005601030340650640c12140a20f0010956074809200117 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 464938057 1250 464936807 464936809
    0x2a04020306060304080c10090503090103050108150406020901090b030c040f0506030408121003120c0303050a110910021203010803040305060105060319091b0e180f0706081005040501090b0f010905 86
    0x80d00c0013800240c50b110303001c01e504401250070450700c00540c0c0008014012031400f45801a500e400103203c5902003030410b0004200c0660010b501d403172118070924074016507201c58495078001d5020146c1c00307040141e20000829485030000c01140074218064049607140c1c64003005024240050304298800d00d820401c2c800410a800c055036401184080030880541381c500f1180a8010701c2c2e8001080c4802c8020644040c64200141480c00c0340240c40a0115545402d4640100c90194203330a41840702403024545906000b8503188074070f50113004075110040c02c114101c40581003644101c00c2039000080074001c000d4140100e46c01000c0580d1450b080d41003400c00810411414032240c000c1d2942c40c054038050255100d041c11401160140311180c2d2034849964940405c2c089422002000c1540011580d18000144034100c2441c1e25014100311814181d08443c040700190480d80c09014602c0c010400e65124441ea038001d100030750b0006141c4456509000040441c03c9086050201a80041210b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 464939307 1250 464938057 464938069
    0x302030124061407060c020a0c0e090a17041e0315020313020f041407050a020f070501050a1d03030d020306040c140f0a030f09031115362a04020306 65
    0x564aa908020340d00711080c0007500040c0c0213030301c0c01500040c14105c29854468000c1b44c0400514000c01a0b103d2890322460741d036002d0301c001e5819030b05aa120301000c502103008014010f014484a54215181c1940c515404060030004511407810752220b0710200300300801e0b00305202120010078001c1d415460300c00806841c2440c5008040d009a504a000749655560ba170b2107840c1840c0120074080312030406000081083c0c01c030408400c09481100e8040002c0c00001030a5002c403441655050b1802d0201d8504840c1428907095540b5010000104c01c1240d40d402d00140c8030b04000144010786900e814070070442034907000004202440604842c4030800c14440c402c40340c030203806440c0c2d6079454201c0801103005101e049030007275503070340303420064002c040e0300075030614541d81c4400480300500d1801d0440c0600741002d980c040030729640e4041c1c80d0f8003004a080002035000f04400e210400c0f0301c007044003074140300c404c041d0034055078a4884c8040c503040301e401291070a142c090b5400c5080d842e00c1c0c404100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 464940557 1250 464939307 464939309
    0x100f090302060a030905070b090a090506060901030b030f030f180d150c0215150a0e0c030601031d0a05010b0a091503021e0307120515070215040c09060f0302030124 72
    0x8081c0b071000a0070740300c0074001d810080c0515400402c0314a1150f4032004244039410603002148a000581d000054040707040c06440d019400c0203005030b00d0300398900010750081030700101d03050300b5005415500500180500140c000200e240c0f00c0150344a83c0392101501001c10f00d084c003480b80c90746084440c042014500300e03105007803075124006414954035000b0380c54105201c0d11030400100000411402011900e016140300e9400d071202024075072213091100700190104c86e080f44070740c0c00b440040e040758480d81102c00c2c04240c00100c0c580d0141d0140600781000140002aa8540e450b540006083c0c10923403403201c001c0c00190402c018840c0c9002c15024200308500c006441250340240101828107062403500c032412005040f0b410042d41c2d690002c1d00010031110944140c000c1d2102c0f0310301a490b502506200e81456030241c001c0c40a40f0311290078584018200342e85d0300d884071801158108641c803072040645154170003900f945c0d00d10b10416003511458814100740041074440001d0404104000c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 464941807 1250 464940557 464940559
    0xa0b0a0e06090702071e03020a0f06080c0313061103071413031502130e0403081e0f04060b030102220b04080d0c1103030304060920010206130807120e100f090302 71
    0x141c2c03180c60b0444101e00d400150b8015656451040030a0700c0081c1711480c101080300d109554440da801c0d550284121548002d1081d60007103040000012103401c600001940c0c0903d4480c1b110383e0100540d110001141d49601815030000c1d000010701c0102070304a010b8070100220f40c05081c0c5001241d0105001e030003201d1100400e884082c41450351f06c05e40c581c050b21307049181a542590300399681e09190380d0000e403da1741580800c02d0140841c2c4611280c4c021401e601c2c20740c200d1201c06480340c06140004141c000c00c00e4894541c0ca03040c0c11081d950070300041403400d562810b07000050142c40c6140342180b420707034410b0a442c0000c0204115111001c64440c940c07654906240075042c015007418001031a141c0b070502e6044c00300001b00303c204901c0c0da100c5d909550181004000d0f54441e50506d000106410321170a015a00680010303880701e41600405042c42d01c0b8201048c142046640e81034003621554850030040b90030943c000e130203400d242c1114444105540740c81c1c140d4020703000029100300c900340006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 464943057 1250 464941807 464941819
    0x40e0c01030f060e0a050712020a020a02060901030915061d090703030807020a06050103030216060f020a060c090512030a03050c030f07052a06060a0503030a0905130603080705060a0b0a0e06 83
    0x89948081c83c0d84042d0050201050104180c902180181c00800088406001081c5200c13016021030640e84281e460308a1640c00819414802343c003041070380c1c1c200301425410140c0b03481c0c080c0b000802040c000400c22600d03110104080d824040c40905910180420700c100d4480c003030070041443c200044410480e42c05007000a00c80e03ca01e04128280384400c200500010304003400081016800200050b00b07550380d0b416509242d848580884100f280c003e81c46c0c0040e48907080c2e88000c00c0840c0d104003034181d09030401420a40d542c0700843c06001c0780d602407110681000c1000144039030140602e80d8040e00440d03420786186060500c0000094014050f4401c014010401d9002e490075809080d4602c0c0c904442449104107440e84682c1e5800304461040c0129640c500c001601d050010030380300080c0b0181c0762541c19600340018024000307144603403d403006403039030800404698458002d01d01c450059004c0c003260324143d40c1e20307401c0d16215545030340220580d0384204002e290250105400001c12521 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 464944307 1250 464943057 464943071
    0x2010b0909390306040507081b1305090f01060308091903050304060309080f03090a050d2a0215040b07031805010c0f0309050a0b0c0f0f0a02060a0225090b040e0c0103 73
    0x50801e0740c201a01000303400d03121303060078401408000245a42142c0601c01142d5000400e50915603168140c01c040580201411000c11050368207a0000d0394003541410480303402e0b5060000303450950302c0d5a4001e8031a03040c00541e4850714100318448070803000c085000e000300d807461582d035240c0e02e2203540700e044209580e80115104105494003114012400795034111707101d0600700e0045444552044089440303215690444441ca4090114032020030a100c0a0000b414a43c03484410891403002003242d128600071b0102106508000141015040c1000c4103525519a844c2c0a41403122060707018507083c6084070300300400d0382d00c000c4482d030980e4040302030188407141e0314007034401110701d0300140da00000303841c40070590024450281040c0685881210b070003214a288040e04c2e400660380000d120740101c260100903003448402007485588030310484111540003004484242610300030256450040402000101e0443c00b51001d51801100c04010056000d08540c0d07681c010200d0007410f041c0c482003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 464945557 1250 464944307 464944393
    0x3061b0f040302130218030c0906010f140a0905012a02040b010314190c0305040f02010c0503040f090c09051801060e032103040614040b060105031801090302010b0909 73
    0x140c1d0015a8064090b0030781028401c0c1c204085d4104011180e00740c05490b0100625250020701c1c031110000190010350291101801125000030340380700002401204a0715402c80c0c580503004215440c0d452f560f120456041400042000358551164800c6520510b0f035254211a01c0b0002114113074100c400003001919180141c015100c4071440743ca034070480c28200708031240032882000d01200010030403c2511411801030b01210800d58010f808101c0d401c50400c015401950350b900254000c00451f400c043d80d42111030b00f04800d980201c21b1898540104031703a032a800100e1070028000c22918072440c07903182004408541014840d100800a43c44c000705982e44023800189880c042000318505480f140160080741d603031060780c080301c0316480c04401c8a5100756040700c490140354004211080b9444002c01150a0340000e045005841710110b01200520b00074800d400302c0343d109030004122441f244081000b07291008061090b144c000501b50992450a90340c0f580074010119003030310480140c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 464946807 1250 464945557 464945587
    0x6060d050d0e131b0f09080a08030405011401060c0c15080f060109150203093d021005090624060d09060e0304240306060804020603130c060c06060503061b 68
    0x80d0501a20074684924080311040403654005489405d1700c9010710b4a075200011681c070a4948252034032600140c14000c00107580000541e00a80a5400840d030360000703544500400400707a211001090300380380e50100700101c2101d008000d00448401810385982c45030054950440240344410002c881000200507038040c3c09204060700e00c240a803c8410985240650303241e0001121506c5a40401c00324040031030046a6540e1144810106001a05001d00e200003a110500440c000358012148005072007041c0348142440790408a009284509050f418004a030000c02c00c0e28000311040181903809885803070840b0111000107200181140719030034494018080c400d04a141400009000508050340c1c2003184901c032445880d001c0c1880c581c910507030840f8100d22401011883c0c1d040001c1c0949403910180da80300e07030b2000810781201101c5da030305d42e03a181d0304c1e4103e0341c049809440c0308420f0020314820f680c05450f042d4010031f2103051101c2000e0b07a850040041d03400444002a045018030910 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 464948057 1250 464946807 464946829
    0x90c0408011a0f0111120a200d050f03251d0103090b01050111070f0f030c2301081e04120f0801030f081b010c020a14030901090b0306010203040b1b06060d050d0e 71
    0x4102102e0b19010f000c0d40090412000c002d603580e4014614205408c00c5c9008249070200d252113803200e62800103c868950450f410080507054580300310158100a071490405110701d620880e9900d0140c1281305042e1017042020230141c0f030400d07141c1070325040002e001d00c012034151142400c1c0110030000c55000140b60002e10f4200305003816400f100001c0c5000d10f400c400003034900c681110305030310b40c40b10178038044c14a0032081050040c0000c0000451540141d08103034200007600c40c1c105010000101c4042528020344040712007030302c1904148544c45d4002c07da003070101002c1c58807e080d5451600c5084090345807450150000c2c500003080500700100e01442c0480180810091286480045000c1d4650500e440c066900000c1d10344014a0644084100c80c45020140c60b02d00c0460304101012180740c10081080d41988000c000218040c0c966802601081002c0707075550000c1401080f60b43c0c144a0060007a5000d00182000d410010f800840c1d100440f0391549840300c0d100515030001081c410311 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 464949307 1250 464948057 464948083
    0x190923130f060801091403070302060105040b120d09030312020906030a0509031608040303021b09070e01020709060b03060a0501050412060c18090509120a05041a040302090c0408011a0f0111 83
    0x9081c2d000100a031040d004005134078060f88140301800c1644418a0301c1340315141008006800801c014070403440c15500241681c000a40541c02c0d40c491440801d1070559004d80050216030f002404100f0954460741c690b18a60b05164150b0400d54001c000c190300c1e0001910b007440254403580060b1b2014000c0042c1c54504080d0f40e07041403000118104442194040d010907001030045400d0049200b260b0b001072401900c026002c01c0c07541d91001d2044894040204900707045015101001640c41c007540240000f4004500d80d1f1a0b50741040c0e02004482d14150380120305100781400200041c40d1518006006143c2040011841010b003c07800c64006082070306a1400010308100031415141d00c4c1c0c41544142314090403148003040c00d44454442c1e0249020090000c0c60401c424001002c11000390f52a034550200350a04141d140c1e800940d8500040340d03000d140c00400b1908210030704007401501e0807a9500d49246403000109004149540364100c41c80f0b05014943d1251075900400f0002d4140c1000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 464950557 1250 464949307 464949311
    0x40314091314161b080c0715020c0103060e010303080414060a022101050603011e1a1b0109050309041e020409022517030c09130209030d0e0d120c08190923130f 70
    0x9210307521603d10b89000c10310f000043c41002c2c0d1202c64bd50091043e041030741d14101000c6120b07071031942c003112440001081120600e0a58120320540700080008bc2d0003038006070b0001d07803103480121300074900040e4003058112003c4034600400079a101c03001124151480030409038510700184000c80d2842243e68401015000740d080e42c142d030704103080040d00a01c491a000300e151501d940f40001e0907035040100241c02d5400c100711181c9540340c10341c081240b18201c0d1b80300880d010362400c010380c1240c02907400810201d4001170317070050a468109a020b044104020184030b564040d80ba0000319400d10309100c0c1020134000085400100510103407041c041c401011700c03649481c0c10848030080d400ca6161140207200c1c840441c02c07100d00541c280c00c09202e000c0c1101e94032020548805c02812303071804103d0705004c54681540b020a83c3c1d00c000b44488102c4003c69424000a40c1000f4041c0340aa801140d0410715846051b0440c0240504680c4070f001c103c0303101218001c21400c0c04010007003d500310642d18 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 464951807 1250 464950557 464950559
    0xa08070b0604050a09050d110a0605390a030b0418030c051c080f041b0f0f0b040b07030f030b0612090f0a0b040314091314161b080c07 59
    0xc029940140300303410a88040c809a11121103d078181e5041c0e600041264200c00c5d844688244203203034010201400c4011035040041d07030b48440c811186c00743c550701c020092707138005510307440940d800c5680f42c0d8410350300c5008507a1010b02400c0c114000c280940b0b080586800c200296a900c5800c4241c00c0300040c1020b515900d22490050022000d040c0d00301c0d52806404291120585e000c041c01c05c07070348115100c14206507110340501462003001002160b409601c00c0c13106581002660701e02c0701810b00d100d41601020700303241200f4083c1d14280d1001a00000070041840240c00400aa4003526807508020550648032841a00540380c030030030183e0000408500403a07492071012026000d02c0c0d2400079100682200800c00d515081e515001610003a00540405d00003445000b0000107140c040fa0102d0400314110001120300040c803402401207921140c3d08400ca80581203107613002019030400025000e00310780044c2402003194910801ca00d1034421800a120494003140c05461a181c2990321203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 464953057 1250 464951807 464951813
    0xb0906070605070302210c040e130602030c0c070504061a07060e0d030f0e010b0913170a0c02010e030c010f050906040f0803120109050903070f060207120801150305010e06040e0a0807 80
    0x940202c0c003551a6588000e103507140312001c0c0011039001300b11047c000380c81c1c103003015061280040003910003180032443d01c0c0b00300003080c1548040c0d800b078455030859640c1c400e040f2290f00e28024198029500c2903103844c81c104400300b407480041100d2040c02d078480752030390600e0401c803000342810565949140580d105280340c1c240d15921880d00c50100c1d400410080901c00b24040c200c0760441d4095800c10a0720011446034420480e15520719032085080d101080440c06460a85420001c407440106224201840466800100d4801210070540082c0208043d2030002050040240c00c00c2d03090040004019505d84c0b00c0c101107901401c00f1000d1003041c550b0f1103003569a21703844102c0700c885e80c4a2850012aa600060181d68011802c000047d410120551111030100003506421148542d007080340c0000200040b00020000c00d8035165001ea943c0740264550740d859483c0c0c0100101403070072006100410440504942001c0c0587c1e001803545e001c00d0b1468642410030001501100b0049840820 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 464954307 1250 464953057 464953061
    0xc020f0918011529040b0721050c0c04020a09122001020f0a0305250b0106030c2f0a0c03051b0d08031504020f04060305060f12070b09060706050703 65
    0x610107082000b041060b940e0030090701c10b41030340d019500307500c10b0110b1030768294400000c241d00c0354010f201000d072800d43d4490320701d4043da02c0301404454148542c0303014264807031050441c2c202c0025504000b8600310354056482d454a00e4a201310384629404143c05042520944020b00601440c100240c1d003210a800c1c21011451051945042d4010b550145046944085400c41c03524101400416000701d19a81c1aa41134110540b1040c030903100c21002c958080c22282d5044c0401e01900324aa515418031500070243c41a0350580c1045c0444481c518800c40c0702c840c0c820106404a01050b11070b0300b12910101e00702510000c0181818001000c044180b22300401c07410625445c6c00c40c20302e07083c407080c402c0c0520103021aa000e4945007050000400a202402021031385002c0103200600e840018118440395070040d07044500040d6a0300200869810072811075100e0000c02c41c1c0d100d030251181001150b40f41a0360240e24445600883d61f001d0641b00c1c0015292159031090cc1442686072443d40200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 464955557 1250 464954307 464954341
    0x605090403031e020d050f060d080a08090c040207030507170301210f06020f04090b01020607090b0a020c060409060918050307140a05060103120806122109040e0307020a0f05030d0c020f09 82
    0x28541f2840401c4003450b081e502d01c05066801241c50307007040400c150503103c80800038100c0b6014025480194130640d00c51005180381c500c6501c40380e448a5250616041085161540492900c810070060240e6446e9011001080f9258404546010702c5460142d104011404009200500206100c255803184e080944191250040c00b0041d0f0745200004aa8858054554002117400e5000030f000d0740111400800800e050360040320703460400540490300b40d500943c02010480d507a04001e01c501201401001503002d2250302e80c41c0d40700090b07210941c8034410369070010908411100c160050075014000b1042031600704080e20007070f41c2d5a08102c1c0720004140341d0000041d40c072000003031203840d005e0303244415100000c00400c000320606480405110248100008100701442003048070b590368000c5000c40f012400c091921035241744140f24041307a440c1c000030f0001a0642d0b082c050b6332000034668003040094a003103140e1b4944d03400030401c5940c640030180e4202c0da41900304001800c080a01c51 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 464956807 1250 464955557 464955571
    0xa05010f06181103271c09060203180906150c030a1218020411090a0b0a090b0a0527120601030201140a0c0b0405070f0e01030210030605090403031e020d05 68
    0x2c01002c00d034041d51001c5070700041550415200034808190520800c41403801344000392003059804003011540e8070315101c0500c40400080c048010700c0c99810358001c242a0050074580011030602c10146800d06c140009200302138018040000040c1c10782c1d54900f8103101400711714030034503070700d01144600b141c0b241e02c4040860f01161741941d000e41c0d0107e1521440301d1005082c01500c401c15481c0d0708000c0904640607401c03804c6102801070040c00c1d0348500442c00207058612203603940720f04e20030f406400034210f0f6000404840c01070100104c9150820101d5501c01038001180c003840130080000c90303503690107a0f10640c001c5404400c0d00106000081c80760b0599001340c03910100d102d0145032612032480389500080000356900940b4000071240c0702d0045d085403003841a03603506910f603010444a4080759011a00121a01004005600341810060296100781c41c0a000f000e00704004140d40c0c0350007900007420166a50603902c4000b0b40d59518464440001c02c3c103541d0b60060740c40010103010203031001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 464958057 1250 464956807 464956829
    0x207030201030c08060918240105031207030906050906072102151303110c040c0207061205012d0504180c09140601080709090c051903050c0306060a020a05010f06 71
    0x10f005602405800e481910014030301507440d6200040c170024070150240c021200e200c3d8101c1c1400303026010001c105803110038100c1050355854401011714000c1c881c80d4842003c081000101c01103a030004120080d00e103207040495841c1da043c008509244502031002e4212440c03440f54002c0c80342c1140440b070013840e01c1e80c00ca5036444100201c3c204020b1064400c0003600b140000d10000080c000c4035080d102841e540d0540c0c1c2c02180b2213001c141581c0301850030200503000340038203210705508941002002600804100036540c18000c407200c0c0c80280d400c44207580b4500e18001d40b03103a20341d1042d00000e000064014403543c0d0320104003440804101c0f034202d860800f000702c0850341000d0ba104003161940440c24101306a100c070f9006441d00c210280c894410010011400706140d9410300403610b0b40c070380942da1203030380346011460840110340825110b030406081c40c040c00b919009080036a90402c60807260581d460103c1c200503407901100200051107942028201c50350a40a64465805c03101c5074440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 464959307 1250 464958057 464958071
    0x20703030e12090f030304180912021b0108060f10120b01020c090112080f0313170c060f0703061d041202030f040306091104050a0b0310150306110415020703020103 72
    0xc9a03207500c0000c0b09098484002d01400009150201c900742600c1006000e592415443d042032410051650351402c5009490318140350810a150100d4002e440c0244054000440c07000300610003903800c0c0d40640e0401c6502c4d0b000c0b4941d07a41d80c8101a00c1c07000c00400c0c0c10f138400381c442d00c0500212555039034240d64903d06008a4582c2d400481e403400254001003504000e40e090510911000c8004030090f100240184016894900705800842c02244007001c40285c0303600510700040c0030030440d09081c805450512048201d98030000d0f0b2250059507842d280f0311642d4501004500801d0594000d444041503411440302d0001c2410780d0354001c038001e403406441900041d0b001da07540e01c9004074100103560b0400c420030204106034410305030b20b80324002c65008541c05000040903590140c905c0301485940c2c441c0d5108030724040002e44007103207020b2030038005a403c10141248040c841e1001801c250b4907290039101c071121031000c03100900300d0001d403c20b01101d9030000965504242c0001c038046490710907 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 464960557 1250 464959307 464959331
    0x41517071d030a0b040605090a15020c0606010e03100b031c093b04020f0402180a0504060f0b0f04030b011502150f0c0a0210050c0c0c0a0303170907030209010902070303 74
    0x1c03c20641604440036010a8807540c2e944801440c00421410490180034110400941c00c400342d071051200313401c00541c581c90045e040b10305104026001c241440030300c0c0d1078070803161000300d40c184c180079055600207072070f02044012a04052002030702010703440d4003d458000c0310381c00c020302c4800d0362074201203290316461070b103164440680d62002d082001030340c00a0380c421340b100c00441c0300d03400791002d0010400e901e48a0042810fa030801c0c1a00c44071004400201007180c200b01d06010004d0100f260305210007854900480d41148a50007000c03203100703000a8210b00507135888100c90056910013044031841d0b96458080c0720701004a600300005005201c2a4001040c0483c00b050240300400154510b540701c5203032180c519408501c441065000c1d19042658142481c410907200c0da650f007180c40d9a0301c40324080c407400c0880c0444920302c0395002c44020b0010075480150a08a001c90041324205d40e103914500d14580b82d55548001c1d0700101d00800826050300c642c014100d0340307203e03440034006150020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 464961807 1250 464960557 464960563
    0x921080a0209010c02090421051b07030201080a1d0604080c15070f0c140f0f010b090f0c0912010c020c09090f151021020907050a05041517071d03 64
    0x10010b0f40000c140040707003009840c010f003249410904c60400043c1001c04d1140c821400d00104510901003100845d100e001d0140164501c2c0402c00700302c1c041d050450450340080d04102c00a849800c034103540e101200c0410380d01034800c8a0402e620030442d0311518251074041e1695100380414645400b420401d0032600c60040d40302c6003d400c0c1034907092000748405100701c82942710003c0955003034480c0360111464002c1440740006014001000d011180989081242500d1065a0940c0aa0614810401031f0080c200565400c08008031b90300c1c0c1e603481000c0000f00031030b102c0b0444075010351034600084505900041c40b00386a072016103003080d40d81e0311000c2d0076449040d185400c03a15030f0441061840d07420700018a255029201c0c50320700b04c1d82c980f1241e80f89290b40c082c2883c41c81b0002d035030145805500d01842c040364010310924040e89840e583c00c800800750301030741c881d52283c103d00030030595840b40a8290544800c0d1140d011720001d00c3c20100c000d101280e0840c4414951070303c0c0045134114203000c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 464963057 1250 464961807 464961817
    0xc040812210c091c0602190f020307111002120d061e03051c020f0a0308181609090507230405010b030601020318040e0a050a060c0507030c020d060921080a02 69
    0x3008140c20101040c3c14004130020f1030320070740011000700c444d107800a10140b01400c031070805c003848010054260724010301700204004400c02554001d201c1800002e0210403d03c100200580340300c011211030200c1689001321004940c556a00080b9078002400a19403110044400d05081f90014403c41d1460145a8140e808050075680040064042032103912103401114505881211140786c11400040d0401d114140102c0000d0b603100148071810040c03110608078272800ea40a000c041440ea034800707401080d2845108030305919a42d03e03100717114003444244000c0c5081d0402140d4800702c203c03c580645002414244102d28003000070480595030005d4910402c8103800840c94050401c140300120142201400d41c0f05072513080112a4074420b0240590700c91042000707150f1a24145817101c242c411008007441005402e01071103010a40c443c00c841d403541d8059a46441024403070501001401d5031410103455030728004640301240c284042c281c01600441d40e00d940389500c13290003100c240c0c892 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 464964307 1250 464963057 464963071
    0x30b0f10020312061f260108070302130b210307050613150606020c13060305030409150801090c03020d1109090c0a0e010e04020603071b0305180d0c0b030c04081221 72
    0x4445010901c64003520641c0740000064000444c02005100c0031b00781d800f0243c000303407220340003c2d03c03c00031810906002d20010002060a1010948043c042440000382e40c0345e103010b059012805211540e000d004941106420400fa1042c0f40340c0a130003501d1010400404942000d892031402941c54001d109400a81d18a43d01a1000f44000020041c611a20055403440305540791800000120100018001494000c2c00480c0c240c514203212001094942e10030500f03641040d01560009210003a11415642d040f1043d0f600e108550610b510070512054016800c8200c0205000003000009071031030640f042264000c480700d4942c4800e81c4140750a204810384540321b000460010300d800c801844d44100a0705e4441d154000742d403248008031012400c143d000c180006030607441105d56820425410708292488102411a80d42d48a91840c041c400c840749400007001040c40070340b0100071200100710714003c803541231a104589412903404072005240c0015244240c0c03201803460f400480c400d9903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 464965557 1250 464964307 464964349
    0x30702060c0c0f030304120806031605100e1c061b02120a0e06040308040810050601080f0a0e03040305060907090c1b23010e21070201030b0f1002031206 67
    0x603010141d04441d0890404002c25010745982d1a03801c050420185102d24020402d03c0c04000070400c000e4503211001c0c20280c045e1704810f40340c441d004460794210f012200155074208504c40c24900032100b81c40860000369103d401d40c1c0a01021000ba60713110b003150f500550307003040038204040c41350014042c80c3d201940560422030821550719212000741080c4545820100034994200d00011a2980300e500115a20500400c1c14484901c0070000010080400c0c502000241000c0300040c189160041600c000001e440c400a207485086800000b098540358045945498403464295180e10084681004620030b80c0e03000652290700b4003401a844041d40c8540784500800e0b1401452a0807041090340e0385030030b40590030307001c1805030800703c640000038000084101c030685905052042170b4170100340104203c400d16070082c4488046840d225424240060758081050111310352541d061582c030360012000024180c4250048004c114051100c0c100c001284d1b501d4080216070941c440082c0d0b6542 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 464966807 1250 464965557 464965561
    0x7030b01180501020d20150103140d0c200a0801020a0e031903050a17190b0a051c03090b030f0601020f2d0a20010e1c0b1e07090f050603070206 63
    0x98010b9403103c0c0041e0a1030440c44400c00c0d211011460002c16402261f2075400000c0100300340f15804c0c40b02c2100e240040040c4c400200c18035001850000081c601030801c1101540600112510104c1b500c2640c80203040111116603c0c4180b0703000b504030f01d100102044119038400804c0ca80414161100c501c421070000d0050384585044910350007034000c0b5800e00809018921400e4801718080d41300f825482102030502d078206c10503906a84403200018028150b41034140305070350b07072130031443d0302010308100e00041c1c0001824219940d4a66520402d141c160020a12400c1120000c2e214458071007a001c072030381c144101140c01d80c2d80000c601c18240b44800000300d01003a11041128401e59141c1c0d5080300c000720312548522524a005141001390402c00001d200035a50f0000b441c00320342003045a0045660b0b104003a0400c55080c05030000341555106e04c0007500c6010b0a000000000c03503032015042c2c05180c82580079001040307600038504041000000041c0501c1c112080300d00c1810305602070002c81d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 464968057 1250 464966807 464966833
    0x31b0609030a140d0608060a06090209030718151e05090108120a09081f0b010f052d03010801060801110708180f1221040305030f0901050403020907030b0118050102 72
    0xb030006405200741010405640e554402c1c1c05404046d04448003e08410300b80710b0020400c0701c4155000c4400c9a00601c8290000c0d1340205050044903085441c0710590685507408000030300070b0f0b150100c0a01c10208012a90801078401c0501a031000a240c0000d039440d00c007002416002449180c40750340c40800300013042c15403d030240204034410b06004800350749996000e41044040034040340459110818806092018001e13010420700a0030091408840d4a030300406d03a00c0f03880e4600c610200003541850050444100e5440303101d00c28002c064881d611240c82ca8043c1c0b00501c1058000c3d800d02c250303038001100c0030080380c009030381c4002c90038030340540b81c01071000b504444501d403030b8480340c00d01c2580940c0d1200f021907180740340c01901400d81c40f0031051140c0924900742d000c0d020184c00a000510001d40d000048801d809010120a9105c42541004944904c0740350402900000342d0000d021115800da00300c0c284446007622903410040500d0050050f1b140741c1e211f47c60040c2e01c0300403d0381e00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 464969307 1250 464968057 464968067
    0x209030a110628020106060e03030901030203191b021507170a06050303030c0d0e15190b030109060b1e060a0f032901020d05071703091905031b0609030a 67
    0x5503809050b06040150f00510000c12201d00301500421001d0046020140381e4288600005402e46042c0403481c1040c0c54082540c0340160f0390041d0500d94008081001c0039511011118450b192203001d010b855800c521020a000d4511010009481048003c24002c5500140b4038410640b41c2d0780c90105c180c03d18820281c98801610080049694040104141c3c80c01c0c001544604015582182e95034004604c0358201c0b0b01080000c02a600058405a0008400080c4580100b00c2c10280440c41500c0320148000340404102c40341c1c19803070121000104070064104143d500011a0710340c05106924500d10354910958610540c008410801e02c0e80141c020a06581908960304c1c0000b400e08130b039100360314000b403454181c1381c0c0c40400c40800209580c1c10020705001009074a04141481001d40c1c4002050480c03001240340311201000080c3c251600308000031031180b070125280180222420450b03201d50080005000401c0da040e220a944000020080d000d03044d03443c011803070000401001c40b2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 464970557 1250 464969307 464969333
    0xa0506180d0e0f210d0e0a0e09061305190c2105100e160f090501120c150c080a17130c0909060e0a1113060e070c0201051b03040305010f0209030a 64
    0x103070b4104029141030500c0708104948050903652901c0c0fa1386c00005003000080096948100c1a0301280b1003041480d480110700581c00920140d031804079030120b860010700b020b20141040304d00d1800c8202210500142c0ca030f084044402102940c0c0c800d2064545840e160720345524013611030b5000c6500c005a10111380c0c000d0310b145e0200d400b07039420556504441d0131079200960211248050ac0d41d014000c40c0101e02c40c00d8010010424a0000c900d0541c0c0d40b082c01515a100d5101c8a00054000121440c014030401e54165440380c0020b40d502d9080c2c0c400741401d000c84251081041e080000124018200b81094a030341d901b00e0601b0440d10300e4907000401038140230303a007295001d848190300c0c64242020009031078240d10841c1019100c1d40e0200500100c40b248140e2503a4003070800740c04104403072400311029008111403504001c0300c842d030f00040e41c19118401c2c000ca0321f8a045200410540004400380c010340703110300c0003802010380101485050f40682d558490b031580041040500140d00c0e40c44140e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 464971807 1250 464970557 464970589
    0x80405030c07030302030408250e0a06090228020705011d040f140906101a0a0e1c02030c040203010803040536010e0a1103070c02030a0506180d0e0f 65
    0x1038039006a40c1c0541e810a900c990048015070700c041010301182001f807080702030041c10380803001000c1c3c02250550030112100c0c41047c55441041003c15403010194010314040c061031001036644a21008180d034a802040c01c805501030301000c03681c10201c0c404207421003142c070141d40d080820010b0800b0f500d0400c20100003507070301c079a0f1841c00288541c40340c01070131203152003050320600b5071030107446007800c01030010f1420103801d055003800d1001d105141c149480610445d4041ea40341d090132401500c40b180b08042d416031040041d21016501c1d0049024a00301c68425001c0d139503400c001d80e0a07c0b06a010038002c2e442c0320f030400c0c041131206040c000812072103c80c81641d030041c80c0d413822414510a00c0caa80003d0340b0f00c056000180405c604022810380c00074030220041281129008004045004c0640400c007081003041c9034a056603002c1090940340d03900b000940e40c0e02c2c01c011010620307101c23011a551501f405248140070401c9c0c01000c0a510303202001c0c0c0241d025042c0309040241e01103e4240013 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 464973057 1250 464971807 464971813
    0x30d030e06220f060c021204050607030c110a090c020f01020f041208070b010303050a0f020c0a14010e0301020d0506030c0102061012020d050f0a061104030305070f050307021201020a0f030516080405 87
    0x241d00450004004240070701e000c3e0b140024400245d080003030800d80a02607810044808000400450310340c50112120030f6018030f000031000d1071900e0720380f500303041e00b401c5140d100c1c200c1030000c03950b00c4455000070000001c03502210a01903104020500340d01540c00d448801c000180410080301e0035400780a001c0d01c1c81159444c2c6021a00da8030400d00b69001e0300264005000481d8100030150400c2c050000000f40e80010301c445011080003074100c4516001c1c1e85102c098070064280325074003521a1b6640a58014000c3d5160130b1440c030400001c12040710308601c030340710f000c010000c5c550000c540d41c2d01451210b4500000b850400703024000c0c01400344170403604189940b1389600407403402e000c1d403104415608040c000701400c0d03080100c23740742d00c2d11001c80301201c10002040042e4000e011100820b9121043c074a10701210309100d800c50280483c00303900610340b4105008848010341c000d00810725584c4071000c28419804003102203d0044500d5120b0007010b620a407119801055441c1e80a0310070b10407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 464974307 1250 464973057 464973121
    0x60d11030405031201050a121704171b0d022112180a05030d2a0f0c0e0f0f0c0702030a05010606111506010504061d100e030d030e06 58
    0x40254022201550705400c049001404a00c00c984c210740100800c84140c00c03114181841c410410081d800010403d4562407852102507500400740c400800344410908840724182c444691245003100c901c1c1140c2d07404010030403a03031401c003c010400a4014005031010520b014002807a40c8481c2e000800f40c0c0f0440c1600e941007050314005111032a0503103d010720b21203812082c400b1403107039504200d00ca904505c103c2500c10b548000b1035035078455845003004c9500300050882d84841d0f0b20b0a03010b406011125070000510400d038040d11700325900c201c1044410758803c14035400110003611004002075001012071102da0120024001c641d0000781078418001c0035a984c1404c441d0b440d4080d0b40414140b0240800031081404884c3e0149261100100c052a02c00002410381c82240030b41000c0c0803100309810040c4102c286031640042000e0000f5400006118001e442c02d4450300d90603107e44586005144050304ca40600340d1010b82403802007800e03071542900c0c030f0728035101d400c00c1d0a8807030740c5810 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 464975557 1250 464974307 464974331
    0x81c1407061d01051305030313150501030305041a0f0f0d0b0a0e011401031b1808010e07210c0e060409020402030a05090d0c03090306050a06120c080d0f050702060d 72
    0x2c6a0410040711403000201c0b0302c41d2150250a49070000c06480c0b001c1ea9003020f80b000300320301101312075001100c000c0c01d60305000c482c0340000c40c2d0f101c501240e00000d03141034004000c2540000003002550503040e9450140d00000c8055030b51403103810b0780d1030326003135007480500c0711240602e000d082c0d4103114203400708110f6500381c080782c00d00c07900c1d41c00f03000d0800303004004001445040e018045040c6c1c0030300e0140030001c001300f0100c1c0700000300d41d040401c0060030301d0340e8514030360001540805031106a0081c0810b0400d840307880d42e100b2141c01390740303180703545d01b003d140e050701d8009210030210760300030b1540d90301500d0071980c0040c01400a151541083d259400000140d90b81e20086216640103480080c060500c02c4403030385000b12900c000d4003071101581c400c001003500310b004002126401000400c0341e50b64608044064100c0b036102d20202c00d03107442584c0030420300d02003000582e00b81004031000c006031040c1c100c0d01c0e0a00d540d1101d0114030100104809400d21500418138405404c00114550010300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 464976807 1250 464975557 464975561
    0x1b07170d1503021c080405060306010c0c150f0f08070f091805040b0609060303180f210f010510090b031501031a070206070e04020c12040b0a0207081c140706 69
    0x388610718460020740070b104500d042042d04451031506403a003203500919964244c06442903016245c422076001c0005009a1b10400c0021091588005180c0c91241d4a036113100915045041e103c0c04502085484040b60b4030a40d1510075110583c0d0b9000515103c0400560709282c10035402010800d1510001c900b03990280b810b1050708500c0000040d15103800d0800982d0390501500091040f040300e01800b0450b42d000050300c24814950b5880340c985440c80c5d00181580c07401c50440c5422034245c0c40d61003024640100700c0941540c002d010341e595900b885504500b21070b01145d01c060b0b41c0407940c1081c41002460748c0182c00c102000b5044407400342000c49008802da900f60310448220340e041c55035420003c01171054a0b002001400200708a0405007c050301d1060020783d460700490f8041214000f00c10708020002c40c0c0d03040c41c988180d9582d280d2100b154075621894141003d880f40000020b064480090b04842c0c0101c900084103a0720140390085983d40300c52100c0300180401440b813080441c8040c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 464978057 1250 464976807 464976821
    0x121030503220c0803040e010f0f0e0a060305010c110609010501032004022710050a020624041103060316030f0201030914010f06180212150409060f0204030303051b07170d 75
    0x8002e50300d4902d00028000e1520050300240c01c014100402042b6040c1c142e0000c4042d240080305e03070040c580e05d4000302c400401c90fa0307002506540c00d000058200d907400c401031031300960341d41c8103540b00c035a60090128243c2e04c0c288001050212002d105010512590500d80c0043e880103001520700b4160300407004102122003402180166441105d03811740c54122020140720300f55082082c10108004030194507058000d01030200034440361035941c1005921411851030140c0144200200002940e201d112a00101c886902034402e110b40301e0b540d60b00021401c82113030f9009480083c030780396950046010b489503c104681c0030300d10a03610410944d0a0040030702c520716500000484600d01080681110360070006208060310402c24039407540c0074450304a80c03000881c800c402d40d040400000c980281517034800034107402c0c5043d0201d61080d00c40c0d001002200d00a560038041601c0380011903000c24040c0d00e2243e1041070400c884400207144c2e074101d010b01c03141401c40d40d0030605040000c60650700c0d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 464979307 1250 464978057 464978069
    0x30c120313090605012303011202060c0a030306030209090a0f1209031e0510050c0315030c040906051501050405010c060f1e05250219020307050d0b0121030503220c 72
    0x40389421300440d6440504294041c00c170641d0722803551601c0707801d112240b2060080340c0242081007410000e54403071004a40084840204035a900c00722410020028055808124490243d01d00841c40c9854006040d001160b00003600540ca0b0126655540c82802c01c07442020a11200c041c0001c042810111800c540701da00001180300f070b03001403030407905060514238801c82051408080c880d0030b5003503000f500ea100c840b64000c03030030701041400005e2504c6c10741400254090305041825041150f86d410044c01203030504401d0022210440c0103413403030f010ba800792500055900040801051050300460024950602c00061110741e03269038501c840d80d603d40540382c550300c131b00a002c2e1200042031080c4081c0761403480004005141a00252980082d5080440c1e40440000c0d030300a66605020078802400f004141c11200d103d140751100d90b5102c24414096000c11500b101100711980148406000d5816507542c2c1c17a698070803688490224070070390b007141240d2203481c1c07100000740d03403092003400307404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 464980557 1250 464979307 464979311
    0x1202090f1206070809010c1b020406080607020a030e04050402030c0607062a0e0301060f121b030309062703080a0203160602090a0b16030e01020f2505010806030c12031309 75
    0x1400c0507004c0c00f44d000c085c0c031841c100da01d4007885c0205c0c0359100d80000c4c1107000501089141c6c1d5038900000d40640282e800603000ea0040e90300f809081030b000134141740d59600ca920f800050341d0190007004106d44d011900a0f4042c0c200c4900040301d49003000003003003d07034403c0700c00040680c0e540c40151704e507207091702141d00a07168030400001007540003070314415a000700701c000b07014040c2041c108800c8440a80303c2c0d0000c0710f644d480d00100704848015500a0340200d09844c1d21070039030340c0c20000e04a1030644a1400841c08484d002d11411b00240c8a9841843d094522000d2151840d569a180f0754001c420b88800c60009000007401c000c200502140c6c01c42c0200000750325652003800b040b4025081d544140d1700c01c401044903030010079141080089040e00760402d50106600d50005030300780640c0342c080300c015000b16a114030349003800b54009a07080f4041d0701500605600da03070065510394020742e4840d602d58407008100050340b40907454600c1d126102d00070f990410118002c40000ba0a4030307000362203216 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 464981807 1250 464980557 464980561
    0x715050a06090504050a03050d0e1506090f0c160f050a060e060603030c0c1905101d01030c0210090602210f0708041a09031b060f090d1202090f1206 65
    0x12164003622001d0b210380d50041102d07052680d034081c0c0d101400080101802030210f10790341c44884590001c802c8000403c25100d01e007240e2178000c022034100b250782c28842c40e03c00c0c0c00f10b058144811a40303885098540c80e06460000c1d0103507400a12005a2001c591203000d030003401c40005c2c0300784441000720b0300c204408502000d0800d01300c2d01782440248036500952082c40341c9031f020300001601040e80c98040c1c3e16580b0300e80341d41103040303030104480d040340340c100d4141d01c4400300c0c041c0d00c883d2050183c40388000c5000f141004100440c1a242072103007610050f4400c000750710741800964428103681d84984030052030495150301d1410408450403401c0403032072502080003002e540c0300c1540f40d400f40562030401802c2c581580c40060000c08140074080704000000040c40708030007001164071460f141c80c1140880307504041450360300d030400c070360030000c045d080b00120300b03400f900186060841207540c0310b010040410740041002500078000d0340fa031002d05003c80202c651691052142c42c0c80700c840c090407080c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 464983057 1250 464981807 464981821
    0x408040b16060b1e150c0105010e090f12220512100b1801030b0403020c031005070f0206060102071403010b130c021b060406080a020c0708160e0c040911071505 70
    0x1e8183e1010b4602501e50048000c03c88503104031501d80f03000044810080700f104d4180210401e00540d4a4525258600300010881025581c2e0b014407904d01c50b0201c9402a1100c04110340352005a00850392140c000e204c102c0074001280c801d0b1010042941d841240340342c2e900b000458a1190003001d0005400c405401c1a0600749401100514001542c00170280d2111201441e0200030521014188507644030115040500c00d000c13070145600e008084403036203144000240002d00c0240c40903030100344034041402200c2c0c000301c0d00c2882020147c014001e02860103001040390420420100d500d95038400c0c40218941c2d585006210540e8880b070002503100070384101a01d8039200f0340c030800c050b520011000300c2565400c0103c60036640c0b2807074024829250392201101034092a510030b00f45010b145000300d142140001c1c4c0140640e1410071001106070350f20900340c0c03641d0040e607081354100340401c002d011003205500002018040f5102051610341c107030300ca004800034550301000201d6124000c0c0018 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 464984307 1250 464983057 464983061
    0xa0215160f21140406050c1005100e0603060402030a060f0b1302070c0503070b1e0412060e1e03040e0903040e010f060f1106060f15071505070201090507030b0408040b1606 75
    0x505811401c10f80d02e200c0140e8a44041401284184002c211000400b04c071260000d1111411602c2074032000d0105050100e50125103200c980205000e245680000400e98a0000351a500031500500540442c0740780c1d40750380019100381e020f03044410b0f40b41c0d0104006500c401c1c445041003c182a0016150504c0d441e0030f0070710781c82030740c850b0b4820340c0b0120061240f01045421a140890324000c072104030041a000d105490040c4d50280c00601301c0007004005010f031513000702c815240302c0000d40c1c0c01e22039075082e5280200701d108003655441c0e0050000340143d03271182d0b0f14a60480c100000b03c134242030f42c622903a550714200b40c0101059103c0d00700100500380d0402c050060401036410076a50108256881654444d40203008a228420790180d503401a10303030f4010200d0005c00814000e43c0c41c3c8e07040c106080e00c0f00920110307001d118944400510b41d28410b200d0025000e60041c06450680d24585564054010190090359504410000025000107400040441940c80540749a60700c1c942d041600c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 464985557 1250 464984307 464984363
    0xe0c010903020112090318030503090f09010605091504050409051c0e090c090406030203010f1e060b041a0f03041113060612020706020d0504080304140a0215160f 71
    0x4140460040d007840140e0300050166860500d081002032179200d03906003121103030043c0d6810900400044408001d00c03c020005080045060352690758200c05c150030310842000c24480e48000810912080703030f6602d40306045100c04440c14400e207007002d0b00c603400942160302210b0202c070990300c41c807100515010b144210074994515824940847c40d2a5004183c42160060640f052244009400740b241d6889034081009144c0140080241c1320201c0e00c610300074219920f842c0092a1083d03604404c198090050740b041c3c40381004c400d4242460803060550028610504089a80040c090b1000c52200321001d5407145003e64020300706a2240710511406808569100048500384041801a1900200b00200380414181d00603500c1c1c00506011009014141c2845071140c14842880103018108000d0b40c021030080401040c0b02304103880d5260b42e5400160004d40204014902d43d4141401ca40070f08805070a0402d200709429a50f500e0203007031404044200e82c0c468550366048200c0f104881d0b501 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 464986807 1250 464985557 464985559
    0x3070e10080402060a050c010e1222050a05010f12050c041d130b06030c03010f14010506071a060a08060702100c05120f060316060509041503122304090e0c 68
    0x580d02d0070190041a22407003001d103010148032001500800b044401d5110080e0505944190744804c0d200c03984001c0107038000100075040c050176001c000b4030100c4c00c01b48541110001042800c24502d007400545070302c00004a66000c0c8612041303d029011b4440c020f11740f050074855246c0c0d0b92141031004942c003036841e44080e045a1001b290801c191034028034006445203803c4441e282d0340c0c0d43c030200024642042c005805d0780550800c003641d101030740c1e5600825445d4251004140d4142c2c2c030b400611031304e40210000a0450307507810011000711080c04c0e00030f64000101900c080c03500c6480b03007886481d051040d41e1502c0180e0101440e010910054400c040e0360402034504070340380c140000c0200a00300c4018119076504d48000c0003003140c550b01009a090b4204440300c07400d500c0d90351914003900541041c00514000c0e414094050008161f44401a0659078000c8440b100304100c28821030318407401c40c191b4902603103024200003800c180306024000034408440f000c544c5c0303900581d031141071050303242c096 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 464988057 1250 464986807 464986817
    0x6070302090d021210020c060a0b03030a120f0b0612190e070614090909070e0106080c030c0901140c010b010306050301020301060c140705090103110301051f090b0109080303070e10 79
    0x900100c0d40c509002c000056012102d100c5408088038510303082c55403400181118501c000b070081006000820310b14482c07103005008020480d0b14009041e100c1c03040203103000000e00840d2150101c02c40c664401c04200c0d5405400041000c070a0020400c60361040180c1e10114841408020390121103409550a030144030800344589085803070a01d41cbe843c0c26016400900c4440301d000c071014203240b819210140c1c401410014182802003145450380c60340d00840003a000d03c0c42c004129280649039103401a0017850641d440c66560341100000d58100306941810400700f0340900c0d0388003607680041e040c0c10000d1000050fa0111213000036044130510b601290080e40107100400c401604611554803150300141c4a1070410304411381103062524941016a0180380d03180013001780300004030550b003920825002048a5100c0c0403449441c00e14a11084404a98000c0c060100b8912900491a84074040c100f902c01680c0754601079082d43c0040b100480054021071030341403140b402c20460220b01007a0b00b42 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 464989307 1250 464988057 464988067
    0x8040905041506060e1017010b040e010602011404020108060f030a03050c280206030402180a05060111010b15090d0b0910141909150c031e0b180408040b040f050306070302 75
    0x1410003641007407454032410f00080d030320007000d0240907804400044d1201d030441f59038544199070001d8005000f010f0180c4550000490b026005110325011501079864101450344d843c3d004642c0c629009100c260449e01040e800085a00c00300030f5926030610945483d0303281c581d40007100d490550714071284044109041ca24520702c2201a42c4922040e4050b40c0c501d03500d960f6070011810064402002c640300e03048034010866180061782c4080c0c0158026a101c07c1440311209945003a1250003d200782e20607180389001581e5030707024000f450300b030384050f0000071400d2043c1c1350000e07041d00448805145401181084401c51141d10425036143c1c60f200071407006040007a81100740310140421740e02d14981e5017440c102480b40000d24030442e01200c84003803114141d00316000f000740c1150980c2089002c00340c100da03030250010b0b0181c0301200310090290705821884451240041320050420303a4040020000407403004100c100805c058110550132003801890f00b818549820b00c0201000105481400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 464990557 1250 464989307 464989319
    0x90f04120e090408030c13030c060909061d220501090b0106090e16030f06060509010809071206111e0a0206011e030807020a05091009150614130308040905041506 71
    0x80455002a00014810341300d80e9502107161b903521400a09a400c0024144000100054804041c05079072440da220750300c0f01d03960380010054a400d402801000f041e0325100c034801c14440081558444124404928854146000b03560220341060040d0ba150b5101d40043d414440c22070b00301401400e40c1d02d80062107600d4003244800d5910b01a090301c01c4030341d031000a864014400d0b0844182510018070812003a42e40d148090314070ba1101e800720740031592800009070303040b5000c2010401c48552010303240c190000381c0e880c48000e04102c912080c00460501a0100c040c503400c4100721154562800165140070701c40000e454100146d01000403400111240c1d6428001a0f548200b20f80d440108180c88015a200045e81204241c1156030006031110420a02840803401c020848140210800400405104020a1a41a0180744085828481c1103450303080e869004100003040000c109002e15140d40d550500340e07010780c3c4510515500c0b0002c1c03005100c4c6d91000340786c0308500000c0c108416440c00d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 464991807 1250 464990557 464990569
    0x4060e16080c09030d0e03010e0106082d1c1707020a030f03140703020d0b060304080901081b070f0209090a1a0709050301060f080105060105041220090f04120e 70
    0x500120100051070000c01c0312207a0010603500e00c881c0080665440c0d025260380203041345480108a480380d8203090b1174078183c1c10107104101c140e0710382901414405021004010b600180c0c107980041001c01406610583e0a06100c2c06400170a5150700c985140085240184015601840004403958900c2802907454000902c0c8048076458100007100e020921810b4004241c0d810700c0403000f41c101e20400800715031550041c84540002da404000c203140103000d01609000803200107000316010441041d1544c05040c40ca80d00c480076000d41c00048040180d400c2c050b4111f25001c42e8900240380b40c0ba0110f140034114240c1c050080d40040110350060344880d410404807001c01301543d408c0740c020500311440780d1181b0004c0c290103802448401e075180e0f000c040c0040341b403007200b045520b803802050341581300c1c20445040740c81800e01c0c00e030101026181d150107c14000710841c010b40e4490800c0459483d4080f22911500c00380b0700c0c0c4526481c19003040c2c1300c0440b10131070447c00c10200b0282400c42e61784079 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 464993057 1250 464991807 464991841
    0x80d110a0b0606120a05100f032019032d1109040204060f080c03100501050123040f0e1906081203060a030b0c0a02010b09010308040e070c06051504060e 67
    0x1010307221019854900c007283c03051085042d800e800c4a03021080180f40d11080e045140a080c2c076460031003680b6902c080081260050f404010711030028895200000d000c4003a04885c4c0400c0205540100100c0501240401301d040c0c2c412030300041c002d03196a00708440300b000c603140003c4404e0810040703545a500d0020056421540e24404d040e07150110307065481d2540003601801b256038071105825110038008e03645e0482900f45920a00c507400b440350600c0d000c3d0088034100e46040c1c440f12200c150b42c0000c2003000095031010b5000c500103000004d09174a100c089200104070000c05a074043c108110640c0000c124540d1100c41ca50a00c20104500140020b4602e4100074010300b040d200c0e20343c04001060040c4540c8045c11a0b0700342014480303003a00c0140204143c00243d0001c02001d044031040c804503020901c0054500b44041c041000340c0c03402c1024a5502207030901c0d00c01c1005010b80c0d00e2000b180c40607640614100800c0d40501001e080c14800d0002500c00c850400056140210701c00c01e1480503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 464994307 1250 464993057 464993063
    0x2805090a12110915280b0f0c03031612050402030705131d06070906110a080a050c390a0911210604060b07150e0c04090c080d110a 57
    0x120580107040c810850381c05014984020042e101a04000ba940030103020040480c030720030240d240009105600f401c070319110101e074500c04413040e0743c0343c40c03a958540e40000c1440121403a04004402c000482031000714860707010a2200e6844c02003001c0c005200d0a0190059102d4034903007824400940e800083c104100c1d42c2c01c48009071160380c000c5034a006400070600265018522150a4030081c1c00460030b2403003071400b69520000d41c2d50340c1c50300703c41d148080d0185082c3c0380c1016125601140b40540148584410707070500c207180c0b000c1d0200d614a000110308542131420035040441c401d505140f0051000003000070fa000451400380400510440c03401d1090110b2141d603403501c03140ca00d800b0019610040b881009144555883ca02c0605911208807151441030b0302d8410049010414081035174103064200d18441445011089404002c0066031500c1f80e962188081c0300ca107941d95030244451640c032515004240d00d00c3d1051140c0f07489100e10225040c481c010b44031590740c800008003190380c50b030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 464995557 1250 464994307 464994329
    0x8010b130e06121005041a0411040c1707080a0501090c20011e061a16020f03120c100f0c0f030b06091f0e1c02010806060408032805090a 60
    0x49400c000340c4212003c0d07951125138040c0740c4410040004961050303104600884065221501c0b506002d02c044000720b4009055000c25001c1d1042401c01d036000f00059401810401601d04940b00300280491003100d42c00700090344281000b58508030b42c041d050040c20f41841c148080d084082e4013610905018001454105030240c040c01c1c080001d41001c800c0020407408000f161a00002c288050502401180c1c5a00d214807007211028401d00c0449000403003501603e0f031420801e43c01c00496034150b080d12507040c803915401c003018071846402081d071850b881c8000c1c08011980504401074941d5828400c50076454998040740e0b01d0f400c0840101c541c241e5140004081004100041e03881c0034407c012500300c00040ad000c1000710f0f2500147c172041015031100c010040348841001510a900c404c03002014440040f4180154000d010b0f0079040b145c0105101d0034152250b86240c43c42d00203007103d0440f10842001d44146556810b103040407201c0300c0c90102e1801c0c00300f0021809e500c507a8822000010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 464996807 1250 464995557 464995561
    0xc0c191203260c180a0f0b030a06030209131104060f0314150a020a12150b070816030c021903030915030f0c0305160306080705060a110a1208010b130e 66
    0x1803075440c2d1034000b40c0a1144444403400d201505141d00c1c0c0146035141200d103022880f1001a1800f0510301007140c406a19001c00d9500b4036894103056007014008092040e158100070006944030341000e480780c600e041c50b07880012080e0500ca20205108040d09018625003402801143c026175015000c0e03030703008018801c81e090140c100503d807131403040c8181c1c180900358007804610a00c0e81c00820241000d9913034107400c0813140700c64408490a6218010403038052120400040c49404080c003d018081c1e03075254200a08c080d00f1400e0b006940e28110005640d55403203000f103280204020f4a9241c2c010b8280d4180390465401428504c001e01030301210b8481300b40244d005520075003140034070443c0044140b251106041020300030301401da4510807000071136480d5000f00e42c03091180c0f0040390502d0000f48142c515100a210f07280d4030009031030040142054185108406c208200007000c0d1291701d22550105500100130701e0503006070800d4200400800079a03408200e600c08a07401e40310b416914640030307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 464998057 1250 464996807 464996837
    0x4060504020d060504050a23060a0e240f31210f0801060c051504020102150f07020c0906010806011d03011104050a1a07060f020405060c0c191203 64
    0x2d030004000003040c55091200300403c000020408a500600c141c0030080070040c411410b544c6100901c51554080c5d0003000010a80e044940010795004110380942d841c841d0b20001c00c010aa20494a50040700c0298040c014000034100341c1c1c65200c0c0f0741c0d2000c0c404020102d10042007840c15a0600074408030104008000e10520003202255410720000312003440307a00143c05440000603240c50400300341d00000005001c1d006240c0c4042c425404406000303160b1301d0704c0c03072030840240150080c0d04502c1861140250741c00c5005040d03000303c3c40302a0104040c581150001e26002c41440d0303441c00740340c00e4010b105159800030b20440d000442404d0694480c21a241d498141102801500740d044d8284440d0f0300b42401c84c18010019140d040e035074607108940310480d0140c150100c1c0070040b20004108030403400701d0b206600842d14440e080b40c1c054642955440024485d4100c030705101441d4001c0e8540220b60710b0309007510107840080c052000000d071324028024415030282c0d007015040c000d02000780810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 464999307 1250 464998057 464998069
    0x1e0312051821060901050c040533130807050a0e07030b19030302010e07030210050d1107060c0305070804020603130201020a0204020a02070f06021f0b040b1005130b0309060406050402 80
    0x500c90282c85001280c000080851400d00d429005404a00880000ca0441c00c4180641441014000112840c2510302004d20629200c0d040607841000d59510381c0c1e03030ba80b80071007034040c1d4141e92024100c2e0319004113018012030207071702e5130280001d90720a0004210507200c05440790304844034241c00542958500c801540940407000d580caa000350244042190f15800503210816079020350700811500ea8110017941d034172070540c0406540304050740420104103202d500200f40d90006010081003031141550510b40c190050b10341103c40a884900d01d070106941480f0301540b10b5001e1038174201504003078010600b07901c4080c0c00c419100b0310800c0d02000f0769008201180c3c180382d0184c821503542d00480c8000352204260700550240015450b0000f400c18070006604066079102003007080518103106003000181600d08590f50002d07124042d1003c1941d4044c0301d07410b07191050315041c1e81e511415171903e42004045d08501c01d100001d00030300507030a60000b103040e0300c26405000064651103900001c0d41c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 465000557 1250 464999307 464999347
    0x60f050d140a060f0e0102031b0304020a080d0f0e01020307030c060e0c1e040b061908130609211403010e1816080d0305060f0108060103020c070603061e031205 70
    0x40780c0c410010341c4010003001d0b6025100c100c510060801880d40c085080c2420303440103555180c1c001c00d50704c2180c070b1202c03a0310f0021754006d0f2000342040401540e40401906100607480c46801041100c405030310202c1d00580e40944201d0240701031071409400c2e50740134004040d45039014003400d07503802514500200030000000c801000519041d850860264940c20041e001c07400c40380202e0805c003003101c07a41022016114071560308800d00804d0019040c0803207044d0402043c0081481321031504801243c2c0038490001c082d4003c02c000d50501c51100f10f00301c2030702c00c82c240034030030046840e1031a031481c48100c0580781035907207149220f21692190420a00700756840360130a0118019240c0310000c0c14502c602c44c10456004100351001d054481d4419000c55a04584c00c54001c50050781c1c4249540c490402c865000605050040c02c00e4041582e403807a0640303903000700f004a55500c03c28800b86e0b83c0300c04440300e10f0140070004061641143d603000c003100e00081141c8148100400c1c400900051403240342c3e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 465001807 1250 465000557 465000593
    0x1b170c0f010e0c010305100e06060405040c0c0c0f0b070809030a0503040806040605011406030402040f1b0903050c040c02030a1202160b010302011d0f010509061b031b01060f050d 78
    0x651801004400300303009004031803140700e03580b040c6894032006501034000c030342c4501c44410344011110303c3c10f0340e011180c00c0020185544500304104c041410798813481800d800b404a90342d2658601103500c0c00364500245074000d14018001268100800e001010807110100d502030200c945410401c40800d10b0625038072402061400040780115035040000398031442640210f80910099a940c200940000d00782500705400020820018025080c6504001c009880459001844201040050b1221000083c0000004031725031010014401d082112090410084508000341c000c0303110f010b036582c0300b0f250842c02400b240c00616030030300342daa03415075818044122455240080380d151901e0034000074001240030440c1200c1d03552192500f0040350f00355950250031682c3c0300e4500001902e8607040452040d031701000402240042c0c0c10185443e80706c1640100045da12514800d0220000c081007a8480050344c1c9000b80401030417088444013811900192015454078800e03080c101c0c000e40c0211030340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 465003057 1250 465001807 465001813
    0x120c030207080f01141003030c0b07020c12010e0c0f030c04051305030408011d030909010e0a23060414090a02060313050f1f090302061f080d02030d0c1b170c 69
    0x2041100c60642204d02045540e154000840d46c84103141400d502041c040580003920031024007000a00e00c0c5501c9411043e203004841c001e007183d00c0015091802c91074014244c0c1d448160010328000100300e0703907000c2b08086a4001031107a0303c1c000b080c2c0c0c4090b201601f07480381e40c0703950100c1c540000d002c030a031982d0342e004019070740d940381c84030481406032034001d00c00c083c018455031203182855804400c2d0b41c54954000c000600903403810105501d001c501401080b21603a4131002d882510103290080c0320340c03803425213100300580b4000c0b00304411180c0ca44859642c00c480c1c1d004000d9040404500085100e0f4119082034603a00d0f541031a948070042e24100400600c640300d100c1044485c0041c11f01e140c504070300ca039003003640f440000c0362068484800d001400746e070050300820700341e40c1da00c05201460041804420b41590361000700c107190000e81d081788000740e00700164901100005004444e2010354034200191641c121610105184540314005840710010443c40a0001140b80844003504295011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 465004307 1250 465003057 465003073
    0x902030a030503090601121a0a180507030b0c12070c151404020f030d0f0c0501090b0408040e0c090a0311030f07060f110d0e01120219030605040f09120c03020708 71
    0x1018140d0741c41940e00f00301c13074800c050001410320555001c4840007503216086640030441000e5108460401a200d068582e03201d40380e000201141d1500b5041311800b400c000e100907031560902400711040034000004142c0100f0501c400313081c01e1042d450300305005103051402410a402c04c800031070740040c041001c181c2010f410b145641015151a80030324000c4440005001e540800c040d620007900301c66001055a1220780b0844038052280f0702c00e003500038000410b003100b02c2c1d80c8669003401b00f00c80c1261b0f5184081800d10503200b031004010b0707001c1c40001283d89041342c0380e000510000700a100040c04115a481c401e92603440900c29408402d0102c403c8910045c1c480c10040d0482c1c2d84c2001c180e000801c88004c45056010000b10022101070646070700118008810045590381480c0708200012a02000300e01c42d804c80c41c0b4880743d1841d500f0b6a002032814203050411003903510010344003810900f0228010301064440c1411461103046041640440b070152405a01700f540c29881141740d03000d4550 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 465005557 1250 465004307 465004313
    0x51201090e061510030b01020705151c02121501050c010f0e0c01020309090705090109030b131406070905041a03060c0703110a0512030a0b04091208092109040902030a 73
    0x90800c0180c810a440241e41d42c0000741d156000055801c50740700c8004c200401e4064000c0d031200d41c40e401d041c4141c4443c9912400840c4500412000752651020300280c001c180c001502ca03855203c81d0750000a42c6054401c0c40b00c0b201401e0301604106454000071500f8601380e0161045641440e500340081c000e212001d00050005c00c688101d0442c5802290400011503101208441902c5e200401d40841034481007c11507454100040b810f05000071142c0c04030105901e40600c621404c07105c1042c580c2801c49140c4019402e16a4101f204680e00c0042400799250300321404000351502660300080ca4045e100c11900003100d0726440e0703078041c00342805018082e4481401031004902a44540e0001685512415525485000d0261039604001c000c3c54100550000658200c108644081040b070305103c00a401c07200300b558119803900c28036205043d442d0b0000c0e0384503485942c01c0068810b288085820060001c41012010300d180d0f000503200381e6503078942e4040d0792415000b90807600700440601e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 465006807 1250 465005557 465005561
    0xf09080a030306030b0606040315020306060f0301080f160305060f060a0506041206110c0709152112050414190306090305032211100309050f15090303151005120109 72
    0x4003095540002040025146e8200501220200c980c0201102c94140044034030400035000600101e41c8040c00700a290a13610016000d140a055520051b1450119407c41c551030079204403210044000d41080800c04288042045640104030b18404442c9544070000111600c166401c07007940481c000c60f011400115400300c50035254440c4904001c1c0001a01d1504058010490040d0950780001002d02c01e040707094000394607080207019281d0741035468004c141c241441081580c2c60601c0191011014000741805080302c822440c141070745082d08010000d503002c4050385070320380503c0446407a080312004240c1420b00464002c5401c1007803414a24006020b83c0c0f050302c160002503c2041c3c43c0301008618441000082c0d40300000c1c25503039149809000c91000c00d02c80042c181907442404401094060045000240d20000900341445201e9a01d8120b0321010b005680503600038410031862121007100501641000c03501c082c0d5198204008031100d210780c0c070440c828030303040f031300000388100d071603 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 465008057 1250 465006807 465006809
    0x90e0708011d1209090112080c0114070315051f020a0c2d141c05071403010c03050c0a0503042a06030e19021c050105040506010f0e070f0f09080a030306 67
    0x180c000e071926483c5440764011207002d182180b07075004a41c1001000b4a076082c2e060340310140c0c8210b28107820a410310321708a003182d00da0304d00741c840210341c241081200741e410311400b1005910740011707107046401d00010a80318400d40041c2e0b4420140101e0300405107000304580030005130b02005008a442d1150b5482c008840c01180b1ba10705603105001c1c0e003c055911541d4030080da07514101c400d82d00700341d807010017207084d000c503400552030580120040f011403000d0100d10041c2104c4a11009000a100103250864502d014090f080510740020b00201c003a07460f044540d04940d918001e5140c0d01c990918682002801e40c03022440c40407081e04464040407404a031045651031b07103040018496a0006584400190301d00700300240c0001039400c0145452422032803c0031903d44840b4281800b65110741c01c40300281d0342901c0961100e40100003210280400d400640314040540240d070034a1500580301c080ca0382422828031040b0140c1803020b901c13a810420003443e42c01e04481c039403800b80c200070f8024485 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 465009307 1250 465008057 465008111
    0xf120507200a05060705101109060d061a09180406022a0d0809030304020d06020f1303020405010f060215040f0b040303050708090c0a060503040501140f180115090e070801 75
    0x75142c00044914000055441036600a805011410b00450b00c940007004011030614894906000c98030458480001900c05040300f001c0005000d41007072007400700e50040a914210860301001a02070989030fa10041502d001901880145902d0300e00c3e000c8007a005d00701c8a4003442c4030b0940b028800b0700f15117210940049646042d101c904404036002c07541200300311141e9000354410400701c4c00505041480100b002e015079001400c1130038013145105e07a54016404014100c03000b220500641c0303418440c160060001810315402c80303107003a002945a10345407155520000d454800030707051140507490030240f1503114080e004035103010b01d000b5000300410b440d04000101070b000084d825100001d449440140000e08503000d403880c015044401d0b600007030003100e965413500130b0640d4460200d0b03440ca0103800004000e0025291480c41003050802c041190302c056810607072241d1824108909550a450200c04007048107158403400b18034019040d40300500543c81c003109580680c49189440003040c60b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 465010557 1250 465009307 465009319
    0x303041202070501080c130b030c130b090306060105070c1d19090320010608060702030a020d0206070e0906060910020706020d0c1a18010c0e0a0504090f12050720 71
    0x4105681240c2d502110b02945011840360404288240122800707003490503584603011550a844001070f550310b0308251a82d9000302000f01d50402e4180c2c560b24400060001c0381d02c424180350032800004d65a000152115050101c002410780a00c205588500050544040d0705050078680c561002059141181c4000f2029000e480d0361109035032170700038485565096641d0030705903800300300035240076007032a03903103080a41d681d00c2300041c1c465003480224401d02c09a00a5625840c08840207400c0c01101e00150086410800c00c0003405a00b2045181a000050b5402074040e039460021690610038041c510340c4c000e003030140d070b8048140e00240d4801a100d240d404d440c4810204c81c010369501d840960000d00a512048483c000d010503590280d42c400300e980256522500c1c00c40c0c5560849849a48060000d9121074641480e810401075582c01800d041e6400c0106104945513010481e038140030080c40000c0b11031101502e83c0c422010340f240140c01c031010400800c40e01c446280300e20b00340c8030100e02841e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 465011807 1250 465010557 465010583
    0x92c061f090e13121404050d050a020a080601210f0b1008191a071e021b01140a0807180f0e0703020f1e040b07050c0f100e0105030a061205030304 64
    0x31407640710242c3e1140c1c0011010307480101c509080e00c041001c2c240340288180180000030303c59035240c49140f002801440609540111401400b10302c1c0c1c1d0503009103645030300010040002c188034450203035030180c150000d010b01074903614140c0300038100301101500000e580c102780501c1c040c01040c00e4085806580444035039044e03111301c0d031703a1a0040900c05030200c5500c0e41103004003d80150502e51014103841d11010040c0114801c544500382045000016800250100021031007881300c0000c4c04401d080440e40070b020740f800c0118902c035011001080240c0480031410290049800d05450003880d80340d442d049407038545200d840d080c030b8820008000981004140014000e108480c0040c0d03100d40e4240c41c050b0a094401050020f4050f102900f080c05c000014820346104054042144160040e02000654a0410024009a0920b1849002c90a1007288815001090910320890a080407504c0f5900e07641501c00800c401d50003e00e14001000d00d400401c6004001544243d104e98030300007a10f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 465013057 1250 465011807 465011821
    0x606020f0a1e0b16090801050606030a1508070803070302010b0402070b0105100507050d0c11032b0c0f030908060a0b0a260f0d092c061f090e 62
    0x8940da4688581141c2194211502040380c4001e1440c254030b4078509211500055a1003640d80d9208440004819031201001c00c80940d000808000a0500c1d80013801a4140315001909500c800307010710750119600d481f0f99100d8035a21034042c0081016105030340d407640d683c1d5001d6032203501401c01100103500c2c06c80701e40d000b482c1c0343c402c1d41c10b11a0065082c07880c1c0c0c1e0a00052103030010310340300c0071000e0001c01e100701000242d04000842c0303020032903030310140d14200c10b1602c14044142410546d02c240c01c502051050300440c502140400b40701c2240059240f802403006603400704150303001800192003180340b07a080c140c01030080390454403c00c00700c503525510004a0003c0f111404003040c0c2c840015602004180c403800c28500d441c5620181210408600c116030700c1c501481081ca00410f17400103d28020400c0c0c00400c2d1500030303e0491030700b5040c98180420092401001f41c0c48101074403400300418000d45492070360800c2c0401d480075110404c03c2200002d04440502c0c840c510109120b4400641e47d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 465014307 1250 465013057 465013063
    0x90c180f140103020f03070308030a0b09060103090b060f040e0703051b01090602120f04050d120306090905064b01171b0f03030706020705010e010501050307061103040b0a0203030901060602 83
    0x2002041d08101e4190342150301700f041000b0300041c0103906100e001c8003c00400d030b4400003036000311001c000c00a2200301c0c030400c4c4102404008c1071181414580303880741c030100396000c0640d60301c2034040f10040385042071030307002a0003401810002840c6100300c550100800000091000c01c15480300715941000a55074011222030103513000304001604500c00c0c4241394410000030b0500c5102181e1841d08203900c0314041031400555000584901c1e110390388110b245a0103100b058007800100005000d00716031500e41a0f50303040090900c068400100c00c4401c405107134040000a5158240083c0c0a0400c1e040c0c4040300c43c59040102d600c41102600000a050070b8070000800d4010b0404050465800e0f004406455a080fa580e8540c00001801100700a0341d010310003041c0c020301c50340c0e0058484210b42041d60840f003000070403c41c141c2c03422005015039600014610100c400b5450625040410f10000c507040d402554000c0300c0c0281c000c100d00c01c810f50007102452007034030502e008002140c0e03211400c9136 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 465015557 1250 465014307 465014321
    0x3010e070303050307030609020d14010e07050f092e0201050c0a0c030807022e1103041a07030b03030d051905010f06050c031303030c0308090705030c1201090c180f 72
    0x1400340d12400c801c20000b8007920155074000c41c207040000781c82d80d4602640043c1c1e400074a00c080d1680d520b108029001411404483c00b4141d072300c039211542e160400b40500700344900c52040b64400c001048003440f940e03e0350420320002c0408844c0c001e564111445c1030aea03038940c4920040142d42802c0005060035045420341c1c128418039130754200020a0ba4074281c170b20700d03400340400045020760000011001428000c20b0f00c4040c0340c0c41c4040350000c600341c15a08907001c0046540c5180810130038800802d00800c0c0b802050070498080d160103803181503080e001004107030002a01400007052040b61b400307080d032145200f40a032900c40c0e00495410f44140c0200c420034000d043c1c10307410050b0184000c510403405041300c5408074040342c1c5410243c5408102581c643e42c4100d0000d1a1880320004040e4091196a046030401c0000c0c1040ea090800194071802030440c00b5000d10881c40c034410b0060402d41007900030316003042481d4070498035509001d00a160708480c400300c26040002d01c0100ca091441288 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 465016807 1250 465015557 465015581
    0x7080424050a1d180114040908090f0a091406040c08070c170f0d200708030103020f040609020c0c041104120f03032d110309060703050a1503060b0a050301 68
    0x51501054a070251510640e180460aa0108043c00d00c0015114000c81c2521340060b018944403641c98142111103402000c1c032118051f6090468030400505020b0aa82061074100c682c031038000740d14004244075440319440000a02d0a0908c141951003081c403456024902c01d031002c0c000d521500000341c9189038203688001c00500383c65642c8006c68040c400030172080c038030582d00600e04001c40d050640d841d00701c2c1864503205036407004a050050469940042551412700c60607041c4087c986500589000c1440080c2c041d12000c0050700c00756559070b01140142c1580c9074110f40b20002c04220b80e64629031480e641c1d0190b840c11403034000c00b101c003409417030840ba003541c3c0307a052240d050340c0c504c10380d40481403084040c56110401400345030029244d01141488858607400d65800d261200401d880c0d42860011800d0820003d03c40891000b09440342d124080e410b000c00d0303c2d2200e805600040c221b04011004040a04401004114030768210201000d422540c241c01292150308240c02ca070b440350046 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 465018057 1250 465016807 465016817
    0x90c0a021b0108040b061c14010c020a020303031801020403080a02010b010906030b0d0206070f050102040e090606040204060816020a020a06020c0a08070f05010c1104050f06180705041e0b07080424 86
    0x20001a120b80320154806c001400020b200c50f140459071135050036441044038480001c1c54a2201c00c2c84c244144031380c66000d031005040354031040d00403a4072880003901c682040740c10082c15a5101c03500350119001982d000c03805581c0c1d0b0144940081c024506803d10300d00284460b180026001d02c280601e084942c1c0046c01c0801ca2030044d403c01c082c42d40300c14800c0781d00103c5e0308a8000415001e102070710081101140c541014946000d202c1c0c20a00f00800a901c1240305100520020b07500840b1281d000003024440035031250070a6080c1d14203c8401170003980504502c5000c920345901040c400b1403c03006461420180e0788804696454558600500c03896503064a170070000c0790700c80c000080c180f60283d0200c03000f00e2041b502080a0b40c0040b600c454501003a5401d00c00389060488a041d503401c21200350605a081c5000000e001d8841d81c810361403071074070095003070300c40801a5607200014201e95000d035a0310066854000d942e0b0b0018810040c001510009800d5820a4000d0f0314034841d10b10750780c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 465019307 1250 465018057 465018061
    0xd021315380a030b0a0e090d0207080a0c05010c080c070f090c110c01051c0501060804350c0f030c060403170c030403031109040212060f0102151303020c090c0a021b0108 74
    0x2c100d004155107182c0d42e5000c0c55640700000c0d00301244480324041c00040e009000005160b40c0040e1034109a54858811540690300400218900302c9110dc02d5170800d2914404c0c6035040e091100307039400b481c00b1600181c01840e40028480c484281d982d8100c940d9503109105110742010140c1d0500300740b48001e407281d0011010131440b503115070004d054100741c0d9025411610f49260304c06c0c0403110240c100001040102091109000c01b0051140c004201341103c01806a131148500c00c032029030501d075251041c1d02182c1442142000e0bc00700030199030745400c42c2d07203074098640e41c40c1c1d9881c4203803001d601041d51354000c00e01036403050484a22503031400004624580b100e9030304400070401e4050207a00c04c1c105204a02e81aa5030b0f0009201501d5050700c60442801c0c0300d020011000201d0401a056500810030007aa600c00b01c139260b075106142040c1102c0044050038164100613118036041d602c100b0034001c100300c054104000e81010342c180d03401c60b0b440c6500f00803600c8640c0c1940c01c03150701140c11000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 465020557 1250 465019307 465019327
    0x90c07150c051b0309031002040b1b03090402211803032206020f091206090705012d050301030c210f0501061a0909060f0d02131538 58
    0xc0011031001d145401440c2c031540c0042d6541c080b441804540746504009461a0b551a00b08414070360800400400c40c135040c80c1141200e1a849001c40d0b0071018541104081003080c0c090003612044040600250b55615040d000c00c3c080b1021145643d122140800201d00c100040c40c0104082c0c0c003002000b14a142c4403480801150260742481c80301d41034403690038000003001d6002078076101343c084840c0c5880d60000010061070100301d9104000943c0709104101e250080054440c0c1210350a081840c22200304119644984040c01c0381036450b01e00e80761440c960240d1040085049034001d1341c0e404442621100c61340380c0702186000e2074042010a10070f141c003091065101c1910706100b00000582c403a5079108400e0307004140152001c03241400310303c20240e420051101d41d072046040310b007103400107212000038806078105240680255190000d5a6520703040d54020020350980701800601655203c2049034812141442280d441c03510042d801401a00861000042d44180c8a4a03041c0b01c6c0040b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 465021807 1250 465020557 465020561
    0x51504050a200307030c05091602102003040b04020102060c0403030f080601170702060105010e030f100e030d050406050618090c06030c1303060b0907081b03040204110d0b090c0715 79
    0xb4400e1071100e42181c0e40500c0d0355003013003a40025803007401d040d00828605402c01000040051003844826585d140c50107400340d011484510a10251000084c402c00303404030050900307140380c0103440462000080c401230003009002130784903901c00d81c02c1701c00035a155001013031940120300c030040100d40144900b6000342d015000c101e50160303062500d400c1d182c10790082030b0009101a0380100160304030308014000703560b10034494021703002d00b07030024581001c0559900307031303a401300800c90403c250341c58a541c512490180f00725403141c52014014441828035041800080400b91280d5115120890030300d24450fa0000c44682314110f0603001e001200080307414030080740c0c40100301c04000f0000300b15800130b1182c5540b14001840c01000c0009410b81c1c1201800020340c8050000824001c0143c00c00141442c0e00740041c0300d110203c0d858035101e459a01c0031401030194510243d80032a4003080030780c0d00c840b466203c00c0810800f1036611031036848600302c0c0f039402c0c815214040e11601d042042c00070008525 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 465023057 1250 465021807 465021833
    0x3071d0403050708120a0603020906030d020709020c0a1202010c080609060609090405010b101701062a0618030c0c0506032202030c100807080a0213050111120c0703051504050a 77
    0x180d841c5464817010101700c840b0807008980f00a01a46d6900e014010b60618440d455400b06043c1d0082001050850000e0740d02d103a1072040c0e005c0c40b90000b41601886000740448925a5031011200a232240020b5020b400303009101a000d0008045500203079440c9010b410640c050000581071701c5c91319034030000784107055a008006440c1d0350740750441446140ca0b40c45074542c00c41c40d00d1740c0d82d00e9005140560130380c07444c0060740f2000800c441c00c0160445110000c07801c0e00080c052600c0e003807901a8034900300b030141c0601322040f42c0d0454064003203c145a04440c01c48a0f103885018940c5003175444400b00442070109840f031104034406500080e1901c15400c4540341c206000908030790030f040c4010300249a00c83c0d1400c3c03100000320100d040c8480340c2d4200300556003041c01030b4021741c141304050341402250003407442448e0400c0b4032813180c409001001c0c460b80501c102c0540320980d458840907844c0d5550301c11807004035141d10030040c030401c0030450a44d05034052940040a8138404e580d81d25038070b20b012340b5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 465024307 1250 465023057 465023063
    0x6031a04020406030b011205120301080c060331060b030105070905120a060e1615050d0923070f0918110a080f010522020d03140f1803071d04030507 65
    0xd511000b101181d840c895040c000c7c60284201403040f000e07840c0c80f90404911040200740d4110500050101304404500031500a405440d21900c0350748154103200c09441040f0b18207a00f40148080907e001c2c2c0034135502031028003c4d40e0521030582002d051508840e02103030181d00184501c0420b208501d84034001d941101003120031105132800300e881ea6022280000d00111041d0300105c504d84020500c1030411000703103001b100e80c50b01c0506e4980f01802ea80306e040c0d061503006942d4a64002000307002c000300142e20303a200340c070314035a92a003141e41d82d91000180600d00610300a0040000c1d15001c83c056034640961994a465003800c0960794800c0307a824030201d040c0d00040c0c524021801002c00c019441081c0805000843c00d820140240740109200c2e54080781545060b090790400360700d6529403003000d81c3d07040c50880b1200300e810a58090a0260240744004e0340d40010343d461181d10011b8071a04d00f8003089045d10320103581c441d810002d1059400542000c0c1c6c00110025000c28040c1c009004100c1c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 465025557 1250 465024307 465024311
    0x2090103060807180b03030c07150c0f050c01032711040209060f190f050711120f0102030907060f0909020906070b0a0e0c01030b0a090b06370306031a040204 69
    0x10b240d0221a0902e20070b6003210800b5250001c0d4154500854040d01000000170390243d850029a192515102d01c080d00070b00d40f01c95110049025018031840c0b0503010207070000f01000800800740391154a620780d148042d0b0001c1d0414401d80503585044a52210b040c80f00303001940e540d0160781c0e1b400340741880f0b6107407998001c7c1d003801041c2031500c2e041c0003000406c0b00900401c1d941c0e034a609011508903080050441008441360700906515040f0041f160741c950021070610324244207100148045400407000c24040c041d05200002404054016500503e425001c1e135040585850084565078030b054001d400145406000700254205903004144505e0042d20051401c0b03215101c201c150300e0706035210b9008555500c1140402d25044c007a40003100f00901c0d090103080301c2040098914032046c02000449035640d05039100c10f9032002c007118038079000c800c0c11030705000c2403400150f502040601c2d00854001102c100364059446480b0350015a903100d0407000c070340c80508000c241d4481004200700c2e00700d5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 465026807 1250 465025557 465025559
    0xc060e0c10180e090d1202090603010302120c031903020601050907140a030b031b2d0402130509070f090b1309052a03010501090e01030b0105060c03160303060627090209010306 77
    0x2080b5001c002d214003200070040402d005d0383c070401071a064030040c07814402e500c1440003c0c25540c07540100e0341126011a019204080302d995158104290701003400d901d4811011410000500b0500c1c00c02524003079000d54949a9a48091284515045a0b5070001074074a800e02d801000961000e01110900e45c43c0004c0c44085c0000400d1610380920800d94001c140301481c422585400180d550b1f6020b80128249014041880f4134a6410034800903075110726004a0003082424040740250b008020081c5a60854104a030300500800400560103001403912000440d0b580b010200321012003024070342d04003005d860004180001d1401500f68034030485030920b0341181c0103140303074a045000d404215190366075240c140058050081136101035800880a401080490710081c1a18111682903610f60b83d03403680040341900707521400590300f40842642c0310001c2410390640c8200c0540d8041c0d2200c1c0c0200c051040031194440c01844030451422001c04188190000d40c1c0207004600010f04000c1891 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 465028057 1250 465026807 465026819
    0x201030e15040c051003020a2f0a0b1008070608040204180b0405011e0b0310020304032304060e1219030207090e1006050a030507060c0f06020a0c060e0c1018 69
    0x1001c401d94081d5850325442d1000d0102c1d207402040100007603201c0c1030461801140f0600a401c0f074a034981d807800d011a405400595039160503130a800030840401c1540c42d148400d1402403d00042524456039141228101080c040c4000404005480c04c0740c03118200f40c0c3d950360802014040c1c001130300c402100c114004c90009480d1a1030782d4000c030310540010885820b9001000c0c180440240d584500c6810100d09010315240810b10048000080c00056641d903200d08098518070705104551031a5000024034180482c4490046c00640785595981502100d031501000344250313403440c0d10300c0320b900308090300a20b040f480c0100b030030317054400c0c0140c0e00c01d01e82e0f95650000319854070310000c505400c1400400c1d111138184c880e88000c1c00080340ea0180150441c0c1b5540c2e03903403041d0b00840c0180039007a03c1c201d003031202d030003d5481d030150322a005550b601300001000300b008248120850703080741005e2000f80c01e180040381000300f24801602c0244024600d0204603800448084d180c0b05d140c1c01c0d101e02040c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 465029307 1250 465028057 465028093
    0x6050603030f0f0a02060f15060f0405060c07031217010506090111010f06050411030903040611010b0607080703020105070c11060a0309050d1707080f0a020d0f050906190b0d0201030e 80
    0x383c028a9402500c603001d4540103401d1000040031000f0544121040020480780d01039a40c114020a866003a100c0395a0b5580c5202489586c10a5a00c00d0012610701d043c2240041c040059030f20820b000c04030b4403003428055584072607144124600c81065401404103040c643e01500c25000e051400d82c0a407060300217054211400e85003190806622454248601c0c1414000c40d51486446031a1901c3c5241c1000c2580e140d00031406204c0820000070450303400e4032801d410128002000420195a4040500d0580502c0e0310060307046001d5424000001d04060080c01c4010885030030118100100000e5420800141e21011800f428141d4030366410380400c03003c0003001031a113410344440b90a00d4202465501c181c10041500b010001444204031000e03051500b40307500105002c03000742c1c0351902040d0400180410080c01000385182c0800c00c101d441c0000381c0d20380540c00008100c003030381c440207460f03806484510030107030f8000c8500701c0f02c4001940300346e1001891101d84408e41e00115020003c4103a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 465030557 1250 465029307 465029317
    0xb0d020402210c0d0b010905030a03080403020f16090f0218060c250303080c031009050601110d08010e01050f0d021306030524060405150f04060801020409020414060a08010306050603030f 82
    0x10f50782c401089080c84643c280c854a1082c040900785242c045242c00002a0b0394002c000004040011810114007050b00801009079001d0912054450321450000800c0a6010920986000606040300c00c40b11115038400c03100d01c0b81c000010b8030305103c080d070280152544104104009031040000c010943e580200c10480c00b0000320b0f00c1c004203e807440c10018295007016002c181654820420f01c0121001000b00340e08603001080081241d40e91500141e03600441c040d0700003000d000f0b00070100f40203644012218140da4040e44110030b140d8270390040c00b20801041042c19004481c0304461005440c080c030941c11402c0d821080843c8254036551680c1c203100074030014034000ca0705030003820700448128503840e1384004199010041d070f25241c0407680c02d241074914014015800c080100d00ca94660b60088030250500c0b000940d915641c8aa094000703600c684200e40000070080d10b036480c18500744045070768194050b82e80d0703d556421611170b080100009401954944070810007032040307aa000c0080c05c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 465031807 1250 465030557 465030571
    0x4090311070602010b1504052206050d03170c161103100c110106060c0b0a05070e0a06020a0212070b1e0c16140307060f0e010905030a0c05130b0d02040221 68
    0x100b0280b05c003200303014a80d41c2c10b01448040300c0d814032050081c2c0d03d5500782e0408003809007503140b15145030b92035020001c2110b50051504010010540824550882070313034100851164042c4103075070fa42040c14516030080094504a07285003081c10070200d2040d64600c4490309000301540d500b01060024a0110781c585c54203680031403014a580300740d044c3d00b0310801000b4219810840a4114075554804207903070700074a1340e210305580d50086040740b8801c103001c402e0410b0281c5162400703501c2c1c40000e95201f01d4509c0c200d2040000350030034400300d00080382e020704403801c0c03405450907c0f81003150204002ca03600303420002940c09100304010143e0800070b0390701c81a22400d148070350904000034061910038411006000b03910920041265130740c000080341445051f860099100c200d5600101e4140d19a58042681849509004400e11881004001c00c64008540310804407003501c03010f0080d50300c640c1c0816444400c0c0c503408005401c154005020040100550507410b8042030b06041a844041e00c0c08 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 465033057 1250 465031807 465031811
    0x20705060d05070f08060f01081f2619060e0f030d060e01051002070b090126060102160303090e040206040b0a03090c08010207150e0a1e050601150503060409031107060201 75
    0x1c001c00750303044803803240d1814481c03030000b0107031506c0000726a040544213a02410010035000040b40a107007910703081150141d0348801c0f1030240da111a1124900c2504880d404400403c040894400100240d0101c0488840c500c421840c02d6688480005103108481020381d4001c0e0b201054640d44140f0080012002c03071840003419030300307011103041d01010580005000d0040c4050906082d50002101e01c02c40d41103480301075a480342103004844030380e400944000c501514500d128440316081803054850f00c802e038219070f54070010a19664040c5a548000b402040c0d01280511450180c5074075a64000d002a08c6c5504e4690354140c013a10304e903c46803d0340002607940e405c480803c080307010814010719101d0b000794108542521060342a0361110320b01c0d600139580b20840781c4481d80c00e00034044410703000940300e800c0d8144210381041a03c4002d004950900a480000c10040040c003505115600700366070360713070560f6503000c1400010720782840140c00340440c4072f054641403181080030b03101038005a400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 465034307 1250 465033057 465033061
    0x210105100605030c071103010b03010e07180b1c050a0f0506150103020c030f03180f0706030f02120c0702030f07060f03050a110717070209040c05030f0706050a050a020705060d05 78
    0x400c8505001500114204442041440040f412440655004907048000c0c208802c03503c8000074018201c40d1682c0d0707015400c04d85075580316800030030000b00300da5803542440041141060800c00301c032541c3d12510351103c540c0004a010501e00000c0780139443c41007040f515004d60b030391a05044109502400c5407070b80d00200c20002c030040c495060030120903003801d0641c00d10541c2c000b096260f009a21480c024510080b0004083c24104504182d00b000c0b80c41c01c0c0c855500041c40c40c2c82d29170059009072008203080000c1c00d41424410f101f140c424407080d040d01c07081a01c030012421000d86c0610340681e410b21480d8004401c136a014080c000003011030b6281d8540138035901c1005016244000e003128256480c008066010161000031202080e034802040704440000102c0c040300c42c0640e102c0650410321140800040150014082c3c003514006c1302214011100344080c1da907500010f000e03007400580140402c6050501400c080d005100d040d005503513102d51604007040144d0000f94410040c9074960781 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 465035557 1250 465034307 465034321
    0x807121b0c080d0e1c02030c1207081e060406020d1506110d020609190201020a05030c03030406141005060306120f0606040e160e0403090503010c0909051012060209210105 75
    0x205480f07440c041410304860302140840003d019a036562461503d003c502c84040c42150b40030b00460b0410403005162541d0600004002c0d651060715010b1007072a80b10361650407000703044411b0800144d0b1001001000f031559a030703881c00080e4010307141010146840b80300e20b002009000031050040c26840d43d9514002c0840d5440c6131a100ca00149402503402142c10720626800114021030429040d42c400c1c5144031f16440102d02d80603a803070000c2d02c82d02001c0340300c2071002000b000450241d40100401c0c00840b20303800301c006800b8030a0b940c006441c0744c50b49080140341802800303981d1081006004003955104941031900b0081a05803da080d0740020003045500c0c5000d104e08002065200000c02c050301c1c0c02118071481840c240600142d10a11034005030070184645080005808040d000b403020031585540a00040c400c0e000d020022030074580050305604000c1070000481360680c1403146280740e207840782d030000e612200d4416008500800340d01d5039008194001541c55802e400000303040e01e0030300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 465036807 1250 465035557 465035563
    0x510030e06220807030e0607140c01050a02060a0c020115060c021e0a06141e0a080a0c0504030215160f110102060c0a1b0209010603020703080604090807121b0c08 71
    0x910900039012244000d0340c482a0044a9000b075560000300c0540d03d14031030030240c54868001c50025817203100015000c08114186101d152813505060890f0700c041d194131b0041d150381c050307040380c640107078012030002d544900d03607402c580d0403206a80000902000c100005021788690303504070501144000072500114240104900c2507012101c072150360a82c41440058020361161050030100103860390b190240b40d80c503104a9810840f400f0700c5e11405401410124200d800151059004c58a058009450311106016580c04d42c1040e540d100d1a0904581c00c000100e1401c0c4007002e04440b05000401d0f00c2e4055601450406001d0100b01143c00614034220000081d540b481904541013039081c012280050020b8401c0000142070014880c4144103098640c13005607080030b54040308440000a01d2601a03000380a000e02941d50740409036034000510081e12805070004059603420460b601c0892001e1550b0110000c1d00d2030612260100b225041140032180744040c0c0d0162407840080240100030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 465038057 1250 465036807 465036811
    0x204111213020303310f0612060e010b07030201020408012d02040f061b021011160b030414070f092a0804150e100b03070e0f070e010302040510030e06 66
    0x70405008001201d42c0807030340b203000b00b1030301550009100240c1704008a6810404900600111100fa041c0da41c0c0c480c01409407400b80f0610340811425600034040d84054003411043d01d03501080c2081b242d00e0040743e100320354081c01080e002c5540c24000494800b1081c09466140030a81c0c040e03840404400b000140d0724600070008114080c4104001c000b5110048100d104850f16402c09500ba8040b204c282040d81c000e00714029031050700141400340140d005401504a0710144c0210380410ba580b400240c2d01c1e1005001d01401c000c002d000080000c0c408041e52680203500d481969100c0d40d0740e891000000c05241c100300040d9444001c8600c0c0d482102408140380c0928483c40020800940b80145c645a0041d10140c28030b9413600980b000b0401c103811921414a22108441c28143c05910581c010302e0b0b10b140e003034400d0040840000707100012403210f0780141c2113240000c240e0303110342c442915004447d4140506240d000c1c00005910b0f0303a445100c8507003a445450204c0c4080300800c07201c2c02e003a00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 465039307 1250 465038057 465038071
    0x2070b0a05061f020c01030209040912092103020601030b0c04030b040c0e0a0203010b09040e07050d060e12030103080307121401260d050d0504020a0f031223030703090f02041112 78
    0x41901404440f035400500b5501c003140a00340160b64090081c0401c001d402e2014000e066142c005e1112800b0b2623005241700b0440d00281d400c00016200e24244c0107003640c00440141c0141d20000043c40443e000c2c0c0c4c0b64a420010798000203260a03903075510350141003002c03a000d64255040c6c070020408464119203845c2d00003504842107142d0341c10400720442c0d034090f81e200036000d0341d40c40001d008141410041040584801041e4850500580c0340050242c10412a2608a0300410b0b0361040070765100801c0e079050700e41c46070440d801c0da607404008480303541a00e0240b03028107031500094100300c62020f29150203003032032000e945542e00c030441004155061300d4a2401c21540418040c2a4040d480300030707507659440306030004c03401e40c48078000202603883c223404c40c50b4419454080001001100c0100028100150300d80c07400741c00c0c22008112208000b07499801c0c0707035242040080d210701c0c07099000c40c6109101b4001802d10354000d402240489105812084071a040040d0360300c11030003000a46640911 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 465040557 1250 465039307 465039349
    0x40b07050a1407022b0c0f060906140904060603090209090a0209071d100507021c0b04060506120f07052121040305100b04180f0206090402070b0a0506 66
    0x301c1848000c040d14407200d10700c0c22211020070f400b82155114054801104801101042c014801d114444a540c25014044840210125000a054076a01d624038216000c1b0b44842200c1850b0010036030b139001118640c50001380c800c000e07006481ea01c1d481844090007855800180c0701c11030348144a164803002e440b0440b580c1c04803418800580d20307290b501c4e40c80040f030b1405000b00309000044070342040d031050050b03a0004141032044c0400d43c1c008050019103000701c41c4048199100351510102861107903015014518083c0040c01051702500300e280c000d0405060411811140f003603007070800700c000514240d00e03045590108094501070440408484208031001c000311401c1070600e5031076141490426010100b480019075200814042e90001c43d00725096486008280c40385000921410843c03911480c6031070240c01b4059106072980d899254003007802149446c81350200820340d0000f000d0300b036005408201000004900c803540718010006400c021625090600401809071100710350440078003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 465041807 1250 465040557 465040567
    0x11070c0506070209180705030106080f2a0409020604030609111003020c060a0c0e030f0601061e051b0c040f0605030c030307020619120501170d0f0f03050a02071406040b0705 76
    0x60390300030446400004003080302c05c0e90502080d107a82821280c1d0701032035041d4600080043c00303000118142c01078410310015103100f251015110054800000c00b01180c68030070341d2080500d400c0903440a00d0803070004180310306090350fa540360000d0b03a122202c00c54015200c00b500f4400c900b00403c00c402000c3c03a5003000e50a104840e00100d039108401010b0324882511648014441da014a410320386e0b074180901a200740c0404c8810803507440500380304400010f20424001c42041d4030141f5000301801d9540e45135480c00d04240a810240d440041014a00b0b000b4a5008911603075140700700a403541c070300c42c0d021a1852a00e0304141c00d040101c0300d070310b0081c2c01c2003140e1401641d41d68101d82a00d241c0d4180450b11800384602100c001c441030040009061502002245841038140301c40040b811140486a070405102c0d81104e0703541581c0c19200104003065009044980690031142e841a5100740060030007446d07071540074080300c00d580e05039030f10740000d03082c030040c0300d400402164802036a0409a20300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 465043057 1250 465041807 465041809
    0xe0f010305150d020411030405030318010b06040b0c0f010e070314011505090403050f1b010b0a0e0c0903030d1d0d08010f0b03071e020c0a090525090911070c05060702 73
    0xb1541400040c0d100310206581141195615400b4074244049400443d44030310f42450030303603541d034010b581c2c070942c0c00c2c2503050a1840700b505006191495034050005428907242c0f2600e003101d50403200c8424024000d00c101c1000380502440780f00d000051030390080510078a0b60038820010340405103620000d9040c01c19a0001544510300002102c006444d07c0c00544e0b101d0800710740c0c90084131003049001c4400110800c0719500c07a00d031a40804107460080200c128402c04001084080340b044030b4507440d50303100180311001d0b0180544079a0601500b602d1030544200550021a002500505d803908002c5149080c51201003101c10740741c03030035070602220725414001081c0c4026501e2040006402c000400100c4142c42040d03402c08041440d071000e0500784003139201949850780d01e02e900313000d1043d940c40015019690b0241a00480c02941065154000c040c40c1b25070398410001c80e01d0900806d0072000400090600ca0800c200100b145400c0e10703200185400400310034168816442018203011070005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 465044307 1250 465043057 465043081
    0x1d160603050f01032306010905180331080a0c030b0105120a260304060603200f1203071403040929040f0b0a0b0306120a030813051c0e0f010305 63
    0x540780c0060105e00720030301a4940c1503680340854506911800f42e42c00004908c1865000240110802c0040506074140100d900d80e482c003502e2120f041c01fa1291300040160b01751509114515600800c09488454550b200300d450007407006800ca40184164804000b8028103c1c4d40602510084401a2190709403028260b279904500d1006401c00940d4443e5a40c4040c600201c80320b5401901003580e224a0036040c618010b003514403050b038500d4402e01c02c12540c44a4039820041c05000248040000400001404404116a0500c1c00c0720f100030041da0f000f1074410250212498034060045548600b003d15400c241c2da1001303e040c0310210514401000300b02054040b40080609940000f08000d100b02c03a000a0002259450b42260009901044130a12200207520401b4140c81084c0480f110540c920358031403000130064001901040411458048851070450050042e07007102c03034020140d20308006001c101d80702c9602083d00072880349040d0600d4000c1c0403a660090904020742c0c038209010800b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 465045557 1250 465044307 465044309
    0x60b03060906010932090c0702011403010506040b0c071e030309050603040807030e0a0513020a030b120303220506010f03031106070801060c05010e060a0203070809030702100c05011d160603050f01 86
    0x3d4105c00c990391099000d50121500081e150010201c072017500300b0f030061790303038941c4040c0c41a400601419440902c284040003164100c50003d40524a400d28100c110101c1d0340140e42e0300c02c41c0c2d0083c1c1c0c400051031081300c940000803c0030400704a414500c0c3d403501030540c0001c2c2c2e2001d4040c0c80f0500411011851810a0b5000da079094203200d0b0728444914001415807a0f250404e030352014010140c0216040f0f1035000e000b9003a0241c50070000803203100104442c5d50010080101a03510810000b62000703d03018402c880480000440d0010246039980d107404e02c94240c00611641c50004010028147c0c80107100f061640d074030340513101608040900900c986d9050280001b4400ca0350f0056080000952152400c1c1c100e00d404c0d1131050414000b481c0181d0300544400d0001f68918010581c001004001c032020726a0080205000e50320200b82074511091109040e10f17603542e5142580109500030101202010904000c0c1c16203d8420b06a40802c05060300440209850711042144105c01d81c03110178 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 465046807 1250 465045557 465045599
    0x40305070b180d031a06041203050921030d050c12012115021b160306050a0e0105040c030b0a09050c061e0a1218020d0b040507050301060b030609060109 67
    0x58036a42d01c0c0200c03080c0911800090410390300c0351030200410716525a11981005200740001600d040c0100c04001a034000c50280802c00700c001480d00f000240928000c00c0303108400b5088030102c04801e4100e00e8031001c900200c9003160000540071030090407500c11294028000e480460810501e0807003ca612241401401d40003a06040150952481c5100031440f080e404590b400b200442c1c0c0c84142c000e900b10501702140310780c80c2031003600100303008200400c0c0e40c00100070060b032040c030b5612141e0181c000600b8205520b5600c80d0401e4030030000b8020a4801e602911100b508a8650b203011001c08000902c1804010b19041030040050310105480c4a020401c445140c1c03a000d000c890598212458145002c0110001911080440d001510300c07003050101d6400b08441e0300349030b0706100c0340c00c6481c80c000d42c40b105000030312000a00448449401c28003c5e01100c81050b2510086421907a090304401c109000120411185280500c4565806031003842c010111900d0710700c0c5400400082e036810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 465048057 1250 465046807 465046823
    0x1103041b0f03081e0408010e0102041d06010f08060d121e0e1c060e1509060702060c0a0f0e090703140108150606160606030803010305100c0503011707120305040f06020604030507 78
    0x2660304d602e8814150f402801e201d40080143c1080100418000d501c0b51040451a413060b0baa40d0748103c2542d02e415204000684540804200100703003192004401402a64882c0c9800c1100011031140c4402920704102074840b900062010403050320b114640b407500c801088040d0707107807c00d41e45410451941d100c0035081c03000c03101c000601c0c280c0040c2c00160450801e521a0001010000004c08212405450f080e8140c58051711101d204a0300c0341012103607005261010010140f91034803e41180f01c0e4588107140980c0c07030002c500e0004200910998502002136159a50080b07468000302d881030040000d0070040080d8a0030301c080003c081402002207200304404140317120001c680349444038800d41d03c280f00300141a00c0385421000c60b04280000d54161041c0ca8008490980c0c520540c0c20003451611014150f0303103441d0314207000d0000f072482040355005d280e00015220a102c490140010310a84a25413110700307102c10010510303041e910040442d4003030001c2c000800e0f0000c0440d074032141c201d098 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 465049307 1250 465048057 465048097
    0x3020a201b03100207060507120b01091505130603020306040b04140615070f15050c1612050f03100312140306060d021209010903030b031605090a1103041b0f0308 71
    0x900f4061184410580030340002549010444160b0100784116055213079441001400c00300c0400b00e880030104180424120002480008620400d0003040d02f01e91074032074900b81d540060000001e03219800340c008a6004070911a1030324242c0035603244040b080d20100592240020742c4010510081c04a6010740360217a81040d041c00c070142203507a4107405c401d403842903042e5450310307882e04c03550200140083c07441c11011a42d000310708030454803110080002c0303003000a40c0d42c49814465490361458400c0c00001c125440d091290a00610710800f44d50140001d910b145007040c0c0d00854900000008100c0303040b0200c40141306503415250010000e0702c0d840d841d411114007450092203032004101c00a851482000b80c40c00e41500070116003407003a41c2c180000070036001403655405000d5203440102d48000000d104a0400341b9541e60b1000004001003404180c0301601d5142e98001e40c1c042c4e0301203070082c00d01c07002442c0c0d40000c04010045a546070248134555100c0c00003030302070320f4038014181000000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 465050557 1250 465049307 465049309
    0xa030b090f0a0302060a140f060915030106030b01050f0301061d1021060b040e0c06091f08090f07050d02040b0102010f1113050901030b07080702160603020a201b 71
    0x3100d14490900800c40d0b00036010703828041c1d6100340450f540c1e03611030705210f03060203c170194810444c010180b03003017007a190b51621400c000700c1c07100040401c0182a800b400103241a9024002e4600950140007070301d0305541010305110050303440d0300d0007074002d80c100801000280703010a640e103041c1c0043c5001122546408401c0840343c0c503143e1000c0d4904041c9401a10850042d0640742c0d03010744564401c04c43e03418424240400c2e15100c0c403444c500754000711441000b5051032001802c801c4001019040e44035103145040c90320700001080c0400180400080110f111800c1141d034400c030300000010070500e03140c02c000800000007020008d0140d525070a4078204d83e4000d41107425069071040041c01200291408024580c004650710000001c4d6140009450b0070009502416a5000004c000c0999690403050710b0301a00900440214880c84202440900b10180358070050603190790050783d20390310814001c0c04840703e2403100c1e10800c1c0b100503048081c00c0014041c1107100c04d82210120041002c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 465051807 1250 465050557 465050563
    0x6080405100c030c0806010914060f0405030a210806030607110114090c040b01030905030a0516120807030e06100501120f0501170609070317030c0f0705060403020f0c0a030b09 77
    0x70030032105250816050070107103901900150f801340260f96504406540d02001159005950b00c910380c03040900c031501001c81d0414030001c00215004030100d41c03506949902191500c127640c002595a6038110500e1414491a011402d40002e03041ca0113000d182480340c0060344821010f0f00d103000b8005c401041205801e820340000000240c440315858245c5410300c1f14503110ba00030440d640c030462408056081a600a00c070b03001040d03030400000c0d810302000d020300780ca9542c42100e841c216071031108164000203c1114085c1c00c5c100240c0e855450750704040b103014094034a0002c2c110310715000380080014008140494000b1680d0901e05841c403014014415030040c01c0340e00c85c01100d00d050000120700c06480f001c0f081e10480d0105d0440c1c0c00e56545101c0e4949400d10ba001c0100206000440c8403040445200950341000c1d0f258030f070500e080c40b0f044071001c2d0b9511600040710290000400c02c024540c0600c030f9401e4071401480034142c407200810005042554900000b041710006d0004a421310b4020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 465053057 1250 465051807 465051823
    0xf030c0b090f120601150c031e031b030f15080a0b040606080f0303061002120d020f09090712050906011827050a0b0601090302060409020706090b160207091506080405 73
    0x1d030a40349072038480c1030f005403114000d0203030740008695004110140d81c820789169501030b400d56541d5036400c00032013070440e240c00350f80585020551919003034039000c20354440ba440d40d02c1c07032902e00080240d080181c02054501c203660400c1c400c0340004007048030000104400d92081d6218a6190040e0380c1c51130320703134028001a0031001c894440c49803072945440700000114000e6608030350501111404107800c0341d44040c2440d00c0c8001900074091403103020407a03006001d4004030340c00034074105000344d00400c0314804216020000140543e0b10b45035030709954414150803040c0c4030040c040541c100050360904080d40b40401c0181c40c3c0d16034503224407081c00780002c511050782c200c002e05002c04030700701940c1e603024803d820741d030010484021844c00e6000740141c004032a40642041c2c10940341100c03100007500001c40596034161603100420020b8800484544100d0030010306a40142c03495400a16080968016042a528040318661141889501c100c1150550328022040340d5852a1890400141d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 465054307 1250 465053057 465053059
    0x80109020a1e0c021207050d140a060f0f14090d0c14010e0a021305100b0c0c0406090c1103210603030c0604060203040b0f04121d0303220f030c0b090f 66
    0x703442c54004580d4400c1c00e28074224001c8a1007283c80003c8010140c440c0e040f0310419a00584d8890900e0029000100070452411440f00341d40042c031040d141c203000d5a6070b40600b1400580d58040d14061000d841c0b00300d000d003606500448129203010303084e0564942c102004641406916002e020810006000c0b01268000001c0240038240324184600d03030700c01ea0341c01d04074801c051855820350340d980e5a10402d441a004002d04902e200d241010701d03a403e511184201c036160186c0709049402d9281c40c003400c0024184408001619841d280d0300070b14407140c56000740c03c250800c00000035070a150240103a01d818070302c00c0c0000c0e1341c2c40d03100c0020b10354400c0074598507007401140308220070f2101d298080c6128500819034481a9510072842d4020300303070201c030b00400761202f00000c0140c1341c1c0704a440048034881d018100400504000000349581c2001600035802070101001c0e603a82e1410101031001044010030080c8590b003107035a2200450b40b030340610044507601207440f10f00b555420300c0031443c440b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 465055557 1250 465054307 465054347
    0x1090510111308070608091204053d02070f0b1c0b0d080702030105160503070c060b0307170f012306131a1e100c0206130b13050d03080109020a 63
    0x30f0356000440d201d180e80d00c81c0c80c000c14501400503802c0030000c58001d46009000a07031518207818001004601d604403080000d4000b02a401001d403114115000b0b0070440011140900c1c410039000024603080341c030b400412a00b403141c07104100d150303003000c165030070210307190342805905000200c006c2c000c0040410250b888441382d85400103000160000340717042c600070b800070f1080c0d940302c0c1e8040c2c2a00218082550018a081000892040c8103650190b86980726a42c040740d02d00344000001d28011268200c0c041c42d03511f540301c2c0d20b4010020490740c1e8035214000000d0040a0142c4809114030055100a2a000303581200146595803000000180d071041c0c2842008080e4803420001c2c1248183c8000e02e014503014a0b00700700101c030303101d252205201c2c0144260905d81905600f04d07a14a600202260020000d0200c110313004450280c150103004d0480380c546d00c90720f071030b015134001e40f2046e4400750080c0f06c00d403810300100390b01c111124190707401c030342000d070791402e140f07000301c603902c140d4004454a04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 465056807 1250 465055557 465055559
    0x924040f08040e040606060c0305030f0a090506151f08061207080109060c08060409020901050607030c06020d020a02120c070b2208101116060b060d090c06080702010905101113 77
    0x86100f5685000b140151005c00c0310603107513001038403030280913140a808603c041c4001380c0c0ca113101151190380226400b00205000da041da8800740b4080055903070100801c419070700c41e1040d0402202100031115109210010402481c0700a410b105000d4901130207013011040300c215890701004800e0041c04044000c001ca1503160802800400c046421480000e042001040061419020740c40340d83d80c0040c0040d1003079290504001c800e42c00344404400380448440c1800100e9040d10103001301201a6401596031600900001d0600d000c2680b0030541100074040c1604050001840000340c900440400e40c2c1c5604804410251140d0500b1404004444005c0032a40c1100401c900340c841138502d4041c02054880004400d45006242800256040e100f92102c04203803d0380085c00300c0740c1d02410413450401205507810645071a0300f41621003034810002041082e0b840390b00e06501a580f48002c001c8404250b0310203888242c41040554119241e41d402143c19007843c0c1181e40181d4030000b210320803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 465058057 1250 465056807 465056819
    0x602090123040620070605220311040b0a0608041b03081b0c0301020c0a08070305120a050f0a0b01021b030316050105010f08070b0409021309050408030f0924040f0804 73
    0x80c0d031181c000c81e000103c40d403113042104803000d1030000492148001804049040c07000480b500d0700303c4a0744002c003110a14000c54003c11900c3c3c03040245000d40c0481a28003170940078030054031107010145000d00440390003044460f82c000b0b031040e0010390dc04007401c02403011084034024000d2a0708050a039040002c2d580311099030007003030507140c0380004041c0c4042d91075000416080f802900e0141200f50002465800040c1c056002404894030a017485402c0c032034044c0f81d00801000890716071449580e45c1c828881d0f0a68242e903080d40c803e400140c01c1c440f60380c6410000b52a6204140d00c003034900282ca0f000708869034248107071500004403105d018201d40c0581090360181c4028071640105280c0392401043c03a0f100807948000b40e40120341e4040c41e003460015074800951141846541d06050103401181d10070490103000d01070340c060810540c03030b410048444004140003800b0f01c0340652240106022011000103101001c85c2100303034850603903a85080c00d900c126603120005120020025000c030394 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 465059307 1250 465058057 465058127
    0xb070f08090a1d07020c0112020c2131050f150f090405132102010f1503021e0a0b09041103010801090519080f0306030c03100c030b150706020901 64
    0x25407105403c803800389890f4814180c2c1c172580d06d00c40150025840002c68200c501c029001048401407070400c6400703004000c0c42c0a81c0c0c8580c400003026505000240c610b80849140524210355540440c0d00c040680700800f10301221100e51051600545d043e102440d1031b569010752440d001c00700e1804140d074814000840c0021070340440c08407841070f85020082802c6049609003201c400c2c2e0b000c0c0201903141c91189001c20b903020144038200856498900fa403074511014003030449000c2c000c2d20542116820741c8104140040d001a480b498103410310001c8000b0350740c18496800702c7e000c20304860303a980075030000324010304a074002c02140e80c0800000040c03449015480841411300403010307280c0036220780d02c50400c4c144051102811007001030201144200c0010001c681220000f07007281e01c10300e203800202e4105056860b41151450fa1030070b44008050f010301440c484100d040311102240c5400b00ea17144038501525102403c0d56602050900460b4001d0038003081c40c68416940c1c061402082d40d41c200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 465060557 1250 465059307 465059339
    0xc03090f08040f0609080309060c34060507030c1104060905040c05180702070509190905010b010806010314010e0402040b060d091203021809090715020604050f070b070f08090a 77
    0x7808005609000030300c24420038180c826140c114007e0344c501708560381045007a40114003d00802d004144a901500f001c032150141400c1001c00fa64a201050420042c0541c0030b69012500303004e402c000100020364407101960741181c0c003000041407006064045802800300350401059076240404dc4428403810940c58421200104d40c86e141145500451109007282503034070700c0141c1c1c414141801240343c4400d411f80c2c420017025021308020321000084060703c008040c00d0341c0a0350740388881e00103564040786490b8820002e00b0140201484580c201c3c1c00d02a05100ea150320403c2480494115030395074100c1042418014811600d40004c0c0c020b031401065002c40460381551820a5101000e0003402502c0071010b403511a815102410f40503c84450703402030454010303020307a91000c580707401c0c03c842c0c40c0d0062046500074080d9203080d00d4200e04d008409510100036900c200c0e800c1002050460441c1c029030b84c08a0641d503108103520380396180e802080d8a50380d0007c03040002240880c2503843c80701c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 465061807 1250 465060557 465060569
    0xd06020f040f05090a090f0b0903091005090a06050306030a030806040f021308010b04050f070e2d13140106051b06010603091e12180f0605090a090c0507060c03090f0804 74
    0x101c16510b5080f080c05c102c85541d0307401000c0d0218031a00300e01050b1900000c0f40d020300170400b038914050903940010340048a18503000041000803d600c03140741030078001c4002a21300303420300d10311b50f080040000c1c0d40e98482d1000141042442070014180341c4441d08001c10071100c0040c01c0d5240c15010340003045400c52801814419807900c2d50002d0f40b45098003c00b4003554140403044ea80781c0340d161040b2072200c000c19003076410600300d018400e0310743c919158141c4400c8092204c00d11184141080040345569a40b00c8400d060030548482900c607500028030307045650030300303000c1d946500c03201d50007801003059004100380380501d000005105030190050302289200ea4540d40da035540388030311410503030501d14018001128844902e0840c5002c1c1c2d00c80f41c0d90000f42141d1b20401552400e60b40740648141c2c114800084001c654444035090020380070300a03040040060140d00e5580b000141640524280070b000c2c10f44858142c42c7c03181c041e602819100d0303000501e580040004d421304040960084c4200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 465063057 1250 465061807 465061819
    0x70f080708071403030c1e16050102031008030f0406030b030a0606080601180e0604020906180a0603110901081228030c091a0301030f020a050d05010e061b090d06020f040f05 76
    0x2440200d40041300301c0c0d21a802114416040504101e0303d040783c80c800c1c901d600080341e801c01000c60361100841011442e0351141d07001503581d19051807806c9420440e54011019a48180b00c081c0883d081c501c00e9400391051032074000745984030000002e14218001901504036840d0000100e80300101140103416282c01c1c962180059446504a074212520642c02e103074181c0000010400603d40101c510390480002000485e40b00c4001c6803007408a0302c156800c019030b03075544400300100003010048840c2920101c980d07401662404440b16241c1444444a00000200007803040c03014500c031050342e24035550107184d44c0100201c0400940200fa400c0c03040800320b00c200381d0020782c11020041e0b01819854041d940303410359181d6503131403036207603d0100102e034041a00c06010035240c035840b8030083c03440d024070004925440c0d29042c031814036001401402d0720030b01d03034501380c038044074640c040303941100e0140d03020401c7ca0000d08280300240552031450315070000000d00095065008890901641c00494035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 465064307 1250 465063057 465063083
    0x51507020307120f12210524060d0b031f1a1207060c0816080301091107021513150f09080c09040f080904020a1d09040b0a02070f08070807 61
    0x350002690a05100070070602c5041105000105d0070740c00098103c1c904d0428010091110781d46489803d1258200603681d03070340d0410400d20200d00110748413100d0240707072043c003101c1224000c40c441c0e201e81204654100c1d12600010034548080010314000f03243c100780c03004480c40714a4080080d180e4550484124117015050b800e07940383c080e140d80c440c0d0301500010540c1b146001d00c252403420170b0300301c141c85081050110141052480184102041c45192019503075810724481c0e40840d980b01d107214480480034400c3c0c100603210564500c00910300070b141c0c4d40e1900250b40c19509681c4054100071911018162100082d54105c1220800d040350760320341280064817481290341d100c0740f0071b074010750041410b400301d80480c12a00e91040d0103030141d11403d103421800404035041c0c0e0300c0075482100240340101c40b0300d08007445200c1403602e160f007160200c0160404d81c442c16403034100a02019805503001404008000358800b0795549664040442d40e21140d46082104464014410a986082040b40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 465065557 1250 465064307 465064319
    0xb040c08070801061404032307120c0620010905030315030309030d0c03022107140a1505060402090301110d0e060412140d0f0911031501090b0604051507020307 70
    0x4825115241c00d41d903034a5142e1800404580c0362840390301e041104c52080001001040399516005001d5101c0c100c0074950603100b1003454901050360b0b220304502440300c61400001120f100c1b00d9000c0325014034084003c90030070302e8121310440a10150803810362030b100c3d00c88200040880550b124900c0e003071480301e00707010003014151030b0700c6146003a82d850381114000e0781005001f0820002920f010340704403008040c500240746040b0317242442c4c1c10069000411040300708074003414011a08401000074140c100399681c0d4200440ba40d0444111a464640001400a444aa0607a00f0650b0020000d0181d000c034074024002540c4240002294182052039000c0c00340c50000348036000340d60002da00320038903c2c02c00c000c48607882c081c0c41865007240c080001c810600d1075400f9000701001c151600107448220307483d144d0304141108214030701a030043c1441c1000b500c403010034141101c92204011644861100020f003085c0306030b8010360390000d84110b41c04d00c502c6000c40601100b030310035012034603c45d072200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 465066807 1250 465065557 465065567
    0x2040305030906030717070206011a0c0627151005060a0c0602070809041d0d1d0415030501090b150405040f030318081c0f020408120a05090a03060b040c 67
    0x200000e0a030354401c2041e0105420030400035503010f0160700e04200308072400140b03440c42082c20b5030351100681c09040140810000115021703101481205154545069411019100c100013030140a40c1c0c0444181100144499500317000800380d1502514403198131900540c0348050155175060924420250200e1241880800c039075072912103448403c9041841e5580c200603500011003164800e0050001c0c816588407402005222440020540d0762043c4200350a454101180f10b003500b003108000288205d05904e10030941c0402d410b94012440c10100f036542000161207500040966180480b00c2c0188a42c100d1a04e00a44140d601c0d01400040c0700d0400c403c0d94415240a410a0201e00004000a000f98081c905000c12480320301e80e031802980f039141154000c070101c404440882c9111080c0850b2501c40d0001c1040602c0f400c40c1440c1c1400326041d56203054001c3e004006000043c080003443c01842940d10f6260000d005808154a91138401d01804880b03156500403400c1501b9845114003a03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 465068057 1250 465066807 465066809
    0x21b0118020607060603080706021207021b0f04200316020601030201080a0f0e060901020c01150b030105100909050718091a1003091401050403090b16170d020705061005040204 77
    0x80301440325401502048180c0e4400e882c100c070703819a950400070015107148003400019010b2031b00143c032001103000d241c0c41c07a02c006101c903003150801451290204101001d41da85500e0664803924042c2c1204081401080102551904046051000040003981100641c89020480d01c81014541102d205903907a007020700000380451289400250712152030390040b0818041d140c40862101c1c4079001e81ea080200a6404982c0e030f075000900000071500900516150007640d0b0b011001891038403910003640c2c0010b0240900c1072046e8120780c4a1f55110745505009800342d0710040003541046180501411180214000384a02594000034602c0051085402040d138240b2040c003850061030820400c2a41d80e03148200f4540da94031040089100040d484400e989040c00003c1c25080c18200a0000c800e1540030740344a4804011a4441c11504d03075054075001d5000b2a42d0580b0404489210301500820308910000ba2011880001340040041c0240c01110000352400d181340d1904148000c0c4d1081d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 465069307 1250 465068057 465068081
    0x504120908160905041110020a0b0105060a02030904090627020a0603020c0309010c02060f0a05090a0b09100f020c0d3e0f0406030c080f01060504270c0302090703021b01 74
    0x41c0c442004660708a42104ea8810301c51340329450040da40e1000101107a6085081000603804150140c04020088105074003405e42210b640d81462402100255030344207525a56000e5a1038428003010030440f50401039004080d0121160b44554400b202c440c40079030b00d5003e81c45043c2d141c0000900500a10850300e00000c007201440c6464a54001901d800384c10f450100d0b0049804c200d0180c81241309000382c8480319840d5906941c039015041008103614558101002c9114100801151603480311095085000f940c00e03d00144044804142c4c240300c2d80e12502504082101380460412605008820869065001c03450002da05848031701401e0380d04a040e0705d01e1024440811850b480d120790300c1842480020008112140c99546903402e180e030550005c5429032141100e0070551400303020f85005424280c4040103880c0912a50801c00e07011007941c0a900007070840c811041c4031008000d40301554015100490340d0821000090007540410511584d80c0008a06082015018080c1400082da = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 465070557 1250 465069307 465069343
    0x40f110901120f14010e0708150105011704080409050403050705100507050a2f0705010909050c03041e050d0f03060b070203030315220c0801290c01020d0504120908 72
    0x540e030b0364043c040049000a0741c62904080c41480218000d00401c0010280c060185c28403a1600941340d10780b107031059034940040da9120052103249d134003a14444000c46041d48400450300c5d24103090b0418403458001e017595500707001c03c1105241d081340c001c0988510420031240d4038190301e05081c0440c3e4042e1100d000107102046019490b600c01c910403070340c0c0042c2000a400b03402c0645440c55401345443e160403119089043e041102c0e41c6c122410000030411004148058a00340341c850800d4400203000030208100c0852000740e00a024001c0300e8a9a88002105e1006c1c4100034040c200601c40412140000d00f481808200c0c2924441550000c5901500131411a2a903291025503d00e40b10000c6030032034611604000b551121900e0202d0514124400048a11602c100100070100507001001d007880b2428604407130341c03000300070030060a00e012105901c2c3c20303004103080d019100fa0822100d0460601c010700040c02481044017800341c0941d200e40c0c01059880c0550740d01c940f8400079680c2140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 465071807 1250 465070557 465070589
    0x50304170705370b06012006010603050c041202010c06060b0a08040203060108070302060f1e19020c0d051b010207270501060f0f0c0203100509061f0b07020f0f0306040f110901 77
    0x2e9404c07040310303002401410141c007021803130900071402da10044012003059011100402000f5010700c502c0307400580e185411450a070800c1c8801c010b0385500740009040044101d515030034000580e00c0700340942046c1d44000e58032541c40e44018030304c11090b142640310f406000c00000d100c5900285410440f136001e07201c142403c03002404209650841c2002500b00b000344040011220941801014140d41c02d907103015600d2401c3c0c10091400c50510206400740b4450403403840400d00002c0c0e40203601403080c6c00c90303507400500c9004030b081c0a0b0650001c8000940c860600d90071050440646c40308440588040000742e90781c01c1c0c12640076440ba0340c9400416910248109000e2040701c80c501c029002030102c41520a540c10354404450302100e0a20458029005107c01c8030b8444400d4810403512518001c90142090b1141c0c185106000c0002d02c200201d00e4450495292072000b04d03142003004003501c91034541030403c141c4414254030120b400b0600140c406a00d0310348000b00e40c0c1601d040f050402520 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 465073057 1250 465071807 465071813
    0x4150513020c070504020316080f07050f03101503060918170a050c1005090607020d0203191e03050717040b07080903070c141201060e060105030417070537 68
    0x1d500140c075042c054042c0e4440440d2548a0380011401442320b20500450078081070300040c820300001e018910548040307024046516800b03400d9842d40d1300d0109806540391a20a1418448034280d400a00400e100303007000c0c0000750b0190701010031940e1031007043c440c80108843c007403240712449000401203188408003038100c011072009070010848900b801840c044c5010022443d101145030040c900b00d488074204100607809204e00d070b410140d42d00003402c0e07100380c13070070003a48034010080344080e0076044291584226209645e07078005000c802078003074400c01c070040c402005004225811070200d900040041351210031403868910450300400c0c111101e13100c522044400c000003030108121444103000302e03408684814015001080304a100d14100006441407011003004840d00c202c03681d01d4500200310fa407140d164800c0d072008003403078820703aa40d90700d14010400c030b0820001d1074224000400e012080200024045414a0602c0714888200c00910320518421030b841d4101c06910714410105400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 465074307 1250 465073057 465073061
    0xe0c0603010b09030703050109061a120c060d110f04090c0918050a270b06121908160b0604060f0302010f03110d020a08150907020a1217090105040204150513 69
    0x48920000c00741d409146c1e8944402c0e080d28102d620548070150f0300c00202c44085c8600c1c440080c1400103581d91a0100c3d03480b1b030030a88451210a2090007024009604a50088e09900c104004880070060340c1d280d210202c40c0e5810703a0400d02800854a25241310130f60a240a00e2a803011280d48044d804420344508424001400014045481c82c68032035881c0c074080b2072601103500a488031102c80e2604020316003003020600070043c100e00d000740310004100b0252080416180080c001440d40d07114000340514001e0503912482d041c403503101d06010742800c02c010081c1e82d42c030700030b403400c440c10710040c2c4e00d640c4101c10b1440680700081c04219000d0700c5414050103070b0480401c1c264240e5416042c80d000c0e07413103d03083c2d900400b800700010b2121800c200c1e841c0c40e00b101306454002c0985075108103181140000e561032140b06005010107070100e40001c410b078440d109408111402d492046200c5c280342c6036445c003070601620100e200390704112403e500901451040c00880d440140f07846042d418032303035207400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 465075557 1250 465074307 465074317
    0x130b01031401110a0e010807030501120f0c15050409050f010b070b1504021801140c0703021c050304090506030c09070e01050a050403050106120b0a0e030403020f121f0e0c0603010b 79
    0x62103549031450100c10524940140103036804c1d603100c04881c601d4220004155076002085807042c585810014401e031500300c110b10009550141404510030720f0307414100c070340118552002000c08070003c80c0130a21603208001e4002c80d41c590406020a4448140e0801200400d0140c05503a040a21618022482c01c0c020a034200c58004c00e80802c080b154000324081e640030241080100d02103071800d541559021903580c0324000d440400505088000300c2850710762180d44800303445003500c0700d180080440c64040c0226601e502600300d0f659141e40301004d9020741412103030a44070f80164100703289c1c41e0038405412440f07003a0301c0e515440885400c10041d40c043d00290800b0301003110901010001030024411400074041e80b0b2140c0007503091038617061603034443c01460000c26504109529240a1000058406881d41102c820340400c440101140e16401100d121070341d01d01c100f282030b110110141c8141c50b41e1041c4044180710442044200030b66a01340c0c03030001508280c0800041002070350030741c0545 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 465076807 1250 465075557 465075593
    0x20f0d0b040e060705190e1c0302160801060e01090c090e0c0c06040b0901060b120708070c061416020f0c120304080f010204260c0f041d0c09130b0103 66
    0x542c6520007590b0b40c6400300445140300850400540300e03003250800b00d8000182c5d805031400683c800e80075804a0040c00c00e644a080c25442041c8146003018002c1c402c5404041c041010800015524640103004e08114480c0390051401c610010442a406020741007601c09252690b801035071506105e148805401462406450414080c0741000001031141c0c034015402f40c1205030303d60a192481508540d0795511034403030720204100718103d041410003045d502240b1414010744030f94404005039217030720081c075006149624050700c0b140c59580d000b001c54040d1480c01c220b90410801840181d1340d81880d01103181d210f0384910b5260b0300364039081200d91021b4294106990409a40b0300b207540c070384510726400e46140e940201e414001204100e011415400151a10790b6608030407041c40b5441e0105a800240504080e02d1000c000f510703103800200d200745180c41680c8500500d001c20a44560503500d0b20382c880d150b008045422010820f40c130a0b0500d40010400c440781c2d2855958907800540f40f4049 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 465078057 1250 465076807 465076811
    0xf010f1d01020709090804081209030601140319030c0c09150528150f080103110d050c0306130b1506030f1023040e06010b0307120f0c0c0510020f0d0b04 67
    0x3141c05851400340840c00c07440b460006d5200c0781040d602d582001600702480382105c0040c09082e07065500003d5450450754480d180d19a850f50800109050000c524250030605102810003000c25920044840e21280103480d00e6211035110598142503440704011400c14a03d064400c0c804e40c0740c4440303070841100c802420380e050111003800258040200d41d010140c15040301f40f02c910030340e4218010a10080c030038500000f156065523560040d00b40d00031041805110300300151410801d0800010303500120040c21038080f1300d071005100f40714400c000e0b41180c6000214011031041c0c6d580a8240351101401050f0600715950f80d00300c4004160000c004050004201100092244680000d5806141d1200c3c03071130301d8001c0110600c400d40303c000319481855803011004000000209042d01e400601030710301401140c80f0240940c000d40749107101c2049003485d00c000880e800760050200041c851040d803c0d1088000e030040114101c1c000c001d846104803404000c03043c0c010400b80d0005c7c1191800030700c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 465079307 1250 465078057 465078059
    0x20010507020405011d1e0f040f0f05030307021207050303070804020105070b0703140c0313031b06060f090b011e05030604180515100303021c0509060a0309020f010f1d010207 76
    0x350598001781c3c44000240d1501440f1101a1129200f056104c450031300d904130883c4026400c04c11203100244072170040d42240001c2000c01994800c013070400394002680a148525030300740701d80c50f0742c004d840c6000581300710310001c50300040c0c010542e180d40360000051420340c0e4501c6401d03140842d00400c100e0400c0000c0200c90300050710300809500414540d0383c00660130f41e950304035032040540941401c1d0404d200344100140d00c100041d10021550385403400c0c60122807080301e8030806c41601c0781e000713220303505004022920310400410f04084518019060160f00b401800542d962808504642e031191111203036245024040e60095400c01d002620004121460158132004007c543c0421103040d00081e0074981c1c03111002c3d003003941140d03418000e40311180c0343d5503020b5900c991068800075114414104010380b2070059007903c12801000d0f0802e03944140f80f1400030014002000b080b8032030b1040c1e1643c041194800c034011503031071001b611401111482034080c03043c12500d407200c3d1411481843c00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 465080557 1250 465079307 465079309
    0x12060c090305160f051e0d061b020f060f0103080a1d0a1211040501050102030a03050c07020a06020706090b0a051b0c0301061d090a020f0603040501150e04030f0c2001050702 76
    0x50034040a101d804400c000b44e090260800d126000c03584424415210100c2000030302c028900f030720b07490328404c8491190003c5189841006082d00d4000c40003428222407461600e00e030045038940c00500110306980443c0e41710069100c00403c02e000190176060107000041c0424094035200c2100c10034080312011000641c0000b403d55070f803a41020280c184040f10450420550f100954030000080fa024001c40d070501e00001d5a03400b449500808254550012484880e10b81c8200d40f1174a8010301305500e030035110700019549041c00d00c90381d00040d03070442d00028803500b00002d0f070321126096590186003100c1e40c220040c01c1d2151042c10511400341440c4100e580c1d41c248603050050042d05a40e020380c492515020340d040a00070981c00c0c8a41207072000301c0040c2d54032800c803200114111002d940b682c540d410920700400d00c140011015000c038000c040382c00c3ca0717000c400310700c035911aa03299410810380400803903032030b400f410340140040305000045140885100305986041c0042c03520303a0501312160 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 465081807 1250 465080557 465080563
    0x20d030504090c110c0d05060c0702060f0a03020c0f06010e0c0c010f0c180e090312180304030f0c090b0f060a02251d07050f0703050c0616090f12060c090305 69
    0x3c00340020075401d03a29804121018841c800f0300400403540c80840c5281c2d03850746a02d801000b42210004c01c030015400d81150340b200d00b40e0351540c207200c2e5055152544510003500a40c4001d280c03e40d1072180310f03000101c0d8000020302ca4140e8803544624034441d1181c0058903a10742001c20800c0c0e4654a034a07081381c848485114403002c2c25626510259031900002200030030702115005031803424825010070100b000c001040320000c0071903e0060740c0030356420280c1012107007050b03401e0703559000c0050000180700720103c002440c90f00442c08861010ba0700e803901412140907040d07030b907009030008a190b04203140000c05450b00240ba40151050401100e0a01c01c90040340c85c952a03000043c40740901505032584403a41e0600c071100c64005007424858005402d0340200f0700440c00c8018002008400c062040042d03400580b41e901c103d4800b030815a00048581100700c0e00e40c40000c8020b140092005e00004009c000c84901d0507480c00350b4002510f42c6400307403050404032018008d4201001002071810 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 465083057 1250 465081807 465081821
    0xd080a0e180a06050901062a02041404050304030c0b0315120102160b0a05090d090902070c09050408070605060f060711030111070305031501020705130506010221090310051003020d03050409 83
    0x1201c0003d8080c203203010840c054034181c1060040010010060315540c0c038801e028540d502c246481248041c2d250b20000380507002d40514060700d4805a0144020030500002500c143d034032920f68143d09a846a0807100b40e070100b00da40b01c500b108030140403d0581400c0030718015400305c1c0c40000d07142c900c0c03030080a4103031780c6480341c221000124401004101038540c41a560041d4041000c1d000d0307458403101c01410b5450900507503801030b5000034054104600359100030000c0c52100001d000d2840d26090400701c9810601c1c0a4a0083c20a0700107040d070701e006c0380c001d1442c1c440208603d04001c1542c488a500342c1448010940640d87d500801b64041c20040c01f9080d603038440d544056a03843c6c00d00c081039118000d500030300d05661106109110b5643c402c184508400b011400000e490f80e42c40004038034100c10000c0c8507015550403450f41c00302c1c0c41408000e103c0340394140e044070540d910307080001e011100101d03940c100903405400c0501c01403500c1800364030b44500910701b05042503103a45c1d0740003c454035 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 465084307 1250 465083057 465083071
    0x15030203071d09030711120f1501081605100e0a08010905031b07030209190f090303200f0f07031713021804050a06020306030709021206040b0d080a0e18 67
    0x5100d44070001d00c00340324100d83c0c403600190185044c41c030140e40b0790b0440c1010301500713407184a003c402a02001c030104400d06100b00c04500303d890b416105510099a41c1d000e019050850042100000a001040b1454802c50701c0180c60880ca0000d1020200c402c0d8054030b0032160700c20030441000803103070300034042c0360030a40c007400103150354039030103022540340b070503040034002180e00003840c10000340c1d1310720208039403124104800801c0e980400e41c00d03a0003440414030101c491032511420364103045d0f040d40040b051410001c10400c040680000c1c1d81d0740360007410034180c0b200c0c2e030801a0f11158403512010b4203e6038400d003403c01d00c41d000c520446840c0a0104c8102c80f1421264031054190702c0c12412244500328040c0e0024001e0420f9100c442d1580501c0001500440e00007011070003a8070308005000041060990454994201c2040d00d0081081a655248924280284100f091600400080c040c5a0001415192440840041e150f5600031000342e03600401c010301a800d15400761084070310443c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 465085557 1250 465084307 465084329
    0x3020d060f1412070501120e061f0b1c0905030405030303012c04050307021e03032808100e06150d1d0c01020c0118050612090609011b031503020307 65
    0x400e00c4070b980702a180e1124054072880c04034805450190012850b4001d443d002c3c6030442072415a0150040030b00040c5c101c90705030703106110801000000c80201c1403182810100c5200e0358642d10301640803180101e50304104840ba13402050044601c071030748903461a9206005482c01c250381c0307900281c1141c000341d0000e80e01500d61040c0c402e100700108013100c40c0148800188a00c0e050a0b04c60307a64038098800024060782c41aa440d0f060400000d162040000000302141d50b14070070310704074003100038460006203070007111307412600607403030003415000c0c442c0519140310040c1c28a0724200c440a80320150605030880500306041942641c6500100013513252804042410004c0201c1104c01a10305100c08020b40c0014900004582e4041070651020b14240b070049891511480140c8850380190f0000d503000354009100400c514802d040e4520415444058590681e581c0101c9820ba4035034050414001070901d4000507120b001741c1c00401d001d9001c00100305e03c42c0d2030342d0200e442e02040d80c101b418524 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 465086807 1250 465085557 465085559
    0x140a0b160507060f120e0708100e0f0c010c0b07050d060f030b061005040513020409020a030b0a0e01060909180f08090f010c021305041a0f0f06060705070e0703020d060f 74
    0x8070801440700105201d1400c40700c1204c2d2440e0007094a0078440791038444a031501c41a090440d82001810b0140c440c0f0015284003800b1010401300401c0e0324803a00c8071034000da201d25101d400c0301040a80300c491043c2c4a0340007511590b071b038440c50b290000706900305110f001d0100c8000c80b8024410b030005402165101c426076401c4d410b0501074041c005049920032991100d0101004c0d9000d401d44040f00c4003030303550050065501c10224068043c54000038400c91001c20200c65680c0c4c585c110150b80326080d00c042150913101c100f00c400d0f982c024080c0d0000304110582c204840c15081d070203054180b44e920b1000a000c1031503540c800c0d0711803034441c0c26201d0040114030344000b1b107440e5106070302c000f00c2401e09140e80c880ca980440e298460103484281d00b15a1840000c0030300c4140d14105044c90075050601c00d02c1d160040032466021004d030344d000841200900024803504015084038802038000e8000c140242c900007000040c000000c00010825800f0700950324005601d014281c040c01d4000c0001c2e6400d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 465088057 1250 465086807 465086813
    0x40b0f0c06130212011b050903010608010213030b0708071d0d08030916060c0c090905070b03100303031a060d0504031e031a040605060d0b0d0b0403030902090708070207140a0b16 78
    0x712041c2c0b104d07450141d1400c41010b05200d0100c680d4501c0c2011410310a489000450001c2d0051032170754801d22495000246604800c20b1680c901070030b59204503103040507500c6004085680002c1210200c0108001c0094103c0c0b0503120350018058402c000c00d0710400d101c0580e00c0707200a400544401006a0098480c110035100c1c0c2d0f000e04000e002607140590050f42c003078503014005661481501c0c1c486a40300e040f00c0c1808030902c420409000c03210b1910f42d9a040c20304440c18050002e20080d00001d18264101d41000b103801080090302c0c200400c802d043c0401201c01348010000504114140000c3c1e107200700d00c01d0024130b5224035070200c0e51400035400803180c42c042c80e01c1071800c4406100d10302d8204103200d207a641c00c050345c280039140311000641448a0011540d135000e0317000082c1051060780108820164160800d5511500c2aa201021900e403a1400d455503a03050b5000005a003081d5410b011800305605031001c00b02d0300400c5190781c0756540c03d42c00341c0ca80c8440801c81101094500d0f000c24 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 465089307 1250 465088057 465088069
    0x80f120603010e01180602220605311511010f06091a0102120a030b0411190c02060f0d180506060a151b14060f070e0405010308040b0f0c061302 63
    0x1400400300c001d0140c2ea1700d940b10705040d2a00340c00b0060081350701240008014482e07040900c1c0c01004040d43ca02c0098a820f406002900045480300b031110140c801882e80010b050302000340030210201c000030036802c000c1002d96107008603203d103040205841b40308049a034240a0209008414140028007504021400e02540d01d6910108a10f40819903084043c1e41e00240d0001c94656403600c80c0d841c1c550002c01207000e804084003059000b4109945000b845a42c0706c0180035420151800084000d11400b0a840851410401130350154050002807040100840181490949443c0c0003800d28880e240c1500320500a4400741c0300c5074401c04c2008040c0c101407034802e02600606171081d2031048580350007860003005002d0214401d0350407801504206112154621340540b11040e9000d615000008074607500040f600480040d01c210040c9030a4101031040c641130380e400001440c6401c3c20b06101d004141d000d9001354030703150e4081141c211900c100f0b0041c40e015800400c010f4100501c50f004000c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 465090557 1250 465089307 465089321
    0x140c031b04110c0307030e03070305100203071b0c033f1115010323031803100b010507110a150503011401030501060e0d0201210203012102030604030c080f12060301 72
    0x1003403000810603281843c900000b0344083e00c1d858582410002d201101003410f0002546c0024401c1c4200e01200741441e6150700514070a0344c1907903a05a4141c1400c1502d2101011154058181d052614060021501c8185000e0010603551860402021801000420203501002540c500c60f0300da85150681c940c000c00010800c20b144009201c62003844203019000041031100030401e00c040d40380c0708072245502c40c8019900c00c2040a03251681e40e03a4000c805100b04018101d0300c80e0044905000034100544076100c0c0b202c4c0c040e51820f00708a6956510501c5007442c0118683c010880c02c00041c0404a0580586c0d100e09503035969600c951400740703958480c0c4a103482c030506050500b40144080c076408100c601002e0720440700301268130380074001603400f45440707010360094040c1c0c21102c811552081d00214100c554001d9480740c1c0c4101d51840341a00030030800000d50640018020501003845110840380c5507010742e10701c40c9800e4004c0203e2120b80d10081d0b8881c1c411544e6010130080749001c0c0700e054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 465091807 1250 465090557 465090581
    0x507081212190f141501021c051e070c031505040b04020607030e120d020c101e021203040605070e120607050c030412030207080607020c0d140c031b04 66
    0x5040c030540d18125003080c04010a41002050440e4400c60b5160761070708060391401074114100211040c0241e41012a82c1c21211720443d41200a9049580c1d440012820480c80d5032141c24414140055802c89040d48071071404c101b0904262038080d10002c4480081c44410711403060303061402d10b585041410300c0b15101303464010500d0442004003244402454561140d41200c0c8250b455445107009c0c4d840c141101c0013650001c08001c030000e088040000c50380c01c070701102d4084a406ea0080400c000c4800340c0395907040d00291480030b003004d960254411800610385039005131020074282440040c0c0300c0d001128103464240d140c6041c040c4040e0803405107009441c1c242d480746841c00c11400d8003562494040c28402c10040c001840003c503100510540c1c0240c0a502c0b440302c2940c8030b50400940c1d41c10319000300002c0f402408003080c9400e000184542c00880054011410007000343c64072a0f5803220f10b03039103030b440f4002e20700c2040055406001e00403d99400c0f13008054000005404d11007100e1040c801c0c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 465093057 1250 465091807 465091843
    0x72708010e1515010302072f01020106050609030322030f03031d0c0f0609060405090a02040e070c1e03210e0d090e0105060702030f0d0e1c03170c09030703050708 71
    0x846056900d8142e000001d0101703090241e51a03a02d440c180a00d0a0440e00444000d10700000ca24010340308400f50080c000000da0084c4036080e01e500410207144203d400465040d8400c0004603410086501008043c0f81c68403035403141079950313848842d580320032a013044000070383d510a180301c04202d82d1410780d182002c60009101b8104000049000d040603101c90034424803000c04c072141140c0c1c90700200c0b4082e0002500701001c9007459010500a50443e0103031160040c00714001541840c440c80c141c40c4102d4220300960150814018800311024420105808201c840342a1601b480120410040804e04000b0005683c43d5100d040909002458190004100241a00304149142c1610450645104440d00d9aa40c40310b440000d00d4000c40344d150071404e002e49500b00c000507030000c08000c03480d90256140d44150282007400d5429000f052802404611981000404040100300310796100010025103803404c82c10000291800d2043e0b80112010350200303006110b006024030810b5552440701e40781d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 465094307 1250 465093057 465093061
    0x61006020303150402040503030c0c0f01030506060409020d092112020c070501050d180507031415041e14070f0b1e070c091802040c090806072708010e15 67
    0x3900c1e40310161524840a90480b14410746503140c0c1d0440d0020712004044a6403001c0854034140c070b81060950192250151b11844959175002f405820b00c1040b00130480e80c5403500748030209000790000a4664400341c1d491100e6000951004110310250407040210021810f00110081c00701444241002031940140420200d010001801130265075003400d200d901c880400b82c05030020103055615000842c05a503001003031000105054054a000b044144031000210300900c0d900d002001d642910300300b40000040c0851025060741418030000928941c10408a443e07400004078945402206500310b08400c010842000c1aa14021b10802c5141d500703020601203066251910342240420140c40010035038100400113041c00d0241001450030003055005202002442500d0340741240294034240e0101503281c020311811080350707202c10047c40181c0c0d8454080786c1c00ba03a60700303510740a03000c910415400f0300a0203500e2000707400800f00006003841502142d40c900a0520107841c102c11542007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 465095557 1250 465094307 465094319
    0xb15030c0a0504110f0315030f01020711010807201b010c0b182802040e0105100308090a0302090a09062a200a05010606140f0d1812050c0610 62
    0xc2440859000321000150002e03d811980040c1c801c29803140c21010000041207032840011f040f05010180c01e808580880440e005890300b02d200e480c001070314000c0c04181210007988a81081ea0b440000d130328007100b212044448000740501d6501c03011584e50442592006680c1c14a0108170070400c0074039082140351002c0e10350741a8681c010f011300350a84c0c5001079510399045c04100a03500e20102d928100107902c40150080504070b2200001c030311441c20b100c07401c4019001405458014100204640d5000e817440e521004141d01035207019400800d50f0708000050ba40710081680300f0b100701000481d802060303103004e40445440c02102c00300b8200b080d944040501c542110507030140c0f51740c1003800d50310590301c4501d038031483e00f2840c4400c2440740b11810020040f041d04200200c50090301c84444120b414144034495000f0050351802c01300b17091024494504039600014041d13482c0c00c2c120100940c460301e07000c584e54170320b80304100031034400500b1a014031070402c0f08981c00081400303410b0f000c1342041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 465096807 1250 465095557 465095569
    0xd031101050601050f09041a0a0305010509120c03032e092703120f021b030a09301a01030f1209031106091f0201060807081209090a090605040b15030c 66
    0x259600603a0746040b0150084002441101c465200504061927680d403490018003030081111100064007820400e9400003290b0b0040d101100020380c0618107555a00c0c08400349514544011240500303201580e0505130320046081014040248d00845c0d24046603000c0803241d10041031842d01c05c8a016466004a948a1030b0250456151140898203200c81d1500c0702c041c0c098884280c01e940310542c1440340c8043c0c0040107103070252250f150b484049940c0e04002072354040303003c0c1c030002502036801400428802d2480a00d4a14850949840c0c13445111072180c940310426001155001c401034958818002070009150741000e01d07141c012055402c60f61103404802c030034443d040c01038030080713403142c038a6403443d014001c484082e5505000203400d010000f07018020b00d01c60b040c6503009444022400042c080740707001c075148820080314901040c0000303000c4c0d4908002c0040e01416a138412050002e2858043d003801180076081ea60150300f086000b0f002421030b50f884041c843c0c0c1c00750302d0340142030b1141 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 465098057 1250 465096807 465096817
    0x170d06090e030909130c150f03050703060806010b0d0603080307090807090e0c0d080c0d1e020604020a051203160c06030c0503102115020406030506150414040204050d031101050601050f 81
    0x1954110b05003805c13500c0c0c02c5551300e550b600801c014042d80d178004e4000540c00010030010404550b42070120f03403501d800c01c1e0111000345c01001e40300d80002d0018004000500700403c140c0c0445440040e80c0d9560340c49801568100341c1e1107400045156504000c000e10404c1400c0152000480401c181c0c0080300c9040daaa98010407140d0244840d0044031090103584d00544071562644420707229844600c050051888030340d4500104490b03410340e011403503107200040d4144113550240c42c0c5410f05091504101001da040822500140300800c081040c82c1420307800d0030a480d04c11a0b80c640c0a80c14050041d0a031010203240c181040005e104000d030922410038100212840d6441c0b0b000b40b41c07031300d50700101e0740d6404500140068183c0a0000d0300220550300070700454180b50740400540d00d0300c03400c100003190058502c1c032030403200744010b00c083c0f42250094400307010f004000501c0c155480001c80c0d51401c601c002a0082030a031700307064403000028060030b5409002483c1440c6040d900005854907070040c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 465099307 1250 465098057 465098071
    0x60b0910150e12061504051b090d020d17075307030c050601060519030203090106031a150f030d050c01020904020f03150d02060d09170d06090e030909 66
    0x8940b048003015124100504254081c000503500b02d442c1026110462510401c000307030249107410000b50044040900040410568158252400c2d40c444104405d1303514016050f40d10107018614000002d00100440301418440400c03c0d0f19007000e82050124210f100c00510000e00e00100048100d440d04007141482044074a5024082e50100e0f04e0350046010b101c41c08002c075600003980c0c0081c1500402440c001a104078111541607032a030608071a02d001d10003984032118250a40000345078003d8020310343c844d411600010724103a40380c4a504c440040c55140c1316840000c41c080c80b20391480200c80000d0100107892001e0508100e0b40401e558003000c034000d00030441d0102e04010b101d8002e404550f00c40c42e00030f0080d0349036416419850003691042d100c402000255031401d0b016820080c0018000540051400b07060440080150019000090341166460f000300790b030b440a104407001420725200010400902c89050400d4941152802644c44c6000c1d80181303c815a140d407406850399110103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 465100557 1250 465099307 465099317
    0x4030507060603080c0304170109050601050d05030c0a060c021615030e031b010605090106090506030609060d14030903070f050607171b010f0f200322060b091015 71
    0x24940c01d141c801080d8a800c000c1c0641400220901d80310130000c087d1040d20281060f9003084007000c13020700d00302c50103088010032540048004020130301e4200e500018113401001030303d15212201580c0360900003121012118242e942c2000b100c0140d040120042c41444440e4003c0000e00380400000b14407001e044403c10140c03500a480075400040c01a194205441c94a1040c01400d070302e00e160181c0080d00886010300c4012000040c001c1c4105808400c44801601c042e2558840707600340054002d00400b82a00502500201ea00081e202803440c0b80c15802ca4000e152a050720104044c240aa0303540300807030114039080d0034000c42d0740b1102125581c560288a1040001c240181c107404c500038070500308402c2110404081d0100c0064102c40240d0041c244200000c02146a4441c1105c0c40f1800aa1401d10707000758148020031900000e540081c7c108020301d103401c0b061404503031402911103084902c140c80b00381e840781504110265940081d00c4003d070714005030800c2c002200e0414144601e104000f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 465101807 1250 465100557 465100567
    0x8010509060a1a030f09120301090c0c120e030d02030c0618071e0e0a180f0510090f06110f30010305010209150c0a020d080d230f060108040305 63
    0xb40d0303031406000080a11244001c20342a01c0c0b400349010780c008070f4445840aa0035400903141150100302c1030710748608803031710b41d00310b03400c0c030f000e400013421a6156401807020546510000c02c00b1440540d0000300d03a543d8160030f02e4000300615060080b108081c00640d44240305401c180c0b0070106020b5440500350f0303420030080380b01c001c40034540102680300741003c1004510000e11440004006801d803044010242c40c5a21a41d0080040707580c0706000c401c80c9850440103c0000b0b505440311141180203004950006054220860031118110412510417210080c0349040000f0744c040c403c504030000045504040c10032030a909180f003140c0f259541d0141e0300b9a03250542180c030014103440c59013075111122560310b0740341480c002e5004146191049c4080c10810030710300c2404040300c00076921240507240c0d600c0140e00780f00b000d4404130011554070005205441400881e449490500600020446011901d4004041c502000603265045e10b00032202042850f98010844982142d49071030f04540d20303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 465103057 1250 465101807 465101809
    0x102120c0a0602030903030726070819020d1406040203070c0219030807030f0e03060106120c020a0f0b0106090608090d0f02010e01150501120213052112070605160801050906 76
    0x40c003041002410184040140405c022000000c0c1d8400c40103502c0e21680307003541800c00c03408000400d500440204074100000c07010b5100d008900e402104140c0c0e41c4000c145814a50f50aa80180450003981d5644d03d20a412412802c100560401c00c10345003140740d03050000000701441e9409201a000b0310301c102c480120081900c0004008681265070151140c1e650310300240855410201310000030714240e0090f1461802152150481e19107407120402c6110b0400014081c0605004841c254010300c5403007408201d50708404506944599040f851542c102940500081c0032a0852020001c050f010040d00074000542c007001d051807410f20204100003160101c0c0500502000c8501550030220103151459400c0c0301c650589409803140500340d40c4840700070089000d406140c2c084003c0c812020040c0c0d0504440c12a40e0814504d0252101c0c09060f031041d107070008261072907d14000016008080c0b01940c4542600441d202501c01e4815560b0a8014684941030107150311a62002d40030581c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 465104307 1250 465103057 465103063
    0x14040207050321100902120604050a0b1c0b0c0a0f03020f16050703060b01020c0f0f030c0d0305190f021c18030503070b10030507060e0402040306060e10060e0102120c 73
    0x2c0510015100da041a00b0121082c008540c10740d000b60b13000c1003d03040424511a40e00a98845000c80c01040f1002d65805041101811001d8400c2d040e03e80e517032070300c901540c991110300400e0420310607440c1c61102140c9080b442c134800040261782040e0050001958165024661201c0e00403a85000b58540c00701a01200c000c1c442e130340d403512603114440001001c001c004102541124000c8004000c074104500041e80c80f540c04c0d08050354010190f508180d07180ca41030449035030126000c0c2c11074034503121403808106140a0401c0580c0402c0e00030a1502c2a25546203084002c1c09003403800c42d0701801e80c1c54010791764081c0d032648420103035829070559040f54480c486c404585100c2e80180c20510381c1d030b03052064903035101100503101566200009190511003902c03140459030700030000c040c82858840b045406e5185590881c0c3d102c0e0b020040080401c541d8090b0f40c000c8d00990512403001d042400f2000c614810300c0c3e02a0080c0000d049029110380c0c2c01090114440c0b00c1850395036070392283c0c4078070300782 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 465105557 1250 465104307 465104317
    0x2090a02130504060618080c18180a030c0c1e061b061b080f0603031c0e03120108060a0e070605071712041b03080405040b01030b09011404060f140402070503 69
    0x14009251000005465074841c40c3c4051410148040c20300e003e854018131234540185008458126051031b0118103200c192080f03c1da840100e01c5403003844111070b421064180060464140c000606c81c030451414402c0211400008105440c0e40c1d00d50501d418030f030000006078512609045c001240100240803141d03139403a400b03481d8440010800c0154903040c295101141c8111500000c00d8507001034841c080207017125000341402030086090080680d0000241044d2a0000400302d80756035485140341d0042010b00340c0b6a6407041013003415810700b0305c124945400200000400d43c241032016942900100c1c001c41565100d01e0110760300c0036242414066040108010b00c1c910f08005080c5050300c40c0c07008801e00075071107880200d408101c042c40c8030503038078070703178000542014402c100c10004c40c9455030001c166002d041c1804030342044140001070301814241c0c04602001c4001481c1e0900e4642442520b0140c000e41d0690103170141040000c43d440c8048003c841d006070b5000503080e09000040050310 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 465106807 1250 465105557 465105559
    0x70b0901091a0604090b0403030f0f05010513230a1e020703080402011b050f0303090c0a030809040504150903020709242108130302010e0a0308030403231615050402090a021305 77
    0xa58a41892315004005240500710101001e14061010070b10182e0380c00303000c0c125000140282920004030710711200814507241c0c3d9200841d1600c1280000d00706820750944100c148c50030000c1d46c41001c00300f950b4088411200380300030780d04c10480348001942086c3e005070403135020b00e4200b038002c5c400c61040d00058030340300014007a03200f03e00a82d001020008020b5100b54903010030b442c1c0001c01e0400740940081d03076000c02081048180141e0b400d82c24a80d10541e8801d026030030b00700b84140c114202500b1500c510788140c0c01604400310910050301030b4080c3c148000a00840c00700103248040d20510004003501410420000c030040c10720b0004020103040e04260740000c00c0c0303580e0b84030b1071203d480c81d01900d01c02240403030b00704d24055902c0d00c0c0191001c3d085130b410850702441c1d50340b02d42c0d0840303000f05520700d28000103004010900b2a103c490003e03141c0170001c8d1040c00b07202c50302410300d480710b40541e40300700c02050704200402c070042e154280c1840c0c1203044a0000340e25081c10607540d03440c91711550096 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 465107913 1106 465106807 465106823
    0x150501092313020a03020c0c060415030e0c0604060801030c1203090b03130b01080705040b090103020609060d020d11120a0b060a0509030102040e040305070b0901091a060409 76
    0xc84906400180b20406940c4401a030400704c0c1c01101c084030003e40c0c0400c05c241e40c440100700d0004000c10441e4480d08003480c142d01c1480321401d80412808154503000c1c4045080c0d01044500c80e40d080041c0200d031950388643c00200200001d00c0240c40f520105c01000600089110141405503007590301c4003840740c02c0044014060b4000740080c5c00c54458000410041169110400c0c00f81941d00b0140c018140f40c801008180c40414038454440d23500c1d00010030050365408120340b103194090354066158800014600c00a02814003024641401d05000040b00a2050003e00400000b0886031603170b40c550130700700400c031160301d4801a007003c010010b0f000c000380640c025001014004001514060b02d50603c4d6a2030682030754102e010800c0030400b1810004048601070780b0801309002000260404e4076481c0c003851042140c0108104108042903503521140c204800c8280c101ca10 = true := by decide +kernel

theorem cover : BRFrame.Cov 464928057 465107913 := by
  have h0 := BRFrame.cov_init 464928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 464928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 464928057 ≤ n) (h2 : n < 465107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
