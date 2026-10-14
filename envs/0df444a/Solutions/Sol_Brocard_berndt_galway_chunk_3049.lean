-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3049
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:30:35.337481+00:00
-- url     : https://prove2.me/submissions/036f6da1-1d51-4654-8158-b37fd1d41135

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 548201438 ≤ n < 548381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 548202688 1250 548201438 548201473
    0x110408010b030703030f0518090a050a0e0a051b2e0807020c030c0409020d061422020319020d080301091b030209010e1207180f0b060a02190606030501050405 69
    0x800307106100c0d411180c41000000d411960869000e107103410026180c401c11100004080c1c034154401350000424007c0162079502940b06910900401c801000340c0380c81d0400a950b02c907503007a00140700d40d10408400e9aa0450b0711f080f002070146c028000f4030582d20b034421000c0200002c8580b500ca01c18548a100340003038208400c1030740020b051005100480e00100025a90060000d515003d190f07033300074050640d00c0300b0071058001c0350040c0060003444000342c4c071100c904208803844002c45250b01e185280080520122000c03140d002802401428000040c0342284520300208a900c004040c80540c0060030328030286000b00045507002424072000d4a400e0f0268418094886c200f510400c04912982c2e0484206035035500156590b40350f0344015510186008259004031055040f0320310409201d034819000380786d001c040a901444521104001e020b2240034060755040980c2109a49450b5030000000c0180c1080c000c440200304550f5030b031556801c44009641c2a48d0a8000c0400403800081d40b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 548203938 1250 548202688 548202701
    0x20418090c0803030c0d0f0e150601020706050702061e1303030c05010b0f130c0509040204030f020f1002060a020a2102210c0f030c1308060130030309050a0611040801 73
    0x800301452071407520160043c2c4d20300c03568807940242540d807d180011004254048081c003402d60f401c940d212941c40c8940ca144000c1100c0c031500503c601c100200f2003601c5102624803240d030180c400d1f42082c0c04420399401e560a098142d910307680c824000d06442000007019507008600940381c4100050880c1062403e4401854a60340181c02d00006071500d5180c08807038240074000214000307046066504122007034407601150030340c0280042008014404241c80c54507121340f003121002c03150035689092100c0304040e080640301503089280055103a01850300108001207807464444441e4408210b401c03120349201008444803a40410001110007240c20440c2405a2001810b0303141d15009040d18094403801080078801040480801c0d07010201d10207032070300d840440681400c00e98a804159586140c2441603076a02d00707641d40c54408280281c0b603046068841c000c0303150640d88050324145e01420503080122030381d1245100e6003001c104148290725940000c9140c0c16512803030a03450a081d03400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 548205188 1250 548203938 548203949
    0x50c0c030a15020d0906150f050301050606030f070903390b03070c02010e06040815070813030e18070503160518150705060f060913050607050d020418090c 68
    0x7030030280010456112140585035004800503a86000d44070079440503200e0040d004000e5070a2103e010500c8090902d08001c0d103580c0c0300a100c04940e00c0c010103090391416503002d90030801c1040450034a4500b12800c95200e61a824010f026968990304c09061510348404c020602403240c030107041081c10552003008022090303000560550400d981c800d0284005040350f014408650a81c00071039014090600410074018000c64840303540d050000e4403903909956005030510306800198100d0f0052030305030700450b03007549040c10748241e9a8041c0c1d50303032144880b20380c2d1002c980c00300c140c04e01d80c1040e85148280410341d5241c0e280d08215082041044a41c2d1014050120612608000c030781d1f14101c030762024004448260804501c2c0c1040c0c00c1502c034a44010f0010300981c020807000001118489001350020345100140d42d980345440550b031240310b84000d14503000800401c120a2080000d0034400c8031010006240543e183c500070102d56004003080421601d0340d54900a200d040c218a0f0014036 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 548206438 1250 548205188 548205193
    0xb01060c03020d0806030708010f0516110d03020f07082107050408030d020d090f08071a0f06090403030f140f07090b07060e0307081206090703020a051b0109080406050c0c03 76
    0x640319a03000c1d44800a05a580081012000014049640400c421070080800c1c1c00204640d1000c4d950050181c01c0c1110340604c4503149500f0100c0d214030070241804441e02030745c064501023030700c244114041e520014080c0d03403c40d0240300382408601501c3c020400c4502100c0c0140c007480d090b060031450003000404c0641840014030040009400100441c0ca9a0440420059507a502111034000400a000d406441c07134000000c02400c01034884010000d8034020b4100007085441805d10240061040320340304649080381000c1115414580120f542091090401062590110388400c04407800444004145009101800795104003600704c80c1d000100c0e8504a10180d04009502141c0d108481c0014002c1d951000088400c50041c800c2d00e0f00340354082c040340c0d5105255409000e102c0401d5962034070034417808000c2840300c0d00030b00c21200c00c3c440c3e548805040c0245100712190303001105010400e117540b10b00c11003000568040051025000d43e44480d43c440c506410824170346084449175600aa = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 548207688 1250 548206438 548206457
    0x602011505010c23030a03060f0f030f060e0303090d0e060a0806061e1c0c02010e1207081209031b19060507030f06170c09010b0910141201030b0106 65
    0x2005a03106802680d0080c00e044000c5010b502d020000a91101c039282c20442060000302c0300d85034080300900384040c1c4e50380c1c01d1040d5921010f04041c0e807255445008410b1960034030820000307031034047c14a0340341d01400002811310f14050290342582d0085403c1145600710b2000040d10035007000c001035542e001990030a0401d806d00764007030114240174040e81e01c54036010580d020b500c10031900c00307020405c107101c41c540c0300c0c02c113146801100130004500b8004507082c0503400410354414840d8800c1100703004003e19211007204140a080c0e400b074bc00c2690824410083c07000801140d00e038031405005803200031982c4548032044d6801d461a0307185000101e400410150a144c03034800c841600494200d0000501503c5020b0150010066605990801803c1150005810005840c9140e484100c9030540d45c0014a810401200f100240110303040b107102800b035185242428010940071101505060360408050701c0071085540007951100b9843c4141e200600c104004204654010b04103030134440f010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 548208938 1250 548207688 548207711
    0x1030c03020f0f0306030a050a0506042112110405040504081305120d03050a020919051201020f070f0f0206130f0f030b06121c05180603060a1418090307020a060201 72
    0x443c0b03d803c03451000d0540110100300d15550034005c4015941c0e0080c21142c404100380b41003601e4140072901645c400030030043c0411109148090b600c003080c0650f80c0c0d00a540c460034a94001061040d80075110a03c0511011901d03840300d00c43e03540158020300c45d46842d031409800100140d811600308034083c1101d13171106407410720001440c040464003428046529030b21005403000901030340590341d40c040c0328400500070b043c11826188058843c03d6400c00c519002c204442401d07880307015851408280708000e50008524640400071420384038140a10000c1c0c00360f000503000e030700078140d2a8004002004104a070404070b0840c00014002c14903013400c03007807458a510403952401020036005400c2440054010712040c080098626496403601c6408000207400600540001c03441880000a00c480f20220340380c884242e0b44100002800141c2407410904041443c04150708a40e0304280300326103606190b0180b41d00c09200340000b00040da103030011801080b22840e9194420415645483c0103043c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 548210188 1250 548208938 548208967
    0xc0403080a080a022b0c050301211a18010c09052b02090c0a030f0e030a12021e09090a0903121e0f050105190e040605060301021e0901030c0302 63
    0x818407201e0625002555850a50300c0191060700c18108440c3c1c00c40000750410401e4103825603004074048070800070a000f000041d11b1a00c000c2c026605801140034010404030002c244d00008107101e0300000c02a003025030100c40c0d21103426164184000005054410800e600740b185944000b01442d010404d6071038500420707c4030340d07004080d214001504c26010010740740c82a440d40419030107040308445162a140b0415207402c0003d4000c006401c0c40b010004840480c000c0440079006c0c00060f40c0791103164041600c01d0542c1003c1c40c10460b409104101c5d03800040070240410a02880310140e0f100c11901c100002080004e20901b00781d4900023091002c00da1141080811a045c10320001d1030440d2081e1900e902090030081c80445810000d0000442c40c080d00706504030380c0709a0310100c0608201c0d003020700c3e0410034010301c20022130744400900441c4c0e540d00059080b030809070005180030b8030003000720940e00b80c0c141940c1ca80300c07000403881ca50b96418440c0b444450524a03046041c20a0300f0745070007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 548211438 1250 548210188 548210197
    0x1050c04051011061f08061603050907080a110108010e1003030f270807150f0509010c020d030305010f05060406050f03090309090a0e0714130507020c100908060c040308 74
    0x501403003900341180c449900403800f21a090b07101104907800c0389402085802c15034080e07500040820a054800910441c000a0741e60065101500d0b80b903004ca886c160480040c100240015030790302c00c208001860300b0040c0841d0845a006403480074140c0081c10016051601c182c2c401c200e52048101008200f110070350020068907803624050840703200d01d0382e04581c600302c1d0504e8010f051003515031443c0c0c2800b4012082c4125074420702036444c110b960710086152242c0d4610741e6800f2641800b2040b960900c1400145000e9a050501b50181c441c25000b003500c0c03859000c6d0440100c1e40c1d600c0140650035a440c0c0d0341e401031a0480307403d4505410054000c285000d1341001c0d50480c0070200100d1345c524424003c4d128079041c0500359200c0b9140c030902000103031034031920004d054019004003084000b4014084044100007400c040e0b00d80c18000c00e08030007800d000b8030308003c44c024030b9014090395a607400042c070900034555542c014a420322005038100301c00640a1100810f0408c000c1000694500698 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 548212688 1250 548211438 548211449
    0x615150504051e1f12020c060105030f0a08030f060a0b03011806231302160f060e07030b0f04050c030607020c0118060807080a0204090f061509030507050607050307020603180f01050c04 81
    0x32a4803180c003100c151381c1d0445e01d50842814030b0000c200b610144100084660484408804940e061403000c2d449030745942e41408007030413280e42000042c0960041e040c007607803c130401030403500c3c086036100c0c0c60040c9074100380c01c12003101c110044000350504403400740300043d04449404984c1001204442e8080b241c5081c07526000c0c5070f8200c004440e161481d8103a42e071810003180740610f184294078201c14128451441180c2c854074000c4041e621160015154081c1c90740040403440c80c0d00c0c0c0728010884004010401c903254441c214034084c09840600a442c0251026001440110b07204000035240d207401900e00581d02e6070000342001141c0d40040c6c415046402c5080504c0f06803a524240e01c040d21031078020494080c01c028811110707a815511803411120b808100c01c2000412100c2191070f8040703803001802c2c6522a0205110500c1c180340201a400d1155007243e20b080b5081d400306005030030858800e035001d0446405038441c480140a511080c4040354020800341c03411418040c420300880c0101c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 548213938 1250 548212688 548212729
    0x120b10020c0f18010e04020a080102160609050109060c11010b0103140a0b0a0e0103080a0f051303170403060f02030603071d0708060604091a010e03070e01030615150504051e 76
    0x341d2042d6151203101081d80703544203291401c02e40e10381100c031044036401d40f4200c2c060b6501d0000003a1009062098551328051490381c003088164030b894030030281410310f0054605540e0707240e500c00080d043c2c0c0314028841a050701e5841d1401d50016910f421911521042810b05091915180120000100555110b041c416002500031610000326081c2c0002d5040b04204400383d0001005120f2000c019110381d903125a11004803030316004046402e8021000d0441220032041c2c03061000400c07aa0060b001201a00505400c02d5926180d10003502c4008043c140d001d9400018405a0705041c0700004c0a03202c0402a50508408640b00c601000801412601008000e00100f81503660350822074005003030f914001d01c02c0500c451140d031002d800b10b1480c140402d42c4984603a403d4103000c06c03501c00721084200b074a240390381303503440380f00161100350450803c038a801400495542032200c0402e8094a0503504c043c1c80c0d43c100002d100d0a0171008070503000c9404540c4940c0c81507600c095440c44c289892605 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 548215188 1250 548213938 548213959
    0x60f120807080d0207150b0f01210f020712081b0304031b14010c1b08090604080f0601151817011b030c080f010b160c050907120b10020c 60
    0x3031000316402014802000180001218000303440a5009000b1450003011260f00312110200070404445254002e50740090100030300c2506913029110b899004028640c0c091015010901030b002110400c4241107030040e400301d0036505010b00011405182e000d1424128603a007000e584448600d440c680c0ca180701c02000100203002c051045603003202c2c00d140743d42c0800c0d200100d07140c01081c2c440c000824036100d6103480b0160f400320340324200801881200c0d101d60046140c503501d543c8203640c0711104207a080380e000c010018000c0020481c00081d0a007007000b42040b9410308048080040751000761408000c140014880030101c0c030706210048800e044c2ea02103400c495411181d014105018044150340c01002d016410550543c0290601c03000c51703514510b29079680c0b2940e50514170203000b071005c41c600a00594aa24910307044030800240a04d01c11182c060341d990015420380ca0403510300c0d00140e59028203252408450040a40e410b00c1141c0d83c1050003080c003c000e66074140d009500d0310803370120301d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 548216438 1250 548215188 548215193
    0x60609060a030b0d060902091303080c07050106030c08010e0d03060f0e1306110316020a081603090b07051b010c0b0f0c041a0c0c030f06061011060f06010e04060f12 72
    0xf800140050000381032440050038500b4444000c3c039100000b68080c040113000600d0012807403290044030360b890f44911106855801c0b281d030894100000c121101c0d903980c40040003081c0016204c50040c06004004141d01c00d5410107907003040240710480081c1420024180400070380580a50152420003038940706540d601c1d468043e0b03c034940c0703002800c028500013020803e0042100214420140030301c0c03840401006203c00c80e512201e01070003030304040080c018007039006e0750400b0001c2018028075001c3c0e5070305c1c2c48010392086a80007180484160340711908581038101e0004c1440078800702400c10407206070740b50310340c2240c11000a140403907151200000a9508a00c6001c0d50090702c0a010702c18000180380e40c900090341e0005000b00c80c1441000c0300d040c20341c5000111407071070000d0300700504003584400e0300f400514101c208070407083c0046041801100300040086500c00d1210a5401415041400000d8458001d545c009406a1300300001030010607520640c000c103c0c0c0c94003054400c0c020707503070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 548217688 1250 548216438 548216441
    0x21070b1305060c0703030201060609030f06054812040b090f07090614040203040510020a1b031706031c0c08070609080a0e06090108150307080132060609060a03 70
    0x6401c2568001c501040d43d600110000603000141d038801d0b0000c000850310f9800540380481c4c01c1c800103000c43e00c1080b194001881a40101e5041280d05505c42510200c8151103110051400b0102c541e240803c0e00c00b101410050141910074034000d0f00561402e210b401c15907846610091018103807980c03940115014803c2080310194000c0620162050680c844040c40c024010501c6511038001c00c041d890102480d00b8800c507805654000c004240c04006c44011701b002c2e4001c0e80c18803050280c3c4448440c00303d0503240c07203402d0880c880c0e46c1d144034036080400a6071304200050700440c020f91110b510011402c41105a81000074642d08000040341214a002c01843c800c11400824042c01c01e41850304100000024010114480e00c4001c2103d40302800c0c132050b030144c840324a00140e50304000c500d02e03c030103410007800181d000c0c080d14502905e034135025003512407806a4003144040402c0e281e0b081d499010000c0240310096803200c6d401c1c10640001216030050103c8075106460005030413103903a029 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 548218938 1250 548217688 548217727
    0x6030f0b1b0f070b01080c010c1212050c041809110d02030f0312091b15030705070507061d0301020c060f0601020a2a050303071a0907050402120621070b 67
    0x60011260390307982d60210840d1542c0114804840ea45001400403403035a0001c0352000801c60107950791040780c090741d268040380c0f00200c056202444034a03010f50b10b4507440350107818401c007070000c8265039a40c50140d48645a600c800021005280740c00400e000041c406103051440110480d92600114200e000007401c05818412a010905c0b0001d181c408450180e040d80d40304040740300030303103c00e000120000c00c0c0b10180f011401341e01014a01e10060344000c1d282c00b454100d0704502d0640c0c248000f541d24245480b05a40003440484d000709001080c069146d003030400c00e240107900035428000600d0b078003503079000301414505010003d40c00140c0140d00c00c00c40e028130035810400740484011800030369401c00000f80029011540d2002c8007050900700001103403a02da0303014100c040140c200c0c030040f668001e8007610280c80c030f0298540c0001c01d8ad0780c50001d030402241b1064001c019040c03500402c039803142c1c12910b030196000620608280c445000c180c40b001c45021070000d81e034031032850240c00c1c41e4648 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 548220188 1250 548218938 548218981
    0x50c010e010b0102060105150406050f0c190b010f0f09020904090c0f050a0e0106050313390e060102030717070c120210051c0e030f040b070c050406030f0b 68
    0x40c1800c240e10200d415004400c101d4402e030256600782e41ca60050010f0b01460358094a11007004000400c5414441e100418560010000c0f16082c4009412242d003010748882c0004000f401c0c415210003031051404480c2c0c0140144080000d00703920300b010101201d2902d2281800c1c0d19800f01d1803895640316a004048151b90002c56027400944420242149000e10b008050181600c0310010900810300303061f03181a80e4032074580e1420359940c07a08150540d42050021030398090300c45100440f81c44007111030300441c0510b102d800c4809000241101c925450740d40125405480c010601103166004030480f4080ca410010515000703221844c003a1880c8505680102080c2e000b9100180c10f400003401c061071188220303a64100b0755103004080b9141c0c000c84e2062a54459124403040310381c9a10b0340151003400e0080140c9060403084503408100f45c00641c03004450040000700c1c9000c10409244850107804100c504002150550b1100d0300f014000c81d000800c549405d1000c5840c503110440086045003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 548221438 1250 548220188 548220191
    0x10b0a020c09040c0308040b0406020f03030601051602150a090501020105100e0103020d110d0b0711060105100c0c090606050a0216080303040201050708091302091305040f030804080d020a030b010f180504020307050c01 95
    0x83e662039011408e45d0203031042000501540e1b04c0b0810624002c81164052001603440d9401d154000954141402d50310b1401c80c1c0c030408c03e00d038180020708a680a00080c0360340d40c60302040286040000380c2500c4004103800d49421102005224041c0030801c1c02e03054070340540e060340781440d55181c2400703007281c0f000d8402d5101261082990400403005241c1c3c0c400c2c0c010740e4908144010341c00790550348071028040c20354002c021810400c0341901c6080002034460040c5070f51640240e40e050f0480c100d5a50350400c80015400141c203005440c0c040103a6a018100384424401c16454246440e4803800050002410001c000680e0001c2c415001d0654006c40d1004200940160001c00341c100258003420b28640141d480c1c0d01a540140428442c05120701d410503400440c40172103980c11194030780002d008850b9404140b1801020401c5c0748040e10044110381c81c009013001020700090700900b041c481050411620707071010070f0302c180c40b15244404c5442c01e07100962a40c032440c0055030742c1d000e0082803043e6503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 548222688 1250 548221438 548221447
    0x22803080c0703020109090e0604030509060f0408010b192d0504051014030f1005041406040f060614030a110112020703030b04060b0a02030313050a0b0405060f010b0a020c09040c0308 80
    0xc1d07002084402c2200c0c402d8881861941d0394126203c15200c40300c1007030364141c01120014000c40c0c064002006000c8000345803504d805030000802031260015000511169511208031285003800403582880d0b0304607007030b10004685801010040240c21542110b004800c020165200d102c840b90141c019010040044c0058a003042008a9000007845517a0b040203001761090310608004c03405a440c0d8100720040c064250525180c0d0005d040050b0046820600c848201c4800003018420240180c0c0f00f640b0101280c8041c4c01c00c2e00a40e5066004041c3c41d0b0000544101780380c5d000985042e0b41580701c520b500418003104010703901d400c1101e90030304030780380000364010030503506a000030f88988040300c042140f66100c03005805a809400580805640b0800c0071a2440d0741007030340312061078480c608566141d1241e07981c2e0307101d212080c2d40c111556480201400b4180f0194500140034000c0c0101007401d0500222000350b580785c60745c0b070340f034042c00c1c6542c042000d103c00d44000c01d019681206900d59034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 548223938 1250 548222688 548222707
    0x20405010b0c01050c0f0f091306170f1b09040f050708030c100605061215030706030f0c0c0c05011d030a120212040b120c0910020f010b03070302280308 67
    0x240c2d0040899910719460100003407001d280b80000c0d40e18203020031158505040f1040c041d6006d0343e0081d842e080e0312105c034280d010f02114550007100041c00380c4000d40c155140c140c0c111549451401d04140700380d900b0039800410120250992014000021160b5440c9500d940c00c014410b002e003441c000d445030041501c04505010004010460140c0c0d6008440303400144040380c40407100180103495201104008031561041e4000c43d080d040b201d040203400882510350300091030081107500c60004617440703a46960700b400c01442001c4d9103000f00e04096020040698694091082034004d0340c3c10303c0034111013040300566132146070941c1c1402504880418807641424080c43c0c08240708240144200402c6961a940c000240c0d0b04850349503101360f0400e0390405900e880d21100901c0258103c0003407080894698402c01c20541031500c80e0081c1c10101440152582501c0444600074003030350203020f08000584402c006e46400041405a04d160300724558644999141d0710343c0003401c01c000c0411b00084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 548225188 1250 548223938 548223959
    0x80a0c20010905031b3a0c0509071e20030301031b0e01090b0f180f0a11220513020a0206010e1306051012080405030c011707030e0a02040501 62
    0x9031940242c03541c00d401039654003015a5034414140c8a07800260109050449080c602990402d80d0003007104081007100500780702d600d00c0301521a02d84101e1050702520113001c1c66500d460040e00080e52050050310344108050034151824061110000481071a140fa05210b5405150f04000c0c2d070740088841800b590586584c1d42080c0810b40701b004e15000507070159101926694205c0e00804c3d28410680e18208012000b402004500d03500521101c00704043ea40e00c03407050001c030410141010b4403c2c1447c2e4030010000d500207040980307841c500784404c190292400c0c00e561204203084514600000d04071075000402200380d00041d000700144002c1482c4605a030060000000340740e0032070305136030ba898000c060140c5003a20403e0140350389030490404a182500002c2c3d0011040f0140080c01d50785014801030184003800c20741d4180c101041c00d000c149824044480f01c1d00302440d20303003402c00507554010ba603242c001d440c80040c907a89070f91150383d0306c000b8004040e1f2141c008104100c03940e910003402d007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 548226438 1250 548225188 548225243
    0x207030c0f11061803151006080901150806150301050606160c090203090604110102070f06030e1e07061701060915210c020c090103150b0d05010c0903021009080604080a0c 75
    0x80c800e004800300380081ca2144091180318003c1703604247d01c0103141110903074050b034004d44002215500c410501d03800c0c00c50b800c0c008000b0300026004046038980070561605100b00c4030340140c0709034100300920402e99104403d07590244007030142d02031100c40600d000340000c5400d031310800900c0e0002c01044840030010541520980c0a0210600241d001400490711505c2c5401034400d48010ba41c0280070303442c4650300070921a40044200d07080440d000707111181c15503000c510015035600c4400140318460340100c2031445118040d00c0e0020550408102070084000d034090103208083e030354140d041051045641003406044990708201d5104050401c0002c0c103400c100700009485201c0c09007000341017000f0041d040b01d4011a207160391060080c418005070614020440e48401c03d9030f00c2d07078080b070028070440d103600034540c441c00c82c02e0380f0318411710204d823800707120300e100f400f400c02010002c40b03401007101170703100d43d08c1001c4941d50f846041040d2040c006281c0c0c0a844423887c030703926070700c41c103904420f41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 548227688 1250 548226438 548226487
    0x2030601090207170f03011202030a02150a1818230a05061f021513080f0d05070c0c03080f0708030906070305150607200925030207030c0f1106 63
    0x40d13001d089100c00c42e1307954450384000502c006030070001009004407a01c102048144000c00399001e94003950002044503003102003e80c1c50050000718a40e0041e00200d2100d5040a1800f600c1c5040f481c000c5a10b0200c0720301004d450038070f5201e20742c0c242c01322450114448898915003c902c0b09040000040300180380c1101da06d40500e10800c4c1d810075802515001b40c1040b02564001c01c085414090020204203010f4078030b00e0444030b008400800112408041c1c04542040e03107045440c2c980d103408040540301c0180101003071000e1066080041a43c810841d015a500004000e69508800b00703d01850310a03500040c0c0007260120605c8487c900118900b4000c2585907401d2040341c940b1044d5802c0306038040800c5074005030802c00800014508980c005505001c1c00b8a1070081c0014408200c1c040001c82e4500c00d40303900e0b2402c01004e4142c089058500386143c0ca421070418095a134041c00e0561488005407108240807024030401c5040100c04413180781c044d00703603905c2c1c540a1150030b180000500c00f2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 548228938 1250 548227688 548227703
    0x70e070e0103060e24030309030a0b06030c150409110f0d1d19110609060a091706190216050106090b13020f030112030c121706010306180b030a02030601090207 70
    0x968400407440c030341c2c0140d42e240225020031701c000c065540d00f603032041c1486405010600007c0303d20340d000c0c41141452406002084281d107000001c00d4140700302c801d4201d100341380c100d04100380441d514080c0d07030039254005000100d0152802030ba0384140100c400f0001c80050014208079191056001545062440030644400710756081c0b0340c0d0b0f20342520b0000661a0722540203e070307010811907088010040b40c090708040c0b4024454000c0307501c1e940480c071440b0224604910400285603111020070120054401409903421700314040d25003a032200c0c000d42085600803038188480e41100c1038100d0125448030080186954600c0c3c4c802c003070110945803510a40c2d0b001d4110300c0341c08041c0201c0310603500b100211071950307007002402024200622010780403c0101c03503000c400540d107418070420381d0740e41d0340780d0800610481c81025905400100520304040c00c06500708401c0961120700b11142282c29000300785008100c01003443c0400504000c0d506120b101c00009160105600400c001401680ca = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 548230188 1250 548228938 548228951
    0x30501180b071713020a05040c03051b0708031602010b03070f1403061902071e0507050f0d0209160512160f0c0b041707020303130504050a06030c031202070e070e0103 73
    0x2025503d61003076100312004040340100092001c2000040180c06610040c1075070300c2203440340081000c0701c103240d000c0000300c2d07a98010b0141205000c5801044003250000242c0f4009855444980c140409840c40d9140311304180d80c00c003c00d000f900f01c0d00342040045c2c2242c0d00e83e507403107415550081c4103106111410701c0840c3d2103642d508001c1210f500c140344454040c03c505030240007a9000358424802912200003045424810200d086031404455014100a1041038204400c00510707020f908120703403180244240c040c1c01a1100440580d00c02c861401103d607807914041d0075120383c8240b405514210720024208068a03a03001c0d01d549090710b180e696582010f0300b46038146c4220309242005441340300d104d8002000501619111009041d040e208241401003c0d40400c1c03943d081a21422aa18080341043c8410b04092103120b0b40511240c42c28000c081c035548681040c0d00580c04054250380320900c00c40da6113130080010a00801c0009920100351400034402040098032503040c40c0043c3c10f000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 548231438 1250 548230188 548230201
    0x9060b010c080915090a0b0d0507050301062001230907080a0803011e091d0d0801051503041109130b0105100e09040f05011e060b070f030f09030501180b 67
    0x90444001c1d40d4004900e500e420319040070400300c04c196442e4891107410401825002e911b506840c8030040c403010107020380301c00c606038001f0140e80008000e24100042400100705441d4007c0002d503078880c0094040040c4149140118054081c0f0440e17403000f0754181030000c800c0c0400c800054400c040901c2a05c40b00d40d1110003440c2c8030082458040c003410420b000500c051071402e5801c0000704100a2608246951500e14600b51800c007004c503801041f840580b285000414003d28001d401c403840c022050b581000c0005800d201814100311801d140440020208941110321010488004000d20104e141035902c841d07074140300141c2103440c00740e0400001224202551074001031565620381c01003152804081c020102c40c002d1094401e42030031400074010860038401c62005901d902c2803650088403148020041c1e5140d540849802c100030051307003010503e5059100f05c2d1031b90614245080840b4203400b1144c80c1d8060b000900f02d94a4050114594804001c2007a4814411040701c0559940d11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 548232688 1250 548231438 548231447
    0x1050d0c27031103030c030a180e0c0d14062803020d060506100516060b0f04050c0301080d0207050f04111e280c020907020f062a070804030b0c1b0109060b01 69
    0x14001c01343d0080c8410445140909c00d24103030740a0888040040f0f0f03560301440c20400406450140300300b00300241130341509009000d00d400840752034200d4003c0e4180385003c41c1f1154030300d100c89034108030490035000003802892500d4004580003001c450354110305080030402080191101c1d07124080c1e04405a82d40c500075802d840341020010803c290f50000e40e2074101c09402c1d1502036941c048000041e400842e5114850f0a005001201d0304c1c5441e5070500500d00d00d05421038080300150350006a040040d65100480c58880001c1170b075002c2540030b003508444900c1c0c081d40c52000040301c0a034003004850340107034003d000c49140100c049a42800500c070a080b900c2540e00c106000513030342820001c00b5092011a0319080812031048429000c2da119400e81003460a8445009049076800c00260541805c00004000300c000481a4542006503880039024829444020030442003040001c032220818410350b060680001390850700042d4440c002c500a0111200c11600179250401121440d40701c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 548233938 1250 548232688 548232697
    0xc020f0a0809090402040b0d0609060605060f180f03030a0c02041a03031209160807030c060323070302040f03050c0111010e07050112060302030106180507030b01050d0c2703110303 79
    0x201d000c0c6000c0a08040c49182c0700300a000360303045a220616070547d81c8a0040d01420a8041c0c071000031300d04d042d440d1100984141d603202c903104030400e2010f220380751203180445000995280a0b0880e070600708000c12010441071383c401e941400049031526056400001d9000424400c6a00704045004a14820300d4006024007c0d03405a205108440d80304188056481d0407401160842e469007554502070402c503089500600c815400c4040208100084d09102e00c002c3d0400342000d02190b265141884000141da641203145c800c10880407907845400b0758115009041c2c110481e0380540e440b03080059854140e188000d002410842c078001203c0018400c0001c009d40082c09484040e2902004540018001071000e52240d980c402c0013005035000d1013040000e1442c844150110784450380100103c0300000c000400b41070410680c05241c2c0ea115080b9a607a5000c9030000490742201a0110703800c82c2404140a50240208100801a42401c65903c11240306800c8204107000e10000e26480e07016 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 548235188 1250 548233938 548233943
    0x10f08060106201e0c0111030c031608190302091e030d2a060b01081608040210120608030912070506070305031801020307031407030b090103020103020a1209060c020f0a 74
    0x1e2003142c101c1c1c0d01c41107004503d84002c4080440c4d55881d001c84144c80020030304030300c0c00e025a104050080c03039035070000103031a00462194013460400740d81134a0b0907100d00c035040032588a404a1b064030410050044103446400c07040c03465074980c0c9030b442040907000b5881154a02d1141d000303118445859080c560820302c0c0902c02401408202c800c10400380c4207004c02845903040c916810a82c1e904c5005680c00e036141d01c0d03024820100360070082c84000340c014000541854505501801d280d05581e03040012550001d6058818000100d00120304442c511004c21000c1c540c6070400200003040c18000029145481e82210b44400c281c24036088a43d4407407141c8585900800b0900105001c01c0c0a00080c5a002014014468120650465003401c90348110fa42e0404282c1d1001a14503800130101d00a42c13041a500b800c11076141400d0010300c800f03905100c02410950001014000700707129000351000e40e28003c0052015099600c1c08402608801900c500180300e11106011064030004c1c403c803000b40c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 548236438 1250 548235188 548235197
    0x1224050603190c031808030402090f090d050f0d0e0a05070f0807090203130c12110f0d02040b04020c2409030405010c0318050915190612181208010f08060106 69
    0x34200d50400c06004078010010031325a035504441e0b1441103140c0030a844501ca000140d42d2850302c3d1040022411019000d00b6250080c0800c0100090f0000394004a00180e410640e80382c0c0e9440300042c0c900d101d078244040c496401d0250244081c80009040d03410a84240146ca001685482040e055050a407003845130b81d83c80705138100003d09003a401076402074501c0d0210800f40c01d4584410803001d01c10740c80b444011050071001d2041c031000803031410384444102d9403200e00d1644400040c112801c140b501922895485000c5001507403594102d8500106071400e403040c5000007030700c8401e034001404a001e40e4083c0c1d0301c00148826008030848081c1c4505845441c13400d80940c4003140d12134032200a190341d800244001048039550944e001d8410706003401c046032500700c01d07401e00c40c40c01e05516501785c9601030418103210407a007141342010003405c1c1d0f41000442d284070607480e8809101840c409042000b0f006184040c1d141c9c08500d49041e203640702401c1c40100d41d0b0721505a52072030300344617180004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 548237688 1250 548236438 548236471
    0xf060c050f0912150c030f01120201080619090e030a110a02031c03060305030d0b13060501080a020706020706020313051603021005030711161403011109101224050603 73
    0x14503050f045034000201e03200c11034044214002e40c10550030401e44100101600110410015840460026026100d0030b1041688108158000781c10404054140d0b8807550316100c2100c0300c001d041190100500c0c040c001070143c400503c100d07640700e9001070603000c00103001003040900d0318000280c40764200c0d4060000c02010420004e100ca07440d001e031502100300364407500f0000c081081003001d080303142d0f101e42c0c0004422950500300800c1d0540b180c0c0389108507003450700070866070385c010b80610340c0986850005645c41007a0b240100080c402c40400614032440031091111040ca02d10b80320724258032074001c075410750311102c00d00d5051003c1c0d0700c0300950107460240340a000d1803043c80a1a00041541005030719000c42003c41400c2c109540760081c04509104003c00c00c1c41075041468262130404d40081280e05000315031110039128815041d40203514000c040e2084030300c21404a0f94101c00700c0300400c0b50095044101c440c1c601e02c49145203003c0200403010030107141c4902100d014421600511004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 548238938 1250 548237688 548237707
    0x1006080f01150c050706030507110a1124120703060e04080405011b0203010c170c0c0304140307050a0f141c020f0a0f030308040515060a03060203040503090d0f060c050f 74
    0x8846108002d00410201a22920001c0c40800c05d150180c40c10362030114445c40d250b40020606d10940380920026484505414041000000000d052000c182c030038208058023249000503082d441301d4160350440001074840d500101c0c800c0a0340c010352056605000b91136980500080f0403a09036406040c5000800013002a50300800c110285200034041080205d152500081e00b15a190b07442d01d80455015400300b03084402e09024a540710740746032a4941407440e4040003079541d00882c000d8010701310000700144041c0d981003019100505008100ea40e005807140a00f061014140c800c0e561720382503011305504149000e907014110410804482e49014800d0f8003044450800d4003003a83e0400e0710707c40c2c08594000038005840140d8001d803201100d0381803038540b00d0318081014140c0b03081ca8503104248a80e03a900d2084010840340c02c07481c05622521281001400d601c5059101503000a59402e0b0a0422117808143c1d202980034007402c10866070246025242e41c441c50710307540f1041004002500c0c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 548240188 1250 548238938 548238959
    0xc0509010b0f040618170102121609050111010207140a03030b0603150f0a09020d09030207080c0603040803040c0b0a0c0210020105061309030c051204230105070314090a030b1006080f01 81
    0xc1460107015005145035546d1614015200f5555a60f4030a03500091482000609411002c0e042406001207403120104103000500b501850b00460b810888034a203001900030342501924080e980110101d03240c600e00c442d41c4ca40e1503000807000c07800b2a04180200d90340d0b2903d501528801c0303c0c4500700001e12071180d010007031000c0c4080003040d031000c501c0d9004035031564036102819040440e4030001810110604004e0b1a0407a181d010780541d910004000600d43c482000344e03030300650301544a03504c130340311460320300800c3c50340c0d40100900e51800b040000380b803a881711640e417075180243c50b000c10040024104a00740c1341c048464070340085801c2e101c90109107040d8060781c002400b13458102c841064554540f820082c00c841e007a9003404010074103009a0600130007451000120725101140441072034006440b5000e07081d40541071011030100140c40790350365800c640060704003d00402d607064991820034910001500c1ca22044001c02e1008100b8078001c9034a40e010f034000d4258a20700340c0c41c2140020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 548241438 1250 548240188 548240207
    0x602120313050601060e0f0603060307170a050d020606120c010206060613120b04110a230f03030c0f0c04020a021218090c030103021c1a0714070c0509010b0f0406 71
    0xc455003a10442200860b00034015035010b0300c5a981c3c2c41d10754036400d10030040f5000c05144c81a01c145010001c0c8041c0c0d80c0c000445a04540e50a8124107200300c030b80c45c04506218404101506d0760080021115001d540800c22501c1414110b68103d5411a44120203903501d141001541c00341c1c0c022000310300d491038404060f00d010000c0c2c20400391009d441d0502400842d42d00030080740d40314031031018030003040714184002d912007100b55481016a80b505000c244078461040014136501d2410034220705949404101300041e002c09000c072644da80c802c002c0107aa40c01c03c0280c8848a01410360f001100349014000c030f8904051940c000c00710040600703800d85c2554022050180c5422104002544a44902244d03610400d000c089032a160341c95030041c01241c2c00100031001c100d1280040f402c001803c0443c420f0b4011041c3c580c00e051a65a00005861524404403c03a000c141c01088550400000a155070180e50701a2070305409079030b8910340c80406004001643c40bd291050006005d8036205903a401c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 548242688 1250 548241438 548241451
    0x30219080d0e01050402030d1b08030411181005150906182d030a031409030a060e03040617010e0408030c070f030903030216140f130e0109051606021203 67
    0x350714014055020320126581800000c20750307512142004294502448000c40502450602e4043c1c0301c0122030320441e50802140040001d40f010020806104241e1907290400d0f0000c0e050201c8804800e881080301d02c0200c1c0d4034065580b06031008200c81c14440c80c060450400c125029080944803400c005d0300741c200f00041c00900e5814106107520740d5038024580d0402001e128803e015440040d4540704500c1c030402954060740c0509410b00010341c0c018082030192404c2080191660a50b400007070601d0071040018003a44e040024015400c0703c04401041295034544543d20412202580f40c40c00080074410f014902401138000741c00715110302d00440d44445024a41490001a60743c0c05600d8a0b0380301003a1b00003400d070107040c0304054042140728444400c501c04098010301d00340c51400c00b034000c03a85050103500d908069007102d465207030040c00c441c2c0d00482e051012441c50341c4082e001b030a030a0740c01c2c3d60300e2259419842d10041c1c0c0e400b03441c05480c12a4044d00860507a0380305010340c1c0d4006800c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 548243938 1250 548242688 548242703
    0xa060509070318060612030909050601080a0e0313170c03070509040303090c080d09090b030319030b03100204080102070201090e0c03011211090f0126030304060c0905090f1f03030219 80
    0x4082c0020f010b07201710805013181451460707203c045424010200400758001c40c94142c0762006000880ea0070030760355640319491540101e0f074050303461140b0703040d8003490888400020310102c0108801c0c0701c0c02c515039240c6c1c8540084034a074600000070903548000300d101b560342140c04800400c02007880b80e085191800c0c0129a10240281c4e5900200d18004039110500001031088034244070100e0b0601a0000e948400c0700103500f40700b0b0101c0e1100002006020410505a98888c20403041e1020300000003a061090f008540399580c61007120301030360002d02c0407400510341840c042840500081c4250207256080703141d82c203681c00e283e02e8074a40c1009060079501c001803044503015542d01c0807801c0303111b40300c0f083d040722295141104040210302206d0122040d17018010001d141d0301000000d580e40541c00130804520100c071000d00b5a52041c40f43c01903900b0000035000c0151845160215078001c4d180da000701100c050500542102900341800300400507085103006175981d4002c0390100c800240100c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 548245188 1250 548243938 548243981
    0x204030206090f120a12090e161d0d0804030b0c1608030c040e07020c04060f080d051803031b061b0301090209040f060909020111060103110112111c050a0605090703 72
    0x4c034645010500726045802c100020441000d940d4030221040040560049102d8207050160801c14040c4030644100704210a0341d0b10029110294100309901150181094070603072554104007880d0352040c0000c1c1c40c140391007c046035110141504460340035440d94503a1010307a94a03079a10b00d1540c800b408042001c0e00501012492000d15040d50b8000d02ca00e0f00181542d02c505001e010540b0125408003000000e00d240c00c1012071130228042120b0320700b07440c0080c1d0720303121141d405401c020720f003811603018440480d02996078440328151280e000070700d008482855440090307900c80010061213805e4a40400c0c001000520929000ba2458010043c404113146034000f40c60000c41e021503002240c9141c40d164002e0a40d600902da40600140e9100580b07065030554546140c1c0d8504203070a1810024060009a90f111140d40900d01c0b07220f44140c0907541d81034802800d00942244040c03907034060b1410000ca60340010030b114a204507000501800140d5984000950040c06030b2141e51424010111 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 548246438 1250 548245188 548245219
    0x1002070f090b10030605030c0105090102010608030a0201091419060e0114091006080a080414011404090f06091a04052a0409050709081906110c1c030204030206090f 72
    0x3400c59020304520000010214660410424100d81d42d0f000c050515213400c000340050741b000302e903c8110010030f08056a886201c040100d00401a940c4203115900005c1a004c8180e98190040c0319068010040a4200c40400b04443d0b113880c85039184644450314001c485001910541000796403080100000030000701c0040801c17400c810450340101c02da0400d910404025600388241800b50100c04001c0c10f020389955209440c80c07085000d40784031916403e05008007a841181020031400c0c2e40040c5030f44482d5120848005425001c06603042c182c2403907400300d1807444521840c050191444070301c1155802441c00c0c4801450041c02411161050301004690042c9501d40903029140541901c1c0d502c44c074041014084640c060160740801106400c2004030040000e4441180000388607207060344240b61400c08000c0c0448103000c100d13160085401101c1d280040b82850704091141c0d160b90185d9501d10303040b8102d100c2c600000f544a4010300c0482d110b0b041400d0f07103082280003e00326090707000480 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 548247688 1250 548246438 548246459
    0x130e0705030604051905070e03061027020405060f1e0c060411040b060f04090f09020a03032a05010e16081b18101d01210525050a0b0309060105100207 66
    0x100c45c90002305580800c812020b0500b004820341c0095485541035006080c148560480002080c1590700c110101004502c556240e504036001880020801a99102040c070440c520340c0180b80105c440d00c4191400e152004800403c81e200d61610f000604a90380d038594884100043c40520a50000c2d510003036856540c881c10000d00d04403500502d0321740c956141445801c01da900310380c405070209061800107001601c40495841c2036a038541029402c20300c00604500042916907400068006104e250006011040d8000581725801138103440401e07420715030650074142607114001d1154807500390350600094010740702003030410040612140841c03452500c070b0504001d4681d0b210284000c002040701d0601e11303404813100741038014070ba807280d890018010298030084640d41d02d507145000345a42000000d12444d001a50441140d050f1704e1604603d54120703101e20b016450282c0300ba1100400d030444800c0569101c1d542c00801000e80380e0814060120800d812140c0f902503215589010640d905007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 548248938 1250 548247688 548247691
    0x906060506030a0e06060f0a03260f09030c040504080301151b030e1e0603070e010e030703050601080d2c01090e0c031005060a0210021c0f02130e0705030604051905 72
    0x400f00c000c14080e040b42111814004c026103460301c070360000212444151180000314080326000341011003001c1c058513001044066002c0c034890701200000b214240e1421a40103001400410342c211b407400707803118061000702c880948002d00305003002e0004000240da07440e01620080414a0300d128401c4100041101510740014100c0205070340308003a845a040501001003507030310580d000407482441d040403950b41d12000d0008010012648a0301c0b119900400040c03000d488081c00f101c04aa40d46d0800a07280c010a000d100002e02a29a0f800b0346103110f00b0700c64210150358031950000c070540f01f11890140c240324500e0703418071040130000242040c100c0d02903445100c009000959a103450460b03120085e060340c000c24400d40d001c0c8030002c19242e00107090343c810020304c4001660740c40304040d001000c0c104100c0802d066803e002da051701d1001c031a00030b0040c0c1003030b10503240f1049440700b4103805485000c032000300001e40140002101031078a90822500041040e106210a881482c1204140d420 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 548250188 1250 548248938 548248951
    0xa030506040b0702010b09040309211b080d0c02060906030615030108070302011e0f080403021c03021e0702180a0f06060509030f12041a0c07180e06010501080703090606050603 77
    0x180c0b03800300000240c083c001c004a0010807101032100340381542e00507040d01441d0282d801801f000c1426a54058480c4026101c0c181d00324502a4442d85491070106c42e218050050904d18040c9079850f00e0428002c04110400d160300900083c02c0442100a002042e080108180d9004a5907008035490002c02401103020304802c0c0041c105440c214000944400c070003000d81011114111a404000c603400550002c40489170b1800b80c0d410345031030030b08914025581122000e14603401c1d03400f00710580c05500a210740d24500ca10141180e0009045111030301a41c00c0c01394202c00c002200c01003a01038010703465030200c0768210019010024961860456141c0d4000c4c80125900140384891454200810114110440020248450706444a00c858001c52140c21800d00020442422084544065544c01c0e8684030172101c00e1513071442140c0ba01d00a600302071100511701003000d215030101042d564181e4006031502c09080d290044110001c003180703142518090360b41d82c00072565944982c0114000c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 548251438 1250 548250188 548250203
    0x60705030a0f020a02010504150c08040f0f051212030c040f030605190603020a0501050f040314010c0f0201111204020310090308090123180304090501081e010c120b0a03050604 77
    0x1c4032410142011030700b407044405541c01048a0001070b0380c414211020303224010b0ba0168482c00b43c11068600014a02005002401c04200800c0a0a80d042d806084860b441a044d0344207581d101440100400c02c400c440761900320b0441140005851310045810242c515001442c05036200008103821400350005c03103185031507100b03000c1d81c604078200c17603c10042016404c002441c038540c00628460f10394401c150620501191b090351703c03040395094400664000101000081500d043c10f4001e00000000a001c91850310200402500c14800c011844003417424042c40c05281d1418215842c2000b00304a81c0f41c0f00d101040c007425031440c010350041c1c5102e43c4403c0d03076038205511440d0035110711052101032546c040700d0400d41f640d00d401e021a003000c04149443c4a966514981a066100704c1c1c10002103c0d0810300001070112000820390400480014040300c08040a0b41e503070700386d51020081c500040c0f0070910310300c4400401c6d8441a20410003c0c003250405559680d01e03418580c08450580e24103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 548252688 1250 548251438 548251447
    0xc030b0f0111280c0b0a080606030f07110c040501030606080d1404060e04060308121909020303030a090303180b0103050d0e03030d0e07050409080d050901021e0904090c031b0f06090e1506070503 85
    0x11f0380042406401802c11111207065240c8504019241c1100404500402c0920511984448014010b44003078410240c8140072568590403c54042c10b84d600c503001c00792107040f01404c40984924204400300812261091401d480d1900c11508914441c080a61156980d00d0010004a07482c0040403203c405100500c3c151030720300740c40741400f900324104520203406c1080301c5005980110480340e0048400500244010311410210001d20303138180b00c444501c4c004d500040610132040e80b00c5040f40e21401c1243c84224a1240c1169280c55240c0b0044d0903900910080884001682190b00036200800032a92420303520390001e005d0340c802d207105603402c510000740b420100915004a40e4414810741c000d51030318280b00300221640000e00040c5030418400702d80c4481d596200d4100d0420142c025214a03009522420403a8403d0070803660780c1c9016081d01c10015050342d40300e0b03001045901070b40715885802e04c3d1007403c0c906120300800000b10340c0e03601c152102451b45ca10010b4103131107020310011350b00c0f03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 548253938 1250 548252688 548252707
    0x30c12040215220b0408070303030504060603020d030c141501060e040f1a040b060306030d0c050f060c0a08060a0f050d11060a031e06050d02060703030902040c030b0f0111280c0b 78
    0x1941107540041d0300f42a0200811b0203c580300140c00c0c8102c035418640043c0e150b40300d0800070000c1407207410095006c041c940704802410380c040c1c6260390f00c0d4000c003404090702e10403403c481d548112078035010121074403040041144a0054074450040c080160000c02c0c011070120044007254001c01c000e141d40000c03407600310f03080e040c5880f503009844c1b000d8442c2441c0d03050440000e41d43e501c40540340801c20152032901800c00c5000c1c040b0348042500c0e0011540181000f11990482d504080441c1001401481c006a4149013083e0f000301100c110395200200f103805c00042c030a00342250302c41550000d03910f101c0c2c04001e480b8000205908062903500254586400c400140c10700b141d1050b100400342040020311a5555103425014290703070484005940344e01c42e260a4001c4c0c40e6243c0069400303440e1401240340203030180c0002b00d0b92841215000381843c055401900d148620052040c290380c04040550948445203219802d0b250603102c02041c1c1c04200e65070381445c880b076500310426020011480d00304 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 548255188 1250 548253938 548253997
    0xd0f11030124080a15151e03020f0d0b06151b06010e1e070c02150319060609031e02010207031718040501120201210f060e0606030c12040215 62
    0x2074004000035040a040b43d0300c541c1c07408888170041c44c809596440803d500b0001e006083c400030581c000c020103a8142100c882d44001c0c00512050f401203c40790ba0782d85282c42c01802511460340d12041d00412030700c1302c0d401d0041e4080b034804001c0312007600b045440017464a04860000b5030012400038405581820280c070288107001e00046542101001c000000394524103213154801180d00c1d00c6003540d149400012001145010702004200c00081404030b00086000c074035820380802402403025951704e14048503018050320015104800d010402c450700040761013080e0140d40144101c41d0040d8590301c0c2c00300300c000318010f00b46d0300642c0090070085015200c80c0011184ca42201d04002d10742c54074a101038810036410f00241000f03c9030342c40c1948800c6150001d200317038009480800050084038510700080c0400c0c01460008181c1800140b264600321048a00c241c100c1c801442c20f00032088011044d00320b000c2c0040384d006d244000c1206010304043c002e80203aa0042106540c06110101c0510 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 548256438 1250 548255188 548255261
    0xf040f080d03181b0f08030304021504140405060a03170c06010501020c0f01050307031b0c0308091209211002090f0109080304062007140108070c020d0f110301 70
    0x3042c1030501e01015840e881c0c1644011107260403050b079081c80f080c941d03210326030107080c0d4100c2070132480c190002040f0003030000013441c0700d0303842603e04000c980b1060140c4015070184d0b00c506029003011400903030407410241c1000e50000710282800403100c1c1c5a99a180c04052100c0c00044a00c1011841c40700c03591013000810300520082c00540280c0c040f0343c000c92a0580c0c2080300b14140000013001c191002c1c460742c040120600d07a4910b4003104840304500074822a00d41100360001141c140c003081c1414400f0801d060895000000145007500c1700f018030241007026444640390040b00c04147e10003200c00c0c4101c00b2805203040300180d413030503550304000200c8003011504d0f0400070303e10310170700601c5000021a0300f940ca8508100040d0036802190014a460441000005000d0340f00c0010324070442220789401034100b41c80d160b409540744407080742c2c0e10305907840c0a544000c80291020104403020310500f8414041c3e501c840103000008003080c00c0d2200700c0c003401140d45c002e00d05107043c980c2452056 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 548257688 1250 548256438 548256463
    0xc0b070804170f030105010c1416061206180914030a0c02040c020a110913081c0c0203030702070b211003050111090102070e0601171801060504020703120b060f040f08 73
    0xd07040288507104520f05000500415050021882043c4c045c080d40a290a005203440011030380903140442c0503940e41c103082e01c01d100105001d2480001004400d004040c1a14680b2160040d01a212060754000d0001d0120640d13070715a1410704061400ea003403004064548540d00c2e603891900c0d0501c14007040f10fa103a480401150012440301c030014090308200c40140004039000d10950f160100d0445018a040200900c00f080018490350030038201c1d0754007007031342c48d203004100720078104840b041c0d80740d100842c1c0f02d50050300a040705100d86061640034150364001b2010404c200e1003001d401c1c8030100026100b640e08140d01403403c1082140c240241d80101030b0441155040c404075000103981c40c4014014100000d40800000e115a44034103404680881d04540501d181d04040c3c82c0e20485460300070410015500b401c40104980c1801e00072187c034554117075925100307010520f030484010810620015885241006281c0b14210340c0c80c090400342c040d01e0b0301900c03081e1512903090718041441d80700 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 548258938 1250 548257688 548257733
    0x18070611070f0b070b1b360d06020d0b09150f030d05120a0b03011d07060906120b190810140402030703080f0705010213030308070c0b06040b010c0b070804 68
    0x14001403d0070b00646540036800011424a0b8440403c2c0300031030600309242d050204004250301c1d5030210052004069503244280342040d040201c01d004d48800100d144071178102000c6140440040e01540c010004250301300300000300d120921000400f4440103842c0c0000145150700c583c045441c11010182c0d5000c000c40c010508660344040251090280c90446024403d01030002447c40d14590800540d8660050080080500311a28000784103428105a10103104003107011989500071004030042c2c50803a29001c041c84100580c1c00d0242002d201c540d40c1002004550700010b40f1209881e001406055014001183d40030071a1070403201d00300a20040b192400040c080561408a2680107981d0051580c582d42c0e818400c28003428880c5940c020101e610005907042c40c0e55410a54205a0340700e545c58017001c4d107410408440d0745c1130350400038014041d160702041c80c40c9404e510040301000e041c10540c020000c0380d02e4010340e1040c11903002c008240400100020801460601515110402013 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 548260188 1250 548258938 548258969
    0xb1818010c0f031a0402130812040b09060a110f010c020f0303040f06050c040e010906180221090a06060305010b0f0a0303021504060b0d03030902100309030e091807061107 75
    0x41c000c015554a4042d041850768541d05284100d802141007404880c003c0c1095540e4510484141c00348605032103641d5040c02200f199043c444007640c1118100e03120484003c1c02c2145000c1003226580c01500da6605002101180f403030b07404424001d00800d401d20704000207000502c0c1c3d102900f08170624984082d260001c004000018080030b41042d82e440c1c11050020302ca40d1703801c0c5040a41d1003560000040c00e8400c000000d01c150640e0080000d0f100340240704540a8402624230081c0d00070342c44142034503054402c54101c91100050394950104d00c1e241160902001500c403401150301d00e410682c0d150f511910113541d136051405014442c0e003c1910a030f8045491900c0080d1600e920504003031b50759465101003414414036401c030090504c0c1c001c0400c4009801032401070003e0002907401c90141301c80c02030100c2000c0c02445132014044e015190000007260440c10030484040003010780754140c486038900070a422040200c44e01502c482d0311900b001068203e4000d00d000000e511007140c20342c2400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 548261438 1250 548260188 548260211
    0x120c0b06010f050d0509151305011a09130201020c10030b0f0a151101060324050a0e120304290106021903050a0f0207091503020f030613080307030b181801 68
    0x1800c03101a0768000f0070015244e169049550309006460642c140b00038140c105000071b0b50b404c8c40d00c00451600c298001c004115050070004440102000d00607804000c0302c0000b10003000790000030400900c14810383e18113485160000790704030005582440001d81c0c0c2c04080c08141441c2060000303680c0e045682e010316a14101118040b07440030100c201c200402140814101042500325801035a48601828152003020320a00f240c1180c1d82d1803c4402c0c0d040002081105015210784680920061701400c11a521400e00c18100c0c1e10240080319404d8052210b0114440c08035043c40c80c000007000100115450318000925000c40c005800025408074101c44c40001c0e0040f085801d0700c086414400c2071110181c0c0d09a0502840b07500c825a11820402c0c0c1d01003070381840c15084207403482280ca18040340b10081c00e1540c0d6410844003040e0310b8502105060216001002a40e4040c1c0c9502c7c000c0340e500300c40f0012441400000703c20100e84120310b41840040c0030540c40b07074503110311400d00801913102c04c0d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 548262688 1250 548261438 548261447
    0xd06120b06010507260a0315080d0f0207030b01030f0b0718050411090d031e02070b0405220c0507030f050a02120318010501120c0b1201090f09120c0b06010f 69
    0x900100e05004001810501700324020400a0620120483d0221200c0903400d400c181a408000c0c3d41001a02d0482003064000440300c10300282c4185070010078102c2d01100e41540c0c0c04840084040c154032034070b40c0000010f80c0340c0c58146d02951140c2d200c00001c810340d1900001101d001b51051042c882050f0f4040140c040304841a0f04951301207401044e1000c082208410cd889028840c1750005034034000c11080c1034002000d403a0b10b606c0940d28450742494403030126204e84060007140c141540801c0100680c0c5400c107101c102103400b0300c9140000c15103d0700c8110440d81564500400300d4008500b440501d83c1040c0150314033350310760034894500100510000e4417803200c004202c00c002000f00c0030036010b10345c1840c17169000940000804c5a940c4ae190440d516030b80d040b10440e4104822003000c01e42045000030344200b48110340c51502760364200950310000e002d100c4072104090b540ca8184001143d10645402480e401d0f039120404000d5080c1440d0301d031404010700d918140900d041c00070001d40c0d0700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 548263938 1250 548262688 548262691
    0x18170a14030a1d0a02090c1612020f03040303080f0604050405030702090c1605010905060601020a0b0708060607210908030a0e1201061d0f1510032d020d06120b 70
    0x410311034a41da9030326441c4a20040c0301c0c04240c03800800000d054507100b80390001341050003e0003210541c131141e440c0088295244501038013010200d40e41c03945100051595000d407020b14107540141c40b920001c001c0130616607000f981c0141d0004000c5070500650b03403070304021103422440a031800d005030300e8541c4401d0341c2c9110f0484024001d405100002c2d003a0090342e401d8500300c81226401081b58001410194003078441c0c270300f041d1841e00650000c11101d6000042c00c40101ea4801c000742155915400c00395100400188640c3d0481c604004000005001080c0052501c90f810150ae4034204405801841090303540c00c03180c2c00d54010449600041d0300036030841d165120481301c0d40313019442d0841d424050006039100f9058441c030020000000c03414a100607106040003501904165920002d6840c0c0c480100d4000350410482d0894814040c4a40c100a8a02a60a22400300903899001e00381c1c8a07040249442c104550200d8a141e0b00314141c041e41005020000340082142415220008039010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 548265188 1250 548263938 548263967
    0xc1b0604030935160e0403170c070f06020c06151c0f050109030f0809070509011401022a130b0901050409021212030a050f130813050418170a 62
    0x16240701030703c10412501c2d5840c0c1030070b942002c0910540c1243c5030080c0d95040c11141c8201c40d1007181d6000c83c10b12011410503204035010b42d11540300109041050b6081c5101808440c61564200b0504000c00c03655140c2e48c10b142d11030400180e0750302e00790355081e0401c04050100e030180205515038102d6070b40c91b05000c102103030040144c0d0a05000c686012060000c071620014030079424143c020081c1900610407001c14911511041045c0ea204440c05031038501c540034807540114000c0052090149404018103501d10600450b0344074805007084650000d051500301e203076041414440001800c00a4282550100400d0240300600416000070142003050017194000c07591529180150746c0c1d5804440b120083c0701040d036641d201e100603101c00315403048451102c1103007004045404d41c41013032031292248460b40e0540030085495034034401c2c0c9900c54040141e001c6101c0a004c643e030b5446120b4503d07000d8118030032048004251034000c1c0c0f0310121342c45504074500d090101c0c500c42d03900309201144495 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 548266438 1250 548265188 548265209
    0xa0e0f040803091e010212010609032d0f060b010f03200c15010608041a01030b130201091502070503071e090f18030518040204080a06020306030f060c1b06040309 71
    0x10743d0495580d160128070207540c8921390402e05880b214078019801407d04040c03401c0b64026581e201e08091301c0076017441c031008210f0242000541d1301030032a140314003a64081001c490501c0e09441d212801d842084032004c0e54800c0d5141c034241103645e045030790784200d0340b1141403d100900c034007101c091614030f40d81c0003002800c0c3c0010300780c202c40b1001d0003059880d070602d01d42800c065844407802405000700f1182107540000c1c29840744070200c10412094100c0f580000d078080d0695030040500160064004101d06009170081e000c584003102c1501320300d100d80e04e075000301516442d08041515201c010343c40181c143d5820141c02c9000c4002c40c2c60740080d1500b0f904041103408081821000615a50300b810703550121003070521041660110050400d20b00003000318000c0c6190708200800c91103148a2080540c0c4031a00b010000755045c0c019503440340d00141664650300c1403003c003500f8550115480803a6607000119103212a2a2140c0c080c00c9003000c40c0240010706e0107039009442598140100d25010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 548267688 1250 548266438 548266441
    0x18030e060c030301080607020d0507171e03090f16061b24020327071e051002030702180405030405010503090c040c02010f0b1c02060c07030b0c04050a0e0f040803 71
    0x94860a086034a03a0710904110b9650f580e50700e1406885040590784400140540b601603580f680c444d4040c3c40a09030004e0007907500034000400d110940d40019140e5a81464403c1c0e00c030903124504d0040d62060280364050002e03229000d01c89400c010f614102d113000501100400d010080e84000030320040b0315500700c2c5031a0781b404da0400681007004c0e03030a4600181d98080d0040040f0343c103a000b41d409401e0030850000f22103045102ca15011140d0601c1040c00d40c03102e6001c001444002c05142038003221861402061901c0700049100482d4841c00007025038000907954086040003e00a0035803021482826900e0409a4407140c50384181e00c00c1c14100500800411401081480003c8070781000030300400c034101900303202174060704004a42d90640c900e080171000403400c21010030030516091f206200c00c119030641c02c000c440d03004100f015200344166807000c800a00b000d03400c903009903101c46440c0c1c0c840b071501081100d03030009a00001100c0150005100c0304200c0001c0c1c103500594401601901c0c2d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 548268938 1250 548267688 548267717
    0x30903050d02040f031205120c13050a120b09071203030c030b0909060402090a02090f0402070602091302070b0703020c1f0b0a031419150903230c010506041803 70
    0x298011500c410301ca0a20019000030b240121090600032640b081d4858180d213061a40c0544403801000035013044200700800280c0c01c490658001d1441003806e440b2081b50365212000308614101c6a0007403844000c000029030305001c0101003c1e42d000b440100102041410600e991804058601c0010181a00d03440b182604a000380c2103000d955901910040651a122040340ea803068299000da000d41c07080c0003c075803000d046008a0313a00d0400504051f0081c0210000d00c4001e510404040d41ca803a4240311082c4141d85a0040d5480103005000260310303901d10b0304003007501d001c000e4121024184104961400c010b40483d90302d03c959240c1a181c1100c0c107030140d018020b840e0001101e030344000240d00200400c5128603000601c0c032840c80445000e000719036401824043d0007480500103d180283e03485101c4226001121401d2003442d00071222075004504120320441c0e04900001901c01040c1c00755090350902c6402e034002c0c0e044402344600b903590700c40340410911642000e4208089900f02406 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 548270188 1250 548268938 548268947
    0xc0813030b040303052707210506090601080c062b1b02390d1719021903090b0f041a190908030d2f030702191101030903 53
    0x640d0003000c0703001545014600100101000c41ea220342c074a40c04c0040131a110003400c190880d401c1801c0081c0005428550700c009515900c01201c0c4100411500c4000010801c0c4401d0b0300540c106001048154105120036090083d2180d8540c01040e00744905000102d000d890100d40c00455000180340c01d403295412406001c00340008030f0b40c0b092141140080b83e40c00541101b00082c00410b500c03405644070f2200c0f482540c080c3e052000b0000b2460040e801d46804000d0f1400c8501c55880b80c81b010b50006c41c1c0c02c1081d0000c03100c2c50110b24a90800c01744e42a010b02440704408014201240e400010355406000c5481e5800f8040b0a904003080703c490510850301107801800c40750366800d12425200c0c0510000d07900c031080103100304900c05c0801c0c0f00107000d880001c05a5149501035810204820000300003820348081c0a90b400240074107440c110400c10703042c840c40c401141e00303250b0f0701c3c54801c0000c1c3c688040c0804a41840c4036680020010a0f10b1403400d0071940024600811048d40c5d9017030845 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 548271438 1250 548270188 548270227
    0xa0b0f1b1c0f090503030c1005180d0206010509090c011e021203010b0301031a010e0f13080a090906080d0509090c09130911120a0f05030d0c020f1b010c08 68
    0x14603071000304046450032500150007440301c00941e51918289520f510500d81c980c042d41550750201d6000e01840e00e10003200f60007940d800003588100c881800d0000c004c0a2400d00390f26660760142c0c2045005002500308000d5440c2d000c50618018584400404002041c280d02c02403880785034140c020700001003a2080c0000c1c01c150380d0303074540c40c3d85a58603005201441d600a10080b074a180083d0485007101520a204134102c61140042c0300390381e42c81d83e54195580b40010035040c601000c00000e02c1c005600000179040c02c00c0c3d00d42e1807900150412145e00e0841d00c0703d41040040d9031207104011590761748041100c001050039a6a01300a84881c5030304c00d0f01e0701071802002d5008050000403888858035038040002075006a1680520803085010f014071f604a050f10481030350000e11180c5e0100d002c60f407900307002c907105104882c40c1140784162b46041756210322180006800441c2da40c10050810403042e2151003641140c144001001800686441c0e001310300204090004642c500e1180542070016 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 548272688 1250 548271438 548271463
    0xf0801030519140111040503010612030f181a070c0e09030a0c0614070210050a0b0d0b07020c03120702030106050f061c090f06020c010f290f03030a0e0a0b0f1b 70
    0x24410107a42c8440d4180136046406548d00a6207444000515040b45071804060980c0603210b0304040c5000c0902180d4403151036140c01c5c070502e00d1100c00612861400840c088042c02100c0c50b5855495510340b100d002c40303030381e480742d50f46a6240c030500001d00d80110813503800030f041e1308000312061080d19000c005070040340e0181074600010b0b420440d9883e008102e80340c2400034110300b080f1130342d91043d00368102d50810340d00701d40041107078900c48001129080020307049041801110740b5540b030100002e24120082c0881c0d504030740c0120b6500304504090103840064101100d03d281c560030110003086241c0a54032610010120740c07071021108000d990b200584483e00050070001c01e500d0f80c2002800b0350f120b032014035429841c1411201041503688506003114510081191551001e40f2402004260078241039611a072810020f01c455501040144400e59064440c0c4501540f00400c1000c41c051550250b5000d1400700085158034440401311035174001054103000400b4a410307a110b00c0c112048405 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 548273938 1250 548272688 548272691
    0x30b15041803080907061407061d010c26010b0f13030f06021213020102070611070905040b06090708090c0d0f0f1b09060e010b0901170109050402010f08010305191401 73
    0x601d0185540480514410722680c403c13140c841e56a16405c80301c1640000424250340c405220350170000b942e42d0468441101d0300503024441c00006103180e402c483c043c003c4031001c07070b012010b25441c0604295100c1c00c00c0c00304013104c00b0301c2e600d000d83c01c1e080e520410031445090400055400007010200140d0340145400c03680c5201002d001d03140580095110303141d541c40200803070f00014a05800e08806810507681a805495403034074000042e16041d002c124401420700a0000119003251346110b01e520803401801100c0307441c10003c050150000d0042c1401e001c010000e410446501c900140320701e4a0402920b003240c014005040810a000b04800014142e0f0022001d0b0018000c0101d4a03050400c482103202221a99802e0b011040366031620940144250b99401000786003a0030340508103000d010704016800401c050054030480c0d03800d8000c0304203155110103100c19560f2010481440f1007642c03d02030019410b41c0c45403580c2e40300105060100082c011040d0080003146000703076031aa05240c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 548275188 1250 548273938 548273981
    0x117060d0c0e25020d030509031c1d012c10050a0506030105010e0610050913021303050c06040f0e07020a02040e071805010b1218060103150e0601030b1504 68
    0x8a802d11207400e44012800403128a402c07103008040c04648100024260002c0c0740440042c041a0050000104216400d000030300010b0240b041c0e51b81c418246042c1d054000070003840281080302c80c01b61444144070030341c0c5850040303507100e02058070114040c902d00c8082c030140740706003140c2131400d00081e40702c510302400c0006022210080d9003103540560402c600a0000d80e0f01d421402d003a160081301d07040d51003114030381440031050040004211199000e00019658010301c0c0c0b01e10180c1c8e01c001e0b0116403110030342d4010014010180301c10419001c080303409614080c034154074045000d2490141209a003540030110703800301e000300300807132040e0349c040c2052214081c181e200035250a0300c1c0c4078800f108490408540c80c00c090501c68141a668940d50a60600e000084894203450004292400708071340ca04840c2445d42040200500862084000301d80040905500c64141c0c1d81c03002001086a210200500001d079900f05900d0f07001c180d44920103040c900600008000e40511034441500058210 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 548276438 1250 548275188 548275199
    0xf0902090f03061605070c050312040f080601060c121701090518010b060301062106080d110c0f01030b0a030206030a05010602190b070507022206060905010e0117060d0c 74
    0x8000d015a040c08444007000e4a92820a15444540480308440505074620400c0704441c081c8003d4082140a41c10b01d080c080d8417071022910702038008036805820700002c5420440194900d4020010b04464806001554075020300176148550080d0010800e280c228112200035114401907034a10346021106461540c0d1600301900400042d07407500120100071101503078040c4140030315401040090034440c550ba107000300c116641030314000740241039074603000d00c40c0c0201454050b010240c0792110141a11455651000d448207078090000041c942110f091b01106554a520701c0b002c1000030708020818156520000d54594884d401c001e50011011040c03240b221119404a0b040e1002078084a002518068004001800b41400101120380031030014803410702c00d002500f40d440c0702138116000c0e101c1054600d95086224001002c001d03690394402c001c225400031030f000c024102824410454096000000c01410882070740c0448403883c64045001a1a61411a2200360300240d451035042e4454 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 548277688 1250 548276438 548276441
    0x3040311011a010210060e010315060e04030201020301060207140618040f02070302071503141918050114061f0309140a080406030f0c09030b0601110105070f110114011e0f09 76
    0x2400b80b6070040c4500072074241c03003203040d12801c0c09840002685000381c0e0310316074401c0410711160030300074801612407100150b01144409520b018030300c2500050784035030403e000203241c61645c2d808401c0c2e4400c00746054103143c54140c115144218444d1414000c1d402010109010780550060100da0510000f0000d0074168041600401d07a0707604070040491001070401107007900c80b843c8141210780c0c3c0a101090340c1000400e0400b18541c607030340700440c8015031008801c0b8100440d50b001d450380c1e51103403421250602d1103041c6e1940300b0b00840e0014411f40c8a25a03003a00342c21400800380c2410303614101541841800d2980114809012044441e0a82545000c0496801500c02c00001c6030a1400445694031503005105142040b991512911443c6486900764502d000d02407506000c554410394510ba8028007d283c032448003a00c8220703001c1d094140c0200b5040d1075040c1540180d01d413600382d4032202a020303082411210302240b007081240035003a028154490740e0748001c0740603e031075000291910b100e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 548278938 1250 548277688 548277731
    0x12d110906250b09010f0b030f0304170c0a09060509250c030215010f0602060112030f0f0513090614031626010606020601180911090a06050a0915050a060906050304031101 75
    0x2018040204101f0a041e9500c140045410b81c5030001c1c030040c03040d089040013940071410610210703656040d51401056541b00c0342d40000d288561515000e001c42c0c1010110290802016403440c1008103090f0585451494800401020070507503004440c1810710070800110314a0100090084a5a59050030700903170701c0500c103030710160003440000100d4090f08a484803500b601034684058110a80004450103001074000d017041c0903040c041c01c624180c0321440d060245c009540002141420044041d040e02c0000001c02d00c258413400035209042810305000049409041503124010581c4058513076000d0f501d03020204a40c680000001d43c107500003034141c103c4151114580041c10343c500c0401c02c1c4c50300c1c204c01500110207012900c040d81400c510a603802001004000b0b000380e02c8100281c00032140c4da004400f26074031540c4400c0c0c0c0701c108070066001420202d4000a46914285015141000340d200d180d06121000c000281818003803102d140080c042c00000300150706903008880c084944 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 548280188 1250 548278938 548278961
    0x503060a0e01112d0708130305070b04050f09070c21120c0e3102070c08060610030218090c07150608070314012d110906250b0901 57
    0x7001c201d421214003443c103c990300b0b81e0801a600611000d004000b51101c0710001030007050750100100c0011400460240456000c03202d40c0400d46441c6041103440e101c1941c110300f00201e03007040708010f243e60f0080c405d00b1601707080d10b01d8007841d0346021068035010240030300030b041c06a02150803184a08124144140c1c040651926034449100c038030048201c8100da800c01c03010500c0100c1c184140e140002c00404411400018078a0300740da4066031200d050380d14542442015000f0902d0f40802c500020500702070090301008004918140000520441c1390b02108001d2642c0001c2014500c68441c043d90140600a000c03520641001c10065403542c1c001c81c2d00740c03075685991503410050381e0f043c0100310032520701e00d00408405040d80c55940d4001010b4040c0d030311565032055503400280350304403144004550441201c0440d110b1031120010b8a80e14002e111500e281041085869030b10001644c901c2e07e410b40c800d408041c1405198507419072200d030007529405800041207005178054010001c440e6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 548281438 1250 548280188 548280191
    0x902030727050106031503060e0f070f050f03010c02030301180612030905130c080c2d07020a0807060c080f07021203270f0607053a052701090503060a0e01 68
    0x2a604c41c1e04404a481481140c840c0020400c2c0400104200e501b10504240742c00c4243d03058110340d078986910b042c8056000c61100076516008104926240068003d1004154000d221350482e0580080d2070f41f10501580306084a40301080300000c0040e072040018004480c07444401a145007000b502e00306842c41018840c2200600d501c08202c41e6000e443d4014038a5168074025441d50050b80e40142c100e42c19666a400c050710300000b64180d5601400c0d011641c000c0107039524120750051201c200096086222550b05c0401d003044546e50003000c61040700e41111002c1e440d41000307412881540300d480700103540426440b0005088400201c018240b101c400410110405500b0502140280881500640c899482d450300720f00c030304107440100b803410310501c280d03903984403510445440c00319202c0451203107030000c015412070240c210500da0000105ea00f800350030a802084424402e41000c403020303d40e048500d1240d0107990241101101a24004094036440d150a1503004001d100c40c819800c240d6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 548282688 1250 548281438 548281441
    0x3080c0c040b120c040b0d0204020d150f060f18030f0303060e0105030f100f020c060f3411010b1302030a181a060f0901082505060706090203072705 65
    0x14600100c5840f03c2150460261028642c0c0004000050004005080d00140300c0a00800183d5403840181a14a13420740002841c209103401ca100f62006904001401c69000e9024400c0f40e4000f8101440040d031880c085402e4426081c0400362240c807035000400034000359103c0c00130950075410040545030300005468403685c2e60300030076a68a017608242c0d0311a801261f00c0c90000300782a00180740c120f018540251414900000d01403074540201c0e490040005008180580c52011042910a50104642200040f52403c00450748003450480c1d645c10b10500922542905000303401584a100d00104540324100c00c8910340c6002e5842141c0c02d1a002e4a0480103079041d5030081900103c40b900316403103444c45031004200c0c058a03840900141d500206032102070031180e5482c0c0e052800381c0b0032007001e0440c49120501603030f1140c2200080400b2004036200501007500c0d0081603440c4180c100101203200c10341400801e007041c005402146d10801007182141645400a038001200a5466010440e5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 548283938 1250 548282688 548282711
    0x220512150a0b1e240a0e0301060f0b070c080d0c020307120506070503040606080307030f0806030703080313031709070e070e0904060e2506021608030301060f0903080c0c04 75
    0x4860000b6049940100b000c0040605240a800141d04107440a0480342c498048442c8642e201d190504808614180c00100e0030520740d8040d468503100e40b002d6000340b10490030810324400c0403907540222964034802185180c140407240b824480282000015910840c1c608040102041c012207002e9020703104070000080c4042035110001c600503008001b80020b07840300141203c4541c03000e44195201921890082489001400200085c5103e501c4410b14009202c001801d105001401d59109403c003500130404100b40b041101d43c4108913080c07a4050300b0062a041c1c401590384040d00d0812441441086030003d0000740c11010385066210851a03a075400d5002c5492111f180207007900b10640740041030004006811003184c401c138003800d03164611100d03596042d9000300004076000f150f494400421080303406100703020310f200814070740c1d02d246418010420354920041c45408100600040c4400442d80b25501e00c0020b10790140c4515920211490215520105008014481c1d0700d0030000d850b8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 548285188 1250 548283938 548283941
    0x50f06120c0a0c12030501050405090307050703061806050f0105040509030c101503021e0906032e0e03070302150a09030c060c23030103061b05220512150a 68
    0x1811103620031000e0007661007050701c8400e900101411030500119454036400584002d2003e011030b000350750005420342c941003c100c1030f18000352042e11a9001002083c0110350085509801c0d2a003182002c00c4402d4070042500d0185440703007026002d5072516090114503115444514100ca0089809010946558018507160302c07801c0031440f219400030a0030301c8a40c2544d08007078004200d225007000c80564940115444c50460000c000041c0740b003805000c2d446c40d2500803950843c42c181c0c02005024416010440740003014031034120384450100300c040001d80c00341c0080c420103109100380e0703803244122f02d4007030b548000d4081016140640200010803510303161140300400c5800d41c1d44c03c02c617140c298895500406101d0030340c504000ea000b000000301d000c10095444951a01e8546642e250725505008044130003200402d03800c0c20500c2132071588a9400000d54081445150021080d0903011601d89550b00441d404039802c10086403040103040e2020480390b1007982c4d2a038107803100707940390000d910 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 548286438 1250 548285188 548285197
    0x6040f0920030907030b060406180902040c02030c2802060c0f0f06060a0e070207080601061701050d0f02150c0109080403050114160e03071205070602071212050f160c050f06 76
    0x41d059101340c04c10004142901440342e04800050b00002d18961121074421a85040c0b02d140344010b0345590502003142003e2023444144007552001d141048000c048603a00c6507040e03074242d45100121141c004130304003104000f044081d40244455992003482500d280c40704051250b09e41c041c018101d0300a06042c02240c1c00e031154900030309500c01c01d030400a41c1c1c0e11200d4003401c0030b001c61042050110300054208491800781c8010703214030311320a0040b0302c040c3c0b8115051300a203000340c80051031040000d1140c001c015140d58100e404045500c03d031048802c3c50f000706050385500798246500b00050094500080040d03d0040b40207000311685801303003844450301560010210f1180c1e0071039201c11441342c59000352500004040d0362540303a88004501c1041110f800603540350f041080204056030f01084054020803170500c441c010080daa0326004007000d01d400c124000d00100003904860049500202c80915103070300444020908142404524191030780a5280500794980c0c284100380b40810588 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 548287688 1250 548286438 548286451
    0x9060506030109020307050c0601030305040f080102040f031e05010603061a0d0302060a0f0e06010308180d080901031808070b0406050703020903100903051b0c0901090c0e01030b06040f092003 84
    0xc910756440c1c01078102c02540000c0a1204003d014007468111410600155000710301039550f850311a410602c00050311b0049902c41c401342d030300c100410490040800141d1088079004450058a048082d044429071140c01c00020141d52810001200704a815844014505511505c00c8419864481405001040010040c0150380800000340c405400c64200082c10344008c040410301180043c8601c0c507004080e0400ca842c094086507240200101e141c0403c0111411075401924000c2034840300d007284038400c1d12904168596484200e00c500030424407001c40c0e400300040d03603120918109405002000d5a00307d95142c24080410001f034800c0c001d503100180c1c003e02411420582041e014000c03c80341c201141800000c2c0080700001740b480c05080318900045016103101060304081080c0c614058010b5808286007020340c1c1070f0349501495003e6039083c02c3c20005405000300c0700081160040390b201018051140c0c901069190403600410409022607510b07000c00c2240b040070749005e00084401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 548288938 1250 548287688 548287699
    0x934031b030e1b1e041b030b0306060f01090b1312080a0e03122b14070206060d0f0b100f0f0603050c040509190e060a05181f0e150106021501090605 65
    0x300080e14015400500c0700035000b0400600341e81762000000c106c0c80074142440c007083e030342c0d45100c1c0d0505040c082c20350700401c01c564001c003a1508000282410085015002c032007a0007066018000309100300f1000a8440305c000c0d5845e105140c40c0080c115440741d284080001d229041e0480541400506d0080ca010000405d03414a440a80014900c41d60b50b0210160607001e84090010600207204290f000784040c2ca50916030301d00f43c0340c040d1801001814850007648070010b46004918001c0c104019145d20501c805101c2e2070f003040741c50403040c1c1a005201c490304400b000049442a0040b8481212207a0318140f003190340e605452031040c090307407050640109007000010340c2d040200d0800311989004140014042401d01c00d51850071504440070081540c0ea60144011445100c00c1401d904410600824105c0400085421350040c00390f076114a454075038400010710701c0144131111003c465407400684a43e5a104c0080d40d40d0211020240018101d80003c55000b10701e01821083d110b02828 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 548290188 1250 548288938 548288959
    0x1b0602030f16020414041b0e040b090a1202060108010b060306031c0c0803151806030a060507020c0607061b0507080f03061f09050934031b030e1b 64
    0x107107030840e48410140b1440300d110480080c0180d03100e10038400c02402c004076040e001c1c030f00703840d00c1c0c18103109541c48401a00410030040004050256406602641c00305070b0f2451170b122604810b141c8071001c0c0f0010805020121403444090340020454100c6a03500000d000c810103100034410b00f8401600c1c07035901500581148502101008100c130ba10743e20b28a800ca200c01c030203450f00c40c51608180d81d2803108131030b00c0e602c1070804d2420480c04848201c1070000381c207440c1411000650b130350141820003030205072140c0028941d90f00034000780d80ca080010b031002c0d9444100c4d02c3d062000304055003114000148109079070705107500c00e0041d9505154068000742c6098a640300c4013020b0b030401003120f50300c4410803c1118514100d0340560580104640302c0829041c03d0804000e415032008000307594440e61a410b0700b501070750561313504401004d002e4144031410402c0000301d02401c81045010505410030182e40b00807035140e400340000c2020082520b01c00c510381010f04507051003a040d050b901c02588603 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 548291438 1250 548290188 548290207
    0x6050d0204050c1306050d050601030203010608131104020f042628140a0b0604020c07140d080a111c05030f130606140a09050106020a15020c0106030f1b060203 70
    0x188019004021949002e0800308001c001c0d100c13000b05600000d00095010901b002c9114041c011150001d07002d082c254295030411000900d01e250050100c1e00300410300766054140550909080342c14000a002955524181148864983d00c18801c0e608a02c40c00ca5611000710440c1d8003003900b0914581c00ba000401803484840c44003c00503c4001458031000008000941000c01e00c1c0f544680c000050145074136982032000c0c0c4050010035082c0a140100119414001c012510006403075548401080c00c202c0e000201e0f66803206540c1c01081940e000074200700300c641116088050300800c10464400c4032264561441300c080c400a1744020810500c0460000d181c00105183d01589600811a041d401500c4100650f101d03940000200541c0c0d840c140d80504002091030080e25040c0400e0080327500d0220000d64480000101915007800e20824801601040d0112451610385000a2041a48030f007091034952101020450380f84115405c5000e458030403a005074210754103038024504000702d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 548292688 1250 548291438 548291441
    0x180b01051b070503030703122915300a090b04030c1e06060501090915050108041a0906070f030b21070e09010c022a040f110c0607020c010306050d0204 66
    0x502001d034880c01203441c04200c1e42c40403c0540181c1c0e000342d071999110b00d042c8160a04540323a05118000b903c1c600c443c0c0714000c1c00140000512000282c0e19500c009038142c1c0c030742c1200d000d40d00022200d0000001152030f40750f044400c402e8000308503400006103454485492040b03e1296100030a00c80503280000e01003401501c90018240c001c44814413404034a0941d030440390b00500c01182c0d0700c0e0342d0b554140000e584c0094100007a061084d001c20417844818882985503000d84907082c1008400c8000508100100a60740ea10043c0305801d01c1d42424004401510b54800300c5244001460210b10094158800d0181e8109640c02605810828080c1d402031113080680c2ca0a46116200c2c2c5d410001e80032914860080c422422900006400120648001d08180c000c0e80102424256056a0720240398030442d03900e03602204032800107070b01d105003240c64003501200409a001b4000440c1641c81403401050582c803d407201c0c1e080d14003011540d001901116001d0180c43d0300844050b11070f60050905 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 548293938 1250 548292688 548292727
    0x1051806070503040f110a09090507030c1403060c0f04030203070f03060b010516060509010e0307030e1305010e010603180b04030203120108010e1b0402090a0f0f0603020a0c02010f0e04060f180b0105 87
    0x949410881da488c4c0070701c04280c0385801ca08071015440300700100240718100c4080f40c0506025048140c0c40040700000a0751010050000c4d04030350000100700940380280b908450046130f014041c0c034030082e40d4003040580d450b941d01c01982c03524200a01140c0a40c842e900700c03581215101ea000d40756541585814009040080060109650f21003810410b444204003904110344645d5071034440d10101000e00c05040302c1c00d100380000c00d082c1001031051080d5000300a0541e0794526000501c5a8034140080308035418400c041e000b84d071010140001d06501000400a41100c4662401542d030f88509141c22160300b500358130400d4001a8003000c00c5a0301449070741c0da54000400240c149003a0300c0010340300009541c03002c500724842010800807049d030302000e0030051056082c21410f140762808090310188513043c000781004a00400780c04914080c050f60600d101d005030041129513103072540c078140320b246402015818103076031120107601c200b10b029041312050706a41c2d41e030134842e80820365122000d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 548295188 1250 548293938 548293973
    0x309060406030f0f050108160e040b0105090403140d020d05061807030c030603120e3604020d060609020306030f030708070209250206041101080622060801051806070503040f 76
    0x3240d48521001512900406000c1c001c070001402d101041ca8a00310010ba238130b41e000c4075002200604020114016040741e5046031016540b424150b60b6910f400c03511507285100405281c107001c6030040200b1659400741c01c9111103d46c08002640341c00c0c00b0041c041102404040480141c1c02c005200d0a120b904030b01050b407014140464480d841c2c0c0e49901801110004d01c0c0001601c147d11100580b40402d0310101d0500003101079200d03a91890381c0ca0b01107030310b4080030701c81e40398048011a0441d21080c0b424040c0d40c0c0c100d801084131a442e0f01c03441c0042c0d40250340d014403902c0343d843c201e14400404012030743d1140c1e1044086180000c0d03035090110034440101581151a41c1800002190003079608e20f0307021180711381c0942103510f010b20f40000032480c43c0707001d541041100c4040022a40307032482800f1071030701e555000e680a440c00381300d40c1021306201d41203209079500b080140502a00c0701e0701200c00c42c0d50b4502c00e541c5182d440102c1120603000866014184042c40d040d000081000760368802500350 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 548296438 1250 548295188 548295191
    0x6150e1311190909032c040c1b030305011707060909090f050601031208010f0e0a051017030c010c05030f0a0b01020304050915130b06071128090c020309060406030f 72
    0x401c42c40e00340700110040d404041410b48543c42d06040640c0845e2140a011145518039449080d5007104022401d0051b001401541da0b400140750107801000f210452034514482144104c80714a00240500703020710440c1d40d00f15850b81015200c0304085500e500f0341e00359655414042d4a0b022120000c0c0024840c240c818240070040303580400c0040c02002e010394042c001c0701c8010084040c0c001c0c00c1c100164000058420001001c0c0401002041d06c503070405080c45001c1841c0d1204185140d00000320b032306c071455480c0c542440d2001d004011001d00300e00500781000308030380d403030f40b01c2d0a0310948030032a00115100515000180c90300007941c0014110340e01032041381d0500c0c0c0c81d03e01040c00c00e0400d54a00151485484a100716880c00a200b10010000c40100344480f0301250041401030003084001003036000d91032440c070b0503600d83c9614800800094070301c43c0743c00d0424a01000c91994903000d00204142411000301c0c6030360002003100d005d000d004c1c2c40d0038a03040c1f40c16021002003d0000114145030f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 548297688 1250 548296438 548296459
    0x6020d0f180906060513050a05010c020f0a211b0819060905060f0411030c01120e03071703160305011d0408130b0901180b071103120706150e1311 64
    0x1103046103e1040900f5054465a40d2100150401d402a945a510051090703403410b00511160b43c0c4281c01c0d400d000c1d81074078103080c034100c050005030302c110b41a00320011442c58240b002c1038007105000f00400f40c1d4020b84008a20001000f0b420388200118060411035500c00e0215011050045202509a41c081d840000d0038062070b540b1242040020b403443d102e481c0c05481030000b40640c10600401c140f504800034010a030b00c07040042c0132a85054005c4010903925600300b203402d201481107039002540301c000c6010808101e040c00059400c10340e4403180c9a11901c0402e0f038050b00900c01c1794180c4e07603004102d00040302c0030700c4000c01d9410010000c480b6643c0074040644c540340c00362280c0c405009010482a01c031000303c8001041c01306c03107401c01a01c600c940001004018184001c45085c590420451481803001c600440d141034484510101240400541c8506008003030b4050950f5248890080c401c1950b80c0000c03182c01d2009683c107980701120b40050380c0000316060b100c02490000501200c120 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 548298938 1250 548297688 548297699
    0x8071b0b0c21071806050c122a0105070e2403060d0209091f060608150303040b04031407140f1306150309111005040b0d09080714010606020d0f18 64
    0x2c03440903500320020444801c001c01310300c460a043d90700a0100c9240940c145401d626010b6503694011414110b00b910004aa01401c91034403003107110403e42c6400d04a07080c1c24402d00b10b0080108642001c0004e65580312074006e4a000581d002d0401030081d10100b001004c120b600c40168005001c60b03612202002650b401603d0b4400217a100e040c1c0c1070003604002c0601030005200280c0b50081c01002c1d0b2410100f0310030260011035803504103c21298424403440c409012910394401d9402c0760b5980280441d0000400030381184407660407404c1c10554403000e40e100040c48140301c402c011107030700c010300d89003640207810f140c13050440700a0307031078001326a00da5503200e5522903044180d0301900080d102c1e44414140b04070399508040c051811fa6181242c1441c20800520600542c01042c0a0410004041c401040356401c03243c071146d04081c1d41ca0f40c41e41d003480c000030072400300c2c01012815401e0180005882d030010a9060021959849002c0803a901c000c2c11140c2070b400c80e8280b002c0320000c00001c2031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 548300188 1250 548298938 548298997
    0xf07031514040c0305070f050915031003050106090c120b030c0a080c0a08150c030c190918050402010503060d0c03060e0a05061f03120c1208071b0b0c 66
    0x70444a40c007010503011120910040c0c92000c140d110a0500b0802840300c0581d01118130060001e4500d000c80d11803404070002094424070445000301414044140000070a00c580d4070002c0700e1251008105290ba00c082c5401503034203a07510000415140c44400104064035007140b580714400a040c2d42081d80c044c40041d80500c0941c101058a42c8140214090380c104601858040d050140c02480c5400b03512207404050040102032036100c00022010611034003034402038498102011810394400880040001c02301480c81c4503a001c01903000c00c4e00008400309100d4940280d8060355503d107560743c0c1509010191421440403211b00c60344560000204407680301d0368990404002c040e00d44000b1030300f0700d24601500038041400d100d005400b15004021030004a42c1101d6000c20040e1020325180d5040c0c9451000031009815401812411202580c0c4580c0076442030540b61200c01ba0308051205481132a6000755006280341860780202e050201c814010706080605050300310089030445e2080348 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 548301438 1250 548300188 548300231
    0x9080d0c110f072c070f0e090603070504020a11010905060f010b09010e120a020310020d051819141c03060f080709090206040b07080d06271d0f0c040c030c02060f0703 73
    0x7002079032140c0401c00f82c580c061f00c6144005800c580a800604000e0004be03120390403442031610580d800690165101d0180a2030560010220020410b0102c1410a15240e00d012948070724a0400000040303a01896481030b90700c0000c3c1030f55141d500d56003501c14001c01e520882c0000300d480c40342c1141ea000595080000009040c4c012a0241c0c449044040030001c1e03800181c045c0340440c1d0070904000c08150000340e0000d207520145078241070f150441c1071514003c48040700001480c0103120500000070388040d20340002e0b08060307404100c2565a00307182900c0015502800380c0e680c01c2003000300002049138011140c1640020b0080d8074059031004100f2140e4405d03181100c0030f520205403400e000103a84103e90050031900f80141c00e080121212081e0a010f0440d05003000ba9104c02084841d038944000d5030301201c01700103c0f29480e184180c0d0343c1e46c801030401068484d60401c0307820284140b2a00501b403038000c80350000c11154840780742001200c64014804010540e61320366a0f12076200068000f07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 548302688 1250 548301438 548301451
    0xc1f0c022101020405041404021018030c080307020102070f0807050127031406060306060a09151e05040b0d0b0106080a0b0310020c010c0e060414010309080d0c110f072c 74
    0x169114540002e0009607020071801f40c01140008041101503125202070756054034440c502160204020800c80200081c6600050070b40c685240d0041645180003009100d80d41c002d808454010340c0d80c0d0705448031142e060090f1000b58011500c100569401040300a6020404c4100015445482d0300d03130030094952030340180c98603104400350000c05d00c005d001c2140c001001742c01401c1c0c3c82c505500803d280700041d11030b102566980e40710030441c1c15480071034840640303030b0203008507800c11203040001e010b01a5406014420303490901020340d5841d04004e8011100d600204000082c2c0c42c11000b5204000014600103032542c4030403840e20346940610409000c03030000d0a005131180c54034940907084420121400c0107101d014a1100d83c241d8074031041e602215071694803003240345c0450300101c0c058131203014014078203400800d0900b814402904112250007140d915802060055001296114420f08480200381c0182c8401d00026560044130044000791495034445010b60407411400380000719844c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 548303938 1250 548302688 548302691
    0x806090a050606161109040c0f06050901021b180403180503241b0d02041502030c070e06031002030c070b160807030c1e0e0f030106140409060603140a03020c1f0c022101 74
    0x9d10001040300c0082d170150034246041e9081290100010350340740701200d0001d421070352503141c0115070707a10b4258a4040d0320f00c040410205050911b00508030740c1c014800c0b4071000481c1e40011a4074100081c001e0642c403045140c402c4815000c03400308241c0300c03002e81000d40244200034800d165903041401403080c8a001c0200698441c50151101059280c0600400454108001c4080a04030000d50362060764015000c00c5007e4540b000000d1030f00751821600101c1302d0000c400c11800b0031a0101501c03034280903045808071a40c40400351000c0c1610100c100c0049140b410204091600c242e008a0300707000541040801d45001030b121942003c8503211000014420300941c1e1141c0c00d040c02c103040c3e0b03c04150001d00480741032449900004013049805401203a031104046c082c8100b98121500568104100713900030f01c10140704544445131a2026400344c4039141c0039141c1800c20303a060800480040e0400700981f01000c43c1103829000001040c0d84c0010244400e03074a018204c0c0245051f550440c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 548305188 1250 548303938 548303963
    0x103020d021903030806010e10170c0c1b0a0b091c030201110708130602030f07200a0e041a1501110f010c032c0607140d0c0806090a05060616110904 65
    0x10440040501c1442c0030703094040a000c600c64020282b1200509009401c010903038500400fa00b280c040c2800a040301d02c01c11103546000f000b07554825104460560321501d10036100e4036510958840c400520307820200c040d65403d02110b810148280a501ca8800400d05034420411148160010706098804020010790705040300c1e04000c114009242c2800a1818041c207070740c0c105041c0c003420380081c01d02440da034400708510202c0f0b100070805c41002060046060b485030034031061107408aa04a90b02a441d110389800082d10a5085105202400700100706142000046503091240c0801181d40d2180102c0014a03460a00a00304958040c0e40c0000b041c1b00701c0000942c255284041160307040442c4000b28404101c0800e2649d44450030381010345a5900140c10b0901511502000f18a000e107004241c01b0b009034025134441c040c05084a5008203900c1d01c8900c1001c50328285c40c503661110080001c0340d40d2050722400c0451160158011020054480c0e01040540d84200c07070450b215421802c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 548306438 1250 548305188 548305201
    0x1c0305070812060f10140a1701030b011d0112080f0d060833070f0207030f231603110a03060509061f0806010608101d0703061d0103020d0219030308 65
    0x109440a00c64105c4d02c05c84120065040501408107a0040c1000c0c10380000791190f10038050251100c1080b030340d4072000090341c0d59003002c03001e40c5028068990b600d019000e4100d1a108840350f0281a03840409182c03212140d40c3c0d460513140e03030040782c809880d103c00384512824a0282c0c030500380201031a40241004a00ca1284025a01a0030312010a264030110716000304031404094141d2007000303030508079490580100c0903441c0c2441c0381e20062440e20340c0c46280d000c0110f00d01100759038441c000008012480319002c00d170b46a10070700e00da03d0b102d100920003c00110f440c041c50100d03072140c0a08071041403900d0303888610540b10111080e00b05a400b02003442107440900c0010340c1201d1100348042502da04000005469205c18032450042042c1207000c60ba82d07890300502d00001f00543c419120704000d0300030600c0103480c8121902e80100b450043c4c0020360b11040113096100c9a1103642c07082d1913070300395820090301d01000708069030441c0c4840e20704409042d01c4100070000e1800703502e80701160b18040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 548307688 1250 548306438 548306449
    0xc02060a0204121202070e0408070506060604080307060f020f0a09080d0512040303110909040b060a0801150608150603010303200a020906010e13061e090b1c030507081206 75
    0xd001061841d204000c10011600c0e80d100c0480110341c001815030422124640403403400502c0e402c4928001a801e040c03008000ca4000205200c501c64000e07141141d851030304120322401a44680046e81e04100440b070005041d80c2c0c0035080c1051a03543c014141700304600a04096085110400042031004405000c440d07801c21814581241c01e18103685849491a070584d50080c0290004050540f0345469188131103000007610448500036002001c9407400307003880d9034a41d105450b04c0c4d00450101c4c001040c6007406002d03401991440700780c2c64154501d8020304480071f490041000da41e00354001d15001155039030724015802180665201c80e40051510240402098004d12034010313980a0075440c40141c46840fa0a94800424200307004251450004522444840030803080c82e44d18100000c00d0a500115420f0161080074102084c01d94954110004031031001e02030a5005400300b59440c035100082c1041c04050b4801e241003400d0160a42e16868250401c2c502c009045d00340030b08011035400c01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 548308938 1250 548307688 548307691
    0x30408010e0601061b0f020904080702090906091b0d06050103030201060609090e0613060f05010b1806070215030402150c0601090f14010b0c070e3103020606040c030e100c0206 77
    0x81c002030805540343c0344000e03140840c0e0740d110312641d4441c42610014806040c2c03036480785640140c010707201898140b401100d59805120124409c1c51004c4c00b294400c240003404078803d0b2071180c001c241c0c1c404612850f0b82e412088241450384000c580303403a0000104140103860080d031082c1c0020803644e00742007020385095019041036800a18002428420800001e9031319003017222850725000360740c0d590a0680140401e00740d2000940c4c240000050b500f0b11034001032584000c1618580004240b58080080c41d21820382c020798000204000d00c0380c0199101e00954110384010610f84d00010040c80c580015003141c80c004d091500090f004002c0c40d41d2900a0f41d9178a2902e000030400c5022100b90b1401d140b8040c00354014201c408582800c8002c000c00080010703082c0100040540e1030102c9030449030396112031001501e4020741c104c0782c103854110b140d010032066168018000c296102c40500c0014030b041e02c0c580003015202c0f200442800d10521419454016238840420324010400b80603240050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 548310188 1250 548308938 548308961
    0x3170c070812042109060509010e1c0b0703060e010504020a260f06060304050d03050604020904090b0a060503032b180524100513110a050d0501060f05030c030a0e0f03040801 76
    0x4803584c414007981d501c0102002035038018200242c640c1007000048903010700e940f0189070130072a4070078062141d9030b8521400c1030640c8108080001e540e1020400c50a540c85031082d030003010703200001880079240c190050400c4013114030f424540300b03003610884084a142200a000080e40590502010003410800ca690205064031072034a5070905980d210b070f590395000f2101080540d2200070540030756458044440100f00100b080c40310710100c2c1030146001405072490300d00285041740011b80340c103012059400260005d8204865001c0040d428110400e00c2505141c10950b580300c6104484040caa40a401e0390040000f002108001c1c0400020040740ca82042050142c040400103010032004900301078035070030b480c02d51200034500000805400d003d45c810103188408580c2027900d0394030a0190a60b049410824007959aa554007500d4001c81038038800c0015208000240c02c03040000020f40e0060340a0340001070780e17607203112260704000403945494900d80000404004a503024050410303481e6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 548311438 1250 548310188 548310233
    0x6030607080424050c0a081e04030f0513060e01080f0108071e0807060c120c020303070206090d0203150603070501031b030c140c010204030b0705030403170c07081204 73
    0x104403034090603051000704000d0090512001c2d1a42e520f10b450781d65165140c040348144401c0c01c18003403410450f0841d02c0400c002841c0f400004410f14100010f401c01d07031005802c44262a00d40c4d4a0444180441c0400034051002c1040390360b215a007070348007030002000540d4500000030bc190700010400003015041d048a62a500c006010001010880e041180c62389540111001a5075451010310540742e480705c0c43d1802215130000b4081c2c2c10091501c07109120311108405240300ea6001d6601e1030395500041d415a00c24030282c00182400b42c01405018001003100c0b49140e06e03940042c4c6020b40b04410124000c000c4414021142000c02451024100c2400c0920502c0300301c04003010b183e40c5405444c000c1603110050301c0d80d41c0b4020715448000000d84c0c40c000d56242e800d00e07080f80c041d43c01440101e031150101400a550103200c1c90681c0d0140758196600c0304c1c01e480b000350760011000080d001d4501d15404003c90030004540e2002451451a1404c4240c4a03203407905100340c12005448842095a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 548312688 1250 548311438 548311441
    0x40306060b0306150a1704060e060108060702070501050d1e0b132d180c060906080126190b0f0105150307030906140103150f020a050a0c06020f12010806060306 70
    0x40d550704c1585281009903070000c580301c03803000d40100d4602242006c112681d251078000d101c20310020382c0000009101040072110287da0f00c82c8940c0d662030701242c1ca5001030f0401c000074046584103200500d48041e4806002c01d1207900c18542500a04c2d41050340e40150340e1700e0300192000d0800030031601b000c1041c0304003001800111042c80c00078010301c00c2c41d481c18548c621107644e100e4540b0781c0510340701c010984010b49005410300d0450403602d01d07070083c5000b00b0801000003820501c10316095050b41c400c8441e07003012581007451694840c0702000f01707200502680d070b84506031400902102c14520b0088022890609002c000d4981c03c01040c0c00c0bc90289480c4c2e90716400d030074845c508481d0001a58a00013032200014100304006004a60b003030501240c1540000042c810600000c0f41c000100c0d01c0c0820600000000d80010ae1003007140c80004180c080c0710200445014118040045020700e01c094507000f22490b50b1043ca51010164034001d00840c001403000ca04200880ba50124080d03000f070906 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 548313938 1250 548312688 548312701
    0x6060d1a03010c0518040b150412050f0303060a0b03070903200a050a15080405100903030504060f05010810021e040303230405060d020c0f010e070510080f1b041a040306060b03 77
    0x200b107000c00c8821b025946890340d0f0310494561620301214003034512074240e100e9484556005d880c2c4038034041a10a07103e03490307501c0c0d000c90b4040300720b90003500000c00e940c4007075181a0351120290001066070061003071410000012030740c0e81140c0001c5541c03040c1c001e002909a1070400400c0f4405400060250040000500c1018894800d4032020800c90900050319a501d1038580d151000b0100c00301c0d03205003400040d0b400c05400d90802805a48107580600c1519034503003000b0103c034404d114114060348a002c0400c0124455801421640b510901c3e003652180e038149151010380c0554130443c00544031006603e00c003a25140e480e140c0ca03080c009038903c0c0501e0000000d0047c05455481c018181e400a80c0e060245030420000082d00706800c0240075803400c0004240e2103920368400c040c0601c21049180d40307540c3c46030261500c40c0310102c5103590340351641420102a10103107070651803007107002c000108074910300b0080e84244101850089a070b0f80d096203481380954015134030440c01e0308414003e000300c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 548315188 1250 548313938 548313967
    0x61a0712030b061e13170616020307050604080a02010e1f0c03020409050a14010801111606112d030408071502040f0f08060f04020a0e06060d1a03010c05 67
    0xd8520a80c9000710300c00c0300c041c0005015101d28034440c504005807810604000301c2c440c0c054800d0000d40c07640c0c51403441e5030b0545c480710603801c820b921001d900400c0c0050004a04101e0740c0d0f1008221340304481c1001c3c416920f81e4074001d8113503410307682c1c1040454000c4030710f0340c2401810304100c1120050b00c00071601c040b820f65003014803816403003141d450328111a100f6200c0d03819640101202c0b1410700c1541481e00300712000302400e10301c00ca18021924004200514140604203146840024291400c010701502d40080d41d94040d0881e10075844203601c1d24040c40a0000d440c180003043c43c4515002d2001042c3c041c0031022000c0340710350042c2407040002140c46c41d000d8950031600842c201e000b01c0703440e002c01030081c400e540048000000c14007003c44d0f848165190710050384c3c808011149a0303101e00c03485011008003104c00035440f040c80394080c80f01c5002e03106c000344c0182000d80410305200c420001d80c42501d04100c0c001d1000011780907041c0c41442c0c24001c544002c922401c1042c03501c0180a07540e039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 548316438 1250 548315188 548315213
    0x3021e1c05010f0203070e0a060815010309021306080f1b0f211e0c0618060a0c060903122f1b031207080f010b090108040f0203060901061a07 62
    0x14502030400d100c40c02403150a400101c0d501021001c11541c0e0f107442c16003d09014105041c0c5802040092408104c85014820285c020400c040c68040809502070044001c0e006854040381c10400481013005c2034070f00740c0540009011410064213100110003106450b00c001050348440c400541525a1070544841c0c0039644e042e00192205102441e42c0a0000e00343c0c40140c04275115489031842c0c1c50b0701000c039000000b51421455003555001c04800040029602418200c10341cac0003012400c0b00140d140035002401107a4050030091900102034507480c088a000842c1600401c001040c04245900103114200945c21084482c1c100600c80144046a200b103008407100404000680008203070424540e00e40710220a000326030740e641c0750601454041009441c1c0f040030500c284089074004841d00c41c81d40c1603800b0b000c44a400c00f207010004458028010f401540c0b00310455094070056103040c05420300c5104888000700c1c00900d03015200408402045a42030307800c00c184a9034000594401001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 548317688 1250 548316438 548316469
    0x6080c07020a05040e1e03041a031014011101020708042c0a0c1407080c01050609011217210f06100905041112040b0a060b07050d2001090302060103021e 67
    0x3040f404c0385403c1c5140c4103451141c070100368081b0710742c90f906c008000300400a682680b0100e0070221700001612075140030035282e120200c0342c00c1e0b41c00e1121203002c0003414920301c0f05140640e88840802220340c08c82e80161420303100413800180601007917842c042c80005070f244540b4261400e104ca1040a000d8000203460803400e69115403289120302d2044200d490020b000c2e5100740c0c0e942c040d91520b50b1480d8019207065400c2c4d401c01d0002903180c500744851904803244082c0b07400324052035999042c5045401c079000d1f41b0310b580a00c103052060b6103465071107080380d4500282c40c4460820201e01c1c849181c0c020b1183e0302c601d190707624842a542d8000ea00b0f01c119141682d02080d14200d00341c01144500502d13001084108078042081b050052031a00d003406000402d4041101c142c5032500c14000c0c0c0b0400c84058642d0303000d102a200c0542c810b545000014400034001000c0b43c001d145a03509444480340281c00523403110005006500d000400c501030201143c0c03541c108a038015002c02c040c018101c008 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 548318938 1250 548317688 548317691
    0x10c110409050c06040b030a1d0703060e01060902160507271a06190315030807080c070f060207032a030b1f090c0f020a030504090b030c041506080c07020a0504 70
    0xd80d010040708020003c0c00d2a401409a0703190b54551000d444550070880b101c4860508040022070002e42000b421500c2444a00182400034111340320710014100044490301c00d0f40d60303060005014420341c80545402c1d1100703903a24210a42d2402c00510b000595044138542a0b40ba11407109041c4140c1c400010360340a05201149103026081039120001850f0815500100001100c90740c48a20003d1020582d107507840800c01d9040043c20030701078000341c2c0001000c0c440c04000003008100b03810081c0024203090780c200d0302683d80356181a0180d40c1c2ca44d01138005603100e14418020042007015040d69180300008028803140080c441c50b031080d01c50b2001416100504004c2100c5600001e500d0781030000004091000c1c5a99050031001000341d950072800159200008104261010480320460340d050381d9040c0c1800d041140030300c000e0240c0059554544500380c0040c8140d1500e00508a14000c1550084055271170130002070003075000103110b00a07a00c4200a0240183e5881c03840c0d5056071402e480 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 548320188 1250 548318938 548318951
    0x30d0f02190c0c0906030f08090d020307030c0f05150f0a0912081309020702090601260f1f06020a0b04110409110103110a021513120e0a05010c1104 65
    0x6020000d22421200003a1482a040075094031500040320b019030714803940d5025034240d40c66401c1000c0712800d0200a00c406041d0090401050100380034114000c0000e002d0014001c0780c0e40020314110465000b262224a0311104008084110079168000e0400341d034115202805c0c24884c4110744203c03030700e4604410f408900030484902c11034071800640005522492244030758182540c290b04000030780000020b00303840114490015009aa000c0d07540940400004d0b01d030000155002480e048103813443c2d00714018203540290340d644c030080c02000207900014440c14541c224519050900b0a40e41e40c5503e100380c1002402c1d4002041a401600001204070302d0322286030810440354484603040d4445d09000045050200c040d4802c00110401d80b81000400c112403a01000d41c040c00c810900540c01c40f25001803d0382e07004480c9580729400d00d44031742040c1c41543c2c4011040c080c00707a00d0800500720300050091802c0c80e06004c0084c150074201850094160b96030b48240310720b00000030380510b40740c80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 548321438 1250 548320188 548320211
    0x4020607030201062115091e14031303060b06090918210c01060f120807060b030106030b19050c0d020a09241b0b13050705040c0f110f030d 61
    0x14000c00161048401050001e0b240c040211503100c0b802c0000d41b58040341c20070b15001603040b071041603043d07035000c100c0815030032140d0311a01c404200d20005642c0001d103900c11504154050008281c0d0003c01d4640c41c0500c0e06604240084802040d0b41c5805403008103d07144107550f40d4910154000029401807001d00000c9080d9820000c2d105c050548441d00e60700766040c01103001015040342d416420003006050790b1804802c01100103031003009030004611400c0d0300420a0900105200740c0110004509014600d0101c0e0841d041c40d0300656030103d00f02c05020403080100000100030311424800d005a0500454620403803013500c7d40003075415400150944401c2c05407240c07000824034186422912119013500d6040c3d00e03601046400003c2440c104841d90031482040c10310455002004104955a184200100010b00500980742c51040c08e000107016a1180104098007446540e6001d0303209500101505070030005a0b201c10076040b0780760200c5803020001c1078a0b144102520701042800460b03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 548322688 1250 548321438 548321441
    0x140105090309120708070e0106030c0201050c0a110c0a090903080c13121b0f0f0603020705031e04090f061502031216090b040902070512120c03041e0f0606080d0804020607030201 78
    0xd45c04032210307000b010700008010a2400f1164101c6120761818400140604070480c222001203800e03400c44807003800301401c041c0c442d15400200001c1f040c11111a482007200080d0002c00a521003060b05881d00f10600c20940e10054080c0c00a1610007980d042c003070a088003803490016401a400072815400900043c80a2034902d540d034140380d04080003200e40c6031020340088100764082c41f2420050000d0001e4050f1080c402c540c5515040000f03036051101241c15035035180b1080e061001149401e2000cc42c0c1c01c02c203445810074506c01070700d001805d2454a055070321403181c081c5034501550401d22100e0828440c03a40c0c0640d0008641520719098a100c103000d544100c42504510810300000c1008111484036034010600c4501071000c440704c9000c2e0107004030b81403242d840900b4180c00e80b0004a8500d8503104051a00544a002e0740d668051020411a0702c01d50500c0f0252000111061004244003e510620000d05a04000307840c600c0c8074008044c10550002c4c0009024080c0001c1e05014181700303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 548323938 1250 548322688 548322703
    0x5090402030621010603020418031202281106010e0408070f0219080601080c09011a0304050c06070312050f151216060c0605070509010c021011030a0c14010509030912 73
    0x40c5035154a183c2c058046180c000c3c02c139400201e020b28a0503120041c05070074108028140741d415501c038502668103001190180d0499662201000358198039440c8015030080c0081c109410390b070f501032200407400085440c00d4410303403103042115001e00500c004a03603941c04540516410201990240c0a03a2021500203001d040208038607a111050100e50100c1c0031404a040310b8a0301d0442b40b452001104002c0000c000b03100d0764941d0f11045444036866803442c40519405401481030742c482c0b50005001c60155400f0342000c41c00282990400c07006400a1b11441d03401c10141d418640c124907003101e040d1100400509058810b1005280c1500200d10030803410001d1100c003090440e845649110162108140c5401120884e041c800001ca80700c3c0705605a50920760146d40d035070607240f60b6409018204078001d83c4c003001c104000780381004074a010801002c1464003a9140c1c036800155080510603680c4202c4111566414003003406035550300001601c43c2c0b407108480c11034003056140002d900e40903c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 548325188 1250 548323938 548323969
    0x11b050703081303061406030c120c0a0b0a0201050901090c1a0f0a05190516080a110706020c01020c0402040f0b0f040801091226310c1e06050904020306 67
    0x1000801410b0310b43d08940000490344241028419885501801c8040d1101210310301d4040d132080c1e00982a9141040100031800300002c02c0d04c025501079008030f01c2281039a000340784a200c0c005040d10805509103e030560090314400200104540780d600d840c405c004500ca0b4241629814114451903441c41048505850540c25a995190134072800603107a50803001c41c01c44101c5007050310b4881c144c000c2d802c82c0c0007031400c044d07020900800d565402c10590002008030040180d241d50b161124207042046c070001c0d10081e0003e003454000b12000a15049040641c140030703500502081192550121140040d1246403582986072900b4509140543c00b85500a82e0b840d824900c1e1082440405840503c04004a9032070382c4440c80d8408502400070b03543c2e241e00400c0c140f400009141c01c00da81896030101101100406800c0d0307842400d5500400c1c152406035106015200204443e4000c40c003000400c240744140b4000162130500080c2a5000e1183c105010b1a0000001181d0343c0d41c1113140c0a0451 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 548326438 1250 548325188 548325203
    0x61e12120a110a170f220f12080301180b03030a02060412030204140f04090804090902090a0b0303031501021e030d15050d120e0409030305100b090310090f0b0c070308010f05011b050703 81
    0x2040e1b0000401208428840c040c2404c0c00007101244540c1000449581c1d2034101c08170f107266900c1c2070140c01268010070790f00e0102036500e522503201554240010440810254024041420070741002c1035209481810700c028548108010409066070b00d6486d441d54000b1200000341a1550002c20041e10a524008003058400580403450a402d6031240305058000d07101c23210140d603140060300842e4040d0004a916034400d0000481c6001c012000141d190810b2040d50514185c59520301f840c002c0c00140b0a03c6c0785c02c04200c04002c1b850707a00c80d40344480322100000104034030b003201290300518800d002030310120951000090705401600003040380e04000e0000c00c0720035240e04008005000555035017100b1030000030001061220b5100350751500700d004010707006408802d10b4080084c0f0b4103017012940c1c61080715503400030410000b0405d01ca00740d910a810f1341e9500500e0002c0200505170800303200c84414001c18041642d000c0641e500850904064483e0f241040c200325150410300e500041241 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 548327688 1250 548326438 548326477
    0xa050a05030c0c030a0b040803060a030206030106031d03120103331a03010509030405040b042007120c0b0117030c0f070f0e061e12120a110a170f 64
    0x8580000201982440b80c420341c1c0b05003c1d0f10701015182d003250070380600300208070300c0843e022441d020000c582140005280c400c0b0640c0c0c84c0e010640380d80090b402000480c3c0e03280c80c00d44a5440c03143c0140b0728032071010059494824451601c240c00d030410700000e004034a0070f011280a5540f142200c8054160201500004c49081001c40c000b50405144403e00c61030494000201410140102c500171451000514102030600007408010401c0c4c4880541c400d80703c544141401003010580c0b502503107800001c41d03a803007407400c250116160720420041080500441c40010840e21440e99055550360902058440b004a1401d0700e1402180b001d10001d0007495403000c1d0349100051048201c0310040c0b601c2e8400c640e6a201610010411a8184e4000010401c50483c06000c001059410b0300e0040c4480d54040303284454602d8000d50083c000c290f20302c00141340c65050707008210440003211100c005d040554142d81e44410f60200b20160340b00c1c8000c0400c2c80c4203d41700c20420b40389a1280d0b51a502c00b0f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 548328938 1250 548327688 548327693
    0x70902070b0f13141f14160c08040f1706041203050403090503010515010801080c06070213110f040807151706040b03030a020a0b0901020f1c0b04062601150e06030a050a 74
    0x180c0c108142c01e000305c0703901c0c2d240780790030f00300c0e6801095030300e000312071000d21103581d140e0700c26000240182d003003420480d2a15500d0300140c50040503001818011448130400c0c0d040480080c080700f00c5a000300495031000007044000f0781c0c01000e400c5480c1040c0360200b95034645103000c2e100c0002540150303034154200010030074003502900f6800c1e94884240d0325203450ba40d0355049180c0301c611015200ba040402080b0071000360034100d40700440495038076000184003c1c1035580101301e4000f0008101c948000090410aa003000c01c0842c0c09405904880c15031b1413a28400a01003080c00c1c0d80d100400d560700b074006002590f880c0c0c0280c40c040c4018003030301d585200e60800203494800c2101c08036400c00c800000b2a44000052094945c080840c441103840c05945a0b03440380994000c8445981103512900003100680703490140100030000078030803010303280c580c003405400901030701006407450b072500740c25030080e204041e404003c44840c1500102e458484a01290811010340c3c0e01900307500c1034141c0c5004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 548330188 1250 548328938 548328943
    0x311040806040b0703020a090e191b02010b030111040e0405122a0c0102031b10021603110d0e0d05070515030708010b120103030f0c1a09070902070b0f1314 68
    0x8940e1141c180f1105950701c003038042c0c08078000e520352540000c4002401b40004480d21428581001890901d100c00414455100056458041a04401c0c00042000304100794090084040f01c0c40104e000344858810316960401602981c03061135074802000010805022091042110402c1c0c90598259284840d4100446082c045110f451491262a00d82e90001c400890210300004050340030703501c0d001441101070b03440d00c211051010140900c00d94016500424401040080801c200c400b844500324100540001501c012101c92500500d0300c607403031550f02150750320301410111070381d40030000c25003010ac0c903140c0141c03c80340d005103000300b1001e1011250000b56228126942e5040c0311a07886456100d0f032802007222881940045000600c006030150745441c0144c6034620340b2455102c61516296003400d003e0000500f0f000c0203605011a08100340f10b10000b50a19150035840c1c806195280e44500c5c034018040c64148005c000407422060b103039801e40904a030000c030078454894001b41c01c42d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 548331438 1250 548330188 548330191
    0x10804210f090f0e01030b31021008130311030904060308090f010203070305070206032e0806010501030b0303120703061a030105040b0409031e0216080105010807061701150311040806 80
    0x70100c2c01c01d00c40043ea01800072440710940302d040050000d5a40385540d0103000c524043c14060303254000030490890040385c3d9820800030091151841c068043c02e005200600e840030740304204000b420000c10200c1c151100c14154243c3c1c1c1031401800409212440c142180564050b2662140c05c0c42c900109002c403990103880c0c1002c1c00c03142000480480ca005980e68400c0d000000c011803006d114180143c070f400c4001e1948841c0c0b8000007072010903504a249413000382d85580da458035003640403e00c45900c040011070701414003030808011403056040080d5490003140321001404046000141c1c4a0344260007800c0180008108a948039100800c542001c1c4c00034010349000b246400003040040c40c0501608104a40585601d107010310a33072030304400b4001351441007007944200c00140048072114604100100340b2600001850b504240d40b02e802c0010307980c40441082031200000b405601040d90007411510100e0302c0c451040050032043d4041d04418601961280000c140040ca038400400c055 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 548332688 1250 548331438 548331467
    0x20a0903020a0902090315041b08030a090503010c230405060304121e080f070c02130e06011a120a1e020706052401030e0f06090d02121801080421 64
    0x2c0d52035600d6038121012801105441c40d403583c040070500b02c25040e40c281c0280c00502500c10811012aa10148403001740035074440036460f4000190628140d5000140d10040c0c24218001d204150101c03200800038090704001c1c4019444070302c1c105041c01911406c0301c000b010040c2180d501c0345007604118075504240c41d0601b010450311252403001454512440e10084010b464010b42074903604031260380c1010040422003409144581000942c0c3c80900c803442d210401c550103d00b603c2e0307001c03a0b1424180d0691224a0350041545c0c142424034110080e0b0300580c0740b4190210b500e5460386517200183c522541a40f038000d01045220a0030303513103a0001d02405028003000d0011703403103030380c20000c042200303100151441640803401c8045601c81d07041803410b00b6401c012604104809207241e0305051013901c4404490344810220010550184001c40d03c2c1c0c0994408c950a0072904d0580503410030090311100d040051185c00101044030f07002107170400c8000064030804080d2050400303042c541d02c48041c1d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 548333938 1250 548332688 548332699
    0x1f0f09240f05040605070f02010201140c03100e040203030304301d1e060a0207030b090f0c180406270c060801050303040311060a05041508070f0c0308060f040f020a090302 75
    0x1039260340030742c04a07030890768656552031821400c0c3c1c862150200f61100f00724119500d4824945000840082203802004c841108039076a00b4807021403040452603034045a01c41c080354080202580d408001d99030b2050f00034040c2034071624400305100c130702d2014902c0048084007054000c40c5042e070040600c0807503d54000c1d02803034100c2003010810030580c110b00341450070904e0070300030050b4100240a041c1032074050045030a42a10380c0d0380d120100004071544807007680054000b0300c030361904101102c102070b410b6604100004050003c049040300c01080503000360b445841c5010071400010381001c4160811040c440310103000e140ac0f025a06d00b512810001604003030011445250100c00c580031298080c1040d00200d5142040c0a815002080640f05214007800006080210a8204888001c061351003102d80c0c90441c0c0d010b4403095007810700c2001c2011b0000034070000303a00070452903081001110700410904030000010054000c0001c220080d078000f258070900303541c0020211060324400c640 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 548335188 1250 548333938 548333957
    0x70303050c07091b030e10090501020d060e0c0d111207020105040201030e0f1b040906060f06090f050d110409154d04050904031d1f0f0924 61
    0xd4007800c0c2c52107100c1c1c1e884100a903100c84010300c0d0286d40010081d00e0302c0c006595104845c90f44090858041c014107883e1030b500022480c009012910406024050a0400b00034038101641c1c4d1503164010303c1c115000d5140d90b130008060a00c41d0b5400d80ba20f1070541c0170006075900e0000d000034040e10045da0201d01083c104440c02642d00004250402000d0b12070000709100f600c4c07030071340030044901286902d42080d542c55007003011502e80e0040201070f00701018200c0b5100e181c000d00030120102a403005410f9141a00140301e9581c48040300103000742c00821040c00d03280541f00040081480c0e42000309102400c081c03401642055400c00d00e80e440041004582c0c07025052005040c00300b40c544100d24609c4406881b00300000220141880032201c0b040160900b0b0320307000401e1b02103c041e981500803c84081c2d103031807040303406000302210304400d8852007203900e0035140060791051003140d80c01c1442503011201007070318401c6400000502e091124040190b50105000f03680c20008400078000034210003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 548336438 1250 548335188 548335199
    0x6010b1b06090c0f0f1003020301031203020c030702010518040504110112050c0d052d060901090b0f01031d0a06050915040f03050f0c010e0d0f09030b01121103070303050c07 76
    0x10036501c2045102c000c0c3c45079845803810010112a07030103e4561207200303040b44101a458886e2140e000341d14036100140c0e2075065040512601094441c91002c040c01003040c01c6400e500407060350343c0c1c6d41d070a003041a1204001c1095800724880c1c45000c9400914100c10071080c003400004e10f1520340400c8c0c0301d50041032400c1004009640c000c45100e024080700300507800600d080b580c00117070711120400d600904801801200c092008141c4210038045440c1c10900c400c600d131400000c0e004100e105410491261100701045070281e2007241e50b818107a40c1c2a10400c0c04081030004c004400d9541305940c04070000b4034215006007015120809a440740c40c9081c209104070f220498060f0382c0050b94010400941e650480c0c03141c1c0121110805a00c050050026504090080e440d0941f01c940107018040c1c0d940d4402011603c0c0c948500080001502082001c55241101141940e169292968503000d0500301703900010210004c542c2c15204400001003451380c040f014101c0800c0d000240c600940e601c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 548337688 1250 548336438 548336443
    0x1b160f05011403010b0307031407022b02060708100909081c090b0406050c070f200306010b0d020310030c030c090f06050f0f0a03020a0f031a070507120203070506010b1b 74
    0x6009038040880b041005203d401c64134009103501c6401c625011802641659500360000300c1920394402580c003200e01c009422401d000104d1020b4a00301d5044054051883c0007075880502800036000d00c0707a80f1020401485440148001070000a0b80600c8090f82a140031046070344001503805203a804c0403240381c14081c1c0780c01030107038058100b91044280c1c1c40b1611f45400503c00a08541e1001c2e40402c0355100045902840f08102802861003045040d4201d01040c8082c007070015061198010340018410440d007081030f245602d120080050b100d56800c510840000c01580001c0e101031100d4000004004c500200c02082d55010f1409001060043e04d40400b61011030007480e601880c1e941c40c0c1d2143c0e0a01d00e501e204580b40c002d0501050950325008641e010049410520035800015814014400060400c0b040f044e251980d5400354600207200500a0250758401440f28040640200d92184204143c40110342c101090b650103503941e4000d10340340d40c8100d100b809100242402092100d402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 548338938 1250 548337688 548337707
    0x15060507061505100f030b0d0f02030c0d0b0a0e070b12090f0d08040f1a040c090b0d051e12030f01090605030c0a050603090709050a050609130510021b160f0501 70
    0x2070071021013101510016688613402050602c2055030b91840c203043c0340d8800c010a11541c0c020405070a010146006060420305000840b60286c03034100500c500007100f032000140e2082c8140400240100038040c041d082068661110300100d202058801c2004070850080d400f54914200b111680e01c0b401d000c06880b280c4003039820001c58180000200070070f00c0c00025981c06442146c0912a0302400c41000107401401e64090355075200400b801c1c480e0090510603884c1350344007180d0301ea0035000380d6650155155402c800820f0404031254009002103010851b21107102072550b04240c480c0740420050011050900c590b03000709040c4800081c4908010030090005c80c0003514103142d07039080c501805840d920280031482c080c8212200020b82c9801445624040c002c04d090118481c1451400c0212085007c2c196032111803000b450a800254001555180480d440d02c0240c2c40c2e00359103204038010158481d014502d800341964001c94070a0514100080e200380401018040e0386580044507807000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 548340188 1250 548338938 548338949
    0x4051b031f0b0409080a0c0b0705090303030621060a1a0a081c020309030a050a060605060f07060903090510021501140f0402070602070203010612140a1a060103150605070615 76
    0xc0008545454009500242d07000440900045401c50141d0f803415802da020455410010344441c50000400040502342038000103145841802c0190b03e40003c0d03101d10014202d9841444181c0d07800f42d0320000341d005558006840015150035150a48941d005890002c1d11141c803000b001050210510389841a0030990f00782c000100000c156203502c000444404080030415807100340010209130358100401c0440074480c202900c400301032445c10700e003604e9158004500c2284c080c408508034403d40016282c140742c205501041081d014101034a000d4a141c1000d034000e914418000070081d000100c501062021a001454680c0e8403421032030346040300c120280c0e00804a0304550000d160a4001d418030a004440051401059600180c210f4003241d2080d44030007001001601030004000d03504030107021141c090940c070b1140e40d40341c1d40140c50b00307942c280189030010080349032640b04e507000146d035200400740f08540300c0d220030010307006030445101150f80c0c81c00c016002c001e501048003400c04551 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 548341438 1250 548340188 548340223
    0x5030c0706031103010e0405150a0e0c100806010516201002070522110a02061e0f06090a020d09140d260910060b041a03060d0602090402090904051b03 66
    0x242050341806d120003014000b599140700e0341241c00352080c00000701600034000c0310300000340041249185420625100c4045108041f41100d82012030b41014000b5404203091800990b1030041008880740c0b0b03240c46c0400b0304804440388400740d404a40d68440240c2c020700701c8594207884000d10b0101c0e59039000e40078283e000602c4489041241d803882d0072003000f07442110804500c40710003504103c2150040740107040140c4c0a50140240640b0351500059040100c1d843d602c41c51414107964880d201029012900a8081b000050312120f441d90660f1001850b442092090b0341c000d080c180508a41d905042e48a4090084a001d00c3c034000c0c40160400425901c100742020038000e6041d8020034014100c036443c0c02103c0c1ca0b02c44150440c401c0c03c000d030000e64002501c0b10300b000403401d40021305152541110808009211150780c44c0140701913002e81c001000350380e41207147d01150280c02400d82090b0000e040000740030402c00c000c50004001401c1108650622040b0400c01da81d401c01890080040d9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 548342688 1250 548341438 548341441
    0x12050411010302030601050c010e010507110607080f040303021b15010b04060c1b080d17010f06270f030c0810021c02070f080c011407050c0d1b06020705030c0706031103 74
    0x75402500030f142d01c120141041c50801c251421000c1c01e5829880303010605035911000c110394030341c00c03007181c10804640711300425980c0b401c034102400030304015112400c03c000c114002001c2603c02e40450340612140380400307140290b00000b0355a10201908c2409840d03107d00000320314003400c0b0f400d89040766503035650300b8500203c13074840113004c1800e6111140d40041c0c80d200802c41500c10030080c803101d1850341d2a04410034058940740580b25043e08130041704503040c0c9042100544c0301c41d1104409028140da0f103500002d41032480f070700490300c0d401341d44982040d101c00014400c0c1c415100e42220400741c00d03079902c0b602208440303049100e580b10281d901141910303c5038106800c0d0b809445050b1080c00900340c1e07503826841d050f90700c0d081110840c88580d1601d1091000c00c48800405400200d00d05009050019a120413500d80d085410800204405e0915a80848650318240c0f100d6603007100c000c540d0342c406070030030039280c4c1c0c0004260340380c5110318100060b50911034400c211190660b1203015003035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 548343938 1250 548342688 548342723
    0x81b0606041d1f0207141c03090b0c0a020a1203090302120a05040303080c040e0a0207050d030605101809060323030f030a0b030a050d02060604200d020c0f030d0b01120504 75
    0x24041401c40303d01626400d0000d4000204000600096141c0c240024140c0c580101070088000320844032180030107042c840b803000000c0d43c2e06100c1c1c0d00850900c0c000c03070321139103030074412071030580c03a001d000d0300f158204000700003029003603448041524025829204140801048500c05100b03200f07210740000d401b0072007080881c3c45803c00a41100e81400464641035070b40854000520055589810032a070000d480c401308007081000c2c0c1ea04e420786007814070201e0300d00800500312146140300b075020f02a030642030203941414075040030040c01c2050800c010307443c1c03a4100881900300c24815980d02c07541811045030602400003d40d081c440c144410b5500d540d07215030a1401074100307035540075010b11840e50ba00c00055800c0c000c660100410342d0091807185003000422056a02d0307140250b001856541a00e180c00b101c940c01c0b29410140410f02680e81c812001840d45841c11081c4060414040400d20104041c0141c02070302e128078099940a00340d000c1c4001250880b401910014091250034502c800c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 548345188 1250 548343938 548343973
    0x1b1502090303070c0803090108090607090312180b0d230712060308030f0603011b0203070f14030703031a040231120501050105040f0207050304060804081b0606041d 72
    0x380e0403009000e80c2c0c2003407800e42d03c9240c0d0388040c0d00300c4841c0c0c1d00007062150540d640402c1c2c4661000030742c8001c1140d03040003071000d0190056804064501039082002d860814061040780440e10303034045004260a5880c44900640d81082d2b4a00c0086810a030320001c10181000740c0d18442c0fa0088804100d5480b5190107503403826030840503031020b0341c0f00c40c00000850003040203544281e0742e11420403020b151900405003181c002000d00900303000385009a0031a140e000040e00c1e549a40491445030040305414141a500c8800012400c1884002900c0c0d040690640041a4107042156095030301c68091003040b060340a41020060850114022801400340e4042c0c1032248511038861043ca540d2a4041c2005000102c28252200d0791900010403490410744103001c500407145c0c400718281a07c0d0303a181e980300d2141c0d1260b5010011100d010800b841469801c41d410070107038011200700a5800f4101d192a40f4040368007501c0343d0b152490400702201c85100594016400301e01030403840680c00e4104a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 548346438 1250 548345188 548345197
    0x60f0f06030d0507021f030209030f030406090e041403210f010315021c020d0c17010b090d05030c011401090b0306070519020a0606080309150c03030103020f0f1f1b1502 74
    0x1e80c060061900201c0200e40540c40c4455006c0c06d0b640940d82d400d41c0800d151515142c119080c0b020390007000b00304192a0f00019400590388500e8641c00c4d9500ca50a03c801002c602d0344200b0a140000034447c030305006034000e003502c140c403030541c1c148140d136540c1182510120240300c082c3c02d80c200701c3c0d84072040d440310b60b0061044024a1500d0040750fa40420070b40100e8001c0007402c0111640d540314805e41c0b9400c0a07120b0482001c0801402e900e60400c1c0c1024014000c6010050040007021111b070200304003441500d200c010524020442a417504104408010007807140820092800340031100c0e40c00c1c00710b80e01c0d10450f519152140303008900d0030780614075007500c407a040460094407541400a942409400000c00080c80110b85074907008040049001c045a280185c4080400c54600c04040100c00c0d281100e40403600c1080b00820900862101c402001f9030365800b901075040806c84507000a03884001074015510640708011001e1089070340444420040c00b90301c0400205c548522440c1c0081 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 548347688 1250 548346438 548346443
    0x2070c090c1b080c010504080340080d050c071a04120513030b090a03020105070903050a020f0409060f0c111203040b070e0307061d0109150807030b0a08060f0f06030d0507 75
    0x39103844c1c2841c2486084860548084032101000400e0020b03940079208900410301d4100048025041600344010b440c2c450100d441004c004002b0340c2ca4144404a01a6041c0040141051200d40b521010341006580715180880740b082e241940070fa84000c82c0d074503440c0f16503844101341c50081403441c82130b14290480e8000d0701c0d624180c4480440016404a003e90043c1e500380020b2040030581d10700030342500c10060041c82040400202000890000111104600c0d0140c4044102c0891040403501030b001c0900c2c081c000c0b50804104040d0300217982e01501045001c4e50b01c1f000c1e003860010400340c0380c2600d080545c52600040c0040350100b09481c0074260005010f051002c40001040d000c2403d000d51940f016010542c15400d183d20704490100c2e18072a841d0900e040c00680d4101020b20710700840d014a000c041041c0700c000640d51a010342c0c00281a0b600050100b400c65654800595a51070210707800c5900c112850040b840c400340002e8400c0c040e0f4401806440b040d098190101c52542050005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 548348938 1250 548347688 548347703
    0x1a0427050622050a03050a0530010e010605040905090705030d2d122f0d061707050112110301260a0302060a0b040209060d02070c090c1b 60
    0x500052a10016504200038400c0001d03004034a0500340300810b907118112940005500509440b00040c408a040c1d18071641c1810b003140c1391160b6032000c640a0203400f0300d24140c40022095201c80410141e801e0340c0d200003824006126a0b04c0391034a2440e50b20030320448000c031f01c062005100c520590b402081d400130580c0d089401441d0b44000184c9400c81f00b90350354011414007081112101c0b443c01907a407841c1106a90700b81401009070b0010100040c1c418401d480f0303551000e210540041c0903100302c1c00310075042d0460302c078404a07030321005060313006030003400582d031400c1800985103041c215440001ca080d0700103017400618100041d41d030800fa801800c501240d40314045001c058140010354081d0801d20580004841c0c4440001580f00c490490101d00d5404048100c0c0041e4cc0012000c0d40048507001c0803403202c00001c0420064020034616990003640883d0b403c00c18105540a44001e03401401304281095581c2502400c0b501c0000e00017000444a42d01440c0c8411451040341d06140318164 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 548350188 1250 548348938 548348981
    0x40e01140c0c0a0b0112050d11031c09050601090501300b0c040f08060a05010803070507050f01140c010b010228030e131e050a020a0e2808030903101a04 67
    0x4410090031401d030013180c1040f402065046c184002000070f08a21022420615a07510910446607502d019041c202101d80b1452600f107409000c507900090303540e640c040221038032561103200c3d10020381424000c0403c2044600421000800401c0703004200742d8070003188902c1da02407074840401442000700412103030302d030401001600c02d040b540ca8070010110740c0084e0000b42003640300402942c6042e44442541e82c0203100000106101041800444208030f8400c100301c2c41c4100140c1c0c581c10b8400c0840c01500010174110320a2406403c407800c0700409034240c4120012542031b000c8442c0300d00c20780182c906101d4144800090090103408040080200242003415000c400c0e0004d4880c81c1c07600c0203504c0040c4002d00c2171080c042c064260043e10120007503051a44034100200702c0c00108040d18460b80e009240010380c07220307001d01c2d0b0100382e13070075543d5614141e22800030581d00d82c415060b460281c814910b070421007030071621428803000c0c501c000442c0c00384807080c2004068003411040d180282007a60 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 548351438 1250 548350188 548350193
    0x50301090903031e091a07050327160305010b010906121109060403050a0b0604180807080708190f09230102010b090a0b010e0d05030712050d1a040e01140c0c0a 70
    0x981000f8440100400405d2000d86858a000340ea2004104108049914001d000740c6681207400d43e0703800013801071542009a1009100040d240709400c1c85580c034041d008031100c0d94507007942c0c2481030364080c1703000380b03e01c440d904011543c41c41144035080004114200c2d12030310700b0701500071020440050f00030310706010301f00c030000c1c0845d0300540c000c545a500102d0f84004000c0c2104d0107a51248085400b008407102019561000e001d4601c4024843d14001500108200620040d01e01c01500451000c1d1181012429001102d4150b0000c101090303c809071400694070400c03d0784140d4446e180d50440a030b914036000c3e0118003483c10201d0540d501c58442c5181d0f42c952a40c11071003440720301004582c0c003c4d0b060024180d41c62918005000d40700300a40d00d40803502c00030469007880c0e840310500d80d445000c0d0200321000d010742e21301c03401001d00306400740c45c005101e041ca5907040071088500304082c0160784806400c030750140840b405208100d2000600e80b4100102401034080100d058030081111036 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 548352688 1250 548351438 548351471
    0xf0507050a260105040305040b0906130308030105031b01020a03030b12010905071503110906070c030501020408060a0c050315090703110301092408060c090f120609190305030109090303 81
    0xa400c52214824090701c254000c004030300824500c07220b408000c21079811305841c020101e1040d406010000c540000d40855640c94081c12242000c84600a50074000d0b11381c50550155403081c42018408e116061300004840908000e190526034142c0040c42941156507055000d0b244040d00302d0b50111500b91002c4140c80280101000c56200b503002d01461410800408001c07a038000290f0105172400c040000302807212412203a00c05001c9401e43d8459040380740c00c08500001d50002001540041800541c4110018543e4008c102415052002c0350070204100e50b14001111000d0700d1034403640170fa40240c1805c82d80a900010b03507140c04200040d562546200d1076000780d1000740156510603400d20001643c1c50014420310550349200301b024907044c3c1d02603071500042e0100c0c00e83c13000003900612650350a81c41c0b001d141d4000d130003140c0080c078002200751174100441c2c501c6007038003c40e22050082010700403441e83c40356158407114216424808a03c004240700b1800f10103040e41d80c44544800341c00c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 548353938 1250 548352688 548352709
    0x12050405030d0f020d0216090e0f160303030b010804080304030f03020f071b08160b03060102070e040501051506190302071401060e04050f07060e040c140a09170303040f0f050705 78
    0x1a111103000740582c840c000e1170640f040480c0340454201e041518540d00c00c072042c02007203e100e80400315007105a0700001c2e0400e00146595001d511614a603c40301d03002c0400450106e0340603807410082c035030011005407010881110000e0540038200005400280030fa0400c41950744149401400c14007600000c00003544841000d4910a10540c2844c1074900d0360200380025040e0940a4400c0807101030351501c19651501a44411080210014440c3d0b4400c00c030000003803154500c150300a042c6070400a009040988074003a80000b042c1e150003072402c10304222880e50440c1c41c14804000700f4541c3c100c009400500007101c48004080360b0112110342409882d0140130b40c05a01d00031414039240c143d103040d0380c000b2000e20a41004800300312143d00940080712003002683c000c46c04201264044900c500116010726407040040313002100c0c260300103800c2007500c034030341201c0e40042a90142c6565038001140c0041c01c000801302d042c0d002400441d14000354030b1152086070442520342002980d684807 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 548355188 1250 548353938 548353963
    0xb04030c1e17010e01050a0b030622060f020306120d02030f07230c0111060f0609041a01140a0807140d0c0f12060c030509070608150d05010b0301110f071205040503 72
    0x464404d00080003800b841781603000602d0700d00030040e00c4c00601c046526800000e05480000da0000001a441c07013082125488180d84100104264288a000c46c00250000d8902a024841141c0e110014442c00603000303e04001c0313074000710b00306120740c1e184030819404040c0032191300075442d0040c61400460030250a00b00c15102c09400803400010006010040f40e5100c0990350f40448280f29481040035072054120f6400d0b14070301065500e1b400d0416280456414014096680900001c0c0d0000401000c0c03100da08105c8035008815626441c02d07680d0381c0e442c011071280c16462068903041c0e00e0081c4a20b0a543c1c400d050b101a5503030b94011810800c41e15501c9000400c03426140c040c1045204d102d00005503c00d801e08215500300040243d5441c0040e00510742800560300c01b180d1004070740302c29070200090040c00841c24020500c1c1082c042c1c58280001d901030b6003841300a20403040c0c0b02c401d584c1038400d8610701e50f040110b0303901e0303403003805c584030080400b42b0204210106054406008c290311060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 548356438 1250 548355188 548355191
    0x12020a08040305060406050c030f0c0702010e09071d0607050601090f11030103050106050118260115120b07030e030d0b010504090513050d0905011209020307150807090b04030c1e1701 80
    0xb0b0542006016101c00234160795107001c0410030058000d120550142c3c02070107107044940c0b602614070040c1c890500c0c590b50658000d00c68001c1001107a4030880454505034070746452100c5801d41403d00c00030b40198030303005010750000700041c006060140c1c0440c951000284020540420100c6c3c81d40a55100380c100b81d8031759460302c005100c5941c00009290340c1d100c1e01d40429200c1480c09080c0c240404040c0507100c0c00040301d000c0043d1085003504010b1f08a0201b80107499081d60b0b641c1b900402152940048505c0030042c4002003a560180c0b081075000010840034600d80059000b80200424048640381d050013020b00010031811002e100c3c00e0700c520142840d59100d08140c0c1007a500c0d000c110f6200b02d00700301240400b03203d40e980c4050b000c28811000700700420307800050f10000b402c003401600001c03c0d6a08540c1800c007416030102e0700c14040e4006491b40c8151075101d2150400c0342c0300b20300010f00400d19001c0f0821a6409008210110889240c500c9800d507440e615940c45d00c407444840788206a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 548357688 1250 548356438 548356441
    0xf0c0c0506210903041202011d09090c120303012d080d080403120506010f053010080f0a080318010f270b0a0203040201110d050a09120f12020a0804030506 68
    0xe0784982c80d0a0f4000249070011400d0610307003050340e44400404174000f81009200c40040441d0320108080019124008003003148a240002c00240d40307070342188116208801c409221030303a4030300c0030044905031a00c900e06802146003540038208021040c004c644454049608005070303152090095003010595551020b00300c1c1030030b050050018a140c4110240f481c03030a0b00b441b00584c1c000070390b10450011b50801e1900c03220610710076005140001c1b040405001d01c108540000d076110b0181c0b500c2001c560440380c03070203500c03180c400740e554440ca00c1220740b503407003442e94002107941440a1644600087d5004840725601c50a45003902e1680304500c03020768942e245040720114420400c0c01c140c0540784400028001ca0b159040c0c4500041c0c9a44c0c56241d00001040543e44560b2003a1891840e080480780c040001e03074070040103680140e003200b002441000c1c1c04100643c24003000054181c115001507607000e841c3d1240684a107107000050254818031040310700281c0300602900c005d500900151643c2d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 548358938 1250 548357688 548357737
    0x40c0c0f0c0f09051501180503030301140103060b03010308070f08040915060221030a0f02090a120618051f061d010e070804080403032303010e0a0b01030203070f0c0c0506 75
    0x1141c000f6080440c0760b41c24041040040303640c020543c0c00040342440c103409007200c459011080c403201030704025018000000080762000b0302240c000507080082c1d9041060315901d00d600c1415000a001c0103082e0102040600081040d00304031002550141c02d2452070f095a404402080b13451406201000c4005071008201d82c54042c040c0c1803450300c44038000345500d643c60000c0c130305500c4014001d11246d0b551360000e40c50010a541a10850318014280c2c141043e01c0d01c903413407902c5061000c04c507403084c03d003080c401510116400011604d0b5002c4010b05003040d4031403000000d0503a080c100c0032010ba407100c0010340c840c96111415010038100d41040c80e25410401850100c440c0102407109000b1203200340301c0014402012141100c1c0c15140003954207601c80103d00c1001c120f1902d0400180d0080b001003480b803807110000c3e0042d150b18070104000440c8000640c141c0c0401c40d20300b0049030502c3d64006546020b80407401c0c03881c0c407501010000c1a100c00000704180c1110030361818031400054080107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 548360188 1250 548358938 548358959
    0x60611011406151608040e0117030a080705090d0c0b07032015040606050d24090b0c16120305041a04170d0f0e2811040c0c0f0c 56
    0x2000907540a15041490000081440c104200620346411900042c0c043c10b2160849104040d0a43c8142500d03685d69840146603005102800b0794800c40c1140c0200c0d41d484403000007106c1c4d10042546440d285c503540c0c82c009548940165848079001450f20700c2800028003061000e0014000c55501aa21120b446c00c008040480381074903000c1408107030074a801032100c001001e415880c08000e440c03a242d5110324044000c1d210690142d41c110412748610f10421001507001400d803150b60b48628094500160940140c445211015000c07a000d100840d40c80740e074650007031000c803080c84114545141155200058554100319050000e655001032204011300020310406422150f4205102810b190311800302a0b00f400300b082c9124000081d00309200b041580000e90340c204018020017214440816203a100c0001d2100350039000704030740040381560782c41550345c00101d030005858817117403e20307405110007840071541ca82c040c00000c19075000025009012612607030300c00c402505130a0f190884041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 548361438 1250 548360188 548360201
    0x6180b060f070f050a05010e0606130203160f0207030f084302040b060d14070309030903060c020a0c15030b06090d0b100f08060123031b040f06061101 66
    0x2485800104601e0310384208010070b9810481c3c0003408100480064900b0602d410b4207040018100e500b07141c24850750340780c0401c205200301026112064103100c040e001e58201d20040f54803544811800e140d07030710302c58030a03001c00780c0726141c03801240c1c03d003a180d80300d40c1c0c0d04081d181c0c0700325090720001a0005040c0030f4001001c409a01c1941c2c101c0c1c10b2440100d03001c54950181c418006007040c6240d500c03065681c1da8220b500c584c5400b400099031659008a0100a031100c10700141002d110000480c03502c510a1007034080d002e825964a440b03ca0842c0d80d000301030003a034160b500031880780407089000b0a24400c400d8001300248800510211140c03c005015100c210022a01c111001e000c0c421294a0304141a01c0301503001650780860740c1d4241040c1000e034600e4101c0c40030211401008102c480700000d840e8180c40c55001014081038001c221100000716880040d909a04410010b0590490321480060074000007030020440841c4094250b040b60b49580c0210002240c103498141440710a20688 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 548362688 1250 548361438 548361461
    0xd15060b0c070f14030601031403040e01150305160e01050d270b010504050f1f080d030204080f062701020702030a030804020f040e0c0609040b19150504060807030c050903010618 78
    0x8400c4004910019171105c07070510001e03000030840940f809d01c1940a008a40150071010050802561240c2c0b03910346115a52b421040400d00d000082074914a000302444940411035a4080d0100d0721000115541e402c10001e407083d09844540da0303946180803480d10b18280c8034004001100c1d00180c14035601c20701e010f030f02041c01145000188580300c03440000d4140d109201207000081d41e60031010440c1c0c2c0511543c0015002c0c06401131020250b40c1c55001403085075005421280d510480c401d4040e105c04080d51440c2d80c03100c03000c503903111801d00c1400d0000440907040005003446040d4000c64148180c0903030482c00154402e082004515150814404641e025034082000045104900341e440660b021070901c00d003c007045280c540c1d611500400171042c400351014150903151b220051100d0075501802d41c1200702c03c80807603000d40c4200155001c036150303550380000c0d40c2c0b44c5081c15002405400801c104006c0c0800c202310258900b40194402042840b4408881c0645205134004550006c400d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 548363938 1250 548362688 548362709
    0x210c0309070b13121103120405040b060405100e0d050a12090803071518020a0305010204060e0306090c0d1e0309050f03031204110105070b0c03011e050d15060b0c070f 73
    0xf900d205007262a1004240c6400410300440041c50b4100542c0141d80481840d5040c4607880500f14107854410182046402c141c03814403005c08140b080000500507401500d41050810108941a03445141c2e4850038080141103040799035241e03240c10741448504e0005480e04840041c5500015510202c00030040c0100c00146040207a203907039070510b101460036031a070a141c986a201d404201c1d0844900ca2469000342070260550340c82c9407841c0130303400520a41c0082601e218032844581070105001e4803898044000d03104001c0d58a0030041d82e403100d4242694800d184080c1184c1d100f0380c0790101102d55001c0c0c1c64094569140c00d081000c00201c0c004a180a42c00031b10141810030620344c081900554804c40102000c82c901c401200d45008030400076040386048030911041c080100011410303943c0f441610108111000484e0a400030315124554000c0d52555034040480c4c8200c0118000380030801c00880c010303990300c0401045402c1903034485280d40044401b081080b104210810041c500ca200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 548365188 1250 548363938 548363947
    0x110c0a1101090b0d090305040803041e06031e0e120d0e070b090d080d0f0c050c060c040b030a0b01020a20030601171c030b0d0303050105120c0312210c0309070b 70
    0x15503003400e01900e80701104c440e0701c0d10520410140a203003a20301400b4a04102d941b59541d0750015060585a5844410994544080800d0503846402500303008072440c1030001d103400c81402600e00800030b00e450014607008846413814444840030040c40603151070350002c82c040080407101d03401d0242c03c0d8051140c0d14010860301c08242c503490365070207906801214143c0c40741101912080601b204600e403844251070294007940860b004000360402080700412610f19a843d03829a000b103100e18090061100c406000060303070241ea94004001110b01071040e54050708041d41d075401c802160f40500d4000004068000742c290404000351401000320700031640292500341d400f9a214a03c20100034180c038440500d041c00c0c1070103500030034032200340689803000f104594200140185030a00600388140d200e05c14540040d40300041100b40034400901a10005030051503074507050348100c0b503031448140320845403405c0d0b0024114003440b829100200950701e10b07141d14240c1c1040030a40050b04054014072 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 548366438 1250 548365188 548365199
    0x50f0f01020d0e011e080915100302060a0c150e010e0102070f030e1f020606090705070302060f060a1d04030e012d270f05030d050f030a110c0a110109 66
    0x508040062118105034548030300b07220049416940307410380c4070070300d0f03140000601c05c043c1c1c8084868441c0404800740c3c2d0513900c081d45021220001510700200600c07030184180013520b4003400901244907607080c4a0080405580c2e10362040b130b008042d00614903642c41806501200070b004030400e800c000d10003185840e60075581e0a1000110840c09400c0003580c8078008000d84500c12200c2014500303555101103060740400096441c041196264002c84081c008540558000c10940c0c54282e07054000c5c042958601c100760070302d0785004140a5005003a8600021155071a400040224200e2200c92203580303000e00f0003902007520055540d040284e8009900340c0e84803000c120f003d21405440c00c039492403481c1078040390142c0c245020342403c0c03100c103800d0400c1085030700b00c180c003212001110304601545e2002007544642420250101040c0304100001183c01e00344029540130507120710014181000c5c01d1110083d800c4105030f1307035a5034030840303641c414002c08541c500078140d02413800e804400e0506 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 548367688 1250 548366438 548366443
    0x12031e0a200a12020a1704060c03180213200f2709151516050c03010e100506061603080117010603022107170d08181e030c011401050f0f0102 62
    0x55111804841e030100d542c0d0f445c0b522644420304111941d0341180e03028203140c02c008000300001915000403d103050b24644611290580040003290001e1402488031410712200740036150707520310040400c95482d980c100543d94075001e448084030030f01d00c00740c6404580300240740c10305001c3c2901c0840017094518142c1641c68141c40d81e80481003106200d600c2d510003012503601c4908906107801c5400c0401c0001410341d0901a40142138000c000310360705542e0200c140b508a038007860400010f031700b20f0001d03454009501e4102d5500114007a0065142c850107505546105c02111130071000219548010450880c03209100301c1d01c0c101c001c0081192528541c0003900012695400810110461440e40001c00050040030000c2c410000c10b500b45017024000b42ea1240521409080894410300200e1020303a04400c005d6500d03121400200000910b40f0216441c510400403a0340c0244000c01080c45010001e020726140160031210040c0710794103100402014050261200d4080c0b01680a9800280ea00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 548368938 1250 548367688 548367707
    0x206100506190c06111810020c040c12060905160504050619050702090405030a11030304170c1f060f0512070e0a0e0307140d020f12031e0a200a 63
    0x48404a6041c182d280c0d410b41c1c4461100d00c1c003524403403a0041c145e260250b03c90007072a221281461146080d4944000c010890360030710441801a4031002402c2c1c180d0401e0781c4400f04244072410901115000340340c42030103480803031b00501c1401c5e0b2104248140107002281500344000030b41030032800d050a2901242c01c1d40540d80a0300c0704442141441f800541c000c0c1d08a43c0041d8019014600074940340c01c005582c1e80c00225440b00080d22548039981642011041d030f40903a50040c080312259902074042441904600b00181c52401052082e62340c2103803104501007071074160380c804508103140001c1082071000c9a03020714001c10698040340010240803903035905454a403450600c154403942c041030014148000481014480000e100090240864013040300076070f03e000321080e04c006004105d84070200803601410795400442c011003070880e070301c0265900101c8052400b0301c102d0b0700c00280c80484019602600c81d203507a100a5903400040e12105170380c07003400c0d208003450201c20060003014080f4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 548370188 1250 548368938 548368957
    0xb0603090c0120061501031e05060a120f0204110c030406030605031c660203030301060822030507060c09050a0506070c0801290a510206100506 63
    0x20411761600b800c1e80240d00040b854045050b501c0d65149001600900070f000a48100707100b403049a6000401d0b210500385150003a0f80302d10340520343c00c640e41c03c1c0000f034406104003945100080c8204184400d0800241000780300c195404a065460101410b003008901d1035180f94001840a00b02417258019007044101c00f5040d0001024000039050b034801c00c0d002910070480c03580c0c20f0301000308840d60720600100050b080107400c00c0400070700703c2207e00000011f42c000c0d0103410900041011a02070f420031a0f02c91100710f5030480217001d1091040d551a00c444049010850101d1802c061010a11403451801400e041c00c01c80681803400141f01d0290a200b21171140400260b550100421103000c040240510030003404020400032a2210300642d06a601c40f9039081103104864a2420f22580350450710100c10300c18070b80046085003032440c1000c0c0007500201c00c0b5849081e00d420b460240f00b9140f040d0200e0309000d0012404c000034200400601014624003c3c0d9406210998581e01250300346203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 548371438 1250 548370188 548370211
    0x40b0d1209032f04020a2102090603010303090e060a050906120a060e070612020403030c020d110d1103070f030c0504050403021c0c0308061c150b0603090c012006 71
    0x201828000c848071406608018402c0e5002d80029008100c0014252006052450360343e242107804020702c0201d00070340d20490000340c030b2032840500d90301d020421007901c4035100d039000d45010409404107980b9802a0300032030005007032010802100020962094008a0842da8a4903a51600c0000f03103031810060311507449800c2c080511100300d43c0070408051010b40c0f1000600c90000c074500d03480e85902d8588140c1d0b000c500c1d401d6400306050300910845003940e0745625450400325098090010403510240102d600d28445000160a90f46000030301c0ea01c82e10410706c60311001c0c1c1c3d40040c14109540780e0f200271100a0320400600000d008845000240c4006440008540d03481c1c0c20100c4c40c0100d0708001088071002d424100c52079540c8210041320003402601d030030b80161a070a0900c840042905448031843d41c90b240c591000941c240d80414000b0011203001c5000c4142e00f0000700c1590054500001590000303440c44140d5800c12400c80350702c20908101e400c04047c0c00c8446842e08070040400d4100c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 548372688 1250 548371438 548371463
    0x1104030c060e011d0901060302180a031b08210703050d15030c0b0a020613030e120d0207060f0f0e01090b12060301180b130f08030115020c0f060a03022109150105040b0d 74
    0x1100b9030302842c00c4034400a00d00c7d0b001664034140180e03034dd2070407480b0748044ac6110700d000c95114400550b04801c800d901000f80405040008002d11035003107100e0403020400300708038191245005002d0035541ca11030b074103240c210615520f40403601c0e000b0781d4420060000c0c18001481d00940220341c0320707403095402c0520300700c20106203003c40300e00202d1104251701c141044040c0c11207180c0080c01148218058007160301c40e64880c0d0054810090303002e0a1000500701101c880e401620450903101c031800d060400c2c6030110345401030b00f0b4598000c1005560120079040422440349070034040c0a08407281d40d0030380e1031081c445484d8661243c078018a4541284202a1080d042045070300e00c0e10f8209070081c003000d0f183e58403910717104d00d00346110312500c0042c807440d903030540c0c07914088114600034800200100d1a04207207050503400b81d0403040500c5a0010341048038140c0d8658030580b140b24810000103080009450080000c0511068201e01e02603403800511140c1a102c405840c01801d80283d0306030b800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 548373938 1250 548372688 548372707
    0x60e010e1c0806040212010609060e0d0f0809150f0c0c12061f030c0e040210091809051203160f091a070f0f03110c010810091104030c060e011d0901060302 68
    0x192081c942c0300304d1810388102c000a00a5445a1000241c6040ea40c6d80c1100c034bd1b880d000c020200c1d0240034054892205405a440011500c0c40200301150f0080c0400780080802a084020b6420035822410760b65070004142e0750302001407190340d05200302240e01207203415450800c00da50700c100810050078400003400d60042600c00230311510040d40d11520081303481e500c0e001107400042040d101207008510111340800c406010700302c510143c482e000440d03201900b2a04003000074011120003950b05010f144030046041481c07400862140d4072184607221b880c01e01810003400d001102e2844400c001d020241806000122282000a98a040500c680781c0040b0308201c0e4904189100082c00d074608150184c0416411149a01201210f5005c2e41d00c560058030041da002a030458a40100110500d8107100c500d845501c40f04240c1c200d00d1200303003010386030303a6100342408154110700d01184901042030030345d680c411648110703404d0502003040c0d02c646050204005610600440080c15008a6070121 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 548375188 1250 548373938 548373941
    0xb0307030803010f060908030306014104060908030a0203221d09010e0a02150703140c03030108100b060703120221090c0402030c0a1b020d060e010e1c080604 69
    0x25641000701240d50b9607540d00010540d01ca18440c2c1d80c0811288034000856400c0401a28422141030315040760507814030f4031182041c0080340002c0341c211411200780c00c4c1d0b560700300f1402015895003142d0540d07940c100b04000c0c0c000d540301e5101d07030302d180c1c803c004407014039a0101c191580100c00040958160118180424111801d600440024644201c810050f00e00450125014100d180c2c020040c029441200720f48078002204040d401541800d800076034a19880001d09074a406403601c0c0d02d50601040a0310403640c020702c41d20010390f00101c018040c06e0024800340d081e0440c485410401b440a40020540d2409110030240c1840352134515108200600d4045450850b00030900c0d11044400c1c0320b03040940c00c1d0030b4460400a100710001047c940c10248202d074019103401c0c04040c100103080404403159030750a0322101c1003d420400403001a100e81000000403803050102040c0301031858421821240c06550903035072580001c04450b10f81d0300482207610b50700a24130306150296110f102240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 548376438 1250 548375188 548375203
    0x402010c06020315180709061101020f07080d0b1e04020304060e0304081005090303060114071103031603030b0d0c060f023d11190309020909011d01110a030b03 70
    0x200300300d00020800094504d0310a031425400011158204103850310001544040811103841020504004e01400300501482c008511810840e0002d8174101e5100d07070b1f4105e250410801100c0c44400401c5642881e490b80c05240c1440006541594032220705c20070645008480075a51402141c3c00004141844040d401140b0380c001c4902c101c035900d503034488401e5170750200740c056407040903d0140415242527001c130450b4011841650f07200180343c402d01907000d0039401500e0031a003030060f0742e0070581d441d18140050259400d4914000b10320000340e05000d01610a0a000c05216044440c000c800003006e440b204019038443c0c3c54100504c011944c01a4542050740340c58011107099802c0391510816860107540c604d440c02c440307908444e0300310000b840c150b031991700100004400600034400d6500149010700c401c00b0141c42c0126500329103401154001405603804c2000d40d44034008554141441641c0310304000481d0000c1000e01c004e030380c90800500414200101f05520b0302c042103d10350702048800d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 548377688 1250 548376438 548376443
    0xc18010e0117041211070e0408130e0106030504060e010c12180b090601030309050901030f030c0c120b04060516230915030703050c190f1e1d10090e0402010c 69
    0x840242064284000001040d840c039000003070381d5520400e0049004030f680743c11141c401f00451896101c60ba100b0b1096003007030361606900420740000280e0a07141d0100b06000300002d0328001014203190408900fa03a2205d048007405a0402c40400d1400d540000a0929482e200800250317910200300e401c1d06040d1424806011250382c0400d0003c200004520720b8100d92080d2900c0f205541d6480a1182c980001d11000e49544002c0100c280030070300400391400703001d100d83d1903007480644901d05400e00200c055001d4409009200820080011301d128841c0c0060404040c0286003c14240007090302000b007000200d104000740f040c9807020031900a446050b00020003e0300f4200040b000412145c200729550300c0080c0c203010104d950390303400f07904882042005010506054943c140300392a50101c040c4960104050241d00307800700b4000d40031f05403003210155203200400d001c000c0c1c0c0502c002002c16055103e41d9582011061705038111414100b00d03038401c8402d0459907a540016a49112040b102 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 548378938 1250 548377688 548377727
    0x405062409090a060f0605030405011508010e06010b03060a0506161707050d0c02010c08090a150203130f1412010207050304121b06091403010906150303080c18010e01 73
    0x4a01080d44800c010781060758003a80d000e040d5556850f0500c3c00d5403040c0c8100c01c60b4061207541803041c548158011503000d4001c000218030b0060407800c041942c0300d141d10405880c1d56540010003000d005120142c01405461081e5085080c10381c00140c241e061032180d184180c00019654002d1074060620510440c0c0198200b02041e500010b100440d91160804039800e000316410b411503203004010b21030845406039950005414103507a038130380c10303801003a100703034802e018190006006074803181e61401413030550301458450320250040300340a40300b5000784030740d2000e200041c0a244590b2060501e4003101310340f00700d2215014480307a80244100500903085010000f404694601541e0340f21510740e2064608108619100c61103000d407030941c1c02000700240c0303a100c00700a001c90360515a600030f4002000001d0304006652043d08503141070301c03c42d41c90101000302708141600440311a0740101d00c105428504044405079805580c0d240f00000e05000c0c04201e6110564811880e0320b00c0f01081402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 548380188 1250 548378938 548378989
    0x30d180e0c03040b0115021005070c12051e0705030a23040326071a0601050c150a0c0518060a0507060c1d04090f021311160501060e060906040506 64
    0x41e074080642c000c403030a07184158260000280b1220300120851201110b5000d8031600074020707000d501418014025504001d01c0d807685802080f4440c03071000c00c000860303c0d202c1e40e50901150444d580d02011204841394030040c407000020842c0803048450b00352440c41d00b20307164844554480c4011b040c1d1030a04032074104c0410f0210030003410324501805540c03c0440c00c107103021001702d812490700c200040241104a0049090785810900340c81a40010b414146030707040c85099155540382944015080c08011404001c1c0081300005114100818096240031450408842812011180307020249030040301c0c00201c42c0c0060b48101c090b91541c036840403092100988000004003003514002d0120040b041814251001e4031b0981305041e0070380c0e0f10001c4100803039815000c0000e942d00040d29480301584602050301c03003078034410007044001c2c07051b40082001702050030310908481c07841c0c00034100c071040907092041c11307030380c10050fa43d204008a6002c20740781c8e65107000ca04244054020011060761405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 548381294 1106 548380188 548380201
    0x2250b07112101050a150506070312061d040611180609121c0e090f0c030a0b060d02071b1a2d0405040515030d180e 51
    0x80c0030015804412070350041002c201d034011030290f55124100700b140207032886082c150003403640d566420141024007081940c40740c5403000c1c0601c52110402d43d6080060b8121324040d01d0500c9240328060116040d842c4040f80683d01140d901d41817844101e0700155100650386607544650403190301010080038050030b03920449000da00a5100c0c06800074040080114a50a8003d052140020f0200200052a821144011604c60700c925000d210821450603a820780020102a00720347d01d0300d84441034001071402070aa01d0f004080421001c0c00d00d0950750141803141c0c09a03814030181c001c03815a03400c404015005501210702201c00c3d569001002c10b01a03d403050901650200b4080290144c05000b450559200440580040c0134045424507000d16078004003000d500c099034030f54442c0080e0326881f28001d00303410000701040040b0b411540c1036103035009002c100324002c803606080 = true := by decide +kernel

theorem cover : BRFrame.Cov 548201438 548381294 := by
  have h0 := BRFrame.cov_init 548201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 548201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 548201438 ≤ n) (h2 : n < 548381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
