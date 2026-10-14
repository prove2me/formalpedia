-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3035
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:28:09.922984+00:00
-- url     : https://prove2.me/submissions/b1797f96-65c9-4e9d-a512-768350b4301b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 545683453 ≤ n < 545863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 545684703 1250 545683453 545683519
    0x905010b2710080105010e16091404020d0e010203040b2502061306020909100906050613030f0f120c110603040209070f0903061a0f190b0f0c100b010806 67
    0x1c000303800c5003000c0c2c10107400382c00d07500000c001035030310340c0d51003103000300207403594946401d0b404a4100000e101c1e4181105840f2140d20000035040c0c28800e000c0a5000020564940c40e21891107024044c001d00c0650b00c124011000464a82400d01400e980d444071020000c405c80c034844c03509850543c0000b0719582010300660307652105480750070300c00024017070003084590000d4682c1c18428888052007022041d13030161801044450b5131841004840e2040001c2540d1321001a1401c10100344030455125105014501181380040750b40d0350310000420181090b004500407110820038060001e03001c500b011010b5503401d04e5030030705400003952110020103601c10400400b0600704154410401c0310001d5603c46024442c00302801850300958542c410790780e0050038006602c09481c0b52a418048a000c50440f855403010709200c004e813503c0c0d000c0740c9088100d42e0200700c1041100c60400002d0340c2c03130710031500000300e1001180004000240141c501032280f000f5594032420a03010f00c0d03e9845c0c180c81d82c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 545685953 1250 545684703 545684779
    0x30609060d02030a0507180209030a0f080f0d021314090406050a24180603020d0b09070f080313150f0305090c040c0504090c0201060f03020120100905010b 68
    0x1200020300744403070640c4002d4050080b03407000c104000000540800f652a80c41c10525141442070410080380200d4240690540c00004d00700d020803200510458944c3c0284e05040c0342a03100a41c0441c140e01c03a9200d1103401ea40003821440d00888651510050200e440818080c4125000001c00741c040140018080554500104c2c4070581d05501021420f001890b140d06d20329036aa650030301a41441c82503450003203484d130040222541c144035074400d695000f40880c0002040380c40d02c00c234900c0d000300160403d104a410108081115000440041074031400850762241c1e0408242c40f40e5405902803101c41d102c01141c1c50041d07401c250707000745600580c42c00051658070074101d80c4c80c084080011710b40103440c05a811006070307404030051054420301c003024410b40b40380c0b0004900701d601a03c242e8501c00414501403006612403444202401142051035000c0801c2d5400710b03003081d4080141c00001d66882046100700402030040c41581c000448600380e140c0340242c4440b105140000007880b0784162 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 545687203 1250 545685953 545685961
    0x3050c150a08060a03020a14011d0a03171303200415270f0204061d01122408010b011407020a0b09180112031b0c0501050904061805180d0203030609 65
    0x2d00300f44c0000458000b40703c0d00006a6802e5000c584e003117035280b5140068088041c41c100914503108042c4c1020002c0c3c003220085255480d5080070f0340a1359280880e040b000c1014400c200c041c245042c019501988016003010b803d90381101706400007002c92402a03041c0421880708100150030f25080320320460101003140780c0b1a00c0c130210382c1c6003d108680c0062410503992410441540640103803021a00c030245041307030600c0f20403003004000c14180d00040240388500b000c2d450a0304a01c2d110005030780c0560840300c80c0050349118501503000407940d03a56500005c0300f55a0300642c05042c1085140d0111700d40280b64000c2451f89940303000d406141c0500103000842500d90b2040c5101c1d052010a0103101961a50300c182e01d00008507906034000303a01d03c603440281d080d40e1400c00d81026071112007500702c07525000043da540c1c4c00c40703105580d02940e11100014036551000d8850039082400c040080c0c1498443d210198060b065200c4210541c0b24200e10313180150004105d940204003102c3c41100342e13907 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 545688453 1250 545687203 545687209
    0x81b0105040b24010c0219091415180c13030807050f010c2d0207032f100e10051308031b030c03030408130504060b0c1b0109030b0402040603060c0903050c150a0806 72
    0x41d43c0d0323000c00c00306464484400b218481e01c070780c02401000901c9000c0744068900d4100450044810703644110002000085044416010001c103400d044e17412041214503941d0b01e0360300164104103000e942a800c00e070551900140203100304141c2c7c0010b410050300000000849080c009645840d00804214a44c0006000c5008100360f400a6600562240c1200c800501c4951943ea11410318140e40c0f00c120303420002880e003c455480c1d010040c0d65245010b00030f8104102050410b44121000d01908210301c131040c01e400302ca010040c106281c01107035540c0e24121881d00b0f514145015420070340052001d8680789501000700d94000360000705264071420741d0700b09587e1b610131130390040e6030042c601280010b9101c14180034220210340c0030151000d20a0048007442c2040c0428262400118802410f00001e030800300056000350010b880064401d803241e4645046566000c1e00d40c0100b0043c8604200300401040001c0c1074900c00c1d605082c0e4466010901000c2d8010460b0f01000c0c00b00c40000501c02d07032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 545689703 1250 545688453 545688499
    0x9030207091806110d0c05250b130c030b0c0a020c1f140d020a030507120e060a0c020307120c02030d0201060e191e0b0f040b030307081b0105040b24010c02 68
    0x2c030f02c9820804241e5406c8080c01a40c088905038140440c02d02030304003000da040000409542c0c010b040c1d0846940c803c4225150312500d04c0c000c03101090300850200102d40070055880c411a100c40040d5959148004007a01e03007064107080a104442500b4150000e0701c0118211180c400281400d5408071034a01035149140140c240e105002407012541581e0360368141c2001d030051540e5280d41d0380d55003442c070110081c0c40384030070103c0103a44054085042c04005a000111400c031500c107490425040d5500c4245640c1154140000101403040190035843c0c20b00038145080242d0000f00590341c40d10709850140c1200030320b14001000e07140c1c0912810a8942c221140f031000c0c9403c02d4480764161200c010003000ea103c041070140601d50805501400d1502c0340700d0140c64000d0082d400c0032010307a130f070160b581d000342c218060340e551500700c41e0f402d071100b4010f0300c2c040d5220700d06624441c684191058404102e41c65801c1d0505a2656901160b90300000e480d014242c060b1120b510500b04004118018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 545690953 1250 545689703 545689717
    0x19020307081006090c0e180709030b010305030d0c020303070219081b100b0d0b0a0b060702090c07021005161104022a0d08040b012d06030903020709180611 68
    0xe00501d82d01c038070301840070781c00074066450421082082c9500ba1104030b88125030121000e4003c15106120102c042090313401030b40c00701241ca815100d154803030f540c01805020a034402c540302c2c0d0001c035040c244249540105822141103100540c11850300700c000950b40c2007161203414107074035a0403c2c00300b40074401c2e089542e21110180748055010740300f03080781d590b100501001a0805c2c6856568403040c0b81c5039501601c015006130b8204010b07220503e039070005020b100103d0354410b01c2004a5801601c40d0f00b800c1d80b2640c802c07089103403246480e005120944002c641c2c588208181003203840c990100c401e04508289400c00c0014500c2100e03140030400a02c10b046400510201c40001c020100083c0d4200c90014480c0c28240e904200c09810152042c500641e40105a260500010f11180d0f202e031904014180000c800c20400c03503c042c5150b4490310251b080040069104e046d40c00034160100a00c100600f070740d42c1d00300010503158152420401c42804020039040d00d5407401c11000c00c09106603640 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 545692203 1250 545690953 545690969
    0x30c0409021210060e0d030809210705060a050c0d0b012c0f0a060912051006060807110c010807030b0105071a07080705030106140714060703050a06051219020307 71
    0x1d6444030301c0007188000002c885250710740c00c0f40341c0b01055691081c0990300c45004050802c10031400965030965011324010310f015014400c014500701c045400310710740060354081d503840c966101800e040980c05d00394010300382d890700d9042106000e0000310b4082160060101218005000c030842c0b001210007403002003da072007032884000201e09418003000003800b80c6c00c0031545146a0440c14007400ba2204291140001041d00308004200c203d00703840b550701c1000d20440587ea5554240d102c46400c41e07060303410602c0007c0c904002c1110381e94200320b8040c4a804903000034641d130281c000008008100081c001b80400d81ca031802d0810340d90203034065640b0b56511000c03942c1c3c40c070407002c1d0815010030200c801780002640c4030089000ca50048045070b068446c180d8a46c184108810f072043d006600000e030403035228003170f45603101140006104580c05402c05950120742c6007040e0203448140ca206802562080c80703911460341210400103070805101c941800342050700f4009000181c00d01d0f91907844049 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 545693453 1250 545692203 545692207
    0x151812050a1506080c03060c090405070c080c0c040b0d05100b0a0513091209030317040c0306140402040b1c060b03070305060a23040317092104080c06030601090b030c040902 76
    0x20500b4060307041041601c508100311070280d80e910f420150388075000d4034110100c220802084040d4245500300301d0348840c1508002045d030003d590f410f405540a034116003020b400080d1010818589409282404d2004a4000040c0d0a4940780c00c1e444008240c100000300e5954403071400e00d501c0d20000000200401010801c5080010070020040d00d003203541221f10400d0035001c0c480060141c1111403c0c1c94050340c0b4401c130b03050080504030b00020080c106070740042d040c040010000300c09000340380d00400c0c00c0c1c903054247e0916105210035500d00200d6180703e00b9000c28000400006409002340c220b0700840041904400300d0042401c0071401d400242c85409a1400c00111903c1340d0070445520003c0040c100a203c8011244229080305550040c0020f0f40f1012144a01c110028941e411031b0b8000160794500c1e1142110742140c950034034940710384000200d800c1050171002d0014a01801c41640c900740756140c140e00082900400c2d01410303408440120200e403800708040140d60151030740c0a0119 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 545694703 1250 545693453 545693483
    0x1d0312030405060a05040b070e04090f0f0b28050a180f1a0f011418011409161b06060e0705090301050702011109010320070309151812050a 61
    0x4459a8011181502d0301d114410200b408240c580c8a80361050307820200c0c0c179041c4d448a40c01110004004882c2c1640951955203800105d0381100c11000c1140c0300b072401c620300d5000362600d1101d42800804040d22000c44084481ca4010005009038420803040c42c00039050303844070014401040000101100380004c60340040400c05401d40c4403002d14040c4c56582442548010f4080b202c0500300d918203000485800100400e1091100500040100411001c800c48502c840d40b610550240d200c9400014518020240e07420400469034211170b00049407064034080d01401342c007190510300e166040c03c44070480c0000340f00b4540d00c248090001d1102202082c01c0c101c0e0028050342090700458465440e100100f064540140300740d110306024400c00a04041c0321b0030054005001100302c94551012182e4103440b412410802480c1044c400d868201506043c083c1241d5039030740c9500381c013041c8058055440041403490000c181290382c41c983d03100a09a0902e00769041100740140101071100c041201 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 545695953 1250 545694703 545694733
    0x40e1b010215041407090b0f0d020d14281a1b0406031d060402090408030a09150906150303020303010b0a050408030a0e040e03072001021e0604020f01140a1d03 70
    0x300324044c40b40c001c84484907118032680c0100c515200440740c3c410341300700c0c0071041400d1014800c400139000500c01c5c19004500d0310341e0345014800c0c07a000d01d0103401101d106100f620203400f003091382010451072540d0b9440581d5811041c0f44004881222030310704c6400040c141c8601691800d09010750000d00c171b440d10b80c0c40300c000d00034208105103001800c0c0041ca0403400301a001074954807403a0000c014840c0c6441c4c035215450154030240022410315255400c180200341c041740803540d42442d0510015201d0030f14144181242c0c055040140c0384891540c041010a078000141c07819940141940d5035552001740b42074400b8416680120080d000101d0302018540e0024010240d04400392401e100814102030700359268881c200b4018218148031a140c2c3d0751481170409991140010300485080340d46007503e4860109120140d001c1c40c1d80f29404110450070180d00c024801e407002e090200d01d1103001b104406d90740c019a8610010084040c1210b1060103000c1030307540c19450040e0984070300020703c0001d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 545697203 1250 545695953 545695973
    0x403060f0b191d1504051b0a02030717030106050f0901090f06080a1512140f010504140118111216080f1b01140f0d020409020a020c040e1b01021504 65
    0xd880720400c0c102e461071000460b028800d03202d05003643d422080c04100000b040014030015047c1030300003c0e164a20003082d100c90f002440e124685400039170b103892091500c00808189000840000e0005000400c0b4090300b1100742c600c07011285260310307250412000102c42c11000ca503c000c000000f0660000381ca07581099500d8098480b48409002807416904440d5003042c00d4072404148500c0c0855942c00701d00d207a00c080c403606080310159032001030200803203800d4801c20b80c0c080d1303104104009103500c10700c1c00b4071410381150b1002c10244146002c58480c10782080c801e0b80c00d11301a42c40ba14a035480480c06001b8610f03141c030b0780240701c0440ca0315041420b5940000503c0800c99200300041c200966100035180500303200b0507581c04201c0ea0140c1c1c51140142c00800c4d0244036444240b0001220140c1030002d00054228828016241c00102d0b20080c60515080c000078052440c4c0961902500d40200d00b0004100d00c0100b802c0310080302c07400403031401d0f05261810703074401c804000380001c1048041d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 545698453 1250 545697203 545697209
    0x60c0d15151d03190204060f06110d030605010e130912030c09090b090403180b0406030b0109151707111015060224150316060207060c080403060f0b19 66
    0x5100009400e4000300031146102c100307602503144d40144d03000300103000e075a0703069940340c1d101600105116654400b052104803142e0054030114040f0140a143c0c02d00402070b000c8204c1c258a001d109251034080040c1c00181d440901038001c40d148206030f9160502500280c01c040d9124913000c691540e4480c005004085510740040020324071680005c044e0385038061480761100007070401c550303500c1766079046c0c4101d02c0c5401007000c4082060000030314144504080c2000703081030b490200302075180400040c50184250000603000e988202c01d4214154007200d58600c240f03503d20085a9901d428106503500d0306102d005a00c64030034600032030070701d01454014040ea603ea038400406165112041030762a490600346520060384031304024402c0d104c400140e95041443e0414404180b149440841c0c01c00c000704907980201210f544041100c554104400c030024a041e2030600710340c491550314465148100d100c054402c0e52540b1001c04203561640c0300281015000303000502d102143c08000c0302c00d0303880d44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 545699703 1250 545698453 545698457
    0x506041b03020a050427050f060708071b0819030f11070305070b061503041a0609010503100908160f031409100f09090c09080106080f060c0d1515 64
    0x510a05014144010504140c039401890f850780d8a0406003808000e060114821000310055841940301c01105124049800d001d82c014000080c80f546049103000c101030820782c1080740e82c0081088403a40801d1504032040c0782c1800c000c01c03a690782807800081c0265804400100d00d18444a4810754041d8030100040d404a00c041c00040702100004100c0d00803c00c014010a0b020040c10340041e22151403d0350003080100900030000d00b040c44d00b03050782c2003210110f1381c0e00c4074814000050091000020f0b4004401c03100e002036581803001007070b241c0b1350340c004007021350340c882c0003c004110409042d0303281060040d101c802404441d0074803000310860741d903040d00406d9018800c0351107030506000300c0b81d00e8400038081c040540121030040310b00e0060310f4841d0081219601020032082418062056400340c50384d500341c4414189001942102c90700d41c00920707241d210300c0302e1014081c80401d8003640300e55449040c540300e2005c7c116420251016044e0f00080a101c4100410810440d1100344298a016 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 545700953 1250 545699703 545699723
    0x17370f1a0405040c030201051b06010b0c0606030c130e0c120c12011802090711100e07050102070f0603110403060c05030a0b040509100f091401090210050a0f030b0103110304050604 79
    0x40e20038403048a2003520060420801d8180034000355008000801040301e9108400c00c04294500c0308508208003a0003000703080500040070301c0b80b81001c000e80c03a084a0120060304480b030392100065000d0101d0325501d5034031911424950044401030001c078031800c00252440254510640d0b00a0702e0301c00310800144510f00782e03c01158941d0052180103980400c1022992514030550200300b0300240042070340d01000741e0344004034141041402020004d07408228042000b400f0080c4480c00c21003107030407481c115485108100810020140c0c2c0c8402c50b00e06040024110519558105103485076410150a45040203001454150f1010086200300c0d02c514007080700e40304c540e0800090310001d41c0c00c2032169000c50303865041080103074041c580301035140400090a5032182e036104645a1003d01c0e80409035910440c800643c10320718030005040465217801480d010f0300d15809490000d20f00e01b10020541d071420040b0301c0341d000c0d500800f404c442c500c00058032440d00789062691000200d40c216104020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 545702203 1250 545700953 545701001
    0x1e090f0b0c0412030c06020706090c050f0102010c0212180a1203021e1e10091110030b03060f0702032a07081204090b0d0b07020a0317370f 61
    0x35407402d031801d44045055200080300107440803511040d00c810241c490715401c2002100003144c6108148241e07108024410500c0c3ca040b04010907804412505415a410311182078200c0e6400704400c6e0540325000c0301c90b5221214018034284000c0d0300324909400c00c03007902000c9410f41f049000c1c81807481c884e0b800c03100c1019082c00039159189002095003000c0d030164103207082d0070703010040d0f90900300d054600b1504a0181150b0290a0f90703000703402980c400c0e8074400000e4181c1001250211200c0c4541414400e840c20000480d644c0c8000130702e11810b8070606008030f00360380d10a00448101c1c0c8422340820348006010141405074000c0b1003c0000306104130100094190390109a800c1ca20f076007081094202480c01c5540c0016210240340c80783d00500304480c3d040013900c14a2050b0003a20716600500e0b8125445c03401401c01c0590842e005d82001c0c85008104e1203031040c1050b02c5040220200702c18127200210322010b070040d88a4407000d90281008940902034409034001800425510517030111855 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 545703453 1250 545702203 545702221
    0x405040204032301090b0403030f0f110c060f101a070204020f0c1c2007080703080405030607110604120e090403020606030d030501240504030b010b070303060b09131e090f0b 76
    0x9180707030014512080c1d51700087c003103400f80e4010440d000d8072250124004451380d8038041210720740c2c03040c0c00401002061100d000c3c18200119a480300328090102e141b030528090907078550744140304001c0e03032601d0846401840000d100a5501c5035501900a41d2140c8a10b100c203c91600900a048401e02c20305c02c01011651003400c408007a14100c0e25180c0360f88060a0503c283c0c42242a440c940724842c03060300040c007102c00c00c141002140110400b6460f02e0805003010f0414a015286404016a14048031110840420b500390030a901140c05245022800000d591000700d01407416800306c107243c100014950086543d034452801107055400403c8244019030032501d0a004124088415241071442000c0344079843c009400981441c0b0300b010fa0381e940e00e60701214240c1001c2e46420010880904054060190f80050a903510b40241001020404520040c12115829050780e407100030a4844d40307491603d4031100d034903051051007070035030758200a800564208400c80b41e03204c1c6640082c1c0019 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 545704703 1250 545703453 545703461
    0x90702010c0c02011101180b01030501050705070804060c060f09060510050102031315050c0f010618020f070b250503040b0c07030f27170f06010b09060f0405040204032301 75
    0x10049489000b42c100d1242c00444841507100344041c50766684280781c00c134001706c02c5115400140b180b0b0f4801c0c070545c118a00b250039604058410018080240010741c0014a86000c0c3ca0030350344503140c5105609007600b400800b4101d1403036030704011031510368601d0612016030460f601c650203245201580580d50801240e403840354403102015107044600030700500002e1001c040d400f590524240c5d0400d00110021400c10341d51440001c0b00c0e81d0b5484041100d646206084220340e60300050440c245410306240c60031503c42c000000b0200c10000c0000b98220b002e00303429075003444d54005070f04200700c090f00e4054203a030710540341900c1d81c220b580b00013156002c3d00c13811503201c1c9506584014590122403020341d200d24050100984080004405444001141783c5481c0142155030312820b02030b8410300340609104410407039002c00d4001c2e0005000300d000040c22908031040564070703150388840c0c40501151034061a00025403203400051b0000a2141c441e4641c204006004901c14203248180d244900321 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 545705953 1250 545704703 545704721
    0x20708071805090307020303190e03070506070311011d010605010315050307060c030309050d1706030a0b01140303040503010f0209010801080109110409032304090e0102120c0702030f03130509070201 87
    0x4034100001e85a010400340c2c101c140c000f00d041085904090403580000d0a54020510100e000e206c038103401e59503150700c241c10151080090303000c1e2400c2d504000120f1818810010040d0502050f10191031016100758411061002101035040c11075465401c1741e40a01a1403140328002420300103840c414544501519085a20044c001c0200c01d1600d1030a603129810b00c03005406041d0380b00111008507000340724140d254026555820309c000703500103410303004880c0034010500030361081408100003440102ca05045d00d02000e420060741c404080042e02d5441aa00419055401c00303d4826a11009401419042400740c07030351022a0b889040301804c07034602c0c070720107050030b4030b224600d020608096200700c10150182c50f041c0d0b240000c05001c886030000e03218a44c0c03800d00d400102040072101522503510100c4240c1d000f946855004400d006c81c0d08806088048010030000b2000215501002504141c0b1900c01c1500d0f01c5046080c0075904182003031040a000345114000111840e00c188154104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 545707203 1250 545705953 545705969
    0xe090907062a0807061d0a35090913120c0f051b03060a02121f030c090b040c110316020f03150a200f030a021306050a02070807 56
    0x100324540300085605207061901d401c07040c442c0c0d08112a94007075001e034002c200b034021005590785004070b00e0240c04a868001024000b84015202c1021020001c02c51910950300301d8007191411a1801c034802c156148480c1900d00382001d036423a0066206c880014200c240001c1b9801e45440e514500d0007000d084008100600300036814200341550b0340950b40d55141903008001d03410b00700300a03035111803070300034141c00d494802039001035407100615080103103682c81022600290f082144c60900000b5103036026201c2c0c48150760304580145107441401c1760000454010400340001a503c015000062841010540c040c80c28612040d25540c040c40c030140b036601000700214600b50b180e5a0314a0b208000740c03001ca9000246a80380e007074540d0104145844110000031004141c10119126402c40c0c0d00d00542c00d120403001c00c12502c0c14000d24050710994900a00020b580e0398610b41340100070300c110880c480251810310b00c085800d42e80100641140700c5280c00321800c9648a1101d6551a0035504c1500344c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 545708453 1250 545707203 545707213
    0x405030d03020a0e060706090c060e03100e03072f10050f07021201020a2706091206150b2101050a17010b0d03030b0a060807021207300e0909 62
    0x64901e229034010448550203142c07410540d07000800150310b03548480b00503940103403210b007400306101504e05020700410726410302c0d00e040c1101c000440e484118144501d02482c0d643c5180000d805401e1046615441d4800903150132842c3c1200208404090007044d0044940300e40e59822613424104e00e11b110340c50481d107842e401e002d605444500c85501a02c0304a0308040b078545010a10902400500b45030304141c1c5030f0b1902c0c041c10507004c0c850310414100126030300001c030380100000c64004102c0740c25a90400d0341c0c03442d1510142000c1000d0508a21090f5580b4045040000c1d90703400c0c900508075507046102e1720107c0c100c02181c40280c0c800d007809010750104851900300000312080030504c9201d0074480c004280082c0c60000907113040954032003600484d45403402c103200c529003150715401922190400001504141200075907a00390320050410300c1e07400144410500c1103404180c01c1e004550601410384214401c64180010303900c0d9800004078a0a8042e004ca6107018039a00b40300d408602c00500c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 545709703 1250 545708453 545708473
    0x702060d090f140619060f05150f0309030912011406010f03060b0c010203100602070b0a1b080a021e07060c12030b09041a06060f0d1a100207051203040503 68
    0x2000401c107501c42203440c00d08000800c1d0028102030b850300720b680f0066028014500d031140000c0d4090014560001c502454080d051010068100041e02690300c203840000070050030340c0040606104d4080516604100031040014030b590000040610040903545250aa8442d820890170b031090301d020510307042038040c0001c10300d502c01c4298000c050792514021030002d55442070440e80764400a60582c10340d400004001607000c04829030f5005040c40c1c8028245140381c140f0302201402890110300401100030056107510020b940710074100740c0c0105600741d0702c250051000e942c0d1a040300c05108901c1d002139480d01451000300744038048500944030760904141c47e58800303806a02c40e0350701406055403040f5881c0203854010310300384118462551401d1141001175040b070558001004103201e03802c100000409402d0030015600b19600d9000f0119055440c600b107023040c0000b244110f90010302d4080d59000e00c6a00044a0f001c5272429100c2c0f80d075001c3ca001c0003548912640c014141c140d40a00080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 545710953 1250 545709703 545709727
    0x506070201200d0e03130602070e091501090203060d060c020d120b03030706020c1015081c0e060d0f0f140112030509011808060a0203070824190512160b070206 70
    0x2d00b86204e003180a581c03800d8031009004190462a03004240140d11968080c40201d4000744415040349200000f400340c81085c07401c0c42c030a81d505000d9000c40310740100101d4200d03190608196002ca600c0201440400b400c0d2000030b55640324503549000043d19600c01c80340700c00503841840303003880c1c1c0600a5860080b294481c0070280d4801710b00c80d001e40c801e0000d0754482c800e55100703003c41060850144403015207004140c0e4903200c02d40c00c01c96000081d1541000010f5000a100e007207070b8009440c8541c03611242c2030068010041b01010302462801c12103590700888031644520124084815051016600c0e44610825a00c2c100d80c01000304d502089003500c198098051a10081d405d200300306070440d11442001c1c00c1c11002e80706005a50f4000c401d110b602c1e50040406a480246505102079a1029000150b070459811549078050041c14a1900f080c0520b8070b050006440c010701580c00740612000b00315038910b001c0c1102a00800d40542c00704004c04c40750211400c0035001002982000100015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 545712203 1250 545710953 545710961
    0x280c0804050f010504081c0f0905010903030c03021f050109270605190204030803100501030b0102250b040b0a081e0c030c1603090e130b150105040f030506070201200d 73
    0xca05104c000c0c0400180c03008100041041203202c500501c2e805003e0000180c0201000d0b1685000c0c0304004805002c540d0b4000f0360541100d0709483c020403502c507103043c00e81c20115941c0108004001200780210b2141150300040e040362008041040100b00440d50051044e800f030740c40480d4940c0c0c1840d00c1c030201790540c00c840d4201c0399800b03000000403000401310080340e0259008507400480807042010304000203004000a00c070170708040c1300503a00b1b040002d480b580e1101e44115481d168020040780c51001c0400400500013141117280c1e250384074200b400305908801c0618000039810000110f034441c540161514101d502900b00c199600c031095851010780000b021551544000d10503e41741420105400e0821402921981203c034103009880404240007002c0d08900004000e185000525100c40d507903008500c5900f0000d606101c00c0100c03403038070903648151000c200110001c030a101011841500500840e0000c018603940c0015284400d91820601765103501c1c24004c107100031034a504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 545713453 1250 545712203 545712229
    0x509060d0e0d03140a061410050409110403020406060306080325060204060509040b01080c070206071704180b03010b0a0b0901030b0604091d060402030c10090b280c080405 75
    0x140104200003803580c0300785070010366046500044d0301c802d11340c03022818910005400142c80751090240900340354902800031940654240506e00380304102c40c8892151003594090444e208003400381009842080d07601d900b150105a2251f40f41400000303981d4040e101d0881162200c40c051820401c09190110f2900d0140c06240d0204440740048000503000744000c002600e071a031100d6803248400014071044807030b140b02d01414802c0440911440340f0380001560540c0ea4100d80a641d00c680a280902090858598141d080c0740040b44c0440c4d948812944882002c03041182080180d1205040600383c03103800010541080341e64000b445030125420040c101010103040100d1122111004541c1c160310680c010035040b6691001c0030203000c841c501c49040300240e503004106030704140e0002906da178500240703030340b24001d805592140b0601071032080000700070441d840350301c44040b1144501d6074070300c0300c025011051710110101c0011340941a2113128681040c50a4101810001480305103540c40f6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 545714703 1250 545713453 545713477
    0x30201140c120a1106091e0f10140a15060804082701021011030606210f0f060d03080705030a020c160e010509090c09060f03060a050601180303050906 66
    0x301c0c40082000704040e09190030365078540d51001040b000741510303050300e1210455006103052000031a000140703039650200070711905c1c41909090350041d140400318a1844043d0152600c072001e655182e40c464600b012003001c9080e00340c0d442e038213200c7c22101c0100c068030045401c2001400f40320312400310349902a1064503800e1030410781341e036801d024440d601c08010920380d10f008103030f009590502810742c528892038401d0007a0382400014050901000700325900070a00818aa50fa01c031b0050030584441442d410580340c4d5040008482c001440300325000d118010b1140301049040c202419063302c000d8046c2e0303a55119455010b401c442c5540043c0000113100e03001d024100c2203042c28004041003040d01138009541d140342000c1442da00c03505071300c0386108031410000c1241021002c200c0e2610791808135a482116903034940095080b0078000700440d0144500b0703080051345e1825a00860040e1801d07201c41c040019071500c1481d05410b603000040c0003641c2840900d013207082101c041d1010121031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 545715953 1250 545714703 545714707
    0xc18031612020f1207060210140112030504120f0203240a0b0103061508090c04020c07060c020301090f140601050609180910150e0114010c0221010509010b04050a090b0103020114 78
    0x400050202e00811008804c94202e01c1013000040d40400420522007581e40b010300c00e46034001000944204140318101d02e072840300c00000c0806100b041160003230f004107210000c82c241541010f160100e01214201e0291154005159003002d241d0844180d0900000c0220815900c001884000d40808982c081c141515020f0100e0b008002c40d00e11318080c80300b80d4074900b1134901031440034034001025400600403881001103040f1944046940f0081c1c509034140740d5420242840801c3c01441c00c1d43e000f5200d07260a10b05a020003090b03403c003030300d00d00c00c00c01118910390326503041000038440d508955600ca2010180380820203504440c40c0d0b030007a001800c0c4c036402a5822f8115040d02d07180781e071014024900803020b20440307541940d072074094107141d548280d202032401c00181030b564017502d010b0b210308003004192302c0802d400c034201c99010015100900160070500840c0b8083d00722520039504c1a81000300091078030032079108502d0003580000d0080b00c2a4a540c00545080d10400b00720f0710319100c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 545717203 1250 545715953 545715979
    0x81c060905010611062212020715030c02010c080f06100c02040c09080d080601050d0e1e0d02010c03020c0d1b0602160c150212090402070b0c1803161202 67
    0x10521440c0c0c0200301513201d081c01a03c590b004513040c050000d2403405060000000c01000014681701d40e6100c542c8240d03440703400116032209034904125540311b034200034842d161415240754590000c1891712096002800b08900706001500c180c0d8046840ea500c880039000082d56502e030040c40c400300d40d020340c241894007210315000310b42525655018003022a0b4403000822003054104814120085140f52031006c1d4100b080009109214820603d90120f032110340c0e480380d13450140086103105000004580e0b66a0510200c2620751410081c04030165117410308a24080d030180c0216040302801c400502050607083c10162021403406580c1500380d0860600703c4001071261000b00b82588050107100b25845440ca480c07020508c02d41c01120101d0010004c2404094000400e12442c04802019176244e05034080031600a0080c810040d2104031410700780312440409000400803403039820346418a94650005060346c1d845114024005030755200030401200104170b0881c500c561000b003043c411080c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 545718453 1250 545717203 545717219
    0x303070c0206180a0e091218060307110a050607080702010c0c020415030c0e0f160c06090516030303020409062106050c1b010515011803080726070618081c06 69
    0x485504000d17100343c2c86509001d2400c80400c00d03524200502c51106144c000a52044181c00131800407141c010307a80480440d640380d01941c1d04640a501d0441180c40484007400d0040da14507043d121200271992202c0401c0656106014450031400703243c8405419880390303400c0c0401405007042c0500c0c0d03070f03440d110044001002d038100400240808580e100c1241030400541c0000c0c070000d080c1c8511070350550559003006801c10b0100b508a5042600024110502e0810078101145c58420924103000302c2c9000c4100340d01075001e00180e41c1c0f00102004910740f100207503120400464903208020310482c4581c0001200c0350001d035072203031500e071105003411400450782d0204580f034a00351540303035101e00400a0041340c07046641c602850900c0d10400c0c05401074841c1c0481c2c0e2140c0805403c541001660a00b0f024078584c420541114000e2023020003500c0d10244080c503046031804454240c1400200c000301d102008003440e409420410140c0340030f1400f2480c00d012041c6c0b4540495260320f0300000507a003e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 545719703 1250 545718453 545718469
    0x904050f010503030f0723030a0f090e240301020a020f0111030103050a080307140d060608060a050a0902280c0215030903030606180a030b06010318050d030525020703140303070c020618 81
    0x510703100003503490708002427004e4028801f0325042ca00700018038600308181030030142c502d81c0000c85140e10b1408d0442c40c410812200c4800080260150700024070300e89500d038000303510f080d624940c1c0020031083c44080111100c40c03100b0300c8054643c3d84010a684046445070000710f4219806060862240c040100c0880e4580c0200407841d990550b2400100030b07168000c14481c1d44810103d0713103010614185400140c0c2c0c03460030f016514a15501060706000e802000d00001039118104035614144080c04100600b984040f4800b280210450103c002d4603c80b80c0065034021044030303014505595a203001c0c0090303904070354800d82c050004d05500011544401c50079201544c0a042e0310100b03850000d0014041d5092140703c1100f6103d84000e1001144001c104109a2105860049200e071200d800070314085001c1c41c0980d41071242b080c159881a50001000b03411248178062504400703642c560800d88071300044805101007032566400500600c4d004009104c400c07000c0191041c1d069046000c10844 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 545720953 1250 545719703 545719763
    0x10f02150901050a0c03020c07060e030c09010807091404050307030f0c200103050c0a020a080f0909010605040303140901020d230c03030402031006180923030904050f010503030f07 79
    0x42c0e550703201801a0700b5540e02400300d400c3d00c18242946007644009401d540c621040c4200b80400c40b2203140001195024404207540d80b8004003004095616081d2142c2c0301d0b4036522a9200300d0f80742c0040c0701820f811030700c881442981c100014500340390081e18140c50580c46040d0a4082200c0e406d0b49000140c0c0c04040c0740c3d07940000c07401540b03810f016800058201c07070707014041010304003051202d4107003d54005400d0240580c00222903840c1d0107403a1401502d401414040e03580107402c04000304031070f40e00001410841e8000d54507000c8050324004244503911a2845080c0141c11000350440958001e50300c2c01104100c14035400052107004040c55141e400c03641800085420000034042540303010030042410600e00e40040200f030f031921059101c404401c1d802101502c0c0c644071450140a403040c120426860b4071309246c44200004d00410392207a101c8148944110710b040042a001041c0847e0305060312000b800541c5070280040c8901c020307401c03011040311030710910014003003c0c1421a05078140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 545722203 1250 545720953 545720971
    0x209040911040e06190b040e070605070c140a030f02130f090b09012f1201030804032109091515200c030a1202010f050f060315090c010f0215 62
    0x10300c07610781c100002d40f40e07a041c01c00107582c0080140b0407004450148802c040300700075000200b00f5101000300d0082c207251a000041d0f03000d1480001040c50b048001403a03103030310031032212000c65101d25103560328003041c4200c01d0300000a440103000092a840664018500003050071500080c4401c0c00d50030b803441c042c0300403203c9032211035003001c0040c007000c0217801103151402400485071000c16050b03d66440030101010b0080102c07144850a030380f43c00c40b0b510103858015482c9541e16410b02141c980e000d031004480b480c00903038078040c1101140c51024840c2c01c01d580e6641b4142d140c54080c2d00541151102140001c2e0160300026494038284040152216103440fa00c8130b5072040c40c0c8080c90141d10b42c1d00e440e42604651541025941d000c40d440000a07840340c24105d1289200b02d0880c0101100e82c84421004d241200748911310091341d440c41c3c400d040c224215126804589441c9601c001d09450202542d8404000b0241c290b000fa20341c8030040902c0e00c1110342c41c810100782d0081e22101580c86002c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 545723453 1250 545722203 545722223
    0xf13110d0e06040b071b12200a020d1101120203090f0c0603010e3d1406121306140f0a051302010e01030c0504080714090601092702090409 61
    0x2140000500a00c041c55201102802d0303240350548940c80c2d80040100124200070602148209003042c21854800d82d6400030342e0500308980d41e52014180380401c0e04c12034542e054074140c200d0b1030040002c130380204079405400016604000e5a6840582451a070a81d0522403c2d011a1070300c1c1c0890310255204010039030083c0a0300380655250360506403902645802850108018081d0b00071030007074035410005203040c81000158100030194001c0c0c29880c40d840607036420404070000b10960220505660201e941e001c0821440301c00c1040510940c0c036071040344008800001c01003148050b0510059000b40d02c08102980d40b588086124070701203070340c0c2c0b503100c4040c8248050000c3c14803800307610100b9071110091004003a00081c102820b501c211904240d1608222402203120301d0035140145901c80c01c4907035054031081c4100701c1c0c040a131101e80c041c070706070381c0080d04940c842c1c0a28000c6420b485001c40d0868180c0140c08984501040003400868003042500040d0b00c0302d02c036240e0744a0180d49049 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 545724703 1250 545723453 545723467
    0x1f0204080307050c090604060f0608090a02040203040b06030c010504180f14040b0106090e10030807030e0a060c0212161e0302131a0f0f040906060305060c030708240f1311 75
    0x103d611703005000140140e280c010305000f81056864000161003403800c0c4800181c0c0d528803c149050710902c4002d4200e400401400108040b00c080c050180d14101d00303445404400300300444081c020ba210711481001040c041d0b140c50754841c1e01c0032aa907401003502194070035070300c030342420340820940b0104d505100340c1d4010800d440e0b01c00e10240181030509444151790410120300d5a0412850201810849001405004140c016018044c0041c0c024013040c7d0a1035132040e02401c0a01d455005900a21100000c0c0000c4100440c02c80b943c00d0880e245154901d081c02c0c2c00410444080490700901d00c00e5070404009a03031030150362422032030311100c0410402280200041c07000c4041800c00d024080d131071503a00c502e542c1d2040b00a102e00e001c7d00d001503031844e1804c2500140526a0002d8214040e94050002a4a02d10000c500c100b115031200c5096403622160501b980e00b03c05582950b131804c50014208a103802c810703041840740d001308800c6030041035a40650846980300760b0700d80c0040d400a01c113 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 545725953 1250 545724703 545724709
    0x513030b190b010504090f0f0f020a0f020601050306040b071115040c0e040201170a0204030c080109020f0306010305030f030709090c090905100501050313210e0906121f0204080307050c 81
    0x4006503201c0700005001549141001030034034021380c024164680c1e141c245d801d4142d2850307400200a001c80700420700c800c03240c24222100943c414071240300004c400c6640c000001d03000040702d9040b210054010001d81d640c54950454025029101008010300111002e4441d4001c03c0402c2040d2540a05c0300e00d03604003131910041e49215039000c209050f80c00e50401c800b40c0e80000c1c0300001c451845142005541c0c900036410004e2041d500020643c10b500c810100308801d0540c00b020165100741c45e5036046503482800c0540d035407000d1000414940c0208004400d03d4810360117140c100b846030811090086c0c88844a1040d5501000000b000801e039240c01c01c164080e5000d11038200304115000c414403810000002c0c410b21006000c6c000000441c078018007004540b402004041001c490b0511f54203200481c02004442ca40060754400c00b00800400ca00c1d15000380340c0c080c1c4811510042c41400300814034079046500302c1c0e1480700c03559400e100003e2180800d20003000043e1140c2e0162186007484010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 545727203 1250 545725953 545725981
    0x402070c0b0d110a090807060c0503031f05060c03130803070b190605100f080708150d080702060f0408061506070201030504020103093504060f08100320010e0301090b0a0c0513030b 79
    0x1c50030400c0012715608021540110449801c41d0311039640403899201c54407580b0343ca8506034001360308a000043c1961070000c000c0094000400da80c0b85100c0700c00ea5442c8003c0da24000c0c281702a1084040030040f071160100352120076000c0c001c2e0034000c0b561980d508006280420007100310004503201c4440d03007100680c090070701c41c1c1c09a0142003811590a04106c481080507040c0c6156009402e01d150b8803083c82061401c3d615056402440c50790b4032022030b40700c52005d0b04035104d1141d10f40300306004500c0044140c01900e05820000e04080d081125a800440140c500944180e06044e5a4111407000c02e00540c006040441c41c0b21440227520750b10008101d031040b08075856801c4c0d4009010a2010326440402280101c956160015468a891050f4612442180c4c80286603503403169003042c00034224031501e080718034243c0700c040c03200355070100345802d940703010f0801414103505000040c0002c0381644000c0c403180760b600d081420301c58101c0040c20401150b40041c1c440707280365070030000340c0d04207400c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 545728453 1250 545727203 545727209
    0x60601020f06070e0d0c090c0908060f040303052a090307140d030809070e100e1e0402120f010e060603060106020a0c090c05220602010b0402070c0b0d110a090807 71
    0x200030050030803500c07000e0b511180042e2507902040501e04d801026136803050048203101c3c1e001109103c00c2030f80e03400440002d03c40c508420740030400500d80003030051408152503110300300c11800c80245686941c0c044004080080500d02e81201c840308810740700c100303900500c08030346070254003641d200c0d0044101894004c41e5841076040700011200404282c84400c696080140e15080140304c0e9250b4000c064280f81e0340d6006108440204410007000048558a0200702c4400781780c0042c0c6515140c103030f20068454218114903074060540490014140082e071010041c0800090303607130b4045001780c01c900f03454440600213243d03484041400880c0c5010700403103004000c6400107042015182d9211040065517100c0c0c1d0003241c0c0d84594085249002e1022580c0c4a44056904805108540050b01650845000e14001507190807030000e0720307080510803540c0d0a6003104200304403a190984c0c4150650040c008103034460b440c5c80900610000e02406003045a907540c503400400c50900040d07500c0c04000c3d0f4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 545729703 1250 545728453 545728457
    0xe09073c03030e0d0c12020301090209040317010e0105030309120309180915090d0e150c010c0e09060f150d09080c0d08040807030c0201090512010204090b0409081c0605040c030c02060601 82
    0x22664400140703845c05c550204c482c50354031306140c1c103000e000181c01001d21180194100d0b140f141040101540002030005138071020207489420390700c55000c1d0910701824096103801d5442013003e6603a034a81084240040781106044a19140c80071021407007404540b8020500001c54405101661405000000c60010841804030961501402956541c02e43c4072500040c400c1009a1003203981341c04208004050329450030035520104a40e01c10b0003886038115101c00150012803107900c625203035510034010000200036241c40c140c000e00304614023038180400b0094400c10440c000d030501842c00703040d12450040c5c10142c1c1303403e811b400460415020700d03620401c01c860b0a007000009505c1905030740c04030f9054074124144c2c030b04c0c91005807054803541c0c01140d0321400440c8200340d1228150002c0c0140c9485581c1409280c1880382400203403015400020319000c3c0601c080c07100b044500051000da1a1000130114442783d541d4042800c40e90044001d00029440b0460030203030640401c0502d030026002c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 545730953 1250 545729703 545729719
    0x2180409080a110c09040f05060f040302061f080105100f09060303080114030a05390a0e0709030618030305071803150e0102030a0c090e09073c03030e 66
    0x559580240344240041c82d0305100c160315060741d10b10000c000039001c00030060142c52242c100b6040114480000a41c1121544030301c000160013040e084503802d002c1da5040e0024070650b291102da0003815100c941d82c12071042c1070306600090a8400340910f03800313072800300d103041c680a0404690840141458105198840c02c0c00b81c02c00000f079200c00d1880c1150755a402100000b20312100280c20b10300f9200020b41107214444a031010071200300102801c20030301c0d10318041c040b07408001c40c903100f4808104013070b88010840002c2140038101001c40707a015500c1d00e40319207410303141d030340b008122204000380030400001e4012103030426805208041c1c00c202e050a00c1d2440e955a102101d000074998040246110307041d035601000310295410900070707881004020b6440e854000c13552002040490003000003d1400003000805048410301a401802000c0280c60801c0c00d160f151a000b070011400004061078040300d07440c40c45514404907100c40c0c6503000600106240d81001000c485140799458400c001c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 545732203 1250 545730953 545730971
    0x10b03010e2203030f021614010c1b11030a080c010501060e0f03030a03090219080a11090f1501140c0d1404051c170301060807080a0504031728021804 66
    0x100304610b420250f06140204c1c13100160b0070380340003034096550703101c41000f1410040070410041880c1d0710301182110008101010311503204541120102800549610400704030901141183c0c0c1c40090304c6100ae42110458809540c0703517080c0b5030110304600200e940d40c0c1c0050169541c452080300d0f030b106085a058804d41c24000000c1d880388550444a814036903110010800c64466203c1d15503014035042c41640036650300c2140e40c0d11008058404ca606036080310350000c841c03611003c07036401940920516002c41d07452060744a01c0802c0420218140103000a84140b04410000100301c60703090100641703071520200d000680f50001a502c8162201810710051040da124510701c4252043c101c480100900b0721800e0403490082548400b10040703200000200d4081d420100890140f1420754596032159940350091003100c0083e100100003c4600100d1410070405512154000000304210005485201200c4402240c1d0b50901010560007040d10700b2640312401d041031041205039030038002215 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 545733453 1250 545732203 545732251
    0xf061803020a110f0105030a1a060301060c02040b031b1908060a0207020f01092301090f0602010203040203060f0f010e0a180c0807081b1009090608010621032f0105010b03010e 77
    0xa081103816503032544649c640001000310a420410060001a5a540c40e08801411150303503000c140e00907400e003084040e4504001a6419941d0b1030307943d81d254291850000c201d41c0441c41d00380c1c4010701c143e140e00811141c4050020341d0207000010700c0140e449850f48144a0a071898441241c18000003840030000106030741071640404400d0441150b1440c12000141c80004880e0841e41d14080f0084010a250360154000c5014a008904840a0b039990350b200020081089801055060400004000c490907200d03902e608004c1142c004641c18424151a8201c1000650280c83c4410308003010000001d0a0000c08041c00100002e04107800700c0403030b03000c4150f24001000b809000c03003104001c0342074451320749900540380c2500305000c03003540c4030021806000e242c0260400441002c01c28a0100c1044500d03250304c2da0306031550051a80e10b45003155003038080b4180007000c5880703c15107100d070110a1080d07901800c0d01c0c020690701c80d414074605007010b240003440340c401c40380305030100e60000c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 545734703 1250 545733453 545733457
    0x21b030a0c0b0726041e081c0b06120a0506040c0e0d0f020d062a0804020f01030b0301020d061d01061704020a090c11010c0305130f061803020a110f0105 67
    0xd9048100d001250302d80507002c0741c42c081960500800150b0020782d462400341c0004c1382da0701803401043d0180c81d416145e518140c8840b0f00200050494104101d8403d80c00c44001c1031005a4141407400a819140c800204042ea4072140071a01e10314030500400401c42d04a2003440e801c02810b44040100011410300504400e50361540d0780d11070ba566000720010044908550701415078050680302e550b8019150035000781240e50345494421210040d500412032100604080d01401a52040748a88803a002c2c000d007045101c25190415856855032100c0d070b1000d00007841959142407000806500d0304408112240c1d050496240200c2541c004026850344106030346903c1c0c042480b00822600d580c400180380e601ca40d0302c11012182800e001c0441c140c1c0054401c0310941342c04000384040f124040c011030480368106c03520040d1204040d144004622001040720809200c2c400010310402c24410a0540d9456860110016885105e200d82001540c0440318a5a00266140e203660749154001034024 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 545735953 1250 545734703 545734727
    0x20f0106060c0807050715090e0c03070504090b1f0f0e0a0b1209030c15060310090c091d0105010308071b05130c05070b100603110426100c03021b030a 66
    0x603003404601d04c014450180714030310092140e041004408030b884100034143c105184102900d4080180000e17800d00c0200e07040f80d20031210369440c1c0d8601070401d40481c0082c04080c0c0130302c1e0045852184014441402c04980110030381e88c0e1124658030b0005100100f20010101115002d0700314128108a2100d141003900c155100c91601e41c603440d41c0700702c8951700e14010343c00c0c54030705031049034404407510021001543c050501a000d80d4103601741854904c05950140c50000c3c00c9003940402006500c1c8241d0010300c2c04000310098210b19907021005a0940d0420382003500e085800140c0c150030404644100c06075002d40c124909449803400b0005989072060000086000d52251030032a00d403482030048901d10355009200d5895820003010740422044c071809114042443e000600400070340f41c0381a01c0883e0300309060000d035205480064101a030240702c641169125008080c044400c8602030050400a00c2d600141c8807000c0402c481101c0c41c000402a601d504100034600c01036a0204503441c1d8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 545737203 1250 545735953 545735963
    0x106031e021306090b040c021c08060604030b09070501020c030a0503041401110604151109030a230607030507021212040308090319080a05100f060804060605150a020f0106060c 77
    0x1248826002044646000b0003400c024207141200c0800d249a081d40070785400e540586003002070702c0e20800c1c141e9030b41401d0080d00d581c1c40030714842ca1040c00e128881e1907900c0000940808d083c2643ea5454000e85403041d01c51075416003104006004a590400c1010305001040740100800300300c42d201e05071a446180201c00341c100c00846003104690107446588d009400d6601110000e1920b424030301c00d914001414081104d09102444004040c0c0b0f0065842e0703641c00070003070040170344142c1d40d071416030148400c2228503607100b1000458070356003030200e28803d1b4919140801d091a011000074241130302040f180118441c00c1c0000234070500c2c1d16049070b621990506281c8511b848000205195020780401c54820780213a580716501d00e41c0c000480350281030002000e00c00c0f0f0702c502e02c0d1504564181d000740101044401c078100540c3d4400d40f00150000d006400c00141d40751103001140d4050440c2243c2000c0100005008a005604005941e03080720b152008000c1c0c14203010004155402075040540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 545738453 1250 545737203 545737253
    0xb0403080904060b0d050f010b1c050a0b0406031b05010906050901030c200304050118061b1e0c0e07030e06011a1324090b0d050403030b13020301090b03010603 70
    0xd150302c581d44a4405040d40c29001500c1c0e0006440507401382c0021a01d450000b240300c000020364914030700546101720101e607104200304a8403420b00e0300901d401401c2a40d400c2c1c0f5541c80480e691a140f1030f00c400703507014040242000800e800c100211940581c8080d04004100c0820048180e011042c0c07000c0c1002441c0204400c80a00301c1150740c1c08442201891074040402d60384540400000100100d50080c0c80741c000400c50060161040c44c51403042e0404500020421046064004144d0910b14402c0d4446c0c6401201c0b0307600c1c0d90f10740e88020300458820300032450910110b03030031441044d40028245000d22145445601d09515504188644600464142080c0350814011000d844014807940088404242d50310320050034003074030070401043c0780300000010300b09601c10300f10b400583d41d0b080051850a00d0901c0c415008110050069041603500e4000f4074407a61101900240c016013040d014ae02c95040024a004885165003203607c2a85015010000221000c400d404030781448880c1d04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 545739703 1250 545738453 545738467
    0x7120c02010c050106140a060c080304060903180305101a0d1511030f0105190e010e251701090e1221010308071205071110110d0905041103010b040308 66
    0x39034894481d00d00240f25508110011844e426100c00302d1003007050480e8a00e000664403107094590501a0f038025004d20750400010300424207079080b0002c0300c2d00c01e14180703c0f20102401846603000164000300e40c41d421a030100a01d0307403083d008600400402c3d000384032002d5504400a01840d0300e80800034040b18000c00900380d010700c07940c01032000807003032050550b032450556284040c5440c240500ba01c200030341c1d803940590389280f140200c165034855203000344c0ca0b402c02c07200b2005098001c000e09a45460007040d035480070b020020219034585a0f444402c408014a10075a818240c141c012075002c0b403516014842444000400884070629803a6003940d544001080486515000003d0720f04000e00c400008208403800004201550041031003a0020f4116082268244151513014040916000d4056200e1a00500d2000d203100d017403c0940b0303628512440d042c20318055155081c0840c0c4460740c00c0282c1d0400c0e0180d43c0d488c881400d42d0628640c10901c0c040030500890001500804011500c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 545740953 1250 545739703 545739707
    0x50115030c030b2806020f060c09040227090a0b03030706020f04050d1a0702010c0509130b090c071a130b0711030f030a0e16060c02011407121407120c0201 68
    0x4243c8016014113a0905140114400c0203410300e801a01440e5003050240003900c244041500040144640080c0040740c0324240030340c0c1d00703401252140342c0c0700342c0c208a0109603100c2c108252010000c0c3c2e42829581c000c003441088520900103228000250900611080316640402140d9006901420040c3c4403030f061009120300b40201d402c0150811500a1203000740040401e000031220b074044548c0740c050f03036044c030200c1c2a46c11890241c40071802c180211082460703c5d88444220460018000401c01607080000780c890000380d9090810f208009500c0061028001800280044000060145041c00038040c03008101c0100040c140310209070200d101184580019004c5808a80442e62100003400107024540d00503604031400c989410005030241c040407031400f110b0302c0c1150603002000e01e461020740e407090700703d4002c9041016681c2814010401d920140650b28040d01000d60307003a9070300720040c000003100100114504803d10510700051541000310910301c600340303072030280c4002900c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 545742203 1250 545740953 545740961
    0xa03150f060314010e190b010e0601020f100221060f0402090a0e07020102090a0e0402031e010213030f0605010b0f030a0c21240807330c03090603050115030c03 70
    0x4103c18001400c1808030001508a42101c404e80d1040d80c100444403460030180c2030405100600449554004002585e01c0600641c0e0100041c01a00c03008116004020f04203010704600e203c1c03440d4080784006040c070b543c00008160f1404111550918142040041c1f114098a4405449940c0004801803551101035a160040103400b0948140d4201444064040c0d00141110b500910348078500050141d09004400d006d242c000e40034059929000d0070800d001c605013520000c0784d41d0204000902903000c0740d8408011030188401c00d01444191602600351030381a0b0200c1344890050100340d44000c007000803250071140c00100021509282e0350144c400c811020320b141c10380d4140031a442800d0341150401e00c00340d00d1740070401104010303540065154007232501424072150f101802c1408809008a0310a1031041051110441e8405040d03e04002c5602416100e002401c1d0341202c00800d50060700303070300180806060078801c0d581440d4001840c3e0700c080c82d19a08140d00c45404420050203548 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 545743453 1250 545742203 545742209
    0x230607051903030f0f06052404270c11030d0b0d0609061a0307180e070510050a0206060102031608090112051617060f0904030e041d0c0a03150f06 64
    0x8003103000903103420043c000f004113111414000707082c01841c014030001c42c403401043c1ea00c0205515041c10004c07110104205105d40180389042c01048085100c0488080702c00141c034901000040000c01d4120800584081c4004801400b068610710580100c01005072180c01d4140140000d4195980300090460102103002508452402040b00f060215980105020144560f020700c40c06c4242000d00d035503500140b003000701607001440100f02c510340a4201c40b003008103040c200c810054650002500e065010700c030040c0801c800149803410540c06000241c1d0107102400910704040a03024200d044046500c130003420304000050004440c0e0080c050049503500102c0c0403c480d00e4800300300100003444c81c0301d02c404569902d0001c14603404184640f440384402400e203000c0e002c210401e100d10350308060821401d01a9030540c08080b51a188290742d0803150020341071b02c3c4441c207184507030f080100035400280212000d80090001c54606500b0000c3e9200055000400031140510380c8002d200c160 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 545744703 1250 545743453 545743483
    0xb1c06030b221b0311010e062704020c010e191208180d02030d060b0421140a05011d030307020601030b060406031b030209010623091503100f23060705 66
    0x1488090300985a07101e030000e0301d00c00c4141c442804100c1c00151101c0c40c800c0382c1c0607803102d02001295280380280700c0c09c003881c10b00e114840555101c12000501641c000c4008407440c1c1c0c2d560070a4a91114003080104800200406d00c41c489840c242c0341c641480c4810941e001c2403080d41b2012410380324108201245014008080e90444034840704020348a81c004090b18420714103001d00070a44401550440782281c07010008000e4044658142080d08440380600fa202c42d4544101030703911410611074441d00a10900c000900281640b0120b982c56220200003030720359105008008005800040ca941525008061801256104000900500072075040102000c0d1034110607188214121018026603208030f51142c01680c0380c0300110f8040c21185104020400081c5048101c0017980008100041015106508101c002c0b450500d49038420744070311a060058940400c2684454244c000150801d500c0b030f4200120602d00a0303900e03000700d03800d0600c074150001300720042003001c00091035850f82c51 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 545745953 1250 545744703 545744723
    0x2190f12081911060114010206150604080304030c05090f04030813051c0503040b1501120f02120c0c0705031b011103040f0b030106030509070617130206040b1c06030b22 74
    0x540b4010700303040c42105001c3c8503103e03400020440080c4070603006c141d410103034014816962074800701900c070340c00340b01120b401c80810040400d0341c0d58144000c00c081c41c02554080022490041440008070004021441c0c4c1401c8034180400654000c10a5400481e80c0001c20051403207400c00c40d05001b0710503048503035903200c00c818480e00c50308140594404c500440f0141c03401e5a6a480704698070780300c82c200b1400030300340c0081c003002500c150b8001245480d03941d0300107040c000000b200e03c08059041d01c03005291000071a1480c001c000400128003d0041030b40038011030f200e220801c4000600c944a2103051000d1000703c6aa801420002d40c0c000f070403000304005149036255200941d942c02800380340c000a06100010343c580d440000d21354120703602076131220341c1c83c1c03000744500708031300e4024010f003041c82240e00303074900035980b4000540098080e40c1c04a55a41741d41005a144c501c100114400103c0d0030817408102148660104582c060a00c0c00c1900341d495aa1040010214592000401480322 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 545747203 1250 545745953 545745997
    0xf0615080d260105090f0c090621130308010504020f0d090308040c0b0304050d0e060c0d03020c0d0804051902060d05100315140a1112011202190f1208 66
    0x4814085480c08180030302c03001494030400c54028801074240034854102c990040860051402c1410455000c031003100250f0920041400290007a4895078042c040340d401074500e10a8060800c01c066044036400c0ca110101d07960302d540203010954144a01449198089215100600d02504803420740282c50001c0154018625001c1d0540300103580035211401003d8004c1742c03aa03038980840e80203035001801070940740b03072412044800c84080c101d06604090f040c00385000001080010000151440c1c03000358403004000c1e503140c0740c0400c1440e41010450440c0c10312002c90004200c2c06440749185540b0011440a800810720320b105020754012040e00d007004100820b90403078050010780b4401e4440d4550248500045002c4d20032400814542e2900d00000ca0320f00c24959010350181d4846136512410711081d1030740e0940c07680090b4480b4064540904250f011850030f034000066490009045603101810542d890075031608600410000d01a000441c400b03022181e000d907600610042000185032503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 545748453 1250 545747203 545747207
    0xd0212101e14072f160311030a02010c15021216090501050f030a09150e0102090906040606090b07020103110c0c030d03021e090a0b0406050a0905030303040f0615080d 73
    0x503684114200491525142100c41c41194240360f010706215558a400c00384e2107206000c0310840b0a20000700c40b0070807114034486000c00d00201500748410100c401d07a041c550b08095119079410311f000d600c2038001c241c1010061380c00050440c2030f5504010807008902080300408000c1c4943e0000700000e02e0300d441004032003120f000c16180702e20166943c901e1240d50b9080150388600034402100c0d41038400b0700001e104404140d0048c50b2490240da080d11200a203052698202c581050041c02680d40002d89110b45080c045e01031508138800395400c004840c9081d00083c24072000d03002e2680c64440018140c1d0a5a110741c204681c00b40f80381ca042ea540351200c446040e941c1d181100300d98041d001d5034078900c1d44a40244292035094510403800a26079020101d00496a0301008a50b81d02c0410100c0110b0000c20940107800034002e40c0d140d030f0303070345801d0404042c20096165000074842d510400410001071400e0881c542001d5001d100450091401210b0500d4a143c0d40c0004c1458031440e54051411a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 545749703 1250 545748453 545748491
    0x9080406020c030111250213230603031b0307120e01180e06010516050609061e19020f0706110904060803030906160504030f05060103020406140d021210 67
    0x24115400b102d041408902c14142a6402050102e4030140305103c200701d145d074901646101400071038449002c56600e64001484002c0a1610291003a0fa59450749401c80003848142c2480c2442e10030400540b915000095903445401c80c1ca0580000811140090010400070744d203809511100045404c0f40281c8001c2605501880e440d0009007601e0b00c009440184002e4581030f04d444e0020b180341c566503403006440c0341e44524613480f8003100c00c1c40c0140111b50107000e280c0c0140200c10141800d03040c000104041d01410402c0d10101441420034024008043c000440000e121035401607202c000098990b980e50103114405003086007400000491444290000c287d0b26504070340400010740c0300d07940d042e542d01080716044030b15423000d00818444009407170708980022003480c0845c54a5100c0c2d803600391312007036000d045920303500910040c0304501e094020b235405054208080140c0120000004030404000c04010703000e200c0c2070a58050520003800f400882c010707605018001c0e480707600b00300d000c58 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 545750953 1250 545749703 545749709
    0x3070f02120d0c0b060402090109090209032b0201050705130905041707140f150109020304020a031b09050a020a0f0e0109090c08041403040f0603020903010f050a0e0d020c031e01020d090804 83
    0x4c0c0c41c101c001400380ca031034403d5810940040c3d4403099a9400c0030341040080d80000d1000ba4140b0448078143d840c680c02a44802805c104400070382014840100084d0945a000d001300b0148001401001c00e812403d0444408407420304c0b0021500307856a00b844d07c0c4c1c102c02c5952941030040e0025442c4140f0031288892040b07c03901d64101c8000744607004000d51950102450896100d4940004124184541d00999003040c0002d00510519543e9501c04c040300c1d060883c408002e8064810421000c101c0748900b680c454100001540380130000d0300c009041030301c0c591840d0300b44003c1c4500c02509034481c8a038603010b040b208000b00012707411100050042c5c4030031a400ca0759664102d0247c48180004419201143e6840300d88040580c200103041d006034000040c5c80390550340e546100e00c0804003500445005060160001582c400703283c814070b040500d10180c00055500425113024582c40000d03c0d400900300951010342c40e010012070b44c901a118810150102600b40401d89040c8403101d4001c10803 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 545752203 1250 545750953 545750963
    0x3060609131a0c0a021e150612070807150e0a0332010905061e0610170f06211213080a050312091f0f14011e08030c03070f02120d0c 58
    0x42040c3c403428100102c140b0386c1150740540000728a8a420012010510b800c954000c00c500340d00700c1e0002841d460000158003005240d80000c100300700a000d9030007030701c00c0341010b8504a00701480303c901280355032800340300c010b100070040b0440c2c200035a08060040b1f141c81c02034100427092204050303010f0207010307640c1040d1350700e000d80400700e0803000310b500e10080c0040d068018940a90307110350800034040e40c156100d10600c115071020803044218900c03400d2044d1143c904400f40c0c0c0c2800070903c00c0310342004a0310760707072010492082d01c418000050341c040100c1c51360b40000d580c1c1da952070403442071170310710382c0825480c0c0300e5400414108140400130b804035084807210b8803065075404114640e0340c00112070122403015918100d00001209420141300f14400c44030121300207180307102e8070b40a41001d0740040d04850b00099010f0f880c2d00b4a800d1880206070310381c0190b040c01d0345007100c0354991040201c006c2c041e2a80041c5c0204640720700c030102c12034625500036a07120076411400030306002d070701410440d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 545753453 1250 545752203 545752213
    0x3101b110f0c090c12011e140a0b0901090806010f0e070c0b060f010c080c0706030c1d09090f0f01021206040e210f16050c03060609131a0c0a02 63
    0x419a40c0016480d450841c958000c08101060409000602001414820a80030708028444289000000c1240240180340300100254a401c40004800c81d05411400c10b812240c140b413080396030b80c80c507480191158518240d5a40c001301c2c0c0140c41d56111039003d41118059040000b400b000003100190403500304040300030385036a4500e0200c2d0311210b00360f030081c01c2d400000c0c003052440c284605002001c004c10b040c001c0c0e003848076403159070303c0e50000b00d440c12841e48400400d12010b5494010300c0040c11180c1082658410f501d500a240b0441c140485400340c183c5500140042c0c00802c0281440000041540e0390035210b102c045000c1e40c010710000700d19a038143c01003101403c01e03105000307010b00c1c0b03407010b03000030110381c0c062602040100d01c0e240f02540061100d40818040c0d103008060308182248280c90295040c54400d0901c80029025842034201c807003040403540ba0744155a9010320420051400a2000e00d450010341a0700c4031074150203401c2000300410201881c0042802903503e8003211 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 545754703 1250 545753453 545753477
    0x601080a0b031f0504200d061a0d0f02011418040f020909090303220308060105030a0b15070c08160302120106120c0311030d14090a03022e030b030304030f0203101b 72
    0xa800303c0b44040140c1e4015083c0c00c166408559164421001120908400480b0340d014100250f0200032811041d030700c134800028494110342e0440c04400cec0b40449600114242030071001240340341d1240e594101d01844d152001e00700c031402c0a078112040500020100b51507030400261035540c0f070f0011140d04401401c1410714200c0a80d4a40c2c1c1c1d8400c2580c5681c6140c0c0681d50070004491681014005480380f584520700902c159450b070300d554402204003225191102540d081122440318582e2000c1e4203604080c0c0e075030f030130006580140b00c00d4070340544405444180464003a0300409e00e69000041c01c0c0c240c2c150382d00401020403001c1e8102e902540741000754030f8908042503100c02903001c180020902484450142d50300c06009072074030510040c031140d400756a039000705a03507900c0c070f48007100c49880c42400307881c0510001401d07c0d44140286003c024404040300032950721701c40ca00010b4090030030010907074110755042100201c0500d04943c14030034000b2102c0307502020b405081e11a07001c103c4001ea29 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 545755953 1250 545754703 545754743
    0xf030601030b090714060405011d100519030b09180a140c0a050102030307120f0209030304090c030c020d0207061224060f0309021810030203060c040303170601080a0b031f0504 77
    0x114109041c002c086515151512006480c125890142b554000c07200ca4089015980c0303104c004d09484d121511040e954810060710625208001084101414940741c8a04216244c1c600004c2c2d1100c1144032401c0142490944e0500d403040400d4020511140c3c0300005900150200d80c80b00180c034103941c9901c0003601d80c80103a0310390000f19010300008408c0e00c0302c40c1c1c00801a40105c40754064010006107003600301408203041d40e019400400605413601c41c90340b2901c0e8140b081c1698200f1501c00342074401c001c128000c1d214130705440390500b00100442c000d00d490080b0b41c03080c034030750314520900c41c403003002801d055030820403604c1030101003020b420001040714085e0061450761030f8024480c0301c02c03100e940d4403003c945402924100c2c90881001000c00181c604211007406402118a102d40f514614500100b01c4445010080c403480c1416040c0300351a60000c0c85140c0114404401095a52500300841d04e0b12911b40f50101c1003040c00c9104603480304250380203a001d58001c0d40000e40980504a40d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 545757203 1250 545755953 545755979
    0x40216330603051f021b01090c051203120702070e070807080703150501050d02091503100909030c1e0209270106051804050a080304210e0603150f030601030b0907 71
    0xb019000350089900f082c5031039140c1403040289404c9420050900c0700c0701207004e45c506c40e41ca80440c1944e6440d03030b400c030034003080040c0000104401c6440c03401880091800580328012080582e010b0203660001c01c04280c001d001c440302a0a035100b02400a1501ea0340081003400103403002c00103e009100480d00040c4a8011074030002858510a290585070200446169011040d00d0032465801d0010034451b0ba1101000c1454a0100004a40341d080010341c170555a00b0aa102408248c0f0704070400001030382040301d03085560342000300070a9045007117134640558038104000a500400711800c01003500c58400344003d0764080c40c402009070b056081c1c455400c0343d00900400e42d01003855a1440050200701a40c039a000340300c1d500b41c4601d071000d55144e201d02e4000f51401c54007800b2001e203904080c110741e803990158024900d40303603490880c682c012a003584000707480d04600100d83c0701000c4042d01d4200100703c6034100a000c40b8071941e1760b800c003403041c40010386001102d4014900000781c17440c0c03940c1c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 545758453 1250 545757203 545757209
    0x606030501050411180714072306100801140a0218090708100e0c160507120507030b1501080606030a09080c070918080a03180222050c070f020402163306 67
    0x2c0e0207001f20100c2400e17820741e03000802c0890b0b4503040d4a0441c0b1240c2a841e440748032000c401e20040a0506002d2056201c0910a4201c448261315101070303018030f000c081600d00d8010b81c0c0c240e80103a40344000660030b42d40c05840c0c3c9485030069a0700e0103110301942d004e044284136803403040b242c0d0b014a03160300446941510a4600b200e00d1441030094907080046107210f840c1d10b07031061040340c0041e40d072804c00110320b07042180291503035009210704109014144151591050864140034409901040003824910001c1c0c407290059001100260b16420664000d88425400c000200d46600e505240f856481c0c149019081c001800c00f40c03540703584032100c1744d0081c0b01035200100e5400c00c0c00c4002c00703e006056110441e8024204100c40c940961141180741c40702082c42c840c140b602220021448082e168080c050310324500e810020140407920391a000740b122a8110f4000da40c440ea0504090090201e05102900385168501000c0200350032490008035404c41c5075504494030070048420007112003d01c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 545759703 1250 545758453 545758457
    0x9011508010b0f1902030307090609081c0203040504021305042a0c02030c0603010b1908010f060509060f0408070807121e0c0b0a050912030f09010c06060305010504111807 75
    0x8014020807000c007000e8821500c0c20f44410b800e02c80c0721464110030310000ba10180250b00008180620960f018880c0c6000d0401030078180051440c042c54142c2e1881c1c0d40d900040a00d09500c09000c010344248100e400800c0010010b42d203070041e815122a0020940c82694800d500d0241c490000c0322409010101129134a00710000400c0140300554002c04410000c90f03140c025030510649680c0c0b171384051070103017203400005a25218051a403040036000e106501c3d0074050440300400c8444460707a04d20f400d6500c03d1901030b4480d84500041113030b5000c0d19032500d0805501045c089040c11000801d4011600b151007140d01450f920059134111550441003d08200d40c2c58604405103449403d21580c0d031445803010403041a80ca40c13001e6110307000880351400142000440081c1440c00c840c040b840d5602d94405149028020420440d040c403031001c005040c04901140744041c000b440e8040e070000c40d0840000d00180c42c0900e81041c100d0f00c00700c0788030303c0350300b05200c51180301c014808a984205070603 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 545760953 1250 545759703 545759717
    0x16171207020603040503040e0103030f031409060712021e0c0d051c050601110f062d15030a0f0506010f1e0311040209040e0c0114130e100801050f0402090115 69
    0x364082c0007081c3e00003401a616444200300005000c4041c06c5201e0083d802641c410f22070108040c0010261071071420129200c1403000c080c8000b4803c041109a00200d40d410a81e43c01541207510502a002d0b400b012a0760b8120301c040d0000e20140c80005140c5c0341d030700e541035601d0414040c1c819a170364002c800e490303020b08140c603040742c3d000300b02940400e0300400f05045c411401100d001e55245841d062100004d42d030742143d010b0002948062050500030325404001100c00300d6448001d1139010340040c2210041da16061074075134251014444a502140c1000741c08485a6090901c1c81c1d0340c0800317200381b00144004100026408611003001d5100d21500d04400c0e070458a141c9070701e01d40300500c60896502540c01c02c5410001d603100e1048914800e29040604411210600003403c0c0581e281903565031004100b041220640c502e09500c0c0940d510280c00d40081e031104020005100000d0300503181c250318007000d028a45d81c0d08032285124a01c205c40510641c0c2e00c440c2c0041203031300740785800e4010500d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 545762203 1250 545760953 545760967
    0x1008070b030106050d090605041505010603180b0a320703020705030703111204090b04060902090612041a07051206030706120203181c140301140108090f161712 70
    0x215400401490780c1d00320011840306c0c03080e00d881c000c450041c0c60803900552540082e26044071140500e500408541c20204030b01d0a12081e0525801240f00000344008081c20004214000d07603440040850307400b44006c2e50400051011030f83c81d60301188464044d030069400107180301d229000700c03883c1550107409141800d8995801342c035541088929180c41e0300680e806a0000c104c0300c0302820040000705408200311001c1c8041c4000c55003190004010107004200b040510784982c01112032914100000c402d0303e1780c541c2040c0010307602002805020040700401c1c001110f5004016102508245802e0041074640904040ea188901c0c851500841c0c0200e6103001c10b1201a40511360042c5582c0703140c5d0904414007135203410300007010180080a84045e40aa00d0542c0c030001200c2e6441000300424a954103003900c1e181000402c1210b6030400c030045c40054402030042c40103492514142e0103c038041711410b1006281d0304c4240c091b41c40907c0343d0244d6000e2448000900b8003e09010038181031505007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 545763453 1250 545762203 545762207
    0x11401171903050403141e0c01080a05010f0b030c07020301150501021c140f040f030b010f0f0506160305090d05010c0e09190c1106070306090e030310140d0b09061008070b030106 78
    0x6c51584030751241d00900c1c0c42c030724085840003a45d441540100d0b025008800c402000505005c10251104841e10300e0140140702c0000220003140950399a60102512a85c03400201301d4284101c0e640290075508008045d60000d140f400c017001a602d0076001e94030550140d0b12404000b20011310664002480c01210000042061000385428000d90326550300e4152a0810501480c105600443e00340300c6010041155030222030b54030001d000e242d00a901224034007400074285c0e0003203c0c001c4004040c800100810140604116490704c0009403004141020398103185000f441172000250106440d103a42d41424034004c482c0b18442e500e15810881190f4413031030310303500814421514000340b01e2130a00d4892507800c104030f803c2c45029540e80104200f0305003a082c0e000d96580100c00c004550092042c0400840710390511400d4510160034568004100342c005800c1c503c101901815034a8001c2c1801014503010406605c503101080e0ba0748034855407200855540c0d6200d105030000c0b61030610050058034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 545764703 1250 545763453 545763473
    0x14040b270411181618080f0706050403080415050702090a0603060c0219290a1b0e061e16111207150c0501060e0703051f080a03050c011401171903050403 67
    0x203801d49491400d00b64030380785200082c42c0c0c1740c01005040d880001f181141c0c2c10100030502c0500002e02d001414a86581d0711501e4900442c040d206c030000c001082104814821000d650480d90020300140181c01c03c40f880d00c0043c807903800240c3d12103050441d074100481c00015034103294128140c42c50b12101d19615105100c54003100c48000d101e043d22074480409003281c54650042000038400900b020b600c40b00d024a03081425900021b100c058442150f0303a42c4d690040d1200007410400344101c10289002c0c0120320321400e40400315082d10100d141c010b010380c401c8800d02d41a0103880c048001c1203c2c009003036a03801e00b0710581d80354003804075815002038030a424011205100b84c0012a602e0384030400c0c00c03c41c0c0c408442c00c0e40080e6450042020144140902044010100070032100ca14100461140c0314032800da40902400300c00280e03048000c000350301140000c0d00c084619070195860743c0005041112103441d80344940b180c50942c11040d901c030b020440410707034140c980500d00f031300d10758400c5200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 545765953 1250 545764703 545764741
    0x1806091403010605060a09142d03010e070602010903080606090d030c06150303082706010603021b0304030c030c080102181513080c030d0914040b27041118 68
    0x1d5521032000040c03076150301c0090aa42074503510b604401c24180440c4156400780f515030144242d85283c0403840e00500d204c800d50344402d21110028403007820b000424058040001c40c03107000d00c281100002c7d141e07410741c03024000314400d0f0342c4c0300035645800c010051280180000698001c5046240b20006130241c003410102e90301c120310104840326001c0e8000c0001049610a40c08100014100411900c034824039a071000701c20340d03075400c480c9020082c0541c1c80c1414001e001c107066001841e05441521802c06441c0c0d400450308403680da644a140c07184840d0030b28031040b5802824608003013081d48040c02500c4000e460760f92607408010b24034007049004020075903802c403035180030441c0c000c244100d208180003070b1012400620040035a40103052820100c04040340c00c01c00d141070140100c055081441d0b40d00c07203044038007090032040d010024081200402404624803120b15011022002d0429054460303030003015003000c1d038041c00d0107002c10684002d101801455201700014110b08180303c102d000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 545767203 1250 545765953 545765959
    0x605040f230909100207060c0906020a050715020f0307050102120618040f031412061002030702220e0d08060a1a1e0f0c030310050f011b051f090318060914 68
    0x4208004c0041c071080b41c1c802001681c0b0f070741e00c58003101e01c4075401c024000c000b0f180c0b0340b0050111401c00c1d140c1c5034440b8058000d0000451113a0024207986101f00a00030381030840c0c200f500d50b101803a01d80300d8001d500030140e2a800008540010b18545800500c07484c41c0120002c1c01a003d81e11035551a10340100303d007046040c00b8604000503000840345c3d02500710031903600510b0230941000c0041040100d100b03d804004c40d4410410307100180c440b031181004180d143d134440103800c0c030350000e00e0303006c0c007072201c00b080c01482405044481640e014072060700440003039502030440358441c842251204500c081e0418201801c100b0664000202e0300c0b40c800304183e1601701d50505603050582c02143e80054107411003603001206200c00c401501128000400c0200c4460400200100000c2c001e100e2800881038410501840e40051110170b00c01080c09649880164401c1d480c00605035008004005040c0c0004400318500c50035031081c8620706090396001c1d10340c85003640c0f0740b0f84c0e64896444c0385488a50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 545768453 1250 545767203 545767213
    0x20a021e010311190216120303022512180b041403070f0803040914010807030209042d150c081801020c060708250c060902030a0c0605040f230909 64
    0x1002801c0c0d0f90180021005408100d6040c2d0340701e8000130300d0700858070003060340301d104200c0c20011103668082c8103140c698142000b40e2248201c100c82c00ba001d080704940c1c80e02180440c40c0d0400c01c00342044a462030200c54580801804c030f600001c20440c0b103240140e20887d40204006d000380d0684449090580c00010219407015880d01e40c0801071661681c80340c0790962000c80e00303000c00d44483c00343d42404016000701c4c20007980360a0040b030b0364540034400a0300603000b180124007400005034485c03004601041409141c0d8010104149018610040681d61804040c001c20312081880c01a40b01900c40d6940703031501a2203684003041c16004c2c01c50101d0540d9401c0011035075000080c81258032620700c58485003020324151500541d804603c04000d10100030104040d808240c003e00c880701040c1e00705900040c4941c039031021904d010b0748804083c0020307400d51000201c8681c804020720a989000703081803070072a50340f40d940400340b9039100c0c1c10052209400070384085003006c42c1090b52007040c85040303403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 545769703 1250 545768453 545768471
    0x81b1c140910030218030102160b041403121915060f051c09030e01140a03020d060509190c0f051603090f0b0c06012112120e01021306020a021e0103 65
    0x8001ea803440c030300b680109801003000c814400074410303203103280785084e4004e6161000700c404007584a102c081005183c00220f00200f002d021181c0ea0031403c80d001c6204485c1c1e112421100c160500c4d00454001008106801c40030054054600800c0300408052011a8905027000780c259000f102450000080046c1400181c0342c1502c0c0c1d0301c0340c90441443c1d04000a581a040c1001403541b00480c50b194140403100d20341c0c900d045c0c0350b002140c0b034604292500603280e9651610b2200904826030141e94089140014000601c1088818442c1b8400461042020341000c1c80300303480ca4401d120081c0c0103e0341c1401700f1319130401410380100c1002e10038504a0845603d40e4031001c030200242e00440307800755011a40080d11601001914003404006841411100b0817090100c00044000b0300101455a0115a0743c0c07928002c0601f1640107038011030502c00440500440740c000e401403c40c2008030100c207000014424004210704c0812600940804440008211415003008030081141e0403d50364203812 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 545770953 1250 545769703 545769709
    0x3030c070906031707120c0510020316090e1012060b0409150e1b2103030a0e010605240c190f03122702040603020a03081b1c1409 57
    0x38000390054810004a460030340c2040100c1c0c00d910402007509940810001c400308000f100700c0b2181995624003212802128501241000c40002000d0407150010041c4101c0c401410070b50b80c0ca84850742e5503081b0a540d1b580300c01010300800d80722a00c082c0000b40f8180044400e00e6451004c440c012140031844103100000305080b204004404d0b511907200c5c181100710f15007140202032501c01544010034408440014001400802e422014030440b42c92805400c8002c0c00c03900707002074100e880d003502d880c4e10b00000144041c000c42030840d0140d52802078003003602d140428240b44034420212202c1000c0400c0d08000c0083d500c400722a82d5031388180340d0450071004060200008941c49405814811309081c40c019025031603100d8210640e505014208010003103c003409071901c01080d40c00101c414640c00804d000b4481a0800782d009401414040103005503070000307050324140704181100c1310790711111050b01d80c00d00380702c00066008600e0341050113520620924041b284000103891519500c0000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 545772203 1250 545770953 545770963
    0x20405030a0503030412050705060c0c01090c091a04110301120f05120a03050703090b0a1d0115031b14040b0f10090f1202010c080309070305030403110316050603040b0603030c 77
    0x300311010b43c000002c0204000d040799480d200c40f0b07030364148a402d2400aa0f10a600d44030001c000514100012545150100094009441d1250021900042140c580307000601a1003220a5031000901b90303003110801e03040610410750894042c001c25411642020b480e0303c0348800e04c103400e0304ca0300303030001c01c181c00700e0070900c01c0d41040c0740c034075034100d5983d641c0c3d0364081c00f907a800400703080525190440c1c02c00401ca81c0e070202584184180d034001500d01c09107020135404500704140d030700d00c2c0d03107081c0007000394281c0d05a1940649004a9052100324103003e0070f100d1b96410360043d5a160f8056503050016030801d50880550800010b00c1c00c04004413010100d02444035031104180000d00d0b8070800c0001842003e043d1000d020b4003003c10f620300d442600040c11801001d00010100c0c840000051400001407000c0c802940d80041130707e688598900f492807818440c1003103140b29015403042c0a4407480810300c11011104c0c09001c2c1401c5a4454880700c0c980c0340700400c0c403030f0036000070010780d8401c1c20b007400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 545773453 1250 545772203 545772223
    0xf0717150901050409020102061b041d090f070b0d09030519051b191104090209070903150203010f0e0403090b03100807140a030219080d030b040c030c0905040f02040503 74
    0x240c05904150604200503011406034050fa004134039088204003d40d03400b04405600006600104500081a400a200d14420313a440007030014460080e003030b100000c80910501400c007010454011013031560081c0c2d10f50703486110780c100d80002007180300cbd650190350300440380303240c028140a401c100303206443e00b4a1074845148100013400000d00300514803185500c41d0b2480c9510402030071080450350540f9044daa030250003034400b9400703440b0424284c1d960341207140659070281002606c3d0401d032202a04070b0711140000c950400f0300c040392024008462007a24101e0b10320004201c1c103540b40c901040303041c40c400f070003d80c108460b060002c2401c090103001140030781d000070000881c031440e00c58954204075017508050303072066110013509115690134a009080d03c0e01100c0c80c02c040500c2842c000360202155100d94118012040303040300b01601503004102c51507081d6800e20001c0560f11045048845d0158014045200c0c80c40074095414107611100142c43e148d1401031402e40c581c00003a2a103901d842d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 545774703 1250 545773453 545773471
    0xf060f03020f131706070e010302070f080f07020307140d020904080d051602190206031612180c05180a02030c0d090501090c0f0312050304170a32030f0717 68
    0x5001300b14000340400040954a0100003410260a0038540100031001e0542080d04058020400c0340c1800070a201c510982680980b1082e640d490543c081d90740d079041441c00781e01c24060725800040c104214405d407a1481c0c0e0003845240a280c055081080401d40640181ca94100900900c003030000940b0410307005103041d1908040105018400a103000d09400310000c00800b2000d008005071540810780e82c104a01e08100d68030100704040032103c140000032a07002a6040400d605022492002c0001082c1d01901c040700d0b01580f0f640031301a5044050841c0342d00c01c0202c100055511910b607004d0354020300201c40080c0307045a090000d006888034000280c565035034031030860080103464145100200941c420191072140f0f143c035804010200c40c1c1184c0d007809070001c001403c200d00c480c0c840003040f00704c03502c440c0c944101c00401441c1c0b07a042c00c80d000b4019280c0010303282a0000c1e150807985600074880c0540b550790780d404010f1500102070b184405010b070200d80b4010421a40d10554881d2800d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 545775953 1250 545774703 545774737
    0x60f05070e031204050a0b1e03040b04050705010801121202010e070e0f0622020c0115140f010302190c0c030605070809010f14070804020a050a0611010e070f060f03020f 74
    0x681d04150070071004900074054000b04103c100312a031a0f401499013140c00f0101c0c1140c0741c952040e55410400129003901c50441c400004100800c001d080f450f40c0110300070b004a80049407140010350748014207002d102540d26060b8140e1000411243c1240d420f00313560f10000c105603840f070b84490718049403032300030110f00c00c0c824040145078150326400580c0488103d0700e944d03848069a0000c0c0700c0032902c0725105d410f1500015070200240307007500400d194080d00c00740401010f540b94200c82c4651409100a4403485141041521030340c131074001d81d0200070b62100e07c1080301d852454250703249604040111800303200310342d001001c00c2c0103100c0d80384100c089413900700c2e40e1316100c1c603d0390840341d00d046c1d400d102901d4010b6585e040c44201940d50f40c03100d45400e103001d4944031030002038000c2a50381c0c0110ba11261581000c00c883e54400c02c104c20030724401c4000e00200d02d0082056485100c68080d03500c0d07415001c40c0030045148100c074041e180032858180140f92800080d00f81040368024800707160000c0030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 545777203 1250 545775953 545775977
    0x61718030a170a060b0306060a210603110a140f030703080c0303090610030f03120231060e030307030e1207080c011215090b041503051018050309010c060f0507 70
    0x1001060f5445442c51004110141c10b114142c0340c0c0b80805098503008400125503203010901900e01c0d0f6040d00803030301804d4601480208002e01410403030108a0f184d854022090b9101e041002198060b81c848100c0000040700040620203042080d0300c4e41c40d0715124143c800008151484010f2001a007035001071a070380d10f086800c0c94a4480301a08945800403400c90400c0810340710014900d1595052404203610310103140564045c0c016030151006142c02c40390a200c104181c012047c03c2602c5082052108607501c0100342c0314580081503807601500104a0400002d1250400b41e541203001000000800240c400341c6151010035008079a1a9000c0c0c950189103603085009114203000c080e109110600040e0050032055100c2e10914618680b115041e50340c590b900c2d0002c0704601614016181425900d003000b07a925030f001c0010914003031419010640034240301820300101c40d0002c00a41c50710f4441001100c042c1c409410036103800350340d030000c141910220300506020307101d2540c840600b214 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 545778453 1250 545777203 545777237
    0x70f02040c090e0403120e0610140102010b0102030d0c0302130b030609011401050703030b060c010c080f01080d0c030e0a15020a06050a0204081504060e0d090f05030106061718030a 79
    0x4448590070082c46400c030010007020407032141d040d9000380d061428400080c0c00c0d110207030152524507200c59060003646c041140304007a03400103d04582007104403e404d451110010b90803a95443ca80c0340c0107070010003c650f024040ba800c10310319298146001850311410b1403c02e42918002c1d003003071894000000522103c0d151000c9103030b000d0052802200101214440040d10ba8451000000e05064480b08400515030791403083e10001da80110080c0038007404800d00402d6100304450803020302c5a60b20002c100b5000002d01c61038401e10f43c2c0c5031401085190385041e101000100c055542c0003504c2c100209807981c80c0ca41c05185048a5001468007000d280381c9002501c4c00108070051082c414002003004c10304c0003898180c0011042e158000540f207a0174000060040e84c40c1c42d61aa1080c24051840180c1c040040000c0310340d89408078011a4840301018242c841078400c03140080c030f030070321082d01d8000c100307070f68981000c5124a09400d07c40021181811358000b803804a020901c00c0100c954508 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 545779703 1250 545778453 545778461
    0xf1c0306090b0f210303130507080f25080d0e030618070b1e12100803040605030c0a020a06060306022113080c1005090606040c020610050f06040b070f0204 68
    0x60325101401442c2c99000810811014050014410b61410100490b800c2e841d01500000340c940109480d0b4030b2030041b100342d01c03020080100711000d2050032000240c42c3c2c400302d1100c826482c6e00c4043c03e05030a10bc03005451211058508000104000b840011101c504210042d01000d442c1c440c002104050000c00d0b003440c100030a0408420b40559052900c04400320b400e800fa02c1290541948518018180480d50725000c41070030780345c42d00062684034442c0354040c040d100c0c01400f0400c1d110b4a03140d44a07a91a400760340f10300804128144046816440e41001510b4800c3e80c44c4102c480d00e00302c2c1e0b1219800d0b194103900954800e0b500081700c3d8160301081e031184030b400b0a03205007998141851303c00c00b91154039004000d070110001090340e6105503410300c500032003150355040500850411400041d00d5103019603a562160345042d004c16121400400e4640c42405030001081c80d0078544814000c1500307240c0000351380400e0801c4085a803041c3c01001d402441d014504050111100d441440122 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 545780953 1250 545779703 545779709
    0x20604030e03010b2b170d180812070c02310c090311010323012309130213020d06031109040203030313050718020a0906080603030d0e0f1c0306 63
    0x41d034101070200300710340c45e422102941c0402c00e0410180d011071240407403100100c00c4030001c2c0b9045254840e07400c08207455010300026003a04200300b2007506d040c909903203148880c1da0000c01d80442480b4031881c0c0060b100751154440f13118140041c2624681d8001080c5550380741070b000402c4511400105d06003140056058084401002005007000009000d40b14800c1c80c80300506039005491a9501a40719400800302c101c0041030902e070072540360325014512607090146c120b10100b25810005101c00c0058240080c02c1c0c0035088811517140c0015542203200e070b00e0f0050743c003c2c41200341e892201a140c4000e16054410b0705001883e18207518155500ea00c1c00b040303440c403826060050101588e008400c6913004507607407003003410183d55490440e0a24449a014076580342c0714a022046401c41c030b40080c40040250340d90a0030fa035840c0e0f4800e90702240140c0b0805d4050f0300600064070b1005465004003038007044002280e130103400d4128045d07d0000d24a04c40d0b01001c1100d28514005505400703141d001e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 545782203 1250 545780953 545780959
    0x60901024e18030f120603010603021503090c0a030206030117011409071d070f05031b0a0c020f040516034803020a0516030e0d060b0307060804020f060703140307020604030e 76
    0x10f003026040340e504c80341c000c1c20b07600c40314000204c004c40d07099942584140000c40e0f0107400c01c080781101140010380f5820456a21a0034010a0880c445c0c81c40d020b503402054903030082405045909000c80811a00900d08550074559602c8040e0307008002142d40a501c070305034080c010106207007000010401d502011241000304a20030050103011030b00000404140d0502e4942a51682c0d5140141030300703800032510350525900c0c00180f9242c400d81c044c924000840c000d0350034040c02e440c1c40e82070004640c4111020420070790345020060a141c0b0941042401d5080ca4034078607103c1d03506414418038a0340e82032138010076107120400c101c20b1004002c5082e411908900301181010035000c000f8180e48594005046103400c405103020801d40038010b8114040d402510008521b83c2c2468450002c03c00514028824840d0100c009400d0780328403600c40c4681d03805071070040314218000911000c4d8000d42000c501380420144104904c2c0505070245105001950040609023858180640296034208003280 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 545783453 1250 545782203 545782207
    0x4090b03030f07171b010f0b0f030a0b0c070b0f060907020d020703030c02061b0c01020705061e0912030f09091303080402090703020f070f0203060901024e1803 70
    0x1202c482200694480940140740784080c1c02400311604100d1041d50650184003070b0691901c44070040560019040d15680c3c00200100c01c40c420810001407010041550b041e403298964100044925010315040130880c107103d82441d02130740d6203201054003240c0f034030b004424580c100145441c0180d02c068100c00140007901c02401050700094940f4a20301001d401d000252401000f191622001c0341c0b03c8420300100003040840364013400d5207c500c40c216050040c405c0b19000b0407036142c001c088640c1c40d100340016600c065800c54800315240c001000c40c6074400500b01181044100030700081c4883c200d102c0c2c1080e0b40f02034030420416004e10150500031300300b000461450000b9000b2045036081601202d0400307095442c840200d000c0d10614040c42c0a03036501181035000c00110b07040c0c15003103601c05ca09071822030355103600103401c0340200c1e41519844501240d5419000700390402c118445010003428040c100706440d40910405402e4014041d02900300c020000b070060034189901641f0461800b840c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 545784703 1250 545783453 545783467
    0x6040c0305130f02010c080a0816020f031b010b09010e0a0f14060f0d06150f0b0309071a0d020a0c200306061e090708071803080d0e160b04090b0303 65
    0x1604402e010100510003100990b41d0019a0b000d41458040c81364848141030781c03020381c044005e01000d0181c1d00e00c11a05030000301e1010075400802c2031002001c07107000640c100365103000c032416124815107510364555a99035440c0701a80341c8540b043d004e0700000d05032000e07900b0071003800e40c1121007000c2c3d90f0f5201d40c9000d14440e54402400c01e9140c02c203000720b41a00132014010f00244000f00f01c40c500910f854642144403402c0d1070800940d074110740d2005420008181d03109500c101e01c0c40300b181da0000b180c01005d024049500e0800350302e2074a01c030707501c41c1900b42142c0c2140d076412a845000304c00045040441c10104104203407034180102800c0c0c0d218601d00d0100000401d960b4440030b003026100d4190322401420500342254000f01c100c0000300304410b45d0031b02c0c40001e0587c0109a0f01e000c0042c0f10400350114102140301c03000110790303004d55220700d0110200f15200081941c01a07500090042c41201000c0f804102000c00240036402095540c841c504444041121010307812107002c0e0b00b062041c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 545785953 1250 545784703 545784721
    0x30a050f0f030a0f0c1b0603050718050a1a190c020a050d020904020906120319110d02060a020f0f031008010506190509040201110d05090306070e1f1e02030306040c0305 74
    0x583c0705414a042103400c0340041d14000078400d61060002c1c1b10001c501500040f010740c035400032802281282c0f1401c2e40030802410004900c102c2c1e000d103d800500d03a0400300085180305000c10812200e407103202c0c0c01d000034030000c044c04165407990800000d2b4000054019450b008021000070002100c68158078071091b400325000c5100108083d202d204030000007461504d13855507800302d41c20560150380c1e8400440700c1c2098881c1c40c03e2a1080024142240790f0b007007010024484000c034110742c0080c045584c84100b5100a944558030b03541603100f0034004804440341c0c4102560080386404031b80128941007000503401c481c4020410392040d40c6046407044040c4042301c1d44e03c1070351f00940f507601c000c0da558001a00c5400c00c0d40c0010b84140308520758031140740c1c0d00c100501032085045040d074146845041d01150322501501c02c1c284e1090680071b0910b2001c6604481c60b003411786a0400311002c0081218008100040c8034a08004d6000003007001210702c0c1500ca03030b2100c0d82d41410108080d003000c07401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 545787203 1250 545785953 545785967
    0x61505070b0f0604110d14060901050a090203060307050904030f11030306010c020618060a0507120309120507020f120d1407030c03050a0c020402030a0605123405030a050f0f030a 78
    0xe122102e942d00810419265501702c9141c00c00003002c500c0e625442c18a80708001d041c1c0c211000e9641304000007080301303032521b00940c6040f5007000704090b01c0b050034003007103100942c00a80040e5140c45040000600c0740c40d003199140c8180d00907200c5400300880d941c0003409100244004040c00d401c200201b00b050780c3c00c240700100322a0140c0b001b41d1600c0580d81c0d00c10403240c640900680c0003a01080941d0030940c0080200b00503803261a1190603220011019000d0740e00c1000000d00704c0c2403100c40508414130884c044c1028a0000b41551400010903012507440e003400032090500b900300c8014051842e0b0416401a403541d00b03234400d5031609603103480c020200e1085210040c00c200e00040e0300403a07544541343c40080c480d0000d10456076806c24003403840041503503104a0340204200046184130340c6000c100c1a01e0249011031001c3c011550040068820b100b00b0100c1121403580f51000c11640c500f081186034061080004010403250084040d1030600c25502018142c1c2c020449410880c2e44001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 545788453 1250 545787203 545787211
    0x120a170a0c1e030212090d02041806050a0e070509091005071206140406050102012309011e020702240706021b010e070303120b0d020d140a06061505070b 67
    0x24180391610180d08049400c0240c0e5200030b0150601146850b07000c611074003541c004544240c00710f8086540c202c0c035012840c003824001550068061036404051300f40b54102961000807d14802060a019910102211310039a10504410f03595001580c40d04070401c085c0c000b80c901210061001d1514550482c0e55102c64020342241c42e80340c102003080c81340960b41004000c220713490b05010a5071030b0110905100c50b451082442681401d1000400c1e500600c50a9500d028024900034003805805450b107c1503000b80c01192190b40e107440702c034504940100c500321007a040200150b80c0b18110300421420308503ca9040c152501e0001215654101103000c465015a000701d0160302c450540050185010700180c0644c815420007000c0c48850308040b50031000d0b40c1c420349510b506400411080c008072070000d100306400c000d0104180001d0300d4001082100c0601c00c281c2010a0707070b8107064690034605180000c5501c1c54850200740004425940505070381040361900c6401c1a420703480d041c00007200a0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 545789703 1250 545788453 545788493
    0x70302161a070f08091c030207090516320409050709061709070b0c011407050903030a112506020c030111030a0b0f0a1d0c210a06050d03080105120a 65
    0x402050100300131070742a04c5203d50003c0a0501513114061001d02410800c0000c50060094041c0400d452071244582c0c4d0282005a50080c4101200d420988411011014001e801d45206010304000d40b04001000c1d80c1c6034080320001d84032403034800110151440035020701c1c00c2c02050f040510140b0390000703024011b1082486590b00c1034880f009610704000e5550005018a0710000700303c8003258054018408030103120f112000706a44183d0101c0c0d80e0b018a0840d40c0e8560800c10540c0506446030408540d60b0460781c099030b1000002032042c0307140050030011407400581c450f10800c43c240d014421100c04180580c002c1c03054407100e201c042010300c00101103145150742d801c0b42d00103d03199992401001000a07180350311903030319007001c4000e04110b40400501c06c0c81800000d01d40c407885200703035022220800c1120411406414440b03d050701c1c01042000c9850b034500c800684c40d51401843d50403140280c0307035420f403541401c003800419104161000c850f030340026040c41c005013000b5140c1c01850004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 545790953 1250 545789703 545789723
    0x40507020a03080c0903030f0c0f010b03061f0f081e21030a0207141e0f1c11160302040501140a05120c0a08010b01110706090b07020f030102070302161a07 68
    0x30000304d042d01a0041d03141d098072010400500c0c6191402c001d0120010920464540da1076503007446083c2e5100c009a550160003440100b09028089000d2a04031400040b000070044e451703085c09134000800e54040c070510b03441a86104c1400507403c204c084d80c3d111000c06071003070b64900c02591071030b1100700c04030601d400130000019440380c03136542c19901034903404501440c10441c140c10941da2a5404081a042000b0803c0350b0050040000341314280c0c0b40304070000d4000c040d4202d00241c84001d0080c11102030180d1383c031303c1d00800d207028810785640552000700d001c1c506065005000c00c880058208014146107117140c114035660765140341c0100c0d04107d03810501c40c6401101181000006402250408002c1002041a9034190010158017400380c0e5840c03e40100303064903a50b5124607100d142c001c2524001c05008000810005042c01400071f482d0580103c6003001003401c903840644260010b8221401240d40200e180d1101d40007442c52580801010103003650b40388407403040c851700a20650725 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 545792203 1250 545790953 545790961
    0x5070518160f0e03030d06300206030402010c05060a0c091a07150b150301080c09040b071112071505060301061a0306040e010221100f030f050a0605010603020403050c040507020a0308 80
    0x80384043c0a5100400707401e50b038441c3e100011441c05007809008211004004850580f1481111401c101440750b080c80e810a2422541c0c003480021760010300160f04016642d0842808941c00704441d900071218034a00160708100f43d000100080801c1e04140760003030b55581007640013003040064640e0b103508143d0ac00208081c4003186001080303c0801182c00c48200545081c1c500c01860265040301e1000c0309039060400040100144440100c4000345404404d201041001e84928001f0b0000f66095084880c544000d8601e01c0954010142c120f41002c148003944032004040d004007900076000340d00a001c00303800c014000f581004861013803041101c1c0800004d1569445420524611140741c00071541c030555034458101c200c03002c03400d021b0b0b24000c1001188101400002d90012518003c40e058052410f50f80c410240c403041d1501540d551207201010b0001c00c0ca503103d0340340240669200140d88a20f14644607040c2071001500034801d510700801c00590a4002c078012910303942c5840c041c0030581e1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 545793453 1250 545792203 545792207
    0x40c020f01060b04060306050303131806030f060c0e03120d1a130b101d0609040f14070207090908120606040e01080604230d110a020d05070518160f 65
    0x6222010003045608001002a07111550401801070b0b80701aa0300384021916082810f55920032003103080c003400361060042001d503014006085a44032022404110b40d1380e02e44404484407410001514400d030741c0e9032000f0301140c01100ca060300c00c400354041c0c0744203900052514032501440711802078254980380f602c211038222920070007040800a000c042070a04214000000340303120b0385a51f0080b840b10071031900d041d02919003200c00ea50140c2455080301204802d0107000e40210030302079080b91302c8103407240040c8158003a80071600d0503210021107500c0d222034000c0c0703032004070703448140c035580f038400c2010109816404452078547c51402c25605500c405021884a220b190300c104001603d407400840e4841011030054000d074090700b00c60494800301c100e00074190b610200032003450313480728102031940780c0124a05101303d130500c000e89000c90b9158000c0780c410b1008100451b0345400c0071805202d245410005240c41c601d560740c1184c0c2074684040240d42008a810494050020910781516414 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 545794703 1250 545793453 545793463
    0x20d0f03060513050f0f0903073201050a0f14010e07020c2806210b061603031b0305040b010308070f15020c100b0d0311010219020a0b070e01080105040c02 68
    0x7428141c01c0c3e0030601507290050500360340b44038400724000d01141e080d1122489240c0148011400b940c0f81102036545c0114071030076402070f84c050046414403804400709280341c0d11046507032500007061900c0d03e4100081142c0e00f50000c0c60655141c480c0c00c48104c0c10780030354203054a9440004081a865031601030b450080c2c6400555844031000b114004a51103a108081001c0861100311030081e884400548815614078403030070001d00a11403000d007491058000445549014000500d03080012540d1401c1030809901a00030a885075200184440120703441810714006250411090402d9500c40444420611018141040128402d8280111844e08031078a5034410081c510b03c490401c03109010750401c0c49009054000d1240401c114100c078001d018041c94000c00688902c0c42070356047c0c0310000305284441d034070340d400e12284d000c0510300c003c800200e8206030001c1c01940e03102d1521000c8044014500003c10072102440007084c0d0704034001506513282140c02203481d00800c0000c078500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 545795953 1250 545794703 545794709
    0x3141e0c0307050d180302120a12020a051b01080a0b04060b0a0201020a02060c3f04030806010e010c08030a0903050405030f01021e09090105100513030803060a061e03090c0e010b09041407020d0f0306 87
    0x13401300f01c2b02c07411129000079065540700d20640175280090142034882d44120076055025010400300320010b203005c4040d61026240001c000c00001e015900c030204101c035500705190010140c3e60000c0c810600ca60100007040c2e10003000c040407458840801c1751140e840440300300c241190382c510340391900030342038141c00c0848909a080c83c4060b40c9c0b51038280141640c005481c801d01051420b80e26110952107014000311a42e040000c0c24070795125881ca00380103041e051415010000c05210218003540c050048ec2d0310940d082001588426810002030100045c0300d1100156140400400403140c44695241d41114421141a0f02c0e107110030000340d4561003101c103d80e0030022601c102004018010001d14000e80040c0c98401a0720340f1b409058a2102c039900b440345504490301e04c070a800d0f910036001099414440d000301c0b00c0c0160385042e641030070602a0083d6160907c0850501d0003403c06200b046110550300440340e02d5070030540e0003c2d48410b002d510880404c4070030000c450039640650000401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 545797203 1250 545795953 545795963
    0x108120a2703021206100e13020a0803090f2b08070f062a0804110a0f0602060a1103071205090102091806040e010903141e0c0307050d180302120a 64
    0x4010712119801204000d9000480c07040c0c031101d41c00740002c6000103449203d10140c400c09080039040c0754401c1d6044000610501381c140c0440391280050f1a205081801010f10b07400641c1c40d00d9555081004c21848280031a010348544540c00813840c0201100c0410717201030145141d210895400c10807414451600041c21103403280707501408100c4250301031b00d18140d00488940130320f029940480c007680040c102080004a414000ca00451415000f0450024000b0038204400d81c1e1891180d601c20100e521802c0035801500401540030164094548091400d8120628514100c1005001d9051aa54a58007035a80d0400103030044000d40c12500706680050078000d03280c4000301d0710303215000d088555500490400c1c072038204910050040007140ca506440300b640700c03050441008e4198004a9400490900381e030840403e800220000303004513210a0b019640d50140c5051a52402d1080e848840421a0034840c11f000d1070112214032055a50444050707141c01c078030b0845940703000700724000a40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 545798453 1250 545797203 545797247
    0xc060a081b0403020604140112110a053015010915080907091e0f090b0106080a090f1118061c0212060a15060203030705090d240203010f0902030108120a 67
    0x300607e00080d40401c056007641c072065686440c0c0310703510075940d600c4121441281e090145101031401200034140f12581c1040b030750600804a841e5050622115080e60a100060313018811005100d0380c943c82c807070500303007007041c00d5910700102064081a0f19421500704500000450f1021405104072030041000711014043c0580c40c42e94010001054040894014074129181003c8c00d8207020ba441c82a410503440da00503841e051040d01d5441d4001d0440b10f0302a80c1d658400c0000c0d9507000490441400b43e200c0300082140a824014070324152845050b5041100c0c08000090783d42543d61007100f403483c1888002c0501074400320390151b00e1410b18850902401080000d0340c2c2550f80200d1855a00c20722541d1015507441d010382c0c4920040d2198000900b0070401580c0504000501c0700708984941010300032204100d0f110a2079102c000036013003146030000010405025901500800b03890070600852030765240134081c80d5254441c40c40d41041580208040070424011003414604428070b0640034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 545799703 1250 545798453 545798459
    0xb01080402271609060306030506010509040c0e01064a011101020c0309040615020706051c090b070e0109060203071b080a05030702041802010e0d050c0409140c060a081b0403020604 79
    0xf4080162030f009041c0052a0340c100024014030074050041125040009004540d0030b10090054071500100240d903e01004500010000901e01420b0f00800c1e00d50780320303078030681c02505c03104600003c81070744e03050101c400e1024110600f140003280a41503c06403a0403d0391080c10042e16201c1c034111032203095520209880d13440b042c021004244010086030704100b02c80c2c499a005807a000000c08080040c0c4c0040030034416a80524000c0c24903d03100400c1428400002e0f0750003058601301e038021120346070039009010001303070019071861160300c0900389040380d1821718000135917078001d440010345855a810034040c800340103a11210068490700007a00c0c1c003050039042c80b541d40d44c421242280220b00c2d0055070110001c0b520703648124154142e440c00b035000900030030004c246241010076261402410384c184040d0b550761190f008120f204152400080900c683c4060030900c82085040c0201c3c0100125040d0720b030b108145a03030010400d681d8040d4441100f00c500084d002c2d64000035002000000e000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 545800953 1250 545799703 545799721
    0x1030b0f1e0306010608041203050702030d0501060210060f1409180d0503100806060d080c010605030106060c05283801080d020f030f07060f050c031008010b0108040227 74
    0x31401100090b01201c200783d84c1e60740100d4001804903406070440d55a000300c58034051007070b003005402c42040c1c0704490401c0b04000c0003500302c81c400e9014202680c410a0941c1d0300511602600000300400d41c0e041d441e1031f2605641c1011007940141c1a40704882c08800516441e01ea242c0031803902c11183c1c11505101040c8c1c0d409030540d0f000f40c0700046500361140001880c0d080c0022903034454000680766030003101c0c0968a0589a4124040d01c3c1e01a5407030300380209081d00e0074800e0760010301c0b940c0e65000900c3c0d2039090090820079800c2c101a00218045210b40101c0203003142c0751280f65020721f048d2118160100c4045050003030b001c1d44603a036011130010200150a0a41071816204240b041e1201c10303c18280580e82c0b0f00034141c4c03602c5e468006010000c50b440302007002d4820b2500400020802c1880c1e513544c03c040b00d0041b00c80000040e404000e00240803101910540a4410368000f00005254a40060403022005100a1044035a0304c1050600501c40c0a1007900f50074641000d4240e0a06d6030b18 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 545802203 1250 545800953 545800999
    0x90909050a0b090102074716090b0f0708040305060c071e0f0627121404120b070e09090106050909070e18070807140108012301030b0f 59
    0x410b58142d81c100002c070b10440303410b100302c3d21300d182d0202000e5440c080315200440400300d02d868444002c50901d490401e008a840180d90030410b6180600c029880e0040c8402c000c0b02030500200104440900305000040b01c10048445202810103078a844000038645898580f00d980c100500c280100000d2050066403803002e40080c82c81046031008545480e00300509407007816101518002c0b92003480c402103091a4090142105640c91200c0b40d81420303103519070741c4001d014080b910450224000744402da881602c00b0342200595070740c140341078503126010200c41c0c110701d00030308800c0700c1501191038140242607520211001802c000900d142c09142140202081d11550340079180d403000042c0021000f240507c01d5134030003614039550b87c07a19a15039007048110448801c00e44a41d82001c9400d280c01c000b1a4010160342c1800c60110420b27800060028606038421000d00c102248003c0c40c040685006254a0000b03180000345186502c000865480018491350b811050740c4407246078200d00550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 545803453 1250 545802203 545802223
    0x5060402041d04062d0509010e010608071502010c020d0f0216030f1101080702030706150b0c03131e03081305040e011a030f0c0907180603050621070b070309090905 72
    0xb108108400090031084003174080e03c0d04010741540c5505500c01810400d80c00a6003082c0e950f0000913400c00c07c00c08450845103650400d0030a030748054010040030310312105100300c00c40244000c0c0038940c10b880007c3d6594402c4039051013800000200311002c2482000110b031542c0c8112544a541607407030820b80702c400b4071840b0985000d801d514000386154012107085004080c0b43d0300071442e10129440d100c004210550b0300345002d034080100025540100009080824034060207556a028194071514212255520120309080c0e2200010042800060f6400403250031803885581d80030310310790940203654980c015075402498009544030a400550004081d00d20820282c2c221104d0402010f1b5070741048000320266031b12502548070303103040411086412100c142040804980d90b0380c20305414807010380107100065681c0082214500e0b0a110821182540c02c1080142082d039041482c1c40c0c200718010720004040000d038601c10544544e03009002005035480c100104000d0381f0780301e502c482d4a81 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 545804703 1250 545803453 545803463
    0x705010b0f46090c020d08011202180711190809040c1b050f1504020a03230f2a24090612040201170f04030327060e160608060405060402041d04 63
    0x111420fa0130781e0001880130311095480c2c4404500da0b19003201e81c1449412920f080f600006040313941c180f0300d00486040e40c01545541c5820f1850100104135520b00a407003102003200d894142c0711840410070700300031508a03040a442c0410003900382d400a95030100200c1c540811350001d4407041041c044082440d030030098014082ea124116000a02c00040806440c06980102003050404c006401d142014a85c50030b03650b034515a86610400050400c02e0b5a0389136459034000c0c2c103405030050b4604a01c090102d40e03205500c21448441c0d008180146c0000500c106401446518003c0f10070101c0259038180d00d00a1115955090200d4280c0e42e00c582514100d02003015020100034000346a04d802e846690014a4079134107986e44d4030200c000c1d02c94507803a0002d00b80702c2d4140c110814242c03400807805a0180b84d02045034028102e180380340c40c7c40c1104420f50001690418000c45a01913030494000700211030205040d112a00058003d00c07030795001d0404456901c034000305000071003001c02d114074011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 545805953 1250 545804703 545804711
    0x30a140a2a0314042111090c0705150c070201120618060306051303120f1e020304031403070c14030405030a050f010b0303130902130305120705010b0f4609 68
    0x60072035420314081d40c083c80c5c00e003100c03c181c80030008500000711266039018807200b206030000d107400f0a040120580d81c86550000010301102802010440702c0c9503021032203d601030300d1420800b0941a03000d043c81c0281000b08145070401020310a03085100030f8100e10120707007124545503000c80001c10051000301c51441c100400030303400052038409510140d4040c1c4900303081030b13210300e085801400d104581141c1075941d5240300c41000408030400305a0a06400f005030ba81c00c003424040e00f03000400c480071030400400c008000b14103501842d14900c083e44541d00c0005841d0a8402c0d0b4158040c9800540d0540700f604c4000f018068000381d90508081d0007002002000800014141c8038840e00e0814021124944010482801540c5c01020442019203241c10003545a075074241c100084040c14690035040840d440042c0602031256800a000858200142e40300341c40118000e1400501e00503c1c804605600c0610765001d41d040380c00040c0d01001903500200403200c3c05408040310b001d103020301031074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 545807203 1250 545805953 545805977
    0x50a021504020901030807150515030124090c050c01020304030206100f0521030903010939060302031803070605010e0115022e0e031b030a140a2a03 65
    0x150010141c01650003400307035a850f81c00d6444940303159025003030441e5500449004070002e117106216242c0540c2a00c1c54500c1e1070481d1008150944490314038400c071000e00d06285104050907a4100c404803040642d000c00c4c45810200244c034240102896051a54000000c10081541c081115441440005004441c407030701e6049103014480240640c0d0381000403a8011342170300072815101e5400040610460785810390241c08a400d69540301002c8803000080c00d9103404810054449403015010a03900f00b0400c484040e0f5442c030503000f0702c108000d040d4000041254141c084003040150200701045a5035034489140c6074004020074890b41c644401080f0011030400e0000001201a424a500401a134441202c135550707180d4140c0400321107006585c09042c140d90f03e60061111403070001029684801c140000e001d01d4450300c0c8000350803900100320b00c2803140d400500403550584404580e0b03441c0d04c2c9000050740d040003c00c000c3c400c0c406121a84030b02e0201462084480da5100340d46150103580 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 545808453 1250 545807203 545807233
    0x501080607120b1c03020601180b0a031205040302090c04090506010509060d0506060d0e060a060b040e0106052d1e0306010c0b13060204060f090f0e010e060a090c050a02 74
    0xd0141c45900001e8944480c0d6003894855400804603020000d2040742c820021100350b880d44400100203e001d030f0030a03001000700581d00108555000091031003030180e00881320001381014068080104480d1944180c2c8010f188075401b80d82c041d540c090000c84141c00d003001d0100883d00103201c0c14100c503007000000b95941d48924150740c2e1340704010b00300d00c1c02e03d600c0ca06420080c00c3c0003825650405400e00200750320741154004d10300c0714900500a0000c41c10046007020540d481e1b600025101c80742007100f04010140c1d00144ca044400074030744252100600035041d0145800c10091200c01544a22101e042580c1032008014200b80049000c142050034040c050450208448003408100c0702010711010501c034003022603211400045c080202801c42d07946900b02d80040c1c01c404006005c0c00800441e0715040590817020348030100c50660180d161610100c01038405000341c1b5235200d689404070345c0c00c1d00d03000b22480145c10244414480c464110100030070980021806200501c10141030300c01d410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 545809703 1250 545808453 545808463
    0x8070212311e0605090a0e041410020703031a0105120a0f0c0f0f0c1e030e18060a091a04090f0b090610120210081e0f07081e061c08041701050108 64
    0x10406451584118034103044031f085000003c10070f9540304813900130014070381000c0c4041c4000c000d91a00040e10303611507040007000c6030039044e00005220a480e0301043c540c2e81003030503180f000d02e2441070310129540d07028181c0e001e09121081000d58904000301d0701d03070b480e4020300503012502240ea0b40ca821104040411101000240310140c5410080600740798880500600605150b00030f04094000700301c0c01002c100690349035882d803d120714801c01404483d191821410006081001d41404215005074038803105c000004d02c194030490780d1790b40410400070f15403800204c0c0da801a41c46162031600b0380c1d4141c1c50707400032900942410300500010801c581c42d04082600150060311020451000000a0b2611040901500141d2403030742c620480079603046001901c510300e0720450300d005091041d000350580c140584200301e42c0c00c6032504134201100d2003503120391000003101e480842040c1440c8060b0b040d020418040c25242001502040d0030311000d04488200d81140000c100980e80c034a2415142c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 545810953 1250 545809703 545809717
    0x1140609150d390f0c020a1202030c0315060d0c05060d0f050c0c0703021512040302010e10090b040312020c0114040c06030e06010b03190e0d08070212311e0605 70
    0x410304410b003503c8007840f811001516203001d050112000c8a01d400003001c810040e40a4642507900c51906011800c1c140080e06003490305600400c80842000c00c018031000e0700510f42406061201c1c08041440000d08402004110103408240e90302030000029000c0e10740e64a003960454200f0000c03c0002c06580e0840310841000809022110700716407c0141e40d803c11032181106503c1440350785000600500f159024078402d07000007500c0302c200b152182c01d0081d0320740d000d01c601e4038103034040b030105480d401c0f125030083d4580380c400c03070f41c2c64100803840c000e001c0c40100c3c401d507620300341194840b00081e85030140224090b500344900142d4440d4102c003500d148420b180129009800100843c84a0038051900001001503100c2042c1c0f540c0703c840c00f224a000c9941116600c4594081c281d241c01020305a0021038a01c0500b80c46440c0d50580030f00f80c4034240401000d4108400c10203105031040114803030000c000361a00385050758031109441d8054010f0141c00c4e1648088200081843c0950111a40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 545812203 1250 545810953 545811041
    0xb361c170f040b180a08030c010506011803030c170406030905100203090309060703030f0903031a0d020f0d061506020a1703060904170c0111040807090501140609150d 73
    0xb5040c20803419825035000307019802c10215018400d052960340d5401178401a2407813a0017140c40b240c03554913540c00d407a0040c00990600494403102c02c40f40c666a00b02009494150500d002d00341031a16104110300d035900d9259003002c2010802080d56585034000c0c2c0070a03401007088a144a40940489040784410303144400301d60b100b000701c4812418003d020308040b034082d060004403009071a0320300c070139940d000c1002c8000990703900a84071000070521842c000072070b050b2071070386550007180e001c10700c54103180b4460303480340560703801003800c11030305410030501519140c03c011641640c90101079650603011100301c680350040301d10301d1702038401030094a05c6994002c24095903910785496444240590000c0740d54408020032990260b0ba10901070204017801111075642c0ea985000350aa0500c0380c240c01c04e004e11428030004104205945035061300c210740c125840c80d82c2e0040303000095590307483c0088074000c011002c9203c0811604a900c900b9000c180d44000c0e405042e8050041c40465000c1104000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 545813453 1250 545812203 545812207
    0xc01120e06010e1e010806060a080307020d060f0902060d05040203010c170c0d020c0115030201020f07121e0f050d0e0406060503240a0b130b361c170f 66
    0x203e1242c0511142c114000780ca5a000d00410030303108207181c0c40c0076004400180d0000e000d1042074200807201a00601941000d1410a6640e50009194070a04032000c0d24490701d0794038418032529107034810181103500400f00e40d503072280c06003c60043c0208130b0702a0b200b5440c0c000c103000c2140c000c0c91705c112400812402c403801f40e0f41c1c40d0315284880c1c1280c090601410790030700100018150921031000340c6107010f090200e429243d071000916202030312114840c41c0d000b01500300145c540808016007155070201650f4000d00504164001808503090054005c514945580301030000104200301c1000b890b903115440c145140c030500003698524443c003000150100001000c806140c0d9007031803421001c2030400d04841c20381c0006900c21495410000300c060f0300081001c080d2085080010084c0404407401d8104501004405c5036064000f9a44020040d800800c00d5040c41c611040ca02844004010408076110001c5182c1c8216001c0011200071610b10780c07100d115034000042e1280c412030046298 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 545814703 1250 545813453 545813459
    0x90c03050c042a050f070f0507081209151201030c18050403120203130c170105160807110304030b0f04050c090c030a0b030f190b071e0e0f090103050c01120e0601 71
    0x54202c0081e040840f08104060100407001c0c02414000c108450052260458045907800c0c02c90a000d02030b40014065404512100e11903000801507401c1001d041700c0740358102c800d012142c0d00758072450640b03155015240f800401008110070307240042e11141c40c800388005403400d50001c110f500586014002c20f440d0b003210701c11568142c0003143d000c209205417021001099803100101a0950044075020302003d040140282e401d01c107c0d40d0112454039011700c601c0c0440c20140150310058940c40c10000d42407443d070000c0c0c50400460b8000c5500031142441d600e40f070b0406446016041d601210303030b4084c1e03455001140c905a00c0b11401904402c01d010b1440c2c541031228401000c2d164901d603058061300c0c460741d007522070900c4001c000e800141403144640465142614644100602c44c0007406800b100c2c61991064007005440024100d040407280b100007040011224440307620581e902190020020080000110301069002002c0e2600021030f8000c804040030384450340c8585d556580054010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 545815953 1250 545814703 545814761
    0x90e0d02031c0b0d170c10050609040b042a0501140a020d03020c01060806042910050613090213051c021305041403070803040c0e0601080a1d01090c03050c04 69
    0x3da0400c4a0040a01c030801c10103503182d8a903800000c08004030390b0300201d00c2c0611400107008510003004e00703400402080c44c0010014000d590098005001440c44a00003410800c01e10301a42c1121070b1100f03007030a0b070451201e0210548129004940c00140e0100c2c8500d00403000d54295240880a074000d0003920b010210110001d40005869684640d01d454000541c1d400510129028034081c0a40c0802a0491060390b800f60210044500d00030000c80c081050555103480c41c4010b41c2c404480b00c5545603a441c10031104503441d03810405080d1710002c0c001900c019021012412600300341c42c1f0910f03411404c2422407400000d040e010f504031555030552201d09007160f1026074072038803880510442d1200168943e00e19001032400702c0c3ca25100000b808240269141120000c000211200f205480d01600082080c0030142807000300c152100c600751000c250754108080e100310341c04c00070032603400707542040020f01206210680c0c550003102d000700c0f4a81007e0088210140c0c03880e00400b0009000924 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 545817203 1250 545815953 545815961
    0x6031b0305071e091a0403211707020606010f020727090b0705030a0e03210703090209090312010506040b0913180605060f0d050d03090302030c07090e0d02031c 70
    0x42c4200b08490203001c03905106140221030400200756960903c070505240c0251042c000e00c01c4558180384041c04100005003124800030210310300180c64002d0085120019030380032080c20514400308201d1001c01580c1680041c4940c0314004c260f031445805105460282c0c1c0340c19181c09081304240341e900c0e182140c88286007010f000c1c001c441d440002c446000e40c850900000064034110300080001091000c07444c4203010303400c0195142006107150417000e9008160100002c542c1c8a4840c100000244081e8020307488200c21540140410420341f900c091681e440b039200b0716030b0344200901c0d903001107014282103094405942081a071545410408010801140e0614100c2c00200f51114400007070300788625030b44903900d8412080803409040c1882045590380a920302d2500854842c4c02c641c01052001520b5034514140c0c0c140011060f155040807400c511602d0380802c0c07240719010b0001403a56495009034107880c502c406840340405c0e804400c0341c4921409083d03100d00b0382c01450468400c0105d80c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 545818453 1250 545817203 545817211
    0x3010626070e0d0218070e131104030b09030705010e03030a240501030e1c02010b09070203030402011d0a0515041e122d0501061412100c140705070f06031b0305 70
    0x71512140c0b0041000e900117000c3c1c100e07420000201d8108440f40b103410400ca1201d807050403801c4c28491028100c0e8412800d0060340702c050280881040454840d0701c050049842d00740e00280240f008822100045940e6170060b03400714000342c540058451800740c0c10303c0410f0281401d03a15445090b28010046000c1c1429910344e1070f07903001d02d007031042c0c880c980305440c54690201c1c0d8001081c1d08461101700590002d001301100259002042007100503a88004a0f1908a04108241130f10001c40408140c28002640102d5000440300142c407447c2c8a040028000315106040740304500b854a50880c03a0003034241c45017098004c114000c450002d21402d0300c46203034280d4410400105e09188421102c2d180300914155002e0f59a40b07030030b01c21441903040038800c603a010340c8c1003981031b40741e09102a40d1314039564161403615542d004801015100d80d9018401540001d074060702c1d85c0079400c24503101da00e030344034444081e2049040014014001d0081851602240b400380941d10461002980a010006c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 545819703 1250 545818453 545818459
    0x180e0c060a0207052107090621140d0e0909010204210201180329070207060c051212010602150c0406032a0302040603060b0903031611040203010626070e0d02 69
    0x10b00041141d440c2d0080e19201c0121310040c101100e0301e84031501b418124650042e46109050a4040c4840741c0103a06e42d100c26084140100030495031402c0a40403c04c0c0b540d07214815000e40c11284000c1d941c001da03e8502054115040e44040c0ca40d588914201d110358442c0d882042015140c1c1c130600f100b807440c040c0003240181442040f40c0c20484014580a190382c1044440300d5203480c2c103500c0307000c4c1c49095114140c0340c48614081414020000785d5112a00c1c812170040101c150700607000c0003418080021401400c0c40c02c20b441d942e44650410252070309020703c070010320505181c400a0001404158012404200d0440c0342a04102044010313103800031400540b400e072049061128050306106511030805541d00580300c83c102200242a00e15a6004154403001130040d201d00e82d90200440303114801c7c035203140784101d0907480c3c03c000090907405a25031041c4080300000340e2a402104003c4506a041c040c5440503004441031502c0400035030f16440011300c606042c000c5407c10402c4000014001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 545820953 1250 545819703 545819713
    0x609031a010311151c051614031602100516020f12190e0909030d0605030c031b1302040e0a0f091718030604050a0311150a181b180e0c060a02 62
    0x300c004039605100f203050b8100785d40c1d0010084070042c45143c02c85002d0852505a401c6072840a00d000781e40406800c0d05e400000c01c116842b1064020460035502d03480004040c829403034519440d0189401d070740400f80250080c0c0d1144030503600042030000356010300055080c201039000c04104410542c8800e50070520650201032041c0da624005203900c1480381200a658602400c0000000c0e200c03d58031843c001c0c1d015503a1906a941d0101e0f419002d40c070074410007035064182d00002641c01201c40c119001d00c03403000034003140869991010724414811031009000404040580004440c0840340140c000298100d6107076592442400501120300b020211540414012000074103000050b00c003141e40e507110005c003a041640040001714058a1035025103403925070005021151000108201c3c0700c61b545000700201640359500044084c1c0d0440304201e0184d0300c9003041200d030b80f000e0040415080082020b503a004010740605401ca8031000050001e4035505418084503802400601040d4010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 545822203 1250 545820953 545820967
    0xb0c031611090a09110a050f0405041e031d06070213050a150e0906010602030a0921060908120c090f01031a060f07030807091a0c0a0506010609031a01031115 69
    0x81e02e4816402401d021000103a844990710346400000929060f030750207415014820441a61010a4003504d00ca00b0390340421541d4441c038003150590807400410b500c0d0703041c10100c030052681c002802581ca2041100c44481e00304070b0000c1007514068000000d601c03841d014207020301c11150b60895604141c40e02008240401100f00102e00bd081303c0d0080403050b08a2010070039508002c20032140181080c1c0003a5141c8228042d000b130880000d800380c80140d003400780c004030546140103030245055400c48d004000400140c541701c14980d00100d9601810003100c4040b40a04d0500000c54807403420042489a24010110044d8041d000d840e000022046401c0300000c1355480c0c4070002c00101101300c06982d80c41c190b601d000340c0003080103042a02000030401e81031142c40f042d0142d2854400b06080080e40715003034840e41c00d1034582c124800503d1400342000010b001034100c0640700969200d4030b644602d101605d822136290310001d202c045c00740b106800c00320103141099003e070680e000081d6280e80c9409a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 545823453 1250 545822203 545822209
    0xb2a07060e01061508010b04030308011511011e0e0606010206160c05100605010f05120f090c0a060f0e0312030c2a150a020702010206010501030c050d060b130b0c031611 74
    0x1c80344c0c800081440c0e8445041c035010b82c440011405003130012002c900f01800c6445c02400360030140290000c00d003404515443c0207010b45040300c0c81d01040d41c024440d403120500e1043c8001039108410070410f003051041c01c02c0440100c1ca891140310103a00400c0b075591011082000146190800c0051240081030540840d405102c0d80904000c65500441e01514102c0010a403100010300c4904003c42401741e1615244107100c550b0b040566035007030351201e40701c40b040542070400c0301800c5544410038020000e501504400402e80d005820f8994210941804042c0750310790324407016202d400e1744200001100c0304490805081002c801051078441c600080700810050408449680e1031035010b04500036007548540c164641c8400d50b0744080d0306000309540083e55412060045505054940440840c01c620910540380d088010741c40c24001c0f039a441000c0003c1c1e40c032507100c86126000e8240c0c0803488038003c0045800300c0b9664801140750441a210201c060000740008646100c2d80001381a4555 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 545824703 1250 545823453 545823461
    0x1202091909140a0c0806040503090d060b04020711031e0307060c0c0206030f06130b091512330108060408070c1d070f14040e10120b040b2a07060e01 65
    0x906000c00a0501103404d003001190310615038840c00040e4405401c0000246001c0242c5540c000300703a4031207040c00c48901c1e0040c00340c50040c55040d00a480410104140a92140000b58130b0106405a030244d00c0620030f0031408010481c64441e09500400031700001605580c006000e030b00f0389203080010b041455000410070703401641d074101075440041c10f114040c80e1544008001024880c0c003042202940340c0403400c02d14000b044016511214040704000d070319200310320340300c00300316900b0b540140c0070b1201079124039030714195142900040c5c1088200c80240a800040c16207540714010407040d540ca540e20040d40c1e002070412110003030015030019103c071640244410305074600302c1c690b000e4541408001e02d0600c0e2080000c0422040344001c1101c2c405d04000c42d0180c0e954504e424086070b171031703144c103603002402a03014281824003410482c1c14080600c41c224051807180400710302680302c1c00c1041460001c040d10300540515000914070755075001400030301200b440b4035004036905c10310303030100c81c216 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 545825953 1250 545824703 545824733
    0x70905040308070813020d06021c061e0b030103050c0d0f0807030e090a060b0d0b041e060314010905030d0911090403020c130509121309020409090c1202091909 70
    0x1003442c15091210540d04a201c8661050280f403c00c00034241d19000181c1c05032824201601c126400111242c0308050300300d51513a0480150070602c074180e80c0702c51a0541e94a0800203034483c0d44803480108042100c00c040b05e040b250000018100b50054604201e114002c820007160038480b04000040081c201306c020705081d5003e520382560a012110a0141e400c000030001c00e40c05181a02c240321010400707058a40030a01c0100005805c1c03981400305000b07040c041054050080343c4080c200f500180c980103c016a07114035804c4425102d03a0001d642079550707038000106160010700408114004d030343d0010400c03600400b101d88000080e0720119041c2501940e040d40160000310f600d13030660401c0e042688a04038280001c00440c81c0605145840b40c03c080a105501c250000e01080240d0031191000c0140c041194210b5965130303959070f648001c05820804883d80804e416000130465002c0911106654000d00aa03220381e0b119040600c001811150700c0754119030b03910154004c030741100030017001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 545827203 1250 545825953 545825957
    0x2112130c14010801050102010903020615060408011406040c1806031a120a0605090c0f0d031418040b0d1509021207140414130b07021e010c030c0201020a051b0709050403 74
    0x102001c0010482001600401d06580c14584144006540002d401c0c0c0d0003240310902414490f42040001c0300b0344229400050380d9820101081a40008044500d000300c1c01141c0800c4802d04504003a180741c05c452002003910300256904010395070087d00074003900c000000c0300396001030f0300c031000801c281c0000840280c10f9019005010030000c0a1058540000100004100301d1280d50000380709807100c0c051b82d6000c1e810b0f840c2c1502c10076004c0c1da401c03001100101401911f50403456103103100d0b98042c5d54201d01c00d6042000140c1c486c10300040080c0869046140040c01c00c006e503110b240500a400710032600000502d10304189030380180088009490742e000008200d13001a8100f2050f0b5003000c000003042a00c070303002d00020390301070800040b515500c00500784080d031301c400003a03040c02402030075445c1c2c07071141d550380382d031204010342c41a4a912a5a101040003030000d400c202d080b405a4108003010807400c00c1a12980c503081d40f00c4018080d002130484a0081c0c0f102c040b0350503a00c0503a82180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 545828453 1250 545827203 545827229
    0x8090607150e07050f2b0803090a05101104060c05070b030a150509010509130f06060f080f01050105030d1803061a031e0307020603180d05030106022112130c 69
    0x704010705104810040c0b500f100e00303800d01010440010303c120115010246c00b10991400440141b50001000218a4010726281d890b881d150003480d03110300300b8000c100e50034040d075481c01c03100e44060703c030703000700c150784803a18070b0502d800c00030140c1e00c4159070103040e01e0a2290200001e520038150001358862275150743c0c007103500c1d00d80c1b811180721090340340c000d80d100720600801406075846604003264461403211124082c4c50349404c0044500c0c00c0c0d0390001e050641030800c08115241d43c3c101c01000c031664034084564641c0080300c014203c07982070041e264503810084848800c00c1c481c45501120761802ca92007d042a560782e20841141d901c000c0d0048803032190701211342c5900c2c0a106a400b0002c610250001c0900e030007180300c0d2203108000000b0310841000c008124120501c3d20700301d040303400301022601400e0b136402c07000c0e2041e0024030400700103104491101c01d0417500c904103100045d90240c542402e00003410100c0020310320091250a0280200d000c5101003101c0b40061001001d222440381 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 545829703 1250 545828453 545828471
    0x21e04650d1506181404081e04060302091206130b09030d021206010e030610030f082505060604060b0708180a0b041517060904150e0c030609060907030809060715 71
    0xc20b404c201c1c0d45400c1e807800d1501c00c0b00ca003074804505003181c0c015417240030300d07070b40345505018119600b00c020681034020602140110303032560158001e00103610100c2d03851012a210003440d03950307030104a4002c40c14800c0c078410880051801e02126401108050031340c0e0a105904170000200e0308401003101060710f01e10207210140d60800700d003440b81c840681c00b81205152000c10041da00130280f0008103034021241445007405180070a54039034a59001030000311141106202c0500c3d503c4a05c191160701230200841d440746001d2113010105c868120709142006842c1e00d031708659400c02150b020104d1000d1406207102d07503c0c00e024001506a00000580365410107480364404000c1030801000c1c0b0104003900d42c100000761044c581e100700211581c8201d660743d4901001c984a0328151087c80c20b04150b0011104800810034404048040e400c4419580d01e803140d0b01e03900c40050710850502c0c1c03c100824004900b4440041c1003002010f030103a072030a80300f070703403880505004440107404a5580e16041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 545830953 1250 545829703 545829719
    0xe0a0f021011030a0c1109090a0209250309080d050f04170f09040209010e03010203071110050402010f0807020a05031908070903021e04650d1506 64
    0x8000300d046034030b40400071203091000141c2c0c80c820b01a00000384200d000c281020010102100321000b14081c10030700040c2000711055648600802c0700b24850142e800c00503014220741074441c9020240d220340b80003860881c507010b0740144690303903068410190420a1907101c45040c0206805204003141c041307114a0300f030a002c004101941e00100030004100031440803107c000003600d0860400319401652040315900588001224200b2290107500100400c2440e40c0c001840d44030b03158150060f1100c1d84c0040d5003460840d1401c0718000d02040843e060302c90036601c540402503010021f8011a80ca0ba0150b440b1140345410809a617900861203810302c1170f140e0b81c80304807550451801d0901c05009400e550000e1003a40000488018580c0c3d00c40c07009015507140d403c08940d040c81d01d4400000b0034500c80001e80f42d072101c414000e02402e00c0c9000040159080381c1c2c00c15590b803041c03004450007480d1444014140042c140c82503440700303c4107100f0740494201c02802c911000072400c0000d00071714160003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 545832203 1250 545830953 545830969
    0x1207020d020f0a0f0b061305070f090540050a021b0d1e231201050105040605040515040314070501090f0e1503120d02030604050c04031505040201030e0a0f02 69
    0x10750b031164200c01d8481c2e00090a5815a4900135030200351004140c3e1020041510f14410039401c01103c0e05100074000d10a401c000c0f0a031448040c1d40c1d969035083d03124001d1181d41c84501d1281c00300c12021010b83c0c03c5042c10040c143d20910490000e000706191949080c100f540d00070345004030101c0d8001502040c4000c0c0b890740550b82c40c46c43c03015101004440c14064000340012041084582da81401520351501c200c03100b80884680140f0f202100c1904190045541c000580044400164000100c0c9a6010780159811185d166507100d1502c0d0800d41400118407001c290100e8135030040c00003000103204080031141810b41a801006030600e00000102943c0f060380c405010031703030000b20502840d000d030181c666224003c280000c56510140c0d010034942841d100d84401c080f90041400c400d101d40ca07400640c0500c0302160b00744010344948000750580e100b1848000e224445d001845007500102d504101d90180c0141000138500e01181c1e1114142000500c0440320700785003115850852510082c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 545833453 1250 545832203 545832223
    0x8130f050a080303040308180a0f120215071d060d0504020f011103090402031e19141311180108010b030106081603020d080405030111040e1803090103111207020d02 72
    0x180e46109516040b96036880c0d2001510240420580c0000620301c449828184401138180600b11a503134034503801c011b17059040c0030703d04440d020355120084511900c001003511101c50740504000068036203c3d41525120000e001d06410818508040e030b0351981c860001c0c0031b4202241001080e585001d104210708c84802440e25418000000c001c2e050314440082541d00300e131000c0c1d1300140d990721900c0458047c4907a100c00075041504072020010382550a02c13510864020500c5c0c10300805403400200d41502e03038200c4100c4c441c003404061101c00b142007036800c80407414000e00460300c60510313581040c000e83c4090704840345d10b0b9111203485441e4202441380302c0041030504043c1128810794080c00e40301040c41d01c40684650040d980400c24401d11204032001880010001c02c8641d846407451002e9400512848440141d010f0005203294207280c0104108110b00015624184038640150000c180321466425041003d1242c1d512201e88584014040d0125800500e5101c020a0000303240500001c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 545834703 1250 545833453 545833459
    0x180e09160f1e080102040303020d11010b0f01050d020d051f08030f030f06120a0c05010e100206180a060e0109050607050412030818010c08090d030618020c0a08130f05 73
    0x100c01081840701c80d40c4000c00b03403100001c40c0c501a004203090408100c0e40382c0c10610b015480002d000082680000340e0346107022079525500109594103400500303d072203407801c00b50041c40304014041d10b588128000c201011300c02c00018100081c03c1c06020403501e084800c11008211035001c401c00c8903241a030640200b00181c002c0d880c0041c1111243d2a42c0009400d982000443c0000328105a6600421903544000d0104803a512407060405003000c0c1400d06c141404107004100282e81c9082c806100e0690035015001407640c3d0322416a48031050b100502848118041c400c160000100a8003583d9031490305c1070004240a001c0d800c00b10706125000e040b48051103404c010401c040347d4030600c9a60150f0701070411041a540ea0300c091907548251302884080d5503c3c11074200b0b042500400d6040c02501402c0840f800310403917a009400702c40c22070044400e20558541d50200300c035030a800800226084d031069542007001741d5182251070b008030040010088149005200802954100c20001c6c1400c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 545835953 1250 545834703 545834743
    0xa0908160611070807051017040323030702191106070b010e0c090307060f0302070f05031b0606010c020405134b08071a01061715090c030403180e09 65
    0x4404c0c807595801c0584207a42c05903103450b48000c221800b84003005a102406100b8080f64903003880c0017402c8601c44280302c00c412018141c0c00c1c41d07459a40040e0b07449051a0b07001045505020070301c540318070b402c0b05d0003180c0d40100424181c00c15126100a8540544946441c3c50030754180311145401f090010401060520140710481c159940020061708441050a03c124840f40d400d004401030300c500352010382480b0a401c0003034100301000005011034655051885080e030380c90075240d51103d40540700c0e940041c640071400000340ca010341c0099007042900100501303c00b0f040d034686c1c02160704810b2492510999041ea20040d00f01c0c1800880b2000503102084007145c3c035050031550194a414019050b80004520f860401060549201d61443c407030070020500d6075200300003004803005600b0550b007848141d0120b01d41c420596120b5024481c01800520b040d680c1821181302504020801c1d400c110310007500d81c1e002c44a51407407001601d24034200003c0d518110525620304040360b5102d01341c52080b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 545837203 1250 545835953 545835959
    0x1701050312070f0309080a0c0305060603070e010902090a05091608070f0f1d0a0e1605041a1c0212040c0509240607051603170f0304080a090816061107 66
    0x285008030340300707243d0188810012003c1ca0900b11a8000107420401c1544203802c201c0d000c0c000c01100c41811a0320031011248940c4d202070070f2648030502032144206914a800061200000300d0700036016401000d040c6280e0180c2d2400040e00f82380c01039400507d100d03a041c0d01d00c20002d600003501d07a0f0119450428110317405611000901c0d00b402d070032082c8108402d0101803c17400403801050005500018801000c240d00d55407182a1494181e0b01005001c0c4e110700740c11192030142c1c043d6402c540d80caa4540000703064484e0064003c0e4815010641c803005410711900d503c07203841c40901040c00a949900d0401d140c185032808110200750012840750f01d0b0300040265699224a000260800700419441c50b00070741c102061352402400001404c5020306030300d01d42010b610601ca0002c03070740500c00d0351182018000c0c1000309d600c103200c4600c0703000600308002000309903443e00510345c100161078035400d015924028242001c24441f0a10341c05488204208841e59201540c4c00208100002816032285 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 545838453 1250 545837203 545837233
    0x1d0c12150d0203030c0f01060906060e093d121101030e030903010903111009021c030c0204050c0702090a02090a030201120e0f0f010e0102070213050603011b17010503 73
    0x14204018015003094031000c503212080d4000c1060780c041c0459448078112800145c4880300300c0b208218070761a1410014081840d80031704011600c00c1e803110306001300040148842c3d10300c01021104020381d01078810a865841e2580c021603091100c8460100503408a02e4105043c4c59900400700000640d4a0f0b4001c60740c42080d0488d00c0c5400d09001a284400c59841411402168481c40d81540f07002803032014160040006ea6400004406441d4507403c46c6410104442200c0741c017035001440395041481240071103c101e4101c40c003909207901449000d0380000e0554008464801d42c412010986e40c0443c140030140903040071040d10300f0f41c207212004000c0748110603144000383c1080000c486280c02031545a12003403c02c0840c509a0360b090b50320340e0b41c05a41d1501c1b24071034042036290180c031040c460018420780b80410390042c21031150380512040d1001600c03000d8140c603415583c4203500003e14440a07400c180407000d68030703558a6010425580740c10340c1c00580c402d500a404c17110314071172241 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 545839703 1250 545838453 545838487
    0x30f0203060f0d020f041a030105010e0c03010308030907080d0914010806060904090f0f0308010f0b1801030203061207062604120c030203040909030c2a05010509030f01061d0c 77
    0x2103002c3d00c0001d504602c5000061910440b40007883d0041e20f8500703032041d402030b241000e10039950103900030311250340d894440540c6090b007180d40ca42405010300040c00014140c1c001150083c00080807034606079146d0340b40e1410b1041c0603c40340042580c0030010490b0420f445018030444e04242810790721450b161000c2100d922540280070300c11030b55009101c0402c000392003410070894003e900342d07108500c1032802030048072081c041c0b4400648089000901c01340c4000495807a50f5050940f0131551a00d180154003070742014002e40d904c000e041881030203182c01084004002c105580e05d409200c909034610690020413008601001011002000041444055044141c1da0309190885e078009071400d04030300f10300840c0c000f006083d051007421001d0542c0030703000b4050702e4040c89a0001894909090b110848500e2000c1c07104903002c424104019805203025103004071028051310380d001462034400d0700710340c01a00701440d41421400748809052411303188543c030440402500d0310b81800d44000074040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 545840953 1250 545839703 545839729
    0x18060e0c031510021f062912060604180f05010515040b09190801061d06031c09080709051504060f030602030c1b1507021f0518030304030c03030f020306 67
    0x34121503a4043c141d41c400c0005080180c03070b00c400e900c6020702e0018408060b1a01e44285290b044000880d43e07070f000d902c40740c280d401e000c014514038640707100c00c1265110300b14000c15242c0e02c0203042c0400a2191040e903d6030307030f03500521240040d142e404000c4103c100c03941030b000b0310b00855010940e03400039100d40044400780c4d01c50800071a106c4e080e240010340d140700c0c00e000c007400c1c0b040480c50005908a0542003002030382c60b851100c5030356030492201c05045450490741e035903042d13100200d01041078071101d880700040703001c0d0b14003241441d442c0c214091400001c2e84c0000e0316030703649000304200a0303814000359504d42c00442e800e2001d2450300b540e0001e50180d500000e407040750b00102080c1c054481804030380214046100e4041980d4903020103a4856200c601001c480542c0780c00014000c41c0b000c1001900c40341d40144070110028040b246200401d17004080e6403078104034150400f820241080550b08c00c5109039241c01882d143e525004041c1c410307401d80148990700501c140041540c5a08c02c480c20 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 545842203 1250 545840953 545840959
    0x10b070602030a0b030708070e15060f03070309050105180f151f0f0906240f03020c0127030f0201050115120f0f050a06060504030506070c0c18060e0c0315 68
    0x6940b02c0503c43c200a048000a15605106140d80060100d401281e15012643c20916202d00740d80d07801010020103000c840d110380c1c406401c00042113915004c402540c0c2043c001c1c42c0000e031281c115640c0c0341c01c65900f80d07945034007240811014440c010302040b19011a48034417018001800805080e50f120b03482c0540707111580c01e1001200035040c664001c0c9100140325620308400c4082c3c2c2c4081101c000c01c0303507009003007001c001e030040c45035a40300141546103c01440d07558007401c4220344400718000d40190074030070450b54a88120511940000a000c2e2444040e40c0c1d800154203238a01c2c014001c03082c02040d803025641854010480b64040c0c4110300500c3e4590305194000440c484400c50003004115400042180303031110950410040d50320242c4039004c0d030b5101304809a02c46400744ca05000340d10009000e603000d400003484044c4103150580c0c5d11403140d41001a501d8030341c64034003414201507040032005503603a201007210340001c000300c40d042005030b6809490b5040443d90b8a24801440b218580 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 545843453 1250 545842203 545842207
    0x180203070e0c0c0604030503061c02130b0d20010f1e0e010c060f0b01021b030733020102030603060117060612070810060302100e0604140f04020307020f06010b03010b070602 76
    0xc0d05181c0d021540280f4551098400f01e01d0a890050030381e4005a030b1150103030740c40f45015a02c549100120350300701d9400602c2e4400500754280c4050117854810b04041d00001c4140d0104001000a5402c0c40c5904d003103652000c1c41b14083c800100400c01e0a0355440403c00d15030002d142004415010039010700d4a45040c2c22881e4401006880400c1c2d01e0344000c03c15840c04a0122030203400e90b114054203a03090742a00c015409003130740c0c40b400d080d84030b26040d895000040c040040d0245840201030444480800f1054040c0c0394405041558000c00c0080c003607500082001418502408998050203481d0410740314440102d910319501e4200801c040d0013100e1075040c02c5540841000040b0043c10800100c850314071500140070054486480708a000f0140700a815039110300801f207403012000081d0540b81000c2c6441d10700251a4021513040b43c11514002110100d0346039800114454101070300100018007000c907100d40303010720590204103c5442800140318180c81001181c15481e00081d000da = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 545844703 1250 545843453 545843461
    0xd0609050a091509111f0806010305090c010e0409020d0b0406060b040f05060d1b0c0312020408062a070f1e0819030e030d061a04140904060f05040b060301180203070e 73
    0x20141700550491583c400e103a410881040e6980300320004480b541c075900d014150f10343da0019000d461094408040f550000c48050318203501c0ba91507240030a100034000710b00400190040741d43e8480e00b00302511004521010030090044030b025401c020a50810341a00e860704c1d0094002400380d0500030944100d80006800106c5119608003200303c2c034031030410100e000c5006001402180210001310082649406948100502403003510115040c45001d0315440e41c454507403111032a0b9690260031a2600f03500c0098242c0c01c00c80151104c42d01c540905c0c4a0800c075030a102c0760400420002094144041250b90000f40004003540d060b1034240b44801b2000380075003802d074003500030710328080c40c42c0c80b0208000000d4415500440221160000c4101d61001440c034504828030036401b034a480c07051a4020104941064611181d01501482d40041c5500311010408141e400c16a802d43d000006007040c8001450b00780320ba44510552030303030ba0868581055000ca40c6460540c4610610702004000003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 545845953 1250 545844703 545844713
    0x11120708070210022401051503060a08060c1c0b01020c010e0f0d08090a0e0f0105150d0e010b010f030903080613090b04030206040506071b170f0d0609050a091509 71
    0x950701455005140708401d000303100300290b403540c9904000c121070120800350b1071103403441d20000c1d05844010308a89040020080d039149141e002030482030b0040850000041c804400340b08041c02000d2401140d90398011080f07140020024032050300e80103514041c95502c0701d81c1c0011301b1040c0c6003402c1c280440c41e000b0250001d800b1009070403000340c2002c122010402042030041c000c004070542200c6010040c3d444012003c00c400c070032200c0750304911901005110501d0806003d103161240960b00d146014581c02410040d40e59500c41216031340e4540000003160341e000400442076003090b02d010040d40126480042001e00c0c0944040c1c018404401501c000200e01d801c00080c160b040000822036044c5460025502d1104582c15502809110081140707075100c1d0403480c03d0f4030315040c00c0e55580c00b0070f1349492041d603000008461803e00100102c504803000603024011a03010750300001146403614510350b003914001030960402c2c510f4030852200040084c0001c8802038101000010018641c6c500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 545847203 1250 545845953 545845957
    0x22212a020307150e04060b030910020c03090d030804020a09050c07110f0d03050c070b0703080403050901020c0310020a08221b090906020903010f15090b01090902040305160611120708 80
    0x12000b1a90340d0050070180d0f860b0015040520b0309020782d42003121954403081c01d82180810b9584921603000000059859110364010b86410100d4105980ca820740303c000045103030746941e808401103001141040254648040800024229030a0a1246261a1014841910400d03d005100950300004c9505031b84400c82d803540c0c0701c880605072180f070b42c55500340034146800000402c1420700c1340320804a0600407840c00e64807481e80c1a15041080d8945030341c280d8417600710341d4180d07045102c0c8038040d400e03a50702007009480070201a0310060b5110505000240959002441d4003a40b0039804c01124000c1c014180700c0342c40a81000b101c400280c090000b600c0c221181d41d100401041c00c100621090021550040403842002c41c0200503600c3c110b102c41013540c8001c80400390100040604001c0c0100310b4001c140007040501d82002d941c0d0310f0744086808ca8016400a848a81c0554060391040c50361103501c038083c02040c1415501000c1a0f083d0030354900351300c0e40c0e4840318031000c680340007000b9030482 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 545848453 1250 545847203 545847209
    0x5101401110a05061f09020f040b0c0a05150910140403080c30060f180606070203030c100605011e0e0a150c03090504111222212a020307 60
    0x10b641407400c0011800010085100352000445c20548000961074141d01c203d41005024094080c14a480c1030b07c50b001ca50400344140311030f80100000600060024003022190000c0d0805261031810080700700c511f040c1118040d850040d03e400c4c9121030030600c506807280c0c000d605282c0030030241d40312a0701c548030307002c1c462030104504a0125541c0a841d200180208080c6407498103840940d101010400310302c0103001e003c1c0d00070a595034107900e560500d004080c3e100e0406004117181100d641d020034950b41c008581100c084c0c00164061807650303642c3c090b0200400c800d1a000c014015141b203c120319910144001c006e1050034458065181c5690b00006c000300000b031000283d00c1007071900601005d6013600d003200021521500455241303010300c07503481c88074181304280d81811441d480c801090407000c0c0c45840f9910b0030030100c506441c0303030784645003140307115404205007414082c0c0110542008036401074248400601c110901c04103440880703989070403494240700010810300209080003c01c0e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 545849703 1250 545848453 545848463
    0x604050711070f0303020d0e0f1e0303040b071709030d030507020a021323130206160803010308070b0c03190b010e040c3c05030c0904020a09050405101401110a 70
    0x3400080c41106500f41d0104481c0680c0131355407420000c40342110030751220320b0300c158050010f41c00d040f0704d414021141c619200411090013110700301e010000745036030001e910180704500700041e56070400c61131058400c41101500c91080c200380d05000001d80740e11002c40d0309410141eaa00009003414400c00041d040b9a0b0041c10013a11314100c07101e40d1010b03200080400324000c140d14403420301c1194281c000c500c00c010500204001c0e502a60811416a0003140c5400f0803841c000006000308040760700550007548501c52280d41d0703408a19140d00440001040c0c902c060f4401d1003004201c004118044056401301000011020340010040e119156041450dd4200703140c40d588501040c1c0080340e49001c00443c0800318540080d80c0d11480880306519a240310301030306401c8842050340074402031600415a041c03043c6c1080c00d03850121301246c22031003041d000180309400c1003085080522030190404007440080f2512810080b0a641c6080c0d061291410412020713055601e042043c060942265448 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 545850953 1250 545849703 545849713
    0x5011b0605071d09040c0b0703021006080309150301031e03051b030c0c030a1a060616030201050a0501170a0209180f2506020d08190504051f020f030604050711 70
    0xd010010070f00003a6503e10348032034a100d0f45030301c8246005030081e881298854840c049180c14540745150316000700c841201548151070424181031030030b000382d2010b003401c03030010354860244008108603200c000c504500389020400042c40466466811b2032242c1c2c02801e081c42e1400390900d41140c240c4618420704201300b1210060040c090070201c01850032401d039004039101461140700700b688682c4203440041081141450048407499402005a48101c0007000e803800d00c00040785040b100d4244600481c010703503444081000c890168032806002d00551140ca48050900d05085139944651400191051384410009810041610650220703507884000340c407407807150b5100b030399520840140c007811036500140301c100f0550740482c0322200b1148154010140b035416140d0680f100b03000900361401448052100a140d10002d005450080e07108400400b1902c0e00040d07255541ca246040a010840c01080b040c44900b00000c180ca070015003c0b1800102030303d176050306071800d8944100241140c011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 545852203 1250 545850953 545850961
    0x20a05160f02120c01080402090402040618020a1403010302240f040801021306030c080103060509150c0a0e0415051c0b100e060109061704140304140102070503150105011b0605 77
    0x428039407202030302c0c820344095211071035000e00c054450704100c603032500054560002034003610301a04c1c2d840c0c12a00141c40051801c4d210500c4003411032600c1c0c41031046640000b00c03440321540c0103504481911950410600315411030b400140c1080444079015003100030340c540351807813220500480d40440c1c80c021406503510303039030503009010f07402c258125690001c0c0f4610000b061406801007110494141e52410321603800c5658282c000c2c0030103001c91005100e959000e80070038921217200ca0003000101e00f01520341226040003086c0c0306003c0b6209001d00d08208440507800c81003400c40f03094401c2202c0300d01c00091343e088600c500311001750b005042880d0f1101480038203d40381ea027242c150f071414103000d10320750340d03860056800c41418841c0000141c200d4082549810b810039130542c105114612900041c0000c1c0e042074a150440c0e045008031400b1514030740455030701000032100802003079014014a40c0b200646140000c8144192410b01040c0d410b918a203500d60a00151440c0c0d000d0020030017428 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 545853453 1250 545852203 545852213
    0x302060a1125050901120804032402031e060109030b1b0906040e0906010603020910030e1501081608012a0c06020f070606170601050609131409072304020a0516 70
    0x2034420540600d007044000b18906403030784040046d407070b04001014a0141f0315039940d0762075034504820f540344001c40000c0c2566042a800118042c0c40d40c2e18403200c01c10b000c0300e20160b580c1005080036050141c05641040011580b80c400d6a1024500c0e00c0d03074003070aa8400b130800741031052030082544004c0014000c1030500b00c031010140251088070485c1d481d030ba03c41c6402e07000c900c102c55009a000406105000501d88031b5000801d5045c404000e582810b80021458803a500d4282c0111000d500410b00040084070540c0e181c0c402090604001d11a001803030030403407410046021444814881c002e840c0301100c0c0210b07001c0d140c1a42c00442155900001a0f0300c1c000c03030300401c50450f40c4038100800020740c852403d60230010612140040c00c401e9181c541045125842808825040300c0b0403025145003e0003403103411507914024100c92668549403040d103052045580042e182e00101510b014004003d081903a041183d050700e0050780c400e84607006403258080d003603220b05804103035800342003085 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 545854703 1250 545853453 545853523
    0x20a080429130501182424060f0e0a03110a08061602071202090a050403030f0908070b0604022502060417010f06050915011404080a03081f0302060a11 66
    0xa80103c000b0090703e107014008495205041c04c0180601c000f01c412580117015005445290340300c644000903820300c0030341042980c40c00d900c1e6084981210100200038503504418003004541c520301e80342c40e01c5000e1a00040c0007206500000e00103100e0142c0501d2552940f404d841c0191400d4001c54615141200746540e40c091140c0000c030042c060392000046004c01c1c22081c0f158964002d1541c8166276035031110740014000100194105600d918084807655801d2090a040c24029050255940c04c2030400e0401c221014196074001ca00c108440d2148041c0d100003003514107a501d048021044c0d40340009246d50103540c110324640b01c3c8180703490394080b00c15845034111080703c04040c01299a282c080025500c8111a0101c03155020f4201c0c00c1c0e00e40c820280d01d8440101e001c940c41c106600d98041034a09128808110003145900050040d803110901c860341b0001c030907a001c0a603650540d40450000d00800c800e00050001042000540d07020a1104a403a0300c03000c110303981d01908041e4800000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 545855953 1250 545854703 545854741
    0xc0601080705010804150e0106090216030224061011191208010e0601050921061906050a030b090c120616020309030a11010c080406091503020a080429 66
    0x144240d441c00101035000305030841c480c1d9048903d4400d081c030443d02a002400701c80d0000882550b8600020403046440d202501d41c100255600261422580c900603242c1110080000342411600a81c10600c1402034039540c2c1c80f00094403401c9802420700000d0380c840301c01340b030564041d00848850f0303050345c24000c40c800728a03806502141d52415541c00182d40da241d0078040c1134a4000703500700140c05075009400918240700c001c2c0020340d003400440b900648802d01d81d54154540c3d04803405000d000401d12000020400b103020003003084038a4540042c2c07003070343c0501c4010483e00c3c2c0c205c001210080107000504020301e01502d01c00702948681c50460f21007408860400ad4141404800d0313500510000648030072240c0030700140340d0110075803981c803114803844483c03078100207855000d0070002d00c500d00070744010011622000340c56800c20085551441d12088604105441030050440055201c1c460311f420680190b01842c8030114500c12110017440700c1c00e9148000462010300c18054032661b045041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 545857203 1250 545855953 545855969
    0x10050d0509030a0f17040314070b09033004030e060403061401060206071b0209060a150302130b0f0a0e04110a0e030106150c120207051c1209060518040f020c0601 71
    0x5085500d88242e6243c85084983c2e0313407943c05c020014000a0190358010402100720708800d0070700c0030690300d0fa082000c0840702d603c3c3c65080411045030700502007650034020040b03000c5001c0d100082c0414100116801000542000b00c99015000140c0301d0008030b0f005980c008005100c061158607044065040a2240100501c601000581e601c0d02c1212110074200901150b440200c81c20f80801880c003801030f01c0d05500601c034520000e00c209003010410f01102140d1409078075121241061031440c4a80d92002d010104100300070010486001d08644d01080c0300d04090f9842951980401e0050043e10014400c204000681144260300112071a04685086000b0b01c0031580300d00c21881c0429035903030010b005c289900480d00000b4540d00008480c500b03184102c400055980c0c6c00103007003c61500844e96070351141030011060000341c2c0002c2e20301044a05203440c1c114134000b8002c08621820304001106811010074070031030341d50f0350482c2d5011066210295152210740c1344081e1168000c0c411105 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 545858453 1250 545857203 545857217
    0x1090b04031b09050c0f091801120510050c04060513030203030315120106050109060c05012702040e06070801090b12070b131208030a2d0e010b12030910050d0509030a 73
    0x10120124041c00788640701018105081c48a071400c0041d42d50000e40e00f03698005230311281c2c41e04540b4040c04890003000042c100b050100d589052540c2401d01165110000c5c2d418101001203a44180d41201c0413290285042daa0b10740c1414090000c061250700001d6140c04000144040c0c24454100700301440300450b0002e040904c1481d58900f20340c080d00c140d0b80450fa2403c810030003640107011f4050100d000d00c00108089032900070403132603100c51081200135101006945015410148102003040d08000001c050390306000202601c8500c0520031000d00c65264602115151100b84041c02403640500031102280e45a44400c00c03960170480b100c040f44606417000003450402d4800784a4100d030065603180c6580c469101c40c401510382c1c0c13400c1c0100000c0360514641504078001801203122080d101c0014146205402c03282502c28104146200c0d8850b51003111859001200b1611003074070480300c58207542c0811900782d5140c001c19580da46407926010800c400c6403400300050010546540c4c0380d031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 545859703 1250 545858453 545858459
    0x20a0210020405090c130801050907140603061f0203040906080303070212070f02210a0501150807180906142a121501092c0c04050607030e01090b04031b 67
    0xc01280035910540ba400042c103004079010001c201c0c028201103c10360740b403c2903192035000c03480c2919002c0d40c45041540c401041000000e1030206644994001100d6046c03440c1410000195030000c86201015480c10181020031060700030022074004220f545018003a030b598988090303072a034008481c13031000340c092400900c0f0002075802c100c0d8422a0300034847c00d500941e035002c1c854407210120750b11203141003901d00207000110401503c00100c0c402c500204841284c0504550410b106600914103540003080c1440448400c1080d00180720082000280354a100c0c1010400b9040710040c00c5070740c41008050010302c43e852080c1005100d405c501c02c0f10b000e034954103100b000c1d214045807896070034043c00204079188429584a403000c0d8051405d1074040d0345600300e019500c1d48540200c603140303051000041808085003425540302002184c0c0c1410649040045003983c030881034010304200080d001001142c0c000e1807090060904444019102c0b0745a15261202d04400c11990040f407030049800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 545860953 1250 545859703 545859733
    0x303051605040f2706090b0f040614090405030714070905010b04141908060c04140321030a0e07030605150901051507030507020d080310080307021e031f020a02 70
    0x1e03403c445441c545078421902d0007818010003001c0b07403001104500028149000c04100d401002c015010f0705900040b0414a1400c00001d42c07100310030180110305002c400c0044520004020401a01c1a544401103aa840c03400c541544501c0d10010503001c0f04240708003034000c0000d0340c0300c26a281c64204116598036003d5211550155100b29580c9065200c2c2e43c080c10306215103a50b00c1903203128024540b05884203a1142041c1c0102d030050140c0703078049010801220620034180580c03d0503409000000e00c00d81002481802d1041d8600c164007001010481304c0c141640894040824103042ea40c45036200d10381080a010b0503500c407000080030700d042502900d841c910650486600408038010641c08081c9081d0580020b58107400340003040c4131803c0580c40d50007440351010b100d0000720340c1d640b03010303280602000c4140e04440c8645c1c0c802d110400058075817002545000d01e400300b040d400355200714000b9103402e07282014103505100c3c2d045882c0c901c0085030050300004290390240c5041c84130325224 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 545862203 1250 545860953 545860957
    0x501080c040f050d03050c01050a0b01090b13060c0206250b15090106081503120a0f0c110d0212030a030c0801140315131e1e08270a030303051605 64
    0x403402c80c1850080c04101c2844d140540c942e00c54800c3c1805401d0041c40c10680e82140d10480720081480d4850021b60269a0300540c408044c6c4105c003070381ca0900540c9503030000d1202c00c034041c0701c0511003090f05e0003055650340c0055894082013401e50b201c0c00c00c00c940410718824100f88040f10140180b00208036040c45011008201c00c0000c0d0100016a10700801100e050034060010f800f0b070140f07042c01810540b802d010b032000e070400e180c210a50f11b0500c040010b154800c0440c01808000d4805c800c030300050f031840602800d108080b1a480e80c0d210060000444080c1c0c50f00d001c1c0380702e101c0010819200364241e04072140401c0350751032340c2009aa0354503003402c034400c03a007400c103515030040f100c006a010100350555810010071000c04010031010390b54200c103850018002070701c24a1000f4500c007001410010703050040071401081141c8040ca80d50764036640100302d10080c5480c156070b40800d0304500500998805440100280038107075030b0742000b900600742a10120009a6099100078406001d502 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 545863309 1106 545862203 545862209
    0x30e12030f090c06031504020d09110a0602030c1203100f060c06050a091509050a150f05060d0201020304260706110c0f031c050403080705070501080c04 67
    0x1080880603040204010390a50000960000f2031300c50009a80c1c0182c09403001c0345490303414000240190181d21403000100e40391030038030028010803024000403403400355161300040d500e99404907140e100d40212010315a0100200c2c3c10180c500764011540690013000c0d4201440d1030b88075010042103e03a000300c00041b480c46c0f18a060000d41d20515401c40c1044404008415050f580d0703002c140c8100501c0c003d041d54a01940301030000501c424002da03079124281c1e1951642da1026480207003460403501160700c1c0b4020010f10542401d510455001d0340507002982000d103004658640c0302c0c103004106001c3d0062291001c60841d040101c1c0b00684040d44400303910400070f1182d80d14014008013141c1c8100d00111071602e01d40c8010541e01d580d08a4041050080c032121301090301c0b244180c1e44010074410000440d403040c0700e00400c03c1820f886d02680c8255403615412111a018001c40c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 545683453 545863309 := by
  have h0 := BRFrame.cov_init 545683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 545683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 545683453 ≤ n) (h2 : n < 545863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
