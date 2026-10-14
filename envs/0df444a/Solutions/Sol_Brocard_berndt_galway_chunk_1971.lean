-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1971
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:20:51.29587+00:00
-- url     : https://prove2.me/submissions/1aea2c09-e42d-4a58-8533-44ad672d8d26

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 354316546 ≤ n < 354496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 354317796 1250 354316546 354316549
    0xa0806030c133209070501020c060d1808031810020f030f070509060f0405120d0f05071a0a0b10030e0303060909010f1e0e06010b090108040302070b07030504030303140411 75
    0x1a2400c050341d26045001c9444080041e00100003002c040c0007050f000009101071088240600000340000b0300052510300c1070180898a1841280009810655039003028140c803041c1400800002da00203071001d4490400342407240f2000711100060f030207407086805448820105000352421480d07102c454905690350000007540ea15001046001040300130031042d40117a6a00018003a031524040c81c0701c3c1c03981e0a003002e10041510045d1079108650244400c2000254040410003060320f55107016074440089150960240fa27098500511103014001080403000036680012039481c0115000001c004500f002582214404072118946800c01c00000d440e0341402260f603034000c6030f44000050b0083c0440480c10803107211143c104019044100440c3c0c0744007846c058516500300c0303d030141025500d01001008039204204216050003100d4002a09041c0280401d030020450b1010b8555100b4003480d00400707591080c002140070901d4a40e02000709200c0c1d104481c81075a01c440030801c0b5203000740 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 354319046 1250 354317796 354317801
    0xa080a20060a15080106060903061103060a03060b010c02030109050606090f01060e0618030a030c03030501080c130903170c031b120601030905121206030c060a0f270b0a0806030c13 79
    0x40c1c80302083d801d055000944288240305400041c1400e13500c041101e030640c40d154041d2a500c8118106090003481031201559440003144200e0b5448100040c01d041e0010042c1c8180283d900080d500d540f820300d4080038401e011501030721810301190202010740d940f040c00400318000380650300015030001e8810718681070034802801c14042c0302a00045200000b80080e2030301120000c11000220b95034002400c05030540035007409080000c010704280c0c4a18800318040e0761845130714111040d141c011003018503000c2c0464060744031005119009074034260380d10909d9a0710580c1c600b00c2e051066140b1104c04112a000e95418054a1030420120380f9284c0046000e0302c2a01001c3d0b8007801406c4189041540c001c0c01480c0d03034410442c007040c55140c008201802c1103280c2c64030701d005101c1000b01108080d030090b4103445151060500800329011800542d03100000b80c18005d800701103640e80810b207440d24001500b00710060390b603200c1007541c0d40d405050f2a108030000c04c0303030002c000240c0400007000c182c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 354320296 1250 354319046 354319061
    0x60304200a0f03200604050f130f0203010e15032d1204080717030c06040305070f06050a0902130b030c12010f05010308070b01060306050108040b07030e0a080a20060a 73
    0x2440ca4410355280c84000075031000c03d90044900342400d40705600d03194003d0301070040d5081c04640711400c1c01e2410010844c98095645004d1054810581c400c01444860703020900d208260001191250307110140090744490603140c040549c144070454a41d01d00e800200030301d40c40408080c4107002140514101e00e40c641e4040502e015015100e400c0200c0e04000d07010f000113150b030b40b008204003480d00c2c04140c3c4113030b40e04e48048215001004001c40300d00001032034a81060b4913191190f070b11216824117401081406178010000c5003008144070b1000742580258031601c1c001c58400c881440c610300300b1001c8820500080e0b40640007040200175501e080500c1c01d0801c2d05000c004201080031220301000c59074240c00464000d000866010300b8803039011040707805042c05d403c082000c107007024006014410300820062441b56210000b508240c840d80000c441c5d01c4426080351a00142441d0860550300300703040f0b00d0006a001070302ca110305500d55055022207001507010340b05c00d4135040700200160414 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 354321546 1250 354320296 354320299
    0x2030a020705061018020f1905070b090703030e0315071209171e12012310091502010c210605090f0714030702031801031808030a0b06030420 62
    0xa1202030701051007840b04510030400c100c0c03e10070302414070240040300c400940c2c140792002e10511038100500e200b07400721400d010f405920160b010f10844030407100da01c1498401808100c040c001d000744c00900113200800d0f82e100752120480300c800d0f84140f55075114120101c116110462001c144968003600307403114816100d58012942e0615a210040f42c006850481c48002030005003e261641c26060f0304c000320003104100901d051074a90400301e010506004001d64500c820204200b00304011204122039500642114828040b001025018404c0d51180140310782442c01d90682103071061040e584200c05540b110312440002c401804500400d035101300380070a070360700c101003560f40c1c540120034071501050b1441d0070301d454400d0004004003031022540000c0403051081c40101c58010003903410509081c0b03074490214000000490141c40800201090552a50351107018880d81d2401140b041040c080300b0702450000314284404c503c8110b802a1051807100034240ca07041d05101c550401440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 354322796 1250 354321546 354321551
    0x1801060914011e200309030c090105240d0c0810060521060607080f0318150103140705040f0e07050d0c0e0c09040c03090302011a090a020f04033302190302030a 70
    0x12000314144c9002d03000388407041d9135440400c1154040c60f042140318440d60055901e14410b501d4680402c810801110b20494141e008501c040d926a0450302901c203c860074100a02403413950314400380001c501500c000034040308164020800034003030800c0354141e5241da1403206840c10098505c111074000544010f0b400340c0708101100108d50b050001e0f0200142d0100e0b45a580c2c1010f041a400d00c00c6c802800f00c50b523401c9188890007100c51030445504403500b00000e0900c03091040440b5040031603a40006600a1400c0105d4213110f50960000c0f015038445001c860311161220100130381103281c018018910a291300c400d00020124003400c5421011500200d0308086180001a00391003901c01160002a80c50000c48240740e424020640d841c0030751821000c42804040c00706000c1fa1004010101c419000a000031050310460308503401140c200f1801000c0001024295401001358001e504100701e4644448100c4445442140c8503120781a81400d411200082d003a0003941000703040c14805035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 354324046 1250 354322796 354322817
    0x1050711152d07080306040b030604080301080d080919020d0821130210030b0d050f031b03040807210f05010617150a090203030403021801060914011e 66
    0x490784500a60003004001081e9220703001210101c5160080d180b80702411861400407001035540340046a69154000500700ea0f20b03036031080402c000e000400b140725054820b03801000140030a0401950681744510140c034140e01880e80100e6203008162001e1840fa0401203842d170045c0f10141140c4c1c034540c07015003ca201a511912559910382010811341120a0000c0740508043e484040f540e901080b8260340ca0b0b000c55641d008642e028070314030014030a065541c0c401c4903480c3c1e40c0080240c0032a60040c215040e42ca9011070903516030700140b05000f02110900841c102041000c0243c4007610f080b00000c00301c071450300c216404003165207083d00c44d810700061200c50108a400304028030300d074040e000200d00d082c900416144209840e270208100d64111030000e00080c002c092000341c0000450401103070504060001071b0840c451640003e6012013a10348030f00e0350402d9094101c1c100c0c0d82035190200b00e0b581e601c00320140440c1e01c400040c000303200c01030840c0112441000d011550030b010300d040b00765603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 354325296 1250 354324046 354324049
    0x40609080c070501090e0c07140115241704061119030221070516020406050d0b01140a0308030c0307031104080c13060f0b030702010b030d09060806010311040501050711 74
    0x158441c403424003450704088410321844d60460320100007003040320100f0407a4901001d802c2d403180982000244620340c07051100340351317601c250011903104050000100d02c0c04da44000480c90451006981c2221b0030251000d115414001c0c010000e040350104440c04041c1e0b07a40e034070b0f03000402c0310001c8107030398100901510540d600b240030402d2a941461300c2c01a40e41c5a80c1c099050b883c250407085501c000f02d030404000300c039640201981c040c05a400710360180700340c013440014003030710481d00201d0704820604514000d0000b820307034140c1202c40e100300802c882050303201408540b007540d01010304006410008940301c900701000641e40106c1c2c03442c00240742c501c074206070400d5900c50340c0603464603801240004251b141c2010307440b00c0144900f03020000541762808042e4114000e20801161400100018842174002c0d040014844802801d0710748001c0342001c0034200180a014440c005401c0e04002402035000c0c0c4590350f84840d48041d2a400e044c80c040c0112070b20740c40840c08440c00c0e04085c1c8401800d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 354326546 1250 354325296 354325313
    0x160303120c02030319200304050f0c130f0207080331030f05071a0a05010f09090c140105070c0b1201060201020a0e100e0603010803180a0b1204020406080f0a17040f0e040609 76
    0x7164280d41e06e043c0d9a04003801c2641c80d0422920740d0700f103140c00424480b00203590302c00c0100c2c00b045c0c00d02c0c0089522600040791074003e000e80b001c0604020400000c0101502108051040c0210320560584030510020342c402100e00329110014045070400c884414017130300031005040d09600c0392140b8502e8501c5180e219103003049c107603010403900d41c4070401841207203820281078014000c412402c220140f40e40d100c06500e030409204d6240b8142111310a02001e91181040b1660150400034402845035101130305c1419900000d03961529612a03c00850a0351043c001c807401c1040a030748e000d0245800700708202c1152241c0d02d050013401001e0340c61048a0300d90754041c6000b0082c0c60061511101ca49080501440c0014039151107213201340e07401d00c0b1442c0700e01c2c140c03002e20401d0a40805241c3d00d51001c98002c10458008007014400c02414000b0000c00146c0200014801e441c10100322150301020f03c8140224040d1211901c918074042c84004500d800c200d0784103004a01c0856405919100e0703910 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 354327796 1250 354326546 354326591
    0xa060803071b05030d020c04020c0124031a07120c030f090812011d0115030207080d050a060e15010e04020f0a08041103150a02130503160303120c02030319 68
    0x2803140400c420042080ba1500040c8002c0400341c020340b52070010000003d45569007041c2052242d540416203008030783e405d500600d11280c00c03c035011840f01488040031003203000c40c8011035501e9043c8c05403001420600100502030f040036100c40e03031150030f42140c51010384011090b28040582e60f9142c40c02d41d0502d8011540c40380e01600c141135842c08074540540044205800400810a09060304286016120880340c11111035032210019a60b07a50b000300d029104101003c0c00c6924003181202030401598802030240e02c03890f4080001d50b64803a06140c2c1c1305412182d400f030110000d1040300c1c540d4007408804010a000030001407400140c820070414a401081001c40021460010001013103820004510301c41d808070010000c620b002107100b0440200100492040d13030300440c4140b021000880c2c15005004020300340c40e26802e036050380011505007448250006510048040d041c000640326001c070459450307000e1441c543c2c0c2c00b46950a2030910100c043c010540d00c292030750301c01194042018 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 354329046 1250 354327796 354327803
    0x141e031b03010b12030306090411060418050a0501051c0f060e03042918130c0315050114041401170406050601030c0806210703060612030212040605040e0a06080307 72
    0x6a921203041030508483c06040c4030350140646004682c2c1681e00001901d45c410402c039002103003641c89261190340c0514100c1c8040d00540c0c00700d808030f42c085c5144141845612414401c00540d900c1111940c103689007072041c550001d007200340804407200d650319982045801010401866802a5503403c05c5032410328500c420ba400100b001e00c210003403000d404220f01c003d0940802d42c00c44000e200d80d09031154101d4009100c91030855140da50f1501c41400340765032040b20042007190f80e003d40c0900504180400070b06405031004022420f036000f003c4aa0340b005040440c9400c05040c18004100c00260902c41ca06200b003c2802c0d4902041c1040a40d105e24403e07800810745042401c000760075101c04641d00010b002110701041140d480b5402515104503038860702d46c0e281c2c5d41c002000360a04899800c0540031070b0070928086031101c0c1560403201c400d88280e00300e40c401100c05c00b0401007030280e400789000084040108115039020a05083d400c0341010000180441d510f0361500e1540d486001c085 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 354330296 1250 354329046 354329083
    0x231e1806010f1e0e06130b040504141903050d020d02040f080f070e0f0a1a030708070821030a0905011506030b010306140d0b0a1404032304141e03 64
    0x284420800c0c402110401200340603c14011428001c00850f1060000c0101d4007a900c4540100124810b40c1c00c616480c00c0c000d00200308905003400e01c00b0075002c248064200c10b214600355040d1500200821200c02501036543c6428030181c2d41310300d000703980300d1401d88007600d0b020700001c5500d41030b0340581001006540000c00c51850f903951f81500344522903002810755000d0354204130b10300411001e1298000301d00c6900081c070481101890b805140342c240296014801c2c200042082500040c42800f070711030550072030703400c00400c045603100c4003c000c1501640d800c0500106084219a41001040c113106100105e8104021032120042008a071300900000b0f4a4014032101c3c2d580600c41c1c800601201d510302c12007241644089040d051418200528564004001a000c022140c3c0a817072103444031002c0074860300701420010b181c800d5190800f6a4605400300a507100c4441104448c211118010821060141402006005001c045d003060380784104000700700341c560b0705004800003245801000b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 354331546 1250 354330296 354330299
    0xa05210c030321011a0d0f060e01080a1a0402031c0509060a081501111c050415030902100903020a0b070201270f0b090a03141906231e1806010f 63
    0x100850f0a069211048241560300071900c0030308040b04550b50700d009100089100da074009070b424020300407948611280110200042180000802c2ea15866800f51071480c03a100184940364462100c01c1e2002940b5901c244100c0c0e5240b031281c45e410a13080c0c0c9504001c0e0a0000c003802180407948034a04640c0010152030400c400b00a43c0050404603960078030345030700341c0d14940d4031490f50749403260b00074a96407445210b140c45c420f200c4e404035409000c2c17841000b100e004020748060050443c00310100d10940342c041a031840303288184007903002c0b29001030207020030a1520108860581c040001031b1b0400c11383d100c542505100d030f4a5055a0aa50184100728113854211054900c072345a8001c9012102c00b0031400c0400d40d5100e8055064030b4000c01e042e202104082e10103890454141060001c00c21040c01c103609210a541c0070082d80b1099450030b00c0d0814918860070010b103000c80301546084680c0c004102d0340030014588641c0120324800c045000032030b00c80194076100c0c0980c000100c03402981d00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 354332796 1250 354331546 354331597
    0xf09040309230117280908041203022a0907030e0a0c0f05010c03020309211504110f010c03030c0221070c0803091e010201090b04031d0a05210c0303 65
    0x5200d64030142c4044190114207042c0040c800818082030802c41540b05c04400340340c400300b103901002c1c540f0b0344480b0955655550b020741e1190703203401c40416800b5014035010542c2511031201d006d0856031114104da1070542d0000104002050050304071010507a03100800d820f8904100200c0b40349a00038110319000501c0c0c40761800b00292581c104604011b605401c80e00042c0c0c00005446290900315446003100e03040540400c00e00c114004e01c2100742c400e003441c135040e5140401c03a480c0168000e00300c8003d5402c0c81403d10551810081080d80012010b12440002c03034480c1d4400140741d101841501c00305c6204040180c800310718009010000480015103608008000c20440000d04000d80a142024a40b500140300c1008a422142c40c480e0004001600f5030f2003903204241c081c1d8090781ca00340500702428000d014400060400741030515544d4001c003c2e10382803110754101c0e44020128414031031903500d0220401618818a03482e071145107021070142e641400600b6140d11002038400205130070b0745 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 354334046 1250 354332796 354332807
    0x207050a030f0c170c0d1b0e1f0b030c07020d02130e0f0a020a030803190507090315110a030f020705060108010203061003050c1614061501110601050f090403092301 72
    0x1c4c844420303424100d0b906001ca40000c07555105000c030480e00c4005e1141c05042c8212030301030941d0400360703140c1110404160340f003049000768000d450030400405500008054507030038042a020303060300500b040c40040c005034440c00080809a102400131008941e4903800320708854012080361121580300c00300b070001145c1c104418030303003800550018a010001a000300e60554a10300001d0103045c00040010f400d407441e55510b0005514400080049241081c0001c25034031007030100b290040c480d180302c5016823915004d00900f0b08031792004c062404030905015802402c2c2c0c80c00e0066295000d01860020132018080780b4001e00c003180c000340c1c0d40d1400c8010068101c400741c01d50300a0500d0f2905100502180800743c4a070032807602d451000300f000b103040012403040441000241031007080c0420440e0010340403c40c03800a4283c0361180ca240032200b03510f171142024040c1903000014050f90040030b150505290390041e0081c2082554191250078010883c1d084580503041c000c41c099003081a546d100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 354335296 1250 354334046 354334049
    0x91b06021005010513200406021c0314010b130f12060e0604050d0318020316030c0906050d0f020a050901090e28110f030f0a0501050a0c0c120207050a030f0c 69
    0xa1000c001e10340c107101c00038426480b0800c48030107095550070101d0a006c6142d540d400d41c1090801001c2d1101d94580c0002c0d40c6944c502203596142c0400c014244016000303001d06c44403500840e80c7d03049168280004400c0310741001402c10090141030a001400900d00364081d40503085842d511f8030303088150700700328041c0c603820b00c583c4081382e0084040001044020812400101040c9008220521b04580420889190501c041e6150003109092141c02c0200c04a0008681c803c92540000a070b41c0c1548400720b42c003e2280d6070b044920703500900e0014000c0c8101d0594030344020b14a4000c00d843e58041145072100747c00082c079989d92000340144002081240b401001c4100c1c0f034034905900c0e00c070a0a8240740c003200c0014805281000342094030707940c004000240c3c180103011218494107102c1e40c181c0c0c0311142c0034213544551a140c0070458680141c0600394170500d041c0c4a069040d904ca94031180d020341e84010788401c6005144d0040395070f44c1d40c4100d50005501411500e0014080e0b418110b1150f40319 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 354336546 1250 354335296 354335323
    0x110a0308030f0907060c0818061c0507030606090509061906020a03020c060702060f0d0605100c110a080c10050d0f02071505010509010b070501110c011b0509010203041701091b0602 79
    0x25076000c00410358050b110110456208060a0302c500140c0814008c010701001c2d802e901c80400b0440301c202021013880c504590b00d403400c0030b106a0b11080350640071120240500000201c84c81c03020320141c2807140055030441c0014010b18000720a100f05034280603125000305c001a04a4031100c401c1c16410400d10f01c520b181151245e2130901030313500241c0d0912032100b00d02c11240c0b02003000c0c11071200ca035200c0001004050648003c0d00000100202a00d418440407a4480041001c00030542420300c1603200342d911003030041c041070300d000e0100042000c7c40c4a00f0000c00c503080161a00812190285010703a02c0b006d400542c0700c0599103404084042039800380c1141c18901401003065544806c00c0a04441a0604e5036a54018a08103240900b00d0703d0148000c40c036000800d03120480301503000d80c0e43c3c11001c40740003485510300c520032034442c814041001d005170300501041c0804c40c0307104400e100e501e01c45000041ca18515030b035072103440e18881012050301618540304103c1d8039014003c000c0010310 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 354337796 1250 354336546 354336553
    0x50612010c050406030902030313081f090b13080c1204150206131712010f051009031218080f0105160216030807030c0c0807050a050111060a0504110a0308030f09 71
    0xc070540c008005025912406040589901c0c5010940d18280200c4190b0440c15486040e02e54550404a40e55040070450211642041000c60694a1942300d41d20340301d54425044143c2c0d0b1175040224088c0d180079801660411030812030007040340c0d4100306080401d41c1c0d20701c0040c0c640d850696a10012007507402ea44081d0f400c82c0d003c2002e40e015a0341c0d001c1c8403e92010510181c0411602d080c071b154007841d2a00071859035204000300c1e5042041c150182112011514a03150b40170303580040741c041d485440000c0c010880b2806003030840e070003a80324004035082c0a10309010f00d40d83d815007510f000840c40a0000a0b50f640040c80303030503403582c4000c007280c1c55140003c1018026224000b05284050b200240c07664501050301401c051140116240d001d420403860141c0c1c544800702d140d203900203841064860249800c000031194007604140e9038481341007010744501c0d6240c3e4181405054020401c580f40c101c00171040f0b01656034891104091030140c089140c41e40f030603920402882001600c4010b8950 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 354339046 1250 354337796 354337811
    0xf18120d0f032912100c050301030c080307020303031b0706020f07110a05030709090614040c1d0705091e0301020a0504030c0b19140d061203020105070c170903030c0105070305061201 80
    0x1030a03d55020f0111030291194045084500340b141d080410060400354518105a480b0101507400740245041c2d80c080c08184550564800c00c56680784240e0b01c00940503041800090107400382c054101d03400410040b0024948038055407000d040368400420380d41d42e040042401c80074441d1213101240240400e0b01e0b98800e25080c01e0000369580a54403038084842d403540380c10001c00040350005d41100c20511540780440c01c0c20b2800c10500390050040610440d002627940142e200c800d00d00340e01506807500c607203107130061701c07030622040c118007007110703113001d0403000314003509890920003000ea0300b081d036503050b485a0a516222002405a80c090542c500082c046031814441d00380103844122100d06020b080165007a41c264068054000c04809041c0b808000194020b1000c1001000b20700c01d6000308596545d4100a0f54151a401340280036a000c6c6c2a15020000c213500c000c1a042c4d1009003140d081481c440c114500f9a4422200c07000084c2e15001440186d0808030146503002054400030b00c81c18 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 354340296 1250 354339046 354339101
    0x5070c080d0302220b09040b0a080d0905090a1a0609190902031e190207140d031a27130602071406060d0812060109080604110111030f18120d0f03 64
    0x500540141c1b601c07891380d9004188280e56a10001e000401c16102543c20311181c04201500400b62071180d240119913460009000c01054480c40300c00d040034904120300350040303009109103a00025440b6800001200302e5000c040d48101c81100142007400000d6920701e455002d51103950700a00380200f800d1030400c00c1c004507240100c91740e1009401400d0041e2110314034202180c04140c0703080440c6160040310101c5580c0303645500300000340c110a0010b01c200507240d0b02400182e0038103a100c042050ba00301c140303000021112400c82e401100e407000403d0760040030340b80c01c02242c1c4050341c03c858a01c08240d10101076030f028040d4a9101604407000c132030740b0b00c03141c45100040c441c542140f04a40c08032400602c180c2c1c00781c2403501c0502072080469103d40350034544406490b15040c071003030201d68003c040c880209800011100d400c08105011070400706c40600c00c98010700c0715040e1a6011031108008038007203200b04500f01980002d5651403107601046407000e000c6a018800a4000f5800030b0000440d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 354341546 1250 354340296 354340319
    0x903030e0409021503040f03090f0312140903010c120b0301021e250503030403080907080307170d0c080a0f061a030916080d09080a05060705070c080d030222 69
    0x41982901e0100e00c8280610000e01e490075040c081a0800c1c2020060000f03111002d480d007c002d511903121540000d88500300210440a9840010846403090509481c6a13105411400d102c500c04100309081c08041c500003800d4480c0105a0000180309244100c408021409030340d00000341600210718042100c100c00b003400403030801901e0170260018000d03030714140c4611100c011194502c001440c60310f041c07404a4503940141c4081d400101004040388030103c02140020480354410001d510f0030307025a8170940460790202c0c040e91011003d200c4140b07415110f0060218403499580c515080d460020890401c036440305070106551842c203c424007503180a180036103104140a000c04e5201e552b107040142c80c101204c06001c2c018900d891000503590b20001c5e200041c0704054072100303c0152180f0385140e42e01602e0301c2c06042039100e000840c0e651405400108440c50140251038142074480140d00d19000a140324840003036400600c985d42c2c1450951000c1d02c0d0700d02d8030700e000c0f00d0501d0300003040390 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 354342796 1250 354341546 354341567
    0x1a1509100f05040503060a2f0901030f0608030a0305240604030213022a010e060603100506010c0f150f0902030705060d020904060e09060609041a070504090f1b090303 73
    0x41c07100346003845084a00038802d450080100030100c170301a20740103900e84090100403260008c60702000300c445c41100701c0621440742d1800580700f40343c201a44000110080c0010b40502d00c0300c40da5403000482e100c14240003e0001240d00c3d1804a13040c184a03d2107080c445820b15203681c09229807a0460a5650395000c80e41101d40484d1003070011580ca01c0754100038030911f556640014080c00c80d11010b1102815030070a0850240001c104c0c6e00c4402c00f981b07445400844580350b06420000960100d44600c0e07005035009001071400c0b000c0c0a415941d03040003015020420703a11106403100f090340c8800c00340030b1805101e1014a060001034203130303400300743d0f140130300d001e003030b1084030f0105580c451610168141d51800c030000f0828170a039580c0d08480c040411064601084501882e0009485414850490382c05554000c0c0301c01030800070182100074000000d8048420404200400519034220740940c06241000d0b0400180c0c0c540c0c03050000c004070990748682c81c1030201000f010800320360859801007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 354344046 1250 354342796 354342829
    0x9060d030503040f030306090c090806060609060313080f121b0f030423190c17100207021507050f0f0d09050d050c0301090506071119030507020a091a1509 68
    0xc00c0a95145c1900a00040e80110555500e8480c07007100c0c069000744501c08642d402b0040d9a140d444000c01d10175580304000c1c0040d00041c0c03c01c08610b44440c810341e0304461501410712503013022121030100d01c00c2d504c00203084424154003002c1c003058105416241c0e003201e01d2004a90314099285002515600000340064a101091180a8401464241c1e44502c1504060030345a05500880c0b01c0100100c41d0001a41d642e0550316010074114403c2d1040e9803100000e1000301500320381550720b680654880c0724102d030451421040201c2c0ac06202000e00382d403520407c0a05024440100340d90314103901440e600c0766580c4008140c10000d0741003040101a140e0550702a0300300b6405042040c5041c03a03000d8015010f6180c600da9006011000c1551030040d8403550310b0f0b1813007020000d84155a00e00344800700e0b10078803810b919400002e0040b40106104c0344086c2070211160740ea074541e24111103c420301c400700000340854039001c40c40c100900c2d402c18541c075000036050028407008981e0344424401002c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 354345296 1250 354344046 354344063
    0x130f30030e3705030a03021c020c0904080901030e0c0618031f15062102090d06050c3112051203010b04030c090209011202090a03050a0b0609060d03050304 68
    0x188815122900c1005102d000801042c1940d07902e40511014112400394040d5450b031148404a450318020454444060300b584c01041c0c440c0b403004104007150400c18008c020740c4940c80800c4030503164a10098422405615015110b6058000147c240c0e02e08540c0d4071529000402c608410f80d40b0a0140c4101e50040103000303283d034241e48042841d0820703109040307000080d41c10107240d450055130403404c1d44101c0700400c0c3d041650b8402090707801d82e03604181604550080180e01404080a42c003030b1410700d00040c5882c01c403104640750355003116011f4900c401c00d018001a524055030202425071414144211002e10901c0340280c10402140d40e0b00070300036000511500d5034103108007007082220202c0e050010f16900d503900d4004112070b501030300c01281e2100390407500050018252095680c1204180c603210006001e41c04400003c0d400b4020301e95114000120100104004001c018206441481d055080e810240704101c180c0000401807441b070401c0d2044400020f0740b0505890300070b98030600a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 354346546 1250 354345296 354345317
    0x140903010b0405090a0c060c0b07050f0906120108010c09030807021507051005040b0604020c1b030f0118021203160b04111f090e070207030314130f3003 67
    0xa015040c01800c1650140c10f01040c4400381102041745d0b03110314420407220041c0350759104191168501d11304050b00103280d183c0000d102e035004000400d441c03d41451b0491812444900080c03181d080b84500146140c0c2000052050700b00034800c2c061482c0d40303810514549071656582031514403900341c1c001d0151007540385007110110520309aa4506500500b41c0782c441c8200100c00c0000c0108803016600e48100744041034075810b181c03085440e040854806000103440702045400340800f0341c6544c0c1d425124400030301e5107006081c4604500e4038141d08a01e510b103c1c5600401006a004600b0407031150420030900c080300c015000c0c40c08006a000808190580d505d0401d010340d109514000ca8200c24004941d807070105003440400302c0d8650340d4071a001400c1d198029004000c0007140d4050242c0e000b03c2003800813a000b1084480c4180011203a14074000120310781d03000f4070034164004080342205175001d1104510a000014805180c40100c0309550082d01c4240d440707940001c000b8050112440d40d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 354347796 1250 354346546 354346549
    0x16022b0c0f0b040603020d14010b03071d06030f04020a090515150405060a0c06020403060501170f0d02120913020406050c0d08092d0703030f1106040804090c02071502030703030f020702011409 84
    0x84a0540c00440241032300c07541c0d4984842da503c1e0b0085518000144800b500000905070001404c200c0e25400340041d0b041d030341c5041c0358500110000e8810381e4082403032100000c9044003800741500c100c0d14008480b8144107141d05010940b000356a140c200440188810b11560700e4040c141d94940da01460003e1210311182413440080c802e41d00090020b50528001049030300c41300b40c0b00c0100c052380350201c918040080382c005850b9102280ba20005070412640c0c101c01100741e2000d0004254020400781414251401c0c00d0100c1e401039000ca00440c0b8046a0707400b46400900c9184240602820640c0340f605c0c00c0c1340302586038181540545007900240c0b09001c03588540403c85510180f00703008840003180c40e07040c090000c0f0307150201c40e8000391914548004500d000b0a4641c099540410301d18102424480b042004d0703e0b115054104511401000089148419500651003a09030f00650703900c1d400c41c10020107640c02c1d03148488415004015210050360f001e09030000804685034001c0e1100d84510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 354349046 1250 354347796 354347801
    0x2100605060319270b010f0e1303050319140915071e03020f03150a08011401030f140706050c010f020a0c240603030e04050906040816022b0c0f0b040603020d 69
    0x4609002240c0345906a0080000602170141070303506000071184c04179560406281650011125942d402000380030724000640500061500003404a210800144c004950320040314100852000030800c1042440016a010f000308040000d0380300540c111403401c15070182501002580001040d071003030b0079075007504c1d100754181d4040e05210b400182c2e681c2030100d01001c1401500403441d100c1c40d04603800086802c0e051140080d0201042855040e0b42e02c0d50700c560901005601c8160b0f59040030554200103642c05000041c0a8425171700c0f982d4a03100c40a08880c00c444560b2021071000d4410054002519000f244005005621050030b500c041d11088043c50090b081700800c100071824070b240441095040902d180218405540400c0350703548050005a580c0320070303580a41006c100300103408402562922140c07e241c0060a0140d41c880611a09044038150a0444424001c40e041c040104051042004000d00d40c0042c10040d19051808070070300c1788180d05c5110141580040d06400078039003034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 354350296 1250 354349046 354349091
    0x160507080c0303091606021f02070503070506240a140102070e0106020307290601140903031206100306030503041707050909030a020f070e010e180a0302100605060319 73
    0xc525949a00320391100a989800948131504e15000d58002d1008103072050990800700c9099034010000d11305e048003c40c1d00e0b80078010b40e8041a68080107850041282040200003d511680042045140410080301c0740c043d1840c0d1070895441c90a80508159074007091002038032019270040d880d02d15402c0050385400e00c0b80d8000c0981780c1854000040f0503401101500e0540d002e410358000d4203083d04550030742c86000741c1081b2204500c01000c110994460410400c404945e54a420314042d200320019186400a1508460b400d40e004100040303800e00c2d58003120f040980d0b041c1882503a0a40c0e941380e82b01d0045008088020485581121661104008c0c5900402014080042e076040400416440e903020b91111070143c81405044661203400144c240c08880e5210046015a4245607408c0b050071400351101580541c548c91803a990b10b0180070302041c0034400d400a003242845010b1070000d4421580c0450702c159801e01c100140c03440d100300d0112a0f00d503502e00008540d0350119070901d411500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 354351546 1250 354350296 354350303
    0x40b0f090403030506010e01031b140d1109010e03012306040b210106062d050c010c0806040606231b070e09010501090c051815070b0a1107030206160507 67
    0x38040c40249501a403200d0700504003a07032600c076900f0390007005501361110400d015103030310310341d0080182c2d40b84510341811055041c00c4180d844d15903504060703001c1c0c1d0380c0b001181041070b00008842605607001600c81980410940090000c1021380f189544c4500c0510015549101c11030b000814a41d203d9000c0d00000c1c100410b000c2224000b00c0c00a5001c10501840346d000b5881c01e58080341c51406014a84540c1890200c1c0d9603070100c5154003462a6405103034011b043c04424000102210028001e84151660a6882c082189008405c01041d0f4a00c3d40c000300502043d41d10054801d459400d488440c0418201019907880001c80002c44000c0700c1c8000038050b0080d00c07004110191480d43d114012100c1c40001c1c4243d90b200c82134042104d880d080d009000c10410800c0400240c0a80c00340c10401c3d100a0002416800c0c0c0643c0c41c481d50722a0404841420a410400542c606030f84181a40030700381a24240c1402c1c210385c0c011b5991000948a0303402c40c2c85404005a2840c8208100c6183d81e51 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 354352796 1250 354351546 354351559
    0x501050a0819020609060c060a05131205280c021801081b030c0301020f0d05011413050a1b0f110102130302121903090e070206091c051908190b0a05040b0f 68
    0x1f600d080c100d455000a41e0310096090414022520200c02c0d0003c90390156040004450245507940013030310030342c2c0854500c0a07031b4064011440002c900307406601101c0070303081d101c0d680440040c0c8100040c030052608885000304031880188800c410000303145108200009580000c004200002880c046074148066455800060103603010031440c005005048a80c00781448640d8035810b079403450203584c08540e03410040350200c003800070a245d04495045410000000341a40040c84000020144030b0000300204e414076040800c3c1651103501d209001c03224000840c00c01d40c1424a09820548900c00a0f1150a0352854100401c00c01d01540600780354915080c99040310501d80070b040c2110700e10901e09440350f038500080410340045001882150164040d00c00300d107502c1d20b101c1c6059510030302241003280a200944c1c02104402c21801002456104d00049150072105d0320085891884001c108501b8021041181d403140310083c0191102200d02081c031001003c0441e0f25600b0b0501001c2e817010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 354354046 1250 354352796 354352807
    0xc01050a06030c090c141809072105011511030f0d06050a0603090b06040f0e07080a060501080703030507020d1a040b0f060303161b0e010305010f0501050a081902060906 74
    0x289958440d40482e88550095010581d80d410500102d034030b5589554049110300b02c103805403148100050a001d40524808006030007118041902068100c403d03a000c90080d60302e2203800030b8a00745211000c4039a0000b03004560400b8000e50000144032803003801d00c9208404014034200c103000340c0305201408602d9039140c810300d0510a000c0c040a1145a010380d801c1040070441a120740900c07090140c11041340d0445880300c8051100a04030045030402542e84d03071180030400041440030a00030b041003001010315424900385001150410381c01314001d644500010400650403c0582d440950111080c2c400110b09040c00d04118504045042d082c1441500700800c21032030300d00b19801601462542c98243e0703540002e055980c840d20000d9000241008111000901000305030620307022010300c03000d030759035880410040340c50007a0001c0340e042c0d4403040c00c64901206441203030300520381122061082da10b0a41d83c07946809961a100c0e407402e400704c41ca202035403210800c81d4040b41c030140a280e6901e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 354355296 1250 354354046 354354061
    0x30903120f0f0302040b030f0603160e06040507020d1707050d05250305070c08090a05030610031b03170a02120a0513090e150a0905070905041b24050c0105 68
    0x1041d150414000c10704800000b03400501ca8802d4406440036000b0b030501d1611010184100c04000500c440d90520448200e1003c0c1c43d04041440021f084d40c3d0403095250600e441000155807001313141008641c40420703030060b8680c1c000540400c4008030540207010b03458840c3c046a10307100e81586001c459040009208410058280b01600b100030810522032000216038210103807082130341c042d00041c041009040c04901800010810000c1c020000c052196907100860305204003151902003082950a081003448900c2ca10b01841e4800b2804200c102402c40d0742d071300420108100390b00100000403e42c0e24110703000f0404075440100406e94a41c80c0d11b25410001e11030b82c4203a20b1503d058049102c0010101c3d001d00440845000c0c2e200078019209800034a0000d85d00020000320060707441e42128000703e03d040c0315040c0600700030a0301240c0b615190424030003100c0c0358003522000c900420302c1000f01d030400d410084d0030f103012074409844003080b080f4121040d010345113002c00399510706024081035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 354356546 1250 354355296 354355307
    0x81303020415081507050a0f030207050601140307120201020d0509012f010c09030807060504081201090212070824030a02060c0f070b1804051008030d060302030c06040303091203090312 81
    0x102c9503d40200c4042c818450902c410609007921480041181400786402d024010108404086410f00e401410080940c40e001d03c3c0070020ba002e50113450f00103c20304194202480003601600c07032003075201800303800ea0340000d41d0340c181c60341c80300104a000b10b541e5009a1180003c420317107288006403015800c0a01201d07040e9031510f80341a1419619000001d12a90f0054000c20308994001040740d0800c5a66195107014001c01482282c18180800c02180c0d2000c509401e1760207020706403001130704c2c1d249030031801c0e11030a030140040c002c0c807130040d08001241d02c40034100984038000780350828580c1c5000d00440e107001c000250083d444140850309a0112000203521039007055008110b1b00129501c40d82400d0300d11800c901010035510303925040d4018203003900280d030000c00e0711082c05c0c5101c0d40c0b07148042c00c5400c0100e50303066040d2102020815854200086124018100e8095280519555020b050540c03588a216908034009010005140c09081460b008582000280c103a01c00d028800800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 354357796 1250 354356546 354356549
    0x2040e0f01050a06060207030b010506030a0b03060403050715112b020a0512070507020105180303070c03050604020f04051005011125060f050316030b120d0509040614060304081303020415 82
    0x10f00f881c2c400005149440000ca4004a942000ca00030b650303420030342404240e910062800c0d4a541e101d200a06031a10104030191242d4083c3c0d80b102c1d100d00003403800d0040c0f00c03101d401e104200c1d410800b0b4094841110b80c11a40010201d18024608010361900350381c2407142071001d41400381c404500e00003801c1d00400103100c0d0b0100402c48000305da44940081c0d8090140d0703207003c0d000503010700a8045080d00f03112101c054040003412203040040f10781d12014918030340d13081140c0e603401000038041142014200f080085008540c144030b1443d03c3c0c040d0b154216814850f00c0c3c10001140b400e00200842440b203902102c03680b940c01c0f406070300380c0c910f4091503504c14414400007070444045030000d0307071103103050300d00540701007040c00c1d800c43c2a03000c102c003c1d210710b00042e503000244580c1070944031360812001403c00c01d140c030f5064883c1c282800f00811102513070302ca0b4500c0d55070002450030f039582d02c10440358007592020901d5154072004050100440e295000250041c0c50220803080101c2c200e0710000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 354359046 1250 354357796 354357811
    0x903060f020913020c060601110712060e0d020f0d050913060e010503120f0702040b01050c150603070603150911131d0703022a0a06020d0509010c2a02040e0f0105 71
    0x600561120701450f0403841402001441c94001c2c82c042681036104007c00a0f03030070719450499a621b5100c41d00c03002d00c00c8620700e0032510542e03a49800f4044250038440354419041174005044d070340f0381c45407455884901e02c0f04c00004000d00014080e01c5aa65a81840d28421041c002000f03100d4481c040420205020300540e8800e100c0c0351007800701d840e02001100c2d644040c8404c1c0c241041d100d0303030911018141406d221810320406001c42e250280f0104141003500a814920284c2401c0c070038117050400080d900312404050a207503448044094680e41d480c100d9501840014000c280c00d403008015000b03a055208090344208030004204c405503000920404030034064400765160320400b60224410501440e842c0c0064075000e4000b00c01140c2510514111201562006407103680c840c0b00300d9218030112070800b43c0e84c3c0140700b80103e09102d00d1000c2c17241c5091032003100901001115410b10b400200140c1921490085411515540c20203002540d00c0d90443c0c02148d2a0032105020301000c0b500203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 354360296 1250 354359046 354359059
    0xf010b0406050604030f060f020405040906240605040312020a1a01092d0b012f070501090b0f0306030c0409050c151602060702061603090602011a0604150903060f0209 73
    0x842d00303240c801d0441e42240d03030103507000e10194001d40d2184040c1003425211182541c0c01e020000300303a00e4500541ca0000e202d0800003800040040020350b01140840341c6c2030349544400c009118072500242124107580e00881203500c0c0274080c0e10101c2c5041c01c1c0c8400201511500542d018040000517046070507a40100810f01c14030090711014668643d20000800d031590300b440b0070041d0740c01103034441c084410f010300d0031000d803031011030580c01c2c0d4007140d941c80003000203c00c0307c003807290034140010b0020301001d2070601061480c0582203580e43c007801005444401002003c10202c1e601033180d140090000742041c03042c10b1050070a0758413203142c4400c0c07a014889241d540c3d07854000c0c040490314201e0002820046032a0107400303000580d00843e0b001c1b40c00080802000499182242c5118083d91082d0f0710b80c60240d0900200a0a542c001c100081c0e00801c50b51684a840d0303640303815502540c40c10011015100c842c02c030100c440d514140d00141180e40760802070940c88800d500104107100090303400c1d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 354361546 1250 354360296 354360299
    0xa03082401090605030901110c160909020603041e06090606140d080a0f0507050f0304030203280f02040f110901200a020418080a030c090e13170c0f010b0406 69
    0x11240d0304480c0c111401d000450050041c00024083c20195420440382c600004101f408100c030f001e441e40c4078001900465112266106807440c90010500180c000c200c024000340c0e0031a8040707165404007620041184c3e900b0341c0565141101d44481009043d00134405100103e01810510002c01040c0079190400041c1c1c400d012060505000118221fa881204a446e100c04210304880088a500000c0b003023010801402000c40d40400c90410410031610266655a20f0f6104143c50000301480020807040344003442c000c594140c1060441c40e94000748803d41000e214400500101030701518641d00c07914003030031011301400c050040c21000d0000e803200c02c04002c80b440f48812070207000d0520700b402d84c8005041c20050038550001c1e03203654202c4000800c8181c081d40c880e01550090300e039040c000b960760390720b803040140d00548000040c001c2540882c19802c007208070340e02d40c0035101005040040303160490302e501e442500c00c5807140b0b0301e540203843e400c0d91414a094040d018503900c0610503420f0810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 354362796 1250 354361546 354361591
    0x4290709240c06020306131b0306120f030f170403020a03020f01020c060c0f0f0c011401140d12050408121b070b0a0c021914100306150c02030f0a0308 66
    0x28071840c16040b9224501e4112042e0b8840c0301940c4001c0c13807250030580304050b01e89110000d00413001c50900b10f0444180c11085c502008013111400d0341320312000e0301d01c82c1c5e4450100708402141d41020350940761090109407802c80c1690066942014420550038803c204002d0540c0800d154100a1181e429a07000c400002685801d1b40200284009680c100b1404a941500038100600954880034041418034012140c00340045d04601c0c1c503802a6510340c0d01c1480311020001405000d41088141c080c640000c0c0e80c00b00380c1d0658400300041540480302e17045d81ca014081c1081d9001003842c00103c0314400d0241426a400b60406441c44d082d03590b000141da0001980800c00d10250f030589090a820f028000c6801c81da800071442c400d80e08900a00242a00100100c251802500c403e01e644100c1140341c00901c005c960408034074008041c9002403d000104211017441403028140c901080042c0060002a040038105252002d41c0d10841c1849002c00d07401c0024203102c0d85101413503414400d48441c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 354364046 1250 354362796 354362849
    0x15230405060a020a1218021504151805060a11030a020a030e040b030d12060b0a111504080a0315092c0a03020304050d0302010f2406090e04290709 64
    0x32000130108100b54440c41c1c1400f85940031030f20350180c0318002c50024016401081018040407900b040b06000080e0501031080a200319003100030701032520b40d004030717800394001020050300d0003281c5c0b24210000e8a00740091080c0c140d001c0368150301e0140d035950856944061754400f640201100858002ca20151245c64a4031400c500c0c08006009044030410010003114900c0c00001c1261403596242d501003980203640025000881c042d49170000301060405000346040b9009102840340b001800030400002c6904041c2c51b00c44456060118001400c00b8808890100b01c6e0041d090041ca06440c0000600e1308a00e50321603560041d2800c0c50030891083d065448045099014002d68002c0108002c181040128005410300034800040c0703101e40401140b01341c0708001c003170041c9842c4008400c030008a003c4407140082105080c48028a454182c0641008100800c050012105207481ca0102c0442c1000350101610b15141e210803841c00d400081e0060b5440d0142940004420f682c1403104104d50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 354365296 1250 354364046 354364057
    0x31b1c061404090b0f0c120f0711010e0c010f021207050102090a0f03080301030b04060b04140403030c020c03250b1b010b06030103051b01140f041d011215230405060a02 74
    0x6850f16100c4c1c0da8190360303117101c1c8201130f103021501e00d0304100f5445415801d441460007152004031001140c10300140c024070304010448225400c1c2d1401c1c00241c01160006945541c6181c00c1c209030080703043c0c1040582c1403140401e2540c15000380000d2140412006600500c0340500c02c8030495012610f03801c1279881a074107070000524000d010001800407610600c40203030b00501c502e10100c2d1143e0000d01050036140c0070040070100c0c4a110003403104168060048140500303040c401400d8030400880040c0c9d5449926200025013548551254108005982c222003c1c1c00c0c2c0f0442642d0b41c00ca0701581c00c902c0001811010099480d1546079005841c1a1041300e0480f50840300400760404c44c41c03d156001d41d000910b6a050050b00c0207035002449603a0043c12400021441075502d1750715241c0303409c420041c6400280300c107407c100d0040c40926450065040110b800c0003800b90340040300c03140d0100800c811080100081d5007103070188041602030500c00e11441c81801a604503440d041224010b90180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 354366546 1250 354365296 354365303
    0x509060c030c070b0a020601060c060b100201090201080916050f0a0914040c1208040b0c070e010801020901080a06032402090d060902011803020901051c1202010507090e01030503031b1c06140409 85
    0x28200402c02c6600c41c0c402403202d2402f51200041c0e003e00913000840d80792003c0384100140c0d440f82446000d40d0780101800c2e906c5503016001d8040020071002c441100441d50151500c505010051000c49440d0b0604043c040d100d0954100050b1180b11440c2d0808403084604892150384030f400820000c1c6c41956400c540c42c0e00c071340d0050510303041903541d9245406c0b4010204403403007020700019892a80d00303442c0b402001c015000582e100d86c0c01d40010304822004113034215560a00d24204001051415621491007240000241c00d600614400c800703841620010f1b5840b1610744a68028043c1170352000308454401d88401c114503005201c201c441c466948400317580401c0b0b02d07004004600700013060b00b0a0041c0c4208101124905540784103001c1024007280006030741d40e004000d81c543c6c000c9450405061804920440c942c5140d40c1d4594a01c8004e003507040340100040d070390405180031001c0d01c4072000e0540c40c4444581c00f2003844001051030b80708103803c03105104600342c0700382454400c001d0341c1c40c0c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 354367796 1250 354366546 354366553
    0xb1602030409021804050115120612030e01020f15240d11030a060203041407270c030603240f0227151804060b03061c030509060c030c070b0a02 63
    0x90044800700039013040d0920303030006100b26104a20307039440f031241c40d0191258180c04020038036401c000400f85a003101d60307260094a4000c060004078413042002000d203a05140201c01a4136080040707060180070051741125108100c440418140b144401e076208000d5810080c15540f01c40d06540c01da004d0b02c03d451a0826802406400851945480c8203d22400a0211001094580d940781d0407a442114242d130442068011107c4d0480240100030040803c0d040c080c50400c96152400344008220340e218401c29607420f075440c54580241c20000c015600030804c101d0700702c80300251040350018002d075002030301e02e4108135034030110340c1d80700355800009503540c50003214500944a071028080b500007158401c1d81c80948141d460305000090000c0c2c0120345608400809507014881039415075004031050701c000340f08200707072601c404181c500c0c0020303090401e02c115042400c0036a10791141003403954008070001002c0050800000084c0f03880307021101120500c507610b92024225014a26640b00140c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 354369046 1250 354367796 354367799
    0x10031803080a1d0604020312070803010b03040c030204050c030a0c03051528060f02010c14070b04020109051003020403021c0201022a061b060604140a020a020a06020c01090b16020304 80
    0x24811081c1980c8403045940c00200040400320120860b41c0501e4900c11a91043c800c12007107050a020220604010b06015418544a503030b030703280280014000d8914540000c0006814840510265002141c0140c42005603007001e0503a1010740e40202c5001c00c4050411f445014240c1c03091040c0c1d403040c1406807024901c00d4001080200f4582d04000c2034200d9112200314100e01c190556920f4000c2c000b507204c2c9903011031400300c042e003964804070b070210a204103845103681c08005d40003192143c503030203070454003e81e4a034401640d24854a40100e600612101803070741c203036500340d0b00074400d6a0080302d400c900003501186640142410f0900280107802600e0303110f8100c903140f003075468000c0701400305d900c80741002000300b04c407a0800069010703580240001080c0b1400140300c081d802400588040c00307456115504001000c401908449a2640c00075610341c48920a03c00009941c0e4014411340d0b44c1c0c4103009225000c3c1907542d40c01e42d008401c6d40e0105d4124505040405c58101c0190007860500c1d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 354370296 1250 354369046 354369053
    0x18010f020720030d0e2e09050102060702061302010c0602070f080c0c040b06090105070c0305150a0b190611070f0b070203190b0f040206040b070c14041e180807030806100318 76
    0x40560b1164802100c1d90080da00d06c031080c1c01604403d0304282d980a8105191100082c54504c028001505541200e804e1290344c2310502c80d004d0710140c080c01c014042c0441458a00028410304201901c070520400405040009039002000d001003007404035403000c400071042000302d0b180c4818050f81700e9000c0020701550350042000d4005580112900c0c0c5843c0c0d903a84410741003985240903c0b9a003c0050104500c0e00081d200b0f00081280c10343e980e195040712a458114604014040d481c00e020382c004011942c140c081141e18041c0c4036003038001e41c0195681300111100d401143d412413081c05031040c0402030030010f6495129007500954401013a031141034601f0f44401000d40113a82183c803c100105030440340d007000b0454a80b00d040047e030194036246031000c10601d1004224400c034240f101020b800b00b107610302200d40c9118000d0008240110340c0d51505002400340b401001000b0105401c400d0503008800030303101d480d01707480d40030264448030000c500300e404840d040c9403000003058820012 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 354371546 1250 354370296 354370309
    0x20d0e0108040b040204090807050307020406090e0c0103091412070605010501030c170604090f11010e01020f100203130615090606031521080412170a0818010f020720030d0e 76
    0x1305001410000d4090603a440f0004180d010b2402903d440d0700005040d1f0850400d4411840140070030384081044000e48c880ea1515000080603042c105500c8848000c248403400c2c5142100711151000ca80343c40c1008403d1f1109030b003107680309441480c502800003d095000380680c0c0122205556805000400e0380c9044000041c09403046401907920384881001500c07414486c502c0d540191020201c0c1c04441c4001483e46090106032411500001c8051025800025a20000308101c0c00007580365a103403180000c0c1c880c180301014200030308004a0440c1494080b040c03105070350f1007207030510016448080c15000d4500ca1080115901c03d243c030204494411040040502c060110440d039020a09841c2c840c0160000d070000302d982c0030030503080c5040206c0074107906555039822900340c3c00c007450b440024140041c001c00e001c0407681a9603050510320402c1d84180040c02c0360b01401c64903603043d030412440d940c3c0720300d2561004003c0c1440242e01361a00149141c0701c004140d079250101100941031203c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 354372796 1250 354371546 354371551
    0x3181e060834020a0b0703020712030c0e01030e150406060810050103030c08030402270a271101200d0f0c020d1203021b01020a0e0603040302060c1b0303070906020d0e0108040b 77
    0x444c05904130309000155840309003805581543d90240c0c88074041d080c00c2e100c51482a04440605141c100f603850002d400c41c86002c40c01000b420000340100c40c0c802000c0c180715001c0d0361129403040c6601000100800c680c08003087d200b454048590b20b10010520fa03040301c100f0b00025000c0380942003030310001082c904c011503100d440a4203c0035007018505000c0d41c540e06022080b460681544201301e002e002501c41d514001216591204a6418071402c440300d0425091015104017001510007500340d002e02e030300d01590031403902d030920035060905400d6100c0120300c00c4072001400200c22820064801c2107400c44aa400401c1c1003081d086580e2100c2d01d161119000740149902801407406180207102c2c107a446144800015031f0ba0710340080000c089190203820f25228200134818800880d42c0000e05c5c80d4081104070800ba601e401801e0b182440000e0105900c440c0e00c0300104001c9115030045251085510a40848804007200300003610510f50080500780015029800500070038a00204640c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 354374046 1250 354372796 354372901
    0x1b09040c1215030615030c0e0a02091503060a061e0807030f0c1110150b0304170a1709030c030904110d0e150906040308010303181e0608 60
    0x2401150072480100030303a05007050009803000350380320820500080f03004041c3c43c2001c090784010410704581e036001101c0202c1c01101403150b0303000300141420801d0342c11035182e000d00808164007440201c4452a243e0300c21190540a03044100b400154140181507004411070822511500480035140c00ca80d8544010640c400b01a29004030311210b06180c4100c0030442c40650354141100102c10301a45428402d180301d811407441c01c4811813080008413542c0d4140c800080f2429a01c2c3c5407070421100111220000b070800500c0090301262454000710042c50400594444100310390303c0086d015100d00401c01040981c1c0c108002c03503402890558003013131441603d000350f41c2c10a15200942d5007160b07548030120896620a0f21040b40510098010b90360184010340203040900d8103641c0240070383d00c103100050074000214100c0400f181c1c82101c0d40f028040356903904906491104442e5440c2d1f81900c1313500049100d130300110340300c031080d00c1403102c2080014000d44c00485900076910070180c03d102010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 354375296 1250 354374046 354374057
    0x80a200907200a0c0b0a0801050a080c0d06060b0f091e030601050d0312050f01061808030406082203230403021e0a0806100501030f021c0f09020306090a03081b09040c 73
    0x380004600a9004c406001c40d180290b072a4210304202038030b9440e040e04914450300c4003510402407000c002a8a5400c000e06980f0000d1081e40352800310090015500302e541c03a44004140c1665140d511b80c0a464055411a051450801000c1c1400c00040c01c00a0b4550507400c10b0005100c0d908010b0484440c0701d00c24034040842c00f440c0c062141c221202540c55240602602c0c3c010401158404507008044100c1200a0155498103d00315a04c0c404e0344610030030f00075050300107000c0841d207020100e260706d0a42403c11010803540f80042c03031030b07940ca00d050a42141c14034400615129140542d8103030380c0d001c1c00046048421410b2a40c030030a0442c3c42079071020b0902d0700030885a07004d00455008202483c5c4078030303100e420000090161403c2d100100c9101384148140c0c25044e0a0910050495220b02030008202c18210680f80250144a10294140c40341c4000e0080741400003038035404150180e40e1300d294a03103804c0030465004402c808190100c0c441032100c4500b500d050760255401c071401f0b0905 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 354376546 1250 354375296 354375313
    0x405042a1205060f09031215061909150903230111040e090d0305090c09040602090d0510050f0108060c0d140423010e1f06080a20090720 60
    0x5500d1001507698049800703401020500031042c404070360b65500030b00104055410140e04040010341150700415041c4001500d080c00d085d00e48908041703480d507090055050015401c00140640803030b4152085840300c00c23404014107203e0344500e050303009032a40241414000718401c1c00300c01c840300d1480c94001d020356880b4212001403209500610050880511001d0f2500d00b80c945981000380010458050605010810022010104940803994011948050291a1428080d009004840c42079802002c501300d440d00b07000300081c038402116103000381485203980b07004480a200d03400b849041f03460b41c40031010403810034031003028110411b029040041e243c1c0c054034200c004000c080d10b0544104120003081038150000c2c40520189480d500000e0201850301d4100e02c2ea1607a0b00414007200c003802c2440311900c0701a130340042005203525000c4807500c42c801c0c1441c202110481c001e1013646a0a01004d441c1820302c0c04245115003026194034420301d81600e030819140074812a92840da0261044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 354377796 1250 354376546 354376559
    0x91008060a0f080607020d05070804060f0e040f1508030f040605031b0403060603020108060306160e0103020f0d0b0a1a07081813240b040504230106030c0e0405042a 72
    0x1010300052240500404c01800c0034540a802d101030049000100107003000201c0210b10540c0864007120038a2920302c942010411044480d0115500603640c45401d001741181c3c20340f0950003188030700f1481e4130315001c1e003035079943c1096592054120081c034840c07060008010752401075002c1c41c3d121aa82c000c4028203d010000c46440380d00a41044404ca59151002d005559002d2600d6034041015001048503013880309802000503000f00701c0404004902c44101c80b2039200740c05860400c1d10070042c403501d907a8841c20039070182c290003a0160185c0c00c014800aa0200f40e640300c11700042c00b025071107180032540d440300035603644600c0e040c0321402404aa4034516448040d8031f40160301060800044031341c5000d83c0c00000d265014400300c51041001c0043c020900391030220f4048035130844000903010004450300300300000e171969003401e40300180000110703036405d5013103104801c00980d99070518410210410007106c40079140a04002c1600ca0340050414804082023040da0404030303e00f40710b07682e03a031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 354379046 1250 354377796 354377819
    0x120307090801020c031801052109010e010207120f08010b0f0a050705060f060103050a020703050d020703031d150c0a0518040216031101060b090d08030a06171b0105091008060a 77
    0x10b00040d0540d2001031b0f17207544100100c1c00d5403120402440d12524090100141d80e2105081c00c80d0044400c00740c0021400e01103007503021150384007540c002551119054100180000f0382d40e030304030000c20200d84003620000c2c400c564981c10790712405003050411050042880301c9400c41044038091160030484000810401c10080c0d22031352100e00b085840e031070200b00060681d940070300300503809030040c000c0400198000054030302c0c851040b64010380369941c5050031006440e0310101c80b00040c4490841144440001c185810002c0d0f02092011b203036213410200200c5886040b00000c0002d2041c00041207446caa60421003400f14010000340c18904000306c545102c021500f8200c0220350a205200000c00081c05164014042007440780e05024215001c00c20130300d490280101180c40000028408643e1a40010043d00f00300142d80d20701248001040d40d06c3d401c0038603400010b081828074689943c46441240c0782110081d0500c04003007951101603e50b10000b800c81984140301c0140031484480c4031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 354380296 1250 354379046 354379057
    0x30c021306090203090f1903081506130602160e011404060e0c0703090e0c03181f0e160503030d0e071715010b03010e01030807030c05060906060f03070812030709080102 74
    0x10b60050762424016a0b4500e0100c0b072054541d099000011855074020183c915009541c1c0c240c00e040c0426179480003010107a0722460425a0302000200b001c41c007860300f011a06081d20415021220160100fa4844040c0c2150384624008000d0701c0c070050141500d00c20820590110180c00490311644896281444403001c0b142c8501c07800021036544249907102c9035400c0281199a488841401c00304201241d52200801890700c484018040409400d01049189036013051502079014050003402000054031030600c07010943e1080607104101c41000c0001d000486100a00a61820f81e0300f0350310030040d140741688005c0f203015240c000244c00380c1c0041c1102c80429070b00007904e191035001d0070f50b40010700180c010552402c0188014840c510000140303606483c0c206000c41c1c0c6503a10f6280407504a0102030000b80f05000e081c0902060900000785d0b940200412a03058200702c2c560810b041d664252403040480a41c001d0280c02d030004100b6004580203103080c0350480f5841d4965103084d0aa82c4003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 354381546 1250 354380296 354380309
    0x102120106231c0e0a0f0507030c0e0603060412020a020d0b040215130504020706020f1c0515030a06020903010b03060106020a0c12020d020907121503260403030c021306 74
    0x1101d00c902d128190748181c40e00c8944001082c10f0624100860b440d20b580051207401140740c0d59070f092541c405808000780d421142d40103085140310340341071070401c0c0c03244050300c4112103074200640e012454004070313071200d4440c460203030042c55907503900d80b6501c0100110002660560041c16404405612031040818509005188040850a20b4410302c803000000050285007801c0078000c1e0b04510035602138100403554100d502681729481c1d4100a80207200703421901c0b0303c401001600401140c0d69000441c44e81e24840010400c651b101403940c0d0b0005007046806916800a645080c0000d0710307903003c0c0c180103102800001d118038a442c0442d18124080c0c20090160788403000903c01c1068012440703015061480c0c489180107030685c041002c40041e100000d200d0703090480080d50310ba11918605400071000c2e002840400300c00304461845140705e0206640c441c5805900300c110800b84c0ca40300580919a141241c68280b039510100c611034041d03d400c81e0f110002003805c03c0040c04a0180c00c028143d07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 354382796 1250 354381546 354381557
    0x4060305090c012d051c0e010e060c040605070507050604030b04111e04020d0f02040f0302010813020108010b130816090b011814030106051314150604050607050102120106 75
    0x51010380c071031500c59104071560410140c00824241103400d0a030040411074108150310422401c0602901c5070b004518035200800981041e1044a2215030070501e203204403100200468422900841d4868004881c000c01044040001304034040c400e4005001c814064001e8071001500c501c002591a03005500540e2101c0e400c1090100348030020b2050b036001070048607000c01005218a10000800e01484030600c00c9501041c80d017481010b50704070303a5800c0c00d24401103503501d032540101412400390340001e84c00030301c1c18400500d01108609000c034500d50161540c0c8281c2c2c1c0307040079a4410b81e00003e06050808198003000a80c0c4204018105600f001c000c004c555540c2007501000c12200f07002d80840c100b000d00d1404240c210010b1200301c09481080b540519018410800301c0e02614056102d00c0e0001d1086040341c60007907082e800000c1046007440749524644170b2038008a60088401d0710300358018000c000c104582c1c64120014010b480c81000050f05064000c0101c00c04c42609a100c14081030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 354384046 1250 354382796 354382801
    0x61502010501051914010e01020a0c03230309060301051c06110403063b0a05060405300d02030a090602180310090515090a0206040b09030118031704020f0604060305 72
    0x741ca804d4900070015040b1140b21a00d01c0c064100022030385a1000d141408a1658020b1207230b48207002a084c115004040c00152560300c0c1703009400b110800390542c0c5030100e031000068040402000b01c7c9c040d4071000f0452070440c2d0800d001c0041d001040d90f14000c890805502031070000c3d2142c0111200c603890f01c3c080607212455410910140c1e103040b54103401c13030507142014509038a91014440000c04860b1611000c4d1120f14403014505801100d020f00303640700b604100401c0110000c2e07504113401c1c4425290f0401408200309d61640c0100c1d50780103248100601a130f11048100342c1c055036000b04807030390100c0c0c544140d07103034142203921008a214260700c2d40034010195090412600062030b40d420750400410101362907054413a4426203440c0100740c07000011841400e82042010541c0b1f8000b0070403651150340b4440a007080c0e01000340c860003942450240381450580790044400c507501511240c403000c280c041c1c06d0b000303902d0080040386d0091200743c0c2c1e8046521840d01900180089846c0002c0c5030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 354385296 1250 354384046 354384049
    0x15041a1801030e2d032206090f030314160501200f1621110105060f010c03180b0a0302070204140907260303070806120601150f0306150201050105 64
    0x554100318141802c1c940c2141070003100107080305032520004107803050000b4041c1da4950100c040384075100c2900c40490925049140043d850843d151034a40b005e01042c0d4501c81601c40d1156889042d08052501c00c041011078000c800c041034216804a40500c5d081c0c042c000040c1203240f1100035141a9920443c0e01680240ca10800d000281d15024103801c20b450394080c0c034a103110b05d0702046060041e41d0900310411508208440701003401042d940d1030000d210310b000782420520482040c866007170001098040c2801c3d00000c40901042c0c0d10340034880ca40f6141a2a883c0d0350001f07845001e41070180000f02000b54102900101025580240c1d89198078010001900d03040d8948510ba001e0142c00d000f003280e80002c1c5942140d13281e00000e8508500c3c3d28070722040c03441c0140c0c4100540070000401207001c6d0f015050703a01c1110201d4820440c843c2101100d0399aa100340580c0d0981c1ca100610f031b45606004000e080d524000034500816034580780c01d000910304d01040d1384900940c0d16240180700c076 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 354386546 1250 354385296 354385327
    0xc0705060c040e240f01020f06010603021e0a081521011d030405060a0305101a03010302010f020307020f040e0c130b1002160915080105090708060c070b0615041a 71
    0x8102e0840d9203001401400844c510050309509005108120701c00041c5c0d000e9000b400005182c2039110300355185580e464202038082d42c02030b05030118040c0c1181d45140300050b8030341903842c0c07860340c2da64a0105945880b0118900c0901d801b05550005d65250204d0458000c88980c118403c4801e00100350b2041d91b0f42014480710345a60f04c550300780c00030f100c1480309841d400f040e00d0051449242c08102c3c0d8039100809080c26240790440f0f5030400141c120b00307808503c207a005504a074400c0c2d076803100c180b0840c441240c40c4c0c012198002e6024240414810741454150000001c010071035094810310b080580000d0703000303020040b079100e03400d07207880180c402d81c90882a80c1c421a001800642005440c07580c0842d50100540103503c44076658002a400d101203202e2060b0242c0310b80c2008103d17908000c004155221800c3c4221003840c0703c1c8000003920712200c01c00740c4066070f5004c0e15522070b5880741001c0000d0700051b0000c032582d041b4203000019020b4011f104645282451482c0035954070001d080d038400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 354387796 1250 354386546 354386551
    0x1c050118021807030b0a0b070312020a0503181e0703060c170c030a09060c0215070302090a0504051f15020d08040b0a0b040605040213090f0507170c0705060c040e 71
    0x603401105014005a01d8101460105404640801d1125625582d00b40c00801c010111550008000c1c54042100d4224900620b0700c113000c1c1d180c007190404a40801c4c0c00780c0c8541042c0100041d8203002140c032a444454801546070f01450a403542e41d200310040c03c0c0201d100300290316090740100380130814024248035001e011502403070841c081d2440c3c04c0025481c0c0001400e000950000040010744104082c3d10041809a100005008000382010b00a41e50b030b60315424010515680c0e000300302c0072802882100d25030030300980000b15003494101003000400d8018410482100c040d074021200440c0f04060360301411114608040440c8401d0000b032810310358201c03440030b205e0202d0600003c00d82c0c0c407c1c131561196074540c0125803c600f072000f140141c201c65220b150020700105400360010a250b4034201981c07101841080011480320b14041a00c82c00e4928801003400c58a081c200c400fa40e0800c1d40d445400c0084551501034240d80d2103160240450310480880d401040070700400d00781c0d040858 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 354389046 1250 354387796 354387821
    0x4170303070c02090403140304240603021302070507030c08011401140108040618020d0308060418120c0f0f06051e100512251a04080a0f0f021c0501 65
    0x50035890308900c0a0a58120954068420700c1d482000030105480740420034101200044a03a8590400b49030402d010041016842d0b0f038004107807000350981c0203510400e400c5030f030010700c13050246103000c414034001d50051f041502c940c0200503021005c1a010000794006110030000000d0003ca07945115103020030607085501d818400c0d2000012680c0d2040350640c009410001c00502d94864541021941c512084000e4014800d00800d106040d080100244180d1041d103080c0100d101c444511101403000000007020042d20b419900c0c0c2643c0324613020303103401d403140b0110803803d8580d80700c200f42d981175010102e23003690302c4804102071400d079080c10001c600780c2d80340c80c1111800c20b00c140681c1c0400c2c81c041c0c1070007000b4251401072512010060461403400c0385107840204d581c040c002d0150310019004414602204031404400319045030222402c854159000d00030303281c0c403036030f81a84906d44041e056542502000038040560788001c3c8240700344500d5082550081080e1802d01c6c2580c68440e40340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 354390296 1250 354389046 354389053
    0x2a010b010813060c12091104060f060215100305100b01140906030615090a081b0312040909060b0604140906060315011101061a13080c0105071202010e030f0417 70
    0x204802644450b100001c82d0300c00008905509901001c960303c00340b99051000580c10003151806218003007400507203804060f101408a203407150b41005111000d032085000507030000118041240e0f02101443c0c100d4181c004001c92281d494070341514140280c0c0210000941c1d504c0d10b0100d640e000030182c400091101b01c07103410040d10fa000960341c0d01009210b540140d0b001025018410b00d92421603a03c4600280f5410190f51240d90150ba00c2100619015500c0e44d084617421061400003401c039040c0b90704216427880c0506008200780a400d0060003216110b8413259500003d81c2c880014101400600b0b51807002c8400c000200a10100c1c0a8155405820704000b403205031700013030082a0540300282840880f45003901409801003843c0c0d40b1a0401e00030181035480000480750060030070f2203c03200c483d90940e48659800792a1030034070488601250080101c01d0001e188184026850700d91400005041c03224055241e0035a0300c401034140c0e49980c0000c0603c0304240014020b02419140d2005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 354391546 1250 354390296 354390301
    0x20303012d050904022805091e0103120504030819020613031e23090910060f082505030105011101020c34080102090109050d03020a06020c01022a010b0108 68
    0x4800c03254855002e918001c1031040002420342d110352081403a503040c5208807542190700c1c8110071116082500480344241c4600e4081640781e200e60950201e840e412680140d8241d29585d07419442003203102150040c01428400000071400d088050901140a0541403071a03002444000307061900c014028012110b4162040d0b0203c2d900074007104c80e501c1640040b9840200503002903030140b00807a001c3c428003001100035204000100040c00c0004420f55540c607a030340b1399080d180e0455646c1d0086200207030f03048420340d200b18800c0c3c140541012910a0185900c00d07100800d126115140c3c450300e011500002c0108200c0d680300b1030f00c403050003d1000850420000201e4151140c107080084100d08464080401d000e04402c052026004078444207031002c0c0382c0d9002107901030b420245500380070a80f0a00300040310308003135500303207115641540913040c07480d0701b80c0d00c000094001b40c42e602c2c00c0c3d41d420b1141603a0380c91100701c00514511150f003a0100e80400000342d500b5645111103650401225806 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 354392796 1250 354391546 354391619
    0x316170901020904111614010605060408031206150a08060d0b1006080105011409060c0c120a06050a050112030807050405030a0b0a0e010c020a151b0810050105040b070312060806010602030301 84
    0x20003202d640007c508081000e07010b9400d015010940140b030b8030500c00140043da43c13400000802c01c2d43c0c810f03403050860303507140070822120182d88041044000c504108891650b03114032003441d4800e40c002c048040011260b1100d0000782c5c0104c0d440c640104882005120654006a2841c0100807d19012a0444c10190303021614061101881e0044d0400300315448000000d0149010055018140d60401c1c5002c202c115075622180c003050312054600004101203c20328003406050711111300e00001d84c03200070340c0c0458000000a00710020490300f8000031420b40d4041c404041d00c540a08003003280740c10002c22030300880380c48403030307144941c0e1400d014120340c2c58002c103585c400313580c010725401080116000c265014102c020341c2c0c15801c4280c41c1d00820b0064000d108180110300c14100c02c03e105071140d005460603c681d0048640903102803141e600060b11a224000701860240800f0074115910040c1500c1c103c2d0030f81102c00907030008401031200e00e10208000104140804490014561192 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 354394046 1250 354392796 354392827
    0x13050601020a0609020f091f050a030201050301060e182706040f030c0c0e0a020712080f060f06040503010207120f0305011503050c31050402040b031617090102090411 73
    0x24000309520f072074030040c0065540b450200e0440f11400782040600c1c1c40c004144400c02108c180b40d180b56042090400b01d15418041e61800a485d4103848880c80e503401c028003518030350070070b21040b42e00001d0300c17199a01130010355908034081d02d030084592a09400d100e0b0803098111f0501081c081651115003000701140064041081c00c60701401e00c64039010150401a40d074405035004100c4110064050000140c0c00c1e40c01440601c2c003441c0120000640a070341111007020075078200c2410f1070b4181c0420761a240284030010079420086c0305518040e0b44001107420798124003001e85410408070101d800e0103400990200150074989410802e0350b04040340084808003101e58002013550f00d00000307071200000070840f1659400040c81d890000c1c002d0411010705409200c11914405004400060b142080d0003a81c0944079410700450955913920580e0300144801d081000402420080c000800e4030800800e078040c007102800980e40b60b010308240000c0d9000103801c0103680d00b0400020b0300284012 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 354395296 1250 354394046 354394063
    0xc020d0605040510050114092a09460303080a0c03022a0f0102040f0902090109030b01090b090c0316030f1d0a0501050601030c050a08130f111305060102 67
    0x10380001d65860728286107151000182c202c00800b03182c8000843c001c0b5281a1507040c02c13404556144032603640442c07130703420045801e1480c00c010310002d045400300613284020304030036540600424260b040401310365600c03407160300040c40c40301250030031000401d80b20508030303030b04c0c0c020700e12007103281c0e803540d503000345a088000d10028800d0350728100790303107400d10030b0301103444405180484100c4945840c901110355407042c511201c841c8240403c4610381741060090318211000d036241d00d29464a042000c0703020f98820902c01d8100100900048001001d4503806806803240b4180054200c04440900c10510300c09008243c8520080c81040070004130300c001100d91860901e400704220740d90043d14400340c4010400e10501040082c041c0224090005001800c00e0103000284000e8403442c005404480048204d840007607400c1100d4404207014983c442e0b08010914019009920543c03102079182203000d008544080d212440c10f4240e1030880742040c0020b03d13a100070461801c0140010f90b80d80b602 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 354396546 1250 354395296 354395303
    0x13080609071d040813030501050601030c1d0111031209100c1b140a060c0309020415030c170c06071a090c06161e0507051f0503010e090f0a080a02010c0c020d 69
    0x1c002c000f404204031807040e5130400c50207901200300c0e0b1342c591071b08134064481103800a0000380f9205610100034852400080ca0602c5960240412040a0011100c085c0741e6080c0130507500c0304201d00284c40d051030840310700c1248100d01425020708c1c041032420035101510a1202005040001540308810301d1068102e941c1d44854003035146001450f2440c00c102c103079000038200c58a0080c032404020303010b82003640c01510848003000800342d0303d1008810b40c0703120f02000d800c002d21103100780851600e0400200c0088424000c031051010401f0001d07405601c210070858585950362202c8440846c2e102080360070086a002030203114240c0c801049a070f0044201005109241c0780394402032014443e0b80c030381e1020106050709105403641c00d20f5030b0385000c98400c4500440030900c2c405040c1c6180c010303a90200020740e4840780f41d0707444c1c1040740310a110044c1040f12230b40114405800030260030400c0d10340061140800710303100d0043c03040290840e500c6031220001d000b446910880180e8811030050107040c0e2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 354397796 1250 354396546 354396599
    0x1608010e1c080106081305060901021803070b0403030e0102030d2409021615060506030c041d01030807020108061203031f08010204080c0d0822090606051206100e061308060907 77
    0x40340d101c5081b400101e81d102030b201e8001c0b1000d22007180010b400a201c40d0340800c944036a90487d081c1417581c1d800344d621072a100003e05100600005c2d1141403180c3d9080c80520460b820b1802003840001110490039001c1d202c0d8040081d00840101c5040c4400010441c9403001c40c204098a250410a4440c40d031000300844c928015070740060040e544498042c00740640050323140d15016890184940c0280070f01c000c40528244100c0582c2d14403220399040c0c80e480448a41000400d50040d1019400600780030ba21080f1105035801d141d01c204050741c4298000f84481046452001c106043d0103229000002903900410060104076400500012180c0090303c804040c41e00c242007140907406101200301c00783c0c0c5662050071642d07580c00280c10903541c14820803c54160b99007420b503410f10032203c20b4050500d1180024140d840c207112410452880f034203060710b102c55500002007142d44012003c030f003046040e040501440c46d04201c2c455005035201c00411119040001c00721701480c82c070803030340c0c540d01c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 354399046 1250 354397796 354397801
    0xb010e0f0102101409010e030307021e01021e03060a05030c03150411040501080d02070909030e040e100f0e060c07480306050a05010b0a0e031608010e1c08010608 71
    0x340300300f0404078280250441007260341440511300c10f41a000307941d17140a540c00c2480e80082c0040100840340114030030b40041c9104915044298041c05955200a00303e540c240400c1c046055004003c0d0916404603038207036540d1410404101c08616550000c0303001b92b00600d90241d55072000180420030030161803c402969449203800054299208192904141404000170383c800001500d219108415020340c0d954588400480c0203c0c2c8840c50080d000519055940100e0f00f416480b0381114200c603000d031454007140e01d8044040c0e811030882d488070142d49483e050b00002c001e0120581160040214500d0b14015491342c10000080c1095109181c0744000c00711800c1034892540030301402e10050b200d40708414810401580e42851000b65040740c100000030349803030703801d00c61641a80d284c400f801d4100003e000f8211500d94104914036094403030a4000c0b00c41d8954020b0690040104400118007401006a15418003c002d0521061010030700d01114082e50408100c03030640b20745207041582035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 354400296 1250 354399046 354399049
    0x15030c061b0c0305160b18060f0d06030c05040e0714060a020a0b160e100f0f02030d0504060e010b120601030b13080c0d0206010b0903030f0d090b07090e07030b010e0f 73
    0x1034524020b021071984840001004004100c81c2440000c2d07400c1542e200d40ea40410440304d215580741d81e00114410b6000350024a0500040e14211250019003414039060a5400f8103c42c11900181c5604e03180b0f02e010091407426019084041d01a900a4070f041d40c544004507510240d41c1c15000e02c508404200715880600c200400109a50011407403006401c0c00f100c668611480516104005000180030a4090030101c003040314254183c0c0d1150303982201084120342020a0310b52080c21400100320000c85c1481c43d0140e180118050840060100041d0070014215001008940e000749800d09183e021040701044541c112600441310700d00c00d40e02c2046113070980510700001440d0340300100d01f2401d000b50001c0c51050007204ca03002c495007640c0310001140a40107605031b45a065004024281d1603218080c05881d40e11aa002c0110f04c441050340d035424903500c11130340140051070440d0100a1b1440311301e201904142c25050800c161003d2000082c02043c7d40e102c00d500070f01500c018050103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 354401546 1250 354400296 354400337
    0x30405090417091f1d03101509060308130801060e0f0601050d091a06010e060409150305070e0a060902030c0a0c050a052a041a090a02040b030a05070315030c06 70
    0x1034040081c000501480321032403806132000c90f54240b0000a4420145250742e6040003c0002d90a400400410b41d0003452404200503260101500c40c0c1e540841c0c030009002451130048030081d5203c0e00c1c0c5c5a8940c0f044903210f10714144150b1040e4696030404d1000c01064200d0b6030f005401410300d10030b505095558a00582e0341d440758491a6050b03a1409850400380040408200c2c144212454064003e4513202c004540ca19001c4045503030001c800c200030440002180d028440302da94030440e049030300f6981d803120350411640c0d0340302d003100c92000020401a080107100e03035805405a0307401141141450690103138513014800080042c008128886001e00008100b1a0303034482e80081110b03020341384108030211001d000960810030700301c1d100103c04949014050041c852036883e559201d0403100a00300308501c071001d45010881d960800c00410004000d200a42c811107260802140c2c1c0c1c101800c0c014100e42c164020002c464444007170520004a428606008035800c915014910303641c00d9840c001e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 354402796 1250 354401546 354401557
    0xd02090904030806030f1f09110303040e1806010b0403080a020c0d080c0f03031911120f010609090b010c03050d1d0c01022a060310090c0305040212030405090417 71
    0x40c800101820801003642c0945401e1050380c00354140c0302c01e8800010415943d100400100b1403207481609142500072242c1c0c84203880502400f03018074280340d404082030a641c440d41100d001c450a2904000e038404a1000806807035410340002c086662425180412070300440c00020000503002483e01d241920070404d10012650007415800c4c2c0011603d04200c03d0761109104c900a409503c1c800aa11032002c010350344181210010408000052a400c07401802c0050a60a5841c014042c021950407054181441065824912005541000c01c060080030459209100440c1014030200da640d9000261894465141c245183c0304c10700b450040c406000c03855200c1804451b44424a070040340b000070880c0e1076820a8090b0785c403104030040a064000512a500c02a41844c5a400b0b44030341014002117620446404500781c0860303c0d0407080c015160034920a40c00a40c480003844254130b0300b14040041c480c508401545020301e40030101c0c8400f103004001a0503800346880202109002104564 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 354404046 1250 354402796 354402799
    0x305031c020c100e0c0d08030606070c0305030714072c070302160c05180907060f0311030708040c060305010f091e09030903060e03040509010905180106060512100e07050d0209 77
    0x102c403807003c1121a401400c2d80b42500c512485501141c1e5a541860a03060b0002c980041d04c9600d103a031240d0610129901900d0226480da04580001000c00c0c4140081e024592007031802d03102c0c80034024035480c60004036402114514280d00c0e1403201c1c8400c2d180041c1821006000c00141695482105400a0007402d280d11700c60003050301c44900700551400b400c0c040c0d0340d08580c6060940300960700c0c201c050004071100612580400ca082c041c85000390403551444256107000716100c2003040f125003098106503210000b25401c0400e201c2004044090a00034185600d410407080d890038094070f103c044103100c3d2302d040e26948e10b940c200e140d19110f203203600740d40c3d202002d1010b4102840e00030403062040c0b00c01d03105c40380b9040308040d40f000f000c021102140d01c020501d010a074204520503009243c043c00310a50700035070380c0720054542800c0c01142c000b0004e0703450702621101c8100d201c01145100601c0301c0503000c2c1d220401d00848101c1592941c02229a242480c0c841e04c9540c100d000a119603401c09 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 354405296 1250 354404046 354404053
    0xc07090c0c02041802090702010e10050c040e09010f060306020d0c0f0225030803010608010e0109060311010f031d03030105030c010e090c03100b0301080705040e061b131706090c0306010305031c020c 87
    0x1f001d06c0d501500581104c0156504403643c0d1081142028200c842c10346074907040040c104002c0140203001000c10f074202a90a00000d507400641c001e010440318294400c880c00d640114114180c003442e40300b002034400c40350030300104a40402d10000e48900300300d05014028000344100d0820b809074461154061640101c1e103075900d503100d00700944201c00034801c1600c901100c0c2c0001c01c0108071b40c06460b088030b602c412204142c402c154019a00c032105a203280e02010341c0c2c1c4511414000302010518003405400d07010f169a035040009160829108900242c103001ca2403c0501058a0719110380c0d074051100005a5180c0e00d03a001d522281039501d40c4010740d001c40120020800c107501090382412100f0072070b0101300d01710b03400e1501034803400304032400d01c9908040200c9554400b24030006080c1c6980c2c499034500d41035165035854103d03028170300700102950302c400b08018180c0001c0020484d1400f04400600b4650303d9560781d2035980c03142042045404504038903403101503441c0d4050303452900c98041134 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 354406546 1250 354405296 354405301
    0x3060c1b0602031515090f0a080604110103113402060906030a090209070305010f0e011811160b06040e0f06070e060d38130b0a030203070303050c07090c0c0204180209 73
    0x703103080d500100d5050748103440f00d600f47c800340d1908101d41c1d800c41300306002604840d91107840340b66080300c0b8241490305068840c84070203202d2414400825030500c3d00c040740c6a040940344a90540380c0804020030500c41c0c1012802c40260303a60700e0640c0c40c1c1d1700044548550701c0d03842c3c0ca0500094420f007840250000c819509101e003164140d0400c9059402030485115080c0d070b9040415040e18082c420301000c4006510f25402c0c005031500b189210103044406180781a800d00c00c0070249001008094884141900034840c55161074001c000d45031007080000d00011910310402c83d100c49015180009001c0e030300d6803a001c5500c4103c150742d130a00032514200030503807480940d98a0160340c041210b07110030b2a14800254a0b08a0202c144034030809051006c007c00c0d01003184009058514040f07030300c82101c0d140000140e80c1004407001551081d918191030321600c044292400c5500c1d08580382c014185a9900c4000358440402d04410b81c041b41d01144c0d1885143c09100d40105928019400c444003004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 354407796 1250 354406546 354406579
    0x5031218180f0c16232a030d020c060304060615080702060f010303140f2811120d0f0912020319030e070306150b1303060c1b06020315 59
    0x10510031400d440c10140d4594030103084030000e00c84c80c020401d000c3c2c030b0f078440e0708041804140c8640b25021241509541c582c94002c07602d161410302c00e5440e46086414101070007031118159041d1103107005400070900c20255400c044d486d100000501c40c000c90022000509000340e80e08050002c09a25203450303170b4144007503001405a003003110201c0140c41100c0214040200344000c0ea81200d8044c2d540182403100c4070042016940001d90200c001c1a040c0441844031034000c6100c90f00c9800c0c0c15902c00094040100a4100c1408100180254201c4160350300350840182c03c444150783c0780000022441c84010344c0c003000708582e84010301805840318642c50003d40000082c40030340c85441e1045050b05000c0021015189824500ca08541246208200040741c030740000d4001c00312a040a441991112004001034116040c0c01c080f4910302c1c4002c0061103941d01c56038001c11510f24140300a45609442d192680480c01c40041c2140d5000000520b0a0b00100483d40702510080c00c0744c50511401d030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 354409046 1250 354407796 354407839
    0xd0f0614010c050c100513290c030d020d06090509060105010809010e030d0507030204150503011d091c03060801090c1401090302010c150908040801050a050901020405031218 76
    0x40c00c041240300c585144003560052402402c0385903c44020301441d04003005000c030010202580509000d030900000030002c640d07121400140c40c1c003403a803400040e20007440c100182501850404c40c0741c42003241c114100e00c0071003281c42800380041d01607541d41413605c044004011a500540b81703140b44c00140210304901050140c104c1d04266595045521440740c043d0817200e00040405155108009080514030f4607001a54814600e04006041994502c6581041a4844078540014100000600200c16550030400e685482c40c0350300611403415101c0ca075510914050700900342d031701107a1100714951203074014101a001c442d00074040c0c00300502d060395140030180604030708900c403508910710701c2d4481e11804080783e805a5584500c01000c6c0ca074441e20807010141c5c060816200c410140c00b28844034000d0000300280b100015440c5802900c5104880d40500a0303066a4010801044aa41c0024549e02c6260082d41e0f0700d80d0710f000400d01014144401c0c4007140d04210031020940c40c6001d0361 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 354410296 1250 354409046 354409049
    0x1807020c0f0102010e0c010e0616031205070504050d0b0612100c110a02030303180304030b0c09040e0a03230c01062603030112060b0f130e071a03070f02030d0f06 71
    0x81d284100008041001a42030750702c18450004030343c0c480d11214059600c0303620141500003019001c207180020f25070710b8180f000103226080c0c1c0421202d4121180740740c01403041d03d5110b1101d11b001c2d8149428900096649041c01601814000d0680c0100e04290b54180681c5020609601110002c1d00c0150019014081071b01400001c200c0c2d145552080304008541480080e5004014528541d03030042d00c0d003000b0181c030400c0c011920003404040002400307103006502840d4210304080d100d0004004210580d29482031800c0b058200c48190303170002e500808a01031a03075007054490380b2400c2500c081000344c0950018400741c0e600304100003070544000ccc010140c408020b2120042d455048486452f03aa100c28440c80e0441035481000602190142c0d106080e00d40004003001c01443c2d41c0700000d400005c19404e00140079547e440c42e40d080b0b4804120b02c07001440c21a4959010021b0b48480c95040e000040c00b040a20102140039840c8038420f00c01c90b01190300b480c0c410800c180340190404014402c9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 354411546 1250 354410296 354410299
    0x10e060307060305010b04052b050a060f0e0a021005120f01050109060809060a090c0801020714010c030c0c0605040204060e2406090d0303090804090e03030f0c03070c111807020c 78
    0x1d50002160503407113402454182c401603040240f41514020034000940c5e24280f07120006a00c040d40c0d880486c071100c4c1e1568103280910010040c40f03030fa0f0f0400c9400c440c1c012032100c10051034000001e0b0f030140f003c2005503480340c0464815010804516050b40c40748a404141001641640704100c2c084018510290689a0a03071380c0003c4c203a15650103940704642566641240d070300900c00254004460380050700b4052140c194000d0b51541c4050351400c0ea00012812030340418000780c82450607000340b1402c010704405142c1440303190f81c45d680282c10382003200c001409503902c1d000090f056440c4c03070700410014400d45840c1452843d04620704481d0b03044507008000039404440010381c0c145803040550360007080c000e0101807146801c0c3c3c1c0541c01804c156a007110303107442c1070000140300121307072103124400080200510740d00e1070078856602c0302c10b000502d000b080039010b00038015429449400c41b8100b60744000e10100d26410003000480408081110000a9481000f000011a40494025a007940 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 354412796 1250 354411546 354411553
    0xa0906080115031e020a0314012a0c03030e0a12050a0e0406030305090d1703010602010204030219030c05090a0905030d06031a0402010f030c0c05010e01140708090c0f0f09010e0603 79
    0x100c01c07005000d14145480f0207018103000d2142d5001150070180c4180040d440100010201981c070380c2c4001010700d64080d600303a140d56070700907880c0f0a12443c6076000700f4444405c100014104242c000360044050481c054209a80c44c0c0641c0c50340e500400200c100c0c981c10022a00071000800c9000304245d00030310f400400a0110f21810074641428041c002c10740b581511030302c0c108a0311009202c0034058005c0c065a140300c152100041c01100c0c44d0085001c2c4c8020340c00513030344600318018007002141a0b11810119041d6440400c04200c0002055099900440c3e500c03245842d40d01841000e000706940107802d80c0070001d40c402c4410a00c0c0d1010040300d00c20311800c0a6803032141500265490121806408141210a50800700344640d103d00405825818001e290100d251103c6084030b440c2e0014003100da5598520510822030010425488022403420000d10319254500c96100c401196140740144070000412a0700e5a80c5165500c0440c0e026182c505c2542e503d00340307450100390079100a0f02030701 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 354414046 1250 354412796 354412811
    0x30b040f2306030a020919090507060906140406030b0a030605130204052d090708070e0f0c070c030303020304020a0302060d06030212010b0a030b040201050c0a1a150108040b070e0a09060801 83
    0x1190101c11a12a0300d0040142c03960606a409100f07040c0c400400281c0b080c2c0c09050b119144103034a00c1150302c0c243c000c41c0248502400c1c05006002000035400030009c2c4000b00604202040340441110f0503111079280200b80b0801c070700c0c0801e501c0c0c00c898000a00090a0108000c480600d861012030310700e0080b074003070085440c0c3d081c48032075102c9104051035480010450304400d1803800910300e07400c851100c040394001540c440f10786090040c00e8021450101d014811702102c03107081ca04a0303420501900005290103101d079908441c01820384401428035030040001825952494000001981c000d004540e4420500010314000d085d50b020880c8500a41243d0b900001d005224400d0786140c0508a0030b0a10300310740b1000e0341c0c10402041281001810421907040034010304c0800038051081d500000d2040002500f5071404030010b01c220fa02000103003450308547c5c0c0c001c800b1b642094100b142190251600602111440e012fa42c0c0c150b045140300e0400070780124a0390150307040f607180384001c010300c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 354415296 1250 354414046 354414101
    0x3210d09080d0b0a0e04020102060a05091908032a040e040c050607050c030f0303060a1208041d0106020706020a03080106050c0a1b03020411040503030306010f03021c05040b07020f1c030b040f 84
    0x42a06407801f900503444180050f500d200d1a61289070803081500c100c03500403030410b0000501302658002180c00d180c011007401782604c4000c140c00f000c0004040c0764200305001c00c41c11002030245200303031050811380c40042030901004884000107080c015103c150741d000e2a0a005a40303504500f519402442036024062070080701101b03032406258000c0c545021a880c2214000704401820010360f030314482003000183c0c101084074000184000004284000e42c0340101c0a401c02c10103a003e2400e6400054a040000f58085103090540c0c1190403e19100c204900300301e45801c9031324200520800840005c9280300e515900e4040440380308a07428080c40d40b502c4c4a40c1c0188c00385100303494141d482071000c94501c0d07000e00c108060000c1a840c00505019040c5c5640038000c084002e10f100301c9980740113202c1400031100380c3c19445241c40c0000c4c03895002907102d9558a02a280c80c603915000560a0094414440c0d04580000d00c0f00a1040c07182c0410710a6030700c010036007094084400b078610480000705 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 354416546 1250 354415296 354415319
    0x20d050c03041b05010e0d1b06080603120712110a0c08030c0d1b02060a0c0b04060c0311071101180905041401060807080601090f091b060e03210d09080d0b0a 69
    0x182c5106940701c4c0c06c00048202413029000e0740031030480704107418644d03004841c101e00190340e00829840e65100c000303003806020305090040b10107500c64024401c0000f0700109240342c03500b4011124500e0b18010f4541100d01480c10300100d0310000708017103000203002038031480001c040d01e004280d040c1525401a0f0561050307403000762501e129484102d04401e20409850214040c003c0001541880c2030801542c1e81d540d04103c10032201258903598446c1e10901c26980f41c880d00038103c00403003009140001c0c1780c40310502c201d00741c031030030341007001d11100785030340c1010311900000401c0880010312240c101403030514007140da0f0743c940403401d40c6071910000b4103100008d00c0c2002c8814040c003400981e420440000040c1803c10f8010f039030642c9580b032020014850403106081c01c140c4c501c5421426003480c0e8000d0a481d01144214841e5004801c05101000a0341c0d1205007000e519203013540d1984480240c40c007074800280003400b400070124021412507641c1d0005484583c0484003011225109c0005510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 354417796 1250 354416546 354416549
    0x605010c0201020c0d1b17070501030603150b0402160303020705060903030f010303080a09020a0b09010e0a1d180304030c17031c0f0902030319111b0d0303020d050c03041b 75
    0x6900ca0310604c241410120f0300c044089000c0e604042c4024006226151210600e9100c85040e540346102806200c8003802940c01a00b400d203424000a80313103883e13030301c0910b801d503901e44015552692038107501e0380e031079044484400095600000507102410041c2c002e412000301581c0764080c4a002600845e400710407284104142840c01c0881e074290b407402c460030345000340700ca0065540d401811016030384181e904c80042101004041e0381e004000001002020402d5500d802685161810b120009034003000b1805904000c0040410340d03946041810014807031088464203000024010082c450b51500c58400e44500341c02b100f0404101c000342c586e0b01c0c03151140600482205103150341e81c542c1282c001c11010f441800d004629140c1c607800090842c0d00000800740c06041e03404504400c01c5d040134450b200d1425400140070030701007800c01084c012030b001080078401c0b8020040001094000e5068600d035503060101004140307040d19814142d50300580c1d003560b8403109400414103041030344a9580 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 354419046 1250 354417796 354417799
    0x3070e01081218150301090b040b0307060c03090302040501090203090f060f01030308090a120509040612052d0f0a150902031507050d05090a0201031d0a0305091507150605010c02 78
    0x1950b480d9081c01000c0ea04a11440b1803d00c0344254100310950f2040d440c945092803030003409540e54540100f4004030342c031080d5030078011403c0c100100041d075000300e4075008035045400e0800e41d003416840c04131410780441d00003d60207441c0800204503030040c2c3e80510312030b00001d02110300011481055561350340c0304842ca07281c41061030005100282c8640035140d003004640303003200c01c1c000b400c0c0c1d81c0f081c0c034500f0080c400300040c0d00429081d2107460503015440051484a890340380d40041522215140c404001c11072000507211002c4085590141482582e251580401d0320f104400807055107440e03c41c1e161050341c0c00ea186000078003160070070b88151000c031ba600400401c41c0d21070484451100c0c800c001c00078810302509200481660403613020b0300e03100b03221840244c0b00030055840058125030b0b80c0400e482d80344481080ca003007508030004a2860080d01800c0258a44101e07900142c00c481100044c800d40c400e002c6885410000c4000340b8015902031110184000c544400044038003c181c040080d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 354420296 1250 354419046 354419053
    0x3020906031b13020f0721051c020a0c08040906091406090411220504051c05040b0f1902030307030f1e0b0d060c080709150e040b0d0c1403070e0108 65
    0x24683c5845610500190001c200140c10080140941e5180313800c0702d00240c4901005005111004e4021201d4620904107130034030506140c0b40d401e070300b84e41c4010f1064040595078005600817455010b01c0c02c000c4c10560101072103a580c0c0e100c03034004001d4180c6100300d4500a04140600e20071101e500241c9119540c05801d0031250b9440d40c41e00d9510028000029330050b07120350754101100a0340c181141000307400123010903207040920740319207045403903004044040691500c40d45035580c01000c550448045404050300c9407401e4417a40c140d8481c03400041100c45c0d10341001100350360040095403003403140b9182045840403440d000029241c2d500009010311400f404926200b03c00d95000d01070110b00030b002c0d031300c60300400c0d0b450004a0320480881c40c04500d8050420110540c0300b030a60010b4403030260111b018200c4140301030003603200303461200e2045455480381031f2a0f40780c400c403181c00c081d00050300d07484250b901c2841c1254035105207010360290150041c0852240d41e81c503940c5041783d03c200003c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 354421546 1250 354420296 354420343
    0x10b0702011d04090206040906030209060301020307020c12100f0c11010b0102060106120209040c05120a0204030b0c0d090b0106090f080309090c0702030307050d0e100e010804021203040e100302090603 88
    0x626500002c0c00500e070303006075940f03004400340e00c80002038405003031000381c0054a14218010010350240041406109078010070400c034001c0d038040781c504919101544c3e4400740d00c00103c109402c15442d0300044030900d1912414509803c4d0030b810400c8040c90030346034401c0d9000d000302003d00b40c41754a01040d0142e8040b40c0100840352040d194800003a0780540300505145911000901303490019034070340000750002c100c01060001080780715800640f96107017185450b00d59903030074080314401041d49030000c8000c034070040c041c2e00503000300e041c02c2d41c0030700c0300e040c02e42c0c41d4000907003482d0341d90045031000d0311a480003082083c8000b040b50243c98006162803019602e50701c0d02a41640480340072a0507001c1030094000280003041a6541c11100e520782014104810051003150f0240e820400204001d02500703000d280d0300503852039003164040d14180d00010a502e0040c3c0303107100340d900450340c2507050000c100c91101c1150700c1105076442140c4a0007207459030001c1550f40c2c081c0c00802c40303016035007210 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 354422796 1250 354421546 354421577
    0x30a02100806190e0f071107140f09040c1415030105060a180e0601170403050a0c06060807060e031c02060c0a0309081803010b04020a1202030405010605150a08010b070201 75
    0xc01541c424001424110b0003540c40c15000b8000d00140e01031280302c2c40d01c20030b200c40d1000c1d845c045980008580b510406818002d82c5466840781c00b44a10001c0000c00f4240c0c820a8660039000c40c011880500201600d042900d0414250080c600c1030040100c80c02c41c61960a15000403514041481011417a045900300320401c200ca91200b0f10500600c0408200207100c203c0104100008005a006140041c03a00c50000b4000100700c16000100050480400c0006600f05007a0380c2008039500d030000c50b02c4610b14000004003240c2c0c0142006210750400040c0180d444510307080307500c10039810340303400d031044000301100e0611000034071025800000008818892040103881c00310400c1c0740118003000301e80c440d803200354072681c201e6150340c4126809241c2c9080074005c0d0f8800a030241c0b030031442e0040ba600000c1c011700e040000c8002d200d40000104043c00fa094118038090316005040d4102e449003175061119983c00b0040003808188250000644006a4001e407410144c06854207025180d1041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 354424046 1250 354422796 354422807
    0x105090d1803060516020d0203070309060e1201020301080d0201150303091205151003141c0302130302030d0507021c0519140a05030a030e03040f03240e011505030a0210 74
    0x7081c206000000364000400701c0d00a00406024441042e0201d06860500c2c40080c01e15150b0003c00056510402001c80040e0380704440b03100300d40c82490b00c0d42c500700d0716000060058802000000443d8008800031078000030202e4075215500a507002000f00c1d5030441525000700503d4480900850100c90301000380c810510044802207114000b40c421000e0410380c070013040101070390300c2044035650707601c18402c010011110040300b5020100030b2505a0100418645442c07028010b00d040503008240301076400b450403490070296a009094840b40004100014550380103010140c1c407614a000021a01ca0b030854902d10085403c10060441503491180c40c600281001c6002c994270940c0080040e002c3c0001e02050840b244548003540c0c0d00c1051400007401d0720610104101c694004020400500f001d01c00b44204880d070228020304502807500440741d4903100900c0440056042007801a01d0002c10740c40280f4602000130302ea20040e48560600d59030f0000034100035040b1050103a0320344614000c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 354425296 1250 354424046 354424067
    0x114090f0105152205010f022a0d0605010b0702010318030207120f050d0c05011d031801140f0409060e0f0402010c06240e010b13060c0201020304050a080a020306090105090d 76
    0x3c510b418682401ca8001e188503080074200c00c250302c103503450180140c0da070050051001610f81d01c01130a0141c000d4800d60f0654900c08203042c550050680c1c0800c4684907801058402c94110404005030760b5034810071142644000c408900081c50400300b51380d07240c01c03c0b15031140241c140c2e00401560303040c108060881c030841c40f420348405040d54103040005008000c0e0f00e01000340d07540c0e400c505e10154600203094980c03003140a0404010708004c0c64120034004181e070984d01100d01d981744c2d40c2c0340c0c02c401a11400740c1c3e4501d046a040b000074068603030080c410010000c650078600204400e81d9541451415071805907907418040107100e0104000d58440e40d00c0282c1c0d54000c1074005000e41018003080088035144501e103043c44506082040180300000d0207a00600444085620708a01102c914015054600a100521030301801c00c10039a4806c009807000340501a198410540d12641115039894201c40b040340b1a1041e10009002130606003d0a0701400342c2070001d1440030310900c0191241e01c000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 354426546 1250 354425296 354425329
    0x5040903210219030b0a15020d080a0c0c030e062809050d0f29070215010e04050a02010503150406180f140610030e060403080402090702070e0a020a0c05010f02030114090f0105 77
    0x8090106807c1e61503803445020000d650010304c04d81081910242c003a80e00100080c02141c07510404507411508400c0e62691240c0c03624103d00450070002c000745590084c04142d100944402005000d013100111101115895130703200c02e4080b5940b5001c000f5140388500006201c50921041c4a00003100101050041030b10a6980c00c0c040c00424045000c80d00c04482030b00c0160f000784201d440b4a04484143c1f4054075a140340c41ca201c0c82c01e40c59042d03a0f0500c8040090401c40000000340e0a0680380355a01c801d44e40c014001c3c4030169840d404520602c840d4035034231004038580007010344c40c01054410610925061804181c580c1c0e143c0007041280b041c030510405c03e02d13844000001c4c96580c10300200b03208900c282c980110380d052500500c00350107401403e0009660110000717003d500000b0341d03813540c0181c00540160303407121810400c90320540b503018020308540c24900340035481c90690b00550f068501c403000003a100184001003088c069020f5500304000391402c0014861424000d078002140c205 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 354427796 1250 354426546 354426559
    0x30402060c0d02211303080702030307060603030c0c0618090c02100f020304060501291e0703080106030506030a17030703021303050d0207151b030905040903210219030b 74
    0x800004604040e9a0b000e0580160050340e0011192a03011140c1400c0d180060304241c180f04075403a003620f14240f140006005544041440e02c01c6607000c10441e41c0710b651041d810300190b0f94901d0090240c1000c40400c0314102c403003400201d0450306c034020454211003c84440d000092130300c1380c82001460410072507030441c06103000800c000c91440c040c0710314000d190240180e403440d00307007004000c40d001a0081c1c21482038940200b5400c102c0f191260301105541c000b21580c8030710070800c045001d000d072024121560400300c0c18200b415088800a4100c6d661a2014800380e42c9007410541c4900102c43d0007054010600314456142c5540800385600c4800b904006280128168541440031403e0f40210794660010528505aa50500c10380000f002ca40000681c1010b40320406484803601c81c94089081100300189418144650034140080c000500101320310003441c10010000000501e414446104204821703004200764402c0320018000c28a40400410302d280c4110041c00c104c02d02d0310762090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 354429046 1250 354427796 354427807
    0x3071b060f020a26010513050c070b04050a021206060d03050c030d021c0b01140906090103060512010204170a030f21020f0d1409030d0b010513080f1c1403040206 71
    0x101d80d80300400c0b000c40e0036224104040450741013120f940030000940a104c060110042060352a45030711148660548000850140c0d120960743c20640540c41d00500b20031307070b10700901003071240c0400e00b6404a4020340780c840f4080800b800e2190341304030651309150407034440d10681000c64401c0020340750380d44c01c500603a854048840c90321400da801000d40070780702c1c0c0c5c04003010407081456481000300030f4000703003080e04030180481806203442c006e100c82c136401418000307052002d50f840b0394016005003600420140c8100e0000107164001d4006000e450740c07411001e04010401d442c0003494140c400d03030543d0b9070881d800081908660800c2c44850b00404840c0800d03103000d800d0002c0c0043e1910b4102c2441c0261140480d0b0312240903500d900c032a4020f400c03244000d00c04040d07404021118404090301d4041014400c14004841c03a200b0160000284a41c80002190300303400410380d460400280c000310760005c5d070700c000d015074040448402c0d00e010810a0702c030000c401c0b240d0005150700c00d000420503820034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 354430296 1250 354429046 354429071
    0x2030405041d0a03050a0809010b010804082b0b040f200a090b04030b1618050103230103050102030f240f0d020d03030506030d03090f1506050d0503071703071b06 71
    0x1a8020f501100490303008100044200e074004101d0380d1001d100c800a1000c00602c0f0000703051042c0241c0050083c4a0002d00280c4108079058180702d00d800010545501c0250390941c40c000b000d90031466403040c1e05140c048820010940680000728006040004a10750041603043e9150701151510707080c00100c0301d0001d0f54035802c1e0080e00040d4010354500040c0d00e0000d164408040221085030240010000d0900c400100a0300b1a8142c0c0e0302800c001500c000440b0103e4401769441510350099404140003201304603042d006180038001d00e0415445940340c040b4800040e0251310750800720700c10b480d64000e0491030074503403c400c0c9180140c840c490920854012615107130903150b06401194030f5030705006c00c0d03003000c0042028001051404202c00b43c1e45542d849a80c561480018000140240c1851203042c0280d002c42d000b0113000305084075010b007925040d0707102c0e005200155654003124101072841e50070b0300201d038890065070f52020300003040842c5030101003005000c10b8812903960313540881c54 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 354431546 1250 354430296 354430303
    0x708032e0e270604060b10090803031807120507090b04020a08040b061311190206090a060b030c030a0b010e070903020a06081503030a20010c091721091f02030405041d 73
    0x240d005800104440c6603000900468500b287d56042c1009007070b0a00300700c02c007030100640c3d804c00120f000e455039200d01e400d10589850f509030040c45050103002c00000c10018005088822600390701028000c41001004000032800369036072003c041a03035072000a0008500507545c2e07074858001072800245c030b91095202c8007190390310209540180c80006944076101414036480003100c00c01d1004203414a080d51a280e01c5000c00d06005002d1a2980201484c41d5024014040ea549025046a002c02080c0c141002410300a12441c440c04080c0c80204010390320414071017040e69009051600340740d107050400c4950300030040c03507452178100b03a03501603031255001e01c011f150074a040d544039010200c80f0002c14042820780a240d00d416850900c0450f60980c0085002c401c498990400340e00311f44940c8091410521703024240c8400c80001c4480718074008854025110380c52080e2900c3d00e1350744000d4103141d01201007800c15005a801072104000f0b07890281c03c86103266041603103001c00c0c40d12203942ea524 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 354432796 1250 354431546 354431551
    0xc0b0a0c140601031106090a05060a030615081e0c0d0603140705061602090702160e010f06050c0c0609010509030303010806090f07030b19020708032e0e2706 69
    0x39811620328081c4880c200219000c80d1100d805005554556030b03c402100b640d48958500403800070a64283c15512105c0150007041e01514596403044103003001001171099000c0c20076419100c014051026110f074032054450780400ea4044030000d94000c6004d1582001481441c81c1a0200010a4406401d004900c0198800c1a22021204402400741c0c02c200d61904510302035242404001e940d220300c07100002400b601524820266262804c0c102d05103001103100d560560301c8031100240f0071083e00c010764100c500040c80940c0c0700c0c2d1104021a081d11030031a50500745e6122822040562900030018001e031181410064a003918a80100341950000d80c80045107401c60020000803480c01d008031821422140040c00c44141590348840305440c01030700310001010000c0308a1283c2d81c95070b04480700d503500b2410070f68072440c00081d00040c8600982501004072245080e041044031001c58000c00d0301d00914212400795101c00d509850041e6540d115034851900b0580381358407a006009050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 354434046 1250 354432796 354432817
    0x12042304020d060f270207050f1504050d0504080d08190c0c0c14060403080313060e160e070f1404210b061504030303050a0b0a0609050406080105010b0708070c0b 71
    0x2c109140013030000d079001ca03581c4524030003400c80c0201c448841844402035107011130201c005880e6060307030a0aa242c02c550b840f6a54481c411603204103105984440081e10551013907003150003081035014100d03140c1c00b4602c98008194024643d1041060207485142e034050401e2048040301c45604040c4403e03078101c64089004510302a86036428050035030300e184045c0c000d5041e807d440c1110603020401c240b2680c4000740001d000480855121941f481d00711142d035802c84400c1c040c3c03039a05480a41ca07002c1d100c00c00c0c482c034000b6034000505801c41c007046a1041455444070401080d480e00e05503259030303480013000b00c1c075201040042101183e40d00b00d201f00c1450310412110580c00c4d441d12800f01e80004d0f002500c9804813400300246c002190781107900f80ca5040c0340114564880e0100c500c0a130130b8061119909c4a800500400d80d03990140c0100c0c00c50350300711000c2c82140d5a55003a5130032a2400e02502c0e49448040240c07001040b2000300418110f88925108440c5950300c0c0250b034000d1304081d802c034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 354435296 1250 354434046 354434051
    0x9030201090b0a0c03051308091002031e09010e0f011211070804170d0309021c060b0901032a1d091f0b01110d021b1305040f0501060812042304020d 65
    0x5031342c2aa49481410762040c4105402201704050362110307051030145c12442072080c0c203c5803001c003205100b4815100d0b11915003840c40d0110000c01074110242e00a00440783c0020710381040c603283c600c0c11410802c00b6841c183c4401c142c2c0c0d40260003c074041d1400c105c1104280c04100b0480300010b00420042c401001e6644119035014201c00c1d41500700704480030340c0303810142014680c1015030386410398100c0350704480c2c02c02e420540c864600000540303c002c10450b400968000000140130f44582561251018096840c00142c155849500002018010409240c48440c003090810f40720012203a001040b5804507101d9011440c600c44800040a070745540702525032030b000c40c6035600726650410840d45103003d4152800302800c002c0d0303075203c07180c400408040120750704641519000c000c2d801c1703008030701070a11161070542407600342c02c04840360880c0c20398a006000101c4c44004505450910302213403080d4641494001c40c0d40c4c002d074014200541801c2c14034603085055580b44001c00a008122401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 354436546 1250 354435296 354435311
    0xf3c05090612030f0c1509060f06010c060e0a02030601050103020c0a021c08030a09020f0d030f030c11070305071a0f030c0322051c020f03040b0c010f0c08011e0e070309030201090b0a 80
    0x520381003600c40e01003446415406c80503c1541d090129200340d00c8440400164840e58500004880b90060004042d00843c85d082d080c0100050210322001d0140c001d4088466a990b158011030032442003000c40340380ce400c925844001841c1c91814070204a43c80d504e09201c009841e2078000c03080e0b00c2580c144140560b5a2030035411400c1254040031108030444540307141842c1c545001c5c00b0801c101c0c02c1041019940e001c2c11549601420315044101146011198516144d203809540c6007850b003d028540c80d00d00c5a82c0b4540280c5404641d455000f044e12a070071034444031307035140568001409002c150700e801007120490021248256190b81c6c0500002d00e0783d0b8a004407440c1103070b503d00c0401d07400c41d00680c0e401d4481120010844084038442d00c091a03951a040b4200c5005000e011f16540c1a1420010070303100041d81725108034169510380a50614024030550b038484054480d200712035405192034002230702c05000b948001d181c07078000e00010540d500c0c1030f038070110990f80c106c440480170340c0d032003d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 354437796 1250 354436546 354436567
    0x5090d0b100305060a0209060d09050f010f021b0111070b100e04031e0f090b07050a120306080d181a07060e0d0e01030e06041403040f3c05090612030f 66
    0x55540103a05c0410851402e007044001c02d0b0244280d601c181c46064966055908100f401c2090104c042014002000070f248610400b0001e98000ca40c00c0c3c0e12840000148803501394103214100140040035549407030302c222903076241c40c3c802005040c104984a0340da4000b8145040041c8144030310f101b030355040c440c40d24510b14407410501d111900403c014a12a143c0c039a1500300440b00f0030380e00b034918050381b1100d01d072034540c3ca854401d0600034180108900d4106600c0d1305500010162000d50003960b11544040904403481080c0d485a50991484c01004203c105202c1164902d4083c3d12601e0a01e4158903403a6401914406071056425a0040b0002d1a515502003c420f11b000b0307003440c052009040d0349494940c4c92070003604c06821032404c482942c070134103001c001300c038000e0551045110103030b681d907000c803190901d007041030030068582040c80b0110b20540080c0c29644103e0600450580c90403c0144048254001c1c40ca0341c01c0380a01c41d0607440d1070002c2000e0540b18a000c0c00c1d095607403480c000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 354439046 1250 354437796 354437803
    0x1523120a06120c050f06070818120a110405040f08070c090506061201151803320a06090c0506040902180108060105071104060e070503090f0c0307050105090d0b100305 73
    0x140b010040002400001d00002e0003803103020b0807036208441c003001c61108880020041d01c112140100b402100007080003d448565000d00c503060380c100d51103500110080c00c65510b4240c0c84500401300c108103111000702d49415807113950424000c1540441c0384d502a5183c00090b03000040079a1407804185c000c00c0301c08024050a42c0c040700940f0100e00741150700c07100410841d01802201d425150340d070040c120b00c91042812122046940000d500b100d650307400d0005408240400d0340c07101d144ca0504000b07108040d202c8040300d44a0407402440c0346007440c1c4902c001000398103c1242c9400c040c030700008442ea0b03440c01030806802c03c58401a542c0004207008032082e1000005103050040100070080d450303804ca41030b80e0f64203400c5010204001c11010028009002c81d8000708681d40100051184039548440a50b21a4034424100d0b210800c150a1059881d0702c5415020741c5940224002d02955100c0c0f009828030f1100500009160f00c85660307401e0350f22a003280c011a0300414800d00700103204040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 354440296 1250 354439046 354439049
    0x703171e0c030403021c081c0e0a0f021009030c090c030b030d0509060315031f0c080f011715070203070c0e013006052d011523120a06 59
    0x100400703107815a40011a900c0c1c0c05544000381c030811340520f0300300c1d950880e0900403500c1381e4080d015a558001202c0d01046072014100c440c01c1003803402c40780820764000068200d0702e16070010701c010307072040c076a07800c1080c145e11224100d020400241800400250207224010140034074000104080d04c502c1c2004081300d415901e0140b00e07600041c0340c01446034100e022a041c0d040c00f55913441d0740b9501c03c2c0e0000c000121200c19075406108403120b01101101c20401c0da0381d081b0423101d00303004c8100003010490302604160740c0d01602d0002400100701c814407440b0180340c030400110039039170541c0888060885485086a8a0f00942c0002482004104800741000040c08140754a03400310b50400c981a821940046280c00d0005034211641c400c0440041d440c0c045550700c2a0240014686070304114400d425055011884001402150f4080c41010030340034181d03060f40581803915103a003402200d041207141c41e9039200062404000c40c8014800c401441000f94100c0754603000e0510032001021103100c1e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 354441546 1250 354440296 354440347
    0x50c09120f0c01170a0b19080d2c0909010605120c090912030406230406090611120c37020d031803121d060115020a05031b070317 57
    0x42c1c0010380d00e9070b080c00c613a0417510201e00010f00c4603000d00070660000003000182c80c1014040e500240104d40020041640b0f030450b610001250094841c1d182d00c640c0307000e541030340c104403061410340c5030070008080c9070700890001c0042401d03a941c0011441c0b0351000e14184849812807480f03000f0504202d100140c0084614005101c03860204882040c50300020780010f01d01920340c1d0000e6103e5400404829030500280407000c5079050034074041c0000c09c4203071803c549141c10903541109203c40001a01c1c0119501c0b000003503141e42d600ca8a024551008038000c6510441c000340b581c04c1e806e00502d40400901610210300009101d44020385004416805c0d102014241584881c10440002502c0c40c4c8d11b40c10304004441c0c04c400d00a003000742c8449203001c41c01c038004102c0c1b55410303580054254101c544c55580396110551200c0100d888030f6142102401d035071b10400c880342440c801100c8401c0703001481000c0c0c0f02165201d40d61010300c420b0096200c040d00b01702041c03852900d8903595107800000d84 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 354442796 1250 354441546 354441557
    0x801030209011e0306020d0f2a20030f0c0c15040501120b0301020f09120309010c0f060603020607030804061d07090e281704030213050c09120f0c01 65
    0x510303800200c070464140295924007004440002031004482180006035902c880255201c4042c00d542c00c0062080c0020118401d0600070340220210a02030f1f141c0c0340a0641322042d140c840703041401e891231034042940062400b010034691184980c01d1001e00a95007520411940c6c0740f6807160781c54503218034a002c0c1449800e00001c0300ca844041d00e01100c0468000303081c180601c0c0c001d0340840d40100a803644460701540009600f402c0c60048400a0000c400d003102c80c400c8048941e49000e07903078040c1c01046070100e8004002c0d8800f040700d00a8142d6203c2c400c181c0810f03921307100e83c0407610a4001c42c0045000c5240502403000f04001d43c0038014076a44a00e002c0901d00804c4001159038264034410203034519a942c5404001140602c281044600c031303000302d5003ca8a00303d40c0080700301e02c032000070b40b002201c050540c80301e11354410840e000c60b90014801c646030b1520f00100001803c019181c3c074040c08040003c00c600752200b041fa95014030600d005804002e060305006402c114003100200e04019 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 354444046 1250 354442796 354442799
    0x3050c090117030d0e1005010303120c08060303030112050307060c05041706061807180315060602160302041e0e0c031002090102250b04081b0a08060402040b15040e0a0c0801 76
    0x9400005442c00882c013540d01155104144440074100002040c401c2c8074281004008001d16800824000c040c1c101808200460b2401d0402100d00150984005038160010401000034400082d1030364507441c020001d492030140c003a51108200e5800c40003030760100300c01203410841041034074610003a01e49998040e060618120380011300d00864545080c2c00c00034000041507207688900380503013900e4100c251041181d51a820201c030450b039081c00111149081c0100070440340c0c4003041026850101e400c000c11102d00b1a0300304005800102c034840e04820384c20543c0c008110490240288421800002d006144084801c1c1801c01c0154084842c425004104040c0ea903640020380e60790402c1e0f000138406080c248440854800724480d800b00c840600c02040c00314403c1000f00d22240c101c0704d6541040f0411403004103000c0d4003025480350307440030f41005001078050306003500200030508005040701c4900c0f020020120160b005a00074483c064000e1040008029a500c00d184019141d410a440d840d03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 354445296 1250 354444046 354444089
    0x4290304030215040c080708010e0601170a03110102090d030f110105100302060c0109020d0b2a031f031509020405101413140f070e0103060b09060a09090603050c0901 73
    0x302d4070182281c080f450306200050a100250405a000d4035206043d5200340d90b44006d09400307060034191242040c060200001071001e454400510a03048900c040c0409071902d480030f0715102c00717441c1e185515540802031845150b075112080300c0824400e0715031039144031000708002d00d0a5482034411429030301d04410701400807400d100d21ba0407254112244d0b40c0d00c074150071505024101e82c102c000d4101d0340295034082005151641c1c10710407401c0e50381e544483c910841c4158840301103520403005014041020a410280c0501429400307a0302050700329449590340e903100d00c0190310b40881d006084c0d0344c45e40702c401c514090281d640c200344d2000710940064107104450b2564004042c64a20661100c000b4070200c01d004d80002640c211503420111092802010380c10301c40c2d030200c625000055083c031074502598007a12030001955441c00c200d40c00c0044490600100382d025020f803000380f210a86000814030b0b102d01400018500ca0400783c0058190320b070511a04140680100704c40340700150500205 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 354446546 1250 354445296 354445303
    0x703050f010b03130507051c020909060103020904020d23030c0c01080c0d0527010207020a0801021c110f0706151a0313020109080a060507110114041b0b042903040302 73
    0x1c00e845a104c94201e100a00c0c2103842c2c0041940000c3e088440d0042150302400525110010765000b924140440d6550001c411b440d401c09000007035014103c90040350140c141002d800414503c00c4001190048580700380c00040c2c40c024010510a0b4000130308580882414444003012030001c0c2040083c50500102c80c6840b03019920ba00c001007035440c0001004021074402e40f49204044103000040103142d41002d81c041d42c0000340aa0213402300745000111100144200c0e411494550745008084890800c07680c0601080411684040710501c0b6104c9914490401420010306c160b0001501842050409200e40400d40c4050355403142224011604030401c4100d0703a000320300a145a4804e0400d100580b104511a0023041c02441101e501508004440c1d02a42c041e48054480300007001c00b8a01035821b0360490800c6207000400d9402003000104d0000d244400d190041c1c096000c0305444511001c01900b02c3d900050740b90030303410240311a40000d68885031500d01314962080c41c602c0d1581f4040e43c4d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 354447796 1250 354446546 354446551
    0x14030a020a0302120c180f090402090603010e0f070503120c0706030509010f02071103071a1c090503160b0705030c040513061502070609090213050d1e08030703050f010b03 75
    0x589800241c050411440303070707040ba0301e0004000d4504126041072000161290070000ea540b29841c008010a18245486600081194402000000b80d0380c0e031542440803c0101601e01c9400d907480d15070002756840240024250310714074900810029142c030713040618020100340c401554610800103e00e59940100c1c00c0340c160f6615040c089600d4458410107801840702d418a5042c81e032001c104001044940708a101010b107003202107602050f2916482c0111350407a0310401c440490400208007007904d1500000d000c00300010000800100ca1380303d041c1140c0c801190803d40100c0c10303140d07408010501031043d0300035545240080c110701d051b03059000c541c072450040034030401e100c00a003004a0403030380041d80a0a443d118980070300c002024003954844d1640072307000100d2400100460044014402d441c8201146503072070030450303c0c00c82803100d181c0d08035400b0f0302c00ca0065035100390f25513040069007040b07070f200d10009a6645000107000702258400f61284210b151154010411511403005503038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 354449046 1250 354447796 354447811
    0x102030a080912030f0f0603060c040627090608070e06030c12031905030106030e19080f0f0c0a1106130b030705210a180f03120207140f0d1403 63
    0x103049403a80781c1038528103007440218007070f032003000810031002004d03200d191130103108525040700c0d541c1c4500302010748800f41103d041c41c2d808000d20042200c3c2e8403032200080e00c185140c51525940510100c000c0300c0d081660001040ba685a06040080680401203a002031038103102d08122410701c41d00281c4c48044040b42c81e8425183c207201c60640801c280100e0f038445440d41488400183c02c0c507400b80c5180c10910035980805e20382500050100000303d05a41c0c10b50701060341e110030359419590034000b90011961242421418401e81454021603002462a0358003840108000140f0b803814030703140342d6883c1d000ca0103004140820180d4148005008050b56032101c002130326661034000898440c001c80440003186d84141c0e600074500070781c401415024044184060084a40c64000138a80ca41e1428004000b24250700f95400840e100d008100030449616901500e089040d071106800007107006408001c45d00111100f0102020030407d4548918003800c003016042c1d4103240205040c08001c0604 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 354450296 1250 354449046 354449057
    0x17040b010b0714060906040b16050d110702060f0d0c17070c020102281b03031205091005090c0a0f0f03020d0609050625031e09020a180b0f0f0102030a 66
    0xc003c001c0c20382030800c03c803c9110300700d4aa40c45c0500d1810354403407080c2d4040d101e034210080445c069031404c0c080b0840f08541520b40c0340c5042c5440030250004c0024429031000c056007841088016a90b00c00202524200c660340b45454914183c010b1003100c448110042c00d01c03028070041c5022072040d101d203982c0520785050811240b1081d000603400c081d107a96a22500b1882c500b034100041c3c0100c0d01c1501024050040c0b0540000c60b48225290200c8a00005e00840d00d0300040011503103075034010946c0a406082698104910305046d2410f540094500101c036810840c0700c070484d4108910980c00030601d080d41880c0e200d2500c0d85090a40215010103401400c25644100c180242908041801e5074080200e610b80d2400104a909500002440c00060203140701e143c1201840b030301840111851201c80d000c28158841c040c0d60040c121040103d070051003c1c1c50001e00f0300042d801c9403606002024011071808240c400308420300b0645c95807c1d110703c0b103034034074540c80766030010a2701c00501b40da0820 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 354451546 1250 354450296 354450307
    0x7150302090d0c12030e1005120712090303060501020c0a050114090114030403080103170703211b02010c110106030b010b0306150414040f09050a08130504020c0102090117040b010b 79
    0x442c80031071402d5000340141c10601e50006041d04136004038400d40e03002c0d0350b420100080034004c0141c29078081c00d801c00007440034011501c0e007240101c0415000390060800145062905409400351446644203402195507400104560b50f0103110417070031220708403580d641d0700c2d0600c00080d11480160004200703c04020510711400e034043c14211807150400100ca50b1a440d046c0380061044d40e090100b207850800820405d4000342d0280140d84030550302d5107e00f03480501040c80401407400710300a0400260700c440c1d4490400c0000034080d034104902d6070011803c400c01040280c110b800c2d040035148103a250603020400b003006800f940c1e05450380090080e0380c0780c8845000904105a14402412a00c800100003e0004408181000c0326900f50bc09011004c00004e00104544041d078010303210380c004600c1e860005a00740010a0300055034018120829100c8004c54100d800c040303035050250b0360005020006603004200004003c0369004025164035155803401660f400c18441c3c90000000801c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 354452796 1250 354451546 354451549
    0x1e0807080c070507081612051c1e170702071d060123090a050d030c02010806060c0106080c51070f1401021801050c15070518030715030209 61
    0x22100c44a030824100c1d01041e45451140f500c40700381080407a800c0c50388400001c7c90514804850f81e00c0ea401074080d0214003100d02030900b0907040d121030300080141129603200c1c00310106040203018101a552000402020101001c8103e0040c00443c00c0d50b00ca1a41000302c000140c000c0300d275880302c0c86a02c40c500d0310381c1c00c0107949031340300e004c222001410b6203034603060100e481e24041c001030389080350402c000c00d40d00d80c03d00140b4194035201400080300c284003100035500a64440e17030004400343c01c0b64508900000f0242c00c591094000c00e0264221074401c03100c07841c020309507039004566000282c40b1001c00c1c101222480301c03d40707044409414501d180038840b045070040c100c0320035010b400340755a03a000361401200c82100c5007002c45500e076403140b4090958005100707a8103460040c2c1d8101006030065001551103402c81c00d01a01d092182d81c02d030904440d1500c0c04ad900a5150b6201c071030700c41c0d4450b0a40600da04d401c0c070307596000b035001000400890030081030000480307019040c0143d031508600b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 354454046 1250 354452796 354452821
    0x5100b0f041505060418060b070b0a15050a180f02091c0f211e08011404060305191e080306041a030111040503010e0307020d02090601110a030f1e080708 67
    0x1400a03a01010100340050720300041e01121b401301e01d80450401c441030311030034814058064010050440310100f00041c0d2090784070390160281d01d106605204640307681700e001503040b07069a001035040c0039000620550000e018060802a2407181c0c80550401105001289041490460104500010020381c1091160411503038054070b030044869241c0c2c3c807500d80c0c040308840c8001c0b40800040c0c2c00d00d41c2da0703039440a04900a00c24503407030381c1e855619918001140e81c903040035960103540690f603110000002a130410420308007070700c07020b05c0d004d00c40d61900b010940c2c184400404200222204121000165010110390307000300201e40006402803019114003034200421180c43d00f561030b180c403140c00e004c200e6000d0b01c11610100d0080c81340e0305100324041c0e12070140880094100e1507540e000001403424414107603000f8410700d012807441c20b5180c03065140c0202c1c0402036012444050b21281280d43c0030b01d500c0a01c20581c840d060340041850801000340750002d000e0010010150041407607030001d171 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 354455296 1250 354454046 354454049
    0x70f060210200a1106040308041208070206150432090304030f0813030f0c15090e16050c0a060b030c0f060703031d0a0302070905010905100b07050111030c0705100b0f0415 75
    0x8001c41c0e6483c6818900681808000d0390240c542c40e00d1800da210045100322920cd104d42d0a540c013a28241d2551000c4c01c4102c034074001d00d5075100c0e0700c84204c000c00799000105429024440c000c2140d072080d10305150b00c02d020303000c0c19804080d0000c200a1001c191440b440d861926440100590366505120a65081c0740d480e42004204101b0142c40c80244418410424150b440040780915008841c1109580020652080d844c50b1218003000814094214006d4400c45205003401c034030b018000e000c83ca09214010b08100d8640c1d58a04080c400380c201002136264100080c2c5078101c3d05649200060a140038003900242090b88a42e010030266040c14001581008084100d58000076940b4000e505c900700c40c003a00c107009203000000140b06406000756030040081c00d80b00680d09007080040d0196610205080c0d505640351000d8050052f481c00007035215027568074400b0b460701304502d0403d05000000998100d41d0381040d555040598990039041c8081001701d50025007100141000481d05815 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 354456546 1250 354455296 354455327
    0x50a120509030a0807110d0c02190608150d030507150e0d050702030105060d02060a08071803110103050f10090b04090501020a180b040b2505070f060210200a 69
    0x10031003884003030100000070300915038031500e40e440c0c01d54480070101e554060310510500e0780e612401210744581d006d00e140800072800640842e80c900082c0e40c03040c3c0030002d2030b800800091104402c0207000920410103040904040783c02e51300e4020940c40003403981c003d252000d040d0058110200140c07181c1640a18081003440f4140ca40c484101500034009405c40c11f020303030095080c038001031840d20302140c103050010f600078541c0c0c0c01c11a14103030480e44000300529a10901141189050546070150b2984000390300c00d56155041c445104001020384101a00250709941c200c020b200180c296603c2d000d00360b610307c00c80050324142c200c0010700a840500b4026000f94400641d86000070b031703c111101841100c00c44001a22a070368210626180b040d4443d0413a40380080c40f680a40d40044507001907140041d0040c0844101a900d442c0e0a050595012140d0300c424107004121264041c071440402c04002030040115160b84952600141c60045140d141352000080078004e031401500703503a01d490344 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 354457796 1250 354456546 354456551
    0x4210210110901180302150a09080a0f0c080105330411040e0705040612020306040e0610140604060e282702030403020a0323070317011403060106050a12 67
    0x203121440c650ba0300400b0b642d400169580d421040c10350982c00c04200310ba41c09407500b07986040015010942e600600d1103c1c0030408401c0340019a00000c02280040d01d0040040c090209000d1910040c4a517140c0c0c01b40f4031310b034102020031400c541c3d10141200c08405a000340204080160070019402c204201c08aa0142c600401c6408251160015000380d9800300c00808054460b6481a92607004071720640000411221354100c0d0b000381a00950b41008000d40041103200d549040541070840c12a203c1810300c0005204200d40d80001000d4503400009645142ca09801c0042c01007402c10490034076402034042102c0303558800d6000d10b005900707c595010380c0942e503032202810071103040f4070011540b029948400711081c1c03016500c2124003480e0b1680003821004e10a640a44049032051010b00c0403200b1480c0a80c0e14908030350040c0040c920954480c504059070781d6400110071010f801521a11002c204400019140062420305442003402d0139519040d4211003168070180d040d020039601d90 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 354459046 1250 354457796 354457811
    0x803040803030103050c0a4a090607030c0906050c15071d0a0b03010e0709090f0624050a18050301110309010f0b060301050112020c01060807050a0e04210210 69
    0x384040059410389110b901680c03501a000d500708800b44c03c0d03600403d40c0d1020000741086241003208210000200340c50000b5000d030703130f03034a0045640407252031802004042071020004035400074040304c0e91284103402c04100d501c4102100034040700c1c641c01407034144400003c0400f04104108402c12414240042030b10940c5000f42c001080240b10810900d200080456800c01d58a010070700b040c16500003070041e41c203503880c0201c400c50241020303042500f80009080042510b83c018002e01c5000040a00c0100740d49141081c107566800714071115511208403182c6041400340d010b0704489441d5882d00c0e0142d5124800710300d610310040c20354406541986002c0c2842ca03519069005984074044001c020051400c2010141041d40c46a42d080e540c400e40400c0103210a41c06074003640c60342400003200608002c0c42c200300b5400c4a500c0d4020358070301d5119a504000c540340220500000e4803d212010100e800c1560710304000b0142c64240e4001125030b0300c82400d819100b000720b80c00304031074608180300c2031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 354460296 1250 354459046 354459059
    0x180507021009030203041a36062503050c0c04110d050907080715080903190807030b0603040c030606081614060c0d031a030d0c0b04030c0b04062703080f04030504080304 74
    0x3c1e440124007000d590000d09030007044400580350080101010723105100c0c41c11908042140c20780c001a4420340d41e901403807600707001e0040c00080c004002d101c0e03194969510080c55407030b0320b406141d0405500c680d00344003c2e8004540e100c415103050240c10325002c9015282e003030380c030703410560305401560291040c007100240c05d001016182c8041d101c182c9540d0700300c0d00ea588035036450344107002d00550f03608240300e403080c01588910784007948280f0a140006892200d60006030302680b043c0c40c290b5040c0030009091090054502c1004002c00482e8010580400e480780c001c050080140300b111440080c9800a15250300c4000817a400d0860400c240e400b0800c1c0c800004c0c006003503141090702403180d804103405640c03c0000c0c8142d400a41e54903802c034bc1e14525540d04081c000000c104504010740d190050002403861070034035000b0340c81148081080000050803011502c0100c2603200e607408884204404603400040c2180c002c12401c07082c0282c3da5980c18240c1c0ca51040342d0018030076100c001000582d2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 354461546 1250 354460296 354460349
    0x51e040302010516080402060702090702010b041a0a0815010306020d020f0f07030e3a020312030a0c140a110a020909070f08030711010c051c080118050702100903020304 74
    0x1d41c04134000c0e144400c508000498109000301c4000b50844802c0055401628100020a9014502c1c0c4008200c0d00003540108042d2148100b20303001d00d20321040151483d2134032a00480107480c4403001000000c00c22018850144010b100c00741040340d00003103040078500300741c04852120f41c2500c3d00582e22a689032150304581d01c184c0d42034000801408c01040b2510381008030421820071349a80762480c800d180c00d420b00c101c04110761341010a8242a0100050b2002e00c0002ca070200c83c0303280e080d100d241c00309202c025503a100400c1000c0042d00c0e40c944150b102c000007652902000d9140500c02c048507075003c0792400000600c081e5222508004000e05001c00095004c01ea590640091039100d40c0c41e00c40540d01d004201c001056403d9024000e96254807821070762125901400031038107080400e6000c401204549a5000c0019008800522030300950301010486600c04a030104a14079022400030b4503502100000201c1a03115070780d0300249482002500c02403d005980e80c000e22115187c1c4034907 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 354462796 1250 354461546 354461551
    0x50306031005010515160f060e0d0f0c063815090303030103060e0304180c0f0219060506010c05030f0a18060914011101050f04050106140f04051e0403020105 69
    0xc2031081d8903155504007158003549049500140c00345880654442141100d5041400d210b0700b0030f8240d0000d44081900e45140b02c0c14a4010038001800c0e44080c1d01280c200300340b5031500340900006284a0a0003548640440728a81d00a180003030700480381c0c1162105c076100780d9008080001c10000360940781c4c100c1c20301e81c841081d007115003d00100600c440543d66000f050481507242c0c01c11300040000c124903400840841c240300303055902c1d05840c0d00340c501d180111102c9514030142d8908624541d00d42045010f400082c0c00d0004140746076145101d40062424014028011611140425a640d000c0c48040001a500c0020b590716014902c02c0c1e1402d640000000d0f000298440e9100300c074403459610400183c80641d540c200906003010b6000e0113042202c0c204c981003040c41944109010800e204050090b210300c60306403158109070078050709440c800d0300b00240110800109160941c1c0c0c141e882002620281c40208107607855801e04a80c10702c0710701c00403844000460400c010181c0c190301051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 354464046 1250 354462796 354462799
    0x4180b03011e05060f060d0b03011803090e07051c0b0111030d02121e010303050f070b0103120f05030903120603010b04022209021e130819031d01021e0a080a050306 72
    0x4251344200c10410915900c40c03109800c0340040110090545040e0090144100050f0020601411600d500b4400c012607001c01c4d00011034405003404a00c41601e030180d00b0685524001307040142112a244001000301140840305507074011411581c1d0040309402c84c9508108240c030384a402506100c00698048400507002c0c561840000e2484405013181d900661502c1c1404281c90b0b0071741e030f0103840c0e82d4414604013202003800c0c090600040c0006200c1c602035480791005081103030b040c90014040088282040c410300c41c050040001840000081c1e8405100401d0314040540300d80c00402c0c01042114001e40d08a400007651a41010001d034140070183d000405402c0d07030580d0760b001c4004034018001d8640034607035036400b109800324100001c1c3c400103014500710310006503074021151601c2d04404e082242c0c44401e0f1045c80600da04041000e50740d41e941001c185808580e480002c1d03e8000042d0400c0c1020182030790039100700070030011402480d40c4540300c0355462200c0140030700503030401c88100e03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 354465296 1250 354464046 354464051
    0xa0f030b120a051005041e151b0809010504030203190e060406020303061f021906150905070f0806030c060c070f0e06041d0607050c0a06180c08060106020304180b03011e 74
    0x40c020721042e441558804c0347c1100c444261107080d04040320614a04c0c0300140ea203410041da848501005c03a20441c02d8080040e940c005c52500752275000381201400801844159240c1000c01002c00e8022080342c10f00c0c1d03110300e4107100150000d001542c038890400c80c1150040e601180109202e0340000c001c5000d101d003220034044402242008104041c6d100d04400c0068200355100d0800c3d101d0041c49040880c81020040b54013108040d0b50340c080e1702a035200c140f02c90303120805d1000e5907400016883c04000c5502c0c1c014004d10b844e00100355940009800103001e2800010035402006082c040c034800b0704403550032400440d07641d80200504480a45520788030700d140c2090912080f40120540c040121000041c01c0f5a030f40c0c1042c107a03095000400b141e40e0760f0240c607200c4000103c107441203800e1000c4d50480701100c00303000d040428403090141c22008155111500501c0182c0d00002554201e50502ca4810b40404015600c00050480e42001c1505582403122070318000e403207803c07912003504541004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 354466546 1250 354465296 354465313
    0xc0312100b0a0f0e010e190609091401260304060801080705090f0f1f0305070315050403080a0e0c04050c03040302010e03090a05010e030102041a0c150403050a0f030b120a05 76
    0x40e44030700c1116207200c007040442449003045806240d098907480e005040c00b064056400c1b011400c41c4040c0c8a1009180c0807040c000d0010540004015014203082c0b00d00b00407421150039180c4050106000d20f24480240e007400a540e6105041e1884800c43c9210a4a480b2a5204030140c003030780f400e000b1028075000e60180400c2500b4801c0b0712070320400c03491060f002141c84002140f80d80407805000b04105e402d01141c00036440c0c7c01a02c40f0801584148000c102483c030f141001c229851499402c0c06280b41880d09205c0801d5100403103680207440c0e05e4000441c00110304420385400950904180c02c1418401001210038a40018510031400f83c2c0080c008222240040c60301c80c800d0b034000d80d80c01518a90148255403062600c1580349501600051034680c4038410290403092410010100c40b1000074034101c2d5400c1401140d0100c840383c0303589420740c205550064210b015500d000c00410000b01e4298030060710942006042c0d03100981061440d106c61002a500e41c07100300001c1e85c092180040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 354467796 1250 354466546 354466559
    0x4050c0708210903191d0303040b0406020610080309130603151a0102060126010908130312030b030330150a06020c03060604150902040902130b07020112020a050c031210 74
    0x1c44840317400440740b40800100c0f806080d6200c0041109804050000550000c450f4408000601c0a04a800030b0591140e180c403c00a10700000240180050340b481e450801c91904000299850884100d407401202c04034252840014580c41d071003d00391030041001c1d45a00b080e142d112280080c006000c40203524402001a42d4a040070301c00d002165a0308550315000c51620600106010340d0300d000440d000c0c0d6241c0b141c9516400076410030342c0c8030006510410421a544403807001202541c02c0510200c8d03150800070b9101c4c011600316030203034200c600018074544103020b507105403880c2503e00d5005c43e040003100d17060b43e5140300c05080d0246100300f50202e0182c2c000140120305401c024010541503a480080c0006440c07458041e020300100c1c200b001c142014940094409031041d9a001030f10745100c0c0c071402e2915102a071040c00c40160401010700941d0707000e84c90480d52000c1440160341d07001e804204072000e102d0343c101042c4501002c00c01d200342480b07031807116000300180280103160b146c45d2103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 354469046 1250 354467796 354467803
    0x30d0b0a140a05010e060d0203090c101d0d03050c060405151503030403020f0f21010507090b0d0c05130b040321021c140307081803040602030904050c07082109 70
    0x49010b07520107403002007000250310a80110a0009018103028141100605100144d170025642455180c10046564000e07007032000d02000081c0680c5418000c0c0085820715241444029650f54020340340d2203240f10516001380c00315211085200d04031440d501e4141441500c8003d0840d15038048206000801e502044101e9401e4006d10010091817500e0b295a003040b807013007885000642c000c12001c0420070140c0d40d100c684110044071140090341140302c08051800c4400c02020756081c4606040140800360300542a1200300d9000b600c0019104a140d000b501c19005000440c0303000400a070000c201000c0b0107000d002220710544183c4125488002c44040300260101242d0041e448502c500d03c3d5140f03941190b942080081c1040d400c030840b21886010a1750044981401240c030030001d0118a03c0c400b54800c00c006003020186041c2070170a50025101d1141e83c00c014400c60311180465000c2e505802180c070322a600001695580784107045010620780098019448803078004002501e004011 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 354470296 1250 354469046 354469079
    0x10207200102070521120c1207110303040803040608060d030f080a0912030b0414010e0606031315050609090708070b1c0e01140a05070905120307020d081902070503030d050c0c030d0b0a 81
    0x11409031110b80c0007207454035203941041e90700790f810ad030303c40320600083d49042c00200050011000507542e00c508105014010101c007610382c90040585180c9000070030b0344046283c3e80300e241c910701034009440326a2450058000c10b0000741501020b040107900181cac01d903000029a50090724284501d40f1101c6043d5170b802030074460b00c80020840e000090461814500a603803002c4a80e0100300504115154903421000c007000b41020941d80e00c05001d10f03440c00d54801640a81100c001345646810501c07040d441e84003910074020760400105400c40107054a030303080c0c0d407a00e200030000c00c042ea8609007441e01030305c503050b441100d040c800d4006c01e00d0044da070f0103054031891091300c4506002c1d1602003405001008031078109002c2c001400404016524500351760700881c00b42d505030340c8a00d054803202a1500d500c90b040800d55021203010070150310040161031200280400005059484210000c958810740a440f8901d010008041d81c4c00c11443c3c0c0091144c02055440303200d03403a1699900d10019002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 354471546 1250 354470296 354470317
    0xf020c100810080604230f0102040905040201030f0c02100c0e04111905161e0602070c080606060909040b040501110703050c0705010e1e031204030c090b0301020720010207052112 78
    0x740c0c0480c100c84441b03050108000c010b074004170b900c0c0030041c0c0891401ca800c039130400d0091984a00520040d0360345400782e0300301059030b5281003201d820400c01c082d6580085010394010162a4012174200e58000e00c12241c1c1c0c0b2070050410710040203280d101c07800750f6003c03a94803a002082406075102c4188114161110301c2c1200c00140c1a04940d0380b11090000c81e24007286c4a00c403110300c4040005120f9001600b405840b815110b00d00e1805d007000c1c5800c084005102a006007000e002d0306117540c1e40c808c50642c210760001d1302d200300c6888030700b030090140902c0c003a580d0b243c082c0050001d04141c0c0c002c00921290b42501c0c1076948043d1903000440f00c40114000d17a03640242c2101000b41ea24242c914200382c0050010112124410003070a4000c9581003a4030558000c0043c10082001600c280a14881d05174128000c61a048880e5283c0d000e0045611342106c1c0300c00d014601c804245d000304a058003401c001040203000c12074000388000c08110402c9000c019000d031002d6103510362548070688030705101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 354472796 1250 354471546 354471563
    0x204110f1207020c0904170721021b0307031e1403031f0e06042d020c10181202010e03030f1e07051905040504060603050105100e0a060f020c100810080604 68
    0xe0315107800741d0708001000700180703011f800c0050600003048401c0190120401c400c41d07010102c10440040c3c10300c1500707a82c0c0a45036191300b503d0141c2d41c0d40801c1c01c0080d2540280c4a030170548103015450a80024444010b10b201a800c0c1c1118013901d0002c09141f24820760144542c4403c1e525401ca400e0340d54901c210042402c0d60340c04a03040c0e10341500001043c242502800300405841020441c2e041c070700c00c42010f2910b03800500d000342558248040c0d80c4001312110180b010030500031a4588100303d6181c05030010591040da28112131003900140c0a40d40004200c9441e414040304c030055102044d103162211b10300d80b001807000d403002500d14511400c66030b254103042c074103110301d00542444010b02600810108001c041655525449a00c001d405150303000561581028144010449110303c001c091040700c14481d04107543e404851815540c0700d03d40400b03642d414400c183d2030704802288050f481481620940d00e41588803441d2441001c007003044110340c65035086c4071612044241c802502e0b404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 354474046 1250 354472796 354472801
    0xa060921050303040204050a140f0106031d0712030909050c0909061e0103051806010306090c0e16030c0c020d0501090309050103090503040e1305160602060601030b030c04090204110f1207020c09 85
    0x81c2c1907008236806040d80c0340204419080414031401c86804450100c01106038100500020f603062203000c034091500c03241e14520420b0008541e640e60340074841d05175441e0703001c001d075001c251182d1400c00c020440d1102c08d00090620009140203500300340003117801a070a44000548618002600900c181d2002101c0c01c080400d05004602500300100403402e070340d44041403482c1925040240764000d601860000030402503c0c0341041e04c0107141d500c18101c03110400140514500c102c00300d00d540d002d0078280003801e5100c000b81074409030004075019502c5500b0103a070f0400d014040d0060b0498510030f658440d04681c6810041d400c440350403070080e240341e006001c00e1150345299020650031084038100180101040e58500d4907001a26103070740000c01046204200c1140c0422485401c400c090800384170700b100480201e5034403820904c80d14840d039240c0c0262000e64556602c94136581c60006940340ea500d0b005030f196000c2c1d84c00500141c1001401900003003540d4804980c40103282001442903e141c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 354475296 1250 354474046 354474049
    0x305011815080a05060f0f01080316050118111305100b0c030d0e100c020a2f03030f2203080f0c0c09010f0e0a060b04060f020c0a0609210503030402 65
    0x914105044090706500c075040400c466404103c5502a18400c500034582c51400c00c981d07031001100a8010301c568505080103211540012003034800318035103000c1d0500c0364a100e052003405040228400c02104c190702001c1424000b440c0e452143c50041074944050a0030ba10b41088200d400c22600985403501c00f25052010b2050780c1d0040c0750400c40281240e003001e29455100c400c0303400a41c0c107452079a116000c0000b40d061f031802560860445800505aa6205d58503818583c0c540c004160092003070b0048a4204240308c00d03001400703a800036003280d44601c0740c03840c019103d520030310404115101d0328010300010002c81a141d0181c0781d00103185403c00c1c044000f034070660741142c0710300405030081501c004400d40300e0724071841c000c004e402a0395519601d0a60714003040070000d401482d825080020a1041990050484040302c1580c80d00102d0b514140c64100c0c1040b1850384c010b40d00900c1e514000070071036407160f00d5070146e0300d00604201aa08420800d1001d2039202c02c4000c110b50824030025026 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 354476546 1250 354475296 354475301
    0x803070507082109013c2405031b030d0e030114010303091d0c07020108132a0b03071d0105040b07060c11030703170a0906020a03140c070201091406040b1201060f03050118 75
    0xb40341e104280450703407e05110710b40010000020140c2100d86100b00100403504e020401580e441080c00d11903031100c81c0c640040398603100b060041d03a09000f00c458051056840950291030325040ea00400c200c6940c40340350081030080144100242000350021182c003020401000c0c501030003800410914107181707540113440d01030000f0b180d000e02c0d15411580b2008120781307071488048101f014100018a007075a880c05201e078080e40e0043e6030120340500401040344e4100f0348056510356094001100c1a90200c0101c1e1070780300c0c80c0c104001c1c0100108008080182030b0300031110102c402c1d11030445182100d20301950764001c1200c00b80c0081c0f0788250b4403001e0710110380e81d03a4026040001c0400d10300500d03110700c000d903800304465000080d500c030745a5005490203505207410445a1111360b00e010303600d400080170f041580c080c40402c503e83d21044100c40c1c5e51101168014400105002d44582e280782d069041080240f107031002040324070120079056442480f03140c4c180c551601c40c04c80c03420030540c5407900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 354477796 1250 354476546 354476651
    0x2010b210106080307050f070b0a120b04020d09060e01110304020d060209060d0614010e0604050a050f0d0c0609030b0108030f04120302100e0102070c12080307050708210901 76
    0x25907550300c0d2008510020188018900759000710000d0005207002441b1515000066012585900042c0180c89243c0e80c400e10110810050700c50202d0344041300b200040080c817485021210300d0386451070a0b170800c0480c2e081070031900355003c000c1005110400c0215410720089600070f41c000d010110907400928198040c040a140161003079042203031140c440c85c22103030380c3d403c505503a155a41d550384c2035690140040380310740d100740d56860030320340f500c0b0100d0010000340c010540316502100c0080404d0320307061041841e194010462582d0342e640e615000d000000280010307141280c0c550b00101c0e03886800802c9442c4035544000d8103140624104028030002c0c81d641e41101140541284004000603500600c46d6402c60000010380d682110b00d0050380ca0921036010081d6000b041030700001240904041c1c82d40021507040c00c0781e603614a890100d40d54411500300e8900c149004514100114188402c28826101ca200811440116200d010241800d904a840b88074514006081908505455189 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 354479046 1250 354477796 354477859
    0x501060b0a390c08010c020a211211030f0708090a0210020f01050c031f0b0a0e0d0c0e010303141206150d0e06060a060c050604032001020703120c02010b 67
    0x800e12030465250440c0c4405141c007a680d20078a02418413101d0800c0c4031b040c542503c82d0000307220b40201e41d0b03542d02d1280f072007803091941482c560011901c480e0103481c0f004150100918104840142c0810148040d0026501408600034000008440c24000e00740c00e4007800f0200c00410909810398200121000c0200e042c40840c040c1c288010205a000d0080600444040d0206500c0e850510704102d400d400c1c404100505005a000421190200c80103c4d00449407a02d000016640c2c200d001c200301c40320b110002032010215000000d4428005003540e41602d12035960700000c50744804085e8054004c1080c62001c2001c440082845440e2030141800340894458210313003845040c0c141c0b4011110300b0403100b2426007140c81002501c1c038081c0440400380c00e41c0d007010210780d4942c1c0c48040e41c81c500288004c0a01a919080481d01002070707086d42c6001d28108002c1d541e5108034500280031118001d00e400c581400c15a920b83c007940107000e1841c000e000500000704241c7c5464402503036a07910342051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 354480296 1250 354479046 354479117
    0x20f040302041803030c09030b010330050d06091a121e06150a0b0a0e0301021902030d1505060906070f0212030a11161205150a090501060b0a 62
    0x3005803218082c500074030f1503640c00c41541016a082c0038003541c5c000110078081005040051001a4401d0701032030540780c000b500c0d81c03c5502003608070303428103440140030094a107044110010099100c402072044403a0402d0070f11121350303174483d00c9080d51312211801c8042600094031074910308007260042c9540c840042140d26000342d00c91115840b03150210150160b400800801810400d0440000c2004a0590708000400c0c50f00364404a24001c0003200703010414908003524165809405492080c00034900d0503e84c402d40c1c0902942d6a440040000b421038203107400e034886060204562001c40d00041c1c42e0900e0100c291040025a500072603049401c540f60401400140c1c030340e641c0e81004005200d00a60b030f11511440c000d000e9031040c4030080400c0c0d00810b144d10b58105200c940908440104010700740c1c1c00442e01d0a54241345662070000898000c081c10000d151300035400c00c80150b4020030082142980752424202144210314a50340800c8002461320f80590300c810809040840501c0704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 354481546 1250 354480296 354480299
    0x2180405210c120a35011508070c05070b090406030c1d09010605220e060901060906080a0b072d0c06050a090b04021302090a08030d230604020f04 64
    0xc00140442842902001540814504220481084801d4801d903001c80030900f0416001c0000b003c841c00517129004450098044007558140c1c071964014107207502c203500b1455030315501b10b50860a424980000091001d00c04900740c280620a58800c3e0b80e00702e07019080150034030500d0381040d031081401da034009940303040000c0070486c42d07100300001d8500643c4d40c2003041480c245005140700040c1001c41c0c2a450420104a140d030b425601980344a01000c800310203058011180c8000c9c9841d1400309094001e1b002042002c110642c042e20039500015000c10040c1e454401c0c103555006601c2000702000c642002141d440f9005000c10b034040b04c201488075001c01800c809992030b2198000c4007801007010f141c3c404041112074002c180d4420720340c0600304080b06060700c50803403803440940064010320180304140309080d02e9070100e03002100003510324800556900d82195076580031504011416103046841c04016042045c80018408908204032094440400700002503120540032000c3d540b04000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 354482796 1250 354481546 354481573
    0x11030a061109040b0a080c10030e06070c024902060f180907080a24120b0a050c1c0902090106170108011107030e0f030a0813080a02180405 61
    0xd6000c0a102103103080b92a4030082e410f02c004d5030303150002c15204005a440c02d000000e0b00040d00e000c2403100301c4545001c140e90400c185c0050216611b049043d01640c401c00c0049030300300c00420100c520030b55000719a40036240103070f0456250644560107414000b16204c04c109100000c1c11003054203180451013401c1203074000b50301548101d0701c41001030701c08916010030f01d60107100110707041011f4495809a03d4442e42c0180003510050004164950f42e0702c01202da01c1300b000341c90b21242110505000c00c0c5407280680c008440380c900c0100c0c2c25189039000542e000e0107034020640642101181203040031070125504c03000c1b100700c140550869980d03c0c1e0000169403074030041402046a602e400c0201240c0c20006003000505800038811a8108100600e20081e0304044410594151800c0710503060003c000808000c1b40f805550b90603c2007081d84020301c0610310040c10b540d80c0d50ba6280e10b1081d40d1b505c3c2c1646440d07440501a6002442c100c0d41585075100411582e401032141d070959482c00000d81 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 354484046 1250 354482796 354482801
    0x1506041a240c07090b030d0504090c09090f060e090307020108040f061401092f04060509031c05030709080c010f0f1e180f0e040206071505040506060405011401020a11030a06 76
    0x15210616408140100068540c500c50117001c607034190302501280190307070000b8205108038032444644550321450100c07854031820651010384402041481500c0c0f403003c3c17000103040c2c50300541c1c0c1c04840910100e800094004229085580c0c183c4032501d207507441d5191841541c01144c2c05881032500d55071019030105004051502800b9402400100384803d0b000c5501510303404c1c40401d0183c080c80031612103030007084040d030301103c08500c0d20341d5031076004c0d201207420114440e41c00b1b04205008208406100c1d00540a50b2080c18503603a5044a00da4602007150340c2e00c0c0c042c10090104007141261030380d00e48164080c3e8190001404d1450401403042c1c4007401c3c43e01800801000201d00c02030f0717507000800c030220000003440300c2000101107605061140300b0000c0d028200920546002070181c1c1048601c43c0c50301c000080c2d440013084103181c1401c00b140c13150801c0764002d11492a120010a0380c020304001e070901210181d000306004104c40d45d44038210844400e5440e03051003040d40c17110001c0d2050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 354485296 1250 354484046 354484057
    0x180f030307031e330b03010906031a070507060902010c020907090504111305190e040f060b040e0d0c02010e220b0f030a0b07030b0409051506041a24 65
    0x10b6038005003021012001c403d003801d20982c0042c1d044d04160550f01e14a405016040840500c0c0144401c0c1401c3c3c042481504038142e4048003044038040000101c03105264000c10880b401900d80c41d00e07100c010003011182c024101c40d5580460301c18401c3c800882e80c0b0b40c1c014442c0b40c3c41030400b2041c402c0160005000400c0c120307440da0024440410900c1141003c0c0503080e54031403003401c4181000081c47e6142c103050201d0043c940030303c003a02e10001040080b80b6a240041c0455040101c00c1d08243c28110034030030040e0700c25112682023a4403508141020700c126020840581c0c05001003240800d0101c071515900700007641008503102582025036160011264444c1c0d0604034010ac48440204407000e8072308c5035101600c500d0003e9441e28440e1400325025429070b41c88150b075501030340c1e40381081c0c0007031400440680d04185003074200400c2000000700c1e14026038242c600d5592690755842007200341c420301c1195040540101c8040318007814606c0645050900c0c260448880314201035010417030340c004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 354486546 1250 354485296 354485311
    0x1030209060712030e010204050a0b1309290d080928060c050708010c0509150c011104030302160b09040e07030203060a06060906020f0d0e030c0a181103010e180f0303 73
    0x5007074240f007100c0d01446078001c5002c40c1d90095062920746000a0840503103485000854100041c000c003001820810381406041421070420840c01c00c03900d4403403d043c2021001e000341c5801441d1404900d044034051030a40e501480c0c0f249004010310600c881d0310f1380490004c0d01c01c085000c00307900d070f42c03455080c0d00040c0c009a078880402d0300140c2815071810119600003410390745054491100e480d40031088401d100c2068030a00c1c4048441c0e91400c0c0c2502c1802c01741c949551030202c5c909c1300c000440000f441200c0c065403c81e0f840c4080d641c4508003040d4648a5504815000c015241e400d003000c0d080070064480316001c0c0d402d01e40d500e8020900b4504201c5031080004d50340c0c001400302c0c0e0f0b000102a00604401c1c0300401c440a207103801640c1e40d2040104107002d00402e08003031065a5002c2203913600c03560026161300e6030a50b0f945201381c1818240c00e9007080f080d0824000280f1590300c0c9040e64126490b002e9422507603224607120140b4451191000001c50041c42d6090b5442d08042005500032480d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 354487796 1250 354486546 354486563
    0xe0307050a05010b190e01170a05161505130303110f0615040c0f0512060d0f0b070f0507080904020c01020f0f0406080f04080d050c1615050601030902030607050702010302090607 78
    0x1100c00400604c141700203003c0c40d003101d800c1c40030b05c520b481c11100d85045d90503a0b40256048140303508038929120829100402500c1020380340011000d08200c15000c070350032140034203824046028150740c14000c111410300200003001c02000400d00c110065203151403036030b0503212031322801b034a0790303081030012120080782840c64000003020341003900c10b129901c03015140c150030b8508420401801449105c040200310070103240818640d030b82d03816100145c1644241500b0a0300c40c1441c00d4000c002003120f402c2c01040e041a5143c1c801c3c0e00460031610000d03808a443c61400000008000082d049060b21030002d65080c0082070801003110300601d01003007208061038a451800c0c400410081004200c84584030021007403200080c114010b0300c0800049940125003640e4040c0c0d01d00f041d01542800450228040401760280002c0d211213039141c1d0085201880f031035444a0066095810784000290581c0c0048000346540c1d202d84007400c107491051502600d003010b4200001c05c03d422001003954540c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 354489046 1250 354487796 354487811
    0x5010302100e120d0c11010806011706031515040506041e1508070b130501021f051506190e0906030618010213031103100e19110406030506040b1807090e0307050a0501 73
    0x982c00e08168206c0074a080b142900e0508002040f042c41e016803401e145456802090a03a9003d01824000100b0711801a140c4c2c0b0b17045115400a034031140b82d250180b481c1502040540c00c25006000e458044031040408500b25903800c00c0040a0724410b0705000c24502c400403469510170312001e0010984030020540b1406101c10091145105a10290556100350a030820320100c1412003461104200c00c00036a668880d118240490300510700b26500c0800011013a040680d80100810241003545d203201010140c2d6003400300c409001d13121181c4c035500c0100003800003007501001c8445214044000760400d419aa4035140300e0449070000c6502500d2800f944446e42000c0003034110004d0b07245400c1c02615120100c190712a0b081e4101800801c012080500501041d01c00d480000300c030107001005240d07560304005031110340a482c1120300e500c400c000300d030f2960003c00342120707000416409840580d103031020400040c44002d0707141400d40418424034000c20400e0020b481c074140140c00124010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 354490296 1250 354489046 354489053
    0xc0a0204050c0423010f05070201020c180a0c08060f1c15140a0510030602090604170703030306060c030203090108150423010609060c020f0d020d08040302011205010302100e120d0c 79
    0x70f541d007928021840c04d10400c100d0ba07020b180c2c403044e5501ca0401558400440c00102d007854a440b03016500031020880050310b903252240030520850202d03004005008203075404590f00e060560b00c0d285d000c0401c4200003030503d0b0070410040c24071a07103c400c1414044554a01e0300d003105000e68861040e94a03054048441d004580d9558855054071040040c3d18006050541e038103d58080503140d1a80071580740d05a440d481c1c1110090050315000100000c9841c000e0f980d20202408210006820140d0005105008a110100940d0b158014504000c3d01c07d004551080c0d00a28040107480690302000c1d454941d0311400c1c400741500300600300800021102025566010b034030039410089214402c010050323210706c1c24481540d04440c444411464000007501c1051103000c06540030700b041d4a1030080241420080c42220310070f8985140b403003940c40c0105c0460300241300181d080320894041040042c42400001c0800780000e00508400640c041d41e6032401950100141c0400d11404442c41803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 354491546 1250 354490296 354490319
    0x109021306080906040b150d0807060b0f01090e060a030204020f03040303060510050d0b030709060b030103060c05030f060607022d030c062a03040308120103150e120c0a0204050c04 79
    0x790a07541001005402d0503843d450f916100100041e10004e104000f00d401d00940080000b0b600740d005281281d5031803107041010b45a40500c02c1202c00e280740402a00ca1803c04500300c064158058550880302843c1c0b0082890141c0010320b180d41c024030805012005a982c2e1010780080781140340030507200e25062a015003103e1440d0007081c4110168140700c400c0c02da1000807100b1411820501081001d00c120100c0e1078101140c0003108a60700b4001c020032042001d0003d5070407640500f40900c00025620f80c140d23000e21090b501080241c00c0440000c089007400001403038081e00c041d01c45523045c80b00014540408407203d40703142c0c4144d06910314020b545810005205050012590305181815041d030307040038419428480088404030812070141050305006503401590007803001661849040c0c080000c001c02404215445c5105441c1d9001c08112445034100c10203003a0000c0c400d4100c0808407403c40d800c2900f42d80ca49220340d04598006032585d000302c600858021441e142c4560421141005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 354492796 1250 354491546 354491549
    0x50601030e0c0d03140a020d02100e030405040c020309090c0d0b03060603061609030807230f150a06050d05010609140403090b0a09080102120702430e01090213 70
    0x10036050802601d0381c4030300415607411040341140c40c040d5420452409032080240064441c6100901007180c500b40768010070003010301c0c107150f800d072408a00380d061031104503104100103555961040c801806242400c1d0300221002550f0300407a410000000001a40d000c0d00300c0d03606089881c08204011440420b01440300c103c501100070300070f03e02d44000425501e490003001c202080200c03002258420380501030b004040d54100f03040c6581c8003014280000004403034590115143c0101e060b654403d00007081220240c00c2d0800a44149603049502040540c0058604110b0302e6851100081d00d80e02c00003201c80243c86800042020741c07500c00203004a500c401884840418001c04000004e0b40c03188403c8162242d0303000040d01d8640d003201c111880150b64101c8200c643c800100e10700f030110009402d500c5030700103a089075400001410031244444840f094a0124140c0d04080581c44c1800b04441c400c500340c4d501340c003407803981d030311502101f40400b87e121850659000a00c03001400190344c1580 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 354494046 1250 354492796 354492799
    0x302070e1302360f060306010b0403021e0103230105030d0c0c0b07030c02090403021606180b070f0b010b031503070b030105120703020907090f080118030c0825060506 73
    0x40981ca8140c0208907121600440784074006003010700d5a008202e103000c001009003020045100514100c3c1c2c40c04000007040d110f80384030b8810f62000040c010780f01000c0300c0070f507176000c0c002a01600d80011221020360a8244040c1403544840e803020403001010900000c100b0380300041c0080754075240078142440b000080300300c100f10340844800042002e000040c42124415110260f0b00d009905084684d1103c0000095101c4642030038070041c15400145480004171840d03902e2403450b030322030003960000c442c01d0548201106080042180040314006080f010b40120803000496149030340d107a02016007608420440c030004000e10030401d9101169002c0030f0001e80c001c0c40700600f0561640f005000502c103c07407190301ca1114040b1000e8041c0107180055901038140b19090070486000390001c0e4003030060901c401450200020300070014050341e011610080001c002902540e21704640c04030345d240c0c2c290b03000b000402070350800704400c118154881b9240040e0340c011906030b103000000e80f5005041076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 354495296 1250 354494046 354494071
    0x6060807150c24050a050609060a060c020105070506010303051b0d05070204110904060b1b061501050c03130b07021005090901171609050405011b050409020d180302070e 74
    0x10711900d80326080448000d08641002c0307041121078030b01003a00843d0607100090700300826510014100803a0441800782200b2407040c0065550a820b004081b0b03400c462090348400e19001c100820382c041c0e03403940c0fa40e03030040c50b01c186844180e480e42450620281e004400192001179050f10a201c45042300154040c80e4000e4101c6000e4080003c11b240200c90004e84203c3e59480840b0080302c04404a404084000d00107204695031003020b40000d80020801600110a00c40001224840850288c2c440c5c0540002140380792800d80045801c3e4002d05010b0000d03101c1000290784a43d03000082000031309074074013800e03920005841841600c1281300e01d44414001e051000040c10303910b501c00c40c1d065520451070320340351050f803494051074500c412104505108090002107404c010135004680300fa0b0140b002807044440300d401c210000283d2003120700c0000c1c0141b0040c8120f00301c42d001491074096403503000c81c03c13041010709116038492251086025900ca440100181000e40f42e1003640040c3d001e100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 354496402 1106 354495296 354495299
    0x5031b0a0504110304060e0313081c080f060904050304051002030717040302060a050f07140d02060f060a03030c02060f041e08031602010804020a031e06060807 70
    0x10540586494900861039041c680102d030f24280e0325030400c1d07203560755a8990074020f0900503010803060104102c201100001d80c505030740038154260107080b0000003101116100410400c1e04c81c180101b01d400c0000c01051882055404501900d008020340c2c0d8500e0b1081c00c5120303a030491603000700c900041c2aa0a90300202500200c2e200b0619403079a1162800d20359440d00481c0320080d0301c004101301c3d041400d0303c05c0014245180b0a0310321a400d1540365655105200c40c00148040306a00c1101e03404003082d41041295080051114000250b0420030046281061280405400c6c03000b050b022404644402c811107480520f0205c6164542c0d88500c0401c8a02c00c0305080842c21006001000c281d041012040f0303aa000340d41c000c03400c0c0c2c06078070760f0041d1070750b050040c800e980c4600740c50000008154202645001c10310f01600740b804100480c030b050350440d04a03070842039190744103a00 = true := by decide +kernel

theorem cover : BRFrame.Cov 354316546 354496402 := by
  have h0 := BRFrame.cov_init 354316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 354316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 354316546 ≤ n) (h2 : n < 354496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
