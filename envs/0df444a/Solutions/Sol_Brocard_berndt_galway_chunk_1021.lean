-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1021
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:52:25.538629+00:00
-- url     : https://prove2.me/submissions/cbab6d77-e332-4364-92c0-1ab851f246f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 183453237 ≤ n < 183633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 183454487 1250 183453237 183453251
    0x9030c080a021f0f180f0b0309010506100f0c0c0e01090b0906100c17091005031006020c1e12010f0603031211090d0501020d0c1e032a03020c06010e1801 67
    0x10b0700030800450ba04e105182600d43c4000c481c2401042c800c1d00e920015201d11441404191404800d009600c190400002440252102e0701842520f00c0411481e100080c44500a141020311a00d0441950350054800a10319900c408207050515800e0b84072500c000c0d82d46007c1d40044c28a4601e09034405c1c011a04141c07400c408203000f9081c02c2e1100c40041040841540b101c0450b000303001138801c6d040015012441c1781c800540301902c154800d840300c1c0e50040c000c5c000091800d20004107005160341c00741100e04120201c0850a0100941c2c8600175444090040c003904200c0f024440d6081e0b940d840500420f9031451030402810300c0f80101380c02080e0a060240d11030341c0d840c949085440c806401d03150701c40109420b040090080c0125034060007003034103100e036041100d980090001e00013414550700f9151500788403420b40c202c03040400f51400502c009803044454070003000c00d48060a04905015107440f201c8250f06040031000d13009010601036120038030040c590400e184001078166040200030302 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 183455737 1250 183454487 183454549
    0xd090e0f07020c272802070503190201180305040f060207080c010e1927150312110106030b180d1d010e0904060b0102011b0801031209030c080a02 64
    0x5060b4801884c1c041c0206030300710796124414960781c1d000c0c0c410306020310101d41030240d1101c48602c035040b504210401401d02c09440250030b4421500b442d07134002c0c02189400d40e6000c0e080303116a0b021070400d056540c1c40900d465842c4103044400c2030380341710f130740d0301540e0300d0800c3c50500c2043d50030341060085500c406014007541c840000c80511900007401c180c00f5603010100000d040030350b1442c0d4031903a80e003070300c03000030740b00c1d000d070398903520070b4844c1401c1181403081d480d1044121640e24841040d010140d00c0f007080440c40611310031640c1c04642c604454801c0b1503050160a5407120307442100c100940004000c0e40c0311008500115495009000e403009401803400200300d2078001c03810249d41c0751146220000f50f80105180448500d006d04134510714501070074401d0003049e40c00c0c850b902650a0584042e41000d041040000e201c0c01c0c0c1d01e03030f4a0143d086464000d2460144e07040e010921204c10400300100b60303006030b030740300401e003020050542c03102c24818460400b68402c403928030b1350800c0c0000040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 183456987 1250 183455737 183455743
    0x7030c0804080d020f0c070515070b1f1203080a05010806010303050d0c1e08090610051e030f01020c071a070804060302070c090e0102040f0e010e06010f0e030d090e0f0702 75
    0x82e0040440c2e501d404050079110000c0c4940c0c1c50260080d24001551400c00501080740411110304130341e12150481c001041c0070303480c818498010030b8221203400144580341d610341000302411480c0014088980c880c070b0404200342000703605401041142c4200b03c1005140e0182c00c0c0501050300140565500d0b41d9005020740c0620000c2c420401d0701c0d600f816910600c10329030503038105808104a00d002c50300d82070140203400161510050750150000040031205034509210031104040c091002c8000160040e0481e0800020100da01d07004a0300300780210302090000d41040d6000b903020340a003600c0e00c24014a2003418101c1c440d8505401d201c1d41001c2408602030307404032809801c015a540d03000f840c0c40c1c80d00400c2c1d03805c01c4000a1038101d2080d24650150301405c1034174400b22001c0c0d02c0a44600c00306071103403000d102c1c01f00700e9024100001c07125482204032604810480c284810102840741c0024242002d9007280c0b00004d0040b60300300031290003458071a400991070810004a4141080001c0d2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 183458237 1250 183456987 183456991
    0x11010b1c02090a02180d0f020d0b04120c08090409031214010e160807080408070512040501030b030f030403030c030c12170606030702070e0c0c0609061b03010b0301060e04060503100b010807030c08 86
    0x100c540c110b01b680c0d00522581e00010071400780d000305203451403185807400c000c40707842c11385059416824042400c00c2d041d0040e00c00091258101605604201703041c01000050070882204038208081350080d00318900303c601402c00d4007032800140ca10300350b04094601c03070020001060000103811010300381c0212500011802e81000043c50400c80c1c59a650500d000c085c0f0810800402078450300c40044902005038000d407044d10702c00d076400d1040c0c01c540d104050b55260700c81c1c070109031900304000400002c0d000e4007064002e581300341001c1710900d032551181400c4e2000203a060002c510800072100988894403442a03101404440395401e5092000e4001e640c0e40190140220351184400440c00e03c40610f801e80d030f2000c079003404885d468500540d000761154400d80c1d5071206081c000c411344482c68021002e41c0c2c180d031608440c450450303281000c02c8490507002d0423020f410550740c8401166036102882101803110940c2004142c04108600061140c100282010b0070140b40400c0005046d503c04600c036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 183459487 1250 183458237 183458239
    0x6060f0904021303050f0f06130215091f050706050105011106041101140c0a0c08010615050f1b0102130e0c0f070204060801061e09060506070311010b1c02090a0218 72
    0x107896080f002e0072240030154641000e8264401c0704000441e10340b00080a0280401c003900381c8281e0346910350200301403c0540300083d440903403056502c48107841e1002402030300100a00410480b0120500071111200703c80d0060000340001a1031018802180102801880f0a20304814040d400c0903080f919014041c00041c120325000482c1030301c0b81c0c070075101c50b6660b0844003403050b81da01e2401e00d0a03a851806040403641c80f080c2078000070324414103208041c2101d154070700d10f401310700d1190000c4603980d20039100340004042c144007d40744042c480c5d001c410455010400140d0301c8e40342d0301c0003c9030a403155000804107541541008100c003c00381c1515102c040d0300d460280c40d0306144c4005400f402d0990801e0242e0362070403000060410b044420340404c3d11000c02d0000d29180c940300c07414165519402403940080c0d04020390800680b0400040340d68400020002405404040000d01284107403030042180c1c0041130040010b5103007010282d500448103400462408441c803a03180c880c2c0070845186 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 183460737 1250 183459487 183459491
    0x80a150b040e06030106031e020a0902030c07030809070308030a06051e100302070812040303062301021504060e060106030c140301080c210d03090b010e0f0604050901110c0309010806060f0904 84
    0x4110300c4e071004d400c4107010f150b0002d030301c001d60300e0059512080b03c01c14001c140d2249800c030000103100102442164094030070b44038041d141091640703040c2d6503001d003e001d04680e40705102001003c28200d1010f18090340003d28081001442d1600b08070281c0d00261014043c0c03c4504401541c607610000b80041d02a294280583c4480725810015100d0003150b86850440e01d108040008250f4142e0041c8103a0f5503c116000c1820b24069054a140b2210182c0e1800f5034040c1400886140b800c41d0020740c4148610004502c2c0074442d90302508002e0203a1211000c0f03900d5a404401c0150030854228681844c000002c0c1503601d0305102c10740c1e48034070b1001c26001d110141803240e012429001d10000c02040c01049602c0794042040003401841d51600c00ea80c0800350380004a880e1a9851065016070901207101250b602d0340300c10000100030180030700d5120741d07850008980380107441c0064018600c0e0140070b0754807500c1460014185240c0200030781e1180f10100300c005450041002600c40c3c840d016a00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 183461987 1250 183460737 183460741
    0x617010e090106050a14030d0c17070809060703020d020f0313090509030724061205030306011107081b120708190f080d09120305070f110c10080a150b040e 68
    0x2142d00400c05074101540040d0b800e00e000c00d11441002000241d0031042d8221004080c0c5071b00e0803501c984121400406022070380020161030107800e400340c14010302481c02203190030b0040000482c543c2c0030342070850242c2c1002c4240c6840704e0701401084103a4030345c840a140740c4090750b0740f5604404120300915907099030f1080450400302040041e6030392182e00c00c211038a030b40c03510006649481c113160000c40a0505060020401107103849245600c568071500560950b1949001910804151394541009200c0c0781c000081c5100200000e0440c9001c0c01c00d1840390425101c103018459044c2540c200c034641c4820750400c180ac000103180c7e02a261071500300310402d0350a1620844010a154001d40701c6a804a07402d219640c103540040b90aa100f44d054028052106000ba0191003044503698089904100703410744150140004111854241c000d072507040f0201d00001d80001c094151030b01c001003616040114038082d030310910522004004540346030740d28040fa00600c41c412070150768400c074a8400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 183463237 1250 183461987 183462001
    0x10090e030706060f0e060a060c061802031c11010203060109030f1b061e02300c10020a080901110301060f0516060e0106120b06151e130617010e 63
    0x761402203500200c107020450780c075252011035000b903024280c0c41e808140c011803031500d0543d514000b12491034031280905140390320ba00005107002030414001510304a07002c0010795052100b004c200721b2401134091407d00414006007491405e07e4615602e80c0b0400034080c080e030300010020220ba9110400c1d100015141ca030100301100494000c143d06000c021002c0b409030b801241e0800200801a00311946d09110f41e42242da0744600c46d6100e6032240c1c501c4240c00e090402200440c02810143c41032850923800d4020549005080240b4000499002c5000c807c1c042d401410150450460700090107455030403102041e003840103200c3c6030203014440d0328026284c0d002d0800e4441c40200c2214101c1c9044490801001500c03440344036088551912002141421214840e5223445401104400c0c0694544040c814032140c5101d1108c00404c00340071a002c0560581c001504d403820007510580c4076001d003070726004403c4040e001007041c48050641e0002c0c099014441c2811195000cbc1c108441d034031019 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 183464487 1250 183463237 183463243
    0xf03150711100912081e071112120108070b04060f090e040c0302010207080d0504030f0201020a2901090504030e01030b1207081c09050d060c050904091b080610090e 72
    0x2020380940e602850400340b0400705250b104801d9036000b84c803841c1080c09410f50403260386404503042024074104c0e030351141e44880e0303c080ca603a000d5034908044403040e00744d0390b0b001e180500c0e0341e410070074210f40051030180505020354020300600c00c0c04018146036041c03140c41002c9000d6402408100181c204903216247d00c0b6912180c002d06908c140140c40d0705080c2480000c0071207a01041e4054855010b0020f820000010740107822041961100c1c1010300b0744d035841c4d52040140b0010b0381140319a0f050b0300d011850350811001036042a0088a0080704180c88460414505a0195020614220800000c25004000c1d0035a020003441c00041d500c0d182e0000074000840741015045512a800d80880d95201c00108203c5100712100b6003c42c60346018800ca49694440c0641a040a10f03100c20700300003030068100c059400b049003001414000003401050440351441c000351644103c0035000c810b08682e0b1000301c00603000744000ba107502d00d40503030410142245072284401c1c152f554901400d0ba0742040c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 183465737 1250 183464487 183464507
    0x160602030319110a05090108090d090311040e15040c0501020d1202070c03080a1101140108070501210c051c050f150d06020c0102070309170604080903030c010c1206050f031507 77
    0x480f500da511103444960090194004260581c0824005130210382c0d64800000e030180ca48840c0e91341c0c140e517942140d491002509900403020740150710340d40490a0200700780700c0502e00182d030207546001c91400d42002c2c5089106035001e20f0554001c070f1603c5035403a0384844602200342c0510b80c0942c1e80c0b100c40c5040c500011a5600c042d146820102d40d5140d020b500c01c50211500201d000240f14005034007049545414081c82400d4666000e110704101c0c0f54001c2d0807081c5950440d44807142814031070403020b4107541a141044000801c00101c2c0001810100d18018088036212030811407403404d4615500000405044071291605140304c0301d5281d521641d03044005580f10b401991186030040246010b03412002086001c0b81c9003010105000b4512009030080d041404014021904c445d10349015644c4030403129909400708008861141d40e090040a818126944ea8009842c0f52000711004417507043e004144205c02001c800485c5640020f210300050b00100512806a1508001501c4111305 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 183466987 1250 183465737 183465761
    0x20105120708011404060e13030504090e060403031b0804020103180203070b04170303070e091e0f0108071202060904020c010204030b090606010807030c05070b040c050d060509160602030319 83
    0x5040200603100d0b80c020b120904844500f031010250641541c02c01059a0190180c081c1c0030010000113154200c08891074040390380a424a1480d20b61110788410a82d4003e62400c403541d4040400c6c0010198503102d512403200381d02103983e110b08441d4a006101d110b01410190405817100e411215411040b440b000007171387e000381200c914580d2001c04901c5034010f4460744406020409804942c2503000c01100c0c03141c84507541e194400c05400c800c10251003800351a0100180440350040414800d1054050140c0d413a50380310201503242c03403885443c0407129000101044240c000d00705c016141d010603500704c03182c1100c0268985003034142090080c003995101405c00d0401c081030100c0c00401184d4980518000e82c0c8050090b43e5138070b0180c0507200399000031030005504000340e1022847c0b00d00802e404c00e102d00340c0b00e4501c940e140300040540c020380c9030544486a6480c18040a200e007046190455903141030b6407400245450030180d16400000e1002001c040703015000310f040f000070350001e100b8041c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 183468237 1250 183466987 183467017
    0x3031c050103060b0111031204080d09150b01090510051810090602010b0603100306050405010e0d020c0f0d0209042303040603020307020d180902180a090c020d090e0106030504020105 80
    0x441001180500401c1c841902d24901d0508000070300d51044180443e01c140e403500a5107080c111008550300c0680040c01038039441401e102c079601c400600d00801e4032803400303290300318005040320b6184411605991040e605001000c40c042001d40c0318001c216003040124180070740c0f2080d103030422260200c40d040c80d00e9030103221208843c142c543c202141106445c4540c2c001c018135494502030080c1d030710050725800700e03a00c2c00d0542003001030895084213500502c980c00220344100c50400c1140381490022400300541c0100c1000045400d10005c046040c00d0221120300500c503013500481c1c141a400f802c0903022800780540c10740d209044c1c2c50f054030540d40c0078003100c0d6a03a5441034020004e4000340d40480c010301680700c0103c0800d205100c03c0c00c5100c00804030303141045c81c240b0944002c0d40605840c8010800b0300c1c940680d20380e142e4078414024003001a0218a0440480b002420403110031034043c01d00c020b8607424010640e01d1203110341550310b1401c0000b042c2c1c03254001070f1804d00408941c85400c403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 183469487 1250 183468237 183468277
    0x1030b061603051e0c060a0c0203090307090e0d080402060a050304170412120e0f0f041509050411010804050d0f050c01090515100b0d020a0905090405010506010e09010819020303 78
    0x954800c004010013501400018a5034901000c0c00c000ca1040343d02481140c0d0012010525064a50b4004a19007203a401242c0c82c041030a80402d003021030640c060355100e83d40d0039001c4541c04c000e0005005507019031404013050300c2c203540050403078068001c0c2002009800700020f0200040c03210f03055034203078034444500e44584d03403482c03d0301d16443c45c003100315940700c06480c0c1180d0030750281b44840202031000700000d503030b4a03040c001d11440c006c0d1101943e0348a44c40740e100c240d03520710a00103075003d0101e01c0350104080c6058203000d03150942c0c0b20980b030f041060020411002c2400802c10240301c0440b03113480c055030520040110340078000d4024030400ca518040000081010004a068006103144089002da640d03c810070300c907606291280300c621800401807154000301942c0244941079280c20203802c0d01d602e80d400318101240840d4101c405a5403403003880a59a0040e441a0040904540e02d201540c18200090380b11582d964122060902c04224101199014429500006009807111301c01c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 183470737 1250 183469487 183469493
    0x60f08191109090c01020106050d02130c12020705030403021207030c0905040f170a090611030d0b0a0801060e0a051b160609080c1605120c09100906060e01180303020c01030b0616 78
    0x84c10368001c401e40513603e000c80001d0203041c41c503032072101e41d50000d00c48280b200d218907111003d030101556803801c0050303084000c0e0030443d0f10f1001d002c095000d44011901c540c01c6105221541040741c00102a40d40240d40402c0064003640344c2800355203110f400402c0c00d858a140c2101c101140240c018400882e01103004075071440800904000c0004c0e9485060b0640c0e07440c401e4483c5c401c0c55050740c2d103542041248e180e000ca019000714201c02d04c00ba1244d02c54560741c80e511130071501c1580285c00c0131000c3e0f100740a10b040c143d00420360071a0030340010350241038100c0050303040c030700c04d01000041c0031040d0004038003400101e03408140070a030080b5050344d0f81c120070000c154480104d0042c101d40c040c90703d00041020f040062182c00b10184400c0280340e5280c507481000948a0020000781303008640b040c011031101c209000c0c0f030000f020b05803203810500400000152800b90307580754091104185c0142000800d500203a503001e2001d082c240082c1e1000c0312030114107548142c0301c0c4020044150441c403010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 183471987 1250 183470737 183470743
    0x3060a0506040b091b090a0b0a0906080f070507030e01020a0b040830040f08130305030d05070f0f14041212080f09070308130315090204060f0819110909 67
    0x1040d0700c111401c00406a1403402c2180c901402d944900c2c2d100c55500008043c400c0410040400b03c04c01011440a00d07a00d1b5100704081d806046400c0c00201074220401c28240c0240265411100c184a01c0b01c8515110786c00611070301541102401704841140494100d900900030789002580152a0004d50318050400840c140e10001403c1c0000300301155100040f80c00010140b8205101c0120540684031a1103803410440c0600081d620200200607100151300c52845100c011480307000919101d40b41c001129044178001024101031102c800342440450f540045030b04010f881c5030401c80c95407000b110015245008541200d80c110b1101c1c0c8800302401542c843c410ad10300220364801c1107941e50129251864482640c050090340d002c600140000b4030341102030b0030024071a040c4d6552155403512424100e03480c0d11070211641d9928a8160305506181c017610700030344444000c0c0e0100614000c411580c400346036182009115034011030170204030041c0030420242c10300820b0001c05080026100b80c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 183473237 1250 183471987 183471991
    0xa020d020c100605132007020f030d09050307270507051306030e100204080303180c0603010311131a040506040603060608060a0e0610120c050306070906320f0903060a05 74
    0x48180801103030000711707444900617450507641095003520202080b081e10403c41c0c012410407603020000c0003101c60b05807803c008900048426070f855200161900003410300300403040d003103e030104070298004048030b8482d856001c04134922400000304c542d11907000b110300d401107980303c40380c00302500000200c50342d050304510440fa012390269609145e45d000440704138070862245e4103494005100061001d4030342000c101070000460182d0302e107200450300107150740d84243c00889030701804a00445003410800d0100350750a503071410810500030722205040d908d540a01150340b04944801c0018a1a207454012200555100d1030a100f2551034540007501d490302102c0c444103403482c00c0c04061440c200040c0d01ca01403c080e181300174402e41000300804420702840d4056442005140300042d80f81c404000103480b82d00030342e442ea07a10030305005c0300611101946007a42c1031241d0300e03400081080701c281400d1a84101c440d03901d03507550a08400c1c4805a016801c8202d5140c01401e0070045401c400c2e810441c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 183474487 1250 183473237 183473239
    0x8030a06061416031409150c0d023705010c030506090c04050109030201080601030b1003061403010207050717160906031401090b06011b0c1202010905030a03080a020d020c100605 78
    0x18041601d00480c03000703500418840f03581c040807450055000c6402821505001410303041c5642c80d00c040388000c60110182150021280480020384c184000e4042c04070400f001031900c081c3c901d240f00c07880c0180224190104e2822442d1400da18408454165240003240c245d00000920540c20889030290081c502102c071240200401d40000d034148424408840944505841c0c14105504540044646032401061141070603070300e41c0310340c07083d031785961040c0c170186d0ba181d40110380c50b4103000c54124503d10700c2007031501a070f00601c0780e4800148007080440c2a00c1405118880042c2660310390f0b4940101145490514030310b01f8804a000003107034000d0010341f07010f01401c1030a14251920342c7d00306c07a514000a0000e040c0100821a250702c40c0021130360751052040840101080754032511004800b50380b0038200703089000c00800c219600f1410510062504802070f08100d24035480140c108540200070840351940005c10400c1801140d06a40c80c0012503000c8603650080c50006400074802d41c0201 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 183475737 1250 183474487 183474497
    0x909020a020717101104080a06020d020409090b0406200f0903010b0a0f080d0822020102010e03161106040b070821041401050109290a0b03190509030f0f0a03060308030a0606 76
    0x5c03528203000808440403210301c02c000308030540341170726910029000300381c000c9230480d007c22000403044214001ca001607400741e92003040d5414036261207c100c6000070300503001e401e08400c0c3e4111881c04c007001e44040c5c4008210003561a40150300107401040c2e44000a640100c01040204803003001c4c041500c00d503000401281e816121060701650101412900c5034416150300403000403446003400030301d40052042c000401c0c03008040000a007184c101e07049501400ca0303009203103000e12404125403607006070700303540040c9040d0a21104030714038410080040c21b40000021611807100025141d81001c0c00c51000e00b00781c3c1c0c00d15160202020070042081c0b9030941c2000008502840341d44500003400c2e0441560398000d125125504540c103d40038402540a0014070700042c0c0c500a1000a600c1110446d4000c4056006800c03e041203032400b0b400c001e0568014003520781c1d032040a0080b2000306214005094540f01140011800713080c07941c1000b0546c170008014481048560340044050f15503540b50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 183476987 1250 183475737 183475751
    0x60603090f06180c0803090108061503042003060a23070e1005040801060923040305040509041407060f03060e060d08030709090e0a1709010909020a02071710 69
    0x12000c0d1250300ca005007080c01e640440d040003400070303404940700c4035503500c3e594072030f4486031141e01d800e064560001815400000ea070202c07640c1c0c00012103901010856804e400e2000b108889483c50000900080003458084012011040c25980c0802584130050898499192084803500500203403130b22202d40c0d25400100ca00e580c003605c4d981c90711407680c940e41d00c00134440c44070412004205180c0e0b44814494108000b155054007800b0301000f80503038203008608120100548011240c1c034145040081c1d107554140800039a000741140d04981c030403110310041d902c8500b0500003817400070044c40090b10840780300040c5250041540250801907407420480c0036607400300390701400800c480299001120948080000d03400c170300031b0b607040780043c9840003202da1200b401000301c0c1d5000d024100e41e9401103414408104a0025480c001c2d41c00c01800e500700440d40001030325181c1709000ea14403c1d90040766080e441c030710800850004100d0079a4012018484c0c13040140c4900004840d11a40ea060440e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 183478237 1250 183476987 183476999
    0x7060e0105090f010806270405120301060e010e1f0201140c07020a03170712050405090a0c08041103010f092103050403050706091a07170609010521030f040b040303020106 75
    0x8142c51440d01d026081c4003203c030070fa10044502e000c000f00103d60004441c031258032080141c00134119400c60083c001d242604003410044c5c03621481341c10a1120140810060006550141c01c50420301c1e0300382024915080783c813001070014040401c0342d1500600f40322200c00106d505410003074100300c6009101003540c40f00000b010140c03090700c00c040e4104500920420001d10b40300700515004a201c2109030405100d43d5490784060100c045940010750301081c1404646004154103070804040ea4003000003040008014121aa0060018010030300703481c0301c0046900c003904036600800c8460003c000007181440c1810a40070741106461110a0080c029003520740a40319550185425440304c0d410683c19550b2000030b4900c01c40101d851403e08c4403020750b180903030303007540340a0480d6855191498071246440642c080d070081045204280c0e0a00410480c0c40d04c07600c1d118cc1000d0181401a4020a000082d1940c419444120100c5000280006124075200040e00c1580d100b07034000c0c080d1560724a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 183479487 1250 183478237 183478247
    0xc0f0402040503070509041502070503030f0a06031703060d0b2a04300c0e04060e010507050409090303060b0a0504030209130c0504050711010c02100e150c03090703050f07060e01 78
    0x1002d60b0790140d00400d030a010f94034050a000c6d900038803d01018001400404005d410f98010351812103443e4070100c1400396000840d030706140d020623840c2081002c1440e5881c1c0c91000095002481d030080c1000001c00e0300c03034440181c0d442880d078000c02c44000e2401c0c082c06200310764000d12312078180d600307c46000451024030719003114212041c807180c10502000301404484451002c1c0301560081c5400d090000c000f8900035000d100401000041001515003401e0440a50300d54070891b14499240000b0001c2d0760740c11000707803415248040400036001009140680040081340c2000c0388900f80850f80c1b1b81603c0d4000d0003007064a20940c0c66039450303141e218400351041802c0703000804080740810705018500300382d888160301141618040500039505813803a400c40d400b6440542c0181c002d1070b01e000a42a96004464000d1144001804903004260814980c20b5000d0b0481c0d21f2140c0001c0858031a840801c1428040e5030041d0030783d80810800852280d03a502e5074490240440c0c20441c0450066001d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 183480737 1250 183479487 183479489
    0xe06060f03060903030c090303070b010b090901050d0507090c05040905160f0809030304060c0e040213030606122d080409050703060906080a030804061d030903010615051905070f050c0f040204 84
    0x540011170568564484126190700411075168040c40107003d2840400c9800300e4043c0207100c8440f206550b00d060b082400700518050300b200e40a4610340c501600016070001c3d0220480704030000c00550f8003c1c010040391a445141e2220714110b0030001403100034410400300c1850750070941c40d090502b2010000560310303020f044ac2c1d007402c907401c14400100414070070740021400080d545406040004802c0000b0b04070b0f0041200706141405071a420f000b00002440760801a00d406003015010b464244d90b031510b24020445290501e100c4058061900d81041000800042d400380c1038980340c944610240300101000c40300c40b80000c0c1010000102c40d0103911415068801c203070701034007a0b032a907620141c92040010b07000320740869480700c40fa901e4442210280081e00c024002459440c60b2110404d403e546658015403800c40c0008010901d103900308084809688000c2284504e50b00034100075502805940405809040001c08401c100000030401c030009100465003038640d8408101880228091 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 183481987 1250 183480737 183480751
    0xf0209040b03210306031501080105061e0307050607050a0f08070c060903120804050c060301060f0806030606212112090604080a030b06040306060e01030227060d02060d0e06060f0306 80
    0x1410200c400c520f910880156881840a41118108500400d460010324003d07444204665500e606002d56460002d20300040300c2541d2000e086e08003040c100083c1c44002c184101d92040c00006086410454148128841242c202042010b0041c0f0b604000310a68480e0320200c4000c00041d2010480d02c5c000e400381000c0e26000703c0c04500d010700c006402d448a20000d003013070f1818410482107060560701c40b00214042c0c420340c1d4451500c0d810000001e0201d00e005001588a074100d00c0c01c21545486044042000d1810303480c1c1ca0f4016950907492500703292072640200e0103000451440201c9081241c01030000e142000340548081c0d550f10705080e00c55106880c002c1070b041c0d0811403419000e210360001c6080f03980080045141c41d56940d14a8200c4025601803642281e40d00010015440d0060003010350020088800d00300001d10285c00100b030000801da1032042161040503402d544a01c0d0550f550800041400c114842060740015035410b030450f00380344285494000315006080104103140a0a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 183483237 1250 183481987 183482023
    0x80304060c02040203130c0f0801061d0a0914070303090e01080f060601030e0111030103050105070801060f0905010f030204030812090f1515060f0f040501120212070f0905040f0209040b03 82
    0x74580c02c1102960000d00005c03044418083d05102082030514041d0042041082c80c0030020700d803c1441d42510300b0755005910404400400495403009103260725405101e0303040020740f220b15172420320b2103c6120ac2c580c18040c4207036071010040540054041065034008449140e10b030386da070248940d4412140d42104070a401900105000b5402a04603052a041076030011444c540e2119410186c2d8100360320940310b03603449005102001d600425401d02401c52440c0c25161030103180c401a00d080e01c0d81c45024104500c0b0711000c00300e42e100350b06039409140d20403685981c0308190460008030f408151080700141c024407898194010f00010303808400b800d400c501c6030bc5955190303543c0d40303036000054009400600410800c41d11014440042c1006038581141507100e50034600010007140b503180f04d100f0154410400d8030100e0721807880080e07000503a49040703c62059a604221500d2801d079002c2d582003800c103c80c00411403c10f402038000b048040d80c08015000030801016541c00407072403d0120341d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 183484487 1250 183483237 183483257
    0x10207050c0a0b09040b030727050601030504080f07061e0e010c05041d10030b040f05070608060105040b09150f091c121101090f1202100e030414130e031308030406 72
    0x2017400d030048000c0140060a480d00c2550700c5c03144100740700c001b80101d0780380300708204400442c00542c4201c5811680c05e203403c01c4035150940d1900a5413250500c090341209021500b01c080141c0e54000c613808003e100c901d0302c0d440c0841e10040020304000401c80c0c82035400c00c4682400349102d070054404403032038542c00801342c003072008010950107030107030091004e0090500c010001ca540c101015004078884c40c104078009096042050400c0400d03080b000030026010b00b8005240e0b0702c5410b43c2c040e2603121042c941e9540c01200041c8440d5000450054105c00206d2004c2104140c240036188000c0181d40d02e1002c6030f104800c010603100c205000400e040e000503221080ca6100b802c0c1e0400e060201000081c91524a464100245440d40b00232a0241004a540d00d15150306010001944009260500840c150b06c07840940703a010758058184415182030a443d0784e80d41c0c02030078003d164485201000401c001d01c00e00c0d916540610f0b10402c01200c1030400280701170340001144c08403103141d41c80e11406e07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 183485737 1250 183484487 183484489
    0x60a0b0604050111102f0901050d0c02150405060a06080c030d141204060911030c0a030b061311131712071718010e06070f0b04080705070602010207050c0a0b09 70
    0x34504c2c049001c2041c4584103920012030306a02c240000c0149070b40420240468031240840b004403110443c0e92000400e100400c00742e6080801d942d000b0100800108000c84000300481ca40700b14404542c00302015401803009002c0081030640c000c589913001800440e458881d401c0d501d04291454507003560000b200098103604c03400403002da010b40740090780d140106042c03a48400e504142da00b074500300c0e5100301040400040a60030442080107074082d00e510001003000400905040c4800b5017901d107070300300040c45076403468007510a4072403e0100b00620080d101040e811a000b95140341c04a4625040124100740300c000011620f4500b800200305135208900007a1454002c400d04580c41040741c40c9500b03100789075038041c00c034861180b200440350b91502800102080800c5141a00502c0100710781c10114a25400130804250450001c030007a40751442c080d08148a40c010180544c0281d5038049146a81900200602802081101c3c1c09454050400c20714550358810030390320060803c43c507030f09 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 183486987 1250 183485737 183485747
    0x30f0b0a0b07230102090406090902011d060412080d0606082e170a200f01110307020402043803060f0a0f181103100e040c05030d0c0203060a0b06040501 67
    0x4590310442c082100f01e88198186000b41c600b040e05004145d40100b840ea80c6810144140001408403100030b002d059204d4002030000307048003180c08407070204070421564a0b1510811a801029000c201901150590410700282d4001d401c145c1b100703500b04140011000c1c443d40800c0c1c0540d88040c0c0d0042180714860b400a00c003d17042058519540503400d001800c1074122034030303443c854800e2010f42000c02c80b524080c0f41410522441010503011250220116222604070201c1d010082c00c100030401c00a8840e01c3c0f031402041030096100d030000801040d034424029000004c14450080f03010400c83c0300d2006041c080c800c540c0440c64940500c0083d4852a20300e140508055000e8014491680c407482c043e180420181c010305c060300c690000b10b5110144512400d0101c843d6080c0041c01d5080010325440c1b504a14032420130358042810104080c080160400401010b0040c00c98030710383d540101c0581a00542c5000764400d01924000a5070000240540c0d40c12010041c50a441c1c02e00701001510 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 183488237 1250 183486987 183486997
    0x70b0f070201090804060f0e0a080d0c15060305030703110d12051306050c0408161503050c040b030f070e010e010e06220801020c010c0f09091802030109030f030f0b0a0b 74
    0x4540d01c880c0f0f2480452070b5180104040c0c0410380d2603518031900b0101c05020b2101d0000700341e02520001100b00031030200881d000f9016956840d1841c80640c442c00d00001c5925008601000b091a00500000b04800000281f106034840d4940310440900004450345811004c9250808202c242d145a500801c807036005d15440f0941002e14480741066840d10307421100207c1d41211101400101404617010130480c00c1e101c03540c1400d80182c82810425403414030b04010008409154656001c07a0307145000400703540141c1124032820b5120314241c000d121600600f40c80702804214007024148095114000302d0ba500e080c181c5580c0c20140c40c080501015610060314102034191200c14485000301d8118070308000c041003400903840311402020142101c6d003455007142808a43c418402c02d454101980c48202d5042000010341d0400324140c880240106010080d80355207441a128201504400d0f04800920140c2e02000a0403051440d03904540e03540403d1b40e8480e401e400c0401c105002100105 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 183489487 1250 183488237 183488251
    0xc03020c010509061803040b070b0c25060f051e09010b031501050f03060403020613050c061207090801020a1b06021b070305010507080105100e0f0a0609090f02070b0f 73
    0x103241191a541050071180c064455520340c0d0081c50034001006003d80e0b075008444010301c080c502d414030740a501c9000c1d01c82c0d580001c00700ea800a0000c0c890040f070400303541c1540c1d8400200c0007007600480c407604406041c0c8001b1944d403450090305003c400790a100c0d9610684c1c0a1003802a050030014404010403002480d0508030f40d00d400f400c450300d440c103102d40c0410b039450b80070100c1d070395040c042084407001c05074081a0182d48110708000129900040081e00000c0b41e080d40c140544030750a216050005410600350000701c00541600c4048210904d281b1804039035489004542c1c403603030001c0c00c3c1d11880c0d02a01c000f40540c03040c1d480103095640d0461680d4815080180384c40c1804141001141040080d2040d0b6000940c0400a01c48280030703869211000d0301e46150b0075810700d00052145003074190030b40b08201410301541d1164480c40312060351818000c00c5c0aa81e0b565511000300054018050300b282c4900b00303450011401450700030b1b2038080c1c1d4442c9005040791380c0d0102c451007070000140a1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 183490737 1250 183489487 183489491
    0x90301061a0a020105090109020105030402210d170702070305060604021809040f0512090306011a37030b0609010c1502030405010506090106020607121a042310030b04060c03 76
    0x609600003600e2140e20401194aa0b4461212150207400c40798001c00880240c0d043c000f105005030390140451b13910580c100d0313003072041c1c0341990809076240760100c0700751007a1300c604041503151039003002110681d24402e4881043c0b03907566803400c80e281c5085100080003540922302044140c41c20360040d102c440a640482d5200f03401c00d0000541420087d5001d6401d10003544980060040c10300c020151042090007103480c20080101003036541c8014442c03041c68410f039031200002c5181681c110707105070710400000420644205500d0f03a11009000440016880e48a521000385001e40030700480700350001d00c003038280903445005603208204040b04450b030310f0b0f2024820030040c40503c081d40c00b881c0200d000090170301d0550103200f950710040c1c1104d81598003410800010303da00c01000c00360710002e0040407400140382202c0d0418119031440199005041c403203400041400050742960b14005000121210b449280d0221000c80c00c501020706003505c1800010003003001900f21b000080581d20700 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 183491987 1250 183490737 183490739
    0x1609051815010911270d0206070515130507120c0e010b0306090604020708070f05031e0c060a06060804110307030b13140d0518031903020a0b0c031303030209030106 72
    0x102030030100d11101c8100c99000351401406030920600c500c0440c2180b2034450b916080070102042d154403641170040002000e646000b120075116400100790040d03001d0105615403c1c3e500d4a55112048211119442024100082c41d66600b4912008003e5004800b400059051864414180111980c1607a40b0703445ca2200040c3c6041c0100140d00919020100544038100102004000c141c041e09886c415801030010401050340b01040f103d11a1b402241540b0415840c0391032401c5004206803940d60950703405501f20340c88009401000b00380300c40806e8480aa40d44c011040c12125180181070000300a000010001003410110010240e0001c0848514a40da41d1300d5135100e4000302c6880c0590908000c00d2010811f0074408040300c0381c420005001d50001d541030090482c0104484000000d4100884030f03401d890511034810b1180381c0952184883ca124100a544c0b40300d0100c00311041074500c40014200c07041c000560340603161a1003c48085141d54400714080c1d007029203850780c15560303114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 183493237 1250 183491987 183492031
    0x30d0f02090a26120c060903070b01091805060709090b0901030b04030f0201060e0c28080c0d020f030f100e0702030403060c0e0301050709090b0406120206070305160605010e060102160905 82
    0x3d1300005240d1002c00d60380c0d80703d2100d061810035001904541181e4024002c103000500f03103454403810f44040d8040000c240c981a01a0300348550a840083d1941c0680c03401d000d001d07540406440c0586034040024001120108144180703210300340f0014018003207103000700c1c00091080d02c414848078070900c000f01d402d544524110003d580107450803e81c031301d0009060710f40540e401c10810004c10131a5080740248540c0070001e0300a80004041009000c40012130740050070442d4180c83c112988500038584900c2d16201d0005c1c0c1038015601900e40361072038000001c042d55900c0c0c8251060310f456014604051440d0344030800341080103a140140000020388488545027413150760f225220076990a180945402810000c403022914224010303410b04000b03102c3c4a40c1030307140e04c5401d0350681384180c1e00c121030300341104d590060007491605241780a581006100d260b40006040e9820104c1116079502c401c001a680d5495209400101107440700041001d090b1130380c04564401e80d10524801c4000b4811 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 183494487 1250 183493237 183493243
    0x1030b1302040915060315060302131e090608121207030615181a03060d140706050304050c010c050d080a0e030c03190905011e050702090108030d0f02090a26 69
    0x2c0c002c245002c1d1394a141070310740c05510000d14010302107030500700403010341a000b10383e42d02001d004200500d0b8002580b84c034a24248007400004000040800451401801d90000114441c3c440c03107072014180b000c0850790b8400440c0d181045404110036034503201ca408160410154010802070074903503034840005e08154225160301f00d003192641c9210007402a900d00f01d0040300c0700e070001854145e40b14400481100c001e0112900078408541008140c60325140800d20414801c40c104002e009022000a9864200014502a62090301541c450300c800d03100440d0720844640d400382055204d5401c45080c070303010b07010f01a084042c2c060041550b04034004240e1565002c41c00c0c003040c5500c00141300f4030049901c585240a2006890304950345c41c50310000034030000e0003da10110352440d002144807810b000c2c038211801c2a902500401040da515028241c41e9044107580e103480d030b820140c1c180145a060310846080510040040d4055802e0056081c1c001440c00c4c0d801c02401c0950020002c141820 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 183495737 1250 183494487 183494489
    0xd0309170705060916080c060306120102040806071205040b06060c0a0204020a11010e15040210051204060b040e0d05030109090804030213021e04030c031716050102270a0501030b130204 81
    0xa90028101414040c802c4c41c640b11111512441c030821020044c82000000300e4064015402200c9007030700d0b9200d000c0024034000d40038140c20010762000034006107119001c55124810703450b070344828240103242000681500e200300c9008000c0c3c0c000e140040c1843c41c114003e003c0c1501e0400460301511110b5001c9006c80c4e114042e05004950440401044c900090161f146d4101600001d40200b002e1002075000d50a0302070302c002c0c80340250f000c020500d20320034811b03108400c04c0003894080724101401c04100a083c041c10003030180e401d00d614807000d00c00c006440d1100b0701c195a1454696841c220100740100030a0a086641c0c00742000004090795036030740c03c403407240c10707141005035180744010100400c2c7c04810a02984140e0500003080419059403410003203c2c1c0203194004006850203400341c062040a00120001e8900d0484205200055028040c1034050305a4108100f190140300806e07180e0302aa15070780320000d180180095446604030328084080507007004078100c4404540e0b01a0380003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 183496987 1250 183495737 183495743
    0x1080a27061e0b0f0406150e010c1704030b1e1602030403050303041b060206010b09130b06210603030c03040b0a051b0d1709031602130c0e0a060f020d03091707 70
    0x3da204511113498440c000520103007085030100011480c000f0020080340d6025101030038000030088030f00b8141d009840d80ea05195011a0311100150102007400d2242c106002c00ea0310081603c001a240603544d9401689800004e856240680d48002440420b03051320716801c0e086000a210010014030104081d502440c41601d002c80300000c20b00c580c0c04603410940c050070441d84031000400c9818503d2040351a165820303940c05800903055040d51001d0483c0701c010541211b00092900e220b0403100148040003190fe00c000c0725075407561410190740b40076114024240b6001003208101e8800c51000a142c1c0302501c1c204a802d104c2024074a0380300c141450b016100c0c1c5e401400e0541103040c0e10281d0100070140c00301000600381403250806a480c05800c5585040310345c000314440543d074440c0f0000c00e4800346c105040c000100b01820003400080c484140f07500550b000c00d400b2030407034000c200b02955910340f0740c0280b03c454490031040300908200c01d02501c2e4206c00340854072407101480020042240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 183498237 1250 183496987 183496991
    0x1081f170105011509051513050907030b03070f0f1707050405090d120603080318011e0b0a0806060102060f070c170a23030126030301030302060601080a27061e 70
    0x850f00c0111013050041035140410021050701c00c0c01141d46004001400b540c00030350030f50721405501c640100c141d116400040d802a1503c1c1003080780b83c1c0c10b804c0285015415070589000a640d000c4200b41845035014a01c200044442c09100e90610020440506003482c000c860b84c050740c600c04035007194019510501c00e500200c1c030420301542c107d00200d40d51b00455070200140b44c51911a203a0600001c2e04411b1050540c10040e0b8003660250404d0198000b5862103000c01907040402e01c0041040e600303160f014a462420000302e00001103595071203608181c01414040d50b0b0300c0e41ca081c40c1c070390040090043c008059804808100900c6803850f015445a88007503840d0341100d005402c0c4030380040702c1c2c40c018110180c0c0c904011002002d9a046402d414407180050380d2200300203001d0031509655411714403012000200741075000840900440b02a2188006034989c10039402c15960740c010b0042c0c12002034901d00e04404110300050017118044c00c0d0020b803000148000640b10080d4050030107000c1c0e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 183499487 1250 183498237 183498239
    0xc0a0b1302031501080a2013050603120702090c03060d08030106120501090b010c0b06030a151401170c0d150c030605130e060604020304061512050d0c0201081f17010501 74
    0x1003003c120150000d14851011a441d40c50404400d40d1108241401010200341208444100540c1110b102c0d14000081400301c1400c4106002c5009040407a0103500c244540b40300032582e040c000c0d04689442c2d0b006481091143d031598075042440d4006003400f500841c0101e4440003180040d40698064510740c0c3c1c6e03803030a54144001c4c00042d5003041c0c100e0a02c81c1d141c8018283c80c1d0f81c000229403150740e44000450302641c3c40350006801c026880760040c0610100110380030300d0400c47e501c50032041d0081001206243d807a000001014415103d4080850340155140d5a4519040080201e0b562203840c19080d42507000021500340ea000320400000700c0c0e2654001d000610701146040b0440a4640c81000940200301c2c42994402010f480903004980c000302080510621780c2013001c01d91038161100020070b94800d201e00481e0002c41e8182d649000e289840c02d00c0c24462f900b0108015016581c03002c0d9500e03040354480741400701c40c85400a54450800020b40300021540050180000d203000095075 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 183500737 1250 183499487 183499489
    0xe13030201060e130213020c010603150c180306020903010b04140901050903090d061505040c0c030f0c020604030209060301090b1315020c0607120605090a0c0e041e020c0a0b1302 78
    0x50b074010f8000300a50b108410420510169000501002940450700d030421714241e00d8800b4001e101d843c5881e0429402c0c0f03200403040c809402c0d0040c10545042a04014440d48010300319007003c04083c045607100c43ca03a03c100042026600030b803130320204c0180002005107030200000d0071155107082c003920604520707041141c80760b400c2c41220346c0102480c002c3c601c0e01544800007500000c4d03011000700803680d10344c01c1b47c80104d8403645601c060302c03001c3e004005c4410540809885805200720031000521200602c20f2002d00c2841407503000c0f0303400380c5400e0030242141d0803c168418000e10030368140d0342c3c0b100414046204214030600500078800d03d489040c40c8c606154011240c0d80858080303003401004580307a100000201c6a40c4110b40c1d02c0c145641d4116102d07110040d0420b90300141e40241100d003403200400041d802046111403a0300c801d0500c002c0d40c4144420380b40403401c00e10050040d00b002040b5951702e90010401d0054100070340d40c0022003541d0700700c4c1c89041a40e405c48624140d030313000011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 183501987 1250 183500737 183500741
    0x30305040203011a010f0f0207030c0f0e071107050114090405101503110415050c06040302100c0c0f0803070309020607050102030603010b0612060d030504080f010506010e040b1305040c0e13030201 86
    0xe0602807010341325020300c1400c0041c111014034061364040010703003214280d201d8801e0140da00510762080c904240a9a600802c210410660003030440c0940108045080c0ca4051544044403d03072810241c02c115113020010b44901014803d040d035000820020f6180598982c0702e000d101d110002c480712100390801007842c075414614001035007454548075004520000340000d0768219100c1c8005540080800e030003c079418000c0c4200074105101d01d40a0104046d00415110001c00409504000301541c0343c0e0200d41d00200340d41c01a140310220040d190100380c05c0e00c001e590021143c20003103a4003503194085a42a88411030543d06a503000c000e00000c0e140038004d1180e000d0003201c070326082c41d10001e154500440c01031720403842424214004802c050103102614014074400041e03414403076400910074041c15049408a00040c10010040030b10b01e4148940c0c080910094002400410100423040040201400c19103803203407954000180580c0284006120300440c010b01d002502c01858083e003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 183503237 1250 183501987 183502001
    0xd030509030a0806090601090e160206060f01051918060507020901050a0e011716030f150213140f12100f05070e010507020a210213140112051903030504020301 70
    0x40250420080c480b81c0c0c5502c000e6a5402c8131089400011a13142d500059903409001c0d0301c0950003164950800c00b030600714001e0700440626940a4070038075580c0b5001c008280c0a900b00e00c5003c643e0610003011120041c480c040e079003850b40d0602c0303024000c0c55000725203810882d82c4800b000a0002464208500300104018010402690340c0e9a0090420080501c0c82405000310f14140d01142d0300809452410020071a03c845841303000000e5030340f45d00f03001001138400c550a5400c242d5082003d44240298401c64094003840042d1255250400c011440e08460301000c3c41d030f0160200c0e2003100c0c0f41c0c2d5409070a0801c013007a8402860210003048501050f1509803c41081c0d0a00d841c04010003607800c10031103107100c0c00034a4038980e40c2e2150b10000e02e02802c4c642001644915501c08071400c10507441c1c0480c100d41c02241d08441c030719490300e0880103840300d529840b65001d100000400401980744600040c407032140b0151000c200c2c8642102809503a50f003401c0d000251104140320540c00c007803203030748 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 183504487 1250 183503237 183503251
    0x306040b0a0909050c0d05032d04030b0901050f090606012f011b09050a0909020414090318031b09070903080a0503010f0b070b040b0615040308090315100b03071e020d0305 75
    0x14107800c0d42d403601f544a00945600104100c541145540548483c051102000c0b0f1110440c54175551070341090583c82c038040300c000307149601e0500815500410100038a2080c04048010540c90340c8000044482c031101c0d540103c450001011042050301c1514030b410035102505000041044038101400402c0b00c00302401814030000c00014000340c1c5400e60b410702a84c002010105424a540c800326000304242c26450b01f502045505105810030088010400a09501c1440c06103894100c101074886258807a68074141204a07070864090070002580c0ba4490042d0a01c00d405650741d8480384c0c89503200a40001c000354000006110303515164210802900420f5109810850583c0d1400e54403500075002410141c0390b54000785a559484010300710b005001391925449503500d24054070143c00004551f44a4000d000089424021242900d8803034410110914403607440d00c000c44900394070140032002004004000848100c0700185a4003500245900420180b101c18070020308650010f4100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 183505737 1250 183504487 183504499
    0x5150702150108060c090607060e010b03010506010302090306010e130c0306090201090906030305120421031a06070206160204090c0611070e0106020d051c050f04060c0f140306040b0a0909050c 84
    0x503c25400001034071980440c00049a9990300310900000d403082c003c020000b00700d5810442d03019801c030010b40007200d070030310190000d0146403610001582a4022209180d4055100000401210308030002440e0030240d10100d822021800381c440100321304090300f094074030030744a00150b03085580c8041c5a00041c55120f10420403a0709545d80100b15200c0c400880c1c403071a804102240074030041807100f000e45045590900b0b00e40340e1200f4090090030318800780e0030503c0044101d80445041410407202d55540c01041c480c9000ca03042607900c0305291960003660072a544002c0c4000144d140486040a02110340b6980c1c18507041410140c40c2c440742d40c00c01c8003050b400800401070030740c00080216002d1040c0c2031250f07c410300d01c418440072400171071034203d49909090603c03803940d444040b060b024a01910040c0520b4241180944003510010042d20004051058100103200c1c000082e54010b132008001284015181000810040198001444081c0c1d221952801c00108104141c1c07030f8401034480c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 183506987 1250 183505737 183505739
    0x90b160f1404090c0e09090f10110a050d11070f02040f0c0212070311100204030c08070503070306050405010b0405040602032d0f0405030c0a030c023c010903051507021501 75
    0xc10386001d584202d4038160b86841d40c0d84c6441c4e00902d00b132404800060814045803802140441d81c5842496041495004a403111314801c0200e0140214091543c4022440c1020303a8904480690101c0b285c0100c2c681d5960203c1c0d54116110000d04074540144034200381000d1a00422085030003807a00e80706102c0c0b4240803001a10f4011808103501001d41c1e10943e121001407c06541030b40c1026003034025070260590031482e0101070303400303402503901884600e2011900c405185a489100e4015035900d40e02c02c4808000089541e00107075803240c41140007103441c091800c00708040e02e8003a1821078410341c01004000d40b2020385048130b109168030840c0020a0f000503d08408040707805081d543c290032641d0000703800d001d404c208840740c1c0c03074124089803c501c030702d810000c0001d000c0d007070200e108078441e1000c030401c00c0700021102541000302c0540c141171055a2400f03000c0101e003030b184038180180060b00002284e410f04c4540061081e404a54034140341c02d0f0302c000c1c00c10000d50300403003211040d580 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 183508237 1250 183506987 183507017
    0x1091d16051c0c030b0a0e07020723060304060615020706120b0d020d11090f01031704081b0a090c050c060c040b0316020705270a0209100c06090b160f 66
    0x1c168500b50100014100000c240300310013070030074545000c3e04410203003000503450301900c16171403040361183d0960704400c4d00c42c0c0041440c581c0a12140c014416452240c400c90b1a02400070764200b84501800601250f4655540440400007540f81d070140e04282c0c0100100741e001110307644545e0864808100584602c80004e2400c0480480a802094000c00c50f1040110b000440c200e9043c1c0200140040e01d8488000d85226100340400c80d00030502c0010780c84201600c1c0c00340e50544d00c1c0707000039201d10710781e106200c02c04090940d00d0321b1380104030140000740d440a42c1301d01602d10f480c0303503201c030b03038030745215004610b0600e01070005419162b0400c420400020800b0035290030941458840d0a842c250040491801115070400c40d44110554002c41280c0562081450b400c041d41203c0d0007665116960b8408074040d201c542a08502c003000c41d11207491141a200c15110310540c2c0010ba00443c40d2120555403070203e811414011074000d15052894011100307400c44000b500d080315160341100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 183509487 1250 183508237 183508267
    0x42406050a0507230a081b01050f01210b07120e0a02060403021c060507050315030105010602031b0717010902130203071403090a060e0705120601050a0b030601091d1605 74
    0x207a0301810030301c41c0b9041c0c07940008103415000c04d180020021100302c1070841c1020345185d8455518801012070b940c1c032143c92494103019261003048002d0a450142c0c1c60301c446505101c1040961111108501000c0000103e2000726280141010743d21040301c204c0a4100030304980000c403242100d0360101003104c00613a1071004803030030799a043e030313610400740f10108042c00c18004081000f0086d908040400c9640d03a0300c100514450a80d001d1085c0c210b4900f1818942216801e0140300016041000510f8040503031414140b07059216004484070159101c003252442041100c3c00d03081079441c0c81c1b8a10951405d01e901d0040c0c0034040004600d1130030f14000280c0300052841c83d004403144017000040c0c0d20036007849240c10341c90b0403800520900002c229031940300c07500390060500c9007080c031801e20b04c00318001500e203040e075901620030306d41d450801c080d8000035040145260b042000c002004207182c00030090081072035075509a103d07402d00f800d900e60703400c14400b10b141804024080c03000707200000c0fa40c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 183510737 1250 183509487 183509497
    0x60f09151b0a110303130c0b032505040f140301230a09080d050f0103060606031a06070c12030210050705071a060103180b060307050303030c0a1805042406050a05 71
    0x400107081e502d00352201c0070b40703810200b1248081c284c0804002c00030114981e05400c1c070941c0c440c5041801d542c0d141c4c004149507020a6884c00c00015038450070119251b040c1001c0c0c85200024103005003400e607a990034010350089900a001000e008211100e4941070902a2040314088044140b00c512035520001684903001880c0703c85143d01d0b4110f074824000710788115501d030a00003c040c06680f515209e803d100d65428441125914504000080c4d150700c04c0c8125204030703590b0389203140d07102411000c00403284c108a60541e5461614640042d01a145090000c0c43c3c6110350003400c2841400609502100c5000f0550801e10600b00705038800039028620410882c00381c10040390550b200e14004074000e280740450b4025240038109100240805503011034030800f0110100c07598a40c40b14149512408151090411440144a04c5103550b010b039100c1d00582101480f107508466544001030f0540b100000031140d4a25440001e5400c5940d80301d8007405420142084c500e0901c030040010014030507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 183511987 1250 183510737 183510781
    0x7120209040c3515011206080d110d0203070609021305090a032d200f07090510030b0613020d090605251d06040f0e0106080a060b0406030e030705060f0915 68
    0x404c84001450b603009402040c14580e80741000c101540c0c442151942d220091010b02000c504030307001c40c460001002500c27030115030030b66000d1800c000b001d80e41c1d40c01411804404036840a00d06400da0140b29407842454400d400c1d1b98001c00406205007405460005000355820074910f0b40b00c09410a4036036140104030800b2240b0b00040c0c2401910029800a070201003500b1481c05000249686044001580419256500010000e80d04c40e070420340004000742c4070007000d40d041d0b40002612032a0080403200e80c0070311048054505116280c0c1002200c0c442003040316404d40d00d5090044880030b2040310099a04c000e60000e490702c0700004054030702c900b1101550f011a01d0030310500500d0703e41c03800392801401e0f0180300040e0716850300000766414a00340141000a000c9900160581c1e100e405800111100710b80701c80d2406040c0081140070702a4401d6408051008012150020340c080002a00c140c264280030b00e5181052401c141c00d00e26410740160303180340041c040c8078104d00b0303811680c01ba10700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 183513237 1250 183511987 183512011
    0x3090b0405060301061d0a151101051009090c030c0b03010905090a02090a0506030c060403050102120903041406090a03081605100b03151015032406020607120209040c35 74
    0x2041d04595a1003800b46c8658030340209200b00700044030b00c04504040c0300400705c3d4071900809154881294202c03041252001107103001040300b082400c4c2c5030351040303003958003410f02000703413548a49549410708041c0c0d010858004001004000300c0341c1600c1060340018011014004079030617900010244040a00008641d40d552000300d070055800f0000152491005002c0c1d03910340d582c03400c2560003900a200c41074800e48104001a003c8003012084800b610145000620b0240d40312040c004250082c00350140c00014100c008004502a40d01400d518900a0380c2c0052540c4c052a2860811003910007000426050451402159402081c120301c00c010036050455144c0d1a0100c5441ca26033544c40301c1c0e50008240030011910382e0540020b070000e0100e100d2498031001c0e682c0c0728040314599215140042c1c00c0900480d03074007881030007040c418012104000d4100800f07030000030115803c42c81079202007500040d415100078030031046030b044180e0320019602100506200e11030075540041030030740703103507 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 183514487 1250 183513237 183513257
    0x3080f060f100c02041812030207080409060305030703030b010f09140a0e070c03020c0607080406122a020c060f0909091504140c0904051b03010b031002030403090b040506030106 78
    0x303101d90314000d0318140c00030305210303100da4100b50181841c001010164015030900540c03040c011a40c508240c10284c1c8050545a0011110070880003034010700c00848220a007044002244001d90041c0390245000300c0285a40d5216842c1c054203d450510119041c08188841e80c1915030708946500202d440c02c0780301b0465442c10707100113950040d00390444092101e900041c0f06840ba840410911403922035000c8440100480c1e01f00095405030400017081d141040005020341403080c103402e00050b40784c2ca80400c0056158542904440c8142e1742e081c950110103203c0e02c4031680c10840c0c1e5000d6402a902c0b41c7c03030701c4544810821507201b05c040c01e500410fa4040031900d08001040314644484000e804a0103e01306494105c0d0000340d2011441080e11503091a00402c1c903200d00c0c000d01480d8450028152484980340c0c002c031640307100c43c0d501d030301d9540c4481d04641c5480c240408038000c02c0c16100141c1e41c0c500b03850003418485141c0c220401c0c101d4144020721213034442900b05c81c1502c4107418904410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 183515737 1250 183514487 183514489
    0x30e030d030b13020c120d02120109090b0c0901021615030c090b0711061308060601030b0f01090614070c0e01060813050d080408070f1208060402070c1214150703061203080f06 77
    0x11b56150030000a5500000f02021580c595034007400020301c01801e485640d990b20940c01d03007900c09071480039100807000c2010459580e26070b07000b03040225040c019220000c040c08880d6110704500e034051400b14861074406100d456051083c4003c10740729080001040d07003840140c4083d405010b00080a0640c860705464141d52444140c840781c94a0550417030343ca076180d51085440711020b032407039030119040000c03000c8945070444000800f07210603035a129090380360520485548200002400080200700280c00c0494000c0e084030010b0155119550800e51606030300900c900c400a1202a030308121601850004001196035641c60741a0700d01003020b902c8a0a16182c031b8480ca080040802c2c0180740300310100200c1811100101070240c0b64a101a075660061105034807d100c00101905441d82d018860314805c000a144290300030b80d040035141600344407040c40c02c141e40031640d071204000b6040004c01d070f038540200001340c1000c180d4402c0d200d419a801070005030014103e90b500003140340008442d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 183516987 1250 183515737 183515743
    0x1030f06020f0f280c0f06180f0506060102070308030f09031c05040203250302041119021507020106060905040b1516111002030906030411030703030e030d030b13020c 73
    0x81000740d286a0794101c4645000c0b0140c0c05613003481c1c030750b820580481d5282d20520b0003001081d030940e1144d0b144d00144c0d90790640300300e042c61800c90f06a6562441c0c0313042140d1400700061198414401510040d106051251510320000d240030704551110b40c080c030005031044141c0b40c1104038071444095584600c03451900703500540406100c03d0505100c900481e682e681c006078001da001340c082d6a404281c0f1040015440b088550002c002e100313194082006003041c0d88040d040c0c146442080d030601d94000c2c1c00301c1a00d0744114071080140c0c02442c4000b240440d69000e940c000c81303180000c00c1030030714001d005840000c1c0d42c4521403103aa507850b00c4520b9601c4034840d004805a6007030074142d913540ea0415002001c01103030800e031401d00c2611001c0300c180c24282091200440142c004609040302041048000c1d072009100310b03026602501c1302c032840e450421040000d544070380c80d01d02076055040141031804060900702e004040c1001c10760fa0481d19941e80c9802c01d201480800740e6600b01e01480145 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 183518237 1250 183516987 183516997
    0x20c01181a03011e030c14180a090212011a01030b03031e0c0d02071d041a0405010f0e0109030806090c0c07090603021504080d080414060f0601030b1801030f0602 71
    0x1801d24a629164032120200c0d0008505071484049102e0401c1e20190900340c500045000040100310050030500c11b016402da032080ca074000041801080e45101400b4440c4030400740c401814064a407102103003146042d5421401c2450940c008100160030000248400e00142100350706040d500c0e141c0d515141c90a2017220ba5800d20812502c039032600300042442c00d58046e01000002d4061340942148441c404a840001c42e000d81c00e52841402c0c0b4072500824491002c3c1040b9981d20350803515402811025900c2441a070048000140070b4502a0480c02a9411715419180e40d9160008800c0000d0704900480e401450039283c9228695503100d140440c1d1040c2c0d010310416201d031160002c4e80355820381241094034401d48a10f015420780c0e075041580750189000e000c2c4540c00ad0b1820550803485050019400340c090580d0b101c04203802c10001c0c0c1000303000c0d03072803641c18125031041040950301030140701e04000c41079031705500e1100f1446001c0248101808001c1502c4000400340b820700c09550141c070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 183519487 1250 183518237 183518249
    0x70501050712060b040b03010311040209030f01050609070504050d030e01120f0e0708010e070b070305091203070c0f05150715060605040e0106080705030411010908060c0d0501080303040201020c0118 87
    0x4001c1c2000640a08107a150509120800742081008540403109905070750490b032180c04075504503400c540d9040401000c03c0c614a800a03400d201029130340d5003c0100c4078080100c6000005e003814404240100080000d004030b0501c501007000300078a8484002c181080c0750540307401c1c0301a082400c0100c540c03208805440c07642ea800e1101105d02820583d00076001c02c100d20088941c0e0743d6842410500b640c02040b40c002c055003218a042200240c154001e00d0b8030340c841e00c1c2540c81c180b4001c001580c101c41404c0c03491625400890314004121000003003101030400001403009641c9000c000075890000701180a0101801140080c00c2255060b004103094483c40310a0000c540c450b100284190003603c01c0c44643d948640000646901400c940c6015103282c2c0d03075051565030355844142c68050001e48080c100300044200007007040090080380e02469026260030f540c0d0f00c486004005441041e048010190004c005100050ba00002c2d1300c04990307030a0070402d14000c0380e080070318001d450341c0d8050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 183520737 1250 183519487 183519491
    0x12060e0709020d020406020f0a0309060c0809040501030614090a0c150905040207120206071706010f121b03110306030303040b0c0d06180606030e0705090919050a0c300602070501 78
    0x343c40c03e60054002c1c0060360b07456802c40322016030f0340d842c076650344a2240b4050040341e0540c4050016a01c1600080b2246000e071b03c03042d1030004418046401c50700268425601c956441817014000607000004030340007009103006150183c04d0381c9850001442c1031050000310b18900e01541c1807140906210401040020011911f03200b05081404101405019020050180100091560b4004c00c503c5c82600381c1003184171659990300c00103403805000000c00c0d1051005201c20212104107500519240c400c402c403041000550b99440a030688404290040c4c62041c00c0c1708018075601c00006803503000d6000300c8400c400e80c988041e282c0702c0d440303204140000300382813081c0401c1c101c9000500082100490404101e082e070f895908408075683d884014040707811582007000700d8039020500c0c40e01700008030141c400489541101c1108201500030840c1c0c0340d00800d19200601c8031852048005000e0080854403520115000d80110000100c0490204501010b07102c01d0206030760565005690102c02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 183521987 1250 183520737 183520747
    0xc010609091a10030c121106030a1b0201090b0613182609090609040503190210050f010605040909060605180a0b031c051b06011e0f12060e070902 64
    0xc100480c0b0398841c8401e21401c290000300710040010203c480031039405c200d03c0c444650400d0f001d4004000b4090090320f600ba071401d0100d141e95158001140a16901180003a492122240e09120203018814800c2564541004070f004505585c00350340e88aa42100c031041030705205100b860003000c8c0c0c800d524204c02d490401c00400c004220f060b003000700318001559201c0c1d0800d05205102d038443e24200d142c000000002043c1e05041c4050b00d550450300c28402e590901d4a14222011203480340c866510041c1e1081c0185c0d94001024407800760010312003007801c1401d60400401134010b01c614421895003a81d6002c0d24403c0c00115805080600802040000d042119102d25030a01e01d0039600e000c22545002d140030b00e07520340014020078885d401d8111880821140710151015009064042420580d0300e16442280009003e114060104104800d4100603a00c1c44014441e8079074210f444555030701d140a22102025407115071070168000d1020400c48041503801d0704080480c0d10000c643da0000c91 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 183523237 1250 183521987 183521993
    0x615030503070b0907050406060903020d0c08030307090323060c032d1806040308070e040f02030108030c07140d02040207110909030c0d141209031e0304060c0c0b0a020c01060909 78
    0x100712400381300020221950340c0c0d158020401140d11030702c0b07414085103240208000504007000f10075503080c0250240c0c01416902d04840c0c4c11503000b150b0300400106034050078420004c140c07082400c9490101c2c40500700103214042556079038001f403c5c0d1808460040002060755898048d1104902404030703c000da00107441010b81c52400040e6007203c12080c0c40c4900400301b070000140ba61146ea0943d4506d070349034513004001d8400c42c808091094100f6100c1d04003111200260005500071b1907140000c580d80c07106112801c0c200a2550084c03544030000c541e420f00d0990f10200d1011400341c0440b070051382e0721180e1900c0c1030074a481c0d020550300030701d000c0108440c00e07074044064001d00741c05805490400401c2402141c0b01c45629204150031074052004591040c0740c1d82113140d0090949003101e29007041c0102107031003d00316181c2ca004c0e480000080000f080300b2402181000e600b541080d4080c0a101c5e9981c070320b42e8400401c86051144d01080d1202700c5082501b28400600004008024403040340c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 183524487 1250 183523237 183523253
    0x1051b0a1109010501050310090c030623040b100c03050a0e0907021e0706050318030906040311030115080303060108040302210705060c03090d0503040c0f0b07260403061503050307 79
    0x141c1c21072007007484800004240d40036804491042601012002d022428000202c005042100c4140c04056494030085002c0d1a0982c00398100c1000301001c0841072003110400007a1040b011a09004220040711f50000e9030700103042c1d0366625414240b66489400344032040382c090400031405076201c00c2550521180030f40202c2d014000d00b0840f80c840c9082e03402a01210340c1ca655608c5500c0c0000c50030400207400c040c03404050100a0814800d41e49001d4100340018001c0d0010b42058500840d0088031070124030b024840c501900c0f004424040701303107203440b05c80b030344a00005200304d05215240000404240c401e120303000a814031718456001e08040451842d056130030402003140c0c42d10610011699561080301660f1080c0700080040415080030780d0201c90580000c6d00403a0440c460000100345009401c0038007014104d40142c1949800303d508200714203c00b403000210360b800725801a0321001024004031000d83e90404000325044100b11428000780f410350b0b00c090614003020a400d13041050003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 183525737 1250 183524487 183524513
    0x213030809011205060d0f020307031b1d130f061b200a110d0501060b1603020d030618020f09030d020c09090c01050a120213080f0706050c060601051b0a 67
    0xc0e603071004107903e0154200100e81e820b4a41d10741c00071407a01c0c81070001d507090301e081d01e01510103000e072a0750316074954441c18001e03505400b04a120b01c0d4054140001d0420401110f0003001c88a0050300b0ba00b42003000034607140d0a15000381501500d2300404042c8110760308a68000d028450f16030350b00c01c2030106d004008110180780c100c0303940294620b0b10550000020046482600070784071036420419030040240314826250215407554880000240014075a805402d4803090501132844d140c0f91031400900700001e03c1e00035024036241000900a103841075488003aa80c8600c40016568160b0a482910f14010544481c0d4140300f9624240e0481d40e010400ca50014002d40340b004158407044070305919030300c0401e441d5000a0040c0034500d8240c0c400c4041d00b0203981d0303400c00149083e500205c0317580c1c008010f8010344655842103000f1408244108812001098035207420740c1049505007035162034150141140c1d04020000c1604032044039000b0552443c00d40b8442241d50007405031826000341114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 183526987 1250 183525737 183525739
    0x60c080702130c0311040308030a1509050c0301030312052502010609150305011b02061302121005070f030603020a030b0a060b0c06040309051503130c1d0a0f020715020d0213030809 79
    0x5c00d54801110303d8035000341c5065a42c800c0c280d90070750390b4045d031410080046003075004900103000f500242c001ca09120b054010b0b02204015030f625810350070081c2070854001c045190380792900c400c015801a03041404080c4403010101c000b800e00310b64800300d0140c01c00b6048200e07150714000c210310f040100028898101c4e441440280724480d400344610807d0400191083d001d0b0f001400001c900307009201940310001c0c4003e00314000c3e452900a0189000010b0042ca0005c5070780394207000d4601d80000527444100300744c0c5024030803c0d05582c086940810544001040c003003a130000f0940e885000e400a80142042132803560311018400381050f910081078078241c02190f100d4102140c50308008005a08420300c094000e03182d5200c2403007203482d0981d1004251115550090089203e0f20000c1e094500d14528600440a50414203100021626000c00d0340024070301c10000340d000908001100d03e503010482c800140caa0b034a144509010b4400c040050000011201001c0204051a00500b040f610 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 183528237 1250 183526987 183526991
    0x3010602210421120f0203120a02041805090105180a0303020f0d021c11090109050607030c05010f02040501020c06040f0315020c070e070e09190b01020f0a0605010501020d020d0801060c080702130c03 87
    0x401300706032104418825030600680041000c00c3c485012000c1d0980c00060709100107150035a6640700c070340c2951907603000e100425164403e201c2048000d01582d40c0080c1d1444c46000100112110a44c2e1002440d4004041c180c011440c10000107a100550fa8107a000110540d0703038035046800c51492101c60a00700840301e29110f15080c000c002c6c201568041001038440f241c03030506200070048103800080b4110100030700c0d8424180090350a00604034070140001000d600e4504040000e0308116541c503e050107401d0500040001490420700c900032a5000641100f800e11a421540064402c003e000c0215205114002170001074524526114a1035a6904800c2c10b01d88000c1280401c000c0d20b203030201d2550700310b8091054249038007641501c607050049407500101c942080b403c0292440007690996610401000300e944c0512015000c10b48620281c402c0041c00640503003901e03811301070f4404004114136001c0400910008583c945034000782141140c20350014020081c142d12007807140024 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 183529487 1250 183528237 183528263
    0x504111b2505010801091d12031902030f0708040c120f060f09110114091f020601060f080708070c0204050406050105010306121e030c020a0308040509070503010602210421 75
    0x68528200081540e0b8160358801c066480c10f80c01c000074141c0102108562240d00e1640c00707054a0030000301c1841c80c0510100c9850745810b50780f150f80340d1501c005103903019004100300400f501071030080701d900134002d0034000c150781c903a800d11050220054200781d00f61500c1c1c09120042c4440e2646804841d4842c01090250300002ea212a084d14690103000300f80804862142c951580038581c0c1d98910494940740c1818001d03900c00190b2880d849400700d200e00c22001e198840342076418003820b80500064101000785d8590f1481c024004c1400622ba00e04000620340070580c010b1190150b80d88440d0010301c2882542000d0902da00208400c0c03003060b010a1400c1d100160104914002880c95900450106041d20103001c2d0191104002e43d8210200300210360050010703a02d04285030051801450850344403800e00c000d102c00380102504800604c0414001001107a500183c034100d4024100e594504143e850b20310104a030103540c015415947c8814183e80041c01e60600c40c0d0000c1f80a251828144 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 183530737 1250 183529487 183529543
    0xd0503030a1b020316170a030209091605030103111804031707110706110a24060605040b0306060705010e1e120f0a110a020d03050702090a0606090504111b 68
    0x4014000b0350241c1c006000007664100d00740e0a201c180360089074945012145000300304035541c400c40070f040c0882e83c0803d1008503803c00141081d0301800c1001e14500c060500070001d45580030510005055150301405100b494070b4150050712140482015a56141850300e00036200c00002160282140d91a60002d106107200b40308408420801030041d144150805108903003100d0490310070902842414181400070352602c0701c0665105c0e0780c00340e003442c00007058400810746074254003400400400344810721900f103999013200e030000411501540d40f00c8031413070007034013400120800207454020400464002e184000b05c4040380b196400c1034400c00c4d4803402c0048200e0207044c0904511410603c00080360130f001e02207a809010b03000c0b00322010602581e0010b0440c50102d6402c030000342e404101c0f8021030820100706608035108080c20300030300e4280707040100000c59911a0170f00c5140c44009140c540f03640c82c0101d4094030384210900001d60290407500741d4402c246003030144000c450380b41e01160 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 183531987 1250 183530737 183530771
    0x1707080601090905061b18120f07030510021c020a1209060614090c07022101060b04052706041806020705030918010e04020f1201021c0c030603030504030f050307020d0503030a 77
    0x700d40303146d03a45828102624280d4a1408400859035041520350444c4000c1181c1045001401041c080040c00040e0861901034101340360055506a40382c01840754140ca010202040510b100340144011385903141c0340000c80d03007103451081a0f06441c0c03070441a8818010300743c1003e4184c401039100c022081851406000414004442d0072171411814440800141740522188140c2c004036a05003140d10441d10f480703421640c3c1607002e100d016000160801c00b03030401c0d09941520640c0c03c2c40d8041c03032a206400c0d50805100050055200300e075203100310340004070081404004540c110314115150341c1705203011079503a8400200e0610826804d0499980d4441c82e01c40d10b8185c034006007914030780c0e489036820f014050384008031241c2d00401c46404031002401c01d202402c188405c4140507840c0290541e075441c00c032450314004804040c1402018008650002e0489040300d45c41000303620f05085c00c3c2482ca0a502400320002d500c0001c040b80700307003404400009103000b40e20034841045500c1000c000c201c6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 183533237 1250 183531987 183532021
    0x30c090807050904080a11030f04030210140d0e100e0303090c09041203020d020f03130309051906050d02120c2101180510051207030515010b0301170708060109090506 73
    0x1038040070303100c000380004171020f01605401c1c240e400c0541070104d1190141d0706682116040020054001c030703041095240243e4005040c25660a008045024000801c00c1d1403290710016038959444401005294038100007581e884202d40600308114603040003102d46a40c8241c4141e2105e1060018004552401c0c5800ca80034641c00700c0180c690482c0c48030254040c1d000001c031a801c141d403d0000034400b660f8840214404c00c50601c2d2120040c3c51450058100314a6800240c0075280c20041091504020500f5805441c2141090313600e458085465401911030034082115010488c0280f010344c5840c2006072101c0140b00340b50362100c1d0400354020803900d1092082000c0c50201c44003400310114180c4c041500440d0101e44210150f4071400801c038002850141c0d80200ea002240403c00d1000c00e000c02106441d2804081130705501d00302140d00140418002c2c00106d0100c12141c1540a000b0801c0f4001898050240e421669642c4100300c020b045500e001c0d6224020b100010703611101d6007202c84 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 183534487 1250 183533237 183533239
    0x100e0303090c0904260a1209020f120304030c030c0e09010b090609130c0e070f08061818010609021e09010903060509010207050105010b280912061803030c09080705 72
    0x10038880801801c00c00d80500180040e20300c52043e40744402c5404071143c025012038003880000f5030340d070309241009080c181840401f181052030400690b0050740e4003d0313542c03841d0400f22036620401c044c404045065105552004051000c3d0150001c1080200a81c40085880b091140d010030340e540038406082e43c0040d8066a07108a0780c00000b8400d117055410b10b9004801c0646500754075003d66034050180009030000540008000308002c0c031103900c406d242c104441185802c2d407007800c0203808904007440c1404100c04a4085070b001a01c02d1150300600e00c1d10080360002840550303613a0181200a511005c07d507924034414013842d1f4007103108101150001001039490b008070ba45151901401480c02620103c820b5400b00300d4a40401e41c00d025050207048504203259650302e81c80d0a6030750105031001041441c0000340052540d541d0003c0c520b0003101e5013240003208505051400784010f0807002104100d1581c0e41101c06c0515500d64488210701c21035842d603508241d11544020f40c1e40409225907 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 183535737 1250 183534487 183534493
    0x8010b0102190312060810090501050a06050d12050c06040c150f02060f09100f0b0a09060503070e090316152a0c0f3905090403050a110708100e030309 66
    0x500003e44510641c40b9059a62800014029201d591090034503800ca00702c0c401c6591150501818080c007171041c0c60300080c04500030000e20b443c00380441c030405900b020140003a9005040070740314600807030860340064660000d0310700a103402e14140000415500500c032441d81c4c2c0410300b03042140180040170010513160002c114907034605600c18030881005000201e64000c80c25903003009641401284407504203410007203101045a01449440b0103550701800b0200c3c1481c208008640300820b0b03a0040e6140c0c030344402155616010600d14502c1072154031041004204815402c4c412030b800ca20320401c06000080c00800354441610b42156150301c0d070141e13030107001492001818016004000d441303104406582000080342c5842c1c084480b4a0325803801d44000f5000c81350700e42200050100742e185603c180b90a0181013001041d0303403100c014002400d000c800240301504a004200c7c10300e8004000c011904c0e003a440e409042c0d15012070b00040448a41012000c00143d0004000e80707100d00002401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 183536987 1250 183535737 183535783
    0x60903030f15030c03100c020c1c08070f0b010b09030c1002070501050d0e0d050702130c0f05090409150f0e07030206070f03050f0a0302182e03020d050f0108010b0102 73
    0x580002c115031805500da2522408182da06940c6040c080400d4402240c1000221510b007140041e040c040018002842035104038030241881c0c0412500500c5d01d504940029200c030382c0c0d845c2440700d20510b000081c00d04c0444000003e01d90502d10002d201c1c48800341c00703980103d00c0001c10310000f00395004031000540c0000e142030000b0b501c180050700b1820020800404d20000001c210360900b000100340500140300000c600302503007406c00d440d03a00410312031000c00c000001944000c0041401e682020200640092008070b290b075190010400c035500700d801d014203090000803007802849440e28103c40c40341000511003600c0300116402d022203801510300f914110003a0303100c51401c019410b040381440024043e06600320500b070042d014910180e01c00603690791514030001340c0c0d002c50160300c078400e18944070751301000344a2030f200d9401c0000030202280e11000004041d8060700800104002c454900420401800ba5008409040f501c080008211013075452004a890700450704039001c0e142c03c0015 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 183538237 1250 183536987 183537001
    0x170d1404110906010302070212010c02061006090504020f0405040c0f0809070522021204030504030203161203210c0e3a021503041a010b0922060b120108060903030f 72
    0x1030030943c810014900107161444a50000350031328003a1414204a03956001c1081400d034040140941002c0f00c6402078000c0e41ca0b0140060514805004a6000da500400d2400410503c20141c801401e40184207019400118400412094010034581c0004018201182c0c000d50003196500c2a504045c14241c1d40010915030481d00b001000355549142c1c0c2d080107800c90104080b0360b00f600603482a9111503a6900e18010145014211031050725411440501001405041d4000d60049903160078030003002e0002d00301031a031000d810f5140414850802c03242d51840c96224800f000c0d9108211503030000c5000e4180c03491800740880031401c82071030300c12000e160410441002c1d10010351004060f5112a043e41c188012a90010707901244c406414101018100440305002405801c2c80c02c50203090501c4000003034041d0312101c0c0c03007040c04441030000d40703000705050b000300b000381820002190762525412b0040c1d5040601f449074218600031500800c0010300044200c034010805514102c0d17460716000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 183539487 1250 183538237 183538249
    0x408030405220e0307030e09010f030b0403022e1b08071803050d110d0201090803010b0703020c040606050a11010504020a15020c030f0c0307060804050601060e0d170d140411 76
    0x803902880e1511081c01030000b10050140000f05070280300519140c0000d450007501d541d9840400c54403806200300180001908100e40c44c0440b9000842418261035070f084c01d80c2007148511881e41d0b000c41000d2000070f411584400c040941007240c4082120303102c1d01564444244020382000300180c18000801e0185201c2c00c5030f0703245441000c21101607030380e41c2c0e500c2c14501100c3c01e801c4008100308a0000e07100303540c28049042c05640d240000d0050041a90350a20f042c80140155601d00390302050140074175100308090b0031919005801000b5890716058040c205070041c100d50400038031014482003154806000d064011507028181c4a44036040c08282e025851102d04650114420340186e803690f0358041211020312008031002d0812110f4107000c0c142012820781207142407103801c03014400050b1002945504591045c42d1002520034200000303014000c01c294060080340034000b4040c0b010b80c580006040030a40050100f20f00014401c04c5e00308450115005090690301000504144c1040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 183540737 1250 183539487 183539509
    0x6080408220e010806060a080312010b130e0c0304020306010b1315171503011d03030a05070c0b04080c0106060e010509040c0210021303110f0d1209030b0a0c030b01050408030405 78
    0x44924006041d4892504030b46800003680724140c81e40c04181441102e01740f50044c0800303819003001462038030500d0403a04000d80d0b03041c4a203040d8540e00043d0380440c6a240c0008101400004c00b0342046401c02107100000c5030820f43e403d91003030140070000074030a0b04207012100c211104514001c521894030703214080b840e441e1082c04040c004454000e541d55821400102d105040003a803201744c07510b54009060840d03c1c030b0802201c03144000c400c03048140c00000281d17030340104e003100b0110740d42d40c60071421100010311140013441003007958140004c01c20030070b0103406021000340007000400d0340c8a00c1200d8405003810070320302081c0704200c1141c01c5d0070b003a04440c44d041c040380102d5450100c00c43c004c8040b83d0000454119050f00b2890610400c206800d0305000008200da010b4058080c9400003038a00d64100401007181d201e042c416140390b401004560011034010390710b910a81b4003100040081d0200c1c00388500064501515103180d0740c0500c043e02d003602e41010085084c80d007020184508a545 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 183541987 1250 183540737 183540787
    0x706120207061410150e190803040b0a12140f090c0a08010b0f0301020f2b09030f0e010c12030f0e0307060b1903080a0f031d010b0a06080408 62
    0x800c0309401040190003460115280f282c2d80341c0580ca0714a00c0385000004a03000913101d41d4840200e81310060744a941c44e00c1c9140110350100c01c8460718002e41a00b202c0503440002c03d408003080008100c1c100b50068100c0001a451f48000c001e0080d0080c41140c2c021690610310480074004a824005907026455128004808a070b540e02200400204c49200a074840301003a034417070410406a04250300300200c1100c2c240c1c0250306040c0155000c030047e00419541c1e0852000d01c814034035000100c10300d082101c000d0044204883c3c1d40d40d0400500005401c9401404601c0c0310078041d026502c120040f0350020303004070356000e803030040800840103481c2e0b81080039000354407101c3d8448105018401050811712888002920390340110074404400b0701440d1313100202e41500c2013000413a40c03041c100c0c3c1040c04140350203220984000c0065006008111640c040f400070308030751a207a07150540c001502c0103003c5542e0084156620070032582c03103200301c400404c03c100c14040000010300310300715503a400700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 183543237 1250 183541987 183541991
    0x7051e0124090c09080601050111120703090510051903050723040602060f0c070609080f0c010603021203160f020d02180601090b0a05090d02010e030709020705160503070612 76
    0x40301504075220038810720000700a80003035610402482540d031044548940c01803c28030f042c0c6181c20b050303a071501c205110316414400103461075070300e00d05d040c021a41e205102006880c0c80760141c0c240202008014041d40d801121800c03c0060107500440c04d4840136030041c0d1104408250142040300500070140605003070021415660444070444070034510b000074202611920b1354035004000b498600050180c0d00030f12404024090070a070f0420403500341580141f00491071404518190050344540824900c81c40c1d0040380882100006401c65800c40e80225000e640034010900c1c86600c030320501e82c08170280c103c1c250070580010300952605e40c18500003001480900025000305154206204500790000382040c100015580c1015004018228010f81d1030b050410402010303189124403d03406101d0790004900c1411a0f20480ba00c00038090058251003415560b60400d10280d04a90411511801040410b85440030500c51110441d90000e00515640e0f192070025a4504c1c00f407051105d4981d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 183544487 1250 183543237 183543251
    0xf0303040b071b0905010302030a08030712050a0e06160e0f040902030102030c12010e06090a02090409020310060513050c0405220c110c0d080d0b032103040309090207051e01 76
    0x24000310203449043d01030b24040c64554042c040c0091903000c07540095145510b804014000350700c0c0094100341c01c1d43d01c208501d0752512140c00030303034108140e4581c02440e05d00300710400c03030009415040320448148032011100c5640701e41c8038900301d50107080301c9600042e4915000e10a140741c1003100c0c0d1000704c0064400903085c0d8041d0040b03401d80e4000c0343c00c15088a400541e5000848207040460b004052541e02200241072080005004160181c031803800b154020a8590056840b83c2c445481d40d640201154070042d030310403910000c0d0100c1d101701486001c10304031200300043c59001d03241c451900004520316050900302001454211039140515848038010795400c1d800b00c0d0f208264400c0815141ca610001505102c41e00e000c1034100050301607032240c00417400141c407440aa403c407074900c01c80407526140140c08617280a101c0c405880741c03480302081203515a0014001180154000d50300c00c114a80c8910703481c030030b034807030680300400c03c1d8054000d1240310880c200c11350703000300f0014002007410 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 183545737 1250 183544487 183544499
    0x5060f090f04020409020705060907030f0803060f03061f0504090f1218120b01050103150303030e03120a020a020c190504020d061d0108010b01020f060402060c12031f09060e060f030304 81
    0x207810a4222a082c2940007c103042840000c000d15640500d440004220540c1541d07107400020544000060140b0008000304200396214440d030b840440016040f218245040c1070300030141001180c0120841350540c4001c151400d080c001d640c00d9641018801c68007440796a41c10000380404d04c508410400080d103020004a01e00940d0701c0140071221010b02c81c1c0040381002e0072140b0061b84443d040c98940154042d4440800340e00504072501810002880403041e8541ea065214400d2a622440344a1040003400c5030719a000e004610856401c030b41c464081b01041c404620745038100346001e41e800500030446840d140c4c000304070b0403e1040010800b99030310f02004420a040b9200030310318010140050102c2d04c024440c1d800500c10920007002480501c030341e42515407401600c0070380180340c0011840500102007024101c0c82000b00358680e0b0702d1901300da112401ca40300f00c03840042a0403c402c00030301b440c0540194420f48018105080349501c40504001000700f41c00070464140c0024000002c00b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 183546987 1250 183545737 183545741
    0x150c0c030927010b030f0412020708030a0201020c011802132d020304050d031109060d090b01030515070503190507210c03060503030f041a040e0103031707080105060f090f04 76
    0x1862840700d00d002d000c95000e02e001291244142c111908580d000d1081004100c00c0307440c0550883c0e04020300e22078000e60000c08030308240b4079810081091000099068090340d05600804d55070f241d480c020004011303521008503500c40001d801a40c4200b901e030240e441800325511900c81402003d0030444801c0d010f0001030103d07a410752011035403c2e8081b00f0001882070a11401c100081e992030100b0440c41c41101c01c403114000c101d81e040c00740e4804500b540c03e418a651140c8901c0b0b402c04012100c940c3d4900d405507449c200005039040220100000c500018041c2c0305890142d41e03042d012681d02d018003042c010090100805440802910107068521041c0c04101c0b036440003d03d40000c550010355000150035034441d60310a9010380d0003000303900004072201040d9403d41c7c01c0c81d0b8220011407180c00c07001071280960740104010701c1c5003400000405411480091307414501004410700c50303a03215426220844244a840d410004c00c100c0c054900704400d0041040c0140185a004405aa02c0100c0c0c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 183548237 1250 183546987 183547009
    0x2010e0a0c080f070803180406050406030516061106040b0c13030302010e1b0303070b07110102120f0c07050606102d1103070302150a0b04020712030b03150c0c0309 72
    0x7250014504103000e858410702089240428034001002000d140440c041d98078418007840c0f041250340c02145071101c0d0b40d241c10400040c10014418003103180c03241403180e121040c032210042c00410421001850a01841c0c82c2e45103000d079000602003680d13407500c500c1200c00300180792210b0003404009500d040d403030b603036110301c0518041e500010b02c4402c13001d03695191001002c0e0080700c40c6111900001b840e40c00004072458135038800226616510740c0300054030b107040070380d54260705540045403400508500d2400300e885081c100032102d1150300d840700d0f102c000e441821800390083c3c100c20b000400d5401d21920f0b40300c0101251811040d2854100a0044541800b241c458010500118071100455004800c1182481c900014629045059801035030300e0310380038020b1500c1540d20001903012152030f0b0040d4200b00000c2c1081d9681e41d081c1c90300f164903080004250003c2840c24a000e4000e0500144030036074180100c1650085484d0002680141e802010318048544030801522003140c4441003110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 183549487 1250 183548237 183548243
    0x2060d11070f0501052211011404060507031b0b07080711030408010b0a0503010501150c0f08040602100e07060f080402060d090305030a0f050705092205010f0807080c0d08030702010e0a 81
    0x400494035500c3c000d402d4035070140c0038175000841c11a0540003400c0042c0d06440c400e5212030005201282d00005075081c07120245201429400860f000440030341081c020040e01c0c0c0700b5130711900c80c7c0341c0a1121201c4041c60020141c0b0661300c0c1c000082c0300500842c042d5810403154180280c803c43ca15841920b158040d0b000808942d45913076840d800c5d400c0a0002c20042c090807030081c0704075810049050000c020303450910701000245001c2400784101e1045404210350060b503825619529014061368414030107000503000c91401420000d041000f1070182d055514607903c446807900e241e0700442d000e800150003664000000c001d0052610395500c202092184a5203c1c0b42d100d1821201890498000406d190004c5040c50304202c1c045a1290448a841c50222081c229034004c407039030300080e0714501c1c4485010354075041c00460f44c038604e500d0103401c460f4105c045440315a01c0e500c1071900e900000000907044440c86d481c100000d202c690156520040c82c2c400061828206600503103007000d000815 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 183550737 1250 183549487 183549503
    0xc050a0b090f07050f012705030105040804060e010f09090f02040905090604120c0201022e11030613020c060f040203100504120f080717102d0608100302060d1107 71
    0x200c0c01410103000c19802444121080d290f0f00040d1720002e01654800c40802400780400da50128180e1649041d21010b0107010b00200b1135403601d4580010030740d01a004100116410195180d01c070361003011226170141c941d42c0d8622000345417403100005846007140003407500d6001c0c4400f007190041031040c80e100c1e01d020001080281424140184025041800303513040100c0e460148015036000240d00820030760001d000412414002d4100f04100780704241301401d10708000d003292070310081e04c0141d402860211764003000c8907654859001248544000042240c0014000880380c4c407502441c158464000b80030344952446503540300c0c046941c1101c0071a4100c240c246280c44042c0e018400c0190384403241401034503402c00038009030030b604054144503000c03155040003a01c210030f04441c0d01c00414401c08103600105032414521010240703c0002817500712114400603c0c20322a019481c01003235264405a00f690440d001c0c000319502c100f2101b10307c15194026234844a18150041041c1c0d0700030112 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 183551987 1250 183550737 183550753
    0xb0f04060305220305090409060c02010c2c060c07030807030206010e0f04050a020409031b030e1002010507200c0a060305060405010801050601020c0918030406050703121104060c050a0b09 82
    0x160480308090807504030310a983c83d910b0030140c202140220301c00c1d01400d21940b20a00b24000030080c0101920081c00c05061102181e45540c054200b40400740e0152500e481d103051200c0b0043c0034409001e245c1c507030340715003409810560070300d40b00401c140008501904d40b50b5481e0344856402d94820401140142d001c0b800400440104da0b8125822074449490801982840e48a0b40d0783d4200c4c006000e0700c1280e40340080000c0500881900302c1aa520301c07084201a401400c018040145a1b50442e0081d4000800d05000900c103101b200d200d40c0c0607840e0856200855a0010820801116402c0d17242c407402c458400c86545210500c0010b00703040ea000301d56440c024041c03106542042c0c0c051540c41e030600c407d0240b6683c02040024420005503454505070340c4100d80c036008048542d58160003800700050110355031380c0c0301000302086806603d07401311624001040a00322003001100c04060041400180181e138411000d0320388a0340600101e42d861001030715944100101910000115840000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 183553237 1250 183551987 183551999
    0x60911030303091507031503032619050f040c06080a060806010b03091504020319050109080a0509011803030c030c0302102406030501140f010c200414040201020a06020c03040b0f04 79
    0x13007040e500c5103241c6818000c814044d01c80d08403082c10b6020050034060b0340511041d410300345001e02000e42ea140c00610010381806442d00c18103400101c40e0007100c2e0300f00400102040b110803415030003294400c500385801031807c081180eaa040142071200c00544440c0d0008511004001c0c09019008a901c40f039540d090030040a481e03c2c1800300c0541c030b181180010000580c0d80412580c1e40d06e0740c88401b5150490141c80e110340100907030600100b1200c004104240c4095000000e00042c200a0300c0e80a1011a007149210854402c0d1000500180884084400091103a40e1031800c00d40300b40110303040000c61040b05400c0c0e51014003583d941214264045e040c0386100d584100051003241003c20141d414020454140540c1e900228050001c1000144c62640708282e9194401d8200440e48500c0246040c800b6104c4400740c0d81512650a082002422040c03010030240030b0342e4160001c003045c001d940e9914000c2c2d00031307030706480c01030005000c0050311050210050100280310494942d803182019 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 183554487 1250 183553237 183553273
    0x8072a0f060809280803090703060510080d0c020d0f0f1b050102071412060712050a020f030f070908030d14100807212001031a030a06091103030309 65
    0xe4400810000501c0038480b4200022800d14010049103541c2c000c102c20f00b01049a160320482c1000306810345c00810400c0c2004c010403810203a92240b641804961502180101e160869000e0202c0b55000b403908483c1c102d018500c5181072910141c0441550b81e1203071200c000b000229001030303864034000c1025404001840541e6510080120418203400e0b08080000703640f51000e000d400c0380d0500c00c02c600040ca9849025402120805034102d585510b030400c3c00525846400c1a040706103410400450180c3e1a00d0080c0e58107652030031125070440d42c40b01c1c504070403281c000d0a10320611503080300107e0400f030300740000e04030b00110020104080614510443e038040c0f009100440c045850784051102c10780210b81882200d0710310900e40704602c00c4502aa0080c280e034807009000b0303440301c01c0c04000f40e034840c0400300c280316003603c04200d0b244a0314290312211203030078911949908186441070015125038001d16510740200c002900ba11b1100307001c6803643c2e0003a2443d4040754003c0344140040d017802 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 183555737 1250 183554487 183554489
    0x3150218011806110717030403060f0204150302090a08070b130e01051c060608011a0306150f0409030e04050f010e070c020109030b150406030b090709020309060408072a0f 75
    0x703181542000111400c41c00e210b0300700c1d0080004002803e070030b055039028100403020140c502012517958845070300103856500e51240c80102c51040c117010030745810104a10903902182c8201400c2c004005c00001c084009500c583d4009900540b054000b00d00000700708541400b9202c03042d410fa9413600c6a2400f80d0000c2d043d540011181701d0010014001c175110072219203d0803c2ca52040035000303c807440e041019080a810002031986003000c2c5c500201041b001a2001b00713030503015207080b51100c61056003d40d800c805155041540b800701ca280c2400c0a51100340304502910703194055035006000141526410313510300c0025504480144801c030241e2504581040982c1062210711801d540080c205c2c072164480901004180c400240d6501c00d8080d0390080c1003001401003101c07179203070325000030035010030740d11040184240034000c9000c5525100712400b074516207009001c159a02d40e901182c544c4043c000301c0c0c10600d0a0030050004c0341c0e400c0704004000d10344125288a50401c1302c181080001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 183556987 1250 183555737 183555739
    0x150b0109050f060a110f0f070e0114010f1d0d0c0905070816050306040608060403080a0b011803020f010509090a23040308070c0201141c0501080307150b010903150218 73
    0xa000b8600090f5a41c01003181c50000c41c5041c40381c1c5444100040074207002c2990086140c901440080602040c000301d01c210564100130980301880e40c0300c4941b011054104071441d0b01281c881d0180121103801030303e40c89183c41842c0d0700090180700301c00c08500c0e00060b80e031045606048ae00c80a101101060083c280d20050358900b400c414940301d90720071410480d64486034244000040401c079540c50301d40050f405031803440304a9203682000e00d8010160b950486980300014138000d51011198843c92200002207501454112903a003140c082200314840c0820f41c0303040c00020410000d56445440c442e0303200e4600c40b83c0000d1b2140241c590046601c0c00560f5a00c4c0321000f02e020000080d4001c0d69542d0000f0042c9415132140005100580e03048819441d1080700b0700021540300d00ea2042d9017543e031503015071510280701c00c0c0d0b0303039680c420b60703e00503404000d000b08064040b501840300340303920020743d0714414541510360741e543e0384625000040c034605c01810700c1c0d00080c209400d01c50b40c5d88084500c0c40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 183558237 1250 183556987 183556999
    0x3020a0c23190c09090201120504020d0804030f0212010605060d0e070510110d0302030601050d0b01030e030d02071a010b040b1813060603150503030306042307180602070305070501030c0c150b010905 87
    0x5e400d0f40028000640141076080059450303010900350b40721030607031212003070f800300e080d40d42c40341c8034104000440010356007207120f0202015071135524881030260704200c84002d0a42801d084801950f2809001c8140500b40144035030400050b00c1da6400c1000f400c1c0c0c07078040d181c1c007101e28000b41e001800c1c02c000c860048207040c0104180612a40d00c1422507107000d4424500040900700329004034042c1841d9102c01039981320104902c42c00d8103047d401411800e12407540c01c0c0d5020354000b5008041340091283d451021006e120420400d0380e03802c02013046101d0390100c44545200d801c0001d842400500700008001d03528001806800d03014032500ba5502144401f41c034250345000300080c0e880c0320051011b406503465103a00019020000384940304c10110311900b09003850110700040c01ca00300c10fa2085041e000c9003130300180c00c900120f0108180c0c2d4114029144040c200741c01540035010500000040003410902d40012400c4d0203440d91000308000400b1032400701f508001000b14000c3c0d00802c2c8124 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 183559487 1250 183558237 183558251
    0x1508070f0803040b0906070b040311160308071b1805070f11070312022a010e09040309061b0803040b1005040b0607021003140901060e0703020a0c23190c09 68
    0x140000169022203c2c020300381c45c0d6603001d5001280107801006c07401008900d441c0c0500080607003100001034030030001800c64001c1d0b11840c0c0c0c0303224802541e22016010319820483c01c00464008201da07501402100d88105c00540d030340c46040d100914055104000039941e00a0203680380d0f008c40c400000e10300d10703d00545001c420000441e160500c80c403000340040b0100041c3e020240c000e001c3c42080b0200c0d007a00c0600c0d21800b03031807504440300705003d6500084588158074010310304140c601d80545d401d69585001c69003090001e8811404c108845807802195030300d401c001500032002184158072070801812542090000944a08181d030001c603c42c3d410808000e4203500c60900f5608040e030125002440c030307441070f002600100100140e80740440b8042c001c0050300c030015007104080380c0301510f0311b84683d525401d08504a00924900d4000180e03424001000300d03002c0300c01e00300c83c800503400c10f00c0c0c000003500c0707207518001500701c118850320800910347c410300c08161019401006029028002c2d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 183560737 1250 183559487 183559499
    0x1050f060915010804061104060306180501060c08030402060f030403030f0c0807020d03110d14090c0603060a0501031a0306011e1e2105030d02030a1b0503060d05101508070f 76
    0x21102c22000d01e0400c940e0f08005000d00c502c6411619804200002c03403640d41e92034480007406817402d401000403500380b0014258030002e01d4492281201d280d03070750b0880c20840a070b96245440d88041c5c01640d00040a10241c1d00d081d1600300158000d40c401d850010700032612101c3c0300281d41d102440c810901c1408010800300e5078000c20038010781c5003245400108075451820240850148032485034040b03281090000b0031032a19a410380c011010442200d00320410001007011038801100c080d50400038001b003c0042e54001d030450300141e0160302c040c020300b083d0f850100e0310780002644019070baaa070310400d0340f03000300341d0300503000141000c550039110940c0b060140c13041008180c884e6581009002c41c52403c016800c0c2580320301c40d9448030980c1c6d03460224241d40030207500150307a401d400e00c0c03401504d964003030880b498402ca2407401c0c1e200e842c11a40c07001c0402407444010042915680608100000c41882c1132240d940c4924401d03000000b414180310101e172a05519070001408044545014448 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 183561987 1250 183560737 183560761
    0xc090302031f06080a1202070f0b090906220507090602010b030316080d020a020c01080604020a020a120315080703030305090f0a081308030310141504030605060303040302030d0201050f0609 83
    0x2c80d0181c22816150a01c11404200a15599000035014003032010100104201400f4220041101da404c880000d5203c2070700c118050150303c64520802c0c420000580141410031002e64002d038001c040c82000b0011074032101c0100c001c10042a0215030710390411900c0d98020000d4000b501e490310080041003c0400800c5c0e8034490262401c0c24050f44001410801c80b10a0889004111140095484a01c100c50107941c0308005410715010945000010790542002d10036242c1070030141e401000340500ca512120084034000c5618400c0686030165080050003c0024400800044009181492540c1030040807a040a80000d04541105101100d400340005402804c0b5802c80b03803a503959030300340300c909156130b81035845443d50b400040b042003007a01c04003444800722428100b50781284240708081205288d0203c600180c8680140000c3c070101d0903660100d540028040e0440c0d01d420780703030340000c2e25100c41c100e5a007005039141c40030070003c00c410910580d00207000341e40301d10513814a4109000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 183563237 1250 183561987 183562003
    0x10509040b061b0303070e300709060308030a0507110a0308090a060e0f0601171b060d02070c1805060d060216060501080a050105010e0f070c0c03150f0c09030203 71
    0xc400c548031460002540e0b201e4045840950a008030440950716494899840b81c008440100109402c01e0702450300d03051018841203420304032003c0741c0485040d61101162029001e1035005644510800810107228901c03640c4041c50080c3c604540340c0c0391002c2070b0401d407540140300404020040d86003a4041e4000240c4c0400307250f25007406e001a40d140410b180c500314a11102511144c10a0700d003195070b0b20085a42c628043e02a0300b130300c100e681c8410271550700141034081740200794480b00441207403c2c00342100703071007403000200507610b0085560040030680e00b1055041e2400b80181808006421601c6090810100c1c00c010600c8580f800d440010364841c080c1d503020300001e400191112584a5031400e14401036804507003080256102c40007950b4580c01203c049651f5841c0c180042941000c0b000c10600c1024103091070b1320b1550703802108640808031001c08542600001d0000700000e030340d5003440c040d07407013440600040002c07542c02c962341554484047e160500418800500160f14042100302e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 183564487 1250 183563237 183563239
    0x7020a150603121d130209040b01080c1803030c07060e090702010e03030103030309030e120708190f020d0807060612210e0f0a05060f031f080a0312110c100e010605010509 75
    0xa400d0b1003104840540d0240401c440a40c051701d2103240344000391550f405814030303c0741901d04100c0c50b44000010341d2204010b4991101c402c07000d1100418250b00410030541c0346001a080c0d90801d0080100c1c00c2c42c0080d15040380c00071440000c00c403a06400c02858443c0c4c0f0955600c028040c10403088010b076102e200600015003010f40303520994007850300601d030351140c04901030003010718212003030420f6031105250700607125607000b422100070000482080c101c0c8090340184d0452460902542041080780e16080304850340c3e1802c0c0400e130302240031489220001c0507a945066400c3c0040c0c074014070f0002018200c6085003107141010318110340e1190ba60381072100e040e01c8082500440e0000240303209107039400b1036480400001c104800c0740b90348001c0c40c050301c8068010280c200c08400a41503214071130007a03070580d910034440400402e100c1d0040050050360028002417100000a03012a142c0c06079219080325400400c590256020364413465040402f014020000c00f410600000c000d8030500790300c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 183565737 1250 183564487 183564497
    0x50f010b0307120605130b0109060c08160203011401030303090b0c0a020619020904020a020c040b030105042a0e1312030513080c072c010801090210030207050a0b07020a15060312 78
    0x5100315a83c1030b802000502801000e41e555503008800e135002805240910a00203855164001a064011481d141843d6030000d9041d003003000b50350441c16900c01d50442641c0c5592502d15244c003e0064101560181d4000d82c0c0104041c505410b017850444d001401c1d5080c000d40410a080d0034560204040350030601c3c0c1400491090100f600c20000307402217034404c9911074400540c4400040d000203081001c41d170195020300c41c4051803001c142c01c0794011034000c1c0c00c5905a00720710482c01221030000c1003d02440500300c1c401502c91200240001d4102c0708081c0c0100d90780c0c0300b0424440301c0b9901d440141d01a00c0d080c00540340c1503040d0b4400070290b81c00101075001c003044240c4072290904c030080140210112a81040020091401e02c445d500b140044040c42c0d00000030072181418000d00500a401401c840c0c0e403502400350407802276110000644183c020405144d001844501c11140149540d60040c0950484d0782000d02c803110182e40d06c202218a00041000041d4032807106601d0b051560078a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 183566987 1250 183565737 183565757
    0x30304030e0103090510020406050c0c030d08131506180f06032612090705010f080402010f0e0402070c0303020d030f0b090c0a110307080406090503210306011719050f010b0307 77
    0x850301d4028202840b900647c0041030110303150f40e000d0040c2074032148100c1128208960b8a041c1910788401101c0000045c94040008801241c4000c0001c4074512400041c0d24500c3c1001d0001c0842d00e042c0c112625840c0c084080b00d0341003c5a0060718090951100104107003461a902e08500b4408a00145413403441003c012010f040100b0035100080c00b60b4210100d14074002c00c85c07988503103a40c041c0b180412003e411820300c0314820140c088c40345030306864542d00400005016211210b42034206644280c00300034402c0010390741920280203510036001010803041d10350014054036034030f1108804151404136074648030f236101c4890541090300308000c2c41e5504c003403030011200c1e0300c1400354500d03582c480091000b040108480050049070415900d0180941d1a24109030310784800c5108004800810419220b036800c002004581210050500d00d59081001c5c039205900301003203408071a816000c0007100c0c52aa8140609580401c0c5980e0403036042d070600d50400c2c1d4501001d803402040201d1104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 183568237 1250 183566987 183566993
    0x2d02270301090b01080105160203180f1302070506040b1b04051e030a081306080106270810060f05040b030a03080a23091005011202090a0b06040e090f030304030e010309 74
    0x441940310383d4102085031155a124101540a0082503c7c620b1b0705c030f1030546010750411f101005403602100d01ca58190b01c041981c7d8200001d40340034140aa501140b21800c0e0003105019200404941e40b07e540500002d1410342003542951800074004d0001c41c900c00071301d1001003c00c4040741c058500440e260145e0100107500320541240c4610041d8251040d0802170b018458102c02410102c105c1100d41c030001030b01c41d44103c44003103080c49000082181d1000b01104144101c4403003402034455601c5c0b000c0d055403498401d20f8000401404035034190396031010b21856154030160301c09032074255814040c40c2c00400200e0354800019402408200380000032a09240c0c13190003008001880d00300b40c03240003421203100e0740d201c142a22900080d204e0864035140c2c0c40b9903401054126039800d501140a02c840d5001d1019241008203517000c03240d82c444e614042da58800026001619407600038049034a001c2c0142898040004295a08c96106000b0440041d9009500500c50442840c0202d46404a49 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 183569487 1250 183568237 183568241
    0xf060a0f05130b060304080c010b011d100c0602041401120504020102070303200d05190314190e030328050118020a0c0b180c122e2d02270301 62
    0xf060301e60180c1c0000a000070f001146001e48a0320000400070000c010403800190760130036852101c1c0c0303c170086910400d4010326080389003071000401418042c040f10380700d030340340d03012030340544c1049034107143c03403608101c0d00d5a0004504454811040d0200007504180e0000307541c854160ac401820420348a402d0130791442e440d400b08005000b07150444110300c50701e03c0042e21581101039400010003985082c000310510030f00400c01d03c00303400c03642c1d588607841c0c3c9144041448603002c0f51008143d00ea0801c03100d9503000700300a61081001c40d084440101c501c0000002452244160684450501c00140000709400038000340c40440c000700103980d00c00181d41a41c401c040c0e05001742212881030104a00201014002507503083d80005541c1c0c05103640c0c0030003008007200c080c1d021090348130039042c1541302200c03078a5918051040b520b130751500304512003090503136481d2104c488032201d500b0020f03590803e20105030a05290845025410302c0d00051034a4100000115600920041c1d152262500e480079 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 183570737 1250 183569487 183569501
    0x1802070812010b0405011103180609010e09010b04052809020a140d0506120d2708070306060e0a020702060a031e09050313060c1208100e0901050f060a0f0513 69
    0x50340c01c00d451983d4a42e840c0400382c00601c900e6020070782e0004452801500481201c000390b41329240900c81000a005004040e0810403040703052007481071504400d0b6941504143c0204483c0e07602d9130361a41001e0504c2610704151108040090729210180e10100260180c0c9042c1ca003030721700050b15041140300c1141d0340010b081c006401c00c0d80001d001b40307032080190401e51043e0003c0d510074651907045100eaa41c0c8000d11148000020750700b40719080c0c100b8030f8501c4034600649241d243e0f40c1c9a034898050b24203004055208070782e410f5440c00c04005e081060355006911694100c02103080107030a4001c08c0d4948901152181013565840b10091942822400011030b0300c1a81410800c1c9841071a1944d683d50000e41641540030304d2480c0000c1552080700289000c5501c02c02c1e40b20001030100b425181c00c80c0140160b03070340c3c001c4c0d00404908080718804c03292040355800300100301401c1001c0c2150007548060003075405007003203c0c001d1104050341698081116401d440240341c4248120a1310020011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 183571987 1250 183570737 183570757
    0x402040e010b0d0605010203030c0d0e070e180106060207260f0d0908070e041703040309031e030806191a0910030e0d0c1a060402070b0106030c090b0418020708 70
    0x4280007181d40c0410002401644a0003d42040001d844200582c0d60b0b00003110814000b040400c9104940030783c41d00035024140c8100b04940100d81c0341c041d64811a04201d60790301d040106507254180d540c009014039002440d190000d08102d0342440c610740749030020b08401c858040e6010740401076040c410803080345c44030404004d6032071004014074000c2c542000c5100f16095442a1b22010842a0400c0d1045014940c8900c22003140184074120552036000140141e06005280c5000004034098241d8018800c2e000c5821403010300c400d107005415184040c00541c090700c199500c58144041c0b0920f400180c0744e2250035040c3d0348113610342120503481001845504804a1414922050f415400500b01b48000c07400782d5542c10800d40d02110210300d202d202a28644a0455004026003816401ca0700400040e0002d0701d02038850312680303074600c03080c0e1210000954541e02040b10a902c54030410151003038807a03081c5450300c0d0070140072400800d004c0d00100c41d43d00188200030003040d042251502c0345 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 183573237 1250 183571987 183572009
    0x705010b1c0507031410062408060901120503070c0e0a050a05040b0601050904060b0f0d06060c030c020126040f0209090a0b06100513060206100b0f1207051303110414070f080402040204 81
    0xd2a46074492440101c1ca940f0f4091b07916440000300418090740488ac417581014192540c40d130f10f0800c030112280c0244c00143e5181c0010803006c004206a4901c100140180644547ca0b0b800c0c4003180e0802c41c0c50040000b083c0c03600c0c050601c400100880c0043d43c11400901c0c0c110b840300314480009004140e682d00099030744000040c1840d00300012005400700e060400410042d850b038540c415510030030403010040001d842d0b01101c0c0d00560044000c41d008980d046401c1c0c1364070346a0711800600b00c0d03050f9000d0300e00140c1481d0b07500441c5000d910540c1c0c80b90400016151002d02d5030723101c107a010405401c1d01d01c51801c05007982c480d1417148003903807544410320400d900016915038001e0b445980c00e032005a0b01c8005030f08041803400e805012181040f0007440c4403840e0141d0380058215085001d4080340402c403040101144040301b41c0300c074502841c0194a415031309403030402003004407010504030030030b1441010200030f03185d50000040280090103040c41c400320360302e600c0018024455a0015080c4034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 183574487 1250 183573237 183573239
    0xf0f03010b03070905180c0d080d060b1b0105151c1401022109070b030703020306040e0f240103110607050c04092d12030f02040b0705010b1c050703141006 68
    0x5401500300b103020300951b07030415400c0500c4041e915280c00c40c00c424207810038907049807080003e81c480014054907400c0d41c0009002d03031b04e445000070243d1002941088104074140c02815100c800c1c400c854100a501c07590081500b0504c0c080354940150240d038024520380031000400307004c85003494088a4600c01c008654807801e0b5aa0941c40312a481c0721509503070340d10303400607204440c00904d060035110214a400e042d680c901208501035070008250300d40207610744030b298080038010030145420350340d01c1340a040c440003021111100f040c00040317041d2003801c0b1000100003103400024515404401aa95a6628821030900500d4510000d08443c3c00a1800c691403040c0300c84110b00303800219140d800316040549144507030b440d2802920000d400721443c080780c481400d004c0d90155040340382001c030241c1080e65030508202103420622080d51302d41d4613048403041d01c0c9071002541c0200c440304da69036480441c158035015550307200340c08014103840007540c00c20110b000c01c00c01d501c441180160184015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 183575737 1250 183574487 183574499
    0x140106090b16050d181d0402040e0c030604050106150c0c060f200703030f020d080105040e0a060906020301080d0c0b0a0b01030b0603100515040524070813081002090f0f03010b0307 79
    0x2103290030888900c034248401e0040b560030046218802807540007170f01b801198503150204130050491940c0300c1190312440401303a81c5910f0600103140f00c0d80c011000001c0a520b4551014900c0302042d080a080040c010702000006500c2008032050f10414640440400945242621603c030942b240c01d01e10840d0314024458410005500002c4e02e109036203000503d0440c800580e0341d4440d8541d4107000c501c40d000144a9801c03c0d52004800c0e60045088403407160b66519003004550a1103400c2d160f860300040103120907001085030100760342480c9043e282c0402180c403003021540c005003202c00075640f00c04c050311030381c2c1c400d130850741e40d418008006a0380e07400d008a0059102c2c03040e00c1118000d00c41b403900c1c0c06c49000504269022500c000c0c0c040c080058542100d03c1c000103a80346e642180440070b0100e800400c0381c00d00507040d8074821b03000e000745881c00e00d4040c9261890000b00b102c0c0341c500400520009407949040c416081006070f501e980c0001965000a001d0f042100788560944510407001580f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 183576987 1250 183575737 183575747
    0x80f0708070201021006030b0a0b0102070b12090f0d050f160c09050402040c05180f0303070602030f010812130612060b0d0903030f111e0405090712140106090b16050d 73
    0x40c1c18403d0302118100ea200c100c1c1d1505884007444041e01c00b12184d00010f80e1f5010681041012100c14815a040d00d074032005500d01d540c10010031410300340404001c21003620002c100078090000c3c1c080080c259900183c0703009006100e40c41900050220100d030324140c1c0c201e07510810150039032120800a165489841240043c6011038013a8403860a14101201d824050b80455a07036044c00301b00b030103850f00030a0034051540100c00b14070f234041c4010000030003c90b00500c043d500a480070415082c55500d065919031030a00d0310064826101c0040100b1145100102c960b00100c0300c050520031801c4800030034640042c590f40c0d004480302c0000050740b441510789030340309a0783d00e8400c0d101004424000443e81c030403030b40030f01c4030244643c404014400c07000c1114241501007104000306140707441e44038000b0a0341c8c0c4400b80e4000c004078090030781b5402c10010302e01135102d0410001c081e0702010f40c500000101613003c0d9200d00d81007150006180a1a06800600242000d401a00b2600c04150071400205 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 183578237 1250 183576987 183576997
    0x1b0d0809061807090c020307020a0e090601080d02030a200d02010f1107020f0d0807050106030c06080604051302060306060403170414120c010815091501030c020106050108010b0304080f0708 83
    0x103140160740004400d4121900c0c0c0c212900749440042144a0800e00140010302010188500398072091111900590310340c942c040151801c00140c03078103070400354651380c50294107801a50301070b0040511199202e900205403089c9109034500500d01040280c90f02c018046600c81d00d082c140944040380314403540541200d0380071a035280041003001d044004004090040e040000c0d40140702a90400b000d1410340383c40d050441c01880740c1850b01406613540d50031108503620071030703104600103020041d071508003240c4c5d603021034240c1d005c0c04580f40c0020904804603203080000d118040c04030204506072651002c1e100a541d11110148544004520030340494002e40701300c00142000410202150400c00b00100d020780034980100150121400195036080c0c0003080800c0340e602200022440d0351341c08050a014041070400c01c106803000200040544031441c500b2010740e81005420030072a41d10940c1c1d203044580c00d207607490b200e0b00c4a00e00280c147c4502940300e16a007502041b09001d2100c440010b003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 183579487 1250 183578237 183578251
    0xa080702070b04061707090b070c03030201050c0903060604110d020403050c0906010207031707030203070213021804111b030c06040c061119060b030708010501060c0212030906030403051b0d08 84
    0x150a0a0b941c07140c2d011144141e004210029051a400c0c00d5482104410203402c5042410448a400d1302d901300480e160b008038005650310301041030200141502131043c250056410f241080c0f4084c00f510110340c0c0e401001d401c681c05151741d942131100c001d002c03805480100340f49042c203655071552801e0141d07135a190b41c8000e074803074809070010660540c00024000100d030b0f842280c0400381d40d4284500d07801d0b5000980d0a90541c04100850001a904c11410901d2400000d000584880100d10420780c0c005c2c6400c4158042c500e00a401800c2c9000324007034812180804c0c10310f280840300001e0341800c50050030021181407144a09100030010a05251001c3c0c80c0d403956900090f045003001155210510910030340480b42c015403040104a82e5045070508070009011100166580d1b0340c03660840380243d0181000811844a17802185018107070482006a808011810b00c2544030003e526484040c00040900100184000f1000944910b035190501c00000740d42c11a009000040d01500c8206ca9034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 183580737 1250 183579487 183579493
    0x2120304030308150306040b090a02060a08070806181b04030c0801050108060906040309030b250e1003060b0901030203060a0801020708030f01081603080a120501080318090c030402040c0905060a080702 88
    0x1080c1c410b8904c0074040e108402002020952110b885000702e100b000b60903880980125050240943c50321001002030f91102d0f0303200c00352803500e00d000518081c0b000c0c052a10805039100109620a0420000e41c0c1114100000e030014801340f403000d22080c0b2941d88018035141260100190030701c41903208a0481c2d0300b41c2e003075519a91f0740c10001c41c1c88070001c030b50040101d44020014030100342c510007500c0c0e00540f004440d040b00582203101c07000517014012107000207480705070107c5460134020301e030761500c4051781401d021980c01c0081c1c1203114050181c0d01c0381015400302c00501c207903131940000c000030882d081c002c55507180d03e804d10384030716030040b81d40300300f6107886000016043c1d0b400503034140c12100b24090080003505665588640350b20104508040250040201503165500e124840c006c100310801150341d50b00c0c41c0420100e464070312824602c50480d05040100c000200401c40741e2140d412240010000070326181602c0502c0326400c026040000801c5480d0f440d500400820300402041e021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 183581987 1250 183580737 183580741
    0xd0608030403060b1801150e0d060515030d120207020604180209090c0f0d110d060612051e04030f0c0c030b0a141504050a1107051609021e0a02070302120304030308 72
    0x280807255020301c2e20017621a40c0c410041144800c3c0380820088003540d031a00c000780100c0000010054142c840040e185079039100280b101b998640021491658410380c090100342807082d501034403032090205031030051a0005040e40841d03481c1c5088a02030b01230460086544801065010300039040721114a004100c15804502c000c80c604040c0c60500c500c001881c3c0c50004042c906a02401410380c40343d801d610306010a0b421111140501d0000d05420780e00c0c0c038030003400000b00704243d400240c84403080c48440c4500d0803000c440d04502c0c81c1d00c203030141040070700e600300c4d0b0304129802844c400000c2c2c2a003111050200c00c00c2007100c5c200c0c0c055031500f1828019004055424415080255103086610034a0020482c45051071703003003640e01c031180e5040060451454000d100b11503008400803100c40c2c100d142c001c100482c54403040b001130f041c0701c2c40460815841101c0c0f5440082c015000c2c950040000c80e28404040c07080141c44051640980010148210040c1c025500e401034001240031928001c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 183583237 1250 183581987 183581989
    0xb0906090106030213021305040c020102091302090906061c1a030c0111100b06090d0602030f13030909092102100b06180d02010504030501020703020307031119080307050d0608030403060b 82
    0xb80000350b035002800c0c040d0400c101c1031448001c0d445030041c90700d0303103a8804000800b039035648204280d80009800144c0e907124084208403082400026a02c08984140800c0303a00e9142c0c514040e501401c01d07520039903960510003400e0441020101c40081c01802c1c10f007080844070b0300900c0d074810070300194211000814480c0054070f40c280310031545049076201051061504a15810085586c0701c00307400d46243c50111000b0901c0c0c5400c070712080c0d0b0f078150000306202810b00d503080b4081d07021140c0c0c25500f51080315650000d101e02e4482c81a0040300380c42b141c45005020543d01c00c0c09448000311003154030b00404890194840120360300100f541031903c0c0300355a00342000d504685100100821408281040004001d0b089507541001d90410170141702c08000a1070034802080e9040c029001161600c02915006083e401c216840d80e0054000c41400e1001c5103040e0110500b85034807180c0c950700e9a440a034103c0340c038020384580800d807030b04065001516803404002001903c0c040c5100384180c0134884 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 183584487 1250 183583237 183583241
    0xd050712180c060f080718080609150603060103032c040903020d020f070806010b0d060e0a05101212030b1507060905120f120a0b04020d0203060108150f0d1a040b09060901 75
    0x22002c1c4c0d01042d01040002c8900d03114901901d04c1c0d41800c1700b505140d43e00d40d050300d0700d440c0003190030410365881342c6100e00d041038100030b10a5104408900030803556065680082004401c001449101000d41d0303801c1a81c8000360310402009980a13100b08400449818001d542d994150310a8026004040d82038201c900c0100e001404d65661071b00610f22a407805440942d590300585450356040d0b40c0310000314401c16038544690042c200d01c1300c04645820400c089404441c400c2c3c0c4106030340c481900311070000076920000d150004541f402e0004900380725102140d02c43e4008003040b0403c1c04000760542c00c000b000c2c0d00c0300751341c40d000b60100c2d1146465449003c0c000d106411501c1e048500c28018980450030002d074540d80b06404c43c10201e64140c004000c42c06903001f13001d400c440a074001c81080b1f030650f0300c88501740d4045e046511601e40b424190340412085011010801e01400c1058411000d00142c01b001400d400c69810400c0c10700e01d811704200c000d000701510040c40034003804020441c00c101c14 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 183585737 1250 183584487 183584507
    0x1a03041202011506080a0e07080318010503160302090315130c14030303011203020102090603010b040e070206040c0b0a171608010803040518090c0301110901030b04050c0d050712180c06 81
    0x2c145484500b908022080c0d44019000f030907500c1b4161180c6000c1140901400404020107450f03005540f42e078010080602c09203070901c0050304011081c8100032440d800c00c49100c07043e002e113040041e80c43c80c0c41e4021a00380001341d400800306d05c41a2003400340341c890904410781090300a8017000c03106500d6003e2640d004114030940d82e0315600030300041c8600301160401c84c00d600c0c441c2c000146000310100120354250030903440064481d901050420044003210032243d80100d20b072000d484246000da03142400f00d0481d01541e0f0500001260341020a4080c000140345440703080c02c0b0900720714025219407107409420301d81e440060546000010181d0001054505542c0c1c000c00c3c1e0b12840740241001c3c00c040c400141102d03d1813051110360303801c5460a114402455402c10350296071823110200150580b9440c0c000180958907000400c11444008801c2e00d129245e41040410300d510741c0382003291051105200b41721200e16000c001c481e2100d01d000c070910700c82d01c600c005140c840d9992405565030040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 183586987 1250 183585737 183585761
    0x3060902090f0603251707020c09150d0f060b04110a0509010c1a07020f0106050f03030706050a14150109060c03050306150418060905010807180f061a0304120201 71
    0x1039002d0b41d002602e060b01c0610760203000d0350200d003401c81c0d1641091034019990203803d40401e040390540c951a00707407000d100da4480c886000503d5500c03c100c0105005060003080b25481c88d0881303140001a0b035601a804c1c003155004804009440041e050020080100c00c0ba4140700d03074a0308040600c5800000f00307851460090381c640c0c5080c05980801500d840000040031207528242c0d8207009a136400448446014030310a0780200706035165801d51501312029a00018451030750340d0340c40c402c0c942d80041103500b0254024030129054851501c0d880107040e00d8010000042c40b00b4040084042e038110086c1c10911099039001a03555460b034061301c2d2140e0120300907001a50800000340c45007020354032850300c1d03200e4801503072500360b4601c48080300403824110405c0207612150104407594a90090f540503003e14000b0708001482d1100f0745441c8500d81d0010200941c0380c0b0500920110a035120200510050103c881104014010800f0541c400caa080314020540c4220551040c0b052040a070403040e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 183588237 1250 183586987 183586999
    0xe0c0a0312050c03070f20030601140d0828030b010903031d0a050402031504060f264602060301060e040e070f030c1215050901020c010c020d0306090209 67
    0x101d41d0008807540d90003101e075980184400c00001000510f21050b40180382d001e080500100d9180002c180c1c0e0201c6000c2c40d051196211200601000c0c28100c1c80103034000c2c04544001e11130388980b516019074040d00000b94041100d40a80c850380d0030550354841031190460340e00b00003601d500d10042d140c11525010150014401130314042e40840ea0a01100074144000e160404a9540c1d4000a050740d000321105a10000c101440902c170303003002d0103030f030f4040d0810600b200d00150400070640481c000301da04440d03209844c0403031440c1c851024403e0b044440c2680c901030030210740c0090040412460803015041012060511400300c0000021007034030564001c280780e15692800030201d0310440c102c07084a1303000d662840c1007040305008228060040c1804080c103c441d601e9401c0c4112100942d9000024003003801e4000707400902c03000c40000e4056940074000440da1507903045e10340240a610301407201c41d071900c0f01240d6900c0d0009000800b4502c00d980500c012511107003400140e00681e85851b400030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 183589487 1250 183588237 183588263
    0x4050f060c0a21050c1c02120a0917070302031c020c0d081b040e01050a0501050c0705100c021306081006081b061201030303020a03050601170430030e0c0a03 69
    0x5845038440f49404209030810a0188240c0328014040310415030380c1d03000c0d031140054081d42c000e2501c4031146a5a2150f40114185408040c1201c8800001410004066030340c40800003000482c85071b200d04480301c200402d80320070484c90013035920f0340305c2c03e55072100c1e141d4110264440386081c001c9070f0146220f01d005d800e42c08900b500568240c000606a12002682c20740c200e5900e8000f00040c00c014540404403070184d51600c404c1c0324000032140c02071810490b00308514410312400003049422500306480403440000302100c100c07000c3c0d080c030000039402420403410b0061201150408410394200d842564100540004ca42c030071150540b05020154000034010345001440509401c03004c4009401580342c44020340003068a103209810407400b095011807411000340d03040c072902c2e5011300c0c01e091100000818040700c881a03440248010880d100a034a84110798101903140f518450940550040e4101b03d00e0002d030103001b20f0340c80111240b03c2c0342d1103101945005408101101d4201144130084 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 183590737 1250 183589487 183589507
    0x70b06091909030908010c120501090c0507081c05070305040c0b0c120f09060403030918110421021e0f060f0307050c03040315050402090901090b0105010c0515090604050f060c 77
    0xd03010100c0d0a800b844074821000900085c00e004605000c8010b55581100c516024442e4040300e9060b000301c05900d1808500c0305c001c503008000c0f1042e81d0742241e00e0325158100050b24001d007c2c25462062003417400d040c180403a06405402042c012031141c505070016949607496000d43d0b001c2d0039a03250865000c00144c1842008642c001d009a44814140c1c43c80e046410b408940507501591046000a1520504020284c503910000c4410340006405218000c8100041c8100380500e006503c1803403114003501407241000241101041d9026140101501c03a419050016165021155010305a9080e400c0820b1030020125030b804140c48101a086498401c8100da036a000603400000c03500c020000440072640b40300350388580a513440c1c40820245001d02c18080c1103400500b50782610f80c10304401c3c500040d0000c1240341941c02c20b2038065081c5015050403131904d80922031084101c80c151060164101000c25003500c928010f0003120401350850748101e13130741d1720200c1c2c80b20480340e0140429084 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 183591987 1250 183590737 183590741
    0x105070f08160e1503010f08030415050c030d0f1a060c03070b07231e0703020c06130b070b04110102191205040321020f0708070e1806010902070b060919 67
    0x40759800b40b408500d03d0018501240c11510405003d00014401100400c40a22400341c0c1402520725900510304141c5000b0401a685211006600601202050500c9420001c00544030710526821342071000c04140c110920090581a10f034008040024010440500b86442200c0360020307000025460850540c98010b600d19014042904120382000c0c5402030014003082e00209001d004192541c84d5510102d07640d081d18050b0104c110140b0034070102c80801d40109030310780103403000d0325903030b036108801c09000c0e40312186a00204043d603c08107140003481584098a44103a100728030a0340021035540069030b03034000d84104031050440050580c40099410241400d036031106060803401c00b83c81e0303560040324080085000c50403054040070b11705840d6042020300150303003c51025204403424140c050b5103c14035401103952608090010459008d401c000e8028842c0c58201607980650f1244004000395008400030b5450380b0208021840300d01d4000d0016024592008a40b90304158140403540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 183593237 1250 183591987 183592021
    0x50f0105091009090b0a0510080c0c0a21090b1b030d020c010c09060305010617060a0b0c060a051e060d0201020a0203010c0c0209010803040f030311010f090605090105070f08 76
    0x410010240554200d50b100c0c40140c01c1045550744800d8803990030440904211220803404510840100c00100300b140c40382c0b00070240d000307280e1400e603c55540302120401103100340c00c5600342d10303c03030701b9009014024400a80e50036080c11110a0380f01100c0000c044a9045460041c15408078041009401030105100010140c1c00c0d51425a030400300c0340b007485403c076000115000d0050f5111203000071010340c400f03400e501a06203420104400e50402c0e1005046403154241100901c0112000c05d94030766441c5801d60062400b070500076030300c11103541c46a407150800d84540031075504080104440e50800c10142103054149064621036582d050704211911070714403000d0341540595a42e50025840078054160131000307e8460a501401901c1808031015050f849a1903d420501c0b05001e41910080380404480c1c051030180c51501c001001c00c0c0c0101181c080d6035082a150000c500c0c100f0005820403885814104001c210603a500d0806507000d980b004000c50008050400041c126541840243d0b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 183594487 1250 183593237 183593239
    0xa05120108010e03161b12020319080406140708040801060806010602010605060f07060b0a0b09010e0402040503150c040e0f0a2d05100509040803041e05031e120a0903030506030a0b01050f 82
    0x141d8601506121406c0401d6a810102209803961008419801c0801008c0c0314a04010866440742c03140c1c4e180c8013100d028a0141e00b0801106030382100824000c2c2c01980c6000350402c10a50b41e9907070724040c03e4024401880b81c120380f8050740300002900340c0107208a104075040a40390514221000081548980c000c1500300e030301aa903058440031980710074080740040c02a1082440e51000c2c0c0c00005006190004500382c402d038010042880300b40c6004c0707403040650041211030030145e140c242142d00240107075088807000b0b408175010010505010b9003418007a00150904110842d00c16401ca0007000c5010612100310380c3e2401e0180005005a00459112110205402c030540c0c58400044c015041a6400e61b0480c0c004018441804038490b00640140c04400105600540f1980c0c0c0549074043c14078215002004513851140603109207080b05c03001c030000c21405d0312901e0452000c40c020310340284181c00091803d0001249070500081000075280c00c62a0400e841c0c0c0380900300702c400d02c01d100c0c200b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 183595737 1250 183594487 183594503
    0x13032604031101201015080705040906090506040c030b0f070f08090106150206061c03120905030915280e0d020a03061107050c0301020a0c0605070c080a05120108010e0316 75
    0x500c1d56400ca25010032503104004c01030900c100207400a5419100e01100012000c00d414104100d00840050800200d4a041d00d021030252003900340302c0d004000000c0094081e014480c10030007000481c200d000140c0e481102c66400540303d401440c2d0302490202d178088003041c400041c501c00fa5000e0030ba0958841d81d50303c004510151101c1c1907645151118500b4400b590103031040c401e01e440d005280d0742c0108100000b121003400b19840081200d407450744400229a550803da400f4024140f08890b1401c0010f030003290140082d65083c20603900c4a4008000c24480056034000f4580c0304d80d0740903401c00295103d1071341c04088401c0010100d80c5040032640701c0401d00c000000284140107440f2404000d500403074540966060a9040032070483c003261207079104210b000485034100700061012a003054002400d0380e1840c2040e034074405e000001800000c400300c1c038000f400303030f00000410110044520610450343c0e540489403c3e10306118940d03820390003c0c8114043c590003013400807509405a412 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 183596987 1250 183595737 183595757
    0x80901110c06040b04090612111903050105010b190305150f010306090c030c09090207121101090609051e0105060303190207170703021f0e210313032604031101 70
    0xe0b50b2075200d40d00441d103001c00400c08000b942c1e414030552006200b602014080f002584d03907045284c10480c1510740c03042c003201500d420b5041394503a01002071503008008004a50b1960041d4020b90040c41c1d20102c00c404550091403d984030340a1203004254600390b420038951580c0400007030b0b420f58140d05040544d40e14000480c03549a01815590345c2103928001020911010f00508400d40d07601300102d414010044000011006000d000d182011842c0242840981c3c0b82e8141c098030602401030314050400c183c010074810301251203001c0d0f00c0705200d038901e103808192099003030302e208440b5190303d50000c1c403000038400d03504e03203966005035a00e2040d1160b0395160003118402542075900d000550b40020f505008504111700c030f00b803450080c0305120307220300e021240c0148898051202e86004d400403002c440f0301c414400311080e4800491005494880002c01100d4210020b50700c01a01c45a00083c001840e042c48000b802c2070001c3c8ca684c3d11032400341141c407400d0100000d40c200504106903209 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 183598237 1250 183596987 183596989
    0x9021e040905070f030c1a04090b010306050d1515180c030b030d050c01110f191e080402150403050a08070c0e010915080d0504051e060c030301060f030504080901110c 73
    0x103c84409010480c081e0142d00d8118106142090016040788a40e00e0341e1440c0c5000b418103120a8504507044000c002c00c9007455540100c0140440d03901094101e0b402d902c3c5c481c10480c0700c04020b040701c0c10150003040202d030000102c90501c1e2246c49132409002d0034200708100e44207141c120b0307c04e800240c100820f280145401003441d04900c0646a000180d02207427040e6040700030b010700703180301140310034160410100400d48441031241d01240c01907403038061005441580250481144201c8203906100043c0d407222001e0114071040b50124803034500380343c82c00104245070080e141580d40100042030300d000c103130b9241d17040c60b8403021040d90180704042c0001078600645907658080e000e201c030041601d03e40d0410036201000d99401032031803a048201a0102c0d5540704094074222202100d84080c2400070a5226040d200070400d45a0042000101030542940c0000114101ea030300d60761301c055a000c45c1030224110381c0305440090000c0410061400f1035071107407004c0c8044141c441c00752030804110b00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 183599487 1250 183598237 183598243
    0x50711030a0803090607050702010f05070c0b1c110a0c0206031506070311010b0301140a021c0609090203061b07060218030a11031506060a230f041809021e040905 71
    0x11000c035202c15000040040701007040c00256001140c1e81019400c0c521658006032181200815400400c2070118401d03050200340c02d1010020001200402c5e0381d114866601c18168180d2014801044d082c0b10102c030381014800c0445484042d40d92f01c1000c2c04000f80d0801510b41c1c17001d0140f044940d5000944c1c1c0155440f1001002520712a071101100040090207007402e58003108011882645400502103c04c181010584c3d4003026411005079600c016038018a40f91100c0c40907503030014600080410446403a90010000300d0088084912a5450746042c1e400b210b080f00f80c46c070030010140212000601590041d184014041020000c17040403400443e00d009043e0900f03603041c0981f0401c06550703050901c80c408031054020469044ca2500b200882c0d400c0c031411282c1010800c03840b05494035000c414070103885420b508141995245445010080142c20901030070000c401c200304801c81c000e0840c840e0a034000c3e4040d1200c092070b203a00c000e54100207801c2101c076030002d40702c00b40080062828 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 183600737 1250 183599487 183599503
    0x3090801020c0a02091501020c040209210606120601060e010e04020405030105073b0906030703050a120e01030b0d1716050a0b0612030d050601180602060601020c061905071103 77
    0x1e00080010084500410846040c0031b8103072001402e0b8000c44250a0341d010400040e6004103480150f607441e10600810001144000c3e941445010311140c2c81c41c0c1540403c09602450085601c82108610b9020315911401c0c284200307008129513110044065014080007131a8510041c001414250395801207800e60700110784030b0b00000c680d82d03c1801080700c900307034401c000c81c0285621101c10800d5001c06462028a02c0801d00c1285000002146543d0420100f406180d100c015903040f14503514212040e0040ca10080b000325110000c0501c13154468442d48150f541c000b03003a0304c4000340d543ca41024189440d11841d5400100b000314842c66004588803940942c452401002c00d06428107140c0c800303c0024003020b1294088240c2d03554a400000300340e8040c02544070b0001100e4450500584598042c080c0007480c00010101c0003034801d4004c01c2080c4208000e809942c80380d4011010071103e48100b03002050702c005500081c641441c42100a00704e554800d0300c80c2103c0000040000c2c0c540022 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 183601987 1250 183600737 183600757
    0x3060e010903030615050a050906040f0b300403030f0e01021308061302060304080c07180b010318021e030f0307051f0915050705070f030f0e06030910090309080102 72
    0x1600d103190308065040c410744c80100116116040c001498810040c414411050054200b15010507038030300076969403089900030520901d8007100142d8490407950140c1146050281e41c2300c0c2340440c0b40e00c3c2a003d041881054000300121201e590f11070b0340c01d4000b07240c5105012000c0755035204104440100b440101005031600d00c5070680705151030340702490580d000309000c6004000040e54001600c3d00d00c01e90350081d078881030483d12068520241c5241003090382c003400702401c02640340c900c64403131039202800f141c400783d80038004400d00140070203040f075000c0002500100b00c1d9aa003403070000b401010148004000b030944180f00042d440c400e1441c0c100e03034015105030700201740515104552000d0307500c58100c400300610440d0780589174021038110b80c1241240c001e840d00d00042c1114070800c12544c4407940107840106400c25400c0013440400105050408183c40c5460011303d85008000d581c86600070000503c481c907000b0207080d0240c582484114248035000f00d0125002a0a0000d04000d002d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 183603237 1250 183601987 183601991
    0x180c20060108070b12150d060603030306050a0b160201080601170c1305010f021c2006010801200d09020f03030a02010e0606060f0d0504031b0501020903011b0906140403060e01 77
    0x10400c110b190801075141d01900040f641008060f80004004504035802449990481d52280c2c955010a40b01d55880300000c0c0303003500d1701402104064040d406601950b50a803070110341c850320b809440803a4403544c1240c1545c102c04241e180300540c4a61640c60b8801810b2502940000a5003000200d0602c29511b03d0911040403d04402910005501400818007440c005070920384e00c0001944807242180301614a42c0581c004203400c0b402442c04a241001820041c602248076141c0661101c100b8001e6600c9075080603442070440c140000c4180404140c40304c00c0345858030418007540200f0a1079812038200e032038809102107585c4c00340040c1296140940020030410a00348081b4207224005100700c1c800d500a00c0800700302c501d44005d0b203122070180040080c86807100d0400b80c464480200000d0089a2403640d0300c0b08100d81900a0201080d0680090201d510a464080700c43c0c5040d118030000203920040402189100b0341031103144507060144030340f61071f403030b52100d0050380c144581500c01c80c0c0d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 183604487 1250 183603237 183603239
    0x31321030207024b120309090106051e09030c06120103060e06071e020a050106060302180a1d04030e030d08010302010e0306150d0510022b020301180c200601 69
    0x100300b03002c1c44c03a8080c2c1c03102007104500504c00751010700380ca00410010103284c2c20142481100141c581c1204006600400c0880558440c184166807640170701c0c0700340c0c0a40036900c00003401c540180d00352001050243c07400038448202c0703c1844003a800c94002554581b01c1e41c4002c0c1d4075911b504000302070042007180798800f1036040d4180b4405031220524905243d903c01010414443e0340b140d800c10701c5480b02c0c540d5441191484004a2a2103031101000d8040d500e426030000b88036405034001c09402d010440c5030a1104219010890505076a2040300c8400760b41484090509140701400780d40613200c3e00340b00040450380800b103441c05446d0603c12011031070120041c4150768204000030b400f24008c800a14503864407116a9a65901c000402c0b0b0242150346041c10800134140951490f81d00d03083c20854a4644441c5040ca10702d01e0b007081080b04c42860400c0921000c4940200d0741600c0d074000540440400f00d00c03a0324000c0a645402e4810010b240d403043c0b410558001c00321000301a800c0090150f5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 183605737 1250 183604487 183604489
    0xb030414030304020d060207050a120302040807050607020a09022104050307030e100207150c08071506061706010513030506090d03050a020405030a1202011e0f0b0f0603132103020702 80
    0x2498410010503803507030050003000016542d809501020341d07400500561202120700d8410301d048000f0600a00003400781015070344940c1e250740904104c031105012030303079499524018043c16110790358002e504514141000d0150b00101e400a00da1000b00c0d05061500710014019680510000d442c111515000010040285640f01c0d0020412103402c03104103c4008901c00083e5882044d481280c80100c000c450703488641d4052074284001c10b410800131a91541d01d490b105000982c440404142c9529100010031641e200b441c03845400c0032803030684403080e150b401c015601600b2100542d01003035081c0b40c01000240381401510300400c90380000704654045403201a00303880c0e004000455051040c0010002503600061814032550040c0c4095042e0407880307822400750890600c00b800e04903101e285e200c00406150320181004004030801c1050003c240b0800081480442040750b00075001e00118180641c01d0242d42c01e26880f403807500b42c01c040318106c2ca5a008075518103060202c0c1d8082203840c15 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 183606987 1250 183605737 183605753
    0xc0a03030e0d0503010e0f07030e03120105030106150903060b0d021e09060f0f0409050f0601030b01030c080d143a0e030a14030c040909141c050301060f09050a0b0304 73
    0x2000c007043c20540d086604094a101100d04000e02d44031500840d00b0101d24428002e900800c451907120054940e00c44501e9a0329211942c00c4c071620303000350301e00500000c2e0200e61202c0c1c0c83d200e20f6186e4940f407200745140c540310040c0100c020300640c8122440310b140b00696800942c0429045030305a203040c201680c90400c0f0416030000d18203802001401541d41d1a0307618080c0102403054220740c000746021076801d200d07240041c40c1c1d00c5500184607040010060007100084181280e2040032100366240d22015002d88401202c144400801d240484240400455101400352a00850300101d148803242c013002d40c40c0c600e624001c1e804009a8805008101141e000345031491a641c4005c1d4540780344000c008020022a03000c07030500e01c902101113081741e034005040b2002030a0f60842400480c0c3c450034400e1510202206004a92003440c0341e46105d900c20410a4960203020385a00303095a1900c5802d442c03140380484410104100c45074082960b55402c51350001422014458039241c0c41c0a16000c58 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 183608237 1250 183606987 183607003
    0x50a0c0309120b0901150f0b16020405090a1e0b0612150403181211010c140105040b0a0c0f080121060e03070c0b040819020406091802030c0d0203030f0703050c0a03030e 74
    0x3d06d0713001d45a050043d403040c03540001c05c40d52042102a40e5103008034154810f892010002580f090420040c07004200700091a140d9050042801900c2030440c002c4240000e0005207008012800c0100061410702d0034000c030400c28034038402a2100300d00407603408401501d0440d401c9000c699424803042202d51010b0044d00034000d102d449a080c512140c640900d0758401d042128104800c0d000b400040242c3c182240d80220f1016000b8085070419140c03100344490202c40040c581c501d0010000c4e5054402d407046220124161605030403a401c000542051000c50b1241244003010036803054002101442440001001c2c400510346848040ca0310086c025456130141d24903417801d0000303108440010941880c60501000c0541c6500002c1c40410080e20711640300900a41c030300070b8425848000341c404401c9441c402c50968200724010420030648500b8130f0b0b0040c3d0198000d0002c01c0c00c01440000404915009060250070982c07007a510718074119601c28101c00003074803007820403441076080003a06 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 183609487 1250 183608237 183608261
    0x14060c0f0a050c060c12030c07140a051506060306091b0426120f0d140a230108030406080a0f05070c1a1909020a030215091f050a0c0309120b0901 64
    0x180c174081d01002025079850841e006908101c80010102d1815401181242c2d0382c594040000c440e0036007002c003442d8464404200c10b540e08e015030045440f8170211100b0003071248500520759815500c585044c0221a00300408400240b8400c809000c00500082c0140c8020205401d200c006040d0305a9451003080c07040c0615070305a80100254202440f4034000e641c0c10140e0509001d44581c540e40c1c07018054650500c0028068282d98103021120701280c10218918610326680300564588800d030100c044400d10507103000340c205100a20003244651612030700034110308400b04458852002c4441160402d441d0003012411100d418410481c1891041240a00d0b44608410398034000304010400c1c000301e013080d00302550b01c0400004659540a8000c061074019020105c0300e030f050350a260040d40600000d910500019051101d12004038100154003162592002d0071311800c42026107403c0501e100803801d02500c0c0c000400c0c0d548401c202c101c0f603980911116465401c00a2915007140c199850309 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 183610737 1250 183609487 183609499
    0x903080f090a0b09090708130210030e1b060a03090215030f0103050d051303020609060d06060f030f0902030d052a0a141b09070314010909020a0503060106080114060c0f0a050c 77
    0x844d8040d81d5010071281c2c002d5135401e200020799030380c5c060003110b041c440400a510840301100041015071541c4010301900038001107442d080d0a605c2072107001d00d0445001030340080108444081c0e14400c0d000101610b201814000c3c1d0b207207280d8454001d9800c1212440c041c0424040104180441040300c02101300850030014a441014150280000002d001c081d024500c0040c81110a403140d03c102e038140074a81c1400c1014a80f68100200000e81020350000005e05202c2c21b00c031502d00d913114428071a540100100072404425000b9101500244c5140b030000da24905018480c0070f1556462109d0404000a48040c003644d24000c694802c040a103410168041701241c410b907481c081404084d071100302d513102071030340d81c00c80210090804c080000d030955000800004844030f040d0800013036140301711641072441e51270320140360307640400748121400646039400401c9901c000702e420302240d210103001c2d00c0c540806881058506004083c03c28056444826010700b4428144440701c0503e50840e08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 183611987 1250 183610737 183610747
    0x30607050309070605030430020c10020303150402070b010f1a03010510030e1009080409050703021c0c020a080f03040b0702030a0c02040f060305071d0604020405010f0c02010903080f090a0b 83
    0x401c0e69561510700601043c042c000012034103200203001c0940200c030f0b601e680358038148140045234110305070660001c4058401c2ca405601c1625008030741c1d0150300c2d0182c2c011810740e55007000c111904044100030541042c0e08001c80300225040104250207044c0340e0044901842c40c2882002c100ea2076014201e00c0c0c0401400140002c0d910790400e2003240308207140204001123142c2c00c90341403102e0a04400042071400034107104114550025000300c5101010411030755440e001d06809a11940c1e41c4d03040a03411307007050f8582441059012aa41d12260302c101c54650a540e902c4260230381c0040d00e034030601761020041004003e00078032002c0d4491b8403480a0750074920400750160a5180c00140207214a880b03050300302e40040d681c0d0140300156001000c0360715190392940d101c2c16181088404115451001000490504203402201c040320720680d84c03000c244c030f85400e0403628494240400c0741000203103207000011030350003406012940d0a4a40c00c5603500c2c5c0c440c0c00c00440c0350740b80d03000d8480100203000f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 183613237 1250 183611987 183612001
    0x7050d09150c02090414160e0a06030302070e040c0e0109091211060604020702060f191d10031e0e03130602010501240203040305100203011a07230106230306070503 72
    0x268502c181d9410b40f100b50740d0b91601c0c9041d21002c20a092005610304c01c0a03a40c9440002c0c0f150b083e000c48400d0700a1085545698181d0300c2070f10600d005c050050b0303021500803c040300d40d140c443c1e6441400740105101040c1c0f10359058031413040aa2000c00e079981c880360201c041c8161155406810f09483c2062001705803400b044c43c2d1111002060144200c1c1c0c08100b807070175511030307078200c60b4245401580565a10061209000c8281c510500c0c540000d095401224046085103035800c1030709401022003250302e105a004802034040018081543c040d01a210f6101c04100d0049404c00010322014648030b6078483d000d480c51024551105086a040c03100420040b0030020003086410414848030211610741c079400d9185200715423008100d80320b600c001d4100c00c8003d5020b5030503510b000301c0003104d82c1020102c282480c0150300d8094520521024426000005216862074550551001041c06991031184240541249600ea04405a0280e40076882d00d0b0510a0507446110740c24114114140b0f10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 183614487 1250 183613237 183613247
    0x1006120905100e19080403061d070302150c0105150301050c270103090b041104050c0c0d0c030306050d030518010f09030809030115122f150c0307050d0915 68
    0x18460304580c2c0e940340d04401003803005001c50034103404602c000c54502c01003480e005003103500c107100a551903468260441c000c4280c0324030403880c42e03400d90014000c00b8119020489501807602611041c43c1007040b8401111100b170103000d22804400080050703a403200d40516007500c100409054820604001c07060002c00481c40001c0d403020142801c2d1545c541ca0303c01680104600c4101820b0400644200710402c0303c03081d0041c42c3c44c1c1d001d075418000741d10b80e04206109400f40c503143c1042500403485400a5510030444100d146000746008208580e43c0c5001c150b00b108540c01c00e50010303500142d02c0140340e540748d0002503410000c2c41d04a407503816840006003c2c42c9140001044014001494a00d541c2c0c250001c15812486c008080c10480d51890400b02103c1504030407508600e6441c1481c0b03452a04d40c41da6000d98510800036000801e00f1400c101a80070f842100c80742407407051120b200707104000c002600195125400504c01c202036541d003e0300c1c4049a40c04000d07101a802c0b9060045540302d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 183615737 1250 183614487 183614503
    0x1290d030804050a08030c041502010c0806060d09021203070507050a06091203110615040c02070e0105040e0f0a05060702161a0d0b1306050f090c0f0c0f01051006120905 74
    0x14a4100340689661074854100008410040d05600021040c447c100003408010411110340c1e0001761510ba0940c2c1080e03098412484026000c03070000c5000900300e0034004018504036039410f00000b03103807445500180c6403410211110085a101240d02c80070404200702c48000b41c00200c940a189501d00b06c00144100d500d07006070b120700c1103040000c0c4201805102c504003000c00000640c1c40514101c400e144140c940e50084c80d00c40d82c100035410000728008110742040d1140311106020036800e00052001400f0050520800341c418221641500310003886510b03c00c610640140ca00c2c0e04144500a140400028880c0c20458010004102d50300c02600e1001c03200c1103520019031294a44108100241084070119401062028074450840801d90110b001d44400b00c0d940a56031140e01c041c03124a107022032301e0200c030420800040010b21001302c01f400755132451b503080301c51044591034040d0940300155015407201000d007a080c00100c0c0c0280300c000c0c14101c000c0b41000070486540798195110b0030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 183616987 1250 183615737 183615743
    0x30c030b0607171b0a12170f010303030b03031c0e0609060c160309051207150201230a0b1302030402040c050a020c0909030415092108070b060d020405070201290d 71
    0x103404804500c1075120351003130100311060303c8120f804d60901c202200315100c0004005a4100c210441c25203581e445c45d4015a5503800280c4160b095235801da0003000c4140d6000d9051106002804074090b0344000d01c59050076035400482d0105100f441549450000340240340d55411a00801c01d180d03940900b507030000c60b10110b1007144903529040543d503081558002541240c00280c0100203410005209000c41d018440700444010150400300c1c02c0f1000e088140205082150b4003030301102000c1c0704143c000c8041d040024080340c803040000e003a004581c40800e0140d03008000c001c150b190609c100070a15000f414614545003901400030740b60304010800510440001002c5030b49800308106450281036150030740c1c2000342801001506d07440c06441045001e882c00d10017191010300e0f01100c07100403940100050f0811515945214034100010101600f25030b00c500d00d003009d603846000721400b520643d000000d02c407000b19401600c0000d46444440300e250b84101003100350b21201185065290 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 183618237 1250 183616987 183617033
    0x20702060708070213050106020d11240a0f1803020601120b0c070606090515040b0612070f110d0e09180309010e0612010303031e0c0504140402120106030c030b0607 72
    0x1c83c0c40003800e170004258903c10380e130f480e0200104240c1c2e000601003c4c0002291135840208082003040c2d0f03a02e000740c4106401035200c41040c0c61b250b03025049107079048061341c0d4021421800001e104000c40e03040c118481407620503a040101416018420140905800600c0b2844d82949403219a50b580001c2c0880d9a000707000078246007402130315480400a1320300302d501401075081c0400e4400540010800703a512507440c014060b041481c01c20225840742e2120480322851380c0d41c540040d580480303400100c000b0300512000f4514149014854800311030715540b2050100c0016109100c40f040340140301d101c0c030500400f4622080300000043e6910320300300346480b0910203140c0000c10300e03034003892442a1080203007200110800d90150000d00c1105560704c0803074807032500c284038441501c0c0210446408103c04000c21b01076010a2400b0480000b8050405450201c01d0824481c0b402003d07804000080c0d0ba03102080c0c0a66498010600004000c131902810149943c036048005212042d004003214 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 183619487 1250 183618237 183618247
    0x3020111010f05040605060a060519051b0d050301090e0a030905060a0216090209040509060712090309030f060507030e01020c030f0a0905150304151802010f03060b04090915020702060708 82
    0x80000d400800d03100c006000140460f003051716040001d45000d4030161701c6401c5417000495001c0c490000c1e00c8503c200c4844003503500ca2944020745013039206400f8010440d600392800720070710703108000d011120012981c0e07aa0f601e40c50100c8040455811a90701c01007038000c0150800482c6d8041c1400054038022150b00d80e9814144405a02e4800c809204e0240d400a55000041610f01d9130301402d408030b070903207050000c1c0e510f01c44920307242c140440d00d14010511000f22005007943e941d0014031400d00c6800c000c040c4030340380c3c0c461074044c103a000130031a507150f00d413030800c500242d00d800f48010b102c080c10000e40c280318070b15141d03988038042d0080301e072904c0c0804552040a10b2140b05200d0003000060318812010a010b00728418503407017210103940d1000f05900340d038a005014401d601c0341d084401c090151540305540111600b444448007031040640310303000486d0042c00764004100504000d00e00013002921441d012660141119405800b80d02c180300d03940141e1206800c64599582c0400c455550f9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 183620737 1250 183619487 183619517
    0xe060d060f0e010c0e10170a02090d060207120212190e06070807200a03080a05090310051612051522050a020301030b090a050c040e011d0c19080304030201 68
    0xb490400c1032000e00b90300308072440700c0072904000c0c80e43e4040820f41d031042c0b4621000000340c0e50310781110f42041021190400043c6524441d40c081c0446e944000c103850400601c4da180c100aa8000200503104d14070f10340590340c1c00c0c2e5010044507154808516940d42495284007085d29541104075103502441103020340c02c9048c1c2e403000110707042103600001c0c4640301d00403403d2002117000700060650540d08902500c64507032400c85d14150407aa40304100f28902120954100d9854104903c02c0ea0103204469070002d0b1407a8a0003224400e2102508510048031a00001044901044050351820b803412041c400e920b50540ca1030b0741c0d99031060b269620019480b90000c0b000d0306c0a04000c1120929100610008a15a400544c1200e006615000c0b6648501c8006030702d40303004180c0240b0603403144103c01401d0416420019003503180c040004ac002d5602c0b804d4901d000c1060000c03840c5508890250845841c10100034078240010011907103000f402c101269569114502001e414006640b0f152169 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 183621987 1250 183620737 183620741
    0x90303060803030405060f010f080c01050711090a0509010f020f0d1104030b2503021303021e0d050c011e0819090510061a0f0403150207050304061101060e060d060f 72
    0x18201c5400b107a83d00c0c81c25051460325040b040d203003e2404100c1100000310940380325840701c20b503559400179201d036924140043d902030380461b404458040c3c4c08540141240d03519581c2501c90000c50b140460903160400046003160321903000c40040702d00c107000c0520171061030010746a040c00200e20005040e8680d20310301754140142c0c3d100814821210007000b9030000120b00640200e102550740200300c20500c0c030160164000c145134a2025020030808002500e0101020380004a0718404485150240000b150070710507000c0c01942c2a80c05182c01c0390580d640b0480802220182c035150b29038903100c2210041412101500d001401d542041d440140205150304c004000765000003100c6058a2010108000c0d15003031007841c100c0b02000c1000603400c2107820071a882440300b0210b2625103821135036000400340740007040c00c482035030034081c103400500204020006000f10b6100d141c180e405486410b400c2d600f02e0b42042402c0480281403000b0b0b5150f5030003180c0a01c0c0e11030030205e08101c0f9041d0b1440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 183623237 1250 183621987 183621989
    0x60309030e040b150a0203070201080633040b0a26010302090f0606090405011e0b030714031503191709151c0c0504050a0801020c0c060a09081f0509060903090409030306 74
    0x1c3c1386a00052030041c15400000504e43e41340300303803200c4205503070307880c2000914407200c40318820046900c9458500d0000101d46015120704c500562410651503003001c0300d9a8202524000115a103030b0400f030342c42e0707908256180540c00e0102440140358156800f20395036401c0a4001d00003251242f0204006513940c0f01039480140c0c016108008545e542e0121110721000e194903840221611030001c0740508113001128400c0d0380c00d03210403070180c3c072035501e10200b076100402d100c5000c0160015585030355070a00103012a0901c500a0b0000c411440c1498a0143d10200e005540c0c1241004500e40da0b444007580301480c40007000b50282c4030b4005030200402c4441d0329800a00280c82c001d04003c031650080054410703140103a8805400035101e100c5c613402c0b0710501d0a00851540301c0c800540440c035105004120003842454480f02c920382d02c0781003d141080b80b007801010741c5038070705001d030310240b417442290f40c00b1080e40700620079401c04ea440380d61a44101002d45009a440340190380030b00d8060b0304034030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 183624487 1250 183623237 183623269
    0x30e060309010209061603031d030417030408070303080f070e011d040207050a030206070323061c05030f0a0e010203161709030f0d02010b0111030f031902071a01060309030e040b 78
    0x941c1d920800315090414145006c040700401d1501c60000100d561115044442d03d180c18000c514150500c103c1e4100d00c05455401801444100000f1409240070310084004500c26154100c003801c0003420400301342c40c000d100d5810010071208440c06a039110001c103007101c40c0814404203844481c40403801034414000003508921030094508201a40001d08920442c0107503010084400e00106404c8c02c0100150a00312484440c804207100340352094104110442e144c424003102c02d6990b4a00e4290f400145c8050050880806c104090035044000c402a4130300910145180c10001c074414412a05004406041d121014540350110810307501180e040c85001021169001c4002810540d0b50700c00100490040d400c000308131402c1d5000b0108054400e1000d005141846200c03800d094480c0c00092907031500d46150404401c205000c1d1000740704440c01000c0c13450b41401112540030000c0d4069100804040c50044010003082d0b1001c00b842890004030b03000315a04602800140155070005001f03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 183625737 1250 183624487 183624499
    0xf03031f090c020d02010f090f08030601020f1b0907050a0f14040906090207060e030702011b1a0f061503130212010902090c0403050105101809020406031b060318030e060309010209 79
    0x30082c040c3c0005001c1440d01a50b802404848000c01010003510014800205054883d01d03040300004c0301000516404103061044410351039400c00840d18115401e00300e0841e00d40c2c204009401030410b207110310390001c551b090107807603e5002c980c01040f42000c103140004100150035204030946206080300e0080205000038080350340c0350420f0b640203502c01d01341140d05a2030120205030341034000c000d441051360140c40f06450b5074a14a0114074100c0607040450321910015050080014000e003441e0003481c04401c4400030749032480c20300c00b42c1e84940c071192405040920401601c4a43c54200392041503041d1101090741150a007280e0241c154944000c1d4401e210a003086006000c0034060400c80380184000d0006865000015244a10b1030285c07401c07104106c00011016041c0ea045407400920107000019056a03d46583c1e824000741e258074101c88841010812160781e140c0200f00c0c0c11000300700040500c02255501030401064070300303100e005400100001b20391000079415a02034000292503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 183626987 1250 183625737 183625751
    0x8100b1c0c0f08030c01050618010e19060308090f040923030c0d0e03120403030f03020f090406030308240f0d0c0f08030d0e0105060d060f0b0d0507050406080f03031f09 74
    0x1c44d145d82082594078159860500061903901d4004101000710840c2a078820b426420050721500c46103004006000d029110102119000c12621404000710b008800189e00ca00c4a0010440300c0b030611703c0c140b4425030a00102d0408070f118404070740b08110042500406861b01220894111f000761500c040381402816070305d070006178001c4c0324110b9601e4118146e614200c440325405c52a40543c1c0406400140309081c1c0c000554001d600900703030340103500300071801c15495100280542e042508114006020041400704500d805003494500c00300c0320408000700481034022a4184001000030761140c2240030401d000c0c051100507150203481c0c1142c00310000c588603008550342c2d5015061800c0c0141c075090280b20281c606200b42800798a0003482240000d10030749604014200000e49428943d030344041048803580c40d60000080c141c4200040c3c800f880c40d0000300300c100d4005500520031070300b102c40d03010280c200c0482104d0b44003141035690f010001203800340666013030f03c6400220030340340361400c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 183628237 1250 183626987 183626999
    0xc0a03050c030d0203270a030501020706061e0302063405030304050d170a0903050d0f0e0708011407030c030b100201090b01060f020309040b06120c0408100b1c0c0f 72
    0x280020a0541c00c2d01124028941031200300ea0f203108480030013550002245a500494180c40c181d8200303158000d080c20045034894407078900b240d000c2c2c441220510350300c0404024030310707003070035000702e403003910650010120f2858000c41d80600c01c5801601c186401140c178a10702e541d8190b86504201046448101e01458900c0d22030b50760340c000c1d1001e50b003070f20407410807036010381c441c4407805400f64420602c2c4501d92140c04a41c000b422800500b2400d11200b8072260085c5090380c480c03018401c441c80e8022801412200301e81e03040c1485608150170b642d060130744003200946d401c0070480e0841d445103400151035a0702d0008070028501c400800303030320040380c0072040d01c415415001605103034041c0261090a0740d139100c0a580c22621848500c2c00340e002070100c003401e03280c1544017002c420000303004c0c5444c0062038241c01c0c942c0780341101c2c00c0407508c0380890300b070141c50b17030410020f403184c030f80c80c0c1040010507030100000d011b901d40240400400026000d102d000c1010340c15102006118003408a115203403118 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 183629487 1250 183628237 183628243
    0x13020a0203041a04051503180102160212010b010807110a0c090b010e030604030e24040b0a08010e1909061e02030604150b0304080c120d0603020103060501032c0c0a0305 74
    0xf03c40c0f4081c14400c44000e0707101e03070310300c0c1c0848044a030000c0c90424042140045c010035900010109142d000904648014a503001c1c0010201c4140d050252518070300c8500c100044c9220520710175160307a03d000a1100036036000380400e0340150f03075030510850b4810070404d20340c501031980300e0041c0342c41458400040c001c01036400031101e02c2c000740c8907440e00100c2c40d8245996000102c8000c0c001400c900e030500c406003008900d160354030071901080340800114541075200b0360301c030358003840e807840002620450140e440f4111a001d410300052100c02402e20301101003202da05540307419413281c0e8441034481000190f500c030810740480e585a1542d04049000307004000e403c11500b25000e98145800703040b14025001004042d00d8003809a04d055072100d495280b4103800c4000840d0782441003c82410740c030b0703440358040c20414805280124031541907100040503901140d019905040c00c0500751898070310701040c000840c5d050310702c0c0c80b0b221440007802c4528200c034500300503401c4119601d021003801008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 183630737 1250 183629487 183629489
    0x906020a030b031603110307051503010321020c012d0c0c090903080c090a0503101b0507030507030c0203030405040f02090a1e12030207030c0608070e0f0105041413020a020304 77
    0x5407000c0260880b14003c0c1900da040c101403448280003040f2060000800b8010b9218100c54040d00b19a81035440f8004206108040c4c40c0c12401c5844c0032004008001181d02c032021240744405000c8401c0b0829400a955403036001c0005040c400c880e404c03800100d03030b902d812608640c40410740316012415541c0c0900101154007094802c04850f180200d000c00c1140242c074541036040d40d40040310355800c031a81c1240d4102005c0280d00c4000d07070500040c82d03501000701409481080300c0000e80c1c4000c1d0070301c170800c05070805007030800c1c03200c00e101450110380c110741a690819014102005e86a00503c0028203501c12904625489482c140c64001401c030309a000d86000041914694200ca4464bc84140d06c0c2440500f400c600701e02e800b0061140b401940111200c09110340101c0301e40c0c90b02c03a920100c03840d040c2c3c2c00c038400103170036081013100e61580623065034480401a90407525020022000a00901c80e5003c0d071200e80310f030354842806540319214000c001c5940071f07e00315240d000c1200025241d503c6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 183631987 1250 183630737 183630757
    0x120307110c060406170405010603050f1b15030c071109010906060e09060a030f05120d050411010f080a0b01020a05010e060403270e06120a030207061103190e03030706090602 76
    0x1407141e8a80d2604080c000c95080d240d09480b031907414842e9512915490000410456443d500d5550000002e013042044034584040320f000340044050324a00014924840341c005d0348661400700401e4003c1400c0000c4940040c100080145e5071000340c10f01c528180d04901c0465007008a10000042004041d40800181d030141d903100e03c90400d0140070003441c01c070207980f900e40c800e00030b440c204002080c9020002c99284140113585141c182050078840a420500d82241c81c030fa2502c04000400100c0500f0591240c8242007001088904890040c00442d005001200241d503a040c07900ca181c1c02003200001841e40710000303010792000f00384501c0d19444162421400714011107181098228a00b00065211078000c0c42e4a000a142c0030114403110320260a158004210700c0d0444028001032141031081c0c0c1c0650024414035291407402824a201885a80302030303042031109a2041141c1c5003128946005481e2815841d00044002402c600c180c00c03005000b00d21704902502040030f19000351883c4e880c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 183633093 1106 183631987 183631993
    0x4090215120103060e0123070201090b010312090f031a040f0204020309060103020a05030d0e0d05120a09080c0d080915040b0c0c0f010207150503070212030711 70
    0xc4001e851107002124480184140409030140140220b00c0000030014000e002203d0424080310b4a0703280d4880c4100d01c041003415100f5041484ca964001c01d200740340796901d14165881b412840c2a0101281c0542c0c40082d00d0984505400100c1c0e4101405818001544514104031000140111514101d40001d00c004d41c4541c8080d40c49450440002e152035411801044064103e940c89903110b41d1022000710000ca501c4041c104603882c042c1d03421707551407019103401400e22024200710364010101103901a4400d9205001c01e003294005805c0d5507400801c03000b0302002d4580c43e6409840a10100068552030504285261b1007000d40300e4400d00740303600c0d90030070301c1e06911404074078542e980f02c0c10b4104840d1409030524042d110003400180301c200d10340104200403010880d40c1e50180440840003c0c13402e40280200c90301001039400c441c1d42c0e4980140043c08240f8000c03407042c8a84 = true := by decide +kernel

theorem cover : BRFrame.Cov 183453237 183633093 := by
  have h0 := BRFrame.cov_init 183453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 183453237 ≤ n) (h2 : n < 183633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
