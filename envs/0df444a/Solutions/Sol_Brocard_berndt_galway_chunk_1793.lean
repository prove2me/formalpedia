-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1793
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:41:42.968501+00:00
-- url     : https://prove2.me/submissions/e1fb4fe6-baad-4304-ba41-ec680460d532

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 322302158 ≤ n < 322482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 322303408 1250 322302158 322302163
    0x17010609111809040215030603012c0c060a1e051210060201050a0c020c120f010603030314130201050702100c0b0a020306040f09020f22062702071a0a0209030a05 71
    0x4141000807040503042d02c011400c00c540f5184c4030b10b034080c0c140c09040200c43c034001d0158100400240c3e056484d031124098000c4601e40580008260106880d07614500701001c078103008104143c035004600501240c0310380d96100340d00204030405c0b14060194050000c008850364401d204801104020324005d00c01d0407002c407502c990454007103500802c602d84942d61110165035a079890040164001c01d864811840d0040842c01c2903221803049640c0b2680010b02d0342c1c00e444c00b562040d00465a21040c15a0581c45641050790240310b40706244900c2903d680080c140d40144d4002030b0007440c100c46103405481c081d00000b586590090b40d45540f610b080014800650300807245039004030b0409a08003440d80840c018000800c0c2d009202900e11040300e824031014402400e01d081308000c29006e0080c00da8080d00c64100a811070b1141c030004a416500c12605000d100c41400c1005481007051001140300c50a032415502c10517240b80d2007644483d00c100000e8026110b00ea0340c5801011824403c10400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 322304658 1250 322303408 322303417
    0x110909073b060304030c080f09090f04140d02100506120a0507030c0518060d02040b0a030b071733030d030f1103040f060b0d062d0e03041701060911 65
    0x905549002003000c407402d000690205a800501003050000c0d68400115464080c1c4801d1a48044190a0508050000300d0110043c0c9400700b405640c402071005001d018a010306030803041c4d900a04402c0c00c0c028000f5503c4e5001015140415511800300317480f56150013820340c06401d2002216149145402c009840d030200f44001c0707441302e0100c8000512408e26070011880102d840b80c19040c159101000e000e030b03a4880b460b00701c1e4030550b6070200e4603c595604107c0c101950240000310381c40c0c0382650000e804119040e10031a001c41c3d120041159080c2191144203a500c0b007600c5400b954a00065030411206503d8005030b4140a2102a080b41c6a0706600c4580c021015480c01e11440000da0000403a9100c00d80f0090402001d881071400407603025000150b08a00192106880429689610044541464401403003001d144e181e00208048805080140b06a02c2d20800642d10300c0c0741c90b40d0303591099100344d03e40c0780051784000e03c00344d03420b510000080240c10303c01d11200302031001009aa130701 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 322305908 1250 322304658 322304747
    0x70912080a080105010306060e010e0303131e080109080a0e0d0209070201360f0c0b030703020a08070306050913020310020f0403230a0b04020418141011090907 70
    0x42d842d00000707066100b402001d040700c00c0750700d807140d4096031540119131003120500c1541c1c251004012030342c5000006040300005007103052401d00004524108000e0f030300c2d400e40c08403040340e041a0422010840358811150007085a0800380300c1602c0030740c08100070508410307000e50702003503103020400d0050b019004112013a581040c0030804a40703071003000c441c40c003480842450a0251106500004980c04500d40c4180c0c000c0e0381c01c8191517030746c140070196a4400c549550009401017880c401d82070b004070700746402c6482401c003880a0303820036000c00c8142500604902c2d6010162542d041952028016041c000380100d9040d03540e101c270b00ca141d4003603601a201c01c035119100c4914000790003c00504108046681c3c4001e0a0308000c940c568000384080030f003050b40e00c0f0f40c1d121162840000001180c00180b0322540500c5000c10070f601d2698100022607910140190620301c1d100941c84410003102e01d114000c482d070390381c0c944801c0b00c100c5000348450060b103030304200101c1c814060a201410b2600004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 322307158 1250 322305908 322305917
    0x303020903010b03070e0a0507020703060c0203252f0301060e060f060304081207090801050901050601080c040506031303020109172a030d0b040b0310050603071a030a05070912080a 79
    0x4074001c181369584400348500c5089440c28400700d0805100380d0895900010584101d650f000e480e5280c00084034100f0540d100568000100c130901c0011000e4001c03060040600080300304141903c0b000d00c69440010100000c042c00041c8040515401d1140d454486020307008005503625202c400402010550700c1c94071400000b8803400d000e02c1c00100712441940e200740c140e0b04055104142203040c00f0040c110009014216101003107490302407080c076100b160888004186810490005010300c0c401401d0b80740f0b9584104010700c09500c4400460360811a08022423307aa910717810701724010220306100502a64442d04038084e03030702841c0c0242800071808400003407020402c00c0303215400d41c003000507044035420500c06d0b035840800a40c80403086080c094408281c00300c4c01400a030410500d0301161100e259201c013400420304003000001c001c1c00100380d80301181d910440d91045103000040903856680d84400014000078803921107035000346114603060304240c1c85403a2042d03030758022444940004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 322308408 1250 322307158 322307171
    0x100f23030c010c110a1a031f060e0d0204060e0c03070f02030310060c2406081204050906090c04030c030b04020f09042303270112060e06060c0c0d030302090301 70
    0x1440e0210311480c60403416110340c20070740400c2d540c0da000205240728540e030001c154480020071030310307091010503025002e1031025920300d48440542d0304200356507003041110700c20000038490725401601240c140380f412030310701001a0b09480054090035140d0400c01031034036880240200664108043e40c0a100c00d030f2501b00f0100c0000408903642c3c0030448450f0102c000d0b500c400c201150081c0c0d11907000500410f503000c0900b40811961800362480c021611400d50744840401c50032005008100112080500d8203240a1402d000a0420f10014104900c1410102e020072100c41015040b0303001154001d4290320300707680da410134070113913070040b07906a0003040341340708821261904256242c8140e900142d202080000e041e803005944030351070031011b694402048642446903c040c942d80c00504c6004000080c02d501e00c0004010100d20180005a00e040c81c0c005d000c4030303040300700703032680b00505844413900c232002071760b1142c40c0802c400d841c2e40c1c01030300641c0b14106041d416001094944d005a000b403101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 322309658 1250 322308408 322308479
    0x80708070902070c050d0303142403060c030a1d0703060203010e13050d0f030209090c070c150806010e041e0605030609280606031217011401050d05100f 67
    0x164400c02100524913081070b2030078001d500c1c000e40c4e44c180c0107029290000b070100c1c0801100400c00801d0f11500200d00e5240702070040c00c0b840511400310040141c001d01501e061141c4103090500020305294103ca89071580101c1518402d5000011070040404a58075990382e814400c0c000e52080c0a82080c0c42540c000080306c213900b4412103958181d1020040c04001c8804408941c00e00d031243d841010140c08001c918801d94138100158000c519800e0001e559629910b48607544d10156404043e08102d82900101a02e810604242c8d01c01c0c0c0a0134112850805400090300400340c0c1c091070076035813031100800b580b8614241d010340c007510310503070444809440e4419420358a400c3da030009240c000e0714040802904034a40c00c60b00c0c1c16031040002040d05612507689e038144100240321200001c01d84500c1051040c000704845004103d000c05d8000c9070301d007420000b8042e00c10f0100c0c03c80d00540350030200709002d034001d0500c0010b00480c040048104d03105c010a038511007440364110b201d500e01c98248283c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 322310908 1250 322309658 322309661
    0xa06020d1503050a030e0f0a03141e12090402120a0506180105030a020d060212010308180a03020a06050315041b0908010b09010314010e01020a03090b090706050301140411040807080709 81
    0xb0b5940010003825a4800c83d9402c07202c40b6041045150889448031300000f080e119001d0150245101e8101650310030100c459052410f00b0850401c0c103503940c001c4c8180c0e03403c04042115102031400a1b59903035510000303804a0081c0c46000c50025043d185001040150174065201c0d40c02a03008542004502845080310300d1022000e02940c0ea054006003011001440e0090b20030744500e1080502504002c4d43c1203640072459070076401616120070003d460305240c15417540e8118845130455800c5541390031900030a00190b1a4002c03076040c020300002141b0060111a8000c01200c001007043c84583c0c0e003c001c0140160740e0000070b00100740001000304115030180201c80c03a002001d003080105a1035600d5903c0403c1d0090982150703075607030305c88880c203500080c00200011080381d03e01080d000014035140c505144010010581600a00c9042c40390a5208044904640c4003440070806001c00c00c0001d0002d05e5510035402c1d10407000100000c2e401c00c0403c20b00300312100a029a007865644118000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 322312158 1250 322310908 322310951
    0x609070803181903030201150801020c0a02010e1f0f03060603050c160212031201030c080604170919091406031603060c0c0206072004090c150c050a06020d 68
    0x440e80c1040c00030500e41c00415491426014008016265050340418410f1600d0003981041c1c0050f5121000102030342c0b50980c0e2100107014600007180f0306284c0840c030b25241c440c840c400034100980d440c03000c0c103035130350b9a080c0e4007000c0f0365a5210503000011100107804900c0302540c03e804203007803800006c0d10502034030549104844d1040054900500100110452035003000100c1e0310401051418460403404c20280c0180c80d03111001c84459415400e00030342640d11039104070040d0b8003407420480014408010807500e541188841031f145d6030100001200607038440c552003103141c1d12050004402100d500204d02140800c0b68820040d1101001d143e26088145001e264850b9400002c10005080d40e20480006c00c0c0b91900120516469000501e103a014482c103661f4912080081401070381e1400ca40000c104049030200700300c0a05aa1326042c1002d04e106000014005042414000b40101c4072030b400740343d00a055078900c0d111480c185000b50441580344180714900304100d040c13250341e01c03c0c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 322313408 1250 322312158 322312169
    0x2309240f03070308030406090c0b180607080d0e010e010e030d0b0103050105100c050c06272b02030102042d05010504050109090b210c0312072105070804060c05060907 73
    0x8080c01c5042da144d00120f54809801215030a90f01c50303003003010800388040d4202030305060042ca5a55281d880030300303040400001e896885a00100030510014408108803208510b81610110301c0d600a01c25903401130680141c640119420f190110080010220060606a0307403180308011100b0044011003c40d0000d00525401c5070012002030425800340744d1514400d481001202c3c0c81c60903040100304a500a20ba48142020b04c1681b4542003800024440e2903032a400d50b90400d4201c1d180ca5a83d00c1080622412001540041515019901d081d01110007a006540300c1207000e12039034400f03101c0100e000c01510b5400c0100c5c80081408c1d0301c640200e44c1100c205075500d0000d281070001c800020039141049903030011500310540740d44008448415a50207008000d4511008200245418000030405100c2c09010800070307640001c084204841003c149980f250100b400c03007100c00d072058070070000068450030020400048040d4005001c184032441441901d08981b10380002540e2481c450080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 322314658 1250 322313408 322313413
    0x9060801020a26060d0c050a0b04091a010909020d0b06070804051c03050d020d1b023406030203071b0507180209090601080618010b0405010f020312012309240f03 71
    0x211340589801840304040500070410300c40c1003941c510000b40c40d070266234006480e80602040c00c001c0c0721028032400703204880c800c01014100e005600000d01c254107500071040840d03800300310600b01c030440b40e1001c0b442840244c40c1c035649482d01d040c0304020ba0000d2180c20720449808089403083e1017810b000800081e4542c65042c01d040c42c00000301c000e904039a0f000c020080d0b980c0c00c901c003440b01a000240482d01d0300d40190002c03e0a0038a0400c1c0100d10b10a00c00c5540740e0211541200d82c0a01c40300c004449043c5001a100d8030b41c803004448a4401070035143c00c1c0c0000241010900002040c1101118040700a800c9658a400c0c401b00c103a002c0c6c0c3c0000c40d440010346001600035401003428a511110080c0421188624441c407182010402c0e002000b40c05001308050059503040180003024101500046042014100000500300814050300e401c285c001c429401600d10004030201844000a08545003490280c17082c0d100b11007480c1c0c1c9070703030300b9000b036542000a41000c09086c02d111070058007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 322315908 1250 322314658 322314661
    0x1707030204050a09020d03110c0f060403080703030e0d021005060d030e040c02010b0607030503160206010812090f100e090709080a060b18010807062c01030902040609060801020a26 79
    0xc100c01084024114414540c50784d05500042e55101a031240c030520a813606c0b012640820041490480078458443c06011504443c2100382d9900082d201180e138400d4810365921004c2c60120050092844400d010384241e50b10000360580102d4642c09041448500304090303580e210800c074124034130319005008207144848181803424682c104500d41c00d0341d0700021511000c103401003181644101010b80000c2c00100900080d2510000e0178452110140f0051501e94101200680c881800040000401200040003001c0f074942280c00e0780060303401040014901c90b042009040210603008440c424484000010002c500401905055601e0b010040c019180a540c03000c0040501d000c1d142c1e405000e8021420f0361450004095028080580152026a2600320094000d0380c0200100100c4800d10990071403040315080544124a403d2a02040110780307400410002d05c1c098020021480c00d2441c0402c2944054000380307a4180d50703940e00e54018024580440a03119101d40501c2d903122143d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 322317158 1250 322315908 322315913
    0xe0c03061608071d06221e090504080f0a0323180105090d050a03021213050f061e13060e07051203090a03020415080303010f0e16171e0f060a170703 65
    0x10050401c0c2d1a585001b07010044000a2015080701650f22130110300036031030140304001c0000708603800204049030741400207003000c0d62008220300030854000c0c00381401190501840303110b0342143c014506082c0b103609074000246130b18451100b003103812180c001800100e86c00940e905124480c40381e80e40da40605402d40841c00704450a600100302d0344101a000c0c004402c0103060741075018007840102035115481144c034900b0600b405048186011180c00440c100912489540c0940c4011000854500100e0360f0f40300004025842c080400b4100d40c0c541001c003409801c000070f0180949074225a1040c8208000c00f00d00da5034400c04520b2500000d07003406c20030050405d60401031a124000036640e41d01612100c0c09e61441e002680006031040304e0000400c08035001e5104240c201034008485c04154007407440c0600203200d0448006000d43c0038200107404003400c8a4240c0340350d10052010070b1541003904288000790001daa00301d10881a0610002c2c9280004120a03038044030358003d800c0d29450764 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 322318408 1250 322317158 322317169
    0x40618120f030b030f0f0106080d090b07381303050d0e010b060d0603031407020906240d060e07111011070215120105060301180e0c03061608071d 64
    0x31410020b258981101940b03542d8140f20b140b00c00c06103040144145800c0190381400d40314550f0041e034454100c00d020405042d4486843d4098500c01100d403581d400c2c482c0707422030380703013a210410040074081820301e0b8407903d03080035034811481a03805409213241c0740c5a80c0d800070a010044000c01050003001045141039240d04240c410074100b600001d540740a4401154a96202080304501290b0f10030040c400c040e00f05264620200b210b050786820a0410703400b1401c0301c2006081d580c49458003000c03070144041c100002d550582d020b036168545810740d5a4800c80900503900484001840c0140040c4a0394843d00b40080380341402c00050405c0c0c41d04802d008002d040074040f20740a07171401c0124034003580300ca4007691118480c00040c00c3e504e2a83c1049038031002c0041e0007591140d04204010007035440389042104403400c004500144880c903601c1414917040900c0c01e02509800707020100211480810105400d482498a5515490359117a2040380e4615640030b500d9200c94440c107081e0551b0400c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 322319658 1250 322318408 322318427
    0x60e13050a0f1d0c010315120302061008010b06090f040f02180f03032107050405091008010b030a02100302090109090606030b03190c0b0a050c011401090b0111070303140f0705030304061812 83
    0x19a44d47c03101041d101c0c168011040121841940075074003500a001c01d22441d689040d00030400e02c00208041000d000000d8081d2281c1502c072803182d0b103900751600031a5a40c3d8040032841101741c10031580c64250018a107500a1001c0c0c54034071518042844c21018103020040700e08084541000700d0214109003184481440d01a00e96000c00c002444041000c4e21b030400f1040c003400941c4900f10b62140b0700b4075800c0c01d4541542d407540c0a42c104103404c100580f02e1440190480043e410f0143e00c0395130500040301c244801ea80142c0b1a1400d2010002d0001e4041e0b002003100403050301500d4000071038100804051824010041203e8018a0704000c00c102c0080600300036442031416525100c20405c5007030940d141d0a60040b00140c1d1000108180d410b60b2080102e29030302070921080b80400c99006685960b003511016051113000b0f0080041210324404450f005140c03420a103440c2d5804ac100241c0d20f420031502100c140707251910381c4074000c00c580004a01290301070402400e0010414007261207024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 322320908 1250 322319658 322319681
    0x70f030b0a0908041802040f12050601060f0c0206040905061813080a0c02120625090e040809120a110a050306070f03020c070e0a110c0304060e13050a0f1d0c0103 71
    0x14131020034582c40da0105580c541000f0304016840f41d060000302a0860525070000c2000900003140314001980862a64111112400c00c0c880009d0211400d840c3c07407501080095019400007004204001282e00082c001d5005950303480e100c040d940708850840030191101c1502054444884001680c40701c010922007001e454603410380c18259001c51540040d140d40804250058000c00c4070034a410440007184806480b442c0c1c1c101e01101c01302400584450080c4000d04c60200300040520030100e0844407450800b82010011000c140c00c81510303103110384822034041c020b100c2611082c1ca460031b402c2054a03c020080c1c8050307110250300351080303550200b160703092513000e0207032a83c0039005200d0b0308000c113a4004079035000e1520f031a9000c2101d14040034104000424880c0b06151070000094030195000f41c180f01c181c00c4100300c005442c4180b41c4080d6004182008100b240c2070060780c20041000c61400010300c00d0441a21a4050350948a4031a020961020700d005c1140d40c03003032704640461003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 322322158 1250 322320908 322320923
    0x30302120f0a0e010b010c030815030a030801080f01090c1e03021e090c0a0903030c081c1b0207030b072d030c17040c09050c19020f070f030b0a09 64
    0x2002200080c40d820811200619040303210030401a801c1c031140200c51001c0042e00080100c01c00e4040080c20b040340c82540501000310344800101c0d0400703803030f01507408038500600b10342500c81a40b43c0207240360713805d0080040c00e000e00c102d1141070401c14020040915130140132100c81c0d40c2170504240e0501c0c1490301215080a00690010250300d54804d5400450507010598480c00c201e00d05001e61004060003c03001840200561550310380d200d4032200c00da944c585040340f004d0030141040207185c0030780b00c4d02c0d410780c001e0381159040c102460741c480c4117039140e42c6891080d12940c002080c1d03100e561f10322000d80481e403c071000482c2030b4401c0510b03a1040c2e182d0b201303541405d0550114500e1054a010419001c00e40d00c40442e04282d8100c01c0c82a40c2c010411000112803409581d5201c210600e44109040e4035103640219480a2840c1d0507542c0c0841805422010002c490800035030b21030400442c1513440c040d0f0398000ca1081040c8401c0705c01d40360801840c01054550f101444010a42c0350815170352070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 322323408 1250 322322158 322322167
    0x61b072c011401021c05031f030209060d0203120d060f1d0c0c0f01050a0c030b030607051c0e060405061602010b030604020f04060e070e1518010c02150417190201020712030302 77
    0x441702005a4042031030a030307540c80d4603460602003079555907140700003822891916200410044e660005416030180c401d4400b407a02030410700c0880e06e00441c50090b841866404548144210b400d907000030210791103108a03065255440f800c440a000c0e242c4218220038800030b00041418070248000c00549810400319120301003801c03055800c4446c01d40c0e9108002c0c3c0ca84a040f0741140d4503006030b5010800440181040b4140550040d100c6d2186022290030903400807036054107100c80c0d5000000302c02c0e010040d46c515140500d0300e66120324041300d21140c404601455850341520501c624940c180010b40203050b60380b01ca03000c110081c0d4800508644c05074864074041098892841000e02400d010786070a002c00c40030004121614a80124003010f040c41401030980010142d02c3c0e01d8900345082c284501da1100c2400485c4d0188a407240c000a100c4c0c000400041050321408100141d81c104829941700c0940d684e00036a0283c100d010182c0140d11202c401d201d0b05603d00070581c0428030a00340103280 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 322324658 1250 322323408 322323433
    0x110604141f050f0a0c05190903230d0206090a0b04060908161e0206070221120c07090501060509010f09210b0f07081302061b072c01140102 61
    0x1d40310000c1910403034644038410f001c0c0b140c0500c00710075001030300000c0c04c1c4140896990020041d00a080000314221609610711003100d0182c400b040140d074001310440340c2081925031082c8160042241d0400a104042a070081e403403000c02c0e031501880d03051b009441a00540e44888041040c0500191079003913440e044040011041002409800c819190855580d500b5081c00c40c18031009034a60900140d4018101005035a90000c4910b019412580c0754001c142c4c196600814000d0344060000a114500c41060b41c5071200005d403a140300000112114951140d4445084c0c5d0000c0c0b10354000f00700248008541503029a4101081c0e0500c1c0c981540c62540c0c82036500c2d50200031245e0f403011501c40c644000107202100d18101da12507002070b00c0a2481c1000c0701c0062a102008114a1107000809103110440d560b040841d81c10907081c802c0d6050304418144101d81b01c00851249a02c2d000110110701400c54030340c001c0084400c00002c1c00c0b4800da180813141812000440700250442c060303201030250 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 322325908 1250 322324658 322324693
    0x101a011d090f0f10080c040f0b03100b0f040213030b091014040308010605160311070f0b03010e0939090a05010602010f0603080711060f0409020a09050111060414 71
    0x440c8a01015420b5a070500d2203c4148001c40680b5542c0b0f900720180c800c1c4014800081c00040c1820140c40c009480e490310490040101018034905502d030188040d03110142e50a50020a030002e411154184000803140400040388181060420804c812040c200041862542041d134004140f805a8081403102ea092404840049256003402000602484180359010074154003600c80c82c01d1481c41d180603d68100c0b200e002c1850b0007010450401100d81c0402800e2046500030100c106d2000170300c5848081c41380d1550000d00452040848642c0050809040003408540000c0440c40b00702403040c07a030300b403040c1c0701d54128182c036580080608601c4168450140251285413210f02c002495418513400a0940b41502c0c0000070003810440203001044900c0100d0740e0840c0d0080c5020040040080818403d024580d980380a1140204000941c44c40d80d4000308014101c0703a0f603031135505072a90015100b0700c41c040c1c0c5100c0d55a000100040020380300c0c01d110310342c21440100300c850074071441c0c18001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 322327158 1250 322325908 322325911
    0x1a030a1401030c230d0f02030313120519020d030c170c010b04050108010b03150417030106020f01110f03040602070302010605090a0c020c030c0303190905100809101a011d09 76
    0x643c21042d45000b0403140040800d208081a40c200b0256038034944100010300034440440c0c094101e654282d4071004540c0d040044591300c2c80310000c035000065881c141d9a1070719100740b40507102c41c01036404043c105204000804a000d038010f045520445094a0880d8000911002142d540030381c5010905070300c0c5005c0141c019544481c0000c68490501001c0c8000d460f410780c441d05c1070343c0c180300a45604c1d54010480c2c9032002c0552054a886035990300300314107056416044074005500000001c1680342e404a569003001210000a110298003903080850034810b0344a0090910000d0005c10001a41134000300109400b91001240194941d0300180200405542c0d505c801c6a031181c05a1080d40c06101c040300300c0030114050700851000c8c4012039100d00c501003400300c11107045104003007020b0140b19004003804014083c800e0b110b0140c1e00180100c2d4040e11028620300c580210090928214040c4110461400744041d90b07140a0200541d050040d000150f40180f03010503000301341b521101c6005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 322328408 1250 322327158 322327163
    0xf030804151205151c03050405040f140709150e01021009110a0612150503030909070c080d27050a11012003042408160509041401060e06041a030a140103 67
    0x2c82d4140007001000148490304a02c680d0540c400c645c860082500704017900c00300e1300c082d5800f240c07640314244250b002b400100e40004080b010b201c2484032841e44954101c013070b915240400141c00c101c01c10256100b003508001c440c010307404104900303100100e40d0000741415110b5081071a0350200a000200e41c4001c60304524009040c5514045031100340380a50b021420148601020782400e101c007290301e9114484610703010b0040400804c00b900e00c91030300802c001740c00080080d10f50340401c42203005809000d0390780c128200c10104002a145600b003844c800140d1040007820181000e0f5500c07291800c40306041c906102110418421303220305200d4407040945d1502c0910342d034508210043c04201d051517601c41d1f860311034540d611841a04020015000f252040307802d45041d081e10011240c0e4880d130100c054006007440c4540d4000c00051611134161a281c1d25103041c00c40c07440701030203180c0c0620701c12468a81000082ca003100304814004540000c6c041201142031796000440b0040590301b81c0c000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 322329658 1250 322328408 322328431
    0x120d0e100b01020d030b181b040e160914010f180603060e0108010203190f0908180a3206040f060c0302060601050310180f240f030804151205 62
    0xa4400035a4180030040002c13a2038181000b4002000c00480c0326482d00850380c50a6004d0300d004134006540b500d000c0b5158504021009503140c0d02d54030300d2008200e040d501551103c807442c0b0340e214414001c0b81040180c54035051820713841c0a803800115180c07940005080d0510a038000008505a01c0a040001800e800d480c0401ca16250161050f05148160300043d0103034810710500059417640e000c070b0202c0010420000ca014002c091302100100349501c0010f0404800180180a00107207140011400804413081d1100307075038075a180e9000081c0c082c0f01c50440085109101c00003000321036400b040c1c0030050101e60915031a5140b43c504140c007500081d02050005200d001090784c10803809074041000e10b400d030f00f9410a2000e82c030103a9200d001d20b024913505c1c0e1117605659030080e4001c00742258040c10030b00102542062449010300010b003002c502a00041e0042070804c91400540d0490354070a400e1481d040c0f80000b803580000c0b503103115204000c10721816806100f11401405d0050499600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 322330908 1250 322329658 322329671
    0x2072a030212070e07120e01050f04060506040e031c1407020a050714010903021302210a0e0f1009020612010602010c120c081609030f0b0402030d0809120d0e10 70
    0x41182c0340c00842800750703156104900038040c00d624003445581100e0281069105074081c2112400a0000090121078561822040045a00303d0031071180c02540103020401c41500e8042c1480b05813000141500c0c0550710070041da90ba030108030050014003081e000300005d2510840075950320040c03015590b003030069100e15108814400140a048000c01002181d46120a030341d5001030000b001d24070020f845819804507180d500012901100e441c54840903400c040c42000900c03044200c13405403002d50006280c058110303049100000c62203c0b484a2100a203450a0070441c0340004e80007507013040741c00100c1131000310100c100700341c1c2d010f000e440e00350004241440d070f450006080c012501e41040066040000d02c01c0400e803c904081e4110985081401c000c25142c1016666052190b20042507510840c000500340040d002c000340c01180300301c050342d0704004681d038100c0765200c081d2548403954210070b40c5070140c541706400a0503680d0b044c810128020314001400d90a02c100c101d52454090346610 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 322332158 1250 322330908 322330913
    0x40302131505032b1b05010e101509051b0a0503061806180604021b250515031b0408061b041a031803040f06030b03150a02072a03 57
    0x25020000341c501500240200301300c101498203580c5885001d0003c48984001600c50f891040b602e14844d40086201208014441d103403030781c0280420503450800d80a01c0700d002d4440201c0780295086821146070740f800050501c10004001e05016194419482c92084021044010f120150503070050b2511035540340c0c9000c00610044890400c440282d400c041030402c505541c80021000d0f002c040131098903000d68603180868028407440c15441c520110110f401500503200090030421000840e01e141781040d08080d40c1c400b460003134002c86134800c2e107285400d2010004540596445000203c802c00000380407a0f40d1069544603400c80f0000d50009410044802d01150100300c0150090051a1406140c80080d16060420308501c203864007001001c14888840160340741048202e01c000d82e07a4540d500c9021480103e242c0c800c0d00b0100f070825000c508213140210b40c440b1900003040c800c500a07a41c0c21007810095000a204541c06988943d2000090f2104000744408201c101c080506050850 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 322333408 1250 322332158 322332191
    0x3070e0415020703050a110a02090a150e04111203040504060f03060b010c020906040b1807030608120a051206040207050a030e120316080901021005070804061a011409030304030213 79
    0x707029000989004000450000790702c04200c64100c28986000d01000e1000b0742503c3c200082c060001c1d50268502c07040c002c8400107580a074041045601500044a682d44081007100c0c400f01c0d0080c001c0a003040001c1ca540c200a41408001c0f42440103480c5403030746400000e4121104e1707400128a400c40c006052080110034420b50742040024200200d00c003e09a001030318144c80103122500a82d103070105903825480d03825403a551811145104007091030b054400800805043c42228210701c251000d9042d681c82d0f0074100c6508002c25a18a80340080006c541e20301c03108081e0030b43c0e0708198204802d0300459824007071240d4591290f96403068a400c1002000100840300f140d00c051a0070800080100d200c0300301d44090f41d1a44481c0c3c4586450824006030308050200c291100001c5c28002001009540400c1c002c1c41244299030810000003284023450781740045030b05050100e41e0040050070004903580280034406001012030f80380a07100d41c041880003005444521002e521210748044c5c66120 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 322334658 1250 322333408 322333433
    0x12050d06030c15020c0a0b160819030c051c0b15070f1104020c030910210c020709020703051c061a03010f0e0903030f0406060f03050c090c161104020903070e04 70
    0x184c402040a0041d2800003003581400d403042450078031002504407024082110030b900069081500141c4a80c100e0032042c0c9407400300301404001074900320700d82005034002e07002e0ba030110702d02424844d168900c91000d10001d140c0110407692001400380b1800b03050705a08028007400744101c06071500c010081c580080185000e0f14081d12541c01480700c880000d000100f600d07010740f41211241f0b0a50201c09003600d6039840603c0449800c091105854201306242e009041c1e00180c5d54200c1e60800d40d108819412402550001000070380c0402c64800c01080202600c101c3d001001400600309603503151030f0840c0921002640c4002201100422018504503042c50050034210105032241c074040381c1c503a80342d10000b4642101c03640380b100440c00740221540410094140780740c140b0411922030510940d0303414207640e5284101882000030b00441c0c008001e4503601c03009010a039169500640d540b0050000301c042c0b842d0815030a004681881c0c0c0d0420035507008080c0010002850705007810039600f031860 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 322335908 1250 322334658 322334699
    0x50d0b03010c0c02060913020f19030b0d0201030506010909020c07080601050d020303040e0a0603050304090204080c0a030c060f020307060609061d0403080c0313060c200a02090412050d06030c 84
    0x2414002c0640d041d000155031a0843d4101c960b00d40e1800920700042c502010310001d40019480401c101ca41c080c2d05d02c004000c420708107000b801d14200030140032410746041465603a008089421160b0040d4029082035401c410305040200901c0d840d60359503800c903082005600000c0e440341c0805c00c09210140300243c09003100740c801110f6111542c0100380e5901c101e209805950200340300142d0310014650080000d5507000017540d5031107542d148010302039005402061030ba4050303003041d030f005880c0600110080380d07403056241000ca803502c03500340c540c0c0041c004440d003036010070009200011014418200640160744000030414184034400300d442040c400110481a1058207000c0802d400941e1540d11120b00d92500c0d9a85d6030b903800c403204103148810020a030701d00300f040c504056508900080c0030801c2102c1e841f02c035040071210095895a0b00d0002a40064501d400319010440d011a45450080f1500707010345824071260080342200c000d0381c400d8845402000e014810007068142070641c105 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 322337158 1250 322335908 322335911
    0xc0510050f030103080a0507050f0c040614210c130507080f040c18060909050705040b0d02210c031f0f02030c03070c060f020d0603051e0303070c0f0b07050d0b0301 72
    0x640d500007024070040c00050807016001c41c00120f5603101e002103c1986a00c601920150310f150308000d580c400700c2c0802d061145040c2000418002c0c502c80c891800c0040003031030b20044510201460401d19070701800040240500d07040740c98951903115650410018810002890b4a400c4000400980340900340d501012115400e1101085000b940b003400d0b208180604151149003800d003400901315070b4030500526090070312200512001017440822134500799010b010038107000c0100200c04440a400a40c0000341d000300060300310500304403040075102e01040300c46000c0c20700c00003440c0214441201c1c0310042d1000d41422190007500440710303184941102035045080a860200c00c90100034401420003003101401c409220890700200c5440318010407c40d41c4680d03001c5c0145c0a0502030200307079a188a540c2b81c144c4600503e548001e865000403000d1421502c0e081000c490310615030078141c2da41480356602c031011600383c094950003801980c9607075545030f11040e446015580203002091083c1d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 322338408 1250 322337158 322337167
    0x15070506043e0105120405010c030f0c0212030a06050a150f0504050906060d061802130e01120212030405090c0c011b08070c0816081b01060b0409020a0e0d0c051005 72
    0x1c082d2488085401c04200741a200d03622180c012a024050300500740800b400510600c801c1c40f0040d84131442c0d070b1070365a4007844240d511009000540d00e1400c82000185d0245a804410b0301856010b1904107080c00004079521f0b558038006200071080e60440400105000c440c0140301e50840c03d94481400b441c02c0c0719041c6072030300d4001441c0346002880b45c0d014500010b80d0301c00b10500c5911820141403140340110310b4885610403c4003d40121000307007060107900c0b20225070f903038417180d06504031544030b803015900300031580c213102140c03200d004100d580b03100600003c2000d40c3ea100c9454400c4240c1105291640b18260f256070030b4440c04403220302d9000503a010308048a500c40c40c065808020f504000039444450b1600100038412803161803460402ca0201d0420040004010540750751240e50325640d49a00800803400c90f0040c5c4190344211030104000c200b20b9085030080c00d01c0c0c00d402c0c2041c020405a220201c0c0303005021943c21a2410300d03100c0144070615107441d1032341842c41c242c50079a051 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 322339658 1250 322338408 322338473
    0x9030e0306010e010b030a1d0105091e0703050309041107080703170c131e0906030b04032003070f0215070b1014060d0e0f24010e060d0f021507050604 66
    0x17a8400501030000c03480e1114189140205400400b17103440c09940f008002918210706226203407200c00c206a0a0740800e0644091440c000150034400d41760450041c503d40074060701080010700c403192a0b1403c01609204510108800d540644038241c026180c0e80c90003507100800c0e00040d0402000340c5c25068052140c2c25404260700c54a0701550b69040d010301050061817a1317000f070710f805036001c229040d040207804070802505001460103141310fa06d507961082c030300d0f10010f0076030081c001c03d00c2003550040c05160080341d40040c000044500260503d591002140400d040300d6004000503102c8802a209202400c00c40c00c1e1113100074070190001c1e010002d04d620008820b0320031540051041600c1e259004041501801080c1120100c04111042c5d081980d6030309084990300c1034250b00070030041000007411001c4000b035070721030303400107050300c0310340f00c86940700340c020b050642c0141c1e0014814001c054203080e0b42c00080001c0c41c0601e0007007046141915040864004030b80341c0c8640303402502c021502 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 322340908 1250 322339658 322339679
    0x90602010c030921200109020306090102031b0d1d160e0702070611030f1207020d021f1508030a02210403020d140a0b10092409020a030f09030e0306010e01 68
    0x70114000c00d040c400c0104c2440101d6003a9440c03050040d00011700f10f000e0865030015400309141c1c500c240c0541d603c903510001e00382c1c01c03408110f950580b8422144542020755090000401d010511381c80300045258821407180344011018803e01215444910050180061000070340010400c503405041c1c1071404481c000d482c0c008a103c1c8070b05020f240d00e84c40d4111003040c415250413030703001200390b40c13660850f01c84520780783d1085e106c1d034000d40a8a5a100d02d854030100c2c02188600c0c143c2c2c01e214240303031034482c0303240240802c0302104901c0c501f43c00301083c8540280700822024506034020103c180d000c800c4030000b080e1008540c080340408000c10401078540f45005078036907030840c50702e20000c2840001d050034204140f2002f03118411200030448015500c3e40c41c0b10075589024010003110030150b46401d0f0f50782c1c12060454001c0c811010410121260b03030020a01c9000514012034130105101d51807007030b40c403100c004401103103044481030380c2410704005081c01085610425050313035161460640 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 322342158 1250 322340908 322340933
    0x301030c0503251214060403021501090207021c060227011403060a06050c030d05010b130603020306030a02100e0d06050a150b040504021305090f04062003060925090602010c0309 78
    0x10002e0b5200d0b0708014461440502c0174010b8400003510518581440d00940350b151180d00c85441c0c040010011800c1580b42c4241c2c2c0344164084c003020220341e200544a04c40064010702143c2c515000c1244450100031228008a0000310303010044030304210a0000d0003001201c40854020705090041205a130348a0403040200c074814140b05550708007a410b1309086100707840a450589007010000100f00c0700c0130b002031415006e00b4908403407440e140c40c403c03800c0e480140c40c010340c503900110444001d850310107401401060a8203150b0050741424021075807440c87d2a101351140c541e2502003106550381030107034000030021414518216820b0070300c6140c0364051801018040e42c0d0106003100b20b0b40d41c0c3c00c203081c00380c0401080c41d186407420141400021500316002c690b6203003010032000709190029582c141310410b05520504507910f04050240349072009009400d0482204000144415208413031001070403da40c070104600e0034114007034250742d62490347c1410186044503441c040755244140c0c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 322343408 1250 322342158 322342169
    0x120905030703350117160b030603010609020a0e041104080a110f09010b03070525050c011409010c110a090203040c060801050f010c0809121b131103070813080301030c050325 76
    0x800e40341603204103580c9000861901500d9022103542d007c2a01c040460203144100b404800a100f46a00c480c10341041e400b444100c80c0c046400900c40118034a0550028849401c03410002c03401c00c2d070340721001e82c5014100c0806940810000c42c4440e0319082c80c14002395804419141842c440d403400d014405070f448011b088504100010075085c401d200740c2d00d0303403840d1044940802e10000381d541c180f090706d8400c0340050b14041800f8500c41c0d5821110441680c03c04c45058451a481c2441e0f80c40e850703040c0c5403038207049511100c1420046807017034281c40914002c50080380300c051101e0034081c000d0f040010603005544941c90341e08a040c000d030f078081d41804a080d4083e040355106c2c000d91000c14012003941105c3d100078000d001820441d609041643c00712141c0803107480c94803521881030f44084600c2c90303804181c40c550800000346c01c1c9004113041a048940c1088030038004002d5250400607070001c0e04108d4440740c0c000c23410400c80c0350805c403400128041d0b05200d101c1c11000c00654100560b44d1084 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 322344658 1250 322343408 322343429
    0x1a0a12060b1c1413030509030105270601150e0d05160305100203010b03220b09060901270609030216091506020303060d0b10090e060901060b13061209050307033501 72
    0x5130405105009444002e00080c00038051410309010103030f54201c21a001043c1041e040da1101000b00000551904848840400c45205040c40300100c40120b40c1c10308280d040b0300d1845854002407c00c12500c0081c00c01c0c192601c44603803c40c41c005007000f481141c5062418018801800f01c0c801072001c803070f040082001c03031000d41d035043c2200e01e54014003410061310b0b449002c0c0c00c0000484001c10002d1092034000001c015001e102e101450f50790f010718844e0b408034050000d60500044542c0d01803c640c0c1d000740115215010091003017400c01e083c81c1c2003111216101d04000c1076202c0d0070300e003800103411140007841c110301e80480841c01840c540031000d030100241901050a500d81c0c0d45403070002e04000d03d003d0105044040105d6694801560030501da5031174040001004402d5074155850b80d45051141c0803090718000c4200c03030003c1c402001d09030b12540d903810b03400051003c100410340d06210b910758450316005035a80b40c805644440040c1d50014010710914804c282c40000ca9041d80c02e41001c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 322345908 1250 322344658 322344691
    0x6050304020406051e09013606050306090a050d0801030213090201140a02010b100f050a030c030b0a120303150803070b0a0209032508071a0a12060b1c14 67
    0x15001e40b035194422a04419010181a45c1301d030704469800e410781094a400c012a60780f40303c000c00b02d08028078000c10403038490303c070301c460084598840300d0911950400821003584510000b0308000007a50720000d190701c000303e401d04100060118201602c418141000503601d03540100741500d1449a981000c5507440804108680c054070b10781c400c030b40301c0044903500c2c0d2028860190007400700c4155070b84140c400d10030030280c0e02c0c0320310014064103241d540e80300c0c1040398098042d405090000c0740c61080c16120b047c0300e08951a007040c508000e08080c030f03500141010303a06018040768445c2005540d01c1603410014041c4586c00804c5800c00c0c0d611400000d0184d40d070501140c000e001e074001459043c095100120b40e5085020011039131020641e8801602540d19006256240e20300c0c41017040c030510086140c0030740b9180201402e010b600328102103003145e1601d503a00d0f084031081c0d00501416140811803000320003c0d02030402e1704500c4c00c0390810024038425120f0780a50300081005096105112 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 322347158 1250 322345908 322345913
    0x90d060c030908030709050306150d030f020a0812180a0c05011404050d050705210706031e0f0e120705030910090308070501060e0601021c08070201090b0a021806040f06050304 77
    0x902c02066036421240094603030a001c44010000e032407038402d280c400e102d4070010640b5002005904c015942c401081d42c18041d0044d541900d50310940a002c000f580501c01c0340c0404034005074018a04058140e162034118500403081001d40d0041c0f010300740d080e070301c102d159400141800801d1406e459003424103140410700f96441d24140d10640e009581c001e201c0030b0082042043c00944102a1003003151031810b01e5081614408841c03101d104915025480070004002407402503100e50307406c050340c00800714800d42c6141c414040c0e880c0c0c81c845034178103940d034020740282d400b0511101c8420002c60914615104c1e107926059560300070480f116103e4a041080c0004072070251358100700079640081100e4481e03e403414520300a0070544165420707085200c0015a9542c4082000b5240c0a0084240c10364040183c0c0210340303405001703041c0710642d980d441546000c1160445524458a145200036a5400c0744203a80000c102e203600310b007030090b1f4041c0710074030a003485040c1d008196241031601c99280e94850 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 322348408 1250 322347158 322347161
    0x12020f12030f0415031103150409020d05030307080103030e010c0203030d0b0409020d080705070b0313120e0315060f0411030f0a06090501060f180503070e06030f1c03050903090d060c03 81
    0x10030072038040701e0020b00000c400c0713064203842c0014041d6032400c0182020100006403a40b00490342a00c103603c602c3e801d241145020f80c00b0391083e50000d4104140000540c0e12985907500c2611480c002c141060010420954458840900e241c001e2034502c4042040e503010a0f501c3c01015030000034540c960b0424083c9071901d41c40304507190740082849100b0012410605001c0c0d000f201c0c2959180201c61004c600e000c20300040f00e00601c03140d6104032a1851540314181c0300c40000100c3c000300b2100011880321590108200110340e0385010442aa03410a0001c2003590000d288201d80140c0c1041c6504a9880c044e03403e603980032a40e03081403001541e801d13a03804c00510030798000450b03e52500c4000b1031601c1e805281501d05104070388a9909064000b1488010702040780301d010b5055000e200d0030710010b001500496040580541120308002980c4592810600c42e03459807000d62103e1000004099850302550303801c0395102018600c0c00c1d44280218035504600314015081da9100c500d00340d0154480d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 322349658 1250 322348408 322348417
    0xc010305180304030807050d050405010912110a090b01111207021002070e0117060601032f0403021c02011b0201142802061005010201140403181706040c12020f1203 72
    0x76400c1d030f07a5940d142e02c0c02e5803494200b0041a44d440c804c10740300c014030300d006804030b40954a05843d0702e62118a0001c21062040345080102c03020100c0c0d880c1408161110308141e00034215401e0049203006010780018110481a032014120390701512060b900b680242045030052501901c0b0780b507c0d460b40c0301d01130346000d0a030f07400340d0700c915164000016002058000c200d266070f810425210705840d81c400450959000144500808040345203216280403402241d4001da85039039003440c00d0a0340c9400081c01c1c99001c0480300d00c41309503003c1c3c0d40f0856030310090401c50781440200e00102000035400080140f402c2440421088a00054030f80301005062024070030140f090405411488400c0c60081d103480040c5e900400d142a034000c00300e51503006000326400204901c0c1c000020f9687c1d074800701e5001c070140c14007220010700d00c2408940400e8a541d6a5140c0ca2400b0060081d0306251414660b0280c140d840301c610501c80090b03010040c1c1d1242c0301d03800041000c07103403d55402c00c03030f02c01035003103104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 322350908 1250 322349658 322349701
    0xd060203090f030a02060703050c0306090a0b130f060920070231090c0f030305030f06180103060605011209080a140417160602120a03020d06090203040822080c010305 73
    0x800305018404c10750026080d0320528444e40c0512154071154540b003e030380401c0e02d401b50700688080c001001e0303500c03944c028070341610010400814960507440007011100780d440b40e100d5840e01d03590240310740200750140741000d00c1c10981085040c804400100c2c02070040e924001d11516036525043c40580303282a02200c43c43c02da4001e819120358048580009144003101103482484500300055030000c901c0180c401c1341c0c0c040d15200e00d0b65030381d221810f940303000c0140f4099102540351403501f142203001045502a61150f90300250250030074002412580c401903070a8203aa06150041700007039500700640b04a0000c604180b03544010103001106603000799040710207011200c040101c40c1c1080041c07610090141d85850720307049130701ca4804076116009071050003407968040252000c128030a500500d40304c000400c0014801d512442e07844140d074000e44055400081c082000b1300c0d004a8404512400d681e45a600b840b2203203003d19968a400484109506056444000030010325580844c0940c401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 322352158 1250 322350908 322350913
    0x60c030a032316090503060601050403031b060606050d0608010c0e091803180f0603010f0e311203060e0a020f070f0b0f090a0302060a0507030f0c051c0207020d060203090f 75
    0x1a0542c60140c3c40096203208800140c10f081000640e4240401c0702800742d94107031748007490309095460950302d000c0340c070941c0e01095644c1b481c00ca010405520690025104655070780303595101d054039403001d4410350340110885924200880e2006504044007044d940c5040c1c60001c91903039202d50b242c6101d440d40840d01c81d1400006a40031713000350010751482500d1070499180001c40b00900a201d60741c00b003400f415401a403103100500200d031a8a041c1944054a48100a200e41c100300300c210740500d6560140c04d101d03c02032007940420040480145800c1c01924040090910700510128031403401740c030f0117001540c002450301c90500514100d07505260040b540c80c01201c950710700800c1080b41200d09452200001020a004002c04982400c80d1a0941c0c0107180f0394840300d0b1040028500070b030079801450b07628106100500b45a01908403000605d40302c0c41d8640401c104846e05503942100c442d1005803040200c807005079101c01d40c02c4441500403100580345da54400340d803840c00324062190410352 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 322353408 1250 322352158 322352161
    0x412050c011103011e03050a0b0c2502090705030405060a0c12050c030601180308030c1305180a0c090b03010b071b030b0915041a15210c060c030a0323 66
    0x21000382c009604803031140b07411180380c04145928407071031580c0c0d01004103a41c014000359804101031032a256008000d03102c1181c42d02e00b406065945042082003800440390703420444200f5032400c041d4055200f81d41341403051441c0780c2680c907285c850000422492042d41e8503100d12010f81c1c8990400c40000c180b00c502080300b42000d04401c00305800482e003190000e60003500702070700840d2441000b402c4075804040f09085440d40500780070544c10222040303040c02601140012640d840c80c9032400281d601410440b100d08047d2010001c1d00c04640d14001845828041007100494410840341110010103105851700040c1c545940d40740c400070110040f0800c4400f001c02030040340c98900d402012000308651b4a00300030301d81c1200703000040380c000c0c01c42507604840c0600b05018461560380301c1c90101e01600c6401c41c1100164018110b007003000d0443e44c10008000c07008100704441d06d5014001c40d541030400c50300c2ca01565691003a5590300c42019242c184901c0b20700202070102c1e880d2003013a001014507 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 322354658 1250 322353408 322353431
    0x110604060305150105090310020904020d23090601080c151b06071d01050f090f03010c02010b01030f06150507081303300509040b06070f0812011d0412050c01 69
    0x20b000c1c182c07000300103400c1152100300c2039030040044a00700300e00503014201c1040c01e285c65000035002002c076030750015002c000603884071010f8030a040321070390901015050001401e5003000104e1000705910038076408200180b00e035040002d004003100e1001c4601e040b5031030000c900d01d4202d001e01d91182682c03040f00c002c051030b402d0380170032858490b4076196109072a00108111034440e420144203803e004c20002c0115100403d4694000d2070b0400000d0034214231800c800010074211034a5000d0030b00141d648103132015441da4140120340d481342a401003486941d081a0160316915a1581c001c400d02000103552800c008169083c0c50701031a0240011500a83d6800c00c01c91552505c0254803180039050405002584e900e92602c140007203a99400741003010310800d100081c00c03008041644030300705100c01400601c1800307149203c68440c0c10b88640715511150040314052045c0c005005900d03100f9841d02c02101d050300c50580c0039030080c0b0803021042410710151010300c01c803002ca407220350804018400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 322355908 1250 322354658 322354661
    0x2090c0f1b0d0f02072102010201140408130b030c04050d02011106011e06030e07180612080405030609030c060c0a030b0303030711060604060807140f0d0c03032a020d1106040603 78
    0x40b403076055101c40400501d2214220b880d40f007030340a0704038440384000303c44c0c44d1500042481203009106000004400c20307143c080c948500001c40d0200c81c4001c0000d10180240e81c0b0340c840308010076001401e94203508014042c003056001c0c03800703110b0040c207414030700109681c0700300d04506540c00c2d4102590502d585a600320002c010003215100c40800c0c2005000680c07610a1084e1000007940c04003400c0c00c9800c00000f00200082c0c0e107100c114590f107a40e800300b00075080b01c05408505119140386540c0303914040505080c21401428048250014015003040410118801d68000000c82c9030301d03070b40c0e0325824065004203102a02c581e050b00c0003004014629400c50f20200400b074900d42102e50316500c2d40704100c19100d583c01903196076084964100020010098a030b24450720040c290500104283c1c00309104500c544826550081d06040410a1580040d09002880f11016481c480d0825030420008081e4a1810003400760410400c10003c2c484218014900214028510b540d0340e0303a40e5000a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 322357158 1250 322355908 322355923
    0x10180b04030504050316030f110114040b030114010813030503090114040609150606020c010c06061205100e16030813050919050603030309060408030a020405040207030801060f08010302090c0f1b 85
    0x42c064840d44030300d8022824482d580380e040300d500c42354220540c0700580d01d28848250b940d00040c1800101c00560f120101d02001a0002d03100540809031030398034140c41301881001c1314100c141030042e010103200c0a000009c13611000e45416040241d62034442552990040c00700c02c07401520b0004090910041000c103800102246000d6221041c1d0241d140700c0c0740040350707032030b10420015921480d001300b501d5000e01280e81509016880004a5595440204d120743d80890021545500501020b1102200da44503603c4685241d00050890300542050941900c081c2d010243c000c40c0040381d0410242081d0200344061b15001d8808009070914084c0710070050b089450310343e031003402d1800140c0541400003d50340b00e04000300040042c0e03189c503151815550f1000d4010b07410310b50200404078607501d65000801e40c4a200b50307a942095850440000d12800c40c010041040001440042015a8a15034140d4000e82d00c40743c0b003030391440c90428007000f078402c500b0310800c03001680034913000314640452101d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 322358408 1250 322357158 322357169
    0x30f0c0910080627070309030207051f18060906031a03011e0b0d12030207140607020d0806300109020a030c060f0804030f140c06040b01090b0a060210180b04030504 72
    0xc030400141000134010f50f811990381904540740c5a00068031680c82500844030712070190042c2d0f460507440d100070507546551900c484100b8072400d0a1100300d0b075441903c00d21420340744400d4261050801100609000316841900200740d03d50340800c900003018903407180380c000c000b4004c12518118594907400303803010307201000d17901d4a041594201403c005440311611035103e844005029081c2c007044c0c4c001e410070b032000d40310310380c0c00c17078403003440d15400c101443c010510f0790010607603255460781c01080c09000415032030017940381c81005400b121081010303290040b1901070903803544000c14203144c018241d400d8007039071010242c00004107000c01c4640190a40340b980d41c2d803600e91480d280c000e46951030143e0b00200010f0342c00c0350308503242e0b2090610706220100700400d145011880081d02e464681e080d1002e0713840c18012401009100510304c644414010b054624070000d41c600500a900d41c103804d914040c409894208031520304440c581924000b0394080e40400c614100b504000b4a181c1082c02007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 322359658 1250 322358408 322358419
    0x60219021f0306030510060302033406110705010c050303191104030804090608151b071a10050f0612060f04090c08070b0f0307030b220b01080a05070203030f0c09100806 74
    0x40000d0041030b80a20400e6035006001064118205280c0d0b01420004035191841041d030f40040030080c0d00c5000e018401080d55537516041400390200240c10400254810340c14801c08481e851700141e40401901d606c2440c1880d0164071403550008040544240c0c0305c50001c0c0703080024080304004800c40075000355000c12004026064403410800e5407180c0061516142c08032140004500441070a0032044910690741000d08100c095500c4a12034028464404041c2c0841c00802c42c01c1144007082d00d00600046848040c168600004a0a5841500c2c0480b0401480d080040c2c0390341c80d8030f03410008640740940100001c150307c0c00c00303a07038110032400391100c00c4c001e1903000580c0b0780500050304d401921100c22549580c56266080c2e00500c0c41c051581d030810340a0300000b80c80700c0190702d080030000f1000d0000c81d817051000e000600604006040040c15032504050185099000040c2d0341e0041400c003003140e0300d40300d082803100036000d6882c61030ba008410000341070415034032621450199406890 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 322360908 1250 322359658 322359673
    0x212070f0b0d1505030a02120102090603010306020909090a031d031203040308040506010e06030c040b19140f090f010302010c0512030106051308030c121b031b0c0901060219021f03060305 82
    0xc0c00e0f0303140da144101c5606a20003841e81c0098507107000710300c8210050034001483c1104290118000da0000da00a98410390f010440d08e1407420045070441d8869010400707810004815031700034003203500184c0b03030a4402400700041010794904100e503036850f902c14018540c59292520b0010031508003242d045442d805480000111503140c01b603414011007000b4080c0c40110040f40038840280b005c4103100703510141c0c4410030f20000303403204610300150010419180001c101103040c08501c1038092161801684003100308084074201031840381c1941e1742480c0144440d0850b00388a8035100c1c1c4003000d0807003a0800000000c4264114000306048864451251403280d8bc503000503450307000b4402001c0c2d42d500030144940f40401d09800503d0b140301e40c075410101221484101910716048070341c800d60960a0448001c1e0024020402d0080c01d0b0310840e00100e0b03d41c14141d0082d1103000703d60402d0044907041e03070000215076030325450a28444604130400039006d08900e004018001e181300541760b80c0900078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 322362158 1250 322360908 322360931
    0x609150503150a0203041a04060e0118020901150c051905060705090618060f0a0c020405011e030b07020312070201090b01051f2703031d0306130212070f0b0d 69
    0x860b081c0040c1d42c8803a15106589100d511000307540014011035101d411404c000c040c206440c543c190159004150004607001c031444034a08580c0c0070078030700e20911080360030140103903190428541540c050201381180801d007440255010354500d4401031850207641c3e042910001428140e00741e060180084480035114548191030a104046400750006000c20511040903007200c0c408152200c0501042d14055120446d91f645030010a01d11340012060000c080c20751030103006550141c04509940c1c540750004079943c04440c0b82520004114085450006040398001c0c01660b100078981410b001c4c0f6854010b00080c000c19024604480d03841d0b8140002c07c0341c3c140000c0900039500c00000300c05101041290944012b085482422900e0390300061246104407402c1125000398400e0312005079a03a04202d000041420140c0d000d406136018004000001000c521031041c00394041c3d45440324068440525401d044e844c2d0054120689000c100207a0400031070010945941542400c12102c100c1c403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 322363408 1250 322362158 322362163
    0x80c10050105010e060a0c020a171624120212071b1203090c0b070c052707051803070e071d1810090e06011703091503190609150503 58
    0xb03004903800030308039554034115800c042009011402c0541004071581d10560b0000e141d0264607005040480c41312486080c0d1034504100c807251100700c0055103010a0309011442c80a823050705195441510302e0b08140c0e0070540074881c1e00e404100c0901095607611380e0011020718560003521360800142e1440c4030046801084c820483c0c0e02c0b5403102c0074442c0e0041e00741c4200c1c00b90840003c162212003134003c0016142c1100c50040c007900f8480e0010074066032411042161003803030700c1c9060720300005484030f201940d58443e03da5036102c4101d08042e038941c0150070002c1c0d00a441030301c410b50948280c600100341c41c552503807064031900480c1e4603500c281540d215260341030310f03c580d0410303003145c2c405200c0184500309801540d4030000d1a80551405503940f03601c9025a1800c0c500240a90440c034010b00c1032204c200941801c2203801c0300190b142c0b22107040440c1d020800e02c2c094415440307002c0042100c1103d00409010200380e25a820700815449a40d00030040c8000300c1003d001d00780c00c40740001d40741400b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 322364658 1250 322363408 322363411
    0x3020108130f38011703040b0a031e020703080103060c0c0c0506030a11070f110a1401120e0d051309050c040b09010e100f02010f02090607031b0f080c1005 68
    0xb02c01461040e142a940d00c08411284001c1c500f0344204090421559180d5464202c040550055000301ca03545043c0a81281d001c00f0041003082d07400420080c00310007644412900d442e803240c60001100e0f50034110000100764001e01031004d640c0009590824507a0000c1c210f4103803030140c1d000308103407240304c0c0c02030740c0c3e0b142055401001070425150801c958605100515030000c2e44440204641040f0015941e6540c17085004648803c40e04402d0b0090041c6034248441d0b0074020364501e4080c50401c010144042030a040860410044000040141d8080c1d0032003107107140d90500b01c42c100140c809020342070f03130400d80c1054404036120b4000107103c40a400f82c00d000781c41038241c1d40d01c4c0504101044e02c0c1688401602b506001b191071041a89840b0342d40064040c185581e5001c5008828020003400e41701400d0310b00c4610b034014407890000303980d02011146803552504002a0380d215400220360001200b54002d0728481001d90f0b0361302401030003001005d141991a080d15008103414006804a400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 322365908 1250 322364658 322364663
    0x5060105010504260102070803040c06110c01120b03120406110118022b020a09090b0601020a020109060c0302011401090903090605041404020912250f1d0408040b0a03060302010813 79
    0xd2012100400084111111082100800003d843d2070740303548800588e503000751411156584240010813000e540560040c001c00107140c0540704190b0840300081205480c0800c508100e561003490141c142ea0420041c03500d6594029202c0d112a81d60802031b010740f00310121b040f40ca500b0b01c081c44540a048104400c14950300400d040e001c02030070054008904450201b03003605a5940030880056591a00584010030358100301044110340c40c80d00703148643e0b002d0565030640d4040206040180c3e002628102950420f04c0c00003044445400c04034090031142c8099512190008000704151321a41c0005e10054009c2d2100d030719039a034600084507203204501c559072284152404402c406c3c07406800070800040002c040e1100a0000d0340700c0703420206080118031025018004034070640300d881c0105802450741214000b0401c0c50700800c0654502e6900124100820140002c1c04008001e810380f00a03000c95440340303889441484003d401803a01c0d01050b80410507500018100f119581e400c1c212040c1d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 322367158 1250 322365908 322365929
    0x1d160b03070903080403110a05090f0406020a0e0604090b0f060c03030a0207060605100806040518120a09030b0906040312020307022d1f0606090e0708040c0509070c05060105010504 79
    0xa14229421406420280646082202014000010036142c00191001d54011030b2480c0042081074100020125164003460042158000f0482454000e640113648950004005641e40c0141c1030102c401e040c0386010164481408140400c002d00e903644180150030f0140c07590611144584100724150240f901d000b03106034003c000041101c1010340181504a218081c080344084d01e07540012104a0390300220000220700d4010084289071a010311600801e40940d05800344c00350f0383e0300544030b6a410505540380ba0300041c41c282003d10032042400290780003020600a42445103199448000645003a400291a0340100d80044a10310890b805a0740e1600200440480071b8001c958000c0101041300f0040e484d6a00030340c0a003410302400002260304001000b80d820703100e88400850341581c215000300140d856090100701d100c03280c115040001810500c40c0b03640d035031a251030fa02d000340d08071503000300760b030018400a036420020b5131071114400d4064604036030b00d0340c00441d41401980f15811000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 322368408 1250 322367158 322367203
    0x15110c012a031503060c21020a02150c07021f030b0f01080411041512150b45040308070806090115050f070c031a0105010504030b13060c031d 62
    0xd000c3e510124010b040c0644407492199a0b0b00c65030100e41044010f40d000c90111101090300030718010309000703448003544003113091078284d213002981d801d6924542c840d4107800202190081c031510b17042c0c1d103484d07500801401005000e40d91418901d030300403607801e02003400c1240000300d5180101003420a10b4060313546400c01c1d035030364444c59100b10181d00382d150802d039a0b02c42070384404003003290500a800041c00340a40c520242c541040400f2401500340340c0349181941c609016510118494005000000c15444222154240d0503044210f181840955500381500603107116500745121703c9140a62101d80903580c60080030364074181e0889240360b00041010042c00b5500009000130b0f503049403032911508081400c124041140d001400580700041080c504004020803881c0517190305800480e0030696525210000c0c000e030203607020083c151070408001402c01e03590010980b1000d40c204a05100f807101444000d0018410192500d04d0000c0390034901000150000b070940040c284a01c200c96103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 322369658 1250 322368408 322368491
    0x60402040b06071b06091d060d14010c090509011502070e0a0b0a0806010509011a03041101050c010f050402030c010207050303120a060b031807060c0f0b0415110c01 72
    0x10300341d26401c0c942c4031034240700c0031010803011003d4808051416080440301418220060700440c80ea034040e45080c00300209004018104422643c0c20501c00e0741d5070711040d8032a1400003440c0c0301202141043e98030f0010048042d6a001007003c0494109903541d6005980ba240710619100f220341a08000d83d000d100c0400201ea003a020141d8080c090140001c0c2060740200061614400b5030321101080c0c0c0b1143c01403055140220107180100850141c0e6200e000f20541428024000284040d0a9500c074002c0904c2c541d0123801140d00c1180b81b04003c0107080c0c84050038000402098405030300a22031010800b00650001840c141036450003402503080003c0d0001079081c0690007001006501e84810000401441960185015480d85140c0c02240841e100d102032500c5c0881d0300c06410448821000408515104802c1e44c0c07250300150f00000c10395807424809041c00b5002c4145200a10300b40941042501c0d49000c1d00da071580c1c14009100e030802c0c00b1381700c03018805002c00e00e900e002d80d2100034410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 322370908 1250 322369658 322369661
    0x4201204030e040e03030a0e0601030f08070302071502030a030609020307141e0a111522060b12030c0606031b0d151406011e091502010e030c01021201060302090306040204 75
    0x10320074880d1614a0b0380304407200200d003d83e4000a02d111081d4408011300c1160f0703169004915014035201c000700515807643e140c64030b24903207a501c081c040b4000080c14006240c0b00b40705480c0649030280c4610300402480800a5813035005110000006e07150100100c2d200200d40200e03800366910ba5243c460041240c0d00c03c8101d81e120f643c00008403600036100103000d100080182c402c0c0c1007151180311040d080e4482e0b0314101841284040c864035040010041c1c1f922080c1018405540d50220b03990413125a0b1911708018061240c985074042014030f40c51018910000040c00d84d1402603098505030785551080c03543e258501c0316410032481204c25207900d40c0c00c00c1300a280318640251071034400c2282d00b0014004449602081280f0080a80200200b40d60426120001c009801ca82005044500301c0010a21421030080001c08101c3c242902040ca100350000c404803441082502d503580041402e6174000c0d8050303880c062403500d04000014080d4040e20946407250710240c003070b2100365038076402c020 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 322372158 1250 322370908 322370911
    0x206090a17160501180314120403050306010201090c0b0a0201240603020903100c0302040311090910020903010603140f0f07060203040905060d080d06050102190c0311011b060b042012 80
    0x220046030740d42c80000807400902801c00451140da01d94a00d0b48128200101004483c5c410450b084008111400b0000030700c0014981c06030701450120b849072101c500403409802503400c0580303003204070030b404900d51803e40001d00c500e2140341c0007040a0001c2c42404007801c000c2c404280d403030028070207041100074040c0c0c0090a904c0e07001010303280941484c10441084600c485030210001358085418010400055141112150100c400c1c0c030081ca1f2205489543d1040214604100c90b00801c2081032500c094111901448d03012214540265114003019030310242d00c540103610303101e8030140142407038000c201a4182d506d5540603514040c00c0c03290102c05440302400180c0c20940d41a00030700410300d25806000460603c0c200400c2061900700024034101c01c410960f03101060180c43d0800081280054400320b80e0f0041c580c40050381ca4000588400c0d4490040100c4903550070108801c01c4a1640500100b40080b03600300306c8424007050100c4c840762002d0f10b2401d00c0200304800c00a4040000106 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 322373408 1250 322372158 322372177
    0x18020f0607050f0106061407020607020d080c12130906120b040813080c01030605101209050c0907020d0305010e040b01061d03010c0914040e2e09120206090a17 70
    0x524140e11540d400346014140b00072000d41303964444062119650101b142c620080c45080545e0600c40c031a00000c0480c412400024828090380f241e07041002910010f0701c0c200c00c0000d040d5000d81207410401c00c03650b400540c0f561180c13062071078046044103051262106640c000e800b0074142d2019581c4043c0c444001810035aa1004140044002480c66110010280a4000150886c0c840100007d0292480d41c0c000c0c40c45000030b035140c0b100c0140e01241c00782c0c1c00300b0003420120b10f035041800c08504040c0000d04490f00842c07040300f001526a00006c245c1002444caa80c00c020030380e0b0701c101107450100141c500030034000755400100704152050404405850a01518070705441074100003d086a011207002d401103418490104882a02e401101400e080162801e00c41d80e414500c90645a825568404041e003215100d80c0320078140d00c41601e580f40f00e00d00020850030302503040240c00301140040341e100600c500b0002500d44c1c04081116280c0301d0744522101c242800041300281e0640040300c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 322374658 1250 322373408 322373419
    0x9010326120c07050d0809190f02060301091d01050103030203120601170a050a0f02070c0509130b4212030c0105100e07050a020307060b060409230a18020f 68
    0x4001c05050a000c05008820b01d6200c160346180300e25004e41400c989101500030b005e148410022804c41c0070030048018910ba504043c06842c0710700d408210031030404000317900481c010001143c1288070364441c00d640080c7c03100750300074160080c1c00d080c02c9e91400d010040040c3c01c140010050701081840c3c40b40c00503014100a50322004000503501034000440e20b00b0a660749035014464101c055205030000040c140c18107515000d19a01c0724480004076201d510b005142000004181101140c040fa9004d980940940c074103080011240184d01000c0030407500b220048410300c00100c180400000311008943c088070084042c00d81005102e014192400300b840c00108080c8000c85400e208246c410010f502210300300b1418070740d051411a2000301070380c0a00008009072841d03103800105a5440355417052011079038010740c3c0082095401203a00107903003035040c21143c5408244200145400390030a85c05060541c0e1601d000304141e684d0000070b070a04050f55052000503050010301840c86000103013a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 322375908 1250 322374658 322374667
    0x7051204080c010e120a15061e0e090f0616090b0403031e050412050601090608030c1c0e0d050c0102060601030b100e0d0b100312030204030c060503130813050f09010326 74
    0x40c509002140f4801c99041004040c07c601401c110703c1058094481300c8045814203203582e1030282038015a00a0251160707038140007a180100801420b40c03444070120a90354941011391030385050000c1e0380d08010201e009003801088034811001910110780c1c060f07641b585c1c11581d1913030522008c10900043c1080100800022407402601071448a0b01440b0702c0080c04150b16002d00c4000312045600698450341040110807019080003440b4040c502c0030400315039204c00c03848402d40f20b80c3c429841c02178000450070000802e01c500801d2030700320b010003a000d8440d607548030b00c011011600f8484003568040e20041680078000d2080001d40c1411001814000c0305648607151105910b00886e007941c400303800544c05104008884c0a03218040d90340d0705082d800c150641e900c1681d1000140241c004020700880014150301d5071010b081d074140d810041c0303142d80e14642c2e4a0300000c031105000c1c06000700e03500307081e08980e410b054072840d040300e4001c482e07a09501d0700c014000f40d0044010b40c07a01d5072901e0912 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 322377158 1250 322375908 322375939
    0x501060305192f060a030e060109020319050c1b0106030812040c08060f01050d110a090605100504150f09030b0108070504180f0213021c0207051204080c010e 69
    0x500c6103100910840c2c80c00140c1d00c2c6080302c1c40c0c560220030100950740803201d80350f400014001c80c40380d0a01c21140d076910740ba03103550b088006203844e0204038254401c40c400081c900c0300302d0b40118003580784109071068949001c011130060322025180003c44050402100030b4503c10100c18107041c0c0410400494003550302d031a852200e030015440007124620050074002045242c0304100010444c80e0045c08035407034959503145a08005200302401035031100d2400701005600034003041c042c00c004085805560300c0b40320103c000c003e50300070b43d0b000d2200070184442c80d40c001d500f50b4040722a90010b18180e14000b0800b10382d038a1000c0711020074000d1000d004030000c2c490481480c00303014008001c004861070170003008291041c040300c0003031404035200a034002c600101c001c454055010350ba0b1400f1750b203030900710350000d1280e5031026000110900c0c1e103003200000c50b001440300c00c0c016412119a000440a00d605910072441601c0269000c5c14003c14554015101e0b007410420051500a0904145 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 322378408 1250 322377158 322377163
    0x50604121112090a0e01030f06050705090306040c051512010b0a02160b0d0f050105090711120c0c0a0803030c2205040608010b0103110406050405010305091c0915030b0108130501060305 81
    0x2901221140b9030208801c10903040c01e1408000426900341040b440b03514644650100302c0c40c0940280c54140c03110300013182c10380601e08135120b404000c0c003100c0c01841c2504010500d00c0080c020ba5100c0c0160315050907000d49500140c810301d00807101d00c0b00b502d9180040a90080e4001d03d0350134103500400c3c10500540c00d003415204c0041c080b20301095510000d08903203008960300d03c80c01016142c90440103000b41d407512018503900007030310704040c00120f441c00c8400d8a407108402000c0d100e4440011209a24803004ca06482c1e046002c0e28801c8003e5250344559841c0d0200703d84039442000c0500070312540c091440701c0800060160b0002d081001d446102003820f9821f50740188903103a44440c268043c42d64540700d90100c0d48e0302e0391985801c090030480000d200f0f01c40d0344180c074101901c5001003100c250080c01407816540e0201c1c10800e0048403500e015000c10b1462241c80c2c0800003180050707410f075009004030b000d0090305a5030801980d46003038001500c0b010007174041e1401e40d030394200400000c504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 322379658 1250 322378408 322378423
    0x606080a030513090204120609061515080c03060102150718031202062a0901030209060d0902010f02030a20100509010501140a29120c030a05060301090506041211 71
    0x10b81d40701c580d00c1a2451000019024035405403007801d03c10007040121600940b04a40320745e03480f2901041c0e41442d030410000bd001481e45d5040d010061a40018002c8034511f020440003170389440b0031086964140c40b0780c03100e0204491403405038015450014101407403146080c2c0c006400c5c10009418944e0440c01414a803454208480b007200006102c8101a01023102540c85031074111045820b059181100510000801039901c680b200801c8608840e070203501a500301d00382c0070f05a283c690320300910b4a00908060101079010415007520074814130b1001c42200da40c0d03505500c1c0e4803203c5854003000344000303406200701100c0e4001c0400f81e22818440340200d601840e141d10010900e541040d0111580300300d4110300718030400000e00300b082610710302c69403100e1078010445029124a05403503860144d10540c0300b20400ba103400741c100000c2d0501031000c4c500820192008000030742d0f40c8424142224004500500580c0c88000001c0001c5c28540644152950300d181034403180400003550b514040e01c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 322380908 1250 322379658 322379663
    0x60d0c030b070807112a01020a0f05010c031103040b0115030b040c020601150207031a07020a0b040302010906050a061d220312200301060324090506030c101202070606080a 75
    0x10640140094541d12101c217401c1a4a00c4020700200201d88451208000d80c1151000101c0301039101c42006a00902c0724580c015000b0413452380b03440b0b00e4a0507500911408100002003850181c052202c58082c07011703284126405036184015908064528494040345c0911204068841007100040e0312180070703400700342e030154005010745d50601d400b104140e00f6032488002158440c0d0020004140060501034444039004071550060702d0b1034104a007070400c1c51a01801d03d1031501c00380410564150b0101d0611401100c080005440d00ca90680545047d44102d94090708010241c04440b10b00c0c403105500f00d1110209000170b2800d40d5081500399504400640100340c030340a0700440614540a21480d214600c0c4043c182c810034550b60a60342e02060142104055681800507080c66050244915a60140c4c1e4403001660340c86d030a5902800e030440c0c800b40640500704078012507080201c4003011400e5640c44444c0f103a0070900c5d5900080d0031400040d00d0306512508000340384401070001182460 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 322382158 1250 322380908 322380917
    0x102040b0d0b030706030c2f01240816030308071e03091a0405070b070c0f1401022b0c17120f090a030210020d020909070e01021014060d0c030b07 64
    0x29120b0007014180b01e0190702c00f4051504200813010076036800034500c4d500412101540c00200d00205081035001403401c0564050342c0303000c10039500917030030002c0710f03003000ca0002140e0303d80785c0c8030b160507500c841c001203450b180158415010700010f0301a82c00306602404500e0801c034800611000345103105107e804441c04030359208545818008200320404d000d100305050034000e828140d0300d0704e81d1070348503100d280b09040021440b00f042020405060004000005009815584070980818107000c414003840c050702c40c211076100b040e000b5104c000c07180e03070641d0104003400c1c5441c03400707503003401403038030103c030307200f42d043e6040b4050400d00e005002000d481e07200d403007842e26000e03840065421016005517000d0380941c40000010341c0c0014500c4048801c15000750711580309483c140302074042d48202c641d01100441c01c0010345540070925a14181e803d03030880380c086e000c00f01e4102c22a001c82203007c40001402c2d00042030b900740b40c6405e180552017a12402d0b1010343d65140c4c3c02c2d5021051b00c545d070018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 322383408 1250 322382158 322382171
    0xc0d0906080a0b042306011d0607080318101401170d030f2304020a0f0305072114060a1a0d0f03091d1611030304030305040c050d05100e010e03040303110102040b0d 72
    0x156405080480c408d43d00d483c03086001b600c00d200080040c018404020301003003001000407005507504803181403a178050340803070305040d00080648001d080b000461701d00c000c0801000080c1d1010510501120401140c0a00170301c0c4490101200600a40d403042480f079030b110381034141e0107880206100b22282ea2007040701c540b030400b40b040040705640c9030710000722101c071408144003244020a407202113600c4009a090441d40140c20007010604841c8068a0388130b108d15445c250140c0411014820f00d080c1d001000240526651020620f0ba15058540c0181018410348000344603521f540c05c4c07860003414a901403d0351000b84e20b1208a402541211500b100818040e0398240300000c44c00d11080c50505159000e02c0e20091aa01d0100400c05000c00d61504045010b1020011140f405020b002c1c20040c031810850030010303541c03000c580d1842201c0d417804280031450784040c4560f61547c28000d02440c40d1501d50303101250b01c1c100080d09c03100c86543c20040050151000401400c80e601e4024010551 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 322384658 1250 322383408 322383421
    0x5012d0c0e1002100b10080c070c030f03050c0c06030106140c0a05010519270618020306010801090507050a0509040b07020f01020304060608010b0102120d020a0e060304080c0d0906080a0b0423 84
    0xf50345c000c4001a0250180d500c00790509500080c01690010340340803490388401c014101402c2c00b01a691004e08120140d440f103409160b806001030652000b200c0c1103510700150071081c0000d51100748500301c006090082c42c0f0440325803803001071908401d6030049510100c2c80340c880d6030840700c05a44410b040c0383d000101d14094502402840102035048040c41c01c83e840c440300d8140f6803500d20354001c101d980d030b80c0d443c2d8501824943e40c0314101500502116950340e1603440180c000c1ca407101c0c00396020712a40b4800581c03440c0c203044280548030302500124154407141d5580300c50030005007400041d40541101540810824405584514040d950110b0903600c1c0c5032600c0e0071a07104040450454110400402842100c1e0302103030b189900503c00165603031450b00c000c8a0600300300da000f69100c03000100380024010b01d000541a41480c0c08260391043c040c00e01e05031000001c5202d82d41c0840c92140004a04e1001c0b5400315404000181c8082019003804046411811081095071400a40c40080c08403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 322385908 1250 322384658 322384661
    0xf0c050309010f210e12030106080c031f030501050114060412110a03120905013b03030c01020412020906090411010f1709010606030501060201020c0c0d02042705012d0c0e100210 78
    0x1101e1600748011f1440d41400401001e011004043d03840a80d00000410002da0440c241c2c54210401d00c0000d021583c0ca91600c43e010340001e03c200f01c40042444c0708452a0b02d0400100c4080318144030100b84181650f64a4201c00440900d80c69402004807100101248031091440c1021049170b441000f080d06180001d041000c0002e840c410018010759200c5000e5416581c040c81d400c0d50f968240c0c3c2c40e900b070b4030000c2d2941c455a03501105550020500285c0da81c1d141d03444001191080380e1411b0180d6403541807048410b01214050a25204006005d00c00c0d4014100341050344624a041c07100b043d000418800700d40c00540b8030310070344d039034410041107895450700c44c080c09040148002e6280c0318240070070301c0c0d503900c4887c080c510582e42000c9c000c08550392680050f0600c60614200c01c2051100308050a1655410300196110350070030281c2c021300340c0406082400d20b0030b02e40c0040e201c0b03000d520410000380000c1132007800b80010100c001c0c0507962000101000e071230b41e940c020402e004c0100301810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 322387158 1250 322385908 322385923
    0x703060b060903030c03190f170a150909120302070201141804110a0806030601080a15020d09140606010c0314030a1e020a020f07030c0618030204020d0501060f0c050309010f210e 78
    0x20400140e00446236404c0e0b400001408000140000c1c071003a03448000b103c40061000c0c0c080e12200c90b11036900011000c0b01da400c29605c517805805480c201042c00b44065050b8401c141000340006d034240d00b112002d551040184c82210504035407003550041c2d01001c1012078441c040f0064505d000401c4074005198000127071640404283c014050305d500d000101542e80c0c1c09214014000450003003d40460f141c29410b07900c1c03581640c10300380040a02030500b924504400c407592003d60144100040d40c95010340d007132900aa50560f140c01c0391109500590700b0640010b0505820b190315142000e800f03100309544005401000080140c5e034152141c0041d1801c1d01c4041c4e08020380e00540784c03c001040c40041c8241c112040e03428180300c0e00c3d0380c0c03000c00c0744840c07500e8100960003440451141c01107141540b01ca410b0703411756251003001450030170080da46113041032002445540300700f090301025440f8442640200e1707487d0400c4800780d030082c0c0103031035404082c800c0140840e030303240d59040c1c0c115801c01408 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 322388408 1250 322387158 322387207
    0x308031909111e040614120f120c0307020409031101060501080103150203042406030c05061602060d0609051305010b090408160206190f030b0406080703060b060903030c03 75
    0x4029040c0c09654422a90140c1940346204040c4007083e070750140200714010b10981002042000056101c4000c1c400b102c20400d51540994241c021008083c500061750180c0649400b0007401c08840101000100e41c0c4031515402490106011001c01a11140140c0a219110f52540d468158280c01d18600b101c0d000d9002c5410020307003600400c041000000300c0305400102c030901581e240e03202e050466245c1c801c0360b0a940d4181042441c03400c40c0c0c1e040c0d03200d00141c0c0c1c8225442c07002c25a44804104090003100c54a420040d88582050b00610304880284584085486d0102e1444c4d40c40c0e0007c03080710380480300560282c10343c407400000c00800381f01d42c90350100c0866101c200c504082c1c952003494003c0300405018441c0c007040703407001d540d078030029140007003c0074500d4030521410317001c014031850000000c100424204202e02503a440c29008040a8a80c8400104403061030b5031034643c05480b4004000350070200810260106440078802840220300c014000c59a4059411030344282c1008054503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 322389658 1250 322388408 322388411
    0x40809130f0c02120703231209010902030c010806090a050a0f0608010b09070212370e1e030307112803120c0f0b09100507090806100807050d1a0103080319 68
    0x1d0020b604440b0800700c02c0740315442c07c03a24a5a0000c2c1310010312504030710710340c004035410800c000240150000c81006200354240c900d10640d40b00156180c901c166503065000b030580f0002116691113600c40c0f640800c1c2c4003030225a0f00c0081001c1c10490307049400c00700140c1d446050100d440c0c10071291660704201c1c02d200920181200038030580250144000400036030411841100616140d014003180e08906800e113a460a4103025018012868120215026141d1240c04070280f000f00ba19800403200d020f800b030f601d840915a5000c111403009000c16a010301f0401d525181c030300a41d407803d01000c3da040701883d001811403c01a040c81054044041084080d0b1103e000245021002c207080b40d5004035091100d4440780d0001d400c0140c00300b20042c4071482e090400c21301c1a8010021412600920280d030740b9a2113a500030503044c040b0b8000c440c1d10741d2100344100b22500340004201d1070a805081d00c0300441e1015000d80c00484000c0c2e0054550202c0401408800a000e510103071105502140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 322390908 1250 322389658 322389667
    0xd02091807080f210405040c0c020306090c03063403060f0902070f0204050c160b010f090e25180f0c052107120509060f09070608040809130f0c0212 65
    0x1019682c01312a881381880110044c080801d0b8400c80055401500c001041800010114840101100f400b440d047e4424400e5801203a1203440c04204040400d401078042d00c2c1556848600d02d0800032000440071380d000201d40f00d410118040180703030140c1d07082650046907040c644480d080810030160000f501892040001d41c0008500b000d8130700119905407404999541c1b002110701d5903015196010844625030080d11080141c2c1101c5c2c18140d0f66072502c001651170315510904120f500d9145403451903800140440700000b110402030011528001c08200141c0d194031030402c100c0c99511902181b1a05c40300e004002804038050035201031014940f45003007125038480d40c06901141111385031a0440c00002c1003840780300d40c4140d02c407400d201d9003c1c05117060020784180c1d11802202c03d002c04041c2c000c0813602604d80070805070b0403207d603543c400072281c4540c0c80c0da4200740d0007008210780c40021420322601445007805036141e030800d440e07400560302c4105200070b401d00100006001c40001d0400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 322392158 1250 322390908 322390933
    0xa2a020904110442090c1206061b0b0c0f0c01020702030d110340080d05040312030209030a1a10050102060705041202060c1f0e0309010c02010804020d0209180708 71
    0x44000d8150450022003a91401c20b03240b01d2800c620058005e841c906050001200586801044000d00b00407074100030001203540c1e52045a44880c603c80f4884140040c00c011008204072003001c0740c120518401036454944145c1c1001001e44c00081c0040d110307500403e54109504e400c2c4040c84501c1c145003840790154080039003d585034441c1c8251952181180740018400c2144a0000740801544014006441d01c1c4084c1c42003e04c8854881c8803110f228000010306811710403016182140e0340007403140c90b00024400c00f50702a40041d100550148100300456000c109140000078840c2d10050304074071982001582e0f03941ca240c882c3c10441c10b41d03102d001400940c50b0301074125401c45040c0308101075402880e10006186114520f00e00e80325208184601c40c4101c03070015003290044041008212100200080c81e03100d01484140c00e0105070760f22200000b55000b1508254414402010103240032040c0e8001401c065050b03d0341400e0756141501d0245098040014002074032255009162450100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 322393408 1250 322392158 322392221
    0xf030403020105120901110c0304140301111e07150c2c0f031212070f020712020112090b0a061401021504020d03020f0f0c04110a2a0209041104 63
    0x244040020030500e800242c1040d400390707c2109160544c9503026911408034400340e07507980081c00b455140c15681201c5000714030b414452940272200c007070b4038035040c4000403000c082083c02041c4640f514680030801000010700c4142868020040c0580000340b401041d400100310020b034041ca8034094003008102125400301803000d1581440c1282c0002c0e4482c272a0010074100304c05080c200c6408480800c0740f1061801d10035443d4401d8086a85061841c01c400508981c1c4e000548100d80589142480c0300001d544200c0080c0031b5052800343c041114001503995060114044520a807015520002402101217100a5014403102440105516000d985854200100151000344100d241c003005100b00360092006103000c5400c3d0703003901d0010301c50402842d12241e011201610440c80c02ca1070039014254481960810070113030340c4102040c030300d16107010b0044c00e0405248070300c0110140003100690b146840baa20851041c01e40c200b195020300301303000c180c481e25005144901d00081840c030007500030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 322394658 1250 322393408 322393417
    0x80703030e220b0103110d0209030f061b0f0705101b050906030c03040609020d050d0801060512070f0306050d0812091c1413330c080904140106110f030403020105 71
    0xc15200040c8070f030141006038001d20303c10720081c00f48400464802403903030345a030150240400940c151405411041c81d03090321458202c9040350340a0144802454002203400a8401b448102413201c0c5010b03c00e80b621803038a000410f00c41320260300c1d10700c00380d044810751030038000d205040e00f4514100100f400005806010082003200b1500c03001c40090144402d940000019075000381060843c1d411a0801c940c50f44d454130f000c0300c0481d8902000144d914400c80c200e400340384402120710b03041e80b2459012184041020f000c0340c101030b103402d000b00d26940e43d86650004a03204a010658401040100380c070958001440301d241d540020141c02c07030501400480f45402001032902d0440820240c60b1149140194880794440181008000c01e51000c205042c20300041c0f681207400c01142a10f034800102c01c2d45403100340014481100030000240d403080a0041c03850001c00101c0c6a001e0004a10071640003613101100103030103095801503807a001e1248440c0550948051440c03e0b04680000e4054400c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 322395908 1250 322394658 322394719
    0x506040c0e0c0703080a0f060b0c011a0d020f0a030203010203180c0607030503010b07140a0b010302010201140702071a0f0a09051806010206060607021311190306030b0403030905070f080703030e 85
    0x176400202020250760201c8521610048100540c2e5192110812070780c010404150040d0f1904201e5000f52081201984000c3d90003000d0321a02a890b90a004540b00c000c03c9240c1c10400d070030300c0030005980c280003452240940400c00061489900c1c00c40e0314110b104000280181800c20580c000700e41c0c41012681505c2c224202c10340c3d140c0403860000401161440081030310300460b48446c04226815041d24100d0703000741d00074800c96060000f01c0781d11040589440015038010b100401a00c00d0001515040840109a00d030400c50f400e900203095502103c100800101d075034100b84a01d241135100c6020f1001c44158040280c540200041e5441c200681042c0c8203100101e503010031559425000e041945403403005005000d9160f60181c62508a0707110341041110001c1540709181c442c0c850b52040300c1d04040700c3c81e05521243ca042d4000c0c14031101c20b4816000d82d503c0400c40110201170032005000d000b008068951031400c005109070740c0c000314035119642c040c4160307610344411020407d1040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 322397158 1250 322395908 322395917
    0x302090c03270106050f09060f010f2d1e0e0d081b010903031116021314010b0705060c09130b0a150c1b15030209030a080301030506040c0e0c0703 64
    0xc503542c10807411076000040700700e111014440b41c40c100e0401074000404407281907070b0360884c1c1140301c0208000070400b245e425412060610007040c2c2c541c0b16030f13460a0310601307505000d0160252603007401000c911701700404005403000076003c81070513030000c10034030355252000b00700012501e0b0050044c1010740d40a40300b8810b22665500303400b400203900807903442c14a4114000d00c3d03240740303010381d43c06000044001e4000c079140c02082000502c40c8000c07107440700c00d14035148611941c90360800a40c0c1a6140646800c030fa501d5511002002c81a40d14a001e031160307220240c1c0b19580d61410718a404401009409074a00900c9000c000b600d440c55011b4984004036070206007901080081180a080d036800f0300340040c8400c242c154a03581241a00e11120300035611690301e00050f0742401c41e43c142034800d0100300d451600c0c0300003160744a9070141070072941c01420f81c1c603041d1158a1305101e40d0020b800944403a000f002c203200401142480d01c03002001400b1081c0503a1900380d01b04009401a09000350901 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 322398408 1250 322397158 322397161
    0x3070303030b0a0b0d050906010902040b0a14040b1204060506040603020a14011101050a0b0102010b1008010e0c070c060e03060a09020a0b0c011413030f0315121406090309190302090c03 81
    0x40d80c40302c010030040c0c44d10411098490240d20645d00103000d007034030403220a00402001050354680350080760140e40c04c903a00c0f20b180444c2101c0c00c035150005c4000b0450607400500c400706e8500b54040050569450362030307122a25082c5401e110081710070107004144581c3c64100b04200581f00d0031703100d1080707400c04400b00b03170000500d03001031700c1800d01031030008041e500c0d0a0420200301c2d0950702070080044280e00070041d04041c401070203141c1549040010100d1183d400404c41221710006241c1d002545800c054203111751a5200b203100c00b5035030044070204081c0407180d40f95003010801581d110b40c0160003804000180c0d001b240c6502442c0c003440700c0c820800a41182c0710602504500404040549207022602d8115803151181044800460002c1d00030001e90f494207110380181540075605482c0113541300d18200000450008081c030840310030f050180317211054442030258078400c0701c030a00075550301e20320401009824070002040125070110802c0520150305c507030840c0f551050b010900b80c2e0b036a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 322399658 1250 322398408 322398431
    0x1e030706030b04140a15050108010b030a050c040306020a0203041805040b0c03100f080f070b030708161b0f05010b0102010e031b1603080d050c0301030f0f0201090504060e100602010b0307030303 85
    0x5030006504c080d070603005000910168400c0c507807000c00360050f081c44144110743c4800045848690a12528010b000c050012500308c94850703120a4000507800790306441c1c1070352036540c501603805c818003250140e0008038040004010500303d0130b080c0061500100242e01d00b6984542050b02c0280ca00042003501000080301811070807401c4000d848032207205244240c1ea0801d09680e024040e580e07a0303c0740603440b03001074000e03c440c2c192406041c90703440740802596601070010b02c59001c80c141000300450304051298028103280305005580c029821203001a02d5400c10b682987c4841c24400d04583c501014030318414804410b603602800022001400303608140303c0289001d6640020300034041b1114000010070024038002d10104000000500c881c0c2d454104410003400244005801c801040802c03a000902507070b25203510314130504000d0f5100351201c0c0440c0c200c4400380c0086100c1d21200e005d21000f400c0080c0048002c00d2540300920610400401090b02c0703040900c00282455280c032003070100c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 322400908 1250 322399658 322399661
    0x60627011808010f140108060f1f06020604021f0507020d0507030210051306031e020a1e02010b01030e010c17090a171b0d08150103020c070603020301051e030706030b04 74
    0x68001d0408110210705440300394082c001c20850481d030000741c1c9011400441d1600304a0030904840001001c1c01140d51580c500008510004140d060403c602060705010342101c00080c0d00545400c1c1d0040000789003d205101c0b01c00c011000e0400c1e5613652180000000d03078802c046610151b410b9910601c0d0001030302e407051800d81c03540c00095000a0524204141552120282013030191218244c0300ea01d0351210300380c086400010981400c100040c19207a4552515001030107418044c1c40c1014000203914048841140d0070003040c3c00503512540082c50035a0705004002401c0d070b110000b042007156085001c1d101c0312a100000c000203c16400107010b6540c00d010000e28103400600c410b1445901100790511607201540f5015941c2d1030036405078800340c0010304524103012075141c0044580352450100c2d01c030111035900310704040e020090b05051200030b10441008240c9510096102c0d4148001c104d20b031103038442c2128000340540f0301c80301c00750b400040600844030142400104220390001080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 322402158 1250 322400908 322400927
    0xc0b071209020301090f02012d0f02100501080d181206090507090507031e1b0e040603050a050a0b070f050a0c1a130201031a0a051005160605060906062701 68
    0x30342c0341d407a0200203402d00c0b40c080f2400c16124400d23039620b0310407110701c80802180071508554927010513800032014003490141c603580700c0610090044641d1010120844401d892098000d1485034021040c070900d290f4120040c03044441c4210580d451031400d1941a4211003205440074002c03a45800110f41400028801c42014114082c0180f1291400e48009000b81288031100454082c01d03190007c03d102503071080c1c907094080c1028002c55010000400ca40105404400a0740070390b5030f000000018104001c1040b240744548050540d528a03402c20031511130004048006100c100c0d00820900c56012089880459440c02c20780d880c00d00a00300b2128440a41823218806141e410600c502103901446d0b4500c10380c0300742c0c1c1c2440a07220119000c105210302c8400242c200c824500c0c10f22681c40c014a03000b22005483c5403190400b015945030300000301801a0980d0325545da1f0083c04024100b0502c41940702c44140c5401d807170041044030218010a003030302070203660010000075805a17882402002c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 322403408 1250 322402158 322402163
    0xb0d020114091f0c020a060e090609040602090301020a032415050309030d050a1b0201021303080702030f060708040b01051801031203110406180e1b0d0b030312010e070c0b071209 78
    0x10616844201c001034144c003c2034800b40c0c40741207046c000043c0c0310301c241070040007000050901100b170b80301d00d41480402c1c800904100c0c1c0c0c0607006c0c0310400c2280c90920180407503403140d40e404039100d00816901c551004100c0d10a000b10040e0b60700a200d40e802107403141c4140c64842c600a0381d01e41c1e03201c0b9030b0790a43c000c40e804400c50074104410b0100703114094000f2801c650601041904400f54400164204d2152802903400051754080800c04104402c0241402a0000c0c043d96034030442c80c40341b182002c07400c44880001c25103090070b01040c001003035241809020103a0b404840050240d00c03100080c441440010300d03901c007800c213030580d0074400d41105680454940d0004c4d140d584844000e00f1104d404240300c50007a01c03010300068041c1d0171020043c041c480c85070880b490840d41e248841300662011003403560075038883d104020161002c00041000b115503096200055041200a006820707000c1c1c03040c8200001d0340d900c00d000c01e01062916801c041107040c40c039012030060b0305801c050200071101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 322404658 1250 322403408 322403449
    0xc030c090904150c1d0d060e010c090806180c060c0f15011a0f04050405072a031707120c120516020c03030408120d0f0e0d02010b0d02011409 62
    0x144000c014014183c0100da146544060000c0004080105d8030100040c400d400d141c180324a42041c9420032001460f0a11300a002c0410714800e02c0109500b9640c0c1c0034514000074107824806c00c150103061240da900310b440ba484094035403580034040d5a8500040a0340c91050600080c8401100d004005141030507800354151052f00311941031424210200b41301d146640d0081e00b8001c0c40c2e007400241110780507aa03d401c010301300360a02040c400103080c0100807005010b100d50291000064030340c00c28681114080041481d00c86500d4000c0030303080d60159806070716601034244039203035400c10414403000380b01640005060806074000c81e11200e40c41d001c421098030340400c1c002d41d001a9025002c00408517001c8600d000c41d400c0a140d6030344602e00c1404065000719445c0e1560007081002001c03140c0110b88040b0b4802441c00010007104c03881482d2503850752050a000c1071880e0280034035a07020008981d40b4411000c640c001030b0400304060b0030440d03a0440000c00c00f2081d0f44100c0040d0013090003566 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 322405908 1250 322404658 322404661
    0x1b09060f0321080601030f0e011e150302060f07031103030115090501050306010509150f0c010e010b0303030103080403111512040309060e2b141f11040b03070309020616060e0a0206030c030c0909 85
    0x3e180cad060720007203180701d615142441080f94440d20701c21810800c490b4084e0a03c0c3c030382204556213400c240c00c000f01c100d003009440c1c54a038019800400195021701f008164401d0011903503d0b0180c03007074105038080c074180320b0107008000031a031700801a203c10076001e48100c2c40000f01c1c01c80901140c0300b0000101d002d00e4000c6500c6e0300c40d00d015400000200c03c1e6030001c01c1501a0b49003015034900091000800c2c2080410040c0002540482c00100c4400050700340b0003800032640c04040f0940104440b807003511120f200300810305078001440350060066040c108981c45c0408003007490040b03401e100c0d1481d1350b4030701e61045010300301b210484481500044018001c0159210042c0c0b00d021001640d000090100c1103c4006071141c07090a544500c2c1d044214580b0789020340649503504020264420f1650703425100c40540c03070f214010003040384241a0941d00c013901d807070250112680381661f01c580d5400311f5031040058842c101200d400642e107402c819101d1361483c800351034074400e82c981d1541100c40c020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 322407158 1250 322405908 322405931
    0x90204061107090608060711070e01060503071b15020f1303052116110f09070801050a060e06160f060906020915090307031b09060f0321080601030f0e01 67
    0x26410a4401d0454141c03040d0b50340d41c0d502403042d40c040d4000d102913a0010350100f0b460502461081d002c0185c20000d592805985000c10003550500340d00035004204000100b0a038540d10a24500700c09984081c0c043c1c0e01c400e151210780082810b41c031184005030340050800840701100d4240c424410800900640c200d81381e2a00540b9800d07002094259503421429181c400300580c421b50341032100450604179550503036202c1e5030207400700b03081c0d00e50400c60040c1107038900c4c1c070740441c01e5100f0042500d0b410802e524010a004404586a114404008000201070042d039178980071114114042c000c20594001e13141400036503a403000f03100400b182c1c9010290000c114441e00a4810054104d41c0c2078500104011000a0361062201c016815000068240006800b03101c0415035013034120f18400381c068548a04a0031900242c122100203000398008008100070040030001c5003048010503078070041340400103451000d010741500d0625881e030140c0540041aa403000b4840107000c40244907401009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 322408408 1250 322407158 322407167
    0x50d060b0d3606050606040518090c0604050117060a051c0c0518060409050c030a051f0c0503010b401a0906090315100e0f0709180609020406 62
    0x308024000000e00e01072540b0315401c200c10005038140c100d000e0400c01480c40e594600100070003042940c0c803070001d200108554a5a402050a60108100d014050300b0545200c918181e01d0200760f42c410318040000340226680710040841095010142200b9a02c4010001c0c0328a072054203d035810509003841c6090600d0050340d401099070040c0c49d03108403d91110180070800e0250a580115180c3c0c0702c000c40c01c41c0c201680310390380150180e02a41d020080042c0040d080440300d41060782d081c0d02c1114103070072406101c2c6407101607401807502002603105414024205010511805030b42040c00300b005010400e146506a86000c1802c0741c4640f0f10f030004980741c02c1d1380701001d10303202a200e098a01041d00d240e03103003c0301e0b90201c5000407981402a41d07003c010f06035104440b482d41500541411480004041081074040d5400c00d60f042105030a003440c1030354003880106502c18410740b8006000302540c00460050503110902456912085d5240d042e40140140e540098022480080c0000391980d12 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 322409658 1250 322408408 322408421
    0xc0e0c03040c05041a122506080108010212071b0623090a0503030c0d021903060608090316030c0203011d01020307110606090718210b01060816050d060b0d 68
    0x8418580e20381e0785650901084659543d00c1c611300019a0245805e03070300e800440021603881201c00c855a0b01100a03c08102180403490035084030482d10050000d41e41280c146405032841200031410114a21308911003110b02500d84424130039030038a001224a002d100240095401640510106148000e03030f8034441c00840308064005552030114174650404030342000c031250894011401c54036140801d08181e84500d200000195007041003031501c1c64030000c0e0440f003400e1500e0004041e0302d404800340c6050001001c41313106402c200b280c41d5010307030103000700c2c00e8850301494298081042840441c1c01400384c00c2e00038041140c0c45d0703d2040304820540046210320035560350003220307546095116590320401d0311083e078001e400100042242d8480c483c7c4008180182c2500c500455458460410195030a102241001d05401180040c0b00c55060117a0040c003132458810300520780309075400748102d0b8418025007000300000e240482001c0f00c2d00710401038410b05d220280d0311104440840d004216 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 322410908 1250 322409658 322409663
    0x305121803030c060f09071a0a080606040e0103061e0227030f030d0c0c0c0609030c0b070308041103030c150108070618060f0c1505040b090105060f09040c0e0c0304 72
    0x18030648000050038048140d449010800004200d9521401031401e801301c802840c004c03c5118016001801c42030703070642401c1307104060070840e54542c4424002010103c4c000c0c1110b00807481000304000b5070010004650459400240c00140207140704007500704294030480c0036568074008680c03408400b000200c2c15481d0048843d904540c1d9517804145034540c3d4001c0c8070050300b80c00030f200c184075144041c1c111907240d0940380b5260656580c03c5e50340101414030354000710001940107a0500401031540c0d91705001c0c0408004403424441c55580043c0800c0300140000c02c4000010341482003501c00300151034250040505036094243d0074036072120b80407024030800341a4841e0394030020b490f034024401c80d41843c501103074003450b00f420400c1c142d0f004103984400700c003040090518040403504940302040201140c6a0105007810203091041040c000500000090b034580414031009685000040b843c0f00001d88101580d0782e244e0820420701d0089910927a8410032003010841f4044448009500c20752 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 322412158 1250 322410908 322410937
    0x30d091505060306161b08070b07030501080a02090406020a032018120712031215090b011e12020f0301080d32032203050d0f1a0d0c030512 61
    0x10b9594041540d40e0758103039030704140400364a2001000300c1c0309602c40030304900f1208081c40101c0c929500c91a40d6481000266036070450754060100055143c01000e005100c49002440fa01000d5000100c00d42c0703015000a10f01d07903000650300260390107500300b02c04aa10170411a152802c4c0b45a116489500820f0070400061002a05a2462519042c408216030a20009000fa681894172542c1c9003949030501b90144034525000400c10f618900903003080c081c0300c2c0c01c0d041d805441c10503c02c0903500d107500458140500310020070302d070714900e080c0d4014152040c03500c03405034042202d0704070003886085d118030340d000c07070010002c610070500203002c007420201c40e0b98094420342081146d42e0350726011260049600e040203180046418004059a08295070004480300520100d02002604100e548110302160010a4400d041d220510070200300391100c12081c032040c40086684140143c01000591180c000030721850103102e030191307114003c1c2d940107044440301c601b0240c045605d600f00da0403104140 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 322413408 1250 322412158 322412161
    0x14070510170106210f0f0c1805040c110f070f05040504150f090503120f130b15010302040914010e010807060c0602070305040e1f050a06210e0a08040911030415020903030d091505 78
    0x151003a040144001e230442c04e178503402402c0004010243c144c51380108100120520605140c0c83e081c0501000d2007000f100a15120340780100b41010b000c0c071a40070b584aa807504007000f020031301a4040c00304040c036906e03002840c4107110440500400308920b01505920022a02025600d81d00911900070401d513030715074034075030785005240ba0110256080208030000c0d450104110000580c0c400e101114141030142c109501d0308034000403100074030601c0304050000c0004001410b5990700483c050101400079002241c2000d0010f041d140510400a00d0503900003400703001c0c140700d80103490103080820301c0781c0200e0800c02010b40f054103486440d03440d64410300c6400101464481c0c0c10104076040b603103a00d000844c441000d01882d000740600c820b0301544641c00410300900c1880100340c00d40c85140100c1d00c6a00b007000c04021030b00f542034040c505144c1001488003103001c826080051034489040542d40d815454042401c5000303a04002850605009645c010089102c0c98070480c200d000000b000315 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 322414658 1250 322413408 322413431
    0x30510060f030309030818120102070308060102010b0d1502040b040605040612090f150e0105010b25030801050907090e0109020711011713080714070510170106210f0f 73
    0x6004240700040102d44089004c100045da04801f03043d1319510a407004401d00c1c2c0703c0b0042075003204d08802200741c50350300080306000c26412650b51038000c142032000304500001403010404058052170007800b00c0c40511170084100e000c980484000e00f0130421100e840f00c1c0c2d20b43c000f802c0358016003c0c217400700e1950038003011401ca00303124002802e85c2007403404140c01d009441e050410701000c00300940359038948043d0510800c09005050007000000c2102e660350702c001d0f9001107101058a042d4030301c0300300f80481101103036203e295107065940c1250aa01103440d81e0030700396a0a0040c1e8803d41c1c28039240c400018144d030503a4060300300240148400000390109400456002d01c5042140c03400172030500214080281d01d074000404c4134413a0401a00c0c1a0458482c0c8680001044c1403010b00d501100043c401781c104102200c140c1a580e051103020401c280c1c001c503500707000500440c4200003149100d04c2d00d654561540e100c00300c2c031a4030104454101c0003000c9000e8201140d201c2030700307401c0c0700b142d40e003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 322415908 1250 322414658 322414679
    0x1109010318120c170f0a030506030a05060403020c0a050306160f09030b070c02010f030506090103080d09050619110c03091e180901050610140a0513140108010b1c0b12010603051006 79
    0xc2e0f6017481284249004140d5109800604006d05a55094820054100006107080080d280114002d4001b4418240f0003410840e030220640c02c1030707000c0d402500c00e11551242510140c80b0782d070018140320b02100404802260030138030591002d803000105c0414420302a4100c10300e10101c0d03000381d96041308104907260176000c1c0c0c0d0050341c4058006880d20b0041010804002c0075001d130100c0c110011403030740a151911880c011098400c0b00b0700ca6181001400500860721a461100301c0300301c0c04500b4640d2143c08242c4a00402c144580190308989484041da0111001d1106000004040c1241600d08504a215200040320018141c1d8038040c041105482c1c8288809000100c0741e60b017501c4469001810b1116411000c1001d0070300005200301c81100c00c41c41c0c1035601520313a505911400028003000148101d8060f4000f0080280800c804102c0c54200d07903031010782a040c4400030403004514404540c4140e4845800310540d441c00c8008010458040b03034029142c0401d080c14451107894424896 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 322417158 1250 322415908 322415917
    0x1509020d081207081e10080714030f01060b0720090f04021201060b0a120f060b070302120307140903070b0d09110a05013204090509101109010318120c17 67
    0x2074180303040120304100030350300105d41d44084201c400108150b9604425807030404a0b4000d80d0754003682c240510f055040401c090121a507400009104070752030644104010710542ca00500a080c441520550b403100502c001075001e04080c0001c0c809241515090016103425030b030881c4241640598030380c1201c0140078180c00d49040c20607840c9884540d0000b0784841c181c00b06c00320106a00d8040d803540c0001c040c40b17982e004005052400740c0e204501c3c0341c000c0c1000900c00001c0740d26842402070094881c0e01c040e002112460000d4050760358010f01c40003905d0300940341e01c0601140703400505040919000d800041c000380c400d56007a0030b41174035030080216401c12030150500040316050b0110007070150b02c03460f040282104c0055036a10304a21001e680ca0781c000d4103e500300548603410301131000c0003003000c818444840b210420810703214012005552264249160401d92150118aa004013480a03a01ca2301e51021030002035844218003d041035400901c103072034040c1e448800f010141e86044c1101c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 322418408 1250 322417158 322417171
    0xe0714130b0109120201030e0f0601080708030a09050d0218010b0c100e03030f061f031a01020c0109050609040f050a051618050d08041203090e010b04060504031509020d08120708 78
    0x2003418501300304101c1c2200d0341c2241c09034101a196003c04281c1c18041c40075002d081c1d00c11001c1d102d65030501c02c0c00d5280140d1940280c0850740304210000103980e00821400a40f0000c0301c514880d03040174000111403e8160044a041041503c00054030540701d0005180001035507081d561450aa02501c408440602511500c507400420018038500200c5c1c64040d0700c00c5008001c90812900c0746c0b0010081d50003851b00c680030030754030794050600300711540350080c48400c244020700a00750004002003043c2c44a00c1031602a2034041200012942c450300410312541d01c1e0002000140b400c9006440070704402c1c2d508041031342a0240d4514240d101d8142d94954078101040324122a2034602400399002e84041d0544518a09200c082190a140e90541074002d0081c0d9803d2611070410040812080c410b90200c05c40d00e108102c104000f50700681518100c0341c0180e140f180062801203000050031a000c80207604c9102500b96504010300d51000d07080c0704040b09202040e55450000694203800b060311203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 322419658 1250 322418408 322418417
    0x30f030b03030d230702010902010201060e0c19030e0d0504030605090114010312091502011a100f0503060a081f0f02041208070212011d120a0e130e0714130b01 70
    0x200702d050320041d00841c02c54003c240c3c2c60804c10b00d40401e8204500740984a40c0010303519121204107569090040a0290071207080843e8142031902d0281c40c9441041c01c0064082181c0240d44140d42c02580041139100308030090320b4550340c1d850b4001303000381d00600040352080d140801182d03c212052080d004040e07c3e003100d1006503421a255081d500b01e60501c040e0401c1100480410002e46e4911b80380302d000010340010502807a0b1034003800c1000284001d07603010b00c0143c0ca140e2405c682c0114000206c1e2040d0801c25500c0e03c075940400d5017582203400c411040c1c03146404100001d8020613804103040c007008000c01c2550550410306090307210f2885030191148512140f4000f10f0102d40062419070310007883c07010301002c17001301c0c0ca00356485e00c100b00880c45100c02164003c240d0034401d800b013800314a002d0a1030003034514070242c50300d10361180d058000c0c144000305a08441480d0301801c0d51250000c01c0303403420b0b6912160f0420321441c2082e140c0c02000c1030307030101d5100b0410b03010f00440c03448141c68 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 322420908 1250 322419658 322419667
    0x903032a0405011107270f140414032718060306070c0c030f120801060203070c0509060105120405210f0a03050c041d0a0b03030a170601090906030606060810030c0b070f05030309010504030f030b0303 87
    0x9072094100203c4440d104140020400d05c0d480300c401e001929108450013280c188003103121400c21140080c0e0323701281d92500c40390100b111568002c01c059900000c0760500c0c120160440c104401040151340005014812111903d030602803071002014103002d40d551891031f180e8031000c0481c2c40b0b010310a001448489400da05001d54502807201e654043c5041c50840e041083c00c0286496580081d0740a403504d0f04802d40380d26640c0a80d0a043c80301c0500c4c240c0041c034120080c205c0041c1d501c18101c40703408240d13540b8080361808504408903001041e200b04d1b4110300c2660409003c100c80c0007035598038600c0f440d000400c1140e0a02105640c4022102c2e1540c840128810003000d11403403000b8821810018240130201d000750346d81c810320002c1c2d401844000740aa04001c0003804904010740395a000341255082000052044c0ca1640301b03030b07000b140040d07444102c81d00e0b1100810232140b2008200d03000100030402c01110541c40f00d44940e0083c0d0302e8207181031406c0001c0d0111862604540e405410401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 322422158 1250 322420908 322420913
    0x706090506090f0706080a0f0f0603050f03040b1c0902030a0303050f07080c071b082a0f030304170c040603050f0d0306140f1203030903032a0405011107270f1404 71
    0x4406c01e5100940d000003060002c1283d00e541c017100c07910700111070400e680700c500f40700307200c1c0801101060703902c0341000b1482d0074242881f0901078045c000325000d01c4c030900c0458542c2c0801c580c22041111340e024007103c901000c0c525000d4040c0000b01c400d078042ca050303d0005000e5070321400e00b0074069000b102d0308918007410f9840f18001c40d50750a4940312900b008031000110340074100007810403c10344008100d640704501c0704064614044040e5144030f09203000295490390740100855080754100200d1042403000d001080d4140700b40340103110740c09450710700f000003400b001140085242c07078000113403090001040f8043d82140d01c03038000c2c01c00014903504a11980e080046a500030150018a202c00780d079110b200b40c03440d40e0300845284a068002005000500c91352a50211401403000a0040707001e0700d02001c035146e0b004501c0750b00e04000c0170320791151081e00113004440207455490f8443c0005070300306804502420f00e0503101d496403450070064404a41492044415034080d105403842e0310f07200c03074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 322423408 1250 322422158 322422167
    0xc03060605091003060e1003030e030c1f03061a040504140f01090905030403020a140102070801060b0d11071b18090203060601050c070f0e0402040605010810030206030a110706090506090f0706 84
    0x20a501d41419a100804102c14840c5040f092047c060b1110001c04141545402005001c440c0c00c0f140c0a0740c071082006103542e4425111120508a03106076520380e1802c110110040e19482d80314841c03028103900031104c15000d03000140705940050300d003440740030003222146001410480b25424080e40d25001030126000c2500403000b182c0c040d83c220790410340c40303800049403613a1540c8410010704c44503418440c196014020b0000520b0310304020091a13150250200c0c0e68401d072100200026910f055070284445401d054030a41600718400b954043e0441d42803031000600b90259040b00051184a40f0361301c009801407500841c2d010340501542d4849000646803504880810344850044003004141507842d91000c00081c038004000c01400d060900520013101d0350b0390030046c10000c00d0f40800035400c01e2581950100c0e41e05807000d03552995170503c90002480c1004181c3e141b0354001034041c05200441c1c04c0884050b02a0081d2401c03a200e015005940e80d0051401c18100e030030220080201c140113 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 322424658 1250 322423408 322423429
    0xf050f1f0302070b10150903050718021605010f05130c0b030601030902060c0a110a081c03061d180708070e04150e100c02070b09060c01091a04060c0306060509 70
    0x3242409401c1600c156101d050307080044440801c05c90340b07000d04100c42555146c0c020100c4030710341050030f100380c02c41c3c5405840c3c100d180520100e6907090300c036800070b194950b0b0480350030311041000882c0d4011645420360180070b1340c1c000c00090908041c0840e10160f01c2403180d01406920010700c140c03442c58a00c0040c02900018455810f06a8546515000d40c5600c802041c1440c8540b0240c00d42e50050710304a01c004c040001143c1c090307400304c1010710201100245510042d020412290012640c10340c0481c00b40520f50000103441a43c5800e402c640c100368240300c0d00030880c0e110f00c5240c280c01500081d543e000035100c0c458455000c0b20041000c40d55132481690010b0244d0700961146620103918801d690021081c140c0b150300c9000116a07542107841000445003442c0f014001c00c03440d00074000d1290140340c55140c130840380065201c00061095103c0b1400541c450082c9070b00083c0c1c0d54001000c640c1c00c0b0f8003a40c000b0305190705403031441d100e0310802d0140c500171384406090104410500820601c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 322425908 1250 322424658 322424719
    0x602011e09051e060403080c0a08011211040c020708060a092406030c0b0415030e06061c060510210c0b1813050a06090612020105130f060203040f050f 66
    0x19501007940d0307082e00306800d40d40f5035072200000d020070f08103440e000b400058024100f40c640c1c1024040c8900180d80b0660743c504440c07030f0f41807140ca11240c500b81807440e13841c03070ba00c2c881d4083d142402c250001c90300811a002180d01400c1950f645076075149003102a280c903588001c0408011003078118600320090703c3d9070b03c0d0004c004400103140703841e9601d01c04071607901d400101072004085810030815400c1200201941460b180c00c0c800f8030f0440d07401c07940d40c010103000644200302c041190a860741c48001c0345014641c20105c14040ea0404000d1482c000205004d0110003e158001c203118500c090481ca64609a100c000440302074a000800121500103205280c075011050340594030030380e04c100868100d121401000030f418203107034036464202c1c3d1041c0d0107285503070700308142000254500c01040200e08d4082c01d2059a030414032030500e455441e0f503046400c00740c401e0040403c420354000003070070990750905158070140303840d2420050402000614658010841440485940b428108007040b048 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 322427158 1250 322425908 322425913
    0xc03040b0c0312130b06010e0301020f040f030c052220130609081203011a04050a0b07260711040b0310090203010507080f04110114030f0f010602011e0905 68
    0x60300c0d9004808a80e2086040e507240364000318500710300200c0200d00f1900603441032520344001e4140d41d03d60880c0700c40140b51314180190b42582ca00e05807003e404403841d0369103500d00303540c1d5903454200f150318401c8a408240c50b25406c03504086080d0030b00180c182201440f00c40801a40400c1342450300180c02201c4500c1130001c2d49025648403250b00d40080c1144c8400700c941a0a41400d0076401070428801ea4020450380d448580c0340d0900c00c1c0c0c60402c80e81901d40010000c107101203144101030051045a00c00c0b40c11440e09803000880c025401c0141100301e1281d100410408900e1040103040400c101c030141400d0010095040007859880f840d9a2820010b0f20100700f410f00c2d0700000303050a41a0304500c0803191038a01c49001c514080c1304540c4d0222407070401d90420b08005e058803050882c001d20040914600e2022004180e0251038041280041c500d9810358903d000c14140c1080a0280c681911000c052400421000d0040c050300700000d104100d44110254200d11040c0640441170080e201c90 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 322428408 1250 322427158 322427167
    0x50711031603030203030f10050d060b0f030f07080c0901061704030314070906110609060601200a080d0b0a0b0f0d0b031009050d0507080d020a03020d15050102070503030705030f0c03 80
    0x80d62604840e01c000c0d4001d0300a141c50349821030700003141d250f00518081c03040e00c0540061100da590301c01002401a04407100090101003800454280c5200040e06513051160a60103017403c68005113250603102000155130302a2400c10030311003030301021b01480000ca440c00e61f402e88007a551005050b0300a01902e800304500034680740602c82c50100f591080f0025076040000d0203040d80141c0105960950f1800400b16071910005807a1510f4000e00014100040c9100f070110a201c900d000d08004030311072095490502e994a04400d442e80002c1003c2e0b02581003803548000c5180c188907590480d030040121510380200840b0107042d40c0e2101c20128229a40e91114082a84003000392250300a4455000102d41026043c064548030751082c51108002c800c001110001318800e042d00d0031040e00c680b0150b2103914036101640a402074840320b110061601d921446411003e51f0b455007100d0081e0250742c055510343d010b043e22031250074400750950380108010916440c0000060042403402001c1d030b03050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 322429658 1250 322428408 322428433
    0x8040b180114040b01080c0a15080405030d0606020c010815030a03030e01090b0118110f0a03020d020906072001050c150411030f060109050a0501030f060522140d0f05071103 76
    0x600c4243e8007030300c6400b0300d00300501007101e040100d083e034640200ca0f05a034003480c2a03c03000f80103c00d03e411504100c0c10201103800c200d42001507601d0086065418005c49232200c4000b9134a03803104040b140040c3c12003000c66003218101084450300399001c2c026200d601c1842d2010340191000110742040b035907072403e054003c107440180c0355002c3d01d41c250280c61400c000c040d000083c0c071503003400b0510302d8004000c5219410410380494040842038100942c5490042c611003000340161003006400c490001012800c005204200b14601d5668612041000361107000445d40740c014402e5114039644490032401d5024000d041c210303442842003101a1080241ca00800c0c20024050030044903070707000c2001407200855902900340e000d003c1da601007102d9807641d180d241e0100c0400b00d010303008603600c4000c1000761030940f1100f140142c4440190256078840d1510724400704411b9803109183c09811520403255110f000c01c2c9000c55115510f15040580c56111401d82d08003400955616200c0c02014034030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 322430908 1250 322429658 322429691
    0x9030519050408010e0f0d080c070b010b1308070807050609040e0706050307021b182a04060207081207120c020306190b01020705030d030f020702031b010f08040b1801 73
    0x903590035a55403030751520300e0182c0850944068080e009103d4220419000380c030030780001c1898001d505450007000c01d4907100440681840b0b818070141c910b14140001040300c1400d500200300e00c0701581d10032040300340c3d00d01095032181d1844c01480c3c19600300e0a4200900e00d031039406000f4019005200040103050f60048030300d0100c0c0d940c0a440450380c00b000b000103623501030240c120070215800703501403e503080e000010040c11510350000a01011400492034481c05611003a00000d50840090b4140003403000480c1c481d04103119450040c030488401150041000c07424090405140ba41c00e410242940d036080d03a5040340407080c00c04c01c00c2039911100565020085e050051030803010311180d860b00c4010328802d40344070020710390640d4007001e01001540c8000451000e40b01c42498006510380c041075000d0701a116006001e507051023410755070215961549900351015400b62909114034403449803c2c1d802520490340904448009000615501050481102c030700320500000a007000d0114990706c2c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 322432158 1250 322430908 322430947
    0x180902120105090a11030402060d09050109081b0c03060a0b1302031f1d04020103020d090206070528050703033903110f0c040c110706020c030c04021c090305 69
    0x12025100e400104840d080c1040d6807a005441a2402d21105d600340400740841d21018000034003e950000d80c501460106a002038262070744803000b402440a80e05141401c0c0d085034411082c1031000142c41602c10000044e00c03404a03034007901414599a40011030401840104440c5130441c071060407880462503548001c51041c0c188451152040003442c102c3d0f06c03d1442d40d04000300b402d18640e810280420110409944941e0920b07001d40e0f105c1703101d047c08024044840300250040804540c040c00c11201041e04601030110341c131403607560b5910781444402c0c001385010140003a0840101400800d1061000140b20f42002d015201e1040e400a040003201540c541220b0800c001d07070460808169004202614158040006102c3d0003410602c203602c0714440e281c020312540c1d0303403000010b902d4042d1441d07280001102c000d0340c00300e550f5518040e4a4200601100d80700340036640880701c80b46018030076284902190000e00a002010a11040c0203102104080d018401c0a02030a4030340f040342a4a407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 322433408 1250 322432158 322432177
    0x308030a060f0501030207020306060f060904140618040c03031409100e011403100e0a0905010c02030307080108061b0c011506030c021621030c0c0303170603010501080c01180902 78
    0x14014034200d038010303102e030080d00014105401082030502694000800c143c020000721507c650307910100d400198648140d84640d5002400e0a014941c80510c118400788100f10943d40e08641c0502d000614883c0d01c0b044900819407a0010f4007440403074071815000c545c580e9403824040c540180c01c0001034844228180c1c1600003190310406c0015940e200004031030414484403a10b0075030400720280e84e48250769000b25105800c0050001d100d0800c9a0460581150848001c0085040b040c00082d101d42c011503008000c00e140e40c0000881c0c07040043d50500c103000642c00c0d400403099103000b4591690242404040d299201e0302d00300184050f51005500505d442d03100090007650401c0060f06145c40c00002d01450800141c041101001e0b040c42d202800038000441d601c11200303443c0c10f5a1110351403c02074965a810302011080581001c4041002e07041c1d040c0000d4603550380c208140c02e8560901a000d8150030204078440780e54000c42c03c031300103103000c070900d41c40386078849a082040303070001081c9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 322434658 1250 322433408 322433411
    0x3090e1303030f0509030910050d0501030f1202190303091103060c0d0f0905030a0e03030d0e060406320603030c06090102180d1a1e0a0b01021b0102060c03040c0308030a 74
    0x210380c101a09032160401c1a01d0b40c160901640c5441e18944e40c4030b0003a070001034000c500301203044440300d116404440505c034403400200030550f101d003016000011150404c5480a00c590003480340b040c00000e5142400d584603602400c28403160784c0407005020b40481c01c03581c0d4040200c0ea03004a9a0034005107210b529000a4a52508003051711181911a000c1315440d1480c44c0c1605000411004000c885861556040014454074220042441c5124000b5088051450161066001703030012a2440c05070b4007640c02030142d040502c03a1452404803011041041c9541058619995050325042580c0814020140ca081020010b4101d0400c3c03421130300488582d42c00550420b958400d56801991410309a40003c8802115512070000100040340104c5241d0601c00080a03840318010744182c90940320780fa9141421b042c1c180e200505260740517140580200d0b1055200d51884010152600005030b0003000d1a440e00e40d4005004d60000c0c20503500201904004404100030300025406807180303100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 322435908 1250 322434658 322434691
    0x1303020d090b09040e0304050901060905100e18060301110d0608060f2806090204081006050621090a02041b09080706090e060a08011b080c0301031e03090e 68
    0x1002420600c40e00a4101845100c0000303000954408041da03a00034029500020a00041d0098038610f0040e0307400030f940155804000f051840d885807484044800680743c07040129400441580d607207400c601401d07084121822940c0c41c11203020042d9030403481c09000014661148071a00d602988500000003501d0345856080200c100704109a6034003103c02c410025440c14210313040d0301c4000386a0003242c0003407844240b00103503130484d60082d0002d00803d10115542e6070349403503980e1503c5060111903038043c540a000107a07030a008088512103080c95105244440e00001503122001010b400e02c0c2ca40e03c91841c009005803030307a116a04030340d00d22240e1a241020248030082c42c80304142c02407000b54218080c20420075800084180c25141603200303002050380c3d42c602140c0790002c0c59104840c95800c041d440c1b800320001030308001307003a8415901e51409942d80d644600f01c501c8280320040000da014000105d0358131461400d258024482d00e04201072a642c1c500c1c08204050035500c0b04410508400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 322437158 1250 322435908 322435913
    0x2040603090c0503030f1603030605061606050916050402070f0b0c090901150512070e10030b03070501020a170a0c141005250f0507140c040b0102160b090f040513 71
    0x4a282d00402c4210003c601c1c05d90781228544960103990f400c840707034031420056101018081c6e0018005081c0203081c49448064411500001200484d02515011325103000300d810000041420b00c0008010020800311138a00024031000b0f50020340152030320b40b00d01c030822001801c05081103008940348100b0303540703a003045410462100b40680c01450b104451081d07481c7c445800c40d05942260b010804034402e40c2e9034414081e100e05c51032072031459120840055030007605415602100d50410281c045604240d00c030401a660ba00c0048406460444e0000241c0d01d140d1082d0700400001c0700718034104900c0411540c801410120000061f909500403040c004440c04040c4501a0301105200c805070360480ca009007110011072440ca4034081014170340002d41028014001c07904060380c441000c0c151441e03002022038403661078524291189041220440c0c556100003800340c2511200088040b10310302c1c00c1d0140040d80d02c420485904040311403a41c0d42e442d41c491140d144203a0941890300d8808040d407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 322438408 1250 322437158 322437173
    0x305011407020a0f0b0a060b0a0206010f140604090c0504030206040b041a19031a03070e060906030127060b040f051503030406020304090e0705120d020120180f040204060309 76
    0xd01c12000c42d400200c0c0c50010800c0d40901031102500034110390419124010700c8005080070b03802480e81c0e2403001600540c080d0303000990714126900c03181c0b0700511680350803100400d0b421130003095a00031018001408030200a602030803aa101c031341042c5207095601e034040b4680b900964041e0510b08008075003000b043d100b01c041d99011501200c20185844240381c100404807402c2507086080650750704484d007418a50070705d1110311420050032a0030301580c0d902071903003d41c41201e1450259403040b02154050505003d48c3d611502009000c404540c0f501c940c00401d1214140705440b07075910f841010249071154894882c031003d0404000c034032403501c0e0001c1803c82480400003400f07540200402c02c1000e501105803003c1d03840045021a0600c8080701843ca000c54507040294020841c45076507426040002e02c44040c0076040d0004c1c400d0081604400700d00426000076001281004c00506420100c440080d00c1413500050010000c40400c0c8040340c1240c100b5000140829a1645000180072aa = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 322439658 1250 322438408 322438411
    0x506010f0b03010b040e044706010905012d0504150f0206150d060e0d1206031a090115090501090b06040308180a0801020703020114090109030f120b0a03050114 70
    0x14010402e00c0c41d40350405201981c4141d00ca00485881000017040402804880407403a0b5401030701c03039603520b1b00034402610000e40c200941154070700800c5910250406200e50442c8550016190941c607145440d00644d10b220380004039402d43c60104150750b15040018219141000f001d603607650b1114141300400d00402e41450b00700c414800100300601e1019400030714a0f905c5020755401c0d01d4480c10304c50101d1202d505900c40181030904160a12081002c00240f046e02d80440340e480c03171004d203491803c440032180c003804041d00d14144c103c03031440d0604801c410560081d03202c8000140071813008180003900a200d40141c05903076190130040040d410f19000c1c01083c0501150b081d45040c0c91a92105c91300d02c1800c0d54640c3c0005010720084c025621100e0020060500000a40d680d8545290085c02002c1a02c0002002c4000c0c1011070000101480381034501541500c6500c8001804036050381d107119128200c2620030307161000b419198642188070001107200d0300010558074680b0b161859202c20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 322440908 1250 322439658 322439669
    0x1d030f0a090b1e0c07050303160303051b070b041e03020c010923120106120c0e130f0308060f0a060905090702060702070b0a1b15140712020d090f0506010f 68
    0x1014031000007020030300040c0c0d0b581021405071091303403603641d4804213080c00c1e042d601c0390f40c0c14000410b11909011003800010f0110307100e650300f0003c56440e20010351941200a4500004240a110a0340000c003007041541d0014007407541a440984981858203401d5501003003200186c104019400729540c0142a24001c0c0128051000d25800080902448800c82003c040d00c80c0035050f0800c242603070294004400760203801149056000c00e41080002006144994503011200c41e00181000701c641000d8510a0f5002c40c40c0e04502d05151801c40d900b01e8013520483d44100c2144050707425940c0d0b00e011000411090301c465090602d44010480d00c00d40042800d0190f40010040008495010582c07c1c01d840d1003a55281c3c4a00c900d68044070240c4c0440d400da62615010100d286c20b10403000c50940c804008204180181545416806054001560341c00040780f04950040d14500b11030b009004906080c101c005401540c43d15062000100d81e03005a403150800750050002a9100123070102404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 322442158 1250 322440908 322440929
    0x609081b010b180411040e062d010905250e03010b040203150909011103130212011b03091b030f03080106030506010c020d080c01110a12060b09041d030f0a09 69
    0x10392400215221000761054601100400d000250401517004a405000c0501910030001003804280b65581d43d442603071001c500e040400401e060f50007110180c09120100d040c460055a440c01114034007400002d4161003c0d1040c804240545c258901180f841014607982c801e01c201da1321206050844200790a4030340181c0c010020019002d9039880c4010034100301791401c00250742e420a20074010110752002c8100940008103015144640f504411501b90007100c0c07003c440c40b484003010b4200c8000720080b0b41d84202400c00c0712107541c069401182064001c00c00e0310322281c84a800d0071203000a641084030b034110564049018503038446162405003041c0d0804000c141010000030303111341b000c00380003031040f40d1000d075400030440808256548915100000d114080000f807200d8844d800c403c101c08009400364111300100341031401240c0460f10a00c0c01c1c68a4103c4200620002e01000d20302d03c82283e0001c0c04031114060208014070240020150b0282c9070f205002c0c0003403c102841d40043e0909 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 322443408 1250 322442158 322442171
    0x40b0603040b0c09120d0e090106050705060f1003240b030706090504050c090405130b0a020901120b0a03050a200a0e06010f111006080c0d030207030f030c0609081b01 73
    0x5140c0748400f40c0100980c26040d4980c0c507203900244059000d0110301d18075008400380e03541c001e5080310ba000b0795110f08507001f40c543d170388400044031540036085014155a00030004a14090801c0c00c046801a8038025805482ea449448020096025071807000c41c40c410000c1c80c241d203800340d00c12170480513400c8001d002a541f408400402c0d60302c030f9006041c4940e0b902c0d40803e04907103002040b103100410160080c001443c10038031080030885015029501c4401d40000904810424400c039001502c058458483d04068080700754010700110348201e4100507500300c08004140c00b003000320106480381c41002a52242401d4641180c0c80d040002d60051003800c0c818041414802010f540c805401c0c60700c0c019009400ca821941c01c0c03e008c00684d42030080682524001495400c070205403007120007210481d00b01807050140d00c0e0111600500140c005d1102407000a001c01441d8001c5402840d0101c1000f00c00d40b00c5908503050710200300d03400c640001d0115000d200d20312034507010090801c001c0000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 322444658 1250 322443408 322443413
    0xa050d1d0d12060909050307050115150c08040305072d061d18090d020118020901030209090c04060603020705010509070303050f07020301020c030f0703200a060203060d20040b060304 80
    0x4440e1240d08074001d1144903a032541c0403503941d42c021801402d0803401844022840c3c102903449501c8404251895420140c0d01b400701c203500044002214088100c030725080e980b002041303910840e038940c11503c0c40000c103c0003010601c20401c81d409048038607201011045400303076960142c0b41045141e00480c0310306000300966900141000a05030034040301001180c0b0b8400010190203a0305a4500003001c0300c07050017210400092041030740041c1d80c001304520402d074040e0311102800000b00941c0500184010300050421415076900300c16030350300304c5004c4181040060195003640c0c0107003001076800320ba01d00902400340038594001908001030b0a0807030175510010964442d100000101c280c0c0010000c0443d2070035412110b040340b640c0306494881c00e11240c0c5174000d40c4a240160300240c407241701000400c40441303080c117a074241d0000503c0d0611082d55990b0180d000100242da0002406034607801045405108080140341440e02c0f9080ba40d080d010842244d10b403d10680c0504000d0081200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 322445908 1250 322444658 322444663
    0x815070f020c06031906060e15040b04060e010c0b01030308060120070b091306090209041b170703090506100f060c050a02090901020f130e15090711070503030a050d1d 73
    0x4000050b03d4150f41c80d074440c10443c04082c40004815000d6190000004205038400b803070507510078040320800051042d8000c02040e5004601418007900000c200c200140703802000c83c0d412848041c14080c04030007c5441c0c100b00011700b61300a801007612442008215a804000b85440d034000c0301c0020048404502c40f00e07900c464502900d0a40000024040f090765269980810283d412000601440c0d40b40c40d121800382d009030a240c1d015604100e42110346c0580802d01101c4080c0c00e541b29400d0308815141c200788158087c003d20b042c565103440c0385001c9003050185a2042d2280690040d08503d80700102c2c00d0700590390b1050041080d0071505c00d0000b03c0c0440c4400140d901202c0d524450307140e003082140288281c11201020950003c0c42c0034480c9140e150960841d10400d140d01c46650740d0b060a201c40e00100041e5580c0b203510354000480450040c0d50700b1461613200d804036030303005865601007403541c0d02c84a402c50124101042c1032000703604034041c0d1f03081080840044121003500f1140c103907 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 322447158 1250 322445908 322445923
    0xa05011b0206040b07020f0723090415090f1203091223130e01081e030a09050d05011d010605040e0f032a030406050406121e0e0102070506010815070f02 67
    0x1c00141c142c80210b1710441c0308001880c00340030382800780c131b865541e140c0c6071010070910040e0500713a960b404074403040750b841c00d56126440345420151449821107900001c000400010108940090031400000082054261055014289500c001901c1c400b1800c140c25001840450795041208025444100116008118410804140d10702e51a00c18442c0c5410000180b5044160001d03070344400003c04020004041c0000300050031035006025480103135a80b82d20507558002d02041c1c51400c10070003810211115101c65010300000140405107004100144400c0c810150a9039101d010900075444d0620907070190440d0640146400904005d445484c0e0041540f00490141c1c0d44c68002e1000d4100d1002c0c120503504941525991a1036210107046031308107004044c00240b850300c070100319032850310900d140300d58851000c0f50304a42000c100d0300034200115010a5954080c810000024400c200700c501901c5004050030b451040c120108190100040c802c2d0104040d160500c80c051341c02080b0310 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 322448408 1250 322447158 322447163
    0xb0f0307120527070332010501080a020f0102030d090308180c030d05030402030a0f0c0e070206061f02030702060c060405010b03030f030609070908030307030605040b1203090609210a05011b020604 86
    0x2180300707080d156414145109944003034003418903100d40c4521140444c06c46609603805000036682071103030440450894200f4002d00707801e5444005da0901600d00031003032111845051040700d140681c62800701040d1080340c1030441c04074422005000d04040c0e0244c52520300805180108400301c001300c0065075841c603661656050103400404501035450034000b007402c00350081d2440e00c00c0c03600e500e01444124071310f02c510b031140680c00001c101c4ca18802304d411401242c0040c41c506255a030761404210701030f1141c072214158881000680c006840d11b401078000140204003a2080e8079207801d000e82921404941c072803094200f088000400610030b001c0c0c80c0c03c0041500e0042155580440545496005400030002444044104000a40d01d80c104505559040d01c084c000c0c098640144802012450116070b4207400510000c030312800c0c600090f00440f90014009a61442448000814102d440384080d8190700308803c04c2c424030009014902401c28000f040d5403070505100d01c000d40700d50024000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 322449658 1250 322448408 322448461
    0x20c04090c050d0507030203030304210f0c14030d0c050c010f020301060c20090906060a0510050409021e13060f080115030c020c03490c030302040b0f03071205 70
    0x185011310004200c0d82c0095035000e81241d60b241854100b2052082680b60203602407501d0001120b0a0b501c03e200c8132108403040d854103000311000e6541c20302c0840c00c0c243d6411040c80144140301c4201e1240c01205241981522004c1c2d0356141e0f42c2039182552400b03042462018010801045170700c2c0e02149141e0f00f90341102c0e020255084080b40000c0d100308030b0001030b500c0103610302400803240020400718058401203032003a10556841c000d2142c0c122103c1c3e06000814014001009218503d400900c200c91058540021460343e07001000420b03040f038402038022100040301800a10f42007240d0209058003810004c800c0d41c90300580400008580e8295010941c490884201c40c2e4020815100d20f00340040c191424804007100b1121603180e1305040382d960b15032901010080141004561485031414104101c614400e0780d01681d082c11180800c5003015801c0100080701250403001c0c000c800b1101b0800703640d80c00d003504014884a41b00c003940992a00d420140514400c5940301055005c2c401c428 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 322450908 1250 322449658 322449679
    0x14060f13060e040305040e07020601030201080c07050a050307030503011701020403080904090201030213031b063204080106240302090307141816030509070f05060f0408011a01020c04090c05 83
    0x419002a04469110b14001c180c007106001c1099000405841981c4401100300c0959454142c126501c000a11006c0d000c2103007140420035a00b03481c4000e002c0c25000e40105c1c0c0c501400c5a85a910f550b01210054001400100c01448030703005001c0130804c000b402070700075802e207801e5803a002d155210f0b502010340718035a241c0d9010210390090301522000b0490a4807100819642d0030300141e1007903e02100c001c01c1290500216017039020300c50148005154401d004085440b440500c00c1c8403807034103d81c21843c0c80600001075044001d01800f400740841071440c09841c3c104054450001d03600d05400000d043c0140718012030391306c000840c03038212070307164160301c0151b08000041802c4250f51031054458a0485003040201e40501c071540350301a185aa00304050307a6040d5144c0c1e16000c55000b124090414880108203501c2c0c8100074104005e101501140340075540d85a032400c41d0040756026812240e80c226100166070180075400c030b401400e6409001040e180c1e40d41c000f46682c2e03401080d104004442 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 322452158 1250 322450908 322450939
    0x703110105130503030705210a090306022b020403060c050306030d080601111902100305060d03030f0b060a02210a02100e03160309090f02090a090f09061e14060f 71
    0x10440c0024003001d000d0780c1e6a150a410003580b623060f10440f0440d140345030181a01c0146210049900f00310143c0e40d409446070450391030704042c1d0b0000c5842540710b29003440d603481e05909034200c03040001e01c00c24010703521441d5103485030540f080032100358144401401040255140481d1540c0344804501e4111070030b503181d40050380c0d000c418485a01481c031a4690f01e44e200c2c1d1811031100d030900c1c000c40d4101c4014601380401c5080d55000c8401c0c581100c2c0e41035820b800a4000d030019040c07a290007101051000c2e840000c21065003007111590010381c01202150446044c42d496000255510030602d85800f84201e4007950b5060709019146010356141c09070b83c02c680c1d040c019204940c0d1440c58800143c2c0142c00c000380016001c3c003030540683d2600001680d01446442101c982060207460000c4842c82e00040200400b0310f0440f0b040c1c1c1c161500e1030754000907628482c8030700d4642e00c03541c64522024448410002c554070044042d810321403003401e100b6655981d11034900c0c141403c4889282494944 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 322453408 1250 322452158 322452187
    0x80703051b10020c1b1011010b040203040818010c030206011a0705030409021c180f1505011502390d06110424090b160812040605010501020703110105 66
    0x1019603180c58010402c03000d2000c045a001841c65000035000c0f40c003101020003c003800c02c3d0018000541c00b0f001000c614812502490005441003007000000030311340c816030082404c0c0c0c0d00c200c1c0d0440340c071500000c0050405042110414a1003000c0c681201c0d070350000d5a01a6039007106000e8822640c81c0000c00320030380a00d041c00c8803240782d840b4003529211030340d2f103030311074040e401c00e501038030404ca5002451840060140300d2a95107040200c920303200c8550130381b1010074044907554142c4a4901200b03a140d054089030081500902902160311520451540001c6c1003001d00d002400803a65040100b04c5041014607482c0003e01c00140b0b21003030b000a260006841c4010300000401c500c0c2000401c0d82407410071400f5008907075841012951000080d000315444818417040040400c018031000d01000000b900074014901000e0303155060100292549111a00100b6010742034903081d5081008000b030900076140140300a000400d000c60a50342e03803c1c070021150220302c0c10480701241020201d103d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 322454658 1250 322453408 322453447
    0x402090c031003020d06060f290d111308070b120411010507050f0607120c05030f0a020409090f0212121b0a0606080c2d01050c030708031014060708070305 68
    0x1000a03190880e03e00d0000c029000500c110203103a501c101c0000740080418510140c584480d86038032a981d03854403042025030b0051080c80ac0c1d119074609289810000f48002401084605078100310154030b0607013031628190164209202e01c0c082071003205030054071090700030341182e80b220712040308401800040b103184c01064400780040c82441821617441c3c43c0458014028007407030b6102140d0324408001e02c81034400d07214038140000c1040001940848000b00d083d40c00003100140540b0b4a69110595020b03a81d0550040c3c541e8500340103043e045140c0100404c03003480002010b800650380b08480c001c00d60007155044180d103504110150010b04083c04141074807507206800300b0015403100f8a06e55101c3c11984e01c00d006003001d0401134400021101c21824000b0a4003000400070000030044607150400039804d0703c54401400140006038005c00518841e2039500c4003150144d00c1e001801111110080d40e460207001d0070003072480403074a44e000701ea0300c840e018104199200c3c440300708a071007030310b9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 322455908 1250 322454658 322454663
    0xe06031b12180a030815011404090c030e0c280503010c0903060f090b01140a1a030601021522150c020c0307090e06040b040305130303030915050402090c031003 70
    0xc0069299030401d05440300500032682c0e034203003003102412481c90700ea0f1900071403000303804074140c000000c00c88200c521511032458010301d4600030f0420000064100e54000b038220903074083e12070850160382c69042c0700e410b070191500790007025048520b00c0400e005c40b2009410b00054040315509130310070f0607018611f10003400c02500030071000300c4a0200a00504407408110b0b103480c1005c2c0e01c0305034076109004a80d48d840d0407003000d40d00e13a442c0c40060b190750004030f503030345400c85044600019031240e91061a075840204800d51070392450801e0009062181c00d00322038010b00941e81c180001c61032030511101c010030402d0190300071980a403c00d004000c203a01c1700c8104003420504c2154209602141d0146000f500b50200c5410300c0e214462601a646003800e4240b15511150005c1c0116200d00d060541150003800c2042c40d007c40c0503044040c1c44040d0300300b5000b29403144401e10800c2020011014214040c407800c10041c2407940c001000410003904105a0040100200d0007403004c04500c81c0007184d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 322457158 1250 322455908 322455961
    0x32004030807030e040b0f06030a1d01051608040803070509060f0a0c0b01090b0303030604090206300c25061e0e0105090a020622171f0c0e0603 63
    0x554a01d445907441d032180408a0014081d014107007804c3c02c1034016102c05420044c514192140c510040c00503a820080120f0601a2190a0030466000e915440701e140384480b00003203200d142c4080101001884010a1000c10102e4010040420a071400f0759800c08201d14020b542d642102c000102c85028001c1c14111040740010006051604080c61a450703e00c9890b008405a0307a800c00308045440240b0b6458140d0001c01c001249854203510032081203100500c82401d04507074115100c1c4160603629100407540039007000d18180804104120b5020300d0013148c144c600f410b81140340081f003080e40f0301c082d01d000000c0d00c0c2d1000c11010b17801041981d005880c10200345c650381c5440c40c1c00341003041c0050010f9403a10000c144072080100d425508140c000d80303a2490300b86c4010344500c03041304101c000881022140c1000c10703200c0d200340e4581260900d00008081a0001c408801ca0307060785029003120581c82d01c410b4106c45a0490340d03e07800ca1070121f0700a41c881c1c3e5400649040321070290110b50450 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 322458408 1250 322457158 322457167
    0x6090c0b030a0b010f021609020351011b0c170706320706020c0a06020315030a11010c05030405031002070c0905011d040f050610080c06030402100320 66
    0x200c0381c603885410f42101c2665603282c00b0282000c00d036141c1d00002c6081d03240201c0e01c80288001545d6400035500400203142ea0440c1c80540074580081c41901ca0500d50141c107c808505800345a82e200010b6540c003038105040c1c03e2a180c000a00920b0b131000e40c4c070030b610b403ca0f032844087c0900360082c84002c110040704c00c140c44102c110541d840d07174468068036000c01d08403030a60348074003140c8094050a001c4044400c0e902050b0401180f41500404001c0395130a400300038102e46280140a800001e0744140000750b124204042c20715088507610085601941c4550140030201766004801012a003081c00d0080d00d800203402e0150441c8138a4214642520401c4627006e0f4624103603004101d0369006015075103140d900e5101c0b65080d24020300c00c0c9514968052000001480d4114003035030080d10801e00c1c8045071000b681c504d800d1010450b07420408032900d100c00c1105440510803092550380482d01903180d071405034005820307110851581d9003015034038110010f0f400134070301d00041100030220005485 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 322459658 1250 322458408 322458421
    0x6010602011e23181b04051510050307121b0306060807020307060c09030203010c170604090f1203090503030408180603160809030f0706290102070306090c0b03 70
    0x41e0419400b591114030308801c41000d2031010b48035650000c5441c1102000c8203403402545420060040e0200305000c659000d0b000d030021042050500100181c0220071031444071303a0401081b078400074a07200b00b90390040380700100c070345e01c030003155100e0358543c101980c6903102c2103c00c5440b000b903903203c1c0588034944007011a60140c03000e09011403010a55003030204a03240c0900f220080c9050b1600b40142e40b040c025180003032456009034042c00300c0c0c2d10740f40303101e959203400090941350005540b01c04030300303000e0101c520306810f102a168003080c256805d010907485595401c41c40396200c007002d0035150007500d410312241d100f0341042e0a030541103022203032a0309007414407450700c1c0d008001d410f0701c03001c07005c0c2d2100503420302c4030540e4807640081c00306041142c03040030259482c22000307081556034003040000301c1091740a4406480c0143c050314001a1640492024508810b0a200500c1320f0400324030703600c0040d0381d0005552007900e910441c04149800185080040050607400c1444d0044002c0f04020300c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 322460908 1250 322459658 322459661
    0x4110d0c09180603140708060705090607080a0309030e030f1509070b0301081606080403050403022103220b13031203020c100b2817100c0c120e0f0d0f050601060201 72
    0x40d00d0080e402d1780150f101c401640c640d52415407042c1c880c243c0180300000c1d2114020702c058003082d6030141034240340c00c40300c0d550080d25a2050b034611000c01e0b40e41440d13101303059001c1a00c3c580303040c041d402440c00354104c011066541c441e000181c1484e107000300010341c9188043c81010000c00b51102d05c19140e5031a03040068a803617080103242620b080d81c410020f0010301c502c0c901c07401a034150720307150f00d424110340a0180c203101c56405088543c48110000040902c1000100020000d0070f08400fa1001000d0440c0400c80540d8450512804140403024084e100003188100322907200303070386011510320a031041c0e01038040d5446080081c0103074446820810120b4010615050381100d1904030303070601c00245540501c01004c420307000b56900106025940e00c850500d802400c4400455010240d80d00224081e41e6804013101c1c0000c03014519801009902c1c0304061214200307080400b00f04c0031400c00314440580c108486072090100040384421300c071214001d100e5541d0003000340c62140d80c54110103030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 322462158 1250 322460908 322460921
    0x260c0913020c0a1b0f0905060303070c03110102070821071b0b03060a050d0f020603090115030804030506091b04091a13021c020a03022404140a0504110d0c0918 70
    0x6034a00c034845954004000350003160404da428000c80c01c5805d5003440b080c040140f8000b002943c040c0310802a02000c502418200801544501100e0080a0341e120009040801ca64015a030703591000d10712140741c1603000c0040203070344600c0d445540c82e209a424005940380c0381c54083c0c100e0072002035001c86c126000341c00840c4100d2041c8c5031403600b10365038014040a50f2179040c01904510360880d0000041c6042001150030011000000c1800705070364280031400410740c0d1084030044400901002040b40501100307501c0071841c005041003036030400070b94140060040100c0e100b00c0d42e50b0790107010490305d4000301c050080c07541c007030450038540000349100c80100f50346c09910841000710350410180c40c448115003d90760250051520a00e56030a202a0f84098031009034555400c50a41c100042280302910040c95101c00340c0035414082d609000e6082541d400c401d000b00d0600410000ec07410000c1290130b1a49204000140c4188005080701d14411540107042000110742c1903194442e1240c1200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 322463408 1250 322462158 322462163
    0x70e0c09010f050702010203090d0215040e1008070b030c030912041403070b0405011d0301020d180c06050a0801030321020d15050607020d020111010e10050106260c0913020c0a 77
    0x800a290202c03010703503881c051524000c0c01a4002c014030021800d10300b070301e260680c6c805021071190800300d00503140c10ba0411f4120b00745c8190310320300b0000d55190b801c040303900606c00a405804240e0030b0145503901c40c41300030540c0c1c500301d2000010400682c000c01c0030079100c1a402c0512502d558880c800c94094a0f140740e10548613100364607000c28081c5699046034111a0140c44010449851926001d28140b503042102da0655081c0003a00580f045802540d410301090107029414817041c1c074110b44000a242c0102040180038052003620301d4010346020305481e01810301030b003155042c2e22590500c407a08031004100c2400818800141340b00c5070414003501c102d0350240e108240d100c8040c004540144c440180d030081e0031a00042c00342d40948035045040c1041000400c0d80c04c0c000100700e00d40303003981d2404d9408981c0d92004010890b0320140c1a0385085d05809062000c0310340081c12004010040d24100c1d0071034000070480620f9a500175101c1240126000a5441e5030011000d542c0b0780128a606 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 322464658 1250 322463408 322463417
    0xe04020916020d030e0304090c050301030b070804050303180c0a08010203221a0c040902030906270c01081f291c09020a09022a0d0e090603070e0c0901 66
    0x100e000300c1401c81004090000540c000c0c0201c61210004501401a408254066000801002ca10b080f440e003c0c5c0c0e0221521921855a41d51461421080d0b00c80010300b50303030070410b0240900c0001100441102d0700140c40705441c0c80811044041542080400c804140d40000810b800003004034041d0003451183c408011613070030400d003214858408201046c001090814a4510110030782004a0040e400280440c0500c1c10503407555024002c903801512480c605074000420041c020900d5a45100805109034070160061901159203a660207480d072080d041c0000d40001583c80070740708081c12241116050300206d060740c1c41441d0030b40010007645100c0c040b109059044080ba6981003101c00100c01e02c00c86a00301c1c452034142c00c00a125085007241d02050103000001c02c080a40054400c201404036951451510070b040303180d00b1210b00b000b10400c2d030040350780128882d0b0040701400400c1400d659201c80d5a032200300290510900b9049020080814414000c09924140c00380201140c2a00d8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 322465908 1250 322464658 322464661
    0x2040e180c01022107030e030a030210050606040612200711030c01210203090a0c0306020a080604060b040302040506030c1f111506060a1106160e04021809130203070e040209 76
    0x498560120780e468101a120020130449400640d000600085020b490f000ca003103160000002c1c00d14130036003001c0c0e005a01030b038412101c1c00e995204aa0304050f00704d1b032643c6024902400900501604004265000c1d69045118010900d403254450b207801c88031b00c126510303925490f20018020150001c68020301c160100c40366079500503428002414800b01c80e40751030201c0345800340040e500c010046441801441601c80000d10007000e4100035501c11000940c40d103013009801048454001c7c0351520450030010100710505001080318190b030380595010440340d0320309011030b01d0800030a4082e5000703c4c5580c25182c0c0310040d000d80480c095442d50752181006280360350305544881140e01d554803900504041803480c03800e00010314690000b4241401d10480a600321030901c0e40450300d494110b0403103101e80b45001d07440188008000c00807101141003012000d40300b11032004001100c1d004000200205841c01c42c501c482c06a10f130b60041c12507140315107801104100e41741c266402ca001d0580e020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 322467158 1250 322465908 322465933
    0x10905060705040f140105031906050d0b070305060a180221010f0602070b03060a1203020c0405070e010306080307080d0b120a0c06031802010206070f03062d08070b120a02040e18 78
    0xe1036100131760140d58460454498450036030072180304081081c1419519040010a911a42040280c09004a00741c508a00e0822405420790b000201038501c51000c417141400981154546c1c0c51402d0b00b25480180c654642d00d100302e28100074040b140d032000040600028003424500d0b10003064a22550a550380a41d55901a01c03450000750760003a400281600140050f0408000c6800070501034411115005076480102d002c8981c180c5400000130101c03080a05956050300401004180c7e00000358984905500e44501c02e0082c0341110358030315220b8604501550b1420300340c090b50b09815041e52f010781c0d20b80c41c2c02000f0035031510a4a01081c1410448041440c2e40400d200da45074040c0c01610241c0d8131440104c4071500c240b030492080c15954500860700b000350a160301080700421000600c40c0444456039425102598010361644d444810240100841c1000303585a60b0b6004604103450b03280d02080501a000c1c0ea08005508500f4008000c02e484400300421545020603041d00c52024151 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 322468408 1250 322467158 322467179
    0x1716080405041b0801030b060406090c090519030302100e0a0c12050c01031a0103051b040623070503040b0d020403080703030203040c0e070203040e0a0912021f0b0d0f0302010905060705040f 83
    0x43d200803011440410042001c2080540504e61041c0c00070000500e542c0c540300004121138000d580a00020403d10050066040851642e020803420300040740c010f80c91942c000f540c4087c01030000480b90380b81c680200039032000b000b40d1684243c1c00303141c0c201c80c03a407140c00c2070030714000c410400d0318a07100300400051154000c2c4035185000e0b140640070f160703000a00c8015030160901411200b0850142c40c442d9441c6001380c8040d10203002d050740e400d01001d03040b0588049014108400103032030f0008000da100001d000100315002c840e60b0320703000740c1c5449401c0b5607403000f0f02480d40040c0112a001400204246d8541d00840c0301d1481b880d01140e1050700c41640c1c1d400403004070303045800340c0d004200a20406a07100d0000d94041d4020300c010450003820341c3d60640025110001c14090380c82200c2038244507000f00c4a03508601c0200d9020041e0103030410010b1540b150a180107485440040800000d041c0300f9000f460b0410b400078200c0c1d1090400502c0200030f0b03401882100d50700d0640b210003241503c00d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 322469658 1250 322468408 322468451
    0x1002070210030915110405030c091006201608060a141b0715140903070b1605070b180f01090f060b181e060d02010c171608040504 57
    0x9449140c201901070419001004480e20030380d551000c4618031004500306005507007151000e01c100c00c1d01c0740c1c540350a00d40392400d00006940700d08001d0042000d600104407800c3d04071102d518210f442c4449081099500a101e080c00c1450342c000c80715101012046003404030210b644690499400c1d54540415904550700d080342e00341c800c000d1304041288071000101c044003100000100b1442d040c442d9442056401007144c5204099498888940d01c01030001c60060340201050082e40c60000b813030b981c0114a603001800e884c40241c030f03554a40d51580c403560a4442140d4040c0c2c0c40103040c00c0280c519010702c20380e00c1811034588120b004071998058180a070514440d030100c9030f0380c05010159101801b400214098540001c0c0040d000810307179554011841c000c034000c2e10f002c03094421340b40109601a01c0200303600d00900840750b42c140144d92141c401c00360550032400c240401050252407042d244601c0c2d00d0455208205e4402c80f06002114005008440044800b00900c1516031f5000803c86003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 322470908 1250 322469658 322469663
    0x30c030c1c053108030c280305100b070b071202070f0b010f0e16110d050403030e040e06060108100503010c0503060a08011407120b13020702040b012a050a12020a05100207 75
    0x100d1540c1c00000a2008001d150000c010306c141e030b801c280001c101e600801c00009020b03207440d40e81110070b4140d6130b018810941c104c00c00e12250050a4140f0f91104d010740f10f07000004117045403802c0000e01a9120344407083d070402082000b55a101319500f00040004c0c202001550315110790800041c161546078a140101c0c1d585407246000e5035168218907c1e0060140e01c0c1c8018000e402c281c10354401000e00503680c0a010759101d06850702e055050041005c450140307142c0c001c0303203046800c500a440008074194010001d00e06101150f0b115401e07042102d82e6a4841901503003815100045e042d0402c015500c9994141d40d00000c2540d91040282680c0214200c007402c68041408102c2a51060912880b00c5461903000308842170344401182080f005074000c86000380d030210701081145441d0145101c50002403030549450b140707180e035000c8000d413841080d03400701c10011003110400c1420b0025030390b6641c0103030b6448826070300000040d441d00100801200c8600540f42400914006c3e4825141c003141c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 322472158 1250 322470908 322470991
    0x6090903160201210501030c0603150308040302040c1103040b0a03051e0f130c090209011e050334050307080115050901081e04030e180c030c030c1c05 66
    0x20709900151442c1d13101d192112141001902006460701c03090140c40e00171031042100c140143c3c50b244008045801529441c80244c00e00708081000c140c01406842c1525011940043d10420410007a02c4031152901e20103014000840d001600c0119280580601280e82c1c40a01041d9184494822580b41c0e04243c01030940d080c0780071400034120308035681d41c010350b00c400001124015454071914803046d98420342d00b0580004500e00d030b559101e403080344c4130141d43c0400c004000c424003018090340002005140d50207103c240a000c0a0880030011546c82c003402e00c010a10309050400a20551040300e84a002c50988000003400d8034048504480c00441030381d8050030704981100469690718040d03d80e520140034090146680f03040484d440340114400d80b51803003c84405400e000506100701503080e105250001003004078418034080b29171004c072403c5c10b5681c9030350f1043c03000c01038064105081010104040344891108080d80400d008003001c8002c644010b0400d2201b03070020008540d441d02c06d5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 322473408 1250 322472158 322472197
    0x10b13090b0c1c02161e030f3203010f0506030108030703030504060e0d02070503010501081609020703091e0503010605090c0d0b041b030501090b09010303051903060b1206090903 78
    0x82c0c1202e0103808261410800c0d03003000101c0901000030382c0c105848800e032182a4440500411a66a0300200307050807542c10a4203940c0300341c4015241d0f422440102c81800383e0782491943c1a0343c400e800300509024525100c0b0454103440e50506640c100340034812079012000808100c1e403500b001582d04a0300325038011032800c8040d5504502801010b40304588441e210135041078441f0042c049200318400aa000b400018580300c1003600356074041e88012400e4101c40000c840d1140704803070420a8a80c402c85c09a61f407201c1c1d03d8203c038034070a0f82d0f0154400d8403101c3d0320310f95110040040e09003161000c0b402401175075100d004020309080705442c1e41040300e408005000840c80607400091941000400004000e06816000c0c4014200301c1d80310f0002a6840d030041c00940e14903c0b611505c0c0d04140c030070300700640c119a009402803141d001c04000c0c000302c3c0041d40e00d080340310740c0140029112000690762100b880c00713010081d40c8020344149104141d4600081c03c018400005d45007241a510718001170b5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 322474658 1250 322473408 322473421
    0xc0706020c1e011202072f03071e090c0917030313030c0c09020c1501120305030c03040c080703060605030d020c1f0504030f03230a140306010e030f010b13090b 70
    0x3000c6980c4402d41400001c4107415a12400c0380302621800d0700659041148030724698500c03d52903003881d004c3d49000a500004165034a0000c0e540c1c0036650908a0100c54985180e550010580c2c130f80d0282a40604181c0404000e81d400b2125034102c9070300b20000f507480ca84028140f6260300048600010754100c3d030808402082c8505003980c1174502400c0d001c4140750715400e141050342e025003140c58090b130000d120004000f44800c00140188044403040744404802d64008000380f00140c01c1a4660304007201203028820403c01500c01441000110360b0603941d280340040c007400c824428540b1038025002c09400c2203001103240030f602c840040c80b41042004003040d540e0440d0000e66000e003008800c1c4008000200841149212503000391101c80c203106107000d0341140410b8600680307001000a1060f0310f0429000503042145000342e5020316100c2c0d46600040315102640724406a25225602544100c52010761040c100b000080d00c51b650310b8012640d880d825201c085000030842c0424100007000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 322475908 1250 322474658 322474699
    0x609061b090f0301061514040302030a030e060c1b0a1d06120f160e070504060c111f11160b070b040507031b0905060f030606010305190903050c0706020c 67
    0x9900700020b01071101c81198401082c04c4840c5030304080102e6400d00502a952a00081c0b1b44120320400203520389030508690100b0f460382003003c8010240002110b10510740c2da100429074210780703041003c40300c45152240d091903c1c0105024a80c0c010400002d0204172191203241c074620801052410b51610b48828060160707052810100d000140240001443e6521041c0705004800d40c642180312034581c1409190380c03c2c6c08029108009105081104005841d0840f481441c6c42d40c01c00400003166050002150114000030704c8241249000810520746a41001c1040c8003207030701034200c5585110741680040e40040354004d40b41000c0c0d0500c9410000f555035900640d201b40f09000ba580d1580c1d980da82c1c480c48100034220018690340c90407041c0f00c80351861251a0784a0000c5520010510607400401e48a00303014001c1410141c503100014a040184000c4107501810602c04015007500c40c00c2c0240310707401002c5078403030500070000002600d51000801308000e110080982c0401004226801d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 322477158 1250 322475908 322475917
    0xf010618050c1e25050a02130e0102040906090f0c1b0c030c12050114060d02040905010b030f0a0308070201090f080a0215090102040620031b0c0a03030903051e030901030f09020604090903020609061b 87
    0xa89284c803403c41400d09e02c802e00191009040007000420070b10704004020041e149003481000100307181290141070700d580111408a007600391f1060f40500503c6040025140d645600044c0c800c0c004a40c000515680c0340c1c4006884a004030020031101241400540701100143d41c8290301c1100c1c6651180945442e60168503154480c3c2c00001d650071a0501080c2003c1041884141940081c8040d40034190001040c9900074010300c0200090240340c0c0c2c1344035814000b00320160081602168200c1858000c00880c001c2c0100c400c0300c3d840910f02070058038043d50043c000c140001d1010b0f0a120b00074002201c1074442c0c1a80c200140d1b0800c0b4001d42c8054240c00c030014202910f104000218101c0d8440030704080c00303036000741e403142d00c0daa05609210b89055000c014181c10006200001745400070007000351607881d5401d10300030806207a502032147c060401038074040d620040025000078010810f900c01c0b01c640f40710307409640c180d0780d90700031941e2a5402290890b6204d03181000b410f02c0503807404001c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 322478408 1250 322477158 322477189
    0xe0304090e01180c0e010e0c040b0f07060f2304050604080c07030f1208090c10050309160801090302010c020a0f02041503050d020c01020f010618050c1e25050a02 71
    0x35201408010f2440c071a4030895080c2d610034002d035000d10100582000d501d003d440750320300d80101c1e4140081c03000450321851042c2c061904011441c2411182d680040701d000d00c1c1c0200081c0074880c000e8240340002c00c038070980001c410a142044060030500702d40c40034811070b0004041c1c00c0e265619110100d10f41c1c46256004103902030b114010000915412060003214010450100c1c07520031180042c01030b80c0701500c40712240d031260701c035071155984001203100c5601191070569165152942d446241c004550242c85d00d034404031001150340101540503800d03483c082d600921200f040389509a0320b44003c4403015160126040341072015080a0b0050f00c007945d03a19121009141e660b840e2981000d03011840b90b40180c004846007c541d603410004940d0302c10003c0003c2001510f081c8007580c0c0c1d541500e601c4401c10381c540340003d40c218100e0003034451b101160003110803110380d074160b1b0800550000355040c4920070000c02c02d0b0f024442c07020844120542c004014014014103408001c0c40d00c0250141 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 322479658 1250 322478408 322478411
    0x30c07092906030c130e06010306050405010b07120221092809020703120c0e0a05060f1c1d06011802040e04031b02030d110f03030403051b03070605070914040e0304090e01 75
    0x1c082c2550102c107000007001080201b001d2814000c00040988980e90310192007141032900500090103407500f00c038006607000c8004d420101d41124141e050964a03030140070032481102034190080002ca0003401c42441c00ca50b034880c1141d006214841940c0c0781c0488540041510509000e00c4461b54010400c047c0a410444194031801040105070364201020300001034203481a000d2030304042e15108050001181c0045c14603020525100c001d0181d0b5a03134035400d4604040c00039182c907103584207600952001181d20f406002031140e103596501c0a114940754050f012201c4107d82c0342c0c41c401e8405032030381a89441c410f615192002c40d082560650034400091280702c4000040e0303002c02c40641c40c2c1c240780e00c80e4100380d4508a04a4200100d5075000c004a800c00c00401000aa0120441c1c030906180e01d40b03504071514200700203180d80103d11008000c0c6140506116800d608a4000000ca44049e4050504001120107002c19280071100055075544144001d0105446c02d0300510b041d1841d2200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 322480908 1250 322479658 322479667
    0x91104210503121014041a060a0e0603090102040f0f051f17010905010602010605030312061002070b0c01061401020f101d0102070f0204050f100b0904020408030c07092906030c 77
    0x743c100401d5400e41d2500703011030601c00e08010030316082c1c210396030010003242d082104604850340c0744400046000c48910a110006135024890b0003110400072000002d8021a1280b80402100b8000d601601500008142400e00010441c44110f290016030ba8050003440d031200e10100c0008480c01c0001004044c04100c8055040943c1c2d001c03102030080144a002041c1d40d450540c0290231039046410680c041c1d0030400c0583d245c450000c001c00d812000948425410026000040b418003001ea00080140d881c0016410300c60801500300314152104428580e00c0c4401c9031006a0740c98040c24910100c50700000004540d0604a5018800042e9001d4901c6200c44072010460708a03801028100d600048010400065040c00c0c481d82d503101c1602003005010341080b134035810610119101d140c0c048240040c0008294665405032001080c3d40c40c12251107004800b032841c2c031070741d6030701030b1a0f0b047d49080c864151040680d01040480c02882d81001060444c20b0184103540e03000030702507611000c0800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 322482014 1106 322480908 322480927
    0x30c020a0209150109260c18150105130b030a050606070c090921080933090f0f0a030909021804050a1410091104210503 53
    0x2e83c261484040080101c49030603940d04483c41c41e8000d2600c035403921012a0240d0820f07901c0c40207070b0300c801200c4018001c0316440001e440390040340c0d42c030100701d1108100703100d002d80180c189086841c09207101440b040d01c1c210759208a004d460000104800e5220340d10449400a0044411510340041a140c11402950500400500554074480300c82000740000300c00500c51a994906001b20281d0035001d0004034003103413020518007a16103100030790740c0701c08418030041010919005440718a401515140c14009200425507c201c0b054690005002c0062088034400c0500138800c1a44605c0c0c01404200540d0100da10300d07005026440f416140b503100c01c88100f4090702c2c0000c5582d142202c144c09440d4205891100d4607650041c0189844090b52070340540e40e01010034484032014400c0703641c0ca881303a0701c80c00c08845000c0d070610307d040c211180800b0307007503001e2070480e4107005100 = true := by decide +kernel

theorem cover : BRFrame.Cov 322302158 322482014 := by
  have h0 := BRFrame.cov_init 322302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 322302158 ≤ n) (h2 : n < 322482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
