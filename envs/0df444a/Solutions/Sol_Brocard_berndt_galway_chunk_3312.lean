-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3312
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:17:41.639419+00:00
-- url     : https://prove2.me/submissions/a221adf0-64e0-449f-a0ce-6770a7dade94

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 595503597 ≤ n < 595683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 595504847 1250 595503597 595503607
    0xd052503200c061609120b0411090a09051209090711070306050a0605130501031707020a05040c050a0207090e0606062811010606020318190e040507090b09090d08090102 74
    0x3250003001d010b078020b50401404280c0741c102815148215030409200a00c203254005100b090720030820040d2142d07024008060710b4682e07041190f015054507140c10303131004403d07082185000054000000b51841507044601a40004100800c54000c0b5501c0c1c0340c0001000380014a403500c5240780301c417403048990641e000140ca07621030302c0c1560b104940a14000f503d9400c00c226904140901035501407601d03004004550660b0b451074461001d000002c3c8082c0c05c00300340e540c03d550701c0c40c034140b00400e0010410000d20900e0310700602250003203006c200145c020050001460f64080c003855180460200281601e0795030b55003000b0041c0c02903983c001c21000300e00c402451103580a030500504d950540c98407501c0c0c81640d0388040c250307a81e42c0c02031421900140181d059641c82c99501c12904603080310101440101d50030301503030200c0d1a40c00012254921001d000c240040824a2003c0e989101024080100100c4c00d01c09002d2083d0703005130440d880080302d0888584605482c03604a190100054038003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 595506097 1250 595504847 595504901
    0x1150509041e08130905060f060a140306010e030715030e0d02120304030309050f10061e0506070501090f06050402040b10050a030b1c051c0f0504030305030c070c09020d052503 77
    0xf03650381000d0075040d61b5200344246460180c440c80c2d002c50003225210310744211507034005d2142c0101c00c041500d941380403000c990345a01900701d44401180140071a00380a1707460100003449446400c0c21f00c04207251613506441c1ca803003c00c0000070003059070020720b50316004213100070041d0700c020070550800d551007440c03100103001800481403140d03403200200b401400f44400c141c11206182c0c00040400650b080c1d444207046061182000c591040b02c156071540c05500304540075040e01d00008009015403050101002000e91105001c0c03030003a2030410100c0c40d02c00a0000150305e4410302c07004121309025030498607120780c00c0341d042c4031405010060301000644078248001d4807004112140e800400b49103004840d503000030065482c5601d040c1c080f00c20307003a001602a100b940005002c00c280003001400010408003102c9400b94001d1a0003440c9035601c02460082d00019001101d50b4184408203096103903072000121881d11103403510020700b00c0424250020450040f54482c0c485410b0803c402c1c4c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 595507347 1250 595506097 595506127
    0x330e1f050603070c1104050108120309121c0b09010501050301120f0c08030714070b03060d050c13021c060f0b0c1011120106140403141c0201150509041e08 68
    0x10405a02c13891340c000385928010814442d0301e16001e00441c0740a00420102d0b00c00540c640c0a041400c121a40d41d0f141d0340d83c1f4a003044c510100d40440604002200c80d88048002c80300c030b25001400208000070b00004040040303645081c4036140c00120305100500100c48810100e5811500c142172800c002074060703450a03410039075580040800c0d00003040d4403007407190300c0a00020860503c03000e4410391f81028001050340c0000350501c1d01500040807050100801000003080c0724100918680d179400c0e000131094040d52200302200b81d550000f42142d40024054042c020945d032030045546506410300c01490816080740601d05141c0c030610000c2d031455012882020004205207111580e40c440b15481c0c04542001030b4420310800c01a807a280104a008030103940560341c2c010303112a00d07440c01840040c42c003200c6001e0540e0740d00030042200f13507050f01540702000d091580216071580076030318810040b0011040f81c02418503035071019849c0d034070100310402101c0540301d40c00c4503040036003154010b50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 595508597 1250 595507347 595507351
    0xf03050a090c0308040f050604080727051003141b01050f0405040519050705030c0306010c0204061701240335030906091218100e04330e1f050603 64
    0x71305131800150500c45803021002d1280a05030a85429182c517140a100a0f9554031a02c5a450446140142540d404100340501071069208400c00e000c1410440742c55180c982c002e00c4125204003007900d41068926001c9201c1ca8100c41a4003404100002c2030015910341d0b00c50501c004a1020030800410181e54034800d8900480a451090b100843c406e590141116809402181800414010000280d08060491b60300c81020b203402c12480310f861003c10003600d10ba4200f005101c145a4401c48484015480041c550120382c00300303c4c506001c07106c030022040050101070b03e00c504100400600d0038074550829201034011684c911660920304000340d0b142c200b540d60610540004081c440120020000c8201384601c1ca02180d14050048021113240d65840c00c4203402443c0f41012105414020100c5c2460004060300500134000314965032998210411000b0340d00003448203115144101441121094841028078180c0d03645a8112141c0346c840c03454500c82c045c00749950081081e49442010314 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 595509847 1250 595508597 595508603
    0x406080f010b18130311010b040912020d11071205160b0a08100f03060e1023011505030f0901020702040c030c0806040905030316020a0f23010c0f03050a090c03 70
    0x40e00302c0c0c2100030071103d030040d0109025005190342c240007900511180c4141d140c1d5140c2005241c1510070030f00303540544401c00701c0c0356210b8900107c900034014000d800c14186810317a800d440c282c03081e40c00292001c520305441c00259900c115800e1040e00c0b9000c003c4880c043c0200308076000e00081c200054450300c0e284c2c0005900d03010108441da0200c0c2c0007920907400030048001920018280b1803c602081000d00c80a001d5a4407502c22810401081c0842e03141100459418041220750644111003600607054a20340b0841c10000000d14003180c10f00b1146c1904160f032100d265845651030701c02c5404000d0202082558200503450041e030361440346081c520030315103000c100d40041000290120000624260295040c49160000104084200c0e0741c027200081d00d0303c198101c0280f01701d244c41c00a00d0001c1014502184d80418030984003a214502181001124551844810314900b82d0302000c0400000c2030743c0030942c40581c0e009420040c0c0c4000c090314001911205620f4009210980b0391041d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 595511097 1250 595509847 595509851
    0x40905030418020405090c1b0601060518030708060604050711030c061005060711100203090a0e01030c0605120103060c0c0803040b15030f060c071e0602180108240406080f01 76
    0x410112402c2264582244000c9004505052428000c1807031180d00510301c0380030302800035180075240b10144007c440c403001002150500d40c2c540c0c001802d1940400303007058a0a0ba8a083d581c1d96240000d6640c0a039440340024180f03a856007820300003e0040175244500748100c1600e40d40600e101080600103c002200052415040080c01101c0f110810f07002140900350030031000e0f01107a02c902561100c0302c020b5501a082c4801c80c14124118025090300301e51240c00310b0340000349080400b8015043c0c0303021384207110400e69904010381792032040710718400d90064680010804180250f214102c040c4442c200142036502c41d50f00c02c0410341c030860702125100004824400411090100c0446000c000e5000700680819180d485558032402003c2c3e000c046000901c8030304009055103c40c0c1d0b204180407104000250602e081c0c0042e4000b5180c2200d40103403032840724a10740c0305403109130141d0030304d89152900e02d020309030b030102480010101c584c01607140c15002842100403c11102d4008541c800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 595512347 1250 595511097 595511099
    0x21030903230901080405011e0207050105063304030b0c070c1e09050a091202061902040e0601030b040b060c010e0708030a051b011b1d040c081f050409050304 69
    0x10103018004800e02880c1110320700425800070107410412902c84060900702803840d40d40d1843e065007d02800301c420014180341c021000c40020a40c0c000c3c1c0700b440d10504c02803299545107002d0180c00c0400c50040540400410040342450b0700300007032021031483d000700342c030b01c0d00f502c0351140b41d9140c0307040c0e03030480302100300007800b0040c0443d00303240e1000780042045070048202400c8000190104c1402a02c060903912008103a2010240e03004c210110740c0150440545e071114000030751200c600b00c5010009107240702c20880c0c995034910884083c2c6406400d0900c46468140c0114024082d90401c16003207a80c483c040d0240765154006019410030403030020542d8120b1100081c185501f42d4003414580c0d10a000780380321142c11030107490040740c00c03188000101701c45c0d0180d280540307680704c09121000b2810050b259a81c0c2c0c03000b910303444608541c080d03180c40704000d428002110345191101c40001c01c0c500104454001d050301c0c003407050010005564062303445000180484958020407110341e840010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 595513597 1250 595512347 595512353
    0x204030501150e10050907030f0618051e040201053406021e0c03070303051b030a060f120f0b0703021b060a1b080106050706020714012007080412210309 67
    0x1405500001c90140c0d150740504d17080116440381400f400540c145502c41036800360074440b45c0d1240c6c0052146e10940b80d07000307103c41c450800802050796194803116051002051405001041c41d00960341039460501d0018590a541c40341034a000c1c00e09112202401c016020550800c01d841c0030307902500006a40b1581603503540c0807070b590100b182e044e0740c0e010302c021110100003000f41c4000d242c00d814082520303620506010103080040022134250f40340407060246510300e40d40510259412008100302c0591110b50801014030300b0700c0c0091a64003501d040d40c00103252045141d800c200030f42070150034508044101c01600ca075203c1540344960001042154a88460044220706d1101074000e00503070200740300042a4001c140225403c4c000001444c000304681541202c103103d800180910040700c0d0000003901130318aa015080d0b04040501240407111280422107081030b90106400d85800c0c0b0300b5400f407120303201010060703c43c0c1e800c601220f0f07034090444c1d00341190b4030b4055400252404d0286 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 595514847 1250 595513597 595513619
    0x3151103091006230f01051e040801111911030d02120a0f0b03030d0b01140c0105060117012909060a05040306050c07020a05040b040b031b0909280303020403050115 72
    0x190050400603000340044030202c440b07a1000c0c61100b03055039400c0041743c2c2080141d41034420404842d241c40301a0300801c13200940c0c00040e0094400340c41c02400290001c07410604140038030f60010a28002c6400100380f03c0e4014a000c0745030340030540550f41132013102c0c00c202040b60041c0800f2201008080204a0070030814411410f6040b80c0c0502008051020f002207076803030103540200790034540d49406c1102d0982c050701e1444045060400c4584e92612055a141d010b41b0080d6040f0b4040345c1c000202c6108000071a16a40c1130b2090741141540c03440020405c1150342c6805a071402c4540d00400c4140c030301c0d4641c803000780034400203500c0301695149949000300880748000c02e0b400b403502051040e540103030303501662581144c00888020507462740150015000300000c134440e80d8035104406500d40a4241580000340c0c1e40d004403076a44840c0d5a8034402a00c0741c00601c0420700242041ea51042c9403402d007402c0801940c042e2900606058480d90360074210b442d130b10440c3c02c05004400041026032a19 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 595516097 1250 595514847 595514849
    0x3150e07031203060e180705010c0312051302040f09200f0a030b010e150f100516030206150909060408070510050c07151a0f030c031005090d0804050703151103091006 73
    0x400c41112040c0c580e1030542c0e11035000d070023030a041011040907142410721542d01e2410402c880c0c07074104860b00300b0360000c805a800301c0078201c0c090380c00c003101d20303000030480e20602d806283c01c4001d41004000d01000c65404007410300e00d5550086400425007502c0c1c4400c8100006140706009525095042441002008030014100404150109204200d42d120a006219080019110b6201041e4500c4d01503940d401002d0601020700c051003464003d00d68001040f5008511001204030240241804d2204038181181d200100394402030200b00042e41c2c0720020510b072402074094840c4c1c030a1a48054064071703020fa402207e40b80e0049012018400c0719003058540c02c06d0507c0030042c41d400101c0003180002c0c111710840c424001003000d0b22503500d05010b03400c0050401401d8901d000441004003000b0107082d10b806034070344200c0c0d0740c28001a0044e40420300580d041402840301c1407859842d400d181404000306c034199611000c1c224445021070025501511005011f03040002005034854111415 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 595517347 1250 595516097 595516111
    0xa0e06060306010b0a05280306050a09060806041e02030a050f1e0c01030b0f0411030f09030a05070f05010b0d0341070f0206030f100503060103150e07031203060e 71
    0x440c1c00108036290404049442030882404c046e030310740c070f030b10b080110080251101c1d0b4010082d9043c000120558154807c006a400c00c1b40c00526541e2581400c008031003580c011882c60768442c001060100f00b14100165071035407030030860402c444d41c1d40d010a0520b000c4010444155019035140744d0010400c2c8000c8641100c8011000700314840c017134140e603592a03455010782c1450b40d5411240c1c3e07d0340314401801501c09001d0424042030084c14812201a0b03c02c030f444880649400010824800010088a2201190b683c0f007500b001d190351140c0922044e0341340101c4541d9a20801c107445601c0328415420200c1c003d842d041c1c4050b040b0340300c46081d803d0300040c054084064540300c0700c00d0707140880204101c14003004226110110b61500c0c044131000d07140c000c0e51055001c070410064030f103141561845550000a00c1c0e003041e9986003499500d06080c040204004c1c00306c0b050502c154100c0d840f0001e03100c207580484117803990700e4a54020320100c84012200003030321200d06002c4002415440c0b504440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 595518597 1250 595517347 595517353
    0x10602010213050913080a230a0206011a090406060c111002070b0a090b031512010b060307030b13050903130e04080a03110c010e0d0e0609010806040e070305060a0e060603 75
    0x1920140840c2c82c0388103000c0c0c240b089111201242c3c5858801c580c0041c0c55501400c0f05a0b01c2502030405059459402d400c10511030000300600c142c0781d414019500708801e03d0300240866428090b44089001582e40c001d01381c1c40050240300131980d21070254400900007a100d40b030707105e443e5042a0034003070401c21407039006000c06480180380c0c50740020032204403a00c050007151502d1b20b4003011039890a665120600b41000407007400310800c1d07086410402004c003118040c0141810054450a80310502c1d026a0b00010500005031214000d07009032100d070500420404210300396800103000c4950998480d5059400031824031100401d418030707440034121404a554180c50f041e41d448600b4444e403040d1408164403103004002c1c0e403491074151010000352000901480c035415049a03a950701501d140f0001490440c0441440d04001045170700c5428180d440020503604c0800f480050031140034081c01d2889444400008608180541801004c03c21001315880343c0010781c003031a041001d0241071003a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 595519847 1250 595518597 595518607
    0x2c030f190213051303030e010e0f07060f02070e0a020304080c06100623090d05011808130b0c0a110a15081f05010815030a0b070503090709020a050906030901200a0201050106020102 79
    0x4c4000455140964180742c0842e10031441c4040354094081a8480400c911a250115442c05c202141c1c02c01940d090b6075602c44800710f8900101c0e6901028400c60160360488000b14070031452a0300195801405890354515001d040300c13106142400031a651107003e500400706201c1e950344450398881007440044910805000409136034410f11410485500c510061015001004020b4004046a4100c00c8224455030454200044290700c260907811000d1104140460344002d084181c1e07000c503000c88001c041d0305c3e41e10b5441400510300050225449210725000141c402094003c2314800740155642c16101e082140e14008158000084220b400c40200c0c010701c406d1743d01455840c0d108181d02c6402a41e40030000219041c000002c0b40985050004010007102c190810019402005c0280460700c030b0701e544409900c128001d00200100081c0c00f0172094034207240c81c1c0c0c0035541001d00b44000240c450f905407552129264003651641d0000c1000c100180b54580a02c070301d600410090000354904 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 595521097 1250 595519847 595519861
    0x2060606131412010c0504031a01140f01140418060b041a0f09090f071b0213020a030b03060a0c090609061e0516060501080c012c030f19021305 63
    0x356082c0110380c00d242032404825043e0751500c40501c2590b1402c1d00800480800a07001401a84a400190782c0490210a81901c2000e02c0001034129a0300003860405205443c0420400c40703980c8030f1460411486140000303502070000c0c0103000620110654248c3e5108050540b01550100d510101d03a0300c005000402060200703811404041e0102c88a555480c00702c003d00e040940513100070217400c00864420400681c210818942c05103607580c580c00c5c1202d140b407119801494141130000c3d042311035070352100d604000503000341468018a04011510055810100323181c0b0710100d03500b0600a40360515a0710302c0340c1108003040540030f41d15212040a0070880090000310703400242031041e41501545040240c4940107030750440c45064201c9000020074180480507040038001c5514500425400414035170151781c21031444074404e841b0700303107030348510142101704401814280c2d0540252013103803420403003e01000950f09a500c412901d00d1940380103102503460389649035003085140c80103004ca1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 595522347 1250 595521097 595521127
    0x612150a0605030c16080f040801050601121506210e0a0b0f1b0a0507051e010612020f040e0a0503210a0629040f081e011506030c090506030108060702060606 69
    0x30020380c5c0c08040c641500d0740f40c0400c2520545500e80a0880040b40c00b040182040d00805c2c0160000d0761400c90391111100300c10304850600481ea101040e07911000c014907805905074400c000070b000c1c0b54841c41b5625540c44410381d101004243c03002d03008550b400d0204a1102401500030101c40c10318066842c0c000300c403240207492031586911500300850781d801400d1003030044030711440c1e0100035140c8150401000c102460381803c4004a41c0d4280040499914181a030400cdc403181c00070946c0a0140c0301800307000040c010741d400b5500500850106001281d0204010000541e010507401c0c2c00400c8070042d07640040001e494207016034104141042000b03403504c4080f00c0d8098004480c0e086035035040e8820014401c0740d008060729903003000000386142e00824188140907010907510645000504254201d820141074450341034180310040c807042e0320903808a080d80d4502d00300a04040c1e162400166180c000f42c0c0b040203294083c0c0c00b0808416414042c0c0c1d5000b51094505905040c150090048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 595523597 1250 595522347 595522357
    0x30a030c021c021e060724110f09010e04060306090b041103070e04062c01020703120603031403040c0306090b060f0a0503120a03020712030c1b0209010302010e0612150a0605030c 78
    0x8030451070107070885010780c4d64100b15a40c080d44020750415010806002100c40550300c00010b004514040422301c0f201110360807104e008000009032440c0140150040d01d040002031003064010303503661800720000d0301910a228465014040c1d100c1a0300c1d0515000a50000521445000e5080008108180a800301c082501329030310607004034100100c041003048aa0205140e40e607446982480b120f80c01e00d06600501c441c030b0003aa200300308010034203160020b9540d01d100050010b1940c0e010030b400e00100401840e0000c2c07048035004501952a2101020359101c5082075860105071000d01c011440c1400300300512803000e645042e500c0d89030400080c0c030b0f03008443c514001c0f00e07000107845a1030b0344a941110b6034140d1010f48207030000070402000300140840c280d110085882c8030080000322041040c071256850f0700030f0000219a00310380c01169011000c0c0c14094220005000e690b000710a03900070140b01d1500034481c0511034655404109000e600765010b40306010080092149966100781120 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 595524847 1250 595523597 595523629
    0xa150f0c02060d151703131a0712050910031e0203100f080d03060807150c06091a0403020105160507110f0d0c090b0a080c0f01030605030a030c021c02 66
    0x1840031440303400031540354401c107070748045250300c3d00022003031080081c0070f0402522062648031000030005400d050b034901c182821403001c4120060200101c041038607103000e80c40c3c00c0700d450318149211a80c4081060f2103805006002c50800300311201d16007009540500c0440d410303c0c5c10300485000480d07079038148055814403400b15400200188202c1404692040181007848841566950791180252034580c55520348002908007140020509000545038040d5404010200150303070724ae60041d1002000c1407803c854080d140c0d09080042000092900c1c001440324221410303030b103807500e002400c542c00200340a5000c44241d00c2e08403400d42c4081625503542e403002960302000b1621001414502c004070b8080d611040c007801c0c1404100340c80400340b0445600c0c680078003000c04240c08000c0d0b40d1000d4004c121071584041140c6000c4e00e03280401c02c0d1085c506041c001100c03516000030030700748481d00c4429004961a40034031005c41c00e00c0c0105e1716900c81c0070010045060801c3e80007462103080c1d200f44ea = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 595526097 1250 595524847 595524857
    0x21c05040f020d060605060403060e100b0603070c110603090d020105010e1506090f030109080a081003021513050301381c05240f180c04021803030f090a150f 69
    0x3c402080081d078001409010300030410350701c0325560b14001d0081d01500494100c5d034060300c15840c806e40030a004005010400070b151324116501c541d0b0496502400c0841070342c0846020f03004015603100c00e130080d03000300d140750003601030302d0200714002e4203543e01a408106464610010040ca0f56001c00c1072560701003048070051341d00c10b1072070002030202428440c80740e45546807102010401c29194001c02c00c0804544841c2480d541d0244280c280a03803911001e900908c5d01312002e40c0c2c0118030303070040c10203003542c5071001e5100e82c03203d0220307003140c11071180740240d4074440b1199044088400d2240e8072201181d0380411400c00d551022558191000d02c1071819510154144c41c20002c0c01e01080d806404000440c000c2c6a50140308401c41034400e58011000d8041c403400f0517074014800d0080a400701c0c4000041050340c0c0d411043c40000d41c8151024044240707100c0c071840135682d0034401040c1e02c0c1c04010301951104d14400800c08207110550182250301e40c0c00351103601040e04891052084902805c3c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 595527347 1250 595526097 595526119
    0xe060417010b040c1e0e0310021b10020d1512021c06140a051f14010e030703050715020304060806011b0812011715150303070b0901021c05040f02 64
    0x440780508002200305503c9402c0c0350140398569030240e800d0082410f03103091782944c2c07903440e44165002141c4045040d01a007202ea80e68007021429001400c1b01c1e0404080d4180c91656203413003034100005641c04514103600006c80324000c0c00c4c540940039000011a81c0c0c0c0110074600520046019a6100c0090249400800b010043c200e05200740810a0300b040d401d020080c0c41c80c031050282001100c02034101c61900b00411102e02c2c00040c0d0104c079407a8403620030200360a247d10300240000360519141002140450300c2d0658406000141c011403040b03009061590500c00c50700c5074042c14064040840d0b109100801c0216403000320250401402e00f460b460080b500310f20f02039140d0351001d000d00700d01400100412a5650b0140710b41c101c403d03240c90281103000300000c19440d404c0c0b6040c0d51101002c205c0201d2003d101c2c0f54900354034130300c0040031240341003040e0b0356690308802c2c1126013805595000c100a08001c941d0307081c1040a0088510402c8a458165034007511081b0304c0b10080d0040d5480c0c06 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 595528597 1250 595527347 595527389
    0x15010e0102060f0c1e090108130b040212011b09080601050108090604030e0d060207030e04141315180c080709050727030b16030e0111030615091009150e0604 69
    0xc100c804840d044102070882c40702d03499244103164005103a25001900c610000ba1027020b080c0d004041d11980014801c050361100e130200000401040c194040c1550386000d2425001c2d001114084c41300341e60344a0310740c1c0a14081c106400d14205901ca0b50620503d034040082540700440c010394450360500340f01980d0480303c008103c4035620b03601c004000600c0003e120090680004c0d0902c8a4501214144240c0b103812103180305403801a600c04003141c224400280000d48001240d540b494203511000171442c941e100c10f295aa06103400c2510900c001c642c060041320000c0c4200d00140000c42c03003d010605286400900c00c06215150030100303001460480c40039400403240e54001e58200120112604005545041012045058002180c50154004035050040c0100600d800c6480030480c00c1d5a2264188101c3c1080701000a5015400300264007065403800c0140d48030654960b21b0b241400e0420007402d2180076040113640a0040c5085d41c0c2180b503684c0c0003100d050740c42108801e109241400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 595529847 1250 595528597 595528621
    0x1050910031107030917010903020304060e0301020f040311031e0309010c03020c1807030f270c150203030f0604050628090204090905010c090605030a09080c0607020615010e0102060f 80
    0x41c0c0052240790b00011440c00307241d0b00505100c2603070300103c038100c0c10f0a285034409080b40c804110040140c0c100b400104410f9003d41c0141c0d000c080d0140000d0302d09040c01d01030401c29817003070700211007001c8001c003d00c0940c02c04004030b0941002e04154002e4140000d89440c1d520700030360002c5410400101300c0c00040600c03d200040c1c0c1d800c4003410071050003010301d220b01e19440701103900200091a0084d802000042400340e1100c1e03540702800f01b00c1021138404240a002142541628070000d03144002588154013203100342c0200565014644901f031841481d07a1001b800342021f442103080ac4240130a03603a0b40000b410744004640e801c112400c80405c4411580d54955200280c0c00d8404a000907182c00b503134000895140c03091000f040940780100040e5040b42c0b01c0e004800000b0418800200039003082d0b40300c0d00c150350040e80014107111091030b5081c030b4000112080c0d0010f810800034032224a0045045441114090a0003582041010300003580c500c801050b452001c1e0400003c03500c1040c0034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 595531097 1250 595529847 595529861
    0x3040311010f0b0316060c06150b04060903020102121213020112020a0e0a080a03090e06030307020406120b2802072603190605091305250e0a02090105091003 69
    0x303a002840300365004003401e00144000c070382d0240640507140061502001c1c40c5800b03c2501c009840d0350311403d841340c41c1c0800820b40741140814418540002089214003200030b000100220781d203004611b400c1d41700090501c0c103d240c11001c00007083c03081506e0072900e40003c82d848012202902d07140841e0b400125040403048080103200c501c001800d031855507210204040403070054801c2c00b14107544040c3c455891500f06005000109500b00500c1440c481c41d120a8110000504403410000702d50009411104154448606d43c49400e590b60104038140f000213a01402078410707100d0f9504050203070703030b103100491a0b030140030383c0d0000380001040681400d07020022801c1c001005842d083c0702601c441944252958010880301005c041140804c1d4000e820948002030f003081d007180c807180d0391205410385000e001c0328940100c04800392030220746500000a40c080c00c1c070b00140c0500d0014044582503016040b41b00e0140104081c1074964bc02404444901030281c42600c030341d40c0118001c400425074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 595532347 1250 595531097 595531127
    0x6180203040f02120d0806030c010f08070e0402040902030711010603030e0105091503011d15030d0806040f1b12020405031510030501060303180e10180608160603060803120606030403 80
    0x1e005598071507800010710000b0380d00d17258455000544400f802c05548040400306075001400d0a840301a00790701c540b00140c1c000055003040f0040a40700800201030303801c6900103000701c960200c1008050340c1c0c00581200003940c6c8500030010b0600f592001465074080040170b90510000241c0700c646070b10740240500130803014401c160780381c1d6110440700d8800148a80365000b81020398002c101c200e40700740405111140001d00412400b8a548025a000e0030018030040e0702070754400b14101ca150b802e01500442054084081c20341403000100580760754940f081940042d4814401440305840009400841181043c000c04142d900c0d41902600c08040381c100500950820f4800000c240c1c00c05445282040709200c0d41411a480c0c0c01c401d1012141115201880d084010080000346038102e0040300d10740c011000030075a5521444458079114042e406019550b880d0003040116541c503100c0c03003020b0020400514900f2450b80741c0b10b0060301c80501400e09c5000700001190400d0700030032410300c00c604 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 595533597 1250 595532347 595532359
    0x1003020d11010206010b0435010e010b0109080109081c09021c2d060e010e070b0c011103060109150318080d050606090d0803450106180203040f02 64
    0x1261410060404907a000a0b000d071103080004030b0048000000c0d40c5c144e03404c000da2520360144031110394100b6000000645054100c06800d0311042c1020301400000d45540400071801c0400d103000113040080661040da483d902d0b00f100f00b4006600038041303c1c46034103da01425100e0030742c820700000a081041000350f10070204130075005544420300076604500c2c020000d18015408007140d01c20b0756449200c01501d00c075624100000010010360000342000e070900000910b83c800d40d202c5c02c0c40d2403040d8000f202094800305400040d49002d01800b042040350381504ca046003450400608920702c107000e403015055030120310f445c50030b1280c0c0c416121406268002c080c600c3c2c09050100c9554400484090785609060020300a03040800403901c181c2d03400340003541ca940300f40d101d01815800240600e00800c003041c240d1004442c5403010072921000c01e000040c4000441c04805100203802c03600382d11243d042c460f040002030060540500c01b10054600965031b5034482c6864026000e0000703000b0b44c800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 595534847 1250 595533597 595533619
    0x60c06100602010509150423010c090504050a0b031e0f10021921091407030b0601021612030f02100c0201020c0d03090f0f080c1f0c0507020a030308100302 68
    0xc08080c1510304480254000304803c1d1201454a5140d00d088a000500a054940441c3c0080c0311710300310f4070701090400c0046007801308c08103145080d5010f0040032000036002c00001d000b01d01e060321400d034110071802d90412503841138002003038580204d240d040f400e658a03102c002c5908442445140d4a810512061b60b10309895020000003e402001a40d41482a000c000c109040d0040e04035010151402c210004203c40d400150005000e6000f03049440481c0100c0b442044030007000048061441510071000a29059000a05d0b020707850038011008e8408541c20081550b00500c8c640c502500751411a02d81400c01e00305030301d800e1072002c441d00780740c3c6481e03406294242c0c194080e0403c40c031918180c4074205e080b04011410f8889030312000d081c00102905010000704081003480c1190b201e2903c603410864500100d80c200100c03501402201103070368420030b01008041c45400e04203882418039a00f000000d80114148104c1c90000078244000d800200300c03000c0d0440704017401944d0042c16a4840 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 595536097 1250 595534847 595534861
    0x50d050a1212050a0533130917031b07031215031e03080901020f0315190b04030501060f0b07060e071703070c0b0c0d0e010c0803040503090306060105210402060c06 72
    0x1400101e504d403041c4846503102c00d20000b02c190140e151b43c142003099030003400a002c20850f031041c0e094440c00f16103540c1c4001c60000fa00640300d0b813880c0c8000302161601c034030304180d04c41280e00c0f1041640380704c21020404400001e4000903580e03d810300c029800100070008040c4c41a00032803941000e04001c410405142420000c214010302a5120765140c080e15203d418242d803d1b8000c0101c00101480c0500000d810341c01d0707240c0c10501141c0000c003000801515160003445050680c0c104c1c801d024070000b0103200717215007402040001c21036010316110384c5107444000d2903d4050355200502107030f15403050960503c0c0c02c214140c060807845990b0900300c0c04007484070740d895000d0302c0121203110700c005000442980580990300480804000781000b101104d80441d2141c4403140e41c1414418680918004642d580000c2d41c465031150000b19075522404040520701540200b0841c10070600b0012f8201c9409807600d4100300002d805400340c070030b8503903200148c5540501c400d400440c1c80b4540801c018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 595537347 1250 595536097 595536101
    0x8041a010902031b031303120914030c07050a0303080718030c080a02090105091e071211091801210f02030d0e09010605040f0e2703090a050d050a1212050a 68
    0x703112070103101604c04105144a40362400219814400f0302d0031000c100c000700303001c0c0e150041c6062422100086e400c04030b540c4c407488524003407a0200c03154070102d48000301130300c100304502c05081f08581e0504800d1556900401500005101c0420003007408415129002205c4805c07001d55401740f8500c40300d035150031803169600002d5800380c5c4214201000081c50f400c20002d854001c100d504041c071422003199882e071041c2c02020b4034035010030100200b004c1204007244035040d1344a00348600c080c2e9401c0d10300b040202d1028100401152074041900401c805180690009911449824090f0307403540075042600410000700c10280d018007540e043e00c004142d114030010561002149d203250710380d0321030300304803001c0c0140c1c00750850484074000140700c40780040c201c055002c6101d40c0085101403c7c00c08030301d07480b03e440042c818658008075003c1e80c03034a440a8400081c0000b6200c4084c1c0340d186031161580d03106200c401500c4074440c04403c2801c14811005103c030407032860030520541c10403c00d6a80 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 595538597 1250 595537347 595537351
    0x180212030a09090b0d080702030708070303080a050f06310203040606081917070c080313060207140f090a020915040303091203050703030b0310111305120d08041a01090203 75
    0x102103180c08107401c1101e01c0303006030f0b40b03001800b00103500c1030a0780c4541c0e43d1f602104c0140e17410f100b40440050b00c44030404c0140d000e1480303a03803000c015040c01d000990554501400590b40a02d0b04400c0061075210a404d00c01b0f921006500d0300038140c0003d1510710b28a807600c0308810701900000410040c44850f400c034900b1994884200d0b50003070700345101203250345005c00009144983c2c2259180c0c0072400d50001c4c0003d2802030413005030540e5140301d020701e981c4c85035240401407a1411402c102d01601405044000c0c111602c076041d01c00003034400103c144140040452007810f40b10046514444a54151a846070002c0c01c4083c00c0c10f80b0700ca0644098105101c1100050070070400410600718039030f65401c0065041d11810f0401d55655003e27000303450104819901849070012140664009010b07481d8126964080d030f07644d403031043c03029208507090f41e000580202e900740d08018864100080407259100c3d180b41c0803c0d0391f2621300e0544010440c10859080107201280042510081e0340d00642c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 595539847 1250 595538597 595538617
    0xa05040f022e05090f06070302120d02090406060c02030f061605030c09060a11010507020d20010b03030d0605041b09170a020301150e06011119030c08030f100b0304110418021203 78
    0x345c500d29180c10014035108543c2c0041c0146c005c4002481d0100410300600b01d00241850058100241b00d408034044802039403100c2e000a03044411039095007414003840c005404460050109481e02d1120214107030b20000c0d50404205000000441c05110300d001c0c1c5c4d0f00b0040040503903580d01d4040000030400d85250300004059460f10300824082800080e007075030003914984a03c050043e41c14048148084658402c180701d540307604c5100381650f82071005103128000c0c1107001a1090429040c08201d50300700e235611400708032007160f407510f4603000903d043c1100d40012171001a903407040d0030a401c2c60143c0400940560901d04408005504290110186d640c5002c10b1003099503008011503480b1050032880b10941c025604030a0b003d034014a140000900a00b410002c40749640c0d2420b40d1a4000c032400d2002d07201c150288074000031100c42007001010342c03019007811130030603444400c01c2070045010144165550517414015000c082d0165601e250000e25140f02e10495120f0140c503503108034540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 595541097 1250 595539847 595539859
    0x1b0a0209070915051b01052401020f060f3c0a0b010c060c0207030b01090c091a0d050711060702010501080c01031e0f1104090e060a05040f022e0509 65
    0x194410301c03880c0b510040710441100720703102000c00c40069540f40e010b800720801d1001c83d600b900b0b42d201c909000d0540112202035035680686443d002d840c900c202d404000714115000a00b2310305c42d400001500640014070541c46e05565210110b8600c0161600c444064141c0d4034001400d000407414034905a0407652888400c04130350321901102c08030340c424503015000c03a024004000105038241d00c2009a4000c60040b1595a522529500030303408099024000d519100c021000c8070561183e6280c00074000071500c1c0701e4101100b610b40009001e20000c00e00f21303a94a40000d42158483c29802d0365890f01071043d0380d650304202d40000d000c0c16003405006094410740c40795407880d5109200d044001e003010448600c451070000350003c0503222a2005c034220544a40b240416902c407040200b0080140c1840022001d2003040c3c000e0800300000c0494912520300700400010031003850782d010301c07140e0441d17000c40310900802c6880700841602c0c8610341d801980194500815811400071301c0407400481e00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 595542347 1250 595541097 595541101
    0x40506090405031b1011090f030c0904081e0304060f06081f1104030606170d230705103b0c100302090d0f060b0904030503070e0102031b0a0209 63
    0x14405440c5003503030010300580c403c00099551150450682c00e109610a003614512403400701824140d82040c0290365140c000010454000d01e0145c400600402d401c1d0081c00c012101000003e0010b00024405880e0700c1d000203107102141c045450301c035410b0601080d000d840e03040508100703004001416040140a01d000c0c004a013141000980340030401c00450000320b50310b080122100900305100c0320300000e402c24040070002130720303c2c010b4501610580340003198612400085901d4100c04550003001c3c000e032414400c800c040070b81d040484900d541040541d940f1124944945094250b000c070380c00c058500340f48001401d0a40c0200c0c404004602800341e540c00c071030319484015020424140300307142d003e411640e08c031f0708240c80c07400300741d0200f03040c01400c0504030b40214414801c18401121a416440100010010580b0541030841415201c5900c0741c6030a5601800501c000340c000344c10700000102c0ea0100d80c0c420000c80d4040c880d01080e000740c0303a28070900555078900c1020308038030510132800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 595543597 1250 595542347 595542349
    0x10020d14070e06160f0c090203160c0c0e06060702130f0b041109010f0224010609060e0112050a0f1b030b0d03080c2a07081e0714120a0f02040506 64
    0xc0d10228954005042c01c1c541211800c12460b49414240b045500c4242683d6240c0410407682c0b84a00525420501527503038900000400410030007a515802032200f80c6004502107440d2044900035181510b03941c16654849000141e40f41c000d1030802580304154070300610f40b000039a002448440c1c0058000d1001d001107a081005a4012490112104400b4030020340c056100b03007201501d00b00c29005603854550420710403600c9200c0c060700310490685503c0100b042d15804101030b001004240f406929103503a040c0000e0404400560740d030503150301c032000b2815924490744842000ca4283c4820410710420b8055180c1e0320460044030b902007032404c41000440c1c2014a401c40003070341c1c15a202c0a41740d690851007480394002e00d845030344800c514452801c2180c01c42d0071800f02c4d00a25401400c6081ca001040c0345040520b410716401452102007401c007020000601d40c0c1035421103540300081500540115104d95500b88000c41c4c5485000c0000742804010544404c00c5070007a6403c2c131256580c20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 595544847 1250 595543597 595543607
    0xc0306031103240604091e1a040b04061508070306091101080115031802100c0209100b09060c160b031e0f01030305030405010e0f03040e0f06030307120210020d1407 72
    0x1c0072000000301000240d01c0c814010016640813000610004015074281c8401c000c3c902013110901d1418440600340c4240403040044035a404007490580c00c091815940c1c5801c10a400b40000380070340d444000081d0610200b08071503026020f0b581c12118803650360b06001c0050650024295000140360101440e254421126a41603030342c40c1d54030300c10101c214042200100f181d00040d8015682d8030000d200180d0380d00100005605465442e01d440b140c0f9801001a000009421290801003400c402c1140030204801d0b9810000212009904c0d5949902d0090426140321000c4ca01c0070307102040851141840000783d4020540203113500c0340480c10b00d2114940300030130f4400c1d50f4081c004600410000b41b2034002568007074420800455400d1640c002c080c5480d81c842c5507603110713030404039040c000d40550040c9250300c40035044c802c1c081800d1060100c1d49a108145002d800c00300603026030703282e00b4004c000140c88185001c00c1150f4071110580704a001f02903840c01c00352840c881c030b0b010414044c415 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 595546097 1250 595544847 595544863
    0x3050a0c020a17160b0105090901090209060103110d090302011509202514010c020a170c1c0f09080109170318010203010b030708070c0506280c0306031103 68
    0x507001468000881d4035940d011800b07920700e01c01d068100304402c101e0002841c41076091039104183c10b54641d41000104100140001e2040010368541608500541d841344130007504000203090001d08076441c0c50b5107422501c00c40752144ca00e541010703410303006c2590550228007613001e01c02950f5800c03038980c2040d200b500c16142c0d00c0c81880500b07040300b00030654204018080d5400c154020615804401d07040f16000c1c081207029a20350002e450b655252200a0140e6001d0380410320251038603035480e50354a240402c800f452403035403d41c0400d10706c0408800f00401e244480011880048014000070300070104450a4410000034180b52400560603005020700c01c500e42d80501c00030103800e03041040c41026003005000d0807003046180c040c440c04003030a00c0114080e01c00d55080694030318200034068a00c0d00085d00741d00c1000415412400850000304031960400d072a41a443c0240b8601124404a141c2c4540c2c0d042c0c00d42e152030740c14940c03560558080d8003101d100766407000010400d00c2c20907480d0100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 595547347 1250 595546097 595546121
    0x3040506010f0b0d021305040c080901150f03230303091b122e02120a06050306010305030d3803010c0219020409050a05011103010e0c0f0a0e010903020603070f03050a 73
    0x2052107000e0742904c0301e40180500d2909148a0600c40b59224000b4050356a01103180b00420ba24505119001400380100701658610010400200e032a0aa904ea26181d99110242602100e010003e20144a00707171440040341444080300d4490034100031540d19042c40307094981003060b803031204c038985040052500c42c01c402210081c0c08000d443d0300301da01070030550b1003031401407100e250800302040c141440903001c2002e151444d10460302c0c00c038208a040b11b007142c21071031180e408200100b00240002084421410110f080031a0401000500907aa000c030702e0880f001c1d10100f112030040e0402000100c071205403048000f40400b03400c04500f81d840d496505441d400c1d500061a1010141c10309400906c40f00e481002102d000748c1c41615030398211040c4030011003501c1c00002c0100110031094542c147c128011207111454484072800000701d0348100051a41030246500d50f00c2c030300d43e000b18200c500170354000d00016a0f074600f103d4010900710308000c095021a290070007080e0810a540325820308401303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 595548597 1250 595547347 595547369
    0x1f0806040b01050d0311100b1201020f0304080d0b101110050f130305120c07020312040e01171501062a0203070302061c1503110d020d0b0c040902030c03040506010f 72
    0x100300414000c4804c644032007941031111404004044001c1044031050f008031800700020480821010404140c40e00703200105180e0040c44604646080202120381150b4040c2000d0364840305d4800000c06040c69a848030b920590200c50182050b401c01c009403104030340d100a039208480600c02d060219001503840524034002540054150810041d5100035503019003004d0382032544140180c4440300d002c460382850101c001c52420300318201042140071581595050904040c2030580c050b58075001403050b0115120f0800d1841010351041c0074000710301400c8501d010140da180c450241c00f04645c1c0101e1042d00c8010303441600d80800c03110a0780e1a16500030f015000f400d185400308000e40c2c00664204416481c1d4140701320f000d031650301c51f0341d4840c0c03080c070030218105d4a0340c00c100403100d8520300b0180c02403861841d800c3c0141d0782c4401d02d8002503407001c03c000250300c1c0c0804e80e004030b0281c2d40016205510000c288042e0b490b204025500c03e601c10400c45460ba80c88801c8034074030440c01c0c404c03024524 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 595549847 1250 595548597 595548599
    0x1305060402060f0c030d0603030f0206042d0f05010902010810050a0e07030216030e04050f010b070336180e0604030e030a1502070c14010504031103151f0806040b01 72
    0x21030860024400054043c1101c1e04140311000d0300d50456101c105110a401d9480c5400c10030950055140012aa45400601050b1519403120805c0035000e210881c1c41c5d01d90084000c0708042c84054000c8400e400001301100001d03146052802401c4d000d034164007040b144400030b2043c841e080c9400d000c2e0b845c060200101d5a15000b800104110301070481c400341a000e00c10a04400c1b02400500740c400d009554010340d01d0568000d0104685000d44442014007040005005000300c031030496215507030500c2d00303021001242e00d0741100080402e0661211480e0206540303e4848075800b000151400b1785980c1482d001d040c0381e0320046540c60030b882100c5411040c0001c001c80e0144014610004c0c001d01911a030101d541daa00e80e10070007030b1140502c003560110b000000e00c5100c1d04100043d1501c640c444c0c28106021001806a014611006040c060603036071700c92940c0c5080c028040381c0201d003e0200c00d51b043c2903264101e41800b000e400244000914000109240009405405907070000386030001a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 595551097 1250 595549847 595549849
    0x1b0f0b072c0915030d0903120518130e071502100207021804060605040f05180703020f1003150b0a1103030402090c0c0a0212061e0610050c0708070801050703051305060402 75
    0x900c42c020400312281807039241c1081140c43c00e00101c0702100050b52400403241c1507180c4180e8200303c05680e40f0400c07005001090556040403030320b0355055822104008c0010744a001400a04111200c1004074001d040b00001c0340c15100ba003000b1402c0c926004d0f5402e48030342000e0081240501d220182d031000310401c0c5000c50b800444e241c607070414060500421059204c00104041d9180d000b1080c815990306e004101e190201d22000e400c6aa003007401410610b480c54002074040c404103c1030500c00d100c01d07101000c03481d0103980001445056601c0c0c1d50585599001c000d400e0b41c0000802001040140300f0618103241c000c01281d10440c0d0082c2400301c1522449240300503a0080282401944919001080076944035400018181000c0006000c20314005040c50340d160410024110341d21140301c14071080e6940da401c15185020307245005500c40d445400700070325121190703004e0b10040c040c1d0038010510403c103402c9144035507a140c07028061501c0d080300c160b074252109840584150050800300e401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 595552347 1250 595551097 595551109
    0x150b070c0b03070807030b180402010f02010b151e19141c060503010b0301020406122a09150c0809040b040f0f090b0106050703020d1b0f0b072c 63
    0x402802804822856a120818486607034003c1e1103100108021000f0010102e5050191903c0c1d81c505540e4030441c002917a0881c00010405030000707051050800ca0005042e100354411126060024050b002b902015155000d10307910410780003422114a00c080d8007040e00700c904440b647da07003001c848204440c41170800c5407000760f0300002515003241009182c06a04558903002c030041c0d0388c024005001391514040500316541c0106880c000e90050201300100d039048902d010054000780c0002c9a000310310305600f801c500d140c41d10460705044410f0500c403426404000d4070190342c0e40d41881c541c0c1450050064032006501da00082514100b0840048036040c950400c40d0b9400026201044421090305a04155000705074603c0665a6540002090050689815004012130305200340f038001182c070029164544880c4080070300c00f540030004840326070000403910340c5400070980090b0703107102d192025035103d040c0d81030b500240d10030b8007040c400b84c101d001e44d10510501c001d6060002c04a07500b4005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 595553597 1250 595552347 595552357
    0x21201360c081b0a21050307060e030a022b11010e011b0210090b0c07080d090804060e010207180e011b08100b030603030304080c0c03070608071101150b 67
    0x5080814284110002185120880d001e04800c2010f0240100310100c5859240700c0c981c0950b10641882c2004c014048030403510510714000400041c2044070242030041c0f6600c90100700134151490a801005810700120180c0001005039007900c0205405a40000c0341c00c0501184041c031400c0c6020071410240184035030780541c59a180081b4079105a000c00c0ea08480d558a422000c111103807e1906c891076044c422020310f00140e01d03081108148135110106100c00040c506147e80000041c58000e0160345020784001c0d80c0013040602c1602440e280881c141d810a00c9420081094261228019030000c10800107581ca5250880c0c0c01071084e2043c10045c0c15003504014440d543c900184050002100c00d8608031400c2c3d480d40a89800c1203c1c045040389119401905d0b40d50040c4240078030380d0b40100880b5002a0052001911424044005810704905c060540d903d4800d102c00080c401e0382007030b00b8510401c2c99448071b00f10303c501807044034240c40d0151004100d02c2d01d0b20b8070070310001034610301400f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 595554847 1250 595553597 595553681
    0x2d02060a05090a0506010b03060112140c07030903060207080904050a020313030e04090b160906020f0a080901091809060e030901020a0f1703040c0929012304060c021201 74
    0x10706102d88684070113041c441e0a80001d61f500c04000208207065030404080c003414060100c04001914405442414400028143d004040800503c41090600c180c20090146403c21011985c0309204c0c904595076500409413680038600f03000000c0c80800d09031003640c0c03280d041107100000c42c800a40e01142e905100542203648160f4035504d03800411700940070140302c6c1da01a0480c9140f02212600900404503030b078042030845d88a0142c00b10094030100c2d400412540c000350707417602c4509060040c0e49105882e0002118000b928040070130801c03454001000c602c1c0101c00c10070108103031840f6283c41c0e1291071401d501507880f5401d14030018220214174480307a80100e0414112800d04a18440b4541c0240d5050b181e1910f200800c0c8504034085c030840480708010301200c2d4607528003010324940140c4d03200100d418406080798100c422010300401107001030031320404660742c0340c6030074016110140c42c0c58264050302d148002c407000030605101354400f61420034a11107010855603501071600c43d4620f511 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 595556097 1250 595554847 595554853
    0xe01051c0f0303421712070809120102070209060a05011403150402030414060907030f031808030406030608070b03010b0301170a1b170d1d0f09072d02060a0509 70
    0x40c01d249080341201180e004103060b150348168071194a00380505100350030440e0300031142c0280d00b411960010700018030f42c294030301d003a07100c40443c10f142349103009804040390000292881c1c03c40080041d8010300c82030f4801c45400303000307441d01c1d024403201082c035014850105010040250305c42c900900034641c407500c40242d82581c0036500012074182e800641301201c191100c0d00c5103414800040c000c09621500141c01410740d01e1560b150f00314100c0726543d02900f8010880317a01c001070304045883d82c024016560032a42e4803951940010000d040f9442804c109026074100030982d81101d004030b034102c5584030021800c0d43d080c80c0b0100418444e500e806051403141d80210f80000362203515a0001e46511b0107104000ca1406024112440000c13808202c3c0780c009a00081321a03070081208210015900c0440300c440d000349003c02d109002c0d000020360300802d514200880385030304c841d0504c03001100c02200f80d480084440b007101400e248605000258101030002080800130341c1c01603601900d54412 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 595557347 1250 595556097 595556141
    0x6030f0f06060e090a02031302040207110d230705030a1e140703030e040506100e0609150901030606050f03071b0209040f12180b03040c030503040e01051c0f0303 71
    0x19201160960390102000c101070038110390f501d2030309401c0103a0000c2030003030070740ca5450010407008501c1704054000384a25400b00e4000709004d400c0e41c0078000004064040b480021041c286140c00c000824000c0c010a81c44444086803c41e000c00d01d54200c5002600801c10030341039540e100d001801c0503492090b1010781c1c0c4000c07000304407104100341200c0c0626024083c003905505000700007201035140c16000d507050100b80035180c0c6980c80800b6000c107042ca45070070000048400202217110305031500e83d0080107400101717034003040240107040102d0243c81c03c0280b50f0b51100144c4084c01030603c94407030310300f081c400510402d009805000c07042105629002c074158559001074200311050f10180c2c1d11485504400e01000a5023600c0003d03524141802812000282c151116000c3c0301d0050000b00c0e603020001c1307401c002886880001555008080da52034503140c414080360001c0c00d126a510401c9515016090883d81c0311146210a40101a601b03044165440c1900502900c0d008000d02c0c42c21100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 595558597 1250 595557347 595557371
    0xe040c0e06123c070f0e09060411070308010510020c100305070c080a05091905060f07140f160623070c030b010801090c1403030427140402030d020d0906030f 69
    0x10096424122940383c009900c048060a4030390707500141040e042c009001c20b036001c4103410040009080714103c0d10840c1d00c1d65a07401080140004850007029100003098040c1055005000b80d4143e4000340c540203101ca445050881c5d85203c01d609107900310310039030a0000500d120b43c0100d607001440d820a042041d40d19602c4070416030040e0034444c00100042400040b070300d403141d618803074000950320303031001517040c580014040e106d01030001d1403115002a00c04204801d4902044507041e0749025616441c0c00c1c000c10b152502c1070a1106046000e0f15140803440070b010b0140d91001e410301d021132003a03c40260b0800390b211b034841c1d1016564495414000000207561f07600c41c5000c0c2c0300000c0040748010721807400324071419240e0801e00b00c40041e00a082120b40300081910211040d074105c0400c3c0900151600d08a041c07900c02d40380e08941015a01450200e5000480d8010392080e002c0340d03203c1d40502c0c812a207840c1661502c1000868600b001c01441d4843e42000305500c0c540440002c0c0018041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 595559847 1250 595558597 595558651
    0x92c0f0115081f030b09010b12030913060308030a09030f0503100e091f0c09050f092a031302010e0f1e030f16140111060c1303050d0e040c0e0612 64
    0x1a0080301c00b140051700b084281d03a020300552505100036581c0c28000e0f1404103046840340503031125140100002004150801140d4028100075074000b01126a682412a076043c080c000c1d090301a00072481143d507843d801d900ca0f00459110b280e42030608000b103810101100b02c62100681030070460b2140c41c140320880d079440d04045900410a000c0081c282d242d032030001d4052999980440e01c200d004100107c0a500d640c001190b0040310b03103100441c0c0182402c070107140c604441c0d100181e624400b000700464400000800501d050003620ba00904030120400c118080b14005036150b008000d40840c00c1882410b100d200c040c1080090540d04210380311040b4600d000108200f200c03024a01100401c9031360500700443e03140c40000e181505400c0f50102070715680e0200506034101d1034200150074a600440d00e00e415005c1c41d444016134544803268140103180d8030074001e045104629056554a115002d40c1c490304207614040c010303d04003012800714900c80f540080802c21484104401502410821 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 595561097 1250 595559847 595559849
    0x3150e0d0201060321052a0a0f02011706100c0204020c01090605150d03020601060f051201060203030a05010801061805040206040302100804030f02071410092c0f0115081f 75
    0x90707800058298510f060012039202c0145a89000c46521608801d0b45a4003104540c007442221003034101103801e568800403483c403c4541445070b8080c0103045070400c200448400560360003646d5151103100010700c0c50b00c6144054540a910900200c403030001319028801c0c01e044140028001030030484401c1083e400e5a0b0789410840345260744008000c1d62004000d103c007011081070f01d080d00c0c0f041096501a64030340040c0600414001c80002a0250030322a208965052a2080101c10b007540e5400019650fa003007980e50040003400c0c0000030070f10140500c142c6c3c3c112042000c0703c0340c0d0f025200c03040000900f40540182e0304008104400301c056151007004401c800e641d40d440304402e2421b41001058805400500310854000400c10018280b180e41d85c450203140840301c2801c68420000240c41e8031000f0340c4139001c10001084018000d11900194148144d2000ea032600640e0b43d84103401032080702401040c40c803240c0c2c2038000811a11541c0d10b15485002c1e002e24034004201d80b02085010121 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 595562347 1250 595561097 595561123
    0xc03030c1716080906040f0b1f0b1c0c020705042a0512070c050d0e04140c030108011808030a0e1204091b0201140106081e01091b170103150e 62
    0x70b50411a05940000925880080034000e820706040580c0d6a42800c0b000c6000580380103983c101041e600070f10004c2c0c510140030209444100b9640d901c420380801d420071326801480e030748400003400b40c01280d40a8040c913060154003a2960604100811004261851958209001c1e100481c1080040301c1c00c0300700300400540300c10740ca401e25044484c4121200902280800c208130384420005000040c500d1001980303820300c0c983d17082032000807400030b28405181c10041a803403c207000580d40098000e505950b44400244034000a280113100074000c44000200b54040c200006140d503e52584021004001c13401950b02d500f86a82c030004082c2c116420030074407690f07160080b41580c0035000b03044086d02d082c0e000a010615003061149241d40051180f08140003440c0f00103071800c03420f0410180c4c151203003041c0e041156181e801003401004003540440325000805410b0301500c0c0170b91100d4a14807181d280041c00340c0c0c01e40d82c0c0e91112030280c110140f00d0645941e4170b645d1004091040040c1907103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 595563597 1250 595562347 595562371
    0x1407030c1d06061201060503040807081306140703081f05060403080d0b040c0c0201080601111204050301060e0f07031e020304032712020409020a1d09070e070c03030c17 74
    0x141035500703041c081c1c001d804288a00c004101d540c1208442400340c40c1103c43c2d0341460303a00c075500e60a0034119445124801051404001100340c1c854840645000540d00070b55184103800c0100e58000405120320000038010407000700009000e800680d071a00c001e1007109285501c4039a50f0340108113260009d40003101e0080300030903481c069045601c41d107a01220115018001d1942e48070001d0980d1201040c00390400c07240704002000359001d07070310015001e001c1c05c00b120100c20002c00c508583d074100340109842542444400203800c400030740108c0c0100051001d0400548070320030f06400901d003000082c11503240711000f03941010303034030f10296124a00071748540b109929040d1301d41c040c0c410248079018251840714010320030b0403001c580c5800f155905a40010f9516030500014540460b154441ca5848142d45241c0801c1b94012241d240508050400c4411007520740d06600c00c480e40c00c0320b0240004249550544c0030070300c80d030440303410209907003419800c94020002100b41103008542c4945900 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 595564847 1250 595563597 595563629
    0x329090d0201292e0906030e030c070605070606030b0c0901030c08041e020f060d090308090a050604022707030c0f1419020f0f0606040b0105090d1407030c 68
    0x25030203001e002c0400c2c095908650180d52810441c103c003100050ba482e0003a42c085180484425030941d004804454000c40814082109003004104103100e0140500090514903d41c0f542000082500c40c10140030028204190600700120b85a4000c610203850507501c90000101003181d1901d00d500482c1500c03c601c1c2c1e603145590024003030300d03411095141008410b804120124207114903c12021042002e074030114540740c0005849441d5100c2d9543d80288000f030362200c4441d0651016240324800e49925005070303103004005817104002c010140072508150002070040c82c003481400c400e129212980342140c2c10740a5524540201182d150006c82d554034001d07524190465020441c03051f203450f28070b28600010401c240c46000d44911000b1868150340403218180c028018926140e03440000c903a500701d05420040d40e80e21064035003900441c9003808115465100d0003c54007202c401a144e50120011607840b08600040540b204129000f81c0d0b8021000071000301d0040002e00e14a50104400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 595566097 1250 595564847 595564873
    0x307030b09061e1f0c0c0b030f0105061c0e0a03170405030403083601020105010f0b07060b04090f06050f0709060206060904110312030f060103060f060f0509210706020313032909 78
    0x10b01025000440c105509104000c52440041000303410f40d401079035803903141c1c0c5d0590307008040c1584de014120002170030319900c80c031405400548001054000d503200350a01440058800a5950640d00a4000d4204000a00101d41c200000704410101031703036030502040c0200880d0401801c8900c11014407580d1100f4164607681c24095180905502c991501c02c9a184c41524407443c46100c10081030991526691401607a81d5480b0400b45d81c0c111410f05803441c42c03450f1840c01003004031090160546402e020580c140c1c0301d20f40400507505517800428180c0c4a0108110360800c0c01001214503e4405044050369281481600884460400c0c590345034180380e070850782030282c02001c19040615120040000201c0415040308458290501501d00312100c40101d40345c3c0f05074001c20350040e28400304500c088215510f16420a0300e12010355581c6500c82008036200c0c4140c09201494031202e06c014408544046232000d40e50001803c40f50a050b845050980a00011954103145401c460286600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 595567347 1250 595566097 595566113
    0xf060e011b05090a05010e13060810110301120303020d1b17010e100315060801050c0901020613020a180f0c050405011106090d030b040b040f020307030b09061e1f0c 72
    0x9011207604165081c8070f03c03040851108070741481403034104a5550750868803512010300c4000910300c5482c0a0100b00d440d030884d180e40da48071641c5047c1241c5458458010f005200080c2c9060300c4402d21200441181a02c0c00c5000e5041401c11458065494080c00c03c1040c4034403001d00616030b00c1c0c44030482d00405480c0d2000d5000c0c141c1c8030340061103164041120503401c000081c030540381d000603440c07403000382c1002c240d000740143d800c03d01e025032819090006240011001d0000e2910980c2100d0540d518542c3c5100d1760361100c02c0080d08801440814484a01b1044014558a07480440002ca00c444800b08105136144140403c0208000013014065942e00109005503141c0c01e000500c40b074142a034400e0f81d03d1250b12424070825030b031001c1c60800380c0d640d90401c00b000000288140140358248980900030360040d81c43d400428642814101c00e810022511442050010b12680d402500e1000707005803680c0703504072141d10002c1c0140c5240d04140001c030101d10180d01d0b80c1e492008008626250311 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 595568597 1250 595567347 595567391
    0x7020c0a0b03100e131e0b01140d061a06030f0603010b100203030a201c0f18021e091306110306031b03031b0f010f02070c0905040f060e01 61
    0xc1c10001042080460b1000c5203e20003218000c0340354580640d105071005400090000f0003c2c40e0080000404111000310300307400c4065070044000443c180d0745c0700e0100c1c1c8000c11086140341c101403141c0388803010424640c40b03001d244c142d00d030280300c524003803000250f650380c0f0403914a0745ea05501400d102c9641824410242c0c820703420380e40b9080702da07461240a9980e0000030300c604490b03600c031481001075018400550400c1040b0001158440c8164490444000c1c10b02c185010124a80b102c08005009940200000115501da8000e4480d10980a0083d8184448007082c880e500b0302040074001e84461030464440c0502d40e025440041032868014180d5111508145d21281d0500c203002d016500880c07024008648040b00c82d0311480e012002c20300b18065040c02c48070342141c48841c1c005800c004070320702c1c151220301c2000300326002901c5501c42c01c03030240c03074070242100310000828860020207500058100e800340c0a154002039079a6245000d4070b1044100f25001e9450f00ca128025001804d9242 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 595569847 1250 595568597 595568609
    0x71212110a020a060b06030402060715020f0d050402040f0c0905040e0f06010825060503060f030106090507200706080f071b0309031101030b0603070507060e0d0c0215040308040513021207020c0a 85
    0x28a5400c003900001e54ad8021400c3c090001d654020056401c1400ca034100d07401e00580b01c000d103403900c090788840b000402e0f0455060303010364100301901245c03600e28030440c1c0035200143c54042086040c2400e0100906004482c8001c038820000003802007041080510700030888080141500703078036201c0054140441e400d65a005940700321003409400e802c070307007a694003090954982c0301e0502c6920000f40500510361200800901d8401444540f550000f00e0080300f24007000307100700c4500c01d5000d44c0e0395058184241d9000904140200c1c2e5a12002401c040c0c002200e03141940f824034503400a18142000248110041036240000f0810420850030b5207110400034282003080c4d038143c1c2c010171101d120042a0b00c0c01c0000004915080084607032014100540c01c0045074140e00c103150000d019800780c0941070340309540000c01c6061000c0351108035420780768030005107400c0c50f14100602101001e0b051507014015001d1221030450440003001620494040d40140700301c0d200c0c1c0d01480100311441d0445 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 595571097 1250 595569847 595569859
    0x120516060503182401050a0b030f07051e0c210c1002032d0601020c0910091505090a1407022103221511071212110a020a060b 55
    0x100061504182640ea001c08081c0800b000910040f800703070709041ca0800c1d0b003502e4010304801c1100c009030052030329050780d1084c0e40c019907035500c03851405030742d000840701141540c600f03c00003911a4814800390802981c41ca00000740321310000d00004140e04050940c07100d60340802d403c00c01c035004c201e0040300c03c0011025854030300a0000049500c031125802290326190300000410001449070041c901c0c103501111014003482c010400307146101c0380030307a800d44c018841d0608241482c50b107a40c0b00740c01110203400180905141131160400703410203840c2c15200817400000000c0720748841e13080520412980e200062a0210344a1000700050090142011503101d07842d02c1c0038082c03581000d01040c5210300182ca8407951501e0f1348005258848840c9000121010030390001c0003403026040c403958070159424401d0742d1400d007409900f40074400015000f060700b0381b01c1d100c651b4003446400031003003000400450741409200814034503034450b1003540c0040e03000720828401d1040d10b03c144690080d00b1924 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 595572347 1250 595571097 595571099
    0x602072d061d0a02040c09080f0c030607020c0618130e030c0f03040b07150605030a050601211208190e2107030e0603090307020d230d120e0a0b01120516 67
    0xb0490f5104507030f03000203001c3ca507034507100d9400300e0043e040c0e5801000200e0880310502088410f540c0c80324460386034a406485403001203200c0500208803005c88010181c580da041c408800c3e1040c40480c40031241e160091540c8650203800c46040c000c01c81c2c0e03110100011a81c0c0c2c0740995202e444c00700035100710030158005100c00d012003e950811291265009814100b072502c80d02c4454009101a80c442941071098000502c108403000c2403c6049600d0513489240207618840300c03d0784001610002407400c420312650042c12409480341030f80084a241c950008529410924411200850800022a80105800d441e1342580d80000107200d110000c080307040c06981d5030301900055940d07000503c1968003100040e903800c0d0801c1900c040c1e540050484016403000e080200b20384486010044203020660b1a0407088170700014440070b00380c002d580d00c01d0480e40000800004001e9589542c0040c001c00c80d032440460103004d92940030307050710070310300803102401e15085203400e078440c0305210010110300d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 595573597 1250 595572347 595572401
    0x110d0803161d060a030e030c071a07021302030c090a081e0114010909241a060c0d1b080c0d0305060d0b070806040f0c0206060a1d040602072d06 63
    0x402c9003a0200d0564002d41c50311003805054000d40250f03030b44c00e60a40700214010f06403280000d400380441d802101e1112980b2410141100540b00c0d007240650841d4a010084900c05190750041d6800f40b40d079001141011146d40001c1c42005050f1301100c49a44140c210b41c000f4000a00d014001d0420320b002003013a01034000704021030600501c00d0718180c9a640d030100c800d00c121001450028001c01c0c02113881020042c000d81d0050018040c40c9514081a00309244a42840412a14104400c1c0300414000704032650880310801440580b40340c0440402d5034000040a8402408001c2d031810003031300704000d400500504541c001400c0710b2050380410244030100715020f803401d80150151601001590f144c00c042005031115002d01c40c1064a0642103100340356010880d24082c00e0200c0b0712080307a130b0b514042c521180505418803035444400304041000902150b00504000b4402c076007c13480c03000074181001e080c080400000c0e0550b040356401504219180c4101c4461010001c00b203200401c0e948 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 595574847 1250 595573597 595573637
    0x1303030f0603020d0204090c0e10080c0a031a0c041238010905151003150608090316050c060406120b091302010f020f1e070b0901021207110d080316 65
    0x10068091342e503840c103440c01d08c5401e0b5403402c080e100d2201c4d400010f0800030303c0c0311000903591040890300d000d01c641c840c0c418070f0052100c40480e60840847c0c0742d00e8071071403004079402202504035101c01c40c04000c00925807000d201d00c482d880b80a1080754000e061840d05c5001d042034803e03c014484940482007040014043c3d08850542e000070300002120350b600412204001410282c180e800107015130030700105a496080b000c030541c002d100002140c1c0c0c2d584c100b51024801650074210907003040c4080c100d2080c40c203843d000200d0040045480340020040441c80079841034000c807001071200c0400119a007103d00590340b407880241e880020b20701e414081d0f0034682d80680402410049207000a4210138420031041240c0c07131001080d0344442d0045000380c00000c000b403103210054028071000140c41d020210940340d0340350040e00545104440f14058160360391009104483c400b5607600341400070340b59240704281c0c0501c1820469a6810808032648461003500004410455040c5225010840078 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 595576097 1250 595574847 595574869
    0xf1e060c120403090302150306040c1403011401090b13080d020f0c0907120e0607030f051b070311010c0c0c05030c0f120304030807080901090f15051c051303030f060302 74
    0x402001500c94440e0f2404503111156035001030340c0015111155161426000d004500444085504110254043c00180e40d2400c0c1d0f0701081c0e052640903c010428500000c0f4852600072051429808480d1144509566904001d0900c0464004108144030301c1108001104000744d0300e0005040301c44c81c000200d0313940d00c0044041c0b8091035551020070046800f880410804540e94081807241418804c00c0d030390340c0e0340122541d900080c1014130300c1c4400d00b5a4407880d401158413604114100000d10b80000c0d1560081d0f8084040110141c0c00780c02100c000e1207990350401490365000c04e2410743d410498075a4040c1c2e000785100c0e8102403201c0e030455485d00c1000310204020756011120a0750f400f00e41d811401903510240c1203640000302ca80c02c02003040002c01105409880c1c031084140c698034103030900e0006000f2520100200180c11005078042c5000c1c00011280d40d11080d5015031591600c13040d50401c0e2610094085c07460744100805401d40030351030b06050010000c01245103150000354102c4aa = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 595577347 1250 595576097 595576117
    0x30510020a05090310091b0e01090c020316030c1b060e0108190905030904050a020a0f0809030904060602030a12050613090602070209010b120105030106030b0406021303050f1e060c 79
    0x100141d808200c41c061020340e0b250140040136542c058030b810310394102411200e08115084002091084075000200030f182d03041d41e17000d10702040303ea030a0408901c004d00d440251a000e41c4000e00408510080c042d2418551500c240c0d070b271840101e01c514000c1c10a6144004007060302141601c14802607034071005100001e4024a4040e41a4948001e450089400d48000080c454100111070092000000003040c0200c03007a03030100200d07504d9081c540200c0c010700c40140e00103000490303007600d040d20440c2240c0d00302d59160156843e160010002900300c81141d480240940c10101e24000d1441c0c1106145460002101040c05180707000c400042850324066009280c072070340d07005040d09100c4c695059420003a80a07101003d5961903101d071042d1a0001560500030843c0c0c000089101d00301805441c080301e902071300808240e10b590740c0c1d01000e90801108102000b010701030000200388100400d101c001d8141c005040502035110302c5600800e03e80c49001c10a6004400380b1240d10244e2017180c5104c04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 595578597 1250 595577347 595577351
    0x2070308060f12030d1e0b0a0506070c0f17010c0f08130f06020c010204080708010911040f0213060e0f030c09040f30111908030a0f0f090204050907030510 68
    0x51210002007183c451059108094407000c00c90495413036040c1e0151111915051901c3d0f0402591080041a1100c40121580012400d5003c00142c10098060041603104803501c4030200c1c1c8400f40c00110582d164000107031860b5100d80303082103e00030b10038030012240707620742443d030b003003e00c40c014003202005494044c40d140380750903010074031003c1c03800c00012940c8110250f68956061100c81d0107904907001d8206580100180080c50050520070b04000d20781c07165140c038002e403480b003c100052a40034140c1c81c002d90208084104040d41d0303250040030704480c0e15040c200b081d0442c10301030480354001c241f5029610814480a5590384c100110f548194400100c43c081c0d56685403014241000505000f024101010b500384071074031508150049072616580c140340d84101030031680c0e542c08141e07c030b5524010744007006030103d0000c4008537800003081070b008c0380e100100c1c440c0e442120054029000e5170b960f43c00c000421450f25000760790300800030f41e004200b21070550b02c03907540700c00150300055401b82d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 595579847 1250 595578597 595578619
    0x4090b0d0c031e29011e060f030605190311040207030c02040902030c1f2303072a06090c0806061305070c0f080304030e1f03090804090e0d11010207030806 68
    0x1611011030f4070f25040c1d008100603940c4244c8920b0840b050710b5000d600320103400000000c100300c3d4903405000c03003065142407121002442c006c01542c240a4494101c0c0416484103c00704658a98500c00300840846078554024207155042050110300c181900ca4412030040140c2030110703a200c0158040c03103404070b400186000c82840040d150800a103e00703600040c55070348246000741c690207401c280d0705003602c40300500054016101051071144010b1401c148080c030104550318440c80e45070403041700911282180c00244000c0c00080e400d00041240e0755515205101c3c2003000c03103e1000000c24500005082d142410303000a00c2000d101601c6000203035690000420482c07140840c84080fa0700320f10b441c0e02d120341508010b92158001c5400340c01040e000074480d440342c00c01c081243d481000e070b0341c0c1e005100701d48150214090031120500780c0d0300343c00c280000708804415100d20000d505485004000d0683c16803000f5040001c1401000090303441032180c0401b0030b4200d441c41c0d03800082112603184070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 595581097 1250 595579847 595579883
    0x60a0b101409040f05040803010806130f03180b040b04030203070e04233c0705090106050a03020405031015060c0b040f02030a1407091503080a18180204090b0d0c03 72
    0x208120680400094280713000c1c0401d0240d0640118142c4ae03640d0180e41180c5e075003e0403d0089000303000010320045000100d100486c0c03041c01c1c0c2000003003a507280d0805055858504101903006a0801d50745403100003010011440d0801c0003030000c0c01c0d41c41e2624103c3c501034941604044051402d0441c1580f012b03000c0c070b000700c0180003411518004043c1149038018241d2003001c40c11005005c000c2c1e25201104ea503c0140000450740112080105200456070070448219940d030801500c4400781602032001140300d54003800507203c030142c200d400262802c540d1200303c2014440340d0081d01400a41d48002021038201d41d240d660007602326418100b074111510100c0e01d400c6a030790f00901503c405104007035904c000450181c00300c959190007401212400101030074035240c10300c402003c0c40020845102c0d418060710111010180000b020001150b43e12440354010b5803003171084100940c00902070001000f40d214000081100303941800390150701c3d5440d082ca00f40d09000241c0002210031f518510 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 595582347 1250 595581097 595581101
    0xf0e0f0c040b03010303120b0f090a1508071820030103030315052101050109020a02060f040f020d050307051504120309110d0c0f06030b0916170405060a0b10140904 72
    0xd0020365501607413581d40342402040c40c8001c009904000d8100081010240340c044c0791104203050040000d0303681c6d00d403c01030b4002021455543c1c840c44d420302c2c000003a40c00d8184501001002d0403618503070140852103181003100c030269856a84940404820000d102d41203098905503640f41c1000548095500100548110243e014561140d12640d401d50b2100000611000d404d80d0b4500910090740c940c50a8401c0e40150b0303140030010b81c0440006501d42c4041000c89410501681a031400010150049903e00c07030b1040303003038409500025114040240800c21280f0000c00c0180960540c203140d0303145a08400079410b40002c0544031543c2e0801e01501d04115005090020482000006107280c5510300102c82e00c6011080084180005174442c081c1c0030f0070b5180b8200400c01441913540600b02d90002c1546903000e001c0100842c00e60800f43c5109141d2400b8601810090240307181100301c42c019501d500e0019800b90b09281d8204144a8010a15100c14118880000d4440c80e805001c100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 595583597 1250 595582347 595582349
    0x1a060604031e020102011a031002031f1203020d0801050604090e0f0607020a020a051816090e181b01021b010315150207060309080f0f090a060f090f0e0f0c04 69
    0x80070240074601c541c00b41c0e0320b642c104072405100f80c00a021520b000010002140400d00c5000d805410044a4400807107460f401107a021030310111000c04d100010484034920348041d0044c5407400182c0510a0030303d50100303d40304002c3c1c01ca1410210b65130400012032500d00451040c83d4555484112840b1103107818042e152100c000103003114103920f02844020350b14030f190b4006a01030b05880001042c1400c019a0f520480540015040000c0d200e00c8006004c070078035203101604202c0f156201080110000035410700815280c0002e0140003203400d4074608041c0d8052044240c00400b8103c0c5080e642c0210f564400590750582c020311165060300180c018184800107002821074500e0302180d40c050304034400c0d1030f900c0141c0c2200d01943d19245e09078200c81907540040c0a010f424850480c4030244e1000904008289007906410410140c0c0420700c19001904194041040403469100e00c0c0e40c0842d550000303001c41b03414415618505107603500d05a0000d403180107291084030003e1038806501080710 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 595584847 1250 595583597 595583603
    0xc0a0e06070b07020715031103012105030f040f0819230303090d09050306090a1101030b040e060601122c1f06050405060a0602060708180f0609060c04031a06060403 72
    0x1800b50b1a2520009440e01c500f8010310304010750421a100c0e00034800d01c9807008407504070104500d10390030480110139618184030210701c0d54000525220000d0014070251100c1c291601e10740f07440f2802c2c60307103e078000d030030380c0e0407828184d845440740f5507d0f118208140e002d0590014004200864480b2800041501c42003404150f07200020601c1400340c000241c00c0a141141e60301e0b1108a074039002010384502003601e0403101a44501868004110300c03812003032a10005043c0041c0580d4900003080c2922515031700c03050035401040410400b547c100c4204004a84190002c0080c800038441c4108210350032046444004032550030341c1c4220f07104000c0031030018081c220145508010b8003020000d8602802081d0041c0d040c0000300381c190615801400540c0d14940140070b05540700581151801c40c02030145a45407012101040c605100b800320620b040a404083c1c40785251003800c1e6403904101030441c0c00e0803107040008001242c4900201314020451283c10f018988030710380001c0e09401150409 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 595586097 1250 595584847 595584863
    0x6040303110f07061418040e1c020d05250203060903040f08120711040b12070609050d080306090712362103060b0409060314060c0a0e0607 61
    0x210515412a645840c0702041808a40505140d102565140d03c101d109910101d0321169242450004680c081c14144280d54540300c0e43e01c48044c00101500c0a0a64942c0076400c03804408a5110910140301c0d800003450000706600c804041004041d0700c90280c031100624155442906256026030f520505140c009003201c1c42810400c24064403640300344680c44140291810000f018180842d010300c0c1d11a10122060400d800c0d9100c3c40808450b00c0c456503442030341d40001c4119559003164042c0d284101c1401030904070700700306000d4200310003a0422031003401c45a244000140039001103960002055405d00c0040d102c00006442e0300c6c1d85515088516400c085082c1303080c0c00381c90b01d440d4990744c001c8101d060f50018034005005d400010ba80240c8880c15400100d090f074418928521403250980c90002800b540e41c64030031a45d80c104e5000b0000d40360b00c406040080c403040f0340506803100011360141419083c6440d0070780207489881200c00078000411400c41c2c481d0f0341c1302e00307170b0b10881c2c1c0040d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 595587347 1250 595586097 595586099
    0x1170a050a0b0906071d09130f050304090b0604080705010e1c122601062a0b01080105070f0507110402042c090106030c050d0c03210e0405090303040b150604 69
    0x260049402c9030f25444511500700040c6205101d00c00491503100c3d40501c1e0201d00c41081d090210420008020804c8004c2c2031511800140d10180103541c4140584040d68071107080c011450241c42c071145020f4031448080c441803002c100c001c500714040321001d0800075225805a00410070303081c0180c20349000c0b004404001002e103c0300004501906181d560b03540c107600c1c000c44000450244030020024624000c4006001c2a0f000d22240300c0600e881080343c01551580e00b200254401a90500301c0b602c604400c01080307041c8007400781d2a0004503a090040110717010380e0000308035004820001d0400c00198204042d43e80315035040324090401e07a0f40e501008085034080d19444055545264840111070300012075801041c491641903a50208420203018a017030100903d40d020b41d64140c80c0385500480c00800184600c118070020b05041160042c0c0c04030310f50b0090510031040d00c1c2d160043e0f06000800070340c0301020084a80c001c1e40010312007002d0b11307011201c2107049443c00d5007503001000058 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 595588597 1250 595587347 595587353
    0x5150603010906060e06040e1305030c10060e010e0f0a0507050405181023280e09060601050a0e10020c0405070215012114100615031401060801170a050a 67
    0x400001d0ba02d045e12032903090204541071000c0b46c419403254508001340079000c203062458541030380304007601032811242008400552682059850281c0000c0240e4441003001a500d41204003401000d500c0d14600f114902284c5a1a010b41d00628402c1c3c2c06995500042c241405841038070040c000c0070303041e0070b4454030b40c1c100509260420350f0318a5075840b100b540012582490a1407050303605045071540c100700e10440511544811b1b40030b00452040c0080001c40080c0c5104039003030f00510a901e03a022403420000303802070405501824446c1004000c11010702140c7d00701c18070307a03071a6500796002c5000004000c070890501c10a108035070341c050308000600030070329800901c404070107402c1c1c00c2401103666078603a2607503490241084001c0e00c1101104050214400380b82d08500c03c0080360960310300d8035402c050401281c1058100408560703a04a400c4d107074039070510803c1c9032201c14054500c443e50400310058aa58814416030002c1d0443c43c0703241d10214001d0041c0156a03074010212007001c9145c0c6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 595589847 1250 595588597 595588601
    0xf12091201200c010b15090d030309140303040c0902030c040510050d0614030706030e10020a050c0a08030a051e151302030c04240c030c02040207020907020c010207050103140604051506030109 84
    0x80c00083c1e4075801d00d081d007900c500c0c2000d528007030100141c4441d4a06400d1105001c2011508030050781030580d110045404030311148404c1d008080c1040265075640b400d0310744901d00c4140c0c4d401020089106108020740d034030307502003101d00341d400c121403404800d10000c000b01e50600c60080c007608103e003480800500b50f00318280d0700b001c240c0c085054bc0c3c0c60640b036840807002c444280380e06805652110b0b01c00c8074100d03001da0042205504502d805da15003400102240d10b82031340d0702c40881d000c4600004000d850141486000d07084142d03c400b040c02d107a80340c5d07000699034030007424100d94940400d44111141e6954141e842140d03113088003d64592070501d08125a40d00140f02d0303481000c5090f07502a0641849480b1030010304216190421409020f8908940c6680340506c102e0300680d0070001d0401690350f2405142c0b0070b03441e55008141b004d4011000a06189090b8000750605041c44401c1c0900c166110410754060b001b51800100c0342c0d280181c0c0000b85007440b011503000040000045042e084503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 595591097 1250 595589847 595589857
    0x2806081b030c06130e07020705030d08090d0e030a0201032705070521030318071805060a0801050121020402070b040308040506010f15110c0907030b030f1209120120 72
    0x4030103465120740440c0a0041e513200b00310507400440d038860000d2188803208040c035138018030244103e51000d40c0340e030042031a2841c049021000310f500b03142048500d100801a103982141c42c0d10740704461102d50000b19903540d98000000341410f441d0304030910f0070015410010312085000104001d40411800c04a403181854000d150050003007021410031308a004510305454034401005600e5596180c12400500402020750071385c600800200048203c000c200c4030260782c441610004680c24540c0810119a4940d8040001030341010700402403807080c44072141c10243c0350b5501105000451000400910400c00c000304203d200d9800e10081c5644000390341c0c0704610030001c40c0d072540d8031801f1014071042140300300c0c1400c1c900108c2c40c2d030751a84107840308000e25444204442458100c0400250005000c940d050002a131b62040c220320743c1340070080c10032489030b20409440000100625242ea501c500c4810314050001e011103020340400960225507132404640400384012100b2003480369a0b404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 595592347 1250 595591097 595591099
    0x20105010e04020d0b070e03100b030f07050105160c05100e090705131401030f0f0e011a0d0b091c1e0f02060105040c02030c01050c0406020111032806081b 68
    0x19090001c1511095441d09901494004201c4008000f0301d039903117200f4110060112040142c0a1405400d6440c2001001b20203d950307240483c121303006e4410700d890080124000344980d801401c003009540d8001040b100c0111841c00381007154807103030516a0071341034164803041e04030300e0f0a801d0020032680100884902641144c00e6412034030b603100e00b2a254014140b4069490719000c03001c0021035102c0303020842801042c14082a403004003040d0000300c1e0b285942400005032102c2500c1d15400e801e1180e441d4065000301e010107090740c1c00f8081408100900002845036040300003150b21800e08001449817031002d08038280c0c1e245180c00000701040c0342e109140e04107107400c0e0894100310340214110180d1000b6075008201903860300c2c0c01c000c0980580f000c42429804204100240c240c0c080c084e0500c80c0a2010308542d0300d03841d1010007421500680412180008244140088882c0084210001c0c0c0402c4400b00705180c05845088010802039000d07180b107201c2e40f0500041c00820100c50005000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 595593597 1250 595592347 595592351
    0xc0b031b0c030a05180301020c01090308090f030f1b070305010c030f05010506030f10150206010305060c0f070303110d02031513050105031f1413061a0607030f0e0613060201 76
    0x41406880650340c0162900040035030414012401041e00c1000a0641035090008146840d2400b03000b203401c80c0e10007105203001d07035103c15548042c181c0010500d500300740c800000f0301c55568880b42c0c058403406003030000c066a080010302e2101096040c59281c1d40c144c0d00d002622b414036034034074003d402030440c4501c44000c00d040c0402c1e41d6500c015842000d04031400645a14a50380d03a0041806c80c0c010010f0000310764041c9150302090240002c0c100d06900481038000f0080365045007411071030420028030f89900c03140100203098801841340180c0e00301a03454240414000e03480c98003485a8080e048001281d18404820483c030042c0082800c41c4600d4240c0303144050100740205a01528424003510340c0580c012138015a0341002c401d8070305040d451140c1c000601034480311140008040070b46000160008803030400c818000c840c8030313090480703004914142e42c151601010803101d026041e8050103200c0065458a096805000c107171011400052409070380380508810251421000d026040041d8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 595594847 1250 595593597 595593631
    0x602070f0b0a08100b0a02070e0907030317190c05041e0e06060f09060a081017060106050a021507030606020c0913110604090e060604050601080609220c0b03 69
    0x8481010040e040e120310351076280c41c0c1100364009807214880901101c0781c2e8007144100180103403000c2c025001d491069070141c44030920b05180d411000f00040c20405040c0c00c0780e207041001940040701f001e08107440c01511000755a486035542d507142c81c83d4590880d901c1c03c2c080311200c5180c1c0f1000070400c0e2a00c40c0189404460902070000d076507c1980121403001c0d00080100314285414009441440c0c4003800151810021402082d41e030340000c422a80810803000601542202c0c11035030201800146c1e00e21000c0c01c82c04011a60f0710a0706101d030b00b050190000304500102d200780480042c0d040b0001d0460150308002e000240105203e110f071000500843c4a40c86d0217260141c01c1a000c0c9088000304801280a030700c0e840c145110305010260b001d5810400020010202e005003615100200d01800c100e151080520040da0402803e10b4100581102013040e00c1d44c48400443d0007901e019101c244510303000c500340100710713100749015000881d00e080c001809803d6900440c800c000d00d1985921103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 595596097 1250 595594847 595594859
    0x5010608070f1d12030912011406180c0d0b100c0c090b240405090a06030218040525080304260c010c0602070606050604170c01020d09030308090c06030702030301060207 74
    0xa0415401c00c120044400b03c0340c102501c0c040c031100c4c1d0280d56082c01d803807400b803803200013407241543e807120809107075101c1c00f00d008000d1202c40c4003580721030181c691002291100705520845c40e0300414030f481a01c800314403400010081c0d400388a602001030081e40640b00924009012a09421000c4460040004000c60740c00c03000d00440120440c058550ba0145101e8096245031402e0611004880c081c1840300203116030f5020841ea0040b00e2002000440321300794014051038280703002d0283c801e5040d5106010002d4400510313403d6601c13603034001e42041c070410701c00f40d00e901c0e800340d001245612000c140412280e040c041c0b011264000b90b580300c46021202c3e400701c0c0d02c418030300303c032070740802c102c02c80032001b003003841d001841441e104d04400a400d0f43c4079800110f03941c000f40c0000580c0810b00744608407800c001c01c90018002000d000030041808031000003440700b0340ca8000101001072000100d110311504010301981100010000c0e6200d1900000084d03903500300340b10b26001803250345400035003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 595597347 1250 595596097 595596107
    0x2280e04050a11190b21181011030c070c0302040203160e040603080922020703110c04060e011203121a09010f030b0f1314100b060c19030c050105010608070f 69
    0x1c5038184440d56240c246003180385c048582129a845000341652900450b02c0a602c944551180c82d614080340c00b882e4000b41450301e00000035106008580c940102c944d0012409810f1325480405120707825030315140d40c50000c4250030f0541c4000e4001303001200740490300c0141c8800030b0482046030f9414040e0700c9482e0070081a02c5c06440090b1002c4420070120102c0d04141c07070708404c2c0005030300c845802140301c0c86503038089901005081c1d0003d0100c0e440300d1850703e420b01510b07411040032101031043c46e05101010b5060341c418814000c0030f0104807521402c0600941010304103042280c030402c00411240b211000541c2810768980c411840b001c000b040b001c0140300610162034110703070403051f0399031020001d082e2100040c001c1c000c0c42e41d03e019960001490b00c202c2d00e411114003806010413503c0c040701c0300700f6541c00480d194450b400900c01441d103c00300003015142c41405401041681281d400c003035809401e1064013402e03035400c0c20004500d05410040040c0a010183e50311004007409800032a9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 595598597 1250 595597347 595597369
    0x18070e220b0c03070216270b0a05010e030c04180501060f180203060a030f0c03140307050a080d0221010602100e030307082211190302280e04050a11 65
    0x80a903016001007084030070a60041c3d9409001401262420210b4002c0440c0d016081d6019000b01304034284045410800000040c0c1422050f183c1440b0040500300000c141c0003460240303030704100d80021b5015140c2e404100350a5561805881000f24a0010313940700e40510303c0c03c1c0180c60945c00d10b840000c003090740e01c801d00f040302c40d00c004280540300080b07031000c040c0d400581000d91000891801102055910490030070080c42102034103170b25071452804071000e02d401040d840568105200e0400400e0700861407a0602e81c1c04858a644c070541800508028000c09030000c80c100d880342000302422101c504014160395003034085504a002400701d22090314071241b0640b805400c140003040c0310034040c842294010759100c1d0108081121003110900c030079250314003030340d0b150400e107035100450034603c8000300001c01d4401114456411900400c1e02c211842c90601039414402d005010300a0300580b44901411440c24180440c1c01d0508015581c0c0c13509113015101c0c19203407411403045180c400344400b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 595599847 1250 595598597 595598603
    0xd0b0105070314130504020d09050c0103230a02040e04030207031e08070b060d170a0314070f110111130501020d08060f101403130b07030c02031218070e22 68
    0x21801120701807101c3d038201c924801d42c14880c0c0b002c0402e0319900c80c000780144540c1c8000001714502c19042451400d9080381e40c2d917050514112031354a2041c8481c500c08607080f03241c00007203640d48440d0030700d40080c440d40c0e01180b40307808a001070004069001c101c242c12240a6002901c0c0c40950f9109101700001d801002000c54104104400004500c52003540d801900101a1526030600b512880050407002d6210341c0442e10001da0302030300c150144100256112484e50100c0c2c54504040081c0640c0c1040f103501c018091a84243c00c0007403025084802640e0301c4010031a150350f14002d0340400910b09005280c00341c01400040b840d8580700d01e0030306124a00040020544400502c01d21842064400c002c3c001c00030010002c280c028600b000841c010b00a14003810561902400c2580305110080d003050b0400d42030504d107180a42d40041070305d5100d1021100c9082c00d4503001102101c146c03040145180b075010f415400a0703081d240710640391180c596001042c041c143d24280004036000311160003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 595601097 1250 595599847 595599857
    0xa080f06061c0b0301090b01210512090d0f060212090303040c030212010b1804030f0c08030604270303051902070b0c07140312040210030506101101110f0d0b01050703 73
    0x5000d119800c1502c007000500c0c1440e00040400040d030100382074411004e8140c4450a4507401003241e241002800285207030840d08170030980c0410fa4a964492030740200b640481324020400c0003840c0c0d07400c046c3c5241594000e0005040000d5442d00340065000740607484002c10a0b9400500d10740c102004a0b0311455020f5080d54049080d6402c116040c9440c41d0208015903840503d00c80c139841e00319101540d40101070110040c0d15107441c0003440ba0288080d0441040750100ca080300103010401a01d821032070444e004600d403550300c080840d2131041403114440c80c0d4001c070b6801c0107050b0568411400f0b00ca00b032243d20328012107a4508002d911480b44028140148580050031a10b5020050111a4891402c079017602480504613861a04403400310b01c504c01e881010b2204614200822254032861400c1c01d2110340741c800001403c880110840b00c0921012847d40405910203600424140703041c034010b40e864891980c0b00d607003503421444405298501d00405a019907000f00f05a81c0c50355030554403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 595602347 1250 595601097 595601107
    0x1022109152206061203120e0c0d0609050c060a03020705070816180609090803070201060e0c0a0818071502060901060b09150706060306020702040b0a0f06050a230a080f0606 76
    0x8055000003100e03000c1e1401580c501021609040c5d018025241600a503500805c005090b080c2070100d6902e80301015065120b4a2030f82c045840321405030011030b4100e040011440c2c841d0810a0424044a001c039a000f080000c4c101c400e50741607805003104500501c101d40c40107071115469603440500c06100d0300c121071a01070400c00381d444140d000d41000342e440ea0200c2c01c1c40c0e60b40c200c00141d909007481110307810008000c00c10b95039424400c070b078001c00d440309102c441410407942a00f03242c410340030048104040c40d0002400d0340f104511041440301e1910840f04440d945030140c9803900c207455403810040c040c9002140c03408105000b070703500742c0d69084501480c00801c20200000c0d8980c01100d04050103043c0310000104a50707118640045014810160740d4203142c0c410000ac4a49035850035109000d25070782401020001e00084e001d903901410041e50310b13102024181e8822030150b6101030408442c10148004011080c054210a40151603141e5180c0b02c580c0811140c25084954642145c01800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 595603597 1250 595602347 595602391
    0x507090605180f0315040b1506160201230c0111120a091502030a0204050103060602030c0a0308070909050c0a030b09010e130f0b091f18020d050102210915 68
    0xc0002c1c424038000f8421038100e828800880d003412010350001400340094420042482045210543e1080b6500c40c40c117503159144001400500400c151184008407901020b82164000d08c103e04a00b045803407960190204051340c00656400f4410342d800550810710101d000c602d01d041034501d10f0364202c0103140240d842450010003400c0309102a0707201410140d03861003141461004500400c011180541d80d241000700242c1074898942c009021907104010f050441c080100b04850f906038113141401d4161a502400c07205101603421107034400c0d01d0031080c0110003140500071710a07080c2d43c2e103050042170710407005c00100c1d1809226002e0105c0500c40094051900d42e005580150301c201c1520341e0741104c9132988551044e0498210029600c950203505002414000c80074400e020642d051200403500a40800300001480c4000d0180320031150640c1008402e4045d5003002c040c5282c091400e10101081c007010300c00981300b0711854098543c4401c182d4040030300d081d100e08124030a10883c445d000d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 595604847 1250 595603597 595603627
    0x1050402031b0712020c010905011d01110709090b10030b010b160803070806030610080d0818030c060a051b070213090b0c04030201030609020a23090415090507090605 73
    0x205520603030b807540000e0144003801c420182060600414400d0b0310b48090110107403a22002810440c1030001400c410400e0760703407284e020220301e00d0403185d020601410b44010f9500201c01c003844c0180d03014101d004111401c4aa1103400341c0d40c0905c6100499840c0c85042451018080c000078249030917a000521203503503450010700d40302c4e10300d1900124461140d140d40066410555500780054445010b004080c58200300071034004489070749003070026250107c0d6659a07540d04944005004132140002c000341050503601c008404090180ca40d02c0e080307552915250700085a8004806242c00301083d041c4401420041d000e0501280c3c5d00d2420146808004020b200e190885890544899025000441f03401c049030003400ca00f00c50300d807507078110710016042d00c280c1d8110500f11031042c0206030b11a544050070f5400c4911844081030361000303200b02d0610901c0f070400fa06800509003165070f01c601d00a50851012510700c00c004100c2e503156140708503000c0f51744e4803030400050f4040c052004109158 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 595606097 1250 595604847 595604851
    0x50c040b011e05300a1505010f0905040207080a08160e01120e070e0601020f03090d02010c0f1704050406050105070b060915041803082a1c1a01090603140105040203 72
    0x1c0c00d01500389030303510b0007525281210181c507400d484580d07411075113083c3c480844240c0042c0780540c03c1c008403040c00c00340b2030f00c40c403a482181d0402100c0303481d690300c4500503061540505000350042d55a01881e04000d0001d0388215110700008040c42c00242c5403035014106c02d05c00309481c2d9214885035403040011200a91000d44000d0035650301c00300303003180c6070040251000424401e0585011490454006800c0c20b034400310f413001c2030700100074001c9a40d60b00640c05445a40c2400c1042402c0580c2c101842c1c1003101a4000301503410701100203a03001e006002400c11a0b400300d905010094550340111003074018124014840050b0f100450814500360350301d5584514410700e024140f41000001405950f9528010000030b403d040b0341d8018107a200c4c1e4040da0251030b040f44034410440300e0050a2040001220301c81c0d0004c40451081e500a500641040d124445c03064144921a00460000700c0303540240080c81c08520084030018a49000703000e400e554020001c0e00c054a40c0c604018003020b9840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 595607347 1250 595606097 595606157
    0x302030c03070609151e0c050d0e06120c09090108010614040c1b14190b0c0c071206090605040b0f090f03041206020403080f130902030f070507020109030b010909050c040b01 76
    0x95100b030206d28030680d0780f002c0c5007141a0780c0e800a064105060050610156041100030809403202284a0b40c40708800c98404130150035407403aa0350f4482801c0e80321307805030444c6280e0209104d03000041c10308054000c001640c0510141050081141040000716503502c000c0350301080c2e16421038103a440000584011a42c000c00540c58155082080b503410324420800c0801e07001c18a58814060205924990354490b203c2591030380b42c03d86801c5100d582d12030340d12880c00c10302c62082410b02002042e403c8079403550791001051110341002c0c07404076140315040795103901c62142c0c1c10005000c0c940c0050045007144228001d185080d01f02650a50b8140c180b95064407819000c00000000071840402032001c3c40c1c1c181d0145880b610311074144c2e52840e40c0d5900540c1c0c00c038010300c2808551102c1c00b0220760080c046041c4159108802e00c0181c428a80c5944040c05240b0b0f043c000013000741c0c903504002e24a074400c0058400c0054000204402ca45001074120b0000d2100c20f1442c203034201d610142029459 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 595608597 1250 595607347 595607357
    0x315030b040f020a1e140603010b0d0603210e0406031709150309160609080c0f030a0209070e0a0f0f0b1e030103081c020a1205100902130302030c0307060915 69
    0xc3c0c3c02064401d000d076071050341c0e285c420080003044c10016404403800352402140d600c00c00c541410020b0000c2c00103000781d680c0d4140010b8911907031580c1e54400301c0290347c001070540c402c850745910700c0c201d582c400e030805000c078406042d810607070f18007403140c40103403035104800c410311160b00b64680c5465000507081c542c01062106500b80410300e4040618450100200200314280001410305085000741d8040010b0108a0030f0500c4521004514a030400b002500c0c0b4161107048180000c0c500a240303980070f07400c90ba40e8010b001c9a0703603000d01000380104050703c0059201e41e590003104085441c4c0c1c886c420041915460921580705040010240900c0003c00d0310314404500403c0d640c282c6c005e9004845505000a18001200d06081284001c12580800b142800200324000e40104400e004010b0f50715510000204115014a2107a0103005450300c119250b0504824a00c80d10400740407c0c1d100e8422541401c03503501c0e00052503019580240d0310307030300580e2604240350700c0e00b4a1610080c0c2842 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 595609847 1250 595608597 595608623
    0x909070e01020c031c020c030a080d020906040302090708250c02040b0a21020306010f0e070e040e07030b09010b03060105011e031b050a120204080d0c2a03060b010315030b04 76
    0x284e420850128168981482120860700888010303141c201d10310320050094100030504000700d1207100a4941d0700344c84100160b074642d2600000b07031551241d500000d41c0408024288450b0580c01070701d01c2d02c94400d0011180c4222840c0317040d160f6400b40100c10320700080340103017240014105508050040c40010340192b00b02921000140c901c030b502e140364900142c0003200f55100303500d810440e031801041503a060b2144641002100c00408100500391010300c10603071402800d54949602407032400c1000d00c203546c0d601d6101d00c2c0010009400f903480301001d40c206a0b0b0044540b4003c100541251016103841010761803041782849000c4400c0801800e05603107030307031056401c0044001000303c2000c680c0c80d07075501c8031880c0014003104900d00300c00755120b2041c003003808481c01c001001100e000c1181055045840c5501d0001d8544101082458100d8101c0002c0d0405034152034403070082da441020148481c880303100044089907511369241d46141c03803200d070401c0460600031945801900031918500a1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 595611097 1250 595609847 595609849
    0x8100f27020d09050303040302012f0703140c0304050a0f050102060712020d140402010f14040915050a060201020a080f040308130201030b03150105030717030711030717010b150909070e01020c 84
    0x201d50701c11041e904c5420000400003016420b1090554001d290b5848840902ca040180c2c01c00c1c944030b844400c02d504000481c201858016441c060b100c07000301175400d9980740c0b01d009150b01e07500240716140c000c64051001081c40d0300c0c11200f0006495069004002e00d9807480350407241142010682c40f822a403c01c02d0b80c15150840c0034551384d5401c00b080202c002c1c101440014102045182c0e014101305180c4a40100108400100e90444c0c01801c03012072043d5040c00c2c0f8240042903039108941c003c0341003400048041c1c06401030700b40c0d0000c9458036110b0344e40d05218500d03e104101c0740200002c1c03101c00020f4110b00326091808401d030041c94009181d02c8024080391a2000c640070b43e072494981980100000d1504004e64405000100000f40c03c001c0c12400c06a0741e40a800d00c01000d0300410f62501203d51410450503009145c54200107142d011030104840c020440c5d00310040c010540d110520078100c81c001e040361550700e00901b041c040fa50b18204104e4103400d44042040c114001c05810b0049 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 595612347 1250 595611097 595611101
    0x501030219050f160506061c02030a03030b0604050405090a0221030904180807060603050c121216150618020304050a0b060622150e0603041b051008100f27020d 70
    0x50b14403170380040400741032600c2042103088148030303030805030010908110016140400c140c1051070b81070401013103059100300003450a0081d900219001881e0400b080b136000d10010300d1704401402075070040c0c543c0030142d8544210202c0d8400356413540d0300c1041710003a02c0c1004d0b031140020000c0881130440740d485651754a003855104500c2541c9603516603c090092100c1484030aa242c48200c440c10030000b40001e40e6511607011100744c0011b540080380d40c1c2da40f80c000a00e0880c44546c03080c5095183c9003c66115402400c140c0200014032110300140b02c0d0b003028520031070f0b0240b03406c40c009041448a5a0ba48108010300511a80e0001d905010308601c50010094500d2031859041a560b038160414000000c0d01501c140d8100800000704074104690b1074030790032a27800c581c100041c1e1408464003811140c88040c00e46c003c941048905101040c2c05601c0510340b0301505540c1c0d0b0a9404696070002d00310303140514000c2c035003441c2c0821540c0080ca00b0000a0f40745031401d090000d03040c003180c8012102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 595613597 1250 595612347 595612387
    0x201050f391306050a09030b040204060302030304170c040902150315130c030e01051e09120304081908091b030a0503070303060612091e0201020f01060303020c0a0501030219050f 78
    0xc40190041030019001c0c007640c6015001d8019461309a0411000050042c0031850340c0c880682104a410302103000c2d500c3e079810040143d500501241d541319038804856050340e00b1058146079a004100001c40103103814054840b0554005251000c004101032a5100c0d07a4000303045c910089100314081011502d0b0314414540071020142c0c0020f88101141000c0d0555804524460869240c001000610b1850444400260700b4080c100c00352a541c01610600d0b01070303c07401c800b410325808401c010800c0705401c01004411a15600031160350654413050300c0303444003a20101c0e02030f04030315009041040c2c030140d108000c000007400c884420366161503c0707040d030340608001d0300080d40792842031066070f0300310b2402005041094410010160f45480344c0a00d01d10010b48910400098640101035a10070080000b641040078000c101706680c0345400b80d610713a64031005c10b002e07828803c4000b5480d0b000307200b558012074030b442502e40e110403140b00448959029178880503035460305112100500c951000089 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 595614847 1250 595613597 595613701
    0x303041217010e0121063209120f070f08130603024b0d110403050c0103050703062c0106030209030729030f010e0a0e0a1709030a03050702040c0201050f 67
    0x126050351007407008130000d0000080e82000c0d02c0c110062200c06203001907503c0d22140c4222000307803074040400ca18001c0d4420142f0190000041e071580070184901c10008181c104181c41d2400c003072a607100c2003581603006840e50807441503247c81500180b5640101500c42d481c0c1401c1d402003421a5403c80c910b00700c0e1150203d00f000030400304902034022045c0c0304094400034500407950400340340d80d0341c055451601c10071080c100354540012451300c0d4002d411400280031181d5110f4040550003c50b6213204c81c8501c50342e450b40410800000302c050091080b206081400b6026110349070a100788800d00304926001e6814000e05000f0f01d4074050341030300103180141c50f07401c4090400c1d4500007000c1ca500360b02a0001080301e02c0c09002c0040d41c1400030326401d44039070099103031800344685c0d40d038081d1a000301107915416004d20407440082651090003050500d00c01c031810048100e0f00d13101207080312012a0501d006130a44c801040b490440c0105010184100c55021841c0805800103031650003c10700ca00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 595616097 1250 595614847 595614881
    0x6061306031d062a27040b1e060306030712030c110f0a06030b150409060302011713030804050a05010204030b012c0106030b0f030303041217010e012106 67
    0xe403010900c05a061015002c09000800c3c080c10310340040c0324110502c0c001c940c000d200013940c00c160868001d0030381c0e4403198000039a03181d200e0004090503405403d454000d21807480c184685401c0c1c6002c81d1400591281d0520007403e00082c1004c1c01440d50016045030360503c80d035440000e2150740c1d908050384051003030307854203800312143ca03003c000b088041c1e025512681c0c1c1c46500031010303241d100d0b01d24111100c40ca400310785030844001140c074168601c0e903903540c1420300050202e0062107d401c02022607102f82e80d026040d42c41681d040c003c0394016149030791560740e581d00302800300703101d9500340382c0007801881550150070b429510542207a01c65441103d00a0511004200c899456900c2c0400c090550003442121564a06640c00c041014000c00d424107950758003034113081d15058006072190344003608490380d82c00c1c5070170101c01102c4903000d00320003e00c0102c45440300d20040c0b007002d412030340d443d20890416420510008151030005410401c19800500544081243c0d4028114041000740013 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 595617347 1250 595616097 595616111
    0x40c0e0405041b0602120307080a0b030f0f070902030c040e0603070f1508150a060305091002130905010f03050316021305040620040317031b040611191203050606130603 74
    0x80e60000c03c151300c46815074100c0010031000c1902801181d80c061000c0c40d01c0745283e5950410407008004002d5059098032445142c03898881e00000c420b0041c4807a04200d032000765a5142c80c0003a0f00c01200c00e41400307001032101b00320900c0b0640c012a0850401011b40b001c180e00d60f0307100c14004c01c10b94460388500b203009226003011a0800c81c6507400031400742035900c07441c05400c040740140007203100c0e04040503030b208001028104280000c18402c0c10f41c00040d90b4640ea079100160850000b405403d00b180d160100029418911442ca00110703a4000013460902c41e10b04c4a0785184109054203981020040c0303108000c4004500c20280304520415000515000d01b0700300600454171468000e404c00020003090020a11a001300b0b41c1d201c09181c0c184da601d42c0c0b0541194076511150703050002010001c00c001c200980c000c1c03c107003100c03d050003c484405120080d90034802c2030594024118a10f20009103000700d2090304a03039070000014107400e00c3d241094114415840c410303441400002d0303945903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 595618597 1250 595617347 595617383
    0x8030715060b07110d14030d0f0b030d0206010e071b08031b040503030f07150e0601141806040e011116031407050c0d0c030c060f080a0c0e040c0e040504 67
    0xc00c41d0042c2c1100070840d801c0c080c07a5501c0c0790300294401801e5202e006108422000c00441c00b808014041d40001aa40c07242006e100b064042d20034645c45020682c2801003130042d43c100000d081c0715918150f80240309d40c2c0d19000800b401c0000242c8a03504100c08084821140d003241545240c4071445003041955a1500c03030380251403c50404d09003c0d0b0706502b004100500c0d1340c0001075400265a41400e2551a0207a10f02006000c0d102c140181e02c842c100000f00e14248030214a0604a03161400c0c41c400c00038801d0101301103414000c000c00180520140030400c9410142c2c000514010102c00025038510a018801b4142d00907400709110454081603800401d588164400c0030604044001d0b0300b024410748d110f0791652561540140229401c5868000b0b001030080b104000303542090410416644900000344030b18204882032012441d004003103081c031200c07403180d0030080c0c0c40c1e66246105020740d50204000703480000c00e80390820a41d28480100d9a0340c2c1d2060f60b001c0c034825015001903d852907 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 595619847 1250 595618597 595618601
    0x708090c1e1201060906090905060702010c200c03010615021002071524060305010303031a09010608090a0503161a0907050609041404140601091a04110408030715 71
    0x1166640030740329040c62014141888006005180d408582c591400e00b140000907004214503400720300701504001d0b00203140c40c840e40c071542c64a4050415514545e454540030382c26074401196500026054040c0306840b803103002d2f442c83c2e15190000545640c10078241c0003c1c29600e42e50020903205101101644189070104030120410740002c80642c1408480e403200444202101309840310740380c0b41d0828112900142401c10413603025803807502603654517010010000c100900045011038034290a15200035400b1041011800b001080107010b42c2c203200c42100c0f013441c0a046c0103140d01c00d0548840c000341313040c0050180311100101804025070b480c2881c81600840d441252140e030b4a8400b40b022400c40812690300780c84054070407940d20900310021900606503203000a592060300c00500082214407291135a03012900303002c0329900e98031821005d04031501038601c0f5503074480c41101c040c014145500400d02c01c10000d002c250034540c0e04d4800e00e055a201100403036051200034201c6000b04054 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 595621097 1250 595619847 595619863
    0x23072406140619030b03100902031612030c05030f0c150a021312050c0603090a02150a051c18030c0507080c0a060509150a050706060e040b0c03130209070809 69
    0xd10381010603a0810022440b00e214155000d551800d4146140b51034500030b801084ca100c1010781161290100f03c2d00400007070800e100304a10030b0144002d070404e20340b2a0000c180075200c0840d0f40c04000749240e5026100c8221051046840b0301080c0300b41010b5419070030250040c2d8802d0805032102c1000091600602d81c80104864881c91042c4005280c0c0100341c015542640e0740341010001c1c1d1159820102d1030020300048003030740440000100310800710003041c0004001e10a03114031200ca20f03542604a418060000300d00c000550610400051034005a80c201d080300180038001031040108140507508001003505901140508601504120f41000018020103c82c1c5c00713052040c150000044200a40d40700e0081044000303d5600144d90325020240b18100e114100e240d500e83c0544000b82c22a00320440603120503151100c0091141d201c9940140301d5a4040e00a03080c0d640e0780b0b01c41c0300c10b5400191031200040e900c06020801601c500440e107000b1130080d03e4106482c44e15947d00c52a000c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 595622347 1250 595621097 595621109
    0x904020a032d05220f0c081b030f0a05121c0f090b0c0a02060c0d0219020f1203040c0603021b07060210180510020a050c1b0a060504030323072406 64
    0x3a40d0042400104204c0c5800146911402040300706469050090440b802a00407203094084c100301200c031400401520100240190292007143c4410020701c1d4840700c1030a8064015049880fa281711419000001c144841c45444820540429030400c80d00300c68103000204940c90b500c004030410b02040d001440d030720400000c469440c2020b400300003906c034180075004510158010444d103900f1015501518102103030b18000340c2190a100c48020340c0c0d88034511000d00d0501a1410265109035403030104e9200b10b8000c1d0094081a1500400b20000d500c01c802400801c00c641c115071418210920418000f0803140e8000c0403046440e00041007100d0074040003460b400324107651600001d80206402c519500340000c0140c031240c1c0e204081c1da080c42210200c07540760244a038a61006062408403440201d010b0350388821941d00c44c1c4080e1000d105034000175012071540b02504500500a01001c207000400ca0911030500900d0750b102c55044104444642c2c0300181d0699030280225188a40402045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 595623597 1250 595622347 595622371
    0xf200303040c0e100603180b0907051207031e0206160503030106080c0a0e011826010e0c06040b0c010609090308042d02010e12031b070e0c0904020a032d05 68
    0x141004c29490302055445441c0905441d0304e01c840340320004100321030b40355801094990003403824040154491045006051094503d220281500e100000d082e030262a8022240c000c542c0c10060180780701005140200e90255007003108071000170f50090786461a82c8188000c5842c0d50520380c2c0907040e954010a05136a18506011400515034009200c8844840170b0a12500d10711505da51003043d0700054211108000b4407140080514104108100302c9045060003000943c11000c20b41f038552445810007075103c02d0078041817250340c132100300421074882c0c070074000100c50343c0d00c82200060701c02c504000d40c08101448200410f100901d110303030301c501843e510840b03110015401c0d142072038402110040d0400010080c881015120203000c0030301c7c2d02040c012251183c03c081c00d06015610392070942e000900501c0c000091b0075a0740c4441174011000e01181908101611050100070f401407140001016142d000c8141d48400c5681c207074000c280d10000e03401c0d400080b00e0000c0706550000d4008075600d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 595624847 1250 595623597 595623601
    0x7050f03070e0406030813080f010b010816030e011506030e011b03020d02040b03011509090b09011205010b0a1502010e0613170f0a0302040509010608090d0f200303040c0e 75
    0x49000003180d610020500b48440c940710b550000c500185855000103002c00400100c02d41000e2549100d0000c0b10400011100d2080c10844510700b80c5c0c10003401140402c0481000c1813182010302c901420f543c3ca14580003552035180501c00d401d50710100080031440e00303a480c1c28050740fa031501850140841046c000c0c03201c15081107180391094020010300341050b0740481c24900c00501901200d006212038000b0940341d50312419031140d48402c0a00d502c0100340510030015450140740104007801c3c1c0001c02c80c581c568645070040460b18034a100c00c540d40d540c1c2c0c54200465039102800c07603029002e440c043c041103e151034406400c5a0701849039851a510000421020141c803002810f2016400a020300101c10080b818516501810340400011180414100401981540503204032881200c188809036a583c1c1d01707032010312090341c540f821500312007141a2158001c1c0286c800c04003203854140008943d1050a07408420403411054080d04000305000038483c0d09a82e0202a00d41e00141c0c05140c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 595626097 1250 595624847 595624867
    0x60f05030a1a06030c030304140a12051902120105090c09180604020d0201140f091e061206120f06011e06021e1e030d06080606010c020418050f150705 66
    0x2d8003031107160725000314a200008503a80c07411700585000400140c02c50740c45949422200480c1030324014110301a0b2007400000031890b404040c049401600a0060002d0241ca5429901c0100f0004400c1c1e03041a03401c0801c0030b010390240305580c490070118001e4081e194031401046074955001d00034000418520200c01d40c004800301e016504107504981070250002d0714030040e00c52110a40b2100344502c0003003001c00c01d03144004018580d08808031401c00c0002d100d01014240c000841d020550403c00502845650a400c00f8109403c00342c01481d00c540741d0b0861103142e161100d2040392054903000080108000200c01c8458801d04c0c29488050182030300b007c2e802960b6014000703606d145140e100c0c803402c0403074400b8000074412400c0031a00d084a00c950440a650b00d41c001000170082500d4120000354401021030401d01455050f980c41a0300031854080102410010411880710301e0f4001c0010700141d0b0400084030880311140c0502001c02c61041c440031110802801101401420842d101a0f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 595627347 1250 595626097 595626113
    0xe060a1b05130e071d0307060e010c1a180f070b030402062803060501080604200c240601140406080c3910090b220501050a060f05030a 59
    0x22404451820503114000c4078841c0c9a03108440e4800554500800f042c04022544041000c50301c041410300c3e59103894010045c10740e1401c1911801c400207400390207070503007903200b1081600f4a40c0201314851a480d10130050054884050321007103000780090170b030798240d4a000d001034111941d8040113080c0007440c012808000d4400148024460707540040c00080180ca0980d803020341c40141c40d034030038002e288140c02a00600701d13401424042480400002d19130324040c0101c000900c3c240e8148426105c060005410719040f8805004150140300309810449034024a0300d03801055003036604046081480c00900b50004400702c3e110050070400043c04a2600201c099801c41441c1c0c5110744d64840540c0c0018454158200111000403a544400917811803001250000c1c2680c0c0e00b510041c074084018042151507860006103021094000100b80b04058202200711809060174050300811319500c0d00d0031550300f1150f65000e103503201d5090100035030b4441c408015040030742c0101075042403500c031140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 595628597 1250 595627347 595627391
    0x507051b0a0209063303010911030907030303020c01020918150901031a040f12030905010507031a0d03020c0a0b13050414041b1d0a0b1023041203030e060a 68
    0x805122108420b024120041038901174800740701402c0000901e04c4e85a0108951082c4540034480e0300300074585440482000c200c900861940c0d002700500c0e89982e81c142c000e50040801001195402d0002600544890782c072414038080c040c0b10220b06140450516004911080e8a03034090480140148009500c004116034450303100b525400300b981d44c2d45840003207071a8852008020603110404007684070f801d50041014103103e0002032100d0360310310b44201d0441c1c0409411a00c000360960f124002c2d401c00300213410220b4042e01c150f480010480c2c0c08900b0700301513540800508a80025208811040d42940c0c40150004450500201c0403104d28010701540240c4080c240c14144030343d800c25441482c01c244c0042c401b102076005440d004219012107a00c0c1181c3c10320506041507940801403511402c3c81240280c15103944808081d034142d818610a80d0409040d0400420000494243d60000658400c0e601c070f5580481c3c5400820640750922001600e4040658180022165040450b00b0410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 595629847 1250 595628597 595628599
    0x209010f12060f0305031801030c090603050a0f051008060a06030305030a0c02100e01020d061a0316030b040908070516030206090d0602190c0309060c11010c150507051b0a020906 78
    0xc1c020080001c00014119503026180c8250318081c00010028040060103428415900e048078013141000150169083c05086400140c0c502109100701406940869042054a61f00003400c00490740707103000f02c3e0010380381142a0b10080c3d0302001201c004110a039440300c0c442c1014031103545555000340c0035002c003400e030036035558480c1c1c0000e00c480c0c420001044032108058051103c1140c034070059000754005403a49140360b08140b404a40403451080c21540000c3d0440c00c2c600d513a81d0204062403102100e811360003015100c0c40c844401c0e0369030f406115003403070107a160303c0d507583c1301407420b01d01d0324611100401090b00698000c00161782c58009441d00c3c0c1d0360a48ae039040c0d00f8000c0c58648000d100303c1085408140c01c0c0e07185101200e0f0301540e202d44480c80303601e81a4900391116020f031410007504500030200c401600c06c0c0361042d4824400321f00440d01c95501011241c84100d40d0324180c0b80115005400148082140840201440000c4900c0040380c07019000c018000d401141510350000d01c09 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 595631097 1250 595629847 595629857
    0x190602090301020705060103060617010506030c09180307030207060f0c030c140a17030f091501050d02060d0e0c0a050123030c070203150403020c0909060f100b0409021c0209010f 78
    0xa0300d800e840a40440d200d0340e9125050710381725a117a00d0810001c0129000d20400300300c2106920340480014850f050007081d0007001007000c4844001000700ca00b0004004061f058842d80d11602c60360002c0024010051003034020b04035003400d1110042680c0300c01001241006803244208000c26008100b03a0901a001201400c4a0b80102006450415040401080d01c2c00c020080715550700010095070050460304a01e000c03944410001f56518542080320548800f901c4004124916010803006482480500403505145040100e4001c660711010080d243e5004404c0200c0c0501e001c1a460000d04424244040c011221856084c03040c50792144810802c034000020640b074040700d001b03981c4610f60050445a2845480700348036019982503a00702c001d4881c10f044494185084c081e1503210307050702401000c595689104c032042481010f4a41246080000070115001020302c00800181c000f140025070f4450000d80b8400a001c03030764410581d268410b101c400300580e40000380c0c00c40c0f61081d00d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 595632347 1250 595631097 595631107
    0x911011e08090f03160606050103020708030f190f020d06080f100f06030c060507030224041e05030c0f10090503040501051c0911040e060603030307050c03121e0108190602 75
    0x4043d151200b0102c0c5983c45100124a004040e01c240c00c5107105503200343c0702404055034507c0190240d0107042d0700100340c0041480000e0b480c0300c0565030b89a2100340c0621494102582e540c4040c11107405130340d1080d8181d0000340c055010585401400d0041c617210703000303028444001e00c2d10764649002c00103150303001d074403000c0340135041c651508504051604a04403c962a603120b8014106e03030302c44001140175000758594081030b1201a240345026407800d25000900b0b9880d0340d039441c1c444a4455501446458000840022403810005007401c6411640100310030480c401c9020b240162181004e0ad0341b90515010600151000c01520221034081c00c14075101c090300790013034018135007800748280e056103082c0c110001d1048a1801480000c1d0a403020440784001c00152502e42c9005c80d84036400da1300800c0810b2140384260004d00c404590801520705103140f000d0107072410300c0e0a45005c4050005441144001101482c115004103440030080c00d1a0b52407490381d0f80c0380420000042c00072540891 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 595633597 1250 595632347 595632361
    0x81e040b0a15050a0902041e06020a06110d0912230a08040212010c030f06120c0e0604060f0905011d010e1906031e031206060503131103060108010911011e08 69
    0x103100c0010f000000d1400c150743d80c440b0701c0207000b90440d00c164440400c50940203500b0301e041400200540e20a42d003d041310414a89074900541810801d14000020410500c08412054854040200d01c01c640d11811181c08010040181c0d010864042385004034010034402e13092040704564200c80ca504065045980f00c1c000101a0b07003004031b0025595082624040e1019807681c003c840a902c40c2c03000b0018240c40c0c100c0c8400c070f003d02d6100189461440c15082c0b0504002e14000d641c80b250040000c0365280e281e81e0043e4040c000c59010a5106483e000148a0302004204c00c134200e0380541072051003503143c0f01030010421009801c1c0d80d41328203800400034448009400503405103400205410031b005080101c1c289070190b40c0c2c0c0a030001103000080d950082400d00030300089482640e280b13429a02d90005016001421800458080307581c1410b1541544003403144900074171a003800011466060f0070120141e2054880076070404c0501400900c80081810100c0061a01450400c0d25503403004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 595634847 1250 595633597 595633631
    0x5181b030f0103061b0518061306050c06060103092f10020c1906120e010b0324060a050901090216021207080f01020309060402060703120c081e040b0a 66
    0x9104204020400810481d00c0494009094100e912982040140c1d181d103030b2150008082c141c00e10800110100324044084508029084401100030701461400392050071ba62031000c3c0d2940114007048010a114042c4401480502d0b0b00c80820300b410700c0120f9841c0e50b100c030088031111a141d1090040c05420382c84008801c05030070700d040041d00900b44143c800202035564100240600c0c0b04000840944451141d801d02d14011110183c0b11045100c0a54040d07401a007140c851207595903580c0e212042c260b035000c000402c040b821030603035060003103d187d01d041c0e072500004080c43c0c00780311603085c01c20143c0c4610030281e0440310795100040c0c84641040704602c400c080b12a010350300c00382900c00c1c0b406040012584508440106007105e0400d41400b040c03500b81e01040700c2400c41a00f1000025015041c40e20003045074a201c2c0c40e0407500348035007800c6034045a001c0300310280024070310340c10840162014258046c0051841c0011f1501d0f182c0ba075140c0c0700941d0001c150348000f5440300390395140002c0340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 595636097 1250 595634847 595634881
    0xe1b090c0706050c031501020c09070f021204240504030503070b0a020903060c030610090f030809011107320d02240c060f01050d0c06031d0f0c010210060518 69
    0x702c0002d00440c10503400e0755a003a00b0540f030041d144503004006915642c00040c280c4900000508400d141c0e5680d00c4040c0d0340c0c40340c3d0780d01203419406440e01c46101901440c4c0148040d0900c2c200c1003c1e000c80b80000f4440009041c4a80402c0c000100018004940000192101190700c80362200300b6644003c41c00c40680105190340b034041c847c1c481407050603981c58000c1e52160100740d0703a0889045161500700d601c5d07c5180701d589510090b070b440c1030011403230941c001d01c42018107040c0440b1090719044414036103195503101e0701000d140071101000c8400704203141120a8010960f0507140310605002500c61552440001e01c141650a4410701081d00d140d10540d441c1c040205154642c00f01c10200e0340c032250111440c10000b8102c3c0000700369807811441154000ba08890b0755502d490401d00c00340c008103010300848038185441522007d10500402204240c0801003016240000e5100000b80c500b48400c1681c5050a003009030074025501c0340801440310005007000c400e0765854004840b030140c041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 595637347 1250 595636097 595636103
    0x70c0e070c0c0b1317010c231b011d0109110607030f030f112712070b070c030609140706050a020d0320070317070309020f010f020705061c0e1b090c07 66
    0x251715914142c40c1c0706500c203144042494490341d0010f0480082c181091980c844031034980041801403807012032482c0b1410304200750301d034000100c0c02c462049810390741410983c5181ea90791a694840d0821040ea01d61380f10511054400f41d0501100313030b80240a40764909034620816544000c1c080203648039400c000c05019402140c03690325030b081030000166510600303004801a039400940c03100c82c100103982d40345a22014010b00b580b1410050b481246900186081d00d440c002c200c40440810750b10f10900702000d100d0111720f00d03500d107007400301c900b440d0860f440007090141c144001c100c0941c000c15018020900380c0b0340000c685064190314501c4801041130000701190110b440010035800c001c070a0007003900345515800c40e41e1070840c22030a8440074540250400e0f0580800b6103154000c08200c04600306600548240300e2312400418540c0d0050640b20a032140c514445c1c44160b4036511036680240741c0320001d8410404c61008954840c140380044c1070140e8049000515030070400816a420700e98 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 595638597 1250 595637347 595637369
    0x120302032e0b0f09040509030c190305070203031306030b0904030e0d0302120301060305070215040804030605180f100b0f0916140304080a1205062d0402070c0e070c0c0b13 75
    0x24000a480c2204d80014500e40e020343d1811010501180000090341c1e0312852800044c600000644e00141070010541700403070610900340041c070010b07601030000d0080702440b41000301d045890001c00409407400070036603a004500050074840031950040305550000815070314140e0b030781607a1074220303e07000700d40c0c05104a5910100010800e160315410290040350b1075400c40f40342030382881c03200901e0741050f9401011200f08020400000c3c032113800440d031100c454401d161030000e02c180c043d8101030707205c1004e0a40f60050700b000101400707184220522454107440b43e92001c45150049024050b0141c024044e003c0c0c000c00e80c52910f849014407450001200c80181e450b41400d1608103504c0d009030070200085500b10b2507080a100c02c40c81414410344000302400c0b00c04404210541d90200c45500c0010391480150400403103031102d00040c4030f45807007a02140710f4907103400d919001c1c2e00401740c010020030036201504800720340402424070076548040342065840405400e840240740320355000d000120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 595639847 1250 595638597 595638607
    0xa12050d06090504052e1805070f06020316060e031201050a08010e03041802090d050606031c020c10090504140a050708271c0f141908090a02150403120302032e0b 71
    0x1a0401d11401141e52180b41121000c5862b02c0407003118062070f0207213000590041c8121020903d005000c0300141d801603e000605019000031982075910155000d038800c480c10004100905048412800902c0303100e0003000040854240507071240718a02c214108019082103150385c001d03240d412105000c0005003007170001090f618244d0b8860004580d224841d01403c8268001c1348901c0d403803003c0d11003255000e0801c08810501300b024003001092028104080d0803008034041d190307442051400582101d09902c2d91401a0203601941c40060820080290310b80030302c41110380c030181000107049450b421030003005141d60180c0c0703814200004070b9211050380c80038610072a001007080c48184225554507a100d1080316101c2102d204100c80900b0648070207079003a22492007008a9078000140b8416a0700d845042c4d00090400c00649102814540000800708204250b040d1071002000141c10194154903003001c00394110307290411030708001d04040c0c6800c0140864180d03400050541c080c00e0035110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 595641097 1250 595639847 595639871
    0x80c0d0e150a090309260706200309011b0f0204060902071217180f100b120705060d020a0302120405010b0a060e0d080c0a12050d06090504052e 63
    0x41c580080c0310301c07814203512012480c10440750180320b2142d0780580b24011101d24101600348007103451040488102181c3c030701072100020034811a001014903996460398040d42403558a12300c06a41c20ba240f80c5d41c006c02550070f050360001e0310443e8805503501c0741110200c403403c007500b450043d018002d506c54600380c40824590029030280001900644001d012a45a0202501e0480f490232032102c644001d0320014200e801000c81d0710300a0760b00e140030740d5280c1d000c804809240c254040a003c0707100c0c0c1c40b0010b8811302d042400e1a00d56070003e10000b0120740c0d2034100428a180700d04000381d0300903900000e218244d87c1c02501102c8210242881c030450718903283c10424028902c024250303205030b010840c00500c0310310a0f560713031100240041624a02e906030344d5030114198003071500e4940761b024071404a1301062060b0004c3d190b0f00d00c551100382daa842d8420448085903c1500700c0c4190f41c1c40c080a200108100050070310030701390b41d03182640c0c40e00310700040d070f441c10074400301002e0901342841080184 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 595642347 1250 595641097 595641103
    0xc110d0201051b030405120f071e05010e120304080703351803220f1d01060f0e10030b0a080c030106082407140f0315030715080c0d0e 59
    0x71a40c902c0404034002503103443c018105210036030b03002d01181c1c0445e1001d02481c1300c0d08020034800d03e030400b40c0d500d0100c095a0b25418411502048218240007408403400c2c0402809412a142c0d080e90241c40d2100100d101070440d0300000d00007810040f13020407460f040501841040380c1c040f680c8004d100300d49600b170b0180076111484100d040f00d401403280101d8483c8030581031202e20103524101641c00c1901c4030080b251403a03200390b08a0440c5a11280005030601d59008400140612000320014001a4008030346000c1d4180d001804010840303d040756450340c000d003140c10f1900115118000c412030340358101c001e030040c96206580050703260000601808001400f204190081d80240405a500c5a040c0c0d19040c003005800d1007032900c52099510880e9620790f4540c8000780341410081002c00e2002c266264000310f0380b18419020002c00d0005036132007004540400c030021401040100e0500000480200403007009509019000000c00e605000d014107641d140781c3e00001c204101c0035001003c03a5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 595643597 1250 595642347 595642351
    0x15080a020720040c020606010903080c15011d070e28091806060803070c0b0c030c03070b0403021507020d0509040e010213030320060106051c0c09080c01090f090c110d020105 76
    0x1c890307441e00713805030101ea0002c54024414103050f12401c060381d1440d119008154820124000a4003550108048024100c19054040c104666014407202000712200140b0200682404180103aa6180c82c08139541c280008101c00345000c0145a0070043d035403508083d988940001c0c2039203040c000282d081e180d0001262042a006680910920350b550520310303103a1068103000340c2a15440202030081c1d0300032000500150440004aa14241100c190182941c1107180300f100c1610740c01003444185903040081c08402c240c4440d458955040080029558a0041a1400512502207900480c50303035a07501840b501980360000395501c0307202c0b138500c190300107540c00124003003101e40084285211400781c04840c21003421005180310b90074074005a6941c0c004080b4051003840d5960000440c00707060080b032004546503160709191a0500e044c060415907440c2d50300741040241c0f03004011000302c41c0c181e5002c0360b107004000108140d1482d07088507a0417201c003900300e0a20030056041c034100d0341544014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 595644847 1250 595643597 595643599
    0x216140f1005061c0203030705030f07020406060f120b030f06010306050a1103041a151306080105090a021e0109030b0702031215180601050415080415020415080a020720 74
    0x240745001100040d40454505a400d140c110100081c8007040c00b031090003c40d542c6000034116824a4010b42e5828078690064101c140240008100b10046041a0040c0b034058040380c28031884064108a000f819107040c7c04070340318410346903030607409603840501445001c203110100303885603903031281002c10280c1010b45251144901c0e18200e40c0c8810004005e0300c0c05598012181000500e03010302140440001506076003040302c0d9a042420903603501a0307502e02180c001600490f03110f242c6001c1c0c50850300010700505039a000300703c4042c010303501c1101c2e0100c030b02841c0d50030400a62112004942d150f940b6000281082e2000081c401d886030000064a10300e03000c0080d040c010750321900100101c0d480203440c1c1c0c2d00722a03c1082d42034045051409107622000c189490390910381ea4824001203d00900601c1c00840c40e00c006000030700030070005044000d0500c49041d4070b003e10f014103091412905031804010010f15401154035107010b40c040303d007075a82003007841081050164071007403500302c880152307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 595646097 1250 595644847 595644853
    0xc051302120906040803010603090809091807090506061608090907090f14010c030e0d120e040f18020603091204030605090f0f0d1116060201051e10090216140f 70
    0x1e0b03095000001d0980c0300b994022855801c591800d5802d0303014142d04042121216014000b040941e100c04401512a190341034044130225040300c8898100b04091304025409420303d420070000c0d44a0b081284d841c510080319808242e41070741003810031030050302800c0d58891a16401d210392036522007100400d90712980c0400802c103680322040401603080c0300b2458045000044080c01190061040503400000641015058001640c3d0050342c3e150381400940880d01045880000d4240380c811030340b10b61200403080004901190031040c440e424014002d10440c80007000662046081c00012550b44d614410340d600d55440f480c086000d0a01120810f413203101d0408126000500000d560170f590303910b01c1c0908400c00c04154101d565060140d11a00300c0c0c85615410034001005104803001080b0315800001e06040404010940d815100000c41d8000c84d05401d11444112a07605182290448140141e031281304c03400008a080107800040c049521040700381030f84150102d040c1d0307000d81400e070039 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 595647347 1250 595646097 595646101
    0x3030c020315040b04120216030510060f08070510090e04050303150303030735040602180a03030906081e07080906070318080a05072a050604210c05130212 68
    0x444040750000300d40180c0311251134404a8080340c4400c69000703004000b0301c103843d01d941800c00c180c100300020781c0c003ca40c540d11205125910708003503c1020064111501024891480e1244541e075407202c83c080c0d180b25580d0034601c0035000e03001e124a01c00600102c901c8444d0f528041c18215183d8108480043c0c282c9400c03010203449140c04801ca074801c100b00e4540010034540b503400f5002400f0058503404070185d540f0741c01404c0541000312644180d02c40c250160341c070790707100440b6444640c1003c501c0d8090701c04200c050000030b42120607402038401902e000000d90b0f40b00c1119140c4011a00340b0b0100904800e002e00c40601d520104580c401d0b03044408559194813582c02c110120380106100c54030302c103103184030440020400c00042002e51490302d00941004019194181c0c09000818003266402041812613504088022640c00800d01100c05070305007480d00b050407501e020000e20781c404444a680e210400c00007d4040c1c40e02030400a480016010300ea046050025805018042840791042e40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 595648597 1250 595647347 595647373
    0x50d080d0501150804060902060d0e0303011e18020307030603150507021e10020f120f09100c1709010f050106200a1110020304080a0c030210020c010918021303030c0203 74
    0x1200e034140d000107070344900e8540d8440c0c58186c02403100c84070403a44130600304407201c002e031794601030081c0e0402d410010710ba0741d5250000d640010307000310000074801d5202c500d0800c240030780050303c024245210304001d81e5a640f0030798118001c00c3d250300700601c1000c62064070203050180c1c2d44903500c140115002c503424401d16900454280c0c0b00d5000703551095001401840808a454010307180d95400500d00d10f04007a41f02454011400c011524952280954410002111401c01c18010000c00c410405c02c001903424400404500c807045182504415070000f15a40d8902584900402400804100859615aa8018402d11501c03540c4a90030310500444145560702103051090301f0f03804056080f03990001c03005c0c00400240e0480e4003041d400140710006007900240300140f0098400c180009041e819441000845202c00780507004660202c240030a803a40c104136200305654003480003021313110f14403000802901c10b0300840f03020503056920020405801001c42c940c0c0c42d1084081c3c0724010308503c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 595649847 1250 595648597 595648619
    0x506120118090c060309051002032d0603030403030c0809090403020705012703020906180405210c120904061706040507060f0801141309120806010309020a03060509010204050d080d0501 81
    0x250b0b01a045510b22041004101d019030300c200304041c820815521000c1050010808a820446288545031025155800c2000c002d107811458910480c200301ea2509004010a9484c043d40c000201070103034038161407061159100550346800d000502951444c0f80524000b0341b12122784c400d0501207410300c1d1030318202d0006200f0307031100d880040d404580d4043c5141c08210703110501900c06c54000c00c030340d500c2c482009007820400d881240940c00818040d420011070304469808141d1504030100188911200041701242000b00300104000154403460310b14000340043c006030344000ea400b180b203920004034003400f14400d44540c2c01482035070640c0f42c0d6640300b0340310700d10310220380070009140e140144400c11043d050003840c000c0150050307441fa1600b0702010b0880d42c51403c240c03407a030102e0b054007180c143d000a41d150b200c0c1c000c1c030302402600107079408140c1000d100d00006000c1d03130300c5000082d5a90302c01d40c165001000300801415a000c51818203248680c4500001c4500c54140000070406030750744 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 595651097 1250 595649847 595649861
    0x100f0f03080f0f07021509030c0a0e0a05090c03010e0c030d050a08010b0d181a0c040612021b0a030801180b09130c08120408010b0f0105070b100506120118 68
    0x4501c519241002d184035a140c2980a4900e041d01904180168030150300c0f60b110200d805d204100d907141e0344c3c00a0310109490075071010b503801d12400214905024003042d01d501e003900a01c11210104013a19500c0942c2c2c200b40030702c0d6519400d0740c03826984000c005800240c0c51007940040c0c0548101440f030280440b0144100e2a2880100300301000420851040100410a45d094840000380c41325107034039204480c1610358010744041c205c6a510f00d01d00d21010a0070360300b20001120300b03841c1500c0c1070400341040844540038840941d0104503c0154210394410041c2c0054450517035000300c405140280c00d440d0b00707016010343c00d0400f0070805050b01241c0f0840351310a500400900003540d802070b09804507000000101c0e4481600351001502c558200880c014070a944001151110704181c80142110701461042d4411014020000d02c0c07039811200b01d0307000641100b400701040d59640896a4411041d60003a034226200241a072030750031a909029050781da4241035103002000580c030f92800e507008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 595652347 1250 595651097 595651103
    0x20418020307120816030806011d0f040b06071e0308091519150e1602070f030209041e03030506040b030d02101e020c07140105070305220e100f0f03 65
    0x800003060080d043e941003c800715611030040140f50401c4503109541e401c2c5110021400329184000703020456801c10043c05081c0000422120b0f07420000f400180d82041201d9003902a6a480312142c01d1900c81404890156401c925600ca00d010710f03103c245044800501c2c00e60000312800d000c40c1490502240c64981000c2c0b8400480203a1520100300c91011200c044ca40807051f40c1e41c000b41528601559014002c0240328880c01e080e291840c0c0032601c1d900509075102c00c54005000074441c692441040c0c0d41035940564410815980324030b0121512815441c2c0c81d003540c001444903a040542c1034000e01d02c5401c003504c1c1840408986801d0564480d03105440202503001900c14590100003507101150743d440c600c181c0c1005040d61030f006822039000d440b0054054201c0c00091001304041011031a00800c00e182c0180303411069240100b1500414418036001c0108200100380f110750201c200c000b40070610f101800b103003001d084d14042c84000703119442d0000e607088400291503896035080f40482e60 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 595653597 1250 595652347 595652353
    0x70f200c0a17210903010509060609010b070336080a170a020303060d060f0c0509090c030105060307030e012009121c180816080c04050705070b04020301140c070204180203 75
    0x1503a180050b25030300c001212180850f006000c455403d40e02405035a00460650340074000383c1c100758040c0030129105030800780415108004840000398030411664003800c110400d1900504180d9460b42071903c00181d04411036420140410307090004a81502c030b1503c01c017006901c20751002f8100c11741d03005041e06900903810070700010750542002c002d61020288210000101040310315044411590024180e00009001043d0050b0a0500b808055044808042c550b419985040000b40a40c40300034841410191140323500244c404007500901e8065043c0c1b608180c0c05075140c46607c00c145c0090801c14480c8002c4252210101400b09004964080040032660b08000481c02520f084070309090031106601c2c0040001880c034400e104410701482c0d41d04000c1181c1389410b072082d15001c2d01301c024a100d28a89400c0c04500c40d0048126032246038407085c000003540d41d40c000079005009094414040000d48002c20a000010038020180f042c800c41b41007121070a041071654691054840007500f40d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 595654847 1250 595653597 595653613
    0x60504061a090a030602160b1003050c0607031107170c010f200307020a03060b0901090501060e1e0a0b0c0f0a020a090506062104030e030c0108070f200c0a17 69
    0x140c256002041103000141c07481e9022a80c3c5e580326401c0b684008109034000c01d901a0b01001c10000f20a80b41e00b0070440d4682d609164110b884130b07900c0780f0314118614841c0d4000908001010700400049014032000415241100da84400d62001214513805600300c5004000f110304407503007e08400e944144143c4d83c0d00280e400a610344001280034103060009510007804104c0c0142d540c41c0c00070001d18030882c0e01141140400050221511040c5c100d21403442c285001801001c0d407150100d603020384211803c0702c03d155002040d001e0080ea2880c910f4101d20101004128208940300800007102d00c41c2c102c6201a445c0301f055521100044c0c0021740c006c84404003007100303a845030003813034111000402c3d20780b0f00080003000d44000001c010911410700b854104000a05070080306080b02214298050302948186000003484034100400039000d1100e00807400b41000d2103500c0441501c52440d02001402c010300040546c0c0c2c0c900031071042e11070b0500b80c6c40850301c0200c00e04148688000303840140441c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 595656097 1250 595654847 595654889
    0x50f040203280e0316031701060e0609010519020606030d1107030807140304030309050f04050601120e0705060a02010f0e032a1501030f0b0f0709050409020f1008070306050406 77
    0x2c2805818801c030095103c00f8682e6601d4010300081ca41020800d07003000c0c1c00c0c9920701d0003512208150481401501d840c20040203540c1e0031100c2c0905a850860300365035203a0008e00140d50b14091040340794060a92240051007564001855030700840c4121700301d17610260043e60807241031207604061078081d002501d0400002d8002c001604026201e0192a1402d0307070240c145601c1c54100b40d1054001404036501000281003001c3c007501040c60640381401a0300d080000030b44583d809880302084182c0e03c4010540e00141070000001401c40206001e5a0b4010903100901800308589070075240e601e00030f201130b00c0443c00003c441c000c2003d0304210420003503102880c40c1d034401c2402201181d010380000c0e10003004420340e60901861054903d00408602418400012900100b100c0b0702c0310441010310001603044020f0a0841310308680c00728400000c0c1c40400c048008002e000c603001721100b81c1c12042150011b02e124420861070341e007009034a90b603404101c250380842c4504101c40c2600502c0c0c1d210 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 595657347 1250 595656097 595656151
    0x7031e20011e0b0a0e0c2101090c030b151c23010815010303050703030f0507110f01090312200d02040303020609030304080301060e01021c0f0e09010503030f25060501050f040203 78
    0x1c000b00e40c24106040c00ca0000c14200c0d0004034140802c80080407e0042c130030b9090304c0c4036400605c191071a0801c0f17950503050108101088586803000301a0000c100c00381801300400c20140c0c0f24090701c5c400d00001d180030754064400705841d4007000100506034004205a400060038650300700c0d00c41610400c99103907480c199403a50090009404050321150300c00250901802020b014400c0c0e591000542c5d5241502c440c00c0c005400300c1d180d001d90401c0e0f03000c40070a500c902030248100b441c800018002010b40480100c1c450626000f00006c130303002c1810b80442500c0d50282c02141d000c2e0302a91004d66a90300043d841b0722081310014102c250034001400a24070607034109401c1c00060044810f1405c03440844141d94120321001d000050b9098071283d8066402078038410030f09415540344149504120010b5213902480381d68043c00b680c00700300741409489940100300500c15500306000348400f2801c0c03000280000740241c9029200c00070800a050400f1700c2240d103d17000001c0e041d1400030110009041d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 595658597 1250 595657347 595657351
    0x90307050607051908040e07171519030b0105090610170a11030f0118020405060409050606040e010b0901020118030c1b08010e0c120307031e20011e0b0a0e 68
    0x74051040c01005058030701c0001e00101c4c400d0140c9103180d04c403481c00f400b80e010324500400e680b0030032400c910401416402c01124540001c2d004102c960b0028040e80030546038040c0f0462426041c440220010034031105210300c074142c401c1510030301555a103903400e110485038280b10300340c0055000b41504201901d400f84050b005444110003007041d240e00e00505034a82c00c00e60b9480c84859049004010078103d544107514251030f041c1080d030405207042c1c0012854020391103071080c4182c41d0000a2035a90300d01c0308460140c0080d1166048a50710f450300c60722541c2102c049103001d9840d1902034549000d1500084d010554507582d81203040e8260313582c11014140f4840b220b80c42aa0f00200800c01500c280910440080450028800d01d40c4140420900044030060584160400c00a55010950041c10505000c45081041998035080300c030480303c0c0401d050b4041c804a00000c1c11100141c019000011303100080c0c0060b2003503160203690340b000c90742c003513400590003c102503007000540c46075141c0e25 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 595659847 1250 595658597 595658603
    0x12010b0d0308060616060b120f0c0d0c0906030f0611040324110c0a1106040303092706030602030405060618151309060b213d061802090307050607 64
    0x43c1407450380405400002032685d0200c80d196110092004503060158494201080d02401064003880d4003054585485110340707010b0154200d60713800c070248845588540001d010414042100e03581d20b081108000d0f94041003255440d040400941000c0101020f0b1401d80c0d03002500c0c540010414080005051846860310340e11a0b00d4004061107118000080c105141c101070250888015501c2c0940c0c03e21030010310148144001d100c00d1000c01d5000c0c401000760355890700a04205c2424442070250701400d1207107002400d082c580c000c42000300b25000b4500491040d005c940c860b4488200700002c01801d005182c0d43c2100c5140011400740342c40e001e00d200c01d0b5019151400725000c4100790020340d140d5080a454590b120707011941c0a04111015416298a54210000108280340700c6500d0380d030301040c0158400d001c034078103510851848140c4101c0e19034200480c1d41c0130040c0700e400c0c0043e105038030442c01c04042016007400391102c64001ca98160f000280030300b072100c0c10700c0b0410a141c2c000036429 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 595661097 1250 595659847 595659859
    0x504050d0212060c0306030f0319110a08070c14040b0f040b0a03151406010809100b0117100609050406030f1509020306090c03061012030f02011506050912010b0d030806 74
    0x201400e5005101007802444512801e03550f900e00340042c12314000e86844035100c20703032040000064110005500d804030074900e240151500314850041c529013103003980003034950507000038804200108000d02c20212042c10141500202c10101040121881ca00800303400c0700d0342c920103201070318059000050181c801001c0e20140c0d6200d840f840d840814500c62100b81030340d1400301e10031034000c0115407a40800d0920740340540d8a4a4503112b5201c0520614044205855200b01e203c160700074260440500d0705800d059809140c400c0804031130000a200340000700d038040501068a040138010f107000d481e0081981c42d01d1a026942d007400400110858041e83ca40c0d42e000e18005a070240b01d482d00a2416000070702c034108010b4100f5042180151001b560524860000c00c044c0d000e154000b05440d405062101e801600d08074180e014048099004000041140c03010482a8005000d415803950550311480d80004c2c207012603080312114000c4951195070480d141c40005d10900e000c1c0c2d8060409410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 595662347 1250 595661097 595661119
    0x6170703180611190302040e09010216060504022b14030903070608100305010603030206091623031c17180312040c0510050301050112060506220305150709090c0504050d02 75
    0x1000c2c4055401030484002034000031f041001401c0845800d030080c149200841c0342c411251016107030320a10100051200d910784c0300160030342d0303030791207000d0510b800e003500009011881d0351400c92881002c00089a0041254061148000e4000191001c110015005040e01b50030000190f0b0b500500134030351407611690b039101000007003083c016007000b18820340090986003081c1c007502c2c0c288036120943d03101c1c0c401d240b5030400800382c1a2040020041050325148020100710000c0707814059001100c41c400c540c42c6003142c00d0503901001225007011607a80441694a4111480b8500481400481040d5106000b00806040080c0d08103402522819090b00c0350750f0340b007020400540740a00b520010641c04001084596041100f64580c400d80d039004106030780c140313000a8894001d4101d0007918003000c11340751141021403030500d005950402d0495207124540c5000c03160b080000c407203620000d071548800244400d85400303001b1138218140c9803a410541004e042c40070461205c14140e030b101d135807c99 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 595663597 1250 595662347 595662367
    0x21180a030507062c03120c03070b0108070612050603030702040e0304030507091a0303070f0b060a05060c010f0c050c0606010503072109020a14010c020415030c06170703180611 77
    0x12210b4020300d810748690304448a00e040000802411400b0340201002c46503c0c2000c9681c00300c1da03049a0746a00e0305a03501c450355120001c0c91800f90060003042d042c0c0413400403490f2000001c25004070354041d55a20b00c000d034a0b00c0c4c420203035041561401d804d43c1c0b041c004c5e03000618280c3c2003400d468564804032401c050fa640c841500e40019580034402c10756403100c400c0303003a1000d003090828030002075005503e015800d9884c010303130600014018000896960215440380c3d10540d46000174000107107019140d420902d0024020064804030001c1d6500d03181101c80d086000d14192000c565490f0050000c0e5520500155907682c4000d006400f0462022102a440040f12010040c0c074034000e100080d2109007071050003c2d1f1010f58101005500a11034100010ba0b4016000390205a040d035004c01c806840c15884120080c0b6604010000403c0d1540401c01e59484000c1400103604517001005644900409404482e0800a40c82c000120010000c002c200d00f5000b40064401d000d80380d61802080342 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 595664847 1250 595663597 595663603
    0x60909010b0303180a1401080f250905030706030e030301061b1e021305010b1c180510050606030105150a0c05060c0a11060c031b091305010821180a0305 67
    0x8984064461440d1000e2122414150305d00c0b0041c10080e2080400b8035440c1c3c0010b004c118000703044203250305036040000c042605074816841c0c0819124203141d401440741c80d001d0107915080c01018003034400c4140c002144d522a00600d400124800d01075403469081c200d003101c2010b019403603102a50b50f17030401440090480c800400c0f642c2d4119510140f558268410410725504c900351074101941403070011b108000c0e1880c01c40d0034401c0c5103003102d2000380702040da142c0a070a902c807032500c8503600c00050344103000c40403641e0305e080741c54200c0c104282d07a5140c0c20046980000c0c0140c903013010100c1d01c088403820020340106050092410b2401e1109803950791103140401c11552102010404190303004096000342460703021032401c070054030f05460500c0080c180c9000c000c08c524516480300420548400c41341048810080000d0650100c00c410060300101405003031103494002d1044a49101964000301428221115100034007803400014032400582221508401c90b800281000b0000000d4020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 595666097 1250 595664847 595664857
    0x3080a09080f040509090115060c02030705030f1f09030c060b0414010602071703120c090607050d030b0117100b0c010b180f1608060415091a041b0503060909010b0303 73
    0x103002e903682e214284002d00c0340100024040407186c2e030400d441c01c00030050404c0304200f640d5991030840d2000d09240006850a5400e0f4007094150140440c850401030740410500383d000e0b00c084141b68420400c0200c0801c40340034000250000f000380c46100d00141c3e050b0841c05c90418010300220301d03407451030102c1e91034140a90013400540d21543e81041056141e2140c07600114201c0c0181d802c186042100540e0440001d0812408100014024059944460580300e00c50780050031205010800a030140007042c00e903028034007040547d01881201602c01d8110b42c8600d0740303014000c8405d4135100254005402c56003030100035540381c040304816515400c900f08078210b443c0d00b0919030350400d0010400785a00180c10300c010403c60b600c40c201c2d041d4111100b1504458140c400080ca83d9880b202065031030350b56045442e00e00e082600044164101c43c00220030002e048a0410054042880036442602c5514140c0b010440500c0002c0492038a00442640aa480000890000d856000090a56200b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 595667347 1250 595666097 595666117
    0x3020d020c0601090f091106070321061e1503050601030209030d0c021302092d040c051306030203060a052205071205010b0909340914061603080a0908 66
    0x8104010811390b8018012402801c0c42c1e020b04108118580d02c1e030380b00d00742100500328004d0400050450401d4400c04107001c030f140c000e1b595180801412105035000c0e044c039110300800404231501c0c00600051180f41c180c2156259940d4000320003200a007500580002011035050544c02c0c402e402c4580c0341401303100d00c140a5a0313a030400004240c4100a2129000d0030410541481800702d4610b50715440300074200203c0702c01c04295021584047c0c03c00e2410030b216410b800c5410116550039603a0448013401520034420161412191a11001ca0072804120385c040d900c01e10021042210341841c03c0f0596043d0301e401d030451800325005440c0025500c060708d4003000244200c2c0148000d151a2046602400048003407920b8400542c000a410144c00380c0346c101d8002d40200b6400f0070340b00f80005441d64001110310848441000400500101e40e01d2107041d0460944d660b0740015854031004076603d403076544500b00c0502403191004c4a8008008021605465032561744a000c01c4030b2001410003401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 595668597 1250 595667347 595667353
    0xd15051504050c07030504120f0507030609060b01081519080706050406110708070513090203060705190e03060f0718031209091415041d07031202070f06030b0103020d020c 75
    0x80d0800501007202d10007442404081002e01000e0000782d4841d04071403c86100c01200c0028007002d0400020424540301c3c002c02c0c5104c0c5207000001c000c5142c010000c9603000e920b0400c09941c0440040d200d04100311403013548050312500220451804802a024281d451800c15400e1a266800140b42c8030303140e004400031402c003082c2002020350001e040600c4460a2018045451034421420764131400c030300420384920f10802401c00c0705c0c0c44075801100c1440d001812101c9500302528054a9a48400035001001c01d05000401c04540108518040d144002d0020801c0c3d03a5200e0200c0b5649502810038410061540c0f03101c40040390405c4400095030248424003403100200001800900480c1c1c4840003c1c0d05120401c5132075281c0c01e48165002c00d071001c0c3e60080d141c02707000040052000c101c044c80315207841e0742c0d0f50400c2540021010162485056040c0004040c20010781e030302c103450311948030182c654400500140d8403e030002010207034103040260030030844c440314100b641c009010716002a8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 595669847 1250 595668597 595668631
    0x60e0a080706150f030c1401030b040212040201120e0a08210c0c0d03050c1605030f13080c0607022218200406060c02061804050903070b07031503020d1505 68
    0x4000c03121030f200074400c002070205501e02c0c642d1350701040d070024851082c1c2c8080d00c039079040b801e9009030000355103070000800455403516940c3d154800a14150381c141c0c00a20ba05914080d0203855116100005c1c0d009802040856150380d0b44141a078008a224910146070900610366818080003260060182100c0e0035203920346050f040d86001d00c03a00e210400c05041106005440d802030045503450040364070842c21a420701e0134218030714880e101b6060030a4000141074101400e60025034803e42d041c49058507900f0f84d24008110940c010f10308080d44c80803c032200300700d807416840e00700780720a911040c011945400440303180c165034440340700a440b0030b007000311075580c07a01030308000c25030380c0d14100c0c0c0802c19181403100042c011151040000d00580e00064910030801ea140d400c81885080100184044c4c502800003540743c0c2c01251085071074a04040202e06018000d005282d0708944400b0144040c511310b07004c100510400c80c205039034041c400313000100d82203118060603110316001d601c030038090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 595671097 1250 595669847 595669871
    0x10181b03061404030e192301030e030309030331080705061f0b0a02030c19020a0911070b222603060a090e030d020a080a0501060813060e0a080706 64
    0x30360300750071003901c0c0300342c10200f04000a03401001c844401d62094610500d110100c1000703116450071500b1a07003403020248541c007400a80d001080c14940000c1c3d8041c003201050148190740c3e1b000580e46c000e03054100b4000100c03201004052450001000e44403080300145080c0d031420300d03154548040d5614040090002d0a222003006681d07089401d1210322501d540100c11320181c0c030300050003499000c0c800000c0a110440c82041900c1c05024888141c2d4110510221380d42c00a02c00c801c8102d00410f44071030001400c89242c0b0604140d6030801c0085844c20304156603a680d0814010400c001381104e50301c2c031040160220903000c00181c40341d00982d0b1340301c20306541c2c4104201403210928a200003001002150380baa080d440b401c9030204d05001c26030b00c0c4010140c60840c0036002504202a1000c981000102ea001c00c209029a400d42010051662a180c048480c02012220504d041038225844d10015210358131064207504101c1c00e032000032540d40e07218840d0f98040601641c1c2c00391988100116 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 595672347 1250 595671097 595671101
    0x21213030b160e151b0601150206010e010b090a09140a0f0606020a0f0c0b030c07030905010807171506040807090b060c100b030a0606030b070807090810181b0306 71
    0x40510a00c0c054050058203100400e0b8031424000e43d07000340c0107140651452020041030722103020040b1155410051315116255030b0b40d409100b4a1140004080404489400440c99074161003211010043c2c80c8e0030b00d080d14110340e115041a9403c00d205d290001829602845084012040c850070801c050819000c0ea409513401900407205052418004000d8a9000a0101c102d5540070344591035100c018200300403040c00e02d41c0b01e81c0400b04c000042001c4038200c030700102202d505c40e07107a145084da100d400440d201041110200c0100340a03401c4481103c40ca00302e41c56019103c24400511444030b0b00100f0740303980159000808a0b8010b03401480009038a00441260f55410780e00c0904140840c0c1c41d4550700c0450340d03044502140d841940900a81b0140300745034500b908030005001080c1d44e031900c2024550300b26141d000061402d07021401080c400c81c110400c5a41e044010545040700108410003001a0071808040348d022003c5180042c0705140c03864a001030005c5140c0c040d0340f9508103201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 595673597 1250 595672347 595672351
    0x60e0a09020f191e0804081e071a150d0501060506160203060105100801150219080705060f0f07050c01061a120109090f03050912060103200406080c010f021213030b 72
    0x5000540750701302c15800744054010b01401c418034110040e600c650034007000f14440c1040302e456000780031341843c900403032100c010050640711349206003c18001e80320b87c81c409042510000344510031032a0f1180e82e0714000c070419506500a030300010308195140002102e9074003203e1403003400c0c0310300403d4000b58581444814010030381034031030101281140c0f900170089941406104000c4949400300c5869034420403080240c10407888150741d54400a013080d0583e41c000f44400c490034403e060001d05920b105440c0c0310b004201d902020400d9845240007924150044100a1010340d81c550f400a00441d81400d0700744032074554580301d613a40300b44220900301c603c0e050300180d08043c1084071090000b0b070215442d51200350145080c03500d43d8510781c00142110200e00e880b06491066000100c103001030785102100c06d12440440c541e0b0b06260b00c0901003694640e2068800c280c10000603100d5950107400d500d0102083e40c815120709290007030300300416400c10108c85c0c03606600c02005204125040c0d000f01e03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 595674847 1250 595673597 595673647
    0x6030c06031103100b1c05070c200108270a0b1611100507052b0f2906090303030f16140d0b060c030406080a05150109060e0a09020f 58
    0x82d1841c901003105080c0e10640348500103102c6400541b55203500080c01e0460020022140d0920540c10100700c001c203c004d0003082038601c50145920195407080c415a510740c0c07400d043e100c6031035039170720740c0703414002414120500d481c0580c0700c07052000c14074002d00c9840001d81c4511171040050800340c5a41001e02c220302560424801128405400041d000654040341c0202c1030f0040b80caa940d00740103c1e0709000f041c0a010300e04c07907250302d940c011456010f000b214501d400003003009280c071800003080650306480c04180e03400e092080c54188011040c40510031140000d451a440c041145020a1556104440c0509010362403414002240a5070100c428111110b151440030900111050281c0e0320401c0d500d03074070140d40e480c004566034072440d01b031700c03460920709040d0398070380d591408081c01050044030721000d081c0c64400043c0c00929010700e01c2030904010782d00c01038000c0c10954117580e20705030420125807014a448000903c0344003800184007041401d000f142c0c0b0388020041380b40500600032886 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 595676097 1250 595674847 595674881
    0x1c03060b0301090e0304090c1e0f0507080313021f02070e04031d010e0a09092a030b070e0301060303031b0309080a030207111206041704030b15010e0406030c0603 71
    0x4100040c198000d503030545103c0c1e480003032242c3d034003440380d0f18501c540d60200d100c6034102040c0c0520303e500030360006003d010249080a41d1401c004040354060303941101131010660a100700804511914051075000140b180f0070600d011098001801803942031880056044408155144040d4103008043c014130710b2038101609410203a81c003402c4440700190305a120340500700d18403d560301c101c3c0303070f00200c54010348503052003600c4102074005031801480680d07120801c0380103403441500b600c450314942c0700d6251b02402d81900f0340e6071343c00c0e403010007802d40810000302034202445640c0c01e02c00e56008510a48001540885190742c050f28400b6900c0c00790280340ca82440400800c90046c00c80b040c1a56034130b8016a501b0303680c0360440c0c54407030424603950003124801e1a11841130380054664022030142e120032503032200e94101800b0314803581c00006c0c0300540300070118038030280b00c40941c2c2503104141010320140440c075010408541d180e0b84242c1b5140401030007003082d01c1e05845480b00d003085100c00c0f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 595677347 1250 595676097 595676099
    0x3010e090f0304081b010e220b011d09090a0c14040f0b0109050906131b110d12020708070203010f09060b030f070e0a290f060c06040b0c04080307051c0306 68
    0x41c140c490301c001c3c910841045035180c0c210708a038803a805140e031780040113124109500380700444140308c000220043d51601d2605071000ca00d0360048071402c01400b0f012005451a80103141840203000016118400b01d10506003508001201007610f800038203403c1c0c400d041a00130200811040e03030350a410084001d45811403640b40e03a64485c6290013510b40644500015446d000c0225031803c80012071031900a140c45684d04406070b2001864030a02d00300e6607965200010200416102c40340e4001680101e651050460071003403042d0080d24200740160108c508124090b00405c0c00e403100b0040c1c0c1104156070751040010070100e849044120072013035006184030840c1c480e005503220203a0041280c4084264000745201400c0c0d0418446240e0490a440c000f01088400152082c03c0c1d0302d20902c500c1e040118942241040825600600341480003400c0907201c1d500e4218000c040580b640640c19070400001c542080100f00404d80184602c0c0104049502082450381641100c51030300101424900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 595678597 1250 595677347 595677359
    0x70510051804290a27060e01080717030403080c031201090501121709061b0d080f0106080603070f180605040605150a020f15090f0d12020d1103010e090f0304 69
    0x19074000389011403824800f61240c0e01000415a40455010030b08004212800c2c0c04945200d46042c9900700705500184821600c846091030040c0d42401541c07003540c0002c3c002c021200400c0e5011130041301000c241d03450310782c03281c0780c188440d0f00c240d07410311243c0d00019506034036440ea02580b50040c0081d900c200103950428821a01003010000081d01501080046090080242c41150601c20700100006d0b0396111701601c07030007000c0045c803403800746014403410419505c1c0594a8039210b0030403115000c1103030b820601c0540d50488040d01a40c1c0510800901003080d280341c032030790030290032196540ca01d810b8544109105031406500a94040c3e4140700701041b0580b1051040740c02001c20303684103602c81d0707401030040380341c1841d4a04002c02c42c490f4803200505190008002d031b028161000582d10514802c4401d00d0b07852070407058102c0000e60740030740f11451803641c0e07001d00884600340e540032070650000c82d00c0c06040d410a80000501c407070f100d024007008a000304400c0d508800e0b8080a1420549425 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 595679847 1250 595678597 595678631
    0xc140a03020d050d2406020f010e1c05070c030506011406070203070311130c0e1203031005010f02240702070e040503030105040f0902030d0201090c050a0b0904020a02070510051804 79
    0x802d0890902502041010490249130041a841c5003444000101040c290002d207100d4883c5200d498091701070b04901004c0f14006008080f65241c0700070050828150840123641081031403859101002414400080018950041c10008500a02c0106015410100181c050703492000420703201e10001c0000343c1c01a02c0201c1c448040f01d400844403601401c83e200840d50070b0007114a0b8a00041c6007040c000d079496041000080000e03025a58910701004112290b41c4c5c0f480f06aa20101c1c000e100001080158801c03105102c8036050383c81560034100203c9000f4803000f05001440f00003c419004100300781d0b50410944004100c10310740114241080c0e1643d07900d0348418090703d40116110100b0098000c41a0400d403915a80036040311503080049400034001c0c03010b5001203440d803002050000e450b00c0c06001010544444000c2e040c5441c3e031450400001750306c2820440e00398001c5407070009182c0d451064085003011103450b01c0c1e58030104400590348188100c0c0c511441640ba150551035885103403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 595681097 1250 595679847 595679863
    0x60515060a08010e071e05130b04050609040c050c01062301080712090503070b0106020c091b340b1b03010b07020d1110050702030c0d1703040c0e070c140a0302 70
    0x1304c846800980c50704c4100f12070031901802d0420540f0008258401203d43c02401070045250400740b202105d6226880b80a01d4800c6204c1d00d82c2c80b800501c50301400d4540341d03115400752001070038800e1800d0507200c030503404c0d100d0b50390200841d80300120f0705408030300020600c00000807007442d2a54044c42d04040c0070b06101c204000c1d00300c07603e548001c00c074104441001241c1000340c2042c110329003507a64000c000d564032050080b0601409841c00814040e14800d41d07928903c0d0480003071141807401d40d180c403020f0003024000b8000c40c00c400e180d03000003c4140400700c0300124011006080b00785001140801c8805d41c06c4480b5001c038104200410210440d4020b0b2400254112021404500d02e8103060b114420407040f0154000008040408225008402841d145100387c1c01e446c8440210b41c104030100401c00d00151801661801101018800744001d541c004c0c80fa10946d810640c031150031072450502165824045411040c0003814414020041d069059920b0000d18210380c060350029140c400c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 595682347 1250 595681097 595681109
    0x5060102071205070801020f0a020c01030c1b0f1b06140702090711100c030507020705060f09010e061c090311010902030d1416080a091a03010320060304060515060a0801 74
    0x10b0100010040180021002800604025034803004100201e0341c00f80d000c02d521001501c00c50407105080e501a02801c0e00c00701c071a403210131540722400015001803074906401c40b883c407030700c00d4044000b5696225100b0390018140301c01e00e01c0c43c20140b01401d06940c40310f5007000f8120900450006941e40700070300307a000c41d441c9800450144500080c51070031031003e1141058074104198213071840d030325034025441690640e080301c04d0a6070340c4c428003140d403003910302c41c00d10990100000612540944480d0781c0042d0f0144c04186445c114210a41d0036000d06445064555180d40c00c110900d0350040c2c005d0f0020003120001c011188840d80001da884503500c407481d0a0041c2d2110200f00300141000b0ba071100e12070310501c0790b038a80c0c0b20710341038a841d400340b4080c4001c920080b80c08190400c140001d0f205050b40150528916400c41d20740d6100300701c1c1498913030000081c80782060450b44403003004e140038030300c1000082a10305009003100e8240101c2c0d049503005140c18030402c0700c1c3c00c0e072000b5001d0440f24 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 595683453 1106 595682347 595682369
    0x6040506060d05280c033012151502030403170309060a02160f03181a0f0304050c15030a050f040c090b04060e090d020f010506010207 59
    0x140d50400a0041d500807002991024582a0038401006000840030407181c0d1031740e00c402c10130348550404c5420440f0b0f481b00b40c40c03181070701000c41e514091846040b25500d44403500100200401c518005045441e4801c030462003100b0001e070406843c6105114000a03034201020355264024841281e195000c0220024403034501f40550b4051900352002d400280c8480c00484081d4001d801041d45003211601c0110006001c01006070685200c1d0b101c84e00320141642419003071500940c07010510780000c007519030400384008200c0d0035815505075010703202c0c2c032035040081c680894200025005107145901c0040d0b5003452010754824011464140916a80c1c002071740e03070707514003030390300600150740e542042c032060303029400a000d03208000d48001100c41d619042280d4410040d261880c2355008016000b00d0241d045c845940f112814000034400e605021b00000c1da117406600c86c1d10380d004 = true := by decide +kernel

theorem cover : BRFrame.Cov 595503597 595683453 := by
  have h0 := BRFrame.cov_init 595503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 595503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 595503597 ≤ n) (h2 : n < 595683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
