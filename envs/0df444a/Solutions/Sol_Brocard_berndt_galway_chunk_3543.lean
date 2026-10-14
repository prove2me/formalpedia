-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3543
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:57:59.800835+00:00
-- url     : https://prove2.me/submissions/bfeef5c3-ae4c-4875-a019-4e62a32e24d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 637050359 ≤ n < 637230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 637051609 1250 637050359 637050397
    0x90203010c091d04050706081003060c050703030b0924060702040e160e0702060105010507020103060e07030524090a090305040812091302090306060d060f0603061e0204120308041106 80
    0x803400c800d141c5a10f16580200821414240d1342c40c1d130344890307038041c01050195120000d00040640025440110340000f0240407100300b408000e000c42c4d120920690010381000032118641c14408010385c040d81c142100c8105440c0c401300c14610030450700c0c5140750b101d1002c0003050050b0703889004120800c2c001d00090503c88003104074202050441303070701118004140e02e042185194012a02c141111420300700740341d40b110b4510040b001040a900310b5111443c0090502c0240340d4140c0c8000d01c1099180d41e414a00d6240c0302032400c0480c0f5082030942c0c01542c0000241038500c0a4010082c0b5509c03904125051903222001c041c2008201c840c82c0156200101d5107505515001c0d003018400751500c0f10461130070600c04003080d1a140000d0405000d201001019000c00100e0740c0702102000308184100500c079201c0c078015010f041e9407c5592800b02110480700b0042c801842242c0c00c40780c07004106000310712641d50503110144000c2081d5600f0320312141c42d21103a110400180b6100502c0c01c1090300b5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 637052859 1250 637051609 637051619
    0x203100f0626100e0c0a0608061002010615051608040b070506061c02010c03121509200318011517060901150b0d060f060c020a150504090c03090203010c09 68
    0x55240300d45001c0b1107400040d40030750003596020400c1d0807110182c040229442010030542e074540740c19403590030740280c0101c00004100e940090f4490040c4000ca03400382c102151078400300c4c2a50002d010315402031400d00d2800e03800c07a01440c02810002d88520000d00c0d15401a203468007290015444030442d4040016040c041000a10090b40e2092084401c00ea200c858002c0400405522210090501402d190450249401201500e040c0b800041c0305100c121b182e03c2881c00080d0f018131600c60410b04007003c1c2100c500c15048083c55110103180b20314207560354031043c0e070701b40b400000640245569481d90202108140c4c10790b48060007149480d01951800d20a0b82c42c980a001003e41d00140d142420f488041110003020404032401e808995031103480b00107050f40200b1496200602003800c000c40080c0603a0024400b040c2903000310b841d050000d50700c021849109280c00442c2000400800c030a1060081c01d620041c4500c02501c0c00040b02003a40d400f281c21034a00c808443c01103600303010300f005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 637054109 1250 637052859 637052879
    0x30c040e160918030309060219210e0606090403092103110a0c030201050d240f060f0806130b0414040219030201120902010c0c0303091a0a1b0203100f06 67
    0x40240104a002c00098101c07031000c24003c140c4650060805444001c10b1040c04400e0701a500c05c3c000c0c003003c40041d034601d940043c003a14484c0d444280e015103003a03d59a001d200c41d00c959640707940440085d2105907500300030483c00c4c445c001e00440c1401148030010500c0c0d4608402ca040022100760380019800440c10040d000383c550b640c035212598003c50231400010210301000080313a50a080c000c0c0c8650368041c2c80741c09403156000c42d1409441c01d003885484d01041244110440e800e07020004c24441e03e40c02c1c03c0740c0f90b21403603c07001c0c08200c040c03000c07030b00b941080a1544038a6802d0503001408001a0340010107440c4480541682d190120090209624100c000e140e641c0f04851041c0c00300c146540d0004c0c02c0701100c41c071540d030b5480c0d94482c000c0541e4081c100703003101c0f650302240151200d61079180c0940043c03058010b015491548006564190040d401120701c141c081c1d48560308902c28481c020a02c40d0000002241c25009034040145007110f00e000d4131022152103800842e009042401c852 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 637055359 1250 637054109 637054153
    0xa08060a0303020c040f021603030204031112060106050703090b22050f010c02011b06020403050312070e010c0210020c03011b080609101701061e0323070b09030c040e 73
    0x40c0c4909003600003000000e800190707442050609480c080340158014090000074000d0a03d1070000804200c101001c05905038014810f42c3e1245141c44c50458900c02840701003e52400d205900382d1051006000301d034050000380009070b10a2400e00c03030468a03005015115001001c820b101400182d40813400c98201c42265400380c03074140c3d00700d2101c0c0c080000080c012403000030041c0c1400f1407014648410111208070f10b11607a0081c1c000c2d96070302d903a4582030b82ea035880800300040c1c01880d000841c2e1013a03c24102e09103030080594503d02c0c400c0a0380c00b0003001903001c41c4102d0542c0300b00fa40040310b6803000e000300d40d061b240142e010064038117084c07c043e080c640c2c0107100030b101d11000d1040180b030b1088000d00701d09844e007410117400c0d0301032040c0250b80184100e800c041c03410200da06062121140282815081da84030300044a00102420540d1a0240103900f490000b034110407014400c007c0340001415444000804488201030002c0106080b9101c90f11300710001c0e0051020080007100c00c80000d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 637056609 1250 637055359 637055371
    0xa031b020d1b030905180717060f010302030c0d050c0301050111010e25030812151c0210020c06071401050705030c0703031e02031503011a091303110709020a08 70
    0x38008035015950000d088038000d001c965081140401c101d0b00f030501c10700140e0301400703001d05800c4074a01d0f0b01d507080d01c001500300c8844000551420b042502c515000d4091400b0f00000340440040f03074800d20043d400307034000401c0140c50460a204100b4146124000d4501608000b20015602e5040c10300040900903c508500700c1c9a052040c940c07031480000400d0686414200c003241002c40003058900e0748064103500107016400c020030704d002201d1100c28400c0c0240c0d0480c06044100c5031000c140005c0c0c0d4265800d0007407140701d454a11000d4108110b0300c8607100040d205032049034681d480010000c1d08050004d64400000c0a070b414412502441040e0304810582400350031454218030741d102c148100c900003001c0545910364041c080158441c05450041c7c12030b001d540700d182080b5030700d03654224640154803c1d802c1611890304504080d00701424440c01900e92541c135500ea0103500d0b9003002034a42201040f0300a1110780b00d208061001401901c00388002598501c440400105004805051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 637057859 1250 637056609 637056613
    0x11010f050405062a090d080f0901030f0c0c1104060b180a050f03120f16210905010905060f0f03070203071103060f01290406030e060a02040e131104020a031b02 70
    0x44207000c0010301c1d441030030b207801504c9038556500700350012404130618002d005244400101d14984034150b80805840003c0c400c1c2c0c0e0410024030b810908009940c0100d842d40f0200d41e40c02c501d2804150169081d06135a103020f400840d00503a90320f1050059070042005103200c00d10f0040e0908940751081d01d020017400304885a6402c021b00300c0000b5181c03401100659a8054000b4440718105201c3d810fa13800c12034040c45135003c4040504200c401c03043e654140442900c1c0340c40e102c1c01c0d041d000304a00800c0d1401030b510070741c01038202014400306038000130601d00500020702501e141e0303038220700081d40f013911154060741d115043c501d048010380740e14060b101e02c01e4014504102c1c511043c8107500c0d0441c0c060030380c1417000008186c5211f502d218000c002c54030f289400a8042401c5405400c40c01084422504a440310740c0c6440860049018a018021410070440b0101304014000100d030701155001d50200c0c0c14045000c0006012030340b01c2c035100740c0440c2c0c072490032a0400e101c0381e000c41c0c981107447c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 637059109 1250 637057859 637057891
    0x40e0105010e060616050607080702012313081e041d04052a100504060905061e030403022803030c020a020a03031b0b010e0108061303050a0c0311010f05040506 70
    0x441407039002c0c001400980181000306007002214070038158550559084020303201e00e030501107402070200c601100e002000d9030901001020038680f8845c90540340c8401d03030982c4103e880c7c5032000140c0f50b01c0c1100641e149681404000003054801c0c40e44c0390182c034140000c0f655103103441c100e4144418881143d410000c15841000089000812040116034080100c0c0042d040401e03010000d6400b0700e40b1107900300e1a41070704c900544da0808005c10a03501140c44a42d111943d400411506210b0f1050201002c407602e10f00803072084461000e990468841d0047c0c132029a88011100140d405644d00c00310b882c900d04150800789509881441e950902c0d500c042c04049030107801007034044125100c02000c2001c403800c403203030030030b16810041c140541c06204110070b0350392200f520224840a0003101800e015040c045000d420404081d10041a45031701d602d81401d010010955904c0400041501801210000c40c160f80e0070a01c541c0404840c03603400041d981c20039007001032824070300a008900140d40e800b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 637060359 1250 637059109 637059119
    0xb06030c0409021303240b030706020c040908120a240b03040b0a06120b01050f0f0a0b0a03061706070f030b1e12030307170601050a0813051e0309040e010501 69
    0x24101c41c280c0e640030300c0c0540c0d07801854040c0707264280598406010075403012412041502c510030110b107038034039140c000e1000462040801d51224a20f209403005684240308800c11030902d40c0018060300d00031045203040c42070a0801180040d000c0720f070f40003c51ba407680300c800360780e00c01d108980c488480c0710380c03003c0c400f42000e050500d2407201a0000d440210684001041c3c0290b84c3c0040700500310080000c0001c050034a0080108003081c01107a206080030390686445080c0500c0400070808018010074150b850841c101c2005e51007003400c54101a12101e011610f407401c10204902460b01301e008120034505014000e002c4140d801e0031104040c144010017040c0c2d50381503080038046c01d00703130004a010103452000541c105010f110700503a601010042000365508941d014001743c45070007503040302d640d0f42001140c66215a400c50804034054201043c100031360944a47c203103e203c0c508544101034903040b060844c40503920402500e40c00021510314078182801940c3c05441c901c0001e0000c1c2d4105 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 637061609 1250 637060359 637060381
    0x1150608060d06091e060509120313050703020306040f0303140c0415030b09010e0f0708311b30060c050d02070305070b16020a0b07110601080d030b0603 67
    0x10702198800c44582e5142020710040b50300400420ba40840101418140d0800c942d26050030b12a00b620000e281800046440c0c070f0101d560b01c400001803880d81d28664484840b0030800114001c242c8103842154004801a14204211801607001d07603410034901d40c0e14a4020706032100c4102d0b203520314050038240b1801403001d00564040e5001c00c88808603070006000120010607c005081d948010140c0000803000c02207080640100d0f201c181c40f11050391407850903107020000381e409038521840900551401c8100c140d20305c449103960445120200496119002400d540c0031240a0380700383c0e10010001407100704000b04c505500c0020143c1c0c110030b034606010504480c08070181c0b00340d4403056a80310701c91103003040742c4007025100da00b1074642c039070b9003001411500641d0781298545889008a02c2c04030001034100940c0403035a00038062144140e0f50307500340b080c2c094046018007a140440103d8500f00b070000c01e01030b101d01001840c58654029000303094400180d003c1e8001c00c010002d012021801c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 637062859 1250 637061609 637061611
    0x30207150c020705060c12310303090e0612150601020d09121101141602040b01030b240d092907080a0c020709050406020d1406060a0c020d0512030901150608 69
    0x120356003501e540c9403105047c1411401c4107606148400003505560481c404041031802000084222607444400008895075401078080540498420203040080703200c11075900740c0c003003805040f02800d802007d00c8070b450040389070b19503c082c0070100104101e55a0401c8801401c500a1501c28440382c684183d0b00c2c405d500c4500041c091022018401c0900c0e40030341c200c080041e40600010703a07580c0c5c0092002c5240b0b201030004034851403c080c5841c00035882405000d0b0018401440c03044030f1310038460701800303d0031800c0040f00840340502155101d01e142e0b11a05060900412055403024201111303203403aa80c000001d0703150940e074201031001c1503602c0b6011561004101307100141c07600080a09034506100e0354004010103043c8020001081034580240c5007540d080e00c42881540300c441d0490301108070413200c494000c4010700460552900c2003140a0000c1e0028005031401541601c3c0c3c01d040101d00c0b8907000848000005106203480c092042060303041b8040c0720340d07074203c0c200300d03000b404110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 637064109 1250 637062859 637062869
    0xe0f0609180414120301270605190e0f250c02030604060b040e0109081c0f050106020706020d0903050a0b07021e0f0c0a050d0212120a030207150c0207 66
    0x22010403000041e03180c94810340c0322a01c2034415a085031500e850507400112000c0300c2070381c690003441324079003441ca448029681625001c051070054801100c17810304a40944c08140454183c0310200059143c40e041d00c0202c2840255110505030380c01c080381c00300d1900025000d01c1c0c070042d0320020040c2250014515602907080620762080c2051442c2c011149980c4901000c8d505010702c0b81408108078407036114160300a0251002e01c03034406500c45c0242280c0f0042e0000c0c03e000020411024020358002042c0d0110580010002c0d8003051460350a04890090b000400942d000f2001440092b8040010038000040303441c106c81c00b80c2c01d540c1d071581c58000d04900209039001300030110380c802d4020b0050a0782c07110180c254103419145440307219a19482c0d90000c038102e0103040000d5916041540200040d2400601880003600c11030b401e00c62403003145e0b0320078420b6001b10800c641c042402c3d58007c0c600002c1c80d40d0007584580710340c1401d0340149412059400c44034604064007190399000304203001121 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 637065359 1250 637064109 637064119
    0x40b040b0c07211208040b04060b0d051006060e0a0305070303210c0c0c0501030608030313061112070e0f0306040f061512150519090c0f1202030d0e0f 66
    0x5007007100100d00d00306032900b014420f4500d02e0a0140f11144100101c07000720700500000c4102c071048442654250341c1071300c01800f40c0c5081c0000401003090b40d0880b144c92180600006c1000c022521001d00f4150b82c028a40b51081d203a1208100c1903912080364400700100700e40da0104940342d560303030540d00e071182d110003014041000311404640540300030500e2525403161043c404809407039001004200b0940088810700700380d500224465110384107100984281d18015403864488211103550000c40000450301c1075143d0207403815a85032040603000000303410a0303009040c245401c000d00074034030200c0941c0c01000511071182055800003556a042500a1030142c01c1040e981081d5003d00032041441d508001e00104c00203111030780e05054008540510300008030041050464020340d0011359495500c03294034000c00300355200c181e00038200c09120360390031800540e86889030800c22005502800c1450f440e54100300035400c040c4404007880459140c68205010040b0006504071030300b022030350085c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 637066609 1250 637065359 637065367
    0xa080a0f0804090908120c030907090513170d05010801411e060a0f0302100314070915021609111b030307020f12030c07031206080120040b040b 63
    0x1c4222041110054510b007101800840e40f1802d058189078040c0405260028014000411401031707203090f28000c5e9405005003070b5080c90403501c000501805016400b85103641d140380c80005103000ca0005811004203005602c03188050f400c00c2c1110416131240d01182d050124030307081501190300780301c510038034650001100c40c1f051024000c0d4248101c1d4200310441310300c06000c184007600d070303004242d00701100c14402c503903440b2000e00c1000d4a5611900440750b19459080c030051504044031540c0030542c1c58001741c5a810200000080c020a0303c4250100b02090350900441442c11004e07030340250b0707a0004111050790750f0050b444038042407080d8a400fa40d00d8001280c809414030441302c0d40d0021140710300d070000241d10700a4403907006546c0c0501600c1a01e5044e04100d00220b0040a80d07001c40c10814110f0707841c0b40262080d03a10605045040060310451040701003a20712469001d0b100c5000005884142d00380d41c1d80b04c88881c52540e83c2c086070140003c100650b1010101c40580e000b9152036916 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 637067859 1250 637066609 637066613
    0xd0203041502160906050f1905060c030f03040f0b09010203070806090c09040905010c17042d02030118021002030c1905070315050a0501050f01020606090612070b12060a080a0f 77
    0x14188402c0703004211030300c01500018100c00036041881510011035102001f103070060204404000b0b01c0120001c0c1e040201c804002d10714021015101c0c44040c10b080c2d0389842c448034000c4034194000c540803604850764031001c1003808510200b640c0d218039508000c529505180001501c00f050060899104440c03035000200c04103c01c80580b10b0a50000e03006100c01b0b001c0e803070300902030808901d414000078144c0303089140f10805e802c140e5026940100c3e440400919018a1190043c0c102942030843c40004150380c00685091058180261fa5064108600c02c50fa10411200ca800c0007084803c40d0f009015400b480680492030207038080018024180008040c50102c0c1801070981c0042c1c030544600d0714100881c495500494822010003104014a07a00e030070401c010078104441180c016070180c000911a82002d17031020f508800c000b0004407100040c41c80c018644403070f6030002071100101284c030314600c1101c10f500d135400c05000c45c0d85141e03075410007203007a503203840c0040090310b00d0b03a41d00c0306481 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 637069109 1250 637067859 637067863
    0x91011030f0f04141506130b1e04060515190f0e0f12010219090801021201060518060a0314010f08031606060e15090f0f0a02070602120f06010206090d0203041502 71
    0x1c81c20440c08151141603401030400e1400e10806c95129010396200a18407892180c00d00c96280703035130750051880003148504a40240b641881001843e041a0b58200220b8955a0aa0604940448559226610800c400341590700701c500358010780c140300c0311840c80c68089401081d90b203003808090b1000304a2078540000111106841031952549501c00910750411203841601c0c506402200c1e102d080c4104d41d00c903400c44c203d104081107904a0300b030040040c060035214100400050404020010004e1000800580e1039070003900d07440c0c0441e642e42d1846205080c1503848034014000100101c5c0228034222042da12440b4402c07101da00c9480681000703080284507445070024095a4140c00007603e440031120f03080d0202201600d00c20414440000c0c0b0b80740418003154841d0340000403080700c0c2d88076190114041d42080310100e0780c481d000e2026000420070503442c54482c17110325110a5083c11b008002908152000c0c0c80c005145c0c000c5c0d03040b101c3c2241c00104450072034614448000c210b0307440000c228 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 637070359 1250 637069109 637069133
    0x150c0309150e0610080706030b060c0607021014100306020a02070f0e01050901090213150311030c0304060e030f1804060815071b030207051512091011030f0f04 70
    0x18000d421052500110010660044a0041c0c02d01c08444582c2c030380103245411a0380600c140f5642d030303000003070034801030f4071a400414100340040d007c982800101c000c40c2d030801000b2140c420050b0b0100f035502ca8115554000c0005800e0840000445070a040480c1c14491401d0b020240005400285245c03406100b041008010828201020030054644100700b000b42c0087c802e0900c11461040003255101240c03080b62810104040552001e601d8184004030703110241816606041d80c851010200c644c4980003107105400c019502692031610340f84c6801100c03400d4205800c1507109006c4c0c1c6000304142c5007111500400b01685000b1042010001400751880d0b400c1300070513010300d901c0306004c50aa01400e5008040c2601c6500f203c59441c410440a0101864040c0050340008420001070400f402d185025a10b01e80c001860b080500c1c0150404000036198500280e000200d445210f4840744950814440085049072071401c1a94800110b2000940001240031004020608105060041d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 637071609 1250 637070359 637070363
    0x2330f0403120513090b0301052d191107050106060c0b01061d1f02010b1c0b10080d0215010b0703051b07031b0503010513030512090a02060d021c0603150c0309 70
    0x284841d1108a070b170002d042c41c1c88240380a9030030000800d01000700c141402003035142e040204a480d02035030342c035200c4103d009080c00c0d0010089a8011003106118044c0b9080c0b840c1d610541591032000d407500c81c0c00c41d40c0704c0d4003a004000c2c003044001e0001340070041c100d04542d071618000401d240c88503100900704c44c036803400301e0384a4140b20001c05003e00032910112a4005038008100c3e5038644800e00500c0045902c0d01240e40a9512044000880c2920441d8002c20001e01c60340c0503035103400400d4504080740c514440964840721741019503c071603085140c054229580b03250304024190340c0c05041c5005e0000181c00d9401120580405c3d8a82001001d0044da0010f81d4044090f40c01984402040030a01070b041c0203508003070001e40310f030300d914a003070411580c180ea0322441d1007101010400d1841000d81800001c0c000d50b50005c0c05170f0b456401a1110f8030f054900169030b80c14000090703d030500c9915846014604000b420030125039030750f0a04188030515940810600100001280200705036000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 637072859 1250 637071609 637071637
    0x1120f090f110d05030306010c080c06091e1603080c01090b010e15030a02030a0303050405120307030204060e041a0108060d0b10062319090302330f04031205 69
    0x40d0a0502611201d06022507000315071040c41c0028440074011004051100600380764010030214103294850301c1841040e5003d0f9001c9414070400c0801a401c04006540080a5502918285500801c030074420903184002d036009200e0100040c81d40c2c05400594407002d824401e0200c0d0000311070b0402e400c01d401096004080003100c3da1282202101030a0950300d4014284140202d00010300f0000707015080c8580080041442c41a90b80c2c08601801005000301c4607401001880e01d480c0e14044040c50040c0f1690301d025031624280f10005029000744d422072072056080c101c01284d50004180b0001012a0a20342130010b55103000110b07007901010300e40201300700c01000c201b00b01c80104811b0798040d28440e565010001a00a890070300d26100c0c2e192108034218100118454000354070b080541d0031106040c109011617803500081c940340e012001826442e20801c2240303012407a200c160700f69081c8025107550601848801c400918022400014400344411000d01038481c091015100b5241e00085 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 637074109 1250 637072859 637072871
    0xb0913020313140c2101180f02090a050c03060d0606050d0f06061512090609140c090702030f040e090705041112070e0603060f370b04080c01120f 64
    0xc050010030507042ca060b107082c114014a0600e11001103030194078602c0050030716040e13001c85d034448210305120f810703103100c603643c0c422044041400500106204500441d421604c3d212580144900d485000349103071806482d0004004a0992800540750400e6040e01c0710081541d541c80c1880051510ba004164050901600c01040269005d05180c0303a0740f00d04024400d55a1341d00116480e0b004405021002c1a00c0c1c01515003440143d0344030711074850040b040071a180d182525617083d100000c5905490303581281220b07000c5030400c040c40a400a800740b00840c81c0c40d032002c0d0100070078084c40c0900c3c2c0e881e06100012641c509801c010000103050001c208000d40480c9458a4003540c1c4505640d0000316404000145038074011442c01c5a54072025220720320315610301d0200b11000c140060f04590001e4070100d000081c3e10038151070502009508120400f04031791180107214404540e218840c0d00350b0400051000480210301d000441e0001e0800c0c503129a110b030400f001518103c9091890107103001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 637075359 1250 637074109 637074121
    0x702190807060329061c05040609110906011407020301110c030c060112030c02040207061415030106050405060d0609140a0b010501030e0313031101110106030804030303140702070b09130203 83
    0x20400d042180c080340c400300500441007100450114010704030300c0c8042200c01c2a0f83c01810031a00134005540d400404100d1b0180c1200c0010884806641c141d444580d14072001c01004410070703440652020440703104a0902d400c1c40000d21812401c3e014204640f408240c1c802151403d4100642c1a0300322418591102d41010f80a66242c001c021a0700e01031282000000d04688200e000c245000e40540d51020180c90039002d00c00658402d0f0350484000780da0782032110011a200e1004e5011b040c4d03204450200c08044020182580c40c00d0700074a00c1a4985410306c0519910286080540c507400768002ca007108540c1442c0d0440c482e0900104003e00500161204200b84104100d0603990240c034100400c01d0340380405a0740f400344000c0c501e01010a20014004140407841005900c001490003e0418000100c40e0342500c0d800e602c1180c00880104090040603018005c65048011a00480090b031901c241c00955070100b521a0329500080044c0303001d4251070b40321900072060035508041d580c9082c09 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 637076609 1250 637075359 637075363
    0x4020f0703031d0c15040e042406180911030f0606190312121d060f0c070507120204020d0504050c1305090c040b03030903010c0909050a0b09070507021908 68
    0xe103421800645410394a00304103d1030b20040d20010203a100800201d90120103000c80410300d1a4144442e40c41408005101d82c1c103d0801ca2040e40301d4051416000640d0801d1400704944c0d000840b20b1301d060201c00d0107440c07a02440c060040e0314400000c640030035941401480c40d0148a020364241c0121400a041c546002415a000f0301003943c0c82e000a40881450704440281c074040104000710007010800c405200781098442124103002c0080c441c0d800c07250303000c50b8400d4003c00e0512508040200b0002e448821030542d0f00801214105150032003d030f8403980c1b00c1c103050144100c120310300c0c4c1c032280c1551666416154003030580c203420442030030541045599843c0040207140f281555008112002d11503005817070050382c02500034008502a14200f002038588000ba00307400d0b2009000404050350240a15200303050b040d160303610203d0410b120300059500081a5100741c50601001c4605600e581c41c8080e13000c0110315016840c1d90032171000442100a0b4612101010000e680224000d040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 637077859 1250 637076609 637076617
    0xc0f0e061317101a010302070204060b0301120c08010c050f0319180212010c08070c02011707110715090306020d09050a0c260606010507020a030c080a0c081603020f0f04020f 76
    0x800d900b00d0700c1d030b0074038140f080c1c0c01e030b8000c20742c280c02510440e80e000134a9406a006003003150303c014008944c25450380843d184a030401da120303600060000d0045010710035208104400f50080d01c00034401c2008490000d440c5100341003c00031311480000024202c1200190303042c01e40d4a403071400b4021040100c4101c50504d0500d5000d034031403c401d0f0410781c11880c05225501000700107480c4d1421319030314400203880542c1481d009a040c09940e00201400c072186d4a10944503059540310f01f01c005410740e003068548803803500054040c00103a044084030710b410982003c00c60794801000340e5100c0c4826503d0014140380c1b00004d140c0d10406500d5030821005000c10000d4449801071304410061408ad00c03038400c0c80c0200d00408681015011614551103103004220090002d40b102010f40d07541d648203440c2e800c0c198446046600041502020002400ca80400400e17401c002405090811840b0040c10107841c40000e104208690480c001521000c8004030b4081c0d000340f0440d168140343e0b03140042680 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 637079109 1250 637077859 637077899
    0x9042312090f06120c03130f0c080705100504030b1003060207030c030f0302040b120601050906190f2d030b13050109050c0313060b010507060e030c060a0c0f0e0613 72
    0x842c001c1000080c106030040d02c040c1a040d09108400d901c4101480c84580d02c040c004507149541c81400d6804903800307400d07100b0524030440300c481000c1c2c54020010305055a9401c002c3c4903403c0000056a001d40c0002614152a040b04441100f0344881c0c00050807200d40d54030091a1a00101e0118241900b0455610110f4080c0e00e8400d01c042117030000b10102e01c5580100e03204c0701d00c140b00741080c070702d510a8a164002818103240d0326220051000850540000c404c9200000030b03046d00b03590b49035004c040c0156007149070a000c160311072500c3e00e200400014007101500403124080310b40400f403090300440644c0c840600150303d40c2c0c0b47c0700051000341200340103450140c0d0409020404845190040b00d10500c00d008007816515103030f0380c480d005042011b0031281006000e1040c030001c10140c0c4200f00700f1030040303401140c0e1205280310060402c80010007030007005161a00e6080c1140c3c1060301d8890130aa24034010f000e81e201e00d4000760f1703a0300074100b030a1001c3e000e80b40d0105075a0400d60714002050 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 637080359 1250 637079109 637079119
    0x91e031c05090a1118010b0a030b0d210210020309070608100e0f04030e061204060506011d0121020a021e060106020d03180501290306060904231209 65
    0x403500603400c41540d00948034080030f81d10010311030010038510a5204000040100042070116044011984c2c00f1400c1e00000103007400019030710880c541601c03031250410b4013075a4141d205000c82d183c40040460318405514400d9020144030704992091040303050f02140c0c00b4013103440381080102c0700c0c0d990034240641c40110341050302043c0b120400340d501703004440204c00d11000c00c1d910316002044c56880038000300d0500048040302460740d0364070805016041e012516441e218603107420310340f00b584e00140402c0c3c140449440c0e08405140035007003a00c1103034401c1c00c00700880100c0301042d03281c903401d0610031403083d440450304c0e0b0010f17503002c201c1c0c15540882101c081509803540040c0340d1610340a215030009684444059105180070303800c1600403101104410b44442950344503142542c0d64038070032101c0e4040710030340d610f13000071241030800c105d00b03003500207000d14074203440800c4c2c500b800504003409042030f0003415980303d0012a00150442201c801355110320907150341a400541001c2c41103031042c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 637081609 1250 637080359 637080397
    0xa060c030e030c0714031009060911010302340b0a0921080a0c12140402011b081204062403061a010c030c020114070c09270b091e03 58
    0x10440000c00c3d56054140303180079100040c038003118141c4403011202100d806000781102449400001e21403050010f01610b800320b003000d40b40c41c0c40300c240308480164605041c030503c5681544281c100069910b081c0b0362103801c14008116841075465013036110000d14212a2a041000c004e20b0b68100f84003031440f6201f08003a04c012186c02c0366103032480c036004100042c14280080e40301c59094000f001030020f00e0405030b2100c02402d04c4142660300320f6801e8501c0c90101d4040c0411941c1c000602500b40e003000d06507410076a1665a06000ca00c6407059040e900010040840c2c140b10341c030f5005000100302e0300d0007400f42501c90713a13040000c5002484140c503510300e00003003040c0b01105090700e9079511405948400c101e03e041d5406451085441c8001d90400c41514204041d88803080000d0010600a445140600f403410140800743d030b030700c9049a017803c0706981c41d00c2d5100f52407a10b0000110380c0203a03000040c4c0d0b50714584516007110603500c001c0b200000d86140b0203011000c00288000560101c3d22810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 637082859 1250 637081609 637081631
    0xe12160603110a0c210e03060c0901050412020423090c030a030c3306080c190e04050f01020406080708160f050f0d050a06081005100b0703030209030a060c03 69
    0x1200c207a0000c0c41d200c1d02c0308005111803903101d2038000e240c25110f041400e00715078040d054070030014030341c01c82032011030594040d00c42e0a2400b0000701c2e900060001d43c0600d001c4d0700da00001d0440c01244243c0300090790450320340045503203980081c40c0a032041c244c842c0d181c4000c114140c00c400001d41d00d4071200d00030300e10441075030304000ca0000788a07a055110500d6603a0395542c6c658019500c262902d80000d5204e40b06c0c0040d456003210510700050b443c0010a01c1400c0c0815541802a41e031a054440c130f1103080c000c400c224404070403008655000c43e200070300d542c8a083c680d0418020592a4406500c00500803900603040700c40c45008046e15580c120300c80d036030000100c5240d070b01280300c0404101f00d08201180c10344220018030b6124041d066003420700440042a0b8196401a20b01c10182515201c0500880350204803000529203020800d02c250700b02440007801d4080540903001d08001c00181031001c0c10b0280c1c048456035030b03024007291100d03035107800e080004114030701c88030000a003008a0000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 637084109 1250 637082859 637082861
    0x6090106081b030717010e1605070c050907090b07030201051005030a03170c09180103021219110a030b19050606040b03060609011106130c0b0414040504030e12160603 73
    0x100c02d002d80d80c901d6420b40c800604802490300b00501c00001c1040c00d04000700d2140702682c00c03a0080c01070001651035424a280006112002d4581d9a0708201040c40003001145446aa12044460a03100c60003d52103100f0100c2d1802019000046408000120a01010b6055121138030400c0c2c43e04036411101c1c2c0f104105603c42c8810000030303001504400d00302c401c0a400f50880d41e005007031090002d203003858960116100603400719403d403109094100402c107609050002032050b40320900907122665000d0a2540150701014024100a032800302c90001c80c0ca504400c0c074007071908440c0006d09480c0203400044044541340441040e1414080030400f00d0500034241d90559800000c200d0841e1345400038000c0300c3d004111500e0401060140c01c0c1510790060121070700031074100b008228141128180080c04034082d0340140300306c1c0c9003080304000e104890240a101035001300e07030100d81903c490608448001d0b90241c40c9a1005500803000012400080c0c4054800004000044040c4e60760600b03070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 637085359 1250 637084109 637084111
    0x31e0307030534110a030503180a0b0705072d110f0307090b060d020301031515050907080921040302120a0809121207060506090f010b0a030c050415080609010608 71
    0x42e030f2550314100400240700607010003090840701e14111100364103c1580600d03050b240081900450000000d0080c0241c043d4428080f4001c0c804c005c00304c4041903602c688040e40014218410404045010300c10865040c108644510a907081030845103000130a030243c80301e90107400ca901088140704000103040403140700c0412503000700030303103515840d007940b01000e00701c90010558012020040313034080071586d1010318040c0d4010b0343c0400710b401d0382c202201c040361524450049006c0185d070f8101300f10b5890901c42c1e03a01c0081480c02201503242c441d28a454516018540000c0001c54011699588040e402900c2140c0c001c80f6000c2e8524503400c08141c40342440100502101d00412546225041403440004286044011520742c0204c4030aa22070b02d80104500311803103922001808a9071514179262038011034080d0310102954500021550503109602404090545420001b090b4a0007501a80e006020b8528010907040203520300515141c0221030781d03442074000078004942540705101403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 637086609 1250 637085359 637085401
    0x19112a010f09050d0206040801020a0305191e02070201020c0411091305060303041401050c0706210515100905060409020a23040302040506040605120c031209090a0b03031e03070305 79
    0x600051401c00f001d016030b19010f003405980002c0208000207260707201340300401c00c1414550300010281001c80001740f03407413500c410250400342803514450482c641002014521413010400680c0c9102920060f420020090300169219181a000000361021070000b0700d003080084520400901d030410711941280c4e0152030060b00740d80300b400280051540d1a03200b07920b0910505040b130420361030040580c074051090700b02d040000d4122982003409075409040c020200401c2c80b0502580c5081e031048248880d149689500c1414072080108520b0700030610603000c0c00b0f016201c0c903901c82d202c04c03049020b03621503880f80300042c014040248815841500070100c2c4031502c00700714605842c1d60204800380201900d040e0384181e8800f00014203541d0805100038a245c010003402c080d0b9981801c16080480c1c28403d076160a0003000544920b55030b030f1301c0c81c0f5403041500c0c0c00000e00c0803440010929600038084154810440450003c1002c00010302641c800c0c045c81e603080c0441c1d0b445405042c10f040a01e904 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 637087859 1250 637086609 637086617
    0x210c0c03020f01030e07270207050c010e1c1406090c36040318060504050105040504020d0207050f03130b0f07080c01111909090b0619112a010f 63
    0x140010320b070034080d060190070b0515020075020b1a0710f40c400e082c503800d5800000c0c0304001641c8248500c9852110401300540441c046041c502c25441c4e51707480d42c4a080d00c42c3d041005502a800aa82e50420700b180384c0c90303114210340d0014104c0c1c9840707035001c1c2d200b030130100e2148680c0c400640a40340010303000500c40c102825081c03030b10007488088c8840505c0e03403e4545d00c00300f0100031101c007008104055071003a800b035541d0100c0003458002070030705007110380c1010f020880108001d2040ea600039040702c01f1104143ca005030b5480310341a038403009001e0700c18010b0013801078840641202d180000506180080d43d000000c095940b060f0b0240e2506c906620301e11014014800c400104030164050b1520140071800400d6013400d94400e002c481d4002c4810b902c90944107403200600540c030116420240c22040700800490b62014001501e60154680320302c0040c20f15018038248511607009005000765a00450384485c80040d911402c40d10254000808019410200146580714a0880e6465280303521 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 637089109 1250 637087859 637087883
    0x1006050d0341030f0a0c050a140d1107050607051204111212190507020d17040b12010303141201061103070b0a020a0f0c0506160e0607210c 61
    0xc5040d1412101814034550440504250205010100c0008001c1400d0b00482c5076646090045101845000741c000b02d00f8501c1d214000780043d0f04003040304c2c00d015032070411005000c071003070900ca220321440d560540b48a04041d1007550030300d48400035000c01131007141070b51010b55801100320b403e8000d08100c10141c450600106020500c1c81c0040d450061018214035110742d40603d84500e0445000d044801c011800a40282c00742d0b00404502261001854400e1801d842500000d0150201c100c0c007038643c20407150b00028090048003210f009142814805803542c190010300801180c09220a8010490710a69949c807061940100c0707168040110f02c2620340c0e42041012180c01c5079111080e101c500c420818480428000104070344550b80b40a405a42d4080704034009000b200e01c990628140001c0c0b250460000300042030350381d40f08070382000310216850301384011107074050b4074170580750042070003d540014001d03641d0a0181c480076585c00e80003540700e0480200c41030020101c014001c580454 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 637090359 1250 637089109 637089137
    0x203070c1202120102190801090b0d060c09080609030703020709020708030a0e0106090f090606060216060302030601090f140901240804021503160f021f0506180106021006050d03 78
    0x1041d025045800a00440201c5414400050890748000c00110800264030407844902c0e41c0107a51a0140c41820740920980c4d6403139005c40c1c0f081010310b00081c10f46880d016030b0390300d8070f00c900c04d102c0050108504543d040e0800c809400e071030707603c5010290010b000c1c0d00c4000c50401c841d4001c071281d6540c46000d180c95592110755110040c05070148070b40b50755480704400503035071510f0302950702d04100c1a6400141245540343c44803c0325616801601950401941c070b800b00c03103d4029060032284107080260796561004012200ba00d80d80e0455a110103003508041148965001030b0441504151100c1425988402d840507103150000c03c1082081c4a0624041d4410b1040d41003a40251002d46002d00002846044000c60741080740c10456540c140b16003c8695640149403103501c0b0240d002400c40c2d5021411b800801d10310084400360f82e281c5030401300b800c17611032101c001020000080d95407050f585541d0001e449110003200c009215003000404191854095150b2a495600d600e035099400d41c00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 637091609 1250 637090359 637090379
    0x80706050d0c12051e0612030a05071b091b0e0a050f010201140906190209131d0a08030a0c090b04330e12060402010804080c1e010213060203070c 64
    0x1d06000b008101407000318111410050040a0003404500401e008904128030060803802005100d544141d00c01031601c1d900340c401100700d840f004c4051901558840450820552010b4042e902c0f03600c180c410000055214004c0c2c1c0f02d8440c803002c60051400d240700011040300c581082e0208240e100d0915407040140d4901ba0100070034000060001081709403851040c035901210480e409401ca402107402c01c59403440001500340740c00d040380b13400c5041641c1c0c0360100760703800175400c0810262030b940c070102a9958038108400407042c0c1c552040341e031809403a14040f042d035002901c1602c8050300f0034244070b02d07044c001d00b050030a980e54000000d050600d440210a091084214000500d80d4001c512102c03521003109210340c0e0300030301d481d05041c4510400a11034640c1039010311003070582110f424007005070f0748106070b10342107600304901d06d40b02c5102c800014107140d00034080e18203410f003501003440044810b4002e4182d803013550041c15815a42c2e8141641c403403107842c100900c0c0124801d0244580120 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 637092859 1250 637091609 637091621
    0x30f050310050301020d06080f06100909140109050c0a08030a050f1602030f0102031f080c040507020c030f01060e0a0e061819150b04020a0c02010e0d05060103080301030c080706050d 80
    0x10204030101c1c015920b00c0464226400004401c10540c1c94040034000407804000034940c14001278028555880d1850041c190355849000c0c2c0160b46407140d003136205205c20110680c9070b50368400000c001c8910310385001c66807801104100f5008490900300000d10540100550340d5519a545800b441d100d0b40340240205544454000006030740040f00000c0540c8080250072a01e00700d400006a42e420f01420004070b80c400d1302010700c1c10000d60b0a080c0144003000c2040e0440303d44c241c601054130f03250001c0c181d0410040125940c1c141c07051000b88182d60343e054021104031060302654000a840340441d6106541c140011b840440c0d2011001c545d41e40940c165041c184000c0b8015035485034034110508034080380c40d100a5a0005120909150904452250041064080314218584250340f88007070a50504c00c60701038103011103c80c4d50101502d410b400d00c060f6a61000c1503c002d1360b182d1031701e06207a80080c0820350701070426100110b0000320016003d03007580d103252103140c1050b541911000c09007030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 637094109 1250 637092859 637092871
    0x50306010203070803100b0c060a14010f05220e0d1236020607060501060825030f0f0203090a03110102090918032b0b0f09040201030e03120a051006030504030f0503 72
    0x515054001a0107403203102401d4500e0071320000d0301d100d0034140282d202f40c4203a0f2603148040448640100808484c2610000485400366403503100100141f540741012162108696013840c24080301d4502ea4030b011511b06003400541d126000c410555542120031038031004424482d130549400071503100341c5210342e11102e48005000c0c1e00c92002c2981e001c210580c11118007151401e4480700144a0340b070b00020026400040099940000f06211144d41c03501c410f450381007414583c0d5266803c0e112002c5401010200000d200c0540d50390800ca04096951007002d4425000513103a405460b2800c0e4060003250f5401a00a00b2001030303481d80d00c803080c83c1c4082800100030520042002401c1000c0a404604200700401c000b004842c031000c8880054075600c40719180302c2c12908500f604d4558031807001c1d0b90803d40a2900103026204080c0b92480c0d03118a2800d100341c010b0580403c2081420358000358841c1e500100440a500d0b5240c2d0290f0a945c5c00b5a00100810b04220700148480c0c8604040d540c451 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 637095359 1250 637094109 637094131
    0x60f0408030d14060117011412010e03041409010e06010f1b110108101a03070c0b010308090a05060901020c04051909030503011d0907150215180607050306010203070803 74
    0x40e945450192465001c1c5803a100c1040d110021401c03001d6840f0501075004e00c007824030f10b014618000c02401c07844814001c030700304034203401524146c83d2a541c0e0804131003d04117008001c40c030700c40c80f401030b501d821502c110070508507100702c0e5a081c0d05050103568100c1d914040c5000301600d82c040151200358402d1041340402014800003030050682e001d041c068240a84601d640b00c0c44a50001003038003000400c0c0400301442070400700300208115400d090300b0707091407100648076111100100d4201e40ca085010f085100c410002209212003400102a030701c104460050303491760380381c0070f000d01e0b4094019180e0160f04503000300c412504068004071380c0039500303081400311180602d421404540b4420000d500050002c001030110f0900041d80c010703e1007001c00c0c3d050040c6400000141d0710b0700e140c0154035042840124209040d07001300700d12025943c6460201c2c50620b8400d4800c0c00c2410812030840462150102058285005a003124000d8006a018502e480d041d034658907599440604028416 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 637096609 1250 637095359 637095367
    0x10c0b0103080d0b0f010f0804170c0f06011e05040207030c02040f0f150e0c0f040b040605071e120c0516120b090706020a03110c0d050f0f120702060f 66
    0x98102004a029521480c0ca2079143c004a015000444844000d501d00480090b4100300040e82c2281ca05d0900045500e45684260f8440c5880c0c0c4052402d214008035007517010460410a10380490307052140e200e020101c5820f60f1369018120751030f000c054803401c1000785a54040c85503051580040075403134040d0500c482c00c0c0e40e542e8042400c880c6612080440580d8400402509004900860f00514000d000c1c0b45407103800c1010f0280d400e1030140100003480b44c0020804120030300d42d41501d00525410340101d84031651198090b20329802004211003d03140483d401651500041d10011030581055a00d14a031040000903148120790364000d440c18400d036003640d8072040c0060301b0000503010316400c2d000b4200e650f01c1d2001625101804544e00c6070042402840303803a90000741c1548a5805151105070b10103801040c0e803e0031300b8040102d40140f403014140c1c5c00d002000841001144894044484899203030303100d0741d03d51b4800400021a00410494000940341c418080c0c90003820a5042d50b04d8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 637097859 1250 637096609 637096613
    0x80409020d0b18060f0105120f04150501090516020a03020606060c0a0204061203031b0806040b060c010e0a0b15090a0209120304031b0603180308101502010f050106030b01020318010c 80
    0x2c40010710404800c3c1e0a00e40400c40d243c20000806107500000b82805400c0503aa50005103038250000c0c103800528500c0f0340000c040c03044850390540c40c5003040600f0081c958464045102414044a04c22000100300c0c0500c024a880001d813004d003250160301424681e1507c4040082c207902501d420303a0385100e40b820800159555214a0700101410060680c000e080d601c2c02405842c60138401400d01000d1402e82d4100c140c002e00310740da0102c400c84002580c1600c1c400010074501840b40c1d800f0031980703042c0075200750100003d50b002034503000d404491913550b101c1c0085034074420034404140e0004035500c01b1400002c6039801604140700003c1020141c1000340c0c0d402403441c1c00550050b60080107400c0840b00181e0b0071203030f00014144618090000c6200d0f40000030408440e640d008040203c4500011141900c1c0c29506018001d80340c030301c40202508650083c0608244494020071515203c000200e00380640301c1c80c52091410f0300a10b0422001d112007101c80e0009802c0e0701e06001960280f800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 637099109 1250 637097859 637097869
    0x12040c18020306030c01030b060d05070c1a0403080609062103210103060606080106080f1008072616030803071e03021b0703020a091515020717030304080409020d0b 72
    0x380000d10314000685030b20300315040504d040100f00c07410307041c54a0121035840580715482180d2100da2049408156070b12048411103031001c802c2000342083c664101c040144140e5000b00c00c2c0558001c0d510001b417622200304010809006940c1c0984c820340035203169405443c103e820703401700f00c1e070141542e00709203000c9596681c0c0d1190654000c0c0310041d1100500070040d0b41d11550740500141d01e40b050403581807a00c003601c00007010301345a01150004000440814508403800702501d40b80c419034000076915038040c210100c22030b00188420000300c002c8420081e0024607602d0000e04203084c0b00c2c25901d5502c94100d1540b02a203d9000c0210340000035012850407000d0308419149558016560088805c60f11910010318410842d1a00700d0a810400b580d1100e402c003050321140000002c0720010b585011202c800e060744000c01c1c0040f40b1050022064001c50060102c420f61100f244e040360484c42c8140d02c80c44115002018210b09110501c51040c1e0703035000d400c05009140d800a40e61440a000239 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 637100359 1250 637099109 637099139
    0x5031c020a0206180907020f0706080606072109050d050307080f0d0e10240b1c05150f0a15121d060106180b090d05030403020a122612040c 61
    0x16801000341c1140904d41400b0f280e066002143d48050009190300e40815038480c40f240c0704032410132403540007040290385c0c0c640448900c5584417524400901a580047c2c04100043c05400e0100d29200300020b01c0c2c0c1012500b221150344d03c08003462905040d075441c41c080e40c0200031489190340e01446806043c07425842010a1200c00d840102442c101c00c5001e03c09075002810036501609003c0e41180c0780801c0b8220200c00c0d501140c42d400e80342c07118140d8000075503c104812200d0a800c1c40c0c24030800d01c1039113201035408842a10001e85480403d002d202c245010b03441080205050007540d4100c0910a01c00ba8244529011011801c40961103113402d0340700d001c0c000c601c02c039009003004001c4541c01c44607603d10006400c41241c0150714000d0b0741c04080c050400a18080d0711509000b6003040380a20498014590040c2a8200c1c50740303c07501c80150510500d421928240601407091842c41c010544515030140040324621b09040c0f82540c61021001400c100c3d001c064001000ca16034a0b1001c0c86 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 637101609 1250 637100359 637100377
    0x4061e06091b1e02101802040608070305100515040614101b0f050f0304081506040b09062e02031201050904050307032106030309140a05031c020a0206 66
    0x1040031410551240c044800c440380403900895545020100c070358005015046044003040c0070301241ea2034020681c14a803000d07018042e02450715440c0d500008a428801110034003c0e2000c0000030b454071000c9540320010300028016038820640c4104c04000342e00110384c0f114000101080101181c401f280550307030a07030010446403041040d50101424401d40d1038418400c10b00e0450020031468103185d0312a120719101034031801c1c0100a600c14000304000107524040d00208580e03549568001c00364a81245a0301007211000e4071011400710700c0d2501604040d807400400310060340d01d42d0820401c08050413581d2100e1010440d54041075402500240c40902c1d510360051030792a01b104031019030f5207030140c10043c4a00000c10a010205d2000401e071900076926062140c01d401c100710003100f0036000b023018031400d242000c1022041540c04003102003180c3c450410b0b1080303151b1450802c11106c07000d004007601a0300400c1c100d0046107801c0c410400801440c01903840094164011540036884401c80c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 637102859 1250 637101609 637101611
    0x7052205090f010e280e151303020601090b090a1e1103150405011401030209010c080424030b0d062705010b011112160309050607230316020904061e 65
    0x1002460749180c4a80e6000d0203201240240d10817000b84a016002c0c4503d00300c0b1482c0c1d83d13090003040350004100815224100c406100c05514002d1610317014100b40e0f2600f280140078030000050b411500340030300444175100070003001c050395564517658000c1c12414000340213a980c01c0092071075a8510301c00c0402d0240c8440f5015a01e00d000d004000c000720b000306c1e896019600d0f001c0100900d0302c940e203190410301d000f4a0007598800d0f4a10040390102da1258010740481030028000032485419400380c1d4003502c0391080c0048c0e0402076032081d022210407240f480e8000c05000500c00005009610550036008154020040625111030799243d03520385400454481c0e5540220062075a00020441d0140c1990b200510350130135041400142401011703001c503401203000d08000c0815004092002c090708018101e940c03039403071074103154400800d18150f500b040001940702a41540c000300c00c680819112408802d0000d802c1d6007030140c04070000b001518140c0e03990894046030303400901700500c11a09014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 637104109 1250 637102859 637102861
    0x3050703171f060905130b0301060f0909030e04110307081015050408010f110d0b0604050603070804030e01181a0c0717070e01030210110c060406090602070e07052205090f 75
    0x440000221210f800502c2030141c2e4400401c007a40e00ca42100741210301c810740201e00030700c40002003400340100c0d42010164010528000c14200000d0340060b2900b17001e40e65510a03c0100300c10704c02107550204903914244410400600c421307018403e0315400100080100600300c0e501e50540c1d0740c0440400e1200e0014100080800090000b4011b509200d00d000c081001002c49107540c0095500ca4a0340303090380b05445240d04038590380c50000765070061801408030f503902d24082200070030906007103900701c000c205410003801c40c5510814004900032200d800c81510030b820480100c12038101655a10440a0101302c85024560180000c40040260500c02446035880c01c40c41402c04c80c1d40e8101c08541c1c180c2000400250383d5202c15441185854203114450101c0a101d85003091003000c00700e9089503001400003111948a440c05080354099420b807048507440384140c0c0c107104c0c01545c0800c0060020701581c0c0a0202d0300101071144111005403660942d07944001c6007114038203c0701c01c800189588 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 637105359 1250 637104109 637104151
    0xa09170a0501060f08031603091a030a0e06060136030f0308090a050309120a061e0608010212011a07060e0706030f02071a150319021017040305070317 66
    0x1000e407501602c00e203903013541c2441c280855983c0d6401030316405c24641d4152403503c1c09043c0242c0010019000103174641441e121764a41d13039621688144ea540d8040d82ca8484440c0d007190340420f40d03e0191505950300d01c1e000a42c1041003001452201d140781214106142c0300c0b0070701c03025201c6c2c40002c51144801c440784000501300600003c0c00180540c6660b0004d1078601c1c000742002c02110740011040324064140c24a80e000f0320f15084041c3e1004000300d05d031002d802c5a4079010350101c54034407452442844101c5d200c01b0401d00f80d000e10060709142201d14001488644202194001c8030714010b8200d6040c5400c0d80c640600791404180b040165400407202880610f5141c00b072050300301800c210a520b820b20559868802c2c69117442d01c23120101c6900040b131a46014040e0f5031440b00002400c440c00c0300d04a6010444208442404030b1085c000094010511401410300071500d100718901509030b60b13a251000d9801c0c0d80300702c03011000c0002061600800d044400c170130501455402030450400704a0f4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 637106609 1250 637105359 637105361
    0xc07080c0307170322080f0705090a0c0c1e12082a0a0f11070816050d0b010b07080f0403050606030607032d020d14100b0711060a09170a0501 62
    0x55004421181c40380f0351031040b01d400000440d20b8010482c8040070015510409012040403103070040d0141d0f0041c000101c1581d040062000c0a6820407603164009841e2404000215016040700d5000308810b95920004211001016051002c40707061424034240c040c1e44620070b21a40d00101408a04c0360b00611001080b002c040d180d03d400000c1c0c041c401c0007030548050300e15002d9200c0c0307a010000703140d440c40501031180c24030342c401040b41c0c0300710352219440d0705006480b80d03010101d6800340d8014520000e101d28142100c9210103030003110410099007420b489007100c0d0b1000c241590b909204102444011001da402800254081c0c03002d41858144001010704040018080c0c1c4201400c0c03000240c03003895803c45007000350928a014042d000301041080c0041c0c06188801c01b010ba1411402e12000304980716014841e111840d807100105848036a0f00c1c10a0107070402c050400e2602c2035503c56242007050007000780715910b0034003030202070703540303c1c491000319444122245981120341c99100700a02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 637107859 1250 637106609 637106623
    0xe151e0d0501120b0c181207030b0609250c020d060b030d0807052a12191b0807060b040e0304140102030301211a070306180c091404020c07080c03 64
    0x503003d0a8000c03a24a03141c204061802800190881d940010348880c060349003503190300c030280e000d0150319048114249440c0c481c0c07024031054880511040001e62503140c11241c0c18401c0d5001009001e40591100c172005003d2204d4419100f0710120900c4038015035035441440d46150b00c10130001ca043e105483c241402e202c0075080c41c60500c80300b00b0503c103200380c00a00fa16448a002c00c41e00030140c0e000c0d4141d040c0c240e08001c108455014881480d0865800d4100a1084450440c0c3c4003c82c640703580000c0311208505100190464481c01480000540040083c1002d0340180d4010903064134050018049819110468032540c3c000038003040080300340000008415024009942150b250100481101002c114410300710700e001c024442c00c1107881d448040b00c403458500e56825034a0802d9004d030040c0507600900c03540e01c0c1c0560550b0490340307607800748800308261503591050142c0b8104404c03c01c40700c1191007680c015000d0141c040c0b03c032020440000180b080fa0014960508a40d00b40f5050a203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 637109109 1250 637107859 637107869
    0x8070326070c050909120d0e06070807080f181009050111070b060d2307030201080a1a0d170c010915020c0717070f0605030405011505010e151e0d0501 66
    0xc18810400030075618105201140c00c00d44a04409580300b690540c20295013040400c0103400128080b40c0c5a40c040c0d100742c11620464046401a8a80c24070035210004102d03410000544581d0000725400001c4402c2500701030494a42000810440714641c2404001e00812800c156074090607000d01109024000d2011000c2900798541415510340ea138507590014802c43c060360841d000c0b40c04101c840072403050360360440c0ca07054050318440f0b801e141d01d545561100740d00161100300494512460b40c82406001800c03641d0f8054a0308408007486026044080c003038a20301000200d501d01d41c503040008110700d000e000c000041d400c3c120b2401180c80341030b8101020b0801d106201c0d4101d412800581001601c0004094540d245c1e00c8203516407610340680c10200310307001303289000a10b80e80c1040c0a140268801c0c0000d103d04500000d81c400741504070320415002800b01c041d01c0c1c54a04045100000c0c0a140c0d1005a2421a40715407820381c02c4200c1890444007200010908200c400c03d21546003d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 637110359 1250 637109109 637109183
    0x20a0305100f27050304031a0f07050a3e03040512151b0405060406050c0c0429010315080a03021005040302060612010e1b032509090804080703 63
    0x84040d140c0f00d0541110319211041c865412012001e111040007504c0045078800f00d4036201c510741d8036282d000e120090f134001e500041e582002c40c0303040c0c0c0a0030540300301c4002c0b641c800d207400184010fa039000401410300f2400e901079010b48400d1410500d031391304c1a43c0c124800216695842c0005001c3c481000e107220500729040003070b01511200b4520700098011401c1d07034040208140013510014244166440a0f902c8040040c0c00143e941d08840038103043c40e90401560040320407101408151107030b190031021b21a4030000d00c03185042c14107991408044c810f02d00000d100c0c100c1c8000800c003a10540100443c1d500044492040540c1000215801e640c440818081070030b01c1d58001e0341d55840507064600c0f4407403014080d2110030095005001c4100314008403111803440540050301059401c100074001e000f44044007003501303015104030442d0070032849054005803038444090010843c1200448140d0010840001e90708405c1040e20301550080d092409110304110f994894003c1100c24681c0c1d030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 637111609 1250 637110359 637110371
    0x8090910150504051e1f0f0e011106040b070302070501020318060c1306030c0e03060403080a0b0303091c0303090f080c0d0813030c060204080114040b070504210f020a0305100f 77
    0x19441c4c405c1403241c0d000410b00c0c1e00c0e04405101000644c15a456600031100c03d809904009056500c6200b8990564503034030b030825a03a640400444180004440054039a4440380102e4005111040788541c04206480e0040c10245a507540e1030030b990081d0307800108080c010001040a010a00c0650740140c450260a454009001000c41410000c0d115000c00d0540d5801d080390b071a401540300d001c5e8078000030241c801c06c0c540751030040c05070401915910049031415501e45054200041114003164009200304051001d46400e99642507240800310100f54454003540000b9441c000c10003042c0e0310800425403501c40000ca054644580c0f815282e0800041d4000e04c1080c101c804034001400d90507260001c0042420b042040c064451640591843d62811058038403c802071281940510f00c251274540c2541c0301e81c001143d844c02103005030207101d81c05030300403505c2450000702180c49a1255800c000400e00d25000100c9400f45035005864582010031017030b854000d84d11818006c090441420840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 637112859 1250 637111609 637111619
    0xf09061d0402030604060504150203091020121b0301080d080a050103020927160503011103010b04060503040f0c170606030105040503160501110c2503110d08090910150504 75
    0x144503000340015006e0307aa5100407a043c032108400780c00c1c0030914454195034a00303000d42c11680ea18903200d0721011052078003031032081070408140071507500f9009000c102c0c106249988a060950030240001c0c202ea402d00c80240421000c120285000700f070f0200c041c0101030850310003c0c0110900800200c0110f03d00030061006035030740768405070004200740e081c0b030121446003181000004001d584000921a076107440410180c0c00c1032503010b89506600030310a9004089600303403d80000c0c000e8644441c4140000c0c02420311480141d0751041c05502544004003e584800c2200c0c0c0070341e00602010288011188501d031020042c00381c10040503802044549403e8a4840d1280580009030651800030040001804000d400c0f010b0b84104440d0034a5071010000481aa285d413844920341d81c20340700d04a8140d540d03254000190850b03400171400c0c8180c003000030030882c407904114000c03906240140140f040c6911600407942c03040e0039459040034010304055210603844150f41010081040401007404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 637114109 1250 637112859 637112863
    0x705060103030f0509031507020f060411040b03120c0106051804050c013e0f07080309040b0a1e05150703051c2a0912020105120a060f09061d040203 65
    0x41140d0300b41c42c0282000850240031142c0b4403c03442055498400c102003c4d003000f4440c00742da40100c09a4003140c00742409600074a807100d000302c03406080340c14070001e11070440c10705400c402ca0080b0000c0656071010341c442d071101ca4039000308451241c01c4c4c0d0f541c9400d100500f040c51001504240d0f61492001c1894240d40e40c5542c0c84001e4030450400040d490100032654010381640c40c45084203060b60812801c1c0c00b480c24500c50740c3da15044040c484e070060025400b00110718201500c40078000b0b10b03d800d101406200c0900004031200b40c00c80c2c010364001076501d00400c040b030b805602c0e0f168502050b601c3d010821003503984100031940242810420100000d401200300c40303a14074850a082c01104103000310800400ca5a501e260040740100c45100200880300c40d001028449500d410303107415202e40004000400040009011501c20841840300d20302480d01705a00c1100310a01085c860b482d008803241514550780007a010584450051150701060304408070300721040d4603406030614007900046d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 637115359 1250 637114109 637114111
    0x50907030204051c150c2304050904030e010c1a0601020c0103023a0507050c070f060c140f07080c030c0402090d150207021509011b0c0b0906040504060605120705070506 74
    0x13a01440400d1050030401c801081030308181c05900208400c410b000000f6101c400350781d00050103114105001d4040c05076950a9030300340c44005e0990083c03640d41daa01610b024142d11240303410b2001c80c0f8600000243d094510170080c051300040807034a400c0030b1002a01d008203621015040c0750040c004851100b9000c1c607480310b604034204001004106404042c010514821400320302242000104868140c000c03004042d00c43d03181707003154200c5030f41d171310880119000c4c2d0180b140082e844500000100d0961a040141036401d8015983e4801040d01824036000003644403d0700c0b038001080411645c6402d03c840301000f03505503400e600d070500790400551003d40000e0002c00d4519503446a03070840c841c56041e1900581e005d00b0440348600100140b18482d08102842030008250076160051001c2801c1801e14095000024100d442d00b031802424803a000410011703040708050200007130b15078541c0910001400e040d00d0b00784e900e001b000301002c202d100080090b820b0041c204010000103d0006402d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 637116609 1250 637115359 637115389
    0x912030e06070908100f02090904060b090a0605090601141201180c08061c240921021507030b09010b03070201060b280c06021209072c0606090d0c05090703020405 71
    0x35075006d4aa07448002400f450500c207400c402300c1004c0100300103855200700d120f80000c40d0b0389485985e98201c45010b4444600803146c00039081c90221310366501038108809492a00b1110609142c80a141c9410303540c4240e01c0a03000d000d04d01c00780e1091a074144956001c072034161a0050841ca042008520000828032350440359403034214011013444403131003842c510001100340c07034071040d0001c8004201030315001401740e8943e01a00720300380b1508242c4121130340d442501e4000e4100c030010b0700c55100351035030000c0101040c561a070442000d141d84000d0340601034260195096145d041c0484028211880794002e1080080b00304450175002c05403001500540e400c605881d00d00300410300049521040c24080105a54008100c1020f080040000244a407903a04d04881d1b81d1a920401280c3c48410300e622600c0074000001c03006804045d04144582c030000260181e40ba007080c0c0808141e0b0442454010356030302c1c242c0710091100d0718060785410b400c80d407036160941c2403a003803d0000b444035048a100c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 637117859 1250 637116609 637116611
    0xf050c0903250e0a05010603060512060604050402120102160c2c09030f070f031e2309100807110c0625080c161e0506030a0912030e0607090810 63
    0xa2544030102c91200500502620041080c10f82031281c0300d54044c0c0000c0c000c6501213414164040340300d080c02d10440c9000109400104076a440e50003d001c002c0c400540700740d0304a201186102600003007400107094080c0041400461003aa904100c00c4544494100d46401149045c89044030100c05184942e00d0a0002d140b084580342c5400c030f43d1840c41041058100000c001c6031800501c45001c510801907802511018038100603207107403c1030103803102400c001050540c074180000940c2d100310a41e81c6580302c0f2005190100007400079000c070420142110000305550200034442d54040440f5181807400d900518800d4260b03800541503004421842c03640c1d440300030810f8180550304501c40c1c280380d040445581c0c0c511400b0603140d01c401a502004100d00c03552240001d400b0440d2204440500509400300c0e580e07400d1004102d516440038000252040c0c0351217200000c9100c82500c00001d100c141c070000340660400e8061400d1070801081102071202500081085e0b40380418980208200104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 637119109 1250 637117859 637117903
    0x314060103080a12150f0303030e0606090a09022403010315050103050a060c02011404030f030b0d020d060203040807080c0c040f02161101050708040e1b0a0c0f080708030a0f050c0903 80
    0xc0307088024007800b40d95040c80c101c40640000e1079456a006c203c1a603000e030b0380a001d015030031f075110b654421003a0f800c550080f458070001210005554044000648020b01c0349400d000c1d041001c1100803e4800944840c0c0c40000040081049007101e2448000c1ca020040c0450b43c550b4031442d40350b010100300a0715094880403075030140d6101303612500707010446c003d9102650609050050460000042c0180464500b041010350341c03800c10190310031241d0003000221441500e9442d10013a4001500c00c50300c100f8240070310800a154600940034000d180c0d002000c140c428101004241c8801d202d424964902c104002202c0c40c901003d1603160b80d810061801c880004180100c1d070078441c09401900d80a23011070f020821400c04200340d4040c2c1500f4080312000700c00760701903465520844481c0e4000c0b03061003041030000348455921081c1c41e070041d4401400d0907200d45805110303078001c55028421640d10820601402c1040c400c1c1a004603400c61400d003000003403800b0a6590910701c441c01c000300c5e0410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 637120359 1250 637119109 637119137
    0xb040201050310080609010905070f030f0f03111e210d09111206060a0806070c0b06010c12030504020310060f05060d020c01020a0c15020f1204050c0907090314060103080a 75
    0x1003c0c1e1000700301c43c1c01256220f20300000300500034000800100c2c1c060180420001c2c07420082c841c08001e03030380c200b9400b070001c2c51140e50300800a25400422004d00005007412861201e040c880b2a00d44180c1040c01154070107001041f0b41080c060003945203007005c040181030b0038403821900703503a40030b0498400041c400d0000e0405019841010a603207031310483c9001c82ca0394500c0c0100755940103c5080c1c503a5580c90741c43c1e40046845200840f0b020000441d5907114802207507806018942240707060600d001c4600c596140c4482221104040c040402c0d2035809200860804010102e00041025820014241444e1104a80f048203124107407280c600814522a03090165040707c002d031000600031952401d180c580640080003400c415142c80710340b05128610384a03203000f02c5a0704444450001e25244c06180c81070110900500300340d41300e201d42e071502e481640360000e529014140c1c0703880f040302803861850102149a40b2070b9001e0340c02d070043c4004100054012090300d12551031401c22000100b002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 637121609 1250 637120359 637120381
    0x70c0305070f0203120d050a06080a02060304030908151503070320040b04230c030618070c0c0305011b0518041d120a08093f040803041e030b0402010503 67
    0xd142c0c081c0d814060014042d40c84400d1000415940c8840d500c01c0c40b0956801f841041101c40a114a405d00c1c0c12042121005191810007503074000c1c801e04000f425192100e40b074900c1d0105180c60702a88580700c5060054801d245016a002540c0807001008100d08683d188616044900a90303441c030b00c90441e0100f801d40d82c50b00101c601c0700d0040c00420241805214014400800803074441c140402c0304c010800410f0110122413090501030154008032282d0f2184035110400200074604102401880c140082c8040180c2402103000b1000402c503070f000300b00c24060302d09c4d1301c915a8061010400c10000c0c0840c84000a44240d8411030b400100342c50b6452520b511024003035040c0c0054020b4141c83c0b01c0554080c4082c0002402c81d07a9000c41d599603d01d03106503185280b1103102044840d2000300d20240c1c0c4a01018016504c880c0800d090341c1084224001d0142c016810040d4541c1011038103214000036803803405809a1032a0080340b0162640d2505c8428000140c00641000400800102c11103d2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 637122859 1250 637121609 637121633
    0xe070c0c090b010f0815190303031808070f080d022205010f020604120504080f2d57060f0d02090f0604030f020a08010e03041211031c03060905070c030507 68
    0x4081c0100047d803003c1840e0f014010006d020032030109103000c10310710611590340d80a0104c254000d17141454480d240d140d414440351b200d40d08443c140404c002440c0d2050207130002d080e1a126504c1104080c054601000c82003516070b4000301c1c1000034203071034120300ca0b030b00080d419000b80e004080d0003000310396018115650b10803a00700300340c0c2e44604000c014501100198402260341900c031100d9080050103011404030301c191440ca0b403a81c0c40b0003222a05ca040900524100140402464801d5046031440031079403848603c140211121000c1c083c00701d100c12003001c080d8000e0480e2070030701d0868600e00c0c40629000b0b070718403000001e6020901c6141501c0d81100a8007002000349280d07140d5039240743c0342003c2ea4114800f00e0041551107c000380d03910307050180e440100104406103081c2400d00220480984514400742da0070400c2c02243e006a490500040301e0ba603c1d282c1214502190b10040035090b02c1680c0d0101c00e040d4540b03802c112005901122502c0469494517115aa42c01c00d8106900b000761 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 637124109 1250 637122859 637122901
    0x30f0d0615020715090b0708030a0609050c091c05031e1303080d18021f0509042310030512090d050d1107060c020603010905040206040e070c0c090b010f08 68
    0x201d00c000044016000a030900c2100e60105a003000c41c0ca041c43c044450f1074291041540044c014404580001c0003180035681c03040407207900003100399070f035000c550542e14151500101c0c0c0c48001840364660401969030b00807151075007036507480c84003295102ca40e648910150410030070410690419075507840f2040302c510305001088020b055441e420000440d5004d50a00e031015440d010360504620f11700c0000302d0700d20380c00034403038021040340c0d24165083d141c11103505000c0041c00c101c8a0b099542c0c81c450011101049600c1c06400d1904441d480c0005401604503101450080740410000704002800070b0300c2c0c0020b8100d0340c1c07103e849101040c8801080e0000406c1401078400e500003155100300d4000140e060700b001c940c030156541d402079030303030030005040607400103000c00050012076182e40205401c1440901100d26043d91448000c080305019926000012868000c041c1406a9039078000b002e094500810130001052500281040403094180414020f00d40700141548070310015841c0e43c04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 637125359 1250 637124109 637124129
    0x610090b0105160507060e0d0201020d05030a090614150108010f060c15140f06060c15090c03030a120b0a050f090c0d150302190b03010603380310050603030f0d06 71
    0x1190f0307180032a1500300c40c3c0581c000040c14810702e41c0745031409460b44521240c060300035012484004000702c1e601d92000b010a8a0261950f44210000e04603110b5601056142c1c0081120390816007803641d540c1403194401030400c40007400500522a4440040045131420b00344500d103140325241c00c000440b108020400780a160100602440c04002e0b10304d4410702c00011010a039a4520040000d01e0007050400e40d00341c2e1100844408104103210503d410280c0302085505c610041d2002038503507840301e544400094050303c2811500c00140c05001c2c0894801c440d841e900508280124110b1070095400381d00c26841040400c000e21200001c644101603515002d10402c8040840c03100b00c440e26100490040303032041888071401055040344000d999903410715601e141d20b441c0341140a80030b51035a410b0107440220012400c150201840704c01200102c0003243e804546808043c1001060020010510700f0b05007000b40503a404021900c0030355a0715003c54032000794081aa00400c01d54006060103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 637126609 1250 637125359 637125397
    0xd171c090b060102100e030405040905030c0319020601060519050d0e031611030303010312050c25060215010501091e0b39060703021b0601090f0c020610090b0105 71
    0x20050314541d140c45610282c00301c07511603c4603c0030340211007192400700c01a80082c0011f2103507107401d4000071502401202180c2c1443c68a042c0c10781503a21448046030900c1030842d640c10301d0b41e01441580d00514940c1007003824200407015864007800c00e415410b0402400040920406405601c940705103800c3d601100d0300d4212081c641c1c0f1720110000307001e4580c4088006009858900007040707078180c9500104541004d00c140c482540c9030340000c00103041900800c0901d14001289a03000b408a05075a41403009452414101a09108070080840002e41c614401070004d641c01100c81011103031840004500c020040642c18000c940503027001803080c400080c4445c12101c00f0481e1040580384485184000341c800301c0c490350131050b4080c8840540c0140001856450203503020b0180300002c2e0620311540c00028091500b070240136040003100d181d80d64034511a081aa1203115081d2101d40000c005505060b141c90742d8040c82d510400002d40d40700e21400302c060340309609441100440b95272079041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 637127859 1250 637126609 637126613
    0x3030c051b0708010b060c07051203161a0105010309121101020f03160810120b070c0615090501060e0310180b0103030915030c050a12061203031a0d171c09 68
    0x31002c2c14440c0401c01c0d802c15128202c40c0c0340c09011502c1c4043c01c41c0040c200b031880c020601c00118080c404170318040c0021b00443d10104a119095100729209071030400021001e4403c400010b50306030046410503140014030300c0025801d240d402803110b01ca080c42d010b0b0b544ca0405032806841250884501d010010060140542c0400d4410400003040d48411242d07954081034003140c40b2042c0300e101c0140580012002c00703e0140e079030750f41c0c0050041c500308010360642c1d00c41d20241c0340c18584d03000c81e0410616003000341907003603c5901d000d01300516083c0c1e0040100400280d5680c1c950444031003a50303440e00080718101c05100b81c905000e07440020040a5a901d083c0030b0209a0f2a20810210005045009440c18440d100d14080d410316038840c141088a03480e0110340c5d500800140442c0190384003400b00301140e842c0c0c0c40d18000b600c690303804200d2207400c2205034020302100b82c61500885c503101884001a1001081c90712052042030b046845003040342c3c969a2030000050343d203268901e03202c45407023 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 637129109 1250 637127859 637127863
    0xe031308032d0a05070305040e04120f021b0108090106081e010b0a180504021504320102070b0706150f08190b010b070609150203070f080f0403030c051b 67
    0x81052628402c0c048021814100115260500c100c1d0401001c02c00035202040d004001900303c0318040d150140c14140c07030f200a0100c0c4981070750f0642c1c450b0521418189800c0d07006010301d4000140d44007401c2e99410804860121a194a110905211440340050a505400d5000100074601c20003140d0082034180c01a441215001e14240700550800105490034106811500e0840f442e08050110415004c1c070b50000600e80500101e0f4003040c82c41c00c040170850080080e00c09410204e1450100680700003208014202c1d80211030303400c0d440044000c1040e078000c031301c040c220340d0403800c000da444005240c03030402000100c54080c4288510300e4045012003010700103400383e5986504032120021607070481102e00300c10140050012080c00014803144000d40058688140310310380228408080c1d40d00e025114150b00c0702c62580c1d41d40401008415688440380e28040c0c600c40c10558014140107607030110b40710713004001806160312050b40d9450f241c480c000300c607222041881d601c501c014035121995 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 637130359 1250 637129109 637129117
    0x50a05070e06180f010b030601030207021f170402090a052703030601321308010204380304110117070f0306061407020d0201050f1303050129040e03130803 68
    0x50b0040802840e4081420b00003400d15004c0c07442008840416031801541c610184d00040565040507001e1010900503101c15610447c00d580c2c4401009441100d16401071094904500c500c1020100e03005000260301c071154840d801a901030008a095a00e0404070070581280b1106030311543e0b4000b001d00d00c44400440998000c1c042641c0703207030358040d80250302040b4002e0130465030120f101e00d5125584c4000e058004002c403071a00c40c900540c0c41d82d5804002c1c00c90700940d001c0410800e8507448040c2c610b4800880601803002d480c45010080700c5040d1443c00ca000040009000d80460043c0c0b10241c0c0c010003080000d000c080c44144041d143c90480201001100007000001c02c1c00c2c2100031450500807000e441046c456814090708166175a001c2120099100800f0707414054100200c44a0090007001890764418003103d0015042c514a010f6003110164a044100c04180440012025141041c4452104401c4501141c3c101c440d0322281e085102e40c40709032a80002d4a00006090040800a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 637131609 1250 637130359 637130371
    0x803160e060a0518010305040317190e07090c0908070b0c01090f050102070302010c020705030a0602030a1107080703020705220209031203070909050c040302150a020a080703091e031e050a05070e 85
    0x344e00c84403005606842003070b100140031070310034583c03070742540c3c01c0600481d48940e00c001d05000801c0b0130035a420485049a02c0e4107603541000708180500d8216005c0c5818004d414500a5400d600c1c0002c0c0c00c0d110010790041e004001d10000d0700c52000d002c250400003600e90000341000c6058580e14101c1d00030341c03254102720050350800309603510f008e0021030800120f0f0009000f62103030894a9480f00020740c00104140c21640d2b440032814941c02e00c0d0710150100d01c2c412004c02c0d64600490602174644440e0b54000b03441603c078840c4443c4080c2054000d280c0c2ca4802000143e01d9849050009041c04c1154039003a5000345c0103c10015030a0344103813104110341540104101d15150818240500d1045000180d00504039500704051810320300b00400c0400041c1c0305a03001d80c900c0d580d50300240e91008406600141203020240700314001c01e0461400d00b60985440c101c8a46590385901c0e13198a496010f294540001096a003405414055003110740e50113000d5440c0b1545400140d641e82100f920a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 637132859 1250 637131609 637131637
    0x3140a020715090210050d020c0a050703140601050a26101b0512060603041704030c030605010801020306030a03120b18010603050924070507120e09060a030803160e060a05 75
    0xb80695070074440c0e55122034019000560a65129009860650080c00da10448903400c11a000f907201c4103011501085110304054440c3e6855410b00f03000d030300c0c0c241001d5030a0b42c0000d40100060381d2001da00000301c40e928940d150a65192591a40b90a0b414924070140ba000b0409050b0300258585e00c0040641e8a01146c62020800c00008075807900403c0303c10400000142c000c20f00500d400b00c051580244100c00b403e8103210152040c20540c1c1040d8021524005103181c02c0c4104000b80c040e03140500600b070002c5085103040030000e51303110351540f401307420300503551404000f45001d900072a4008030043c0240003110100303160401b41d10400d205980009142c0004140300c043d02081144810b11242c541c1c0c1d07103001a0b07010a036400c40740500028144541001280009a04081e40d010101c105840d00032602d40f606040c852601e41c000c103000e00c10014440c041c80010081c4040d42c0d001012032000c002070121061060391a0307107070181071651100c804261041e0a56021005021a000480c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 637134109 1250 637132859 637132883
    0x2040219090f32030c0607110f10020a060c03020c01060f050301060501030212011806031a04050616020a2d050601090c0504051e0438030304060905010c0303140a0207 73
    0x101500050100798010f61082103003060311a40000d0300c4925620188000b020b403110400e07100e0010b0f420350300a65040304d104d4200c1945602500c3c115035069851001030350111f44ca803c2c8800025100c0304101d2000b02125510300940c0343d254480d606039128041400002c0004c0c5490b911f0342000030070786111325803181d03003040c50201e032551181c000d8030703d4030920320150b6109034280000b014440b042c41c0000078a9035550040080800c2282458040b00301d40c60010400c1c41c106800d0081c04d15034001c3c01d405800003041007600c0d0039a40001c20307400f40d6400040c00c05010f0354001c40c6034500c1900e028040b070704109a01880090003000b04803d03040f03a4040d64108541042100166024000c0d40300c0c240d44550011040111a8060500544075040c000c00005032031059814049107000545a00e01486000d480001a510b030340c40104804203904900a50415250000081042c0800d003c2d441c10460100c600108150198000d1601100d2041d06210300346804601d1200942100300c0c280c070074544400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 637135359 1250 637134109 637134119
    0x10060f0801240b070609061d01150602060601111903080106020d030605061204050c090a02030105010e1507110105120c19030c09030215040503010e010e0d050c060601080402040219090f 81
    0x100d480000300700b284941c9040c0900e810200b998940000205440040e01c0d40488000502240700c0e5074400e058001c003103001081c00e140c946086940103041c504008100c0d100078070240e600000d041c3c0e4045400d207000c0201c1300315488114203210f032a0303142c56040e40203028407030b04140d00105054140c0b5460b80c2290b111000031581101540d00c14030a0f039400400401a075440d503540800580d03405409001143c440480e0200490b0423101708403500240c1e50390200045c401c030f40e4071141c00400180120358000d0b0034018900303075a02510800074010915a01e500f01070b00306034020000e80790896443e440108043c41c00229a44940d07200ea140340901c0030020200c0b820180c0a48581070208170280d80d4444100e06541c203020114018900c3c65a038014203200001c0c1a540c01d0041e444c1c02d9108400101d511000c0d800024905802c084940e4140f040c14460000c0d8281c0005020740e1080c0c003486d02035060f4070307680080750082c071a29032306080070950a0341201201c1e0b0884001801c6a2120041030386540c2e5807 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 637136609 1250 637135359 637135391
    0x7061b17040804050409083105030a0c0e09150a090303060614221502010b100806090a18020414040506160f0c050705060a230418020a0210060f0801 65
    0x200d41c01060540d041c4000c2c00036040a6024600c01c80c8241086890441d0950281002d00c21036000d40e002d1819031914074140340d10001280c0001c0c0743c00d4004125100295031411a070360118014010041c04d04070000d002c1190402c110f1414201a03a59428142411a6560041e02011100b507021a09203800012441e00c04d095000300d4242c8208100e0401c0036807003044800c0d608005200c100c000c0f005901082802e0084040b103901c0300c00381c000003140c00c2000f0600c5200c80300e2510780c1d02400301150230080241c68911b040b50303110445220028120000d04025800302d0f089030000703900a0720380340e1100402105e0341e11181c02a070203002204c85580e0780503940c40c803500d00e04030501c1c0021000c41031110302d1030140d440151406e100e030003541d14281c1c461021400130b42004d01244000303115451464114090300f40e072403123402100f00350985010b0820150411301420082441035603a4006400f2510520a108460308071070542d40c18040b0607525130480a42501c54091421903518090450a44040c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 637137859 1250 637136609 637136611
    0x8030f1b0304023007060305130507032d0812090109200a030501050903030613020c07150c020907050c0c030102070209150a0803040e071b050601030602090607061b17 73
    0x40c90405203960303a01d90030701c0512102c00031450603d1081400b6544004144202d008448841c60b000748006403030504003c09850300a0091001c84440342003030000300304040b4030741007903981004040941c590700c07001503240218038807504468403150036018402c10440c3c0c0d0017064400340e01ca41c41c450b90b0301d0740c1010b00d00321980c5400040807050081c002020709104504890001d40303000301040f640a60780d455171030a448044508040c182c00010030404549486030601c64000303402030045007007040b40342074555a02c519010341d034401861810a5544e05101e21a680c0c0141d41c041e0040c0d0460400441c003508940040036a1f000718001d1105560b51030a052096a84498009042000c2a11128411031401c0402c082454200e4403c03a000300382c14001f000100001c084c030b40121030701c0d458031140c000e0054068000c000075001c22403413881c01280000a050381926080240140e4444440c0006800341c0300d60a001403800d8100709000b00e282508480d00c0ca5103d815403900303010751454140c16801400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 637139109 1250 637137859 637137901
    0x406090e13020f1302030c03060a3c03021305071b05072c01080c0f0103140f0901020d0c0302041a19111504080a020d09180e07050405010308030f 64
    0x200c5100c0076805840c20324049a102c140c040e0100c18020724a2103004140d0340b0031255018500c1c0c0c00414072896003041c2d041400208401400070418589000b5061051004002c0b0a650035460b1901740302c401c1120701d6000f00455002707018441404008400e0006448100e60711800f25000700501c49042400c0f411400910f80d2041c0a860660306010001c2d40d16141084030055811100e00c80600e62000010f00d103019050310030081c0252031400f020814030348000d08606041508041115003c0f004481c0003a40000348036180040740e6075139900c0c041c028011084181c403194240074020500326050790042c4140c07001a96511000e0025010703506280c4190f400344082801e400072402e045030b2050841c1000d000070328096a508000f25440030528030300c03e80d4103540000000814200250b010807040340040d0303650030400c008920700001d404194040080d042034054a40e80f004400c10024000003010380001082001256168203201d0750303503001141c100c41c802e40ba4201081c0c40003120007520701d00300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 637140359 1250 637139109 637139131
    0x6191106060a05060c0309190801060602010b0a1413020307090504050a2a0c0807151508060c090a0b0427050c09010e1c030e0118033f0201020406090e 66
    0x1501d00f405009903507208003588403640c0000d00110240303036900c0b01c10454a203a14005a04220f0801008608460590f0f01030003d580c5012124480f0f074482001c50000c84918621034440200c401002c9481c0503200910411100e10003c00c001701d0705d41000150040c1d64058808108030b03520030700148101ea15805400400b424000e8825040e201c201c82c686681c4106440d000c88180785071f585407929508070f004125449281c42401c0c0086a0070342c403510322100e107000742ca0301801e0300e80f0f1191078075290064881550300b400060842c016032100c23042c0000404c440c0da40d80d596969500c080314000003400840c10840c4449032080c1c00c07030b1030903409824011102d001801d80b41a80741d400640701f41401440c02504055090610402e0070024408040c90500a031185a45000c04000046c10034a501032840000c0d007000905202181d603034400007480c180b02c003d072a60010207005800100d6117103030041c0c0c000d0304524507080e005550306401034400c449482d12101c41c01d54440340d0001c1885400c0390244410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 637141609 1250 637140359 637140379
    0x203100b010e121518071e0b0901090317040510170f0a090b01030507170f030301060e0a031203050708061507080306010509150403021f0206131b0308120a06080307150b0619110606 79
    0x4230241e14018a200b0b8014140206190b41d2961007242441c41d9901103c0310340400300b403c1040307007040300e011814410680703000e004599000ca03e50b0030060014128507000d500c0080041c4200d0780d5503002d500d1003500085a015550703560314215589540038001d2280c990b8400c0130880c180c0000103420b2420014a030302550131a13091043c115416141001025030112410000001003400300c085560742601d542e40110717007481c2440000d051120b0242c55640103403035254044051081c11415180c4a0303034002550740d039940750200101e0b02d0380104601194020486411051801c0080c801002261301c01d4407201070501050161031111006001c000e005130b00300000003030540c2103411004a280344915039000201403c01c00050b2141da00b078108460788480000c0e222142c100c175107810399109100300c2040c88403500708a41c154407406040030003810100304800d1880c0c9010583c00070418550050245c0d1f03140c0c0c6807180d003a280f010324905840c0c041a21410005907a40340400c401d489034002070000c0301c80c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 637142859 1250 637141609 637141619
    0x30613020f0a030c02070504050a020d060b0901021b13061205010b0307030c03020d030207030c091a0405040c060503150904030e01030b0a0602030a050c12070f0203100b010e121518071e 81
    0x50244c03414110118040d540001c01d8541d070303d1240b5801030101d0707140180c4500c1d010f1541021180c0582100d80303c00c00c180078000d5640e038001200603110f00004d1494014284650201e400c540031420482d000f14189070000c115000315856203002076009030001c0c000411000281503e486640c0000703440c40711106002c2c00581000301c5c0c502002403281c412500c0103a52500c51790030444c100d40120440c6611100c100c142040750700300c5044508011030341000541019a030b9828050003c5c4203410501c4400310000740100003a0300c076a03c0806d00580008060710345031900807d40b42510b51000d000ca49081d07040f00c16400c1002040e415110306800440c508640000256030a4005040d80e440612401d0031103030300500301002070010288030700e9a50a02a040e40304140c20281c440340b01505583c40c00b41c40804680e40000709804041c41960b11404005609414a09012181d1590510007008600344030b0800030004070003034405c401500342c03059182c840038806400c1030b4856070b00d6582c3c81e1071242400303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 637144109 1250 637142859 637142861
    0x5190806030a12021501091a030114070c1506270207050d140c01091b0602030315040b040b040915110a12020d0e0a0623071d030c060f030613020f0a03 66
    0x20210483d40100c0d9500342c3c5904040725803c8013608000c04030758440700042c020348118640b066404104a00911003000304500f14404c900d40201032401b01300d4070152903418000c82c44c500d039000c0c2d507810034140701c040c0d140c64001d88d000c20104641196040e83ca84104a000454400c0e940259442409400441c100d03507000c861855402c014801d90843c10072104401d0002441034941480c42681c00300b086080a00d0800e0a6644640c840c4081d9041003042010752030305a040040c000e213048500082a036a5400450010280081d0323103078009245c280c1d01414040415608611018158010700000c87da41c1407880c100c0c018860600003003080b04c90108100c1c2c166401414014240850001e0030302d0209011a1801c0303000e40c01590b0066892100201c5071702c40d140340c6044c0c1500381d0014407090804040c01003002103a401d96203d810084441c851659900340800c019000e002026039446000b0340c2080d000552055440794400e10000703400c030341d54440300d00035104604107003100d960800383c9084c000d034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 637145359 1250 637144109 637144133
    0x15070e01120c140c1507260c04031e11010302090109230414090f06070503040f05010608010204230d0b0412110a12030b240c07051005190806030a 64
    0x1c002d004042c41c075203600040100240c585444c00b50b000305250509000c1c650891040500076904102c000c10b03040d5141345c00c010300c402c140b50040c41014120b65035410407221303c1c021508024400c04c0000010300000c2e0413100a800705038000c900280164002d43c005404030300ca401ca8031790101d0b030005d401300554000b401c43c801c9403100800c00c1036118103440c4006070460b050020001041e03150319051010855007017003e00000d40e840740040000b8145020094528040104003d210348440c424050070010b0a40148000b030014000940d101c40c1c8035400b030a842192803484003005242c05c4203010301440c06a010241d400c2d0441d0005045894a88508000c4040681d41c0d00621580b112010f0075640b0800040f91218000c88070154801800c0000609464544040c14810003404080031540c5171580c4141d09812140c00340c06a503440120310b100d050450036800198821611003a0442e0f464102c0000d04515015017002c080003c22041e05558202080c1d40058140e0311449810000480540f011 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 637146609 1250 637145359 637145381
    0x6100e06090a030602070c0303080112020f04051f0e01151b0201050a050c030f0d060b09011707020703050a0c0801050606030103050304090207150f0e190201020604110f0a0815070e0112 81
    0x301401548030303244c10742039a01030582218014591001001450352010700c00c0e0240030041d102c2c82c00c07804240c0018541c400c0701c0308454403984c0d03a140490102100d026442055080f02003044001c1580c486a0748a070a6091090b42030340121821411503e501c25601003500740015030502140e55600c2d00119840e41040c0e82c00c07024420100925824400c2c100068242005080d24190340c8400c4605504c0030789030141e001c2e10303e181040c401000c2c181c2e0000600000180e104070008440d6403240400c0b45001c07041e600240c003a014220500003805030504115065402501c024441a00c40c1c000380566440244000740143c3c206100c180008042070300241503003405010b00303614200880c04014110382c5819031001c40c0030750f42c4925102245c0107001c08a9500710802e160040c6050b1a00044c0d11801c00810007028407104001218440d0b036108800040000041c0c03203548841c1e01c03560825aa084618001540841001c0c00600014441c5940881e80303241a95980030b12200300100101030881c428030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 637147859 1250 637146609 637146619
    0x1090215070507031b140a0b03060d150f090204060e0603071e0b0313060c08130b04080f0307081e0103240f1e0f0b0d0f06090203030a090e06100e0609 66
    0x480e102040301420780c140d0021040390941b034078459502d071102001c192806102c0342141000341c4581401560361248059546a4102880d03190420607006000c800b1420386107010a9450300702d100e54000c0c0c83e80352003a2030400c480d41d2100742400f51160200c580d83d80c03645c007118040c411503200080c880c0801c0105200108510b031921000d12454104076000502c0d1030700c0500003418022180299281c03904981001002420a41d0000d2310303140c1802006400d4141c860701240c100400d8404880c960b198150686441e400c200e4070007080001c081e20010421105040c103900810412200d080c102c2c1e501200c40d00d101c05c0c070b2042c800035134035903044107500f20741e51034450810704100e6010b480c12940b80000b442c0103201208a4150481c2d540c803420908180c509070880b486501c0d0060008070303451b0001548140703501240b0389070000d0107240c1402505800f001c00c109080f0354021507417409a032940b000e824550340e14402400901501c10801030009900c00e0140b401a0400d134000b002d5950380505 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 637149109 1250 637147859 637147873
    0xf040614040509070e0102010f0b060307110a120504050a06030e030d05060d0f033902240c01061a121f081507020c06070804051003060509180f010902150705 69
    0x980c1c00c1004c6800e0400300310422005481581e0a01c40c00c1ea0f60b4194500400c1002921404a43c1d9804000c00c0c55061110103035466507540340401000b12000e600120840c48050180b60042c8950071610a40c1e0090011311004101c281c00782c082c01c2440b000e03040c001c50030a80d4119891015040292440b9003140361000d811010030804120301242e00e00030780f02c1080406500b140021010b500f40c90700e0006901402c1c4140c800c103800281d00030b9241e01290030403c1c1c0900d00c040442c000b04080c40d001410100021071809408040d04050210707a51141c04100701100100518032904c00c0748004c01c0b42140b101d0015a002d03508050000c1d01c481d241341c00504450f1600d156a141030884220601450f000401700402142e04000d1001d9550094501030705040682d980d0414600a90050b544100912003003011201e2003903009500400c8010201002030405401441914289034030041d040d008616040940070814000c40400f04d9000e4644801c20700e044001007100d0300a540d040398a400703018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 637150359 1250 637149109 637149119
    0xb100c0f021c11030c01180b03040303060f03060609060e042307180509061503120f09100c06110313080711040c020607021501030b0601031e0e010207020f060f04061404 74
    0x101d800840f40304912212a03802103004051400310030060250401000c40009072091405003442e40c111101c108031640c030303034445103000d0703015081c50b4000c92070b0500e10510000c14028641c02c100304503000e00800f008443c0d1115a9040242400c56000c0c08840390510106600f0000c203500a030045218025103c0181c4c8595456180e8001902441c00c0d05407500140003071a5014400c41c0d800024a4034012442054a804a51030340d41c86402c0d040c07286000b00d000d0f45c010b089081240c03001040207084680c00a03228101800c0842c2172441907694921700000c1c55590102c0c04100c0c0e0142010004101019640350381e615640d5200c80d1048500c843d01c13001444a0f81c039180562161035400350060003030303803900b400000e1800c50400c0c426010307000c0700380c010000306424480d2290060801e1902068007205043d44d1201d561003649595a100e190608903002c583c010740c00303865510b1007290f10310080131121382080014001d85d040d12350095802c100401c20280184035a003207081e20a4211070916a41d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 637151609 1250 637150359 637150399
    0x1a0f060f18240324070c020303070b010905090f03300a06060807021501060c03021f0204090c02030c06010e2d0609072303060d0501061502010b100c0f02 67
    0x3903460b1910307040c10366580444990492034000b4004002c2c0d000700b0300105082d0071300e0050802166070ba84ca286400000c186854860b01c040700c503094000d02200e23070b510703660314040d889000c003442444c010510349000300d09036240214950807506200c1c1c000718140501c8180c01c81e0a00d801c1d40081c6002c40b0900c800800451925030b0651141c8000000095054a00400a003007102c0007000307a81117401c000d8482c0c0701801c0007040315042d2101784c80e100c8443d40541c40c044e8608416000c000d1124402180503120119040d0000e10684016003402e00200d852030109907524058003482d0b00035504001e00500c462031103c0f030080c1c5d2140c1c01c50044020800134056407400d0f5917000100b982c10b101e43c40e0411186080201d002038100340c0e80e1a180b0000040150340581d1a110708900045000700040800e0059489406100300260820000c000c10741ea10500c64041c0c2c3d144000c410095400c0c0b140e28a0341d4500044060f001c00340540b9442010400b5a03a044415040008226030000e9121190038407400c2d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 637152859 1250 637151609 637151611
    0x121b0c0501050307090e1e070918051003020409110f030d02100506061306090609240c210c050c1207090209240d052a180d0f1a0f060f18 60
    0x84440031f40807200a0f04c0483e41000c402842c1360240008503e003001501324281e45140c00c54004000018642c807890310240800f0702c0c5900c0690f00c2810100030000340036000c4015240060125003017082452500c1c02d1640b180140d8100c1d40140c0c000c00d02da0b00c00c00c200c9411031a4400380c010181c40c90012456411417900d44681c000900003162200184122900b081c003c0020f4414102c0c10700354460f0290011584d0f40101200c0c504004040c90600100154084804e600b0003801c0c082d0f10000320031900c014042d207805241900c05209400c00c000040c240010103001d008199409001070f141003140c560060350020040a0f0041421640e85040c44511500400807010304003046980d041c9125811060380c00c00b0341002405288050020610f180081c0c0110461010050f519111482d4a0fa65406001d100f04460307000a1081d420b80104040750b00d2104105100c1c8100700d1841191003a5200d825008a40d80e81e1305483c3c010100e050f03482c11350902900484003c1c40c2d80c807100c061019850324101c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 637154109 1250 637152859 637152871
    0xe190f0b07050a093005120c0c0315040503091e0607060203010825150302041509030201020d0206070206010528082a060a1404080a121b0c0501050307090e 68
    0xc0411011412980308402c907000702915080d05285144880364400781d41c981549105d450500c0d1100e1900b0403105110756100506d401600310307207030b08603007100c1d82d107940b44040320610a0145507050448240d02e802c4045c0510b0b00940158140881c0c0743c144400241180d00d02c43d180003081c2115134590341d81400810b0424410600580c903545045e42040c540010208100d840040076022854481d8604600404845050084460b12910707490240c000f0b00c25074111240500c860103004910b607800840100440303100ba400ca450780c5640c440f040b40c49801c196070400068022100400552034500445408141035081c81120301d00f54207544002d0004c2503000d5071080d04903000c540c5240200100d20038807200000300700b140d46c10708000040c03071a100d9045a2810700908420a0300012a40002e45003e040c2000840e45154118249400c1e20003513a01c4480025010746038018645100c00c0c00b43c10219446554911203604000c0150703402e40008014800308440c055001411450190045000716 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 637155359 1250 637154109 637154117
    0xb0304061d06071202090d020406090507170c190e0402030403080601090801110d0e12070620040302030a0f0521040f0e010b0403060c020a12051207030e190f0b07 71
    0x110070100d0345503400310400002555008941000b00c0c20350020403502c0d054a050300010f17550910f60740040e003000640c10020303411600d40b03c408540b803501035001501503060350f01e8001000e00600c0c0310b40c285c03140460701010003040074081e40b81100904140004c815503541004011660100041822031300115400c0d000504180217204283d42c00c04000d001074a4104001e1025000748581c604040c402c403262041072035602c885d5004502e1003400140c03d51038220346030964681280c24004064894103456148503c031480c02e000d0205a608100c50850b45c3c050080c141c000b01548944000740a1158181c8050054400c00394020402e07480d00702d100d0800002c45616942440c4121a41e40c980e07411090000b48040014860080400144c80c2100e070300c030f0784c003042402c10322004034240f4503801001407440e100c205a191089401201402c806070300b00c01c0c0300b8226995400202c041c1c0b03c130b411403015660064008210400314650201d10828001c810f050305214255880b644504002c8030040b0000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 637156609 1250 637155359 637155371
    0x80f180d150b03063601060303081f0f0308070609170c12040f05211507020f010615030b040207140f060a0c1403071806030615032307090b030406 64
    0x950900c15180c2102c000d0b401048a4988880890403000c546460301510f4441114108228604203040189003102c48000780700b50343d900c0c900034018030415201036011103822100e400c0704224411041c0100c5081020008090745507031100a500d902c40c1d00300381c0b8416103845012000c0340d040c20103071050700449554107664a60031095036041c400070320b00f0b0900d140001c00041010000d00e03d03260381034440440302d4003c901400a80310030040c103006040b103124015021103c070424004941310384142c205409a41c0d1005003040c1031800c8801a01824070301d0401c0d60190100f1701c3c030a40c4840850310020700010f143c50f100e501c0d600c070100d540e5200620682e01c0202445200e800600c003250300140d11110511802d10381c040040e001c0580d44410036228000440082d02031841003403062864005084084406501d03101c0003000b9108034050145c6c080b101031485102117210348990500e118401d0700305024128900002c0b10700c082e020340700e0001c20500c100e010406802501c002c5001d42d00c10074001070300c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 637157859 1250 637156609 637156643
    0x1050c120c011404154106032b050c1b041b080a0506010903021804211d0a05090c09030115030308130618030518040207080f180d 57
    0x203486984030000f0100d021401804001411150480e640709010000811200e4900881c84554001ca881c1c1490380030264204d20020707541c8a0340c01405200c0c13040e13a40190381c1c803541415614008800c4640e04500040d010689110042c0d640c60110f0440380741032458103014109107490700009404a07506400078211401091038248202e80000ca030030400118100042c04020f0042d00c4020000a078081d280c40011301d150b8480e0524601569000f014040b5120203410300303c44c059000c0701e086400d41c1c141c11480880501e41e546002c0031100d150b42d0b02c20080c00740b00e60070089440703004070340703030880c15460340070030296074886000c0e01c240e403817403140b9480c0c41904042501703540140f0310403c0b2003001d400c2e040c00400e0b4402c0702c103a070010b5407011008400d80c41e0b00c0d1050041641103c14940c40c1460b411000416601c4802818804088000c62495050a80401003244100d1070010120b4900700711007031040d801e520260805d07403c0b40c0015142c080303280d800305091101d281c404503401002c80c018030f81 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 637159109 1250 637157859 637157861
    0xc012708060108010e2a01140301180b01020106050328060516030609020723071a0c1b010c0f150f0204051002071a0706020910080702060c2701050c120c01 68
    0x128024140014129115800140d1201b8285001040e142207000803d4a81603405801d82007141c40c2d514500703031f56030b40c4d5900d0b1380307229000b02c104150402803d19250b600c036584140200740a5580003005400c410036071450108004104da11444d440602003c0810003286192140381e1042102903803075810006000002403c840864106103601441880400040b03030307513584010892005504010f00f5604082185072900515030b124903402007c08002c0366400c0c00c90720141400c004200102d504040c2080940149090318000b00b43c001043c00c4004000b00f0f0140030f01240301802000354000f04024a04c911003581c0f50325202408098000a003004582083c410100c2d4642c0144007800700d0b9030500c1920b60621612a1038452642400706040d803c0c4800340d41100c1c50344100170f0203c2c00e190300d00764010300254000c0b5150000740c000c40340000c5e20f08840700c0441c0c11b910000580015030115800c0c040f401c030600701d4002da04000007440802c04065040040c840c1c910400c10100361100442c01c90a4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 637160359 1250 637159109 637159121
    0x5060f09010204180906090507291602150403050f060613050702060c1e030411120d05070b07090e07030510080d09090203061507060e010515030c01270806010801 71
    0x5582c030400c410000010b0503d250600340540a01c0480c41805034200310014000d406400340c241c0c0680080003400b1940b01044a81d04151000240e4002d41014407a03502070090b650521200401d02c0ea410006141407104a40c1c05481ca0b41094281178407502c03040d1801000505983d081c0d4052000d10015142c00e03060b4070b450703040c0024103222619000c20000d40f68013010b48100c440c4407011424000c07a00052000400010055031190344070310305410701d0624007a41038140c6004040c0d9070f41c4500c00900210709080010f00981352036180c10311075925075100c0e042c01403084080104419001c036140c00070049050140c040c50354007003200d00b814441804c032080998020419684007034800c800d41900444880c049070f06180b0010f031250f40714004541c50061203c11841000d1001038180100f00d0150f000011f050480e0b402000b0a0762815110b1440800a4081c158541d01003075240403103610404000c1380034036900100c041d0300a0340101440c0140c0080c0c1164619070170180040c4901c1109101d40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 637161609 1250 637160359 637160371
    0x20c0f010507120c0e010e04020c1b150c07140a0506030910061403150903190f0e040c05071104090b1e090606010c150b150d0c09030b010504230405060f 67
    0x8001904413608098069030454051905000e60104440f106684580c1030340c0080303054806940341c0f0084402c80300f0403a85080d0240d40320309d0072142e8114031208404203544685000100074414281040408451003201400e41c03903021260704001305550b2a008051801441314034014621641e05a400b48240c44a68002e07c030041032810800300d082c2d03800240c140039000b102211004580b0740001490451203204401c0151443c4200040c60703003517001e401d059a10724256218081822608200000e54520041003400158144074041c0418104c5146405040c0d00520016800e00503641c0c6015804049a10b441e40a04106566101803c82c140e9a940b1280450103400a4541240040d1020000715000f80041c10b000d0440352114010790b00c00c14056400901b00804108000e0401c1b805a200c4001224814141002c1c2c40703025008980c0c1000382e9a0100e0284166828541400028014840031400f4160420781e480301e14074001170428007590003400900f800c1d240c50310040001034005004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 637162859 1250 637161609 637161611
    0x41e050f031c14061c050a120e03070b030112120c062c150f060a0b0f030a0f05091507030b0405010b0304020906010804080304030c0221070e01050d0305040306020d020c0f01050712 79
    0x4c00c907050755407001008500000800048050145003072680ca0100e8005c1d0003461000d24555908405800c41904507005004501f290005500ca00c00642103000a20460003407048580d03082d00001c0d04180485030b5295689824040d0700c0264607100186c840640c0d807004d61503120780300601c0d548801c03690f00c441561094000c0c444108400500e211800000740102c8501103050081404c95850700006402030031000c081d43c1c1c0324108000b540141d0360054505148840c41c0442c00403281c0d0041c0a05441141000c015080341c80c284040c51101d000300408041c1019070311042c660b0565654811305001c0c00101e41026207131701d054414800d2096006d0f02e840d042c4181a0204030005003c0e80480740e00943c5480d0650b111520780c40865240d0000d01910301402010703401414144100140d480121001e411003840d06076071310000e1260003a400ca102a0014800b00000c0c0b0110744030350000d20034a012000014a800d2900b00c40504040712250701030380c2e40e5152418094100e030301c682d00c00d240c0404804 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 637164109 1250 637162859 637162861
    0x601020d05180d050c360c0a032004080304080705091b0c0a0605090309040516050a0e030304030c030b01060825120e160815041e050f031c14 62
    0x1540410340c50301000d10500c41c991003d82001008003c0c045683c00340c1000d84508103041c0d0f2003050440c000c80008146030460703052400c00e04155807800c08980154188a0483e18040c0c0b54081140a44003040d800b618281e10380130250b1030003405100070002040c0003400365844030308000000c3c2c28062182d101c076103e803c0f000284050000e50740c1514910b00e0114014641da5a411b00c00c0900703044846901074821450314040102226002c0010500c92070216001c0025a031003609905446181c0746000c000904103004c40203034a0702821000050f100000d0071641003656903650403c1e560020b803c110391281440700104100d680090a06400180980b007841e0545142008945040d180318416800c2007400d0540800e06e0b03c4540c401e0800c00b0202060f1100380380d5140c0b0200030900706106d02c41c0c0754401c0702156a510300100c03424900a0f07920902c000c0079000c11020710022600d02c408203680502407a144006440000c000400c80180c501e240e4110486250340000220790b610720340b0356400b1121030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 637165359 1250 637164109 637164127
    0x30201140903070b0a03150e0a15030b0718080d0201020a0f08011802071e0c1d09100504230d120207020a03061e090b0f071803080318150601020d05 65
    0x400d0b0742d800e81da1024130607511803058110440143c50f01c800b01d41101070464074003080c40c1d0703480701d1310740c0c030440e0f040e00144044181c0c01e4000104e00c40030705c4054580d45803140882d4100d8400d1902010030030100b51310141403a182e420031402c00100d0081d29000d82e5002030f880d04c1c8070307400c03c0c6c480c000d4260303d061200c4258940385074503400f5500b0621f0754554a03030000e902070400058540c1c1400c441504034804803d480d062a000c000080103001f420081c6500b4072400c0540e05003070040e20f12403242480582070210f01608103002138a4045e004850541d2008480014000c020082074011071302840188034000710b03040082e000c01e44044041141a004004120242c1c41d424802ca0491b40c0c80f02d4000340c03000a08101c5008040400c0c4969003080c20300c54035105004040e60b8080c02804203000700485515079020543c0c8000740990030700b0302d4208410040011801c84000341d40e21510010300c1d003540c0c4001d00041414584c0c40903c03909007070b26034030912001d940e041150944503001810b25138074041500b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 637166609 1250 637165359 637165363
    0xf021504082b15120b0601210c020f06010902090105041809080d151202091f0b0a08190905071415030f09070801060f120c15020604150b0d0615080610030201140903 72
    0x1b011036040c0b040c9580a0785243e03981b403c3c8011440e0400c4000c200c1e0240d40c80000f900c41d41405c0c1c101500e441500004124504544210f076100031058440c2894546010702d1030306112142400c0351015070f079603c042c6001c2202c0320000c11540c4840000055280100911501540e04641210002c20b0070301110800603102c0d061001d401c20749a00301a040803008024031000e089054016a41d00003010806240c000d4008007064081e2410050720303a030740d0100d40342440456a400b24050150b5001800420502090880044101c040508405490344144601041c11383c029551004200c0c01c0c2410044c0d90b180c1408a0000323807004d01e0003408464074040701c442c4a500306000d904041c2d001145230408025103080300724020480e11100719048134000388003a4440008840039220400d020602da803c4e8446403140f0703489850010828924000d0686520004000241035a003250509040115a40ca02044070320300c1045801d0031442140c0c03c501c00100f1a803036096105039400c10038802d000082d500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 637167859 1250 637166609 637166611
    0x420221d041b1e0519030807030e061b15160f020703020d0c18110d020f280e0a0312110304090501060f0f021504082b15120b 55
    0x1182410001079141c6051180365014903900100307038149141c0000440305825040c0d00364980708803d480301e0b0345507036100b4002c0350401070b144000b82c040c04280074030018044401810549000b4a8200c050b40340150108016501030a10b0340c0c5e544043c3c1c840c000044204002129000720000107035243c5080030001d110303902d0080e0f205101030245000440c1ea2261003000785100950300100640c40850f114102004a82503a006880e448211014601d072b090003136000700791500c180000f505d86031120381c0d10080e00079082550b441c4e0408004001125010880b11020240e41c4203c00c10604028004007000e0400c00d66500d46e01e0048207000c00401c04941804600e00000220b4100144040210b840c124110320070340e040580d2240c07511001003105a0300c42190501c0340800d0300d81c4242510100b1003030342e80d240c20601c04100c0c550401c0016000418010181021400c0842810070b00d02145401600c0c010400c00c540000d070ba46c504001c0d289400500c80d1400034030b8002c030807860b100165107a030160303040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 637169109 1250 637167859 637167899
    0x120a020306010e180402011107030819050403080a02070609050a0f0e060f120a0b0c0301030b0601030c051306020109060510060801060807020c18060a06020f030702040902042022 78
    0x940400054090390182a4920424030020b04080407100050142180e64406403400d0f400504501c1e50309040c094001058429a40c10070151740c20642c00c920003e07030901c0c03454894810850140000000184400007030032040b2070750380280000c1800c2c400700501d038a40c01d60105120b120642d40410400300c07140c02010030740e407001a00030446e640741d20114507416203c0034844d07000361444840021580011810440c828807030801c00300540c41e00f00800010b40000c0c0005031210b003180b00850345540c000d41c4041e000d46c80c14101142042c1600c114400402c046910200c00361351550b01c080e0030070120b40700d1154050a9401d0080320241013040003400310405018400031702001c04041004c01340200516156500c000303022a500401080e80b0490300c52007a100c95020729244880420101e0022500d130010781c00c070034000c1d806c09a2503020080505041d40c41682c00a42d40c81408050748440146504200c41171800e456484001d1301403115074400f4610000082c0141c0682884990466610701000c84 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 637170359 1250 637169109 637169111
    0x307060e09270610060c0209061e0405181606230c03030a020d0e06010e06010c0215030a150e06180415090b1602070317250c1a120a 58
    0x5619400c032046a0369106102d840707a415030403466481c10714000343c201d11a40895480d1042980c2e10300d402d50701844400c0000b944481204000340f00350070000344d001460172400c91080750400844020900300e6070b06488441451049041d8028802820005003403003d640942c80c41e8154a00b840051103400541c0e00402045006a21000c590900380152204031070b03210240c0781c1d02d08262000100035400010510704280c144103101002c10004903105d41280c0000300488626500c0e4401100d442d02640c030201d0340000c2035040141102c0708140598400c0c8800f40001507141c0100d21940540c14180d841943e2006500007000201d4551034440c1c0e000704002e220b58942904c4a240c03d24095001c052030b04410741c541440101030100e400c03a0300d401410788070704208101c820100100d0319842540009030003680b80b1500764511f950114000c040c2031011640040403080f4420800c0e4061644140035190540d603170f08248a0042d00c420000440780d4015815441c04c000a101d5250014000f000cbc1c4080e2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 637171609 1250 637170359 637170361
    0xd0512071803080a0c0b0f15060a12020403060911120c0103020a1e030f0e16050906060405180108011514120c03010f050a0507030b01140d1404080304030e0307060e09 73
    0x105803100161006075030b003c40e003070b0740320700450800401ca50b0b400903042d00d280c502440030a248000c0306030780c203026100484100824022039800d100003030f88484058000c11031858011520b10450b4800b400195103d41d0300412100c0e9281850310ba00c11141003041d11070400c1c0b1400c003444c0d03a4000f61743c0e85602d0b42030902603100c0901c40016035100b80030500c05440344001102c807000d1640d151340030031368080641100300a443d0740c0d124240e03544c10901c140e950302c40500103010701c00c0b03113041e0a64940c848070060800d4901615000031030310804c42c8440380f503491540c0703400502542d402801010b903d1141f00300403010247c0740c109000d0410310390030551b6000389014030b1070030b81500d024080c1c51020400503000780079175184441d1110080c0011146541c04c1ca207040081440b071840381c0903440d0034032816500c1540c918090310145140b540242c880a0015580e0440e1903030ba0500444018800d40c014403c00e5181e282c00c0c00c0c00340c58003d1a5206510903080000203210058000d6038406840c032003501c1411322 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 637172859 1250 637171609 637171637
    0x60a0c0309090504030e01021e25090608030a1d010c0f050a0c08030d1a030307150905120c010509280809060310150801060c08210a0e0d051207 63
    0x7500c1019000034071200d00704010407080c55040100c0008400003a421201c075410078920066155200080c0084650492864190701d000340600f081001c00307100400c1c0c03140e1130340c0d0a100000c07506140d100c09940e0700b02081065000f900240b207926900d03c0001d00d8540c0c84000400200004c0129270001c2c03105d5241d0f150b003010300200300005c0740d0507684108054032803521031400507620f810003a6100c2c462414a20300191004120700364084229015004604044641d51101c21100500c00c9079414aa40c400790f000c00f2500410412540a007241843c554441021704464250313800100100015800a46613010b90a0b811449489503c56004a074140e82c0309454905014880e910002354407100100601c0844020030134a50216885111082e46220240c81d059a40c04d000744034540c081000070648102203407000005101c2c0304225804188030302c0640401380700101c000e54a0203c2655144050040900b040040b820b04c184203042c094201611030f4204008180700034140000c10680d02c0c2280c4c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 637174109 1250 637172859 637172867
    0x8070e04050a0606141c080f0307180b0304030e030c031b040b03330705030103060f0605030a0b06030d021923030c0604051e1504020105162003010b060a0c03 69
    0x303000755101806025255a1307409984280d420403100c10311901c040c030144104000e0b06c1ca400c2c20410b034001071281c2404141c20b42ca14007a00005d00000c01e1050b401d50a104400da60403100001c0c05c50720b0b4602c3d841e401c2030709004001705400304240307011342d1103e010000300e41d0f40040e000c0c895600c0e001c22019080e202d0b03008200600b03910070f105605031040845014908030f100104080c4074500f10030030307107103c601d1845c1c91400200c150350460201c2e8003040144003140264220300341000341c00c00003041003603030b41d0046864882058030998900b2044001d0240610b824007401921040910042c1160b50b004d1004a0103071200060003045e400c4041c04004212515403114003035000d0070030640b515000c05141300b40c1c442034211400c4405000d54114141c00f11420480e13035410b16090002003101800d444142c810038400900143d050003428484142581c0701c100c80750032114480c00e91441c40c0403031070b04204141e000001c8010301c00d13410f100c000015602e401007904c15a41c00e92404401c40007e40c00d040e9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 637175359 1250 637174109 637174123
    0xf12040b072003070e04061103040f08030c120a150b030c0a030b0a0902040b0a020c180705030a0f0509071a0406140a0912030504140924060c0706020606090f0108070e0405 75
    0xf40c040c081e00800051901c05c00b1485480345010700028080090340b513448102c1480201e500404074500f2962281c0801c1401014551000311001b0f001c1c98003403041d0000c0c4034070000f166403044140c0c81304800d0041c2c00980084130000d01d00208080c2c11802d1010350101c40c2d00071001000100f40d56111800304a55034000008000d0500403421555070ba00c1e6061403505510900410015100b1982e10b5049800c200c0511a00360301203080140f02a123a080303040b10b040d8806001114200d0701c454001d00c075400310b4070030140211641c0c1d00130601c2074644650380e0340c04c104020400c1c039074640611003040071a03000441900c4901445880f2680c0d40500802624001056080309003202070301c0c8414010180c00034024410b4680e14480f52024000344020807141c00c2c42118a1400301508a000f10503241b68800400304140c0b0007407038142491102205140b0307200a030b51000700140d1161080c4207003420040c1c20741e50000d402c5003981c0003c0d03041c500b86940d900d02d24401d442c42c481d400700004082c03010a100d10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 637176609 1250 637175359 637175423
    0x14030f0a0b011a1c09020109080d0e010c0602090405102310050f120a1a03060405120d060503060a02030406060509010b0910091e050108072604020a0f03050f12040b07 73
    0x4c001180000c2031204001c120b0700c54105d000c10b15901010030700c984002408007900c0c90f00d03516100e800402200450b005a203500007140c205409102c0a45580d407180500e80c8294085804901d10602d403040700d02880c1a2425900c41d03029031858000002c5c1c540380d64450b190006424403645c4e54503c00b1012803544a59036180d040310403c101805054103050b04811140c10f10640200380c01c0b00340a003019102e40081e14000c24562152032240d0900b0151409410b0300c4c40e03034550001d44182d640020030b00701401166840d1001c1c0d40002040200051441000060641500c0407203507981000c110b08583e106990f400c5105541d1181c40360082407040100380c002d048004100b60003802c00c5011031210003002d0058a020034480070014081a01c1040554001460209069010011004c80c01101b0350054416600181e80c0766021520010b0782140741c0096100704010030618503610001400c01403401d0900028000400c800c00011050750142c0da4019003109110641070904080280d822030a4452 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 637177859 1250 637176609 637176637
    0x140117071e03150b03031e0d0f0b030118080703180906060302090306070219150e030705030d0b0d03120e0f010e01140c0910080702010905060114030f0a0b011a 70
    0x214040c070680c0002000300301d901c00d40c0d8a42e000c0307004101020560707600c122082c0d016070007482440f00300441514881508004040c01c14038042c102c0032584207980621349010074040d10b89005100702d040134072a40008100404e85460240c0c140c2e46c580340148500d00020f02040510021011083c4480c03405000400d17100c0c504001c0d841c0d60300d00c00b4020f5008400c600b0300c40d00820001407074180c00800d102c030a8500b42000b00074401803a64911a00074502e40c0b1003900c45590701ca500071404000c20041001500490080d500d90b0f682e00b06d05410b42da800c1050340d006400400b00d00d4002900138400f6650b05d000020041110802401c10b03500d020700d1024280b580b0740c207003c2d560050020650040e560380c00002d1030b18240da501d00c841582c0602c85e003101150492581c4074002c851500c50b24041d6003210103071001042c4003400d40c0b6138500c3d0180a8118110120380c91028919502c0c08108001405d010600545281402c980f10404e581c0c17014800d04040505151b58209000c01c80c408a440201d44000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 637179109 1250 637177859 637177889
    0x100207050307181b05160602070f030c0c06020f03030f0411031204060201060603060b04060f05120f0a0b1e10050705030c010e2404120903050d030504060f14011707 72
    0x40c08102051108243d42c100d1500310051060f980800010750203001540700c185c036010f0380c0103410b4004100400306640840e400c2c441c010000e0396200309001490f010b6a03c5410002c4c0d1410500e00316150340d03000c84c0541d0301c03e40c4010000305020065940c070024117200b00b40c903075030b0300d0801034404044288502d82c103002d0f9010300805a405c200245c07050b0307000b6038004c118280e1102d070290304032681c0f0302030850062801c1c0407c004c41c4d0712494000c01006a180303091400d100d00001003092600080e030308844216440d9040040d180c45170b05c01c815182101300d400104500d480d6003114016400035404501501c480f0b02d1010320079005a04489010f80e0060481e0303910004566250b00a00f180050402c0500507000b081a6940c13003051003240601088030005059103603070b82d41c001c41104004413038050011260700080800ca00344081c0842c0342441d2000f11303071442d09251080c04c0302c030004000c2100d00c5c9000380060748107a01c0d0358614155000841c9510580c04070740000352500c419079001081d1614811 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 637180359 1250 637179109 637179119
    0xf150d06150801272d18030c060c110604050a05100902090f07030b18010e010501080702030d15090612030905040216110d0c08071401050301030818010e04021303140a05030405100207050307 83
    0x2501c0d60154040c031200b001b8400310107004001010024501600003200d8800e04404100c980e4040c103029a898200783c4040b4030346c1118582800002c440070f940c00d0300003482c03040a00c04280301d8106492440c240802c1444250f500260341c40078054142c00554000c01c00180c501e80c069400f0351340c152002802ca9243c5007004400c2509200240104102e00301c0070000003072994000c01c6107500440560b0099404e2281882c1c402e00240300384062080c0d01958001c0008a42c0c0451007044003400071002e0241c0115401d0501800c2c2c2c00b00c5601c00c07801107204009d1850f8150202e0000c00156078040c0071f01d030020804034005007121b10082400350446194500020310480002664401c80350b07070030245c40a0007110b000549140c0824032028107100000c1055880104c4a03105007401c50105050151300c0f200e8180101e0100c0c0c02c019102480100140014001c0c840c030410024409036a44000f0241c0403000d030760f2144c490147d481003d0260002c100c0040c1c26600038000031015040107021503007181c0d515 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 637181609 1250 637180359 637180421
    0x30306050a1e1203080408130e0a05010e10060912150203012403020a02060601111f05070230030402010903051203061804020109050f150d0615080127 66
    0x100b82c0480041c5070415001a42d0707405410f900a040740c1580703a09050f580d4603211106e481d840507084540c40c00c00c00e0b10200302240c1c0e01110380d00801c080324000600351b040614010304050040c1c4841000031030010104051940728400f0310aa6017014151568001a1700c1c3c07009018076031b81c004a644074008000415142e00c0041034880035110703d0102c3d0700602881c070040d000c83c403e4203004c0c00140c0044000840e40e501400ca14024944144c2c00c4a0242c042c2c00620003644e1120036a100d442e580b10010302c003065504010a03848400002e035001c2500c800440000c821000c0214800c40c031440101c0064207580c02035810200842e0414180ca80c1080142e601300c500f07910440d0154412181c00c0811840382703648086d2039100f40c0d410f846882d00141050100200c00c00f0090433281e12040c0140b644103840a05409084a000d4801e404912717541400c014661a4070340221550030054003000420003a0b0000003034140d4648110001c2d813282d12580280350162004074090f1841a065440d000e0f554286 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 637182859 1250 637181609 637181639
    0xc0318080703022406060703090b0d0c08010b12160219030c050706080408030a0e0c030a030315050108041a091c08061801050d0b180706050403150204050108040609030306050a 77
    0x4a03600352005012500c04190013601903030568800e40c0c03401000108181041030041409900900340140d00d02d90b103c0900d2010782c08001e4030910726450301041c80d8865001120a80540f0308804483d04240718041660444c1200030070401e04034103044240180315001380181c580085103c6c0420030280c0710340c01d028090034112002100e10303228106000500c01d101d584000e0065a0280f43c451039a12500741da44040d00b018180081c880c081d40701c680a231035904110203950144aa00d01040c581e1410044000d08007540d070203281808140820040000c6070030031519141004441e612400d40c03070702650b907854214050084555902500510302010327821100c0c961280b24103c55603561100c1c80300792046111420b100380c941144a25118030000741e1119540d507849070b0305c030388095602c02e000e18403140f500080d40d02c040c004c540300180c24818000c242c0c0d05c1394000c6201007819031601c0d14000000b022014020805059196502e40160406100360004402460004e20004000d5203c0a078020380c0d400f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 637184109 1250 637182859 637182863
    0x2160f12020d08013c150e030f190804030204050c0306031e03041503090602040f050319020f090a3b07050f0d08040305010608151e07030c03180807 65
    0x10408503905800b6110342e0360f26040c4c1d040d291440c0c10507200c0c01c121811200100003084110268030901081c0c031a02d19000030700038194070620b4a40c4d24a0b0030006091402c25500d010b01940211050b4181e194000035949031034980101d090101400c6401c000d0340a0086803c020b42c0315040c41c0600c407a0b803070740b14041d6000e000105c0a503164915800300e144c1414002048070709250300144801c00c500b4000101d20064402e09040102c0c043e011a07492804a0348030b504801103140500ca0140001d040410140714181441d040c801c142100075000500001d5403503c40c5441402d400e00042c010410700d070014070407504001000f0090070310081040e110b0040510b04c60002c0080245141c07140300000804030211540588202c003a42000750a00681b00484442501e2441040000200044092146000410f5400d018041d444004118161324580142c00c4031042c0c0140c584081c2d440058606046e04610f0720b00300007503590200f00c0c0c181c000e03206c1c0b0304c00d0810f450701078003908003070080860003856014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 637185359 1250 637184109 637184113
    0xc0406081534020c1e01080403050a050d0e0a031b08090d1109070309030e0d0809090c12010305070609271e09081209010e1c0e04050a1e05160302160f1202 68
    0x2001c00010200c0d000c8041c605d613001075200030100e8080780c02000280f01001040c076000785800005c00030903050b11032480c0d580a0725406070703251806059200c2001c0b540d070052180707141512050342c0ca0301900c600840072000d111f0248ac4058034200140082210924600600011690710308184060020214501c0503004107211004118081ca011100403144581c000e1001e03003007481e031006002c3d480340001c0038540703a0300080000d018a45800240640207622820081c4045810000f00405038012030340801044a6200102500490200ca2000041d6001a000076000c18040140d04074024000780006055107004050818040c1c104004d003010700ca8071170100040c0c0c036401112400c880d660304051000d90030600800108040030341c114111100c80d4903001000344403040020701200c500761113403424181d44064513100710301411020f10070140907460070050743c6805901c2c80b0340070a0f0501075004040c1d0000d00e495114407183d1030206425041140250018060310303025809619041c810f6001d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 637186609 1250 637185359 637185379
    0xf04060531020a1e140303070c03020f220c0314060108071808100606030e0a0521070501020d02071e050a06020a050d0504050c0406081534020c 63
    0xd20522004242030701d44801052214482045820041c000d18481240d005042c01400520b8084100d031000b1401360000d1404001c43c54000e4280c5002440d00401e400f0b600300388101c0000c10301c040103c0e8200c0e50103450040300d40c0f850600240c212844040410a2034069007a901e0394001d4176030000c800d044d480d850401c030a03c0c2c49490f8042c0c1800440e04940000c1000001a020380d11030704155030044411100b188501d900c42d03050b1414091005040003070310707960f414100019a458010031010314442000390203840f104d170321029150385c0e00d00581e1944212076029040c1d60344001e4221a54a42c020008640311202410110040e40c080841a10461562090051034180301c04104284c0d950000041050006968500001c0d4110403d10800d1180501041c800f6101074040e07984903d120350080d04d540306081c4100000c441094000307030603c0e403044440028445d4100c07800741d001003c407080c4c0070b9542284443e207012041840c00c26580d5071070a5500304170f084d400207050416000111014180 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 637187859 1250 637186609 637186621
    0x50706050c1b0603070f0210020705011b051806090112050a05250e040c0302090907081b09030c04151203230708180a0518250203070312060e0f040605 66
    0x2190204640d0301d81e10071030800106608078010300317003e00074045900641c0c2c1e00100040300368003260008581130b61240d441d1042002c16000701d0000dc030800c0a00c0c14540c0c14105148007030790300c104440884500518000840158a80c041c900c8003143d50394000d002d020900d40780071010007606d01a03030f25050311044032000c40e000c40c08410340345920308816900c41e03004000407000c01c006032030121401002c0c140c0c00c10141500d901d8205015100d0655500c038029542040a0070706200344240354012404182844409802c0d940890910b1422004071400708054506598880c00c1a00c00e601100203408040d0701c0c0010550008118018a07542c10030020070101c403250180c505214411300201050410000d8001c0801c1d070880203994041c02070320804c0310f00d0b114004505002031010200c0c40b4000301c4010402803050105144020148100d143c060313081035101c1c003035528003807010010280324900038480144040780e403000000b0b2501d03008680003410b02e5804000c24080507981520290304040004007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 637189109 1250 637187859 637187893
    0x904020f030f16060215070804030509090a0903080606310807080f120304030801121110020309030c18070c060b10090e070309150c02010207050f0606010908070518090a050706050c 79
    0x2210207102c04803c0000d947d100c50842c0d011200038421014008180280d180903111141ca00d40304010350070001643c0100d909002c0d1080d000103013110710591080010000d80728901289811100e11302061000000b640e488240c840d4225800c10301c0144241d260018150400084031007851f004201034840351600102a40101d10003190b0113400714a5240c01000b110480c5034505035440d00601e454658481a02c0000d0705103041000003070300683c13012540807040d2406004884004500300c8200c0e41e4506101c0003408041e000818510500c40821310300000c1c040c60340c00c33161400c81c005044c502038168032500584600118010b038841e004801d000030b61264024450f1841382a08091282401c0080640c10320203062121400c00c1155001d10005002440401013035520b080c06c40d0191220f450950001441034407203a0081d00c9075489101c00b00f14030740741c03c1170300c0c0c080e00c44110504020755542a112440d04021000c01005e40c030460342d0024499130f10001504162103100283c07500c1e0f104c0c18802507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 637190359 1250 637189109 637189123
    0xc03041115071524030b0a0504080c060c030a2d0e0f07090e0c0a060c0f03031116050c0103270615030c0504110c03090904020f030f160602 61
    0x800e4452030300103110503460400d0705081440307250410703245040019616038040801c90b610005200c1d40f00c0485202c04c1d14869042c0001d100400c4c00b03802424903540300c000b1000d501420542c21a650b0304049028001c80504407044101d0702c8040310000e0a00c0481c2040c03c0d84100c3d4401e404a00e4403011902d80140040600e8032100c86a00c07450200c4001c800d40001025a00c0c044007840c80780343c40c0407042d0715081c0403540051540100008120052080c0103003000000154244201c40002e01804040c0c0c024800150040d005545c0034600e004034a4141d0007002000f0100c0002c81700852010070185000c03961300c44d0a845001680c0003098004010b40c00d0701c0e800c2d4101864400304426092090b040400d00c401240d00030302000c2a10305440c0c0902c0c600c00b1181c1c00c10389000380d035010280105d00785402140d0035442c00480d02e80ca00300880c40919128068010001c1c0301c1da48400c0840c09541d0703a1000106901801000c3d59100f1003540503069403041c0f0200000311800e019040001c800d80082211 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 637191609 1250 637190359 637190363
    0x108070f1707020102041e0302030c0406231503090606030f01051618090c0c03030501060903110907140a02010b0f030c06040e090a050a0f020f2407020303160c0e0c0304 74
    0x6054181000d007140d14050010320502c2159800d0000084d040c03032804100140e0024001c09403505803c5006260034070704220400c074000d5060410421050300c43d00e8098100312112404078082080c200001580b2010350b402c098200342022080c0600c05c1070101e60240114000c400310b8011050442c00503081e00c1c402c5400d00c107020107046050030030070700441e00341441c100c440065040f0300741c0b00c070307041e20884200003420000a140241090101a00f51041601410b03450038501e803214078542e80c486258403011813040c019a040c00100354014060300c5407050508030102042d80381c2d2442400203000b0810200c1e040d1140c894407a44d4081402c0100c0c41c1002c0c4e40f40500340c107180c41d00349405044c031814050015000d5214500c180400301da0140400111f05115445031880951140100040b040010700c0c1c00d441100314a8248a400b030808400e110030200c7c3d0001161035941900010b1f0a6010302041204c19000440c00041045241060542660002d4182080030307151480e50042d180000c480c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 637192859 1250 637191609 637191617
    0x80306011821081e21011202131b12060905010513240807030b010501050a0f0305091e0715080c070f022d0306011203020a1509080301080c0108070f 65
    0x2003a210120302c40c81010255010342c040a2a00c03491840d00b4035060074203009650800c6000c034032940b051701a910030201801c0d15081c010b90650411001c502001b00301c0030300034071851500d245142ca030190358000c0c4400d29900009400d000910b0000030b0b004501116052014614004002c68115290301c01c90341039840123010640b44481c0d000000001b8541a01c1408a50f5642c805400030b103090070310440080c0c002c15002d0b200040c9035240c0705800340d0060300180c0c107114003481641da60350b40c010a06403801d81a45000308079070f15407000b11414001c510b20400b040d10382c0042101100440003900404036600d030f02032840502c01044007210074403c05d071543e07050030000b0428038000c603949004da4500f1600040081800100c40c2840001d8400204c00124032110508968051803505104050042002c03062204240a55640081d103403024110001c09840d40209841c184600561180e5019640103580c41c0e0b032561664041c1d0355500a0100c410b00040e00000003618651140541144d91207060f11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 637194109 1250 637192859 637192889
    0x18040e07080a0b04050c031f050105010e01050d11040b0a05041706040b04060902060d05040b0f0903090a0303030218030d1101060906050a06030c030915091103010903090501080405190803060118 85
    0x1d43e9000303c80303014205903003e20804000c04555502800455030180c044c05611001c0f50b4100412030668105030f10907818040300009901080e60840101c0e48804d0303031a540011845000070242c5014040c40d0048500c0c6d40001c0351082e1103542120044c0191260700c504480c0c07000b03417000e0003682e60f0002c88006000c04007075400724000580c5500308a12441c4024034450901c1c030680644e6040303440c116170984881900b0424003080250b240442500140c0000c06149081c134401c000c5001d40c4d11034031000301010b5000450b6130440b07154060114000700000c013600c0644460f190024034100c502c2c2c090165030351030a48005078030210b6101c2d140440307001400c940c094a2074000103130024100110341b98241511180480c0003d01c1004040500310405034002450344901d013486204046000a540c2c040c1c2c1c503091400703000c650040144c2007200d10910b850042d56489191060501c1c1030000a00d0b004680001c41004001c0144040c510564080e42d81c1d00d04900258945140300c00c081c41840e0032707622008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 637195359 1250 637194109 637194113
    0x170304120320011a180c16032105160e030c010507050a0213020a02010f020c0a0b100b0a0509100302070c030813030b0f0a0c1706090a06090218040e07080a 68
    0x484200d002d0002d0105080d0b200c4a404860b095a02d44002c009440312214808a41c40c40c04501301506820003070040704a13440d2900c84000b007442545254010386079894036003000c01d07100b26030f40303100c420110006078880001d161203a4003070310b070a5408000d042c12307510011505034801c01c44503094800003002030440c14103507001547d059007c0c141c213540c50300038145000c0c05a2122110712101d500c100c880160345042c092002800c5030080c05041c4a81070041026620035407000a4500201e900300101c20595182c90300240750010f000d1b40590100d22000c160441040d41220180416080660715407040c4030341d4440407822031081800003461800c1e41241480402e5242d80600004000403203408011510303900c0d902c2c14903c04036041d40a004092041000c0d607103860180351010005d40c201008402c69800c15010303040310051120b4090200000024000c035000c1e00001c005001c0d19004540e02c00c040811502e6520329150310138001c80c01c200350034040c03100000f40310049079461006045150704503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 637196609 1250 637195359 637195367
    0x6240108040809061801031104180b0f0d06060509060603040b0f18100203040203071a030c091909050f070207210c0911040e0f04120c0204140106091703041203 70
    0xd00181c680200500c0b010701e403030b2a20f0008000e1074132807030581d413082d074445c1c0001803d503200e840503801184020300041280c0741d0400304054102c8090003021440021a1001c02c014508603030307441c0e511055054110060102903840002624010351b29245e50b6075a02e0240a1684000d580050807105490001040c0d507107410f501ca03801003242c0045000311818820036602c0c00009400b01c140007036001041c8000c40c9000c001c010028441c811a0884140760756400a042e0300000301211603003a40020305840f035544101c802a18036040e000328400031521000e11100511044030500100c0c961a030100318802d000007079150864103c104603a070400701c84001c0031800800d03844100c0385481e051501181c00d10035230048016406141c008140c80d180b41c46040c0d802000301a004500c5a11500144008075a005100c244821203a041454008141d80b020130010008990740ca034007140220004181988c0c0464804d080765007031344102c811004107a460b81d45074402da20451026419051220b03000a001d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 637197859 1250 637196609 637196611
    0x601061704031709031206090402030d051804090f1e020a150905040608010507090609151b0b180d021506011404031203090312150605030a020c150906240108 69
    0x2c60701c1d040c000c16445600015400400303a03101080c0e5000411044080000541c4e042d501c9041120200c400e41003540200c3c1c1c82d0440103803a04100807002501d84c50025140300d000080e0303c0d01070010490144581413895072500d1000046501107021806e4400c2c0c800704182011480342c0040c0342281031850300340042c02da41d0581c2182003d001011100042541e5544240c000401c0b0000011541d480d01c00c2c0010510a03081c6c11003002e0222916082c402454002c0c01d400801c209428080c04410395034409084a000c00c1000401c5026800c040048000030a880800040400822554600994501070f0f1300d520420601c1c84c072441d00400061102e40c82092854104000010030782d1415031680c88004c0f14102004208001c81d880b803030b20001f0035601c40321440604091400400010b00074030488400c4c01010300c144010001c021002c2000c0c542d20368119030351014070208031a181d200ea001d0002031014110360b0b11030385000d42c400007200c1c5006030010f0618000c0030302c94030461068000043d112480 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 637199109 1250 637197859 637197863
    0x170609040209012c0405030307020f0d08010603020306010c050a05011a041e180210080906060a0803190201020c070609090e0309060f030421110127021c0501020a0c050f0601061704 79
    0xa182813008500300015007549004602500195949151840c0040d16000316519001e55652120704008425640404072505580c89813901503078907160100100c2d0a1040304002500324001c8081c4501084015806014620548500400d9603c2d9101c2004202d8100c20f0014a04c51400c0b40052081d10303082d4420300300c00c002d4010514220380960040745811000d50700714008a801d10090000310a420001e071a40f0a40c1242c03900080d0b4100009a501c078024400031064950b1410300d5a01e800e8000e4040c0d510750b030440320480f103616a032030b0001040c07401680304a11100d46031203441184038038080220740c4000700152a8524040340d200e10080315920003030083e9086801451146150709034a070280c5a00403042c0c0c0e540d8407410081000908550010700103012a0080154080101c0c68282005400d1501100c12151442c944402c5c10001107182e0002813495200051480e00340b600b00400c03c8400380180704a8039125103071844681d484100f030060f9004a041c0c580070329144603804140d160f100e4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 637200359 1250 637199109 637199159
    0x5090102120112060605041806050702070e0c1e040506040e0717010f150f0f0e0112111b030301030b010b0f0d0f050a20070803091c17060904020901 65
    0x3000c01451112000003c0c0c10007a400d0505406010030700c02207001c0c001c06032200310303010043c0710301e201c0001c0079041714074000402154179400001d1500e070081c81040f000307068810413a02c061600400540b440d030300641d8154400c104281112004100070f00554080c5c80029000c4c4e468642800c0d0903441c103000040c418004c003d401c40c5071042001c10340b203255008101c21002c02e905a82400114040600e0f0150a501042520903101741116440300c0000c400380310509000c0410200c120040350048261030754114828180b00740280c1c990111801070020111070200c910304484201c4c85181c9070311003840060070540c020001802000540c6000b00311544c590900c80d460a0081c0180f04152030a4101d98850140d61f2810421850694004e81311010000000303241d0b2003c244000342d6060082070009081801e022000440107c000c02c00b50916a07a420303042c0c095001c5a66008155081d40c0c0e00821b80300d088031f00030855605140c0c12030380c022a40240807098076800d00c2d56810311441c006e100000c1c0c00d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 637201609 1250 637200359 637200367
    0x40615150507020f01050c12030c090603011509060507150f020405031b010e030c06180f1c05281205091005041d010e043002030a02060703050c0d05090102 68
    0x88015965115402091500c0707040c0ca6160710300401411101c1e040c40641844400c01003542d00c41c901103590340d0b001c200350101c0fa0301ca45420030050068025102980e0304410000008034040d000c01104c80c02e41d5100d980c91244c44d58903514202e4aa008601c00100b80183c040d80100d001e41c20b40d040b02401c11100303400141041d640750b000a15003001000380c510702c4045175210400300e503030201903a60801c50030340c01401544a03c02c045100343c4102c1484141000c20202c80c040c240d914094250310b030090080c03080c03880064942c045250320011003011201c03172095402c001c40c0c0402100e030031540742d0a2504c02084450040c6c850b1710215810660007130800030700b00540d04059881440c0e00402c1da00a40e01c05884508150032000108600051540d20526401c0100705a00001c46030591050f4010100c07050103815848445124030b0740e250b07040403075554007035000e041907002018100c031550706c2d804c0390816203039050190708982c000c0d04c030f07140d022508102100f12004650456034022462a00042c50 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 637202859 1250 637201609 637201619
    0x1905150103060b0f0a0518150613061b0209010308220f0f1e0b0706060f0e150108090d0f110a0c05100801122306040803060a080a0209040615 62
    0x5145001d07001100c100307507140003910b5181095031008078012816030b0001c060b2428000000c3c03031100145a03045003413a00000280100d108680000d40c481c40c003400171501c1d086090101c1030170340303000c1c080d580c0010456642c06121790310074070382800f03d00c1e0060030036030941e421603e500d4241c1e840504d840c1d004a901c030515942e02d0b810400004c0050080001c0c2c2850355041c0414070007202c0040c1d02554a0343c480701e030101500b4802d05051011594110302039a91642d2508e0400e010b496582d1003009540c0c0880e200140d802c014144041c0300f081d80400c03011054078100c00651f602c04080d200c240380b65014004a2180c580542c40c83d05040b0b8080c144204840e00320703201c0d40d02c0c1c08445a0100c0352144408010081030030404024a41031085080c00a42076041107044120050400ea018201210403c0903100c0c1e0070801e4804600300c280c2d6030170390b006858070381420b0005a005440709030040300032400015446c50b0215040080079401480003480da1150b450b00c601030079180c8891010700c05070700c0c000a9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 637204109 1250 637202859 637202893
    0x9020d020c0d032f04170a0b10050a080f1209010921170a020c01050a030f090308061219080d15080d0315030f020103050702070909050f0708030c1905 66
    0x30301010300d40c0c011581800340003c130700010301c0c144044080c801940d664008644d044d142664141d40d028040d50400c00c02240d51180350000c210005045d8411200a02c40188842120007041e0394094800e00802c50380c4a0000d640c0b00480381c14000903400c940d80c22038803101290b000b80303011641403604000103512607400d0f0a540c07000510500006074180c00c03400c2040902c24162a0300586088080e0610b04c0410000c0c3d1074010f074542d03860400a00051558400e80654084203040303c443c14100110340c0c152501030544d16054603044e1140344002500d540790720000035240d00d40d601c203101c0850702c0301840d5655505500403008600c80c40d900c2c2c100c4051180c6030502400c000300300100041044407082400034046641030303000b0b0200400003003401c7c0003096500400030980c0e582071a0000300c0350b5650001300d0400c4180d802c12042a410b02100700c0a1120002d015007400080a042d1460503a43d881003940e64420100511480c0e0070211350729940b402541c010358403150083d816910400912100c0d0b074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 637205359 1250 637204109 637204123
    0x30a030e0607020c01091e030c090203100b0a0207090e031b0a11011b030503041115070b010e01030b0103150f110c061807091e090606050108130206030109020d020c 72
    0x440066640d103400d50300d00c1001c001c0140c024081d0700107440c055040c075000901580540c0200403c6c0c164502c203000c000300303040d200c0e07100440c0c100443d0035406480b8050354010350300948030075403004981c600104140e03c841d01140c1c18542960000c20f0014642206000540000d015842250000780103001c542c1d9140e4443d45c0140c94008042d044c200c8141c80d00407034120031100c0c0e903810030204407100f62409018076481c02005030581446512552245000d049000c5a22407480d0440c420750403001c20307181042c01901c00d01e0300c5200e821909a8a416036800c2511007440044d207131b154213800400104a1040d82180d00c0d8211601c081981003034900380c00140c41140156040702c0c08005820225180e00b484001c4e00b251092820011051401e50003c3c3d5806803406030030959540e4140e41d10f42030301a0b240a07403800060b0b510600c00c0800c181803000003807500d4403990307001c580b4050001d42a80313102051002820b6004200030b0440c3d08210340d001c02500300022410724681d00300105603003903401f00100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 637206609 1250 637205359 637205377
    0xe040b0a0914071709060103020105031305070806092e0207050a080703080f01060e011e09080a140f0a0c0303030b061219201602011806080f1803120406060803 70
    0x400341c1802c0040f002030203040715200a48007414200240715400304042051811a502480d0240e144d0319071030907052412005030302c0200300f8401c201c00002d17200400b02e0010b1140c215803003981c000801c00f00c04000c202c07290681c41025611112001c100c0036210340d0161034001d000d070080b2802c401d550b40d02d400e4a50302c0401c040e03000c9400e9904015140c80d00380607490140075a0b2801c2500201e1500010705020b94000c406c0072407145a0394440d0f804c82c881c0103000002c16281d002c036084e900c9182440700001c0c49000c440704050080c02d190450002c8001051800194840f440988441c07a50f00c04600900c600301c1100d40c402c0741004980c1c2c4c070b810301d00d00c040d02440d4020298040b80001000d41300c02c440803200210074200b0300700341103114044a04103480d071495006114295044207032004840034103211003072040740380c00f58801068141e4001c102922900340d402c03d04426480701d04ea0000b00b403003030051005a0ba40200014400f4031310b03808401f41c000d8401d4202080458481e80320303d081d41c1141203c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 637207859 1250 637206609 637206641
    0x1505030103110a05030307030c1b090212011d07050c030910120c080c0409020d0e0a0b070e2e020c060c010207050c09060a0e09030d02030103111306060e040b0a09 71
    0x50003840b82c20200c070526008111101400d032840c10f030200340c0b43d0080c6c0f40094144002c0009040501103200008480b880c040103d500c1c0307158403881450001e40200d03c0040c0041d0034403001140044e1a0301c103482e20700c1074012002c1800d0751900070031160b691010307202e14107a00040c04890004d4541c20004207034100b0540b0340d10018100c0c0c4618908441162100700c0401500c0c4050001001c0d1400480307044d0360301001c001d40c0e54605450990003400745408000100c0c844c10b00703100c1c280318070b0650603400380000d0303550384030459000820010b9141203407444d40c1a060b1401c90005030701c84003444102ca41c2000d40182d40c0c0a030306c1000004e50542240883c0d841da41d400003804020041d0030310901d000b0b51003c9640300c01c14141000489c2ea5804c0a0080085c038115620100340140c0c020400c1d2a807003070b0300300015952981c4038a0490070b008400401d250140c156254900003640e103500800d0141d41e029a02c01d00c06519810401c005090f854031282e0301b280d60003c0c0850b03001102d01500b809081803107a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 637209109 1250 637207859 637207861
    0x2040515030607020d05030105011206030b130b100b03060402160b09010c090806010f0b36040506100e0918010603060b0109170304051504051f02010c1812050106150503 74
    0x4149030424100825507800c5400c401c4017480010303005010340381980c01c2840c1001c00c1445040380a001010150406010340005104102000b140b112916082d140f06d050303104810388941c000c4151048450003426a295800d000180d100e04140e0b014001150407126440c080044548800d100b411050301c411a2694640c0780c100c208035005618a40109002002400c256252088440d81d50b82ca90040c1c00d0020b500040c040114205502c10500d00042c4070340d074030340d2840051021030849515201e1344d802542041c000441e1450711900701c50010700c481d11350680c1d00015904118410b140200b00c0c84c1004281c40d45800042c900340701d90800b56219100000380013102c1400504941c656502801c0351003903000c401c408005000c01550101e0790b003070303c10740090710302c0075110b04440c0940e400042e001068082c802e210200e40816611061203030b9002041580c0c0c0300070f000c640710312071841200040c020a61040009486284081d9442c90151000003240341d110720500d82d5810700350003e1400a00c000c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 637210359 1250 637209109 637209151
    0x1d0a02010815060403020910080f0d14040303081501020f01090308090f030a0c060218040e010203071d060f2208070e160f0503130c06051c020306030c09070c020405 72
    0x50303103660040d00c5651580140001a03000840f280300d1400003e006a12201c0410a04440b1a042c070000d03109110070784017071002d400b041a1b07a03041c0da40b82ca080001ca21020f201c8540c0d80c0003084a0560350142d42c1c80b24150b444070010744114002481c1c0504611440c44100382180c020300c45e52190740c0c4640d4032020307582842007015107480341918840c0e08030342040180c000301c1c80c0c108005144060348a5030158917002c102c02424004440125616000390511101d4030180206500461040c10252904140454129030503a143d0740c2d10000ca1b500503204011900c2e2104ca02400b600c6035414100100c1c1035a840d18149154401c096400500395a01081050100d901c552030380d81d9001942e0b45162004a072000001415071b80915120014001c0c0000800c80711016a901e10100681008090700380360b41e240e10003460750b805221510b8044001d0820369084070014021217005250040c014014034034040704108600308080d040c0c2081c083c9101000c00180c9036400b03003510a0824203080103207039041c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 637211609 1250 637210359 637210367
    0x1005120a02040b070f05072105061003020f01120f1803020d0806030307060b1818072718061517160b0a021f020702190608010b0702041d0a0201 63
    0x600000c1003580107000074840800c1c40d10954076480d030040d0441000c02da550500608042054003c41c1e02d0000742c00034140801a90030320b03503002d20301c5081280c0c0b80743d4454480044ea080240002917101d840d03204071140c1c070740c0710f105100880b0301c00701e20020f40d10048a45031802c44681e00e4480c0f81483d04480b240c0207064041c003072442001450f092079945450040c00080d200e204440d40140324965400c0c00d1103458485020303159400708946004c81140c18850300d01c605001141c03030580e075a4854120082a01c401000ca400300d0070304007a440d918840348060b25000581004d100d1791440021210f690340100c2c056010380d04906c0652414104010b05012450b10f6142c2c203401504500d5100588600407144055140c10423078520525032602c40101410403070800510f4080030b018900e085032010712100d00c960003403c95500c21a81d906a00e000000c0403060160795118a50100352000010420a461100203000691000b400000c58403070f100c2e081125039010500060140c1d00c005024803c40d600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 637212859 1250 637211609 637211611
    0x801050114032509020703200f0d050403031d0427050c0103090807021e1008060a120b070f05190206060901090b100c052803030507030b011d0f100512 66
    0x2079801c143c888400d0b444690300780910f003441215801c03640010840c080c1880b400140030001240b008541c0e03d45103820401d0355440302c0440c0074410b402000c1039140001e0040003102c01720307a80b40d110b860008603140c425074800d200b050401038105071a00651161080140401c400f10941c9042c00b00160426003450b07880d102c400441d072818189854050b501280c2c080c0260340c03d03154115680c440306c40c81c1440c0e01022004240160f0b801010800c29a510140c001040301c0c4200301c00d0b16140001c69880602101808000340081e0042e0941c40125618901c190006010031f00da500344680f80807000d513240f081620720340030000300580084c41417124034a003180f40607004010060b401d001001d440d0000034100402c039074460040c00541884042040014084921109041002040340042040e5030740c0c228000141d08a000034945030004451601911455006c4501a5034050004056100ca2580101e460100c95400340c0030400352400d1380d903142c2401101c0781e0302c0d60315581c070f80381b05035511025640 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 637214109 1250 637212859 637212883
    0x50709030c14010c0804090e0c030111161106042601110a0315120c180203093309010b011d150913020c0105061309170a09080105011403 60
    0x1801000304082100c00d4580002e84101e01511818085400700603590b09003c0080141300e12804140040c1352222a848024521090070a407045071090304101130807500c400b8140300750030205100f00413982c4800c1e20051440c500c189079108003c000c0c0ca00140d9250000ea000c43c086000b030754010200038019807500818400680001d203c02c0e46983c02408590143c200c10034100340ea107860621980b0f10f51046000180f841c0041519541d1550030401c480308810701680c08800c0c01c41d081c0000d001c1c1288200da110b6228040902105100c5005000c50540d40140c103120032503a42e1500c040c3e50094501700d500565554000090066a21001400c8000c044407455050b4101040c08840342e01c4851041501e8130006080b81d0391540c103c0e00060003550348020300c580840c80461800742013401544068020300c070455144003500030000249040c0d68440b80014641c007a00e285513103907000708401421751b41ca078a050900146440da03801c2421190b09070320450003038018920324012402c1c00e01000801903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 637215359 1250 637214109 637214117
    0x611030a0605010216091802041508010507091202010e120118052104090213030516140901060c0303050601021c0e130203060d080901030f1a040b06031308092709010507 74
    0x1c4404001000240207510843c0d980c5030700e42c00300203440c2443c07e00903007509034000e101f00a0301c0308281e0540919203641c050803040d9840c00b804240c030580252407120803103c00d10542c419801c80c0da8011117104403650140c43d00910461107440d400c82c802e00608600d00c6e0684440e0110483c0d909003113191540c109490240016034015403002e5020700c0040f00c098619441000d40d59545401105402880540c0081c4c1030340155070b0060448051111131000719100d8107403a488140e4034508100350024280314002c007042800b03100f40002402a00040d501c0203050069070030711400c448080c5090140d810440000901c0040c030740b681c40ca802c45007800740c0d42e10f6403021400d52501c00c0101e00c4598004101510403000070034526035580c465008110300300030ba0b17141480118000000b000801d480b8001d503d01c11800d0104001190405000b901d104036085800c10200080c0340d01c1c1c041081d40583d4646800044c0092108c4110b4204c1d0f000000061040c210b810039860b10804140c06c5400191501c0100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 637216609 1250 637215359 637215373
    0x1f02010908070f1101031104060806061614010b010302090906012f1e0105100b0c0a051b10140f18030d1e0201060305101109121b18040b070c0611030a06050102 70
    0x404d0fa171f0010761741911060300f803c62064480400203001c0b030088030309141850300c242d10100b0401019204540092162200910030a8882c030b00643c2a0b014607030a20b5040703100c01c00000c99561040c102502045400580f00f0320400c002c5540744544020049c102269a0100401c811a0b0b08032010100744011100000c10107400d0041490f60301d0103a03481900005500490080c2d65402c0601c030005010fa0f101c021144a4030401c0300c0c40201c0b0510a00c0240301d0802d110210b90f01a010310140b00400d580050381a10344500402d10802c0c540040000040280e07004030a005551000c0181505c0509251034000403150a84842c3d1103100151a040c011641409010030000b81d00044207207a2480d02003010446c00e103101000c4455025400b9807690101e010350010300d04d00c03804a800c084010000d502c0f100e11081c02401d1101500d43c82000c0301c102d40e18440020049011306d00060340040031490a00c004a105441e41d2042c0e958849507481c0040c00002400b00030503041c4108002058280043c2481c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 637217859 1250 637216609 637216631
    0xb040807090e030d0903050f0705070303110303090c041d03070503030411060f04050906040902190504051b1b0c0d06020c19080313111216080c1f02010908070f110103 73
    0x30703402500e0301c0c0090b1381e032101082c000701402001602d581036014000c468136071005042c6503545400611041e80030844202103440040c00220803240700702c50340002840c0e010b01c1982400020481c0c010030809182c00681c1a850f0714406000500d6201e0065000b076891b0304080c2004010121640d010078481d40b010070203c07482980c82c1084c0d408a0380d0031190b4048036a6103001003400b5140020000394045001c601c1b05016211a18008041c0c62094504111960700c5111044803002012400c100044040c002c0c880407040c990740085030b0182c0a0142c4818200322000f0482034410343c0812100942c0124041004171410803005441401d4180d1414000416480e00b020910000d440d031148034070550844001e1151048503d24904d070054250104210500220360710741074056141464038000120010340c0000011f007441541c0c0340140000d0012000840c0041201c070f00312110300642d502c900703e03c00030803220409040c1c160300420884480c007046180c00700c4103030400703440c150525281402d00300d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 637219109 1250 637217859 637217863
    0xa11100302041a0304032006250c0f0501140906150a060504032003030d020a0e040b092d10030b090d0816022506090b07020d03031e060b040807090e 65
    0x290780c02118609030b0389031520704003211803a0b010309201c41d0031f901200c84a0807107000000c1e00d43c03056884420b81902c0b968243c0100001c081c40741140c03070003d0411038245011035800908054454492000040c400c0019003100da901e0908440c400903640100d0100504600380c032062410300e80c411100c6500d01030908201030701600440c01b01800038048a00e1010300c241c0100c241040380e0400408803a150110210003401a600c80610200080c0803014810320900303241c0031381101d0b544002c048010585d1040000f141e5079604c100340c0c010194141070350075008a00c0d5411b1602448016a09213561800c6040450521070064031406e540d502901ca00070215600206403078111901020b40000c034489500100c3c500f41003542203001d4102518003000414040400b0142210150b0b250040c42581c0d0300c28981941c080c07440040d4000b4410010301000a21940c40494051109156000b078101e0340800001118090307042021402c030002001e202c42d82c007c00c00c19000f0000e0502c04e0002d0342e0848525a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 637220359 1250 637219109 637219139
    0x1008071d011403010e060a2309030f0703051908010306051e0a0c0e0303030109020904060e09060c03130b040308040311011a0d02010c020607051f0902030d11030c0a1110030204 77
    0x380c1085000b03042c06000c0c0c1d5003901300307071032070400d0f841101d201e0300740b4211000007410b01c8590b803050b80d414590f012000c01c4c02d08031018850240a80658100312034104080101d6116440880800c1002c00c500380c42d04401c0041400410f013a40e0300c0c07005647c15450801c040b00d00181c031b22041c1000c20414605010100c4c1d001a521406000c2c000c0f400c60026502030750b141400d0404103905020100011641121550280c08a40740c112002e01055554448050340d0303003002e03503060200d5080384000070344811012005540122840486280ea42c00646031100c40d00002e40f0120001030700142808281940f0540d65100020150000c00c035130794044615001c005514030b0424083c2c800704203002d081da07004040100c182500a00035541c3c0d180280303000380c1c070b89201040450700d100c8081c142d1701d41e01082e0300c551024181c0c09402442a201c14480c01d071071300d140500305020303076100403c09000d61300c0c07050010920f4517205205d41c1071160450310412908090410b0080101031042c03100704044140c0d06006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 637221609 1250 637220359 637220369
    0x80606180f01090b340206070b04080d05010303020a03090e010f05040e030d110d0f1a060d0e01110c01180309060f020f01140702060a11030a0e151008071d01 69
    0x40c1c0038038a2400050f10a046550300a028070007000c01e0303001000c4501c01900364030031803d030112054880764028070440c4951003031300131b50083d0b8240100c00006111135581500603000e07803190344c28180300e050498182c1e03109810880050300801c0030481051380106241e0060040c1c030703481d0025581070400940c0000040c0c0308503441907887e16400c0e80c0c0b80a042c02221140304613003005014504801940351229441650504419850b100101406020038420039036822070000043c0a501d446400f0071086e9000b13071a044080940d5071104981a1170300740b144258140b4689042c94580c0c0f44c6142150031944124080007201d50b1107620342c1c00082d480041013081d1942801c5c100d0b00812a10012847c0c8024030711814403540ca00a000301040003600d810070310032031461307007222401e0b42d4801014059036443c582c03055100c4c100b440440c0351549079400450a00505104448d0078030107011200d20002410f07140a04c2d0541070440600c200e08041c804d6102900310954030324002c00007a00b038004491414490 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 637222859 1250 637221609 637221619
    0x2d080c01120e0a050309031204080604020103091104050a0b0a091416140408030d0b030f0a060c030209040f061a120112080c10060618060801150908060103030f08060618 74
    0x500784001c0e55400104211800d4003110031100c8030f460007a6a80c0d00c4210420312038402c008910b034030a40c005044500b9a60f020014100c20303100c0f60b00542c054514210f040300d60510005031034110352181c4c410341c1d00c03600380391801280f003491400502203400d50b244c00c00c1c0c5049007442802074007000010821500101c000204036001c1a032000200d543c0c1c2d81c0c0300d050860f42038002800042d990000009404d401d03503910800c00045903100f0400d50f445000144042507508079542e07450201c2c82c6036004560050641c10058907082c01440010225210800d0858209640e84000e000724a2035454401002e0790f8088071f9403616000603446003101c041446001902c0300300c90309400c100040364040d121782c010018115042c0c1d10054600798050005805070000186c2201c1c0694003c0440d0303c640412950b5503142c0c00d10a90030100c001801803080d12403c000e1217a003031000103203c0810031000d8020340c0650746109034420b6401005083e418050001f9200300310034801500c0340b003060350078403a001c8002c5034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 637224109 1250 637222859 637222877
    0x30209040507030804030503030f10030218180f01021804200a020a080d020d050709060914040b061c060b0301031101080601110106080f0f0a05060105100c0c2d080c01 73
    0x3a100c0d2810009400c020130a142c0400c00004109001000c1d5020b0244400c1d000403903507540007403148100051001a40c031410100b45d2078221104050020b41200c2441a0501840c49000ca4149009047e9042d821103a6000900c0445a901d4840d4011b80c40f03411a420b200c0011001044207200c0181080d41c20b00e0400040c011100c0d43c02040710448065204010750344075104403190300025008034102c00e0b0824242000501d043d441080c0b64001e40c2c01b0b54542d200c2c0142003107004500d44006684154001d40d4480e04041c0340d42d01d0b2006854031780c002c0d01050f50070001040a0009442c00c550040c0403410301807006000003010012403500d50700080c81c01c9441a42c5141c0100c03000d43c10300f11445890752a000e00400c2400020a82d00f442141e081e00300d0300145000d8040d40d644480604020780f241e00550011300044c501000301102c4601b20f403034104940700181d20f4001131040507a00c002c0c40c21002100c620792034006103150100e4000c421035940071603031420840c2e90300c0c3c02c0b41c490f000e810081020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 637225359 1250 637224109 637224113
    0xf03071206030c120515160e030c191503060b0a1202130902190c0f140a05010509030a1b02090406021e0c01025d07021c0203090a03020904 61
    0x41e220600464001c08200369071541c4031402030342c0c0080400c050b40c42e800380c05801795550200408035030042c1105e00d40301e0000c9094400440c1c032021482d040b5541801030702c1e0201201e54691042e12079100800d1044403140b8641719030b4280ca1301f0208400020716080400070020402034100740ea25900541c1403449088820705901c000a1280025129240303080c0c07840815144031b2a80541034494144941000200458806031190349410400801101c0c0d805548030001e044034500080801890007103900e0014155541401c2d41c204803400021988041820b074a03081e40b01841072109401c110303458040c1c05640d000703e81380b60002000640041e40015840a60000da000100da0400e401c001d000c0c1c84a860080396030107580b001403076000d094814045c2200080070401c070f1228502945101c1318240601030f0600c030060f01c1c441400030315144420286c100d0765032103405c100c1c800c20f00e9038040c054520449100ca81c103c0d281ca00c0460031940103001014203611007402850940c2d404440144039507aa40c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 637226609 1250 637225359 637225361
    0x3081306020d140a140703120b010504141507120c170304020117100b070b010e0618130302010b0a0e04031106220c0504020a090f0b031909020a3501020f030712 70
    0x8400b01645021700010810306040e400010010758108010381030042c590014011181805607000f081908895100c0c02c05803440c040074032441c020340c144030381d500b0f204030340c0c0301c034070840c96884c452001003444040d200c800c001038050941c080385060914282113040075000244148040352600305014500004502102d480700500c00c000d04a000e03003503135211141e10b000048888288030b0b9404000c21040407039a2451305007240921000c5100451403140e444240724600d0240c2d000c8140d055550320b4162180741c0c0c48040e0b00d01c2c0034002d40003000042d4101894014000c101d401021a0103403c04001d014450260055440e01c09102004080107000b140c240040c606005030712095200c1e10000b0510300b9aa04003001c013040b543e256101c2d00364907a64130f040070f115100488205003800007141d007080403034405600072840303a4000341154403216102c051802c6406400c001c1c83e0340070b07100c0104010540110810100f50001541c0c0207604111003482444c140b400007524100900c09484005016101e007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 637227859 1250 637226609 637226627
    0x1080603160f0303030e06130209100e0a020304121716110f06090706091512020909040b06030c06040e01141302040b0423090c03150a03081306020d140a 67
    0x40074191407210303500d0342c40095080c41803000b01d012a0605490210a07a0f000c1192846807004003880380b4084107582c200302404070000c1043c1252804080b01040307a143e040b80b0284616040303000140c1d43d007000d007041942d00b49036108060070800e01d0011041e00c8480701070080c1c2c0050420500894400078400150742c40304519002d05660321500400c45a040ca0008a890140042d0010b860080c0e072900e2044800c036029014141030b482c1b8000f00301800520501c3ea805c24018856001800c0c950f8500c00203204510076502600d00003092001d101031880c0502800040b00c0e01111490300d441d01d00703101406a80d40c140b02c1e140744003075100041314041c0c407224002030b990420084119591501e0300f5a249140c0c10501602c01c00c10114842c18404e90030701502002d041000502290b429a03501d5a02c00c0b540e4802800c4400b2480d85080c1d0308165144c1001c40d5000c2c40c8034144141d140c05c1c00e0140d95070300710842d601c1003045600030b421540e119038000345100c08810031031210990300e15418000f6110044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 637229109 1250 637227859 637227883
    0x1306020a031413030806180f0c1b0a0501050105010314010e0c0c0d0306030c0b040843091a18040819021e031305011119030c11010504120201080603 65
    0x80070042288040342d965280f802c0d00c3c0700ea101c0e2881901c0c1c040621200030491f40d00f2107490302d20203010404030406c3d1140198458901c003036040c03030b1175000c00ca10820802c108517851083c0c0d00801c26035003000421700030180904020700e8200450740c0040e90300455000103200301c2d84140300070400700703030180751103011203106561080407600ca03030140c0200100203012510058590003070282e4041407000d001e004503021104110010421240b030b240d9924480c4a10034211507480344521101090382202c030035280600e28100c205019103500c0c101d1424251800e62110981c0e101c80e1800740305e083d070b4520100b9402c002e01e011810341c2981c0d552404220354401c484c2c0003061241e4011044d10f405a00142007100c0010821100010030010f00c0d0190b0b4034042d031118140c4400201501303010651048000202510b40401281c980996a061307002c0e2024880c2416000600da01c0c0010051110030314225014400c28030705545060b00c2c0100d07440d8100d4200000a04000020011070b029540404c80802c1143c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 637230215 1106 637229109 637229141
    0x90f0607170709170706031505031203150405040c03061a091303020a0615030c0b04060203030a09060f0615030b01020a02061207051e0909010803031306020a03 70
    0x81004204204120114070005050a1280160141c1c1380c40140500340341400d103400201500c281c0d203040804261494402c00040d140010b4000701c95000c401403548a4030b4032100040c5000021034841c0e0f0007410702051100384008299540c1c100ca01c120001c000310085d076460088412036248506070f11644180014900034848403405412510a10583c0c0c1c00201503a1401c0445206841e0b01428050808061040000c0ba446000140105002442c01c061905034003e64900c00107000018072500d44d8025003c000041d00440c01103901c540e1305214503501d6011241544030451030040010f81051560880d650004c00c19440c8a41c02a10f45444e00416110340584038030080c15840801c4406c00c4424101d20420060564041c02444269601d90806041041145040c2c2050000341c004205104140808840104040d0780c840b5000d030b11060143c00550081103540304810001c = true := by decide +kernel

theorem cover : BRFrame.Cov 637050359 637230215 := by
  have h0 := BRFrame.cov_init 637050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 637050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 637050359 ≤ n) (h2 : n < 637230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
