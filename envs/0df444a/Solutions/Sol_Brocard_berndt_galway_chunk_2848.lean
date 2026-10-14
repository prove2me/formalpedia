-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2848
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:55:16.976996+00:00
-- url     : https://prove2.me/submissions/9508b3cb-22fb-4e9c-ad93-beece909919b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 512050359 ≤ n < 512230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 512051609 1250 512050359 512050373
    0x140403080304140c130915150e16080402040902041508030904050a020309060103082803090515240307050909010c09081b0d05010b040603080a090b210c07140703 71
    0x420059071180c200300c8650b143e9517511a03200e03420b201c518001241b08442d90a00041542c20460768070f20f031611301800720706810400c0750702d030040781c4820201c80e2003aa07500070950901d5200d00400300000d4203400c0003400520f0251720603030b29103001410028003049001024401c0804582042c1a65840801c0034090751605016813680486c8001e425400c40c100013059035525041808000d08101c40402c440042c4c2041c0f00480036523030199a13070540030b10350540f8041d00519511070243da560190307010491f01d80480c4c1d15000d000311300303196114003454910200419503100f2a07681c10b603d4001e40314000340f20f80d2903015060207442130100009120001d408040c000412641c00915680c1082c030558020151002554005400541c0c80140c000304a02d0540c0c0102a580069503110385041404014402c3c050007030540301003240c0344c440038180c035880940018090742e0b01c404906040890714007454814440c0b21038018291114880c00d050140d40c441d060b1110382c94802e01540d001110400911000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 512052859 1250 512051609 512051633
    0x5092a030d031103010333141f0504020c03070609080901181202040b01090305060405060f15030703060906090c270c08060904050c1002010e0606030c011707140403080304 75
    0x40d0500b0088910031660f10320031408141b102078030303a00905403119150750300c0d041c110f0252124251180e0781400d40100f02d0004060440344100210324010024100c170f4041c0c00703620400c15200110142d101c3c130340300401001c0d500c03003480d2a40ca400103100160010340940116a5003038480e039000d9454412140005000d0102500300d144083e40702c3c00d00700400e10350b0003640108113030180c0d80446c0400f02000180c400d400c0c141d0000301980300e46410031082c020003041041c00b40089445070015525072400c1c880029420180d56907050b00403920420000c0c400e54000c83c02ca901c10500894850704603242c03070465150344d0f40040c011184000010040c0c003019070420043d56030b41d007000c000591100302c004040400042c1042c3c061480322004c41c05104c02001000007c10005040d04c92542e0042c02c000d028240703981403020180318504c007045007450045003039001d0f008103958500201180303000c1b04040e08400f422240500508880c845a040c104e100100065130003142400d681382003c3c5401446146 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 512054109 1250 512052859 512052883
    0x60506060f180f01030b090a090206070b040b04060c110c060c07031a04121404062007080109030801170a0f1104020313110a060e0f040204090c030506090108030403030c030305092a03 80
    0x864042c40c1603007940c589080b030303030850f1008c0000200d104040c8041419032041070030140940d0b1000081108000741d100c4030038420741c4034ec0401d2011103007040c401e84070040111010103180d00044000d0150713041c0b00003d0111200000c0803070b61610341e03a880d4503603140d444400d030100031191842000280050030141000140fa14648510742801190365100d070b034003690264100300100c40070110500045080c0b04800d00c81c0e8881a9824240d48911850003819403100480108848100002c3c1c8203146600070302c00400400050305030070300701e550303035081c9920700340c4044aa44c12100b000700800e440d50720281d40308100c030784c6e02040d07012240d09050075512200044035115030100c1c0300901c05507902042d548204407040e101d80703040725034890018000e0f0250313030070070350b1018500403002c2140ca40c5900300354001d50050b40d80c214181d8a50352840c1e144d105d60702003d004101043e0700c0c100003900c41d9001a070f00070000420317220a1440c80c0106090366000c089030804801c950070b52003515203000e10003080150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 512055359 1250 512054109 512054111
    0x6090307030801151101110a120b090106080c12190e030307210b031203010e07020a03021c0e1003090c0b1303060f0b060f0a080705090d060506060f180f0103 69
    0x1031a0750300246108414001c429406454105402415028035055000845254020300c150b01000c40d4511032500031185180004211201b07002114149120b4207403080b038082e080081589c28000181ca0610340031b010b800010f0010010441c800c0070615030203010345080c1d4143c1c00c0020010324031100343d0f508000c00750441e42081051181c1a500440703624a1034243c83c071801c10242002c1000c100070711041c41c00640500403203042d10207015280d80110b040e9161036110a000e629442c104a81d24203456200030050380c0074100d010701e80483c0d41a80700903540c4510b0903200c40c084090100b1244079141441c000031945401c541020084140c0114000c1e160f109a0903052078000c100a5000041e18032018000c10350b14010341d2040c0300150089050b80c4c0c000341c009551820013000c41103039a40300c208000005140d05010500d085e1041085580754500140500181d1107151200001041c015140303d82c4140e00700050040481d0700f00142001072310302c20461507100c201c40c0900c12941c660414942c109 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 512056609 1250 512055359 512055367
    0x62505011515210c0206040215040e0106030905070306020d05070906140906031e010303090f090b012c12010e01110301060804081b03040902090414041e051006030b09060903 76
    0x400030000d07640040e649443e1106850039003c051070f8203007200106030511a030401d050124510340010b88240154804e580f00d10064510446019090040740580c000b908945401000168400c1c4c2042c80b00901400a48040580d41d41e1294101d9021134014014280c0b2003041102c105e40000c42d50008181505080039030301d8095000314503d00c191203103140700311808000b043d0108000c40c00c00d000802030030f00002565841c1c2c100a02441d24600c20303081c0426a011010800f0741c0b5a0084202025040c0c5407010320289400b1800040480c00cac091489400d200c50102d502c40d51488410004034080c20b000080c3e010408204c5030a40d0100f10301c240801c2c000b000100302d0346900c041887d50164201d4161034644070040503000a1320f690031070482141c44041030219581c40c8a5000304900c1000300d4040080c0c1075045286203190700704903000b6010751003421a20352080c4c18030802040680c4660140d8150050b0400310408495880e0820360701c42d4a07000800240d0303101003040c0754000301040025414 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 512057859 1250 512056609 512056619
    0x10060e0406080709020d06080a05030702030601061b1719110106060c0203060705090a1d0703050f04050705060901270e01051c020f12011409010f0b06090d020625050115 74
    0x503aa0f03c503c01c0b400c807a9400142007500b0001c503070040700500035104c00e990034140541011541da800211003a446802120000240e0600400c10146407210701e001c0820025182d4660b81142c001c0c0303d0310010b500004105503800c04003084858040d65207c0e444400b40c110711603100b642162401c0d00000c042c85018208413000d0f0b41d000452a500ca41e00d4640181e03104207030400704600074240d034070046031661403401c685041d070a400f00c8a0710072050342da010042607980c000100b08a82007941c01401642081006001c1400c05400812000006040c01c1c1074055184076803032070540c021040001c51030304d00f02c8144076200e0361910180c01080e080384c61301400032484100344105031041000a1058200e18a15401c44d12074049542e17150703450800801c10040880326480d4801011548407207154a0f2581ca0104803d15103d1001c0501c8050400340c1096031034400e000346440684000e07a03000c0001c0c007200da003000f680307140003030581c0301c141d40b807001114640340c564203480301c01602031180401240c060103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 512059109 1250 512057859 512057863
    0x8061504360e0a020d020a03080403080c01150e060904030302041802071203020a050d09290604050c0a0c150b06070f1a010302060702040b040b0901081e030f0a140f0310060e040608 79
    0xf805501220712040341c000c20720007d0404611913200904040002c50004107000f1494054403d8480100c000e010301506401d81480c04250750040d02d841c900c2140100301d190500c181499030141c0b00e8240103140c140c490303590300c11b40c1c581c15000c3c12a0315000641500bc009406030300020074843d5041c207500f4036003000710140040c0201401008200d030340d400c00d0350500a070f4030301d04c1199400c03140354100d80b01004032803481192400c803a610700450816000c1000c100703034070040300e41c5451250f940045040043d0740300c00c1c009070740e054140006900c1e40c014081d00e5680f1001070003100e01c0ba840420024000d4a080c6a849040480e950340c080ea61400400142c0c5543c0c049441c0b00368121400200340c404900081c0040407001c14080c1c000c0600380000c10440400545400501e0f800341000c49240141040c0540c0c0340f240c0e2485203c00700090000001030750243c103510100a00020b101c605202c080c241c5480300d50070480c1c2441d0031005240c01088140d400c231880740780085d02650240714642c24200000e07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 512060359 1250 512059109 512059123
    0x100b0901051c1a01092901271512050403021504081b010f110c0d081801020a08070806040c08070f050409090818060a08061504360e 58
    0x500580d440b49000c48039454000a0079511984400a01c684201108003298080c2c02406120310051900700c103c3c100d0850185060f18800c4100b0350040703003034440300044403c042003054194031a6402004007811400c2d01300040041c21132602005c860301c000c032800602c2800c0c904c42c4000701520340307003c4c040441c1d8041084400206640081c0c641500c8a1420301441e00c02c41c0d40d000c000d030300600c141c44048001134002c000e80c140b415605020540403244e004202d1702c14540121308a82c80325a4071b03060b00c2d014405d80c40d031048525400c00c3e60700070001403c034260390007402c01c01d00040d140020004801d03042603101d03070068029101042030040c891800b801a00b4041c045100b40b11610108038080351041e000c5030090800410b052105030683d150642060304600341910418040c484042800e0810900f40c40741030394507540d21202601c5030070038403402c03284012055a0000c003c0101058005c403070f00380440d007200300d14070258000d10401c00403c100e400030720221401500b04141031100400c002004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 512061609 1250 512060359 512060369
    0x5060a0807050d11100e04052805040303090213060503060c0a02030a0e030c030d020f10051306020306030a06090f110a0602070905060a090c050409060e01060912030e030601080f100b0901 82
    0x3c1c200c6410a0401840360003541001992107090140014000c0350711080203101444247c40520542c2c450440700e000000c940510084803a1b240d003001d5545401c26000300d9085070080c02c0001d0600c080303030086070055800c4148182095101c0000704401c2c10704015190f0300000c54043d02d8140b66a03488025242c0c1715480c40f02080104950368201207070780501c40c1e000718000040885074191580a4040d41703d801b1b10b4050394030b0703005408840004411030301904d482252070050030424951555100320080d00041c0245800d44910749001000030354500c81c401d200d50084e101803591a0941c40c107100e10f01020712103603008455185082024a40000c0c0d414191502c68002241666640c404503403001c00c664480d0000314100300d0440c0d6200e820500520980d411814280b10349a1203031182a560349081c420200090040d04040155100c50342140f08842d00c01e00c0c0a40c1031001074400223141602c00c0e002003d0580220003c902c0d5400100b2150000c3d290019040c030921031003500144640c0814420 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 512062859 1250 512061609 512061619
    0x270c130b040e040b1e1609080a110904030c0c0e0f09011406150c031b0717030301090f020c0706200c030a24060f090b0103090210030f0b120105040605060a080705 71
    0x10800c2100d4501040002161303c605c9034800d4640251441860300c80500303054045601100c012858150100c0c06402c1c4981100c08280750104050610130001e100038020f030104100c0d891020b000880000c4640d004020401910010307080c04401101190400782545070207a1403c0e18250001c9035085a2507030150003101c03c246c6031072110440c06028496070a0a10842c040003482c403403000c841000c80440448100200d0381d500743c4034502d140300016212001e004c603510500040207141100d420004000c1c84284003d1305102800300f840346000f0142d04840f0110b42010041040d890142140103c041400f4005200b1003502c600401d44403e03071580c0c00ba0500c0d180150911515040c2c030070129000b05e02c3d1004200e115038039100c0c1c041a00f200d010f00b82d019030801841e800c2c1d940c0f013400b03007101407a0000c00400403440c0c1c0481c258000e00240c04400451a181c0603180312650390700b40c03004c041610400001c03669242501c0e200c1c0484d100104001c1c4103406a250a00c010179000400505803841920 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 512064109 1250 512062859 512062861
    0xe4306090506070c090b180c03011a0f041a0903011506020607181211030a030f12141f12080409110703020604030e1309290c09270c130b040e040b 64
    0x40400ca250101784076030a080a0847c060207410900d4000550403205000c1c80110640301d0b5089061007445040403100700c06400788402e001c404010650400039a8121407082d01e0151100c0c08a82500c0c0d03000f0718000ca032901030302c0406c01d903501448890b43c408410314103030704902c01c0b1914000110f81e885c011480749402c1c03217004404000720686c90b43c41e1240018111140c07100c5500e0002d01820500049600180811a8a08030000c140c090000c03030301400301d0100800d645082ca0f980c01160003064858043c112002c0010f5440e0401d810311001074001c1d01640d40d00c07410006914169940b4242074600c448003080707954040b070760100c0c0e0140c00c1076061421710449180440000d0340c000207503a9219005d480c03d1041010030010303a035901669000d410004866540094010001410880701d80726164400c00101c88075103040180d0072404850200c1c1c400203100501030000500604895401c021080015403013040305205201000501e07072600c2081c134160030304030b0b4402d6411010380010011042e500c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 512065359 1250 512064109 512064131
    0x30f11180303040f080f010e1c0e0f210c1e0910030c090903080604150605070204090b070c1a071409030c101e030e4306090506070c09 59
    0x4000c8400a086a10020101d80c0c0c681e94400e07212006c440c2c1c400c006601c4e000840b85020404910310300d140300b20041a080708442940e0503544440300100059000240194241c02e5980381600305242000c0c40034240007004019103141d191402500b2031511941c40540c08000403003c001c0600103032002984c4071000c1c0d4a44001c0801e003c0110340004200e50750120b004103440d5000d90103410018040d507a20b51085d11100c1c24042143d100e03400105e031000c0318000c01e000d9240124010140d0600c05417000a60704003039121030038100025110500042d07400c060360300c10f21100e010090041c1e45800d641607800d040043c0060302c051069036a070703000000c02040a40003507400780082d48850724040d107420603004081c500180141200050408407500802102402910030310542181800040c01040f2805002c5160800850105075030003041003034410b9045d10020f640c0b0750300082e403402c1c0c0c2c3c034580035810120040c0c005c4000e50000343c0502e82c01d101141c08038000c1d4040780102c5810700c00004884a00c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 512066609 1250 512065359 512065363
    0x4060e01090807061d06090d0201030b011101050a050603070e0114220f0917040803030f0402041811010306060512060103090302030f0f03090706090e0a0e01060302090f07030f111803 80
    0x703a88124214050100f000800d1500040d0a82c01120726650402206820a081110501030716890542040ca00342484005500980c01b1044141050601c80c0040c0d4a030440c0c03034255041104c00010040e152424413242d0301b1708011040191503505008400ea40c14050542981d15807089240d105a0b1f014482c40b10001c0b0300400d2084944401205211038a6061040f101070b0403141c00031920303440ea2400c1d05410300341c054140c4055a5001018502c0c58444481d480c40302c020160060760300c540e0301c0305000c040c200c903810700701d07800d5204002448802c50000c0c0003600b00c83d00c0d94031210070302071304012101080c3c400285003a448002420002009110760408034550b0081d81104800c9440016281002c0141e19010398415100c40088403202c0d81c0303d900481e52003035940f01d40d464036110007001c2943c2c03146030f40002c1d0030804c8c03c000005150750b40c2d40000b01700010980d500180d00d040c0c6014087c14580c1070082880006810800f404900f4001c81001500d110700c0c084e402001001191291041c3e5003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 512067859 1250 512066609 512066627
    0x10522090c0504020f180f1320030f1b0a08011203090305160503160605070201200607030903080601020604261603020d02061302063a06080f07080304060e01 69
    0x140013191079800443c07200801c0d40c006144074180d0400c966a081042ca420360641e80d000f107000d0221840801c1c04001c240240803106041050707c17014007940c200003d00714028510403141c0301359140780b5040144006608030172041e010202448100310480c13800d41c012a08604490000c87c00c0002e02250f410b0464104071690001440c9000740b03d91413001c0016215aa000d5541c200c2c2542c0040c14000c0c1c91000c0c10085116901c08540c003071281d031025601400482d440388810000c0341c800700000845090030100308482210110380d41d6181c1c002410303885082241c2c00030080c002004682417603242e58558905031185c0c0c0800700c06084d4000700d8003103040e0030b884244005614a420701180d914019469100c00b0900c0070042c410100061444424030962070201707900a030801d45030200034040a40c4e002c504485a445c2d51b9110780a003000c5041414110340c1602ea000c82c001040c80c01e2280060410b90f224201e40d40c00d910034a4103010304180401103404031401070404911010f04500180c030f003006 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 512069109 1250 512067859 512067869
    0x101505090d0c0e100602030403230708060a06090e0d08040204050c0d09050d0807170105040207060e0a060e010c03021e09030f100f1116020d0602041a040509010522090c 74
    0x100d814800242043c8010041d0b0044021100e83c0d11491746481c4101c0c0c0e00d0080b80b0000d021561040400840c0e200c048103961174100400054986c0f10391645410340c03800c1c009841407000143d4505041180744500d20840b040310340c640e03025000480d0a503000404051014002a00c115500c0300800c144450031000c860007019824814003400469007046038440781a140100082094100042c2046104804040500001c0c0d10024660390801003408020740046908880c0580d56131040c0344400820040101c0a40c1300f08404501c010090300e40c1400d40d95402e000c401414018480060400c0e10140094140c0d5020107203942c81d400d1040000c0c1c41d040c42602c581d0024043c5003000048107a0f00d412000610f094900240407000f070958003000b852198003181c5007204950f58540c0010300c4d10052068126000d00c002504160316030b84190704100e82c0103070306030104d200080e0410a6040264806004050850388054041c070f240c0d80e1044c0e0781181300321131030186940e1a410710800c14042c1c6500081c00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 512070359 1250 512069109 512069123
    0x1060609031208070521060f040c0801060e15030a02070c0b09030d030e031605030d1a0609120708030a031a0a0e010b0a030609020a0903061425020102040308130e101505090d 76
    0x440c0800103c2c580e40f2069a00500914a000300102239082c030340100008402266940c088aa1800d102116080840048254840b402d014003440ca0b4881c000514040e0f4040f002c016035440d05e5207800008a00e46d40d00000d42c002c0107000b0300145960126510300794091608011456500c1c54000d40d0451080d1182204090301d140c2d0300c0d60034000c00102070031f1180e240003020054900c0020032501141088681150300007030402484945003802e058000e91140c0b4503041f240d0103501c80130094195048441200c1c0025035078100c05039055080b10032118600d409803a40d0101a05050822008190501a40600803400103030211440d102c0d5100070000d05500c0000c40d225841c1010082c0401102d00c42a00e515040400404640d02c2c0c1c0c041482c001c1c200b10003450b50303615403400b0707a202101d040d090309010f55609010000121b1506402403513013128004800407042d01b82a8207050905000c0c0c0030410509042e1401e021715040030b5003200718000c06023061510b400882c000030700f5000e10003000030190 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 512071609 1250 512070359 512070397
    0x24030a06050114121c0c03180e0603070b1317160608011a0a120c0908030c030703020106060f0512060f12010b01021c1209110a08030903010606090312080705 69
    0x3410000300070b11520701100e9078400031045000b07017561848842005400e030a5083c1421401a015403800440180319040c54000101107c000c0b120f030028a038041c02a40b40c0d02030400c1090f00c1e040c044140038081d001c103404c2c105429492402e250581901403810411401c980503913490500f044a0141c068000000045c555101d0b4002010400700384180e110185e8010324180c5071090200c152058142030386c0e02c0381080f40080c2d60705005007a03ca8004000d004181c403000c507015800780014080c40c15003d00940c0d03502c0c81454000c0c2101c1c07080d0300c0301040100000c000e040b010fa2000c00c4804020180b5040c185544510000400000c0200201c69000c0c034000350070115800107401442c403a810917000d580d004003020300e105004c0c200c4d071003102d8001450414008105801548034900081c05400140620034114012982c51505600640d100d43c0c00440c6070421441d00f40100d002902261400302c8a113461940c075024810b425520000c103001c49000003441180c854002d441400858030006c490f4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 512072859 1250 512071609 512071619
    0x11824111c0b0405040203060403081503070905100501020a02090403050d1e0e1005060d060e0f0d09080d090b0301030b071e0e04060b0f1605010221010e0a0524030a060501 75
    0x10001d000e41480301e03a18100840200545032620400c0e00c5030741c024029240656035603800f11000b840007800da00c454003104e240c0340c0b01c0e910100405400350508940c0050682400c2110035518101684400e045500020061005071503080d038158009a140c104681c035030900c0c1e180140500407111070000b4030450404c48400951144c0c0040c9114407050b801c0c1c4151200d8805050250b03a8110350054209d80460786140c0058020380c404590103100b00243c0c3c2500c0d014105c91030030000c010310442c0000b64904030a1189101c06d10050700d68512904045420394544883c0c600e0340d0105100140c1001c85480c00145442d008061010316420101c41602c0c8003003460b00007074003800f080d2201502440c50044049103003907030301085030b080441e00386441e800c1038500e1a0292010080c03001c1290340755009d010b503040105444015105903410481d0050442d81845203603404410300502224505080c541800140600e0310b480b150044011160030380c55400000c0441d103000e888a1005000c1842d1000000e1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 512074109 1250 512072859 512072887
    0xa02030c0105030c1909240801050f0d060504030c1b0501020613140f010609060527090307061103011508061e010c080d020d060f0305071e0513060801182411 69
    0x800d4501480c00300e410304041d401760340340f0811f450300c0f060702046c0b11900600051520382c91540180000038507444083c80c980e43d8410a0301c0d420366003240440d200c140705104208101c1c60048a4002100c48841c2c25440d1400007540c1e42000380403404c6222180c8c3d00318081c01000305440741a072601804a80c918400032107118020980c1d4031800801510b0103001144c58984000b07070310a42c81c0b500c16001401860b1811a011003600a08041603600c020440781000403030030301680c0e444c903d080c04130320346030340c900b20003007038058440aa442e081201c00000c10649580b000da0b1151030071084041d41410442c20001078810b4440c0b03100c050505030740801d04042c0013189130010140362181c41c005002e4103907103911481d541c1d40380d400020032039003000c5420301c401c0d540e002c090501e002d200301400442030307078980c04a00c010070410b0810401caa280d41090190100074003403001d41c981c0c03401c0f00d50a0740c4050786910b0b908030000c031a50800121911000244002242c00a22003640840f64890340c03203004d103910729 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 512075359 1250 512074109 512074127
    0x7050321010812040b2515050a090f0b0a0608030c0604120e010f0e060d020c010e0c1e0d02040b1f112103190e03040303110a02030c0105030c19 63
    0xd424140440004036003150007007266085a8011400c007810181403412243e640c1d0040d034881c010a81e40010010554202802c0050825001e030030840001c8104140c0300d0159600100351140440c10100c14070000b0302210482103a00340c001c5581a0291180b02c011405019964842c001910000c0b0303401882c0c45010503103d000d540300700a1000d01c0c0d1007514064419071000281d160125040c14070041d0f40303d00aa940c01310306a8028440c91818120108a00480c5c1010104103081d80d1f4444082900d20410018101240c2d011a040079400820a000c64106001844010702548204040c1000c64640750001007100344000c00d040c4000d543c00b80e000c078128001000480001384007844100c5524008a841c01c1038000c28102068641e004170a120266440a0a2107071640f0004582d40b403000c01c80e2084518500e100c2000e035580e5461401d0052203012021074081840d0410650007005070b400040240000a080c20050b4a90f55000c52401d0a40601901d0130458440c0103d52000a94010707101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 512076609 1250 512075359 512075407
    0xd0203060709240f110a02030d0903060f061511120d02090a060c03020316021206091c020c0306150d08070c050909010b030706110a051e010b011701030b0c070503 71
    0x1501d40d41188040d1807060201c502203c20100700800e18804040f8440c00100c22121910130407100e0b0740b01c2d2580421301e02504510001b000645990060042100b6070068400c84079003000240085410035215451096081d507094050209400d4050481c5d8800c0c03105602c840c0402c4142c40d103c031042e41c100d5001c1c6d40441c50241c8503034940356000c00c100c3c0c0140d50100780345d605a8029414891444203040c4064500391042c0d1344144948070300903e0302020072a05125084c440d000c0c000300b00214540081d104001c4405809540000c410130009480009034280d00c0000070881e80c1c05d903058a0b010039034bc141e040c5c001078021a400511001404841040007044030b0081d01c0e817003c42d540c0d4061403401c89408040681d0b06801c000010800345100340c030041c10b40c440001c169025080c440d0740e203030f1030800d400c0c00406180d210b20a51001c1d1003c2803192680c840b0082c240b000f4149040d00741d282d4000c205000042041c0340790300104070b040c0d1015003510009984542100c1d59600700d03d0b2004010042c4a403a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 512077859 1250 512076609 512076629
    0xc2215030b0c160b131e03180308030c0d0e0f010203060109050406030818032d0606060703050f03090712061416050a081510120f0b0d110d0203060709 66
    0x85000b00108608035000c0766941e50348908080c0d5643c2e12040c00b21005031820014004610b124404154080402d10314070200410040e1a01410714001d0041c40320500b8060034043e0301d40c010804204d0b20800c8035404400d14030340070f517548020081000282500c0c0810909440f50100265118805600075406120700f6200c509866590f00208400c1d41c0481c040200300314001d01c252801c0300e14401319101c00d45d9004054400820300b91406000a9030341200c9a04d1443c118000380c1c0510500b4080c40345c00c04020303500d0a1a065443c2c80190942c0315510807600d010302e00000095200c1800e10140c0b02030030403050401505201030401801800540e140c0071004c0a100e4081204010390917240084502e89845582c100703801448213850701d0100400b80c034041c840140300200360303a0740c140d92555541e085485a0000721103041450381103c038110800c40c40d841c544140301a16549004600d2413140e8004404001501400c02081d1401c54081c4001d4040c485c0e0001d10038102e1b000420070040c5d49808030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 512079109 1250 512077859 512077861
    0x1a07051305100f08060a03081804050c0f030f0408070506043207050d080903100912050301031109061f020714030c0604030f020604030f1208060306090c2215030b 71
    0x300700592180002c141c2c5003c14808906000d8042c020200e07140d22440007007820405a549488242e0194031501000200c210a901200c0c1d003450544075040d0094a00d040441c200040410902020b200280500c0021030b40400028200301c40742c4112021950304c10b0a680140c203292410800d00c507039025107008490006060822200001c03030f1440c1c40c1d40d00c030000401d011842c2c01705000380701982400664040e0401c02500c030720754034100019410f100303000c10700060400c8641005101c43d00407410401c100001080108007003410030b42c00084100044038a8042c5454803c0055a00143c03501a52914060600394101c825000300c3c141e8101c400f81440210351248280c201500c84194207000790f03114034248018070114160400c0001030360710241100f482c040d00e0741c589070502d61200104440f0410708204011015510422054100c44103800804841c00e087d071095403146c0f10441082e00503c03035860042e0f40701046c0c0c15041406900c40c2010000780d0390385075005603030344820b00042c0e40e0311070110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 512080359 1250 512079109 512079119
    0x50d060605090901090f0f021611091608130506070c050607020f03030a020901020c1518090106080402040b1306170105070513030f0302280605010506030903090105071a070513 77
    0x107000c4501619008100180c203030f0806207928001d01982e8243e0401a940700e00b00010481e05200603c22043c10000407a983c1c02c040c6014000304812052a50040001d0428440600012206840c40780624184040f440d84d0300b031800000c10700c1002c8054103d100320014480441d400c0003000600700d000d102035522540d52804180d03950145031074112401c0e032040001400500c800e5014000200c81441503c002d45190300c0040c2442100c03c6644801010000c6d08201801000c002500705c480140c0703001c03145624155024003880070092000c2d010315100c0891004598607032805070480d09003600100700841d1245001d401c404103000038408039600e0980070515882c000c00c10b80d0f103100800050300d00041c0c21541d03410500103a60008500354410084100c1041c04084201c07070543d50354042d100305105007400c150041d6541a884075015083c104148101080e0102c00c03074901000a085c00356903180246081044080c04001910f000c11003030b410702c80f03010b83c407100400c1c51a075043d0390010070ba6154 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 512081609 1250 512080359 512080367
    0xa1e03030c08090307030c050f060f070e010c03050304150f021308161406131a0910090302010504090e0c04050405010915050c0a1202090a08030d060f03020d110a080a03050d0606 78
    0x39280d500c5184e1060104a002901ca1000d2002c4a44100d00f5640c0d8000c1e40032660749000015a10148150419400c000080e6131040120006030b200f40380218041d00c064501901c0d61202400180c88000010703402810f0804030382140748005c1c02c80304d04556036090b105400440070854001c0403454041c003100b01c1c0b514480452084159008103403c14690b10b4000c0802c4510f03032003d024450000030407800041c8410030340c0301c0382d14200a070381c11030381d0784a030071604020341802941a00c0c0c040c821080014800740c1d0b808016241590101d60300095041c4440d003103189043d01c12a0a203030700030704203001c100030460107402c003025051040140101410340d01048100352842100c202c500003005000300140c42e4401d400c0c441100c5865a00140f6040700b11022501d200150780248815500c00100c6a0300036080f403040c9001020103c90348000316003035034000b0350485803907800502100e41c0b000c1d2884d800e59078401608010a008022208a01000d01e000b4201c1d03004a00b40405492500d00300140207402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 512082859 1250 512081609 512081611
    0xc030203011a0a12181110080109020d0b1e0f03030f09040902060904180b1513091a240603040f0210030b0a08151f03060e0a1e03030c08 60
    0x3001048920b49003100c540c0c80c05a80040400750100f04021380308891001407482410030301050300304c01203103502131420000b089160007451103010b00442540c02004c154480f45240c1910540c05000d682ca9401030b502c0c0020308020180d442c0d220000b1010b140014420500d182009030050700d40080403140c0e2020180c03240070b40c5085103801c480411056003d41381c194170070543c841c4014280c505040c0c1140c041012141c2c00341c0820191003091918106020080d80800d44c003101d003109a4008a550030b002c0307a04619200154544a81c80340540d0081209085480c032108042c0f22082d04075181158040b00444581958144040c0000112805da82030030300440c1c1c0710300d8010100059040d0164280a000807100003190101503943e0152001944d4030000315004041c00b0004203142140001003c11285c2d0140c011001459512208000340c0c0310342d0800001c6903000640010201410742c030035818100c11100013800700700300c559480380a00c1081c8425200a00a80d8200840240154180d0300c0201c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 512084109 1250 512082859 512082869
    0x3020c0612100603140103030f20060a0f020301081b040608030a0f03060503031905031905070509010206060409030c03051309020319050604050601080a020705030c010c05040e07144602010c03020301 87
    0x80d485e00600c0400d0140f14042038505003498464906940cad4801d09181c0e414070a10003109810900a006c030041c3c0500540c80e501403c2c82c0114a1540b52038100396407242e001d802c4c001019051070140f041c80ea01c55006000910003c010b991382c881060400400f841e600480940c00300b46000301c0801c0d203040000035190034040403101c140040641e890103030784a0704000e0001c8c40340d4101d0280000400c40d00e009180c041c403070725102c41d910b40c05200000b82c10503600800d01d0f40075901c0e060700900403d51042201c9130950301418a20754070361504c69074000c51903c0380c10001a6600020070302800643c02c0c441e1b07214000885408002d541c0720402003006489007a46d0680c0094a05804918120402d07401018030620a004603454005045001801d41d0400400c00011401c040390800030703640040c1140c1ea01203490b207054120f640c1c20100790b194a0007560101401401100782641c01000d07085600e8000721450002641d60703c501c0c19030f4542d1650644101c3d4015400c1a80000034180a4000c1d64181c034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 512085359 1250 512084109 512084141
    0x105070c050f0a0b0a02220e070e09240a09050403020304090e012009040b0406180b060a020307030e18180f0a080906070606050901080a0c05060307020604020d03020c0612100603 78
    0xf03101d403405c040103500f003404044000400d889000600803001000540204005c9007034044d5441d08a4014020b10b007000c011500800b405400c0014124040c902c000d90f480705052a2603144401d000482c054000503005403031035600d40000c0c0814140c0000140040b2858048180700f0f5080900200303007a00c881400c2d0300c15004024036028107114040014000380305019100044070043d280009017500e03e26880b5007848104404c0c07103000001c40c0c0c0a0007d1714841900d00034070381045028001e42d6445460000350400c40e400c40c0500c2c01d41c0e035001c8004000c9854248089403801d1014642e0340520b0542440d5809114150050b603948101140f180b01e0140c125102500b40320116040c8212980f02d5042124038681e180000b01e110350301c452407a0b0207070800ca002000d42401514281844003440c1e00074600c18034080c81000042e035400a80756900a90595048034242c1c1d2038601a071508110f03c410aa0050010503004410343c4101e41c41403040d541a124400d0040d80d40300103a0450300e10003109620701c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 512086609 1250 512085359 512085361
    0x1021e040e0601210c0c06110f03040305090607200a050f011202030411030601080708014703060705071a0405071511031306080709150e040b030105070c050f0a0b 71
    0x50340c055a040b070044140139910b0515060460091802c580382c080710b60000c80c0d040002c0c0c800784000c9104100420304070482c6245084030b1880114a0742c04014001001c0210000b80b01400d5140c10041c0ca5015510804190101039000040c100c2e0200707016890740507000000c0005002d1410351406002003e040c0c4400010400340300900010f9840240709a8000d4440c2d03c5100480d02c3c1048440c0c02490004d0103840c1582c03c00840c07500f541c021080915109480700400401100307052048040c83d556810b01410440400c4548444a11750342c0c01c4a41c903000709400c0150440d000802040139610130140324181540d04285e007880c421003610050242c5c0c0c040c4000703201e00003e0f12600d4800061a05028680340d1001c4076241c40c1da409090810f0040303060702c400b0804103811103003003904282c10f401c280320713003d0034090038231041d0000d50403880400400c51500030241c0c4480c0e00c41010f66402900074041031501c504080e080030b4a1076400c803110711690071541046d420104910b50300d603a014199140d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 512087859 1250 512086609 512086621
    0xb011209030c1b0812040509070e030109050106060305100801060b0706200412060615140a030212090d1704050c0f01091205010506012c04021809010801021e040e 71
    0x5100000d4100e092000040d41d40c00412204016141c2d00c0907000741c900140da003411241414000081240d003603408007170005020350b07901d840405900c10301603d084082201108002400b52000510241440d40b034028049011a03154103d1031003800e42c80982c0b2050755860511130f088920504c5907003900791003405500c00049554000c400c92690200039425504a5100c1c1140340d50301ca0f900030b0294001d41010082000024065000106413542d11003000c00d8102c1005001d402441c04070404c15900001d014001a000f98181c803990740804484210070300d00342c10030039541c240d00c4440f00c0210b00030b01c03202003803810b0310010a449981d010020b440540c00b41c2051140903000605141d05002101d440400c040d4144103098281030300490001c1058105031002511030344a645004144100b140801c08107000741603118286e0480503500141d540680c50041402031241030841070b4030582010002035074680c1500584984020356402e41507050540c1c500c00c80a100d035104070b103603c000003000510 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 512089109 1250 512087859 512087861
    0xb272b020c0d021f05070203190317090708030a0c02030105130309090e03070b090a060b0a0503030406050c07050d05030441030a05011b091a03160c0b0403080a0f0b0112 74
    0xb80520180c5169815401510b0078030030610000a02c1c0001000400c0f0081540b40c100306481300b40707219804030200e40e20b403038500500b0b5400c0d120140c0c5a0340c5032003010402c2c0034401c100f20b0300204030042c1560340b12240c856000381a441c450038164840e41c01c000c00704e000c0c12000d90a9040003070345501c80360000740c07800110070302500c44102d284a55000a01410340803079500360401e882004141d01a01e0ba0203980c0c5006411a00ae011000f4001c4030b00c180244155180042110151255410200d455071071003040c007444d041013a044203401c6020f68401e041080000009001079a8aa02011a0044400d25030450780180580c0143d500d4105042600ca400ca07804c04d5202c80e1200a81650f00241700da49400d820348452200304000c081c4098048071119903c14074030b03c00b511002600d40d286a4442006010b50b01000d040d0807002c2041e1505c1550160080004c0e18886a100e4551003a1745054100505070340c0341181d001d02c0040c00c2008071590712002e403040301d40302c80b03058498202d001c954071400e00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 512090359 1250 512089109 512089129
    0x7091a09090c06090121151503050f0a0f0e1c12020f12060438061908090a2a05030114070305060f06040e0403030b09040f0b272b020c 59
    0x850400500346c03a6000d5400e80508101903d910200a50032880c01114407000395140000000f05880c0c641130150320982c1140d0741d9006801014040382003140145410300900031408407420703600c108800441d103001101c54803005000c55880d8a04050001d80000702a441042030001a80504005500078542c030042642d41100707019100003006001180c454014103080804803a01600507441a50aa05554005811000260780f413506196580c0b00001e400b10380c421148003440380880000c1d0013160200460424241c00500040d5220a02d0341c01904098031811001090f040300000403846040500448821003001041c25049688801c4210f00401c0041d02d41a031066805e0201d0b00e4941e07420002d07101a00050300c42d03880ea82064500901201d0a081500307000303001541c04c1201040100f04401d01c040d40040800c2450340d1140703100c80c074018020301800f001c000d01482d24042d049002070b500c5048910071901e80c09500c0f90005503402060300115442c01a0b00c040082403030340c10054021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 512091609 1250 512090359 512090387
    0xa05040303022b0c05070201080a09080c161e270e0f030c01050f04020a030b130804030b16020303160c05070302060c060703110403020f0402070507091a09090c060901 73
    0x18200080402c05040703c40369024143e400f80b000d10400400300180d841119946055401d0070703440c0c840d450340080c0021000502c240c258642c0d074440c1c00213000c180701c111394441e0b84401c2516080c107178401c903e1020385154060020701690340c0012000100c0d482c80228250792440101e13601c0d41604407000a800c88a503206000c0d80ca07100c1441d501303840000c0042d00312480c07460010f5515a855401e04508440d00140940c0760f00c450b6005103c003613240e00d6200020350750495a107100d59a5a8980c1107104102c00d04020822440080c002040c808545065030181040810003a400b901c0400201e0740c80c00140d4282c00d1b1010058050901b882c0150b00404505201d0700503280c48079682c0d000280f803034010614025194208100b0091401e5040c8511130250410b104201c2c02c0074116008a1400c42e4680d07580c0c0e004613800521072003480030800811000f040503e0003801120740b40481b011110300300200c080d000c3c280050210b8078400c404a282d5051080c0a880141000402801106d4004c900c0700300b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 512092859 1250 512091609 512091611
    0xe100b18061b1c0201140610080702012a030b151b0c0406060503090f010e0606011b150209040b37031a04021c0c030b19060905070207050d0b0a05040303 67
    0x100120450081c4900e070300e010725503c5500005804600d0190135a400c070300d0291101c4044408101c03043d59070803060302c61a400b9240c985041e5a4540040c0e0042c52110000c9000c0509c01d0031304c0b0150f60700c0b2010501d081c000740e54103220690301d40c02480a560300d440104407a4000900541611190f0f60a0111582800000303c5030340744800c2000c1004c543c500d030028800100300204006481d00b040200c0d0315001c2100008108405899074680c1c0c440c080542010704200c8103421001e0300300e0000f0710808900f03800120a0640746901ca00c24802980918080ea00850601440d0302c04c614140450181000d00a8011810255110140b40ca41d0701303490302c0340014a140c00302c003002040d401c41c41800749101c5194565480c0c10f160040040c40c80f0011002040130002114090010b8009001c00e8100c9074810809801d03500c515041000400b41e08504a0001d4605080001c0c041e450717800c0580a514181c094135866621081480708031051001c01030003884c480001324a130090164403440c1c1c05402454 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 512094109 1250 512092859 512092897
    0x1b0213140a0c0807050c0706030f0b06160b13052d0d090e010e15010305070207050411090406050f1c02010219050607121b0c08040b03010e100b1806 65
    0x48921803001511003042035660381030764001c010b03004805540c00c40d2441c14000d040c002c20300421940d80e207590061000301501c80a0455100e80c80c0c0c1c001211104c402050291500c0308100c0000c40c0700e65001080c0d4001382d0f04070200e1600c0c1d0600e40146081608a0090121250720315101c04481c8440340c1143e054404504240140480c00d004000c480ea4680d82d5042809180c419032403910801a0043c000901468091050b821205220150148420b080202e50f660307500e0016070828000b640181c1c1c206040c0b11500e841d21905030018074041000311820400561100e0900001c2840c0d0030034076802001754680b52000c031038103840700b09656205104450040110440d01e400e10807c030a012959948964107001c0c11a40043d401032501240c00c4040040b0b02003010118078070510342c41c2c0441840103543e03e40052000100850b0003918014850175030303c1d60b50b00341c11204540c08498050180b1160f030400301e042807050045035030364000f448020100340030110401215510194440843c02c1c0300207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 512095359 1250 512094109 512094131
    0x280b0c04090603050304080f060601050d1a040203010906051e06040308160606030b060102010c1107120309080f1f020c101d0a0b1602070302090106081b07051b011b0213 74
    0x2008a402070f500c98000b0f19102d62a01d000e80385000c9000c45c0000b0306070001c0c02007101d00d0f680141036400501100c2400308403c50000100c2c2d04241c1c9501e0b2058002707000100200301c2d154240c0024040301d038196070404246000030f000f0244860b40c9280d16910182c1000100085410318001d0044c610403101220180442d83e501e503c211251948100c410500d00f80820078250303028030445041d04d0460800c48400460441d510340c94009034040c120b00301410704106014988542440c0028202c0d4174115012071003800f400c40d80c0c03201d000311803c24665900c07000c07a203a9840c60080c5ca0003894500010310034122100c0d0307560040c14455000c500d10303c142c1e03081d2507490b400810158603c6401491401e6117402d01e9405190600800044001554030045081005860308070300c0c641161040e2410f800e0548441c480d50010140180302c1c51604000410b60074140b00010a04038103068005040303000d4010b2003001074441e0355080f4030001140c10f00b104140054248030251a0804000f4900018050000c0f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 512096609 1250 512095359 512095361
    0x10302280e09090a060519020d050106080c070c0506180406080606120714060307031107030309020a0504090308060f0a03240507090b0d0b1903030801080d08061302090d02150309280b0c0409 83
    0x82270b002192591548010040c03150400605600003c203280342902e8101c40b40c0f03459400e07040502c03030b075070203003400043e2000703408112000801d0a1400038018801c1c00e95481103540d59203000d80702d051042643c1484904d011314001880d90458003020380070001002d02e41c0800086400c01000c041c10725031524042c2c0d1141d01d00b030000b0f00601d84291000a40f16400d0300502c040c1321500d8014900403440c0c0584140401d0700310900c41d40c40002140e4075540006814007040090300705900c010414990940d40c0c03c080045000706c80720072110744800f0455540c6020088038095880d1181010354078040100c1c00078299250000d80002c1000307400c0f03032261540305081ea40140c0c0990301c19400a1040c0b4018803850703405101d050030110701c500d80000641002d0000860141e03d80e0100460b035035002400c0c0b501512080034401303040350002c00d0500c460401c4410220b2550080700c085405000d550301c4d0f07503a1410300c403001a01c1840c150680342281051540c074440003800290001441c20000d000000d611226 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 512097859 1250 512096609 512096617
    0x130807060212190e0c0402210115030e03041202121c020d090e0106020303060d110d08070203060a0905075103050106050f09010302280e09090a06051902 67
    0x80314441d0100386009152018002c103c0c000380c0a0031410501001080c40c0002400000280c08540060362411044420403003000c40108080c08601000000900400a12900c28002c1c8030b644050105560105880351a486107001e0005900820403050003d0f04200215400e60b0701120300300c0c0c0c0341d521a00c41e0070803110003030340900c80140c2c000c2c1c0891403070690084140300106503010151145506180b0081c3d1a030000820f0140203240d100c6950301840550118248608409005072030160814141301c5115404940264000e11510000c6a416180e52185d030b503281343c00030083c141950500440842c40c0100c5441040c0d0000c0c6040620208181c0070750f1005400fa045c51440e146400d00661020004148800e000615242c2401048119046000c554100c580720101a644468810050700240a03070b00595901a8070004504512580300315000050703030300c544501003010020b8080000400040b03900403510b0b081207881500061b6150869604550402c0040c040c201007041098100e0304 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 512099109 1250 512097859 512097877
    0x813081c0b0d110a080102070803011a070b0103050105040c0e0405150702010b12030408071d130606030f0b0a060f060c141f05070f0908031804020405042a05030f1308070602 76
    0x2c2203080d900c4a92134030314031a1006045030b40003542040156210050305020500c150042601c54a60400340c3c09401d001305c41d01c9942c03100003020b05507140d05000e0b009205c01c0310b08a642e0304103c103021034031030030103580705200316803080c001d2186005035800b603940c04801515401c155900c0b41c411041941c0c0d07180280e911880000c000f15221440e0211440c9403500795800705044200c02d200d410210080c41136820f43c406060307596100300003200d1400741c008104507840541802510001c0000300a94011900d001c0c12202009014a5484052544200c0e03490300c80e00c008980d0380482c0c413002400141c01c68030826200e0043c0ea0005d080c40c940e00c0000b04200710307119100c130f42c2c800c1080711044d0044003100c3c00c0c0e0000d01c1e042031801d041202c200d40d030780303e280100010b45100d03108000f51552240c044070003414002d0028403803881d0903030503081c15501180070f240c0f03528071316110005160321400581e8440c0d60145c0d00303100d660b160088044ca458845040c00d440100b010040b0901088550005041c14a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 512100359 1250 512099109 512099123
    0x42909030304092c0601030f032a020102010c030e0a02090402030f01050c0a0206010609060801050904061b0908010e1b091803070b07030e0f10020c030408070f05010813081c0b0d 78
    0x400000004a4078001e0b40043ca10b85510f820035076a8413000000d602e4103590b4800ca440013402001d0800703440030104407108401d0300d002400b524102d0119903038424451403003a0003e015a0721506815022ba6819151140d03055000c565600058940220a540c1140c00503080d500b0440100030f1450035500200c904180c0704500085405009504000440c01028907182a00c4c18a06000005100700070611660384640c014002060510171a94007000c50040030380200510324400400180c40340100d031003080c015521b4421002c500c060f000c5644a01141e80c4180689610921f41c20880103000c040c0000c00d1803030703030014121303003004041008103181802100003540078500451300030155445480d50598a40005484007168640051800c044040d060009603c400300e91540358a903000d05c0c0d0200d1014858040d00040c203d07482c81c140d00c142d40c003c0e6180005551240c1c0006285003044800601d401000c1000400340c0050f549070840301d040e0f000c8081140d5030303044006043c503440c00c40150396075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 512101609 1250 512100359 512100371
    0x60d020901090b0304050642010306080f03031605040e1509090a120509032d06101512020f18100e0603010e0603030708030405031206010504290903030409 68
    0x10341c2c0048a0000906443c40400d155280540c0c4143e01c50314090a600704040302c0e00040c01d03049154030294101075400b00d60048403180c0c0301140c0c141164043e110305010924004000c1240d1502180d94540c0c60110001140b03940c03a2151090012003849514a041080500012603a0000000c0403805010030034580300b8032494800070002c6811300544a20343c123520580000000441c1c0784089211039103181401502c0f201074001090400036461026160400a0303801e1704200c1030702405000e0031454440c00c85401da90351045514808030f05004072044420800d40c80d5950074400d010445000c0c0441c8000341c08c09403444446e00301600203120000d41601c2054017560103042ca151030b105040c0c240d03d000c2d40141e030000c001c620584011b0003240740c0d0b6965400000c150343c0701041242d40da02c1c1d02c03e130203560328078040c1801ea440703070444410051410141008928198480c8050f1000c1d41d8250b90041c00302c0058141002c07018810baa400c1243c000244280c0605540a101a200900c032020000c070301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 512102859 1250 512101609 512101627
    0x261e0c0706140403020a030810170f0106050d05071815080a0b06010207050a1707080307080316080103150b04290420191814100c0312021602060d02 65
    0x80d50710521002500e800c0b458200300c0402d600003050810b180c2c040c1040d0b540342d202d032729003200c0e4204107411400d6540207008559034190b4001982c03150541141c0c00801049855004120000c00d6800c4003500c0c56100344030a001d2240f0015003010006802c440000d80240c0d104c11010342840325900c5115503810034122a414020714441c91a0702031401d01c080c00d40907003004006a090401402030074140d031000c90700760800c82401c200d000c000c0d0145a0440b901e170344213403500c5161580104c40c1040480444258101d0b824003805905041c2e80d4459490300200c081c100000008010900825902603102c4c020002c9041c0c800c2c46820002d03034a03070200100d4406020500c0191120440380449480101c40740b90104400e03902a100301c1a04007810f0820480d4411088400b101684406440e100307503a14001031103000110851030040c8240c8078445d14a423800c00c2030320495008600640440d014228082ca030408540c020b00c0b00e0001d40c114080b5204003034021441c1c0e41c0005124982903940080c00441c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 512104109 1250 512102859 512102861
    0x613050114010f150201060f0e061507020112090219090c020c0a1206022b0501170613170d1401050102060903041505090609030d0f0f261e0c0706 64
    0x2076500506030081180d450078002c01802e0610b4461002c980e040c0903400400d0710b10039040b40d00102203100030380c081541c44c5d01d1150340305442075401c14480c0301100402c607107a880c10000d440b60301b0b070140c6580301c400da506400c00001e001d0154040fa404100d03980368001404916540314041c21745400c00084403200d07034202918112507003070018401c9040500420401300b0941e010700140e0342c40702d80940c071040c0c4c15018405456603030614030040844240c0003000024180d02070b0741210204191180d0741a2446800d03916000c00351190710040c403484085030041000d0b50142980c60304121102171604000b070000d9012a448241c044034508045401080150f0341040501d401a5001e40550300e0580f80040442c19910000c1c0c60b13100380100420300c904156030701000c0c4d4400200140549200c1188a0f03c024410300354140b00328081410089240640c501c11000300042d0840000c0001c0c500300d03989070110b41c400c0000d00c0e8445580581d11030902c0b142c52041954003801c00045171a41700c8600d860118 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 512105359 1250 512104109 512104121
    0x204180506010617040f030311220b0307080f180a0b0402040e03090612100906083a032004080a030221030a0c020a080a20060606070b0907030506130501 67
    0xa04100c0e40244c2c401c0300c80c41000440d90015405803907001c00d0400791506401418800307007200f840d0500424040c1c10310302000040310020581495103ca101e03103808000e40640003d44031800000c000200191898103140b01554201d0001500c90506d0400240f03444d25116802c501201c3c3c200300384040c4411070405010712040c1968020246040004003408514140500c000c2c14806517040d50104020740c40b100c50502c05024803440501c4000c0e03e40b19220350f2040703401c5281c2d00d40c010252007030041d0450304510300c0e13030400d40c1003d03030389403076040300c400c82c0540390f02005000440c0744078000307904416100c40103000901c01040034119820f0b80d412302a080841405181c00d1040914810a604680c04011642d1000945400084075001c24800300d10f000a4580000e28506001443c03c0126401511880038042c0310600c0d005510902003845495100982e140d68024105101501c00103030145000e0307500c1880c0f00d08485100e41d0b6031719500c1c17901001f0340740c0313500c020310341151402030204c280600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 512106609 1250 512105359 512105369
    0x10b0a20120403051c0206060105070f0b040308181f02180904060605270a1e050702071e0b04050d150609020304061404051c0203130b03010504060e011208070c03020418050601 77
    0x154217060000a51210720080981d030400100040310000c1007d0851050141f64200c0801c581c9072603e480e002e808440d0a035100c0316401c015039254809000005000c00c1049007082402442c10214446040a03400820741c81c51030907407640307a0141e0f549400071400c1c800d600807a40840c0e8185000e0a020b40d140300700010681c00e0f10346c10081111265030a01103030b00a0000c100000d14048030403213281d502e010300d015050216041c030742031046c41070b400907041043d100458081c1c18444240c80006200d048a1300c107400d40e0074024842013000d450310b4102c58442e24080c40350100001280792000084a04075080101800d6000c8140814800030744a84905450490b034114103906054131100e6a0310f40c110001032100400c9251940c03082d01c05c4c4182c0390340c0d100040442005907281c2200303030b20702e0b0003d025142c002e07403a24800240449030424018100d500160142030220072a85500a4a9204007402e50704080d907140000010303100e82c03140403040940000344407107500c42032a02508001381a07000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 512107859 1250 512106609 512106643
    0x20f04030311160b09061c0b0a060207060c110102030c03040e01030c050f0d06050403020313030b041104090c060309170c030d240b180306100303080c03010b0a2012040305 75
    0x554000540283c405061300d8856414544079204400041e60070f01c10203013151001c50700400114101d07204d40c1c0182500c8082100d01e440800d0f02c52904907034500c128407685c07001828103a0708401141044600c5070590030184141d900d00b034100d4038442e280d84d000fa4070240d0320b03e085a0040062000400100003d08802c440b900030b0507032400700040440c1e81070303080503207550f9840011400309030081084078152100791a00701c0d03d4540c0c9090007800396500321401ea40700c00350005150050314017486000b81955100203003c40703260405004030f005065498044a001d903202c442c0040100d900805031200910140c0119030750082e603030182c025500c14954035440c075540c014000340440c4880001d541a150305061190b100c1603200c20b00350040c1c0089180c103170075000d117805001c007490a180c0080b068a00030780b64000561070710840940343d88824404c440e100f18040c001c1c6190a44038514851b500a4240c3c0e24010304001c268050341031800d4603210300780d040c4000038200300708481880804c541c2c4660500c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 512109109 1250 512107859 512107873
    0x1e0302030c0901180306051305010b0d020a150c0b0a1a030106030206040501050706020405040c0503160c020f010809011508100e160b1b0f060411100905130e01020f04030311 76
    0x99051800d002c1e2800d40341c144900103405030144050114201d00030f60308050144520304000c00c031003464400b20700d01038803694200301627038286080103928596140d501508002d151440d103080c0608030442c51141b0307010841101c64109c04503840b0b952950190601c41c400040d640304050040009a4400e140940280d04100d001c00c0541d442c001505c08513102030a0441c1c2c0c0741410f1601034002d10031508683ea020b071410154003416684840a50b11032090802d06502c4804404001d40707041d02c0e0400020750121000854941c294460800b803500180c0030700c008945000c9000800307a203c1119000100650320514607482ca0403918000c80e03070020403a00140010203482c9401c100303007100318040d0320507607080000d10116500c0121645050524040301740c0d03040d1003203c58019120b010995069500e0340a42c6410700f090b181c4a20241000142502d50740c01c010307c1c090510541c40591601e40c0b2030540e0306d07120790b000d10100380001e02c1c2046640110070340d0b6604500d00904140e21440b0480019807001d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 512110359 1250 512109109 512109121
    0x50705090a080a0308191104120209010608040c030f020f03010507022d0312040203160906050a050a06020c15190203131a0a0c0609080a030f05060f03030a0503040c0e071e030203 78
    0x42506030000706d813a40214031320b10544040301c09060f489200005c0e05200160000d0206403201c038040069100704c4503800140d030381e000c0c104d858100a0f580903007904412035040000503604020f4048442c80900381d0002900c1c2d4600107401c45030121602d002580000c1c08120708116032140448458011030108160030020014841d81e03030003499110607039852070002090035075404010502528221507130400f0050344400c0c03108058286813050502808030040c000c5030758640010f0100642e00d640d801840c402c4c11700c000308586128a0030301c0940000e401c00203950700c204280841100307100c49800075036440d40303a000021201245a03001c66041481c02407107024900d089001c90f49000e4062400c4841c00e020350078024024038600400403c200f03000100c8911041d0150080303250252000c40400441d0b8136a001c0c014251076803070429615400030060400028010b01c06035400501400000141c16142d1031030000196040d81d101001c110540b844a03030084460700c445409210031f14003075045040c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 512111609 1250 512110359 512110367
    0x1a1513060305191d061008010501060e060711210109020117070915090807180e010903080a020d11030411030601060e06040e07230d0e07051f0c06050705090a080a03 72
    0x24510b0f60110b03a8503581c007801144026105481c41c241481e00f5580c240c2008101c4a103062481c0c45088120f50130000005011401030115000c9030402810083c503041c2159100d0395001c000308410769000d0901503031141c0d4140c1500300021040100000041d060070f0724000900301c0da400c2014842d1000c200381c00c01069540c031840f030303000300c40094080500c0071400f44410ba820001030b8001c0c02540c407a00e10001403220b1010341d0403401c0d281842c8108684250800f54a080c2c90341c250f17020340890314500204024400560040510000c0010001144d072460f401100e2070780d109a800381d5a0014400c0d801c502d91400344211401400d440c1055640001c6500200d0505d0095205103a074128103040000c0704207005850021000400030f125010204c003180415189800490800800c02d24180400c2240c9000241c200d080d194001c0441d481c0c04001d10010715080d141030700d40820004810a01000102c0d5801280c1c0550303e1500d0f4a42c64200b41c1040c48804200c550220610b5808484484086500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 512112859 1250 512111609 512111641
    0x24050307030201110a2108090a1205030601090b0d02030f090303091b0402160f0309060906020c0409060920040507030501031e3e01030603151a1513060305 68
    0x420300301541c8165000e40410b081ca040031001900e1a44900e9844100040c80c0c80884400c01041e107e890150b1100701c00d0980d01c0140800c010243c403a1003883d80700c0140500007455010710145440034090f0748a078410340c0070b50400310070100301580200a002038010b049201c070f50302041c680025030462808017081e99031280808941c00c12101c850b030380241a038846030121518210440d40c442c000400714500080e401c1117040c02503000520080c0003107001c0c1d00c01c0084000321841d507030007003d1410101040100400200301c00700c580d50355a0b4008400502c100c210004020061a41042c001000d0300034030040e500300800f4503040500d000014070006202640010b40c800d00788000a000300c40903d0100010a4003031402c0101510307503100345800b4480a0510180c4002605c1028401c9061000546c00d0301c3c547d01009098003144100c0c000c140106034001e8001c03002204641000a6511010030803440c400c0200609405001460402d650864101000241003a24042045141c120f1840c429810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 512114109 1250 512112859 512112863
    0x10f0804060203060d0c080d030b06040f0302120321041412040e100f080c01020124120c05040213030209063a1506030201090f0f060509222405030703 66
    0x58080f0104585072130b2822094405644240140a22a161905280d54654180045d4000303030130002c20300c0c0b00c1d04100303064604a41c8a280e50903079603400d5508006c661091224442d120344400e0288031066403c403841480307089447d05c503201d0a030401e82844c058001040a60b500c2d180c1c404015010049190011a07040704c0b918a075070701d030355122040c17260552091648001d035070700824040402c004801050464060310260003c100800c4c12291652282101110344240c42034404030822140e08802c1c841c550451068013403000b041c1e1500005800c076000521b2422004055003401c0c021400e00381400350b0800002c580c0381200e190301d801807142c41480340d0481814200102040d0504007501c0e400703210000c1e40051164202c4101c2180312000300703420b20059000840100300003408256500c0d141c4150b641d82d402d01c802160411b00261501c0c0d02446913540c0048c0340007d40da24503415541c40123029401810b000c9041035913254512585004403801642000f80700c84200aa0354002030700b582221303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 512115359 1250 512114109 512114111
    0x3081b0415020a0c090221150f13090b04030908030313031206050901030609170f07080915030405010c020c03030f2713050703050a09020d171603051206010f080406 72
    0x4a10034080b400d02d07040e008000c004080190022980d415a40c004c0d180d001c0d0b010240c60b442500700c80807a02c26403001e036051482852a12070100803400c0034226401000000b07400c4ac140784001101440403203e103031900340c660021200070310080561080080004100c90700c01075045060404240c9120803800380d000b003e210300c5011116601c0403541001d8020440100154001c1d030b5a400c0290182c0007245c1c04592188500c1100d00da015a683c040d100f270355a1000c01e0a05044040c7ea4290361a8440302d04a64000c216960360b00c540000c00e8000c0d44142d104200100d40440c404002a141040403070301c0c640700f40c00900c0b821064002030010346224141412200708100b1600000c44021421040d10035080060780d0011150513043c0e4002078003c00701d130b5804211550341c100c1d03008116a110f580003544849440d8117400801c044021321446403c1400b54689080a003903080c10102c0121030040b004200301258400b4500c2c0c802001d50f62241003800c103c09a5001c6210081100c000180020122 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 512116609 1250 512115359 512115389
    0x20703022d0d0c17060a1b0c060b03030d090302010f0e010c0e0607060e0d021606090b041203140c0f211209030403023a051b0612100303081b04 63
    0x31000b80280e040041c083d203e0390200c07031140b03805007988500d800c41d455800d050504680065850081f0842100e0210b550384d5001e5001c0181e50300e001810075120550750504c002d01c00585040803034841c13020098820b0300001645100441131100343e483d92202c4c4095640752aa900c0d41e00c0d03030807e022020000003200d00c0d03a82d50308545481801490b412200240c02d01c0b03611040340759650000b83c0b89298407642559260340c1503896504440060b09400341141c4543c0a00040100420b1005107a81151190911403180f4180f18040d51a0b0341045c0c1d451a0941e111103001d01c81480144100300360894402101c848066501a81e0500da224100d80000b44120003c0098a1414107105413030143d035004007507840303200d180302e0600c044440b04288070303d04a800c0030500715210210f41c0072080c07141e8050090048544507000d01d0760904000028560810410045010051648083c492280c035450000d041e10310706500b4020100c2c3c10080c41000b1038046a62500720105080040e1800c4a051514440ca2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 512117859 1250 512116609 512116613
    0xc030301180e0616030e0f06010602070f0e07120f0e100b0f0402163512061f0302090a0e090114130804051905100809060601020102090607230d020703022d0d 69
    0xa042c25a443c40000e60242300008201a0f40c04240007044841a282030420326880710001c0080750025103c990200b44140c80e0034110f4102500900100003004000042d80c2400e200d02c14245582c5407584011320b91303a40741d51100c92500200c1c40b0b5034001c0c2603500714100344552188403a0516140300103000c41002d0010081d8080b410795401c0066030f44020124481d40306030003071640540229005240c600d45480001d080c0c0e003807103440c205082a214044001408000c03070190025401541c40c00d410900340c4802080c0001880031440c007880e18000002620f00c01550074400c038040c0a0303c00c00403028000508030110341200c003690280c50040310500341c0307d01d400300804c00560716944455048031840c03498480254000d40036910404064040c0c507a2607a46800480c200d200d00014181c1c05042440004046203151041103400031003c0c0303480c01d0300500190300c00d02d42800715801c0d400580c0405014000c40c1403400031f4120288107134007668502c40c1c440703001114401002082034010310a00d001c00e81 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 512119109 1250 512117859 512117863
    0x100315060b0f1b0304080109060b01141c1104062003090109140a0302090a05040506061203220f0b0c120310170a020a08070302010915020613080c030301180e0616030e 73
    0x144016920b0204c0f82d4682e56440490301134420100162201c501d0090081c0565010b41e40510304c4000b03520400386416110310f0440149448800c0302c00b2260b036610882c400103ca104000d1001c1e0080b5140c1503680d00300c1070304104940c802c400449102d5082440000b0b0b02d82d8210000c141507454102800300344010b07160100c2c10b1384000d60700281d401291541032002c401c940b41d0143d070056000f08107071101c40c0c2d00c101c00e00c090740c0c000e004000042d41c003c10403003525144140c80841304190b83e00c0c0f40300c1c0e100da0b5600018860139003500314120b4103000050f1500a41000c01c6411003030070107405214110b01e0008000800042c05200341e0114900c00400002c200d6014082c0d00c0441e60300401003201940c0b640a0b03c3d41d00c4a003400124085a20004042201d510402c004902a107841e0700070030311565100c070340c0564001260000c440404060104440a40f42803001c2e5000e040183d15148051440030600c034140c945407010709000350012414805140709562a03c070f003000c0703d800c000c01c0004000207464 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 512120359 1250 512119109 512119147
    0x6060111030d02121501090602100e010b030a050616031e1e05010b0316020606030613020a0b040b030f06040b0a051905030109080304050c03280804030803100315060b0f 74
    0x140ba6440013402d50001c002c0348030150700035603501c03048803068601ca0006556a001c03500400016038007140036024120034540241d01030a415200118040a44401013460001e42c41021601c0343c00420400c81015004030b8000c40b10103152800b030007a411006010180c1c240c3c501d80da4001e45031101c1104007801d4142400500c5072190740390400c419a592126a83c0c15001a1900016403080c4410340150324800281c00e4010318004010341459140d01c050645001700400040f602326181580000d10081c95402074002031040c2180d0b10341d60310b0710011101c1e4410001302501d100c0d0b45000540c4802c0c0d00c846031030b101034aa080d00c58221020001105c0d00b009078550340000d44c5503080a13200410420810055801684590b0494400d01214020551a40f030000315002941c40c1880c04002070046002c041c1104034001c24029280648075100c060303880e4411269200580c40c05081002044040060814400541e0808001c000d08000d0901014810510103010410380404c103801658101c1d2240d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 512121609 1250 512120359 512120377
    0x903030b030615011b08040905060301060e070206090114070c030311090613031109010b180103021605150a050709140f04060602100b0303030f0112060605040501120605090f0606011103 81
    0x20703000c41c505908451264a061021079001035179079034104000c11140ca40c0c9200c150f034005422070801e800d02100c04014000104482d6042d03484040c00105540008403003030158690b60302400311890410b482b1800c0d1548411289080550b00042010307030390b80a03220008080d418600460b8004000d541c550705402424101540104002220019980110542030440c0d1160902404102c88c500400401c0c40c402d00c55880c0c080002c2109003d43e00070b8000b05d030143c9005040044c20304a0150080310001d074050000c4806030700401c5401071042680d00000c2e0b20084450080c4168507002400916071400d5100790324051501c03440c980b503190780d1a100898003406c0a0002c2000540c3d6034402545c50858921b54034030076142c1002d0030201d040200440c1e21901c0384a6440c1920703482c0494503005e070004d0820030707618141d444030049401c0d036a81c0a5903000b4150101c1b0441a41c58500701401101c40c003410f403000940c0000d030300100142c000306001e03912800c242003250500a25010301c60451140402c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 512122859 1250 512121609 512121613
    0x10315051009060908030301061b0f170d1d19050c03010c02010212090a030f0f030b03011a0f040504020907140d061203030b04182a1d06090f010501030903030b03 71
    0x2480d01c40c40d03000d01e0740011210682d99070313050641c0d42e01c032540e1a0f101c01e00504000400003102803001c0b115900c40b0a004a04c60400420300e401c6c5600c400c0d509505142c00480710303c40005010b04049000c0c01160f03a50104115560241d4420422480ea0f81403010400c5c0c2078004441c1100302402014041181a184081d0090005944010009000b54072047e05040e0f045000804207186c84800101d0460243c3d041d240d81c0840380f0064401d40d00e00020354416420103464012140064401b07000e12446151000210342c01e1a1041041150f050300400c04c041c0207514280c2000003590300d460f101c0c3c0d0040c0150820410211420000842d2441020503150f1542e080420014000c000040c0c43c545183c0243d4003005003500200c100070545400e0313031440030b0803403035862104042403820204409140e04421003000880070504407a41c10304059002032035450510a0b4448001083c81030190f100404682c3c2d500145805d20000100b5001801182d04250303803001d0000406000e80d008404040300202 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 512124109 1250 512122859 512122879
    0xb09010311040f05090706022b120617070303020c040b032a1e0f0405151509040903050301051f0f081f0803091206010f051915090305010c0f0e01031505 67
    0x1711035036070910b81c8075140040c46400481c8854080380e01c0100100d9000030701d02141200d6140c01200d001c00119450914244d41d06000507810000100140b0000554005051002e1441c10007906000501c0402805241000d00949281c0e0b8041180e92900e1024038007440c00034a0311840116805040c0f08190f00010610000aa1004500360b0500d201000700c41c8005100b1003001031005459055404c0c1c80307260400c4c118070143c0e150181c4104c0c0341c4e180304000350b414680d062000600790740142200b43c0c0841c00010050107181400311444100c003841c541420000c1d0050b01d4020403d8124040c0c0108103e40380c0c0c0420008014078281c164921494008040501e841e020196225413241c0c540f82c0c8106e0307401e02c2c80941c080700458003604898198050001c12807402d014400e404200307130380c1c5103030300f940384080822010326a007070f060200d00e0950f4403035020f43e040d440e2060840fa02c0701401d070140410b140f03441c0f0200d40e100f003111090500070f1030702280d1022000d80800441d903003500700302d5016000036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 512125359 1250 512124109 512124121
    0x303050c0a081c0612080702122506080105030111120c090402040902090f0d0210110a0804090e12090904080c010b100201020a09050901030f030521010f1401030b09010311040f05 78
    0x1da02c00380c038121050f080044d15a03800c42074610060071980103040031001d00c000d130050b180c2042030340d10750140c040943d0010201e222a80c4c85222644040c1c100d8140785d013109100031507100c1000360141c6000c0d0001c10946034054440c2500340a904a0703000c070001c00c5000990008881d200b9551650f20107807040d0340700da4449071002c019402102d0780030b01882004940c00054506a401215030310f8011b4041448170500c04022900441c02190740c11742481210140c90009200304000d20041850040004481005007509030515020340051581548207014850095580c03042c0d181c3c100358030a200703035a501080492903000d8401051026440491580c0128181d0f070190000e001c908080c1d5246045036484408111201d0000e0102504100014088400081c040c100500c50642caa00030401b035020b40c0702c05d44040f0031003600b050030880407044d0100890a2a052000c012110909003031001003e00d04c0419144541440060509008442c0403115a1111b40c0082024850000c0c00e11080c6045 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 512126609 1250 512125359 512125387
    0x1803040311040b0105210901020c0a0b090609030a0f081005031009030806030115050409080705060709183b010f02071101051c1a06160501050603060903040303050c0a08 74
    0x5071582030700890800c80c84000700d41c800c0b011214580700c00124014401480f92140d82150401030031081c079903500f00001c07000e041c000c0104041403403080c0c2c03c0c952a442e01d540041e0400c01c01806070001c5a206220500c9016000781124040e60700d1444e01c1400c45c0d40b41e400c0c1001074422036010301d07010f002e0302c49100c80e1304455400101c1d41d05d00a8131040c20a4481070181030803034030041042010421018414040f516040d00101e0a40e4056110315082640d03a8992700c2c24110207551541c04582d030b00c0350030808540b80c4c1c05100e140c4044242d04010030f00000e00441d50b4100fa0118041d0340c015a0081451420610f004602041d131344503001700b00c0c44403400d409200a600112040e1080170081d4005003141d0321800440e2410001056807101d2603007040d403004060121911041040011900391ba2243c0d203d01011303054021804503100281d60300c40c00c0940c21608050000c60294000c10200003959030000110307000c40b45d00d4a00150382d44c62030083c0d14206030543c0c0000f450748100050201d000148 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 512127859 1250 512126609 512126633
    0x506070e1818010b010f0c021c0c0b0a030e030a080c091302040b0901090807052805030a060218040c081f05030109110a0803030618070309120201020307140412080318030403 76
    0x1981000304080f034000340040d40c91400d4950ba840c002800303c07e0320401402c007039030845000740384514038480b1694640d40c1c01c00101d407103800c9200300d28008035010842035072500034042c207400c809003d145807040c021801028518020700c4068141000030b070801c901d840d046060700b0041c0001208640369920b4003800c0105502a82409000030032110340810765600c04545a070480e20000c104807402d40300800d288100e80d1085880c07000c0001310100005e01601d0510003020040c3c85410010b82d9004111080e01c004204c07100c805005a21b0101020201608941800c0c0c1116502541c08400ca600a1040000c0c40e15900a29055401c02d0703500e6040001154803450226812901d454084e600c0386011540c03408115a12680503014201e680c0703a4515900c03070503030402d04a14000c14403140d99140c814411044400610060394000204810a58800d00200b40e605880c06410301d03151800c8540c4030807007220b0310b0240c01c090001000c55140c10301c0080100b05000d4903002c0e252503503a24200f07012031642c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 512129109 1250 512127859 512127901
    0x106030605190806180a0c09050f010b090a060302340201031103091902011202071a01060512180f0d020102040305070f0605070f2d060b010305040506070e18 69
    0x2c0240350316980442c0840352401070ba42528000c041564800720080340741c40103c03c8514541c001c6054082c081103800020030041e00c0910404a40760500041070000810140d100d03410620301801405001da41c3c034554001100c44614000d40c5441549070f075503510f18840000000c443c07180c80501d40c0f0010946085031000c0c3e0007603c08010a02400043c111140700172140856590001140d03401408060710100c0e50050041c5800f40400000900c080c0c2240e00c00070054034035407030480031006950144003045025003010310f8034500785010400c1402a10102030180d201e030100742c102c40d100c0c1c110100300e0907030441140340c1100c481c02084500a4000d601a000941d0304d401100c41c04150350300e000500000711001503588500c1d240b502d40302d40c01844200407081355041580310705a5070120300c0603c1c40480040e0144084400310031480c281d02100c01d80403100d0b043c1070800d0200070100e6004a032155100c591030520103480c9011000003084000b10b07080c0000e0402c031020601845007040c40c40c4c070038201 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 512130359 1250 512129109 512129119
    0x406051002100c03020301120f03210905100c020309060d02070c03380621030309010b0103050a0b0604031211060c120702161403010b120a0302060a060b2704050106030605 75
    0x2080c83c2404030203a200074003134007598400c141076690020f80f84803421160f44c0c0c0603280c403040c6600d0324010007140c8034112402e0b08005403920402e80500c80b0621200c03020100641007048a100b0b02180039451380102c91805108020200e80141d00c1c45070f940455280a9000750489003030340d242c0c60656201d0010382100b1120060450050800c482d54028152070001e0200c55004140c0d640707002c100098850464000100e1403502c1c0811340654200060360103001010004105812600001412210b00410710f0300201d0400407000b84540b00e003001c944c01d03207030403080e00b02c00c0c100c045c10161002c0d48a80100c01d031610800f170420400c50310b01006442400b120f03100e0420640c48900d001c84c0c1e03503001030340c10b02417440817920b0401c84248001c4000d2000c800140c004200401c0030340004150322a0a030300c400858100800071400c055062202d41c0c0d00c24109401040740f1400c001c1c5c8981c05010714602800520000d084060080c111054480c48490300200240702540e112440140984040c1c42120700070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 512131609 1250 512130359 512130371
    0x8010612020703091202010e1806030d090b070f0206071704050a0b0a12020903071206020301080606010f0509010305100314010b030706030c021c1803050303090d05070201080f06040605100210 84
    0xd180e40212601140c0554070503480c00d040c01c2155500c1081c034001241401640d8112029540381d070442d051582c010000117403007a103086018182040929802007003041a0048144220400d507000e5840b8250481e002d190580303c9880811440d11481001509268402c00c0d060014442d034070041c011b80708140c440194466440c020400c20703000d40c154140c00710708404002cac6540d25040d4043d1411100007412541c0c8a55180e002075080d05080743c003521010380000042c05641010851300c0d030804d500f8a0f2414940030362041c01402e0303010700c807400344c100750715140400c0d224150040c442000d990808407105000301c2d0096607a009044501d03005000e401042d00c0010500c1c041c0c85068040e00098010740003450312200e03428210799000300ca0340280f102154130180e4020003080514080e500c2480150b0b600d041c2803282c2d03840c1068040c0718004000d802c010390720040c1d030300c10302050700030301000300e440c0c429120b0400003006070100c0d030011600861902c8403c4251540045d0310580801251420002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 512132859 1250 512131609 512131637
    0x2070b0c09040c03020702030a0201110102090a0303031410120311011407230f040e0414010c050a021b060a0f0905030123060d02030c151218060f0f151f080106 70
    0x1a4090f202000e541900050003200155000303009040033480180e00041c40c02145000042c0c1d0794203250004c0d0002070b9208868440c02201c1d101e07103900302c3c00305030388900c4062401e0030036040004000b60003003c0200340c5240c00100c0c1401d4001104501d0120120101c40c0350030319000740031002070360700c010400aa44884884004216044456103200d10020500d458106105902000e501800852708104092084540d0417030a100e503410155180c0e989070395501d48102e0007450100c9180100301c4c0320714030440f04403d90380e03000100c071407104550400b0700c0c04444010040d18441341c154448d940650810b101040404200074401c155404100c803200038548450040c005040f88403d002034055124161411803890a0f0040e402c2e41e0070480505031038850110410800c01c03c050342c600103488907103107140071480b805208565000c00518000c036000c1c0340c0841110503a4502804010b000c071480c207140c4078240c50702600d10804180024034010f030790189000040464034244200e0000903012103241407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 512134109 1250 512132859 512132861
    0xc143714090703050606040501110a0b011e0e01080627160609080102041802030c04171e03070506040209180312061009060804113d020d020a0b0403020102070b0c09040c03 75
    0x8055130021301b40b031707003414140401907a1982c0003040c9a240707031180c550f4103000140c95140440c0030300314004d04912107805901c001c401c10031070b80d0481000600c20f14014840c40000240d8070340d1049501810701d000b007007440031403140c8400b42c0d0204150b50123280300e942200807043c01620f04890032940c54040c0030b583d480c250b600b00d000b2402a146410702440c041c201803040e5401450b04071050b034000a24056a403003204030710b403031031986910894200b01103a00c0500c29000c4000c801d5500e03480914900f0400742d448985a000061000f44943d00d00c2002c5000c411000000d024015444011641d40c0c000e01410303220f0b040b0044480521508005007513075280c0c0d200d80d2201c402c40d5140e895000007a16141e41c0d1164413030101c00f1003604284101030b00c500c40d49580c909000b4202000e28412030000d2840c07528441c0c83c81101e602d009551000c007038141030300e03070000e804507440e80c1003d0f40e550b03203440318601207019104044e0040c0c10b0700080e40170301c40fa00c21000020180403400720b074108421030041009070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 512135359 1250 512134109 512134111
    0x150402010816090b0304050309060403050a020a05100509042d020415020c1503060d0807060b040c0e0d15020d140f01050103090305040603090614010803070c14371409070305 76
    0x640442010880b0b540d030701380910b42180c403d1043d40d0421241001048060300a50703c15115644081c600c0c200b5818015141c601904040d1510301c6d03d42400300000d801c510414100602803940c40700211500020612204111100c2c41c00c41401e21105a0311400603400a0007009034424075000c0c908030711070001034001611100500031700200100b8100c4d00706c040d08018000d5800411010301100000c80410041072180d1081303c0000e05950340c04240000c42d041d181c40d981c00d100303030340c0702410186da01d1141c118072103a44070210418800220045030080d01818088008241c00e000603040c110101c106010301c42c914901000d0301981e0f8600044013911400d450107004504200001e02c01c8074805e8100481450003140c01040042c074008044d07180c941300b41d1285049030001708203c0100031041c140c000081090862400070703d0b031100009000c04000319080b5004820300b80003603d20321005050030009411811841d101c260742c41070003050000311181154416004600041c402e10700902c01c079 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 512136609 1250 512135359 512135401
    0x3040603140f0609061c020d0f03170408160f02060304240209010906030b010c05060907050a17060f0612031303020909010c210e070f0501020705010c0f0803060d02031504020108 78
    0x1382040d61902018000c8030000c004001000d41c6801051381c1c050307200d01d041c0855141c070400342c001c8400618103000340211b80d042048881c8142110030721000c1150300040c2d81d403144c4600d20361003003072000340b03060316186201c05002504041c0c04010001031005908100e0310a19000f0030f10070701012a00000b2040340324201e081d5005c240310401c00e12416100350b21424400106041c03440c040482500c1d001c1c54280b04803510081644909800c1c403040c200504903400402400040a82d584200745034030391940d00081120844a0b107620010380e4541e02d0f01c0110396540f141b601580d80c0e4014482020401200c0c07404103a0040c04000040b41203800d0500c83c2c840d62004640d5070840003200c0f01068010b1628102600c015580c0798501c40c18900000d021b810300801703011907000031381c51400001a040054550001c0c0c18080b544a404001c180c030040e840820543c0044c0e8103a50750340710000038040310300a92000e905442601070031030360179001000f0680910700036203580300c403a600c65800143c856107152704 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 512137859 1250 512136609 512136619
    0x2d19080c0403060f020f0c010b120a030c08031b0a0302030a060e0c030604050411280e040302100207050307120804110a06140309010605040e070e0c031605180303040603140f06 77
    0x80001c103c50398080c4101011440c0e0143c40e00806501c20885034000001051159649a0304060345103440000030803020600340207048407889644000e082c1c10007000c1c018112580000020b0ac0f40302840c0d0442c00514202c482c22a02e034803000e60002c00a410071100309401c10325240000c200411208291362041070702c610a1440c5580340c80c10b10025040c0038104070b4440702c0b05405074446540c1c541070760080c5540e00c404c0e82c0b90b0f4403c40311050300c1c03003907142d00c1207141c22001e00500c0082a404591010750110b04c000160f40e034803040c58442d203544624900030340088219600c590046602c1038001d4040c500400500c81c05012540401554140e00d10a610120341c3c4500344081c90b800703a03070155030701002c40000014100e0703a80000c1016102715003200205500824401d00004200c642c8068000d15170449160131868038000305110b418100d007050b0148500032900c1d210506420403400c00100c2d000e402d0303a031526920340300500070b030100740f01c0e6480741388175400055004011006003500c01d09000340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 512139109 1250 512137859 512137867
    0xb040e010f0f140d1a0a2f030402010813120e030607031104140d0609080712020304150e03011e0b010e0102120406140c0a0b060117060102070306022d19080c 69
    0x41000740c10b56003d030080f85c2c0f5041003c0303c02140b40c0c002c9407182c8120140200850350a000000d945400103501420850b0302c038400e46d06804242805054a500a50a003400101c0762540c540152070032100e400000c00d042c5106505184943d845610000010b83c1074081f40e61f1034031515010f5003030b91180024200340740020301c8200002c040c2112160a40c3d200581049045209902c0b8001544d03400c51054400f0100010343d082000700da5140100c3c80c141600c0034608007401d200080d000300340c000d0318071020040180002c0003980e03801c2d4020071031b100080c80d01130b441564940d00711019012402c021030104e40700a14003400c550011491b10315145680140c1c0d4503050414000342c41366201013146554240c0188011141e41e8010001089444c2c01000d0040c103a14141000411a11480101000503a0b82005000d0180d80001d5003e0560b54003140150304c50102c04000200e81c0a00649003807001e081b2442c0d8803003001020000c003101c403407130b84043d03036030001000c0c0560f010081519019210b004c200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 512140359 1250 512139109 512139149
    0xf030c01090326041e081332010309060b1e031204030b01050603070504270b100206040b0903090307170105010e061f090914060f090c1b070b040e010f0f 67
    0x800c00c3c0102d541c00c030419a81119050721400703641c1e00000c02e00c124203000168184a24050881203802380c4148a01040b024036034004401000302d423000c941414103850303923019010007071903400c85c05d0080300141c1160004c0c1411805035202e29071440d91540280a1425094001d0714084200e5041c0c07a001400b00c4400c0c0d1811050144035803001b401681005824480451082c5103a140180200c5603596001d1008898800c07a0f012503080d144607074824040030100c640b80c140c011a50692064001a80041c240c1e24400c1c51170542c0309201c0407580c18050b0030404143c80b401c40503108508202080200034170382c2c0380c0c51070000700700094510980c403c1031042030f00c420560740c10800c1d00785500c51401000041d9142891410780d4030b20710140301d010f25007100b00704044c10401d440100b44101203858050a0414071300c003d41d188515450f414002c000b60342261028401008900b004000b072002881c0e5440e41d941c00c0385801038081c028440903079810000029100c180f5500c030016910780e0342c20780304204034003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 512141609 1250 512140359 512140373
    0x506100c05030405060c1609090f020904030306180e150106140706061a0d0c0c0c210b07051b0c0f0111100515030f010603080702040e0f030c0109032604 67
    0x32000c680300c1c030007004007050f6a01c0d484c01800d200e184c101c1c014100c508920265240300d0445e0b401000e03040f854140d240001c40d100301d01c4803441940590300c0b10060f03269403d04030007401040d00a0510f00007488040e817441003d81c4c1c007032a0b184954905640d508802c40d810b507841100284104000104000e5030600c94000440040480510414001605683e40d0000c680c3c0c1301594484100645004074002d548685107010700c0e440c500c49482c1c04020024141c3d00c2d00f52020860260751940a045401911703843ca071810481da03001d80080440c0078520b01190000d1003984030801d40110f0100c0b04800c803489a000090034001c00700c00a06820a00c8035100044035140e407440141e580b540700741056800c08041e244205805402c001d500110700f01c0c1c280303040c146400c10171940d100c00c5a00d000300800100c1d50220a59141c258102c0c1c000ca0344242c28400c07103140604a007040740050200042e6500c2d0004150f00514850344240c0b95013020003805800c048526007406d884103001064400010005003007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 512142859 1250 512141609 512141627
    0x1b080403030302210406090c06020f07171e0703020f060f0307053f07021b1c02100306080c06123114010b0303040b04030b0702030f18100201050610 65
    0x12040b03000100c440c1113a5003600090503107081d42c26645d1440c190301480b201d48150000b804260000380764480c01c4040c0c40e555a41d40f846030640700382d03201041c03100c0c5103424043d95502e03128040c03041c6c0c025446161790549030035091008911070082030390314025a007007500540d558a44410304803401d61351614000c0e10306500064001d20702d822495941c1c003038003452205920f20328000d10700c40f0600032001d01d02c5000d240400b50014042d07512101403051000720707420141403486800c3d58140205c0c0d8403001c505c0245465400c0007544072000407070b07030030380350340e05d644510104c03107a030021203c0404160051209910901070501d900e100702000207100c070341c030307050309402c0076401202c4411441030710300403000c42d01c8880780040307817200c41004038a8401a003d02403035030824001c9020314034044c6006a241010703c594400140214505030004503014002e10940d01e0040c040c40009030b5500d0980c140e0350100d00d002441038860b244440c042e802103481482464800c0b100a05800d00c1c6201595090341c809038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 512144109 1250 512142859 512142877
    0xa12061a19090905041212020301050d0809060c0102041503180812040c1a22051c0303020c060109020703110c0105180f061809010e091f02130f05011b080403030302 72
    0x701c40c0c100143e26000383c401c40f403255000e041c80d8a0040492200200b0b0544403984903c5554018001801559101005540e03102c0d41300c0000c9680d1003001022690303502642c4260007440d4804031300050790341e2803400d9181414106a800700030340094451703a80c85000a42401034821041800075a60506500c603e0b0382e00300740907080c070303000b9181d58500301e03000b84180c0c0107101d43c00c1802140e80107000140f03142d20101031541504d01000113040101080166820741141b00d80a4405200707903003410302960488276048403010544505685480c28480a54801d074403c0303000450155040c6189200461109101601690313100c1c90a00f00304030110b801c0785040b203071070740c0031038481320155880c2e480900030030300207011007188668202d8070f1041040c001c0d0141e000da02e40c0142e08082011542001c152507410100000c95490300080d0108094020301880c01211110740071840b000c903804001c10019400c40e0002d80c2d6689074922055407a03516007414120007060340c5018042800024040d40107441244 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 512145359 1250 512144109 512144117
    0x3020a061d040e010e0628050408092b030203030f180607050c0c03070306060f0b0304050c060d1407120c0302090d0204020304111c031b1a07050f0a12061a19 69
    0x30017145002400c201007a0380600f00c1003000403034410341e41c1f16099010b0203108024010000d130315194990403074501c502c400c030300c1c400d0750340381c42e200706552003e5050366280504040700c80d81104d283c540030350f490b80140c80040400c0d591200188400550418030004506220054410707511041416101a004401c4807034079030203420803411154404129640c010360294801080103031a040f620f910703440b200d8015a03080f50b0100100070119100190070303440004147c03841e83d0b5600508803440010a10030250f0040710300c0380400d000b00f099000142e0300c1e10a442c079804000580303e560301503040348540d51101c3e400600e01940c402c058581755001d9680f260160001790210a59040080c40e2a100c5100b1003000c881d490080c3c0d002c4c581d11080314420819803180e51100c1c40b54a0700d49a80501c0d04545109000505200081809214009452401c0110046144c5401038900054010900d0840044250b4034014002901d15103012803828910754501d04246000150201610401d9201c0041805c0c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 512146609 1250 512145359 512145371
    0xf02091602210d02160c05030102040b1c2c16050f040911030f16080a02091f051e0f090c030f071b08030a0c09030c05040e010b1903020a061d040e01 65
    0x9507650b0000304400b4254510175000c0300014500080e01003030a0308980c2c002c6c2c1c0705200130700110b1803081c11203220000e511711142d41e1980c503081690141503030700100503841c984500c518155000380d00390300042002c203506076011310509030311208110b4000e2284541c0070311300691400b05400c1c117034400302c002d901030103005031010400c0d004640350504a070444480ca50040503000d10101c1940f0b181d40c0a89a0b52000e00307000c00190300001c1041d0300182c2600406a908180114051208902030f4010040a045440700048450784480c228490b901554021002c58050a00519004264520440346800507034116110020706180c9a070000304640d085c030038000040e0480e0113000d41083c1840d446828120358a00e0f02c0c032050004e4418281a00c0244054400c040c00015004640781069aa0685000030340c28236501043d13015028900c0e042d504048000f550344481a08180030f02c094a0094428000c042d0b40d52200300c40e51060240708030b0004c01103155140c0180327000e400c200303003070f000b904008920 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 512147859 1250 512146609 512146627
    0x1101060f060c050607031e1805121e030103120c0203150a020d0606050a02210d11071a0c07020f01140c01060504270611040f030f0209160221 62
    0xc4510341161022480a05881d01000820000c49901010710318081c48441e5070140d080c041c003c0c5a076070b403001c610303110400c418001d100255091506a0004110f5094040c812116001607201412540c0751704850450100c019000404580c100ca44c403191000005021160845425100c500704991501415540381c841d902ca18a01501a60400000590764200c0325010b000f200c4199200c1e10030f010081c80107203103698012800c8400103180740164013401d1035401040c1d90a01c105450980c0c0b03a450b08951700710b04414080070707000b001c1c811080c080c100d0104803860781c40c00408817650085580b007003001d10014100032006001004041c1080a08120f0b01c0139400495000210440c29980d9200320400081c50180104028010801a00c120f25040d444091042c1103048501401c542e444005e0103c001c4918000c4030000d001c220544d00c0c80540343c1c909480100c8051a00780e1045080d000810340903043c00000c15681c0c0c10325001000301928060703180450400c840b0221003c28018007940340 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 512149109 1250 512147859 512147879
    0x2011a13090f1a0a0903050714010204080d1e03051b0f041d0901200a0806060d06030b0106020607080c0712030f0f0e071a090607060603150605040f0902090106110106 73
    0x2c0000e11800b103214110751041c941c40103401c0018448040c2e44c0c200040c103030100703421404907603000d03803c80140b2440d900c100040302d003e84603e170701c518094400d0441c030540140e07022103008c0300e4600000007461400050031048003a100300782c8001c02450100d4150042c5140004010050800c1540c1d40350300700341d650507490014100f1040640030010003841000000c0c0c0c001e100d0401084840603580c1555600b202c403911403800340f0401002800110004261190350710b07410340c2c0c41070f8440c0f0024492540c0301d207804034000c5000c0c480e000141c45500081141a0f00401c0b50301d01c201e00c0e00c00410308250582c0c172849a91580c01300c005043c0340d0366604d1040700140c03a00071030346864915000440c585007419800c1385820403942c4001c241c106e41600d94142d6143c060201c0d4101442118507030f840d43c1003424040018056030344001c0003000314082021072943d86812801c12074904841c00c1040c01c2d144d180d02d03000da501c1c62400a501039891801880340c40d0003101402005072241000042064546107400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 512150359 1250 512149109 512149133
    0xc0a060305040203010c03270317181e0307020609180108071403030c1504150204060201050a060503010b010903030f030b13020403021009030b04030503191503021002011a1309 77
    0x800203885038100000c0d4102409402c49440203483c040103100d1605c0d0b90000241e01207800d409450310121211005d052141c0d80400c1c2900c13400c501200faa04040c4400508582080b0412046014040c440801002c44e2000e040e40002e0305009946054103076401c2242d140d0088c0e03165503000300108000400e0f0038000302042e018120b1000105051800d203054074603450b20102d0240c1c8254420444c82c0c600e20400f1503d0421562113003403512071911585401021480081c520341204d5102250029000d0740c150007075402480d1007842003000d162110107260a80d010681501e01040002004000107480b403035100659128510300062841d83c1e000000700049074007032408840c2030700804d091003076240c429441403031040c0500b0160f2946295944058004200800180901002000246170a04915402d18040100740410450b06146403100e40400c40c0c94001a40200700c03800400480361700510035000f888005400c170b2900c0300303004e01c20004103c00018102d8485512000e11100041c0007000c06 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 512151609 1250 512150359 512150369
    0x7090801020d15050a030c0504020307030b09070c0b010e0403021b030c190911040f0306021809010611070611030d0b0609091e221b030219050102160b0a110c0a 70
    0xc20364220304034220b80e4449031134000034840c162502e0108002010104028101c543c12340740580c895440d1001540100f400428564001418404210764142e12001c10100c041c4142406545649c9030f590f1040d8108040f10000e015912420101c0354110140300d000301005801821208118140300c007295280c1c0e48800f402e1103040407400e007808856803034001c1040da16802ca002e45e003002d01d8000b00403a00e03021840050030241c2c0c00510b046820301c4284038103c0e01c64001c1e1124420b56960000102031101c200c2050707a140c0150340c03010074014480d11540c02c1c0003511800840c10901a200d5a400410031025290b0f805041002f10020513211034000d14411207070005070152484c0307100040b10310001c0c01041030390b40c44020b0b100e06111030380c000340542d682d46e002039030744a01600c0d440300d8100002d41500042e500140004803407213005220b448030001c2e55004c3e800d4400050325550039600d440b5460003510100b507028404036a5031340c41005404140050002202c00703820684000c03c07070300403590f000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 512152859 1250 512151609 512151611
    0x12070f11131e050c04030212010609021207110109231603050f3a051b010e010b1903080a09090203152106010b03130605010806060f121507090801020d 66
    0x201d00803200c0c1c4640079003603900c4070180503c5545425006039160340f1071808000c3c841c101c055510094040254002c902400030724008554500941580d6550404100c81c0140010409442440c000106001d03100c14690b02000b0900b40300028118801159448c000744491842401d02c0e104441c1207030000c0c080118003a00281001400360582d10381002164441c0c04901c03a21041d0000e40642981e04041d0004000c3d100710703803045552181110b0324441c089400e402d50a8000d00960a15019801071071018550340c004c20120283d2018400b800620500b2090032418000e070404c007213113150009012000c01c03850a12070440e1030790010030403a00150b9007008000306018680300c40c2e05020352a041d445100800d00e101e00f105100043e40e540030705000d100803010700440421070150b92a10a140e0450b400042070043d036854032a03d41d40d814040b5901782c0700e009194018000e90910f03481e08108030701e4940c05014004025200003200b01c4010741200200b0848444c00110481c2c284040c100074007405c1c0c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 512154109 1250 512152859 512152871
    0x3030c0406081006080103060b061902070f0504090c0512010209090a200403050309010f020304120305070b150306151914010305010e0613091106070b011712070f1113 73
    0x11004102c03140c02014181140c00d5800c0a01101c0d410403070310750442e50f1041001c149400d091020510a00580b104441c0c40c032510400c01441c0c80d00810b00406483e56200b245850315515410070003a252050310241012180d00414803850030030000c6424800507450015203409407280110b10f62640807582105050f54030801040c154a03038000000018010865850a10b41103888058991141c002c1140c18460004a180f8483d4002c0c011341c0e00400c0c1140c08040b500d00603090242166010250403207205600380b000402c0c9401c80d0301040c035560b60213001003110395a009088d200c070120042d034080d030100005466110038000d400c1548003820f0003a000c0c0d40200c00d100c0000d015550181c0000d000441410208002c94550700a1418000600400400c0302c180a05010141e0a1b40002058005c04005020418411031319001030484811413001e0304035080183c1881e840351001180020841c00c10041c10011444494500c510380e8002d4141c9161841d100d40081c00003c8840c00c090710b0552205 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 512155359 1250 512154109 512154119
    0x1a010b0c0105090111040e060a0503060c090102010b0414131401050c0405010815100f0903050105131a060303040512241603090b071107320103181205070503030c04 72
    0x2c0261500421154000e200d1203204e0311614a141c0294010074000b25803120000f1b48595615280e44000c1c4405000d850150030262001096941b04440c01809582082d407565410304040c4140032a02c11b04243c10300c065213900c051640a808506801d584030900341404c1003054500703208880c0264004810642c2d958036000000d0800c010081c1100da80d0396117048004210303110002c2e030b51980c091a203080859502842c1e0107407407400d92508041c090750301e0305003048618a1100f000d10440303801002d1690582a03c00503607282480100c5001c3e8254100748010042403c012409852200c406020389070f035548001e000035040c94110000060070480e00c8288030742d06103001e1503450100707460b1405012016090725003801d03138000074000c101086094000055060414450080a044914a02030104005c200b21038420410071061110590500341d5182180d80617216020082c0200e00c01c101401805072a1031055540440180040c030108012030030015070144011440303000d000e2402510340c0d0500c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 512156609 1250 512155359 512155361
    0xf0c0c080a060f1407051b01060e04050f070812031e040c0906050415210b071e09080a1104060b0f0c06010e1b07030905060f120a02090d020108041a010b0c01 69
    0x424140f04280c0741282c101480e4000300ca4075544441c1d10b0908603580c00040b60140003a00740d0f0600c0903442d52070001c0101c0c80c0403c1c01ea4190196000c3c404443c50035180030f0905032110014400d14000d40e00c444007456112240030065030344814049006480514051030501c0418004ca800b15076406401d041400000080e109000240005440070045901e0b940203004882c4402d0285500b0740d40c40030160003454181405492449607c6006070b100c41c148400054502512800707802024541c0d007030b0b80d000c024403e0030007008a44541000f0107031f9500c503480d0000514400319900d40c00540750704000c80c43d182e042000305a05688404842e540381c6400c0101030806406170807a01b2020f41440a005048001c4000e5440840c140d0030010b60700e41c15480c1c1507c40716003d038080b0ba00008081200c0c0b40074020b0300081c4c0300c0c05540d02d0789021203948071507528007244100342d45036074040d11030300c101400f55110302e00c62075106200e001d40200d100040b070b92040c0044000d0f0300040c94400d001800d503c0205003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 512157859 1250 512156609 512156621
    0xb07030b030d0e0a03062c0a061a010f180b03090a03120b0a030311010603060c05070b09010e100207060b0a0f2c010312050918090c0d080a0f0c0c080a06 67
    0x1d00c3c908100100e40c41d00c0003031280d5601e07100c09000c85807940322100901280703503e2000c0741c052000740400d01240d00c0c4019911000b08070015182070f4905400701c00c00042c0c0200c9014a030304169240f1400c5074443c107041d60704200144c500d40031400030140220b02044a84011801400c02c0b100034487c901280c40c0040a038030074000401c2c40c0d03030f0401c207050a298581001800c107590381400c02a881c003901a030594010500e950001d0310260502c01003112503a0000018441180110305880059482100d41401c0c0c90764132080e007880c1d620103208610140e01950142600b0352140501040c8100710400042c00044550480a100008010100724601102d4011050001c3c00101c204031041004074815010b04148005800443c081c1442c1e080c0b0348c400c0e02150b09040000304048190601d080c115000b01104849000c450b01c01c60345001144c4c0340c0700070a401c1080d4000c11980c40c0c004280f508964818903047c1c0d50040c005040d0800c4005881c1c0600d100290042d40001c1c03106a4a5060000503118 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 512159109 1250 512157859 512157883
    0x90702010b2419021002071b05040203040b06060d0902120607111506040911210c0103060302060f0903011e0903090501050301030809040b0f0a0806090c091905130b07030b03 76
    0x22081c0c820b003601000350300742c0c2c0c0300c00c03110010654280b0400400380d00b0f0171004c120110b0b1891000419808005003c2d1f0b101482c007040b0402d88084030f4451040c00100d10050b42d019140d0701d68440007604a203454030003800b01c48000700740810303029072a41c0401c9035055080f0090409401039010008940c3c0c0c05882203015402c0d503802040b00c80382005608191000207481d25000d26261100101803081200e10b81030081406003001500807084c900c19495403030f102000c05414001c500e41c1044540c4240922010f9a030000c2405282c441442d0003100725901c6103c07402d800d552245427810007550b07421048401003121100c040707925541d80c540241580250b41240b41888010b200620201d1f00f8041564051981664005084002540020040880580003e41c41542c0b44008181c20101060681c0103100c5402110000e40280081210a1008a6820050040840316007402d11803541040342c0000551189102c00b8075540c455a0070850b0480c0c169021a40b0742108642d9400c0400c81d941c1c81103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 512160359 1250 512159109 512159149
    0x3070608040b220f05030f1204021302130e09071502062203080105300307030306081b13020415110d080106080c0f13031a07090b07030507030e090702010b 68
    0x200600d40001c0301010040b0004c0c200304d51215030302080203010000c4500b00402c1100e095196011000c41403107210b02198100e0050b06995010031840046000759407a0041072800c041c981410b000207580da20301c2c000c040b1100c0d0b1040c9800011564001400b031101c9070241c0d80a03012a20700303c910035038820b0700503000c4601c03e0401240c100100750b02101c0d19040d550b04551070310b0070206103440d12440c06c0c410000d40444001010090f44854000002022003e1003510180000e60780c410689495118035010000c001e554840c440540340303000d103100300c800303175884000604103512400c00441200305200038034086442c512080c0d040740030420881120440c103103400c005c40c0d810407200500307030300f405170400028020110328200c0425007801660b46140200d00a50382184d0340781880c911807002010711600080900010500051040002c4410f0b18150103900f840e000305603034100d030146e00c120b405504208c4840c4800d40c1a54984051600820443d400424035040aa00304054042215070101d448 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 512161609 1250 512160359 512160391
    0xc030f100b04030308180d0905030d051305150d0203070c021e1302090a030b040c03030f08040309031b09090c09050c0c070e1e040b010608070c150c0e03070608040b 72
    0x820748402140c042d079926140c40201601e038095440081250919066064064100980020b030f61140000702211821800c07035010a4420905807098415413192040380140300105102d9410700d0030490400e01900c0c500b041c500390611901204981040e03540e080000c081e14104003c2d0301d42f03410242e4078002c0100c954015250b1000004130101da151440c407015035004982080e080d80c030920404011500b26420f002107103441e280444542940d401700300d02040c03842c03814040562095680b00d00c1141d168403044811811a26003950000c1a440e0300200d090000c0404113100c0500e004422140d0320641d200034565007844a14030070f0700c03130003410600c3c1c46000707005070281c0c0000043d00c0c004a8445000000c1251a481414030620030b504103000445600c0005000401003213191880c100d55503981c1e24a0f540c3c40e907440894506110391700246c10500c0800041d10800d50039400525820211704255044040034400f280c04d003202503000c0c00108401da0100000d20448900440d482030300416103142c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 512162859 1250 512161609 512161619
    0x1606021c030209220e10141f03030c0507050604120201080a020f090402090406090509060a110405060318101d060a02190c0809040501030606030210030c080117150c030f10 75
    0x7202403001c40c4c07a6040d6010107011142124070343c00442030350140c50a49030a5030403018440302404540300020058001c0e0342c0003c40c0b00082a00d4407a42501008000307040b07601e140c80c12180b180040301c043e940d0340543c92000407203941d000000c0001344880c15000c101c050084c0005800d0180060051002c2c07030040040e00030740d00800c02154a82c0c8411100180c0384c001080108000f002d8540080318400d1401b01840070201002624902c40e00901005210b4002d03041d001c2c410901441c418640c2103e41170011407814080d00145000081c1c481d804c403000d004007071100c0301c00d40b40606c01078070810b208240c8400e01c0d4030301400880d5200c00c00c007500351729001085104801e22141041c0210400c84420a00b008010703d4004540100800500900131940c4a05080c0c00a040c203103c00c80c441c080000c2d900041500034080d180a46102d6250081540c0ca01304011040d0000c00c09550018025000c1c01d402011a07100c1da41d0044080c40300050f140d16044c11018005c54020f031500005010207001040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 512164109 1250 512162859 512162869
    0x30e070501200a20090c120406052508010f060206090318010c241a090106080c04030c031b060908062701090335040f03021606021c030209 61
    0xb886810704030705450810710700403100e0824002d044018a00e00103413011045212a0100c81c40355044105c5000c05603031200c000f2841544107148400c1c81c850b03200000140410603a0f440107038001d1140903040110000360300d41c020450b038582118400b03d518400180404041c8100301c0d0090455400101814201905000c0d540d010703550030018200403600100312103910691510540340c0e03000e1a000c814404000c06003211606151f1440411858915201c510012494010f16240009030000c45e8a900f015000c40d2082002000911503440400002000800d64000c1e940214090081d0344021345402003a10784440140d40b010702084110b5405000b1014041009500328060507401208580840000d40b0741c54501c0081007481c0d441c00310352000381034200600c00e00c441c008181d8102e04800301c0255038030100c0c0b4110580000740403a400200081c0c59144081c440a000f4011640c18031481085c85000400d03c1e0089001a0845440162500161180203102070142d0905600700303910180400d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 512165359 1250 512164109 512164127
    0x152d0a0506012d02070b030703020c010b01090302010806151b1b03031911010603080c0a05060105060310090b0d0f050d080708150103051003020a0902070c0f05010507172503030e070501 81
    0x103c12200c0307070b1000840a03008020000003800001c5000e902c9140030200034000350403010705070445509062081841e1340c400c2c0760f0701050b29416140d560681c1c039032109000302c09c901c1c03000482100c00200600d040d41c4010f0707065042c50607100d8000348182c214029008540c2c0480f40c100c28000c1d482401074a0310300c900300c424102c5031180d07840d040000340c0d11103100034058104c0d40d10140c40a50001008102c98070702007079001c0f1090017181152500e90380c80084c0107240c401190204001c1c80410300522101d66180c0240d10403100c000c000c2214204641c48001c0921000c00013202c5030b0784206094140e0700c0d040f144440d4048d00500f0980c150b0300c0d080350300100307071045003d205040569420000354420b21714040007010755006008584226251214803000354050f09060f1001b0b00744243c00241d40c91511401d10a9504c1a5642800c04400c1d40d10b00c41ca400d2060200e02c0303000414410001c003605988200b40166180014150080142d0708000e0100c40100b0b548000680181c5410f01c11039802c640c1003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 512166609 1250 512165359 512165417
    0x10206040b07020114040c031e111306030b01090b0a0e070e2107080f0f010213032d05030a12020a0e0111010e01020309031b0f152d0a050601 62
    0x180c81c0a548064049006250050100c0029054041400240b2031070240003c00c1c0c0e0312802800c994200384e0440e0078411803843c4001480f0030035010391554035090000c4100080f510321900428000e803255114010f00800341c002c1030303039182c1c0d07050f020155140c2608010000c0c0250a4000360a0900c920010030440002c8031581c0250400703425400c1d44245000320540d1180f409007611441600c50001688804101400084500c1003000060000c40c040c0708440550350b5002c52401054519070712080107020454150002c01c00003000c03101d084042501c0401c0303640c8500040d550745c040c0602c000e0500c21745800e03144a018410700958140030f4000b40b49056240342400c1200c520002c1641e41130240452403480c50f5194004428001e6010001016011444492402ca5851407598042c20780d2407408482458aa80c00035a000c1b1202c0300341101103400400a1166140450340b511401c0c0c07402c00010041003a0241020411068114034400c05800c0f07042441c005507541042c1e000455036040d11000c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 512167859 1250 512166609 512166623
    0x40807050114040332130303030b03030a08180c0604080105060102191509020303130e15010503073501060215090705030a060b031603031809020a141c02040902070516030201020604 79
    0x40014140424a00900800100b2174441d41c5048020f480c0621001500c000c50201c1c1c00c0404040c0e451030b01109460300c2010076074580c401035446150103a03005800025071001401051450351083d160b132802031001d400f0420001c2820b08120000a2905000720121f4441c91409030013880090401000309800251851000c106411a800041d0031445000c0c240200c0c2c0e4011030b00080d0a00030420410b2085c800c03120040d03107040300c1400540b6140710072101c0b040040c90b14100d524000e810303520010f0301c0c0c04607110008108002e240840c0700803c0c1c2a0403d0b40582d2001c103000c224860000105a800807010003c3d200c010316040220f07948200440c4010100c2d83c40702c00039038060320104079000c80c416205518011b590f95904010702142ea130b9010b00100343c641c140f404141c214660080f20920781d0196206618505544400c41c9507400c0045955100e68100759440b00b42b072050f001030406080c070b03000300603a01d650361700d00103142280b4207000800d540318031101040541e0700410b40550003904064 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 512169109 1250 512167859 512167907
    0x1706010c030f140d1a0d0302030a0c24050a0c39061a0909061003080a11010507020d030b12060f090304181a0f030d051305090408070501140403 63
    0x80150f03280e00c002d102c400d21580c0042820032840034260040043d41203502c004107000d0401c6414490340645120015001da4400c001030000b0500c43d080540510b8021400081042d2900088040b00c0040c034a42000d0140c40740144280151a0f104080c4000d9250826008454002c074620007224034940702c240d003e40c030b000a6944000a83c1c450900301c11340c030200801c400c5207030030566012000d17403200b62401452914000b551810300010303180e00580388040d100c60b19914540d2031041c40c0d070102c401c0f80c0400203d899194402d84d001d0203a5800b41150350042d00414640d150f005080710300240c00a4483c01035801a0074410f5400314040e070308030801407805045660b414003010b1035031040b944207019011120010040c17002483d03001c504004a00103500680b10b0302d100c1080711102c0c00c44e0f1120b61540222801d0000e1500450040403c840e1907280750b502d0940c0e0700300003000c0410482d0b0030780d030300302c0e0020b030795000c00bc428410070001c078190011084160030140c400518483ca1500382c401203100c040303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 512170359 1250 512169109 512169137
    0x212090406030510022508031306021b07080607030c050f0c07030203030c1f05010e13020f1206041703010602300403030c0210030209060a050315060307050a1706010c03 74
    0x307044075000c0c64103e03007210000c2000c03035400002503110100c00001e104050950425107168040d0805080c0c0c0c0000e4014115142c600e481034110303d1001c01110b0182c1c0c20044840140780c05040150310030070340780207800514540001141003c400034800740c10146082d0300b849095030000309481c2d248804e400e010b80c80740c5000010f079142103299000a90300d0f1201180a43c08030000040503a100780b07848101d00052a1944602c1c016182c017809402c110389048000103010b0502c60704c0c98910300e400200350520030741030607000c6080352400d00381824031500300c58100018031034201c64211000c1c0340c205000d491903140040003034440345038039017882110541e06400306c1058190003a151011052000c00bd640d65582e02d40600101d000741003c80c09104810341d00c4480741c1c024820381d804608040c00780307031801009010440c2c42d680018461900924032035192809501c9103005180f0400d11921240d50740d2201c10f90140c50000d030100c5103140e0005840c200860f03a40d1207003139005200d60506020340501684 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 512171609 1250 512170359 512170361
    0x6090601030e0a0f0215120a060b090d020607030306090c0e1203030603060c160804060918051005060904020f040b030717090c10050d050702030904110403080f0319090506040b061002120904 83
    0x11ba01c1c0c8403070600860a03030320a0000d00d03400ca000b00c2e1562400c1111b0742d85d0b54a002c0441c0582c1b007400b0307401000c072200c00c805810316400404900e4880d1600003051621070700081b081f20782c40908000050f00040e83d00c07400c0d08101044c0382c00c5041e18030086d41145411400281e65841c001c1c2100c018041c08198010340c600c1d03104655620550000c6460b8580b522104e006204040c0c1e48500c108100000c1000030b0842a941b01d05030003049032030b07540480c9a0074001484002d501c007826142d00030b5400c00006201001a001a1000d0300d641d984140e66411300540061010074a5440001800c80840c184440014005010121404159001000702c0c050320020381e00c86c090801e58040090408040008903070740072005112a40741146d0412031041b0000b2141c02c203008034000100000d130108140c000940b0b01401441c0d002c000710840c400c254400204c0b40068031f5900d84112019401141400104210040401d9000c0300a40780c2d440c004460520013940e440030b451054180340400920103600c0c1d119 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 512172859 1250 512171609 512171629
    0x5101203050705152215050603030405030613060b0a0e0a1104050414090f2a030a080d06150e1f091703040e0106110307031413030b06090601030e0a0f02 67
    0x121056901076200c0e46489072400c60300300c40c0310445d01885d035009048944e2650000b0b161380d4201c04442c09480c20140880300516004c2e1070307550702d171106000002d0f09990420646201e085030851118103a8374a29002d4247d4010360f05113031242e903200310140f080c26003090860703510050303041002c00c4044083c194402e0034441c1d034102070317041401e20030381c01025000c0e044414010a10001182c5400400e00c8043d84c4412040810082c00e484000c0c945031a6035a4240c031011481e00202910b03000342c0141d81d10145c07584030040d810f10164889004200040b110f882d521506030690a2003615031940301c00055080820b0403000d180c814420f003400711194400d405440c0644080c00f41544084020400b00e035a0b6000781c402c000903200100d002250303541c451000201c3d1080710300010360800015503801e5640c660542408440c002c02804a04110000d00310000019806445c0e080d010b0b082c18404e00c520150000e1000c3d05150514525000c0340744001044a6501e4002c00d0840d84071589200003440404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 512174109 1250 512172859 512172863
    0xc0c030b0405030c0606030d0f180e010618140a0e1801060605220e0f1b03040305120f0c0f0702030c1e0102280b0703020702120309030709051012030507 67
    0x148560030072040010020090520707040b4042203c0e140c1d522041010381c0e40e0443e0408800244003410442072142c010703000d20124080b85c855118965488104d09010240260302640c0082c003111617140c086103010750f4400c060f0240036501c9040c40069004a101d4a089216000400d4410340001d540620403448465007411000004d0040d00e5807100028000d4105030384091000000c40c002000450ba80e00080c41101c042c0081490242c0c0d0b00503020f10f110b1401032a6681a00195082c681401030507802140f180b8400d89030f007a00c5010941d540c45a540f001000b8140c10361140050100c0c048054042d6451070010306280f56035601c552000c0390914502200103a00800801d802c4800000300c0556104100000e07421a002c00503d8901c01d400d000400d001d0f1540105251311602c0401c01e070441180d80010340d0300700035103400d00950101c0c2045c46507031034040c11500045105041460b040c4613800c0207000c040c5040c44203051070f0f56004a072965510a40750b40312104d40442040501401c01e95a07540d07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 512175359 1250 512174109 512174123
    0x608100f0e25030b1507050a06090c030b0718091e020c0709050a1a0d1101030504021804030305010e10052b080705070501020c010f020c040b060d0903030b040f0902010c030c0c03 78
    0x141a40c0b201401034803600128604c2501000a20b500c010040010750303008641000042c114541c840d143c05009200e01c004c19988090000004004916040c02d4180586420f03034544400303e9000304490301602550308a2502079042480c0c00347c1d4042e1040340750001840b2001e0069543d41c0f1700034014544205a801141100c1c01c090401c42441c03284d90016110109950303c1d080712101843c104403a0710f000d001d0091520011300180c20340d40d403082d030100e54003a00c060442400c807030032021000c204040c101d0b02100005d45a80040c403441903d0840940c00405054a90a03400e0a000c0068420303600c03042c0c80011141d412014030b00004039058020b5000380c0003e40e480e03486481b41070091715500e02e80101030143c4940725000c0065449148a00c20b40087d03a03000e000a0f802c0001040090148407170080d0740080d05008041404109109107202c040c480d8074006071410105c001e0009035951801042c58a0b850500e00f41c001d41d8100356030405041d8149000481400360303140c14000c0c0700c49034001600c62 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 512176609 1250 512175359 512175421
    0x503210a0b0102211b100b030a03090b1602040203040f03090f0503030a03020715090804170303060105030c0c100e070305070e01080303010e070c0f12080a06051e0f06070c0608100f0e 80
    0x590101d10b0302c00001c2d1b40902881283d0b00381041c10b0303035007441c00d80003800912100780c00c0010500d00d80142a50402c040114074900106030009401d070780095030150784001600004104240e01701165400910b0610b042c0740e20030b890301c00001d440e402981d07c450141a0002154010171a00210140d8010b08000003000551420705080c0640d030024001c0009500141c8480c09030b0140c000252441100b05a4a00d4907603550714400c980c0755001f041c9841618030454100c0c004844003402201e0402001400820920b407550400d02c1c9000200e0b40031419414100006202202d070210449054840d1480080010703119a001103070404120392001d0803200001880c881000780311455808144000d54a0f00e03026101d440c0c0c9181110100e00c1541d0303000464084505da500d8140c0300720702c200384004003100448190700300890350030b07408441c0450b02100c112038107002d10760304218644e801a464401c01c1c54607a052100401002209001e041c10807000c0400080640302e810a013040880005d0301c3d95642c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 512177859 1250 512176609 512176657
    0x90203070e071e052704022b0c09120308250302070b06031903080a0b090c0d0507141206060403080a020d031107030e0603040f0503210a0b010221 64
    0x7051401980e00c440d14400510504084d00c100280e0300c01d440300700d0a040301c0094059614282c00b2a80010b2500550244409244c02c6c0b00d03a10b0060140120b007100c4100c0c0c0040c1e454101c101d03405440720030180415640d0500c4580e91402da48641550f00d401c0c689059181c1c40341020810072901160001c84100c00340000b240e83d85a005444a035100301c0c5003002a80392041015190031299091030003d640d0501c004002c6441152119045140f91a000800420232004118036120031a150403880f100017030750f01001a40c1e4840c455101116140161900c00129050f100c3d91044000ca8024003100f00081051907940390f0888d0001e55100e840b040d0b98441c841d80182d01d0ba41310500010100c0d2416460712280310700070040301c0a4503455920418500050f10170499150406007094130300244458020001420400003089608021060351958008025a49035640c1d8000d1119414504090482d0a0b03039030000340002c48500219103004c0d1005400702c44068a011704e460207444050500e060800e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 512179109 1250 512177859 512177867
    0xf090e15040f02011205060102030d090611070507140103091a15130c090f0612150503030c0f24070309020d050706030e1c0816090810062402060a090203070e07 70
    0x7411500c04c0e00c40405280c01e44040c5c10850328121030300341c0580c2041002103094040c0364824211944600b1000445082e40d900740c00860300071103c202c030240d11440c000d01c04080420444180402c00340b0b42441690000d03560061b400c1030b0700076a82c0d00c0c10114000305500c220180c2010721403500240c0a641c0300c40c4110324140152000762070305008241c0090380401c0b032100c5d0898030803c1d140c1e991125080e014100110340020070807012a103070340c140c0c21704011880e680e061000304442101c0e100100910304021403014101000e01f0303110b007a0340e0341080c202c2481d0041c8000300c65200c4440c3c103001508820300e0022680d180c6c0411001401e5003d0814003041c0305406d91300203007111139480119441c010061002c0f003405a05813464202140c1141c00007000304150751101441c1c81021f1a0100707587c0da42e00b001500c1c2c540b55440e50090107031106402e010b20038104480d000c0466000c50080b412018408019440d4440a070543c8400741c5c558101c14150b44040155034014503c8039250354052410040c028 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 512180359 1250 512179109 512179133
    0xf02030c180909120703030e2d160e040302010b28060c0206090418080304231b040f060f09020a030e0f19062403020411040f090e1504 59
    0x4071400d4003005042c20180c601622654011000300350b0280303001d003000303840d403c060011000c054440340e00540a4000b40510301d042aa501c1d04003c0c501c4880c1c4051992034031210404003658400744240d03400c41000c24900e4100c43c00c4180c481c0c0580c645040c01c0b0302415180e10520b400c4040041d40341c1005007000030303c0110207400e85034041c0050710342c41c0890300d080b031085011350f10000601c400710b003500d0076600c1401c2511192022180d5040f84d60740d072503682d810444080e500c0c41d000c04c41c0700d00300041c501441514607180401604800744050b0002d0b40d07100d1a03a07140e81c001d03681c404261111000d2503015402800b0600885510583e64030f08400c013030741c40b50450a0000f410608065080c031000103140c501c080d9074801418001c600403030f100480b03100703c0e042640c20030380707440d003001c8124a4022208101000c140d00e00e140d80e820f41c014841540c0f540e41c0c05035040300c0204003c00c200c4001c082107106a514400d80030581e480e41040f403d150000003001c0f80320b846550814402003000c012005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 512181609 1250 512180359 512180377
    0x90906050912073f081b070204150e0a0507030c0c0b0411040f061e060e1e010c0f050609060601080c0f160209013f020f0102070f0609060201050c0306010912060f02030c 74
    0x1020303c0e9446d01300c54019100c08400e801c8024505004240c0185810381049683c220f9140101800c3c90f1f4907913804408420030340b80c01c0e0010f6030312414441301c10317814010030a12042900701741d083d42542d942c1da52601c540040001d00440f1041c80e09800325911500080b034503c4454a0901203035444101d2690902d026140b240b83e640d00f640b000085c40c0b40284025620f4010041c0341403000d085100c620700848031002003c5040103101440e15001030a03c5040f1451a07008900510303451070134810451402001500d0f403814040740508001c440068541202c00b241e605c0081980c07a26000d422800310070300d00741d200941c403403180d10000c200650300e2040707814910001022031060409403a0702500614000c02400c2c081c1c000310500002509042140c1c02244070184100d81500b0f588041d40d042e240f07117031307007010002070f410300c404002c10740d4240542a005a4001c500030710314100100003810758049413180e0010500700078508014001c490b4403c0f100c15242d0b100556882c81e19101a420303a600a08403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 512182859 1250 512181609 512181617
    0x3020c0603100f090e070e0c0d060306020d0c021c2609060f01090e030a0309030507170306010e2d130507030506011706030709180c090906050912073f 66
    0xe1303040d80c2c0c0c094601441c1e0480090b0210604151419010490040030f110b00300004001c0c0401140e031078807072840194051800103845443c3c0440c40c0007075401c516a0102150300a000c540070b0427086200da1004000a814228200c0c0ca03080803030b82c480502a92607051210030301c410003049280110300c285c03007000b1148507840d65071789030b024400484850041c3d400f038070b90003407000f480124080d0740300300e51803802411b0050a03c8000d50300e01a140503841500814041e0200600c006540c010640442801e0112100103c40c0400c0040c8040d0440d1801341c1c111050060015045540300c003905103140b55801c4c5001c1c4080e02d440240907024090546002e80050b00d10008800d0a82054451601620b0014082c005a070b01c1e01070390b1809001003040c03d645525805e10440c00103031084022074010300e500c2c00e0124100c0058100f801c01c56100822000d03c0760440180d60b4103980c02c0100300d41d511a1701004209542c520040c10800008200c20202c008640d41d114a4605136003011200200c5415591 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 512184109 1250 512182859 512182889
    0x908070b1608010e07080612010f0e0105011202091302061b060709050607031e1e0e2707030c0201061a030a1b050d020c0a0c0b13050a031e03020c060310 67
    0x300b101d036030200348500140140500041484140f1601c2e0268121400600c61080016000c2c0d0380703821100003038440151300b9030754000780080c000d003805035900619030f0f400c00c05000c0895030080307140b21000a181a0100426030805030845d620b40c025601140072000903400c1d0b800c482e0031015903402c0282c480801066031628001650701d40942203c00d060307850743d1050102c1c0c0f003644d40365200d142c1440402c402e12511240321002101100700102101906030b03540c0901ca1a40e106000e01e80e0074400748190120300d8150701c840400ea0007408144c000a261900003001644d82900700d0040007150800901610b9600c0207d00d1021035801031809080500c0b0108000031074030007005007040c105a0500080760301030010000306541580035040000106007a03a00d64082c84c0d03140400704045401038104600b0100d01c440450078102030017005031a0554410b0551810760b2115404046c1000ea41c4100550540106040510030321640d4403440d4080c01c031540307030b08140004240006c10ba02900080009140e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 512185359 1250 512184109 512184151
    0x30a030b031c1b02060f1c1808032e06020d0c050601050f1f02011d0703150509030c0f0124050a03031808060c070b010605030708190908070b 62
    0xc100364107003020350400b214941c154400255450202d031a1401c001084503c3d107000507882c2d14000700300e0341c00d00c0c1507125521002d000564200044641503220203600e000c2407680d002e81c80740d520987c07064108090135102c0ea00e080841c904411001400d1400c28900440c0341c05032050391b87c50800b62005034003500d500213000130003120352508a100250541c2c1c41034004005a040c804000c034410200940111048800d01c041550340202c1007040c500189e41d2240340000200e0a03900160302050f0100141140c0c1c0d1858807501e88034101c0070000480c80350750f01d002c41c05c102000c0048422000420b000e80c1c48510240c690107009002406070380c540103200c403543c000c1005440302400141c410080800e904103003180c03070880309401c0c13815452000c00c8074a1000709995004000c041d10400120103840c3e660002803401403103181c0306901500070b00c03809105011100303400c0005580d02c401c02c4940c1e5403458101044100250420030b001400d0310704001110704c280141c401c50701748195610340044458104070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 512186609 1250 512185359 512185363
    0x306090b09011401020307050102190813050d050318011b030501081f110c060906010312030e191b09090b0c0c030a080601030b060309011a030d021e1e030a030b03 71
    0x40c148040e48424844014401d1000340340700440c00e9003040c41220b05001c51ba648607800c9034410a40c0040000900381c2e4422060307440508540c1c084001032a10088000f25555141d0b22104e1900701030a000e0044001880702002c203c01c2d0560507950710080c488140b5a641202d108180d005200c00000e0a160001c10240700008000071303460060f0141044005008140d44c0c002d000070802600c440e40c0070001c200d09400d00304100d5010b80c0b03003000134010350351451400194140c8602008002d160074042030740030f003480c04500400c0303219152080c15a00d1419250150200c00003190b0300d43d40c0b800c0c00d400403e42c1c884aa0011f10010720844080302c0235200c0c03948580f81401036000070580b550003000701d40c52142c86510043d801004c181000f00358184a03100040881d08101c6250301540c1d96103103844c500651054001b125944141c001d4800c240c1d07101c1c0c0c004e403154500c031344000088140c05186c135035000302003207104031a031030316403a000240b1824440c02e51a503005032500c000107401c10399410028580 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 512187859 1250 512186609 512186621
    0xb1009061a0f0d0903090e0703050f010b0d0e010e0102090a05180613060503060c09040b100f051804052a1204020f1c0c090c18260102041203030609 65
    0x1006a44800320916070080380c04551090700c6640103008103008400000d4400d006100501d44240c0b030340039481d4100f0540d09100000244640b04041c2044140100803403a40582815590000c850b2076640c0e205198000240401c95103100c4a580382c10b900030110300065029080b05007045032582d0a841e658002c0100d90526500d80b94040d9031f610001ca0030a103021040c099010a00e02001700301541d5550000f030410308111011b40707586400040c101e001c0e2401d403242d81e40b5018103c0e065102d01e898002c00400400407696480d00b0704c100001c410200244000d0761130404170005105104625020001e0030100c1d010751101010150b42e101602410183e03201507400c5104a4400351003a40d88640030420341d0364407141010342141050341c4070b49001541380c03103607584240580340c40c00c20180303001e0880e003c589492005034104a4844c070708141811a840307801049842552944800520111b84603801c0b21804d039081815610000d4002100d007000c14118840c0c60090300c2c1044090b9444c1d1550702a071760303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 512189109 1250 512187859 512187869
    0x5131502161a07021503090a0c150c0b15040e0f06010f06020a030f0504030b13020f040209010203071103120d2007020d060e010f090c050a060f0c111302070b100906 72
    0x1c42e00d03500da929101c00000781a60b540003c0142c01c40c620700c1d00f0608401e5000707441c2c6115a0b080200120240702006400c00004c10f10038001c0d0348003255159004090841c540c00c0140180241c80215924602c440c038030301c0005100800421520f090314130043c0e034502001c07400e00c0722406001c0c00002e20031074082c100b104454a0343c01401d01b00b4580d0b54101c1c0c4488060800700c1c140b060070b00000c0301180720035aa203445122419901e420011f0b881c010000701c0030031601001e1045004010300f81030b03640c1c0801940d00090b849080507103a200100c3c000b0741440c61600303c0c00d0801001007400c0b0400c0000340c200448001405c1650703e60b001044d4400007003031144020103074015003015240310000d44141c0c000c100603881d5030000180b000c00490103c080c6d80070030f0402d54210034100070600440c504550084020105801d110841002074400034064403074210f405420110058002c0100c0e413902c1601803085925500215610b200c20300d07100319220829200101000c000c45400f184040c110b10840c4242d80c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 512190359 1250 512189109 512189129
    0x120d090b0a05071e170315040b0f0d0b04030e0109030221010b0a06020c0306090102030106200a082107080402011e0e0a0e190513080a0513150216 64
    0x1900300000204598814610503081140800980001c280c640720307210007018443c0000c240c0c0400300d0401c003400da00c80e603801d510b0b451400c006102c2c1b0040c0c3c1011200200c9000d5130041045034800c000108031507108043e880c2c000081842c8081046424100544114070941354000e014844a00440704115540030094014140c64401021f43c1d0700401003c00c011180d00010841c03644407000f007500f80c009a401140564081d03c1c903070a0500d07040c0b12060340540b00c84021811036243c800024040300010035004014005017513040c2503400b05104401e0903a0704008180d075a0144020b1030640c0c00744208503d541b03142e008000c1807841d4402c11a440c000c80d0160f450781120b50800d11090f00c5118204800403d0261850800f5040d80b030f010140b80050007100c00d40d900610f00890a019400c401f0790b400030015140104004505c000701c08451036060b004030a00307454a4400381c0039903943c8210030440c03042803a00d00000807491704040b040b074450342160303080d524520814500c440c0c16400a00424602ea = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 512191609 1250 512190359 512190377
    0x507170a05030720030f06060a140901090209010c0b151509010c12021e0a0b1018021c0e0601030c05040b011211070812090d05090603040204111e09120d 67
    0x1301e020722440c0c0c1c2003181c01405131045580e120000920707240e00d440c6031070025045041001428900401d1200040c04680c9403440c0c4a000d9030001400e07040c0500410800e154007007004400b82c3d1051045040150b4840d5100d0070342e0038840124881003428042a910410203204116440c140c840c0546481820607100d01e149101107070340b603485036a4000510070452180055013402014580641d20030401c0e13075000303400d011071103040c10008001f006103000200d501c0d4040800c20703002d120701e00e00c140c00c0903854010f8844e80c414004c04080f450300804503419600340058144810b00220708941242c0c0300d06082c80780d140c0d54000f0b0105480130b24107041d0100b41412605400c00a850304001c01d031141d4006003a00d0060705658130300b269042000d01c0d8060082240030070414003810800402420400d00300f80d42003220000000310355201c000d0000780190b032100349141c1c44100c0e40c0c060750503110111215003201084211105a00e0300312074001842404c04240c000740900000c00e1100034071815075038203100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 512192859 1250 512191609 512191613
    0x6050913092301020f04060c0507050108070c080a1419111b06070503041d01060e01020703080d0209010207180f0f0203060f011110090c0e060a0e01140406080a0507170a050307 77
    0xc0b051400312010300d195002c0220145041e2020000c0c00901460384800348200483d051207494402d09030400d5042c04040801d010303549401040482c030256004002568808481c0b60442e8058900061440101c0707000c01d024070081a04011400c00b210036540317107482040c0740c03a495030b650400c403c00f4070304041d90240c00074041c3c10700c20300610a050099044a1415a4030f0341500110b148043c03201a14608400062000c1a44042d0426600800348002c004090440c1c444204e14420b89003690411540041c4582d00c690081c005000105400c1c0d81d900081c20816201070701410030f0f00034980c1d503645898601e000084051003540e001e003001801c2c00040d0505c070030040d2401030038807528644a00c214140b8a03038105182c011019842d03c6520b4003000c080c03030706c4840b0244000c003404013441409030110610181911030349140c115405da0643d0421821003c02060040c0f01780e402030212070203046100c400f03101c400103001e004c6904407241c00710200000800b240e102d0540000040c40c5401c10405080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 512194109 1250 512192859 512192903
    0xc080106050313031107030f0b070504030206270909010c02070614040302010f021f060f091b0807090e09010219090f1e05030609060901390504030c0605091309 70
    0x10720240709042c40060002451407851411506d0f5004075808090385020400f004481584a44c1100403410010b082508580c00101c2c580038404406010005a03c0a840500000c0c40c19190504014009082c2400c02c08411400381480c114080003500c1050b8000480501c01c4800310304900005940368181815036004460204a80003400304510403030ba003010701349a1401e0040741d05056814001080d138901445520f80c1092a4025014580341041030b0030103820440b560110000189003100c07050f80c51020030b56069520740c01000a20000380100610b84005500a000a05400500401c8014020401c0f038101e42e1320f015080716401560000c101c2a040c40c504d0321149051403030300072251034603203006c685403590480c1d1660050344040240540ea00081c421000f000844034070521002d032041000501c3c01d11100034a032402021008150f026912a8050703a02540e800b85800340c06a0b0b90f81c0c0001c10581000d40f0750b5105482041b0104099031040c400d515a03194410a1058103c1445003014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 512195359 1250 512194109 512194141
    0xa030b040c2d050c060c0c16050d0b07050d0903261b0d0f0c0e09011403120d110a0c0308010801271109100f0b0708030606070501140c07060c0801060503 67
    0x702803040a004c10a20a182800b03581d01c02d42140001c580c4400c911007100d0325108241320a01c0344030250040c01c2c400780e200d1990301e14206411906003141c54030341306412102845410701c0083c1003441c0030568410558400d40d940c0d508220808102107000408004a1a00c4801d54800c140811041050500102c2490241142c540303011000200030040c3c110100a46424800320301c001942c4442101452502d0b280aa02514091900c81014582c1c02c0100c0c2d610b20925038601002400421401c0c0388001c980c01002c0046c000380312042d114000100e01629008003003000b1404a8101c00c004601210140f00301c8200070298913106520034140300442d0380b00b1009640c20388401040c0080403140e9120805018002c5581c140300881080c0741c0131110036940c40b15044031171504c03000c0200b0004240b4410603644c00807000c4030003035900c40031881c04500414565141e5540307030000508000d400000c06000e84000340c0120418000032040d0141121030610034000c0c0800718800784080380d152041d003503800d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 512196609 1250 512195359 512195447
    0x7030b030105090102280228120201060302060a0c02042a1d031903022401090b0f0d0803101502070510030516050a09030605090a050111030c0d1109060a030b040c 71
    0x583c00b0703d8524500021014a41a00181c03048181d040d034502700301d14542049840d04036440204106030550f8002078951040c2c004003400c010b0003400010a566540e40309c16483c0d81143c4c9108007040c241010905032890700600700d40814200a0304070341c00000c8100d0b6005011000700603040326801174809a02c42d0010303038810f40c04c5105501102c81c02607d10802440c00030310783ca40ca580550300d042044410b079640c052456000e101c41d0380e0640c55079165100c4030f24600e9444082a40c0301e548415640300101074551000b40c80d41c00315018644490740218084042c0d4909540074010b4490602c801d40540304150740c080040c00b031025665250f01e102d1806441039058510301580c0325070b40d07900d8200c1035403401d03140c05035160002414082002424401c07c40402c10881003942146000310442c0450b00034480c11859154075607903002e1418003100129a41c00500034206038543c201150014001c00c02152498083c624040782c091500b0b00401081d50290554581c00a50028600400950040031115 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 512197859 1250 512196609 512196613
    0x230603011d1b130f08030901120b0616080301030605010605040302090a0903030e030a0224090714040605060a0c03091a071103030904060b0705121603050703110607030b0301050901022802 82
    0x28882405030a4001d00c02860083c1480100908081c041e03001c0c081680c1c84004e455008100c44101c42e600420480d000040b22500003520402040c042040ca00c1101c40700500c1010038600c8004200e166002340d07058900405d820440307a07072142803e460700c2c810303400040c0d80191501c00090040ca455004007111510a26000c610108410a901d01d5608910915805604030100e0300d030345102030003110300032600e1081c8000303998140300c3c02d403540381c040034000c01203298100d030070302e40031074a4a230056801030601a11440c0d44109181c00142850302c100e1b4203e001603036101001600207004020001c8030750460b680311341351107525503c6404010b001e01520b60503000c14845e400040c2d580d031042000519200070a99940c2c112032501500b420f0703d0001e0103030300103018440042041412201050b200d585414103a40d10080c600b015500465400c00a00061261008020403140e04d43c0010306030300401c1e802440543c85108400d030903130180002020300c01042e0411400e11095004884403424001c2c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 512199109 1250 512197859 512197891
    0x4051503060d1509031d090417160c180c050409090609020a08060610090819081b0705010f090b1818010608060f010305040b010504022101230603011d 66
    0xc1c440d0064040f00c00003850701c56481c50b00a0901d60000043c400300c3c0104034071151100440d600092464002070000340035014160105410380103124101c545a10910203442c2c220122442c00c03031201300850099408100900805070760a61a50181e006040e030320380c072410704003410001200b00500d00c61500380d940c03a40b00c442c1c100c05030711050303460b00c00303802007402400f02850a42e00340620025505440801c0202052081110f500e01080031065003d440d210180410400d04240045000e801c40203600c0798000f040060602d00001130301c5040f15002e8039154103140212201343c03082e0445200e0800c00c003408110100d20300a9030f60b5504080760005244c0802d0540d83c1000c280809003d130800710214020710248a04c501d0030150201d1807090910b8180602e00e042c1e0365002410f40d061140f40d014580100d1487d610f880264103502c1d5175007070325242c203c296030740c1c0c0090841050104885204c940c120f01d140382c42c234204102124140d9480c51340e100e241e06828000c1002d60380f0014141c0c004441d082d5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 512200359 1250 512199109 512199113
    0x25a010f0207091505220606081303080711030d05060f010906020c0d0302190c091118090703181514061c02031227041a010c021f170a0204051503060d 66
    0x40c1608135041c810341000c00032642581c40300d1b4212403244c0c10140a104201080102c255003c80d40b0a2055515182100a0b511a20300542c0c0003071405100050134040030500341d0207040303a07074070403440b50300c080302c3c00035909108100540300b40505005030b1006800c520f80e000c03c4da06040000c9070341b413882841121a01400484035444d800c45060040300c01551b401f40130001d0445a00a41c454480e03100100c915005503d0444e2080030030120304140601501c0c1c00007908a0700a40c09448200d816030006140c44140b45008a142498121403d03031007803a00107142000c00c42c010110380701d418094095071082c030788040b080e410560001422030381882503015084418000c0350181091900002d0780c00e1b40003482140d1980c641d9410200d29010300e00d0300e40040083c0404a0601c41c0200f800e090410340021140081800480c800c00d84101803106040811421580310030070540074403a07180003c2c650b445508900d03007039200d50320803d98480180d45907504010b001000030351b0030150090080481c640700c1d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 512201609 1250 512200359 512200369
    0x90316022403014211030f0913090203060601140c1902010e030d020d120609060608071209050d2109080d0f0504025a010f0207091505 59
    0x140103004400d880110041008141c0c030000c000c100807100c440790b03c070050700c1d0a1030650b01e03a241e01240b00c0b0a02c042203076032000e07003c2d0342030711100e04445d0140e82c1d0392400e0341d05d4103c85030301c500030a80c00303001d40f21220003498140344140180c0c11741c0140503100340c0e143c500044829190343d40344101c8054041088105491081202ca03a01e00740028200c000d6441038000903102c250240c6040303000760440c003000c000c0140c0c08240c2c2a03a15001f07042c08680206144140c1d07005000503000552850f1400c40b000c07031580e80000307a9038420005c031307a1b1340c550000b071031000b40c0156241c0c1c40f001843d540c0166561044030b0f006112030064006071100b2141a02d03001095074050340e40903103041e01c40704000106007000840600400141503c0000184114281b96000c907110740c0300c6141d044140b94041c0b107540d6400c02544a11401d40b0256025000301b0440b407401c078a051b00b01500c1d01050028081d0100400c1c1d4012440c0713640050803500985402c03441c0c80c07941c0e4090400390700c06c0c85100710002c0c070100d190b0307030781e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 512202859 1250 512201609 512201659
    0x70e0412052113030f0206090718060b030901022517030601120912020d02010b0a1214060a0f06050901030816230106150e030307030e0301090209040f0201090b0309031602 75
    0x1c20400e01c036015203401c0180c2003202e000018170440d00048200011100e001030048200d85144c160b9483c03a003101100710000300141c0c3c10120481d9000401d11441c081c0c1500541101d0707807003640001160000c1c0d000408402c0103848001d040f8203211129880512021000c1c580c03050b03048c1000544940d003411040d0443c2c1c2103050890b1801310a000380c95085604104201202d2120b0008000010700640001e40b13198a611680884903d228408010090440070300400d400c4424210b81442c1495018100034000014124480501d0131100040701d242529546040b60b80001c2194a000305016483d000070328400c00543d56000000c0c164120f4091740b0520702c03800511a00002081c5080070151101c40e0000c1a40c2010005a015200c0e981d54020044841490b41401e0040300c501000b00824090154918041d503c88051000c000510101000c1101514400da9507400402c3e19241510f201d40000c0e038400f086c0c0e0f44203000203460030f8003440c0d0550f00180002d2a03400c00f490440200541c60017 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 512204109 1250 512202859 512202871
    0x50d050102190e03150603070e0f01060318030e01030b040603080f070b01050a0f15120204031208060108041e0302030c062a0901080411120717070e04120521 69
    0xd80000c02c010801105000e200d080103580c50300d169600501c100203640d0700d450110811100d20188046207541d9420800031000f040707108002e14071403410001c1c449070440f00b4440e00c00800d0a024001003151011030402c2115a815240d40c9840807a510044000700303440401150007503920507000c004695003002034108043d4002d40f10f960342d20149002c810075403040c0d02441c041c064100e0b0a0003404102140c60054a42c0d0300b45c1c203e00394005000c00c803100c07940b01074425603076880080d01009003d021000c10304005955120a4410b480e1000116014801140d02a048680042410898006c00030000c0d015a0103071040304d0801003d140d90300d08281040c2c0700d4942401150244e95001a5140c082990a801c3c4004040c141340c1c001002914110b0000d100030075803080690315000c1540c030420310060042e141000c40b000d07141c64005409850720402002c1c0e55610882400089900280c84254416030303200c20700d0f900086046c101a50300d50001c00c95018850000340c403d4440182200d200b13480380d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 512205359 1250 512204109 512204111
    0xb1201152d12110304020f060d060609050a080d020c1c06020f0316020303070503060f0a0b03091b040603150e01020906030f07030f05070c020d0c080f030d0b19060315050d0501 77
    0xc110700c0010b015204240c0e010b1461500300503076191001494002e50b41d20a4041e10b20610340e42d203400008006200d2290001c42080c507003800030510f02e50140a1806981d019128036203055150400d082c0d60702c000d000c00038010381c4050261105414080f10f003c0500800c0018181400742c5a0340d4101030307070044503c0307514400000c0108814401403c00c080c40049040c000b4510b54100034100928603c0000c00740d90044d0280c4110303880944032800110300820340380c0542f54481c10a00745c410741303c039011800248031807413162107402c80c0c1c40c0030b201e807800b1a6440130050866034003440c1c2d400c0103070040750751804c1c045d58288040480c54036407100443c030480c221a06d80920f841c1516016049540035183d01d0310081c60901000601c0c0d811030401c40c606901118102107081e52403508035010748050f00b1011590043c8200e6410003070002000d8401d0705071880050190000840a01003810000351030030701940703010b180c03c00c0700340c2c065071204038a8409000819610741d100c130702090201c49564422079541e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 512206609 1250 512205359 512205437
    0x60b09030106090c021b03031204141b180a060e090f06010f0501090311150a0309050c030a0f0b0a02190914010306050603060f0103090506070201150b120115 69
    0x1440c00303214580142c422007000304801920a41d00a66501004c0c042e0b41d1903482100400302950b500b002a14212012040a005d043c5000d240040c8426030006000705c503441081d420280920305240c880b65407400150000c034a410041016806408000d0310022240ba40c448010a001c00c4e01c26041d4400c0ca29900282104e40d9400c0880b03180100590000b0003c40c0c0300340d02404580c0e40000c1c0281125004120700310081b03440d00000d0313120388001042840c44200003d42c144810b030590040f920060003801540c000407540414940c4411001400501c80110704403d80005040c0d50195500310715404001420850030b14209080240450a5140420b50b152810003501c100c0d2059a12420020b00c0c00780b02c42d524000110303d040c00003500703c6104a80d40350841000c0d9100e984003001180c0c0000031034032a4200108040d00030100681a15000c81c07115a0106103482903208445105045000c01c142580c81c01c26103c1408143c00010020080403000c13410a41d0302c105014081c030080e1032180556 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 512207859 1250 512206609 512206627
    0x905060106090f1a0901020f0a0c080114090a0f0507080706030f05090a03120f150b0a140f0703080601051b070f170619110c0d0311161b0801060b 64
    0x410b03210354021050414160824040b040c0c08100c6890300340da22a0b0f078542c460190348010b03820300205c80484c0c0414440d030307080d1400703016407075903c0360481e0302d03040081007104158206140a004110340c40d16032030303111859010020f404d44540c0d0b04058011307000d80317030441d484009107170038031050f58800c0e40065201e001c0c440b410b1a8610540c1d810130400d400805e0070145a03940a4091242c856200840d5a03403a652a0140040e82d0010800c08000221140c100398507007440301130035003020b4a03500c0051038201580c2c00c5010a54202c5458481e070030005030504130b50713607000c65044000522450400006100c42c0e1503094050055200322515080a001100c0c20f00103031200050407a0f01c0880c60311591110002c2081001c14425040015078450030000d104042281d80030b40000b08003401544000180b4a81d08000442d07801d6592000d030347d041c09140124803042c00a030180c402800000700308000c41c80700086e250302c0010304c580700b40c03441402d26079a80c0c45801d084507859402050f400070009410b580c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 512209109 1250 512207859 512207867
    0xf030708070c030804020915040608031b01090b043003020306240d181a09120316030905010b03103806070507050a0902180307050603190905010905060106 68
    0xd4031940318640b089007200d00d9140204000790151020703001e0184a0003040e0203040040300fa0801070300103807040c01282d40d00c10b0700303035030f01c2e0301c90701002d11642d040c000103940031001802052030302d03030f04041081000c3d11a5203814031b081036080f10103c0380c04d0404903580c1d496540c1800343c0c8001e20554a0050300c1c1d16190742030090f103d403980411042c550302ca443c0b00b2076059541c0d081e01c20705a034081001404d080044840d010000d0105000b0300111148903006ea8004000c444040c480c14916064603030304c0c86d61075440006808103591200140d250b9080c07403100140309500038400c99000b40c1c00031480611a50209050810f0b040884006039100c0e091a81d0016001d1144c2801103007a2401d40c0300324064407502002c20701c43c0040103101d0080081c4000a010b8100b0001c0042c0100800703400d42d03a40c0e10743c1103d0095002600300020461901c2e050344a0b403401041103000c80d08003904091460355920003203400c21501030640131070559203810200c0420740c240b0580319803d204900500c9694181100a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 512210359 1250 512209109 512209111
    0x16030b030a0c17151f12061e090c0b1c09200d0804030f15050a1a040c120c03090606121b060906080c0c1009120908061f03080f030708 59
    0x7845640c4071040c0c5249841400304c6042d4480300e04035090041030303103841100307050280701e83c07080380c034042501500030510000e0390025201c2500d15902201013160204500d0640c1e0713840c50003800e03200c0712450402c049440840148441824040f0701d4001d1081c031007a040c2203c0c881e0300f040e50002000350031061482c41c0034180161404084460307040384101562032020070f00c184d000080c1401d100b1038035070f81002103443e0702d412008684001440f035440d04d103003401c00a19100542d09445c0189107284841ea0a05101d2a40818003a658404840f106040c1c5000600603400c181d104166950390880c001c18000d104e030002420401306031110185280c140490050701000030303642030b290f1071542001200e0f000405501211803a0504e501030380e40c1c2405142443c029042d24240d18080c01100d44482c84855100f41c8100748a85041800400651421143c0d01043e0140c030b80940d010401040d0245d18140e1084c104a442c28180305c00c41340c0f01c1d078480b0510f80100d011841d03040b070044141300380e50303170044642 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 512211609 1250 512210359 512210399
    0x12050603011811060c120a08070908060a05071107181a03070e1e0114030f032704060b0a081905060f0f0f04060b0405012616030b030a0c 60
    0x1e0194034484910011041c045510082c4101c20301a103079050f54903904244d80701020740d501980d000012140c03020a981e0f1000807000c000803455000900c03402d020301ca22100399030450000700300940d07071510300724020003003c5c040c6414012102d00c28000341004004072006070070461007080d205001c01039580291014003c150b02c03200f26211922a4640300041c04404480100d80600680d450300c0c1c1542901021520000103804814000440c403407800040e0480c11680903002c558004281041039516400f03405070040c004540e90f5907040505c4480c260700320310b40f9002000021210783d100d4001c00d141d030009246101080e1180c040220440600d28214540080c0d14003d02c41850032030000b0f9500e0440c444414407540c140c0900203540d4542c02c64498840d00040d100300003050300c504065050707801070721480e8002242d6150854801c1d0010001001c443d80000d0f013207442e603d84c3c410542103141e081c4116420559036494445180c4d408022200c1c4d0640200606002d003424483c9541c0030350b00c40d01c04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 512212859 1250 512211609 512211611
    0x8030c1606020a030f0c02060315131a010f0207090e0607120216020405040317010306060911040521031201060c0201030e010e0a060213030204020c010219090602100c03110a1205060301 81
    0x1001078640105a411889506280140c9545100e94043d950344035400d84c0a90026070100400a03100c0c064441c40400e442c003158003c0c45041c4242c84802070729203050042841c1d0211050310f40b00355002351400340d43c1d04040d005a695090b211503104080725a91071203a042580304c002031000f4960410105107042c2c594203020740c0f405620700072030381410b40351201c000d0140760b03544001014948a400f2900c40241c90190b1700290f940d580c1860000381c4041e000b0012058a44012907c690b00c038501101e0450700043c003000041800300b500541d0403076004040c4440ca0004001d1f070100c080c0c03030410341c40c00303440705458840c0e982d40340f400014100d030100a04251385a141403e40c10100030001410001d95501c4400542d40c0c2d0408140c03000c42c009a640300039001030003c03e00511714a4190040c0c4000d00d0b500022440944c8c804000b140d4039100c0c0e20440d030140e0003901690900851940022007002c50608000c41c4040c0e003260104400c1d070201081c0c0340001c900d4045558910300c2402195040481100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 512214109 1250 512212859 512212903
    0x1080f07050d11070f0c1d0c03061f0903050d0504061e021f02031503060403050f211503010c0e06091c0c0b0c060703050c3108030c 58
    0x501098181018062006004000c599085500c01d0b5030000900b0000c250405611074019181c00c0640381181001192040c6100310081486003142e013600184040d10811100c098851451949040d48042d1500740c210800c80c6080c0f1280c800c40c0c404000c8e00307806546052549240d8200a0b040c41c1a001407841000000c0208001e6039520112000c01800840080c000d000b91200069190801c1c10b090310800300c540d1013056810382d0907580036510910110720501d0200c0d903c1410141c80d038008840060100c0c0080c44580943e6401001030324040e046403000c680c001108030445d0b615801c080b0b444034400400d148040900741403e00440102e11000e082007508854908001651030252821075401101c0e0050390000d0000c6010003001c081e900034401e88105921144207007007a81c000207020160307105000200d0a01792291050034031a043c0c2000e440d0a101c00b515521801101c0584880400041d00c40380b03403c0c540780549000000d01401d0021603540c00c3c0e07100710742e04001d1482204d00116103003107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 512215359 1250 512214109 512214121
    0x14090f220c0e012a0210050c010f0c02030307180506030c0307110105160e06040e1f0b0906040603020304022d01110c0a171f0f0b030d1e0302041d04020406050108 71
    0x1c84d09034a41c2541c0d40c1c15080c8064401503c0c1080400d4850103548402c054200c8110300707412500501520320801c00034410400c00ca4215801d0b50641000500180d2080001996061003000c030301d117480c2550815081816a40c03000225150425506500050340000a01c298107810000160302c00c10810000c3c025484d00d903c00c140e004c44100e080c541404241042c0b00c10300d90381c2c08100d40240060507020300c0319003007280c003411007502c10000b1400b4030742021b41c01081d04c1c51810160b0361030384001007441e031902e4140b01044029400140040780c01000c00b1a00c00709049091480a80f22a021001542d00f03801c13000004006003101002d0304095002213400c44c41940f0b405c4401401c0e03d02c400c405c0c0e115004100da52924050b03c00f1041141d00c503594204401e040c040d0380040013002000e10003800b450f84800c1c10551a01d00d240082c0780800c071000b691b617400d448010509180c00005060060806998040c4202045c00c11501070300900b400307004000440c03501e0710900028050a10388181a0300d0f181c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 512216609 1250 512215359 512215367
    0x30c011a01030e0c040203060303071a04021809060a090f0f032c09010e150307060203031014010516030320040302030d030b1c060615050304200114090f220c0e01 71
    0x11102c445c000e43d00000000c540e03850400c1261011540f001c44004166035000691200f40d071f096500b00d1040c122201450405801242224000c410500140c4415101c110f4100000c5c01403180c100c502200650121020500b0000322120441c020340f00c0d050300081e075082044860804880c422550f916404a800c21034075030500c018103440030984154956140c4d00300201282e0520480150b1511403200d020540a40c080003541c0550034030594010029158131b45140d4126007010010f00044050003070701c1c00c0109554099602c1800b80c10b0000f9004111501813001c65110348002007440c1c0001801c00850034204103444012011b4601000001103404c0080d02001c0320503108918480c01c45010410310074698883c0004000088003038812450120002d0800e030030440d82529048051039191805030070301055841061016034036401821044031162202d904042306050b0410300f0801c0c0c4c41d4403512540080c41c8416a0b4241c0e405907889502585019a00c1d00d041e00c8003044480b010343c2141c0e90304 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 512217859 1250 512216609 512216623
    0xa0e0a060f020c062802071104020301030311010b0105070f0b1b040b04141f0c050c0319052a0d050f0d0509130b0105090d1a07030507020d231b030c011a01030e 70
    0x142c44016a603001f55040c007104820b1a081101d03400791001000108040e08400720540d4044840000e00ca052152001528103015460001d01194034075002e140000d540c2c0401c265121040c049400e280d42021001a8416003041d007102201c0e40c0c2c00103003804441e2040517808035040048812040d607280038400741505104489580d0306211400e0220404c005041c043e403482c0d0403010b4115071402c6984405021805c030000005d46890184404143c050b1a0b41e00320704142842c3e6000381c4880b440c00d00184114101030f0081501c0500450500590041017403014500c1204a0f540c2d840d01c80381980100030301c0010b255961079401e49030000c510303c0341e608042075400702c940c1224110422012030503e031030b42000c00d02d10710060504420421480c642c050f40031a0080909a00f15a0065040001035521001e1151048001c24040220708a0039000900510304903071480b240242c1849025001c61841e000724103568802d035120321000340408412100001320f10804d280a001d60610680700c5512403032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 512219109 1250 512217859 512217931
    0xc150d153f0c0b070503030f06061911030904060b19080f1b0d0513120207050d020f0a03020901080703030e01030623061308011506080c030a0e0a060f020c06 69
    0x288480340030180040e4000d582c000700000550190f8442d228588983c84e035008843e00070000e40d030740000c1030480c1005003e0326910185e025111100141800381610020102c08158000e80f00030890515140c60303c1c02401c0003040a45100754550201a40e075044165903441034400300003240d0200190003452403206908001c888820042a0310b11400382d081d24800e505d100c5100c0c504100c240314080c0303810340e4209800b41c0520007181300c14144a030226210115031052561103c0b042d5007420162a007100001d5444000400c030a243da80e607540443c1e10804243c2c80a52240c102050800074960426074030049003009280400c2101c1c00c00d1041c1c5da0308200d80360307101c01d088a04100040152252800c403076003248283d01c102c203440e91b64428103018144120320f40100c1c00369168001203181c05103440714000c110950f001c03030440d07640c0c503041c2004100d4291002c01c5071281d80d0350303c400f040e981c0c440c0410310315400c880960358201d540906864aa00074120048410984402240500812845c7c034842d00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 512220359 1250 512219109 512219219
    0xa0f060e090606030a330c020313060f0c020108060d020901180c1809050901060503060901150e1e10090507081515030109110f0a09080d0309050c150d15 67
    0x6d48120100e15155901400c16020580b07007400242a007074000001d0821104064900d0101d551100d4003201c14291800c1d281000c18229114500150702032200305504c86006047c440c842507083d0000b5804210a03441003140000c81081041c030a02d660082401c40007041c10540300110700c5100c90700c0d04081e01c0c8290307002c4550f10740c086000d0f41429003180c40200030081c100d42c12420f051074400c1c020b028009402c601e12568540c0024124400c4500d644159020a000b101d03452409841c940c5041c802803011b0f041c6c0c0030946002c20280994441d4078082d85055507840224030b010302c0c0c1008002020705030a0711401c85684c03c60341184071401200c0c19680940c5010911110780b56007034115000b01d00c0a030b40060400304940c400346510141e400102d40e03030395040f9400381c1105001982142c880020240c00d9070030007111000242082c000000c00d1032140c1503503914205e580d035800d40c101c9111820401c08069040c0c801c000d1282d05000048081086641281686d903214081c1243c00444101c100858 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 512221609 1250 512220359 512220413
    0x409050a0204050408042d0614040f0f0e09030313022403010905041b18090f0602120403091508042012010209100e06090103050a0f060e090606030a 65
    0x209000304103100768040c009100314181403610366070980117400303034007a00701400c441101c0d01122a41010107403120311019000250070540c1c204d550310386c1da82103280148410440011560b007903040c4180101948503894000702e0410130101320b8400d0151440e10395a0061060100c101c24456500844a60445030452012116030a5400b4403040c0c20013091907981c04800011546a04d811081c0318070b1040b5604040049420032601c15180c690240c201000c0303070703c1c1407019940b44950084e60303814040c80440030109441d41d240c2081e40d1004041c10030044402090104042d00003403a100a0700310525014400100c0640003081d000f00144041c100d2590f41803110790300070801402c0c2c200e03000d0142c4004a0041c00e20b110710702035400031403420f01400342d109071034000602c030300411003400e4070050101d490100c5030001107018001c0544030010b01c0c1d0791402d404621030558030501000708902c4c2d040842601d802031019080c00802420a4002e070401e464400c0003c0c05040b101c8100e150003551074580d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 512222859 1250 512221609 512221613
    0x40f140103110732071d090105040f0b0a02090d050a021801300204050c0a020d0512011511011e051f050625060902102a051218011e0c020409 62
    0x4804403d01c1420b10b400b4079400810749484514a603031035608180d0354652952240b0058230700300c480480d4040e01c1a145403c403800001c2c402d41000d030300000000f0300035003800c1010f40061800c1c80300000c00c03102c542c09140707140118281000150602e071201c1501c941c1542c03400c01929004081c0030048650452002c09000e080e100c04041107032280c0e0090030402c020328140c0c4080c070250b842039002d140076202e0090400c24040c03164049881c80c1060002c2d002c07880e4a01101c040d815022410311000340160040141d0724000c0911800805111b1201400400344846402d9800c5505c042c20320b12200c058415a40c0100c12505441c0044902c00c1c1c1d1400d03520b1f44030610149090100550340d4a1410161003d001481665040400200c3c02102e08400e04588100c00742d4940c503000c00c0b186031200403001030800c460740340340c8000a0180140280c072110141100c01080d10341c401079010200d840c0c4120500c0455070310404101441d0380c0344500d500c4012040e40098607004a01030001d103e01d8483c1ca400c41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 512224109 1250 512222859 512222933
    0x190f0b0a030c4e06051504060c080307170a0218040b0d0b1e040b0f06010302070c03063209011b091509030f060504030f020304050d0f08040f1401031107 67
    0x20000020850003882940103040c242c0180000307100c1c2c175103d220b404c1c00c002d100310581c508880803a10756480724601c000ba203a480007416000209081c0522003c40c1c6030102141041280620031000c8882c010395920503020001101c03a2402c5c03001d8021854000c10890945450406c1018140c1000b03180e1159074508120464280d800d0200300c120100c079030107020800203c1c004050052080c6080b514095840d00300443c200c2c0520070000e40040c01c4003e040001c200c0aa101201d416681c081501c007008a04000c542c00400040340b070300d603107900001045403030341c000e205100c4400381c3c1d80020701804402801c000c0401c0114010404011122412140c2d0fa0f40200b450400440d803015800030140b82e02d041070030042000b250241d0120f0450503c400c4007500c080704450640394000e18404e04c080755600c50705031004220000b00d0b10040700304004030b0f103021010005001000f00031030214003894841c00040685c0d100740503160000074140800b10001d90765454040152940401e0a51040c4010014003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 512225359 1250 512224109 512224217
    0x5031303050708070504090f02040b120114010302031902061b0715050306180112030c020d140f160b09010e010903060608100e0714190f0b0a030c 64
    0x40500024000000400c00c0100b940011910b0f55815a00f5640c1c1d1407040c00151904c045e070003444c404030300b0b00100040c9007550004c80301c40c4024107034640c10040120281d08442c01a1846094012140010401c40c502004011260080314076040140c001e2a802f0690600905115200348011031204e011032083c20030150b1700034100318070441c05c040203805010f0603580c800d0751103500030303860446104054921150080d048070304c1d0b4010010440301c00d803002c440c18007114070220303804a4a420042d0110310380c1c41c100141c00081001170450747c44240929440d0074080d8511180d40a502d00e420051407072110181e0300d070444d083c20b00c1030139078410100484045810b0380005101d0703443c1440c0880d0b00080000d4040d0115111a001c100c84c8501c40109030340e4010303601c0349a0740307607402514031086810503800141001f8400c0301c00c000c1c650344403074101c12501d50baa0440d016946001c9980521158140540c0007008054201078100100300c540c0c030382100d00c001e01d66000c08011800264003041c4940010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 512226609 1250 512225359 512225377
    0x50a02101704030306031202010b010e010f09170309011e1d031908030709050d08040b1303050601080318010c1a0c0705031306020d1d042a17100515070503 68
    0x540710319040ca006001414107000640300c00071150174224919005100351508640142c4914034034440d9003004450721303603002001170708004c09020300207640c12050b90025503185008007e0360b103c1840a00040c200c0204681c0012600301780603000345116001400919110000c00300d02e105107c1910109280088030302c601d20030102c2c4092000f05002800c1e0185000e101296910154150b498042148400d040040a000c81200700301c03c01c580d800c040014900f0040c0c040003220983d50320b0b1581424110240d0203480d09420016411075440440b51080595a1003424410300c40d241c261907402c400d040001c2c00904645030140483d00e40508103059a410325031150440361b81705480c4648018040c81d41c80b800002d8840c00b000900054003451281da81c1c500ca0152003e0700303841d408100005000942501c801d1400e8003000b01d03040707000a448001211030780780c0315411903851003042a404000001d0a1890040241c00c05001551319140c1540703140180c0d141c055201d0155003803c50840c0714085407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 512227859 1250 512226609 512226647
    0x1211406040b01050f0d02060d0f060b07080304260712021c0e12010e100c09090212150405090d18050907020d02070f06080402130b130b0a12050a0210 66
    0x1c0208021007041030a050b590306079481c01c4014070320810310004080000000350f00c580c0521441009280b250701c0a0030404c1146404100c00781c2d6202804026803010000382c0310002e00004210a111407040b8880001c241440104030014070407255861034000c010004000e20404008802d4051003080785403840c851300c42c0c0200f060501c500c07001d401f02405100c000c1c000d20114007400302c40f13581032250a0011191202528060030a5071040000300f00b4502910113100807000003040803240c0b4409803440070b4445042e05000d0420400c2180092083c107100e511860a100800c034030210302007803868090805007403900c1000703119070b2140441c220075045940c00c16048020000d8140d80040e5069501d28503030252500983c6804c041c92a0880740d0003114003249540340400d0040c01d10040000b01010085000680070b09800009402d40c02c015189145c0180c4440d03e0100a2601450200040c141d24905001c201515540e0548034006104081e10a1004011503500309000709503e4013402e0001c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 512229109 1250 512227859 512227861
    0x2007020d1511070b091c081b27030a0314090103110a03060510050301060c030809150106020c030d0804200d0b0f22150e030d020d0e1501211406 63
    0xa19808690001c0f80103503040d0545401044850744085100c02503c48005032040601c10344150540303030118064808411501050200c06c210300030034000d006407402c4108211000d206003d0034511803402500075038840d820511030f1500183e0000035100d09420b0021180307881e000c410005070001c01c8402c100004005000440c001120341c582d020341e090b18070845165901c00d0b03200004403110b00090041d000450944101407020070301490f01d0b070b42e000d480b90049600494640c46201c038170382801e03489500507038017604503030303031a440c003481a68450200d9182c03407002c526080c0c9420f400b290040481e0b10006101003060303200d80c0c41d06040c803808250403090080c00d5042207001288402030440340c080718086d980385d4541480002c0c3c15003662060301b0aa80a0f1501c1060111340d00030000801e00300000d00c010010070080a941d07002500e50412008000650100d00f10601e60924040048403020090b4079401400035000d20418180c00c22440c03000c01142120320702d02803034448080d00c100703042441080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 512230215 1106 512229109 512229131
    0xe1201241d0a18030c02011101020708030105040e0a0203030703081009020702031e030417031908060604030f02010e04050f27030702270408030a2007020d15 69
    0x162001031503c481003440e043c0f40504400c00c501080506404d0400d640c0c02c142d0300315454880348000d500e861440e0740c4140307040c413050061500c265543d04003c2d0504a0400607001120381c0582142c0c5e072400241409400c92408513043c01101034039900214500c1210300a0741c00703503507010b40202030000141c0c481c504a08502d840b24a1a0300c402d203c00200c40315038071a40c019140c030340c4001e15034078200104e040301000303c8044044240000d24003413005a44030401281c00f202e4200e201000e091000f4401251010a90038446600604240902c0200440702d8200e50050f65441c0d119600c0da0300340034109565050258120740e05e600700307220100c090306200c1c2c21078131744c0071503034910500c0100403141c038040d011420b8034160361600c000300402c20742c107281c2d00c614540b141c982d1003c0d803800c800c003500c117150328401da50009000ea0a007003031a0b01009a4401d1101000421450070b220007182d034 = true := by decide +kernel

theorem cover : BRFrame.Cov 512050359 512230215 := by
  have h0 := BRFrame.cov_init 512050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 512050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 512050359 ≤ n) (h2 : n < 512230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
