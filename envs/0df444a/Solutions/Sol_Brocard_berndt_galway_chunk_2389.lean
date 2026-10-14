-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2389
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:34:10.355279+00:00
-- url     : https://prove2.me/submissions/f5ccaacb-ea3e-4b1e-a9bc-78bc2a76aa03

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 429496402 ≤ n < 429676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 429497652 1250 429496402 429496421
    0x1104031b060512060105070807020d06050708060402040f0e0603030f22170a030806042903010e010507050d0e030f041d0709080c04150e070906170c041e0b0c10 70
    0xe00701c3c14041040c0700c50b40210700c010314a40c10302c2000502c400910045005032200154010803001120003e4588a400307013070181e6053b80460a0107001c1140351900d0f0007520b01355500a00c01039921407804004080e880300241c40b1303c0e09400108108641c40b40e0080050900b2101241c44240480510402d50611a08c43d4080074042a8401c01c4600d0700c000410081d20581d0189003a40840d140d107800100181001c40c0300c550b01c89c442061662100c0c11442508410b6507088008000700e018052031182a40e00441d0300000190081081080c944c1980c0e003d801c500d9030842c1124140f86070603046215581c010780020408000035a43c45080352061009140d0001b0a4500980c00d1031a2000259440346800c404603c501d4507010a47c00c40e07a420b01d01748004202c104020b0031903041951001d082072410740a154001520442902d01c00181f407901030b13000c1c070440050186098a03100490f4280ca10b4070341380030000284c891000403500c42d4240508412240b140151628015218100c0c0c01c50342c2820 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 429498902 1250 429497652 429497657
    0x70f15050c0c1014010b180a1701140708071404030c0b032401050307050714120c10050103050d030e0c03010f0f0c0e0603010b0912030304030c0209010806090717011104031b06 77
    0x10254145140c50206031350455000750704003611081c804407800c0c00340d45107800482d0000b00f00c2d41d0000d407640a0042011114808130020021710040c0b0740c4181d82003008940b144082544203011034140c40c8200c45c00140030341e04c80070050515440b41c1d100030a00c1342e240d2000c05c82000210610181e600d150001d00510100341e04841c3c004a002c0c0000383c20750100400110034050080349100a00030403686054100ca03550007502c0c040018048095025003040031140003d21844030491030700400c52254a0599820000821455051a0302100604004003004030030713000d001c0c1445a07a0720700b4001e000c50030119141c0414868800b81c44001104c200c043d00c0310410110303156039202921800c3c02c0368191500c0380301141e5a40c000c8000f051041d24100b004204500c0000104414541c1c80813664491074821110b04201d640da500381540d0b00d09013915440d00c140c1005100b0007a010b1100d40c11a5450324090000c00c50406c0c40258030741540040d031045d01c100714140c00140081d02107043c241d01820850 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 429500152 1250 429498902 429498911
    0xb0901050405150a0b060c16120302030706020a032c0f07050109030807020d05151509010b0a0c02031e030d0c030501060c03050c07170a020109050114070f15050c0c10 73
    0x20345445030f44400d18104104000b14180100d4000000c0350011212030790701600e01513964000020140da20b180c030203501d045a4080c0c103804111025060a41030401e81c150307004606080c000d896110095025100c0e4000b40b656030446080b0320541040c828500041c00745004290001d440c4059007485400000200d49402061003400240e800003118420f6039045044540c80e203410348040ae14106142001420501c0345820450840905114240c81800c8000e2680a105507aa042c0b00c0e000c0028050007070b41103800d100c0440c0241c8164004a44240014103c600040b6260441c480d400d0580b1044289508001803041112740c1d036000d04460310741980f80800081d8540880140a80e0340b0045c020104800001e091040716010409903024003516001c040805012040c2a55201070b0200e040340441d464100000702d83d03018480c101d0320065141d03030840c5018039580d80c0b010280a0312004072108292004100c0171540305119a902c01c0620401490790741521030099480c10945100c501d01c100d040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 429501402 1250 429500152 429500161
    0x10903030f0516110102070503040f06090e0411091f0b070303051005010207030b1e010603090b0702150c0717070602040e09030405130b01020a051219091d1e040507030b090105 77
    0x42a0000f550300500d842c214169022926079240a48240341010f00144001715001c0ba111609051070740480c0e820351a02900c0a0340c803c600258072404860240503c01d26004130130f03036410b14003802940884180281c141c440144180c40754145901d402000c070a24000c14400c04041c0c052003000e422400f4560b00f012403c0c94400000e60340c580c98080180071212842c0400e400c1c149030400c6007040b0111150b03504c05503841d050001c0c020440a0000e40d91841c0c001c010540c540e0000c41e070480e130750690b14202540350380c50742c5901440350300c4050110380004140710503480403000840039040d40c43c80b5850150340d407440d00c3c0700140e26401c007421240103030f0020807040140e030307503124003450001171060004643d2541030001070b0b080070704021002d4140e010b040194250700001000402030704100c034003440d400c000460030448000d4900c2c0035598650a148109150701c80c4960240d90b44242c0400e501201c12411260b60820010300390343c11650355100f20818401c104031051801d81c0300306001c0003000f66103003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 429502652 1250 429501402 429501421
    0x3060906060f0109030501050f04120e032505030313140a080c190806160909020c280c12120e011e05090301020c0715020c030601092c010903030f05 65
    0x1020789100d10410001034104550b9004d484490000c0d034114008012610385483c1311103c080d0126412285018404000244d1a00610345032107610f43c0980102000781005411070300d0241081c0d0070315401401110000f903a41d6040004140942c42c2070340ca288400e16010010809a080c55052446821940d8080c454610000b4100c05000d034200c811090215004040a0744100032340c0001c0d82e94041da0f07080003051814242d40e034000b81c0081c0d450914180c1d6642808040340190005815590070480102107100b1590005d0701405070241981203081400d6600c10030024025400b000342c121000a5500520400076411501d40c480d80c24401281c40d24403000800584a402c1300748107000e0b94021211001d4403420030b41c0c590304009002159111150000941d80710344501c00c03403814410030314003000624030110f42106e4000c0081c0041c441d60342407140741c8000c2c042d801c1c00e0051528140210860001c0c200101e5984440300c1c0c40001462001800e00030103440694860011181c10030042c03040140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 429503902 1250 429502652 429502663
    0xa1202070b0703051303061803020d021b1207052101110702011707030f0c021e0706050a1d030109030c12080c030a0e10020304111201111b012018030609 67
    0x1ea00d13140c80ca9a49242141002941543d500041e212500e4a0020180f4543c880c004252a40c0207400b180e1882c08803a5049a03030f81c0b28003400300c0f043c60740301c01013003076500f0b1000d0180c140e040d00e04c0540380352a48070808613442c041c0300b40d41c240301c0c1106e104940410035028450109040302d10760310540f5006150300041c01c880900d4600c81601e034000300005e000344e803181d440240032080d01c1e80180706a0081c00c030025650203000d070f61086580d1008501c8901c0810000c1c450003107070341549900d400c1c00c07240d00050b40c407071413407030800314894101c201014207950782846200c070140d100e83c40354600c508403824012004807041001d0014040d2040902812400e04000e4035800700384c0340400710300a1580b51410b828004100300b0944018008400d1000f0030041c18495140010b05070b6041c8040b80b600384a042c240c6080c01001c52860310200a54607450f8551884000e5090b041d030008100c6000303815504003103404164a820a0f1100410100a1000081c001801c00b207030840007800641030046059850302e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 429505152 1250 429503902 429503917
    0x30c0a050706020702090109150807050913140a0b0109050a0e100f020405090a060302010e06160f2102010c0e0d0b0606280f1202040311010e0a08030c0a1202070b 71
    0x4001c21040d04200302601201d0000341d0242c030b4103030f0559440c3c1e062400b400030402001100c0840300c0c0040f404010004a40046030402003c4c44a2034075078000d081c81801c811601911070300310580400c1c00f0020104284170545124661404d401d40c03601c94200b0864101074a03041415040089401000c400002c410b400c15600c0740700010307100001460107000b4401c07a402942c06c00c003080c4c108088003005501a008881c000c2c0c803013045010701c0c03a0421905100386694a25041d61094080022920b09903030003050f14403031a1023040000c1c1040d03e010000040e48a9000182e445510110955601402d480c4000c07206403103003e2a0b140c583da0304100c0000c02006140541d001240414000000082d02c0f002078004030180300741c0b1012000020000046126a0000f080c2508611400d418182c801c85084036004540c9882c15004040112020304208004c194403007441e190104800c041400100743c443c80860040084444a1a04017216501040002c081d0340040508200a114050451f1002c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 429506402 1250 429505152 429505157
    0x1501051f0e03100b030601080a080415140d0f0e0c1003050c0f070f0605010e0c090d03020109060216020a0f03051207031e0845030403050d020d08010902030c0a 70
    0x80a12840c1115a6002a82101e40c98803580110705840c500b164400382c2030078000d8090303524681c2c8400b040c90782c55501010003021450200010050031303c180318581f6043d02d017840d244085080444a0200d1768000d80640320f821992610200b540410600c5403c0e4600aa107014064000700d50000910742020b0b00e0701001815241c5e00003500070b07848042100e007036180b0184e080361107411500b07041c502403208010840d0040d00d032600110302c862082d418184a5204403906629040c030803800d100c05100c42c0b55048080d07649074401d49000a8180c00940803084c40803201c1094030f2220300400c089407000ba40b045401d44070880081c0702286011581000083d20100002d0b5201000d180841e40041141d56400b800c0103407080201c880b5900c05002030040c0b0064206002c440413130908403142c010545801020340003490304484103002c1450380741c0361f050071110030b0300d0030203650b03454403070910844000c000c0c0140c20007070b406050300c4e402c252094050042c800c2d0460070342c0340004c1c01042a1050705c000700705 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 429507652 1250 429506402 429506449
    0x60a0b1e0f040e1603050f060c1804090809090f07030f110a0e0307030b0c030a0b1e0405061201111207020d0e0613080f0606030106091a1903020a0e09150105 69
    0x21003010002403080e0700291000113041a500d0800710b803240701103030052109020b8a008500a05e00400c15076828070410380354814401d644104200007420345681c01c0300c511200b440802c0381582c0f00350145108840c808010005458000c000404079142c6030a600c0c0341e14641070340e203014900f508007650b104119a042800d020414100024035000c8503a2000f010303c41500304006c405c0c2d50144c050342c0594101c44040c441c942c120340810640c05c000b82082038070540d0b2651408030b94601034102641107a8007a10365201005800b40c00c600f5505d002c448c44240450010310200036240030036500d0f91102e03182c805045400c594210042107414001c003418401c420100c6c0341c100400558240d10010444441140e019909280704181c8030041214101c3c800e5283c001c0000d40030300386000703510f40c0006080311900064000002c00210452802100c24000f030360300404401a255014114080c10200e00c16460910340081028504031025680d40104800341e001004181c90300c09098129007201c07101c03041d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 429508902 1250 429507652 429507671
    0x31e0d0c0804140315040606030c060503130b0c0c0a110907080606040e04021f0f0e03011112091c0504140a0605040e0a1401170610150f0c0203060a0b1e0f04 69
    0x91511702407840b03040031a80710300140401c11025600400850384a0314004140c0382d0f84800a441c1ca002c11030780d10130850000b58003e0001000030700b07101c0d40808071584039400c160103090218902a522a42103a840703409040c822118a49000701d1a8013402c0e030f2a05021a10380a008210507000314421200c0e900740c100041000c5584201514600e0722400b1118580b061105400078071a1101004200c00f20300407a4460b286814107000c0c950030082c150321402c1c036055882c4c8844c024244014894078003030040700c842c1025034032071021a104980c055074440b506c03030b41424801200c1007422a0303001c3c0301300382442c0100001d54100c4d042d00c2c119103141d0841d0081e0b035590342d055009040c00032f40d01031b0b180100d40300106945190003042c111001d20b000490b0380302c2d602c80b011100030100701d0040c1c02c000f078060505400b16500c030f50030030804c0c0400303454a500807404960109141030419610902003e8649081070002d06025001d050507600114050f4480c0ba030540c00700d10580b04030325400d80102d465983c0030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 429510152 1250 429508902 429508909
    0x304031407090203160807021b22060b091215010302090403030b030703050304060e01030b0321071719030209010c0602210a0225052a031e0d0c080414 66
    0x141d000b0700401105541e64a0300600081408210101c0c910115000d440803601c010f2001807144d103121405807a41440131000d0b0104601c1c1629008190415001110340350101021801064000d100410030b81d034841c1d503004100700e00449903141e01d0015030b010140405200d0350340700303132241140d40546103411240c40d01e04040b00038201038440c8039050300c03600e5400420480c0000c0140111092542c8529510003040011010b8a0307000359002d51680c400710301d1140071040b1315480c40c0c80c40071500c1024500480fa90351060703121207a0921050740d200114600b0010b01c00907100d00002c07000c510f03046150120f64000602221300c00780d4058045275021441d843c0c0000c00c00f02e180d45000265a40f42c04030700c1c00340f4868001c0d501880702480ba0200c01800348001c2d2116412044041d940180517001c00700006610400008407000c90a0703a080580404101c50b8905020300202c40e0086400d4941000000060500d044c5d01110300c4010040490350030780100345480d040c0c5080d03d040c000c006880720901e0303000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 429511402 1250 429510152 429510163
    0xf070303120e0f100f060b0405060c0f100b01090b2a070f030b06150301060804080d060306061d10050d0809030a05010c081e010303050304080c0a0b09030c120304020303040314 77
    0x11000d105620800300b1104000548107084c3e00307071440600188004c1da01318400e84846204024170910103200038000d0b03203480750180445004c03944c2210191801801e032580340684503094903514a66074040340d001940d011100b0000b40041c401401d18007000030304644103650041e20306100e80c5040541c1004078910511400e402401c00c140390020b801d0b22030a010f10f1000d01540c030b1034821102286114030142071542660b049505507114105159a180c81e01083c0e54408005200da8a98410f030100005038684940c0010b031001050001485042d2200040c80303507400390550340b1401070302004014559921180740181c69100c10b07600d844003600030119203004968603004109500701010551400c0c1c0c41903865110701801481c1e045408100860003c521500f0701000d000500c0410020780411000d9004080d1f03650980200c03004030800380c4402d00074207000d50741c060751307900f001031210380c9502c04000c0340504540c1c0f0035845255003002d03800680d8038815480018500c020140440040d81818001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 429512652 1250 429511402 429511421
    0x609050a050708070e130b0f04140613060c020c090c0f040b0307030207150e030a050f0910080907060201181217040c0314030306010e040b040b040906020414030f07030312 75
    0x444058580f140304103511401680189940f0116040000d050b00c2020721101c000a604020000c1c0740d51291580340381c1c0d010008009035600c51140e81042210b84040103941d200329238480742c1c4464070280f0b151000c117440c41e5618040456002003180800c41d0745007e00c41c6e4028800e082e066649141d0000d206c65035004903840780008020200c10450030703030f40680003480300300d02c604500002c004107800088112030703011683d2255544180140b01c0a86c0c0910010300080d141d1403000750800101d00c0c0001e2221001c9188100021130035428444c104004025540241080e400240080c80881c400c2110362454880090705800080c1c00307429440d4002d80c01c070701c0e11400e0049105c3c400c2c43c2500340102c40010b107100481e8032942204044503a51800300903680034500595038103103e00760344c0b004c22010308258840d07254015920240d02c202980d13284114024a0310030300015845a20700130581001c41e01e6510518004d801180092110041c0841c00e4002e403541070030191752a081d0b001202c00103125800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 429513902 1250 429512652 429512663
    0xa060f03150f05150c030a0e040b04020309070603050915060607060912050901020706090509150a090606030504150608030a1d060a12060504020c0a140c27070e0901030609050a 77
    0xc00814407a0001240c0d00590f60180c54041c510401c90100001a10580c0444465034109203c0c24052034403d601000300c00000070310100d10301c25403400040890380706941002d41940700010400080d074041c02000d0344820f410002d410b0442c0f00c0800d4807103500c4010449480341c10f00150301c50400807194400a2400d40040501144808003800605164080b5801a0252156440005010348030303440442c19544041c010400d00e0b120344a841c580304844101d51a88000754890200d04181c052050074001c20140d940480c0070304103418050071380c141c011441140241018024003200100000301d4015400714034000601c1d0b034643d914085c03112880004d00d41e006500050b900d030169807007507408101c0c4076000c00c00c00c00140d4a0341080101d101d84120142680c10000d00d400114100640320400c00c1d50350b200381d0b170003640e4100000e14600003003070035145c1c05420780d8107031008103501d010200da020b8a6401e1220088c0850000911840390500c40282502d881d40130050030440c09104011603685e001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 429515152 1250 429513902 429513941
    0x40b090f1206180111071a0910110702040e0105010506040b0f04080109030809060601020a0c1505040801180b130305030c0702030c0907030f0b1906031d030d05060a12020a060f03 78
    0x103120403414003070340c0741100c582d0b9030134404440803480141d000c45601301c2c0d11240d041076845600c00c685c0100c540050008c60395000325405c110031135505000310001070000c403180032b40da07511500c1008111441c0c0000c800f0540c1c5404014401c03600c40600f00d8068030b040e0304900e80ca588c2c041040b071085102d0b94000003c01c1d404d02d004030b0209500300f8801030080640800380c9180d55038680c01280c0c2ea021404000c0d14400940b00f0801c802d190140c0e54a02004591401070f250079102c0101600303407181500b60780c0400030442800408d200240b030780c040d04504009458943c1d0b8040ba00c0040c07060001070500c280c240760000d020011550108040000c081029040010600d040d003405801040501c124111450070042510654a0b202c8060f8a0452904c280d0f02200d505125085005081613180701d40b0801c62601d170310b007090b042080500440300030f2010104107454030000b031002c4502194040030060006110040c0184d032480410000d803401840c01c4004221840c00c11000b42040120704940040032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 429516402 1250 429515152 429515161
    0x3040b0f0301030c0503010507120b1801080703230c150706050403121a1f020f07030f060c0e031b151b06090d08160c021e0a0b040b090f1206 62
    0x390300618102c0c0d028403041000c0036540d07000e0600360386003200c03c0e80001d2425114180c84440070344c880119a980900f80200c0060000702d40700011b2000c1e0800815a84260f81c00c00402000b9801c000d0b0000101d451007600d20355401c0e0f05a83c442d00d84d064a40308841c0340100700d10952061090783c2c00e05810110612890600d418058400305032808188507050401003140304a00d10709403880900c010281c030f041c006203003282c0d04680c1030070300c4d00101045000707158403450b201900f003180402550040380015101c5036185003c0007290000103862003402801a0340c144c0d69500450091000d550f035200001c400038110b400030b0b140c1d00110380c441c0007050005c00c0d0707201c0d0340920000c0003407041d1000088818640380c0c110340c540d07580410002c010000c0d40d0b40d00002d02d0491407881060100003e428070011043c020b500041450240b1000100520360000304c0841c10310f070860700040100b8900038603030f2403d030a182001002d4440c2c01001401074229501501c295103404866904105030f41007503c955050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 429517652 1250 429516402 429516427
    0x60509060717030610020106060f030905010204050a24090312120b03030c010b0102070f050607080706141503010c0903151109030102040b0a1d061b0a0f0c08070e0c0a0c0503040b 78
    0x400c1c0c4d013290040144400c0c03c50b103030b401480344c6400d0b03032901d8030703103503040344100c20708030060116841c048403155001d002c00125500c0740d032017481c082c0400c2c50880c4900f40d002d2402050075286800807004100c00000108041060182901c646005034075140001c01e2001c03080002a19100c00314542500c0001800e0140714410f52000194040176402e4800b820f41e26185100903135401c0c0105a441801044114000341c020303030044c400b480c820b03040031030b221030032241e05150008102c4154440007026006440580303420f00c52a5091000740c1801d8101c641152101c1105181e581c544c041c096075a0461500004004010f81d8000040140255580e60700e58401c140b04d80c10002660010172400c0f000e05036020324030507404202a101616403401d00b00f080340d41941c49400c0c0c4240daa000e0094855460100b0034a00d0f905400d0f038082c0c10500d4074185003440f401d2514000f0b90041d5010580501440b003988540801c552608000c0e181090100d1001e08005055101e1503000e8464048001260001101d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 429518902 1250 429517652 429517657
    0x30f0216060905100201060b09040c11030d1a0d030c03050d0908161a070c03030902060913060e0c0a1d0109180615051602040510050414040b0c040609060509060717 72
    0x2081034130750021080ca400d80507820381c3c00c14003442d210f4078018072400703c46081c294004008048a46001944d82c9041000307135003541d0040814101aa4448044450014540001c00d080c45800d640b02d803050012520018149030148400608101e8005549414000b080d0003140e112a0404607282d0b035990b00d5801010740c00098402101c00e0340e40225001f028104174031070248180314984440450105a64003180181740710107040340c0c400802e0000002c41e44466042e00341d03040740080001100c509006803100b608900a21050015608000c21440305600c01e81c101d401c032144c01c07080d11142190301c006a42260140c2c001c428000b04041c280e040d200855005101151901100176510540c04032003101c50380b184080c200c1803180c1c07024500c401410f1035404903500207698000c0244441e1280002001e5603481e0340100410911442444280000404403903040f10740107860a250070320344680901010740700c1c441e034002d02c0f02c0801c68010907100c2030200c40690768480700965400d18540c0c410450394 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 429520152 1250 429518902 429518909
    0x6050a2705160c0501020f071109010b031902161b060f0207050d11040905030a050729010605070822061101060e1602150709051813030f02160609 64
    0x100444080d0110090840c0304040c000e92004070445802d05601e002990038403544202103c040d03608000043c002e41014005d059201d22880245800190120400424100603005003c00c010304000b1300084c1030a80c26800e010304203600c4096250325086801185c0001c0c0b00c1070240a03400d41d170507015005c11800c011882a070349685c55602095080d0b0808036900c3d4203900400342c020113540e200300c0115912074005c03641840018001304108900d0ba03078060458002d54039890100300040340b481c04001c03200940c160078020b0041c1020440c200030120407420b90b0188280c03c140320001601c1401e012440c421551b0001c0b00450700b548031041090340c54442425442030100142000d0382407940b4039818040d000c1200d0580c103002219490b00105100c2c1902c0d03241042c801d62140e848603030400140501d9251180581e910303100c3c4014640701c2407008400c0340103040c0150a03501c204001404d9444400d03a507500d50503140090041c4103c40042c0e18160603170f500c011b5000c00c120b0000030700700e41c001d5030442074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 429521402 1250 429520152 429520199
    0x709090c031e05120711010305091c08100909050c15120c130608100e180f030405090c0a020d08130807051e010608070e040c0e01181808090405090106050a 68
    0x300390b9481a050207000711760000b0821640240f22841c50345c460b800094010781e604043d21f6000740c066503c015540001007620012401c0041000400e0008100440c010451010140190302c165540d640c1c40e820340309a00780c424160940c0f075252111200094408884440624000b1400d208410140c190441209108561514800461418855291680513100f80c800300c018080c10701d04040f210990050484c46034205200d50340900301d40820207803100c0d41c0b002001d1a50703241072009001580303000500d12a24440c003004004100c69001403040b0b04490140b40200340d9496842d00d600c1c040003440406000040c0c00325858003071180105244221400d021004490002030103901c90a030380f1640f00700041508201400c115410980000c05e80c40f40c450340614007400d44607040714110300d0003a006003c074000d01050009140d0014881c8a01c0c0e10710062400c8030031003d81c0c1d00d0110604c114210f0a00aa031510b0104080103004d401003005040014059220640c80f41001c03100140d11150f802107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 429522652 1250 429521402 429521413
    0xc0708071202011b05012403020f0904020d031103160312050f060d0227040f0302060c0f030604091103010c050904051806010e07021006030f051b030709090c031e05 72
    0x44034052420407001035036040c1c6404078106003492180e5450781200009071202d5490b01c903001c1100041e08284c400c031100e25000488254214018000d0080101000c02d01440000c414000540d65a65a55043ca6850702c0c00c0324040480e40c1d0b5140c1103000c0d010074030b00a030211007145ca080641040c0e07101211400c2e0141004a0345e29501d2024070000e06581694000030010b08e90360141c01c00700802c031070241c0500d18a01d079510710545401c070714140458040e503c010029070b00104044d41030113403d4001310020300040c14480c0700d10031702c2c040780f002a00061280342e0f0344803d40c007003104014500b80301e408010002c1010400b04100074056a000111051007070745000001003417040c45001c4071491083c502c00405482c0c1c00c00d03042600060000d86100c00354864415051030f5a41a8040d640181d84107140b020764044c00b6181c194541006074141d021082c0a04001080c40d40300041c0b80710899202103000316a243d000c0c10010241c00035508090540c0342c1410b040d003600c3c18400f0900741d49510910031204c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 429523902 1250 429522652 429522659
    0x301090b090403120e03040308040f0518040b072601080304090b061201030f0f0c08071401020309090402011808061003030e0108010f140a09021803010501080f071a040b0c070807 78
    0x441907421100203000ca6001840078240e00c0315035000c07030420170380c80c000c880c0350580701e442d014082e8000d980244020303d0200c00c14806803c0509400c210b903c0c11a00410960400c1e94030282100300c02080c860400246131081c0c00219148104134504c060105181005540c4070700b9445c0c0c40b54030030b004480c20182070034041c03c80303420003074100e5108012080450282d6400c540c1c0d4641928120601900c06030098100c0c4070120b140c4c02c900f24010201c80e0700805844c4d15241180001011444034141550810f101e100368079250240510382c0980d0920702a6050160500d03aa0030100e1550003050700d5100c0c2d00104482074090300d5a80060741d000c1d440717061507c00780800440300030b64240240d520488032610f04104001c02c004001c02c02400c0101104204c50307e481d034690480c0c04c002c004009a8001d00341c601c919007020b20640c0d014103641005011404501d031080f580e280b085200d2000c441c8001001030600bc4680020b0350080d0131000710003035a0f0004075021035a42c000e9401444858080c401001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 429525152 1250 429523902 429523909
    0x2120304050108040611040f12020103060906050d0b091e01090c08010c05040b030c121e0a0501050a050111011407080901050703050601080402010518130e060903071113140c0301090b 80
    0x8034101c8078140c0d2218140da51341e59404000e4076180b000d0260016040c0000306100c50507003034401c00341c01d5102d51000f003801e45000040944102d584184a01850844240401c0c0c542a10105580e600103000d03a8282c0c80300900a440e10840b0010361542c2c0c914083d90908002042d080104603034010310a003403400b511112140e08032608242c9080200300b081000b0441c040fa034401450b40b100380b01c80694184100f00c0780508044004446034090340100610542d0744102d2004040c4e0002d016180030800c0c0d41c100300200720684081c0c0500c1d4140180c1c00c0d441d2906000c250400c02ca02c7c40c80655280c11820581d0300509580e5007070720b11181c0d41d420400014152417007440340a1041c20140e450000c162200d030019101036000c0601d50782200c0ca044642c03015501e40540482d843c060318513000507001c03a40c0003000d050400142050400750420800400407600c60701c0d4507601071000300d44c4040c0005c40010210002c1074410800e062016a50080000380744629010f103048401144090142c40b6184081 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 429526402 1250 429525152 429525157
    0x90f0609060a0c050313030b06030105161b02040618050f090a02011d01170106200a0506010314030c060916141518030a2102070308030a0c0c0b04030903021203 70
    0xd4000c0014005100d60601c80c9582c1d000c2640108256071405881b00d00c24880841c842d003081d2103480c00b139418003420381001d204140c0c0c05160f80800704900e81c03074040d000b89589201c044104107107615418003010355681358840401000311030450120b4000900200c2c010b00011190002060628030001c0d00d0340714003088a0030031940c1650340c0c413443d000300e005000d2484018071038941000200d904840e103501104038414080d01c000c0e102c84031031410614044031540c45150641640d90000e49185000410024582d41941d174000c01d182000c2c05a510054510f00034000060002d100d19014000c0c016404102e031154050b202a12040b0390742c031050002d0b010900194000d82110901240f03141c40c10804020b80500950401c058801c20505d90000b403415100c3c2400391007030550320b65888450350048020306510304031030018005d07540c55903d901d0054000140214051915214118141d030701c2070711136004595110203150414101424000d0000d00705000c12401041000c801d0300090400105 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 429527652 1250 429526402 429526417
    0x140405130b063001090c0605040e010920131409060102190204230f16080109020a09091d0c06030c1c1803021c030b0f1903080f090f06 59
    0x60848151160400c0c0702002820141c60f4100346102d0700c0c026000c0c0c40295085414150f14800802e00e401c0505000c008610341c1c1e84050305005007000100048501c1440e1641110882c6500061a10050b10b0300c110070401e441c01c50703080c0301000500c0540c003c4543c002c203068074245d0f01030020705080c1ca03082c0406000155100ca01503840031f0619644c041c250300d40950540d03c0500b02061800702e0348003e419900d54504c5550055880c0420803030840714030788a2070391203403030141d16101900041c000500b060206001d041181a0001180441c2c5405100c1c4a001020300c91010499200d101c1c5040c01c1c44440e04142c08002c0c02010700e082c09130b00e06842664003407008000c506203030600c8613450392001524440041c000984400b4000c8040c1c003123105200704280241c010744502d0008840c000050b41c0c1c0104440141450b04040301426203071541c0c000072040060f00c036015450081f80c0d4964980c3c441742d200030424800000d0300500c070120000500007044040e96449440e03000001000b816002d223070b2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 429528902 1250 429527652 429527663
    0x1061701061e09050711010515040e03070f0206161a070219020307090f09080c01090212011803081909140c04051506130306141e16050a090f14040513 66
    0x110600c44100213a00035600803200f824142030b4003c14040041c2541c0f400c54101c4860b0071100807482c00e50038180140004101c00c507002c0c40c40c00c40555188807107003003a014080e0090300702207031001003603801d52240b1300d8041e0461004079014508002c01c40d111001200c640d80103020300b8250060b10903801385610016540200500981c608203e240c80c02800b0240c03c0380d0060fa154104000850032038001040e5142100740089081c401c7c43c01031102c403420200d00040700c1d0380740581381d100080500d08400728035a4189451011910b030051151014032626500c0c1218500c1c0c280b0a20401c410110254a03601120099501d2020040200400c40e14100c444105c1c0325801c94032903089141c6140140500c80c01480e0b0161181c1e2652600340459901d2501c40e204122680203112100303001d00300ca80d100629441030248540342036100c001c03091074070600a50500501241411400340551700c820301503e84828159042c2e6500c070021859010b16031091406a40b0703003804903c0091400340401e45464002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 429530152 1250 429528902 429528959
    0x501051909051b18011e05270628052b02060d110d1a0607030f0804330e0304030c0308070303140103080a021005060d030e120106170106 60
    0x10f080c8044529208024503074032130341510360100f40c81421011035001e0260200800a0f00d40d42080d040800340d0581c01c40ea108044558501d0080b1080701d24a052403d208071007e04c0e04e4a817075001c40c4504940da519460b40001da42d0444009441c1910303514102c8500315010b5850703054000e503c100c5000d58841c10002c4e80f00b00c0b85000058203090004041110542c0310006003914a40f00000d803541001c2c00030b82903d9281c011075004005003c500030f40003c0216011841d0103d1640c0180810000c45482818840300b180040c00b0700202d10404421081c40d611003002103006110322903440c080d103c1528140c0361910300114418030f800000c1d02c0641e0f920480c606213403429500c5200c007580000000f2070400d078503800307207201010403006a64021446810465154015a000603081c203031894145640035103064100041c0340d40d540c910001c641e40509040229a8803100800d440010360340e1240500d600f00f0000069100f0380e0341c04980c04104450003045a142c903a001f5640400c01203400041c9103518 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 429531402 1250 429530152 429530173
    0x621071b08090a0306060b030711060c09130603020405090c1c0506072d0507020108070c110613170303060a0e0f01060e010216090f06060305010b0706180f050105190905 74
    0x10000c2086100007042d024501341d032a6030358426144642c101c12140c04020090100ca00d0700031001c00e800c52000b4000d01a145042c0c584140b540c02001c40386072140d100f124185003d1505644414095600035105000342e02e071003c051030b51076203003a0945000e00c1045d011a09020042c045170883d503540207000d042c1c15240c42c03508071440464516a619121441ea440d540c100c0404c920741d50300d40081c0d8a9150300c5600343d000140150f08001d0644080c403400414400002d00c0c1301c8880c80a05604580050700d400c0c00700c0c54203c4003031190300802d6581031003e01d0a21001000030155205d4001200c0c48280e680d12207181c466000829500f51071044070301001880210f01031500d81406d08030602c101c500e14968064034003003004082d4001d5904aa850001c0100d5030306c3d83c060340d8080d00d0f090905101c554074092402000c2c0c41110b1000d40420360f501a0766000e010f5404418030707a25086044911701c00c60f00d0811900800040c2c40716100c038034014815030841441d6002d210042d6812a01a2003500d68 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 429532652 1250 429531402 429531413
    0xe01120b04080412051e03131e180b030f0f0607080a1803080a0524100203070c080105090d030c0c021002030c0102180411041a07020d020621071b 64
    0xc0140040b42c0c0c060050001003807541444840a0049000340010070582d00020701d41c18401007050141c103801d8104008401480700c03804191400c0310100d0741c64040b20f00200300207225900d410380113207402c04900ca1204031024240d030861000440201d050301e000800d60722502d80c0e286840200c60103550882000200414058040544d00c40700760600460a821241e81c2000000800e101c01c03804911100207110b03114000d889010391051030640c041410182d4000c201c81c041980d03507500c500c00c4079103c00e0440d52510038010344141341d40c402140c655080e2142004c0780030340300031a034080041c0302d40103120b4002c038424050324102d0384450729010741c011a69000c0c00f045a415000c0340b800c0d84030170415518a4982403005041079090590324411a82e200070802c0140e07000c501458065810500c0305110090350469003031840d080c0310750401c0e9691450301c0031480031450181d01139400700d0081010501404103500100f04107481e20402895996410f0080c1c0e819481400450403000e10345507034400240c0f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 429533902 1250 429532652 429532673
    0x190209070e0d080c160f0503070302061b070b0c060702010c0813050f241608010b030702160b041d010812090f0604121b0617040305070203060106020303060a0e0112 72
    0x350050300e0700c0290b41c81a100e486107984503513510843d076403240b41407242050b65244150050909603440c44042031070500040d43d20340050101910504000407885800c03a21845000c0d22140c446045e00c0c0c0031961a04410402d801c4006001c000340120030010700c81c24410302c2411140d41c071503106c074000358603040b00c00c80d9520041e070f004548030703c0b4442e24070f040100c0c00c12160040d007980b41010f042c840c003680d000c1c2100100180c40e801c00c052000e0115101e0b19000314507141518001e100454480d61801b004900d410445603445d00640c020000200d14407080b000103000350303641d81e180c01d81c107003131f081600011840c02449a41da503074100002070910414040300821081c2802000710686103010000103043e64096172020140b520215003410030000c42c50b5903000003100504900c1900c902e0080040c1c18800c80c0d160100e0480c840d47d0010303040501610944a02a4000e0100c0b42c180da1240e170085e55a500a031403d52040040510024910f440c0900c004c0c140c50390120800d1200110b5036030406c100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 429535152 1250 429533902 429533927
    0xd1107060816030c1704060b0411070203032d04030b0708070e01020a02041814010b01030b09101e2408090106081c0c29060d0b160203250519020907 65
    0x400303045d415400c1404e01030f00901582c069400011120712880c100b104581140041a8244c2000d1000c200507075004001d85040201c1c2900740c042c2071100d0801c1d00102c450b038030004400b00f040800c0120901c14460040e034030070481c1e522000b401d610f80210584030303484101131150042c2c1c40903940b4001420140c11500c2e100c05041a02000c070500e6035141e1642203100b91141c540c8d40c2d0761f61400a010340e85402500c298880540d8007001c5400d1076000000048014003a00b400300291414400c00004070031404070040141e5800010904200320b206072100b1541c10110300012001808511003402c18844c406c00c842201000744121250428800744c401074840381c3d03006004a1640302c801085209000c00d0030071001d448808442c145100001c80c4121014000138005e800200d421000102c0e00c0c4052034000c1c640c0c0b02d62a14000e44e0f10004c0380342d80300e01d4074031030007603042ca102d5882059505031040c1103651203401554000d407590001100c1e41030070b040b0081d51044144c00440c46c2e180c00b034100000301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 429536402 1250 429535152 429535157
    0x16031e060b120c0310050601050d0b010909020d0209040605010504060203070308060a1703072d030e0d21020c030d09181410031407030302030414120d1107060816030c 73
    0x31001c0c0c0100240c2c4800c2680b00030312043d0000941c003959440c0c203014458040d030b20003100301704505080d00020b205004445c22090100d680d0102614941e004030316070303401008403000540d070316480840705c04040d40185407028001c3d428400d01245a40c007640c161000c0d10250f80c02181008201d07101110b0703204002c2c24040d00101c0281011501031034402ca4520741200150007103903541014504500e0b0a2100b6140044065442080f54042c0d020405c0d106001501440e000780070341015000901340c0444554001d0007100319007a400901c64080300e240102507400c2d000e8030f0705400f41c40203164582d0700b04040c1e0800140c04070014428190340784400360080403002c00000e840043d021070b0280c911410344000c040349a110604004102c40c008501201c032501e50007a0800340d1031640e001e50341f0702443c016030200c8208031810500340e450b0b50320300024010501041b83d20a40c0d10032400f82010240e03080980c044e0180100104d940ea0140007500d000368103074042d01c0c0c1d0b5201a96401c900801104884004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 429537652 1250 429536402 429536411
    0xb07150504020f040c030617010c09240305091f0b0a1a090d030c050a0c0e0601050909190e07090e0d05210a0e0102031005042913060b0d0e16031e06 65
    0x440041d80300400c15080008000000e411402d075030050000e5460390302c081c40a00d000541520440034ce415081501c880c14180410f50340c440307800742828a01c0e1800c0380b00302d5000c41020141c00c2e0b0055000706d2014041540ca00480d162107181d03503151540c0d0030348207000d482c02c104500c80c51801c103807010400040c00f03407404281056140d0b450b581040c0e81020207440711380d042601400002403c10b4099000030003401c2c4107180c4950800402d40c0210010040c95403124210900503070308503140c0040d40002c4108055590f41a243c0c81d44100420010700446014461200c2c01c030b92250055003200d00802c0d0048071003108184408501446c00c0c0000c00b802d452030340303916010300340b842c00340041c0d80548500e0038182c1c0e00340d040c0300510007241c1001a0b03c40384851aa249070885060031114101d10480954410030b141e062a8040b0000c0c1000382e11154100d8400101101d100d00190320010300e9052003001d4600d0000b01d070000c4241c1c40d100307004c090164809616040d0150040c0740f03003550017502c201c00204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 429538902 1250 429537652 429537659
    0x70e132a11030f0d0c0801060c060e0304050a06050409113408070b0f061014130302090126120d1e0c020c0901090e0a020d0c0306060b07150504020f040c0306 69
    0x41c1107400c03d41c040810b01c1d83c04142205400060b014000849a282c030b8103491039031400000804003001e10f00c010301340c0d40e520a002e4140d01d00070301c222800744c03001030700c1c11024a66a4070300402c2c50707026101e9110510301c0c12040da4055214401261801d8480c075801c1145590840d0300064540c4e0a000760103102810b40c2018070000c1e06520161035035a0140c112090189400b42007078880c61401441f452050100003040303002213421204070010051118459922042d1800700c2e1206940a40c2003e5030000240c0c00020342410200b415203200712a03441c61524404007001910390f1540c0c8032080c08200c0c4c800b80a8245510fa55074070106c0a4140222941c0040031015000340c00c485000c101c041c01030700600507504185c10200d40c1c2c00c2c01050440b00800200b48101c1d03d00c0d44030001c00c18001d1154041089180034042d800b1a1200916004001008200d91700d40340c911540c0c3c0941400ca449079048000685c0c4900d0a10850340f1880d00a04102c401c1503000040000034665800014103241d518400030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 429540152 1250 429538902 429538937
    0x30702103603020d1b0b040501020c100b0a090b13060303030c110a1a04022803120809070e130f06020a03150602100c1106070e132a 58
    0x2803400c424809503401002881201c10355840c01985000580458188807500010760300146201c1452414500201c080c0e421039803010f14a43c6002e406030803178a090080c001884010350003411072100c42011a180e0b5404d41503c0011b035108808025841004804100705052540e088020700341070060011700695840f81ca500111805a042500020b84d90000e0300a002d40008030443c0741c594010091510320304d240d40341c1e81110b1145024841100e40ea0000c20110f485004410148203104500107107566603814910485510764803080e1a001028111490302600981c440c1e8010b801080140801310305003041e4a0b03451f01d016080180042c0341c6c01052010170304c0d00710342540491142402596a451041c00241901c01c00d404024203406d84680420a59400044c00c0c0c007034400c1030380301080f8100e40e941c058940781440482040140200c0c410890455880000c40008401c100c1e901c581070204182d407002150b2040500d07d80421040015001e05400d55000040b013050902d01107503036500840c0007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 429541402 1250 429540152 429540161
    0x50d05010506100507320d0c03020606062505100e0106090e160303030b040b0d080a0f02010b010f0c050f0a1b0501030203130b07030908030c0d14061503070210 70
    0x165196551030040c0511850004081d0342d1005262a0942c1085900d4540c903c2070300ca01c4e003041c9060381c050009100440606401c9a064440d010300ba04c12003000d952019082001d03446084005000d102c000510510701001501c405240b082c12130060a41e000f501c806245d15111025541d030700c110359002d42506594000c44004111100000c120310f850021900300b1344850220101458121460030400010040050000c50f501450041010050040450018008149003981088855100405022150b0b00400350b0740c1840e03035010002036900000700d08907519042d00d0785c0042c801c00344100d602c0303103e0041c030141c0791b021348103442c1c6102015030a030380b42001200b42116000718001e0441d074171002c4070100300002d01080c00d042d0b2075460800b501e4403810308031442c020311080218010641b401d20075031140451a50001a55550f41016902351286800654105607603071304214203c0d417015850b0f000a40280c0d4041c01010080041000714000f5400060148045210b41c058048000015018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 429542652 1250 429541402 429541429
    0x201110304061d03190e030706021c05040801020d0608060a0524180106020c1503040c181b020303090712050a06020a050d0606030603060f0507080a1a03010905030c061305120307030605 81
    0x500c801c0d02252174000e0944442d40e00c84611a40150b50200309050300070903130010034541e00c0c000e002c444100703110a655074052034001c1d1401e0741c07000c03840c2c1c90a103050754080030580d01d40d1000c4812654030001d00e0030945c0d404550f08141068180352040e280c480d4480b14040c001e00080603418480302c0001e2200c4203080c264031500041e1f1102c00e4540482c00c3c0403442c440310001e45409285545042d88607190030500d2407145da4100050208646007400280d0321243d8100c5d10001e0002e5900b601c3c900c002e40e00d41044e6540081405103400010b84014060000e0518684c4075000c0c20548045840d120025000980d0480602c8003c200180c000e822030b1040d600507058039100040c105080d4182242202c441025104a144c40c040034010002c0e00030203100d50084031308001190020a0030110f41916148819441d0990b00703090928007082000b0019128001242085070101d50701d00c512441c00285850300504281c0020f402c120340309441c4001564407c01c20708011814540d02c1010130403d815a00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 429543902 1250 429542652 429542677
    0x5060d090602070f0c0b07030509010513050301090f060b030d02070b0309010216080717030708060415080102040b071b121202070509090a050d1e08060409060207051501060201110304061d03 83
    0x166010170000b43c182d40102400450304070509003001903030f0141661150500c02d40c144100460850201e01038111441e01410f4058000d0060342160f10b4070340004080d0000c2225014285000f0b000c807401d0004400050b640b4560041c030400f0300d072491100c0321b0781c0081c02d4004d0a540030071015a0052250306607500c0240f080e114150fa856507400c00d0024034034803c501c1c0200040802c240030002d94047c1d03131b09412141c03ca0b000100702021010101d06c140341d17a480510356500100d400502d05000d01e02070280c10b40290048014202d111007026181c04a5000b00100c40d10000e40c0721001c11140158030b203285199004403124252113000040700884101c0d40e507030142e8042e40040f01081000d0000741000116428501e01070b1071610151651081ea20030070000700300304040041d840d0341c3c4942018903100d8220314110350b0344080c0d080054603122400ea030300030504402d9000150380c0b841445000104c5001c614510708544840c0c1d5020003501c41c0440d07001200e002c00c7c0101d042204140010010095600c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 429545152 1250 429543902 429543923
    0x60403080f070e010e0f030f19030905030c300303010b0715050601050306010309060b0d050304030215030c0301050906010203070219050a1a070323070506010f0e1005060d09060207 79
    0x441e02814600101400b080110748500380c00140d0704824102c0d42c0c49001c5500c010840c2881d004a4030300901c6607240011403003003d540700c0c29231a42c0400040130900030303a10001e45a483c0c006240d5034400403003000303030000e08401030031481e0908262030b070840c0801d486286000e8190300b0380741c07031071350304281c005c4000a000051240100070307d03561008050400705a052106152180c0060b000f4040101800e05140d01c0b0101c6000700b000d00d50144545031802441c042e84600c041c1415981ca400c0b600089000d60080072030207441c4950102924400d0751035000462942c0e0a00382440912480506860f0640c4805e100c0c890050b651a00180341600300300c0b100091031407801d4104000c6481e690720010700c1f410030002c44201d40f80710600b2a40d00a4150070043c004a50544401c100f004a000c440d941c40907021030340b041040800301e9218101c0c0c1e282101111580d842d0300140d00010b5040d0b03182e100d003080044081104d810100d000d00f020441040001411120315120030003664424101110441c620 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 429546402 1250 429545152 429545161
    0x606030b01050a14030706030c0908011b02060f010b0a0507061107031101061203020a0206090d0f050106090c08060105121504090b04150c020714060714010f0c02030906121806040308 80
    0x561103000040030100f41043c038204030701380880c0d100d0444c2e01803c4101501e40b2556603685010715920030003040408000c1091071024010006849900030840b00140500d40210341c0440c45140d0712816030308010b440368a48141c1403010b0b1001d0f0311042085802a40b00c0610b00c0c0041c815030050028580a503c1e815000201b01054908440d81c03030708002031341e6040c8031151002c240d00268101d049a41031302c0242c1e07150b00e90030004084404100e070052404e104600128204841900220202e40701e90380213004051405105a500e0300341220801e00041c400d00c40501048607060701290420204000c02d01503407035079030105003600c0c210a801d0b280900c510040c0402c2208000e101d10b40b11400d103100300310580d4500002511507a5603c02c1d0121a0b16003906041c03607a4490048070501070f03110024442c6003051002660203031a102d501e40341002e1920141003162800481150180031005041070301e00400d01203e106140c5002e404944170740703480c10f1007a10f500000c005882c01103020391a0145a8a030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 429547652 1250 429546402 429546409
    0x7022d010e010e0a03270b0c010507020c06090d1407080c0114090117070201110d05060f0a26030c2b2a0f1a060f0a030506010b0c03070606030b0105 65
    0x20912566a15003c00d1a030442c1010030b80942a603410300d401d01140c008602c98a00304003074001101031503215100002692640c100080c41c0307860920000f0302c203503903c030402030b84c03101d0045484070382002041100101502c0d080b0041c80d4180d101d040d80d00d02010410800600d4003c0f26001007000e0307807000030309101c039603000034603075503040c0a43c85403511380f980d180d0000b401c0001c08101e0840c941c04402c0890403041c002e4011400039180c80100f03a031140740b402d810710040d00042d1103903400340ca6400c0864406042104040041d104407a400e04250464109186504040d4241c40141d9001c1440040d504000c00c1c407604204060080000703e140303401d142203107101c86141c0c2c444c00070700a140342c0350491701051401c1c076070340000070709c0781140c0d00d41050401605a61100700c00070800d03103c0c1070400808640690400b4040c16055404004030b4a0310802e011150300c00303010141c8164001c0c0d00400040c0407a20041c5980d9a5a0781500d080141c0c3d40d80e0f080c1500c00e00c0c2c10890b00c041104006005504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 429548902 1250 429547652 429547661
    0x10e0709060e0c0412150504080304060c0e031c0207080f010c030b03210a0309060212180c01080f0907050603150411210705040b0c0102041502060603120307022d01 72
    0x515042c501001d00300868960020300ca14450703c0c54100500e101e14062011100001761190b154200c2408a8942442d102409034004c0700d086070f040d442d210300c0d028040e00c135890034805480090020150f42e05288581180c00da0b884100300110720600102040a840a0014008640c080e50001c2030401080001505481c84040054041d034050810503500103240c40325800401c5203c55040c0d0b488000c0c180890245c4620070b0050300e0320707000192103543d2100d5600c080c1c0c41030402c10104001c01e282c030980a03817180400b1036101e001409000204140c0d40d400c80b04540c00c0491042110170f8107581e40003142c03503500100d41058010322018508081c41c00c250240d40d542440c9400404d01c2e1100c400820f40000c0007602d08551503054890019080c0c901400031503000c0e180002d0242e844003600000305010303500c140180300d80d54104115070310040e400000c0850180d03074010b01400303d00082e104a04c0058000070849000c500c9101220a2041a0f44840fa00364800c0800c1c240c4003140d030500402d00b0344 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 429550152 1250 429548902 429548909
    0x2105070515040302060c0705120301080c010e012c1201051e070806061803070b0c0a15020414060304060b0d03030c110d1b02030705030d1808060103020f090414010e070906 75
    0x7200800411000030f5000c05e02941c000110507005032900c010341001d600d8584030100301d6101c03240010000c1040c0900090800c2c10344400d03651075104070304150045a4010103040c404000c042c01403000b02c20500501d101c084c1076130018100c4131118441552540c2914000c0d200d41140000c1c040003507150074004116580d0081d07407810803803800e0611102243c050310641c100003402903d00c4180081c80e03038041c08400000c01040440c40e81b100b0312884000d0b140c0b407948034100c03041d0b042d520070f941d2000b040c0c0c002d540846040b43d0b41442c2441007d0f0a01c06680d00081c4110307010f6a4503401114a81c1d100382c00c0007500c0303000343d80001d5141017403175000d004001e90400840042d0f20161504040c85d50212151000b528221855040d00c402440400d10b48441074120650500a1000041166038803040180d120035501c43c003101105c1c1c0c1e401581382c4411007804065005201100041034604000c84400e402c036203d104054440b5032204a494215043c00451000c150009902005450007038010100603 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 429551402 1250 429550152 429550183
    0xc030c0806070c0602180a08010f1d0c0108060a0e04080a0305010e10030320030c060604050c0c1513080d060e090c0a050f010c051e010c08070c060921050705 69
    0x950402d00b90141404400f8040180510f400040340c6540740c04010700303902c100801801d2134a01544401c44075003c2d00000c2a5224071524208202d11104000d207003026414038075802400246944400458800d4001419180c1220002c070740001c3c501d1503503152170b1090b409040000d4540844242c0282983d5069104580e000100424070038012148411841142e52500786041003c070348607500103440425440000c4035010118011402c50360128881340318034022102044196101d11800c2054007d103414224140d021021011600d60142071440d0418101802041c0d101c14543c3d078503c142d403055142c00b0040b13844072801c02c00311381a1741405802404a0000d040b91300c070548082090080e107031051a20500ba1600722440f146d0041c0050384ca03d68204c000e64020010070280b00e2000c05030004884420740c0f802d01c1e81c4460f203201d10310085c000c650030340d01d410b1070000c01d480300c2002d420660000e0740c2c004500780b040e5201080c80b00101c0480422034644984030301003400c00398100860340c180c1c3c511 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 429552652 1250 429551402 429551413
    0xa06050618160e100809010b060f0409020d0b0a080d02071410030b0d0c080d12060b030c0c070e28060f15090e25020111040b0f070501090c030c08 64
    0x1008004003107000d900408000c03042492001d092002c4414080d860415500040d488402124041d801056107202d02d04100090000c8480e000a0100038460400603940c102d106100074068462030387c0081550381d01d000404a9985001000161440640d40c0880906e0784441c5180342c405805100300e800030004881c0304024411070401180320519005244000c05945140c072110b03035a01c2c801d002c0001764015050005180e1148a21680d80e4000e20000000c07403172840f03000c03030790003120b003d0201603992036900682103480f50304c504000b50300403c0e4a484540a070311030104001d000d074402e06204c0c42004000744003580c00e00c11484020101407091038070150074a08280301c403004103050081162201281400c0c1c0280404040359140702c7d42e000541d407440c10f071061004511400c40401c04000c000c01003100c249100c1c010503401c80b101103d031012a1501400700300031080c02d4030058040c2004c04555285042c807282d0300c042c21a10300030703401c41c0d84058140c4103000f030100da00c44010203407410320010103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 429553902 1250 429552652 429552679
    0xc010c08090103020708071b1a0a02030904050c0706050412030b01020a0b0c2101031a0a0b090114030102040b03090f070b130905060d02030307121112041203020118050a060506 77
    0x315841180501ca0600d500081c010003000960004c1f64021a0040c5126200280d100240b00c0c280707600e0310902d280c000e4a62001c4407078484001c1280d1071072425070010b5240444000511010308001801171100b42424046003010030154010180f082d4400e06401e44400894030014041364090200c060444d40000c1080000440c05903080d508400300c0b455940c3c42c0c10541010702c4152205500b03a0000344001c1d000002002018201200140c09006216045554410701d0501300d5210b9030030b0f10340c007280b54001000b080142d05041c00103000050700161805886140500e1558010348e1004116440407403d401c40010512030040900200c150b607914120341080c000212013640d000c1c0d151203580d5040130944503640e80496078030303182c0d018040c0c0341c035a000c0342040030000031b141b8285400704a2000b4200b180b0800420809111143c0c20030903800c0600748411001c50210322241117055660f54800300340c0115180c1560609503120304000e180b104040e14100c0241d500c050a454090201c18003102e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 429555152 1250 429553902 429553913
    0x4050315040c080304180b030118110114090303070b040503160f0b061002100f020d060b030a060f1d041401060e070f090e010b0c0a060c0c020316030b0c131a0c0c010c 73
    0x1b9886042c1d40d000850318500c50400a40101038007002e600c00400f802a0020030041e40200c514402402620350304070002c08484072140c0c0380b081603a29940340d0420410a400035590000041d0400e0149003101c0c00c0c640300d403205800c20b80d083c08042d2034020000c9005030070040400341042e401002519488076500340200c01079590f00b098000c48103180e03115210b03015500760035419190b0300c0e01005018008243e407071821503620382c02070f07900e41d02503130034600c1c042071745480c0d60040c208a4507030960070407400456503d10384030880c015000310340c121942e000080307040400b40203100180203030400d014020b09101e60054032034038043c01c000707040c0004518100640d8414000c0c16044440340f5543d103640700c2009908504240095000400e007515050b0f0705030703a140d4001c003400c070010700c00e40c2120410080c030503161040d091507120017800c1003c070100003502c10300d104001d4450840b40d1841e0940080d10f52680c0b40b59002010084400c0308004038041052980030000441600703020300703103110400066102d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 429556402 1250 429555152 429555179
    0xc171803012307260a0c08061206060f0d170901120504050c06070f0605010807090f0b0d141204121211060a020c0f031c0506030610030b070504050315040c080304 71
    0x303c90610000d000f001401c0950720030b000f240c001c501041d1101a141103003500000704030a11b507050000b400c0724000781250900204a56401d1840c100400540da00c00302008042d0004180300c5400c0301005c20b171400007644004690310910480392010b521001c100e00010f01d5a00003003e5041c0c030780d05050500c001f04401090900c003203841074804964a0249041c11005c010316007a00800d101e10341000080c00010100d9070310140d5000c0c400a00c5141008075424043c5d80c50181c000358490701820540c0300080c3c0e1016407001c119510800d5810040c5c0b039015001c01030300980d02c1500840d000035412070404c40210b62000041c05076080c5030b40c1c006103a000f4983d840600400300e020884d070004d1080009101000512001c00150044035940e503124500c0d070300350140315014040320505000100c1d00c44d16000c146c1c18458000513003560001d42c0341d42c40e0032005070b901528110a1000030400415551802e00001154200880d54850b080c24986001322560341103500c204403c1d00280001c0c8500030840e1003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 429557652 1250 429556402 429556411
    0x27020d0f1820040e031207090803040e0a02030403020c10020a0b0a0606051606061203090e090715030b190306091b05010f030f0e0f100b01050a09060c1718030123 71
    0xc4400d601c00030b00001c00c0081c020406505464800443d08a0040c6000c4038614404d900300e50711a107641c0d41e580040b55a034025401210381e000c10020004182c00c0f1150b000d1640700b0b0003403048030b200050b04800307d01c034524085403d90060f00000c01103814050400f100c2d64004104200401c4100c1c5840300081c154001c041c1070300d4002400000c00c0040c0101500000060007030403420002100b175a00e4060101250f03031045020140181d400910601400304102c411a543e0185080001900c41d10807801040b40180aa600240e110038100244001201f214040d46c800d40000400d108607040c40d6810351801d0700400000c0c4813010081c0a1664440c00c0b010424140d03040102e18006c00f644414003030008031540d0380c0184600d40525034a43d0740014103603203c51250200300301c120703100401140c20313200c2d0f105d182d00031520004080000c0b45c0304031218400b150094607000d0b00340c10500d03100d070781d2903201d0b0103882805106007a900d1401d1a0078400c94980d01a010340000c9021003000c034010094034003c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 429558902 1250 429557652 429557693
    0x1060b12060108180f1f090b0414071503022710030f0207020915090f07140a11060a021b07031509050708010906060e06030a02010927020d0f18 63
    0xb241e00304c00101c0e903403200e40542c03605940354083e9540a080d65801021512414601150394103c00500144a52110350340c0003070f61001295a15115401105c80041c00110745105055000801c007001b0001d54444400f01d560140c1d0351094483c40d412807400340c6078520821100004070300126a110054550381200e10b090100d02c0c80135142c0880002d0041840c003a400084410400c10465000308900529440884500c4101d48600c1e02c4104500811076035880480c5000c0d0481c0d940c1d21580f4080d103a8891640f5120391100702c1c82e86014100076068501c00c3d121600811840d0510301d00c85688000e64600f10001c01d4203d1554894211b98000344036803800c100da132400c0003c10b21070280324560152808800902c0351f0950741c64440011b00991088030440c0c54a2008115145400725403141102d405950300c01030f0b141040701c00030341e15400e940c1d07580034104201009103001219002921510f400c0c0c0500142c0030000e03070026400e840b202d001302c848070019000c1c8040010410000c100c400c00c03400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 429560152 1250 429558902 429558917
    0x30d08060d1b4e06020f090a080304030c060518030a03121a01020703020f0402040e010e06040f020f0901120b1002030c010b030a0825080408160801110912150705040801060b120601 79
    0x460355140c09543c12802070010340c00060b004a10032008401030408540036940316044503076441e0301a849000e41c0c00002d00c0e0690521341040761510a402078260050b00c1810b0702d446078100c01c0068981000140100c0105001160401c02c542c054483d5562403144181400814241e00c00000e40714041800000e100d1052520000119100d9905503006098080c0040303680d96150b00c2d00040b0030800b183d82520886c01c0c803004a00100450099410252944500c2c9041203030003401075840034a82000701c00110354521401d030740703030361855070140103800c49130003031682c0d580346d5103206003035a607a1103200c0e0096204038000c0c0002580102243d142902c1000100c0707800140c881c050f0305d10303211428080e00101010034041940503010400103024640003000128040c2d85030b012030300b60b44501e09c400e0b02803642441860a00d0514a50302c0d40c2fa800300e40300341c610200d8520125442401c1c00e507085800694041018003200c24240300e401c029281010045040c5020100c4401030340c0c400411460412141c2c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 429561402 1250 429560152 429560279
    0x101d0c0904050f060c07150216060b030a0501180309080111121504091a06010c0305030a09061e050106110a0206031819060b030d0905030d08060d1b 65
    0x43c4800100b02c8402802d40d00c103410981e8000185410606090340c05064503005080145003034030840c0e003403801c580d120202003403da444001c02007626554143e0107019041c0c0c61000218203101d178507248062000c0010070301809040003445904141c019a40c3c0345e240031044040e03518400700380d414001480e02280c0150740e070100964080c58462001c150480e003030050740410020712814105080c00c102416607520f0b540c91004442900020201a01003030302080406c9594a6541021821a004600115901450030440c0802c08a50f07021240541d983d0b00040c00b03038681c0a12100c41030a4032200510008040341c000910600c4081d22168140740e080071403c156070400c7c80500c0081040550116100c8640c0c200b01010749030501c0304a00c2406103010740c01510340200e03a07410035030b10080e0041581c2484408144c611910241c47d660b4002c01c4850450b001410f005c0d440c0803026051421000601d1800012841c0011998814074100074000ba108031006140c4200815041030b8080041500c4039 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 429562652 1250 429561402 429561413
    0x603010b1605071a0316080709150908190203010b0306041a040c1e090b10090312030612050a1101030207050604060c1206030803061c02030a03030f0f050405101d0c0904 74
    0x10b25070300c8441407a6100754011130f40c000c51409140324521103240c080c03100d404070360210752505088420401044204105000c0342401d508400080d01260034995811a00c40e00d00500e81032610f10000c82c1c0c41014a131000c02c508080c0601e046070311007500141402d040503680d100c48022604c59480c211000200040d01b07200ea44002e0030300801c42f05004000320000603815145000060140304140d07401c00d003d0304540d081012000c012040d0369601c62910504640d13940c0e01c04260304800e001019110807012403411001012004c1c0e0030320505c021b1500c0201454503094031201198501d0606206202d2140071440102c3c00540c0640c0c042e5000a50a00700441079400320250503c0b0741344540b8100c004810011210f004500854003200c0200401900314103111411094030350080d0107401090f103e0700007074081d41080c5070300b04ca103407000f1401c601e0395180b1a01f00c1e0300840b03003030302c890f4002c400901c030806141c031a101005003582c50b0051170340e501c160b44598664802501d80d000c1c07102140014144030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 429563902 1250 429562652 429562663
    0xf081e0a02090411030c0901081509100e0f060c12010e040606090c0f08060306060d12030209060d0c0e0108090c121203090d08070302070b060409140604051b0603010b1605 75
    0x107a00414003900390070541402000820101c00c014064480c8040d0502c051074188101c9040325080d90060140c1d0290b00100004807078083d060705082e10840d4480032001070b06000e80e1000c15101001171814000c50300320710b403502502529030362190200700004144504e01d0003050f41500d001010a01c001d450f2131030000300505550b4040300d055440e120303414410a600030584854681d555130f60320450b4803043c04250300c1d004152015a44240303048038000004011290140c6144224203005007810504004103d556001c941c0d04030211343d503904154400341d00301468120101c000e1030100454039100a105585100c0111542c0c03203a1105054034414074403c10840480c2808042c51b281c03241082c10119030384204020221000c154004000b07504c1511030310a40740c145030020700300308898941d03a0610004003900030058480701c802c5071803481c40140401103240514841c03c020004174480700003105a0000402c4118031400c0c2c1000100f285c005000103843d40701d40880100e03503040400d0b1410900d401c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 429565152 1250 429563902 429563923
    0x7060902011209210518120f030a030c03060b0a09141513030c06051201030b0403050702090907050f01030b06030109050a0204030b0108031c09020907080912160c0f081e 74
    0x60800c1a4401004039003441024144c44100f040c02c103051500c2000c0e2114028440700d0301c81c2c02d4510303508422500c0c03d000090031404010054070310318000c50a40c131742140d1114900c480803a444400b00c03403020354113224960003000036150b82401e007154003c0003400b5101911a81501001001c0d110401e95201d200110105880a2135030f03a942c2000001000c80c0031680c403059405801041002079150b00a000301c400c6103256010900b116801c51341c56081c07844000d4015000c110060006200580310040b50900841c191401060b80c07526090401a650200c0400310707042600f444440c00d500c0d241d140071303207064507154400810780b0703901c501c0d0b410000d029541c009028080d149000050103107000c40149028038508201e00c545550495540d815691241402134020240e00c0005d41030901c1826a030350445880385c02d03a080c2c03241e80200105240c00c4401361070101012044001e04000c4260343e08002010000c58002a452408035620345510130582810741c0407120209200602c2810301c5038040c2c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 429566402 1250 429565152 429565187
    0x40506040306090210030204060c080f120705070b0606040f180b190608070e0a0603021c0f0c08090708070b071a04060b09130c150504050a030b0f0a060b0706090201 72
    0x2a640c1d40d04005001e0140714506034052051240e0410300c40b8403900031101034030035903107800c121a1520b41d40c2000641c446010440d030440e082c0186548002c9044a15000340311981e900e50700e038030380740c2407201c140c0740003802c0319100310020001041b00c01c2e42401c070481100e24032501e8081d5002d4194440e00901160790416030f011403010070440345440050003941c2540c1e84d980c0e40861903030343c00708151000084c401031587d00007104c041c1000007034403030380082882c025220080410084000b080d1030a85580c2d10031803a2030754540c1140d0882c0759015081e0b59101d8000380040003540d140141d0240c4540c424020740124610000d98181400b42c940da00e000c5c0f28002c1103aa00f81890a410400f00400c2c543e418144a64048004680c00c0d1a0700d403c4080040c0d0410440790590385030500f40004249020111000e1000600001803c1c0e590640b10724000c5000f104041d801c0d1600b02041510700c14020b200d450701d5482e00d001030110490400a031514a9440340c40042d2040103800160307179424181c11510300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 429567652 1250 429566402 429566407
    0xf0509010c0f030c031706010905090402030c0a080102041409060a0e0403021f0507030c02030a08070509040609020c010504050d09060207051009080f07090f02250c1706071805030a021005040506 85
    0x4060344001489903483c06552410407038001b1100542d40c103402610308070b00050801d0011f01061910b03c403581c1e005480107088400000384940441c50252155128088a942c041000c0041104082e0640c8442000307c3c0d05d05070b07070300c0c2240000c0d01c214000c2c0601c040782e40b10b1400103806c05000708040c00c08484d492412003202d2040070103900103010201e40311400079040c4542c10589074000400d68a4912480e2202141a40c803800e023211030750003114a90760b00684604001404211070304c020b0200c42e00010002c105031a05040040ca445845041c440030402d48100400540c0c0c1c2c0480c1d11000d80703804640c18a10220440001c590b00c03002e60300850000e00581c08502c01d88030b40040e5000071103030381103000e10000c1d10307000e1410200c3c0210072001b60544115a4100c03424030500c0d05204060744546014418103458482907a02c003071112100e121242c0c0302c80107211400c0c1e0048480483c001072100c503540c4940c1880003203903e032030a910000b07005680c500c1d4503981140c014000c5d40c0c007410024200c0d98 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 429568902 1250 429567652 429567683
    0x204060503060a0906060e160f03021605030d051e0a0e01020708030106030902090f311209030b1021020d060e030a120203130212030f0d06030209160f0509010c 70
    0x4000c08548400702c07217052501400140c400c041c2070100d0f100380c0c2010846000c6048821040e1303003007002206010101036007048a000c0801c4140440f545060003000250317100e2884070a07030012035102a00c403c1c013445440c1c242242e2640f030700307911561212a03004041072044074003400c00c1c0a401145001400402c01000102d84554540e0040d60024000c940304025074130380c2042c2129004003a550404d0b0fa4a003848481d6180c032030058692440380b58a24151407280ad1038440c03541c0c1c84940034144000650154041003484080d0004a80050b0020101207120385020500ca195800e141000b030380980700610700c2400d558a00801043c01600080203002c03080d1440c51484d2a54407803000342c0d010414200e201c0a04000c01c0c4280c038820800c6035140070180009408000000f041c82111107181c0c403080205441e01c40300100540a502074040c03000c5900c0f419441040300b050001410711501410720952201c002d40d10079002161111242001079031800b0501c0103c907030011540001d02410b4101d0140c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 429570152 1250 429568902 429568921
    0x20c0d0c15110304050606120303130507081c08090111041203110f0f0d030203060d030c02131404030e0301021c11090a0b090907080f0103080f0424080a0c05070b04020406050306 78
    0x4610032441001076030f841e41d441f02c08004499101281140c900d92003400001c0004021507002039045005008032842c140d44c0300c050520304100d00d0004200e20001c50040e04209030440029a0170082480084c001c52a0880107886107002d244190701300c20030a11142e2040c075005541d81200340c01c065042c0c1c2c089500007580c03d0f43d50030b140c0d000d4030041d21491901c08545c6119100350b07401040028500030500c52151400c40701084281d000360382c0f09144001d6008101d101e445542c42d02d030052a04a1400e1800c3e040103404405443d01050181e40100128440e640c040e40d0b80107241481b41c000040e10030046e2528440c240507203c003142e0018030070f83c00844c1c40036030b1501801005000b115490707101c1e030f103000045401d45011703505042600f05110042c000202c61a000d001340039400c0001c030782081d544011644030003407480d6100d10b5042e003014280c00c403c1c0c1e00001a03640505200e41c00d211070b60014000a01501c02c40b04094050f88081c00840c0440d501c03900080010300f001001c4441e54103007500913 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 429571402 1250 429570152 429570157
    0x609040212010e010b0405060d0b060c160f061d100e040207030201090b180303070c02010507120807090b031512010e070b13090606140307030902060d020a020c0301020c0d0c1511 78
    0x55002c1d01d602c3ca800018020480021034090314005400c160409401e03e030b8503000780c81182c0da940e41c0400107120f1750340b001100b0400040c0a1550040031261207151101440d507515031a0400800c0000050b03034100301c824484201002e1034020b0342c039000d03243c00c51072040703078040d0030041000d178081d0001942c54181035054210101690050030400101c0c0c4407111310015210901019900756002400007442c81c90007420031030700c40360060618502d0300d085580d8241c174007d2004980c1c03020402c05400e001816900c25003940103408a40300b041c2ca14185003040071400d46119210038880c040203041a030344801c007034100340640542070b401c0700c51083c2c03101440c400c0d6030000d90910b2421044030b14009040c01c0c150052104580007626030220303040070b0055100c210f500040c41a01490f4a5001200061321110000c008210007060b0058645280c0040242001c009242292003607005110000c440344010a200400d01403e042003624012585850003030035580e020741421540c98500041e4000101100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 429572652 1250 429571402 429571409
    0x40201140c010c08130b2a0304060f2906090328050d02071404091e1407050d08040b13090c03060f06030203070c1b03060e0a0302010e03030106020a0b06060904021201 73
    0x290441365030795484101841054450340034003151503040c040382440c0003108804c80040d51000303400240590724055042c50394000d880032552660f8500f070402e0640154411509403444160141803200120100a09022844400130744a8103001034000c11641d41040021280000c181282d4101d000000c44070b01142818482511140180c8010400c01c3d807003c600c01c0162101103041030008010441840b0044c4104242107504002d007100483e50001c284074410602d40c40b580c0075044a07000100d0b01420141d85500060050800180940004039603d060320150380c045106161104001161040c0c6051168001d04000346000c00203903205905070042d0b0140c948000c0c09103c16640c0b8013048049100c226108030006000c1100800004d80440e1074a80c054024518403070050348030b484440459002403240f01c0c0c1c65020b03521031001c0580a010352104080060083c1d400c5601d44003003e500ca0100210003002201c42c10f001a80790381d602c0064480400015000b1500da421045014481400a00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 429573902 1250 429572652 429572657
    0x606030c050907081f0e04051e03040b090409030527150a0e040b040b0324090a0f0b0403090e0c07030207050303040f030303020706020f160b060603130b040201140c010c 74
    0xc00118039401c0c0328000c1806000c0750ba03214000350391000c90942c0d803150040300350b4400b10400c0800052110088144501450180c0040e0000070b6010091190300c10342c24914100ca50000c0c07004104590317030102942c1155205540105100c022403034116168807030301014401c200c07003c0580790404070452019a0003064161f604280520b0640c14058903406481001c000050400c5959506420140c0159242030b07809440070400b540d0a00000381007510064861800302c540784400880c240c4000340c000d0300918150041c205000d0b56490350b444c00c0c0d62030b60015043c00c04000120b000c140c07007800ca800050111260038641d42c1402c3c1d111004561001005500510a03290003140038640070044504075205070170071035101c2c0d00e19581540650003030201900c1040d82806001001246c0340000c3c04403103c1c2c01c0040700180c840d85400340406c81e01130100c0e8050101407080150b618561503a800340a130300b00a000205a4403840104c07518681408419440c442c08a0440c849a105400c072440401007034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 429575152 1250 429573902 429573923
    0x50406030b06041211221e06050108012c01120308070807080112061e020c280b190903080106021e1c020a0f0305122a09011209060603 59
    0x1e040140e640141e0041c5603032041421071400c001071400d8806000c190000d0480b00f907001700c024800100040e540301c0d6100ca0364607041c42c0d20402c0e405010103600700b40058020040703281800e0000340990b10500500008441203050b00050108070100e035049908a6154003c0568503105a10005072404404801082c0d41801003803046000702c506510519995580f01d000da80303442c40380c00c00b810070280180c85882eaa440c5c0081c4d0b0910f030036003140b0243e60255015942d02e20307101c42c0c68540341010880aa02c103440c83c00800d00c000c09551401d01c0c0541080c1542c00d01d40b00c140b401680c1a9030207032a404030902c0c0070a0b82d0308042d080300203035040380c1c880d4003950b48064140071800309145403401011115085902031410081540d04106944100c6204442d80c003c119501c14040003ca1001500450004100b5840c04482e0501032503201d00f80c1610681c00950a0810750311305001d44060358401c21000c208a41c050b44280105220b440754603030180701044150500000030422804241d40078100c0c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 429576402 1250 429575152 429575171
    0x1080105061204080f04081603290402100e040f0e06060409080702062503030509010c0521060102011e0b040b04020a20030f0a031d1204060c0c051005040603 69
    0x22600361012078642082d245280da90302c0da9540459480700a000c0c2c003884e4180004134150800300525110070b00d81c2c8090580c6142917041204e485024030100c028950003621310030417040d189280b4143c1290381910034031421401c40c1010b170ba4840a1240c0c1640140c908400742c81d070a0100d0b0402184c2c1c0303800030705480340e5483c0c590902040e42c0c1e080f0005008100100300042c01402c2c101d000b00300100000c1805d002005000b0a50100f04205203429000a074856091000000003072003071490103c10703802d100d440c0140c00780e40420f21070098040081c000841e0070000f5580e9000b9000604640c001c02001d04640854910907030040ca036240c40540950b14044000d620750516100f110405441a152a4400c14000c0c10b00358900840c03800824190006100300381c03070002c00001130081e048491f00d0100d0403079032004854214909000c01d07945a64002082c0c0314034a002d01c021030702920f581d4503202e54540780f5814806001c4071540c0c059500120241c1c200201c050307201c006481500d5131a43e061042400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 429577652 1250 429576402 429576409
    0x30c061b02010506041104061b08040509090f0f0c0f010305070e040c120f020703140a170a050105100801060503011701061802040806010f080309121905010c11070b0306060c07030c0603090201080105 87
    0x70394020349010401409d12001c088911803061608188034101c01d078030b841d8494012841464003034a42ea1002d502c02c80a4410301d50f000e1200c4c4034041c200030000c103501c94000000500c0d4101424005050607a1035010a05d000d101d11010201c007440a0020b2009840b9520003c18241904004103642840d00b44004884000c038002c5a107119015560441c2d802c00c0d00040c07030080c0d0300814401090187e02e03010080c5900d00014620f2141d645000c00141c10744c980750901c12540190459103042002c200018009550440305985c1540c03601c811b40b034090035801106070b00600080d00034450070907110210034003210480d0020001c0c1d485d8071041e5500c0303036a030320507028000e43c490055400e182c009025900b0103040040020b500c0c00076039030840f108032808020301040460100400c3e11a07135180c5c000300250075045580c00c2c07841c1c11840c0003440240d00c2c020b4820380e00d01015026034400c08001031800615002000340c3c10145400210400019075a6440030f0010500c2e41c004a001c01c2e040e4000064619 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 429578902 1250 429577652 429577657
    0xa17031e0c0f0a0908070605250b04060e160905100501090f03030f050706180b01080a02010203190c0203061e0c0405030d141326030702010c030c061b020105060411 72
    0x160301e4112141007041c1c500040c00290028030710750080040350040094072200401c02c420040c8626228143e40b4503441c510715142d412003e00710a581030142c0d1025001039020341005500541010001503620008103020741081410904521a050008800300b44561242d10070b40c042d4003002c107040f00c1182d4800065510300c100748039803100c8400700001000480d0062403041e00a84480c9011490507070780361b07205000c40b01c0303410a00220349a884500340c00c004081700c0e07a90142207004000c0c44d5032152580002d6030307881030300c400d84c3d5000039844200d01050700030038080c1c0300c1030790040035640103140c80510100390003090b0302c204060700060000309805011032001ca41c00d9510280242c21100c0348550b00361008522000c1c40310070b14004200d28152801c00314120400b0702030a15000402818298420801e880a0000e000490304200451300050383c1010480ca201903160820005158071414101e000f0049214a4004500c00f464821243c2da030650110344500b000702c0303081103d00c0096407050021f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 429580152 1250 429578902 429578911
    0x80c0409020d150909051c05040f0603090308070329060c0a030216050d0305070303052e0e0c03011d0a020c06011214070e060f0303090303040b0406121103010e04050a17031e 76
    0x9401c5041c04220344032100c8010300480e147c90816078600750f03413007841d1401d407030032070740200006656403008000701a07100800c10f07004409807600b40b0001c4106201c0350300c017540702441000e10f0315850095030216241c0c981958030340510034042d20b001043e203090194030340e01900e900c001c9129242c80040344038a0301001c0e18410a030184c0d12141008200c1d5400e030014500688411000c000b0401d4401d000d41c01d02c42203a080300c907403040035014035181070f001d50108440907181a5003400c0c00d00040c0700180030501841040401c1c90341001036a140e02100400905c80c03a41d44050601030f090002c154914440350840c0c025124000a2180c0810f2521403511030000d4000c204403c190307540428141d14094031080383e44107008045d00d00e0203400da40000e10350740c01680041c1a455001c00c0070090745070001c41c00e81410140d14018841c074031f01143c52100ca480140168082c503040103001ca4140001003200f803111640c420b4101220701a00f1005030140e410032500c442c170444c84180024501408000c6d200d028 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 429581402 1250 429580152 429580163
    0x90706020c011209050d020d030608070302062b110a170907051203090406031a0601050a080613180f12090e06060f1e0a090f030210080c0409020d150909 67
    0x44031480c00459080c0c0000b008120f0f4292a00c0309500030480a00103c00c0c14010781c0c0041000b180c03028005000d950380c507400f01c14a5040b520303040001d610f4440460320090840350b04004209001003140c400718500496a0b100c0300c1c07800a841c00586003401c01064030550b02c1c0c42d0308003c800d84490420199004480c9102c094010038810041811b040c0016000041c8800c1904d080140781804102115400d40c4182d40300d40c0e5034100080900c0024090b15000542803914510340b01d03106001603c00100500390f40c0c001e2200a604a0400b002940040001d0742c00561086400342541840c02c4a04400d1a050303940c1504a11407001c100d00840f1100f0844d46102007081407a66000204021038001c165440c400c030000700320f01e0344006c20615110452280548200ea16542600001400d08045400030000c1c83d0700001d0074005603031080400c007211000c034600f400385581c0f21030b0b1547c40350280360321808074107001140d40300d114401d581006860300c0401402e01e1029990303885100503200840307009081c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 429582652 1250 429581402 429581413
    0xa020a050a180f0e010207050102220e0f3301030c08090d2312040c08030a0503060609030f0f0a020f04050606090d060b100801081b01020d05090d05010501030803060909070602 77
    0x6260842d64003d581e0000000b2040e101c246020f007640d000c14030032a826540000c62012050902a01058070303a0380e882100c101d141000e40714038200f0b102402c01c82c05030076510002044000c0251549024040c044030422540c0c0c80300c501d800200810040d143d0200341021032600d071403441031403c1403040000c1030003002d0095013080c0658100d205141c2e02000036140c8111240c403000c402c4020300382d480307004034120903e1516007003030008032103660080325580d042084592030b45540036080d650040c100300c8885d56240c900c000020f20344840c014520754640603204070400e4400300480d083c07518038002d4801040780b6889004000844030210b5409911050901a80c1c419080c124520a0524412080018507150441c005941c100c4440c10000010b004600180080c42003402104840980311702000064a55000042e44407514440f00a04200000c2551101c941d01c50244800d13650304030340204500c0d40c6070b08010340c031070340222945402810404003249402e200000c40000300d4826901500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 429583902 1250 429582652 429582689
    0x40804140a03020904050f0f0307120f020a0b070306060e0105130b070f24140f0c0a090b1201050a06080106020c0f040b04050702010f0b0a050a0312020f0f0a020a050a 73
    0xe2290044880c1903801c4000e2103030110068403071035580760003140104010400c01a0003060f070707451b014900d0322249940d0014085d090000707960407020300e5018414101140c0c91310110030100c1c41d0101e0b0420180202c110541070180950b09984000e041d1031190b40c504d07413800400070054860340b0910f14070030041c4c030701d0b00002c00141c14440d002d011810f205000c9092040d2640e180c010414491100310300fa5441c1041503064a189240b2403c0c8042d442511940c3c0d0324503003286040350305000140050003190002500c0d8035018443c01c4e010020304401c101340c03a2500303426038619040f207000740180303801036003c07001c0426010f014100f96812105e16900402d0914844e400340040301c02808074550f08540c82d1254400310f0b58a601846125424031382c000a90581c40d4170400040c0da104441305800f5444200c1c00780070645039208440b01366600015001c04082440300d0403494601c0345909402d6902a00d00c010700710f0207010a0100c03405000315165500075440b40200802e041c014403030307101621075104281 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 429585152 1250 429583902 429583919
    0x2a01180818010c0203030708030601080f010e0f15040603231f0f0f05071d100f0507110a0602031e1603030b010c021c14070e060d05160e041406040804 66
    0x3011440700600d89000020019404285507401c580c0f021038980201000300942940d200d00e41711750000b07048001c0712a0303515250190180307035006884642d0305108080066160314520100401038100030700304000b0b0795a00d04060200d088920340d5060381c5002d075001600440303c0002c0303200241d9804440c0702111803005c9254401032008150351801c15844101d14500c0c007403180700d4030340319000a460340300000d05950541c22000c02e4101c89644100c1101d40c00c04661580710204050080c40e03410000d40c1c6d402c15007401c070f08030a208185551700110b41c1101041166004c405014a00c0960100c0072651120100860140c05180004040d0421905024001ca4880e03041140c9040c0181080c126030492070b0081061510150580d40c50900c641030050204806035403900d1207100080c1c05002c12606001e000050424041c01c89403141002613290018400c0034408408506c9900420200381c9980d610380c2e0384030260458081d107841410b2107400d003160001083d040c2c812035200c11914581810003460 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 429586402 1250 429585152 429585187
    0xd1a010822060501030803070201150b03221e0201080f040f3008070f08100603090c090c02060414150601120204090e0f071a040b07082a011808 63
    0x214458501da0440c90011480501c20305000e14001e01d901542d03840c1400740642540ca50300304110f4004102403040004401103170503240c2001600d42500301140400b00881c1d041804000c019122503401d00c1e0300c1d41080010344c40700c0d04103407017a00e500300c1c1a81e4007010281d24120031540a814401400304202c00180700000c8501042851104403e2610b2a46c1d4001c807801160305c0c811307000c2010502800710090f04601140300d03a07959850150030624001c0054201d124140c45507105242d224000f5100b0004039500400140144940410a1102e8031400035520300050710103440090150600111824020030181ca0200054214060540b10b032001180c0d1080b00180583c074842e0b080c0008141850b440c05444d24810b0194001c000d00e180c00c100c100d0404d490340e4060078000040c0520702d000d9102d10003e03902203072189401c550f00c072001c40c24010928400ca07441d0401c80c0a00d403003d94404041c26001d81c1c0c800c8014402000003000404111410000380e43d00507001081c14400410300700020040c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 429587652 1250 429586402 429586441
    0x150112090506070809060a0603112b0b01030c0f0e040312060f08070302030d0f140703031803170a020a120b04060b1201080c040515090702160b0d1a0108 67
    0x10312020944400782491000c2c0c44076000102d1910074030150740c8082000c2d0380c0041c40e496040040350301d180d4491b0302c1c041c0d2030b40c1b0343c5d402210300076007029120481140b5481c80ca0a024103030b01a2156902d03183e10840424001250304c0600f13910080b514106900300d642c1903400e00007074801c540c1c4480d2411754100e603040e64080303403580d21110080380490010009c0d0006140c000007c00c5850705602c101814145d000e28010b04008140070500042a0301c11510200c1d07010420307190381c1c0c45a483c1001c4000e8103078045661550b200c080b50792420558058080c607840d07407003102107180d1500c9440010069201c0c0560540004101804540784074080c2d85c001c0b030410b07200400c00900c4560b00c96030703a10b45411503008012008100401044007810038065842c8292049504020b149007680440e100d01c00c410303044500a40c130500004403024000c10041125030300c680e041c10b94060b52138030300c0c140700d80c03014010001a50802441d0002803600254614031080161650b83c0c0e640e03108180007082d12420034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 429588902 1250 429587652 429587687
    0xa0f0602030a0b0a09140606030702060103031101020f121f1a16020d11010f141905090a0b36060a020304030b0f010306060b0316081b040f050907081501 67
    0x505660990744c26650400620701c80d840419801900e04009007042001804a8003842d0100100000c441d408541e150540340d040c100101605e1540c81c0300e900a000340500d802000c040051034803111201c82400300c2c85141c654024102e4032419070f22080c0816203a1040080b4400008084501050740311701410403e454464035501214072a000280a0303034034034005940c0f1096044a8403041e503800b040c244c00b00841410104e0000e0311400b60b11603588101d860107052800308040d8551040d00c94000c035029143c00171b01d503900080e26010000910380c4000200300080100c0358513894800540c900d2a0444000c006042551b51780c52024400700c0c1d4060780107101140004c100c08030009080040030303401031071280c80041c0198150320305581103800719000b00e40c44c0300043c82084162610394504120b244210720302040381e03454000b00120311121108128800d41d001040106912404203aaa0b0449004854101e0780d62550b000a4400c18815520068110701c1d141525a080d4011031088040000bd80e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 429590152 1250 429588902 429588911
    0x62039120a232a10020d020903060906090f1203010b0f07080d0203060a060c050a03110717030c100207020109060302180405040f02090105041503170f07051e0a0f0602030a 75
    0xc49007004244020301c0d51180800071402090a40d24940c424140346811910801d0744103074150340070344c0e514107400c15070011500000e42c40e0f01c060094055802c6242c010303013120b1040c00c1c40b0a00c25200d52003124020740900c00c8100900d20345000040410f590a6040a41403035a400c044941c1d1041c0e1043d402a034108004102c2840020354100092400700b084580068883c02c1000c100b00000c90664810320801c440c05d400000880d40228042d0103a543c9418410b6040200c48451820504c02d54007090000140740202d031441080070005015195001c0240c0d82c0864000e90600200d009044000c1d000500300102400b1150080e40100f2201085e0a0303000c6d00d8181c0d0030300040a85008441c11500f440602c0210300460410300001030140c481181d043c0120382400c1d010181c90400e030301c005441955080d010080414103e012500020703002c00e40e4507070b99806800c00541d43c01d0400072440c446980e00c4032240c0240343c0821440b949a91185456003012480e8a420010350006421850a656103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 429591402 1250 429590152 429590177
    0xa0212010b0301031704030221010e010609020703030609050903040501081e151801030b13020d050604080702091605041a0c070f05040c0e090103062039120a 69
    0x4020155000700408241ea56480d811454000021040c50080d03086085003440184010b036035400301b20440b190b50b0340641c940380c840c40c030340c0d00c3c00f5003502400ca201e594a00782002c01c503162a60014000c06010351414010180d603000c0c0c0d001260411911601d85400c240010702503584189281034000703011030181c40c100310600c1107200e59104181d424040c40094949100d005007410041c0d041c01d5901204110200d600d0740c2c44040c11031070000e00049802580e182d481c030442d52258802040d241d0400b003101e006251910345045140d2000c0030507446007000500043d00c64840c12030707089001c0c81c0e50759154181440c0204404e02c02c8600201003400681c18410384507808001c0140c40010282c1105804079035207017500f84400c56403072554050400107044030f09032164031a9000c16044170750042d4005401201c1c0c8805014100c403452140c20b074104000307014502640c01c400c4050b907803602101c2c04451200f540c07a41c1d151038004000380040700d4010100c0214591641c1d0090f0502c1082400c0c1000302000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 429592652 1250 429591402 429591427
    0x703020f15070c080601050907032a05040305120d060b03041208130510060f080c0303120604060e04050109020406050105033603130819020a151205190e030316080a02 73
    0x3582c0c0004e0043e80c446401000103260a0b0a856040f155a0908011f80c040c9442c5c202c0c189000c0d5035000008c1c200c0d402e05449141c0c401d9049400641d0401e043e90301d480d40d030a034400c0ca030740d00000d0302c00c001d6070400b01e000c00c0540092048034042d5501064070f0442015615059640000c010144640f0341d480c144c0010110380c007400f410180d00d5100b030340001c0e4242001c20300d5a01d031440b508840041d600c500c0101c00d09132000000c0b0f660000d04002411340d40c1e40c4d01c070b0000d005048070b038100301c0c1c041c81b0000a00040240540054031040d1080350203000254461004543c10300084940781c0100c0078561040c050342d540541d1006c42030b1010f5041c079988011074121245550f104403280b04017000d080c0e10800020400b44140c00c058400000c038140051041d4000548400c01401911500c0c00c1c81d6107080c200a002d8685502c50000c04c46091000b072600b8a0b0000107203030640a0504414204001c16802c000d0200840b841129101305000c1e1103080b442088a10941c000c2404100395030070064610303c000c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 429593902 1250 429592652 429592673
    0x708191709060a05030a140903120a020f04060903050d02060601090b1e0c0304060801050303040e0f090115060c15050c0409020f0c0703050a050f03030403020c0d06090c030501020901110703020f1507 87
    0x9913a22601d40da03041c90300d0204100d80500041018140f0480d0503c50340c0b00012040b0760000c00b512180f90a079403101d805071070081c8907142d03045020160001d000182d079500031b035907a002c803030003036098907204444010240d80f201c81c11546c1d0b40c00210842002e100100c290000792038400000714200c610701403005040360700e961202098034455070000c1000c201241c0e1055640c0c0c0900710a6000e1400c2a1914040c40c00c40c0001600c82c02e9040d6010000415103282544003080d03a2a02024840c3c049544210141060b00580c1c820380c6d041c81420048800e40541e4085d5a0144840c2c0f10b030381c0e10b443c0c50400650003d4111a0042d0b00d1b01000300308514280e401004000c020b18010000350146080070f1516610300115240c0b541c20076041130007040003298000c035500846140658011041039541d203404030040a1400000305182c02c0284c004c81446415406040400003c0e01d03001c114141c1482140d43e104040d20000f5400b0002c3c1540e02241c0c01d02c14480341c041c40c80013481a051030308641d074101d03112 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 429595152 1250 429593902 429593917
    0x50d09020a1806080f0d051b03030c07061a0f060a020a0c17071e030f0305160318091e0b0d120e010e040b0108130c0b130503070819170906 61
    0x74804500d0001003003442d84200c0c070041c601080107104035214008250f4958060400c0d03001882004121860150050300c1584512003002c01a00d40d289411079401e4907582060310207a4a031480c0040d0781c0c54600303801a03110042d410051001c820b5034a042c00300241030340075441d05403c5002d126525400122210864000f401e41d030111030300f844c02406c40b92803601925510100b084403420782030203410160011040c0039281c104c3c0b040c14021145040907162031242d50382d89112101c028801c0414560b000032010640315542c040c4d0b002c0790f581c1c3c10f092400d0700c3c0b99812140d00c001020409142070038030359200c0f40a0b0350f400b8007400801d00704d0b511104d50a503603481c0c500c40490201440c00c0985c1d80d2003403414140c940d0456007005000e00c150002080700c01c008146540c41c0c04082164018441c540c0f6401b80142160007040741e840300e00c4203002c20b03100c040c0d100d0a4080d220320b0f1000f00760500003081c0d515412883c07e07030100c005001511001c90182120719510031a01d004c00c00503d060300c07000f0080005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 429596402 1250 429595152 429595169
    0x10b060f070203060a061211010203041a07020102160b0a0503060a0f03030203120109020415120e01050901060806100324060506030a09140609071e08070e090d0e01050a050d09020a 79
    0xa0791038600500d424070000614410015150001c240040e08800006611594100d00061520b807403400c010f074503600c5160080c007480c09203610f44454800c21000100200c9100780d0940b00c1d001c01c00400c0c0905050240030307800035040c080c030461803201e1180c0b01856000300c00400844080340d841c504d0445403085600240c0044e00300040c0390691a1002501c1401080c0741d170021890329203044c9034101400c6c42c200c0100c040044132008203e00c1007080d040316901c161843c000b0001e42c241601c001d4000c01091084c45002d00607003000509079200010448204c9402070102c003942010111020107500c895852070f0500790b074610000c201074441c2d0340950700c12442500c0004100d509400c0140002d801d0312503280c1290f000d0030810492001c003080410448842400015152001024440306c0798110703004500d10340300b0000006408100b400b40309000c2e4400794155030341024134074011101e9020011929003c01c0382040b52007036091007907000b056179001c071480004052000c1e50009008401503031001c0c00c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 429597652 1250 429596402 429596407
    0x61e010315090e07121502070203031c020c0d030b100305101205011a030a0c14010e180618010f06051b19120302070b0a0506030a0c0e16080c1209010b060f 68
    0x90441002540007908904d0803000c122017035585c0b1040200440c418071400c1c1a0040703134010441d01d0800c01d84640e2250030010004001031620801d000b50030448a5107003a10810740c200034030710f000748a102040c078000341541080141281e01600504006009075031901285540003800d00c1c0003020014016110750008518003070940110141a4140c2000070310030b4210b04026000aa040076030136040b40c400f0000360001500341c9006071001c1003400196900407440c525a05840d10414044500c00c440859001000d42882c0110499149003401007031162300803800d00b070242030f00640140480c0d1106500c40c00c0070701000300030503042040c42c118401400003080c41510070040c007000002035400e01c0303140440c1024030684580300c0d02e0501402d1040362540e9903021035040c0d1000c0c003c01d11001d4100c2c0070008111354640c810440c038a030403612010040079a0381e02174122481518501e00842c01c41d0109414010222190382080101500420503503581e0104002c882d20b580c2c2c081e08030a211b17011000e4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 429598902 1250 429597652 429597671
    0x70806010e0a08060f0a060914040203010c050c030f0304021c050d0e1f030e0109050d08070e030109080a110a170904140c03040311100929061e01031509 67
    0x1410180480303140c5114800040041c0078100e00015040e0348a001808450300c5d988880300d9510080900b90400000c05040071035001d0304003490790140d40124400c1d4001c05c068201d0700340840e428080c01d106d203071454008100381105598020003454010380010b0000e0380708403404141c1c00f80000b50180c1203c00d5044101001a0075400404181e691030382610509482c58052658903180f000e44581c00044c1940e920300031101c05000d40c0324031803031940001101c842171864100641148004c454150004000003840348290606005510f001075100742c440e418040700d51000c4c2d4440c1840210070420b0701c241c100b040e0209201011144e04400c3c01d90141daa5421a0800e000585000112954000c1315072414890030841e0b140c1143c0c0d1181e0107144c0308541c9031141280904103189404d444050345e042590034003e1041481d41c440d000d0080c454400b802d070a410200c0d8040680481c2c40d075030b000c1604003442d504032070781480440c0b42d003105240003c1c445240e0198501a80c0e45ca0b00701c090401c0c0c0e601c0a00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 429600152 1250 429598902 429598907
    0x90603092a090702120d09050c0a0b041703070804050609040906060e0915100303050c0a052a04090201090303030b0307050301110d05071805130b060309010c02100b010903080a1707080601 82
    0xe400c41c0c2c0f144007505205030540c900e0380313003407069403c4540700c260349002d02d400344070060211070000c4c503009001c2804155105d421003038541050080e00043e46610040204030100002101c2905501c801c4d041e0030719190a00700f0203070b504403040154206482d11b50580c0010320a2103090050600503070500c02c24240301d89850f180160031104c02012540035418060001340b03c5120301d00716585454010703a2448a44426420030440240c000c04501c607501c2c1e244242c80c0400340c141910500e408100f17040260040c00c00c415580c02250103808070b4141941400401e10940240d5010340000d0129442e0716550070119084524501c880051a08003062401e04e80b01e0501685400404d545040040143c00c41e0410040110b6031088500c11030010908070030300052500b00756046107004210940302d16000003282e010303188410f900401802031148541c0e24012510448e8150706040e99405075a9040d1380d1017000c6a800079440d4400e10400d82c10103003020010516041c4910400c1e40c07003401905124002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 429601402 1250 429600152 429600169
    0x6050f09060c100617060112030c0210030507020c0d2a0810090b01090203010f1e050904080903011506020a02010c02040209030d050711030604031b030e03030a05040806010f0803090603092a 83
    0x11000c02c4c5d03040340018000210000780181511420395800b00d143c0f0340ca280c02d541000c0410402500504e6800002d18519051740c0014820741c1c198007a06c202040b0b00c0100400600a0321004103d01c039905180304c09a05403a00d4020005400304640f1541a01e07804058a40090407690a40c0507855900f00010801e41041c880c1c010f2011800030360540d4145000d400c182040c1c0e000d202000b0410006100240300c00302c250394000e003400361401046050908140d2000c2d445414800d0207907013005d900e00f401440d012069821a84160f001d01541c03402c0381d004641b440b04640d4240d07400758007480150310310364051040c00036684042d00c44c0760b41c8131094504030b58042c010703051141c401e4004000f0000843e8002c0d00030310244140c104489a041d44034501030783c2569102d48050380503c0045030003000319070804002c20944030040122a83d60380c1c0c86045001a610070b006510f42508140000d100340d00302200a10781103480c18007680c3e02c050703401900d003441c40440f47e0341c9040101110342541d441e0805d04403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 429602652 1250 429601402 429601409
    0x61e0906060215070309060c03020a021e1e0715050322020d06051806010e15120d030905070e0c0a090506281407110a120c06050f09060c1006 62
    0xa0000e01d00c0d08002940301c941c0d041c3e01c0300c010f80b450030010300850f1082d4401c11555034082401c00204180110080c0290030903000345015200d643c60f100030100500311030402d003c11180c0140718001c0100d41c01030b40e03041001c80c0515135201d600c0d0301081105000000401c18201e6640d440e17168a803940583c0d50200856000120325000c00401c00302507150004523810250300100d02041c142c450f00b0b00480c02245000c1503480320300030000080780c1542911016802100b06850030031840782c002c030401c81003440c802c01812566110981d0740c05003034080d03040340040d01e002e40166821541d5410f507114040d60308a644520750240000d81003a440c0c0c002081c4c0f03026003019030740642402c8512000b603a440301d180542015081000151800641c0704002015880c810103c66945a50709403500700030802e1825039081c8151208000441c0f491011880307044120f03003250081d03a5080c940794041d1241d07803008040742c6500504002e814040d880e28001003440583d0640200358021018803c2c20403229141c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 429603902 1250 429602652 429602669
    0x90902094816050c0a0b0307051b010905012906370903020306150607030e030f0a0f1415041509020907020307060b0a050f01210509030d14160c0213061e 67
    0x503170a00c030784038905080d6a4000f0080c18a2542c526100d001d01e00c0120300345164051540c2841100010000190001c94074404048c01142c411404039030071000c580300400d0b055421880a01c8488030602a03030705801d030104d21004140d445890380c1c9194106440340300c00c1410200304a054200110300b401c02405901c02c08440700f030403020740c1c5d590002e07840d032140c85d601904104914240c45555601400801ca0f22aa450100e07200030b0760b43d141c80d0340d10fa005400207035076505003407088502c0c000c0f022038a04a02880410304500c155141c2d625400c40060348101d0003c10356503410410016212109000d001325042d4000f16180d004030300d0000241c64a0810a030b0103010305d410104915181c14001400841007401c10540c00b00006a11055840800546020540c1018103112280c100800140020004400c0074040b0700c14601400d0b6a4220988803e0306925a484103040000e20800b01d22a0103131004051880020416007c0301c1690741c2500400108000842c80728460707050302080c90300a09190 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 429605152 1250 429603902 429603919
    0x4020910020d020c03011a120f0d02010902010e030f0607050f0c2b0309081b0f03071211060c0706022104030e0a050307081b030a0507090902094816050c 67
    0xf22020a90301c91f403070300c0e00f0302403400040401e800d400140050110000345000300d40d015001c00800078083d0050103000c2e40071a8906003452036606010907444071000b4040000d110544404204954075030140c4224042c040092080c410000014454079004070850317010407054008007040b00010300d403130f18072080c2418a45801400013034001c0040e00d504a180380b4030849881e558040540c1400c0080701d100c00b19010000f40402008050f610381c042e25105a55080c1040e0079852a81e965440290f80f41c0315200c800340608000180250018a07010042d507035611130b5061210111040c0342d42c141c238105d000c07030a4018006410700b011040c000c0140300c01c030001e000f41c071319003000191107401c40d110300c0140910400c01840c03107841c10882c0d1034141c0c3e8010210380702c41da92000c03210020b00c0d42e080101c2c468618040171405104990f83c414500d40030080f24284c140b200c020741000c04020071980900711140400d0000017941c3c2c1803001e0651035000381100520f082c090300d010307070034141e1420503d44103107004c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 429606402 1250 429605152 429605171
    0x10080d020a020f040e06011701060b0a1407020604092c0d1b170301030305190804150c030b1816110a0f0809130f0501090605010f080604020910020d020c0301 69
    0x1004801e0740d4040d5220f020007a401d10206000d04086803181d1039600c906000080c405111500c40c80c0c0c8250090000c01400340c03100c41c0c001d02032050b841e6100014100481071703d204032034140204001ca20003420185801e64a550301000e80e0102c00201d6150601f143c9142c007016601600c0c07180c4100804060450b408403800060070004103030801314060086403a401082010704c03240602c2c9451404071954803036952f441c1c001c0c29540120440b0780c0404c3d0000d03c86100c14020411203009903800041001c009989040c1c00e4020080030366030908168030b880e540f5010341c86030752f04100e080301907400304002880c18062001402d5140f0f0032030400c201c00700c1105280190085441004c02d644501d0300c21003145581044802401008102640499268201e17094140070390310081c02031b05251014021030faa40c605800440e8501d10440307010880000e01241001d10620381e540c0d110300003c10050900203c4008101036015182d40880940e0141002000446d0108030750462410110002e01400d901c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 429607652 1250 429606402 429606407
    0xa060c0e0406050406050a030803090307050f0a050c010c03050a2607050403050606030c0d020d0807060507030b01020c01090510110a120305040c0f050a060509060d0c0819060f0e07050408010f0510080d 88
    0x1c14440274110ba0707804000700300100000c0c0b088038003c07031304101112842e07007030a0701d40340c2ca445d041e0304d048400c1e201d010200710071940503200002c1c485405444840c20300c116480250b852440a407041b195611600f4000030102e07010001c40c0f80035044980d625030b202c5095103002407501601a021902c254441403a002c1983d5650302900c04155050310000c1d0440c07007030301d0800d40381d00038004001c020794240b904006085505500901c0603139000d038200c45009001000541d4208510300a880d000040500720b024014010301d0794082c200300400490380b201111b43c40d5062620b00319501d41c0300003500d4005100c00e01c010480c04c000a01701450034400d8241ca0100040c01c8a1101d104030014084041071218199031000e007a18200c601680091116080d040d2008010100840b010b2260113005960300240190b94492801618040340d00341c0c1100c0d0810300c400410000040c681e02c2003020420000c02c41440a00a6003e8031182c4540860203040204034514a001c3c0394106072aa54080782d000012130381d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 429608902 1250 429607652 429607669
    0x70c0f05010f32010b030601200d17010b03060f0103240b040f05030303090d03180b0901050603100e060112020d0c0905090c150d0f0204090213090b01111c020a060c0e040605040605 79
    0x1009080c0349c186c603004016880e45c910300c517185815060003200c1a0352181d40c0c01c1303c03100d10103c410146460250b17813100e0403000c15010950304140c102c04547d8030540750394040e500070003001000041404044205204404000400b80c01804207a440410200b0442451a00b0113001d080d007103001d142185040044103940b403102a0f036480405441c0d0400c4585500c5603d1031180c603a40180500b561403600c6490140606016601140244551460121410b50a1040c241600d405401608079640717040e0300305c40505c840300d8069034840148004400041c1c02191107000415080b040031500b8600107591a0a1541d20f4030030030300442030100f040a41c0001c0804581c07078006d040400007900c00f03000303c0301c1c0d000707000b07075000084518800550310001100c1241041c080340e002c01c4081c844e8011032001145d01c1c054100603001d060340b14500c5030400052160b0402e101020a10484000110030303100d403000d68003000e01d09030100300c00d511000c0403420b02c2d00900c80900310070b4800780b0000e460301d4042420036 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 429610152 1250 429608902 429608911
    0x309021903021c0c090501031109010e1b1309021b0d020604170a1103040807090f150501080912120103141f0b0307030c08160e070c0f05010f32010b03 66
    0x40310f146524040001c0210800040c02c0911000c00140d1303100e140c02e101d148008600244514000000003928410380d040d030521071400442d080040303070144441480b041d04015114a82c41c46c1c800000700344050244050400d42c030f030b15a402c01e0041e11416402e81007000c001d80c800c045400000402c03010072444503070b10442001c0304064642d919442007003202c001d5000e0010509070700001a001030881800914602500c50a4004004840300070001c2d604030b0300000e140c0c00c0302da00e804908110381d60081034501e9022041c40280c42a0440440d07008010303500559540c81e010090100600034440b142030110f40d1240b0710401820120091540d0010700d130040c1d02c000c11446c0e04c4d10020219034400b803014100a40d80100501d100c10f0b03d81e11116107482409204e0035501e104018001044401c1807943c600400440d12201c0550a0031346800d9814030034800265155901c0f0000b40c0101a981c0c407801c05903c00a03070301b128000451407186040c0e05241040c100c0e010b542040144607118540e012a50032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 429611402 1250 429610152 429610189
    0xe0c0304020915040e0703122a03030c0504030602040306050406063f020301110a0315060c08210f0a05060d0b19110f031501080712050a110703030902190302 69
    0x520f820310024000c0c1c200e00c10b088030305008881c0f0000411003980344c8440040800c0d21a8201a01884440c1c03904c4c1241601c602c0701c2c20a041c440e2001319000340e0002c0200780795403400f58035154490b00c4443c01d03a40641d00c112803040c1d03240200410b110302c0e446648040c00c0342030003d0a18004c4001e01d040d82020004260324100a035595040001c4680d14000320a580c1c0580203003d41c5410740000501074001c03801c11030100b800c1c0715aa03c040c50b500903264cc242d07805510b41510100ba07030b0304c5842454114002100401c40c00c2c02c4140440c85550815a02c16499200f448945103041c1c42404d0658a02402c6140682c0d0301c1c2c040342d40040c40116002d07901404070200300e042c004500740e459020f00300d05003e0003640100040c5c0c0ba50005a5000258401d01c1d0480d40302c8854880702004503544e030000c403002e900154011100cac484481c0c00c0c1d0041c64211000c5080841c0e0030400d5003010f4507552202c04110007081c1c3d289441000c60400306030031000743d228040040c1c5c4852540e0049400050112212600e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 429612652 1250 429611402 429611431
    0x100606050703053a02071e020303031902041802031902030c0a121508070806090706120b0a0b0406030b01090e13080a0c0c0f030204050907050a050f04060810060e0c03040209 76
    0x4c000111034403a0140c259a54000400d0b02001500324001c0d0302c00001507c0403070303003107028188071400304182c1c0d0700f980c0e0b0240003146550356000b08400540041d62945c5144e80c1c08100c006101110490301107040c1005410040c0d03079003031004030001802e94012021022030300500810640440d440305594045141d4280342000c510008a50001400c551600403041001c10201003400074000502d801903501c0307001150181c0d25260704180e50340d40548680c90024614140d5500c1c1b13480990000880e100c0082d203070f100085c0d01c4d240145016002034100e4000660748081e011819030344410008020b1505c0c0c0200e188a00709a80d10040d201460500a004204001080c0e05640d1040600300d90f500d8000b21482c08032500c42c085428031400a200036481341f41001c012502c8240c001c03410504603000200022006403a0400f80b0003825082c50b50f040d4415507400000407202d405201164040030410b40004040303041000b041401d14002e040401001400d100700f00050311354503c1560030000100a648 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 429613902 1250 429612652 429612697
    0x904090303020d090b22050304051c211b08040302010e13060e060f122104090e03090a0e0705030105060d060b0c0c0f1210110405060c10060605070305 66
    0xa01034460300f48241d811a02c2c0020030f8082c41001102280150544105507202c00c0049515481810801102820703540003008100030902d403462002c1064012202404245500d5499a03150382540b41d04001d079542801c2d4151099550000c83e0250742078481120041d11502600d030b6808030700403408001d050210001c03400c4690390700e507100381e025440e101006000c216240e00040c01c01280503146030713000d51110070001a0340d140c0100c3c0c41c003090748088010030410520345441040e288600c50188a2040100004074001c001400340c00341680d6690300541c2e45203400b0050100c13001c22075024032440406113060142c002e51160440c0e0459a003207036025280c01721108124001c108076402540c03590b000103903403500c0640100d010401400c1c103c40340d0303030800c1300c0009028840c3d4214140048541041d00310700301400642d80f203600038400b005070b041d0600f612180842e40d140d204000c2c01800e0b50011516007101c0c1d00074040c00015040c103252040c00c050095401030500d0103080c12402003c0000391601 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 429615152 1250 429613902 429613907
    0xc0f090e060f1e2b0201031a060a0e2403070c0203121c050f090a0b19060623120a0f11030c04030b01050604080a08130b070308010e060409030509040903 67
    0x2c103410500030403610030a120f500100d948092948980e60141080804081403449500c6000d096510b0125040020003415030044004080d429001c500300000761820344155160b4a01a0181884a448180050705401c1c20048030703005c5900032203c517100c110100781c24240054180c0f90458402c2c20900c840e60140e01c0003905100b100d00c0d5002003007202091102608504003c444004042e00308100700c0c0f51501143c078503544408984040140c1d01c40100c000000da40450f0b00c50b804459840c0d101c5031140847d001e0780c10307203441c0ea00190004210385644810030039026000740da84220440500c0c5807070303010301d050b0181400c010440f500491384d400a0030052106504240c142d030321503402d401d0381d030b1a010f12461a6074000c1d002c2a101c840c18070b40080307500d0811108603802d82d0742c0c220041448040d1952031401c1640f04000b12006005c40540014002e607560001d0b0079068440d45030380d0002d40c10210042e05498008107110b2295080c2125070000c60380140445241040a80d0042401003050905 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 429616402 1250 429615152 429615169
    0x90105070e0907050c0610062309012102030702030714010c0c0f06021e040915120b040203031b0a200117070e0a080a0b060d080d021606140108010c0f090e06 69
    0x200344642c000c030740802580c1d101f10300348481a1455034540b00c1040003038030700d0040030400d80d044c500940c40b01005283c00d80d6000310914400c0d0340402d8001c100c91070110650074140c1c0c0003500c0100260f440420640104002e00070f95183c684d0b804c034000c2200400041005100c180046c10203001400a01c40f40c40038404079404031100350840714825207508840b943c0000781c591251040311a13007840d0503d0301c1250104007040b6411170b4848925200311120341d0302c070b80007085000792040ba89031004000c0050001640c0341003010b5224440050300c40c10740b5034244400c040c0765031440c0c9010389040740c074044442d0380c002620140002030719200c0e00f07465444131000d40d10f0501810311654000d00c01100003580c06000501d19007a03070f2152010301e00d04d856150030300c003c5d40385200c401806040c05006800030540182e0281c040c24071404802482c00751942c07181c1045030541d04441242c00702000040c01220824042d010644685145c0403501503c032031070050201d40b07103000d80d0012400710000f050307070f5a490a08 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 429617652 1250 429616402 429616417
    0xd020c06100303020610060e060a11100605040506041119020c0a2702031605070c03021e090c0405010512060a03050d0504030309080706050409051b0310030605090105070e090705 78
    0x111a02424405190341c0c481046210440c0103210317040c00201041c06c5d0f411510f08480c0f00f525110101440c000802005130000001901089880c11000c44a40002c0040344880960320340d000a106042c00300b400242d9200400d035601032824402d0f80ca02415190341201d00703544c070200a03568100c0c00f40350102d0800d520444100e07844542d091b4081103184c1d4a0280da080e410200341560f2100c24007030068000c6c0e000490307440c1d541c1001d200700f14884900403c01031609030b01c079407040d111198907640041c03102e5028000510b1600c00d2000300340c41d00e08000c0700d02d0340c11000481c0e07101d081520f04000244148035261414540b00ca142e004540c640d200c050340200a07552040030780390005500b030b4004002d45c1040c1b00070380009100d40f0300021841d1001c81d080041c0c3e5070035959140740c17904200010b8040d00000d05104d414500d0320002800c46a07404c4050350103400841502c02c0d902d071640c10407105886000e000f03500319900d000b050103012034114440e403014050075100203000b90f030b582106032038030b004804 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 429618902 1250 429617652 429617677
    0x90c090302100e010e09090706050a050d02030c030105010e090f0112080f0f0306090f0f0604020307021603030e0102011104120b130b100905090604032012040905010f05011706060d02 80
    0x42c2c1e00c500c0940001c0c1c0340b440788100381d0b40c0c0c184000901701000f50104007640c21184d40d0304075280c10300640e8402c0c00244080300e441e091081c40c10520380713852822640100c5410035501c101000600c001e60f808103403416000c8080ba25040582032402d075040c030242042c400d004010100c0701750071081192003c1a540440b80544c09151075046901040c0080d51085441d284205156800038540c0d1111043c100e000d207042c512003039a263f80300000e100003584041c22110546c40f4025003800021000d0702c60f800a1846960f841d042284200000b9081d41d915500c0f00c14075103024803090041d03001031140312992580024503056581c45d0241041d1060316100005880f0184000030010480b45000c010000c40345803080401032580c400310b885807074000540f00140007400305a00200b141d1a00000d480c0c042200c101500c0c50b04038800a103440030b40c480d5100f0010320b9201d1004101140460b140c3d0300c0200020700b8001081c445449400d0500000180b04910a60700855032030074042e819415180d90b00c2d00c00303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 429620152 1250 429618902 429618919
    0x70302060c0705120a050c010309110d120f0923010302070c09051902041d1512060a050a0b0604030303021e0c15090d020a0605041103030a0807140f04090c090302 71
    0x12464072a02c00f409068001c511403081600e080000007600c1c8080d603009005030203180d0010004401400744041c2c1600d008441c034900e80d6696868010a000d8580325214446107004a500e002e444130050002020900003250b0007000f665948001000303008004811600340300c04082d005074020300071124017600700c440014010608502c1503001c18040c18010310f01d0b80b901d0303d0307903500b00c2c0607881903005903000c050015840c2c00410198803006900144202c00308a5621072850200d501400d103a010b4961503071100082c481141c1081c85481c3d0007a200c40d0040c803202100402140b07680c46644401810154005601a80e66038441d03095410590320b000c42d240d80d04a1505215915075545c201e80181c2c40d090801700d116040000f40d0784c4403036030168005d03044541d495104c010041c04000e106580039010b101d112806917400740004c10142040c0c0c0c40b1140701e0b04103c1d0b401443d43c0302c400c10b80100c1c04800c0002c400080d840005907803c4402082e00030030010310402088070070300f0469000a4114104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 429621402 1250 429620152 429620167
    0x90e0402040f290d080a0503091e15011d010501110f030409060312032f07050d0f26010e07110f06190605090604230411011202120f0907030206 63
    0x2803071125008620810700b81d0401040e983c20403040a03845007004102c132030204a401e002074040c40145922501034410346481a06989044a460078110a02402c903044403008003d100060449c6601400e09240910031400d0060521000502d042c005e10b81449145640e132050910100501510042140300756611566a180600b01034003041c002290001580d40280c002e040c40792050384029008071014400110303c4007800d60200c1a000180400d1302400c00507131001c1a0100201e801000c000d580701404484048002010b0000e000e224940d01000000c20103d0011a40c0903181503d03048845d41e01caa8a41d280b050300d0881d03222045007a1802143c0c0844031405002c180700b0711950350141515214500b0119a004903806400b800e40c0c08151440810202e0030254484050000350040e40c1c8c4100f80d981d0110030501c84110b0b805c4480d501034111101541d41c0c005070703160a2200280065043c20707264282d03085541c0c0014035840c000700607500094005941003250380e0003590003918440d130b603841 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 429622652 1250 429621402 429621431
    0x40303180f0f0303050c031b0a03181514070c0231090308090a17030601170405010c1d01051b10020f030a0c110604030807180801020903011b090e0402040f 68
    0x21110b80c141c01003458040080e001c8207582d802c90b40f05076504894104501c040480101c0950042e070001810160340c1e010040803501c0440c10112454000c80c51020300c0e8410b00e13800010340b0314404680315004452814404101d4101c50140510382d41185c181c400c5a5480e030f40c0a59903850174040c3c0001c1034443da805900c1d07200c43e50141001c54003a039a01c4800d076507a1580c0c150307a0b0de05482d006040c01d240c000d00c0c51800c0340e00005076405c40030516100341405096403070300160260558040d80d090f552640206005078006d09517030002c03100d09040d01a0a5041000a001801810b03041c031210340f200c0001c20340013801800301c1c46024405100441d261260080c10203d20b400c1200c030b04500354682103942c500180a002c4e0590600000e10040c41246c0d125075040b1100200682a081840301010282c00e02400c1d80e100701c0040e260f2580010b0f252402d43d001c0500b901c05000001041030b103980450f6100c1139101c5948800c0d0f402d88640704045031240d00c00300f00200041f24a19030800d2a00b00c9484440c1d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 429623902 1250 429622652 429622673
    0x415090209070c12030e0c090405150702160602070302150d0e16031e022b021f03140402130908070506070801080706140307080403030902031f23040303180f 69
    0x14004d0715000840c03800601c040d001c440e11800d40b55580ea00200103046240340405540317611a101c0c00988240c20700112101c500c0000581e22800075800069201d1843e00c1c400090300001c0805100812000b85140c0201f95a502c4486010902040000e03119800032925084481000c00c00002c803450079001c00301045100c6002d00080302c00c004d5800e004074a4030300492054005a0b00103022611501240c00707143c010220240200c1201064801c86030f016a030345010711403a156180c0350003415500010801000c80b003410100d40c941807030306800d010150f20f5982e143d20606a604d1400a5840380504141107507029180005180f481038504001c1801e81c801061812640c0b5282103841041d254001500d05d207020a03d01055900c00303000042d0440c0c400e600854110f4064200094000a10b401207820103100400202001000d04c0e070042e40c2900601c62002d005010450000914000701000080e10340b0151000d010185c070352241e042c0b15002900c0d50031420303500043c00e070240441442d0104894 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 429625152 1250 429623902 429623927
    0xb071103070b031602030403020907052a07060e1207030201030e070f0906030506010614120402150307031b0e010203031f05030601090507030c0e181b040b270306041509020907 77
    0x74244c9620601e03609000100303a9041da1f500405851141c0e891031002c8440c4d4201c108a108100355401410903600c91b00c2e104c13050740030342c100302519007035003030800c040c104510500c103d600034241040300069120006c203203407090340c2c0e0910b40410240010100c0518040c0351780c2003070801c500c22581c00904011645d0041c03044a100d082603a866a80c3c2d26401c1d504201e10101c200081c82c8200103522040150140c810307801031008182841140324900d1a1314281c000721241c070b004c696122204071521110315104031101c062440c055040780100b10000703440b07020140c012840c50700a000c0f00c101c5a4124103420b0041c10317024045403201d41c1d494001c10003400b01511003801113071800b0150740c100780c80703036400c25004000031704001d9041c0d086403a9a841980000c0c82a5071225417071780c40710018005800204010a111f2075069112400340241c828520202000c100014400100d00b00d1a91000300707855500c6034104881210018040140c4805030800070402540700144c60104100b0743c0d040008545007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 429626402 1250 429625152 429625171
    0x6180c0d111e1905012114160816021506060408030a272301030e01020310030c0e070e060307050f0706050717060a09020f040807030506091c08010b071103070b03 71
    0x2e080c2c0c4020441010f000350040f240020307071013446038403002e100003411111118401d8000624214140340815000000e89040244c443c002c0015883c059003c0c118542010058041c010540303598100a545c1304404e04544c041c2034540b00000340302d07650320015900140b0740c070002d90341d031480605002003509002086181c804a900702443c032410640399221070650b01841c1001840034280d07804110300442c400c41507410991201136048480d0000e0000d035000711070075892840d12030300358588070200801d5500f0040008131b4110400181c40d0380040c511502080c03d48402c4e54984070020206c82e81e00c10050002c01c84480000c070b074030030004142d11461095520750313540c280044d0000c910a0161400b541e9450384056601e03410b2003246541e60040c010700900208031440c055441c0156410700b48c0034ad03c03d03219a00528100318505074107000c500c100c1158a1454110001140009807452030103029031001e00d280808c007081000350658514040243c000d0441c0c085c40c0d5607840f410380a601c100c8a0000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 429627652 1250 429626402 429626419
    0x111222090501050604090b040f09050d1409030c0103050c0d020406120b03030a0807030b0d05010e070314060108070b070201031409160b040b041a21040506180c0d111e 73
    0x30301110600c101c0741610001040e940c5020318000701080500708900845a00903905c45c0804990000703842007000e03182c800c81c00f400d00020341c01000b0b4602d1551846292070741d80704104688007540c0115048403d40c9007420f00280e00e0b01d0392280800540103a10540042d24030002c0c0102e40542c000c48690f400e919401c84c2404480e040c40181368681c05484505004a100800415102030090300480d40b10980540307a40b1070344075187c0700c40e802d58000384040301c41500f0034803003401070081c03113001d005085048130300030b05080d4581a0342c90b0360b0340d04c03034802c03049840c3e4080b80c07810840e03201c0e40000b690b00100031030b221281d0400030b250036200e110381715405250f040b4650303000408801c50800c3c0d600720380ca001e014030f0600c0c0c40d111070102e05450744001d01c5400035007040744903a50400220b0007803000601c954a41c56505e0180b409501d007034006040c114100311040561413446034000b62058040300103443c05a03200c24145400e880c4143c64a5900e81d021103000003224080400b504c4013804100200c4170303840b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 429628902 1250 429627652 429627659
    0x305030a05180a1214031603030b1003060b03040b0915270708250b0a0914030109020d060b191404060e0f041b05090711060a110a111222 60
    0x10320b800c01e40309030041130510071900c01c0882caa0382c618131170845510003642d21b047e1030400d61241001e07480c14201e000c03d6445810441c41d0422420b200c0c10510941070030810181000c60380d1702d01d80001440113198003030341000240051800d0040c131299019006103040181481a840c03071f4195616034401c0440350b9900c142c4002090001000c504403a071500c040d02c91440c541d400d810001c100440410748400d800e03100055001e90b0303c0c00a04008100f0f45d00c3d045440d05060441d00d10402211605110f42c0c10302d80010007513604c004507015820340c8880700062501d070440109001900c1c000700407c1c0c0540d01c80c00081c650390300c0e002c2004018403c4504200c1c007619030301d04000d07005066401e60515500e0100080000700654a41c4404907204501491407070f40e168001211040300f141d02c0310004425079520b025901d400c0001d513400a0500d541030150042021000343c0d5805084200001c01c40344100010149070244454042c50888826060b81c0d03080d0500fa6141d404d6a4465481d2000c00580001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 429630152 1250 429628902 429628909
    0x807060f0c020a0c1203020703140706260a09020f03060702010519021801050f040305011a010f0309170d0204180903020705120c04050c0c061305060a02120c0a090305030a0518 77
    0x8001d680d41c0300c041d10395105d090518804400c04803403011400e62166100c00310102d03600042d49007900e210301004204081c1002070042400407015011414598100c00000300d09098609440d880314002500246a441900004800e42054002c042c0c140c043e64007800f68103981900031601c641ea00c00650070220000008000c1244100c40028804448080280f541988108010f1810420306400300781025281d80303440d03003150321604142011008440c508000c9503003000410702404d056003001c011501e030b01e89940102520000c3c2c04001c2d40400504611030020740d034182c4016041d000814002c44e0681441d280007000345220660140c070900c60300082c54640001000c00d03004511016200c00c2800e072040c84003804010f01840f20400301807240003112901040103a06c500070101c005040e111580c00c2031400d156001d05a619814010400340039091041400b4542104400d211181c1c0c070020403074225034a00345904010500d0000080304000715500c8001340904414240044140144038003c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 429631402 1250 429630152 429630163
    0x213061a13030209040f0c080a0302070614090d0c080706020a02040608030a02070b16021c060501230f0a09150911090d120306170f3a020304030807060f0c02 69
    0x1400d240c0814400034801401c0074400690014803507402c1c03d80800d46c0d50f82d50100140b071070b00f0942d40c59001d42c3e0001c09150703041105100800d400d0800320111071441c034200c40540300c2c403030110380205041503516040002003c0c0300c030300402c01c070320955042c542c69010080d2507844d240400c0c0d04c10340c2000340c0032070707101c0000c012600303602d14540080000790700d015404280b58211034010301b0341000e40b8010f0070142c4c542210711004880e106440c242000d0f221700c2e00038200d62060b00145841e9071086d01440d00800240507103480240b0071a240c8003004900c10010710003880c590498003100c0e04015031140c3d40c100610000e000d07100151424091240c00031a0406c0d41c0c0186030205030700111034507450012801e13450511801e14400d14004c0b45e8a4ac40d4805000481c1c48801d500b1041d901c041001039441c103091165001c0d10224482402c200d1740c3c403c01c409941e8101490a101200c2e0000c0300d10103640c02081128002e552103995152100b04070304108000304070325024206081e00b414007450402e48013062 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 429632652 1250 429631402 429631417
    0x30b04051605191206060905010318170f22050325030b04060b1503070e0114090103150e010f1d042406030812060a0b0717030709030213061a 62
    0x480c181422046040350f15003042c0e40700301d0401e011401c501d0300084c041c64019007020b0500c07504c403000300e18500b5000408175071201c0004103034030380000c1100d000605001440c814250420b047c1c1c54070341e103845101e003041c0c0c0b1408881c400e07200c02002100c1c00b445095000c1d007088070303c01c4059a11207215409000b60081c404203004401800d80c40341800020010340303071981c02c107000750400100c2c1c07008600424907045060480e14031141011007081000c030b9110f44403902c486020f117080001000840e0003c08180a031300e00d00d034141611194805540f642105c4140020258240c41b9200c0c2c0d65501c2900c28000da80780282080c004241400800301103e258689028540c081d859040700100c4031214860000765403150301c4100e84a4000101088051014100078014031220801600300141008030b20300c5990f100381040c0c0e0082c40304201103141c0c1d101c04050607840710280c0f9503c0c0d48094084504a0a6400080d03004241c24901c00c18a041c80d4040c4003030b6105865074084603050480307114040d02880c207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 429633902 1250 429632652 429632657
    0x23010b03070e0409140102070c170a0b0a021b070b09041d030d0911190906050315072718050606040f03080702030c04021611010c0b0103031b050607030b040516 70
    0x1940b008050030b295100400d5a401203009140458007602c6460a9a000600540b81e4152000381400710340d40c02100d040c0c5040b813500c0145955686c80d9219490b0450003040f0842e243e0380403131a000510420071540c110106e030201601d080c0740e201e003100b5115030081080b56018a1528442e031700c460390315003103028001034800f000b0740c10704201040d05009040d110500310340c007100f10814842035488000b50103481451403034481d038049061200c204201d551640c4602d01c60b030710540402224800050b074854010400c1c2c5480c601800c43c2902c2e039412130a40a007140560320b520000001c914116280e0341510304c04901003805261144420410780307010383d000d0107016840100003000007030940001084074500c0a019204500302100000313040382c010000200b025840d0040200c00c01c402070030501069032003401e010b490748080b6122001000300c14040141803100d100171500c07418000902160145030b001e02110360515203440003e0280103290300c41d6006a0815004c5002070368401001041809240e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 429635152 1250 429633902 429633917
    0x180b010e0c12011203030609020d0c1701050105040611070513090201120606050306060a200d1b1e060e0d0905030c06271302040e04030909020705100b011223010b0307 73
    0x1c07100311583d8130524400c805250f0780f9a000107031842e00c1d0018106110201500098030000624081c110103c48104003105c004100d006008980c0c1103010b81c0c054648034903064040200c14012549400a140c000ca6400070580c020509105c6068000001c194400e0307899280082c1c101c610582500d1842c041c1e500840c605000150407810050040c1000032820f141015140310390054142540d1106000300380950230030400720f04a41d4018400b0b400d905d00001002c42035034030903144c0c010003c440c1c00e0707003822108503c0e66000a102c4941c02112100a5400584071040800c8101030145500b42c40b865000b402482041c0e42d09180a200390380c0e280c4652031003002104003414000502c40741c03074401383d98413034102542801d0104041c4007500180c140b44000b07030000c1c1841d041c043c044800c241e010f20102d81c010020700c80042d2010541c0e26100740c0d101000b2401413202d80060b502d801c0c0300c031803401005152030a180700c450490012000c90242c1c1c106021000e03600da4001888500c003c40703c0c500422244d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 429636402 1250 429635152 429635159
    0x703020a060e0102130305030406170112060207080403050318090a060608130516030b04031407050d1101020f070803060f03030c070303110a08030a05060102100c0c0312180b010e0c1201 81
    0x80e00b01a155800060005207819180c80481258140342c1e007050368503a002140074008541c010b0480b0380c0001c4600e10300300b085e41c54244d00d252840500c0344000c02c3e964021651030100701c420b0080e01c000d141c0c00404d80c2d4031425004030300c40c41c44901c41c2090f44900f481001062403180710b0700c15042a0fa000740e071000d81d07a503030380c690440d0b0105032140200c2e51803041c0c182c25089842c6840686001d14401c03000c000007030819090003440056001c481140c1e09808110340306c0003485c00200e20081d0113690030050b520b80700c0c1d19045402030054035180b07801c030040019414200b001400c02188900002c0380d40801c014002c90506690303000d0400c4058003036100c19010f0000ca40201c4401d42e03181586406c885140c0c095a82e440074a070025503400c0c2c01d490300d80c420b0020035a0144500040b1080e400c90410454810500003000043d014034050188031032444101050300b0550040c40302003080c24000d00045680b4604840b2641d001d200784440c240b445008540902c8504089800048030440c002070075909 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 429637652 1250 429636402 429636413
    0x1d010c030f021903090c0e090d09060207050f1917031e090603190e010c030f050603120301230d26071106031f03140f01020415080417040e1b0703020a 66
    0x144c407181941d9904206c48009144a517840e6000d02c030380c0341070000e05600e248403800075000300e10321b030030490964010303090620803504c030400c481114450840324002c0982842c0d84845205140780c1010244210303c04080072107801c004014049642c08070520305280700d894420408901400745640d901c55010001300e09030019180300d059000035904800030312880d00d0043c05003182c09150a801c082070b1503001340d210b014483d10813564482019005000140050110840a0f1005011310700d001c022540b00c800c0d0448031f0260303410501c03c0207004103040302840e045c034420350704213404074040f0368036081500404107001100b0783d512282c1c0028034085c210004810006a07410042080e9070380440b0721140c2d2240210190340c000110701401007880c0000740d9903425400c010482d0482d042c283c1c010402006405040c0251007451917403841c2410090321070386080110010003151030620f0394000b0601250364800e03c80c0313140c05200c80b000da80c40002941d010381c0500e400340c98000390151300840c110703001040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 429638902 1250 429637652 429637661
    0xc0a05070c080d031b110607050a0c0f05061803160f02010c0206070b090c03010e070909170d0b030705010e03210f04030c031401050105150703031d010c030f021903 72
    0xd21a02540e01d100303440d00c018501c1d20440b00c1140340007980341d00031044039280e0140c4c0303039034400c00070729211900343c2d02650096950720000d002c1400f04a4006403190250313105949020840da07000b4407640c451480c07801c095a85130340c00e680a82d21944600300e1510103c03000422250000e02d0460800500c020030748802c0008440024243d05000e010342d20580140d469000910045106069440c2141003221215151818230800a40686c0c50007484803050341001445108035240c203800402d50203a54542003a0f01d840b94080c400b01d01c0310114070410140169000103460b10010b804542d1150754550046411030380716116141c00d5004140407032507100b50113422017040800c41c03801511301000c0c2500850940e100c0c0c1d00680b50480c0040d014001c0115651441a2034003203400280000e505103000200301c2a003000b1410381c41301c00010103004050103074015a05108aa4180305645032140700030340e020780000304032080000c1c80c1400c080d0512800740309543c07030600a041ea214109050110540080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 429640152 1250 429638902 429638917
    0x70306050c040f0602010f06050913060f090204021c14040305070b130c0f0e010f081203130c1d1602120904060b041d10080604020609130504290c0a05 66
    0x75002040301192103010100614000c1456500000324400100a0301084a0140d00142d02c2038080c5030034005403410004e0607402d01074011500060140880304540c00418035941c0080d0010b002085407024861040d41d03440f480b0174254001c1c404034100c1120940f10410403200140450b80610021000c207080403a00b5921402d41d07001300c0700c072480d640c0b52003140d034505038807040c0c8a203103801d02030091500d148412801003500a02904aa90624507060384922500130340c1404c150700440061400c203110052460b0044d04582240d4090b5110003507004071000c0500381d14004c050910120700003640d142c100807903c43c015809400b100e401c0705103138462940000c105907030082e00c2d20070200b034602032070000300020300d908010b0f050510428041494102c1004009001c5070309110f000f00100b49010071241c0d03100b581190410ba803000e030705000400001c400d00669080301d01d0b01040004200036003200700800c20004400c1851144146c10303540032044200c401d012908000c0c041d062006006001620030b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 429641402 1250 429640152 429640171
    0x60a0c03140c03010f060302090604140604090e03132c060d02060d05010503160308070201050f19020a0203010b060a2a050609010614090402210106050303040b0c060f01030507030605 80
    0x91140c40c18003055030744029241031070550000801008821900d44484009021509041d030428400c035001a410f8010341c45103140c10312072482c11504982d141c20071103004d004402c40400c09840e03000d20b015500e810000c0011070513251104c4c0440c0d0701c03101d1200d44410410303540014142800030f1140d41d55a8802503d40e13074004021541d444016a40c0d03001800d84050b950000007039661400041600e031040c5001c020215007240744003400490050030440d816a602800c003e941e03200c086800000d18850404246000d40c800003401e03001550220300c1c01c0320319000b11300a000c000105803c1200301d00c1100800c002042c10030a00440b885120200d5031002001141100004605034940c03e0810b501102c0c9491603035540c1106100009845682e107080e04015a80d0b90180d02d0281c0c040740e42460103210201010204480b03007180a44250410809808090142e071b440b80c0c0d5402c040c001c2c40d00704030300116060240e0700c00070741e44046140380c5174101c940003401000043c3c61a200d5900a00000d06134406 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 429642652 1250 429641402 429641411
    0x110604051e060c01020703020a1e0206070b060f04062301031a010e030102070503070c06080a020a05030c03100f06020c040e030a0509061c05010303080103021f020607120608010507050304020315010602060a0c03 92
    0x240c10343c28400b415249000e60094800640c10740b800248076108010000102c01c5007009940c0943c560348180c4003080d9010034001c0d100d4031000002002c0c2201a040c055106007402c1d00030072516480b0f01d04102a070395245000320203012820055050f41d07240000b0401000031501c0b101b80941c031586148040b40c5014000510b004402d40f5807e0440e48003002c291115001d03103104200303481c1d120050503480580d040d811803c00f4a4110002c3c158400075110328821003001c00483c0c400b00340021104d00401c0c0d003001d5081c2d419618200651180058020b40b071069203002c0c5203a840940100482e022003c003503139540e15000800342049201d4010318000b402540d4410343c036100c0b4600d1032040398061800780d11140d11301c3d8034600c100481121884e0b0380c6180d491000340c05002650700010101e81020780350401c3c210b0504988104e5000303140300da10100c0c2542c04c0c10240000160890004d5004034001c0e410380c2c000120030407038442804400e00ca0b1a00580c000c00002d03503503201c19030154107581c680b4078000c078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 429643902 1250 429642652 429642667
    0x90c02061b09060d02120a0501030507080a050304050d030509030105240307030c03023a020405060301090c0506031803040b0c010e0f03251a150f06040e090118060603110604051e06 79
    0x2812964100d4403101f030250713038600601c14041c08100d450010500d030001030640703038129074a180e107a00807031090b103026040c031601500c00c05000e04192420004090000c00141c9068062114000c00f00b10381480903030f9100607041c803103040c0862403106494106071840e490078a5a030900016558030f400740301c1074040c101c0c02015201001d217084086000c14000d0124107000500400044038005400a803103a032402ca000b40004500741d19800c00c560049400e151207a8070310f01c40c0321030036000264140040c080010080b44a28503d400f40130391301690802008101d09401c1012350302c440f01000a07409a000780114400140b2001c8441031040d0070b203080b20b020a9503540c0310310403e0050b1900c0380c03102013903008200440c06442d540c46003111080b0741c02c04d42120f4000100e401440b0f01d0099058010b89a800580ca0000942100042d00304861040c54651020300b44203004090314041191001011490002d4900d800300554080e184c00611450440c28143c00c00c0b04661014100c0300e0300200c0c24403851 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 429645152 1250 429643902 429643927
    0x26100f0503062202120a0b0c03010509151929120a020f07020603010801020714010213090906021204081308161203020705060a0507050c0303040e041203090507090c02061b09060d02 79
    0x201c5c3d1842280028000455641303003080710751000901800341700f081030004100959844071516003104600c045800012504000b044240382c081644030403544245400050140a584146100d03881c1e0a00c40b00441e00ea00001c10054483c08190185640068000c10318103146070b8001d1034004c02c0801e026240c40c156901185454000343d01003900d42e5070205880050003840d081c0c494030501000000c601d0118801050709592600c2d00807681d0196072551140b003080150b504a890019a508a100769032800f490000d86950252100c20712410f1507520004080f6000a0107501a4440542c0641c205080c100700030707803200400720103404510801d00c0000307070b9849100061000c10b1503503a60707994034445414804d20341780d0070009050081d40204401c1280998441105400070b82c49000700b005030203840011406048501c03006412401845800500303240e480d401581c1101581c1c01740d0b00b85642c0c0141d900c40d240003203808000000f200301b280340b49038581280203000170604244014180136440540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 429646402 1250 429645152 429645169
    0x90a030c1704030f0c0608070c02011e11010609050105011223090a170405180103020d140f0f012306010c0222051e160e040c26100f0503062202 63
    0x41d201170072008000d00486901c00c465603403120f824202084510180d070b0008081d4100410074030200268450306882e40d910642d0724007580403604000b481155295109140184020311806000c18101101250114820f029404c2440a002404610107010040f0001d50b45001000021035000c0c115810b40021001c100160804040200640d00c560a10061041c2d600d02c2d00c42521241d41c0407801000141d940580001c0c5603503000b20314444030000a88003074681041c282c0d0044590140300d0b94000022015403000c0700481d09407400802000b114541241880d00a45d082c07070009001c0c2c00864003505245500404c0121050040311314a4080f01c00c0c1030031188161400001400076109100102c10f0451b0a41e40117502d00c00705d0402c168040a001e0321900354404800d00817501e03501d042070354a020b0307682d4081401e408080500040040c9994221150049038645080304082c007020070a600c04000c0102561805002000117868121042d00740c0040c030f19100750403141c0c50030740200580341c0b40d04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 429647652 1250 429646402 429646433
    0x3030a020708121c0f06080a0b040308060a05100c080d061806080607090303030b030a170705070b09150309010e0d08010801061e061121040509090a030c170403 70
    0x740c28981c2c105a0854100718503030300c0440580e001070000c448125210205201c030701040b4400004c021200302e40c0000a04055441030b0090301035400c000341404014070311648514070a07910040b585c0e1762401041a01000e50042070740003c03910301b001035814066001c04119601401d10707141032010403a00c84c4169180354000fa0012000b83c000681c102d045c034000c08020b40340141c0907003014070f401c0100270400a2113200180c101601e405407115551014400b100c40c3d0340e0040034290b00e40ca500c10074902250703c0b51800701c42510a1640c001603002c900025900c107002d004248403400e200010360308d40107400c0541a03005a5503241415107021208228180080c000e646503440590314ac401038a0850300c0e250701240c03100420303552104a90303610b4240c150a694a0303081415400701c20000c040e180561042921014500541072181c04962207005030048420480e035500b403d81e1242185603c86a08140080100e51030b2068580080d2080d03070b4802c03000da4440b41c164101545c944442d502004801c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 429648902 1250 429647652 429647657
    0x20a0801020c011a0907080f13061143140303130c08010603020105160302011508071401030902211015051e10120f020c01020a090e0907030f020f03030a 67
    0x31315040c092050b0300d8144070b0864040310540c1c468985440040e00d40003004216080d014141e100040889455500c1c02c4005504110204007545140e4441d00c13096002c1c00140305c441e98020b0f80d4041488000500008004081d4418030108401448980f0450990002114440244c042c44406544204080c512a85580046004100082c1003814105802d41c104403060f034101a014005030340c00c102120f07540c0003940c000620340c00706405e040340100342d041000204400440d070009605c160004d120300c155800c030b080018040841c0001074048500c0c03103200a42140c0c442a80c01c40a002540302c41507114508010388602c4c0c5105182c13001125140302d550709104050120a126509081c01d6090000015400e802c10625203200003540ca4410958001c1c10002c2c3e4800c0c00c941400c00b03810115001c0e08500c0c0039034990504d818954040c0d00040700c14400103050000002d040e0f0707034903081c040c0030303c000a0241c01414215100c0b800161070b1080c0a036080504120500c895480404c0145032101166 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 429650152 1250 429648902 429648911
    0xb0913050f0106080603060103050a030c0c051c05012904020a090b2803050603060f0a0b0307090519180f051203010b0c01110a0905090402181609060201060b030c07020a0801020c01 79
    0x74080c01c80d804c040c0805019900c540010300024900095040c56280c05007026001400a440d00009680e00d0f5008a80c0001c04a17442c80340c030710103800e49240350505c81d600a0002d1034824070201c400c40481e100100e0384181c0b091503c0501c1c00c080d40140082009490b240b0b81d4aa184c400052860748650314030340480080ca0600703000d8450750008208195201c4c41d040c8064100f00d400a9030fa0310340901920701c0d0702d50b00d8000c2a000c204039440180e2101f005410b842d91103544250000081400321040c805a0003c403845081081c4d1510407a288403007180c01550041d003043c0c640208041038214203d60505c07800c0d56007071041c00790801450003095040d080c10390f1138408400060940300c5103c90902d900d18103100010031182c10407240c0c1d040e10030940c2c2400840d691400056015900048680c418a010308107201c00b441e16068000c03492030f42512100106603588008034201c4480388180c070a12002070010408400c81d4000810f085400142283c070790a844000a07422684030311030046036a95035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 429651402 1250 429650152 429650159
    0x120615310e010e0d0e0a0f0b0c0a0b0108010c11120403030503280e0d0207050f0d060f05040b011a041503020d20030916030819021c0305100512070b0913050f01 70
    0x405d400c0b0040c444142d0390080702c41d240145462400085009402001c0300100d0442c071010003c110725124180c00c030211404550f51190710a0007407941344281000955894945812410000380b5020114180492185840d196480c00c5415402c007030107071120081d881e10980e84030b0000180d00060090801c0c000151100d4081c0b20720315000c4514115001d6400030b00c01003202d9650342203648000001501c00052060080c90140b00801d89c4020701008203141c00b00744824080d0300c4091798140e802c00300590722140304120300a030460095114401042d01811038020b40c561103078020300700c140c2c0c1041c004210800c0140c001c042e4140f92040e044002c040110422200c10b508204034118403201e450b111883d6811501d403000c252007448102c50f40580714561a5004920130800f4020a81100d0368407241500b107440002c0c082d04c03040da4007030b5000b0840017012600b0b183c80c154041e6010b2844008000a13450941408500c2c0c00c800c120301d600c442403440501d03065025004642c49924140380c0c0407015810f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 429652652 1250 429651402 429651407
    0x190903170108191709040203040b06150f090103200c060a0f06030f02040207030917030d05012709030207050a06110607090305031204060605120615310e010e0d 70
    0x141640550182e50088400b420340006001408480c550130180c0d00920210f4240342c1101480382908030350304284000104414006011080781c0112011120252560090313008100c59000d00500103000b98000c000809040d8007a0b88400381450742920605400003001c2d190441c250000d4205080343d4011504102c41c85640344650403100c1c440350b000300541415920f84604040c0c180f00d00a000300e0380040c1c0c0405145c056071810000b060303211584594400e44011240c0c0302c0e044074840c0107a0900b410004151b0b6546a50003595010a01c4100b090420303a180c1050f0150040c1e00065040d4001d810000c14103803280241034003d01016200d00c1141231a03080d2061400c1c1c2d00a1141d020084a00e42c00d10000e00040200d6460601d00a54000782d505c43e810850028280303035000980c4a446070502542c00c0c1c10208540307100c1c040f8000e0400e0001c3c3c5039401e0003410501d04103541005416044d0780441c0749903808a4070b010240f0031000280070a110203039030382120040f110f01c80160344145007903002541e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 429653902 1250 429652652 429652697
    0xb1c0c030e0106170304030215041a0703030b010503130809240406140c0a121b0f030e010e09070f020a0605070804050607030218010e0105120115090b0909040b190903 73
    0x221149030b91142c420780f04c0308036449010364007000b0320410205190300110b054250584025095641458111aa1b003103141405940300c100114082800c1080c1c410840d0700507010b4901c10710300020b030040c5048032552001030940c49444681d50050091070b80a018120021746183c11607450800c4030780d52804d085014021a169019a00c4402000c205140032118013240341030318240e020040c0b070103500e0310f01001c1c2c501107944820000c0380c5020200120138800c1070011102d84e18040c4c0c95403080840268011607459000710003664108582070040307044039215900900013135080d4415107800034050740d144410b41e001507a154002522130360500040c09400e1003450b8004141e03080861070300100c012042c481c001c802141505000070550301c220203034042c104551061484000480c2c06603107440403020594855010000050700d0030a0104000b5541000c4070850b1400808041603640c540d035035904400d82c01821300000110301842c0385003004085c09001c03003441c4603031102a01059422a16000b00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 429655152 1250 429653902 429653909
    0xd0f030801140913060216080c0307140c0d2d0f050c06031005010e0a09090b160c0203072610020d0b09070e09040204150f090b030a08040b1c0c030e0106 67
    0x40c5882c4042c0211308460503c042d940592250000d41c6840d120782040d0441000c0c2000540040c1c40003071103120fa00400300c0104400c40c410398643da056816031600715952440c0404141e0002050700c40075000c1411a5802510035084e02686200788024404400121601030001c0b58186240850441080300a0010809180d02680d81034110720740b8841c80b0600c08403a2040905118501740f100b2090740b11544480d02a10030320320140100700c0c00d46000304080108688112180e01c0904449185078031503803070030b000036030014002c00e03c0030708011095082d11520000b04080401542d400001202d091101040c80b10700400d0058440100300246030035282c803404503a214034000010048901d8000030780e41c43e0804203564006031a91544007080082c0b10190018010201600b0002000c4c61840180026607013140810f01c0302592500602d0f590301c04550004042e060107100c140b00740a45140a061014221000000a4085071201c6402c54000002440010761540d020318008182405548004e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 429656402 1250 429655152 429655159
    0x1e0c031b02060c0f03040f021e0f010503100e19060b130e01030210080702011d0705030f01270f0b0103060f05061005180105090307080715020d050306040b0d0f03080114 74
    0x5502d00f00001000c01d02c620b540310000518040081001e004c41780211908a56015008001800e5429949111044040c2c0003e102d0404140c1c281060351280e415203028034580015400390504103002c0d0407400e0743c01494441d036500c0000894800c00705c2c40c00750000a0600c0d0016a90300c126041030300050071855000001e816100200400060715294010030303040350549405055511420822405441c55680e02d0440e000500b0000815145c0850082c040300c0088007200c034200e80e445103940c265108084000b14a000c10410000d2070800640e051084504c21003070501c45803440c0c0e0301da040140782078200340c545940e42e062162054915104494000f1310888014000c043c035964024150b101e03d0042c0c403a40004441c6c01c94150b4007582c02d80703584010040995004039111443c1503a1240d407840741d00340c0500c210070000c18080c00802c10010641195843c82d103140d0b942c20501001d0841c3d40d00c900d17007224504000b040407070900071040b6036080c4a03581d08500d075403511454091594818082612 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 429657652 1250 429656402 429656413
    0x1030c1e090203040f020a14030d0314040330020405010e0f030c0f0d1e1b0e0f060105070b070c140114011406120103030e03060709030201020607031e0c031b02 70
    0x10403818114090308441c00c0c1240903907295a1440c1c0760b25212090f010017500442c800301c0200d203201d00130000d41010a42503049540190f0414000c0742a5440c54000001414400b4049800b281c40b0709108d905a404071089000d20204101260401160706a002d428865001c41c0501144d80e000341c2031030312107204503031900e42800d040c00029200c030041c100d8644585178590480c0304546605d4918802c0035000009081e480ba0741e001b40b00c1c0050703401101101c0304640100703041018885036004070190743e680303070f08902103940c1c07141840384141c03018005038103102091101da0005005420260700c14891943c8000c1c0d0450310b0314046c0301144080c03540540d181d040003003040c2050b0030400704c1d90440c2c003036040e00306408600d800452440c5c4182c0043c0030403005444c00100600d034010507442c50043c401d4040b500c4503554410203c61810041c0002401130300000c005c9809a4400d4000c90b001900c41d4601c45040102c8070051811120000d10b1345000c01d498101002d01549024038003240b04142d40003510 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 429658902 1250 429657652 429657689
    0x31101080108100b0a15030203220b0a0c0210020c15010807081906063f0b040b0402040b0316061701080a030c050709050c0306190e0a0c030b0d0b01030c 67
    0xd0f150140396880e5034480b603858a036402c480d034401c003500000300600701d5460001266a41b0080195000312100d0004241c9050282251150740225221690f082004101c41d03440740c2080c0c074040c02d000107401d81103211301074011508031214402085000014030007030149010340700218441e0071059114021640210800300320322100807400d070301160505100d4842c400703482d142c9180103200c0707038111071024005656407480800654070b00d00040c10702000c81c02884091001c441d81403504000707005241c0d0300540302040009031404025a0840d00c01400801c08040b1040460720789082d64101c82c0f000380e520502089815001f413249810343c10280000d01642d07040882c01680c0d00f103444d000604001c00c960031030050000611070708000c0d0138400020700135810300250006142d0000d55005100345840301c0300031301c40c010010407001280c6808000406559441181a004081b030201442c28152030740c03042e440559070800c415622520840c0b041150f5419401d195200700c0c4950080310040b05000c0440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 429660152 1250 429658902 429658919
    0x1e020d050612060703090302070305031908090f0d0507022205060414040c031e0b0106050403021018050402030c0d05040b07030510030819140c0a03182405070210020102040311010801 80
    0x180d5120f213890802080d110303001c4c03800728541000c590001e82540408142d05161940d20448180c9441081c3c1e83d08105441d0460090b0301c03482d25802240055021086502d002401100a840c031140000e050300d2010104080c64a90b000180c082c0503081c0350f652007080000e1400344500d00c40c08032214007a90321460195207990640e50940809800c4d1800f010002032121906040034480a51103001ca061559440d80094441d070400d0000300c0c424582c022842c13294038420940001d404d00e800b030280155510b41000d10000394000307400ca5002000403c10174030b04181c1409503a00861259540540780c0c60318500040880e00040c11120080301d4403002080400e00c110180c0b4203624034071513208260f0f290408199003031448140c0b02c0070886404155842c0c24640401c401c040d00d8000d4a0740f000c0c842074105440d1009181d40500c260040042066a070000305c50040ca1340b0842d05810710915080d02600069000340c103840f540c0340140c0d0000340a0080010b590b608294202c42030034000c4c8294103001c2d26 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 429661402 1250 429660152 429660163
    0x5010f0f0e130f0b070e0d0305031501090f1d0108030a05180315161106060a1802041e090b04090308072f161a07080c011e020d050612 59
    0x2081c00e0356000001203181601c84003031854500d9440303001c88940c00803516140001c4181180c502003c5900c0700d408a0603820101d011800c060307490755489140d9500e20500e90720b144c840e2115103040260394500418040c00504958002c0d0002c0c00c60081c1901c00001d00718640b81050b00b1141c40b68005220f070080003a00003003503a000040b224100d80d201e1490301c1c04a460400020142c100203103800c000c3c400104041d030400000c200c01551110b4604001101c4182c0c1d074207040d02d9007500102400010015400101021448920210320142c03405035601105a54000765035801401c10760380510821903d0343d01e100b450b000c40000d90301845044035548000e0b1840d1402442d800c18440140301701061100a4214448030b03008410b03c060300c0500c4080b0003a59506032001180d080e04e40c0d078001148820403075070140c88280800081614000c00caa03104540340c1c00581411400d5074989406000e1906c04144120080c01104070042e10354074180803000681b60090006030241e00c2c05541071140c1240801c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 429662652 1250 429661402 429661409
    0x15101202060f120c1b0c0916090b2b0b18041a040312230a020a050f07060b0406050d02010c021002070b120702070503030f19090b07110405010f0f 64
    0x35055201e48880340341850b40d226900990007a803840900300643c00d0000d501601c0318420000a44440c907030020202580d80400c0c0000340e9000c880080000c441d4080c0f1807011000743c0041c5082511b00382e0714000d041c0d4980191041d003242d20b07480310405859082c540d22000c003c2a41c2c20b0148650401c00f000705510350f0808402c14074150350341d0002420b000341807101903440c25550464107050b00d000d003801091582020380d030008642c109140301d00313402e044a502e050b04401c417150380204d5803902007181c00254401d029110910400f845118450360786040078000e054010b11340820380d07040e0241044126481c030b40068ac0701c1c5100c1e054102c050f0768400d0025410941c15103028150900107441a4580403007548600200640003584000548940d184280240c0b11502196049502e8008240d00c81c0038000002e00318680511100203500542c0703c0f501c0e140501070a18440180d1550b442100c1544856070940e0103480c10b000c01580d03400d10b0300c01d050040401801008950341000100942140d11f0320 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 429663902 1250 429662652 429662659
    0x60103030e011b080703030902040f020a0e090711120904060f24110706030f0f060b070b0402011713030212040b1608090405040f050c090f040b041a0915101202 70
    0x1a65108000180700f00000c0c054120059645550380d92030300070040e01182c2d000b01d003c0c50034119038031600c1d0a10b0095500d17900171511161010814201404000c0074002d003120200481c4910020303c410080c414508240300000b00c0325512460030f030a0000b03941041c0c2c0305075054030201000b00283c00e981c11030118404103103200c9803040740c4074000485580c070141d03880d44074034041c00100103821601540000032031804e000d000d220003511880603404865540c4601c0408810420401c1c3c00261141d0301c0780c1d4000d10504020b423800e10214803002200f40708898450b841c07407460340030905064040040010f500c101445551815050031038005440c00b89554040341850314084401c2041351100170f5504500c8064810422031529044c90580d0841c4550262124082c880e4049806c0c2040c1b0756480c0700f0305240003640d5403a1141e03031300d00302c9079080240f06660244003050040460f42c490b04c0514007a10621000301205c01150400c0e0320780100180400080c0f91900d5020003880300c0003103881002e260101c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 429665152 1250 429663902 429663917
    0x9050f0603060a0801050712061422021908150d170706020418020405010810030c050906011e030507030e0c0337080406030f0b090a0203090a140a020909060103030e01 73
    0x10000f141460000341c0007103001c0d501b006c01f00f00006a0100301d4182026100b14180722155590000e5000d40d5140b170b0034a60400f84811a684c0840c010f0b0350700c0c03211007100c041d0040c0f070001c600030144900eaa50104090008644006000d02d1188880b00c3c171400c003104560007180c940c11a0b80d0340099807010641d059001c84c0219100d02407180560507070f00142183c2500c0c2994800d0900350740c0c000d40c001d024440c04510360b4004141ca01580075810410b0f02d03440150340000504003420002d65900050002d410045d00c496400700d032500180038200c0d10349968501058a091040380a8140c1d4050802085c0d02e038008684c40806035400580c12050b102141c103000713074000010304a40c3d030421031100d03070800c0781030703c00860303030400c200354004100711495642d0070000071103501c0406040d80d0a030009564030025400115002c1d4645a000355000b2031164115601c034041c941c0d9010340044144115800c5400021002c006d43c2000c02156511203000c402034642c640c15036030003502680c1c502c008541004800c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 429666402 1250 429665152 429665161
    0x30d0b09091e01150e010608010e07080606070f12031415011d0a050312070303060f080a1209050a0807051806030a03032304241118060403060501031203050709050f0603 74
    0x30f40c000c010b440911410526101d44411417200c040400b03208410014800300c00001d10000000c00580c020803040e40d620780d85403290070400c901a00300800c15260580d800c001407000400c0150901c01d8070751203071800710f1800814880c1c9640e0744c030b009255041e000d040395070b609001c0e0ba0041c094030100900c004140c2110340314002155054074160082e940510400d000000b1103405400034003840c078400d640520089849440044840c512413040c00d540b50300001c2c2d5800042c0040d030743c0500580e81c61802c40041c0d42e039800041c5d440e030420f510023101500b04240900490030821418a05121803102031081d900348100460b0352002000d10207020540d0354141c0c10f1031411400c00200946411459102c060b00745410301d81c20300c510003400381d0003100491100c20701800c254010980c2131072819030098107019244007040f1300058800b150030ba11107010400480000ca251060b280a54080c0a4017035102250b0100541141e0000c0d0200c0d041c44a0310b5402c005655800188041001c41034a03c3c0b6120313141c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 429667652 1250 429666402 429666463
    0x20c0603091203010303020318040903050403081803060709090b0a030b1f09020f030915090d050903100905010209010212030105030a20121b09090c010c0311030c030d0b0909 76
    0x101e8110310b498000c000000404c0c1a800000f51013140c40d01e117590200d100c1050104001c50b064500d00401260082c003003000401d40920247c820f80d06169501070a80c0041c00000b810a101203690030041a84400280405030b0984500c10254505036091601d80b03083d511406a0b020004196007803000200185074500c80c01400030324001c04501e8001d54442c01840a1f1002940003140d00380030074420f07502c0600101c00b685a05a0045070b104000e42600b41d40c0c0c400032903140c0c2c0810542501480b40310b80c0150052075901c2501902c80c0103100058460030b0060009040c05922880341c0c0d202001803005104580d0040303035502c1002c2d8454440840345800022142004034802d150700c1e44802911040c0c04070100c0170401030b150202c4542000e4142e00110100282008240c9407500940d000000b108010750140b01c1008a090080c02c00b01e56032885103103407074519444105d00d210140c00100c0d0005428040c0d02034803c3d00002100c60951521b000d05607a9503d07010200000402c0d08600c101110f00308 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 429668902 1250 429667652 429667663
    0x60d1707050303040b010e060618090618040503071e050729070b0601090902070807020d05030f1b0717100924050f090106030b070c0602040f091a030d020c060309 71
    0x154001c0c01d407522481c01c2d04052214003403d1048440b49501080020040c0c03404808850b440e00f00c01e1270010068813004213000d20b08000800c01600b0a05001421040d60a40c1000502c41d601c50401196216079500c1c0c580480c92200301c041c0244c0c220701c0d500000294011603118181e41c4282ea00d44442e1148295916090055245c0e038482944002400c1c0180b00c800d0603001e01c91802a200e40d0b480b907030b54250f003101701c0c0300304280a4505142844100010300d448420340e01c1940c00790303088900705541310700340150f13a5204035990400300821010480004c001445000000e04152200100110000d141c2c107441d07800c071420104403941c3d1a0140c10420070100103030b145103038400f0500c0309458598450300c001000c1c1039a0301074000d2003180c009071044205000c1c00c2c0c180da030301c2034031850651140003080d541d0840207841140d800b81c09010100d00074481c2c024103001000c07460004a821401d178001c0c140d0448003075001d00e00a4010094000e2003d0300000e00146070a019245c003981ca80d1914100303410324 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 429670152 1250 429668902 429668917
    0x60c010911040b04060608071809110703030501050114121305061f050603101502070f0b0a02010b06091020060a06150c110d02030c0409050102090108011e0b070f0c06110f0105060d17 80
    0x210700c0c100301d44c80bd01c0300810103007104d0791080c2c60801203130340ca880c01075801c070f0907004032801f10810130000880c40341c0c62240e5098000458803100c0640d01c0380b9545031800c0c10340c1242c418000c04051014190328401c0d0000e548010035003961f5040c0b950404414184400c00300307004802e4968030b000b50f0201d1062003008000c0081c152481c12074041c0b603d88035104070700d42c4071000d01001503080c42480c41036480c080d0200c41c0082d2008003030b6800301c0c6200c0c0003500c1c10100802240011b1503c460700c80c0904900388003162080c842d80e040021200c2c2000024400f01c00e442402c00c0802880d07440c202c001a0f003005516401150848251040c5c040b284002485c0000403c0d03201c0c1c1180c00c0c4000341c1c0403c04150040e0045c80403d0301c54004503a2905248040c00003020203d00d8009600c2c0001c01005060b0401400304a00500154829003504d031242130400c645a88501c00152200c9039074840684140548010314100c03100030b000904192000800c4944900c1020303000558151814064060240c21981c8030f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 429671402 1250 429670152 429670169
    0x8070507021e1002071a041212180e0403110c03060a0b0d0c08210a092304021b011104050109030b071709030c01110307020a06050402060c010911040b040606080718 72
    0x100700c43c40d80094a43e600351040220f0301b0340b488040502d40f00c903101030714282d8111401043c0f40d41d28a484000d00000800a18414014076411030b44804403c44107840250200c001c40710b0980c00c0510b002000e00341c1d50701c1040003d404c622001e00082d0f4001c00e103644c100c0420000461079040510014040d4014680020800e04c0076500c00104100003003404480014500d441240314040341c0e49010b403d102d043c58400000304182d9060064141c8021401a42c0001c01c000c0f400017501400402d040741d1040e0007441b81d100200c50014400d940034003c0180c01602c3c0112207081038607210001e8030b1201140001010b15030004005a0a688549031284036482c1004100c2181c0c104203141a4a07075001c2d00c002400c65082c00300300c044866100044a000c1c060960007000101060703155800200b0024000700e0303100b0010011140c41c00f10074000d4010341400b44003042d0404e5020800c0008856004084501950409104102c1d0750380001d0300300d81c0a0440e043c00206002008a240203921007a00302d0f125 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 429672652 1250 429671402 429671419
    0x30e0907091d0c1206060f2701051c0513080a0c1203060b09040e03090306100602061f0b0a03140a060501080a0c0c08130302041b0201140c1e0d050a1b08070507021e 72
    0xb10341040c8d40e44101500c240751841c00c011400c1d8401100c0a10030754905c1c240030041120310107240075056000d1544050300041c0707165602043c0e551103d5035800407561800280342c114101c0103101920b000d21354a00b859003401c01585140050138041405642d1b0f119110760307070354203c04007602010701c12034040c024001c0a4913280c0c43c00d41040568610980500c0c801480349270001060b46494048204d201405460200b005a251181e001c2c95a030214031403604164891650303921488141003040e000b00c20013800031034001d0600000401c60740004003009051803c10039030401e8280c207c41034060700740d0400d03085a43d405182012410000c9264402500285400c512414035043e440d130700240c4441940c024402d48140050514406800307a07000441c403c0c0030811217988014040c680a0039511402955003003100e00d0412204485d01110020398403a2030340502c0c0d40c420403c03e006881514142004281c604090034014040d018070b42c1c001303016491980280c10b02c01d42c07410051001c040001d02006 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 429673902 1250 429672652 429672667
    0x12150302090a1e020f09040903300e011802041d03041203080a0504030206151908010906060501090803031302060c1e0c0f0f0904030e0907091d0c1206060f 68
    0x10040030021031040080a120242600124001c4400c0500f1072442e17207003818940400c1000030701e1240c2d0102c081c4180040408420b0b25003a0418400404a143c51505415840400b01c19154051030462880c0d25200c2d0801614018209a00d526501614001807480c10340302065105c81084142121911003c1800501540401032414060784070b5035440d6002c0c2c841c0c84204058030001e540060158100c403000503151180585080c0c96a02c004003222054500d48079601c0003c1c940342c000a04e140d44a5018005101007400703680020482031910405051a14181c02c2c0c8a02020304030001c400307000b034030a40941d65058241c51501e0350110a681d03200c0b034000360f01038002c4049540344e10b003400f40c040e980c103803484c00b1807810b000303144090b240103480d1049008001440780c00510840a12079580715010407915006c0e41644a040c9985480c00101d0404107201c0480c604404400c9240c0e080307004000d0004000c01c1071f1068003202203544410364844800003a036034015602e15800c001030104048 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 429675152 1250 429673902 429673921
    0x408100207031701080a030309060b060d061401140a0e13021204020f040605061e04080d090306060905060f0609010c02101808030702090408031305071203020f0d1215030209 76
    0x24420644aa12041018095800003c001680c248217410b1950015070015000c03d0003070300040c29941c0704800000d0348000c40d000040700e03034010008e2410419540d010611040f1890054a9102402424001d10000c0b40c80069501c40c0b040300315100c20001407402e003032100e844282101c41d24180c41641903450b401504102e0301d0400c4121000da11481512410407600d0030300b803251030240c4401420140c170b007980003075441c0400881e1400048941c0c000704130025088000b807114000d0910301d55200c601c02c42c55401c110054075204c1d0060541c83d440d01081c0706440d40d07001c2154550302410b680c01600d0743c03410401038410038003410f006500100b0200da156030055200580081c2d03d0503150544811343c0e290b01075680c1d02d00642200a401420020116011560100103907600c150084054107521041c1c0d030704c03103007045807503071110b94540042d44045003010340500000200d41e011000800340030303c140304000c1082c984241c171f1011056840100c80a01901e9005084c00b458010348203620b1401d104170b48 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 429676258 1106 429675152 429675157
    0x6050703091806030506180604020d03030e070f080f120f03090709020a020a02090108060f0c0a030209090c040806090703031d0a050d050a0203012706020f04081002 72
    0x70301154080368081078441600b5010442ca0314503e40b15142400282181210420310f6404444244000424030b80c0903404881c142e2502200c2e09050700102400004c11031a03004004000c1805008040c0c0d0604070b83d45103048618420b4100d50080e280c00d0070780022901071100b00460300e210003460001d150400d83e0401274440c0340b90380300c03902c0c412a0320054010b070250704654610002e40c0303460002c8600500041001d44070030310708420b4040c000381c4001d08440d008180803a041103502d10079410b4401401c009000c1c0d0001e4241080300c95415041803241e01401e1040074009a04c0440108044003141e600d91102101c400c15040d011041c441280212a0000011a000241503984000c1c241c8118000d03806130246100030300605082d1f0340c0400203492400b20307540e140d44030726800740c000d41c00098109000685401d4124810160781c416544070300c0c543e20440c0b0400b180b15445030300 = true := by decide +kernel

theorem cover : BRFrame.Cov 429496402 429676258 := by
  have h0 := BRFrame.cov_init 429496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 429496402 ≤ n) (h2 : n < 429676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
