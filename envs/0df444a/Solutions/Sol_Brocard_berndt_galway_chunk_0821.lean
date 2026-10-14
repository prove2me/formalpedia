-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0821
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:59:19.23799+00:00
-- url     : https://prove2.me/submissions/127c0083-cedd-4a39-b541-0f92fe67cfba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 147482014 ≤ n < 147661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 147483264 1250 147482014 147482017
    0x30209060a020309030706080c09150d09050703170c03120a020904020708030a060b0408102406092c040609110418170f0a0f0201060b0417010b030706050f0c010908 72
    0x300701c0d00116640c0b034079a001e0602c0c280242e4454810070410f0307402e004407000340700202c0e040510308903880c080309071351082e012455100b880802d26840b40f5101016003046070110f604000c50b409004c04045038013005503000c11900c00c4881c1c0e090039401c100802a00da1034200d0310b1a4100303404031001030a2556001c080f400f00d0f40300007801e561480e0003000300300a00065000e40c0700a0404072040900703142c42c0c40074260b80d86424620f0f6404260320740c10700d2a4080d606802c151040810300080b820216034030350010701444038902640c0e00d894403010808404400040d0704201c208401c100c0700d403a40da81e6448010007003001860454562040b080c0480c450360b9035004420381c12620140740300800c031240c58240d0340c0c02d01c620004240c0314418480c8a414400315821354104018500b0000c4007070500e0041240100080c0e0070a01440001080110394410700c21a80c08281d55000002c00c860015101056a660791922440000801c100302501d03030030007124042c00050b0281400401c1c050541e0340e80a004d07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 147484514 1250 147483264 147483277
    0x40c030b040c1805010510030b0604050d081603030921080609070c170406020d14030705070f050102040801150509041211011d010213060512010b0a1106090606100e130b0103020906 79
    0x20144c40d000140400d2038a0002900da050040c1401c002241c00040403810758003c81c85201c3c42450058506c80c10700442404680b069071a46e01c9980b0b90540620380030380141200c2c0019215541214081307442ca809000038510004043d403104500c5903500000c000b03a04100411041c10080781118100004203442c2510103030084000b039044d21745040000c0203203010b0104581004014000c0c1940000901c08401c40341c00204c02c0c0380065491105003400801e60094540040c050340c07000030009241f07074040d44134a01030740300300213080d18140d0355030300304003d940381078034068504001c840c40c105409009410032685074065000105120030034070b2510b2150342800302c104800365000201400070354508009007025000608105080581001e0040100c010500a100845000007000d0b1002d5001d607040503003140b1030700101c42c028034102e1580d5483e000c0039242240120081a40d1603100c90041841c0c2420110151504a011105240c3d20018080c000390f058189582004100c106488030401810ba = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 147485764 1250 147484514 147484559
    0x30906090d0b04050c01080703061d04020a0807031a0109050f0f0601030f0908121015030b01170403170105030c0d020f1c0503030708090303040f0f02010306090f090302060f040c030b040c 82
    0x1e4171050780024009550003040e1108251801c8400d00551504c0c40d0481d4401c2059540e41403160386a1002c5000d08170550411402c0e44a000c0d000410404100e48030701072126892255011641c0e0741c5a113006440044e03888101c4038180ba00040d490303481c3d0b05011030744403505240c0840c007a00e000c0e110703404a40c0d5455003a0390544001a0800c98608681c40741b641082009400ca03440c02c2c5800001843c000800e03100c4410161a01c0421f20079a00c668070001040700f40c200390205a00305031a02404050a0030b040c0000e0175100c8000044a20303011801c00b0048101a041d900040d801d41d003000030740100d0901c0240e000c5180090590248074810781801c44500c00d034021903030307800c2403175025041001c0100f010f001940f080040100007000d20703200d01c000b070358040311225a400b014401030707001c1d00140e003141144c070f880d004c016000208039410620030507021390240d40c91030302da04420340d1458004960142691120300c00410000b01d800050755402800350180c0c071141a201c4400b0140e4002e401580d26 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 147487014 1250 147485764 147485773
    0x9060c03020a080618010e1008060703020c0c0a0f0501050d09050106080c1806150a030e100225020d080f070506090d0f210b040b03120706060b0c030906090d0b0405 72
    0x21843c0c0240e4015000f0703000700c401c03c2c1105100d45400695010500598030808900000f19a14036031012101014100c260241c642600e0103c10060094000342c0c0c0003044c500c1a040d05100504000d103841003901c040304081041c250402c401519158085071661001e282d5400819011800030310840020b040703d00e014001c244a240100001d0820461020034100b0f0254103008a1707a907500d1410f0004043c0f4418107440d045010070070740080c002050040043d00444508200b840200d50040107089841c0a104005070040c0b45060b4541a0085000390001030151a602c0841d600070301500340c0c1c1e06107040303052910313038596545410050180c40c1d0402c194814501204103581001c1c00f080c80200030f14040c0c142103100018030104001036620f1030901d0303566220f0b003203040d1510b802c98030852401504980004a40d0b05489005611070314003a00c10301c3c603055011542c01c01500440300b902c1e615074015402d0248c03000c00c0081070750200c1c40551340480d030724086100291124092130b00c5240508041d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 147488264 1250 147487014 147487027
    0x15051c1406040c080d0512060a0302090f0402150903250506040603020c0615062a03071a06030a020a090f0b0a0e090d080c070308040206040911030a0e0a020603041509060c0302 77
    0x5440094890f0848284c94010300300c42091141e02109a4010148010500134252145400b046442c0d010750400303900300d0031940411050031350050115000350b01c242d0704403c10b1814102480b10501070212090b9040c1c0004100c00b0081d82c54600e40c14a14050025407001c06588400080055102d0360044010a80110388808000b0050009943c0030301084040e004207108200010758520644040039201101d4401a4040b190b0894050104101c04000c50350b8880c1c0354181544d01100c0b0302e000500808c2040c000819505000c14019015a07001d01400c48060500d1602c0014111104480c02c40c559501400c40e240c0d55a814210024030a02d182809103003040403941d030521400c48200820320103007500f40402844c98400322a5040c3d01361808800c070340c42c0d030310010b07443d4480e41d4410700c0c48609151108004400c410001d6010f0500305104101c00741d42000f5890b190222050b0295212105000080200d80041e08020380390780d2414000500314204d544d008100c0d411801c20000007680416034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 147489514 1250 147488264 147488273
    0x301211401020c0609070603020909040803090a060c200f060c0a020c0306040309060e041415060c0303150a150207090b011101090302010608010c090e01140112020d15050415051c140604 81
    0xf00d1b0090701483c6810f51502104002188004001a1004041d0704000002920784402446a04190380e40145d040c000241c03090701c0200310b2501c000316401048a41582407103c00c100040110030780c3e107601c028020300c0d80c3c0c20034122244d0b00112000020350040c100c506000340e40500069200f584603858420445091250083c003408034884a40c0c015440d144c942200240400c0303c2642c06449503900c8440021104003040682c0204515201c103880301000740484500b862a050894030700598440c0c909640e505142a103014000441d44056000214140704020f0a03810141d4034100c107050018400117604052808c4496020041d80183d54808052064103000c0c042c44020101c103181a40c3c0d080e0030a1002c01480030188207031484800314906007034550740101c0080041c000e5485085440380011170205000c3d04010424046840c1a854081403900d01882180f5003901915840c4a03000d04200078040d0b001446030b0702140036584840c5a90000c3d0054185a40c0300310b000c2c01500c55401c140c5003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 147490764 1250 147489514 147489523
    0x1208030f070e010e19120f022b0b040201140a0801080d020705060409020d06032003010c05030708061909110d050c090d1101090e010b120601050301211401020c0609 72
    0x75010401640c1800c002d1681e900c00b940350018078088448a0801c0911240a0109125940060003846c80c050401c01171001d8140c004034018020b80d001d210700c1156061000c0e50069014444500d0350901e01e910303002c14030345012998414418100071041c11030415940425411841004000070710290040c0300502003031003c080a007000d4001444030500b000005204c0e401035000300c11050364082040030b5400c0c07040d04488020f50b048003280030900c940d140d03010031880c2c180719064041c0d800c100c0206041c2d031080088078402c804a40e1900650344400040040d03169000f9401544140c0b00d90700820401d0051203030380080340c5882c0e0000d40d5028154048425220f009080246402040c000350076551501104088050341c044e000c3c2308110196001070300c96401c6600300458003030102002003040400c0400078400300210791007110003691110700455452109026440c0d1840700403108615010a910000c1d0b449880360031240c61058501d0a04c600320b8101e1120804290b014200380041103030240b2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 147492014 1250 147490764 147490771
    0xc0f05100e0d021c0218060d1b0b07050a140303010e2706090304050103050606070201050301211b060206100b18010201110307022803050307120f05070203031504050411191208030f 79
    0xc112071407610b047c00001c0e890b0170102401a00580c0b00310501c540140f00c0e12840d0014010b003032003040e04c0e5402824000d660b2031211100b1111070104a9500918510001c00e1303e0494150000301e03421590381e02c5942002203d424001d0076100ea43c00c403100b040c100103010003481900e01500654450745003e00050039107001914050080300c2c10856203001d41d03400030440381035800031030300c11210303440340d201d60000702c800010040e215022400401d110940001c1c1607000319407003942191101c0e12420070071400c100040c82000080c2804203c1c0203100340d00440b00e80c6400005000005850044090343d2056500803102400140c2100c0310030013408441d05c80c1e0320a502c07005c1100740d100b01120b40c0c000c0c0c00c51201805507020701242c3d106581c601c02c41d030382104d51800800034082c411410480000382d038a0300162036101802580045411584c01c2070322403144143d400148c240035050b10750081c041d03000400d89255140b0712001001081c0308480c010044000781c8510402a50380c58907600004140c0c40c00b8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 147493264 1250 147492014 147492049
    0x90919060b0336030a030504151b12061a0712020d271206050702070602010e0c041d06010b0403021c03020c0f040f0c03090c0f05100e0d021c02 63
    0x900600003012019001c109000d001102400d1241c00945007900b00107016031a0f031a4140302c00650a040b05515802080c0641c0c070840b4241000001400054160f464808820000c80c0d4080d000180552060021146c2c0100b40880010703200d4454a10000341075010900c0c020386000000e4075800c01c00496103c0e012581c0b54400b038120740b59280001015070340c0040b100c410341410808000c4000410101c00d90040100a8910f41c1403002840c040b805010f0443d00b510240c0920500090858018084c10240d03090440c050038454484404010040441011040120303101d00304408514004000c814080d00c0842d0015403514554810010b00070140000303072204808848615000940003c1c0c82c20700504200c0e9440c07407800c41d1802080c010070142030018100c900349420039148a815510034070304103004844070200c440c3c880c51000c280c094a403248542040035900c06c2c02200d0700c20345002e100f03100c0040058902e210150001650404032500b04000550007008010840c504198080710b40d4140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 147494514 1250 147493264 147493267
    0x911040501050a03120210090311010c0f05220506070803090c041a0d0609060c030606090905010e2205030316110d080610050702041506080a06081002070503090919060b 74
    0x140008160500ba4504c0018041c0c141d103035403903811798028064428003960003281000540154140100681c6e49881c82640e179501e4030051541152260081c040a9952a02c40a143c0b0181340c00c3c0b0414030f50861510100903440c940045200d80d2808009d04400340165121904e9003006017180c0e05140c4100d505611036494a8009010602c04003080340c120712302242c10950680071405e22002503c08800e0050460389007102d0400c00741d42650280054031a550b49011003141c49442d500f0480714203000350141c0c5000340d0300044441080c0410b5500d0890701c452150080f10940d9220383c65500150303840d15202c0d155a0380046001d43c0f004480d507000e00c2c2c64000f4045040684000703058940041c0829016081007400082c8450103035045881c29a400b602c00c10400700c641100e006800d000d4082e810008a40703c004c103003003c004d4007404090f500e440010b1b0001110701071002c0c3c0203501003442120740d0f00060008401c039a035000e009078421031402518080d034001a140303e00032038200f5001803c2001d070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 147495764 1250 147494514 147494519
    0x207120503040c0e0402030a021216080313030b04050328080a02120402040510080708030d050601081608040c03061e0b121203130c082b020a12050405130911040501 72
    0xd0710108012150103035400c0c204c0b502d8500210b41021002c01019400c11b00804600e072061400180c4001c0d07403448010201300c0c2076160030341c09072640700c2c041401805004000d0300f07102050500c1039480d04031b44a40101d0745800000030044043d094954648035410b55a04200c0c1a05a0040c201c650700815601e0110318211644807200c0a0600140002e801540d4450014100d21140310a400c050800e400407248440e03500c0c10031564a520544405a4281c20140458055400b0f48242030044106980c01d000c603082c150030850b100c0b9001001500e0304800c4110000100f03050348645028142c0030150003181404101d0100c042d0b40c0d00401c0300c4d004543d41c181c0a212100d01062855681311848000c40d03494840c00c100405d0400d42190280001002490000d00c0b8000055048006841446441c0030034240b0490440038018144858000da00950040c0001540d504400c040882c041e0811070704140e183c0010075440104014031640007540c2d0003440e401c1c00a02c10920701c9504003114140140c0d0b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 147497014 1250 147495764 147495773
    0x1090b0313171309020415170403030506011403040f0b0c0c0d0c0218090a030306090209100305040201021e0a02011202090609010c03020c04090c031101020f0318040b0a09020712050304 81
    0x40c07406450403225044148000c80c1c2c100031100b444001440c400002d6031240052402075000c2d1041e1f0109000030b40110b50030314007841100800341c40115603140550781d03e031400c0d0040c101c0100b41034100803454024a0b00c0100c1c02c000b860040c2c0c05000ca01944000394504888041c0d0064034880007400144060310800500148840c0c40950034a0b0802d81140107202043c0030070f1904c0002602c000c04030003042280e1400103800420715010350303028010181d840c01010228403401ca001d5800001ca07503643c0b00210300030303004950800d1040c0304032841580c261035040f500e100320320240100c07500030f42c840748159a480300010b0011017400d03404600c0d00502a00140305841129402414030100000a80c2814000d020346404258007038170520001e0428500200e100980e80411200c228000d030b215030055100144040316034030f0090043d071030039000d400c214403240e40000da1185d0050b00c0c0c100c64031941e118242d0b080014041d0b610b000d61500f22516118038041800d50f13080040081c140204400f08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 147498264 1250 147497014 147497041
    0x15080304053a0b0f09030a0f02070503100b1003020f0405010e18041103011508060105011107080303010e0604111201050609040f060801020a090e041a0709050d0c090608150a05090a050a0501060501090b03 89
    0x2480304e418411140a08000c8c00c0e42400740d01e42c40070742c1c1030258000d091600c0c2c0d004e4011102c1c0f00c3c03040f40d80510803904644280d0890042c80c1d070469034076106120034002540100c1e03807446540700050490000254006035100d84100455084a20f0841c021a090751401d0034050041c1c1041c0e2295400110381c10032010380da032000148603030b42c100908480d2840c050304041c00100c000d08040030540740e4079a182d04654803207030015159103015500d003085418400d50300c1c005540c2280500708400340c460b481c060070840c02d50400c01e0a20350140d0755803804400b40705940308250091000c0e400150700c500607948060181c5050341d10824020304004c0070840056460400703100d0b543e09000309a0792b6512004402c40c0c01b400700381c000a07000450b20042900b032265001d04503040792a82141072103e60744443d003480d11190300030014035404007640c0c041070078614140c10050f8000e4a00c400c0b02d0030700550751520792078504141025946655103800c1801076591285418000d00445000f10b0b2945c01d09040c040110b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 147499514 1250 147498264 147498277
    0x21c0b1507060c181d060a031109091608011508060c0304060e0c04141b04080307020f0607060504031d100e010813022215080304053a0b0f0903 63
    0xc46640b54603c1c03e08074040c1e243c10500c0b50041c0007144504d501d9140000c0d425000d1500d61880603412030020785649004d4000c0010b0701d03805594626400401e2042c8100301e14041c02202550003201d0415100d0b5a0410500b00108142030000c00d10992491142c0c0e2010180c0d04104d1070394000a04228100050104032074220390706c0580021800c031105802c604141201130841e46c810705101040c0743c502003c2d61a00e009090100b02c0a01c0d038415500380c0c10843c0304031310442c99142c0090020034098500002802c0040742c001d01010725004031503582c0e20840b40c00300c0c3c0071004101c403291004400240307a408224110400c0d01c600e200c04070046009007118526008041c1085202e0001402004162074121041ea901400d0703920a00c05000400b40010121075080301d01030b20300381c0c0303580404c101c1010501c2110707803850246140900300014410b03036038205440211076101c0d80c20110700300c030408401c3c030315100b4074001036a4012119140c208440280071700040b000160107820701c20050b8020007155503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 147500764 1250 147499514 147499523
    0x50303040330050105040c09050102060c0708070804080604032003030609040602120a0e0c0102150406020f1204060902011421090c091f06050f0301031212021c0b1507 73
    0x70b15030140c40d202d44140700d0300041050002610000480c280a64000d54143c40007101c00744190031041c1022900c000e4103108003401079218401084d03401c2030314402090094010f425803450040540ca40c40c0040c0d100c0d0b440103d81e80c2c045001c000c1856880f0341c02c0e03560325000d02d8031001c0d10249485104d640b8000505514442d107c1500171074204031241c1c1c11283e00442600c1c12150510300552000000c000200810799140146080d41c0d0f915031001c18007003804a030f50480b455030b58070395441c3c0b04000c0d0001c9802103000b40c420002c1510b1081c425524032304c81d601c1942c0100d51151540b00040452100c0c07a114900c3c910144100602c0040da0b486d40c5051078256202180150707135070014180790148840301c0b00e8002d1009803d010b0b82c8440c4501c203988107075030071102d218160ba507004d048078580308085108039081c0d070070300040c00007940c14904c62100c1110b80c81e0082e502e21501c220b0b502280e00c00d00c60203280d0401c1d0000c00301d8003102401900444c0c0741c2101c110251501400000c1410701c0369600080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 147502014 1250 147500764 147500777
    0x7150906050d0c03061805060f0d0503030406090203010e0708030d0f060803030402240d020408120a08040305070302070e011502060601030507051e0708070b040501140402100c1412090a0506070503030403 89
    0x103128405d0780000001d05455407010004840c108488005000954625008852403c4180d142c1c0c2041c00c1400c4040c7c0d4804000c44c0b5503522900c1d603500402d50a10200c0e4955200d264a00c2d0401c42044070744041c105180246607903010090740002161030a15250101e24100401042124400f000f52688240c040d60ba072403a0745408241a803250504460720342403c180840e4451300030f06190702800c10b4072180c00407146860405042c020281c024034203044002003e040010340000e20074030261035202d10a0045403086e039200c4c1c03482001c100c000d80008200740010701b11041c0c00c82d410494550005c000782803c000506104030300414500c82c0181c0c28410b0642500b103030120034990130407203900a4101c0380407604c2d02d05a00d0850401d210139a400e41d01582005030070001c00c2c0103d2402e5000b0342c1d0041000d500002050300c10b0760300301c511100540e1800e4114410810f07207801809801c580c54000c11003031fa82c59004004012060816800c694040c0c4410701035800000c000000301c0b0b8025400d410200c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 147503264 1250 147502014 147502031
    0x6030a0f140a060606050702030c090136021605060f01060e0d0314220f0b0909270d0f050c0607050318010c080f0f060306040b06040f05040507150906050d 68
    0x128a8505030b5100204601c0c82c4c070724000b81c0c0a5000016028a910845c01d4420200503c820000d54007000e002e0711600d0a084081440f62803450548400030444000040c0210880004418126008041054100408041c008041020034403130f403a4450300c41c01d00000b0725410b0040042139500a451014018000440d5210a040c0103109075503049031020f0080b9591507000001d030000d9024040b1584d0900c0102c1c20210b040d040c1d1a00f07110907030380c0c0c10003168100a208010016260405003c0003c48074410b144d00b11800b10000640201034000001442e01c40070b046070091124003141c9041003040420b0003501c40c2c2220100b040d94122581e49011074480e1079414007880d803c252410740000d558a011089240d054108030707214440c0318a02c402d154941e07142e21080c0240c4000312003440d03041e08044000340006040c2c00f156034001c1c00140c0700060714001d245c202d00c01c566060f00c1c25505540b220781d040021002c0305001c0c000c529224a0080c2c030321440d0180103010380c0503003481909500c0d1610b0a8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 147504514 1250 147503264 147503303
    0x71a09071a0405030a0c080105100b030c0715050a0b0a1a030a02071b0602070609050105070f0f0512071a07030b06070f11040903051306021f0f0e06160806030a0f 71
    0xba900a014000c080d50f02150f01890803684604052085520307a500b44030008100240d007e501d0300c00c444000c010701d851035842e024071503542e9010440450320024603100546003004c003031040c0c620444000c58005440d031001020019200d80d640c3c4101505a00c45800c4100d10382c107002600c0d0440c3c01d4000158980825151491105440f1040083e0342443c035140020402c0d8002000d0f400c13240a52202c0d28129150780045410784601c22010700100300400007100001c0d110800c17080405d010b00103403401b403052034601140d00d030301400040e51078005000e00b0000307240100200c1d40e00499541020032003500501e011451500402d08090180301a02842d8030034083c0c0c9031251100100001c204101c0e4030100c0c50054465008a411f00390391441041c0301059140c0002080d8151001a4040368030040030402c038000a8583c111040135550346840b0090301c0303198100212030080c0021482242040207101c801018a807004080621039840344070070a012482d10342e00e42d000745800c1540240034202103a030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 147505764 1250 147504514 147504517
    0x5010e0607060c0c0b100e0408031b0409020c0c03011a060c011e052a0f0a140703030501060215011a0a021c080618090606040b0a030506070203071a09071a 68
    0x1074082d41c20803004001c01c5030b200c981d101c951445040c0000c10754491080c8242500380c240030b1210080c04480205000c1f038480000b45900c070300300302c4030803c0c511323003000304400e6a4216500c402240d58000c5a01c980c0a5018005150300c2e55094008000b003040485400070042c3c140c02d210741c02010002082040e13a032003034200051003007030100d000210303e600e0381e110b40051008980d58114100c0034036100e600704010422410f02601c81c041d4a6080c980000601206030b4484424802804102e07001181031910b013402511050307002e6100010305600d010070107824201606a51181d60003c43d0040c00048410200000ca000c3c00180560f111040c0c61070591801241e407040030700100044818bd1125036010b42040d10815003035a84003d482c12a10403440c00c1ea4081e584a400303500700c0c00c0015854282a0b03c040e94000c0020552008141d42e51905810310805440782c000503040061020103209940071090003e02e0318000184061400708029500c2c1c180d1405462011240b00610207101401c050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 147507014 1250 147505764 147505777
    0x6020903120c01141b0c121c0f050f0402060a09050d080301080706090305030a0e0f090f07020d020d08041403090603090607020c06090d032d02010f0b0306270a0605070c03031a0a05010e06 82
    0x86a40d95078040500d00d42d0009400300440c8c802d646c0c20110700a091030f1041c01007a0150b140300354125001d84850b401c000d031380e400202c0c1a408000c2180c0e00000c0641c1d44400060340380f0f0145080c59502c0d41810b0340141850b06030b40000c07003480040901003000442c000100c032203540329490301600c0d44550b4400140d0240580301c0075a4400d4030301050080444058500750b01641540c0c007250001d01030802d041c0e8591100a0411001c12038502c005804180c04c5041a6007041141c42682e181c001d0760b00000300319800699030140a0382c04182001202c640402007140d500314100c54507424044810005070003002440750040c10840107100308501c0b440030b908205021849022201509120908000d00038002ca40841a202d8241290140b0505020031580e02603500341d00146101651003140003c1d5008007002605540f10340c506410100e00c075031054034020100d640e01e81031110701c0c90400070306a0b050704452801085c8440c440c442e1a544451110b0100e82003820541c03200b4188a0001d1841c0c09002c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 147508264 1250 147507014 147507043
    0x120304061508010f0e160b03090106030204020f0408070503071206020d0e241305060103031d09070915090e01060309060b0d050c09010909080a030906020903120c01141b0c 75
    0x7000302d03140c2419000040040c1039075a0421980d4500030b0401d90f41e44881c020142008003041701030104900410046603c5804c1e103001050850b901c0d40850101d0303002e1404207107044400709d8140305915040c44001e00400040b001090000d003402d400030413003013030440020b0006900207104c090460075600028030328000003040d502c2412101c0c0510f01111000400c191f264581c21001904410a2103070140d452500a00140030603030840e038090b510324480184604c8040c1034a002c510b5650345400400e489030280b5038403080c0e014030b00742d20718051a001c5170601c401d1002524060188410360014141100c00307620300850f0031940c43c02c0440080010440558206450741403034418010001100072980c00250f80030700b82682d0f00d110300d404665510000400960b020020004030384d02c2904148035050003001b00500d03040804001925180551500040500c0d010601c00c20300d003002e104030503241c03030100c1c10b580c181e207071404203076102c0c1c0e02c114141c07031090602140001e0404810040e0300b00d40e401c1d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 147509514 1250 147508264 147508301
    0x60d02150d0c090305190c0b0301030c030b0105030c01021c051605060709051008011a0c0f1005070e0108040f170c01051b0406050327010f05060a06030e12030406 71
    0x10009031089503110880440703490741000c001d40c0c2558840d44420f0100c0e500000985940103e000d84143c4d01c003081e01d029990344030b0580c800700b40e60022200035030085104031742510082e0f00e9403034130031071803101680054400e400000100e00240d0300801c50b0b1800707808505001e0220148105c0c1030710740b4000c1407502c901030f0800c80c83c80d00c100040040d69a003e4000c5071141c94510b95218204145440f05041c2c40001030410700040020510415036801003444500c0c01074141a8030121079840c004510350f44002540c450f08140441c40d40901c00c2075042251454081c900003001000070f0b200b007031702400c0200382e40c0e6403800342c106100000d284104008550008650f407641905800b0b800b0740801d4400581c01c0710318170b01194031080d410040f0750445101c0d03161b15086030365901c40358480b00b203082c0c50080e040c15407468410341c001003881030b0106545410000500d07414880c00b840202821030700b1030424103140c0f02411b2400003002139100c042a104042a0350b03030307548078035000b00580311060310b00002004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 147510764 1250 147509514 147509539
    0x908030a0e0a080f03040306050603011107241a01080405030d02030f16050a0f03020903010608010c021b030c0307030f05010e0a080901081005010f0302091912210215060d02 76
    0x5116030002481c060032a2240395243d181c42450351102c10301d402021346580100b0041000a030590016984100024000a0001c5004d0880300c5541d00c116011115914401c18800c440c03c821038011510340d0059504000c9000b5141e18030007104480c81c4258180500d9100060800004208030b60300c402c100c0b48155100e0034a03800b400300640e81980d4181c4111500c1e04bd00803600d00c01d00c20303034594544660703d50842a042c2e0409030b0082d0302019000e609952103000100e40072809024046900846900800340d00450500c02a0664600c12a1350b2082c4c1205001041c2d9980c00541c030801e5942198408040c40b81c85d00e000c074010462a16611480d000d03445400040c0310300d440281091001c00c0e00c80c00d40e280c0c0e81294480200d0000d004603404620684000d4103014803a0340541104000503200b41c01055036079406406030f0141c0d0380418550517410350a14100101003100e00040b64280c001e050055481c2c040107525030007400346000080c424600054a1641d60060310900f16801038070703600003040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 147512014 1250 147510764 147510767
    0x601030228031719021506150c0d050915041d0c0d06060507061406030a14011d0601030218150103090c0306050f070e0d02030a02240a0f0806040504080909070908030a 73
    0x20481040840c18404c88140c59200e9400821101190400c150360940c0e030781ea6000402589450040c0740d09078008040c45041c0040c1000c01007486802c0c055100c2c2034450254004200d02c4003103c810158980304140410064801240d80101c10110f00b003015910341e40d605c00d56114580928100800c0f01c0c0d041c5a0000303070113a0004001c5c61100d000d60803d002d110b103240d003c08040b46055820b55003590100c56140b010030926a00d22030142c12000000ca00111030200c42e8210300007881804c4195000300d00100110b1074000003889203214500c1a400c218030b4100302224403030b0000c03070100d414142c0b02c03003081d4204125018030201440e0311078801c00440c1060a805144100c00722503280203c3d13024452541c191500040d0046032300e40c02401020140b156900b84400e1000c0341c03091501d243d181c8000018091081c40203400702c198682e40d0031658107201c2000401411380036105a00131442c0c8001d020100c0c0200084981c16501910502d00507224a0811200811240d1100c01c80340404602800d549 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 147513264 1250 147512014 147512017
    0xc070b040f2112050903010c080f0a090b0c0c07050402070302031804021e0906070c06080f01060806060403120e13090b06041a01181203110105070206010302280317 72
    0x40700440c8040310101e88a8031105181c4480b00440c48401a0608203000002c2c551800c41c28010075915045050090440c0401e0030360b080b058444c808985a00c0401c41c000c0318460300b1643c4a03001034070500c07000d4643c1d150380030306c1e20016000220f0400300203141c000014041000500405000d04119a10202070400940341d802c0981400601c0420140840443ca06030080c0c075035450b040d04243c4400500c00b040c050540e8003c600b926000030041c0183d1001c00c0e000580c000043c112a1038820f04c0345031101400610190503080002030254850170300c03005031641002e88040c1c0758001c8200d034905926440640e03014194080e80713544841d00d1503d090b55680240c101c00e5206100e02c03600d200c030341c40718000c110540716144c0c0841c49418011070010f005611803a41c100700104d00c513071911042626224400c8609141150a4002c00d411891005940c0801d22440342d03c0b070202d101030b020750750442c0c0c0028010520314030312103001d035001689a0f8040b142e030210700c0000c59120701e6000480f11070204a1456 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 147514514 1250 147513264 147513269
    0x1015030e06070207030803060105070606080a060207051203100e040204090b0a1a0102010212060f0a0b12071d010c120212180f101205070509030a060e06060a0509041203020c070b04 79
    0x49010352808034001c03d000050020a403580282c1c00c50030350395044011161a00010000d54401340c8444000503401c40038440d900542e0301896015075100307001d0400c11b01e455070503074400e038240000b00200003036618650710f8a0207403800181103080a4540d030002901501c2950000380070703400101d0500c03849148940c0b0940740f180f174442c046240803141100681c200d004001c036840d4044549030008049152600e0350480081d8010301c0c400d0711548942c004821500550b10b4200d501c04c52206002425401c602c0d9080c00b54040044200c0142c41980003d00d81005000e0080c0308550a204801c2018001c0c829048607003203544800383c840341200d030f90307070508010100380d039020300a5001c0008080c242001248100b401c41c5d10303403c2100f20200c1c800030040400038028406c1140c01d10806140356800e00818454a01807403001c036840c000081000d091a20140250b4850040e02d40c08200b25100c074848240d20035000149024840c003c064240c0207407280c81140c4402d4010290049807030a00340001d0800e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 147515764 1250 147514514 147514541
    0x2a1209070e0108010c020c120f0d020102120a020c100c0516051609050105030319020106030b150a0609060f030207020d1a040b0703060b07140705040e070311090606040e101503 77
    0x2243d980300c81103400c9503168081400103070001c51041c40581040b9000303982007807001d02220f00f4041d1403070070303a4104003500740880010303500003402d001c168602501d07a41d0804443c0d8001c61920041c0c00f81a59101e00c0c3d0320300c195034141c60385c078540344060140d815140c5454a2600c0342c80558521314165403900015020740c10890711282000c85c80c00110302c03034141130351800380003540f90442e0114160300400010010404642d00d0b90b03c00f1000440400b17149008844c0d0820000d0400410300402a09150b5900708501300719119004012007544002c2c105162001400d0050b61441a0300102c0c0041200c0d540207000e03100000c40c400000035203602140d200c0c50042d401c4200039140c17074504400341d4000b4480c4985181d000d019100c04155131a40c4084041c2e21380d4120b4441656410100c0d0654030102203d00c030b140c109007004c20038042401003520b40e000045800c02818074160002500c21701550103800f241400990000f580e00d528011040c024100c582c1c0d070444201081e400040103802080141035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 147517014 1250 147515764 147515789
    0x1612030806361f1a130b030402040c030e030a0e0a120f021206060102030306010521010f080d0309170a1205090303060a06020a0215030a06030206040b070c0506032a120907 75
    0x40121440801100c0981d080720001d604031031405450045806410f5001d04e050b24080000e003082c01d103d40f103840001c011800d4072a45a1815004000807900f800d01c29009240c1083c19080e1140401b200302d4881406a007028551403078403101050f1283c01580296040b500002c8288040c48100000c4e5050541308441288042103420850b80d280c01040d2203450169000f40702144c003039030149000c0c00c503d8020701018044c03400c8440d60304111400aa00071801c0c040400e03001d0041080601103540f0082e1141011300c1126929914983d0720340d19050301700c11018004c600881114410044205520b03500441440746003020341c282e684951003940c1a900c542141e01c0300103920303800030902901042c0c0080c001e5117a9501c49424801a5000900341d41006644030f10210059951101401c0500104258a5120f1804d407901803034182c10b58210300e00c1501c0510800c18880080c8100030b441c0701e40d13144100c032188241007441da0140103c0001d6400400c4402c10442241000213602003214071840c4440c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 147518264 1250 147517014 147517021
    0x20c06010f031407060203071e121110020c0703020d050a2a0501031107120225090e061909060f02071202060a0213030311030f0301060908161203080636 67
    0x255604c803c81e00c0b42d0405600700f40041d00104c2c0050041114202101c0203080c3c0c3c1d1031240e076448440c411040300d5031780401c0c0007a4141c00e2014040050507141d041103031046140c002c601d800e0941d5030314503100c02031080884c01c854004001080c4400b041207a400001890303481078401604041603500084e444154040c0c0100188640c464000c0180640c8441d00143c40c0c01c07039585858002004c4001d0b6441984500032a0310348817840e804401d004d1966141e07402c1c60b11070501c1c0c0c44200b070315403064240740598010810710001090802c0d84101125221000180101903441c18801a0082c20b42e6802141d101160074010b01540107400c54091a01e507080c1d070169039541864104a00a9031030320a5081c00441003400040e014542c3c1e5032182c14000200c0f420600500100c24160b44241c2100700040c503050350400010000700318080d48040d9101000080e682414450303440384e40f400c0f401508010300d400221303200362510710f05107507000410a45038625105803181c2042141034202c043e00c28807481d6000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 147519514 1250 147518264 147518303
    0x1216090c0e010c03051303021201020d061a0a0f0201060f090b03010e0109031d01030204031509020a06050403080a14070f050714091e0601170406052205060601050d020c06010f03 78
    0x103140c0000705031030300720007a4070b5030314116981c1e000b2000050303c0c10303035450020001d651940000210807200000243e40c941122440a0554020368028501e15070b00e001906c90300c1c01c0241c2074031602c40d141e00d4004440c1615017401c03409010107902c1905002c010380740120305d112240c3c014074004031040d4024070020342c0c0080614203d03503110b4000790003d2100329203903c1200307000800d0f500e0700c0b00515000d42400d0312921420034400d03500c003454626954406c001030441c103000810400503d0340341030250406185443d02c0c10240f0981f041201008521090b80c180840d050f81507070441c58020b04040a440e0341d91a20503a80d80c1c01c3e010b900310768000101c5c000d0003460702c1000c1600c104414030204141504420f01244807240103042c503414091500c800a00c003500110440d4413a6008070000700e8142003991011814540000803910401601601000030410004685400450a00e0055910030507400041c000303009000c503040f21806094000140c02d070142c40c07120280d9001d10010703103103605010749 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 147520764 1250 147519514 147519527
    0x160e0601080a0c0e0616020301060b0403031215080a050703050115080c040507200105040204050610050318070b040602060f010503010608060a0203131203090b070207050a03020d021216090c 83
    0x20050300007482100010b00b07900b05030700041da80c0034040c28115068010600010007581003100000e482c2940c055283c003e504e0240107200041504082c807070b29140c11601c006264050400c0c3d4545c1058440d0480c0c1c0c03c90701c1001c5100c0c0207045910a40e03003d50400c2c40e00076151792203032000341c0700ba60900c40e01002c1e10401c480300d002180c1d1414002c0000c1c0c08441d05100140c10001c00710701c28071038504250b43c0c01030b001e03095044e0300c602c0110000480b07140a204200231500003411143c06401e58050013100745400c4004c5a0700110941e92005180400c10045458800d49412a03040901d001c90006401500000d00d140280990040480709a8951061500700e0710107204003845070f070140001c13441256a55000b1070b001480340001180204071510350aa0b070607000b003c800c00181d070342e01a0038248500d06003059004511440640f01c0f0a28140005881c52001d02002c1e00c07541401070090210343d140d40032840c015426905881c0c0d800750072000d03200071034568840d01d400941401d0014060911810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 147522014 1250 147520764 147520771
    0x80616030b030c040e1507051e03070503040b060d2001030509030309030f030901020d0204060f02100501050901090b0d0f030c1703070906030203040807060f06090f05160c03051605160e 81
    0xc2c002e1800b1910740e0100400740c602e00d81d02d082240034801c12040d5240a030382c40750307104080d25182d0b99a40c00e0a1141c03140f240800141341590110305200344024140d20200312900b05030082000ca143c0e8640e100001c4030380250340d100818010034401c80d55181e0405410088081600762020000307540c0340c1d43c8850b100d1200715140315072038004021f0501c0c044900c801864009a503040010f0501c0c01602000c000c0384e0040d044a00400c1540281c0c00e0a01e50405c003142d00691144024000c0b54036000c0401e221400600410124548640010810340c54017a40c248103140c0010105000300030310704018010080b161000d40d5404e19030791503981405040f808481c0194580d07030340c82660f03610b000c40440003500064411904c201d020040c40b008954103015240075103c0403800001d54030700c1c1030002d03012500341240311905203003014108501d201d00103200d1140a541410141e58280c6940b9080314a8812000030b06000c50891402805020340040d80c600071443c4118210b6050f52034500d20201d00008a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 147523264 1250 147522014 147522019
    0x1140d0503090603040c0e010618330201020702060f03060405070f08060d0c0305030c010e0c03070612050703020c061005030118021c030306080102040b03090c01050301031203050c090a080616030b 86
    0x402026002d800c002e001598050301490010320480d80f00e0210b12460b002c20391142c4002240c0c000381101075248920010000c00b0080c2d094001c0408207140c0310004140115004210f1003100001c0e5002070017034040b08c100d158003d10503562102c0c41c1c5010742c6580c2054440502a40c5007400060016002c2d10102a8500c103a8039210460b958010400c44c507032002410850310070704803120001c0007030001c10161080c0a0380c00d0001c02d07a03038030050015280200312160300e4400d522411003044556082410180d400500b008007003159542e982081e4064403400240310258820142001b010701110f86a61003a11303812002842103008400301400c040054405c042e5203d802c0e00c000e04140d03a004017801003400d1190501046841c2c0d12041c05013203030015800261a00400003c0081070901880740080c0b20b0000d080c105d0844d41592609201e650034082c401050550742c501150204c0443e109803680803000074850f01116403641d0f10b282d129001915000990410b8440c0b00c0381c2c850007801000e2120303102 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 147524514 1250 147523264 147523267
    0xe01060b0d050c0d11030f060604051509030a0203071e0902070b070c020103090212010b0a0f060e0111030c070311120a15111201150810060206011505160b01140d0503 73
    0x210030700c07500103200241c01852000801c0040c84100751460150f508100760040e105506c81c0307440003580340302003070081c003291140004201c24032141d910000460052606031031a00c2d2a0850341000c01e1520b0100380c0f0107540b501c540e01c00001c0c1c1d41800c040003100e0515481409811a5903005840e05902800e0310051012440000281060307100722130b04400d45005240c0410032010a1700810010301001000e0350701c0d0707511510004002d040070b0b1002030051000d800040c00440c6400b00c014a0500c0c0413602c03504100014000020924040040e603242c0c4151fa0706481c22141d8901e800b9080440710b410441c028100310b071449114001c0420100800c0d83c121441442d02100b40342c02100800400c43c1c8100900001e02400f103020020a8440d406000c1801c0b9090700d07070f4180d05029190041c01003011107000f641e80e2041c0000c550100e00581100e608548036003150100c076505403a280110344008038000b00ca42a55424080c105460904130368030660300080030803c1c0d50a0201d540c0700c508014055510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 147525764 1250 147524514 147524527
    0x4a0f0d03020702010e0409020103020d141506030405070311060c03040602010515030a03080f060d05060c0409140405120f0f030723040e040f060e07030f0b01150f140d02040f090e01060b 81
    0x80c6908591f01a51051600525102844007020300326040c0343c42c0c200c060442e4008210708042054401144004200c030194150300e0503030740785642c0c0c40d01400001c000c9403180600d01216190003083c2c40e040d0311028242c0382c9541e103450b802402083c1c111607442d00100c200106030428280411490b058582550380c4043d00d50741d0004066151002401d52030700104140403d10119600f4440503001d00090b01e14281c2e913070310b007510308030a8039260703022103010510b03503021f00c800940300181400003581c900c00e10135101c00c209117102645010b0b042e445104a0000010000c45e03e5104d0076085580344005010982c03045a8421041a8040c074040d044105a5680118011505540c41c695640d403042c0300206d0300510b0103461714180b44482e401202c04200c0c8144160030802140e0348039003d04207030f001e80c6500310b00076a4000c0134011980034510601c01c8103030b040a140302c0c5900484a4000c3d42c51002c1d0740c0d40c1c0d07580b11a8204100544178000b1180c0c81e054500d45808018018a0101c4034051700c80740c180340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 147527014 1250 147525764 147525769
    0x3160608181608030301080c01031b0f030b040608010e10020c030f1b0123090a0c0e0a0902030105130b0c0a020303010b0a050c0d080103060c02014a0f0d03020702010e 73
    0x210003401c10165106a40c03400500e4aa50030904025100c07076400342d5241c0d45844244d600d0310320310311035403030505003000400c11002d002d8001e0f016a0343d007240342203080b1541303050043d030041000710507442c1c02078201040420041c00542201805e07034124011100003102c1c011001040b0300480784020380a80041000000002c2d803840508048001411380e110340c0c0045c0c00d94207084440300c09810003c881030711400d42c0c0300140c1034941580203218030040c0c0118105507980e0003008200d4020140c83d1884440418403024440d4080016941e01070005c001c0c0c3c1c100300342c00d1100006100801c0701c2010110001940c4001213105403a010040ca4009500716400c1c028150a00d4100c401400c04210741444a0b640310074040040c0d042081407a15045895415401e02c20181d83e14a413000080da8145840250050040500d4240b510034410100d101c004240c0c10010300c81d402e400ca407610b43c111480d0720818a28021a403030b20f5035100c0c1c40031501c01180d100302c1901a40103101c00680843d01c58080100b80d0b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 147528264 1250 147527014 147527041
    0x30f140a0c12020f030607080609010f060905100e03060421110703030516050d0c0204141302040b030f07090f0501061806030504140604060b01020f031e130b030a050603160608 77
    0x10b40f00805400190480a0101c1d15005044804400003030042c2d00b0322070316040071341c1064007401c1c564680820403402c042d40902400240d01c61280100c00d0700404c00000c52280c04021040c9000800f90340e41820a420080b941c080e042d004001114204180e0026050107a0031a0070307821100c80241c8500303451030710151a00c1c1c01491500340e01000741765500c000224144100c400650050f01c030000151002c1c0180700885208800a40c48510600280700d540d400d0800509401c0741d04807400319201e010b94002c80e0816070b200c40500c0b8903214410300824000e51a8010151429801404119030b03a80e07a06c08691000b1034608882d1805099002408a50701c070f40c21042c0c0c0a8010411042155203c08409103841e40885094503955540d03030030b02042d50b9051141c0520490307104010740c1020b00c240340d402201c118034645891840000561040d525840c1c11440008000b805051a2a884c11501c502c018080448a15129000d21117150300034001c040c41903402d446003a500c000b032603680c2002d9940e50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 147529514 1250 147528264 147528299
    0x903060a0e191208060406081005040312090602030402121c03151706040c0e0108190606050303070b0a0f051b090103110a030207060f05090307080a09030c030f140a0c 73
    0x4038002c42c2e4030000c004021008070b01855101d0021491041d8a2a800401040020b42614461800d0800070800300c10001007500790859904000039640e19076103803d0f50509040710782420110300b440882e40c18400d2035805584914001d6070b01003900c2640c041c4040d2140800504401400400e00341021004d00c2035000c43d1074400a10040082c941d15142c2d44e0790020b02000440d01c1e580d100c0806c0104011900101000824603910290305550400300440d41b40c0322400ca40707120142008081c042032281c41d8111000a04014003540e80d83d41c00743c103000c1c030b1211085441d00c0c00a03052800ca00d049040c141320b000e103d648865080c2e0300b40d0584080e03113030480e403042c003545040540707030280300302501100380040582d01d1440d00d0059568613185000001c0c2da04003604a4610b45c540001c2004625010049840403a440b1a80d40c0e5600080c080035641d071074550301702034440700481d0804820070101e00360ac0c00400303005103010b140f20340464103401d0b82c0f0465450700419101d0035000411855440e110740551 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 147530764 1250 147529514 147529541
    0x9050111011404080d0b0d0b06040b121f02070813031406060604030f050102090a06050c0d090803030402060309070e010f0501140306010e0f0114030c0703090f06020a0803070909090309090b01050903060a 89
    0x9100034121b00103200c00d400300c90181c581c00654028440b20385810b01c26842c100c5025600c200071900e9001069403a16102c0d082d01d4040b00418069012000c0c89504030340c1201d50150200c0d0b1161034840601d5030070200b50204540781c0c2e04088002c5505100028150f10a00340140b043d85018110340d9402948009000c01310345a6409100001a580e00c0c110000c016119130781e102501c4071440c903209031629510210309000c0c02070684082c40710310004400c40b980b064042d204d441e502d80350701814514210725036100c1c038170748810b000020402024042041c01210401d84c2c0315040140c003d402910b0034442510450301261031840c10318603504009090000c516014100000030203664440740e852030307000f195101c11409000500c03800f01078008040c031000e0200018410103590500e00d01a44d262680e800151490f200440081c107100c2c1b00e2803219025086070301e41032021074210f15002e482070744c85015600b2680d0138500da0000790352054050302d190040c010000c10540e1510351001c0020815000071b2030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 147532014 1250 147530764 147530771
    0x80f010b030114040e0303130b0a0209010c062f090108010f05031b1207030605040233070615060201020a030501050405060d060b0301020405180901140c091009030b0709050111011404080d 82
    0xe1045d03090005d9440703480800240f01d0194410310b002880d1410080600045600c180810911a41e01c0b030000c962a51348220001070014843c940000d030b480002490344071861102001408004918004d0628240700f038a440645980795215890801c0550007400e8165022800c14440489070700d80070000614007030001d140d20001560b45c01e0402740240c20070740d07407141c1b520117210450810707841900130420f5002a030b60400701144540b0400b2090154000340350319010540a05006413980140140504141040d051994031000179020390420172010012034601000094507040034059140700e224028400c9940c2005c680c1c0d850002c101c03036400e5a42640d400c0c4404100754855004014201d4a020459442403810f104c0050960306161121084d941d051401d020351032140a0555401d010300b2184a10b039111072000858a0b0300641e403001d80b41043c0e040c10310280f650481082001e03600c0a98511046004da170300c22500341ca880021030800c441c02c5100017004503540c43c024001c04d20305000d012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 147533264 1250 147532014 147532031
    0xc120c070314030a0c0212040b0f0c1612031d0906040c020c0d06021b12070609060b03100509070b0306030303043206150d111309020a090b01080f010b03011404 70
    0x380b15a00202c5040d00255900c83d0000e0340c0c55010441003501002595440d40380508210740300c003490140007001306103610003280007007801000780301407021541c0803a0919641036a900c00f51000640814080d0042012070f4209090384019424050b80745030040c10031401500c0d01c20501c4020990704078503104501900041d0328140e90f076201d01c800624015200540c407510300860100c552030f2180b042c61515403042c152245480b280381c040c1e4a030680c10010008031100b8a00b82400a42000307500300340d040c0030702680d04624145550105c0c1c091040c840031240042d842e0b0380c00000b244003d54029900d58414000140007030400b03801c3c04001c0a80382050700fa8841e005281100c1c00302c80c600c1c2550349401034403c00c80e1107800d11a4000f150f03101119850002115620740700011480c13400f682d800b41000204050582c0d0b03050b0402d0f10a6a4050170b01c403107039590b41031010300402140510a000542d00b4012403180b0ba403160701c0e28140ea5240007000c0ca140d10f80208550088d400100c02c03070300f098540d11003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 147534514 1250 147533264 147533297
    0x1110020c1206040b160804030e0d08120405010b0a0303140307110601033e0405090c060d0509150402010f0c0203071205030c370204090c1d0c120c0703 66
    0x70318400a038600001c02c29402c00307142c20607210700014021001381c0070050410541540c41060143c01940600700840c1ba45114004240c0f2490000c8018101403400910300c0e0b0003035541d9181d10302c01c50266008001c104444c1007005800c41c0944005000690f1589062140d842188000c640040036400c0071030903055a078031400e0504100364002d40b42142520b0150031041c4900c0c86660f40c014160401440446030705240f41d9220820210041c000d50f80c0c1d100180b190030042001c29094600145429150700501c2104c0d4043c04088544002c940a05528a2003907038450b02c03640d00456058403481941e040f414011100610980300681e403604c80d115000610301c3c0e0000e1b00c4940d4500a20186070340354443c444440c41c01004071a401c40d0101c44500c00c00c9903040c01050703042006008010340400c4d400c1d6000140c050b04c003880c1c01030700c00703c0001c900040d49a200040c4c208200d200e0011480c1d203540300070898189003c0c00303600b046080b840c940040d140025010040c200c1030710a041803090003c1c5e0141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 147535764 1250 147534514 147534529
    0x60c01050403050c010c030506010c20091018020a0912080405060a0509190308040b0a11030a0206040209071b020105030903070b010306060627120f080a120b0603041110020c 76
    0x80650210b60001036010703401c0350031b008a5100e1402030600b80000e040030350008100c01204074014103190390a0449500b80b500f007038080d00d0000c10081100c00341e82007800e10400e03150510301c038000c00c40748440740841d4000b55600964000e8591500c81c00350461421f502d429050702c0020044880c000300308008141e0740c0e107140c054400a105a1359240d2622a0301c010b2107030080311500702e207503500d40d00802000001c58010803181070f508042080c5880d41141c060589030501090f800d805140804201c650341d01d5030000c0da1900c102c0c002c031007d104984810100341d428011104900d240221021300c01d001650140c002983c100c20039a040740d10f408050740b80c00704000000c1c2c200b151501e45585c403c0040603071000719288104a00d042c082c10410310b100c1012500c035914803450014520414005e8140306540840d02c6002d50030169695503520204801000080b048160000c2289009400c40c80350a02030142c038400c0342d00c02001c0134140c1c980c0f000c208640b813a86400c2021071181140d103400988a101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 147537014 1250 147535764 147535771
    0x915090304292d030402030616090509090105040302070519050402071707050f010609020f1905160501020a03200901180f17010c0c0b130213050f160306080703060b060c0105 76
    0x2c0703c40500070100700c1c150b00740861052000983d05003030013440701594021400036044503010050b0000f01c0a5281c0943c6d003a01e030b07603121030f6000c20700500300420b1a0041d00001c3c415803107a400d49801030703100c0c0c1c10001e01c0d5980c244024264520810b060001e0308041d802820000e020f5142514440c3d891254000b10354070544007101ca682101c03c0c00709500700c09010b1140980355004003581000080c0c8d0f01c1045a00514040c0724075a40c2c1111032080341e81c020803c68910f0580703422a00318090940c03d1841c040c1d8081851800001d1030070008200c0c8182d06001c0900003100100340d240341c03200003801164003881c0003500d50303004100c0050006844802000c0000204080c0c1402c0d8030320008843d0003070842d46c44d4440341c410310140b040e01d4000160640c91281d401106611050480b03040d50011030840803011800b041d61520b0320080c062004981403d1030302c102e039001524000c0914251003241543d07114803c1c144140c1c040d140a1000840a40100d4080480a4042410002c14504403420350f130068 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 147538264 1250 147537014 147537037
    0x507081b042403060e15040207142a01050301060f030b0f120d0909060510051b0102030f09100608030d020a021002070602030f250f030e0a030503091509030429 70
    0x400c0d4600615007501410005158481400300341e4903119048848100010300f03102e00c22a0b00082c0e13101004ad07440d0035540001410030403240e85854290705c980507226041d0545c0c0c0c0401c0103140441c500d42c41041141c0c1170ba49213695644210004440c158050400d50301c585074410025a00c2030081e407100c1c0d0310540425070810003080010303e581c001500105e01508041072107402e040c001c0c41b40391141400400500c8052030030070b03603c208003000d1520540310a81100c009500001c280030345509100c4545002d49465025510341c2c0741a1320040044811620a1907901d03001032244500002280e409091054018015079006004401009007240d02c00030085a07680d50110510006038455510345602001d0100008521100ca00412403c0c800c40351031101080441e800240e65030f84250091030085118038111010101030746000303022600b00b01c0e5480068071507607141c3c524041b42901528090b81c0080091440d15040c8100107010754800c07111a4842c0a0080c01404030004100040c129001b00b07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 147539514 1250 147538264 147538319
    0x90506040b150a0506070f0c0b0f040302040c0513030b060102031308010501060306150804060218060a0c0204050703061a09120f0109060c0c050d0815060703080405060a0507081b04 79
    0x2c1e0003062480022054075003d044420414070035600c6100c1105d411903000558505a12268584142c4180440e00029640c00b030101c1c1d8180792000c0c0c10041c20540340708890a007c94451034030211083d0050701c8880b211849c64031010030105aa00c4500c42e0001018419207160880540c00f001070800140c0c061511a9074070001041040e0303061107100301800d01e21401c41002c4500c20700c0284881d40c050405451207a0020300c081130401082c00350401b0180142c400d03074031031480c1040071742290315082c41a0701447c242000502d2a80c400e00c1000283e61816802d00700c90410002402916008002000e402401514845d00036110070030030304042600c1b120001c20886000d00e003102c04e41d0150310501051048403a00302001410110f00070150301441e24084640b43c0c0e80c020168503070040000307145e42080000a81d081030503031000742c1c503104601a000b22940d5842c0d051035481121070482c3c4800010b200100441e081800000612240d5603140071320508094a41c02030600407440300c0d6092100030035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 147540764 1250 147539514 147539521
    0x220c05042c0903030906070e220b010807231606060e070e0105071208090a021017090703030e0105030a0b090c03070810061d0d0b0703020715050903090d020301090506040b 75
    0x4407090a0359201022601079419400c00390403c556030b00c00038180303500b40314413200e8098454580032030b00350418160500000d583c0b401616100b0003400500d035020300182215000416150240080e07540d9000d44111403400c15014201c490096040012603640c001404083d40f40030a815000d8000a41300080341c142281c10000000341100403c104418140f00d41800f0034004a5401c800001c4541400e040c41741c0343d5030b5050500b80c204a0240c00007544200403500901240b5031000f0501074603401c00006008031744074192455500e80107840010001038515101c0b40f0254418006181c004900c81c0300480c0c7c1e480e1680000303001080888600030304180210404c14415404901a5009402e00a02610050400320010300390f40c081c8d0119008188003d5800000e519141164220345400140007003980c180464010042e41c8551400d0310075100c01040149403403414890b140c0a485a1001507252125083c2030011182403d038050383d041d541c90303030307000c004c100240411342c0b0a503c951440b01c1c0615 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 147542014 1250 147540764 147540839
    0xc06021902071a0702040b0111010903020c01020d050412060207020117150907050c0a110d060f020901020706090806060405060625021009211704030309090506220c0504 74
    0x941d01c40110396541404450f20040c2d04000c89040d540c050301d0114100440317100503101c0031101200350307407158a040d03801818181d01144500454070300f41c2c20703290b030413003030503400c40ea14042d9001e001c8400c203501a80c0000503005031300500344544181040c2c80070007070780b809602c4510003ca4418840f1400c034880b2424501d0304045a9601803103d04003141402e0100782076a55407080610000d00b9410f81c900c200d0603503a144000c00f05595803082c030510110b009400a40d02a410110f02117000d84034081020443c20300485c007582c02d5501c00c80c01485655079140401014000103021542c02c000100300900540d007942c11141c0001d84000640e05240189205200c07050740048100c01c1000103400060003020f8001c5c000c0e03109441d0227421f052035080356041600b5030b42d104482001d645000054000101600300070075004654080108000d03695641c2c06002d03000c503181103c0d401c12540c8881d40482c0c074006130b100c000e0a00544c98203505040e16078260001c81c0b4000c12216003046220202204111f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 147543264 1250 147542014 147542023
    0x1060306050d0b070806150c01060e0106091508060613150e03070f03141518010c020303160f0909020414120a02010c02090702160f03050c01020a03020d0e010c06021902 74
    0x5210540300c0302d040d050580c54010a10b000640380b0300800020310041405070382c900c41c10020907048000001e542d5410305202d035000f00610700c200e910408281000045180c0609041012500451004e8200b0080d00c00200d0f15990010140d940c4000c0c140504810142c07801008405400820510200c01e040301b18040c8c40841e189040ba8030940c032040c0700344015402d031207801040303c1e40080a140000103042c403c0d81031540d451a02c0c1805171000b010045824400200b0500c002440310080056400a2204031b13100d2000b110070100b060744150034050b000344140c510b040c458040b460310403200c41d02c03a03d0300070503603103e94020034148106145044807031a09088451030030399880010a079410956001030680000c3c410081d1186902d04002261640240a000e04032000c402965017460385441031782d603d9141ca408142d506210301c8201840c2940001283d10b201609a00103146008080308202c40f08500b5409050400103d00d045400181c0d0500203056494441824075010742080c88001303140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 147544514 1250 147543264 147543269
    0x30b06042009011b0602031006110c0102070501050306010c05010c02030a0905040b0d020f0a090c030c09050d050601180b0607141501030807060c0e0d05161502120a210501060306 78
    0x8085101c030760301c0d4900200d5012601841000e00702460602e03400c2520713801002c0c00d44006000140004108807030004020b14100c1600e210380c1b01c00d4211051082030a680380d1101080f1409684284024801903000780013550388404149000c03002c041a036a00e0500b940e40c207400e003801590010503a1040140c200515202411060782c2c1003042420070380000d8106980210040e00440391601055460740700d1060700d00c09426010700610200040040c020000c0ca40032201300c000464006011605150a0480c030f07043c141c00c00d0013000c4607420480769505107030303404651240480d540c810350b02c12074131084003800d034050055800c1c500c171000e003400303090400c0f02d03010303080c0104d414200061001a602c4815a40c0864000c58009400145680c080e50280851804140d220010003210000c220000800600301041b4641e103880e900d039903a1008a441c4015204000035030030071900400316418840103003100c19114a010001f04c0c038284c04214440c424500c2c041c5d80c554980e401070043c40d070103001d11b100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 147545764 1250 147544514 147544541
    0x6070507030e0f12070f0f0b0a050306040506010e031209120d09060311040504111c060b07080705071707030309050604030c0302040b0310020301121103060603060609070504030c030b0604 82
    0x290400395a00104102111000703207200302a1250500c0f8075407a000c40c100c2c98800c1c0b01e0100c8034802d440d034a070400c007502c50b846070f1007103444644000710700c1d0401c1a040e90728800f0341e030325164203640381c607010000030300001805641001041030702500d6580d020009040711100140c003807591010102e0a100380c100031004047d09580c030941d007540300140e1001c840001c48075103280006408881c400071652901c170319485554440d05007806500382d401c1e81001404607036218000d98440591071482401510664803a80000d50424401200400c04480c01000e903284100c00340c800d035640390603c41c4021540c105a4545070b600035070007401050f8100c92808013a10085902d2405c0c1071442e61050700c04101ea000007805561a814145038944040144054100c1d5400b015500c968540101d410312460b81c00c426a5021400c5030218000d080c0401c0c0742e80602c1002d005414a551070308184001908041e22590820100700b100101003642c41400d02c0c0a503118105902590034003078200800c1e5080451200c1c0d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 147547014 1250 147545764 147545767
    0x30106061407030306030606090e0d08090d0c060212090307020a140a0b0d021b0c101b1e0b10060801081501090c02030c0106030b07091703090105031504140108060705 73
    0x400c40e08600316855203610500030a03511041480c0031006030040b0750006000505001c0c0c0440e50400035006001c6941150f811141612800c107000c50312900c0560b0782c039a15170060100c0c009003074452610354200500414016150000311480009502000ca030700c0303070305604081507610440c41c1400040004100d110601e4102048440000b0300b008403602c2000c520201c00121101ca40342150150344180c1c01e82d500501e4200f2082e4403d546034210700345241d124100c0040740c0103600307005544001080e100408649000105a03890030306680c110300d43c81c0300c8290102c0982001900310040c9520540700d605106c00d41510708076000c0c01100060f001059103400203110301082060280d80541111203511001c0b90030103641d4400d0381544100150038000f9420014003105024003004182e02400584e51004c03012076440400000d00480d8020317102850f0810405a00d03e03610034000707146c01004100c0c0a150b40302c11880002c08a0392a071109206071400d8070b0040000c201c060011990250721400c016 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 147548264 1250 147547014 147547019
    0xf08090910030c0504020715051e010b0f091302120705120a020c0613140f1b01110712060f020309010b01030617030d20072d0f1e0203010f0c0806030106 67
    0x643c0541c02c500a00c0e0242d42c2c045482d0043c480025000f0204845184040085062915000410803100307030701120480303045000043c0d42445241280e4042003044030311405c00b802981009600f01a0700144140c1c01d8081c000d4400c03110038500001e001c4c2c0100d03103401c0e5541c10545040032804200a04050b04107205001d0032108103c00b2601c0c56010b084000070260902182c40c1ca500310f030441c00381400d11441000d0600340e002600140b0340400d50071f110b228807030041c10350f030044840e01100e55000714682c100840c00c0280d4091402d41b010042d110b1036011803103504c5000102c04a030070480385001160744400f0741190b2542c00d0301c00d200180401e038841007241807100b107c950ba01e10a880c41c0e60015595009002550488007034100e8511140b550300716903803101800c201c03174600e205600c140400480c2c003c081844000c81a00045003540c070041102140c2c185448101e0f082c0001c58101244070b6041d03541e00c0040c1d900303111300a2403011404000401c0f0003101c00041804100900c854007903031501c04107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 147549514 1250 147548264 147548273
    0xb071101060509270106180209030118030c0311030c01091203050a0902010801210f0507030c08070305070924030303051506090306011406070803040b0f0a020703080109050c070f0809091003 83
    0x68200d8070040030220000c0c04c4014005401000c19612a03411142628010803072196603030010080200114005d02c19039000c00c012190416261f5402408148608d02c2d05000a005a5911035002140415030381040460020113003525260300c0e04131451000405181c00003501407240c0c82e080a5507060401c0203c14690000e0304401e0103004007110b0101c051110310203001c91140c101c1540c0da018036481038600182c42c2c056540c01d180d002c01c4640002e600d1011406441c0000c141040b01d4202c00108030305031416901e240101300480002d03034400d00c02d491000c1c00c0f41c075414594000351b100341c0d0001141e1800d1038090101031441203c03948640030400c080501d964000540300c0c10361704079a5802c0c43c65040c80d40083d11034881c450000b041035402000b044140301000301d07030521401d0001340309000c0307a50f030722001d40c200e20400800a000c5614840140284802e0368820340e0300c070415520319450311099031641410224803140031901c0c1007002440e4403207400d1003078a0742e07007040c5001e145a074103e003503684 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 147550764 1250 147549514 147549541
    0x3122211030109061401090b030a03020a0813030b0f07140c150618040f0302070501050306030a06151a0408010606030b010c0f0201030b1804050c1212090406030b071101060509 77
    0x50824403145036009030558080d400541d8079580800c0401c280d030401d94440785502000d208240015203407440001160602043c4d1042d000c0d8558094011501950b8034100c003078200300c42d102c10900c07207004080001a2000040b40c000e04901099a05900d80460000c0440350000b10180800b40140b00030805100c0000e080560015502c01d44505591180003291030483c441c04500c55880b41d034000e21040c048d00c100d42000c0c9034003d50a0f07491041d181e0006488920041c0c8820340c150740b2041c4a0400f00302c0c0c9a000a40c41000b503003003c40850b590f1138104104c0c022940b41015038000006040111200074803401c00106018101449240000d00000c0d1400300c80c1400507005070701c00a641802c680c40303a442900032500041404201c5103500b030003c0840c2c4011182110b4500c184149410b9901d00700c014960301c010840020400d801031100c40341c0c40340c0c00856240c0d0308a41c5038500800003890404246102c1d407080c2e629208042c640c002c41909440c0300e5070107180540d1240040c402d46880500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 147552014 1250 147550764 147550831
    0xc02010902030609071a0f0c0d05070b01120803040609020a05090705250812070c0c09060501080a05010308031303140c0f1504110603181209010905040b06090409030c140312 76
    0x101d50a803244001fa682107501d21a680e82245c1c2d40c020b4032415070000b074100c0c0c00741584500820072201641e0f00c800c0b80c58913820104901030401c00e0103000040010394280c1024003458070103080d08600b15a64800314101c82d10540315400440e0020600c144072400f2410142c0180d141080d51405142540c2c0f25041c40d4881d0117103410100ca082c40000c0c480c980101030380c2e450030ba44235480501e01175491031150001c103014003c0e140012007060104800300e00c1c0e0301900d81aa07810207041840c3d515030301d80c1114445403503030044050000d403020b2040f40003c40c40c041c1040041c008040c00c04003010100040c189000d188030301c100c0724091418040890400c0070402103882c02a1210365036511161441c0b04441d064000c2040039208100410f441c2d00786c0c14012b050f11400a80b40c00b51030684640c01c00c0140c0340c15117186a081407090010b1a000c0c609070b0008140700d40281000d40f05404a521402140001002641c6442d440020944c50f100780b0b03940b41c25807020400a12441022010783d84008041510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 147553264 1250 147552014 147552059
    0x30c02031b1e0d11030f0a06020301060806040209011403100e0a091103031204020114090d060b0307051008130809060a2f0a0201110f071205010b060906030106110a060c0201090203060907 82
    0x7025000319030f201081140702c0014090111f4038000d0852424401030341c82409000d00080e10740c40421410f090034000e540b5020780503103406c030079034603903084544894000408a82e0717070030f06c880400140c2d000705158880c0505151400490408040c2c01d0521800000d41b00d89030183d8000c01210b0501c4c8100f07908160805c0d070901e800a00e4415901c503110b05405603d100c0d035405003008a00604000d801d51100d42c00c2c2206606a5860540d81e400b0402071229008401010822010002d5035500d0710719219940c4500c03541907541000b4400c000f203a5181c0003098090041540b06108610088955038404106a0300130761a1840c4091280c00c0e6072500f0361020000d0501c00d60303c1d00206d000500703000244005035004100c550f4155103002c0082140000c15080d5a194a4001c43c00b80a003800021120825406001e00e851070740b91080880b211822000200514021808600c0c0091000d00a00003007909035030010404503040d004243c14440e0151034160b065004010400004244140307511096400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 147554514 1250 147553264 147553283
    0xc12041a0c0102040905070804050d0f050f0c0a0c12030314010308070204020a0201110d090c0515190201090204020d0b090f0103020a0b0d2408060f0c0f07030c02031b1e0d 75
    0x1d444800e80a406180c10101d107513814013003048143d5610400300c901ca1380c0210105c13000c3e4170140d0001c0d84e03041c0001c007242340041e40c1082541c242c003004c000100101c610036003c42d1034101258456143d80e4045405c172030303103681c034207081c4800f499418090280012080c045a05032545140d40d41d090501c03851200a000d03c1c0c0101e40c498659000b035114256502038070740700340d65030702c0c040c1d29030b000a02c1c207a10b0864500f10000404203048c14040c902c5815104e0041105180c07169800d1a08800500144c4010456495110180050b210340c0058107030301c1d04054020035503000c4d640c00c210030315034020f18070110580b101d0300402c0503940e4195594101d64903203100d41c1c0d82d05801081c0704061b00183d507180c0f02c89640a011120903a41b075490290403181d8890076541c42d030f12541c252213446034003500d0749000f101d414044c6400070a40d800040c1482c034440e00b0584d00030241c0d079012a051003020301141c0510b503a08644041a410b126542c41c003031100f9508038000c4100c0200c0014503411460b400907180c0c100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 147555764 1250 147554514 147554527
    0x1c050706050c131502010612020901271a100c0c05060d0603080412020f01090f351606020705061b01090b0109050405010c1d090a0b06070303020c12041a 67
    0x151008440110341c0c0c41c0200320b40e850302c8030a100104c52040c003a000043d0310300b0a0000e00e500f003106202004541c024541c0000c5d910344284c01000c0310301520500040030010790051001b40f000e1050503010000c07808040c0c40544601308005e82c9841d60400a41070010000c072000019210b114a03c007a59011100603460350f50501500e40140544d4000815001000502003101c0383c040c030718843e046108607041c043c800c580c0001103070f11030700900c107984080302a40001d001d4801d4020308521905403081100c240024a0180980b14a81c0307203851101076000310110a481d41c20800c0c0c100003602180c001441c00a20b8079010500314454000c886aa0303840f1180402d04c0d0030829000000d200d60040c40034803542d44c480340b00310001c2c2010341c1c04941543c03a0201048160303020f90000311b04e41c029160b80d16082c500c03c80c02c0c0105142c1c000c1405041c1c9070b40f050641c519640324006084140d000c0d030b8006868900c000320316440d1844088201d03e082205000403c40d58055468a6140b492603090f113039100c50 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 147557014 1250 147555764 147555781
    0x5070219030201060305283305040512130504090215030c0a03051005010906080403030e0105100603050108010212010b0706090606144e1504051c05070605 68
    0x51042034100314803002059250180341d030541001c000c1e40d0150003a52101d41c010396a0020a40ca011101d1424548000c0d80402007280c03401c19849141410040c07000800005c5614800741c0660110030202d16070360010700c418450200164940d4503801c42c0c40c28a460845400c45407840741030f204403803056850703100040440d12140f0f1043d0612415241203612400c110f40f000001b13401900d50341000034074103c0015040d185403510031040b95010f03100d01c2151401c0c402d00700c404030b00040c0700340c0516454411030a03582909103d00e910820b405091180b40d10f0408600809640d0306a00031150380c1e0052100080b9070b40302042840c11101c4104c0b68580d030710b98501c0c019001e480c000368054182880e0041c002520b5140d0360034009541e404541100c102581020466028040304802a44410020a201e01c20112845269026200c02e05031100c1d40b06011098600c1c00625940d081035041400040c003041107000c12055011000031245483c5030584010018142c0c01050800307081d00e130b01c490100c4d8404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 147558264 1250 147557014 147557023
    0x219081801110d02030406020d020703030f0507142d0c1f0c050102030a0207020f0d0309050105090d06050108030a02010c0207030503090409060605032a010215130c120c0503060f060105030703050702 87
    0x6145602616450064800061740740d800610505016020744a41b2607402880800c011080d2907060f02c030358a010f0301e4180202c2e07807078204038400c48a11600032840d440c40b6808106142400250b000203000d01c2c0320b035180480070382d15881e0640c0c4082d4400d105000f52503035400150141c07210072039508140381c501110304592520300b10801400c0384d4400818000b42c14070a40050000d02e0003a0b80814291600d00c0500000b06003131b810140003e940070b9010701c800e600c01d100806c0f41d920014942c960722122a00d403e800c40707100f81d02001d069480064049450b40d02801680022112400908840351841d1a401e450f07106201c18648600d17a2143c440080010130740c400b501400010f4200c0d4404070700000381c94000f0746555055042c0c043d504215001c41d620015040c01511200c40c2d1005040c1c54040c1d000ea407828520904582c005410140411800300348184171010900400d00e60807524038040500d81000006440e07400d0640c01d01c000c10045903080703402c4039001180761500240035500d4500881c2070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 147559514 1250 147558264 147558287
    0x13050307140c1504030305030a2a030915060f1806090c110f0c0303070206090307030b130606050105120708090a02030f150a060f0608070c0606150219081801 69
    0x154214000001450100000c1455048405a488103c802542410388019014a10004000420400c0011a0700b4203d40100c91056005002c0b80b4261850703401c0648011958984500081d584100c240700f404801410442814000c01701006400d003881704606000465008400f401d00c0415040c0a1407101948981c0040c03010342c808100030300e04140000c0c40200c48400d800b400c0d210318a2803844011010842c0011207500500030340c035103c12076082c0000c0c0e80204607813a031b02d8001d6040000200d84040c0381c1511031210100c80604803c454500b22003211003e070070490401c10140074000b40707103800d510f03840d801c00e500381801c0d42142e071490034251502d5038600009400d4061501d0800b043d842c00141c0d1043d181491072008403a42e15004071038211021441140c412000a40d030400a03540159000c940045c841d10b400242072810b03031126010341d480c6510020510a034150099503c80d07040c000d0498644190b035825109000944030b00b400b600030412103556507503003100401000ea001d10b00310001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 147560764 1250 147559514 147559523
    0xb0a050f04030f0b181f02040b040f05030708030304030f0e0f04060b03060f030f0312090f0d021e0c01080604020a111e0f07062c030f0d1803050613050307 68
    0x75519100c0c41d10030301e40c640d1000111014892903011605c0c0c1e800d80003990041106490040035001000414445007800041a10500c030340d0811000c26074400110042006d01411980185281d00e0002814508280c0360700100b5030360014014440020b0b0700902c0c6002c04070944c40e04003807503075001000509030010805070076406440c240f40081d9082551024500c42c54084481c503000e25101424952201821001c03800d2a800c10800e1070089001c003c24290040760000072240602034403e2800c2c504486154050050307440300028854a5610195410301e50203200090b0a5003241c890000e041d0150107080d030b80c400c41d00441c40d00a81442502030568401c9494119005402d2641032107001f00480e40c04c0880b98011400c940390300200024031507040300c60560311701001e0310600c03410106c0882c0f11010200f80c550507010852040c0c0e400c119020368180c240c0080c0030f148100c1d40b0003338681d032a50080c0080c09200c060081000c1800420701961111150300317240e03030480f090300d411411442082d03002003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 147562014 1250 147560764 147560767
    0x6050603070206070e03010b0117040606081204050406090b061c0e160302040f0506010804061a0d1a090c220f1112010506070807060c0905031b091308040b0a050f 71
    0x1071034550020300309004080070b485418008825a00741405e8540e4100d5103804a001d0105200310900070b070f05400c2d801030040100117001e0385c0715151181032114a40f0552112200400d06200e80d18081c803480008101148040148030803500103d1090f020f040c1400450720000c2d0003c40703030044141c001d40e0f5041010f800b56041a40d078566052009102404140d010f60300d031a030441000c07001032142d0760040d14161070303010260b65950388101c00303401c1301c6e040d00c10030380034070240d901090f1910158400c0c01c03849000a4158044c1d143d50103011000001c0400314160300442010009480d800340700e00202148080a104900640458074040c018a1110004540c81e00c1d02c0c014100d80400050314051506c080c1b278583d183d030b0f114108003590007030150103002640300f0801d01c80062880d034065400e500217802e1032688166501c0c0002d00740760140364506480035000340403000518000d40160750007090700c0810300c3c06201036103620450340550b0080d5100c4034030005c2d0441c00c1c180503001b902c10002c896181c46 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 147563264 1250 147562014 147562021
    0x40606031707031106090703080c071d07030c0c080a140f0403062f0301050f030a141b0901030c0605030910020408010b0907030506180a0e0604051e06040c05090a06050603 75
    0x800561040c2410f4002500070700e54566101030114440d03000300320000040030103e0640c0c0303038114154001402400c591003010f0f00040e1101f4409e011a400307040d081c2d01c2c3c42d00c074903103607201900b1744244004003003c03c183e980c03620740003555500655140c8079661600e04c40350500d25000d40843e2040703c00e01001540007040c0002004402e4000840e80e18040b13101c00f114030074000c1200e0f24600c0455088101070b0045c001846642001408c2e80b0b40345c08020308441050400c3d440e4600824a910f1540803503800c400703000c0f4510300d5171400c03001c41c1c400141c410616540c519114142c0700c00b104d01441c010841c0000200306403460820030140c0c04401070301c08554032562205078900900301d02401a000e1158440051130841c000e100786071044502420000210f0001084060038601c0107244d45041640e403412415032a80410045d44a184540003c20415080c0d206001c0301c841c84221210391944001e00700310004500503000812108181d445450685444010ba0040e0080d034100a0f0800d00c0030080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 147564514 1250 147563264 147563303
    0x71205060604120b010906270b0117040f1b08060a02070309050918010b040207080a0804020301020d091a0903030618060a170d140414010e0619051e0414010804060603 73
    0x681202d106010030081d648e42c80d0001007401c0c1040340f07454031083d00c031841c0d00c0c542c80094000c002c80301014074000552038400c0c61080c103000c40588041c0c03441e5950368210020801945d050f4551040d4520343c482c441460076000c01c1d51404010702c030120040e00850010300301030082d030703030600900f41c01000c000348c0f03190400090010040070964991558240607200355681824421200d010b50031402040c6441c0d0303c0340094500030300240049825646c20000201580040d102d42220346108034401c4500c5210003001106150018144036a680c008205008540d0740707a68400c038800c0c0900751012500c0e50b40c2d80c001035614010341d0006d2201c1d0b0000352070b94405000440d9401501c0d8168072114014551040100540d0142d40554400715001c40302181c0e040d80500e885940c02ca100828482c03615483e4414912000d00d104520030214102090002c989050901a0104c900e12000140c2c00c0615040c00400019101002170f414001030314041000d00040340c1018016603001442070101c01c100241e0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 147565764 1250 147564514 147564533
    0x19030e0a060915050109050403080112051612030306080102090a0302150c011407030c0f091806050d030e09070c020303071103030904050f06120708120913050f0411040507120506060412 81
    0x103c20202614040001c15440c0480c82218003690305680c0b072a4042e82031401c00c603210742151006950b07500c07030100842009050484c0c650068440c0b10b5401c14a41c10034a009400e80b120364205c0b04060340141f110b01075944032000c01004407a01101e8801000c005420b50000520038004040c40c55428490b807440c41000d1501c405015044503034081210003641001201c0d5251101200c03800504407901c104605c40c0348200d811800302c1c0946001130940e6440c000208084003064013200811070b40c0c20455240c0c90039a00c0c40358082200d00302404034000e540d0000741c0364820801c0040400380441c0f81c001058504000f0340d800e50202801c1040726051800004040c08801c650041c4500359038140300689032008185441103070300c4c42c03008281c0091036010300415504800e20b0384d034114064490b031200c201010300645010342030581504509090030b0070107403030002490118601a44c02d010520054aa012101c1d0002c5003001c3e90000b00c50322a6400510948600ea104520201c5407080c00001e2101c600d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 147567014 1250 147565764 147565793
    0x1012060f211104020d15030b07030e070305030910051c1a03030708040911161101120c0503060f1906020601140f1813081c0f0219030e0a0609 62
    0x141c4a0032a95464415140028951070010302d060140140989a403c0035000f50001d20545103000c1110a039a0034191091180340c1d01c16075805c903000007800103880c0c2520480c1c5102d103880014010703403802c40e12030964900c82c0c08140c0e40500c1b0300c4110b03200400d21660940f55120044071007a1800c10b151203904025048060111003017290450002c030840ca80081200c15043d800300c4401c1c00d081c40c0501c150b0007452010f0305900411000c0140100c414400001c1c140024415442c1e855061a100001042c0640c08050310b41101e02e4201824035054001040c0c9034000c20449064240c4079441011032005011440740c8009103458900c0864816008980541a155403800003a1000c102c1020800700d450354002c0142c01c140350000354480e0310360305007841e64041e0a0904074036a154403a500c0700c40551004038001c510140402001000380a240584454161100d20035030400400c03003200b2071408042c0d80c0180c02d00d5600c00382044507100c1800841075044e04594208494242401c0040042d035484 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 147568264 1250 147567014 147567029
    0x16020102251b050f0409020a08010c080403090e0f01031101090305030408071a0306220209100c030210090506060103180203060a1508010608120c01020910020304050a06090e061012060f 81
    0x5150300381002141c40281003c403240240074111650004040c003000300302240f81a60482443c000100d48644240610b8484c0035031940c1e1071800c0c0c5400c0c2030050140748507411001007d0301e02c00c24414115010f00103181900e0300858000c1010740040f0042e110b00005600042c0180030105000032a5940882c4d100129241c179940070329001c2d0119800007842c4011500154841c0740e40d1902c09090b40050340d1510302022540780103140c40913400001d203111500c0c184e2400024030308040c00040607414844010090a481d10500c00815203580d1161100e0000303100c18109595405240300400102401c00e140a8010303094074407a041c140030600c098081044450004400342c0c0000032141030502ca03020807508144085c1c0b150100c4601942080d90141c1c812300b0043d0f400303008101882d0780d1200d00fa19500b49540045a5640c5070206000e0f416156a000300c06104003068200646d12105480a40c000412184802c06803107044080c1c4203042d9816004041c0c0745400c00120380789035035003049410345400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 147569514 1250 147568264 147568283
    0x50408010b090405030d0b010516050304090c050c060f130c090212070f0903110121050612150115030e03030702070f09020307020a0201211a10080603061602010225 72
    0x2401c080c004600c070255001002ca6100f002841541c00881d0b00c141481c050506d809460030fa210000040e2040300800d00351401d4200040c200304520302c9201d030355015134513414000d041c207404007c02921208001c11030041103440303c000400c4e600b201d0402101155111481051240e180c0d5007003002500f020344031100c2a03a0450210392ba640c0210300c2034648042658500840c42d05581d04c1140070100c1e02201414401383c01210705001c2a0810100d800c800030b4070000929182c07400c00c100d9070312840e000f40c4919807ca0242a1801c4520300e01007410f4841c00071180071580402d1004130010280c0440c7c82100c1d0101109010b030030795001c6420800c0326901404104980d443f400c810040307100988681e80980d002c840702000550060064400769041e4212216188482d040300105031000000082c0540d540070306a01c645180c07490b2100200042403500c0003213898100d02181c1e40c2d101c09450302203000324011034442880e00c01d40449256000308900850b141580500d040440c00780e2410031550240e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 147570764 1250 147569514 147569531
    0x80f0703110c0d0f0809010203070606060c06110f0706020f0f04080a03020606031203070e1f0f030e030a0219110a0303090302011e05030c090103060e0f100f030b0a02090102011b05040801 82
    0x50407040d185419801881441300c01520303a440c00c2c1160702138424981540400e00040000c1811441600020a00d44cac07101522400c0c1031a0240c202d42d05101044c151000511202c004201410244c83c01d071580501e00603600c442d03a119101d040c1c001e10a1441312000001004107100b200480c0899045101e5000c5a03000d440341c200b01911110350061156880400784001038142d80300b040c045007040d9020f842150340180207108040c0102c01640c143d40030a440140e00104a54980710306459485030002450810a8001000707448054901105124006801c480024010b600202c10b400600003004803071156607900e4060321a0300c1a1209901048400d40710001541c5039003481c94401c251562441e01d10790720b000081085802841026040540d074a00100e1482022074106000b40c514400405a910b06840c0964060b40340b50030010041855500402c000341c0542051900900c101c240962100c00800c0100d0040a0b001242c00000c04000400000c0da0b402100078416210203d000344642c46 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 147572014 1250 147570764 147570769
    0x5040608031b191211010501060801080d2a020a21030f020303090a030809030d02041206060f0b0301060518030d080402010f030b060d0905010b03100b0102060f060d0f080f0703110c 79
    0x110607122030311483c400d0351050b8002540700c003c4103500c00301c1d038101030383c04500200c020343c2150400d8102c0360100720b41d0700c0144a551020000c14003940d4071b61410b070200a5200b407801082502210a122410030700e0f207202011580c41080100190510090784215080940f5050f0001811400203a020600c4000f060010034801310869225144120080083d0405030368102d6060303a00034005460760206000c000240406030009200400461000030f071805c0080c180300003222481d6001c40081d1403140c90400042c1c0589050b40d044038100d041181d1128052035400d82008454048140d0500501800c9072481e50010481c83c084d5000f03903100c09000e0002c03101941107801a04247d03074001c4003800340a03103d00d42604085c03440780c4180008038000075050086440d06c40c0c08100134698586941710b40042c1d503070400c403030313923000030702d58041080c0742415000f0401340000c03000041c0000b07521200003024050101d00300c49008010140550741e440c1103040080c400b03007101c0ca1208481c056880d41010300d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 147573264 1250 147572014 147572023
    0x1707032018041a070509040212060a090204060206070c080706060b030a060f0501090b1305030f0f010516090b07020d050712020406090605090f0901090b040b0405010e120904020a020705040608031b 86
    0x1e035800440401c50b2000580d43d06100f2a004049104000007004140d07200e450300d00103030001400802420b0b0440c00c100f801c0100401b01504071005481c4140010407213a5030026510307401c0004d5003801100244242040002842007117406822300782803540028401031a440114803540d200003040000304d482d40c3c40340c80400000d101c0c150000b032080340103010301c0c5900c0009100e8405480314862415544802280c240300e00d040703c4001d140c00134070110f1034640d0203000301c96000c01441d0148a42c00c80e1802d0117058081c1c1d5020300008004042044d00441d21000c003003841c0a90040125440c00f55a40800b00c4946c220b0321040b0300490510100040c54101c03030103600269000284800c000c1d40d1403071280400315500502150b260b649a01040f004541204030550003940181c003d0320f840d18040c01d01c903080d00e5000c00c0002e01a403103138200451105101054521960301124050b0b650b682000c001c030324200c02600001d50043c40c0c600c000500300c07400402044550b000881480031001054815500c0c1c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 147574514 1250 147573264 147573271
    0x9040510030c140406090504030c03140306010f0804140f210304080304060203060d060c0203091f090b03150312181c06050c0f0a0801030c0503070f1707032018 70
    0xb01282e202c0034000ca02d51510214149100a000011900e0b9900708030010f075841a901680412a00e5500805140d40f012611501903410b580311441d40c140140020250303d2103400c00410404010081010000e01d915074076806012a0704882c02403081074032040d1140914520b0307440c1181e283d41664007900d09d0f24156481281c10000741410b540d916200c0001030342c00204507550203a1490324890019440c1d10803482c807010f103540150b031107030007000a129010000400031012488050a044000f0b5401820740d419103900e030881c0c549980717079200b000c2c5c0344100c0080310301d61500564024500382d0300d40d6805441d01c07941c50202c014103001024280301d40f018442d02d07104000d88008041d000480c1d40c41d00681c2d00300c443c00c001c0d1464035001d5440c106441d0801a84000021030600040003440034021040c8081c003400c4020700300f071914104034810104038511a208074190062500b060310002407003c0c0c00115004096490021034801d4005200702100c21202d1080982c1000d040f038140880448070310 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 147575764 1250 147574514 147574523
    0x1005010906022109040209030a0c030605010509150d050337030618090c21060b031b0405040f02120a050d020105190504240b180c030f04081e0904051003 67
    0x110000d481c02d180800c3d80c0b021350100d8000d03408002090700c0e900c0411000b1007003402040400b40682c01e51502034103445041e8441031007072500c1000d101d00c2c01c06c0c007800c2e0010440c080303c00300202210f5203451400c5000300350007400c1403da41c9e0030040710102e0001e495404041d203100017a4514980c984141e0842e0554010051040361000d0700c1e440c042450750220031170074000d180402055a450880401d064100175510306400c80f82d94001003003080c140500c8844802c2107010f80711100b02c0d8035500108074010b030411446903484002103070901401d014038408081e0050414203107290000080707550381c2c1c10352070200e071280300307810f021810f592061140c00d010700301020070015008554400c0c1c0001d402e01500944100100104045201911200c4044010f0041901041e58030801c01041914000c0314101031014481808004000015000f2203901c44542c103010391080c0c0740d81c10140710310701407105909822042c2459488441842002401d00804111030034001e41c1c0c0c40c081c02c880c1c410003612000700b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 147577014 1250 147575764 147575803
    0x1140703080f09032206021b030d05070c0807030602031014010207060503151e0307060912020d0f080d0b10050901081501030f0f02071a01030b0109050a0b040203100501090602 77
    0x203506038000100b440d0055100700072a0b041c40344a0303a0120306617008802d0701601c810801c1c020403415405001c02001c0711000440402c01c0b00300600426224403000203400100000001c001c0d040244943c102405400c440003140c0010b41c4a1800c003000b54400c1c2c1d040398038404c031280009032070b000c0c4210b1f221f404d10040cac3c00b920352a46000ca06441c660005405040180004440460251259128240c20141c11890315682015000c245400c10005420200c10000340400620402c16036a00003401c095064503a070b01c40192905003600300c4800d2100040c61200001807218911800c1e030410f510940003140c10241362401d460044d03459200b944c0b00140030800290005041c4c0910320062035140d8011b040105450034041c01d400c0840707200380e0312700d1080c96010500200f403050300c41c40c3d002980e03107000e02c5040d0765066460b040d2014030140b00e44503540f034071800042c804240eaa0800901e0b2140a8000d545038180300810700a503240c4c42c000e80740052642440010110710010714807051198100b481b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 147578264 1250 147577014 147577021
    0x1e06090b062b0204030516240c080703110607031a0a0e04030f0e1005030a05060405060112020304060204120506040302010b190905100302030d11010b041e0b1305010f050114070308 79
    0x16180d5400041d1400c00b96500780400804110144241044c101a40500780c15081c18912078403c111003110307402d07112000c00100700c411642c00c40111041b20ba00b0070b058684907101032a08130342c0190f4000d114150b900418050244064064001c2c42212078003104110b15000d8410074070060120034403407a40110004d42c04200820b0007021003c0c40c1182500d000310050205101289207181f034014084e0000c0c2d4004100a240c40c190f10030b0a8106c0c2045501303019a0805000080003030862005503c140350b40080401c0400c082d550480d0001c003503280726a880342c0c0302820507035100c10302110260055420105551024900391203894041c00d1641659407105007804580700c02444010008840d0070000100400581e400300113140012240f507960465865894281c9425203c030001e070b040c01541052030415803400603050b05d41c603000f01c101c0c00150304501913000a8180e071040b0b18950304070386000c0020445104820300981038640a03207901440c08820030207601399105080d006000140c010010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 147579514 1250 147578264 147578317
    0x100f1b0f0c1806120804121703011d0906060f061b060109020703080601080103150c02030c10020705070f03032003070609110f010507172107231c050a1e06090b06 71
    0x4c1041d882c000d103900e03440c1034103492110008da4400e0b004882c000d0000c0816624241581002aa11a1250010b001c56042100204000c0c200540589210704070202c1d05285030340301340150300040200a81110b0785941e4402c40c01c0000d510842094001400303540c00500c5d00c1d40a10115812240d0101d030b1459102980282c92005282000c00c0d04214002040325288138802002044041d60760074400507603594041c03402501d001000ea2085030560410764042010980080c10308600e81d06150088404614030302201d030030740c400d2480051509117007000d00001d0100d198850b0b4010041519010b454107040001500c8a0007004001480d02d2400700c2d4000303000b41c124001d041c8000d01c2d1001444040782400501c9a04082169041c0000342046c0c0301c8030041800c901045180416400081e01e40702801003903008414404488009451301c440120364106496441800d1560383d224901e19a00341441042c4041c1c0350512074a4009410240c40c0f02103450468100d031064040c502909030a42040c014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 147580764 1250 147579514 147579539
    0x309010c1119240c050309040b120d0207150309020321041802071e02031902060d091104060605270103110706020306100f1b0f0c1806120804 62
    0x100680c000c0c4510302c154034045580403145014050a0490f1001000e50400c1d1484114003031241004005141901d000400c4000c011594010000e503004910f40750040c001c181e01c94003001846256214a01c8120354050b40450f016065940e000c005040550003607008030281c521851000c1c3d0726030001c115460540c202c00d0801c1548a41c0020031904140d60340886ea1800105045014400340c3c001652a042250196400d141c1d000188011181c01c103054022075940d81c45d80100c000045031030709140c81550b0b1404281c500405201c80103100105452408014060b0130145c00d5009034200580820214080c4054407020000c86252504200e540c207503410744005c240c0d4245040c50f1341c6074644071001019174020321206016850245c0d59080c00420b006600032804003140030042d900c4045941c80307a0003a010092002e900030310580010300380c10b006d40200781c0000c0007007140f400d203000060084155a2001010504040d08010032903452403100d4000000800060400c40100024414403000b0300f07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 147582014 1250 147580764 147580793
    0xc20060f0304050c0a03140d0807050d050604140c0d050c0304020102030f130812071e0209130212010606020c03070e010f0e0c070228050a08060103030806030f190605090309010c 78
    0x3181d0114841a0102d4030085e010f800c2510003400c02c99146002d114104250300c03c131681850103020a1404200081c50783c05410020410b568852001c90301940ea1504600309941101c480c1d0200d0b814007420083c038691044210424880c104400a102000041f082da4800c40d0103070051031412001a0075a00d40c0d0748250155040d0038045440440c40d48002c001007a0640b42c800007403562800107041c20206e010100c2d101ba54070046001c100c0740140c071103c03680f58000ca48603255810f8549940700184c8c0c005400c0c0000b240ea51b20300500010501d40c001068000040160161004c1c0c50301c80c036011710030480c00d010b56030742000c0420003085455151900341d544039104031505420600154001500044841c11f20340031070480200c00c0c1d81424004000e10000c0c030b0101c0d004043c0c1407038940751039141d800c148406414400f54500044840c0c4017445a40c240340b80300015503030500c01d0300340e000044190200b000d0321160b10784000140311003800022034070b0f401016102d050318004140d58010103c1c5401d03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 147583264 1250 147582014 147582023
    0x11b0e18090c19120f03090b070c060302030901060504020f03010f05010809030304020d1707060507091502060411010504050907020304090c030506010e13061508010801180b01060e0f0a060c20060f0304 88
    0x103400001c115011041049805205401245126000c6d0600800d036105079008248810000c00c81e20002401030145042150103a044c0540c5039030b5145102801002c542d4401a040760000801c503111110207401141621004480c04601d2030311000110b8080104940d001c100303038800c02c00314000d450080d03207000b600c41c81080c41c2e5490203d1610712100582001c241140c0013501e510922502c0b513045010745015110341002c0b250201e0b040d0300700a5450402400260840459214102c0f80e80d1050084502802010b0301084542c205000001d5580d17000b84100c0c03441c24540701a41d140c0c00e21a025040c0070b9601690f0341400030030001c0030450481d541c40d2403100490b81c0c5143c00a400500c81403c040b06804035202c07d1146c0d0715111556080d51100c0c0c464402c00041c0c40c100c100040d8031201014152642c0e0314010b0010201d10000c03554250581105950103881c1c00c0e07001988a611a502036002849076029489400080940c01c9c1c1c046a100000c0d64800400c2c06101e90504132903025642c040d024 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 147584514 1250 147583264 147583309
    0x90a08030a0503150a03140c090c030709060503060a170607021002091806041b0e030f0106031a040311030d0623150702030304050a060e01110309010e0111011b0e18090c 74
    0xb01c3e40c4000c020059801c0032107240d00f1455083c42c649c48c20030041c55001c2c1961091915514217007000038000000c500420301404004401316a5940765210b410303000d000030809545120300d0711712069980e90303c21030b401d03401403285404080360001070f802606c880d0343d4054410360720810000030395111200010700c4c0c203410654420b070183c980f50b401015246448899217509200e55541c40034581088100ca801109981c100681007001504c1c1103490030640f680030411043d142c55030b00d01241c52218610400486110100e202000c03131007a540050f04035840348148400354100100401c401c5903e103a07002d03a2001a80d803480302160703001c200410216200030103482c507294030780c40001c401c0034286d0004400100644c907001c0070b550f0000c05040c0807040c0a0001c41c1031194490009207402003051000c0c0c100b00030404280400380094106065601d8409902c2d0b0805880d082d0040c194049428114030030444414121440f00000078160f016100b500c0140c08141001c80500c0480c0941101948101c0072 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 147585764 1250 147584514 147584519
    0x3030507051f0b0406060305090601030b091203010312080702010b0a0b0310030c0b041508160c030504090c03050417071518020303040e060405011a03131e08090a08030a0503150a 78
    0x1c05000b842080c040580000030500c0b2030106100807a40250055001d01d07241c001440b25050300095100c3c1120390040c8104a541d440003d0541800c524183e0501003120110000c002c1000443d6101101400d607038608001d0754034054101e0903161800f0a1315080404c207103017844454100350007198803548a089442d04580d0f2035583d045448079980c0032105c8240701160270b202d0940101c00e042042e2283e840c20424a0807c2d00306032780c1c0c0c1140e089846040c4002e1000c04003c15019405950040c4084c10f0304000e070350710724900070b005000d0841e01101d1001e0a0124080e080341c07514190b038000f40d0044415000000f0348100c4000400e801514100c0c4482d42202c0c00b40142c0d4104024409071004403104440380c1404402d02080c2d03107044c3c000d4440e04401400d04a04104c078042a29440080d07414846814420b03801d084028030300100c04003000300b9030000114107004140000701007040060f20011070742d940e603601e40c0b0b49070b0058203603030000200200301248517000410050a0703e02c00042c40d0b04136055 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 147587014 1250 147585764 147585793
    0x15080601020705120f0105071713020429100504140d06090507061706060301060c20041b080a0605100c050c27061813050c0904050f0d03150303050705 66
    0x90341c0030100d45045d400b0503d00d442c20003003030081a400948a040c11442d003000c41c44c10740da403008020044800403071400071200c01c0d07503100d810013140d0142c1e510001c070907100c0c1c1c20540700071900e00800b041e02a1800b1400346030810312135070407a0100c0d40704111405040101c2030410080c00100402030382c207903840700310900c00b145083c00000001c00c099100e1162090310400da5120b00c0b078000302103a101d213605200401100390008070a2210315445551440091000504151098800030280d03800618050a000303501400081a072016540c03034071464120740c1c0324034100003030311110701402c2d400102040f80117440600803805000c450f80305906440710540d400b404107910383c450348100e001c03000d00c00440c0da100d180e003903040b10f80104065660b41400040e10080410700344000d4900804045c5000440c0309201081c0705000300420300030007140441c2050b0414564a81310803c81101900134510840765450007072040c0c6000f11034002c2030941080c0303951001d49143e0481c550a40300c5025003060141600e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 147588264 1250 147587014 147587029
    0x80306100903060e030408061303090b09120604060c02190c03080c24041119030b060418050a0201020c1c02010f030b2701060e010e10020312040c0503061015080601020705 75
    0x1132600d8001181c9407450a0b410610b03024000e4086482d204004d90f054020941c085180b00955204405982e60b075160364000c15000b10000340e8604080c05040306010070042980c010301449a520780c01c03210458030f10f02c480ca11301c84100341c3c002c00550741c1c1481040000c0c0b00c0300242003600c00010998110588100020311b48000740b00f118029010504100410042035203040810314805449038502e0080328410020501214003001d0b002410302130010315241d031240c00c0700300e150b207210310b580680450702c0c17038100d03a0f41b41940340807800750007004014013041c2440e070008801c49002c1030400b01100c0c0301d5001500d44102803043e02040584030440380755503072103080c034003107554001c9030503915203940c441704c08001c400c0180c009008000d0301c945100c1d102d0f039100d40c403c80c1c000f900712080c600001c0c940f1800c0c1e155210303800511100405e290104814088502d401108540d81501602c05950b14541002880080340c050700503544030120100840510078480940e0052b0180103c828240e284c40000e080c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 147589514 1250 147588264 147588281
    0x90807030216320f0a030302031206030303090a060b041b0e01020d181e050a060801030b0f01060f051803030c0a0c140d03050304031b060903030e0a08030610090306 72
    0x140c2c0c809030810070030411803404078005011001e4459400301100d01002e01c1c201550140c458524030440e003098040d9215010b80b024180000c10311450190f072440c01a40320703001160814104000900010f18504011044901c600051006007084048075603c681c01045520816600107035200041c5160030505c404211a109498882015044581000900d4070044402c00c2e02041000e0041d402c00700701902e850400da03088400207505044d00c801d191150410203510503a4030500700100020199000420030341038a001c1e1005682a640325081800210070030f1054400146038060728112452054000d40308070b04184002174040583c2c040060314541240700040703000e420440d6103404018140310507400030010800c05010101410000625650940d00b0107002d01c400000060101131107a074001004002c10601c1c034552404904040b0024002003604a010a141440040c485103000656800340d940c000324007031a40d40c03172600f40a04110031519103018041c0d00600031002803a140180c031803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 147590764 1250 147589514 147589517
    0xf16050303090d080403080406120c02070e1515030106031b02010204050607020402090f0901030302100c0305041106031b0f360402130b0316170106141309020c0f01240905060409080703 81
    0x4c0c03040028664402f100d08007042c1da0155401a40c0030841007544001c1c00741e000c40d690085071610041800480c2c1192646150310584040000000c43c440350154040c1000c000650b140700341818122070282d0807841140525680440c00b4400140145459001007001c2103000d401b10468617841c1c80841c0036008207800c210b02680190610442e0300d03d5a1242080000c1c0618040c80241440e40742c00c000305842441460040400200140148455069280540c45d030b2540166480b1441103104500c0d8020b6241034400108801c4249006800c40985c0600103002c85150400088044204402580928407040d00442d48490009241c0350100c05184036010070101c544141d514180d009110180c0a50780011100041d00103000c4264080145141c0f4289030304260b50310581c40c004076005065613405032086500010b0090f1501c100400c5108022003580028000e0131040c240c00d0702c1b0180e00e8440807c10304034400040001c0c81d00d94000940020303029000041c4042d10382c42c0c0808a91000c0e80c10340 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 147592014 1250 147590764 147590777
    0x4050403021b0303090603060907021c020606030d0f05091e0406030c0810020f0a033603090b0408030702060f120916060e0a06030e15090f16050303090d080403080406 73
    0x81e03842d0b060140500403810114051440c2a012900181c2c0c64000540514040c4005100050445000304000140601ca1003001000088542c10003951080200d40940c02402000d400c01d60040c00f4891020700c0d000b440d100d40d41058018000d1000c0401e56003003090010583c070300214000e8070350307202d01000385024031001708141d030820b1900c2c0d02c0e141c8400b040c1c2c0b080e6441084541c92140e8604150b03681030036185001702e0042c1d8401d13051800403130800883d030f007012400c1c0842c00d046072502c060030f510302e0b11944449648954844400800b40160303c03031380025800401c6543d0051610400509424040c406154102011190802040700b030440b84030315035a00542c18941082da080f08a80d0062000c0c0c03034954124204100440d0b4001d44038841c1c4401e16880d4860b81303c9400040c01041340075911a00040706030300e45180a81d45d41c603c2e40304944901e025040302c42600c0c001c01e400910589070040c0046207000d030448107000d08407240340b000785c90500051102100040c6610010700080540c0d540341c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 147593264 1250 147592014 147592033
    0x10f0c0210060b120613270203010f0902150a120e070602100501051518091501030c0c05070608072105040309090506100806041401030b010e070c030e09070c020405040302 75
    0x8000c4881da5004110b443c03000b40a0080ca4200b078882c410b501c0b8109031000c03040000f00c90302000180c01800441c000307003d1203588580f1580b54085000c2d202074001c030001e001110443d2880022500541000b940000510158040d1801802d00415074990a0b1a01204100c2840000d6088540c1020030f10348a4012040412505604100e000001506e910081256514040019480c6240d0022466010071701080071441d003d920b800c858103020000e440d100045c54101c8903054810105010240405d02e02039404030050310072900c115042d0740c440000c2a40c5824540b0903641008001c20b0181040b01c14803484200d00b03004004c020b03080011904c089980d0070300c0d14024041140301d410800c80d40b442e081c1088a1503a49007280414980e6904280d0001e450301001700f0064031560441c0e0340d0307002a02e800001041805d0301c105040f140c0500c2d4103481034590748000c60f00c2c00602003024000503006112100c5a1401144007500000e0904100206107510350114080d2801100c040e40540c0100008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 147594514 1250 147593264 147593293
    0xc04080106080c090c030106020705011404080a14100207020121060f0312090b03090a0b040206221a0c030a031a10020d0201060b1603080a09080f030a0e032505010f0c02 74
    0x311500129001d800601b59070520300001d503540320038801d40d41000003504520782c0b604000011140a4a00401030f110346075018241524080c1028103400200d2003501a880041559482075811549e4165505241c200d902c241c120404480a404410b020341c1c1c80f14001501402d000c002002188104e00c40f1030450500d0001030002d007080c1d400074020003402c0003080044107000c01e84120f06903000b080c0304400e44890002c110315000e00e803610100811099080c03075901000003809022500441c0c4004100701c4801c100040b51b008030280c01c00303540d0050101c0108507010b17400010400c1030140c021465199070320009400082000c0f003000150b0890000304001c1a82130045a0240c0301e650192481d100c8511f00c40e00740246201e03000b80400c410b540c00318420704001e0b00700a40d80c035004455543c80d0080c92100308410303441030794421b42241c80c000a0103400003010090390703611100c55102814243d03280400340c1365007100c54000c880d070f9507030f65084000c464941e100c2c0f00c0d086005580180119000102e2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 147595764 1250 147594514 147594529
    0x2c06070806030a0b010603022805070c120803010302130b03100203010306150e07110a050703030f021b030604080706022206020c041a01110a0c08010207290408030c04080106080c 78
    0x903072400380d04002e02d044080360005100c035045a07803500c2c0059807103d800403050130194084020300034035000c01c00d100600719032050260140c130780283d00440000c1c0d80d034224040e0f42c2c80500070003064148144010005803070000076510f1044920782000c98200800300000c0d0524001c411a03040d02c0740c0c040010300c10b019461090f8510800068070840d050b5040071100c12420400908600c1085040c40c3c0d211100e12003480303050003a075808421241c019440380b030098181c03645050280010300c900d034078501d81401804d51408010784d002e0050440c42c8c03110b407115079035940440403d0720666005c10803412151807500c01d0b08410480103002480590a007000213003401112981140700307508008940d066081d0320700d1090010802421314054101050440604180074140c001c0e0000c84418000030f0b904d407043d00240b14441c441c0417220411241050720250f04480d440c40703007210400380d0f0006000200c0c1d910041d0740058540c4001d6080c143d03540040f50079a200c1d608809020b4000e00c6500300c030b9060482 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 147597014 1250 147595764 147595771
    0x1005040804141c060c020a080d023402040917030f010f05030f1015030c06090618120b07050418090501051e07050310030c0902070c05041e2c060708 65
    0x743c0d9440440c1c0030951501101c540c0c8100036181c195280340c001640d43c003c001890403994410091a203420011484200a403c450011141e10f2141401560002c0a0250031200c100f01071594100000d010340030f010040000e0841141c001c1446510009203c0c0303000c0141d44109040d0f0034001d01c543c10305648546104150344883d0003603000940c06003501301c01190703425000e511040b00060300740e0500081c100e0103d0691004c0d210030038001c000f1075050f5000b04801c1c02e0300c0440d15000c10308820740740c1e256856601c0e445003000048104d5010fa000400501c0c155811614503c0c02c03506290312444240c111001d05070b110112107a858000c0d800b080800e01865500101d01021020020315508040344014801803020041007400400a107011034041140d2000e50b8000d0180c1003401d4036144100021340c05100181c8a81040c40c2c4001031030b142501a2401040c3d000e440c55240031b40c0c00c0620800b500a00038201e840245800001641603400c40e02c0c4221820b0200052445080c41003005c0d00051026 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 147598264 1250 147597014 147597019
    0x100809010612050f0f0106060e04090602090612010306140105091603060302030304090b190b071e060c03091a2a0c010903080403260c0a0e0a0e0a0f1e0e100504080414 73
    0x1007c10044107400c04580d460303800c8143c1b004110300115241101c000d115403102a68004400324442e03030200000800181a6403089208000b501c140c0c80012094840910903540d0010300c003000540c02c005000d1404050101074180450b820ba01c1e6800641943c12940003091042d65441d0400707010b00e0040f2440c11101c49035a500a1043e04180741d48401d4412001d02a1012960011196003401183c0414601980028042200542d2800018054251178a0a0701c0c0c03074107903401503a0116103560f2994000c010082c01d00a070130708445601100096003207000325a011003805152070800c000e02406c550544070384ea989070145001d1801070b101c05004031900080045080101030107030486650150402c40b08914140c446855001c2120402101c624154000f9100381c0300007400c6004202040c014401a0380c00d210403a4105002c6003150540340003403045110309291019180c41542c42040d11284820030b0340c1000c2c1110410784155501a2400c803400d800010b070401441d546090100e0004104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 147599514 1250 147598264 147598271
    0x30a02071b03060f27060c20010204050405091506010f02030c030d05010602160e010b07060b030f0106060806012c180112050c10020a020112180302030306091302100809010612050f0f01 81
    0x40404171000f181d00c0790040400c1d035600c01941e40280154111388a4540c070031800b400304020603040700c1c081c0d001071080500450803d03000c912070150201ba14501c0c013036940010701141d80c5410044450703402c080404c40960000b08441030784031000388020400010b00710404912545400b0000340307440c4042d00c0540060241010a0150340c6079441040e046070780b003e005075110380640c24000c00400803207241c03550500c641d03d0780c0702026806400c88400c40d08541c03030b242507955580006442c1204154486d0200c140a80e4228801d020020500750b8aa500540303400c2199000c54642e40c400d02d4217802500d01d5a40402500c01000000c019021a1143c02d0302c07005a018080e1001075030ba04100c1400030b0501605000207420603030703545e200c41a481d6403031190005e9241e03030342070180d01c80d130041d02c6140c0102c040b0800503409000c405521191f15074041e28920f41c0c110603260449074400041c05a812554880d20001303250303080001180003a03400b505c00f80c5582e1540f20303c103034a04000c0f0b05682003984d05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 147600764 1250 147599514 147599561
    0x206041e0201020d030b0a0506070f060c05180418051e0f1b010815060d150906050a061d0a060e09070e060315010504051003060312050708030a02071b03060f 69
    0x30f020601c0c0710501040e0401280c841c00c08000a6007442c12600680c0e00480d0100b4080103201b08140d00c068441d02561003000140b0754500d04503040d10030105c400e00c1d54100084441c01504181c0c0c000002340c0750f400b20b0901402ea00380d4825042c000259884c10441940c01c0d050300c00c8610510180107801c0c0310230014109901e0140d1200c1c44030614060b10f0b4107100390500011000e40c107920300c03000f0700d41005003841d40d40c12a54641c200101311000111002d4800b00c5001318008250303206410980c0d00082a030b400c8280340c02421900c41c0c88502c012155007820200802c02c94460414101c0078088903241c0b000e03000011828403101c1000200100200126101c006542d515258222504901c2c484d0440700c801c024080103807214442c0303034480c54001c1821464110290341c1548000243c92207180000b1140c2001a01110540101c90000c1c20040342000070501180740d503802045007900c108150114101001680808031203203510540318182ca038030100c201c150452049480d602c90111108980c1c50 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 147602014 1250 147600764 147600767
    0xd061422030809030d05010602010c0e01140f090a0308030a06030209130308010501050f0c0f030a032f16061d0c0103090302190311070f08010c03050105060d0507090b0a0206041e0201 80
    0x402568050300b0b102108020810041c0248101c4042200e0705400f030206503522a0000e000744400c1c4010760010302604100f660540c81144020740c0b219400d501d45082c84210b40da03040741a4819102d0b41c0d4044000c00c400800540003102840c8a0100701e80c0000b2910301d107005000001000070030b02e0000e00561401880000d800084050666100f07107000d545803580c080160060b88a407650204c4207104208505156420001c02081c1c0718000b43d4045c00303482e4820415040c0a040d15990b00c6801d41d54158120700103103400702402c40c10200c6120b140001c0c11580360101102c01310110042040c00c1c0c0644c07806a400c04100000002d42e00703180401102c0c1c2151402502c0e020400d80c1041901e81c08a888402c3c148181c840b104e80c450341d40d055a00321f03540e94401a0b4810a02c2c481c03107e4950070140740c1880c0601030712039141200e801a2000b46400c5010804e04006c000051036081030111030030000c90410600c1d4003801d1800b52540040c41d4904182c28503e1551900e64007002c21300d1410442c0b8030048c0d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 147603264 1250 147602014 147602071
    0x411030a12020a1217040b04141603020f09190b030705060a120b090601120509030d050115030e1501060f0201110f0c120c0d08090a0b040b150d0302030405060d0204050d0614 76
    0x15400c00120f03882030310b80d807620104000c80041038044612030094074581d09442b030240301d4122132003120f2885042d580c88042c040121000c0b02d407040c03841d42440f032034111000e072a00f04501c4050018242c90301d0a44600006205400072103000e4001101d0f0340a4981300d000c0c41c480c4000041044510500c1407034420002005208146c0040980d50348500101c0c103001070400c252141c000a180043c0700540c5c5070040003081d5034080303101c0c60000c0d003030054825002c031020070580c0c0c41c0f02181c074240d1b1250b82000070540c0d10341004203441085650b40e00b03c01c0308008860b400782c450303c0300c0f455540d42d03901c81c2459560b1030010040d001c000c00a00c1005240103c0000003081d20303a10b800c1e0705054cc903558504003181e00b03041104a0181081025a013008200440c007461648a0480984180c2c0c1c1c454202c2d0a020340008000d20007000360748208002c3c003203440c2c510b0203010b0000c004000503180175122004107503031000700c95003210a66110b04400100000c07019000b90f00c40c41000d80e800341c05141d49203803200c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 147604514 1250 147603264 147603271
    0x1008010b0f031009150501060e010f050301080d080c12090309010906050c070909020604090c02010516020105070c0212010623030c03150a0203130807030e0405010602030a05030411030a12020a1217 86
    0x29558000704401c10038071041240d13445016840801030b940c2d403250060800107040c0c270311a0006000a8039400301d08e00079005d4030f05a80402d4000c00319583d9450007030f5046c1c58003804174405010140290401e02200c4200e961040456201a54070b03a1101000500181e145030050000d214052210003200000042e50100312461032401044a0300301b070010600d6807040b034000101807420904048609501504002e004941c10025104607c400c21300880c22250140e40460000d440c020412001d842d0440c00351005076015400054059940c0c01d816030028004002d200b81000c610150200c07910342445241c1c803a0005901502090300a55180b000b81000108244440da07404004a03615640c513244010229a11024003507484105040203040710042a40701c41c41a03085c6800800c00030b2003c425280311116549a00b030545d00c80707039981501800703608007050301403007401000303004180803010048540c41303240c000d0325079070081d4205491303d5400081c20f8030502550b030300701c045004083c4028550 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 147605764 1250 147604514 147604543
    0x31804050402041407050a090f030f03030e012306031606051909030c0e0a06050a1805090c0307030c0f14180601091a1809040803011203050f031008010b0f03 69
    0x80a035164070005006100c1c1c1a0710035001d10061003000034003604100202130019035508d0701c042890f41d0b40061045243d1500000301301200d52080c400000340240c128400e00c4001000108910441c000e034922099640810311108424900500405007828010401c5411040090750341d1a81000d2000c0c0076845440100700010110500c240d80081c1310707080703080c00b544d070044403101211750b2030761404207120741607607010616440c0480001e5a864060b0180040303030b108900d60400c4070b1121440000410340204001446c1c083d64541c1034095406100f01c2000d9882255a0160a070801507045600c80c03a070b0b080540e101903102c004040d591350b190803d28440014019040903903850b440101d800c1810350340100d14201c4a03015032204230502c280513084c00084402c0205181041104200c140d060564024100500410047c41584e84190b05000024001e04156103000341d00045007289900440742c0075400800104c0602100500b806090080740040704c072020662400e00020340c44142c407844010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 147607014 1250 147605764 147605771
    0x140310030b100807120203010e010504170f120f04030207150903150b0a0b19091d062d040e06070f0503060a05030f010906110c07050409110301090c05010f02031804 72
    0x620b20601000380b0310280400c403050324100d80c2d0715640101c0c1d03201200402c0340700e03500301152501101d1051003841d04c41d680240723114880c243c09030643d1006038032195580000d20010854a080306406c10f40680c080d210900012031a45050f0500a090030801e400400e0380070003005602c00000d80c030000e002c050340c0c0c000d403401300e10017215220400140011003003e50882003406002a203881400098100c00c0e494828040e01401ca500f011030f0102d820f40a00c202d40400404160703079045030307501815402a0060300d0b000300e1a000c010001c00720003200c08544101d00c500034209441d03051a004407007100015900070801c40c101110098202801d441d0f003081082804400900e00340d4804410100614003e0155401e050001c00102e01a01142900f95090ba05204401c211407845078101c84c507403692a4058070310a1704180400001d000c40b00380c00d0390174a005070034680310b0350740030300c1142101446150075032042841d12001609070412038800c0400c0d900144010300c0e000d041000c0b030b0134200b0700445000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 147608264 1250 147607014 147607021
    0x120a0807030305090d05040b21090c0118050604170a050a0b040213020f0910201b01050319111e0a02060901020306010906030506060d0e06151903080d06030203031306140310030b 78
    0x3c1045c500b82d2035480271a6175400e0244448503070b002c940d84412000a0383e44054104107060a03c028101603c9599000441088108150b0f08030158181c0351003189810b40d00712000c191245442c207454800181c1382080c0c0e1300140002c51a11811598450100b03407015414040b000d09191001e000e10b01000e8060803107401400500341c818402121000c601510389000c5d03c05410065998a03100f41d60003866036043e00340b4050a60181040e603215440070f142c15000c500c5021905005040184c46000480c81c0038445001c1207080c0d0030b5012400210701c0003494854041d00402440c0510161080d406a4810002c0c00190f907844a641426038034a8140480c2c0340d03d440002c5440b5104030f0181110061510400c041c2d9000007041c007602488040c20f200021041582c20045546805818090344001580701040001e04600140c4809a01004006115941e90f00468155400700c244103400c1182d002c0306110480d0050108004012488d20032800c501e00326460055050705030001030000e01c0f001000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 147609514 1250 147608264 147608287
    0x1090c08010e060105030402031c0c0213140c2203060c02061303080a02160f030309030f080f270a0b0a0609050108070504090206191716090e06120a0807030305090d05040b 75
    0x41c180c48c4c0c07a11028142c60402d1003400200042d03554280cc0f8402c074180240c00000102d41c0c010b011100e44181e00901c016101c3c0c000c1241705900012000d004040280014030b040c108918010300198082e10f0301003400d440ca10002410950001c002424482e04842080b010980c40414254032042503100142d44112012410b21011801740000385440041140b40b82095807541241101c40e119072035000b1038002c0e158055a0002e0b04403003a941c084540800102042520407404401d5a20a0b01000b0311580e040c8445081c0703401c00d54169541e000000500241c00c0c59072080c1c400401070140c08200c1941003021842d02d809a41c49520301c5140c80700700000555888401310755111120540c1e15600145031a4064059070345603d0309131040314000c0000b092421068008500c200b11a40e5070703010642814500c03e540c58025003119040010f140101082c0354080050031503140c01018441d480d80e420785801000d8490080240480ea002404590001500082a6000c0d1085c0c8400c0c1a01c542d4203000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 147610764 1250 147609514 147609523
    0xa1706042004051f0806160c0201030612030314072c0414100311060702010c0605040c050303070501050901060501090509010b0306011416020414010f05010c05070b0a050301090c08010e06010503040203 88
    0x498a90140c60b10040c003119501d500944c040444403c2541c0c180300d42d0f9000025100c103800c61700049100008103d04440c548201102043d039407050400050302500c885020815180100c02100440da07038600c031a42e1041c40e01030142d40401c46140c02d210900c61405444568450107a111003280c00e2081e018945645a801500304150589010940e0340703002c8031010100009071005542c0350b83c45520101041c20140111080190180c4804440c40503a030303591002482700900a81d44420407280200d080d5030300340014218640a08004030b03d600740350000740d0854240e540001e05001c1c1342170003040191541c0d030381c140c1150503074400147c403541c403100142d0b8529042c11000b2a2050001807101400c240004c4200180d4002e1341c1c108074040c60841007100a140a01803841062001001001290320904a8a404070721441c150361801d41d4a41100c0b1254000400c5800400c00110050010741c40500c03802035900154a804d2001d54903200070080442000b03003155040110000014066440411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 147612014 1250 147610764 147610823
    0x10c0305010f050f190515070b010b040e131113090201110303010302030d08091c09030510060e19110c0105071103040f090c02160915050603010803030a0e1c0504050a170604 76
    0x100300c5180f1500e000c1c1d420400b603000b44230488121012030008111a05041e06072000e640040384a082907413281403035103444458011044400090100f9101583d444e51104421401500c00c0c0114011407944005001d444e40c100d000c088640c000c1c401000540d500099a22400945090441c441d0b140d400785241045039107900c45007951080e215415229510140c0e00e01164041d0b82540c0480c501100c81c601520964440d410101d40607001151901500481d1044070741d07141000096031032641c0705842d209800c80040c4280c140d544004000c5126048001d01e50803001d075030090351078181404c44d01d00b01e66401340a403003421540c403070b05100024000c0000741011850001c018600329590758040c2c0190070881c141041040c0d00c020000340d039080c06406c0d00c1c10386400002540c11651802c0c01c9000900c81d0326400482c9200301001c07210340095902c107170f501901082d81c0e00d0f5581c5040c001440070f020000c1d4800110b05481e1105421212400704102d0341180e0302050017a0242252002c0c402c2849012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 147613264 1250 147612014 147612019
    0x90c0f0901020f150a0c02030703020703060b0105070c030b0105010f260402060f0c161202030309040c0318050f192103060b041715070c062c010c0305010f050f1905 72
    0x1c84c1e0b4a100035610940c114810320f4003100030702268003d02422610380c019804001c01503800403405100107000da0700000034105040c500a400c00c0f15544030001801101e0340b00303035840e481c510014006075900c032101814410b0b01e82001692840000c180303044801d040b148401140000002040c00c55644104441e0074210010a00307488007500d918440d03d0307012240d005101440103442c0003554918003c9007003520754009015501b0a030a01c1c0c10b02010301503000d008030400d65964132100b980424240410fa4041c01071006010700701d6100410341c60004150401000540c035001140b001500c2260760b64841d40c0310794a400303035110f4041000e401610103504541e1941c4008035000c10001d000210303d014500da0507040756400c2c40000c040d1681c40c0390070340d0000c0c0060201002240421101e40101208e5001c03402450304020f003c4e1640f81c0c0810302d9801c468666515202c0b1000250b81c5402858050030ba002c818840d80303880c01c40002e1480641e82d00c0540504c000c0340310b680d040400d944520b801800003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 147614514 1250 147613264 147613273
    0x6030204020307030b04050708090d0e03010b06070302100506090f07030b120601091a06030403021504050703080307030209040b0f0307120623040c14030a03140c0a080408010605090c0f0901020f 85
    0xd4024025100c5200c5c118055840c0c003002a20017813051004038042c240c40d03030141422640d403100031110404841141d83d01592100c0055126845820041c903180d80039502502200398404a283c05640d000342615115050482c2800300050011100c0382d040784842c10b0016910401001190100c001054105500d001d40301c000900c140d2150001d01d410103c6946c0314a90403404403c10006000584006d4010b910942e03c805803c02c2510000e40c00602880440c0c101c1790342c0b540d6403411036004484401c0041d070017042d08042801d06000700050402d044400c90540c00c00c00e17000c2941c4814134402c601c03080710508004402e100300b961001304500c001b0b00c0c8541840305003040c280c00d039079810f89040306d901400c8140085c0c04c01200d0340c0c01080040040183c48422520744044901c2c1c1c010142103403000108110080d00c450f0100500c1c04a00d100340519519145410f5070345003110b107691b00441c05142110f0400a00440d68000c40b00008140d42880341c4602e001c0c00100c1ca054040b0b590320405205 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 147615764 1250 147614514 147614521
    0x50f060a030b0901090c12090b01050904021504060314070e010c1101030902060304080304031107030302061b041e14040e0a0212070b04120b100608040f060b060406050c01050f0408070f02010201060302040203 91
    0x10380e1b00301300705043c82c5484a05140e00d441c0c45a40c201c0700100009040209404014840e601e08a8142e540180c00100940c001002421244032113503c9944000082a503440741c0340e940e9403903a9036403030340700003241451044400d8408c0007a020a00919008002401d0861600350766030003a40040714650300036000700d480345044c0c17070020620b034000d031015404541d01603c1500744a100023850f01c2601d915074050f00031511f400c900d12014000001c1840303401c4006000218442da544880d07040703420b080d804148003d074504220004008903a040c10360041382440101c3c541c3d2440051103034500c95050725030802c090744800005003040521380004040c03820006d40040c15605070a221100d1600072412154030780c50340700c92001801040d210712070128940c5400500403c1000c18103000182c0a080e01191070b8444000141141d8461341010000c28008519131180e28402d100b81ca9111002c0c260444650400c0d0300c4052450140c01002004504500591400c41e40b00f0b400120085501400c00d545905 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 147617014 1250 147615764 147615779
    0x1003050a2c06060a0b12040809300607021902030304050a152705300d031a062b150302030c030c010f0c020a03020904140601090501050f060a030b0901 66
    0x4610340d21200c01d031061a0100c2c1562900050010444450700d8003c0c0c504201d405c04e00712015801442502d00c420148600000d03910b0710b00000012400614080700c0902e0501c0002040f0900d42d810344e40c055102c142003040f16900020742c590f507624190b50318420072103d480041c6c55485940c0000f600400d0288000a860308421510f003600e500030703101d0064401c401000e00c084410012018401c24120603401c00c02810305815450840b443d41400145c03040c00580c0f204080c46c490a171503c41035110020484901c1d5151061480381802100d132061035003115800500310703002d01d1040c50001402d0208524041d2003180c0d10b15000321480b030f0b091019808690300304160700158402039010f80240c0107000c800b440c0100c1d5019400b84142c4896030480c2d000c6600b2a040100748000320381064803130074007201507034410300710703901c07880c40b8850b6244211003109045040c07100c1a845402c0e15401c0c0300040c006503a441440e04020541915016103e940118044001c1c21140500a4101105078008914203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 147618264 1250 147617014 147617081
    0x7020304141207090e0f0a020f0418050109080d0e0307050703030513091107060c0509090f090106030212010509070512060615280f14040302060a2d020601141003050a 73
    0x5d505600b40c41905812205d0309440d0012400000d6008103000c408201c180341c0b42d80a401c00d02c1001070b26846260f655035410f400c41d00140410f807079403040440c0700340c26040f141c0a2418450a800080d505001251740c401b9669030050000400f8490041000c0054401c07800c0d07420000c11120005005680c01034840315030950000c402560002c1c1032000b4603a03038134001d00865100c250f019244a0540c0c1c0c0c1c000d007280c400c100c081c220000c03954072801e002015903600c0441c0364441d540000001114101100894941405035006c9070003010300807020b03203054602290b101e40c4076001350b9034108c1441d40c400384008144218030034046841d1034007804030003c0c66281044401807500d07850314105001140030a5400c140c1d03d00d0140141041000700703000504041d400751907400c64604180003007138035401405148143d41c1d040103219404402050815590400c1014018001c1415041680129034003188481c200070b1402010b00d900d4401090708204194003049410320030009541c510142c1d01a5032804 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 147619514 1250 147618264 147618281
    0x70306020f2703060a0e060f040318081e0a020603041401061205060604050108010513150f18120e0105160c0e07020d0809030a0c1202030706020301031a0703050702030414120709 78
    0x903c04e00c0001821182a842660000c0c002c207801014143e0341c060402e800c2035030080007281040300003c19010b800d50600d54407400342c6a0040030f001c042d07180d14156801c00d130b840c000042595015000c02005a00c0e04000c0740d03005a0007184c2c9070400e2156500302405004203a211a103850740c400b01400520501148030760103010300712401d0100b660f03504003d80c20f03900d09075661142c901c10407815200141c0c0c02580c04501c65500c1002007500705d501c8031941c04965685154200b801d0440040f04200310b0000b0321110740e020541088800800304c0c00000f0828020300d2401c82100740f030785503460144801d4000f11002460140240380141c984980020b48410303200d901c1102140018002c0b60350080c010041e24000700da1980c69180700c0100783c66000c46486024541815808100030000c04251030340000c602841c0591148100904030240700d03690100b0007041d0304101071801b0184095282c0c0801124220394181d581a1270b580e1810000a1855500880d0000c80c4e00c60b01a00250110380350708002003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 147620764 1250 147619514 147619519
    0xa03030207030813020a141503090309120a030c03140c07140a1706040303050c040f08210703091a120910050714040306020d0f09032a05070306020f27 66
    0x2c039601c401325024150382030218001c1d40140708130028040741c4c644101503038605200a000307112112540514040d140e2065416102c0c94000150080c078505181d4094100880c0590041411242603240200200b1161600404111500d001d44030100000302c15210071581e528141c4240302c1d542c0440e000c01c40f03004008540224180080080c41160541442e4080003000d0094440c5a580f03903011002448020300603403100b0020310012415014440d1300b06c000c2c001c2103000700081d0000d47d10b605808a80402200000c4030208071481c000b951260300e4004841d816400b0259850301003000003e02d01540d1003140c10501e1140411841d04000201040406654bd200f04415110034804462180000c05200380310842000304000040c50b0f5801401880b6030020b002440e4401c420402c03041d039180800c00e0340094405440a030380c2440c4403c510101c000c1d08074603402c41110329a03409803107401c00d21000d401c1680c08100140450907003800c50750464100304a00319440b2504800c18018102c4103038850 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 147622014 1250 147620764 147620777
    0x51005030304030b0a020a03091205130f060507020123070b06211207030315080307170a0903110a05190905060904111011010f0c021b0105040303200a0303020703 71
    0x18250802204032000d998110840f0701040c2c3d01c0351490000f035070007280c00c00e04055a410124000c651205110741c4038120540c0c500760b50b1000100310760b445800981121480390f11940d0100082900075040303a144030ba0a00301541900340b81034030350712941001070b602044005c001038004100111444414403515086600900f640881c50140c0080340483c211740324550311118200d08002e1121024088492192401040d07160f0781c01a6810500b2240c0d0202d00154800b003041401c00c401125500300113000c100400b801c10f001c0b03c4006040d904507100140400141038ac0c0825291221000c0e0000303024003a05446201780740802001a4804621030300210302e01d801c0c0445c40910f44414802c2c00b903508500001ca12024900410103881d07520010303082400f101050010100c0b40a004038141c0525941d80000c40300e101560203414018000d51143c071030f400560b00b407019603170040140c41c1900d070946441d0114a5103290340d04009100b111041d41a031144109050401d075042c0c0040070068401e075901e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 147623264 1250 147622014 147622019
    0x70609090b01050304140721150504121805060a0e0102100b060316020c151b0601030503180a091424030d03020307050706050906010501140307081603020403080309010510 75
    0x24030840d1500140103001031001c0012401007106005031050207280710040d262030070360b00d1400c0f418401d0ba580d02ea20000002410000c2441500340d443e07044025550303014001458180c1d80c1d41e0300d84544011003824046c0d86507443c8585076079040c040e0050300020308100d80d5043d03140c07006020350f84d0603818079005100d0058130707080d5880c003400703004507030680a40142d0464445000365050f140300a80d1242c04c62044410f040000e40e641c0402000f034000001030382e0760701d04d0342d11940311f205034654107034801d1640b21800400024034000115440b0012050781e541e034101030381000541d00100707944900c0c03085040c01014882d40540340140f6003c0e00c64034101021040d803451075000305250100c0415170540010319041c6c03404c6d019800955002005150442c5000241e03541c103012190f0030340720b8000c140e00c00401440503503006607035104215590010701e800d500e01048000d02c4680000c0031440310411a04020064502980607038002e9503201c3c0c1002c3c0c4a01d806140c0a00078481121807a200742c00d4100c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 147624514 1250 147623264 147623279
    0x405040b04050d1823092a04062c0a0b0d050a06230102010618021809040804090b0607020a0308030f0a0608031219111803010b090f180609070609 64
    0x210b0184c0d840d6407102c0e007100340b0304141150112071400340301055141c0c0d06542c2071990f5803801d5161084105011000350054410a1200303200428010f80601c2d034010001031103010380100046603005074840c406806105200a40000300d407800e8980303900b009641402140104071400031704111015002c04004030b945040301001174418612565100d5103800320201c01c0220381102107560020180000302d00b495554100b5070900d03542c8079900150030b40c0855070100750480e034222402c0103402120864042c1c1000c0d2501c80891186100301004150345500b079600390b85404054034142a0000c1416003c1e95407810404c1d00c03648100d810b8040c03507030a6000524014a9880f0340002da0700d0040c000d42c01d000c00102c010403440d10242c50045039800005001081c000580140410700411995040d15075903481e00103c0013000b21440c030351280c0d04005e0740442c180c039001002648110074400c070003829111b003403110001540c80d503400c0741240591f004114044c000042c016040300d209a4070b448400340d41e00031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 147625764 1250 147624514 147624527
    0x80a03030c1b08030703060806131b03030801150309051608010518031e0702030a0809090a05090a0201030507030207020307090e07050102071805040212070e18030a090501030e0304050405040b04050d 87
    0x1070a140c4540251100d80401d080c1005140d0148441c100090720b12385038a4004e00c0d06c10120341b80e440007210011018104400e0101c5580340c0b146a10f1415012800d59401800d03104c03050080c460a100401d0b80e8075425031003a045100300300d800005807440301d030716400360054100301d46c0125690f5600b00303004152031000b8101e5001001525801440c10441300d8654030200300d00070066090010018440180981d5061101003605071003170309415511800c410900640d40c2d00100640402c1e4540b1041081140001c25101203960742407034005140d40c0c0e007902c260028010580040d406208004021a01440b542c0c420590a80160115605503607540c004aa89003a14000d020136051101e007400360b00c80094101d203400c1032004240000d8101e154030440d203006110f510041c0012808030034801080308a43c424130814400001452900044ca100030706222414829141050343d2030044c088c5041090040d680a020002e0040c0030314241030030120001e80c000d450a4650380200e84418500d00e0240b0b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 147627014 1250 147625764 147625787
    0x1d0103110315070503100810020c0c01020f0d080c040e0414060a09050703020d050708160510050f1c0b041802030c0f0109140a03080408010207050111390601080a03030c 74
    0xb00e140c8060b038600300c0c1203c03a600301410101c00300600c450045004a004d2140401c0d28010081c0140c4441d550302015180140c502d20581c15034000e034401c03c8941c800810b03507000c1100c0a00704254541c03590845550b00c0e118540c84802d50f120040184010089000c1102503010000b000f1140241c443c0141c803400c54050032801040c0360b000391010001801c00d40300d11800107014070301b901c179169038a840e16410000c03101955492060004414845440d01d83c180362200112450401d0401c1310102c03c41c000c2d031040000c01914621082d041094001c4140c100c03010b0a940600184100c0c8580460041d51252080c400c0b07219008110901044d82001d80d03411908200507915406458030b0183c10741120804c9818072500a24041c0317000c0041004500140020700c00a000141e561031282010390854a4034007201c0500c1c81e04004a085010314a40600c3e5030f00d03040c5842890402c00c0e0743c1401a55100006924a2401000e00000f400c080100750440c0c028065101801881802d080c102c0f0003402030f8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 147628264 1250 147627014 147627043
    0xc020d03051017280b010b041d10051e0102071d0f040609021c02010206060a0b041404020d0905070e0109020c061303050c1b210601050402070503041d01031103 70
    0x10004110005440c0203100b0488803083c1610003000944194405044440400340e00340c03005030600300e0801881800050041088401e05410282403085000000701542d0550754044098000304d006100348075138000041400510142d0000030448002c04d030840001140c42c00360040b0000021a0081013011102c00710004107401000d942c0c01082d1641010054019a6820340d111218001a120515884001440303a5085511080580300092801c00700070111409400e41030002c002c6880c010080d00c0550b21440c460000ca40c400c000403d0090158140600e15982400701d0300050020105042081e165a0442c1e4035043c0e07214241c0c4c07002d0b8498826010440d9000e40001903003114852141c100444c424500580380c44624502a0314043c4041c07201084000b03802c1d00607040d032070300b2400f022100c800d07000201c040051840074203031203000500c1941d0041d134000400740e0811405004541c0503088551840c50303140d081d4652012a20740900040b40d099040d801748611034980050b600343d40140a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 147629514 1250 147628264 147628291
    0x10518010c03140705030403020406170622060603151d0d0c020612191b08040b1b0a020c040b0f0609120c0d050a021e0604030f03140301090c020d0305 66
    0x1104011034103a18001400c1e0100507801c1003500a1500c1d003c0140940783c080c00046d900e560450040008450007903006000c030300201681c09260341030220b0100c0d403042c29001c10043d0140c001c0d882c034010701c2440d600100b0340d526100c004070801c01180c070107044404064600300203030f1030b650502d0074045800b42100c0909031b00c024000164107100d03401c2c100b201803010300b803c0e040c004064108640120145c4140440c80d2030403081038501d0540703104140c25180540020030000141e040d0143c1511800342015018140c03002c000b440981440c00d1829003140c0581780c9941d02ca441090080d240c40356021000c0c030480c103101c811000e80c40e040c400a10740140040010386400307200c1080013045940c074203001469000d80740390703000395654844031280d04c90301030b0000c0c00041e8568410082500060a2901d407444918100b101d00f584a08050318252544043c060346a1180ca0605880340301003022030f120700600000012030140c03056040b154000100c0c1e000c803900d086801c00b080e416104201c0d1642500041b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 147630764 1250 147629514 147629557
    0x100e0c0d0617060f0c13051513030b150307030804061b0212070e0609070c080c0705030d1106070e06090d1506140a1517250f0e0105 58
    0x2500000d1922806540c80020019564410040724180901207004682c01500c00c10145a000043c242c2c0d0164140001601e0a81708400c1c15000c2103190040501448020084023001008101240d0401401e140e409080703d42d2860200d01001c01121603070881c4a050200814a050018010341600d0f440744401d401c180c1032140c2203840710754840330100e0203c0e5180304000541c4030108058407108a0700c0240001c1400c010040c00c0d011030107011036014a80500c1001b103000e034401b0080c941540e22000b6903640d61401440340f4902040b40c1c00569050141c40004260030380c21082200090440e04140c0d40c00b07549a41003616404500f41d0b4554001c407040142058a1500202c0340b45028801c071201e503241e881003100f12044038500c0c3c100f0604030343c040b0b001890b149802e19504004019a9203000d0301540d6140004120320342086403900440c80e4840410f24258410076585c100c0142428000d2044a911400030904d0b18003140410105002800f008c490b548100c084a60071980c200e4509503040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 147632014 1250 147630764 147630781
    0x20303071409100806010e010c0209040201050708190801180209030a0213020c011e060f030f061107050a05060a050105030106120813080304030302010b010305010b04140409030207080d0203070506100e 88
    0x74122064512111000c000c2c1c0d02c0c0681c1d6100ca443d0800080ea0383e000c44900d48100050400c0035541500e6040c000c0003034442005a41d0144407039801982803070f1003501d500c0c2d240742140080c028500800c0c961000b800008225541c007140c61412183c0200321000c0030b103a20721400c8100d01c0f801c0244d64264200d003003540007506101024075950a884000140307401c100a40309070841340449480400ca22403030300c0d483c010006078000e2a020b82008444403007550f142d41d80c1c20b5141c00828100803c104c0d15561a6842090480152588141c0100a4484841c0d0b9890542c2d12860308580c601d1030603250000100f05810140b040c1e400f035070b44180d4141c04a00003903c4203281c2c0d4104c2c4000700b0142000840100c0c0d40401170025000a501c242c00106400c40751304005001c0e104140c1004000d010144001c00040c079410340581c44201d81528006206455420100d0a0440741d230082c1c0a00d00c03c41120103180d80e400001009410b000d2002c1d10219281c0500b2901041214460907459280344000302e0130a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 147633264 1250 147632014 147632027
    0x504080613080d02070b100603060806070f0e040606081902030720160b0703031a0901050103200a120513030206041e020904030507060c03061505070512030901060609060302090102030307 82
    0x640604803031403c0940303103018001aa880164210b400041c48030600c00308030951401c00025240c9400c083c8a52030415046594949009010030104001e181c80300e9044c80c003801c880450403001401c00d01c503103902c460018240050617503007442c6070f02001401c400021194030035079003e0441941c07a0740c070703c4040840d08440c21404411030040380c040c1983d50201c1da440301d107113100205450107580d03440782240d060107002c44031589003140f905081c5492000711984c5005480741511703003d090004e429503400703010050007920340f07003180e02d028000500043c0458010441c1d04040f465090180140d80e101c8015105074000b4003801000b40c2d0015000c07400041400c0e0488091200040c1c1000720b2a1054000480900f01a5410750104000003407400074041d150041418180d42d0b41018043c0030700d000c100114090174980100d04005011800600b001410311030100d03020204d10ba00c40d00c1f400d060002d00e009095a214070ba02044980e80f00081c203e0081c02600e0713403240d058019500b5a6074220068561 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 147634514 1250 147633264 147633301
    0x6030b0105010f11060901050603060901090c05010503090307060c020106090b01050403110114070c03030c120804050601090509010b0a14101404030602090d051c021204120809190b09040c05040806 86
    0x10b001c0c04d0844150649020865144a10481400400c0c0b9003412400c0c541041005813203581940d041c25a82c00100c0c4455401000300c550a10340380d9a02da940401040c114040c0e080000c08040c2826074461170103038150002000e41c0c400344002c02c550401e80c40103452038841c504c0300a2074040c210120b541d556008943c10b030031500304c4038041751600100c1d81d03444c001c1d140c06400480111f5905201c520034050380707062650180d122801e142d4028207240d1101580c81038140f0819134080c0d12003000507100502034004101026001d041042d40f80e0700d40008224001e90780a00074010101420810707111071186898407241c0c00c0e85e00c0c80307034901815621802c01035400818620b82000d02940035900080b001c000c03001e0794030070304071808035580c8603808000d0426246040e40d0369062414481488614445d204008038a42d03c10b078250780e59a0f040c0080380b21600040a12404590004000a944a400001880050303c200c4040214a1507a281522140298000e20311154009400902a07035140e2003160702 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 147635764 1250 147634514 147634517
    0xb091609051e07020304032303030a0905012408150c0a030908070f111e0105090105030a0b0904080c06060316090222261209011b06020a09061206030b0105010f 70
    0x2500c0c0e400302c100742c54100103445940060740000307410803e0241032040c86510078140080a5000303003c121049130f4901001d0001203401da81c0d102500c003005025403140605031500b4540b421034000b07080401504510070b128090050280a0a00c2086d00003c03600d64482e01d508500c141c20b00c415804210700804c00042c040303032888010002c01c00419441081c40199a20800740081551051003d00007201042c2d8401c00c42501143e809001c13580c0c105040d602114002c3c81c0041e160390f13502c02d081c0003804812280d983c1100800050005000300200100810612102140d100380c490740c00f8141d641c07400c0c024170360340a400550144003048181e0000d1082040d9034043c1c01000c514200b9020240b102c1d48e00a1003c0a614a0703400aa45003004400d461001c655000d80b4140c400001c0c000a03902c00d10308403a0401c03001d07801c0b114048034000000310016402142c11901c1c2c44030294050f00464103405100003080741302a84101c8061a805900244d0ba88500c501c0c11907441e100040d60441d210611100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 147637014 1250 147635764 147635791
    0x60f09010e010f02030601021603020105030c07020a030f0506040c1409010b0a0e041b020106060c11060a11010e010c0305010e10090b01030b030f0114060a0f052e020a0b09160905 78
    0x44000509000303c014582c6001001a07072800d059001a141141851042815000c46c0c0000c0002d41e8000090301e610042414505a039503c0920021300b102c03129030801000010890308071024004001a440c6c421031060302000440f54466903281e02050407129000c0c2d101c0c00031801402804c4071040584a03000480c00d1101081c3d4401cac0029042e140c4a4403420b02c014080e004003a9650b5090049100401107404e00340407056980e00e44061b1100b00c40c4031540500700000d030b8884814412900150000d06510080144030040d200d05070181000c00c0c041c00009084c0307000401c4c21008180310364010707020040d0f9074020364500804400a000c5080d54076050541d2a20b001d0040d032000c1c460050750018034000080e85983c400c1c035800c005071014040b5402000843d10074809245010395100544501b00d41040c0065496024200c09410601d8910b031800301c206d9100d00502d0b00058105c1c4668801e040b4802581c0d60040500e903100c81c10114101c8403c84140100442da1095000c21f810000d03101142 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 147638264 1250 147637014 147637031
    0x30c0904020a2c01021e030d0c020309090a1a0f011d1903051615020a0816061407020c01030c0903032d090f0603060303050306040203060a090e0106060311030108060f0901 75
    0x1d8011540f01040042001031034062001503a0620020000041d1a0b0806002c0c0141028050ba64003441c1101e040440e0b96a540f500481e00070419914a084000c11042c642e20b0842138507000b030521504d0315a00001007a1603402249419104501c282c803040c0c0d100002000c00c0c2240740191829440c2090300010010091510400144020700c0650b001c1c1c0010b1140058540b00c0c0c58503042541d01850307440152503002c0340b1040d0302141c41d2610f07681000000744c651b00128182c4070080c8403c44000c121504d40030440240040d8000920700c1880240c003900d80c800071301001507043e00d43c0c5000240004034141e50600020b401220001412501007404107100991140c45082c0c81d0700300c0886a01140e0080360030170401e102121100042c00140c503060100c14610303500540b5501011303203032030711680d0007000051064171240081002020355881c2808050104040b46c1d0081215002d40000207080100501100d800d031022681280d5031540103000740c0d03407a502030b104840c0b00681006465500c90a55 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 147639514 1250 147638264 147638297
    0xe0a0315150503060121050f0102130e0a0605010504150c05061e130c030b06010e0315070314390c0607260601050c010f060e040204050903030c0904020a 67
    0x98121104000000500c88180011a40c1d1181a075119074440e501c03070401400010910001103216a9100942d91440b00e850300d8190b04002e030349030461040358030120300301b084d4a20074801c0000302c640c0c603091190240c640ca9000020f03502e00b03000c0c0d0f41c08500100410030003041508100300b41303d8503902d4000740c480d441380d031101c0c20b00000307440105418642100c200140000c02200e01d030014000064a40b24400950310080f12000a10019005905600002c0e074243d0181424461003540241941d000d402d1b4104030700d029074001e543d40c1000a241061880400d0404007010b402115004403102d4020030051140300c004c17142c0c920404a1401c075915036801c503042e050251001c4000000600718518001000a0100c0364040b5142c90040740a1824076280207444202d6800000a181990391005c111003600d001d007030000c0c406001d003843d2682c001081c00390040200e000c0c3d031084405000d81d450381d1170034aa582c0403d641c02c00c5c0105c81049504920b182517801040040600e0a05c91440c460b01001e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 147640764 1250 147639514 147639533
    0x140a02040207060605210a02130b061b01050a1109060708090a080102090114030411040c020c0d0c080d0c021e0103060e040b0f0a150b070611030709080c0904030e010e0a03 75
    0x80302c080c1c3e01e036001805180b401c42440c4241e46c5004283d4805100e003242c00c15642c01000307501a018138000c040d806490f45d1319404c15081581e0281000340d03103c64466912071441242e03407480c0c00c20351804010a072a201a800344400c260f0001348000c3c10200d01c0701c00c2084c0d95100e90b2080ba681201040001015221001e4010003007800c0340c00180c5038100c070380002d811101c1c00b5403040180c079405c004010000765030b6984410008426100018601003001c03090307143c581101d40b41f507488100f900d4030200b008858070240c0251002103054400d0075907014001d032400848820300030740c8041e03d244c890104d810444034003101c00f04140340102c2c0941e40c984001c45d0b010000e50702a00c040144404101c4000f1084640a8021200c07580402005403a2140d4109065050041c00e0b04030307200090050502c103041d0004208241c450495554a05019030f028005843c1031050f00d10a018080242d1080e01c0c0c98141c141c440c94140c4c42c0d01440d20500001110400321141805a1200594a011000c40e441a1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 147642014 1250 147640764 147640777
    0xd0818040606090e160914010e060d02040f08030a02030708250303062105100e160e04030219150209122a040506030d03020705030c0115090c0516140a020402 69
    0xc8a00034902e0800c1240c42d00204c00400d50215100100903e44a6076813219001084410845041c0031a980c0c03000105e500c00b01c0000301c1c0380d000034049208016408070303500030421103940081020340345940d00c0d02180c5a005007000d040158000b4071006003c60b03103180003000590186500c1c9150340d00c07090940d0804c14103264054001030307039920050004c10b20703100c0d01118860140d4040d601c5204140c1d551035952003504003900340359849040341c000d028801c001900d5165004050070340300ca03440340d428a17180f001c211011343c010b01c20f600e44251f65031006010b0501003500718188658000c101301c2c08402030b501c0909240c0d041907044001441000c0306109800100201d103088154221251074800b0100c0e0204030014442c51521007881440e550016500c6094482400d0142e140c00d52410130034158061a40044482d5080101c010000311510702140c050300c8a8020403c284480d00c0411a0079020f03035104903ea41d10589140ea001c0f40c0b0301d00e0020901e40150007100d02103d180d0740490244d03003000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 147643264 1250 147642014 147642017
    0x20d02030a170703080105191a090d050604051515090403050c0f0f010509010b01120f0605090103210c1a0603070f060809010b0907050a05091306030b0403020c0109050d0818040606 79
    0x42000001c241c5c0c80440540181011030b40401e121507002e07840181310760107200750300c680c10142c900702c114080001c0903264250f0000385010383c802c4450030a0746d15540229400c031418010a81e4141c0441d00540c60300c0d001d6440040c0585141d0307030502c140310151502500c00da044c0034042c068400102c070308100b00d4a81c01003410203001c0301300c102c007941425100b010b4540c405590400e61946083e1b40e00890b0f14064001400c0c0100d83c440300115814001c003081e800094003e14000008014000e45000c02d055180c5146809100303400d070114200c400314034800005011040040f07a020b1a2080881c40c1d5030005402000c1e550166541c00d051310400074103034400706c04954014200880d440c000c0c45051a404000c0e40d9104503864541e4004019204440c41c800901901084090043e2502c41034404100c102e440708000715512801c0c41c905100d0216001c600520660303803001c40750b51090b5103410407180040c1061032010083da482900c03640140d60f00c0a85400380c0b40101003642d5480c014a0010b0609 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 147644514 1250 147643264 147643267
    0x503040e040f120e01140927090607030203100b1b0708010c020c1e06030a020d090b22080a050705100603081b01020f0d020906070203070b131a07020d02030a17 70
    0x928140180529050400c3e05111013075600c0070050b42c00c9040ea400401001d0103286e41c0e07031030401c0018100b500120401d055605040600084450540011342c0507505580807655295600901202a440308980007a0341180701d10081004602e01000350079940011039111250102d03961001d0302e042c5069004414581d150451045160b030103108207188500181d43d041300078042d01d10faa540044100200c613000f224000001400d0035000d905403841850320b0300b814444200c860601c9025203c0644a0180203020550308d0300d54401184810440168840b21042c105046c0391000d65854000200540d030754007134100d400c105d24926100c3c4101840c850b07140c041d02c905220000b03e00e0b8100303403010640c1c40d81c410045086050b50120070380e01454800d460241e41e846500002c00c1c542d000702c0704001c0d014841d040c004201e501d010000307056881c2400380803a0310340e035445c0c0c01c40ba9103210041040c0d0441c00700b00b1010000d1300b040031800e450713213001604540c581501d603566468050082c81075828101d10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 147645764 1250 147644514 147644543
    0x10c170f04020f0111011b080a1404081303140303041406010e010e060a090c02010617030403020d0209040602091003050a0c03091505101701240303050d090503040e04 73
    0x4200011400520140240011a140680360580248405800030340700d003c0c00200c420742c60380b14101100904030304200911070241c0f442816410400f8402c1c5450200d01070000040c0307811a14841e1801440d04007240c0e030b001d0744550701c8101d41503008016604450008000c08400310b030b261407a000d4007584100055a42c1d2a250501d69918190700c3d10007203050308041e004010920f4280601415204d13841c5e07000c84142c82e4a80000c03272070352659014a03001814582800138003501944081e04840e40070b81c150341059038007202c1d41d2b10780c03069001c006e40c0005052502c20150030013000f07507903201c1d1003010014a807020110000e0660014030a0f0100000d40354803c10883e06540c0c09035040c007480c00e060138400e03041c260380da007080061207131000a4503a989800082465800103c0040140b1001c036940d080f03204004101d038003a000c0602010080c89006105410030800741301060100c030f4043c0e81d510304008103e1201400317444992020707100c610043c000851114881d050060060b8440c2180868008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 147647014 1250 147645764 147645767
    0x8031602240a0b060412082b0914120d15120b0106030b0301090c030206030601090306060f0302120f2112010e040b0901290301060b0403030f0207081606030507030b0909010c 76
    0x310343c081d0440c00b030003060008114199121458904055100034120f817610040d0303004001a8036400c80c88841c6e082142039620039091264400d1905c6402180100740c2800c10f40d04032035403040007804e41c1d0181071301000031317002001860780101174580c0b0303807030f01101d03000e6031004100d90503100281c05440d086041e200410116070507101700040000e0540090040c24040d0b03c0b038108000a5100280c0140c0002000482a0780b0803031f0303000c02448e8002c004001090b150303203600c1c0307503000345000413170003100d038124800a5030f0f40014641921514090042c042031b0036080004060554120900385112130038030000040900c6200281c0c06807000c00a1111a85440d003821200c0130800f400f00440380c3d142c003070070034821510308059100c07148003410705044422808010900508055200c0704000401180120402d580020080300f0310166900b214000c0da110300100c0e4036150610701e14041c100688200300300190181d00010b511011600b0f0015070001d0003030200e0780b404030454803c5d0042e5541d41c44452001d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 147648264 1250 147647014 147647021
    0x4030201020a0912020a030206030604090f0b06030c0a0312051605010e030a03110a0c020f030f01090f0506090d02030301050d1a07020c010f02070b1c2703080105060708031602240a 79
    0x81c00251345034929406250041130341888a40400703401224000000b07046c98079240c0008850355400611912046903500300aa07102e80b05840f0030b4440d028034914201d4910300f1805071000e1b240c012101842c0b917080320300240e909074841600341d400c1400314203003c00468400e204440032858200003960382d03584e4290700241124003124081c91000c03802e000300500541e003c60390350f5015a059680f684402e8241c00020b00d4080d403800d190b00300e07600389401841000850244060131902c81c02c1140c2e890f444441105132103980f291602c40060b40240010041071911800740006a4003840c8400d1500d204500c102002c41e00c00c417209800f5131b000c0d40c0c080946580c840c40c841d40176500d510151848a04210525400c0d1040000d035000103246280302400826003540088241c40018202e0120300c0d0401319414000d02a820054010584801c00068642044000c031104035901003803036855680c420820b05e03000c001a0341c1c9181184926042d4651003961041d400755565528a4098805c0c41e1640851703044c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 147649514 1250 147648264 147648269
    0xf0f07030207080901140c07080304050a1409131b030b071202030601090605070215040f0e01081c030203180607021b0f03120c03160b010503060601030e1b010c05010504030201020a09 80
    0x10988104000008105001c3c181e48407054246002005d410421440340c0d010700441c4500f0005009181e000a80000c000009004841041c1e9a0100c00b13540c0759084c030f440d80c2100f44070540119124001800d0168a0070304070ba02c00d80320721052079401d0500054440403503441e8204444082d800014411000e0f00b04102c0e00c030032035070740c07a080d071544c940000020b16880340b038443c210a214000c1030705e03401c5540b501c00103121801050101e40d141c0707a0781d4100c0300c2150344512603c18103148601c004603c2034000f042c40044020b280429903d003801d008411802075000030150004011a0704011441c0d0809110203406030728648e00920380404490754134024916140801403140d10f86454002c001c1d140892044604a1118802a12006009903181c00c6104205820040c1c0d45090740c09000c204d2032449540c1138074010f8007101c000d90b841c100150b04588034091400d04a0f0311554108400d80c200e0820350307200e4841032400e9205491a50390f602e09540c016102100980d4001c14044101503001001500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 147650764 1250 147649514 147649517
    0xb0126010c020c0d0609060e010209120703030206181e010f0c0c150c09120c060e0d0f0b0703060e0c0c0c01081312111606140c030315030f03030f0f07 66
    0x203a8000c941c806542d034400700303041034003841000500d07074240215540014841034210134180800500182414000d5010142051041c00c51040b130000c0148001081c40a89625070000c1503a500c41200f00c030f56240701089084151311441c1c49040e02e8004070980d059090001c0d40c00400c5030307448500ca0a0544107043c0300c0104004ad20481480454401c52881100f41c071040703c0007640c1c04d5111404c07152005035820a803c07c038060001c4004101005c1d1f01c4c1012111a540c81641000c0c10b4000c000e00d08030055806011040b1000310709020071413605c0e109402c1001400c000a403103590390120703200040102d41f00300602c034001ca9800c4490105211502c032040342440c100a0317614100740014010b02d0029400340440d118030b040b200425025014080c500c0d241e0b50215510521300440c44219945c90740641000a501c544080c902401400e0030740340754180d1100a1800c555409840c0484890360788c01c9558184103448000000c0b00041c00154000c11007206000000c1c0390942c000d0003043c1001c0c10300b00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 147652014 1250 147650764 147650771
    0x60427061a01080a0b1206010305061608070507030f020c18041205030103020303391c0203030c0403030c0203010f02070b071b0305070204091703010f050406050f031908070b012601 79
    0x1c907a03100440a5106902e0310000500104400200703c00007400c0300381e80b0080c0314003000401030140003e4036a1184541d810034119540620008551045d415207800c00403540521852000901440120403280a180304884640021200140601d030702c5915010500f800c60b828803091001917001884d1000142c04c00c28a954903640c04a42d492041e52011580d6220345800c500e1410b000e9252061350042c8011103503580417805032025160101d40030408107105030541070306001d50010003500d20900e11000890300b0b0a00d1340e00c003611a001052000c0740d15560380c0d01c8500580d501c034030151544600070750010a40c0e180c04040541442d990b41d60030355000a140310f0010000f548101141e845982c152808140c0c040d04d8602491850701e2202900f4401364040b00101e85c50444601e0202182d42c100d60030311110351f40700e080c822070007902600c1d540c1540011a4402650800900faa042c0c00d109084946c85d200700c64a885201503020b8102028110300e03034203950341c80c2d0441010044c400070408000c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 147653264 1250 147652014 147652061
    0x330b0c0703080c0a0f0305030a050601020106060207060309030215071e1b1101050702100206100f03020901171609060315020315100e0901090617060c0406030506042706 74
    0x165512141407200500551000507000c0c81c0c01428020140c5280d80300d034204441c240c603490054541d8008480c01016246444001070b1150310500480088450940180481c1d034109036089024080414040e001c0d0312404c400c000c0401d40c00e40100e8410015903031855418410401c41c9600003028070f001c0030403c20600c4001007410900c0c06407112960740504a01400080c540c0161094002d020010f984101460480b5420030380100c3d10700e104114408000754220744602e8604010b0302c95000180d040310600005014040c0d5550034000c00d92920804c54020400b052103c41140a280e000342c01d0407900d031842082000341c1f41148902c80041c4001c194190f160580c002e01c43d410284508603c0345032010b144030326a90055060328092500a46072100b59a103884031840030340745034425000c1c0c2c02031300c003291307010400046055401044404003041c03400b40b0380b00d400c0380541006007145a11a60702d4079009000c101500404802c0d223851a842100c400d07450410400f203440c5042845100340b0741110300f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 147654514 1250 147653264 147653287
    0x70f06020705060d1415090105010507200f0d0c03110904080a0f05040f082103040c0e04020f0607050c010e12030a05030a06030203011503050c101d04330b 68
    0x107120070745500750b030740d151200d503109000005003411001208100842d203003480419800d060010207044030a59085c007030750343c2e99001140e1900c070f03400014041c960021541c0004018211090320060390044c2000a280200c80001e03c8491010354101ea40d44200501001004041e11a108101d0381c2242c61100c1468241c0319442a40300706510901044200d091a0b0300c00d134029411b56025041030400c103050143c65102841c0d13200c02401c44504885005090f0950310681c49040361303c90342e4484032604100c0d2800d0800e6410b0080980200c1c2e102518680540d0035031181d8014110035400b0300700405100f18940c001401003641c910110303005c3d05100c899054061070010403a80c03000d045140c01d40e543da990035108002480c0c1504000c1d85942808841000202110103140550303004e0026180e5401800c404c02000800421030355021940420200080418601020381090340181002c201c1e04a00240803000010001d00694010f000005031a1020f05102d20200038100141d040c03803034545000030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 147655764 1250 147654514 147654523
    0x90b0301060315090c02070e01050418020613090f0615080105010503011712040902030402180624120f07110f250b0c01090204050603060601120c031508030309070f0602 74
    0x7501c028035071108440f42c15012020706100c0102140c4408004a0b00d140d18001e4803081c4901c00c10220145080000c0b40f1450310748511303002040c070a4800766041c02e05909000540d00011000035004004000010f140000c5010b103020040500d2030002c0c040303040c0b02446800b03081041f002000c12068800600c80399030002c046a041d125004c00011484008090a40c40e0010610345203154500c049400149590203401450081d84216504055103001c0b085820042d10300325030541d80000c03407518a040090001d4560941c11030080c80a03442c20121070000f0240810590340f400303211040c441006002648008135011500b001006410420703007600c00b160396824019809010400c4140004c003400e40f2130b088520007411450001526003420328000c0b07001b01a1940203a0086003010005400fa00d4003003600351085205854031000c0c0003012a50030010844403812905040e614005180940c030030003652001401b40c00011030796454642206801e00105070710101142484000c24801c290f00400d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 147657014 1250 147655764 147655769
    0x11b050309010e0a0f1a0702030a180506030f01030308010503010b0f1009080a030302030105090c0c0a111c0804330503060105071709032505040902060712080405010c090b0301 77
    0x98295100e844110706180100081d40716448244601e11140007004074031030741283c1c000d010b03070f804000a9000d40c4038a204a4412120f01005030010428003200d64050000d0480f54a40c0614140000c1c0d15540030400b554015111204200044001001010750080206000d0716040e00280f05207195140411031420310442c0f290b12600340d08184414681c400d45004008100f8941141e104224900f8003400039130003802001d00515000d800a03074951121411a6060300303186c001000804599140d81011007030340d401d01c0303502035400b40304001003039400421200b00e00c1c02841c00603a501e181c08a002d0090200903040c404200d5140d20000410820443c051000006801c203160340780d80b02d400480d110b101f4544010b0140c006540040401c50564014100008042d011210201c01a056254400c04000c21403041403540c0d070381c103200e00c0c1041d800070514540301909482c100b075141d0303a5104540c5030540d042000520303003000f048280f04090080c41c80300c403c181030184d15030781001d0003d5410310050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 147658264 1250 147657014 147657017
    0x2100e0d1211070602070f110307030b0c0a020a2415150507050a050106090b010e03010608061303090b0c03030f0c0901080a050705071b060f02010b0a030f030908010c09050405010602011b 82
    0x1d420080212002d1821210303403079804a02190f8500603440c26542e100c915680c01c1d034000100c2d074031503203050400013079010549402c180107640707641d6080c01c401c0e0036a0001c0d8880c800c60154003040400108202e455505150202d0351110a21104045000403a804102c83c082c0c00222200d00f009006c0041242100c048030514186a07070380700ba810b000d0300e024110744004140790321b812070000d0144090f07807004103001c0090381c5901e4680401020035090b00d07001e000380c1c0c0b00794205001290b0006c10b040000300307682d0b1090410040050369560b9846080d04401c240000c0c0f500004200812440b502c0e0100d80c0c844000741a03141810305110009054030401003035034029a507035101040c0d20074020802e40311800e44c045005a04000240740868603010680305d140046118408204111030040c0a500c00c482000f805000390700c1e00d9070f11004031501c50380340301390140107100c000803071030050a009094002e42207882d0021203500e0001400221001648854216498041c0302c80c41c2002415510085071042d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 147659514 1250 147658264 147658271
    0x70602071b080307060b040e15060f04090b0601030605010903050607030c0c0503031003031206051c02040212010905011806080c1905062206021504200406030302100e0d12 75
    0x340c50201a0844100c0440c100018607200006007001d0000080c00d8061003410180b0172070003104140404d4a440d007a01840c0c1d034000e0b4003070412408516103002e0748104018580c102d523101d001d02082c01c032903035000140d80f9020b649042044550700750081000409080c81d12417140c1d443d540310341e515070344080d00300800c0680f0740c0c4c8042d2480e44601080907045030014142c9076a030a22006000000340f01e4401203020030103c0001c00400c00d198800d01044030000752101c10217007200e4401441400040d00201e0740503609002c1042c034840f03040e403041c1c0a809140f500207003650610444e5040b210011b07102c00c00603401d00740140032211000c00c03a40307076000d01a03419100502501488000711040346d000180c10100210f03860b5141504a0480d2820001c1101000000b82e1200c00498540d0740764001400108980c00106000031119028000308034181c8190311241c241c0d5100041c25103c4030360050b801684003048828240c40c030340c41099001c081141c000d2842c0441480302411290036110307801e507003664 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 147660764 1250 147659514 147659527
    0x51308030a0b060f160b010b0f1c180302070303020c0303070809040207110303031005040f090302070b0a03020903012a18060e0301020d0c051e0906030406050402010c020a0602011d12070602 83
    0x3184001d42e1006401c00d000e1300d8a0f2801d580c168030b0f00ba20072131000e0b83c4000780b02000040841e203070011202603e041d001001d140c100d4000071000e202065540428002e80d45000e00000d602004481007001846170f070140100d81d103181002880c045d0a0958680700390010030028002030360100403607800c1c030030075600540c6914150405035110440940b0540d0140000000c00403001e01c0c012983e01500d404580400c460108100528111400d41c100100542e00c010018042d40f54900c0c040c0004824030704d405894500c03450086401d4800e000c00c01401010514980c841140c0c0400540c90030b0b100300d191500001403551a1211000c5040c0300c0d01042c8841647c400600e03440a4044036074003500c0410500c400031007004000c0844c1e01c07507540f5004081500e4904201d030602401150342140000f00180d007903441d81d0702c0d0303a0010301c1e0141c8104d040c06001082c11006031151509a001010981c000050864001c110b01942222051141c20250054220b210500c0002c00903a01810303000040107840b0310 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 147661870 1106 147660764 147660769
    0x20d1b020306010302041503080f0405040f0b09070503070903061406030705150a0813060e06040209010f03080304080d1508010e070e07120506010318080d051308030a0b 74
    0x40000d0010400f500c1c6c9038000034003403c00d04071000302c41039880d56442c0d010b038028003082d845c80d80302003030400c424500351048074401d9110300700604c5031400e900d00007500007000a01030b0040c80f40200100300058403a580407805140d000c01d0402904500854810044c80103c0381c80b4400c0c85001004134103400c110300c0d00c0c40c4210340040316034201120403d09641840009007004000d01e1803007603103004217000d400b990411074501d5016100740e04241c01480100740d4141c20540d003048003c80104009080c45007180c1c1d100342c001303643d51b454410406941001e4030300704582e003643c0d144244000c50301100662084041940e40c8084810341c1e640ca0786580000300b001c450000208051011141004e641d0750041caa109205140010300b8002a0320140420710160000b0740714684040751081c1c0c1e01c2000c0c0308140c1c0040d0709140180110042d07584451662000400c1d0180690f1100d902030f29a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 147482014 147661870 := by
  have h0 := BRFrame.cov_init 147482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 147482014 ≤ n) (h2 : n < 147661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
