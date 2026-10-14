-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0177
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:16:28.270271+00:00
-- url     : https://prove2.me/submissions/c2e2fa39-443e-42b7-95d6-1529c8154963

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 31654681 ≤ n < 31834537 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 31655931 1250 31654681 31654699
    0x507050a0803070903060906020909090c0a0b090a0b1207020c010203040e150d061a0109053f0a06020c06010504020315100e0301020a080a050906100e090106050d08030709051509 78
    0x1841c0c0b24804884c0199846401480461440e00e80343c00070390046102b0501031001407000400d0385170005008402114050a05048141810380480711a808850800d8120084420014a40b41104014406030321400c8141c0042c0c1003112000703041c000000746a0341198018803003409505000c03c1c1a0b9040001000031418071070100c0007107020035901c20000b500b03940c03402da03d0b542d20688a81d001040b2400c01d9840302444c50700d4034200042c091b200016400c2c04203034420500008100c0e0700300d810042880d19a031141c0210090401481c15010744411528980c0100310800020340802601c0d02400c0c0840d0150f081d46000700402041950011491788034004104901a285004400310201c00101a0003036548a40440c805805078001343c0b580328009152a0005001250200340107008000d07482400b02842d28015840100c008094034203051950f0324030700041c07280c0d039507100c0440d030070710078040e480c0c9a19180b14040c1c84120140d02c50382c0101c5030404c18403099802d4800f01c1c3c422120444a401d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 31657181 1250 31655931 31655941
    0x80412111507030f050108010906060e010b070312020903060103030906030e0c01050d0903092d1202030a02010c05190c15080709180f150302130207020607030305130c03030e0a060507050a0803 84
    0x80906010340d80395591360300e0800003054144041d0400c40c0103d0241000707019003075a030f00103130395085424400c2c403881140c140500f41c0000d22641000001d41202200542410320000029040a400780d204501141d5009000c015054250180c00240034000000c0c1004508080c00038010303100301c0342c1d0891442d6aa10300141003500034680507019059500407000c40e40e07845042d016180c1074043c1401e1090501c8070001450990b4007000f042e0f943d6001d405045045da4070b41c01036034110f00c0e0030b4048401c1d0140d80c101c0f00d00c10b0712400c41048840d000b81d02c5058410b00c1c0c490900c4403180e40d102c0d0301040104002c10441019000016338085600314601e44401014002036103006200841d0f04120140c10f0020004904241d001e00205503402107a140b640c00700c1445484089100c0c901002f50896024088480071074080d40c84035600c44450202c4810200942c0e4860050116941003100810507081c5a080c45040a00501e409000c1d2030401c40d180403121303202c0d660f44450a0200402d01c0000000081c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 31658431 1250 31657181 31657187
    0x9050904050a0507140a09050105150310080d02010902360c0c01050103081305060301031a0709080f070905010b0403020603150f1909050601090b0d0c0e10080412111507 74
    0x800b0aa4001c410740354813035191510b43c40c60383c2000c01c1042c4142c00ca40307004142000184074140c102d0b800200000404600940360501ca40c03c000c0006400ca0112180061058418809450013804a038000688104588100401034024803143c8000e100511801c3d450441100c1c0d568210629180c7c9a4030555100c54080c09241f041c081d05107019420314000100f0002c0102c00f0344000c40c0c5126a00c03160a131501d06100d81404244000380803074540c01c99000c001100ba0080b00c0d001051440e15450880e180e9181c103103020466000c10b10590b000c18001c00581500d407140741d001d0820742d400540392603d507400048450001802409016140312300740700441d56585030680c0c1c1850041c01c90403448100307821548011344107110b0601528140400984a0f61085401300142e5144000340d0741881c40c100700c1c450040000020b40c030207002201e482c01182c1d56030f603002c6404075901c0c3da4605d5070910302031903c10400135a500c40041484881c0d40200711410000c590701c040f90001c102d42903040c0c1d0b9100811 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 31659681 1250 31658431 31658443
    0x3050a02040f06090f08010507082202210c03030306030d11010b09040f0b070c020604090c1710030203070801090b010302010c05030409060b04090c090e131109010b1e07030905090405 80
    0x1a200b100d01c00c0e0006495801030003100444150b2564841c1d61a69040380710700f41e405c00c58100c000110034600040510415146e4500b210300c98145803442c5170302c20350215118407140c9841044a9a45004c801c01134a401c02800380565000c3e4059411401c000d030100fa5150b420203040d0041c080819281c006489095103c06160a8024620307421030426040003100c00141c0401560801c00d03100c0001c40f40350082c0c2950207110f6020340708034500392030045808002c1c80888018130403c1005505503409041815020f409403030400e0484146600e0340c410580740500d0382c0c0c0030740d00c10b90402020304040f03404080a14116502030a240080c0c0e142d40c581642148595080328403002e00c3d00c1c0000c5607160f44040070384190f81c075181c0c00f000102102901512440080e01c2040c020420400002d582c0380f206150488085103d0740c8002d01c2d0400301c500046003c0401d81200003000c00120b84000300003800e600b015286c2d12b584c2e540502c6c1116948000700028507601445014140340c401090420004001c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 31660931 1250 31659681 31659689
    0x309040e01111603020d0206060604060309050312010603020a110601050604030b040203030f030f06010905030c101b060221010509040512090120060402030f2a0d080703020601050a090203070f03050a0204 89
    0x100341c0d983c42940c80004502c3d4a82d50095006100f040d4002c3c03806800040c0090103400e00408860601e80740c0b403001c801802e40b00034102d80c41d0209000301280903541d030304141c0c00b074140ca0703d0258699001c01d41c01011010003001d008066170001d0010811510380030101c5040e290824103c000d207640720b00200e0f2461082c2d881001c0c1150001040100110400601c1e90042200340d941c281002e940c0c40030969a5071403050318a41c00040f0030342056a03a800b5403800340038072824548901071a00d081d1207800890304900c0320841c0c46a9007003140b4001400300d004003405084100c1d01e20075981040c1e01d680e59182200458a540c0000001d003480fa1a806200c611105d1032004400b4a0340310f00104880b41c540341d003038400324001e02c6650b40500740d0340c42c013007000b10880e084d49001e410320700305281400f81090155038200d42c000380a10000404200b01c0001060800c1c000e030000c000551401e02808000300440c2e00000290b44184203102019502c02c5034290613506514010603151100d0154800903c56644 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 31662181 1250 31660931 31660961
    0x2101090209010b09040f05010501021902030f0d180b0c070e0a0612080d0b042310030606060f0807021207020907090915031119030201050c01020d0c050705010b010207080309040e01 79
    0x1000041142c10f00000b082c403200141c0d070070f03c0180035a1560109642082c02414050b8000072008425000307020300fa66405400102140d00300502081800e042007084e50001e0000f58a84d542280e003d0040c003100c6000740020700900303241c51003816000d0f07128203483c0101541003c030640400c101c1c500701d4000f00c000e8400d01150250561451030003045691115a1042c005810111028072a00c0c2034401c1403107140c000c0c150394090b08240040198203000007490140420300000000c40403540758401d24000c0e004684850100481044001d095007000810a8007154850b88848010b0820f407402d948145906548020960f29a080107940310704080d000811920324000003001c12002c05481841182c2c001c22744510044d4905041c4901010400c0c0c55640c0c81d904c3e80410001544540010821405240001406e207001030410f001074680c144100e00010b14042106000d201088c801d20102140c24001414110310b81036072207469003d66a45240301c2c50380d03601b101c1050ba0080d04071000301d030700480d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 31663431 1250 31662181 31662199
    0xb0901060f080906014704061b0803010506070303020d020c01050106090803070f03080c1605061e0105090106050f0f07110f040c020c060f04030b0405011a1903080f071a2421010902 79
    0x2211b0040321303400c02c0c032690700010030a40010304a91145401c002809411896075440d5a0a10b4180151548806000c408240c0d0822203c10303103c9803407010300202c1c20103034004900ca514011004011500c42d4100006581080006000103548040310360b1040d42c0c582401045a900d1404002042c0140c0d45078900100030100d084007080400700d1010711542c4401c448030800c8150080001d03600c0c000340586901302d07503c80010300410b4014006011441c01580d81c00d8030344100050785502d1a00017172000c1382d0000c0304102400d46440d042c4840c00c0c1a60342940c080000d900003d10003950b44028000c942e0140100140c10305200522070200e401940d080008410079007003d00d13019000340204000d0411000c11243d4119240c90550040091025910184070016095403903840c0c043e400700300509000c600802c00340f00010701208911000148614408046282190421000300122034010101c00310000306944140d03601000907004080100340e03580c4588007041100d004000031000654088108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 31664681 1250 31663431 31663559
    0x40906062105071202010903060b04020403080706050106020c1509040b010923030606060f30090a050607111504020a09110a020d050301031101050306040b0901060f08090601 76
    0x3040c210721980b00c2c1085440c210b9a50049602290102c00028006290780313000704003240c9641c20010b0020310040005252566950f14000e0302d40c0b001108446660710344004000300ca4043c0079901c80320905882c42d41140c0915207541503544101031030036219550700c0e108802142d2080ad00071020f09552360042c502c6403505d078031484038840c00400892191003440d002400900340704042c0c640260850340072509002100402420304104050f61040c6c8000f0038070020324080d10303143c03060300411038100a000206118240b0b0750801d200240488240021150302d0f03041d031100020200e035404a495002c6105848620015003144040c0d44030302c2085081a003d04c1c8200310440003040c012095408460f01c51000303480130b0350a40000d03c4007074154100852007030815406503000390b40c00b1100800010700c0080520001701100e8083c0c00000000f50f05074200d40000b030300100319a42019400d00142008d41c5480e844899480504180e88058410294100e41c28514130724460710a20504040780840804 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 31665931 1250 31664681 31664729
    0x30e191715090a1e0b0f070201090507030305190305010806071d0405160f03090308060904240b0112060807210605070503040b010905130809030705030709050103061401060e04090606 80
    0x8a40400da4440124120321901204c610b10b043c44031300d40c46501607080e0380d40c00f244003a800d10000c10402c10344d502c4019080000314140000713009981b09490312134035a0014400b440030300401c8107412062500d0500103004d9101e000907625444002440d040c2c1071031018580c040341c000c05800b000e81c7c009003000c0a00c101c101082d15035072000c1c109603841880481e8aa031044003074620300340000d004505001d000c2402c50400c2d40009078002c2c000d00174060b102d01516041007a100c94401ea10150507950f00d441201983e0003d250b4913078400130101404200e00b03140d0559225205807003180039400c0c41c6c214030303032110305003520000c0541d801010400c030f1880d00c2c1c00081c2540d0303c2110129100c0d8120b00012600c510303030780303e02c5028104c031000c000c00b01c02c0e20350707074500d019400b0a86e0301e5450f104d4550f00140c0c039582040800007a00b60001c0211300d40d403561400d6400d4402901c024900c0f110040e0040c082168043c0c012070600d0401c0350040741c2e07441141031040c014507803500a0417094203580c03034481c500740b9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 31667181 1250 31665931 31665943
    0xb0403030201050c25021c03020601090509070506030a090201091d06040f0903021905100e030702040c030203060625020a0608040b011a070204150906060903030e19171509 75
    0x40203070000d01c4159980390107400c0c284035090001d2012481013a03092810407116014061035031000d8034100c114034100c132500c40342061444e802c4005034460310042c0103112450013a6038110f0368140c010000d40342040700007015400b009201a1a95030789005030010f43e0303c10310102d00103240b21540c039001c081892000300485c242c1100d509000714189000303401c00619620031018902d0301540940381484040e003804007210b034080e60581b5140705020140c08050320500c58501171402000c011603850185206201c181e5252611a0701031502c14801c010319600c4000845100101c401c0600c010980f018406010300c84640c84d010350484408180410f000c0e410040c01070260740580903400441e030761001d00b03200700740701c460710208025003d0106400608140d0000c060400342c00d5900285d5603219203020b000c40d42c0540c010000181c0e815030400c01c1c5500711506d401c0d00f040c00c0e1400c504510600034455180b0f40107106003e140c00c1e908500c00302c001c03818001d8101c0004000300869149c203000f51030b0b0f503a803d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 31668431 1250 31667181 31667183
    0x40b040204030b04120504050907210c0315050a080303161b030f03050a06030c05040b01050730020303070206130203030705070e06040e0604051221010306050a060b130b09060409060b0403 82
    0x941c00345c880c44d0070314050f00c161022200003c05a40496948160440b5501000d8038428118900c070b40307446103c003a2500400320300242c0c0e554000f0f00743d0082c0c1c511a1080b034140c0e01c174601855811005014102020040703d5000c41c4181c40c070013540a8080d021100d144118401921000e401501d41c0d003055032014508185d03100c2a83d0034000c5c2d4450101c1c400c211402448010070040c0c18040800c8281031a400200341401d05040803400c0800b191a841c414900004d600100140c04140c01110a03007104520044180700348000c50443c039100101030b540c3c11021340f15180d1034880c0c13120343d011980c04004950320154803c081d949950794580e52400c0d605030550350203114071705090b401c0c0b490402c000b585501c1a500000203103809502802e00304190f9028800001c0c0c1711444800c846014001c4081c024001e601c541c030000780c1454001e01d1b40f012568030744c00c1801d10030010022a40004c001007804e00aa4040c8150560381e40281d9000851900c501e0707200c40f805a043c0080011030042c001c3c0900122 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 31669681 1250 31668431 31668443
    0x301090b01200a06050a060f0f091b0c11060f0c0609010e0109051e07120b0603010506040603030c0204050c0c0a060603110603041502070602070803090a170c0d0509040b040204030b04 80
    0x26541d814a02da407009400c1c00d281c4030540c800d030040b0000c541c040c2c0100390000040000003035969203039400b2018190a941060b42000702c4e05808225042e0244100c1a44090038a54004880201c0e03800030003840c82103501400030b841ca0642d0100d240c0d510b404481c20321440303041240d0340e640c5d0f90140e240c403840d00f00c03110a00c552910b2000c8075041c030113000d418502c0b0351000241c183c165114610446030076504204a02902c03409401055440002d00840241c1d4007410401e0900d00c0d00000b014207490004014501071820100d0070000039810504620095a04480c0440e0940c1c49491200c014099840c03080b24602c180d0707001c50203101480d881003003942e004401c8810801c1c52703282404081e220607603000f40072a85d82841400c0403a820fa0262045078030400000d858151151940e1001d9003090311500600e41100c2c214400f000345403180c807200c030410041003d043c84080d1401070b4886c907035100d02405103c80080d144117140d07a698407504100c0e0004000b10f4072103840307040075003100c40211000c07110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 31670931 1250 31669681 31669697
    0x30411180402090109060b090103020304080c010204030803010906050d030e0105030402122d01020a080601111603030815030f031611090702010912020601181109130209010f03020f03010302040c140301090b01 91
    0xd90210360048401f40d9084580c03051a100d03000e80110005d501c02002966120814404411210401c0c0000c0c030041d030041d04583e480707506100c5040221111340d44820321440032500b140c0002504039071000d00490b000d082154590f80c482c0003180c078840c0c1101e071511560092841d51410340c01602d40c2d420884c07900035501060700030428001401c070300c13070b882c2071001103140711002900642c401c00341c82c00e42c0b129610586020003064900c0c0311450b0a55003044011036180001c05c035486140c00074240c81044120000c104400c48180b130a5102e1080c3c4041d00c03082c08940c1034950600030820072854490780c010784040118030b0002d40080c000e00b07000c1400c0710442c01e0121000031080c8000780e0281038541090842c100b8480382d54819000700a001e503001400c840c103024502440c3e8031440031030101c0300803800c09a40c07038902100042984401610702c1c1d00303043c4144a0740c0329068002050f0703410b5a5064400060724407600ea0140c800d0040394440e40529600003001142d014195000701038128000e80350319070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 31672181 1250 31670931 31670939
    0xb01090c03050105030604080a0507051209010f0c020127050a08010212060d03090504050a0b030a030908070504140f100803030405150f0601020a03030c050f040303031b030203100303050304111804020901 89
    0x1520b10038811242d05602110200c2c3c0400e0041e0700408044040d401c0a138580b9041d82d0b5aa4142078a80a02071107d0001048035030382c13542c00070171041ea0080703249000c00f48940c00307500107041260141000901e46041d41031a18041c010086203102400c401411040075556840d08c1078082c1d80110f812000d81142d100204a031801c290034404041e81d40354031010040c03401c00090100401c0000d15135541c064590030000c2282e103003488081e0b10a030280d9600151142802401850520710ba440240642c2c0740070f56100e04020b5401c403e6401203803a00720240162a4076071072420b9244550003d04940c080003060200300100000e04e151074028941c0003040399542c81d2070301250322508032100341c09a04015080380000344a940b0295042181d0308200307007070a010441c031108039041508110042035690600c0e14004c0c241021840c480200745c50103600c0c6282c80a40d20302a5012444001c0034040080302160030024241200041850b01420f8080e0070901c0c0e0760a000c0400f400d41d4241e00940d5a0302c0041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 31673431 1250 31672181 31672187
    0x20c0a020f0a12121b05030306010206070f020a020f030106030803010608040618080a030b030708060109061a090d0308041a0412030506120316030504030c030813080102090a0501031d06040b01090c 86
    0x2c0111805030900709000c207265100c65054904103450340d02040200c1c90042c1010b4028001410007034050070045442c3e2030904000b902c2c0890203860741e000d100d860305104010030381c001a40c040c00c0354180d2300c41d81050b1100300840d0160416400087c4200404000896080d5100c1002c503c580d004050500020701030300a010340c5100301e80e13800b61105c00b0400171401c2c100d0183c0c0020b094000050119070300503640300081d5080c000280c002640a07a10350808203c018181000c6290088800981c241340003035550000c2d540b000002c0d070080912040d04000340500001008400c0b034000d215515951038a031500e014407204c0104050720021070700d0080401d01a08151502c500c040c840c7c10004d40c50b00221804d07074401141c8105089040210400004c0001026070640b03900840c42200d010780c403a2481c000001200a944d004600168410b100b200d45ca0394070303001c10360100c440c20700380003500118440d5194001a11841c032400c0c1881890244030030402c04008150403600070301ca003000001c581107070413 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 31674681 1250 31673431 31673449
    0x10f0c020a060c0203150a0203070e041a010807020f0102031005090c09090c090d02040905030711030a0b0109050a0902040e0c040b040e030d020c0a020307090c0e0108091b03030d020c0a020f 83
    0x180d0440303901e4074140300300741c0034400011007076000404880c052002c11400000010044903180070a135008004e00c40800c0e04440c1d2856074820884060243c01806001300c2540c1d2000d000c0e2504104551000c2000c59009200e00340e03000540c24020745d0b1703900d01001d10084520041c40340ea809501c403140000c886815240c15a100d003c0b00521000321501c07040c8243c0a56086841c0c4650320190b42c43d00380c0c00680d034501c0b413100d40305d100d1006140c51318150304021043c0700107441082e010381c005410300070024211007150790548001182c00603090725004140001001034050094100b4640440c0c6c480244002035803041d0a0011541446200d01c05414801a60010310300c043c029841400302810000640d005407416034244000c513404600703950000b030f00e0030502e50700071104980d80340034034104076074000c40e1445079090a0a1404907400d05284d11943c6422f81c40500d00004580840400c450b0703814422141d105004030300940d110b42d1140c00031a2103000244049208022030101403035582804104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 31675931 1250 31674681 31674683
    0xe040921020a02150909061002030d020a0905030f0303040b0a0504030c020904080d050703060609091a0612010801180201050403031107080f03040609080c101202070f0309030201032f090109030b01080c010f0c 91
    0x1c000c0d10703511401d048c89043d2220040440a5010900020110b2081440a4490b001c80c17541c1d00c10f2480d02c0d2405141c10100400000c4c1c0040d00200200310110789581c5180e90080380901001541c1e90322030408075441e000b100d200a5104440400340002e101d070020103055102501407007001561a61001541110385910603074000c500c10301d03010010001207078005c0104800b02052072200140c000300003522684200f50b940040c00f2404018401c1403024480c8a02c10110b4281c1001c1925542d00064543d01951000608006c00700460f500f00c40d2050010302c0080c2006012515250101e40f800364498000b40907000c00140200c6e000600d031800016034254964010f040703c07000407400c11040f0303401005803145402040c1c0800400000400044450b051240284d8a0350b1030241903100060544107941d0900303423081904c075104100750b205003d5844c680c981801e00c49560740c90450043c1e41c0d0809940c8007502c00d076014800026861404140e003916907400340e0305d24812641c26001a80c2000345214 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 31677181 1250 31675931 31675939
    0x501030c060513090509030712050f0921010f050601020c010207030c03060209030f03070602040f0b070c06030203090c04060305060603070e0c030112020f0d030e09060406060e040921020a021509 85
    0x104014180c0101c000300308030280d03088540e0380541c90340700040a1317501c251410b00c42d6900014020050040710240d1500c0c0e07450341d25003140f500c422025034414902910321001d12807540d04200b01c204613400c030082149014040000c0c00b500e039942120100810044516130b0250140083d032280c0366101007480c100b640e9001140e0b1480c1400d6444100094010114a5405119811402403840801c00203006410302c15280076940b0b030b04184003070700d00c84c0c816400380b81c1c144400c1c07190100051034581c2e440192003207440c0068580e5a102a02850041c90300c07815900316290a102005000c00070034014400e09080d01102c05840c1e48525030a2030582c02c071000041d00d20103100501803103c040c201c01c518540020010074405040400148006c141c003034084000ca6071056040c3c955003404004550702880c11102088914640003000d0280d0010b802c107544a99914040310040010030400020701c21b40185030049c80c2044c941001c0c2d919002e0700d03030603441801e01220b030304c0c4851780e0201100c0c02440c1c054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 31678431 1250 31677181 31677203
    0x30102160f020406050a0906081e0c010305040203030412150606080402030712110a0602010c031a010c08030a02070c080f0c03191103101104030c0e070c031809051302100201050103 79
    0x2032222508504103800c202d0b8040d454080010341546c505c07103000040c1010140010300246002000c070300d02401d241c59046080103003820b5008007000807500601c01c071420b0802149035076032840001d080d489250010102c50600040990500c085c0c0760340825940324005040018940701c0100b911f00c40c400f01e034000d61641c000c09007404210b80b05107010001e244034000070318400486e80001003401c49550840d00040c1c0d5200e0389182003583c940100e4a42066100b608140b607020003000a21240500601822031940000412601031084e4101d41c0096000140c802801d52035000305901d80300b044034407070018803500d000c4006510740400d03001c031010344856810315000d2495860352400781405507429814007510f04003204d1030b802401046104007040e6041580d0300c0c11880c085404990f03070340040c201c02200a040004003600a25031000040d05400e200820318a1010702801203036450f000b8011440c00e11040c0440f00319141a040c0a191007280d4039010300c071004804a080f2002484043c05441c051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 31679681 1250 31678431 31678433
    0x24040b090f0a030c150c061406031b010203030c16050d050306090a060803070f0203010f1401050109080a05030306010e21060417090d03030b0d063e03010501050a0302040315090501050603010216 85
    0x6080c0c0a280321659040002d07020303109840d1f0604590394545500d0015011a042203a00c0c60207024040c0c0b121030401c14800319241040000b988d90200805464480e0000100156080c0d410302d44106101d41c844111190141a00002019a00709603810350180300206c02040c404100740c09048180d401001c01542800301d15290001c034008084016038240d5614003c07201140441e01541e43c5078042e9640c40740d07095250500042c44400c0326440411a81c20150419000920210440c3c0c0c0040092038030400c00030985000510034041d403070036061514500c070580a034220b4041802132207240945003901c89150b0040054400d03115400b07425920607a8811500f00081c0264404480044040c0c001c0b00704010b07a80d2510106e6004040c0384503440f220313018160008581d202035000e400505513000e2525202503040d40c40d90300042c010a410f000ccc002c5099040c55110780d051750029078100000c10205140150344ea8000c1c460103001342c816500300300003d0610f013014000c8a0002c1030102c020b50204181e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 31680931 1250 31679681 31679699
    0xc17071226060d0209040b04020f01050c06040b0603070e040506011511101116050303091b0a030305030702150f060a050f0105040306020304050a050102030c030a050f010b070224040b090f0a030c 85
    0x600b8030303610103152412000941ca9103001140b040b0310504100d1a141841d0040049884004110074104441045144510200454103541250307010350a9581601c5840009040c08010742210018030403040800c418001d0001d1034074101c600c8040b001e01c0040d1081c108a40c8201030300b1005800d644031000c002e00601e801d03031040003000c850202c85820900036184d1801d010f480c010040d03c5a40c404014448124001d0203010100e1440d00c080046200006011484a24040c40050305210011000583e094024005484840c51505100c80d543c5400c50030100b0044013035600b54090360354130001081071f043c035580c2480c007001e05841d2141040d1440d80e440001e0343c401041165240107401c48103001410900181d40035048140240351a850081c1c03043d0f003250002080c4000f120a52001000311180300c0341120075164050f114031800d9070103010f140c5e40503140d9001510842400003000a07402110034053b1440b59000c68101001c160010104600d0412500029080c190804400c220f0000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 31682181 1250 31680931 31681007
    0xb040312110f0a02070906050306040b09010b0d12110a24090f0f140303060a180b1002030a200607210c080f01052409010c170712 57
    0x14211201041c010300d03941103407009070020607110110410110f42246041d805028280207082090f0b401c0145616010000e941c0c5c20340540003030120721110010604102e001c0d0801c40700b580c0007400301d0352000124a8146140c541512100c3c0008400c40030f95400310340d0100d5403100302e0360451810508034400e040f034801081200380200104c107945000e0b01d030010309a10b419103000d80c00794840e50424503440c18404008041ca08501c0165001001003141595448440005132501480388040141a0765841001802c0a01d412030f0b02980d881c00f010b030001d60001c010803c0440a90302c82c103010807850750030068851070080030720050300440005042070744507690040c140420000d161041c03a892074040c10480d101f00c0410030000c1d01e0b01c030070001e40c80130040415005040035030b0701c41c42c0700401d001010f20b00010140146c10b554030009156015a100d000f10225140d0410811400c40c0c014a840c12419071000c001250600060901c1b0b000c1c05004800c480b2007401c1c111030908002441c5641d90003040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 31683431 1250 31682181 31682207
    0x906041b0509090102030906010f03080409020702040e01051017010b09061009150903030f050903030904090602090301140411030a02060409090c0f06020a11060a0c110a08190b060603040b0403 84
    0x1400030009020740e20180b40070301403142100010707a03c0c20500702e1641055016004441920502c0800b04002180c5808580403102680b50060701c0d81d07001e01c0000c019000038860506590300381400d0000b41c600049a001c211400828920f102c21042c81e0401d00747d0342e4004081e684420a031001803003030304060000c034580b00460303c1e04145503500e40c8501d041c0940c0d503440241c0020031146040c42050b4204001404c0d22215040090401011900017550703482001e80b058011070f21020258200042ca4040e1050b100e030050080c004c1d0031030000a05c041100841d0140c480032032075894202982404140c061b48070350041c100e1441c0c18107143c502c00141c040704c1400c50f2480409140060700c0ca8a003450103001d00490b5018022400e11424007210750303610300d01054440e607810409005016004200441c825a015400100410036440040c608810f140c1c040315281c091601c80007a05540b41501c01d0100d8403c5940c04010b8440c2020701c00e940c001164000d103910002801700b000306c5d01500f5205029 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 31684681 1250 31683431 31683473
    0xa02090406080c010e040510050f130204060f02070b030c042138060307050105030907090c05040501120b0307060f05040306020a050c0601080105010303050304020906040e0706110d08061003020f040308120f01060503090604 97
    0x19039800bc0c80201c1c3d0107175001c0400121000300059078194140030180050406017540c0b400c60400c00401c4880f84180e20501c80c809441c5040c0044002e41c1d82c2601d450395410501c004003038a903010f44043d041c1900c81d02c5025410407206416005031101d00081e01400000c0c004000c6a07007840c00545903a40090007c8003284142d00f0300141780c84483c014000d00305160f6990a07103da02d000009400340c500700e03c000d600ea900b02141c0024a4a0000380042111810b00d00101c2008180070150346c030303202e940c001400450001424054040d0000003c100d60003001003160710903aa034041c1182201d00a000040001d03004101281c0507107071808802d0b07041280100001078074030940c001a4030b090f490798090004220100e0103181e6001c010311180c5a4120241040010b40c80c00a00060a4190582d5010f051540c082a012616950309041c4c4001d554070a04999442940004e07152071035104845064042444100200d41a88180709403409461803000030080c9072503a658007403203101c400c44051f0325 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 31685931 1250 31684681 31684699
    0x1003240810110f03160807021504080a03021b07031103120d0504080913050919170c070b0f0408060a2901020c1804020901060c0f06050a02090406080c010e040510050f 73
    0x501002e0320095000384403280d005117000e025468054000d00d07004049070195000740b000b492400c0d0240c0c1c1202d500642c0a84c1030760717030f0700c0c400c2109400038010ba00c54428074034419001c000d11140c00188220540e07018840e000f1300050700314105680c1d8490380d01c5e0010848401d0042c2e0205000c0d94000da5003082c8a54074890420b4405408541c0c001c0c603681080d035180751510280401921b09000d412005114039007484505981030321513019000e00159010040c19001601d00a903d10501400e8040c05e0108140e0380d44001c40d2540c5071007908a03000f1032529000c2c8201040782403034148501240705442262907540e44a282d005500405800c40b5160b0550140c484800d5160707450940001005021880f1040203042ca40188818250160460424080883c40f818041600c02d0540d071074165018501081d19075a0f1510100a8000c0450384e6400c1801c0c10070201f144d42000c03d01e64079007002a640c3d01185480343e0301300016148240c0d0150505094284107000c641007144010a00c03010180030041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 31687181 1250 31685931 31685947
    0x6030103080d09061e0b120c0d020603040c0312080708010e010e041101030b04060f03060b0409020603160e0a03080a0e030607230403021e010801080a200d02100324081011 75
    0x204208103851174440b07884d83e480d6446010703d070045003000a0000e580c01800c0790910311004c42d490300002d01c1d01034490b0304044001400c00c0190700c4030002031a48801603d1040c0b81040001d440d4120a40d203107004141034074004500e144103420094101c5250981101c115100e9480e8203440c4491646c06074109602c928140646888034010b040c000c200130074a407404245107091000444890110040c0b1440c1444101b0025070f0b2950150b0350405207160f0716070f8604950100641e002d000207a10244c11011580c03000040c00300c0c45000d04146c1c5240d403118a4416075000030152205011144480420602d10801f900009110080e08042c0c4004804520703003a00c0390002a4800141c5a0800c0d80c110328110152040d40c1c40380165004142e0388008001c1002944c0d1802418804180c00003096038070300da00104143c0d0b0300707030000310901d13005440342c100d50f4102003006020b4051003440e038071074a020710301e480214003028210000315039400c8040e240c011032608994029065001301c41c024880240b018a03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 31688431 1250 31687181 31687211
    0x209040501090501060f08012403020928020a030506010c051518070b0703030c0207060903020402090604170f0d090303230f0d05100504090f0605070210061403060606030103080d0906 80
    0x1002030041e00c15040a81c0c0c0c506000d2a01359049e8007080f00d00b001d131400d1445c4c24428502c01c010140d80d812106070840e03548aa00701c0c00ca0f0440c1d100c80c03924003a005d5007141c03048501c41e401448003084640d4140410750700c9070015901c0700c101c200d004010f5441260324044564403605110381104c02c42011201348143c8001e02841c0102c04e8102800102000894004240c1c062081d0b20300b0200302d001501c4601e14212000c0c00401207844042d009030380000703420440343d0b0303000120340c050702c52201c03100c04130140d040390140e5490629411080034803070003c1c1c10342d200740600341e40001c4a81c1552080248488503022181e4030800d44543c1c0e1610380e041c4066241007200c3c1004d004405c80c4640c3c00180e40c40d1520008c070080450780e115038003840c684000b03080801d00300386542c8400750300140040b40946842008038684141611100c0030545031010118030110005005c0c500e800b0110119000f0b6101d210411001d0b10080c40f000b1b0440d01d08004e85143c0c0c0f27805801c5030560070f0162800042405982d2504 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 31689681 1250 31688431 31688441
    0x60a050609120c0a1e08010b030601031101020106050603070c12020c060f1e07082d0403030c0c0b0c010b0a05060c0723040f05061906020309040906180302010203010608090a050a0209040501090501 86
    0x1d0500304800d0440403100c81d0b91045e40000408400d4000c2c001040111301003925510306000c003403c10321400c2c3c450001d6174001d421580007020090952a80c0e841c12201c000e11400c07405008843c0c0c440c6d651010050300e8400180d92b50b00083c01801d00f40341084c804840c41030f581c0f01c446008040103254409030310309400c000c05803181c075004901280d030329006c44558241a80890840121001009038242039400c0b40c001942d041d40c1e4142044522280903040c16031042c891039014541e6003100144420300d0201c103401c07003007580c4000e503040034810742c8443c2004903a004000e286140c0e071348a071200b00001c1c80748000314800c3c1b00f4064003d4024040d41004078096507415a0155256a00c0d03d083c4602030804140965082c4480c00c0c5e1a1500c07414000006c0d1a4402c4c600801d200765100e401203000c0c0078a07580850090560790107000030b072041502d4003a0103500244903000100c0c4078440011100440412000022a03108001e40b4000100d0350070000413540c045c0050b2559907988144800045d02480742e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 31690931 1250 31689681 31689689
    0x206010b2b090c0e011d091005040602040f140609060703090815060114120103060c0504090e0c03070e010b030105010c0609050105131401020705060f060301090f0f02010305060a050609120c0a 84
    0x40441c5050460500042d841e66582c40700e1500e413402001042001900010b060034160500f407903041e0340d124000502e02d040880030108020514003414003013040051760040c421507483c00d1072620740d01c2d03441a400504088001d107294124008104602e0149085401061114400d0420062950b21454018544a00c0c203440079081303164141440300641e0800444100b00748407820041c58004c481001d0560260184030080010f5160703c44244a1030086d401d4401070031907901d0402000004242c00303503039100341d40d0015000b401140d901003030000c80340c80000e040c0c03402c0d0094180713141d1821004491415122500b40c071559030324200e06d00024030a0141701d009070038202c07210006110703e04080b10305008142003000740d0b038410045900052030115000780e10100e0411000100d607a0000441e001d4154620001c0000c85c021000c1800c2008140e80048400e000380d80820180d6140c6050001b403080f07238000c00794820020303c5940468905007440509060015040d40d840c1d40400f00800e00210103500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 31692181 1250 31690931 31691017
    0x4060204081501080c090714070803040b06030c0d0b040201030603060204141305090c191a0c0105070302090a1e09020406020c0102010b0a030c0b0f0f0d020a1e0206010b 74
    0x9810400c490007042841c2e90140300a041940c0c5500d04103c0c90342e0b41403111031031800350100d440001c44241c0140a10020ba414181c0d0359a6140103900d021044e55204940440c0d9040e1980d000c9a003600380055181d4048802a140d10007058944d1521a81d1040080040781090b884a5000c80001c0441c0050001040e18498a00000b02e0742c204001c0d440c00c1d041d5680035440d1410302007001d101030002c1c0380d958880058039540030440000391300c4040c142064001908843d60045100d90300004d01c0000c3c0300c007010a40003000300751102a4220705074480c0701c402582c011038002041c0000c14030007003c1c6655108000005074440d13629141c4d00c4c26a00988e11903030140e04040301c8138600796028010704200f24811a5620001400c2d50758050034034019020712401c002d0003107018a00250030500320780000210314030a03921007403554034807000303540300707400c0d51000429810000c081c145004518440310340305078001e800141c0c00d0120f0300c08550000078120800c2d000b640c200301c100d20705111004e030220510075 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 31693431 1250 31692181 31692187
    0x80a0e011112090105040b06060702010203070602030709060207080f070312030f09030336030e0d060204080c130516051303020a030506010303030b03030a050703080c120f04060e0706050d0b1503040602 88
    0x41220000000f06651180d0f41020208400940503580007a88840100d540507241c1c880740c00100c0c0303180107124000780b8062000080c0982590000c03c520100d424580c01c488015031076400031502c3c4d4003608a401c03040d901c582001e00005a88030b401c41824071803490002503d8849188110555800480c10781c0403d6a9000c1c500d42d030340d45050849504003d4100d942916002c02c404d41440c0c9001607805410000d8216a0b901d0b6551090000451a904070005548454a170070340c96031100c4e81114028883c0c10000500510140c440c0280c0b03110300690300403508900e0758400c0c01e0b034460348003140b004d441c00c03088a404001071382c2c3e40f65903102542c0910010213041d0304502c0e010b0204d9442c5134100c0c1c032940c414400000da059000c411190000d40c14901240c40381c0b01c0010303020990066000e10904c10401500f0450b200d0300740a58240304600940b07060019001d51644c958641c0154001ca40024404120b5006401c007980c005076005039011704000c0880d202405000d0040c1c00550b400c5410030b07000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 31694681 1250 31693431 31693447
    0x10602070510090b03041b080615150315060417061009020403050d050706090b04050102122415071b15020606010503070305040f0506070203090103050a050405030a080a0e0111 77
    0x420500020700002d03203511003800c9000340050a01066445015014080080014100071110780b0350702000800c0034403006802c1d11802400e0300c449007110052075280c00e00301a81010310340800b20052181280c0f0b1650f01e9504d40f41e180b0500001c218008540100b0304100004011425022622060405a0280101d81403003160a03040c400f07507500c078082260045c00184081740010904c10708440141c1880780c0d8030002071824401811019002400c0d490000007040140407040d002401c2c0e00c060350f0702c014070703d5591007034003440341d803a4500c2000d051904000e286d9950030058a11380b2440c14409060341050041c0d81c1e060425014000a04900803142c50200080003503c260000d078045540040c01d0107243c00f04c0000c000d400014100c50400d501e910106081c444242c030034100e0f007a00328041d6007840c6001711006c0e54942c001d68809000903d040300080c01ca51861180074003455200026601c0c02004035402c41d60218041d190b650144d583d032440700d0305100d0074421300c0040000c1c100c10700e442d1246 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 31695931 1250 31694681 31694683
    0x1413030201090806071403090708070617070c050c040b030a02060703030b0a080a03080c0a05390102030c03040201050c07090606080106030e010b0102070303120603020a030804080115031104020a030e03070605010602 94
    0x307a511191aa501820601c45e026402c44010781c1e40c0c2090316441902c0ba078511170707031a10701800c59000706018004c42c3d0340443c1c519803280b2901d034440d0590b898034000751100c00085540c400c070100d000c1e046410000404c01d6a18240d0020742d80c48400a04983c2c001d52540c0001c0c84640c8480c070218007195075002460103030300305092440001c00084024200518068401070a0301800526580c0d042200048011140e0300510a507501c00c169400124003015000a02e0040c442000c0c000315002c4a1020900c698150140211b0b4441c030311141e01a81562620b500548003500048003000003409206008a080c400d10711944000f170a1035035400c98654903205000e42201c4103490244c100342d04100d543d52543e40c000a4a0381103da1501d040c2d104880340c00443c10041100381c000a50110850600005100008014105881c0d0513402000b8000b4907007c40b103c43c84091100034042d003600d002c032240a1030654082c00362140c45050201c0c06440d495140e50950340602d0013291030940d104014410180c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 31697181 1250 31695931 31695947
    0x1c0308010503060f150a0b1c0f0603020105090f040e03030f040b0a090506061003021b06010f0803071211010626010b0a06051218061003050105060405070c0209071413030201 76
    0x4040c0c018003484d0400c00d00d000c04a580082100884040e80190a10181c80300d21000d0000e00c00c280b01107464209165107182100d01e03040c00e508407141860803001119003144510301c1100c1e4161122072924592009010640801c604010b038071943da803c140c04621401d00c01184144030400a541075464149082c610101c406000c2101c058548244000080d4000801680001c8200c2d00c4954038402034904401034402d0b10072000c01300080020380494a840002c28034148c0f140c0c280c80701107040d1103080195070b07405020409091507a1000c807080b00c1601036899005017401e008001724000f034a50340304041c007844802c0503110003076180941c0c500e400d401b80700340004035200b2207020001600d01700c0000d0072401007210095205003000e02041540c8071f410509091007000e0001d50b106ca1818401041e125980e03880160b840e54203080002d40b20303190074890584140d9058840034006030b0150244281c4180c002c010205025002caa003680d00c0d03d4a0024000c2400c10100d40b441e45410b600c00141154 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 31698431 1250 31697181 31697189
    0x460606021f02040f03030503130c0f0e01090504050706180510121d1b040e0a0308060901060810030311010e070306020c1209060909060109030c0605130e0403020c010f05091c030801 79
    0x244180000e0118014204207041241c6d0941b401c2c0c0d4898481e2003d24440e0400050014440d02c1042c0c800202c0050080e001812500d24039030b444500d03030740c84c048201601c02c1128010400d8100c03100601c452400382c2c11400c9a00c00100e8003200040d1070302c01050600c03820b00d0712070000c00c1c1811640025180b01e4010b07808030403040b01d81400c422002010340d46d5a41010040074aa4500d80075901095848070b900c003043c00308000c01100c108a0b168200034010714000e6800a0080107440d00115605000304801070040024400b0301250b180340d03481c11100c3d250b2408820242c1e5484031101135010508003c4503000d54092040103a40f15040c0103560b1030a00118413000c40e1803c00c1c850110350340d58a41c2640c41000055501481556a07213004030385840460b0802004191110400300d01d11b07038400e0290020603684030180c0545900c2c1d4040c01075414041710010700591182c0c1b050040d5503c200038410303000034a030030598200059080000c44070200c072904103203001038400c44d41c4241540107403003034014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 31699681 1250 31698431 31698493
    0x40305042c1503060106050a12020d02030106020609030403030c0b0408040b0307020106260a0807050c0a080d03060504090b04030c150e01020702041116080c0c120109050646060602 79
    0x803202d88004a520b03400144506428400c1c00708424884500030110002c008403082d03070441d0754503a841c681e10000d41080c062000148100c0d4001002d0781c1001040b501034a826848a000c0c1808039541c04040c204000e00444518105000009064060102950149203660004110f40c1c1c1070511684030640408081c00c1d550f410144522500035010400c3c0e031a6907000560f00e6910600c50400900c0c0c0071682d0361003a0441c2420304002941039020482103c03600c803a5605204040c0e4540c01c007c15119090800380c000501e50022900181c0900c03450300e004c0d441180744c5c00030890f003100d046c1c0c102c42048a440e203059400142080441c51304c1c1c03041540100441d80309900b85080d0f41200b2002c40c1148400500c003070b01c00030705c44030604070411441e424254020650351503400d0302911540070b0300030440304680b5841910046002c0d00b00c45400b20184081d64804a840d42e03030508014034008446824141c3d002c4040304030001b565285008030000350000350000c2c80789404003014a41c0c40c4009031002044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 31700931 1250 31699681 31699711
    0x20604020f0a060504090515060703021e0307081207030603050f03070605091203011a07060203010609090b0901051e0d02030a050313060318080304020301021201230105090a030605040305042c 84
    0x40b0351382042c2640c0c191424540c000807c1d5071080340398100a030050f04207940c0b01c440450074004055002400442c001441e9007004404000d00454554a00900034020704c2940c0500010340d890f04619040f039442202483c0200e070b4140c0c0c98440f941060a00f004804864100203686c8040c407001e4001c007074000c03240c540103108a015600e4412000d00040c0600c02000d00c8000e101122100c11708240d591440d0400c10071503503941d680c0c001400c441c01903ca508a11030412400290a1a2240034a412100050300c1748000c101125031300e403480d0994101c1643d000c00d42c810300d0310150300c0800091340072522a034000c564540403660854420f0003c0d0307001c10f040500708403505100c0d00782510030b8200d2642c82a4090740f6074079680b00007800780c0201c15401204070107200001a00c501245e285c40d21800d20508800f2542e240440111010310030303252201e1b048400e80504000003240c1ea404194854001d2510341d06140c0c64103107807108a015001d441a81800c00802c240300150350f100700b00e410011029141c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 31702181 1250 31700931 31700939
    0x1404030b010302010e030a0804080a020a050d050a020103050c0706020f03041a100302130204050603100f1409010509070207080f010203010501021c08070815060408010207110a03170d020f0a020604020f0a 89
    0x111040c0c0c140802810001440c440e0002518100210044550300400e50ba0b11581c48801c0b071648e640440c41c06034810910b405d40003c035814440803038000c90760030801600c00142d482d00194050300010f4544034081d60200014000705000b4409019900c5c2d034448407550380d080c02c3c2848a007005100544050030901002401902000d060030082181d0303050300c07812a08404207166400902842e8825038001c403000041040d18014100c5240682c0d07900900707607144a031a4071105080000c003100d0144c018080d48010322032031905001041c0c1c40b111610449142a40718402c8030308028000c2c4c498031590f034010005101d5503806001101c0c40ea201c00490307198030b5000c4500240151000ba009500303200e211808140009604440003a5030000a0000e81c1c1d10340c1e840213158000d60044805490742d684058010b00c09140040d0414203c80c0c201c1100d04206845c02c089400951046065004181d803c0041d00000030b88800079001e4017105030042d04081c17419005101d0815880400d81d0710540d14003070188 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 31703431 1250 31702181 31702193
    0x40f0f0906080304150507120c0209010e1603020706060503070b040f05030607270e0106050a020105090a050d0f030b090c030601030f090c140607170c0709110301050607020607060c020d140403 84
    0x1034210352580c44080341d005c6000c802a0b50030b1140140181c066199069028610780e0082c1c0c0e03521080d40300b030700c190110782e9032a0841246248280c0b00040c60a6481d00c0c043c155600c00c0e0040c0c11024029100051086c0d6038200003490003120764001c0c01041400320301005108158425800102019009001d4910380424010302c00750ba11140c00c68488020680c40131106e900b15981d6024001c1500b611121b56114040a40180c02200c42c082c015030805000410700640804c2a141e60781e4030a0040c940e16003010b0b026190401075240c1d15003010ba64251808545e5508070f51140036490198030b4541d04d041503400101501c7d58202c20b03550160611b10b83d00300040d83d03005020100d840c440b03068080e90302c60342d00103101c80c42101c5026281e4a41c50b82c00e02e400d039900d03074003e01c001cec1001012280c80d00c0d036880b9040700342c0d2515683c10b094000280010815410030b80c0003088154402017015107000d0180d507410007110f01c8019075100682c0203140c2c00c2c60f515001140c880d6058500300a487c2031519580d155 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 31704681 1250 31703431 31703437
    0x61302040308030402151b030d060609140904030216060f030605041a0405190f02030a0c0908070308130902130305010f060509131e11010e0603090c010320040f0f09060803 75
    0x20b00400d041d4400d11b18204840007134a49000090403510388070110108030958a420200d505a002c42c6032440c001101d0740646495400c4a00002ca0500130009120030044018002842a010340c02844164441c08285403d594003510301600c40a520b000e15400090858410b504454000d924040c1200340d80700d0010380e80b00b102c2c3c1c0e08131070200d03003aa1a80003a0060340392018100751124201110883d41516540165200708003601081100034048101181c409030140b0a0710702c107401c100000c0c0080b501c050000c06004c02500c0400618540e200411001c0360700100209490384440b05c000d1041040c20b00468880c0c0c001c0003411300841c2c0c10180003030a07588000d4426035110810f95500760030014400c01d01c40a001d480c0b4854416140c0c0c9080480c601036146280c1800070f0141320035403030f031807602009890103083d11000910000c40e56a005400512030450040c00d801d10f42c00d041c000f40d44a12005001410041c4d0107400c2880c90201c0c0801d0721440d5810500c7c440c0d04051b02804200e00010603 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 31705931 1250 31704681 31704683
    0x1c020a0309090216232a0d0206030703020c0111040303210b150d06030b0c0403050705010212090405091501090f05060d1109100905100e0907050a06110717060613020403080304 77
    0x106201300808040381c025075074070000c0d8403500e000300d440301d407881140346c0c0804c0d01042c0079031810b078802c10400781000381c80010380000030f41c0560180702041e03502d40700b175020b0701c0381e410b440d40000340c071054404024003203400a038030880004001c8180061140d003105004141260700c141c080c0446600e107000a100304484603450110000f01041c108409030320b6400c50801181c001508440c642024102110300c1d0b403103800203542c03a11520304009600e510001d01198071000101020b400c14501c2010003000d0305002e81402c80e64030480c00e604140c40c0448010b28001c03c50040001400303040304402d80b00703403200102141d00c00c180c00c944040119060081d03200c0c5160088806a000350303140014026001c030146c118821452030002000a80c200e040912011340342541c03c0181c041d9104190769039200701e01d010707068201110000401c0310758002d40e0040904481501510001038030381300811100b6594681d02c100d03580c0103009012a5080c90414104039600c03c09040d071506040d500d440000380700144c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 31707181 1250 31705931 31705943
    0x201020c030609070909060209060f07140c150d0902090f1008030f030114060706060b071e0c060e0102010b030f061608040b06010e01120203070201150f03031b051c020a0309090216 79
    0x6c807401c20440c0642c119150360800900d0a81c0310800708644265a82040c003007114214407100100c90601c00c009122580312100511002c0c0802039141000c009800060701500a1a101e08502006a0300d06c060345210308048804640c0c189002c1d80307001400002c0d580851144d0300b040241d00003907845941280e040d14450400810101104000b003003842c4900500903050900d006800b02e40c8802ca60000d2010300d000b0080c48040750882110460001180c0300b00030103104080800b00965405422684002c100500002035036080701c4001c203080540b003a480c499103421080401203078504002065511007110f00c4d00c50854501b40c2d480d02503206d006450b0034184181c804d800d00e11a0f01c00ca1070b00e0308817880300e0790275512410a001c0103400303801d40520700364501c03550800200d90b05800e141c81404403038040d030714040c14483c00807040e408000e40d00c200351000e00400800b11529002d00340c61000841161b8010001e41a0300e003001042c170307600382d008000454010032080c51042c00007113003243c0f6250865 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 31708431 1250 31707181 31707191
    0x20409210c0812090f0703030c030f0305130219171006090207030503130503040b07050c100f050d0506060f042303010501053001050a020703030644010906090201020c0306090709 78
    0xc14064178107055205008118071484038044201680240c1703002245119071145a0000d1400b4416010365070112440b400c035015918000c0c2c0503142108c203000d5103125415101c0740072500e031485021941b6400a2000d0140c0c0a141c00350420078051040c2401404007070411400e00d541030f62b005015100c050421009849810240780070b000301881180d008051740c514160752028140781c129100c1c1101d9480c0d51141407201d0313400140364000c0c000031013480c483e691550301d80601c810140c1c00500001d005103070005020301070210144401070081006e008a840c00484072038002d16028101417250f070f045402a4100801080a904e50442e242c10441c0ea58080342c0700400344070340580410366112810401503003050f05100e401f00c025401080c900340280e41c180486030f1104100301290104808890307662002d04021568146550000c0c04913442082c0c0000b50b1100d001080703829545400c0054810741d64920a0b43c0c215038040007828100001034028141a2602c9100c66498003440d00c5401d074103584034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 31709681 1250 31708431 31708441
    0x6120a02091806010f0206010b04061d10030605090a0e0a03080a090b040605060a06020a08090105090303160503030612060601021e1005040b0103060c05030907090902010c020409210c0812 82
    0x80d01a10402940605045100c10b6050301c0d2100c0d40100361401c50100f0070303400c00c0c1c14143e8800700d80c46040e0b9900d20b0b40c040c542450000704960000a00001c48442d000300b00c144149650740e01a0100601425680850391343d04180c10010b4103e00580b0030b94500e4030b00381d5014160f210100b690790885c0c0e01400c101819aa032580b1040c064000030000500001d039680402081142aa02140c00b42d40d00743c65203600303191190b1050366141d0080d0b0b009820644144009015507115a000703060300ca41c0a400d0700d060150386103040c40e01081e240005c82d141e40003c000c1100390709000240840b1010760700000e00f21418990000703074446d26841c080b0203000ca080e07032410540410801c20620042c0d0482020001894107003000c0744840400e010072070b2543d040c420302501180c80342d020389002d4a8003030050403515142503a600c000b0f00d0b80d03040c103c0c140520080e1941c0036a407644103001106004056403401014101c0b42d16a2001c294100c1d08180041100f145001c503a001e01925903180265680241c5a10341e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 31710931 1250 31709681 31709701
    0x519030f02040e090105040c0605070803060409050705061801030b01090b12061c050c1201050609010e04020d0804060f0f050307020703021207090e0a121707030504060e010f0b0f030703020612 84
    0x550780009221503020343c1071104600056102c288076a010300c0c00d0f01b40550702c81030100c90521551001a01d4120f050000c5481e5140550007440c002c0e1241c002c0310802d51361040882c1d8503800258642035650175004100405507058020a2045002441c1031640b960a020b0a01161300032600c03400031002c80400007030b0442e240c000300a029074401101c02d201c1e880d52450416565030800401174001e228100540000c40014018130b8000d10300249000081da00f080092280e40200800c00d980c410b1110702040e0200781108018405000f050b80c94180b05106408060140201c0300c01c854200a010030422100d5540400c020b402c0e26412541c440452181119041c5002000d800c1220f01b03500d000c50a02e441c1078002001d005083c450340311814400503040054400105c1d108807456a6511100001c043d14400d42c86141e016100d0700b00040e0301c40f1810203150171110140c02d0f080381c00d542d41210a4440c6082490b485601e075088004100075815607011803054003440c2004642403006401140400708 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 31712181 1250 31710931 31710937
    0x30e010e010e03040f0f080303040b13060203150108090706020601090b010509030f01020417030c100c120c0504051201020405030a030302070c120b04060615020a020f04060b0c011b0519030f02 84
    0x3140001d00601038401901d645030b9016124070021464401d0000542001420030241200e0120380170310704507a40ca4607020001c5000031321107080b4185c102e00710b000140b030b544041c0d40030704555205500c20038000d03030016001c400c015200c2c4501d80c0c00075030100106030380090703218150380c0070500c08942d0303400180041c0ca45010740c04c059030b490701419400130002c0005502400071035003c1080603020112044e101c131740368411204420825003207005206c03040000341c0c0000782c4110b000d181c0304000b00821a42c450444200344407140000e01e0004e020012031401c80d0b035030b1041c2c84101008500e00303880e1200213a6242e9981800a09143e000b0500324180f080c0403440c3c000528204500c0620452070346072104100c0411101151202e1501501181000c00c44207400300d6400903400818002d50650204003c0b0354280444a80c4203445080206503140356a001e0f01148040303a001043c030100402000340c02c0b03a01030f001324003000b2050040280610783d25000200708c055500340010800b01400da4580644 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 31713431 1250 31712181 31712201
    0x1107151a03100e2118280503010c05211305070605030412300605100305040b060d050d0f03020409061508010806010f0302060306030309150d0606090e010303030e01 72
    0x100507014000803031906904002c410541030020703a0b0b06a40600d500006a80f200002d82107601428444440282030341c91800290303030402006c120310b008050981082d00307030107002104041d40c2d440008104a0a0900844400c46000d060103400c0290014008100140c41e1300d07400881c01218021400302d030104a507101242d508001502c103901d4a615001e8516481540e045449e10380340821901040e10035800d00380c004801003450103101e0742801700b1040c50b480c81181210300507074070314000802d0b94819149403044401c903203022a035481e26081c01601e03840000c0606000d00380c07002e00e0500141010403c101494140c2c10541d15a15a40710124024000d94001007401890402d000c9207400044655803071030780107a500c03000140c2c2c841c112562030b10028410108a80031402d001c0c001850100d02540e030140c0c001e421642084403104c0081d00c1a035200f280143c8803280018903a0489800d80545005090f240c10500403461400c80c11390b01e40d080511010b4105582d03035000c106014002e400040c400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 31714681 1250 31713431 31713433
    0x30b031f020f1912020a2c040e0a030806030c18070302040e010f0e15030607051b0d0306030c06030c0f11011b030203180106210318090903031107151a03 67
    0x420200c03c2d01000c10010402071070128103058500c0d512111680200c0b0044040d607915a1041c1800d0756800c004034048194545400d481034100d80e07141d40340c80c814403035401d034a5801807000982504002e0b108502c040c0080b80207402c1140b000c01903488000740302024078101451400d02d036440101c110024041e0f03030492607414008000016070548400c002c20103035070b01c0e4018022192542001d40016000c1440e040c1c0d0150048400034141d54000d40c00340540944140181c2c0c4040003c841d224144440000c0b00c10100e40c1c1c405d41070060000b07030081d00d40a0001070030104050046003101500800f0001d40601c00c202c44925110740100c02900201e081d5010b01d040c5e2100d481c45141c01602a401c202d0340f04642c00511414551240c1050003240e080321451400c940254114031a480c5010380904019414000c10310074035a01040c035110380100030b02818800080418062030f0080651b02605405581800140520b00105552442a24500f100d500000805428082c0c0c160f03d16819408282c2e81 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 31715931 1250 31714681 31714687
    0x316090b0c0703020405060415140d080f0a02012304110d0b0a09030f092d0e01060302090117010605030a0906060803070f060b010c0302031804090c08030d0c030b031f020f 75
    0xa20710000340c50301540d00c01c40703041c03100d81e13a1035081c4411030740e15043e8000d003803018510400900c10000d003461100000a807079841801c1c015182c1d56806d41c400a0900003400c400991808030590a101f032404010554140070125001c1e000c0d544002e075030103040070300100d81002c07210390182c1d11421070304049035114a01322000c0c40c111840360005c4c1844c18094001c0368500308000802c91042c41c0d90815501c11400540e10401921071408404091f4080c9100010031b511020840c102c5001405000300815680907036208a07101c001803080c10581c1e814086c10030680014826540c1020a81740d1001c0342d0000002c900e8564102040a0041c03070740f101c420342c040001e075801070207010f00303194080310b0080304184040b0f5880e000440b04d0203024140500181c00501400c4003d401d44450041c140800600c041444c03000c6441c0d09501754015840980e80350320010315050410502d0040b90190b4050f4141088030310400b0f400f103900d030341c00101c140080e64400410000b0328140d540c1a561003103148815161 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 31717181 1250 31715931 31715947
    0x406030f0c050604080a0b0901090501050f01080f06011802130504020d091110020c010f0c120302071209080309060f040f030b18010e0705041d0604050304060e04110316090b 76
    0x2540032500402500c100980210110309800c2a008903000c645501c1d008101101035a05d68201c05940548403001554942500310b022031001d000d03d5001c0c1e00d051581402ca5407601145a290145000083c0c0c91a04070400402c403022001028075500202c5c510056502c03420342c400180413800a42240b5440351001c03071524904032883d0b00500c0081d10810001060a00681c20410441010214000160301100001c0f400703502c00d4020003400200303418002140c11883c1d84103130b425407203140c21200090307000c20340c501801940800a40f62940506204140c141882d1045031240b04901d00a4000d0f08006030300c400c020108400c8500520005900c001915164548294128410b440c101c400c1440d400461000300f106118610440d02c010008045c003500e410148009840203404030300c01211441d5680791030000610089100c2c5115002440e601c9080810140c042004160303418001e0f403501c03070368603550340700b00c0202d070380060044e808404501100c0320200c5003203070301c1d411020188a01040810b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 31718431 1250 31717181 31717193
    0x30c010f0b010e03060c0f07050a06060b120a053c09011401080601120b04020d02090a06090509030909010b0c010b060a020c010e0f0904020f01020f01021209070f080d0e0609040603 79
    0x1118003507003640c41c0d68100310755504055882c803007900c000310041020040c03000710545000c02061301a204105640390f82c08940c40d1042181c461f58070803040204d001900b110000c0702c1d881320960040f001c0c40100b0a50034001d00020b251a410440446880010b840500e031000f040015095407119081a108080c54810201c42c06000780d01359600601030481c1c000f00340c0001c04102c03941039420201c1d00e440850810348805d1140c1070027a2003643c100040400707003005038850000b1140314107007501c404500c0519000c560811180c005100b031210385c006100d008072940e07492040c070381100c0056600584450586480d42c2c010035404003155030000c00000c0c0b0040064001c14a0030390307010240c0fa0b40400e80301410520039600705c20540030740e2060032a40003c3c0180350801d9101c0c0601740600c12102604492854107003282c0c40740c4038030f01c0101804d904010100c60104132460280050060090700d051400c04800d07580c40ca200b540f98280102013081061030340758101a60030800000740f0610459a076400d0003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 31719681 1250 31718431 31718441
    0x40609091b0807080a03030b04060b0a05190e1503060f06040602060711010204210302070f090e01060803130510050c061008010c020a081903090204060b04080f0114130302030c010f 79
    0x20650307103119200c0014422901081c15021500d40f0030280019a04613a01280141840308803564003a9407034501051400c0000081c2003011400e071107250b42c1c2d961030242c0c103140103600f00d4000e041004030b5210541e26280c152001c450840300d40e1543e0f4481d19110000350802441c0100103800000200c2d00285055000410368001c04154640e40c0030f041e98401d00600740d114600401e8a403403580320001c525100910030010a182c024416120243d80710321500d104202c15600410116450b00d031b0412482c2030070310810b001060740704001c0d4900381500b0400c0080c0b040c944101403003644809203048211740550100c504c0c032080101511032074035000d8140010b0b0740603801103104a41c40c6c211310b01c41450001802c1d06843c0c0e04400309034204544101c01c10300d0240044100001c05888150a00c0140c81da8014a40a000d0907881c050319142000066480c1840c2144020b400e41c0c10818125101c103014103800360041c0c41452100d208280c035040682c91442081031850700f540c6840566031100c0115400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 31720931 1250 31719681 31719713
    0x50c07021008090c06030a14240d0209060f0102030f03090d0905030307020a090c0903060e030306040c050f0910110a06091b1d06031501120c1512050604060909 70
    0x3100031a00001c0c8401c691981c030444140b4103d900a0303074028030f50b1a10901030360303000646000100c0c0302d1a1071142080040d90549034070b100c9048440100e805a440002100c51164040c2c4501d90301207026000983e41d0007020f84541d001e044a0000c884003a40f0078800c9900ca810f828150340d40da42003d0381842d65804c0d411802e44000780c0303003990101d9540350200c00c8802c1c03150002c01b100382c250b0a11440000074291000c900007802024140000004e48900640100c614204081c5480345011024482a20304480c41d00041100412410191740c80c4841691703d0340741d0640b815480c5000b0000161b0b4921201c5115982c14825211400200522038001c0c5030b656106402c8400e02850200308407191000034024001250040c2c843c4009485904a8680d03010703000a01302d60443ca403190344070706d2100007a0800d14108030482c50712014040d0346281702c00180307030300240d552003400d10541c000c06640e22000c00c0030259803994040f481660b12500550081c00024600708200c003820704d041e5503407102c4004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 31722181 1250 31720931 31720939
    0x40203070506041202040506030c300303070c110301020f040803031006111018020d0309060f020c060a05030a060506040602030a0809060601021537180c0b0708040801050c0702 77
    0x802050310b040a1098800b243c01c50341c045a40840b003a401c22016140040c80c00e5014402d00104540340ea80d0f0005d00459400747e8441c80c0b50044c6141c004c2c00c20030392031600400d1a94000c0050100065100002d00c10051700500840490300001000070302a1060010a0b4036640340400c0201c1e050130003100840c00349a201c0000359207903a0303a40742980e40e0801d10b1034a1802e42c2044800e5001c07807169401c0142c0d6104541c4030401c007513613254001600050407404c180c1c0011092035080c00841d8205094165100c0c0600003844040d01c4003000403044d102c2e595595003080340c0071010a450840b1070f0040005460002c24240e150358071f400009682e60001c207006800166641c0102d8403861021549070f02402041e4007415425803030140d04184410041e10301501c0c81e0703a003c1107612000741880c3c0c230301410b10418280b0800344001844041501c0031019804001c4500350380b00b40001c1c16428084007107400b41c40c035060300c9103507504040000740250340c40074005500306020021181d03030703042c024a105c41c070840d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 31723431 1250 31722181 31722193
    0xa03060b03100605060f160b04050106060207140d140319120b0d050d03050402060d020a0314180c0108100902040b12011706010909020d1208040203011109060412031103040e040203 79
    0x40d414050780c60301c0c0b0986800150400203506c8600342c89005101200d0081c096070141285a9074905030320070201c0e02921181d5641c142404420b0b810f2000500030554865071058609004000480c2c200040d03100829040b041cbd1111401030405105441800b0701c0e1030a66541601d4030300c0e000d00403601414004107803503d0a0717a00b0310781d031078840310031032003640c01030000d0200c113800b10b8041d00101005081a82c0c460401d10041c403034080702c0e00090210141d550303004a90803411107000805020085c00020b5603034180301121209041c0010300710904807013481c05810307d8581c84240350209906030000e40c0d040e030000801007001c0c166034000781070004400400030070680c0e0340c00c2da02c0c01020100e01e1003d429000800100001c01c540e800c2f544000e0700007030074244040c01c0c1e030765121602c1281c80c00060124424000b000158502840f07520942503e2a15561a020030030000403080c0c8030f940507000c0d40307501411088050502c6604070010034004141165a0740743c4404001d0700307145048404a03c0380c8a04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 31724681 1250 31723431 31723453
    0xa031208011419050d02030a02060301120317130f1e030305090c060a020a0f0204110d09020301051005010c03050705070b0a02070f090c0801050f1f0e03010f05010501080c180a03060b03 81
    0x10ba515001d00d07040b4840f900c10084d00303160801c4074038001c1050981e414400c1400301c1026a80303072002140244680c0e42a01c0c040b050620b400341c4040070300700340d5800304280c82c1e0411208803000c000b1030304c482e64002c1035a0b84080041c504200c800030600c0e080750342050030072003c50815815a001c140a250f0030802c903904412440200961440350034400c00044e005666014000703042c484510701c000e40b0081000c103180c40d220440c03403800e0b080744024041c019291030040e015400c0a1140c1600300c05050784005c4400d0810002a180e46440b280003000c00100080d8502407100c140300b50341c06001006695940c1d00c0382014000c1d5940d00c90300600002448001002400192500c03c00f803c80c035168035101090ba20700400c00480390b80c01e00740c1c140c10850248003071955408100c00003403408541e890b2080c80440c000d0506003140c1484d4644654549444010b00041c2c0e000754405070f01801600d41e8640e04c0c3c24040b003804484020340c1d50581c000042240c04020030010341c10004422009a0031204080c4030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 31725931 1250 31724681 31724689
    0x30c0e0303040f0e07030902031605130b060f0f120906071205041101050901120606080106030b030111070b101508060411030f15041404060902040e03031b03060a0312080114 76
    0x8501c035035801c0c03001040d0308002c0313210450b04442d4418590b041c005010301c0c054011a04000c10306982d0180301c0800f0b038091105103811800c001c0c0c0340644210400c0a2111200810160f108503405007000c108042800d401c080056422113100108020b242020b50030604015665043d00b0b0718694082854014244254010381c03082a2142e0b0300180c03a00c200d050720000565050f031103564080c0c10007038104c840300b00c204500e02400b0010825513554809070740c5092001030864480b0a1a94826410680320a02210050081d00d0030b40350401550b001c141c840407203000400c200e541c080b43d40c800161551524240e00403003501d104d284240c805102d0143c2e603940301c100600c8101d0b2458590345020001c40c44001c402035544d0080b06000d800041c16a06090211414580c110b44c102e412907202d628071000c5003024040c00706111040780c001c2d1f0950615902401d110644042945e450740b40201c00500259999404d000c000c54002035180380e80d214100001340803102c240110007081c1180711040c0c0759424 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 31727181 1250 31725931 31725937
    0xf1302120c07030207050103110d0c0207060207080a03080415090507030b010305061e070e0303040b120420090c0f120c03060103050106140703080915010b0703020f060403080103020d061b030c0e0303 87
    0x1d0f0590141c01c41604010064009101124018450201c180024000f10800c0c0c4140e00011030545c0007411810316182e0001c0ca002c00759044008076400c5a0b5078040000d410905194200360301042404090300140808401004041d0f0003a0143c0304184001050001503580c0c14180c9005205a85666807034504000300045c1c044d05c2e0300100e41c1e41d400040c4080384100700052142034010203692900da03503880c20502d40e4010402428900740d0800a10003040400228000c004027200104444180150b000410482e002440d24007007000c002400310002040000300ea4552020b008007226500f0b207403d065405802c00c5070310b58003007880c2c00000309000c0d00404000300605100d03101c5610307001e4155030442d140b00b805001c07255507128021007a050303c449412183e001c1e04203d89240d480e8111810700a1800040260540386904a602404046a449011941581d406842c02d981c2e90b0700718039007100144010011400c0c0b802c40c1201007a20960305821140c1d51400b1660b400744d0714481c0004140d01c0784 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 31728431 1250 31727181 31727183
    0x90c05030c0322050f011a10080601050318010507030606030f05090c01050a02030c0a030503040515010e01050f060c1204090605030102040e060103151206060608070302030714090f1302120c07 84
    0x222081c00060f51a00b000c2000b9840c90070900441490f812180d920030f032910f078a4502102c41a511140044042000326192405440007220950081c00081070058500400a85403d041100020020f2101d058808017040d0421501001f00710a00d007070344005000f0003150040400090400a5208a03840c003030180a01a010f0b4801411030134a903640191007640c000c10260040d0300003489400c003500030034860f80301c00754080e4a40683e28500341c0b4040341007000c44441580302141c1762005000501e80c40340140d043d20001e1383c80a10021103200002c900380680d0f0440c0e19184262020b04202c166844050001c86203118018045642c880c401c0600380d02881c00340645845c2c049000030030700d41c802d401c95026a421140944145a00c070740982e0b444a000e95410380b400c94946a0401ca4941d000a48581c0541c651404504500701320600a051108c103501d4041c0030a4041000d514903030b03518a819084440041c64200640340203110310300650400340008500c0c1c5145800503441c0c0b600c01c01154425 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 31729681 1250 31728431 31728451
    0x10201020c0601090c140711040e15010b131e050a050307030203030906070804030b01030f02010f080403050304030c06020903010c11070909031713022d0f0310110702100504090c0503 80
    0x3d0703003000342200007400e40d082c4600401194000e590031403006180188600c42c050380c10080700d0003082060005403030004482d4030080d4030150000c1d09100580c10000c0c1500c16851070196616185040207155170a1030300000310001e18034440a11020f0754400d280d040b1903003520311140e2035581e84109a01c501482c400a5099002001501030a00d4000c008003b0148905019030070070f40c0701d4590450051090304115190703240400344105568018200300d540720b07410329010001b0300d0255401000e42c00702070401000d20a100f45007008105c03198050f030781c100002500030402001c01520060400300c4c002185461070003400320105046005001d00d04400750035441e405a2806803061b0010721700002082030303024004c03070f09031140180d5800840c0c80880070b2582e42c20348500c010300d08100c0240c1500405601c54002c08a040060742c81c04124040e800122000000c2d01c40c4000d2841d05180c032800c0f10003944115844c56044996400a02074026210b6402c010030501800b900207079550312040e41d40c6034103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 31730931 1250 31729681 31729693
    0x604051e070b090d050609070611010603120c050c190905010801020406020303010510020102190507020306091b010c140a0302031e091c060216051c0e0a0e130b15040605010201020c 79
    0x2200c5402d002003010703850150080030122241e468071410484241c4040d90303960400f40f400c00a982c0d1081002245c05a810020488185035540e040700e110703140c148443c20310400e40510028010140524488258050f0000680c3c0030b81ea50321030700880e0580a00004e90740b503d4000300301c03500148255016943c0640085d0320b541d080c001040304080c0f80320a0201159020041000300499000b500080d1000b05d031035045e225032283c030400d070400900401c030204a521041c0078240c12401e502181c008000d081c2040554079009080403802c410064081800354860110cd070010164000700070900514040520589052184001840b91103004120b543c840b80c4c04034501040350840c1400c02d159032003208014944030394203441d4540444456010f03206908124800011503c3d02005100f0403005441d0142c0b21134040381c0000c0c01c000b00750007001c01c030f400c01070000b03103017040d1101143c1500f07a002401aa01d40ca440b850084100c446d4100c541e0090b8108070001800754014001d9416045030307072001c0c0c54 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 31732181 1250 31730931 31730939
    0x1030c0e09070c02030a080d0213050907090b03060d05030c060414060c0405130204090c18090b0d08030a021e03010306060506090904061e060609030606120f03030b03010b04020c0604051e07 83
    0x307494001168285d81c0340c0100c0d08604002107090b00100880001d0741000350721402200048100c4000e60761159000b07242c41030801801c1540014000300b543c0d1201d01032602c0313440d404041040d500349a900182a4440041c494031b6020001411501c02d030b214070b05030404403100254840c0c651a040c1d902416090040c80284118500041481ca543c1403a4400506181d41e407407820080d40c0703410311441c01058481130749590502d84a0740743d901070720104406202c006860707400314110000013400a0900b900100100e0f00c5050644c0444003404056080c0d241c00c1088803610340d40c02c1d402844100e400d10700e8828006144c0c00c4c01c40c1500c2030072000901d008099aa00c1c0c5a44d4003519001844280e00340351b00c6109440c8254a200d0000a8503540c1d64804403e81140f40010844803a60041c103502d20307225034080000707000e2061800313800c2e5040c680442c2000210b80400d02411100e54000d600c180003090401e51040006000c0344601d000b501100e03244400d0010409241c80b846030380303880c01c0d0040c81d401c0c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 31733431 1250 31732181 31732187
    0x120106050a12031205010608091509030904020d0204050a030c08070e040b0c0d15060c050105100b09060c010609090f29060f010207030501020a1e0e01050702010309030302190e01030c0e0907 83
    0x541d94000d01348080d04150070003c02003211400d0b00150040b819403800c0c0841c00d242000000b801c0058810200804d0600d001410303600d008400d8054410b540018000801e03542d150160340041c4000f52000c510161a86402c0e5040c00603400f0340d424910030520300258110001c40600e004035004040c4840300d44a0300403002981d4800b0040300d0010b92519080c001003c582900e120007090b5603035030759400c14200e241081c250364000c4e0100700200e1010304188244034a0710100c5221580803110160fa0701c4080082e5800340c8010350000008034900b1a01000b44503203404110001d920500300c920311a04604945482c1c84001003101d4881013038040002c015003424101035668040500440741c442d0b5a9030750ba942685c1c0030011000002e030a841c0d000c0344030440214000880724050800c1d041c003600d4000000d00a01904c00007904264440c081310043c14065030480d40a50111000d0005100d400c3e88050004402040120f00081c5440408514036120f888541c2341d0143c0102401b040d501c54000803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 31734681 1250 31733431 31733459
    0xe0403080c090a140307060311030a15080d170c130302150f030405071a162301020c1507030b030601030204051b030403030501050901050d03080604090c0503030a0806120106050a 78
    0x642800500300000020ba6840600f43d41c001e00b0415880c1c3c4100342503809060506080e50b000303000303040c1003100c01d1291148000549a010594681c00510301c0410b0903007441418003a4000001030161401c03141c4800d60002403d01101d9480085204645400341324810342d110b001171624051348140400e0006103003049284c1d4403423305010503420071480c482040030b01e600548044034190310141007003001400413210034000100d08400d5500341034002c041c2d000056010200101050810350540d256480d191407000702c19502d5400854440008400880e510940c944d1004001d0030100001000d2510134040d0750030f081000382c00f5105907460340c1d0a00000c1c04010382040c600c4d405415414800e064107102840c400c0f0f0082c0c0d40440c403949410180846241c040c0c1100d80a0b03603001f540c1c00003185e045142141c201e0800c0d13070002500c1d00f00d070a0000a1005540000740d15010000e52010742d20b501031182401020f040703450454000c50030f0303200e90072207245200b600c0c1c01c98200c07041003107500780007451 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 31735931 1250 31734681 31734691
    0x6010309020301110f0c070504020906120a15080d2007060c0f02091006080a0b0a030f050a02091509130c1e050904030302070605071701120213022a01060e040308 71
    0xc84c1025400c080c018098001716042d5070314a00c041166162003d00300000c000400040d90110315000303041002c5006032080040040c5117025000204004032203039880202401400c040d041c107419101c0700030a0316100d114070001c0005034aa4030240c0344c0054400d040403a41420310041100d140341c590142d4000b88101001e40f044151460500050384400741514411121560110903c60401001801100000c0c103040303140d41c5044001300098a40c0000603003600d821082c402007107006440c009240c03c802160080d04404d0745000c0c0b160403504c0d41e0421440f14005c54100c207240da01d0150710b0551080c1c020014146484001c4c1c104044602840c28110050740703000c250003c10b484101103001c6140c1900c04500103940000c02a052000034441c1e190000028548800041403070700b4a03445000e010700500c400103c0303d90b4800215900c0303007014004805180d8065403141c0040140881e0b5445418110813284c8002d00050000007041c801c181c00d45660100e91156911280c40407180d4580040c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 31737181 1250 31735931 31735933
    0x10f03060e0a0b0907140315040e0f010e1207050307060b0d05010204060f0f050316081305160311010203030903030703020a09030b04060c090b0c03070609030201140708010602070b030f060103090203 87
    0x50085030122280c28542e00c01c06014001141d901c1c0444140003016a00a04070020441c0100c03841d0300c145145011250810782c0c0c50940c10382c4000c40c00005006148a50b8880c50b28400c1205500d03440c0019088a103074001c0c1c01059400395001e0801c0c03107445114418006006400c104074640000c0c0140c1c0c01000020710162091100510036901c103402c81c1d1081c1c0160000c0742d41458400e01c81544445020010b081c545032141c21418040c00c104181d201003051201807000410010303000c81c42503c2c0c4891034a400404880c00c0c1d1111002c8801000d81c2404161480110b03400a01010350000040702c0c000c081400017107145a442402c220004d41101200e00700f0041030110010100368059803190003980900b400050020b01178002a20f6540154000d10040c0c000340104202220080251540361340c108601241c070002c54070742280140041c031507103a1040b5030542803040303040d0300003c10390513078180c2e80807100415102c281c800343c180822194003800c03540074800552194842c0c1c111400c0300e031000e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 31738431 1250 31737181 31737191
    0x40e160c0b070305091006051c020102010f06090902030d0c0305030711030d0614030105071107090f0209100c140c0a03030f0309081803070906080a020118030804060309050c0a05030309010f03 84
    0x556410a141ca0550b00b02c0000303034860083c03240c0c0f40c000b400b00482e012084601080000c1c58403001c5440f1210002d041d0001994440920040d64000e40040789003682c0c040040110070b4030f40c00c00170018200e603c0c080c3e0080c490b5080c004460fa0103030100c0844c280d09900e50314196940d102084031280b0591850302c5e514081407205001d02c030114080e400c0039125400c011044901d00500b070508685009120008202c0300c1c2c142640328100100d0694160b400d0082c000c14000d00c0d8030600c4000c0d03c5000010751700825185500e00c8007590000001040d54841e401401c00e44808100c1942e03a52807032182d481d40490910320030000280100c042490341c4029003804100c54000d5102c12150b608a40b035241e03242d0700154034015046c0350a105250150000c3e0000700021410040074565408409400038140000c20a0422030760198404401c01035501c6004155241d80350700d80100513003c1e42d00111528414264071103480e241070807445050307410180c02035003885065001190b04029280381101803650320 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 31739681 1250 31738431 31738433
    0x120204030b0c07080c0d0921022803170306031902090109020a020f0f070f0506120115091211090606091302160c0b03070215131214070b01050a0605040e160c 69
    0xc3c4001c0c3d04806d095100e41c2c100600d010704001070100f908441d0038084014549010050341c5000d00716038100c01720710044095911402c42d07080405c405400c040d00f480601d60030074441a03034050045110388001d5050b1005a005800942002644ca01c0000e51200540005020140d840c0d07014100c01c29440c81180d4095200c5030009040140c1094401a603401088040c400f0307040c4000c440340103103401d80700c3c00e241c030403007100004003290107014035046400c6440c6c100d510380d846103a00401a015500040c1c03040c00711840c10800d02e4071100d80345c41c010301c010b10000f0f245182000548644003005016220451007044920001b94083c88200703886d00018440e11002c141441401e00c003500c20703400415500e0400039006458400d0300c242d541c15603031107103041110b50144200c05454046d4030010100c2d001d0744070705007030720b0024494840d1442c00d1301c04070b402020b001d28045400d040340c8054483c01d040c02c0c2c0f2030104460350300c918003d1200908101c0c0101d44201d841505c00c602094080c076102d17401c4d450b5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 31740931 1250 31739681 31739683
    0xa051b010e1801140d050a060c090b0415020115030305071506080304090f05060306010f0b1e0a02010912020607090501050706060806040302060708010501030b010804121419120204030b0c07080c 85
    0x40700707800c0020b644a001889020104401c82c3c119460844030302c008145560344150391151012030081c0f95507191150801c055001d60740711000f0b0580424007549603521046191201c0f140a02d62030015030800d0900d195030f42054200c01c0a0380e405540300c074501586a1100207106d080603a40c0924180c1d10540044d2908040c0058402b03014485000300714890100250003d540000e0941c40c442e8104030010803405811107070780001c880f1603500441d240e5020500e88521031490b2851407403502d4001840002940e81984a040194440c0c842520503002e4a801260f03140c900701c0f004004940c02410034000e660240d00589802e40c4205030218616440b10790040c1490800e88040b80541d100c1c0c0d0a100186800190843c00342500380b0f0200700c46215000000d14006018101501c1405004401a0940c1c4030754075404a854120341119595600301c0101c1d80619a1841520005410a10100c42614260088908503030f00524032b0152034549400b00c40032a4030002003140c0c0c454003000b14140c3c07890 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 31742181 1250 31740931 31740949
    0x60109050301110901140306031e030c1006170d0f030f02130306050106090b07050c0603091905030901020f03030903091c120518010c02010f030c0c0b0103051b030a051b010e 76
    0x741d120255116020394001500720106e140c1c2c042000701c41402000000d4400265280d002d20103842070910312409a08068210300c03c80501e04864000c600000070802c000b5001070307003141c05110000400382410346005481c3c0e003414844800140c40712251100f039905c260403081c540d034801d41c0b00503e00030000c0c2c040070440313171190300850300103427103000410999030004c448000515512907005e2401d813840d50340703c5c1c48050800d8010711440000c804182598020000349004110700d500c21100c1807001c4c1400c079a2a08a940e500340140300c0d112010b45800400b006a0f80070355280c40080d400d01e00180208680880440346203045039403040c032140046100c540d1051042d800399201c0598030110a45015081c805410141c2d052280395039560b00140d0f4401c1044424841038a00040e01070b104000844181c52040b80103030042a040c0008401d11a000c03650030700c0082082c854080e4200300506060311000e40100c050003035000070080800d80885410140e035802e0051424182f01504200020b41c018 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 31743431 1250 31742181 31742201
    0x6010905060304060506040b060f04061409030f060109050a020c0a0f0218130c0b0705030d050c0d0218040c020f0604030302030c1209010c0201060602030f16020414040f05070506031b03060109050301 87
    0x4e0384840501c906ca080074450f1400b030a40c00d03140d041c035010f20618040c10910803842420100503540711501c915164200556000032001000d8542541c8125222171b5104000e0241d05035451819001c40c0301c038026032007120380c0141110040c00b8080718540307a076030b8004a950003e03604403514082c41344800c0c0307003400220712500900c43e041d1503541d0581040c11148100b5000307401611400c1250601040e03000040c0d0310070040030b40e00441c45640b8640d01c40054083c150000d01080d0021503000c4403542c0220300219900300545003048000c00c5c0f500b040b651b136090403828940e250814000715001c00d100340c0003907901490a6101070718010f100e040340c1342040000c55800c403040e55502d4050054607070a0103100000d10041c80218200401d161820109102d441456036035010005403090440d203071a00f1070480001e030050313251f0040c5454100605125003414040700c160140d201b020a1900d043d8080c0c03030050b00401c2090160281c80c10f40f000c1982d10280010703051000402c030001f0207607000d0081d80801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 31744681 1250 31743431 31743443
    0xa1404110f0325020a1509020102010b03030a03060306050c13060c0303020405030a11011101051005011803290703090807020609012708120301030203030904110706020c03090907050702010c020906010905060304 92
    0xc415400031000040181d454507801c40d0019804040450884518107170303071b0b4050800005040301d0780e1005038010a00440c18135098080415580642c9801d0340c807510440780903100603c401c4d500c2d88000314851040762050030300b03c2410b4a05021151140a0805000b0700c2410b0051805855600091501451040859040c640704500c10300659101d08503485541512000740179030b0603d12908076103207409008181c108041500c540c07a1605000c0303e94002960807080204d0f08410311700c1b501843d12602108000e840c03101c01c01060080c1c1c0309110364000c00390001d00042c2410100d5007006651740c0a2510305042280466010039041c11543d41140780e80364488402e60200d1428038000d0400b10417110308d07000f02505000400250b1004011a42010000c503000280c60045d910071a1085c0119038010b002c091007c14524407480c00003008043d5030104465040e19039807884d004440e24851004001c1c0080c80e002000d5006040001d41c0c42d410400504001511315222000b28a058004071016a21 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 31745931 1250 31744681 31744711
    0x90201030b01020f0d1413080c0a05010207030b010501032c0a060501050328030302040b0c0307020a0918060c0203040911180108040308040305090303090a03060f05060a1404110f03 79
    0x4668040c031818501850a00240032807250003944691100102110402800950011400120191b000701e5110500fa98a00021584c69189850b9030b42c40c40c40909010366a05c80003c1050b60000070781e03d003104d612004542040c2e080800444c0645516a81440601c00001d81d00280500381410b00400030300c1400109410681c0307003000402c1e1141a4007450003600072806850506807001022140c0c1140101400c00c0d01e0780a00c0c0440080c40f95511101e030384800032542c490006004801000214002c40e00110705586402c19401200c4031040c9180802038000e0142d000607101d82c020340001c1400b401620b0425680391030900c140c84640021400b03104000070405102481d051840e90030000c2071800030000e00e41650050004c0c0000752019086c0280440e901030103950030000c56952883c00b408403010241c0d01d10b4540b025280c8035203940309076402c01e00000c486044c510940300441c0c40e942d801030b1142c0d01d1202800010030129000d03048494080105c8007281c88124011405a248161320110b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 31747181 1250 31745931 31745933
    0x5100c051c0605030d030e07051f08010e070509010309020f030304060302070c0f030b19110714010b121c03180812150a090e0a0f0507060e0f030303040b041403030a09 73
    0x41c1500707070150440c1c503044007400513490002e0440da00d5802414006200c03654141007501e008941d601c4903034803031512400c07032a5844d20202d40d112500d615480d910b6060340c0ba60060040085d08650a41c0025018410744080d58030a404c103820700d50010385640c0004c1d50003c046070441d400b9811032404640c00185503000c02c007044403601e0040442c4140c000c0d0305401c0d40d40d903003031620001e8007203101c100980481e95400102e6a1001e00921840c1011690303078101490040640c401c05500c10000394640b00ca52091070600d0b41400d5070490011014140c1030b81d081c54056100a90810744804141ea0789032a41034454080c2d018040f40c42c01011404d171907150300106901c5110008044282c120030352583c081c010313200c44001e101030b10650b0401060b5004200d410b01d141c03041802c0050f001362040702c0003000303010022900c1f80c01e031075265883c80e0418003004180544122804051034069204200140110304e5080c4810380051282202d49100c1200440c19480c541082d50014640c0d555024000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 31748431 1250 31747181 31747207
    0xc0608011a07020607060b060c0601030302062d04080307030617010605030d050708040b070201050d050403080a060609060503040b06010306150e030114010302090f18010c080105030d0302030c0a030905100c05 91
    0x101110700c41d100302d16202040d03000c90224050400300805032902c80107120959620803040e074041d000c40c14101c0d402581e603814003e5403400203446000107414011170408a96200c0600001c1040040014188688480d40c4116140d840100709008060b511200841c4c0403507280826689003540b00d00210700c140c148820103090040800310181480410005803001070140300c1510101da01d03903001980c69005900043e01c2d140304030802c421819203803104110816800002250151074102010045c0030380b1281c0c16284011240903e40100318240700146c0018060152280d00c408180740218410740d84070000d81d14140500001b00106540409505140c1024491080703081000d00400d0000d5255801280c40d1200290079440c1c045a14000502e030201030b01440002d00210000800800410b200002c2100380c080c000d151080c05041c804001d441d00c00c0c000d4900454088204518066004c001035000305404c010486150044400c01c440004580c480c0028207081502c8130703540d5080c4a900304c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 31749681 1250 31748431 31748459
    0x90501060816050a020c0907051206010905030307140c03070605280c02090912040909110301050f060907140a11010c02011b18080708070824070c06090c060801 70
    0x180801001c0e1042100e114500709021920345454102541e9494412804034140741c2000034140d00102603e06010380507034003100410b82c813040c11442e140c0301d4072814011141c1d10400e01c99103600d0342c401d024500101d4041101a10001d0301c2070100c0300410701c400b02090804c0310070340c040c102051002c1034107801c8507000410540a64007810002811802490024008090101c00a8052048100050a200c42c02c1200078156258070003e141c90356511003205010b040e400004645e04420001e0480890038140200c0d4000c2002d00a800a1503917807000307000d0107400c01482e030300070001070404112400031100000d0560103481da880d0398526440d2042142503981d001c4158003160701d031281200030072544c4030703140c1030304103040c5014200f60752480c8110790503a2240e0030240307690003201c000044500000900780111000304c0183c50019140e41d0a0300c6801d910b8a100380c030301b015200c0004a800748591000320320248912030005030903040e525132104070f220769080003011482d20001404542600142 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 31750931 1250 31749681 31749689
    0x5030a030f120c360305030c010e15060906010c0807050307020a120210030e0705040608010203041209210f15050105030f01270204060515070209060604060f0e061b07090501 76
    0x3e00100c00b000030002d0000c8000c07103858400c0810000a1a0000e540501981241d810507096401c40341d283d080050b12944112400c00032586440d00d0710140c400c000c107072201251240c201d5003030b0503965201803248625009050a0400c00c00c905101b0000d92410b0142c1600c40c010310085840703c0c01f03841030003d10005a007082e503400003030100420069550520b11700c150102c9240c041602d025000c850307480c00c0690340025500034100a004101204158080c6100717a0041c0c0700040c40752000301003034a001a0500905911f00c030301c2d0290f440324170010225007018620854204100010b01d880e2195000b40c1c0c070382c46501d581c2c1c484004100720b140070820080c941e50700000070000349101c4011400140382d20070b4940500b01c01030758204103540c1c035580404002c120140a400703202d0a061103140c00c07035203c80c10480c400e14030140812014100f0030260b07402e4400c1d9407605029a803239480140e0301c089264002c0d81d403141041051350f2401a4501e90204000704200050000074101740d4030350107448050304 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 31752181 1250 31750931 31750967
    0x20c0a0203100e0d030b0f01030906110a03090605060a05060a030e0304030b090a03080108010b01050d09080408030406020f1b310609020c100903080708190203070518040903021f0605030a030f 84
    0x2030001b2081d6106c0322510b00c500350900700028401001d1420001425104940c0e104080c0041048807606425400800e48a0310541c400c00803070390341e0000c000d502c8102d4050260011030501000c43c07094080d83c42401642d03d501e00701d9040c00d82e01c0c0d503020601401191003c00e1078000c69229800c064124141c1405440c18100034002c285c04100020428000c070360b0901102619030000034180601c0d20100c4002d007101c08180c170342d1551034100184d03940c00b0708450440d40303118004100300e24034081101d41e40310920080008800e60103841c0b154041c01d481c1499095104a41c0c01c0d00d402d456010f100d20001440c00400140e2900313004c2c03c0050030b144101121000560415103c0c00c00241d01005050707101004c1e0404290756103404604462128801162a015500c00414419001d4112010340b800384001800403070008050028082a1520721000501691010401244980ca0010345840c0804a80d00c0050200d42d42c80002c1c0c1350848560781078000c103e070004001801548100d036403129141d180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 31753431 1250 31752181 31752191
    0x30b04060b1c060314060402030613201f09050f0a03080a0c080f1303020a05120c04051f12030314010b0405010e0109031a0916080c04020c0a0203100e0d03 68
    0x2401041a100e900004600210b90040304610300c403995024102841c1c0241281d00140d001e100d0b0300e0b83d100700a41e000d134841d1140038000b6000b06280083c140c0d0380f035032110701d8810900a900c500c030100e449008034a58000306002c1c00000345840381d070705601600c9080d0790307202e034441c0b5240a000c081980101142d00030714807a442800814512812a400d00c0800d14021202c0d46140c1820812400340031502d0b003540700c00041452020760071450403400c0e039008036845402a5601c07001c1110b032364403036000c16460340c0103001e010200c1d01d080c0e40b010340d00642c800a01e00350544000308000d12081180c00c22002e88a08010500906a262148c0d520f400c00070990992254100408500540503d204d0b441c100720344540c9220469104c0d2201ea0003d5501c910070480c4ea08040b003190041c584c040341c0f8025140b1460500c7d0030300108006082e03049605580190100e0070351401480041d50264580320183e208050b01040181c4040102c0018840041ca0024181d0302407091242032419850038803003054106 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 31754681 1250 31753431 31753439
    0x6080a0305090922060504201807050c0106030510060909170904060e04050d0e0102030310060c140304080d02010c0201090c050d0204111c06050301060b0301060507060b09100303030b0406 82
    0x7000c111084039908884901c41c6a9986030742030001040e50348280011615200000e007046140d4000138003a80c49000641e401c040070b500031194440500707940780e80c4190206501c45459003030403240c5402040500c2c003d89460030b800502825a1056031049589901611303d42c100c1d01c40601c9482d024113039100d0103010104850f06c0d55408100d602c408407083c6000054200902e40e0f0720f41c042d400038950481003001501c0c0c00e0502c640c560118070b5196000c1348160744108002d61012045a1017807600030503071490141401ca040390070502c06c1c441140c00c2e2494007000403900300200064001001e00a00030300d070340440d0b082c00074251a50441c280c0190381c18828036000165030800c1040c141c500989030f02d116103e0742e00001d00504082907214602c07400008a4040650303c640c03400b404844014400e00c4403542e110245422505144900103000340c0500050202ca48108004c0241034021400801c500c4100350005050441c00c0c0ca6083c1c2c20310040004008060302b500501441e0802280c0800c0524a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 31755931 1250 31754681 31754687
    0x10b040e1b0721030f0b06030c0706090f060b011103041404050915010e060f150301120218101d09060103110301140a0b1206040f1e020d03030c0306080a03 68
    0x1402014003107210340000e01400304480d05a960701600000b804442d14400b0b03918100d09200a1041c80c0028200341c00d040941e000c0380281d6000e508094a814a5a40d803450b10080a40103080c084031844e0712000c08001103010050460aa2801400001050110b58001402001d4040041d02c0650402d02040000349680500546018010344001c10160f40381100503040621708000e460710b2002480c00400d40d0800e490031309108040603229180c00c2078203c801c0110040442c030544a10200420040c040c14094810042005102800030810b03c0d00100c0642d0714001c04880c0e00b0b0b0343c0c03880c4007401c10041101000c13000160400c1c048400d5581030010566855101c14080070b810100241d21004c0d40352025486001c115500b40d41e004031a0602c20101c001400701c0c0003541d841104044418140d030000840d0139070180d80d00140d0391a40d10703140d60790401302d0305c0340300d80c140f2000b440300d21000e0242e1a60802860b842d07101c0d9138000344841e0100000b03421101e00b9004480a580048510400213170 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 31757181 1250 31755931 31755959
    0x1f1205030d0504030e04020a0f090503011416030b06070501090209160c020114041e0302030c010306050105040e1906080303040c0f060c020d0501020c01020403050706090b03070503180c0415030506010b04 89
    0x41e0000c01081550b00d03400c0035100a05200030030f80e0464400501482416840480d00c0018006503030390f150041c1c0d40c2d404041c00d817000060102110030078040803440c01e1101442042080e0480c1c1004600099004005200e80c1c0294605680e00c2e51921740e00400c500d0202c3c0b456502007165080e08007036541c1c10800401c0350402c068000d05101b4805c1d007804000e105c103c182d600402102c401000800d1441000a10b240d0035407108900a100350007c0289039030081c01484103450042e5200c0e03003000d28109140c03d2092000e425500d401810301c090901448007801400050054500107565900705841c0028014031580d1000c141b000c100c18003481a01c0e44103c0b103403200390301151088001d680030300b0000d009204070b207079000f019840010000200480410410201c1e411030b112446601c0e80c882c600d044610007114a403000032020400200810402001c00b80800011000c440313440f500b180c01f04084070801400a4601040e45108104100341001403d014046e007522450610785020010000c0e51 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 31758431 1250 31757181 31757197
    0x11071101120902090a0c1107031e080c03030c03010512060708010b130e07020c1201050601050a030f0b031b0f0402091c0323070b01050306190507020102040e1f120503 73
    0x30056a00038107440425401003034409400800243c0c1604140100c140148042c4900c6400b007100c61317030b0b4000200720106200e003c40e60000c44034242e2100c8201400d00c1c1d101803080032140d00e0810b102c44020b43c08204041c40c820203480f090641d0303d5051400b00001c2103640c05131088145e004004004c0c1166020014a0441e0104601030b526041c0944424000001d1600604142030303c000800180960000e1a45094107060707442d45444016481c82c9801d9440c110307491400b084c41000b482c24240d00c03a40c814405150300980000f003840341c4200090030300300d02c0b9840e120011915401480541f41403c488505800101c800314900740d80100451041e284030350b044200020300c0ca419100741800b403c0389180140100c60b01c0c2e800317000014040703005604403010079200c801c41c0ca000403460303080001e0264060f508031841085140c010400c00c0e4060940140300c0310455400744400218107003140c81c1c1d2400345205005021200300c140484912354501a84400740c1c22903501030580100c2d1021003214610 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 31759681 1250 31758431 31758437
    0x127030c06092c2a180109060c0201080c0c010507030f0c02010605090c03040206090604080307061802030a24020d020403110d080d0902011707110601060f090e060409051e0111071101 80
    0x40c1d075020000d42e1081804a283c288a18010440c3d9403500641d0001701060041040c8040440341a0b030011151902a8060381d00864441c180e403401660003041c4640d404082e2001c200c0c5842e910261181c01d542c1c0c15500c1c000802e882e6480380d4a801114082c0d0b04403000684020082903180a0010b401d210010307000004114000000c5000d40d103a140c1110444030014003016500c59450403420703565480070f0300660f140d42c40e060303068550f0340c2200e00810030035800070020412030500351114504100404200500042021901c2c038200d015030000d0036001ca901d460068079189141099085208a5045644600c2da40707180c031400038840006640580b400210000780c0180bc0340b005031847d080f0304c0d00404000280b8010014002d03406168901c0602c0031000760384550341c0c0c920054809400e005c4140c80400c034911018448031745d601c025a5070040000708003140070502604c4040c1000310f501c140107100c591000581c0b42104090040b03503808506220554a404099110180589080481a410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 31760931 1250 31759681 31759769
    0x1d03130e04060902030109030507150504020d020405060406030b090f06090105061c0f0c090e0f1507230703090f06020607050d020c01140a0501091103060a050127030c0609 75
    0x2802410f41c02485000d5018008001009160401902c03c1e0440c402c112055084103444003030300c442a0050b1805164050175080040c1125820440a80001424140c0140d51024000045010003540760701036000b24010b0728030300401c004803a0920500402110040c0c0c140000d001240c1c43d034218a803044144010616020080c44c600482e4620362120050311020040d040424140c3d02130388400d400300103100c01c844652000b03620041c2c4407041501d40010781505900092501c2d40241130302d0103006407244045811a069045205c0e658103d00d00c150009a4150001d00c2081080d034540c0e0041d00c0c0600081c2894034144000404078454000d15013111500800c010012a00941120002c900c0040b01c4000b070b4548241030200804091003800d0307059007082c291282d10014942205d0040c080640401203482c1800019140d11442142c15510541c0c500004000600c00718030705805188903039880c00003903180c407100030000c2e0b81c96000701890110806001d940e510740d50042d45400e0740710b9124107030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 31762181 1250 31760931 31760933
    0xd020312040602010b011707020705060306030709020403060b120a0f150b03030c0d090f0605041703071b030b06011b060b0f04021204020405070c0f0602090d0210031d03130e04 77
    0x81000d03454400e0515040000c00c01180362501904040c1000ba030a0360341ca01072040c80ea60114552806490410160300002c0c0e0030b20017800c220004bd540284003504031001ca03980d40e10f40e04101e034002c3c1e1040d9405075513920a03200500e40031440b885000243c030001c040001c250748429040100b014001410100d1705d141c0485500c046800490141000400740c90f01c03006020300c031030f0304c030554042c05100290340107001203041d0b05083e4480c4151034150340d60a01340341c00d02090303000500c4c0801032000144014400c51000601004c100708050412401d40940c0c145140f0b00201e03542000351003d4140a8a00291482d5000307102d100c01c0d00e01d0700f111021a00402c00300201c5c81c42007141d445c0a41040c000101d03151701901c10003429024920980e800c0001d682e40b030000304e8286207420001001c03246401007250202e206600a03021410b0024074100d0245956400a0b82200000d020384000c0383d150916144081c140000d010b0709200740d6070141d4549104e80000d00d005030514014000c0c01d0b05480b000c0381c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 31763431 1250 31762181 31762183
    0x70302010b04090312151505090a0801090807050c030601031515050306010f0e0c0a02030906130504061403010c030903020d11030f031f06030606050a030504020609030105012405031003020d0203 85
    0x200c01e008003400800a80c025803c00600c9042e10701c4200728014180580615444000d0002d01c08880044900c0b01d9000d162075001c076556480304150a41c40907101c1004162820f0a100321480c5e40d20a41c0810b580700c8461410302d0414a00003003d51194200100400204101055000100b44980710000351150100552004003a070364120039014032a102c000b0400d00240c0314110213689020008207090f1b13036044003001c21449000d000d031300140c00c14488060141840400340090083e012074402c00207440c0c501207400c441d00c1d50711042221007243c01e00310103070a080c4a1401444041e25081c042a807003034038003941d1920050440707410040d20303041d550401d0205100b542c1a00d01221103c640d2070405503502c1501400b42d01040804280031140080c01601070700c160412103c40341c07035060074420702c92015001845c00800580c0c1240c0100b10742c44d903e580a1080300d018000e40f46811100c04000056441e07030310390000c04402030013400c00600204607c240d00d0302c03044950464020507039244038404a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 31764681 1250 31763431 31763441
    0x507080616080108030a031d06070206070e03060606161502030a1413110f060903030c010b0f100804060510120b070f030b03030f030c0f0403140c04111602040b06070309050901050303030403120207030201 89
    0x13100148c0944024000ac070740e03020500034040c40f00c42c0d0b516407886603440101601c8030020b0790484c0d4090800c1000040002c006030002c2c003000e0256021440407101d01d00d07440141d0348200d61301c4070640c1d40c3e55905000c3d903005048a41c0c1290380e03500490f410340c0303250340d030302e400d0300d036116280c0f440740300d404c1500c180390703500d1004807040202c014050f40c0d221a1301c0c88402d80a0040c95480500c114a4102000040c0c180300300c090b10100320b1561840311b20744494644038001c00001c0d0106001c034102c03803004542840314903000000d0341d1045120020a2402038070003803111200f128928105405d0180002050750300000f07961120128401c0300380d50380c581e446401c88c02d1240d5800c810004802003400030501c02d00200c0c0ba680214900195074410108804100484a1500150072900418490b2a000c4800035480d0810f40d44007600001d003c62034103001500717540080708101c00013107a0361014805810540002401040b09a000310b085003050764016010b1201503064070500d9502040480504d0300c00d4000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 31765931 1250 31764681 31764731
    0x402131802012a030c0203010b0108040b0708040614040812010b090d022704210e06030a2d020406020c0a030812040c03020907080405060708090c060d090507080616080108030a03 78
    0x48003081d0082c519000d0141041003030b00b80d03c07230351800718803d100b9400741c1001441140d1101200c212540c440c0026a02c41501410582e2003564440345440700300050500240600e0150307001c580c03241038607c0040c0d204401600041603101c4103002c0c4107050789a21103c00c1c441903045405401407081c4014001d00703440003601c0030030b4402468003071000b03114400d176480641e07010500da007c29681d4944800d5802d1050081041e070441401c10004404048580c080700c1c03148024803a4850500c06150a00303007101c1d90ba020381451640c0082d0800080b0f40401560300c001c201900c1100304140b454513801c1c401d025900c0ca140e0004c00800000b01000b41c81c40c1c80c80d0185030b00501400180c100424010b017498421201105d0501c11003000c5440c09000b0100b4901c21500800203010300a6108188034143d0040e100c0c5990054031100c0d80c030001041440290054103034040203107101e25040300c2ca02545440a43c07004c060050000c01030101d07070404812103050300b1190070041200040403107142105415840 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 31767181 1250 31765931 31765997
    0x30429030403030c0207080303010302010909091115032202060a050f0c010c090603060e09060115050c101b1416020a05220b03030a0c02090907120b040213180201 71
    0x1007008060305540041000042039085a444036104c810740d9560b0312003800042c0c00300d9460001081100c0c51508211156071080003c02c00d16110306003c140414001c0440c030925a401000304044940d600818842c502411755840b40c8280382500400c00307e02c90130401c2010450002107a4800300b00580860300d0504d021002003002c1307258088001c108021034060000000d0a10600003481e2220745000c5d8003401c3c0c071350007401c526440c02c0d004030400310101c540700041c40340a05c0688a103200c00e003c1c1840030400d149000c18030740c80710714184818400c00800102030218117140344000b02118010789101000c4c0101c0c601803d01c2d02c0c00050b00780300c0c040d400385a210750004400300c0003403400c0d0880c80c4414003a0005101c811854800c258503030040b81100d20000309444110000b515003c3d8020741c02010120a0f914540e845094421100399110002e448510f01c02040c40114100f03560007001102001c1c0b0308000f03541d642e490b081828840e81e04040c0c1002107131080c01842c4c26084020741c040301c0042c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 31768431 1250 31767181 31767187
    0x20a0b070b01031208040809040c0e04060e0108010c030c020a0605040203070302040e030a0807050c1203061206010b040e060102030a0c1101020f0d110708030c0c0603040602040302090106030203220203030429 91
    0x403800740407454090104a0b25050221402c480c4a07009050650180c0c2c0c0c0150058141011802440018441d00003441d04000900e0548c80071900e0340c0c85420040e188103800c80701e0960408100e0750075a01881d41c1c0c81c040603e0710019108150340481c0480c3c12503480320010500d80c50b1400001e00d40101604041d40c85407424100c501d0016000004029203c10780d00c401c69540e5803241c09603442d008100030703200c55801102100f950103400000840e80001e00a1040b5080f10466000510701802604109242c0b200003800740309005580c0a0300b64084400d100452a0081048006101021600000f06601020050000c03107030300034000e00400d5001d2030b00300c0790200d1503444014016482c01110401c240954074010030f030410003008580c40984030000912130101c481c410302217598801882903542560034080400140d0302c0e554403500070305081e03901688030b080100b018245040d868130f9001550b580c01c0908401601c000c02540c04641e1092501010409139401940d4034904040004221113000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 31769681 1250 31768431 31768433
    0x609120f0d0504060f020d0f050c070b070507030507090908090120010c08071b0b070f0c080301060c14010c080c09010c17130e09030d0c030207080a0c0506090a020904060504020a0b07 80
    0x2c10040c004461070b075a21080704050b148400d07601c942d10f16078041d0019422620700040c650080c001800e841e41c0d000d040b01e10199492422a10301c0c1c000c13140841c0c01350861041001403100400c10400a000030120800c02d0b00425a241142403040d81c0d51641072044000d00b00b04180d2000f18964010114070000f8420240c0c005001440403400b12040c101003005c03060206030304540304103180d040c0f130f40c40a181c5034240c86204058804c100d84800500c00c11269908240004026201440c020f00f850384071000c3d0b080d518600104188075054822050342e1610303101c00d1007180c3c06021107070031080020420b0399480d45500101c5400303030444000341c400f841c0c2c40e2070300d01850604801004044010251800750b5500e9071011250340c801982c00c20180e600611215244004d268003c10014140d410018680142c03640c80c00450340100c01b03041c022030070010f404000c3c0403090041c00da02403e81ca018200d4203009600103903126030007600c040d01003903940d000101113440b000c900d0703006000c142600585030082 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 31770931 1250 31769681 31769687
    0x513030201060602010c0504030609020f03030f030601140c0a0201030b0609030708060402121c0807090f06080a0b220203060f0d05061602070303050d020304170301060504090501050f0609120f0d 85
    0x4048005620380140003943c0e82c4103120300443e8001c541e903650310302440d41e165680600785159080c1c4c0d01c401c2a2801c008070365002c1000b403c8100e403032000703a51a80b0b001e030000340641d2030b11024440381000801c604040c000001c1009030b842c0fa82400d001506143c0d90010a0305402816255905841940e42c08998010700140042c0b055100303c3c3c18040710000d070440d0945a0303541e507507041c00d198110301e2880300450240c0c0c410b80d0311184c80c2c90116110b5a460b00809402100741c1e0002d4041400036080c848084498041c00d5502c910039181c04854102001035480142c000840740c1160310350101c04912680e941d6540f28400304001000c4c103000e240c040c209107440399819540098038550f00072021858070b00114090040340d4141d110300c0d0620b0600e0000501950005004860229030021003820400fa0900130714040e05207941c551b82c4440c20030007070074111403040e0001c51094042101c51301c8207564036001c8a101220030b8510340c1010f0305040c840d030315040d881940c0c1885805100799030340b4400d41c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 31772181 1250 31770931 31770961
    0x70e01151209060c09030521070f03021216030e090108030406050a030e0601060203030709080708030904050702030702030f0c0112020414060a09090204090207170319020a020f06040c060e031f0c050d05 88
    0x130084c015508250188c2140001e009468400400314034401e20880001c6400304058441c17840c001c2c01905c500e0b00ba41a4080d10b2980100201c0700c0055600401900780740d4015600c2e4141703007081d155600c103941010150355980c015441254100312000409455052280d0025501d041001e02140c8065849840103500c07a0011a0441c000070f241c50400240c6610000301c00d030032125004c000d1458542da560900000e0300c0300611210075440108504001600d08010b000c0401c25000050964646103074001403c0340145041c2000d024014002445480a03a01d50700c681c007041154030942c0c400c61146c090b20522035030344c00600c05600c04280003a1150341074004001070751069554288800680540d554203000558404044030300e604030b21090302701340b580101070007110f0340116140c094035008154074043c011078084481445114040001503000a8030090004080b0050a0714401580742d004010446801d400044d82c5c4a035070207060305010f0710407503001c81021001400149000381c41070700380d8a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 31773431 1250 31772181 31772183
    0x1512070608060102070b0306010807140307030605100306080613051501080c150301120201120b030706030b030601090506010c0b1b04080d0e010f12050c0409020c0f070e01151209060c0903 82
    0xe252000090b007075032000ca40c1c131003940c4000c241d05e401c50b140d4000441d420b480c01020b040c244444145015005a4000c016500c628266540841c40d941440203014115108104580a06007094030900c01c0803c003044440e0300911560000c54103480605001d1701d081584180701403843c48910000c41c0c144000701d100c149410083d505180c460070400b440400e103100910174a06102082070083d00150311034400d9160303402021601007103100c01c0708006418403000750300020100755950101da070709003000c1c01b81034010031200c001040036141c1080040c0c41258155001406d05203801c0024645586054a84504503440d050710390310f0399220488141e80e4450311031f1180c046115481026515032203001c2458124400366203c03180035074404518005404040c05d80c820440e000d20011480044610142501c0340740d40c0f00401001e035030750f000c007420540150041c010980f0031100601007500c900765200d00281c003502e0201706006c81c101c0502c009040910f4020541c03424582030384440746e80020b0302c1c8190303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 31774681 1250 31773431 31773437
    0x1303030c050f0303040b0105090601030e0615090a020c1905010f050103030c060e0c1509030f0a060203040209010f0b0f09030a0510020d0b0a080712150e01050f07020303090c0915120706 81
    0x1000c100400b0580c0c9000480d00100203451070001841541800c4000715005030060401203104001400d82d0340c01c007042280c00700b0501030030698400b414944a60b0194120640402c1145080d904c510042d454410f0708001c61154107541840c1001c0110960150340301c4141400200041c0d41c40e40b0b802030030404280f8098501701e041c41c3c806070903075a0100e2070085c0e2901c01440c142d5407151a40010348075410101000d0b506008642a8500c010420300c543c2800c2403003082c0040c2d42c0d14051041041400060308440c1c92618405030900c00340c680e1000300c440c0070311428900c980320002c1c100041d18040f50388034020242e002d4070000c401d41201503009010b0001d111642401108140414030a440301e142c45201c2050f80480000c01025140600d40f24426000f03d03079000d40324210740c0040b01a0380f50512200c00c6691359904101070f4914460690350084000d2000d5491410060141552892151884c074403440d0031001049101ca19500c84c0000c81c1c5e006450a01c03036040c02d101d515202d031128442c52001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 31775931 1250 31774681 31774693
    0x304020f01030e0c01110a06020c0c0102010c05040e0c1806190305070e031c0203040506031905010603140a110408010f0e010510050d080a020313030f0c050906061606021303030c05 79
    0x4540c0a40501d81c00c6490703010051422003044001111846c641501c41000c60282c01001c50100d603160004020f260841c0c8001c1c00c02c01e1030070000a084030742c2c203103402c0200700f0140000d1101010408100342c001d001000c245031191f003072903a03041030010403050f41c2c0d90058000551031080d456410380d69070000400d07141000f0a03a0317071745029074854002a2206030701da0403951071101c2e00304950031440129982c2d441104c1c1425183d8001c9101940141c880c21010f03a120902003102000781d000c0d40e8090840d07031030306206460100c90200304040c0040c248802c1940c40344201010a00b41c00c0c150303401482c510000344545100801040c00a1042c00c0e002c4101e9428140003680008010f1181c0d81241c1c0081d081c203c00c0003641e140c0c16102c0e00000412000c600040010310314000d0811051000f543c0100300300202d046191900ca9103940c4160711043c0241c004500f00419076032800d0640b4030602c07881500f0360020089203000300003072003030802d040d01004111201100381507000c0036038180c4910410458031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 31777181 1250 31775931 31775959
    0x2031c03051e010803070b1312050c010507030606080606090d080f0c0c0d030e060a1b0b1603090c050409061401080115060e030d1b050d0216050a05030c0d02120a050102030402 77
    0x1c1a11024040c51000d07600c100800c00004107000301580d03005010302950001c003440c42e528401469109c01c400300004030007240300c0c2c2220b44203104054100c18141800c2061618040c8060078403c07000300104c0c403880c40450720715002d8894036480400ca0364000c61032680e1301c0300e80c841824150414040941548150504666a41000801141c08640549a80a5041a020400c0025441064200c003001b40c40d244042c02e04a68002d00c00c1981c0c8039070b0740000c80b0714164070603204628030403804008140c18000950b0114221006002c291042503c000c943d80c501401d1000250502014031400b03424044000205040194413480c2c40184201c3c10840c01a90742c1800c4030040f100211183d03254001d4150288507500903011107000b5070041c0b224000200c2562107090030b08014000502c0580c00c8261051006207002d28508050001104d020141c907041801081da6100e41a40c510b01450a002e003040556480110300c13444030a040703040382c2401c0b419107003280c040d4006545c201d00812406035800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 31778431 1250 31777181 31777231
    0x19110a0311120a050408040f14100e0a03030f05040b0403110307080313120c0e0a06030302061f0e0601030b030a060c0801090216030f0509030304080106080d0201090c09050402031c0305 81
    0x10942d150100303401c0c00545440c00410010003000e0011a03a14a0401000038903040400d6604014100c1500d0591020405c1e014005407009a0130a001080140344203e8a29903400d46948196505498040c030444100c507401d9449202d1a00301c10324240d0040f400204000c040a00b144100704150180e4010550380c4c881c032076490081c0149080b4000c000c900c14040c041400082200e401d000d010f4010f40b2650b540a03041c05020140c40810140b03403a000140281601007041d540c00c10201c0c40070300c200b40240100380c2d051a0b41400385601140d0801d0202e50b16a101c0c0d04a00700200b002000d807101c41c04c00c0d14046000b440744808180101d200c1c0e100001e0308c80070920076203040344251146441c44a20640c0d044039210310340c05c00e100a1110603c906c0480b610b0800150002d000e900000242c46810031010500d40302030b10b441d0300c04582c1828038020014038000303028000c803030400002207100e8685100082c1407040206c003101721040c014401d42c03c1c0c6da9141c2c04c480d01070700c00404610542e90201d0800 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 31779681 1250 31778431 31778437
    0x80106181104080307170f12090f0d14070611190906020601050d06050601090306050a020409050109020a0c02210607050319090203030a0c020a030807030302030919020901030b19110a0311 82
    0x100c0544c1c0c005100f05808500340c1c0c20002a0580902441403038182d440d038440c44150050740c11079154400c4c03030b410003151040c1000741401d00702800000b040c20019410004248030300e501804903c030300c004140c5808010054111544092401c0c00a41d110301c001100102031100135080000010028280027640341e00100740e65041e10409031502551444586845003e40000f42400d41006032400000012a80c6403140f10700500003190701513070319031514031280e0a50320180c1201d102141b040103c0029150800340c0c2e00641641540c50702340c0307103c59000c4a58401c031a50040c039614080d103410066041c1c2d211008510500c0d504489c442c16490700c411180c00c9030350000000790598070400c004003095004001820200744020304111502d604ca036200b032925000a4000ca002c030b034010041c070801c00f60a00c80c00110007030341d075402c50801006400080c0140810310001c0d050440080c041084007410340411414010400010f000801d40040303085855030151081d1070010b46230424244100d0054011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 31780931 1250 31779681 31779689
    0x9050903040501110f010603051b0105090a030618080309070603050c0c0a0b1009230f16030902040f090506010312050f030c0c1903030b04110306010519020106080106181104 76
    0xe608040c00c040064a4220b10100007455520030400d005111041c240288009588224060010003c140e49800c02c0d4220b0a03a080d0305214003400983c0080d25621a00c02c200c9400810100e418a40c00b002140007001c48000540301003000810003a41e40307030000d0148115009543c08010f55941d41e40b0b0101d15008101c00001540c21055052011641c1d11784a0b1350031000e0b8064500210b0313a500d03421403c480c00b04840280300107410800c0380440341c0400d640c0303500c42540241c00f85586172001140e5007000c060254041890340d51008407040d51107641c4000e040d240b56641c1000242650700b4566524842480120303a000e00c20f05000c030420f403040082e100c0039100840c4550450300c2c1d003030465000d0303000020a51258072403207140c2101c814207006504803031030184e10000f4402016800340300039111042c124001140e810814090f82d40d900c0300880d10440c103d0881c4201955111074128050704895204c0105903007444800b16036200112030300441100010010000d13905481c02d40440c0b400f036441 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 31782181 1250 31780931 31780933
    0x130c0914061009050a08071502030c030d020c12030103060902040c1e030b03160308030f06060403120302070303060b0c010e010b0f0901060f230301030203010b0a03020f0409020604090212040309090509 88
    0x407811508055120200c2c0c1030081c02c107140c02540300e4020030303070070901d95000c51402c1e0b005010802c0340510b406154071103500e8a10107145230402e90303c0341a642e071090503066a09998001900710120f24244400d410441d0300040300780c0e89581d070382030880c041c00c00490103a00c914035200204c078116004103003180390102e951051031081c0c0131035841a0000c00342028030640501504421110354412140b00001851017051410340b00c0c14039442621913100001c00e101e0003144100000d1000c078801c1010342483c044a442d002d60b903060145030071005815540d014941d50345004c125030041140c19040385030700c001100001c1010b0080542081002003001c03d840350081d1140c030042c03002d0780c800d480090081c0e0203400c03c4101c0c250102d00d04511090302c90614105404044010300462800b8004c440300c0c208101d4501d15883c1c00c5800280c0300102449202e4401c95452120700b00310340f02d05098070002c2401489c2103484901c020b4a204003400100d40440c00554001000f1411381c94078800c140c01012910 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 31783431 1250 31782181 31782221
    0x606010e060913090303090c0e060102060103060c05070f11010e090114040221010f0e090105090d031a03011103060406080a030207060e010306210b0108030f090d08070506130c09 78
    0x10302401000d80c40390100d03d4004481d4152400105001e0241c003196500c20340c0e0000c0e1400d42804c00e0f103c1c500d0150462115102d407801807014503a80040c1c92815290844000100d5003036400090301d1510070007034010021401080800b040c0181c0443d4105494420389900d0901103440d82000200352090142d1004161580840101406e12354090001180141072440306407100600c84448454268404195030064071000d02c9070560704070007103800003182d0009004130700704a4070302a1070719030f92441030040590381d00502d038448000c1c40004400080c00b8000304603150f0741d0480c8090741d0380103c0311680224189100010010000072f0004030040d0558060301d100f5041500458000c9417420384681010307181c140101d04e0030385400000c82e90055a0990626072151b0340307481c14107500140e0100da80e42e08140440b00311000071004680511400b200c000a81034030504d07203201c0e01d0281240141c071074850360040100e2a0160182014443c4c020080600e10960791102841524040c0341d511a28180d50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 31784681 1250 31783431 31783457
    0x80706020d09020d14010c08070206041719021c05040605120a020405040609021b0304050a061b080c030c07120f030c23030d061202010203090909120a030b03010e060601 74
    0x1a50250070000d055180102c0c1010403034002440b0340b11043c0b425600402101941021410f00b4450484149001e007800d18183c41c09030006510741d40020005004004890b040b207031030404890485524100405440003020500c0000139607c00032901407056071380c03000f81c03000702c007030700403816101143c000d41d480b5403400c141401c000c0b20118000e088807264513000d2202040c0c2d641c413409201d026141048006880b00f198081c4140440807107030b80e64100d908100024825170f00c50102d0741003030b1015402c101042e12210850040080f04496000d080f041c0040340c401c20700e0802000408074000407900315602a600c0d40103281d584000c1c4d50005043d0b00d02280a4000070f800707201e001900a0160039a4066030050048000c44208201207609031600700046020368440b0300e1195070060690b410310b124030a40281c0c000f0b5504c1c440c8801c0244210100f40000d00051001c100d56401051407100345c80e11580c50312000b8000d0404ca079075852081d4209100341c0030f172000000702a0701c690016500d024071407034a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 31785931 1250 31784681 31784693
    0x7050904022206030f1103010c0c11010c030e0901090c12060f090507051318060b0705030a03020702030a050d0503040308280f110f040306060e070804031d090f0f01050307030807 78
    0x510000202c0d09a00d0350000030100e400d0f01d0210301c62502401100c5501c20712002007500b102d81c4400d129040c0034840c003007400455000c4d04086113020081c00c2444801c02c0505042e44c1140312000310079840a8218004124500190040c00d031203c299100c80303104440040d140010340d0941d000342030340d000300140204014405074001c10340052050400924118241c120010800307503c0d0000c0c1d8120030859040801c4569a00c00c0d980100f0300304a0490070050284d8680ba1203104244040341010f07000b0503140190740c1c05200720b0320710300d03400780485845161503400502190000c407030a81c0803c07490000520800766207000d00840d10f00d92120303030855030030f91740c040001000441d04020565a5800713003d494015450f0080c400010001000758070f0b18034614107001a90713080d0b005450b00038500c0051100070b98000e141150000c4c1e02d410000461031100114160f40031040c0700c071039130101c100000d010600031490381c0755002c0c100c0c1c044012034507a2a42e0034141c0e01c804030b10000780400d50401106003c88c1d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 31787181 1250 31785931 31785979
    0x21804120315030503030405010501170d1e03060e130b0f0708061504080106180608010219050705030d1b020f0705010203090d05030c01110a09090501060c0609060f021306020705090402 81
    0x2c000b0604100c0c03240c0b2038071458a1034000700d6044920703a41d01e00c01840201c0c0c44c041d006000c071040c03100801c00f411440c50f0042c64842c80000b00e010130300c0803200c1d4142c09400798000344040d11a1a80c1c0b54107500c0e0881e4503941000307030341005403003801a0b10045550b5005031100640304052588641e4090744454051101d0050903458011002c030041c000800c00402c01e000d840b0082040d6035641c2d61121824000c142140d002da441010560710400410040f04225a000381c00c080c510b082c0319031502d00b642401800c51103400c0b08007845528006000e11184403402c5070190f0b8070314950031201c1c1a50b000b075080e0354440b528000c0e02d015900a2002401502d41200c1ca450320a116109480c2412000f2400500f90381413203041c800b0001000c100d248203694018052401008185005c1c03000e0351500401800b400300178980601410f440d0603102d0140011500218070500650000319994800000d183c0c101d81703240e005940c010300907002c0005d00303484c0c501102d40c0030382e4004000b00c0f00f0a80c641061021f4030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 31788431 1250 31787181 31787201
    0xe010513051c02040501060306030326010e040f050d0504090b03161401020a0b090c0907030b0a060507061506050408010c050c060f0720071403010c0207090209040b060d02070218041203 81
    0xc40c20b030905400680381c074001c580c02022a500c020841504519000d0004088200c85803541640300540e96603848840d40c80c6030459012501402e0700d40c4846c28070001e07038054000041c10303520940502860340395024001300100c0300045800c0101036112400c04d5114420751000b105081e20702c4100b8050028040c02e02c240d044414012030f22030f03000070342c1e4410841104a0703142a4503002168400d010741040c55074a507102032a40782c1001031041f43d800207038050920b40074500802002243c100c04000b555030000104902c102c40e071681c0d042d80c4140007056070740113000d00150b0b175080407000e91078035004d4000d5543d113910300340182c4015aa4800303010720301c2c2d100503d03100400c4001d510b00c140b070280841c0c509000030012009010511304200d5840c000201402209000340e24049034440200c0d030100e00340c01505c9154801694507921000010f000d4801101b6280d886500020341010003400c80d40140203192007501c80104c002c00319906550035460485015040324415044166460700c690302c044880 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 31789681 1250 31788431 31788469
    0x3060b0609090901020a08131e0f15050402010e01030b030604060221070203090102010b0a060c0b070509060406020a06050714070f08070b040609020315010b0403080c030408030c0703030e01051305 86
    0x200407840d0010b04403000c161a48500c503540068080a5194080c01d00c41e4004440b0301d000d81072144035a224099203442100300c509403503000c40d5010070842c01480f900b4049401085c228150023803c04004000d01042da8200e0100f419074090b5400395009010b6880c0001c1d008014006555482e225180654020a00c40820403406281c0c0c103a1910316107400c0b40100303207503401552505081400a0300b111518100907200300a1703400300304143c96000a02c0200c4691214003142c980d16040301c280c4041c0a150001c5911420205000c910991700099009210340034000501294480ca80305441402c41103d00e800203400c2004800302041080000c0c00c0071034880c08030346180943da03444204056500703513001c5800544a100c0c070700941c60200408000321203100d4040d1800d5250403450802d034482c40c803008280701c4000c1031410300d54509000ba10000c00680d0182c07035480031060703005510341ca0140004c0340403410b60200d00400d54400c800b0742e54809400700f01003903100e052004000301040c107450308140c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 31790931 1250 31789681 31789687
    0x20c010209030f1b0d02280302090c130e01060519090506120405010e0706020c0f010903021002010203070912081c0f14190209060d05061203030103110a0503030702010903060b06 78
    0x5141c40070441c5030103d601900180c6403074255591a41c840313054101146110f41922003400c40507a9030540c5440d502c0c041a040a1158140740c1504420b40c0c0c006da10107540311340d0050402c141c0c10040c2c8001c0c80c1121a0150f03a160f001e07210640c2c007816010a0140400083d024807140c4040c0102e80300301d001000190514840080e41c0f800040c0942c0c0c0130500142010544405010030000240113140341981144040c000240c01e1840081d42c4d00080400c1600c079041100c1d0300700040e409098400d000d5034001e00440007030341c4004070180c080d500079512803001642091001400385140548100c0e90356220884506d04145032005000c1c0c10020910410f185503190038280075810306d441501880c80811118614900c0d1500c40086101c06900c0c03000703106801040301424580c0e0300c000b00c542c0204100000245a11843c01050381d04488450700001880000b00100c00d110751402d0400300050202c5048540c03075100c4007459200c1c0100403009002c01c3d801e0005000054007500040e5007002c01a141e03d003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 31792181 1250 31790931 31790947
    0xf0219050a021009090501081b060a020c0603130605041416030c0504201603091a040902071110090509060a03020d0b090309040609050912040b0406030b0d06050114010927020c0102 79
    0x112102a4046d213041d6020442c805a034810080042784224400c980c6242800400c04000c1d46911000469902c105400400160780047c100140700d00c05030003000410092805160201d071101c02002e60f07041a200b1456613801003460343c5000d134140d0b42c0c099050300e2258a0441840003034454015102000f0060007005501d0042c4d80c409000700c8040c100d01043c4010003410b01070b12007505a00007075103070200c0307141c039001c1420300500b100c0072560000e07001a40c030300c2c0604000b00200720400c42c2e00d6108403030104982c0f040394000031007400c2d140d0031140c0080079180c100c00c00064180d00e11000350008180b4502d80045601c007080c150b8015900d00a81e854040c3e40c0300042d046404a0f044a03851a90703d00c04e00280b0907040189602000300000c6152a003420b103190a2128040d6214a60404d83c5503125405248c44070300c149462103601c110b0034081561604034840f040c0307614810881c00964141030014903200d8940d42e01c00d0000400f140f091040315680c4c10300740a540002c920b0101903400b040640 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 31793431 1250 31792181 31792199
    0xa02070e040503120106020c061b03120f010f060305160c0221010905120f071e08031005040f05250908060a05010503060901090209070c1407060f0219050a021009 71
    0x5100c1d0344650083e5940b0b600b50703641e803904214181c2003c1d04661003080c805d5481d480d03200031600da440e19504210f0013000104205450f5204000c03414903c54030a001b4051020301e940d4020341aa00008000d400890b03e0b0b0783c0450844108131060102d1080700e1940d42080c2c1d00820082004a0018160420101007850b500060b0341d40d50300440705580d92503071000d05100c01800f004107282c04107000c03a031500c042624444e0440c0143e900180400b000e00b00201414540f0407406c481c3c1a0b0312000b02030300d03407512600d0821f58100341e204c0c050103203040020401c140c641c18170505128401e4100004501d03207500d00b00001040d441c0d800c84043c0309043e00007040c00d000410185118403030390100410a913050000f403500b0700d00094480095a810800d10a00603528802d601da0700015038508104400031078281001c1e42d41ca940ba050500f8000c0d40300101c1c1d519400052034510216607021211210070502c0e000179005108100540307107400008540d0018030342001d02002010361480d24000058540f5421 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 31794681 1250 31793431 31793459
    0x9090b010503010e130f03051b06040b0a0e1603061e090201081611011e060803072d02130c090b04030203070509180706020c100c1101111e0a0b01080c0102120a0207 72
    0x680100d4008203031005a0762700000c851041000e01c6000e0034a5003000d58408110a4018040c030b070031251074400c031108400c4108801c440b025094514001d0456680c1041070040c00c001d06440005001d03803883c80302c0a015401282d03411035041c4c1da10901070390fa9041c0d048801a40ca00d41904010164480d00c202072424001c80004915404040c1148415514060222091544941a16002441518040b0700c0301d074040036175201c1085000e00407900701961400510380c1c1c49402035010803942944008015980c0c404420500310b61135803200b43d0786404085c3c607940170340e10000358190311000052240e424404070060700a15040309100d4240c14802000d0300301030194000d00300680c000044108285070920b119160154141402048111240c071b51071001403050009a040c004100358030200d2010130800c4110303074050380410a91107540300c2c20254903203101c04c04c01e0b02c03800e41440c0082000c2c44041120b100c0500160000c0000a01201c1c640d8001d4021648410a50042c02030001d48800d0724000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 31795931 1250 31794681 31794683
    0x3130c0510030f0f0b10030b1503040b0f0106050301081e03090619080f071704050703060c170604020406050703140c01060e01090e16120204020409020c0a0309090b010503010e130f 79
    0x20119048540050f60310440c3c00040c1924003541c2000c4050105403114038203c0c2400d480c5150102d407070400340d0082020203043c00511030442c1c000004010510106043d102e0003001d030b2044244081c5d80c0c4800c01c5a05000078007403414150001c1c01000c001a1203514026201010113044c0d90503c3d9023080040c1c12a04182c81d11a003034661942489156581300e010f040d44951102607607040c03402c096900420980e00600c5115211003810b01140601c4010400c0e103000f954840801e00068400b2140105011031001c1007c141c0c0c00c404021509c4da103800d000740c4003610b00c2c5a90f018109921500c08588107a0904c100380101c2c0401c109028849500703001c2c40c03016000518000f086549010380f0388040b0780c1d000c80051010382181042c0319800c02100e0540b401c80d00c4082d40c04690786040c0c000903001784619444000e02a20019482804c0c2c1d6010850102d114000e85680080039942c51240c000d40b07440c1e808060000b0300800051080326003071a4100d410840c0d0600040c440724440d81d0307690f40d903030310400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 31797181 1250 31795931 31795937
    0xe2a040e0307020a120b1b0d050a0204050a29090604081501030c0b16030807020c04020d060302030d05190f0306090203040609140c030a060906090210091503020306010503130c0510 79
    0xb00102542031208070440180100035030040154416140ea40c04100c02410030035802040904520b03186032100c054a1185550010422117400c0c0a14490000d40c020710a0078010400040005000c09140c0280d00403100010a21080b0b9000a58504030b0795001c4031031154400003e01c4041036140c020000d1304000300c45450202d80760350450030040300b000391303962203100e07254130811000e001c003299400080d01440c1d16082000040d00c400c00c003a0708010300348034015080791021500c1034480fa102d82000301101e001b030781503c4440e840c9201c12181442920301c81c21410b00640e2032500d0b5240308046100f5400340c90702c0c00040c1c55444202c00000d03640203680079a0801d445030078032410b03c00c03080c1003210005601001001030002d002c0200c0d4031101c0501d000f620096880c0c0c20b24040c4442c0d034220b03480c0c0c1c69008248040b9032518410143c03041d070207070041c1503641000c4207000e110f0354000d100700da0007054161078060441c0e44203414178401902c4030400b200d00e00c20406000440340c030b5280310341112105d00e031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 31798431 1250 31797181 31797187
    0x102030403020c0409050c040c030f111206030c100c020a0302090103031d010f0207030803060a080f030a0f0504270f05010603020703030e0304030206070836010e03010e2a040e03 78
    0x7060080c640020316500d50320031803510030454009080013030704c42c2040c1810b076400302d0b46c20800c0303c013500181070640d1051009810015008514286400141040e40140c40e94040588680050540e140303a001c1e05160021004500200c0c09402080102c0d0101d01c02000741110541740d5001c5001c0340820307031088004c9201e146070305007020820302030341b003010601380380c818803450715107100940d58022440080e008650000100c0c0701c540718189a040a05103650480384800c42c10a03050b83e0383c4d0b00120344400061f00100c5120311b06442501154200c602c043c0d100c646001c4840341e606840005540d01d0795032141c2c0c0d645c408510300f0240c00748038004d04103034400580311405428080e0039030350f0b0b10210000c240c00c200b100f440180d0340c10060700c1d2000d801c484050703121411b4200c0880b41a82c580728030b0080c8042d54559410101c1c00c4081c08549050070303600d105280c0801d00c02c0c035090319401d45442955400814486c1e4443c00c2c550301c001d01000030740004801c4540d200010030301f00c03160032404d030b00340b07030000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 31799681 1250 31798431 31798433
    0x4080d090e06120304090209010504080109082203020f01080702010b0a090506030f0f060f0403050d02030a0603030905030a020a0614130e01030201091502060408130801050a0f0f090209040b0604110c01020304 91
    0x3400031507201109039084040b191583c0c5034240c4074441c40c010010b403243c1c080781c0080e159111740103a9015055540003003000501c07604107030005410407c3c80320301c645003c0e4001c13807105454004c2c40040b603601820f001d0700c0d180000015540324900078000d104540d650541000f281e0303594a1010024503042800041c0342c20182c080c981880540745c401e01c010707800145e40402c4001c000910690040409041c3d068640b101c0c80c0c100d03164802c81c0039040210740013109001a2481681c0b00208403442525481340c00b5607518180b68a070800b02c0f01c06588001d03050f401304440ca0290440e0200c2590044c0c14074070b44030009015500712112a0084900c0011040040c030441d6008036240001d0043c0140c5003c186468a4000b0340c0d41d28000c1004101403000b10f0780c0449550182c902c00042c0004400a20807031034041181c40051090170b0145000c60700b00a0581910011072107103184190300585582c48564550300c6810b5642800f41605400503950380c0c0724003042c03021001403c60111140c001580d41d041c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 31800931 1250 31799681 31799699
    0x304110a1703160305041203020304090b040c050a0e0f0a03050615030105090d0f14041502070e060a0603150306050705070501060621091a0c0904050f060603041704080d09 75
    0x3007900000404105075110509814001054030810700d00619003195030003052070121080e00030b99020740e45c2c0c8481242076108058011000e803044d0345031110100194140c0c41c08202c00e030398a00000201091041102480303036442025aa5240c44016211480c08008440400e48c0d4089561080d50541c2210701031200011703a0b0354903002c40b840210024403050501d0f8048075180c000c1c2c82502c40c2440039a0041c1129640240b82804441d00c4c448440c1b0b0300e03655108003070100c40403451003903030040c042c00300081017440340e110750503000340380c05882c0c07509603414814142c2c0140f0045030312003800d502d11480040011041c1c01202e1103891141e5455461f12560700d0010300355942c1e5000302c41400310b22100600300d09401d10803450054100080843c1030b0000342010070700404a04a621106d441040404c04503c107004014141034406403410006a0b0380e004034110a25415a08103910510400109010a0b1000030907085c03112001c024903d41940c0309022880c1034192841d41c0d0200b0007000c010000c0000e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 31802181 1250 31800931 31800949
    0x303050604062610020a031a011706040f020403050105070207061b0305032d010e011811040302040e0304080a110909010203090604030807020a140f0105070c0f0f0611030411 76
    0x14107840520009041031074451034009020300045082d814801c0b0090502d0080203c40e8040340d182204541d10700c48104010054070540d1824000300c940700030189659442064000e00e108401c40800503079444a0003000007510f4060b005007141074081c0000f0000c680f081c07081d54002c1819030010000245490000b03003840c1c149443c840d52041c5c1850307070700000c01d03000300c101e952044002d00301c0c0640755484201d03551711030b00b0480409000001d00c000400c43c2c91540c100503060302c0e0100b035042da001c5c1c0e525180c13000f624003c1c018502c80c00c40903c020801030070140c200c0c0841000d0070040d02e080a03140e0002c01d280070500e0304151902080c82740c19101c2400c2008440d40c000d1031000084d0709e17514203003610700d543e124041c000800700f1176100006001c29200b4407141681703580c01140600899a4910015925410540b900215520300030215003d640243c01544480b50320000e2030442d02016114002402188007040d5403050301c1d02d151950400792700c0f00640c03140748514052680413081d07800b0b12200b80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 31803431 1250 31802181 31802191
    0x3090316170d0801060503040303022101170307030c080306030a05030d0c031a030a0f14010207030203030a0621030804170a0c05060109050106050715060306020c060412090e0115020a0519030305 85
    0x2c0c000e40d004040c12a8000d02c05030540d0410b05005580752154a4110001d00c140b02c012040c042440d410f03204000c0c0c0c912400d03030403034103400c124103250121000c0c02e60316889040c0c4010041551500c0060003c1c40c4000035680c003400007002c0e120302c0b01607506c80c681998000c41d1034078801c0ea40c44510b81c0c2a15010320469142407101d00700c0110b000b4110b00465980c400411025221340d02c0010480200070041c2c0003404c111b0080030080d521100e05107006907480e0020f580342c404160038140c000ca410758514418426a003940801410075076031a071000d440d5000041c01c10754120150302e80d07000168010400400c41c0d161295075899201505061160030250180c205003507190510004008596000007624141600b0038410507644441546190050150750300c02084d8500100e00a01000808504d03148075a0145001c46842d9048150031501d0940c00d0103400702900382c07400103001128040014038450401801280c80111840c0c540c940b9014203245d03c10b03001c03055101050101645405416044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 31804681 1250 31803431 31803433
    0x901081f0504110603060409120c0201031404020306010509040510050708070206090601180f0209130207140f0319030e120d0f060506070303050613020708040501080903070f020907020309031617 85
    0x60a16648199400c0c3c11031408070700c546800b00115503c2d540d513a00840721180d008154043d1100c160502401049000d01c0981c0403074540b01002c402212801b420354420350b4014043c1c6010303800d050802c240c03220054000c0c1c1300c6108002e03260007041c01a108480c01a085034460000070316008900038600703c002082c020480d00000c0040110080c1c904402e0162402e4590114441c08142000c40003401030444a039845515204105d109400c140e0003021158080c02d04094401d104071411562070300c6241181070340d94000c100c0d4109090017520710343e0340401c481c9004124000621007061130301003550340e4240000300000789992400300c68403500082d904480010b001c003038900000078a40740104800a0141a140d800041d42230b40e4103405400e03002c001040440d20784500b42020121604540a01741c00309014801040040c80d00106980995500c149141041c2d0942d6080c48841c0c030019254006520003441076501c1030b03901303014040c003294201c1c8a98a080340740c040e903050704001c10407c10281d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 31805931 1250 31804681 31804691
    0x206010311040c08150d0633080307170702090a0b01080601090308030a020a031103070215061e0d080d0c020307110109060c03030c0203040302150a02010501090203091b03010b0901081f 81
    0x101c3c981000d202940008441c850030310202c400c4003c55031990040c00b00400007490100004450000714200070b030f11005010401c00051102c5980702d218620074003404203ea070060120340700080e1111a4050b800d00030714159030404540c0d5011690850081c1c41e00c200182e2608001c00595038088442c9a0104092a024000a20315101c0b0080c83c40702404806007581c000032054617280c040d0b00681508103015040b10358918002000a40303552003016000300d10003010f0081100c0c4c0ca032000b106d203a26880e02c121000b845841d0b004010052540b0b14040300c014800b8051820705401d548601d078039a41c4039030080c41c0d44010300c0c1741c10001c3ea1030900205040c840004002d10200f42d10900601410394541400559910b100405a20394022070780002d40c8100f20980e060030849820000c0e01c0541869002804103076201c1e14000e05900017181d412000d6170125080c495500c00070fa00c80c000d150805000002c055508102180120b4004d0f0051302ca16800b40c401424510001500b00864040420b01045 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 31807181 1250 31805931 31805951
    0x411090d060905030909040f0c08062203020124030b010e0f06060d090503030703060305060a050403050d020d0f09050715020c130b0609030a0303050a06090207020d0303020f0d0c020601031104 84
    0x14640845034040c14095403a40c0c00020480100308aa1040100400c14465031503e454100c1038881c20560850f402001c9140000c0c1040b000130300c0d6402403211403607003454100b83d0381c00741f00d0000d4504000d50456403a46402c11380001c282002d02200c80d0b10710301015005095040c015007071503061384000c914002210030404061a03d900450300140112005960b402040d0040c4016001c03101000e8504d0000006002c0d4254240c2d010404030391080c1c09880b55561500100e004481c012100030b40456800c10044180c00700540c0107040c01c0c6c01c02000040d04203008000807080348d403501d90032902036000003c240914100a07200604990580c402400c074404100081901c00e500a40e000f103089803200c52000895075010300340d9506901c040d045440c0e01009080040c0034140540d640a2414500710011808030300c03900807210203c1d0080c000388800c0042d40c0c2c0c2100251f00828441404501c00e004041c11190640221b20045602e98003d000710350450130141280790740c00300b403030784035500d07002e0040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 31808431 1250 31807181 31807189
    0xa0e1204030803040c080d08070e0d0209010e0c040f12060605060f0d1802030d0903020109060c020625050a0b0a050105040603051905030f0d140105060301061d0109090911041109 78
    0x2030580e5400b0108a450b610707286400701104500d500034030018015080045d202c10343c401e04d4035120f910255650350035001e00c00240700c4070030003408019420070031290050025085c060a6150006e58034500c441c6880c0c0d903003180200d04541508842c1704900303042c50034028001c0502800300a04411a2800d16002c41d426150489201c2c0000c0408580e40f00d02c0c947c418024480c180f0703941c2540203001d94080c1d20b00203d004005030428042203000c01d061180200700c00e8071503075082d0400b0f0307409040c0f18580132a0009240d1904100360303404c9812450740c0f0000c000500c0c140200d404a0344601716020160400421040941394141c000c1c0d401641381c0101040415000610703041c800c030100e4900302d9024100c0c28450f04520034200104030242c1c0008548009100c19808a41c0c80b07501100f8042091762100b08000940c4000c1c410740740040c82c0c02050805410b0b19442c41e04103201c0c141410880140e9446003072082e00c3d40518261902e030b84446040c6d5081c02c0900400c4d40380041e2001b8030380b404400c04001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 31809681 1250 31808431 31808437
    0x301060e012102040f11030f01090516050313050d020a050f06130809040b0604080c0102070503010b01020a0201080702190605062404121103030304140d030207020f01050c01020d0507080a0e12 84
    0xc0490702c1815038906545840d84481305040c1501c5050041c086640b0300d5082c0c540c0103680d91441d40c02000d0000134810700e0742c80381c140120040c046906401001820403151504058411440702e202c4004800000c5c00070441c40c480d80703420350081c4c1064455420002c2c00e0100303100c00500240c100c031003002804110032a150408550011007280c84001a001042c0100413184a0366081440041c003c62103840000702440511000da003210380b403580b44c000b0326007030794095410680035a110300703840d00c010341c01050440e512025a104459089210040c0900341040c41d082c00c1d034010f603407001070141c03034201038104050b0505288141a90a02545400140c80c451446002e0b041c4500d603803140c040200c001240c803412413005040f81d41701d04107400c1c010103c54011103891458454050440301076400ac3c025203607a10f030004c2c07040c0d1402d41c45800540b025403003d0500803203035601704860814140144034190240c05550b48401280c900743c2d54440071214101204089981300411050f0030004800c11 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 31810931 1250 31809681 31809719
    0xe07020610060903020d05030903010c0e03010608031201031707120c02040e0c031002090102120c010c030b011106010605071103061509010603021c0b0f0901060203030601080105090609070804080904090507050301060e01 96
    0x458000e004642086810340c0249c0401030707415401c0c000d40c0d20040b548248000240e60003280200b003d0703696100010740d00e10610420140290138200104007003800c00c044e420b40351505060951804800342d490307007400b000c0c0114080200d0f0b01d02c00d43c2810340c2040c0c824640780c0b10441d40280b06c03001001c40001c7d44c5040c2a0404644140c0000b00300105074820300040207422803803103585031201580e454450107003011004260020303192902031041584100d4602c0301214075100030381001d03401c00400315100c8d8400b5009440c145040980c50079940c40801c0354903c41d6845042038224070f41c44100b041508001a8010403c250061140801b01420010856040340c030003000010450010800308214014414400307511068000000801d590044015407145501366075412540e030302d50b0200402030b0020349540e030f00090310a0001c2e01503801000010b40260080b4110b90400340100001000d440e242e80040b281d5400507482000b5034113090248001400942c940da003080d41c1445203002c10000c0d800c0d9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 31812181 1250 31810931 31810939
    0x3060f040302070816180b0a06180308030f090606040c020c0405190903050406030605010c08030c031510021515091f180501062d11030d05010e0702061006090302 71
    0x10100d01018000c01c450001040128191040c82007440c0841219034481c0c0700c0c25400000c0728940307200418080c4640b80c401d0200801109405003420b508480c4042080b51740e1448407107441d0040b0124003460083c600c9035002100800b110314280d4495400e00e030020302400e001314144900074014035000315001030000819200080d0b59669041c0001c0c8074102840d0b054082840c0c03543d04030a0603030042c02002611144e40303043c44020742d2100119140410800041e007a0102840484c8008400d84001c5810440c1a01e400c8402501c0b040010092100c0c0040f480140c0d00000042d001d00d92040f02055210243d158866624011301e008604a100014808510b51514000d52a54443c0340301020019210043d00300046419228003080201400c2c02001c01040d00b0a40d588815182112001d4074000c1c041c900c40c018200440d4161a58041507a001949001c107102c0c1380200003151260354020840845c034285181410704020307041041c09000c050740310f0f4980d241844020342000200003241d0b1705071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 31813431 1250 31812181 31812211
    0x50d03020c060f0703080c031b0a050910180f0308090603130c030303050414030304030f05130e0f060406080a050706050307030204080d0207060816081b1309061e03020306 75
    0x86412424a0491500d16a0005020481450003004400980030051003a02c2c0e1101c01c1e00d07000403150b100c2c0412035a0160a0700d600d4030442105800c000604880d40c01400c2060034800a240003505419405c0c80080c002000d11804100c0d003560b11032100c1c000c003524850240003d0958644840303500c104030745c10380074105c00008039103141641402040c1c019000344240d44070a0b03d9150003005003909940030b40e0032502442c11242c00d42c60102c00c40780965450b4442c0010710700d84030015543d41c1c01505400c0404c080842c4001100401e182c807032407081c500c500b912050351915600b080116005500049403a60060341c002c00001e03c00500c2100b5100d0605055803650b4844801f1806481690000744030360140038044800c00360001015025940c680c1c075694810781d03076482100f244441d10400403001500c5200812065100428000c800701d450380216071400c03243c42d806002e0880580d210000c50750382c500007000b00c282c040185000c21517403c044d04181c0c5245400207940c580c0c001d0a0103009003502 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 31814681 1250 31813431 31813433
    0xd0906230708071401150b12070f020309030a140d020a08030a090f020406090207020405070216030f02060f0a020601030c080a080d0203150306010b0705060108070303022d07090b011e09050d 83
    0x101c0b09541d03180350b21000448032400c0ca400003a020344082c140c100d441c248640004075281c8510401e84000c0060850310851941c1d0b031410440e12089114600c00643c00708101e22091600d0500030000c000707015058040740710319643c029618003080075003004215040f0f82040800107191000b100e42050f14040e01140828160522104156415900a40c02031500b140090341c0b20054014228050080310100425510b0101c20381e11199480b481c207010f406205d00c1400000c410f01e5060045500281c1414145051000398000d1503100340804805a4000c06c0100b0800c020072520102400001001d807410041ca030b51001503902940c01071106241c1c001c4002030400211043c10301d200d0600800710740165a48681c068842c0d40300c40c070103483e58003ca5002103034901d1f0028201c0201e960541c001c20f60040f058165040381d8501c21840c00c404d0007980c0c030020350040d0420620024001c54407000600d1801c01c4000342c02025502c07242c8001d2845000405020b6810101071401c440c4191031070b941c50b90381 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 31815931 1250 31814681 31814693
    0x2120601050d0b0727030203060f060303040501030c03021306020616020307050c0d0303090203010f0209040b0607020d0f020a1508010f090b010207090c110316061d03030a0207060612050d09062307 86
    0x100f000f4031703076911180c01c002c548490806038410003200d0080d8240c681030b403505040180e400000711050b0b81c05074800c200800045d442580891180c18a6207401414071a0002c0101c141000c0703540507000590200c000c2c030440c1e042415017100c00c00d4032130000b546400c0c42c0eaa100e46d205e18120222a01c81d202c012284001d15013707810044000b0f9008008102c42e6841c2074049009411410f5954041d601c3c03d450703035009003403400484007610b4008089101c0a8143e940d5481c0c000d10303242e003c0742c002220303040000d2041500c41e4085400c040d5522180855810045913850807203155005d00d2245007094a1080d059801044207403ea40400d9004280c1040403402600c544104d080c0e5181c107403000181c3c454119543c4021038440510989045c490034030850130003019280ba40411000e20341007000030035400c5003d9402040035620550b0003280c62980c0b4006d021001604240903900e603006a04031111003980060b00300087c180a04025000d816002001c00815089107401900490b00003014003d10803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 31817181 1250 31815931 31815947
    0x306050403051c050906010f03030806040b01050f0a020102030603060c0a0c030c0203070b0d0614010201020703050a031e09060b010305071119170c0304081c080a0203060109091802120601050d0b07 86
    0x14100000c0b03244001c3c182c28800142022100041c10b4040e0700300105808503420008002c81e5015600c03c0c619484030800c01c002010504003076410700c60200f10030384e49032840302c0c0900300022064000688900e4110241424108000c111140700a001c0000b444010b4110090f42900c2c2c0d054500a1005002c1e803011a1400340240c1140c003005902064949a8950941146d0700759400180820841c070519001a400d030301500a00501091043c0880d010203842540000c8010500812201980e08034074a01001c94818840079918941c0700c07480c90b5020751300740c055103401038428648070305284404020640c44d010f10a20200d03294100310001c00500c4001c85210441c0380040100507680c826444a00b640c176030045c8111a241e001e0f914802514415025412211159a0710f4150721a5610481d80b8000d5000a0134103040c8003400c0b030007084004240c03003528440c024402112140781c039075004001c40d10060141340013190740000014802a20750525486142e035010324031100f11b440c3c403001a01c4a00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 31818431 1250 31817181 31817197
    0xf21031b0903010b0306090a02010e1002190606050405010e0a1a0609040b010201090b0c030108060108010b090106050f070c090f0b09010b0d0b150703080a0c020a0515130c0306090c0816030605040305 87
    0x8806c146c01d01c100344801140040045100342ca0701616515094180804003022080990143e0050914080c94852125808c01c444c0d108803000a403441c1c4440006084400c2a04450704080c08441046210112481617484803506501e41c240c16550303803000211184a0f02624901454640d0309588540e4000d4001c102c20a074480841c0300c07103281004c0401c1c0c00d03800912540b007041c403402000084000062180c503840f0b00d0040d0641610b82c3c00e2100c19251588121140c0d80d02960800144d03000c2103485080402400d03d07500082040e0360780030032f0b0341d058405103048c4900c2042c00500401c11980c01c0c0040303c1a5501040e40892a016001d0000c0c251501d0025034502811000445008150784156228030402010710100001c6010310000c9075511200440240140d00c560084812207401000841e400340c18410a190340c01d90702c0e55203000680a940c422500d0907211089030080150352250400035284810080960400702c148084100c0401c1c440030b0031144c0e9410100b0241482402225184 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 31819681 1250 31818431 31818433
    0x1061704020f0a0e1503150f01050d0f120e040f020406021b031501090c021006031208090f030724020a08130215030403020606030f030903100510080f21031b0903010b03 74
    0x3c0c607245c134001980002000d051032083c011410f021100300f122040f42400746800e80610940e0f60300b042c0c01e000511b56940e0083d102091142e49210009200c034031302c80140941507882c0d49681c0c0b03c101c1803000b5110010301ea101881d00502c814400241d0010b10000c2c3d00040c80300d40004200c4440c08282000640c4d0b12480300f410f28440041203900e495000744510b10b8803a822140c03000d140b6100c801c1241d42d203001c010070b50b03c07540e141401070601c580c0c0c0554100b94160241c0d607040754a50041c0345075601c4101c01b01c5403c031a245403102d440c081d06032114130007005403c0a602d0401a00c90091544c1c00c020110f26a05011602260a44d242c2c049108071006413181d0441e034034101801e01940d2508101c660511910402c0142146510b02200b030b95880c4901070000c00307079030b0f000c0001d50010b884000c0090384000300020b000a040f03003003000b0398080075620101500c0906040c0c00079402c60f0003000b2410b030700c2d40802c1040c0b00360071940411842c4480008a002501c2e45500d50003e0f0146c034080c18107030b83c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 31820931 1250 31819681 31819709
    0x5100516050d0f060f060e030111220f080c0a081b011209050102030403030504060f06030201081501030e03070f0b0108030403050a0308040f1407090b041802090405150c030f01061704020f0a 83
    0x2c5445550700e0003060f1b640b0790301d50410b000e100104040c00c2e0345c0c2a200100c0080c400b0b00407460203503000a026041074a000c00d511032110f80303410301580514007503409049298802d021081441c1800e480603000740c030a440140c074001c601000c880502c07032124407040d0b041044000355a071034018a41c0c06080004d83c000000c0d95241460709006000d0b040c00c0c0c1302a03e20b18a4a50080155034152140c1800c40381c2c1a16141040d07910011503083c40303002d441803103050649403141c0d0300380c01d4820310040451610503d6107407107245c901c1c1000d45030100e05030072410342503001300700c18000304200007189600381d6030514000c035185e52a4540305040507140c1c0d40060036409401d803c44044031001c03c80d60241d41c900c2c001081956401000c00040c0d601c0b015540105801e01079044001d804d18140460344140118100c030740044110850607081c4104850403d42c1d60f202205001064540c10b010324014041e9241151408601d94070540c01800c001c0d000030312030451400402d02d0354988043d0303000140102d001d81e450b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 31822181 1250 31820931 31820939
    0x150705030c040f062a020d06020313050a06150806090624130905060703060f09052505040306050c0309060f090705030a0804050301050f0112030507080906031305100516050d0f06 78
    0x30010b41d000782c940c030190f172440c41060b00e07000e07009580f21115600140b49030640c0b40683c075403400940c00501513075408860b11524001207002040041180c03480340720b0000d80c498017158100040004c94204030b41c10b40001c0e0501840344000102607810000030001c5c1c10414000d604004084481c0c2c0320340a0300302c11034103c200c002c41d069a10100700980681c00395245a614000d00310101c0300a07026098800700486010302c12640f1b940e0240d5171241e010000c0c074041900450a00d0010440c15500d280060400a02401002914020540c01204a0070102d085081020314551140e01c004c01e00d11030300c1040d000051702c0350420030040008180c003409860601c8002d0030304042c5d40d802401b800b4083e609042c0480c09101d0400c00080c1241c80d14400d060010b10207130740840e25540559425a40541c1c1401000d4144d030315400114003900e081e04200c1301581c082e2500c10b05008003004000482c6142008000700c291481c4840301d0240f4903840c1941c0d64010482160008100040411802c5031400d170f0082 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 31823431 1250 31822181 31822187
    0x4090c08070f030204051e190b07051603020105030703051005060301090e0114090304050d150f1b0206060306160c05060403020c0108010f0803090402030705070203010504060f0b03150705030c040f06 87
    0x3a0040740140c0d075410003a04080410ba050f0b00c280c0c4180d5402c4003c81151003c002000c050422210100501c41e0210150308003026050003410303041540388400c0002c1040802004201e010840020242c2545100d0315507000a00107000c01000c100905440c0c100003540000300c5400744002d040001d0074503442e56164080000145009045031000b036280c68400c82007030044500d8144503021560041d450903040c01c06011103241c4070001203038080d031030021f00220011180504218500420400100301c5000d1101c80205601c940c00c160940d048170003480741c43d440100f0003e0303002a0109c113940c092481e0ba4011240300501d84405801c500403002880201640481d0010050300240c1c1c2d40c10084e44c032a9104513520031103105071425548100060582400c15070045c40d8000c5d0141081da0600c0280c1d004642562002c030b6040343d1540c2d65400c80c04080030305102e05541820160010006952440c01c1494001d4018203981c0038044040005940708041c041110f0180c02130484000c901c40c0d071000c001d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 31824681 1250 31823431 31823447
    0xe011428140303070b04030806120f071514030103060902040c0305041106030c0c06100f060908070303030b0d0501020d050108120f1206210d1b08160203030d06060509040b0402030103051506040204090c 88
    0x151245150040c2507112401c0012048030913000070bc0542030141c0ba01c3d40070b000c4081d24240072424440401141d8548082c03c002950003180a001c0c081407001d003d20401c0704680c802c020740000e041c6808107000104581c2042c0b024021003e40b411030796900d03484042c1006005504c1440e00900c41c84081002c0c040da8201c0400454031355920140c0403030303200c09090b228002c1900814000e075100d10000c0001c01d109030000f10191002400040301012039484030380c21391780725008481d242ca440b1001000840c0042020464180c9400745490910304a03c02c501c04611455002d001340708262804200c02e580c0c0e441940c90110350300007080c801082c20041070b80d2140503554118012a80003141009184511001e80f11442d034801c803058546900c070b401080ba0a21808d90503a0148002d01c110984a00684140d8026044940b62251140d8807501000181e600043c2c1141c041e9005000401c002000012980402d2443d800304465940c0c0e4030010400038081c60b41f01100c8182040c80e03401c020f681050705 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 31825931 1250 31824681 31824691
    0x304090615021f0203040f0b090d1403060d020103050406020f04080601030b06030a0201050910020c0306010b0c0f19020d0303020702092d0603120706060e011428140303070b040308 79
    0x1100142100d030010581c0c0f03503502040010481c00c07100314a180f01d600c099004640c0607119a10b4080d00b1051501c4402d045c400854082055902c0142c1550005401c0b0310102e800021810000b0315504c0c003140400c0607840702c008000c0c181610b07940030508100254050b01c0f80021251a403603112503a4808150b40c900080c4800c0e15951451000701303059050204001c03190a40603101c00c1d03e8081007000f0300c030780006088000d41c114001c0000e0f135006544c041c0030542c0281485d24038651100070a082203800e040500071181c04651210100740009010b40000215554048802080039021810260f010784100b000003540040400200024035070b0100c54801492818450904140505281c4641c0e05a0944060303626500c800100c10030240c0400061840310300c564004a0900d40e200c4100c031090500fa00404881c1e4001d80c000001400c02c007505581b20094483d44140c084050280100e4804a5000b1a114801419a40c2c80d036602d080003219040e550090700c4c42e51910303241c01d0040a150003550 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 31827181 1250 31825931 31825949
    0x9030905100201050103020603010314100c02010501090b0a0f1505130b0307080708091c0507060e2104060e01030f02160b100b040303050f0a0c140f010c050a05030a0903050c03040906 80
    0x1c0300840a105109050680354080c02441c9035034207588840c0109251004a90100d115608940c04061141d014a210040a580000c652941043c24440070b8809000a540c060404c80c3c504110842480c50b10a04a41c07804008046044500100310b0b018803400080c00c40540d2070040010ba00f8211000562081c296640c9100d00343e00d038814111407145054550070307a180e10191400700350000e8402c04c1122040181042d615000d4170750744080c26140c640100f00c130560042c583c4c544001b80713540c1380c01c0d8484800c40c8060b85001e0502002030054000d0341c954a04240ea51070030691000314640c1240c05d00e0240c906a02103002c9146009601c501c0100c5030300381d03481001c000020b81d1600c03103c2500c0c03d0700d605440301ea00308042640101c50640010301c0800410040d10070043c041018640040401030520001d07213500f00b0851041c81c02d40c2c22605001c41003201c2000007030710181d0702000b42c90304840c0007800803400301550300302143c0c1400b0345034000400b4000024001194806a444001211a050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 31828431 1250 31827181 31827199
    0x60a0b03041a07030e0a2018090706050703020a260d15060219020402072901031b03020a05220507020309010e0a0302091b0f04090b01120c120903050405030109030905 73
    0x60045043c0d4100c0012485c0c40da0110340c0c1b07140024484000110a1041007024101903c003450000c0c000240c5451621a12420001407100d00c510038401c00019050350308100b841d2500640d4001c0d903408010b2005002c1c8015604698101c104a0b04600445d60501d4075660700c45501c1103140000700f1402c00700301c1082d10346000c00912503001107401541c0840c00440108114145d03020700010354070116040300c0c0c0040c50301d407541e0f803202054114601c40740740090562540d811440d0140710280c082c00341421843c0c460100b000180d40d80000b01054510503640f111418034103203000c2420104d1080d441038040d042c1001c000c1020750010150080017400d07038406580d0343c0d083e404c7c02103820780c80c08069002132600000444100101e5090629448201e00180c90038400744031113040c94000e50821078240d42c868500d041c29682c000305107809124413031b900700061440c010000d8001d0759010707481c4400743d40b82e035806410b050083c000d0b940141000f800a01c0210090b140c000c02217200303401450320981c182 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 31829681 1250 31828431 31828441
    0xb010305060108040804150c020a06030204060f0806060927040506100f08030a0503190e070f080c01020a0210020a060e07060201050f0c07110a03060f0e12090d0209060a0b03041a 78
    0x100c542d0f0b80140d81000901e031501c2e040c03010211540f000d45121106018030351002400588410440400800b0203a07001601d40e403c20f0030060400011203407500c06c10405105110072991070f0300803120690011188240344120540f0f482803001148081e44024030340c10000c00051020101d00e0912541a034212003015a484100d480000303040da00800c1a030364014440d001d0810701500041d9004005002c00c40c6c1a92540340c010020b4034a4401250102e0304903807020880286455480b0000d403404c2000741400c0387d41c00c0c0000f5551031014002a11500c1e14003e030305c05882c0280040251540c000000348541c0000d078958076650021441248015840e02c000035889020102500380a81c0c03003080100e01d006410b4030340c64005000d0110481d841103051500100162551190324500441c284d00407414009501e059420a03115404070320040c0302c20019080c84d551403c0b4068103035a4129501a903e407030b030310049001d14000e900120003c100c000140401c2c080e000300304014802182c00e03121b000c3d82c2c0d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 31830931 1250 31829681 31829687
    0x70f0501050a020f18030f070f1a070206072402040f03051b0102060c03060103060f0806150406080d14040509090a05010501050a030209040303020c0c060a0f020609030702010c140109020301020a030b0103050601 92
    0x18200c0440180740017480045400000d0178001d500fa070a00404440107480c0c000c13442810840c1e0380d070024140040c0c80800700300d5180401011000c000150814500700f116540208150748240d080c01014018131700f21700d04241c500200300c00705880006000315200c07615860003c50b18080750005a500e80b1402034480c0049a07601c940d4a8200810b038050200703601e44102100180d00b000c0c0026051649501002c2900454251910b0050a014008168a0030120b09074018103450300045070040d410080280240100010040f401558510703111003a1a200d055000003401250060760b4803e984405010801c2800102e41c1080b5020b02d0080021341d0342c8a007001060011444000e4000c020480044c000c04c0c000d42c042e08502d00c85c50269900400c7e118005100d45e400b40950714007040c001d04070500c0007541084a41c0e0301040030801145003d4064001800b114001c280050048803c98400c0e06042d5081d04840c41e555400782c000d548601c5490f5010380508822000ca60000c2d1400c0e00158103984 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 31832181 1250 31830931 31830937
    0x70b030408070201080712090c05010e090106051b07030506070e01090e060108040308070c0516080f19020f0a1e0e1303080403030e01230103060615270308070f0501050a02 75
    0x140c01940e00e441c02c99a40d0064850040041c0050300340007004c012070802da07201d8000d081c000b07803045d4030844e01c0a0a000001d045861807400c4240a40740210040c0001900101210181e001003800340c01c050b00c5418107589003500300c3d0030003403650041c20144503803980c00c207a04090412098845240c03183c3c68290720000740f6400c442d541c1c0001da0902c0820301285c018810150480204d1a0120108815884881c41c020b468031810b2843c0e4a02c04081203900b0080c404291512458009008ae500700c940702c0c1c001540d003800010f4441e04541c20700505a507500050f43c0010725201c1410124840c6034900c0d450a100144540204002c0070400165003280b61003c10b480203505403195070554960b07032021001030040d070090081c150f6840d07400c4282e0322a0f140c030080c440d0300b80c0d401249040d81181380c45010b59132141d01c40c0821020f0128040201c2d5000302451868135600d861481c0d02d0100c030007841d6116400c5a20203082041e0006201c401e02c004444441d48440c01140240083e0300d030703211000201d01c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 31833431 1250 31832181 31832183
    0x50a0b0a1b08010302010f0309020d0b04020f040207050a0213020c06010e0415111605030912030705100e0307030503070203040906090902090f011406090301020c01051e060105090604060f02100e010608070b0304 92
    0x600b1910040c001036000c2c0c1c40000c41032800b8a8000341421159001c0b03000610032481c1907512000c01e5081004600c0e00c0359140305821002d85040d403e080c3c6d03554680d590b684070110000d11071300d070441010b000c0d802c032541030b00e400b0703200c3e4012583c9070b5949800240582d4420703501500c1240e01d00c4001c0007004260b0140341940200e280440b464461510000c501d42d824144085070b183c001004001c0107035982c81c0389202048081c80255941c0c0e0740301d2414070b10744004103d500c000b59040c20f140340c0d003036000802a135102a401d420001d603070303540351903089003140308980050a40a16020f000b0402411540c0046200783c42a102801503450b90b40405002034024400e0340b0040340f003600405402c0c10000702415450784044c0000d424180c5000b00da900799642180c001400e000c51082c00450703a81314000050b004142030800703601c2d0259070303c0410300510860044c0000c0c00b19200c0500c0d0035a20030400d0310000c0d640c40c0001c000c030984004209018040d00e01c52807816200d12500130802d118120300b103030302417 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 31834537 1106 31833431 31833437
    0xf02040f18050c03010614090405010b040302010324180207150b090112030806060a180801021b01050606040501230403050a0c1e030605090a050a0b0a1b 67
    0x121a0801c440d0080c40c1410280800e0440003812641542c01c00d113024061031f03e600a40c5d18540c490009903942051070034000280014400c0c001e40190b030f200740c0c0e00740f0841844c00342a0a41584004a00020b4802d030041040110202c018106080011040150a007089074848042d41040400d0000070381740ca5082100d00da1070401010343c098003001c041c1144459140d1001040080c0c010400c3d409640d001880e041d4050042c00c541010280b0503600c20301554407410224040c0d0400e1000c40346021000c0402000c0e200180540741c490b03080a13000e43d080c00e1a1100448540c0d04008041c0c103070401ca8070034079030b00a10301d000070000789d4060340c02041c82205502e440c140703030b8031207901600c00490000180780682c80920480c0041b01c0d0400030204958446c481c0c1141820304116004100d40300f4400b42c0e904200300124000e11460300d160003084805d0b10414000b12602009240c0400 = true := by decide +kernel

theorem cover : BRFrame.Cov 31654681 31834537 := by
  have h0 := BRFrame.cov_init 31654681
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31654681 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 31654681 ≤ n) (h2 : n < 31834537) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
