-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1486
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:12:41.183969+00:00
-- url     : https://prove2.me/submissions/96832231-e755-451b-9446-7a3c04370323

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 267086330 ≤ n < 267266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 267087580 1250 267086330 267086353
    0x10b0f04090602040306021204060501060206162118060501120b0403050304050a06050103030e0316140f010903060c021f05010605090f0303090907020303011d242206090605040c02 79
    0x10740029103049403035550810000c000030b0a584060591100602d0706203480b23280a103018000c545042e000030055521500801c01ea040e01c1c860140341e44082c034905001004103443e0400610841c030312610100354107028801640d1841060702e010701501803201801643d84e01d181001d401a0340030000ba001000c4a000100400e00400c000c582061040b400c480000840c0e84a07142120002e030022000107080910a251620f000c114031441c200b40340402d10072043c541400f003160503200b907401600910b50307020030300416070007003407080000c5400420501c030140d441d003002520fa401101c4000c00d51066100310803549146489a00d050340c1c00da449292401601c00c0400600822a8007410b502d031108204054564482d240428042c400540095440b541048000200b1100808080400503044e4041103a042901000c0824504072440440040948000460200c003100034009240b090011180c42d0000650350240044546030001000156180d80400040d05c0e981d200f0342c001079102a14070304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 267088830 1250 267087580 267087589
    0x11270a1514031c0203070c0f051323090304030c0312030e070e0a0213080d020607020616170402040e0d021c032325050d0b0306070c0f0809090412030608010b0f 70
    0x40803c10a0b004603030030441c03144d5500f695030340f00b5040220100c11810042180b8140401000c020151028040c01481d80c842030351035200184240081140a8007000b10350200d4041c01242c0c003442d000103000c181c9640300d007001a01d000704101003000007454012400001240400d0060680300d1020070032800d5204c4004a801035000034190035000d011544001039141030030040c86402c00d007180c01038501e07483d0130707613000e4100b0100828004686140e103140d0003446074040b2a40c0310310210709040c6600c984036800850f000b0a0ba1450898240c81007a80c00101e4640008a20030414a095030000702420782410031400e84e2848080713111140f1a0200821000440c0d00201e544100707400c44480c00d00d150b2030f02203500c2e03110550351a0003141c1c000070321342921000e5024808660300c06070020b00032810f0900c001056010400d0014203400c02a0603204c04020345042101c0e100b070700041400c00d150030306040a200c045148620000070134580301c0001004c100c18001e541e1808030003410710074000340d64001d01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 267090080 1250 267088830 267088873
    0x8010503060c13091803030f3b0304080f07051e060c0109150213120f03050703020f01090c05030f060c03150102010f0c080414010911270a151403 64
    0xc0040c184032080104840c9101d1040c176240d1421401e1007a00b041031410003908540038603000c1071000d400c00c0c40c102e20b0068013800c00c01071420103213501e01c00c0d00201700e040d509440940e1100b460b03034000007030002000300d800140c01d58204000710588980341c2d80c5008101805c0b40362800c11492940000e825149440c01002808005213400004600203140381d81710140c655951000341c0f40c05d54045528000603a00422500241100c06010500c0c04429160100040c20481c401000c000300001c6c10303001c05109000648140c07084c40024000faa40600c2e191960310700b540200c1740644030303504004911103030001e00c84c2d0042d1003c480041c03130b580300d406a44000c0883d142086040d5034032102e20300c0c1040c0492040c044499504d0f80c50070f0b00d509203840d05000d012046c4140c4007148e070402041c04081000c41807202e01d6008219000500310300b6154016220701c081da2000940808100d04200120100e41c0008800d481103082103400152a444031000c8814114103498160344643c082d1b00c9058044003d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 267091330 1250 267090080 267090097
    0x2040f021201080c2b1b080705010201090f11150409020702040c020303071409120610050f0612060103020913050403020a0605011203090b07111c02030c040221060f030f030306030d08010503060c 85
    0x80001c5c0c0700131901e9040440c000c000b403a00c03250010380c5080024000901240018180034070080c024460192154158503900401c0a020381f5404c1c0041903ca90350082c18804285035840b01540340c07039840c174000009400c2020107a0046081009101081d413010044034031500880e120041030304d0340f46400c041c807500002c80442e00300d411400301c401414000c00034540710762042c041d0314030f8050034141070002007100f8541050007070b0000d0061110000c0f04131240ea6001000b8640142c45100100000300c12884114006154516203400d000a0560128041c1399240c05808144101d90740c07186041d104241c442c4010300014004201401006907100080c002580a00f911400c0c8d441100c5c001804c0145000d852114082c6c43d035580c03411170400340545050345108403011428102040c20b05c0c20409460240d00410f442004001170b039aa450484504004c00e010b01100e031701c0010395404a649900586903188030b0321803612500c08140c46110a00d06a0303001802a1005898058901d0000d4200001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 267092580 1250 267091330 267091399
    0xc010c02090f0a0f0e0c03241b040e0c0a0e150901030203270a1202030412060903030e0303010603020d0b040b01020d0815030307080d05060906030c0f0d02040f021201080c 75
    0x6841c00031909802005c206500020280c4400000071041502e841e048012190800700c030307900450208061034071410ba00034001c010440c001902e032a401d00c01403103a07401c0b41c254880940240708007200100050080203010362101c001c800d805108014002c014200104481300d4100400c0302d041d44a038000c0c542107074140303200c2c00d0781c055210fa982082d11003886903c046607000e01e4000081c0070702000e450b0201301a1f40040c615181c149441d203103c14030300c1e00e40075200701d4031010340740c0805120b50300055140f8034420941c2d44070b5071204002000b941c042c1c0c0e141e504c09800c064550199240c07600c100b20607030105070010305503600d660f0703002d03916000c0060501e54860030701c10a850080e01c00780000c0070f041d0302c01e140f85035a070346c19055141c044130005030916002d184c400d000c00c4036603100010170402c0084110303042149400650005000300401d09030082d00f1070f0504110428901d041d8000d805142c0325520820000d0303880708000d980d14050121010350081c00d1023488440300c889003409002d941d04292 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 267093830 1250 267092580 267092591
    0xc0d08040503010c3b09041505010b030105130e0703111c05011d062a16110a0501050304030804080f040e10083c010b1201050601020c010c02090f0a 65
    0x3001a003103480340813144000c41c02003000c0401c91141452004685103c0c050750b02c0107402c4503d0120906141d90303030614082c2c0011004942400f5165840d03640e029201d281c1130080d5a160a08403220f90828803070b2502401c0c1c10082d1004000140c0a041c0700c3c460100c009140742d518640b1004a0880203052080d0400a00440012a00659081806e4081c0102c1c000b28a600070600c440044890303880551440d500520180040640b10705291100e4000b1990b0307083c038030309800160460500c2031507010420044d180c0003410030050801c000d12481c40d412244000c0781a919030040d02e0310720040754000d0010b030400c00043c001411038005071141c070380950b06250501e5100d12150300211800d860704101201a04000c01100400b0800b035000640c080c3c42500c0d484528141c9891071402050000140c1075800b003500c142c080742580140c030740f054010b100c0740340f000201c42c11600030b15098030401d005004500001101d0b501818110740fa203030740600901c040c2e660310354003440704c114003402c0307044840e841c0d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 267095080 1250 267093830 267093839
    0x6030203121201050f0d0b15100819021204082104140f03090612061906090602010b010815010c261309090201050306100c240e0f0c0d0804 61
    0x20848004840042000700340d5a401d4104207540b0040168042441160f4030210310849417078010f0380310201c2c0e070310140b400394030740701d9040c24240c03400c10514058000382001c4c2030700442d0798804292400344d43e041202c64a4001c81a000030140d02c5001c4090240314070b0000410001201e60000b44060007100b6032610221f0050f0020300c0e4909000c0d10291540507801c85410400d8100307000910380310f10304400842c030b07181c0e0000c0815140d028080f5460700d40d00c46800014015200e030b903c0030503901a83c0c084c52070056240d041c00b4000420768088c1c0c00056107801040c03034055008141e018064601d000c9484915003100d001190500003604040351600c080d082c030f500001c0c00c410314800004115051458a94800501129848501c0c0d4809848942001100000750340c2103c206d0341c200105541c414040400d40c0c0003540e41c11410fa10091041d00108003180500000d90b010115100360034100b84103858200c10042e81d100d1950074122269000348000c8078803403510b641c1d6842c1d400c1c8106942030030640e64 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 267096330 1250 267095080 267095083
    0xc0c12040902031504060612020904090204051305100e1c0509191d06090c130308070f0c05030c03060a020c0c0310020a090e160e180901090b09012d06030203 69
    0x1907880309901d5070300807040c03002c0e001100b004140204416507041002e82d24180d0001c1540c100322200c40c0c145a80010f15030181c0d05c40790050003486030080c20502a90404195555401380e00c8070b82a41c6900031001c0141080304240160803843c0744540040814411410f20786034000c004141460920408200a6100d0f40f18000c6a0408500300c000001c142c3e442c0106001441070342c0b03071400c004410305400b00b00c450b0761501800398101402d00341d81610b032103035003140141da041d01d40c0000e00800740200ea03c01c00c0044886014079014441d605505040c0d5490090545d0703400c42c0c4040c254580c00120004039410310341d9000d4081c0c094901e045a01c040e1440c000709050465211a061480e40c000408455254012054400511400405205900d46141c5199448082106c11801c00600400750407032a603440440450b48264508601054106030b02041e00070f00980c2c80071202610010300290308030b841803180480d030808040600d0341e10034020541ea00b1003070241c84080f211a59450002c009030702d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 267097580 1250 267096330 267096337
    0x3010e130b221b15020f12070809030709091506030803040213060f08060a05010b070c091e020c010e150c070b09210c06060604060e010f0e1e150406080c0c12 69
    0x24800007041c07640c14001103c1d45134200a0068041d50b000c40283c8003c0300c400288000311140e25406a51a080980b804071018481c04809907818401c101002c60300701015800030100381c1c812000d01c5010a040b407034900a684a80c840a000b0000c1800018094103001e450444d00440440c000640360ba1107405a1f032000302c00350050308156200030200b2914080500c50140075014284a403424840381d07503580860640c1c0e0740144081e403601c42c0700c0d003417441ca074500300808402c0844005644078480d031400d01780240604a8814114403401100040180d0000ca1140c06440903201a61030018036454040c0c0c0707400064400340c03043c03103040d10f00d4001d44030b6000004401c0b84403070103079540d0301d1003040501d00d00000580b0151250790104000c0001035040b4800001440c820300307010400000740c0d44280d070114038041030150454400741c407a001802640c0507004015100b1240080f03204100103845a580c011401004082901c00c7c0102d0740800342c0d003000c0c18141c69006c00711001c5d0842005900010340 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 267098830 1250 267097580 267097613
    0x608190c0f030b030a05191b03080c01050601080601050429070b1602120315010e150405030d0504050607020f030f030408060609090307030905060c0102070206040b03010e130b22 78
    0x345070407800345034103915000d682d5420b10304500401d44104291649504c1c0d0130600386e480c03204118502090b0070050100c1400c0b1242d41505000301d44147d0b0303402e0403501a03011116000c250b5281c50006021980110203480c014036040e500d440c02d090a0055241c40008200010350020088a95040103900c640004119180c0319681c0b40c407090030310f2026040e80340003072003003503081d5046401c0030289907003104140e030744c00b42c2c1c5080040680c074031003401a203e10041070a01508607191f01080380c00300b80300030010801c0302c0f07080c0c089130b11107610403400f01e0b1030740114010160f209104103c1c01c0094076010001c1039141d90000d085c1c4101e412501180c1b031841e0b020354496401604500b040000501c1c20390b01d50b0791300100c40300265280200a603030084c07170701c0c48a010300751190801090300740f0306280942c10340303a200350701804081e0b03101c0d2141d42180e01500244a055030300e42032500050703443d952071101011503a6000002110716160042c0c0403448540d03003410103d41c070a06980c3c0501043c0b1740781c0d80d401c0c1342 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 267100080 1250 267098830 267098837
    0xf0a031a01081b01390309050a0305070b0a090b0c010e0705040e06180708030406021e150415020904060e070e010305090c010509060708030106080108010605030105040c0608190c 78
    0x2224041a5a004818141c2c80021640c204a50076180866644841c900b40c240918000300c071416a6031100d1501809104516401c0484400a495540d21032039809280303070003501e480b0710706540c6400b04898074046000080c003d03001100c04225821203c80500380034046824086540ba80301d44001c00700d07812546003229180c0d11840000d50102c0c0901c0341034080c00040e40d0030b20500b00d03070840c8690740b060060241d40b5659201440072524903014800c15001d0090001030b80e998035601d00c1c0c0259544e0a000c41b00045201f0500d56103245040061407040501c42501c0c4410507aa4a880b07101c5061030340d800f11755241e83c0030002c8104c01c1e6124860940503280055507960309040500e002410030040140c95410b2520303100c00d2181c00c00700064601140f80007403070b28540d188603007000716a00d806036200c0101081e00100c000300303106d42c1101005042e00c00180c000c0010355034035130404d401c1ea0001d0f680548203508510080c40290310a4010542c40104080300c8201d48003070035003150032914101c1409000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 267101330 1250 267100080 267100103
    0xe0c1f03060f03020d20060c0c04180b0403080c04080106030606150c050c041e14070212120a0b030102070f05010c1706100e1f08060a090c0f030b0f0a03 67
    0x596014812140a000015502034049040d540480c1180c01c0c5c242c00039280d06801c6407103829a000d68540301e1a2030b84003420013600d401a90503001c1d9140304200034140306d5810000540f0400b4030502d40c0d480c0c02a04540380c203449490f0340e2030580301c0050140100ba2490f4040101144180090185400851050200180302890b003001d0100100b0f844400004120308003072080c022910016000c04060021900040d13004c40b003131603a41e80a0009405c0c00070181c1003d0340c250518101006c03041c4103008a80035542003502410b8084401c0c49030b180502180102d0f0004540001882d40c81f000e07068002600041c0b4109858450010485070b10f482140d06a460b802d0301c01846500076164803100d41d1017a02503100341000d0000801420010350500d04014142c200c1407259904c0842c1041e180d038150b00c038000f8041290a000745141801c0b030b040c5025201442d00050700098520420802c001d50795655441c2410041b000c6010b800306c062599480314080781c2441e01c0307554101c11900210300c1a03419104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 267102580 1250 267101330 267101389
    0xc03010f05030c0a0e13061a0a05031212150409050f010f060b18301207030e09040302030d060f051021050406021603171501120e0c 58
    0x50540007030304042c2c069044502a403c243e192480040190b03000000a03030342950390f074800e201c68202d00c040e02810303590500c0c40e410481904403014a070344620a48045400c2503d0310103266440031142d10f49a18140200002e100c0e42500070a603a07004640007401e0112040c070540043d0603500c00c19000ea559400c6100c030081506c00c02d1003146c56130743c00594144000d524081005586001c3c1c450404448800900c222801d07641c1d04030794ae80c442803c11402003424a411a05034071513444000351007401d10403503003003130303101494181540c8016605a4950090441c0d940502540c000080c100720150311040c40a10403680c6a4041d25000c2c010a900c4606640d142c001004817203c0d04030a2901442859131001034000348000d01c086824403032100120712a10b4500e0448001e101d4080b003000702000c0c020f2100101588007280596414404035003005e40c1c0c59900592014004000c0300c07038042004641c1c7c04807004541e0300408a0004c0c0c1d85c0c15164110384000104031075540062890f5034800e0510788151 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 267103830 1250 267102580 267102599
    0x60103020706021818060a06030f0e030a09091415120a050304081b0909030f1309050a05070e040507020606010f05070c08030403120e010e060f22140402031605070f0503030c0301 78
    0x4010b1312040003217102d203050440100b008650070b8068a8201501d410403071f00310000c41d40001040c40341d10303c1103d07501d07215020b0003400c490640c003500041d82e0a041d0020201107070001218000c0a0035143e500280144030100072070720b80c51500c5884580500e403046000304205201400080c1083d1010f80002c030a181d20591190000300c429030b105026080511021000c00000e0310168888818081e58501c2007980d0903030b03ea00154407007011607003803c04000c0d0200b5160002405a03403651600e15948449108110941d1000c9480c200107070301410004170b4541c440c003c502440e10183c1489882c2c4079041d00c580c60707646440c0d0003d4805900c005003c10822071000711000400c1c04504e400746007000c080c0002002c00620a00c0c0d00d02c40d02001c10405060081d2104940c0010030000340d0942c4400c4005c5110941c00340c030b2240a00e1004502c0000000d400e150007200d10070140300300100010982445c0a40e85c42e0009a0151a0046c44410550000b0b10800043d40901e01d0341c102d0b00c1c2c07658544820310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 267105080 1250 267103830 267103849
    0x50c0a050c1f2018010e010c0b0406140a020901080606090a080a0c0608130b070807090e090a02010f050a090506160b0408071e050a02041d0102040902070c0905130b0601030207060218 80
    0x8003e880007082890341d48840c00d0101c0904000900e003c1800e0741c21200100c51034048046c016220000c000c05210400046902c0006c0b0041001402c0b0555500c0703001a80c100c0c090b100403680415008c1c0700081081c501200180b5480030001c2c08241e015444050b12443c0200018048034201101d60b010f225180e08280c140703922900140c040c1c81108050b80c0c41c0a00c0c00405445082800414400300346001e0007840305c1070192a46030442c1c0070a1429545542eaa1050300d84240d01184d2151400a83c035031142046450704510390f190b020070700e898081031100c5903000c22149203035007080c2450040010b2154841303a0003540a814229100d401e20304150340320040404003401031202010b0120001000820350003501501180e002401d1415410310348e4082c598014458102c1d4400030b80850881050340c0a062003c0c0694010743c401d98070ba051207011074a065401100400c07001401c03000040348225060790003138042c5809400c1080c42d0766080140c1e08580c400150b03098a031103d420603400d00880b00b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 267106330 1250 267105080 267105131
    0x31206040b0a0f060c05010912020105190c020705120312090a06050c030114040207050f01110a020105010b1213080f03040b15030c1003020901020a0807030c030909050c0a050c1f 78
    0xd0581d40c681902024214803a105102c18010741c400c000061060079446117580d540c001c10800402c1a103027000034001c081c05c03140c2c40440400300b9480201002d80380b040780c0542e9051b40043c005942040100411203508181e0840b0b0707031208100d002e805820100e0454011852080180b00c0072a0310702d410426074400030304801c40301c80e0a100412601c2c0003034200c1c0d100d0341c0c0c1c1035500507500e981c0c600b045030030401c08603032801903036003005108000c0c0255880186954501039000f00216600d40f5080c40540c07148042c4c01610002c20004601d200f4511f2a8200c9401e20038a419441c0c21400582204160011242a280c0108a00030094103122a200d0721017010b000301d000e00755621148000844c1020124442410940d01140c10002d41e402003260301911038002100a445607411714008088002e80c1a08500040240e20000356015090050900075081e0b04080d50401c40b4108084031140c01a505e501c90510650340013a01c0d1011400424090850034036001c106e015075640008000c4071030186 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 267107580 1250 267106330 267106339
    0x3070503180310200a11060f0a0c0908060c090a030c06030b010f03020c06041b091406030d020609070b030703110307020a140d120c03060e070f020c090103081206030708031206040b 79
    0x2c40140004a80c0c030184048884403640c07a0719101905c5080701d10b1040c01708403039410320900090010440c40350030b4481c4035000ca0b80091107540310394142261018028400c0031a581d1110012481d1030390f8a9000c1d00040320083d009144c04c039a00d84401440c81681e500c90300100307030380b0f0407001d0321560b204414080c07299507414150b15028034101025a0748000900151005001d00b00001e0400c15124441000f407000082c00d019a00040090312a840b00948140703100e48180c03415a028a800032030020302c0340000c0005080803a06d080d042c2d1149a0004002104255646554001920079038000d0760003220389500074039060f040d134500380714405030705185011240d2015968a803030a03840144c00c2950841c0e001d010504080041007640078100c0794014001c1130100f10100001c5980c0081882d81850259080340c4140303a83d40103100e0600401e020152410208004048410341c5001c02e558000340050220b80c4d4091b620710106083da00032100c0b04080044171000d0020915060141c081101812036 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 267108830 1250 267107580 267107591
    0x10302130515010309020402040512030409060503070e010e0c130312021b1c0606121b0e1303030b0f0307060f02150112140a0206121911041703070503180310 69
    0xc0e000c014401c0b030100c0590401da20f03014a4011521107030151001030001501d03002d940b4040742c113619240c2c0c00c04c1c00703484400c3c0c0c641280081d05142c0002c06078111031450030307a01c44503400d06e031480300b00801c01072548540e02c00400080003c03660a5410f00c00940c00303680524210800c00c2030080c1040000e400044080219140c00300d0b640e0b407040b91401041959852002e242c005d5498094007510b0641d02c8003418035810f040746001d0080d990340c13002405014417410490346891f144030100c0d440003994469126460516140700003802540225990705005142e82240d0b020040020300e003c074207400081c002000300c560203030030540400906405045442a6214540c1403c2c04400154055a40942505040c40e0120b0048600740518426240c000e040c07a60345445e030491030400c504050f1403521049418100d030a04182580c0318400d2101080034940385001d28103e403508850301c0ca02d2040c40303070b030004021081c0010b400300000e1620350815411000c00f83c04d4482090705001d17086032041c040e00d0805 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 267110080 1250 267108830 267108841
    0x2100501061e0306170a290606091207060f110c030a02091e10050a09090b040b100803180307050a0608010308180607031107050f06030402040b180703050103021305 72
    0x9481804000b1102510020b011210007044001e44084d90200000313050018648662070008a01481428081c1c0e0141c032803a40b041d08002507c1103002640000111048007182c0c403850310360001c00e154000202002045a102041141003804542c0035030041b51001204480c140c1c1c01541012000e400c290203800c0000881d0b01282d190341400704024400c400c030300c000a00c0240c016070044c403004c09042c5c0348940780c40c20502001c2103074500c0c06204e00c1800510300004510b40385000329609141c0c031a80c1050241c6407591001080c1c840501402441d880e220008102ca00003040641807080c03a03401c0f0b809460900c10285404d20081e40c00c514018034580c074040c00703290b0308041c6050450b50710144040d038034840c0d50000514921035843e81a4030071400103250050507440f18460311485d9108040e84c4003642d66030200400704000a0481d034126805000280161070241e203d4028800081d04c4458040840000400c180c1d500b1071b41399002c42e40c0c480061096050001c80041342400f058800c00150420 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 267111330 1250 267110080 267110087
    0x6080303150105070f0506010807240e0301020f0f030103150603230c0a08012a2001060e01030f030206090c010905041505090a02041a04051503250903030210050106 72
    0x140700a00e01000d1141c0d81d0100c1c1d100d07200b100c00c1190080e10468040c0941d01c0c04030b0720f0311000c3c400c08029100d2a01d000c155403000203a00032489071030800c5040e81c6501e01d0425070702600100307030495055500b070200c0048a14010014800600301444882d0340c0e6040d0300d000c2100e000d0340c00d000760174149002c0040c4005120342e40c403a03800d10031010342005090420101545404080b02c1103c1e00085e14020000b1206015084412801d4030103c0340b00c801b00c40074140d0600d00c1013481103d0002031007002c0000c040d840e00505c29074943c584c00c0000c030b00c1032707282c52000c0b2178802c007a402101e1034064030400206140c0d042c0304094000c1441c10203402c080081c507000070441070050051500c01c1e6580e100501c1c5840032003010074000d080142074200300785081a0808000e41061003922108101141e06103007035007103001110b040e140001c00b001005800c1d02240040d03074100a042c81c060381e50b4442e881855142142d01042090099550708820600354580281000d2101046a4900d030900d030061095582 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 267112580 1250 267111330 267111337
    0xa061a190809010e0a06020304020319030f050c0c03030703050a0807080105150903030c2d070b0301140d060f020414061c0c1701030b010303020c0d0b010e1b031f09060803 75
    0x181c0380000d00794490305200e50042100044c0000c15100307105e40c20042004035005180310340c1c0203c050b50311011119a11090034020001e004000407580143e01c884903000f6405442d0402c0550100d03551484003502203441e5074804801500400c80c0421840b40b5298000e820340da01c11068504401154500404219404030000c400000e465021540c084542c404105585a40491404581e00d207203081d410b160a5041c90038428850b540c000d201d109004100241940454580d041024078680c0b8180592a00103800d0451690101c02c2c0c0d9000d00c0401d805005200014140400c01a81c441c81e0140b600d0040166803100c0e8040c030707018410b20b40c50380a8003140c00d1101c001803001280c20b80103a101196907000f040800203001c01004004000c0c01031001509044c1da00c29000c0f074900039101809c01519404c603400090030110018014024049030f00d1190b42c0100c0407805c1d12586400d8040c0240082d0022158016554401c01c0c02043e040c11240207000146a002c1d01040840d0408810030707203034403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 267113830 1250 267112580 267112627
    0x2d0907062a11040c08090c010219020402030402010e03101506140714120d02030906010b09030304030f0309150f120b0303180a08010c09090c0905090415090b0a061a 72
    0x12140c0ca000018003200c00440709000b5001801040388032408400580b55040075690380620703200381d1a507500c865000288046007020781d81806000d00c601a820400030350f000420481c1000700c0070f00064800c2c1c504104590948215035000b01d15215a09e0400d41c121201d070388500108200a08030440080070501207a802c4d941107101b40460f1400e003841c85241100441d10000c1c42d00000482c095030550541c00f55003c0d949034070a0f0754040c0d03601d80a48149000707280920780d01d904100b02c100005400352a0704c402203442803c011016643d0750402c04514849800c51a021900c029480302c402c1c1d910865410803001500b10403c418055200429070b030b4022202c0010509154100218540d50380034803030801400d40b01c2c000e0104218840000740030801e076214101c0c10705c1c1404494100c0794003c1011000781c2e1000307003c2c043d0580e101d803600c10030341c1000a0780048d45a540c03946280480c20030389203903114240a4102007809440c1c205042110700380c02500423521802404040c0801020214460031035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 267115080 1250 267113830 267113897
    0x12110904170c0114130209062e1214010302030f12031810020721080402060304020d030302270102120f04060c0c090c03140a020901080402092d090706 66
    0x260ba604110382d0062982c0750072410854203807030812143c50000000c0c0e440d41c900c261142480b0707407145001d100305031009103a081d00c500300400103002e03017040c000b60680c07492600380340410750b003032109032000212100c6d004082110b041890046c400d5060402404400e8000340b0004c00c1008010040070640e40400760285480c4100c4107003050720380c0c004200143c901210400700311740d02c0c1c5680c0b034045002c0c0807825004007142c40c00403080a8440c002c1881b54421500942103901e16600d03139003042000c0c402e07008200e060590a20803440d1019045401000c5604603111400004000343c001910b8490055407281544070200510a481403214003618112a246e080880c0f801525140003a84d814690308840c0002c0d1900740500c2c2c42940c540c002c440c65a0784003403005007649454180b2001d0344940b441480c04641040301003001400c020700d0159020f14140b1000000d16025450082440380b84008048000491800e01158071400d2144000800c40b508041401c03410011080845441001070074802 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 267116330 1250 267115080 267115087
    0x230a02090a0b030a061511030a05071e060606030f0b0f040c020c030f03090a170604390e06030102070b01060e010c0c060206040507060807020c06160c1211090417 71
    0x961180300c07020001d015801c03040e03a100c1c60005804402014144140102039201c0381940440602070354640710329524a40196240022180041d074496010010441e9a8104000c2840b001c40302140c0340000581714441c04111030303148c51001026034144041203c0d4580c680050961b40d0742e0b900029820344a4107450206628030009000d070708107525a011260103000303401640340010300c00300082003040d80c1107404800c01902d48940041c420041102d5000640c01080420049a04580510030032080b05108220305100428813820540d801c4900000410b106030042c000600170b120540e6020a003079008500b41481500d0303920020f00107100d0041400155046641264800d03200c0c071b80f46503008101050700c02d644600096549004a0701035540e4000d00401244262049c0c3e04140502c0082d0b00400f0501c0c3c3c4842007020640c00604100c00e10a542c0030004009005003800000804202c8131005100c5503d003018a03441c9468001c051180c80481c0400000444001a1189001800e2285500e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 267117580 1250 267116330 267116347
    0x120e0604121719050c070b03190e10060b04091404020f3d12051b090a0801050106051314030601090b0609030f0d090f0b0307030c0203070c18230a02 65
    0x512907411003d40403088044110030054010004151070043d400494491503619440c16081340810f0f00c4e0059100380c0341301312000046e147c0d04000d03603500c0400141c524086c86048014200c07801c40c0e00100d440c41010408110582c01c0380b08044410001e004000340a1610f40d0000300c04514402110703200c4c102015880015944080254044283d44064074480440c003d030b0b40c1c076400140180c0d6a00051504c507000c554842035008260055609051400d900f0010b5203800d400d507046024101c0e040702d00d6071800601600f003409058002d10417a11603d0f41c440310110701070782e8004590011048210021190205c0f40c5000032880c0c1111112440024619410000104203100d400c01d01c40d418071410100e8800400c0201c2c0190040181340c4030801c245a56002400f844506880b410400e0f0313105000040200b07000790003144003000c991050300e10b40101c0780d450b89a01400c07504102c1849040880030411101140b1500090105518120003480d070954511300351040c0c01045520010340200fa09038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 267118830 1250 267117580 267117623
    0xc0103020f160b0a050705090a2304090c09060609030302030406200d02011b2604020a08030f030603010b04020f0315060c010603110306070f2c0a03120e060412 70
    0x1c21200c52401010802501403c003002100c1042d905a0300c0540342502152910b4001e40c1102c040e5607010b880c154171a8030306200140c4910960101d00c00c0840f480c1e44440c515510f901ca0134400b02c0c81506808101e07800d1072040421100c00b03400000034414813801c14000309030000161000c07911245000c501c0d64101800c0e040c50180c403081a03803007a10420414000711a019003001c400c1b524074402c1c404003614910340440b000c00200c00c44100140c2c80d41101080d2681501c000360f40a4006001c1007141a0340d00e00141c50b41e880840c000c440c1c408044207101103131070203010307072945800c084801794144030880940342550710010b48248070301000504098519290801510116042d010007000404d5881c14450041612890780070310074066038001601160140940440f40d4126a84140c02840041241d490318007403255030760b030a0044034441209581e11801050041c40c42802d20b14140e400e003900203008415406030003445500140028042c82c24017500e28105141c0041940301041228001b50 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 267120080 1250 267118830 267118837
    0x30603010f06061101050c03011508090f0a0302150a020a050a03020304061e020901080c070f03320403060c020d0212090f0d0303020c0f070605090607032105090106060305090c0103020f 81
    0x3001e80c0d060082c00500150001041030b007200f48a8000d000990f243c40400203244824001d96001050030065414000e2250240c01d0344080c004007195400f000140c14240b0380145007004500681c000506078903400880390003d40c0000c5034540a5040c1025014041c2160080c220701c102015400301c00a4240b045580110712012011000031100200b200795007000780d40010901408218220f0126200924002c110390150350082e0207001c0410f0302d59422a5009a0700c40103048409241044640200c40d5032541c1845016043c2d1182c0c4d59031543c07030104180e4020f2203503034081d50492400461251b40105420802c201c281441a0b9501c009100080045007810491034000c0804102c8404150301a0300420109103a0811910621404602d507941e0f40ca0074002c00001542c14401f081090400201a0404500c24101240d054450a20500384c58941070903e1007890f8545d8248a03a1070420302c220b0001c0c2100d864184041e01d042ca0380c1340d41e01c0c2485070079241016800120f03a42d030400902e099 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 267121330 1250 267120080 267120101
    0x40602120307050a0c1b0b0a030b0a0e0402040b1305070503041a0906010b0d0e0111040603140412050f0405270a0b0901050d11120d02010f090221030c03160c0f080303040803060301 79
    0x81ca1201b035200d03c0c00d2026130b0400c50001010900e040c4070b024951904404001c100d4020040d000c1007540c03103600f40000340050080440d00304413480500504084a801100c0c8035000a51720f0b59113034070b09401c112072aa018158003502d09101c0c002840980100841c1e060306441420440707aa56200440c1c5490040440385a24403040d40b070b203100b802e198503031140180101c40b0700740da0034000c050030b01441c00c40d2840203507001030610360817000e2801c420b80260041c1c081e8200e01c1071118140741d03a5202041c1c582007900f00520711100b02800b1209a142e1413100150010b50703110341003080f1b0700480c000c546009810701900d031068455015035003c0006540c00c01010074400b50203008400c038404021a81c4104484466000d5400c140025071005000d115130101144c0003001085220400c18443c0c54072070602c01216000c0c0000c010202e6845400c100030004612001c00613250b1040505180ba000f8060b0340221110032201c50b42000145000000d40ea005500903030340d640d40b61a074800107801003550948 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 267122580 1250 267121330 267121373
    0x9070c050f011416090b0313020f0a0e0711031303020607020f120d02100212040201050a020a12050403020a141f02070305150f100f140103150902040602120307050a0c 73
    0x1030f040b032580004091070307005450b0213034401c3c00e510140d2401e48504085004a1028413810b000248600d00208441841c1c58000b600010940314082c0105075511803d400c61a101c12525041c49011644182c101204090301c1000c1e505009a81480116040ca80c7c800644100004202802950b603103410044178508000c100c000d080b40c691025a40310f4542031440c0000d40138068101c9454000c9000310782c40b520a01400780845c0d0f881d41d0065400760441d40c403079000c501c0f514001000045404901c600ca2a1554542a03102d503e588100210901150841c0c100f818440c10000c10743c0c0c45428105400d001a403100810f0040d091204901c3c0441c00e1f40050b00c24420000402d498051095586000e123004102904495441c2d101c0c200320141c0903c2082c420040c04113080013001d1a1100c2008048014500460a80c081c84200b20740a4190303044a0140c607800581040041d8040040a003c5000000c2085c290318252601408a0160560580a20000b071001900700002c01c113415807204030400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 267123830 1250 267122580 267122591
    0x1b02010f1d030d0201050f100f2112020c031e030301090b15030a05040b1509040303050a021c06050102010516140304021507150507050c0a061107080a11190209070c050f01 75
    0x54001d02918050b0340b00c26410201f6030100e00e194004101880598049840340c0d207806140070102d47c1141c055081180d02c04042c1c110f09000210801001d0102020300d5004254110645003010f0030002c841031a8441000d81802c51005040088240ca04454075140009880c1d030180700819050b00c00051081d40210b400420414800040e5201c0b0340600d005080b12030070383c0e54490b0884844002c528089600c14240c200050000b071003a04000da000480c0d08002d802d04288540c428504002c0d80084903d03151140800d201c43c0d6070901ca00c0c1d91000c1c00d084c008001b07a0000300042e140190500641800040020010342591078007018040c180d24807801841ea1101181000e4240744000343c1219011401e00011030502842542520306c00011013001c1c225501603607036840c00611001c1600c2c410024280300311400700391103101034011501c4589451400d220f1000307090741040d00d11300d03210705010088a401400f42c2c0300c50000315440105400c0090140019003021446c01d001c4940b81e104560034503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 267125080 1250 267123830 267123853
    0xa0207120305031e06010c0209270c040e032506060e01090b0a090e1e0f0a0b04060c02010903050702010804020f09150a05030a2d02060301151b02010f1d03 68
    0x4512610b0000c4c042c04245204500c0548003807410740c0c8043c00901440c42e442c001d8a4903031202d9030010707201800242e8000000300300c020f00c1300c02c4030700e020080e400011003c1c205042c43d00491125071500d4020703501e481a0b912603001400c070803924140907030440490782810018280e01c0a00507185c501c620300003540e0b48401400c06450401800f6009007040e1000140303680c0036014119103900030340040d1220b601e0400700b451840b110300341c084006105140c00840d048074240030001c2d515003c2d0035043c42c10f00e01805e1180c265000905c420f4210380c5800b00c40740101e0341c45000d0b25540caa0911f4044180e880d10300000f4824042c03440071683c45032003038082c461025050080002e42e61419149040d040307a0302e000709500c44625250213040b030000c0176480f90003120040c1414100c11001e075a001080d014940105a0541090b040342602c2503000c0e00010311103801801c01407904086072988080e03502030707034002484030141c68514010300c07070004d03001d0b1483ea0002e004010300c4900902140d07032140700c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 267126330 1250 267125080 267125087
    0x4061106013501050f070e0301060e070c1e0501020c060708010b0703050a0210050c04061404030804140d080708090a080a1205090307091406100c0812040822050f10090b0a02071203 79
    0x546c1c0c2880030800c9060124800e0406000e8502100e8603a42e54500c00e0b038a0030002d07220b019540d902151845610100c140c95139400103480402140203600058492580c030450030301e060000391074801408900c23401048041c200360102c0350740c01d6040c40c05640719060118240d19000760481c00502032410282084400c0840b90041c2c0704880041c0d81d030700b019883c500d075803154038803a502000c2d180a0040200b401503d8200103011000310001d0b000c40f1200d809a294000b1a401051040342e1584000644003401c0c81e20204450180170711902900d11351300b841c3d40382007170615002c410009022010a4841d0b4175a02032145000038696020706100240384d05024240400c070840f40c0342d11581c500c3c40d225030050f1007524804005a13010f00e8030342c03500c50030030a90118600c008004664030107003080501003030380d0f11200001c20550102511280d032410041013040086052030194061407085003c491826030007101002101e0107075007182d507075000300581242000c0c0250014440c001c0000d4050381015031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 267127580 1250 267126330 267126361
    0x2120607030507391509050c0103050f13060605100207080d090609061404051201050a0e060c0a1409090f180a080706051503010c02030406110601350105 67
    0xd903035410009a603075520300340c03041441c5070148403c1825655522244d03030303100b00714683c075401c0c6007040d0400c000d00c45d45c0d140348482000395152121760300d425241041180410101d54103074801d00b4140214038141c4a1f420050754000c1c119a495421f000d80345040c081c60754001c2010740406001c40307205e501d03900c1004e5503441003441107076118030a0510054401d4032500c100000c0e9501a61132100c0c986c0b800d40308684483c0e4100070000c2d25101004000303520707620b00c3c0291407018240400419035150186804c0e080300c00042c0d40480d207821100c200803114903c0d808640382400c040c205035140e540100e03800c9185016007414503030009023210a0041c0141c0a0000e1440f40040704007084800541e181030f2521415004130092520344248403860000c2e000d60440359005d44500c41c0c1c01d00240d0070f00e000070300f034603450159140507030000036043c0000756100701038102640d041c0d07004050652408002d204100b0310940d01e41c54208a03119100710242990402000d05550740c4000d10007414641001c600c03061 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 267128830 1250 267127580 267127591
    0x908030a09290c030c0f280c170d0b030a06020304050d050708040b0a03020d0c0503011a04080312040f0803070e090105030d170601030e060f010e1e01030303020a0309021206 76
    0x10064019800c2c2c22540180e0882c0d02c0d10038480c841c5090301c9510060160350000750003408482d0003480f04025100c1d190018080820340c45810308020340c02130900354185100020403004105803c10341802203040641d200940d1750200414650700c0401c440090300070300100d44865414003c0b12004c2d41401042e0300a03500442c011015207441c04c50390a0281c4262007119030060801000f03100030400012040003a0110f04d800741009442c1c0140480720500300c7d03084d0442c042c04240080014440410842c07035160503172880182c21481c181c00c1c101c6080d601c1c000c0701042400301c40440001810040e048104c92401688184015100c1c01e108001414408004030400d0150107803074000031f81c910f07001078111842c03c0e0036111403004514403075400241000040841d4149a00d030340320355100e00c4040105c144104c070841d000d01440d504101e081382425a001d00400701040036182010003483d1071b021546c0c1107a505041c010394881183c0410f038041c082410000c1d500c10b1082c8201800e448000c200702c0d100b007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 267130080 1250 267128830 267128843
    0x20c0f0f0d111503040302060a02090d08070302060a0605190905070c0f0c0905070f0806210a060501150c0218060a030204050103050309030105063f0304151713020f040908030a09 78
    0x20750340100c0b14984c0c0402c84014005a201102040319490ba42d03008001c8888054a010170b000c040e41c40e1100d06900074081100141d01920400108000c1031084001504c07040307410003501a40c90f42340303021850440c014030342e440c0d544d071010031981030183d900400307200d1744401a81c4a40c002800c056010b078800d886255041c4c1d081100250200384074544a2075810100d071a4840301d03031035080070b020101c22510030441c0e141c0c20080d1008050300d0304001c8070088500c10034000c100c941c10883c03440b0010400703482c1c1a051040389152200160303a07182d1b103100004071076143d01c117041e07aa03c0001490061540e10194220b440d05001100b403107004030041c01d1000d0305400078409600d034001800750103008101603e0003156500c404244030314036071303400200c110407030302a401859101300361031f40c115406544110b0b1103c643d01c990b012603e0704814211243d4004003101096403403d0400c00c224081d84402c028440c1074420311035070195403240d1003400c5e2715402054480d1245460900140100b80010040e03604 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 267131330 1250 267130080 267130099
    0x1209250f060c0308130201091e0807050a060c0308090a12080a0b0901051f03020706020c0a05060a0516030f020c070326070206300c030601030c0f020c0f0f0d11 70
    0x4034010001c1e10041589513603141c1c910741c0c030301000d08902e25803480101e0400070b001c84000380c0040004410002038004c00501410b661410010925010050740000e0286d400b01d142001848c0d00302c03c8581442d50541418501c2d03170307547e46150f4203148060500501d900c1c0200868010144c0c0503600c0da105112041c004c00c20028800c0800c8035200003417107015802803d000045e918454501c1c1e00031919802da08016090079480c0d919442a600f00d490b1421603640706035180001c1c0f007000c1044903044810640104618200188000c03070420f0658204000d054403040c0510500c0100e50403a98204c200600740d50009031240352000c040209251000c920140340000038a000b44800c0c00c68110750b500810081c0b900a10070215803882a4550300c1c000da07454102101a004a00310380460310440e1480c00040d80d03450008005001c48800c211030400308075015000034042c64000444110b180c0003210401203075070b0508001000300c181d0901040c4c20660800001080000000b240426400700302c507220b50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 267132580 1250 267131330 267131339
    0xc060908010e0715030f0e10050601180510090b0c0106150e030303060915030f1f021213150f02031012020108013008070b0601141209250f 61
    0x995004025082c840d401490040000c040312410240c5105800d0801140000745485980c040361010000403407035030062050107080b03198912440d07501c01d00900b0901f10118403a0104501040c180c0111805004810f000c1c0707600501a4003070380d0007480c44440f041d56441440c0017850103000c2910500c15860582c0441600190040300c041a46080140085046075607203000c001c00300c0c0d00501649038036074000c106071078280c900384142044180214024034081800d24007810340d00b254403913207400291060080000d50040461107503001100a00350807400041c5003400c841c400f52000c0000c07007441c9001c000d4131504229802841c07040b40c000c112001c10655840f54142d1044a444000340002c1b501d400501400701c0c50a006894404201302d0551043c1150b1200002c0089a0100341c401d808003042c0c140401130740c4828294445001c0c60000146204050400010700078540107258404a1000141e404c0c0003c01070426040032008281d6001c42c00100b030300c0340780c021a026040710511220004603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 267133830 1250 267132580 267132583
    0x82205010203031306020d0b060f04140607020d080304031110091115120403021c030b040f0c05030a09020609151b010b0907031107021905040e150f06030a0b040c060908 74
    0x2442135180c072040000d000e5440d500c041c002c0d40080601340145598500d144c0d2a070326a9405080c2481e522403c41d81d859041860380300c500310740300311250311450f403c108400c01038442170b083c42c8165901c070030542e03100e844519007902c2d40130b48034088040901c10419815049842c1e5003010241501501021200c2c2041d01c0c00d008114001007500280300208104050301c2c100a025802e170b0041c043c0c410b40c3c2e1408202c1220440000c41d40c2d1440c1c0000351146283d607458500341c89024185c0140440421101002000c013a0003408020000c019003030340e07552500103540354101107440e840d00060010304001d542411017961500213444040d0101c11500415034088414400d610310312100038210900b96a951200f10b0240104041c00321001c10280601d0300140c55075150454111481c9030140b0301030381400280001c448449a1321115a4080c1110750041c030b44595210b40c111480301c511102c1941c498000c685010a801c0004102118440030441407015444c0b40100f03880035075807110faa080c0c3e12020503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 267135080 1250 267133830 267133837
    0x4050c0f01170f07051201081b01030b010906180503010e1c0809190c150c031b02060405060f190309150b131d031606050105010c030c08070302010207082205010203 72
    0x7400c0d007005000104032003a10f44084590301c034800746040d0345052110007485203203c1d02a440151a90b01c4520b00c183c1e41540305a0035080d50b902840d01300140c091030b4000815800c01031244505007d40041125411302c0148405c00107418064000d2103452842101147d8884000c030228400d05251000801c907140304902c0c5d1405031044a000f072180166400f28224045508002201c1502d01c100000a07084400072601040d241e82e03071501c07210b50100b0300b03014010460360555503400b42c2112200c8401a41d90310241d030155001610415102e0310600c41e03030301d80c91150001400e140e06440c409510340c1076160b000f854400d441903680300410303607500d00d1b107400703a8440982c459481070540e2980300c0d080b10181e012860124850031250141d0700d15444190466004400740e0401800c071600758400d0191501815004010030320b0100100907560b01d005100403c1c88100030300c05100003e10714280761007501541c4402d50004403081d511812203170414011003450030103404001241c0d0f4005a55070010003079 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 267136330 1250 267135080 267135107
    0x70209130b0f07120504060c02061810020d0603060207050a110f100e0102100e07230105070201180503060a09050d111b0111060f010f08010902030c091e04050c0f01 72
    0x10500035440c0e100045a502d00010700c90301c100a000e0030141c040c1c0119008240c00b0724084d000008509142510090601b40000d208010119070600302110000b0001580c000306282000e0068407240340e248440080c2403142d00c05015180042240000d004005c074001e15a20301c100b24042b4030194140c01e006003802801c00c0706030720400e583c4544007228050013007004007180510588801000307404110003102c0860700c501e80d2a611403031040c0180c20604c1c481c483c29004400c024000c014043c80000c0c9540700e0302c10000c1c108100001050003000e5a000c850020703000c003c1c1513035110301c2d04004110080903c400243c41c40d1040510003481503006507080204510010003130014040c0001d0010320f60fa8204100c5030400030000c0c8072141c503400c10300c1007500481440e54040b1880d450602a1482c00340b00343c10810302c036450140d4407001070f82e001921900700729058420a0003940c888075071010741010b401400000c040c3c400104401c020000c50580030300002100e80c2584903009200440c1c800400150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 267137580 1250 267136330 267136343
    0x102060916090b130f02090f040e0a0f0812070810050f0d0326010902071a070e0915100c05010c0c03120b0a081002250218060a050a03030507020913 65
    0xc1440011143e402088025101401321000207511024000c12034008001046001e540411400c41d10b203481c80810440744d804583c00c0c00300d40300013401d85484450042c0c0c003d1440d461161400e0820000d0400e942c3c6d621406101c001481c0380c0450054514a0225004210f50354070a002007114980f070406055080c0003c0d14051030794080e56825151505000380c070841d4203c2d210f032546043c00c2020881c5002e0842c8920268507140b10340b5011146486886c42c01c545038540704200101607500410850122030115000d000b59122060107035074050038100b0454001040c03040c1c181c4116001203800b00c4041c41000200801645101c044460300c00d1300c0c000070700042011420b070a41440503041000c12000051000e88403d40d502d01072890700d940210048c589039004100c04030410a1210300b040b40301c888403102d51800886500144602c00005d001c010070303140107004224692280c003a00c42c06004040c190560858407424094455040404c040303100b40c0c00c00000070420111400b8401d035242d071041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 267138830 1250 267137580 267137623
    0x16060504060e121009050703060f060302030a060b0604050a0e040b0705030709061d041503120e0d15090803240a0b0703050a0c1e030206060f09160513030b0601020609 73
    0x1020080c4007140300814071040d01c0381d10384d500301c031191038451005000c1c403600007040080d185142510603500c41180000b80e0629103102040980c402182102c20a9409000090300203041d6002625601a6800c030b81d40003480000082024114540c1c0c0030f02680c000d012242e003560310316000f15114032044030441c001507010f44041005a015040e03021881486a015000300b501e0103000c581150300f0801d115a1704600e0140400501c96404012040c104841c03038142580f4410300c001c45c1070706010900007816a0300d0a01c034481340452036844116510b80c042d540704d50b40d08103404001030b101d82c0c1c8042405030240c026100411480d08441c03600440d040381c0c1c400c0d805c0c0f400e1600c0641c2d50750030141d0018240003080740c0c2c41e800154520551141c076080e141c41e00150362500d0800034074264005000314081c04101c811a803482d603601d06056400007285940408422200a0840b89400386d100300c000c10f1448880040b040100c04800c0350301c11072080e0f0861300700782d0312410920f40d0348003c09101d141c5804c505 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 267140080 1250 267138830 267138857
    0x822050a030302031e01210218090102040f12050c091906090b1804020d06020c032b0f050f010509060307170607080f07050711011b0b0603190b0f040201110703051606050406 76
    0x10b40b20316071f940f4002007819490090304031103664001c80c110f030607100c01e0354001410300849641015800140007525020b011058040d501c10359075803014802d030b601c134207084000504d1000401701006c00c500c000c94400c1c03000d42d42d2002044050705003403d640d48130f400c0680f407440c840b501005460f8811500241034071060450742d12a03100a50164400300c40600041241c20003d801e403c0780501c00b0400d0f40c1740292400450107880302141c480400c5280418180301c144041081c000445030705503034040315403401680f5800000b80c83e0030801da0202e41b087e1080d2070780341c04400d400f0540510440c3d141e02e8010039542c80164134000707100102d840d4400300c3c0c01400b200001c1401300048a460b4201818542110120410003201c000d000d15070480d02c180510041144c0b83c00c003400441c0d0b0141e0480f0314100707504510340c1c072064001c2d0000d20900b203490906001505581c80707040e100180e80c52803000d40d9005612800d0660302c1d480e000003211010a9005000030300c89220398100d0303040f202541da40c020440c155 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 267141330 1250 267140080 267140129
    0x91b05150f03040302151f1a030601030e0c0a030317060f010c064a0309012010020c060f060f09060d0c0f150e100822050a030302031e01 60
    0x40e00584c110712070202c10b11007054915140c1802980c50796204410384140c10384002d00021150402080f40a00d070802c454103130344403010b40350002c8090a01160341c440800d02d440c0742c003500b1140c01e503008920010000c00e242e08610368003010050100802d41e1507840c2003d002030381514041060014000c2c0c021040811f286600a800009024008580060384402c0540300510661020003194044104103080101160340c9120700a00640c007460034103c40c0e40000c0c09450560001c841c82d000401e034800031986c8107124903541140c1c0c2003411502c8003100b03407545544a40c2180c41980828585000c2011807038503504070003400c10010604155a92940b00344121800b103448112540140a1808200e010301407400d1005400444026206114101c000811880400003210302843d0107990540003103a00c1462541d00400a40c5044140c05108110054255007044003500f28060403200c003041680c1500114052000d44011301c040c28205c01214013034100c00e2017011844014a00c485081104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 267142580 1250 267141330 267141337
    0x10602120f0c0a03050c010b0a030302030f0703050f0307020d1103032205010e010f0506010906050903100c020f03040b0a090b090918010e0a050715023c01091b05150f 73
    0x700307071000d007441d031100410351515410400403004264040740c0801c0c0120244121003544030101c41d000140d516684010751170744100e251200102c0c0c1c00003148424180035100702c441c0c01240c03c50080d03403072511410003910340710050325800014180c42030143c00c1c40d5000041c0d0b40944403200c85000320203d42c140040c0d414039440001c8132955201c00c0300c0c4e0b800034400c0c0319411038041c90600c0410107141c62000104194100c0d0083e1007417003014420041d403600e0004501c12404a00d180000310380900e044141e1402c81103a8000711148000980801c102488001621020800e41c82344541a52665502e032560b0040d501e81540029804c400200c0501d1f400c44002240d00d401c0c400090350449403218117040218200050315168845101007025880040341c842089080d4405081c1240d80400904d00120420145141411181800340c041600b4005c001100a072100001c11142c1c10078a0891240c1044402c000080500e8907800034030fa003419140444c0078206a154a031908030f030340c4800300e407a40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 267143830 1250 267142580 267142597
    0x60908030d1802090f061302040e0f040f020a1d0a0911090615120411010e030a1202070518060910060c0803150d0c0e090a0c0315110315120601060212 66
    0x25080030b5005a1500e40045004403003104070510319203400c034140f0420402241e036204405104020801c04001d40384409604800700010240e407a48031418100c1e100c83c3c40c290080d601040a840004420310500086070301da05800112012583e2419550400c94414600181415495840c0303601a80342c0040381c03540c030403401410482c070510132800c141c1c0300d50400c4032800480d200c850127001c00c0c00221680800500390034a84156000110720100c1d449101000004040c80064455192514028071400000c0d0902030034003000c034a140c840d01c10f120402507508a0040d001d03d80030901c400141000b0b0002c0d10243d032210351a01c1142c1c0e890101b01d6000614824a4000200c4920100c2e5500601e440d5003d015000092205051600d0f01c01c001d10050308102d040d0380080400c000081d401340308002125001540d05c000203c000440c3ca000e4540d10020401c10b4400200704012001c101458034021182910081c3c902c64514110715607805003070041300050792180c003024241ca42d86074010310805 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 267145080 1250 267143830 267143861
    0xc06060e010603020901090b030705160c050907080601231909050613150c05150702030d06230108040c05060a02030c0a03030204031103061006081305190507060908030d 74
    0x25640d05294000900a8020400082d00068400083d69010714400e0140000b6140c4031726608214101070228807171b41d0081c000348550141d440e01070280c2d21620000403c1e002d450000a03243c1990018891401120000c3c086040390421207000700c2408801485a210b40d02ca4925228403d0303206559601030300390700002c000c900301000c04c241d1100b03006000c1d22201c10090701c161604020a0301d2048447c1c4040070200400c482d0b844010840008001d4000c541c001c494041980703603c20100d0661044141c691000d074204040003a52000450054500a0044050021950220700111a441010f4070050f080018599092011340780c820700804480303250b0b0040324074091031804017a08200c0185029408030354003003401c0081c8102204002c5264000f10b01a003e18941800400080000c500030341c0208100400010075a24010201500940d002011a8040324843d00700311800c1100e10021503c070b00400d20700080e03141c09622400c0c00e45036148061420701e5900c030710000082c50180c0010000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 267146330 1250 267145080 267145091
    0x20d0e0a0503030d0203090705120307060b15030f190c0210150806071701120201080a0b060d06140f0105070302070b090103061508040501060503070807030f02060c01020307020604052b0c06 83
    0x101c2d54204024091045081c0d0003507203c0c90280c5506041c030b82c41341c1c0304900070b240c52010503488007008401c0321107550b071002c03000a400080002140f551007804600241721140002808030720b2210051681c4203084450f80600700c0e10100300c0f09025201c40025100140c1c4c05130180150b0b84640790081b407014010208207100103503440351800d01e4a0000d4030420041441c0984005c0780b40010b08407540500301d407481c660341243c8958002808005e00600c151107495071f0358000c2d8100e0b9545000c855000107030540c1405503c3d02e9419429040048a001c2c40c454030b0200c0310322010303500070b9090311071864068001c3c0c0111440c000001d01c19034805081c403810141e644402189200305030360b159400d00c200f56103c840618051a0040c00c5906642211348a035000641c1004443c030b00059406c140d981c03200715140660841d20224007036000303150b00b03204594008030401040036030020300544290702480c102d80b0944a4002c000078244400341d5501c0b0400b201008001543d40110b14a406541c4542c02c005007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 267147580 1250 267146330 267146339
    0x2030c071a070201060617240406081f050f041502070f030c0209060307030b15030a060e01050402090f16050a18030b06042403020f03030c01020a08011d07020d0e0a 72
    0x30980014400d8403640074000203004503280c0c2445044d0161a00b03080c0200811154481c0c01c200b50401001c82001007024150460861400c0601e459454000382c41800b5880d16440320070b8840e25500c0c102583c141c00c50302c1c00e524545260040c41c1c0110044030180038075464546900c00e110301c20030a5103800c140c00b0452240028840705000513240e0099540d40c0c03812204d841001040300014095602c00c0d8862601800481e140d415400d401c40c40b804d40c210202c508040119080242d00e04010b00300902c2d205a0064402040d00001d110340d01c219898520760343d641070300288041c000e03203c1030855a14028240d01d0240542c00501d0000071500307195000c4c01004e0904034004c3d8240d04201d40007050310082c0080c6003010301600f440712400340b25101003a02d104682820381700076484042d21030140c40051b20840d8500344110390141d2801402950f403201080c0c80a00360600030300c220180300922280c1483d542601ca10b04900071022940030b0070600500e060308a40f0300580c150590b40c84111904c0006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 267148830 1250 267147580 267147593
    0x9030b04050102030a0507020a0b06190308040b04090605120601140d022d0402070314070f050d08041211100506040b040204170d0903030906030905010b062d09060d02030c07 76
    0x144920712800016a80b86401c103021400e8407030140003241503600015500002643d6000c10031f03070046080c2d03181300c10b400b2014507054044c0d5450b4805049a040000e011030905000e00041c420b40380249400d00000355200244048000c94281ca8010b940045c4c00500814407020200641e01c0b40003419404000381039000600b9088c282144e041d0b810401206d800c02d1040712505000f80322504440c2113040110646028040640000d4084980345d00062494200242c0d02c480000442d004001c85034140b42d900400741000c80d09440559100c0c03107003503028504a10490250000400c0c100180090300d0940d00130344d015120182401c2e42c482e490719090303400f540b03c80c405400204181d810703036491220204005801d00303c0e042c0001d01040401241400070a42103110b03407080b0303102803400080720382c074070708040b401048a4940150701102c005a181c480c5203c550f13a28640c94105560b0755000c90104800c101684903181d10183c00c450140a42940030310540d014660000c1d002000c58541600c565a51 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 267150080 1250 267148830 267148853
    0x1091403011e0e010c0905030d0806040e0a03181a0423220e07061b0302011b0504051008090d0f09090212010e31050c030d0201020414190306050402010903 68
    0x840d0015901c44444900e20b209005d454016442410b01350304240c2400c001ca034030386080303034294030610145801044450711198000400c580c3c0001c01c4d0340e9040d8861400501c20400000c0d104911020b80202080e541400c4403a8962062003030466450286844c080210500c6020340d1035824142c500503624890710380300414111000813200c5800d109141502500884140c0348002c41c980e4401c1030140805508103400d101d17580800912460000504d2404070302501420614880914039060820216134001b0090401d89000305ea89a000503030700b40040b15002c1c011605242d10340c0c0b04480302401c9a006024646903402103140c4042c0c1a0744844108099902c10140060080ba100004000e55410300d81f000ba00815804043c80980e1840348440c4002c180b40d8408001c400100c00c04201044410001038003180350140945085091050020f0b001b074005120740030701e0b0140240056160301e080c4110003554079a02c400c180c2c4050441d1207010040c9801030089040c0240350304084089081030214 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 267151330 1250 267150080 267150131
    0x31107170301060320161e08090405070f0c03080603031b1c050703020325020909060405010b010c030816090b0f070c05010e13050a1d0304080c010e0109140301 70
    0x1580d0380c1d4903105004088480005c000c115000f60a02400310041443e4101e486c11130180b140e40010240500340544820300c540303820503207000b8140d103000402c0181c00c00340040e600704507000c00c80c1e5550b00ba03094801a4143d030340d8100080b102d170820070000e80115003058002402804490400100003980480c6020800360a10280c0c030092040c10064410003d0210902091038202d0030515556006942c034054040c01c0305000b010562250a00c410300315800d504c1c50740003402c3c000030f4100181d210741c0341c00c41910142c1d00b81d400d21001c81003d50080400103080d60341070342c0b4040b05580b8005602403a03041d0107103583c10429950000540c0da1190310203062003005940d10070b5911021442d04410403481640924184034034061100c955030303102c0980711100c000d18840426142c0c1c9804002004044400f4008580803203101049081080007002e082910440822500941464001981c03080c00e9001b03140c0c000b80e000d0300c0034010300c19203642030f80d6030020150010501c003034040140b4440888041e40d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 267152580 1250 267151330 267151373
    0xf0e13050907051203030703050601020a0609031709120a030203040c0527070320180a06030902030f12030610020109050a12030b040501030201050405011817030703091d0106031107 79
    0x18488081c1c01400400010001101e00c441e481c0b01d03210103103440c3d0200a0501d41415900c1000883c240d0003071000052095200c4410012101540350243c0b010f00341180320760881c035107600001c0024800007900345100c0078500c070300790400038580c2c421400703540001e0044540480c2844006465101d80b0001d240d40107004081c00740074450303000c07080e2074508010445020035007030030411500d80c050114001c0f0720103000c00000340d403101180341c41d00e640680f00d000ba40c0c10103a050000116598180c1c414402c09100b141030700e1140600f50001559000c82c61278102d2402c0b000c201080340c5140c8403540b910710b14232500000c81e12007000d03140c41d03003080110007054401e034400320350a0000685c07501c945042c04c00e084074108159411500020320f00c1c081c074090b10307040c40740079a1201034541c403880c0040002e021034031860768195101c0c080940c07a904469400c070042041b6034400700700706400f031f511039540a54075035008860342e20f0400c00f1409886507025012289200300040d4002c1080d071170030408800c81500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 267153830 1250 267152580 267152591
    0x9020a051e1c06143303100e01081e070803030106170106031503261902120f0d0908040e1305061e0408030714040905060a090204080a030f0e13 63
    0xb10202d51680c01e0700440c085140b91010600c420114101c0c040384180060380d444240e80319050f404501c1c0e4030280b41d03544e01d4106940034040004030a000a40c40381c1c1c081518400c140d031352005030300c0034003500303014002c4150886020020304840c18540c0e000d044691004881c5a55a00d146860840e8000c0c1c0150002904c0c0b50a89407031b401e21180c0c1540144074601e420046800100c4541700c2905050000034252910020b000c10910303100003590803180102440c06603a142400c01510280726411807110141c050725090641600c00c05056590140d41c10b61982e29081d400100c1d8401081c43c42d0040340da030b030703828480400c1c05031245002a2003566407813182c015851070b038208039160480c018500e41c01807600200d40001c0c2e0a507800b00641040d4009a065100d899030542030f00e05100007401d0a030300741c0c00440c00280420f01d80e00168005d01e030586000031150b4807815588160310541c090021a6401001c0c09130000b0320550346040001580c1c508154450303000d100155140807044945910181c1301e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 267155080 1250 267153830 267153847
    0xd0309051801030b181902120f07090e060709031502042606090d0e0d050c030a0b0a0b010503160507061104171228020f01150806160909020a051e 64
    0x803441160010608440410400c0d00f107171425aa8804804c1641d00c4041b21000d80821515001e10304d031402c1150606980d10607250400329540c800440c40b5244c0c605091003401d900782035020540500840c12031365019403d500310b4882d80c0c00408980c40054005074200800076078010b03e10079200100410300030b824054210400c94500d45000038115884a8008440c0140040d8203c1032400c06030105403181d020300c001c542000e03810b24401030101601409150b045604004a80a03040d200d05540d00c1e0402c03450300b88000442e81800202c0d9514103451b00b40c0240700401c4c0c0244081c01c0318500c40c01c004501c403500b50384d040f80650015804400042c0910215401501003400700c0c08031012070b9820b40d41024041400031600c440c20000d2806840349105008207000d109108039840303400400300074041c000c445800c40040142500c54236200c0d0041c9008503000000018082c1c1e440c1589030389884025040200e6040203600842210007070081c1000205030702112a042c1081c03405500c68065242c1e8000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 267156330 1250 267155080 267155093
    0xa08060a1530020318060105100e040f060902070311010603030c02130f15090e1527010510030210020f060f0705160c0302010e01140f03070329190b090d030905180103 73
    0x1019030305c5240e040080144000d8403420303003c00758035800d2720341030700200b44400c0820010417035540e4a1190b54140480814510016001001918803030394849130030664401003070b4201e034130a002c02000a07802c003048002614003150003640d052000000060004942003040b0215007842e034102008000c41a01003240f10364900c035024040094501a219100d60011741d001c41200050000d42c0c0c5080100504602c0144020680075201c86540208882d007400a01d01214041743c0c40201c4c03040580c044100d400a00c04079286603401400ba000304441c0d25803071074032036040c10300a000c04100241404201c80000715a0707600c55615004204520155040d80001000a10403040b45814000c000c0c1d000514503140d4003c070b40c603401c8070758070315900c03501e070383c2000c030083c16102d9034511200c0300041c6000680c1da00d20745118200c8408031218100e0341c070224440000c00780c141c46050301c80d41c001d0084075400e0070081c1c0702807112172080c035020861740e88413000601c00c2c400c280100071312030442c3c03401030003000f02c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 267157580 1250 267156330 267156361
    0xc0c0a05150a0e060103060f06030f0f0c092a021f0f0515031f060e1f0e062404030501090308071404050906010c03030f020f0a08060a15300203 63
    0x20750b22080c8a200c004543c1c2595664040c071000300381a42d41c07083c507040e460940c1e0000d0041c541c08401c0c080d1095030750a1a0900b000050029204407541100000c0c50301e00b58404c560310301946610521051114a02c00004094040000c405500401045003800108007014003c03928200c0400a040c0700711071604000c031600201503100100f00c80d026600ca59070006108591007182441d0190b9132503410202001400242c0c0c020300b14036807554180b040789140b241b1007054031402911030907622903580111250b031610550768250032072045104103850b00b641c42007000d03200e5040700700c0c61303d401e0f0303296280c41c215000c0714401c1e40004e00440602c0b04840d8040c8180c40060b02c002402070030310741482c0020700200c402800950500102005d00c00426009800184000384084011915220550090301283d440121400000741d1981c00290591170224071580a41d941e40000b10484d00c1a000c1c03e440a154044400d05210601e07007041451010044486030180d03d94a40580c40c7e08114000700c084c40e2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 267158830 1250 267157580 267157591
    0xf0503040c09020f0d14070e15091c050f0a0b06042703030c090e0415020a0e040c08060f0a140108040312050702210307020d0e06070807050c01090b040b040308030c0c0a0515 76
    0x481c50303013030001f000d9100a9448082004441c02c152204c1e001c0c995100501c03980c10185d400c9032882c020304902503c0b8458100b8024024010f0b45d80002801c0c44113500c0d100c030400001c00030110340700400c5181c2040e03841381c0900d60707000c5104415034410800e01800c040150364200e00094483d5441d100d01da0784411100010880000c2168803401c0c19590a015041118440881d0b0355022801c1c40c2035612892400d40c181501510400003100c1074480180461800c8072050f000300351001c444041414040610b00484e840c00f0a11300d00884140c0045803c100050400d07400c000b2840c1d4988990141441090b000c2d00498000f032104400f48180c0c110b9440009042c81c19041050080219194000c10305108048051600141148403039002800e94043c00c1000340ca8401c01065610070000000f681d007000c80b4003601d5042a040c1d0303504040c0b4881c4554050840044010b000810010301004013458202c106006041e0034001c5074000d00c0e18200c00250151031550220050511030400030900c240c110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 267160080 1250 267158830 267158861
    0xb0c0c0904050a02040b15030a06030b06030307030207090b03030f0415080601080c07030f02071707170118170702060c030702122a030a0b0906090d0f0f0503040c09020f0d 75
    0x10700c0c041d1a507649030b44242202900460700c444280b10b03950380303070282d9807410352003102c070742da20781c01e015807407000512060004981117101c01010419900e000800c0e601500d50641c01071030094101704414014110401640750140700600200428044800c0508098400131007080d60f01070070200003c01404003e48000e050041ca00c0512450401440850711980e4260900160a0300c00c0c420891030500290301c011401e4402d488603407004c2501041c04002c448800c800f4002c0b41850810b154201d4901340c030702c03910301c181d007550300d9000681131b10180e040c4020079105a8101b08081c0c02040c066400041c007040700d40c1000030158110301d0038018004240941e140140355009100081e402940420070780120a08944005040c1c0b07580d0400c141010168003400381c0b090350070104500350fa5100706482c000001d0003800451001103204c2d600c90000c14045a441b114034800c120002c3e18a94005332090300ca60240080100c0c1203516070008203060034010060079500c050f03803849031086808112119040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 267161330 1250 267160080 267160099
    0x1306050c1002070c03061e05090d0e0f090712060b071a07030e07230406030303060e0f090c130e0a0b150d17130905010e04030f030c09091a030102040b0c0c 68
    0x2140713425000350180c0f90300840018580f042e1500640f43c104d9854104440e4508020810044a05c08590080480b815454101c0d03c841001c041280162850300810b400c02c0c0800001100a44901800c89036070790000f80000b2113584030f00b0440349a50281c0c505035480440e829000c0b1250303901c5500c0c0780d403040c11031900f040b140c003000b041640c84510300e20031500101010060842807030182900c200c042ca070011701c1004426a00d01d006005003100344959402181c200d0009003480c820084158030a14600c0c000d442e000c0c901c031013041001940b80c1c1c01114600d58501d1a80601c40b001c001011015018541c0f0b0005490701c001c1002001e458000410b0141d920986001c0006034410081c03c04086003d85c019202d940c08211100c070b1603025804070310300905240000031941c0030980a0f40c0124066682c070840184107000650607203603042140800112244420450040c00d54044500c00c44c0c0300041001450400c40041d0a903007103030b040101540b03400180b0001c50030f410000e1018000341039030100f20303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 267162580 1250 267161330 267161333
    0x608030708033c15150f04050613140d030504030f150e0c0301060b0a1b030309080d090201020c04180f08041e05040c090b030103081312060b090702010b0f040e031306050c100207 78
    0x1c40c1d05801941e5040178400b05d1080226101e0600365405444050241a01d4110116403200008110711606003e9041007588021a00b08651a016800e030184c0354180703010b145581c0c250142d02c90880603568204040031084001150f4000c150000c104800101703809448601010300710748079035005000c0080c0802c0030f180b10f650032400b0003401004010302c1c0780c45060b590600390b010305403c1800030302d40c0f0000951648020400d601414000d4002e0307085a504614010a00c4122032030000b100903100c410940280000701c0b40e1076040701d6140704020640c1890b1b55151450312075002081860032808420000340400d09003881542003044013458100c610318070744850340e00144010700018205450000c2d0342081406511001f500400010309800030101d000d04001000f44103500c607031885080c05401044c45d151050045004054006007100440000c200c2081300a190b00d2200241500042c4007540001c580104441d000b0642619210355074640c100015041219915140c019148140304000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 267163830 1250 267162580 267162589
    0x170c010b19090f02090a08060103060f060e0408220f050f04020304120f11030a0503070e0a0302010516032f2118010c0b07030e100608030708033c15 65
    0x200301e4204010014416a0f455031a601038030401c210150803201c9070b1070007ea94503000883d14101c1c0c0c003e1100300003144c4a10510340a030b810134420811407070b5040d40404c000c5100c0031700400304040c1d000e00312910944520342d615103000303240e4000c64408030b03182020480e6007003c00c045100700000f100c0441c5149015074818100c1e030b0420301c004040015050b401c0761a94014901a1203a128500440707440c2c4ea0f9100d402803056104841203030000e1461005014182452540201500d134141c6400f420305451542c2c0014041c00883d00781c08020081418040050006040d0000007810318107000c41c1c0d10189895a24000380c0c10203051201781c0040a600c01d824145040e42c4620419950402d87c1e58802001291401201c14003e40082881000d002c051501a400b642440016500303031040751034500100822100144903001c41500f0801c00703680001c940600841d404541d03a601c1c504000e0004980d0f100302d095044421604202c00d203000c1060b5510703082d449500110141149a0b901100300106 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 267165080 1250 267163830 267163879
    0x130e121603030e070b0d050601110a05120a090306020d0605210a0b07140313020a050a0f090908040e01030503120f0408220503010c03021c05010501170a09170c010b 72
    0x41d0416645656030304208109101c0c0d03100a207180c0320310a84820b03104140034010001070f01d40343d01060300c0c105119003030200414010000384e04080604071001c0780c1c139040d418a603c1511082e0401c00e90010210010740380f840070740207846404500044403803c08091011113500c90740e0465882c20340c4100c03d0310b103200008002000a910004001c41c41d2a4244140e8410a240412008842c00031080241441d40c0ca840d0428039802200d6014015507618140705484c2c0b56801403810044009100b8051395040340c11010701c8922965560f4605a66035002d1140c114080c0c100325034a03000050030540303c0351101c070140c2d0012401824465107060a654600d800d00c9204100c02d009010011142c03030914000c1112001490060300910400c0300032032000700254000704011450b54407d021810b01c0003070038400d040c165507041e10381d00d841c0340700034035108076154000b050350703080303548915080002550380c0c1d002440804119282989481d941034029081d00e100040890041038514414008030300c070000344 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 267166330 1250 267165080 267165083
    0x16080604060209061303050609070b13050d0c03120504060801050a050109050f01020708160602070b04080613062c0c0405191808070803040308010909031d0d02130e1216 74
    0x50f40c910b0090003203020350041a8820540529070742d000401d21001040d454070070f018400076521788503181d00301303081c5501072641c1404600c0d60081c400c2c40103042684a40c600c03603020f0f9190300044c3da6280c3c2d03018030240303494108000140d404581084070301d8000381e01502410044403e11001810301d400285850070b903108503481526440381445c8a40d00a001c29400b420561055407400400700706d462080d05024030901c401449000030002c2d40e02c4e0398109980503034050f40090041c9441c1c2480a80d4100d0011106503411a91420084041c407200411440e10041044000035811800b550190400362100041409281000c0802c130090042150100003002c120500181ea4078501003807084d52441c0c01c3c00204441c100103250300600070201c0285106a01c00d0356003956603038803001c580040d0b60704110002c001c1100c040300103420f041a0301c4005000321002d4000e40c0b0302801d9400080e02040300305000f000669807003001450040e018841c0d00164240481c041c0d04d0010000c1c072105850030940e10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 267167580 1250 267166330 267166343
    0x60a021b0d1b06090f05030c0c060c0d0c08120106090303030b12061b13090f0e0706020d12140a0e0d0201021809060f0d110102010b01140a0f050405060a1116080604 72
    0x7201c000308550f80d88104159500010300069603c41841c0c0a42d0f41d40c0400056106c5200300c076a04401031412000f154030000411019201130006035000741c0e0148042581240d110f18140107041c10001241c01035402042c041d07881c5400e05185041c05011a48a04038140c002c4000388031112020f80e00148880e000b49407401c40441c03070700c3c919814840030301a0740c404021046141000064001031600404001c0d66210020002c020250210300d070788030040d21881000d0703084070070510820f600a418002400300b10040100340c150241a0904001804981d401d0301156500788045403590204040d0180b6201c0e800214900540038044e02c80c0040d640300d900e4401e0066000254035500c4181d8100c1a441d8060305414181819140400041d5403410300d0034015841d280e2400e40f5984503502d007800c0c03000c0342a01e0600d0310141203400c8604140c00013081f410701c0410040041d0b55200d0400410382020f0540c1c03060400082c810b081030602c98600c1801c11a1940400180720150022483c150001d40c03218 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 267168830 1250 267167580 267167627
    0x1109130b121c12050f060910091a180108060403080a020d09080c010e010605010504090b060c07032004090f1203090b1f1a040e040c030b041202150403022d060a021b0d 73
    0xb4100914201c0c0758010841403401d041c0e40042e0510f10031041c0b0800c80c402c0701d144d64450f001e414042f210700400d101c1c0c00810782c0950301240201e07000300401c0340c00045105000d403814500c3c481801c1510202082115030180024800c007481fa0f00f0b104844814904100a01c4a1031410b00001c2c10b60045008401105a81d440c0c112030a40da05c0307040707450210b050030580343e2407552402d012159161040241d80d080404990000d80c9180c5445080c20385a40441c800346e410780e0644130400305010b050304402c18166105180e502113400d900c000c40c80f070b0540d010610310403481c40415280c2e0134201c0c6e00c2000390442d12507030000a082e5000995013501d47e480004c180350307951420100e101000035400030305811890720a020511054804040b003001c10f03a0202c510194460810424080040741c004d001600950307600b4107400002807243e82401482c1319110703000c002009007503040a409840d160030170760340040d5848030b103115200e170208895400b20103000b205482d0360300a4000710911400900e03088292 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 267170080 1250 267168830 267168841
    0x5010e070f111221060907050d02210601020706020109020d02090c04091a010e09190b040f140a0c05040f0e07210504020102011109130b121c12050f0609 67
    0x2001d502c2214071141c01143d55458403a08241d085a04c1404580e01ca0200003403012002500c00700054010070014003041110703510340780b084030183c104c4050860559006c20990f120107040c843d01c110301c2408500174000d00e007401000039240c0907030350b0701040c19a418407032000c01583e11807008803a03a5806444041055031030030041d0030b0510440c1c01036009685040003680441d50010074661030310501381c840c1221440702100b041501c140c21a191107c141000805410717144407604501488400684042003202c1e019040c0e405544241c00b864151403441410004440140d024510400c1160b00300700e0718160600c00305650107159402541c0f40c801da0075000c281c040b0321440d24884500e40b500e4117090000e891404002c00b8003021b98040c1d00560a0010a03003c4116501c119465220003c11851011506802d114043c0013004921b96201e680403c1d1052059030610260200c00c9074111010f40e203105540014164105680d1401040d518017020408200d036800d2106420010480d40001e4550b0307603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 267171330 1250 267170080 267170087
    0x80901061211030c0913020109090b030a24060b1804020a0525080a02060406060605090609090a1103010f030b07020a0206030103021c060c090e0115080f0c0702031c030f05010e070f 79
    0x40b0240390300722890700304100095443c0c9050380c0c440fa100341d07070704101c841d2b803101090242e4405d82007060b4503800820002000500482480c201c0c00f080c2d85c8212490100000148215688d60740b0020950500140308010242c807001600c80580c82100c0441c00e000141000600380d0082d215030b4000140010210301e210304520a035400c0c8280d00900b2103a4903008024000d45074002520100c944e90309002c80031480a015405a403c0004042d14017030500500030204400c0e1000609020301965443e100014844407140045001c3c129070080045014514a8090340d01e40000304114115004001488010782d10b620840c1c1c1100e40480d00c03141216180d108242254010000c018100c61400c040d440c0da050304440c50300d00301c0321415401f4000340e9883c0100045017440342050000582c0810015400e402100c98498002a14800c05428258154042440e1611513203101140b08008800e6840942d45805180c0e9501100c41c3c0911103540340c0340e414a407000d0054055810302c82100a134403200c512 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 267172580 1250 267171330 267171343
    0x80301061d0a03080c0c0a14010f090e07020d140313080c15040302010c0e12070b16061104030b18060a0b0d020604090501031109041a180303070305060108090106121103 74
    0x40041c00c100c540c40c1da03841c2610b2150f110151200803406100800c04032440c000803207d0071070302607505840303481c0800001110801c8a410041c0c05001303030000f000c6440c02101c6041407107844107800404c40000c3d00140542010512010455800b50800411140301c4500120150043d03100e4102d58503520202141030507d01c1c2d0070a80700d80224681c2c20081410b905400414420402d80c0710019040703410414090103e41079900200c0d04c0c2c4c007111041011080c0d0800400200002200d03c0030b8500c2641d80f1a401d603201000c044036402c801181c1441400001c0072104d42000d03a07a03034400c0d01f035001032680c26116107008040d0b0f07030b46981c0c0d00c201401640704d82440d020500e070300403c1c0558481c0c0301c1c0b00500050000703000640e0f040704000c41d100d040f400d10b0003685000701e8000606c45916040c071a00458010402060614048031000c031607403403031100f0005107003d00d500344c0300451030340350240004150071402480ca08807681008420095642480101084590040ca48003c00613114022174075000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 267173830 1250 267172580 267172637
    0x40f15030204080d0c12090533040b041e210206090d1406070c03020a0b0403170708060f1f0507020a05030304080607030b0303030403080115110102030907030212060408030106 77
    0x21300303000d15420715800704903540c9040c4a5911484841c2200008803042251402a984c100c80c49801c00c2c000e100000100d41c072013110594841d14011030001140380070b908140e00501c81d005001c6400d10004401f0012041c03192105500f400345246040c80b45900c0c601500598100c14040b40300a03000e544600c400c8031922003024028065a240c1c40c6020705101d800355403030f841d040c00342101040d4060b02c0303001da407100c1c15095402005000840e88480c610814064802c8050103400c04641c8603202c0ca007106248111000c2d2296549071400e074050201072411403200178031031607481c150b506448014400034000c0401500d0019129402c0d0301c04100c0c0b00c82c840d003010f07901d844040342c001080030001444034807506896a091203402d07480f03000d1550f42c3c00241c40c01404921282c0041c48808030364051080d00792844e140500d000090041c2c01030880e84241c40710b1079140c1005106000f0350400858110100c90440018626460680c80386090b0340010300603a004c21021403e5245020001c100c1c540010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 267175080 1250 267173830 267173833
    0x11150306010c062406031407092304050a020d0e072d050a120201120902030d050315090f0702190b07030e030c03030a09030e0f01022d01051317040f1503020408 70
    0x311030060404401c0c890703100d144002420301d40c4514841f0440007546009404a450325114542000c6030610110000070660240d4114003c0803410340d560786c001c8074050341000700c0059440c411055601c0944061007401447c0c1c3e4003480c000c00c6030a4061111000b03621402c03c00c00170b1081c0408402c0011601a405503038003140b0802c011238102e0352108802507840c800d894455111612503129003c0e07441600003e0b6041d0002c490b6512024014030003107078072042c0950302e03000818060340041c070000380985403035002200107010042d17599010000d40b0300c001c0300341c172071a440039565595402040b84002d10460402d40c440c611040150130070400d4884182d11407044d00c3d22868448010700042117407201c264005103002d400100a030511140b03002135518180d02a002122680c00c1d100c1200020070000c8111104074090005204800e110b544d000c0c40c203400d9402550511420501c00380344019055540c514000c200030041d003800882104101c45810703540d80c0180700420800e80080c0541d50140d40c00e07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 267176330 1250 267175080 267175121
    0x13080d2c1809010e0d050409050a24030203070b0c030702040b030a050d030c020d0905010e0103111c02033c09160603020a12051509090c040c0c11150306010c06 70
    0x1482041c1c120640305000580082100c801600d0b29181c0d41d0740035041d04030100710308000038802080386800143c0d0103d0036010124160414810100e900b003500c00060040403580841402145070502007d03009102e0b040394541001c074110500703500c0380b040210003449159198004216504c040c032401900503040801d0703e0001156400c05400b40100442000040c01400e800e50300c07003406101503505403041a501e51008841e0100190700410600c110341400344c80900200c600c0c91504140103010a000d5000961681080741c400d00c800315170300700c8044d00440038081040c00741600c03803540350345400300c010b102e401501c0b0184150304103400200d03500b005442c6540e000c50307502c0c0c16400a180300201907442619002922400108030f4105a600c1d07503202c95901141d02040c42cac010102c941140444c41134403608600c48000804a03080301949030081794900300794001b80103041e21003254020b005d83d581001c108002510840310b00c002824541882800c81c1440d00340b2440c0e520080c0f01c1000025501135 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 267177580 1250 267176330 267176359
    0x9051c02030406020c01020604150506121002040521060c07080d0c0903030e0a081e12191b030203040b030406090203060c0408010c050f04050105090112020f13080d2c 73
    0x100da40c850301451003d8400c01001c0d0545c0d520005480b0f210b03d400441000c0313179000019400c405010041c00e80c41d40a10200d403120651001404641c100e81c03100350b00160369a1408050104c421240580181d25503401e00f04003000e250042001c41e482104d2180b842d80d11070b22072801030824018041d40080940c0340c40c012242054100d492941502c0c01381d2140c00d07404c03100100300007020100e40107402c4a07400c4108004c007240d00c021041c402001861b406d07210b0118442d0041c40701600300500200788114090003c03140c46070030070346108995141518400c003039401030714040e5682c41030b40704000c00000c0000004e000c0c016a035003d0190306a0090640d2800e05010407203d400b0b80050140c003445518000c042d801e21402201250b611207044d0418a0900340b80c80010342c2d260300051800c506110700702c100c5190702c0110388000c4c2482c4c19180011070320354454004c003200585080d003041030a948490b000c0c00b00d15404c41070400030b04040311078510b00742402501c0d211003490804411038025071070307204000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 267178830 1250 267177580 267177583
    0x40c09020c06011d13060e030d02120106110d08040803060109030803090a060510060e0603060d171305010306180515041d0606040506010507170f0f0702040f0507050d09051c02 77
    0x1412030300064903240391548030b903502002808017903074444449000e50307030b00d00001082a00043c55030028402074a060943c0b40c0002400ea9200c440b44101c0540c000d4018880560030110010304490717a03100a00006000100281210f0000381010b071034244040001985684506e081d9805564007550040e103c0c10200003150b40d404100a046174403074104000143d03481c0d505424142221000d95802d5040b200b05410700040b50b00140a4940140a0b4140040401c46005070512418608001d141c2d88031405000400d90000c142c000d21b04042c10180300f08040000034004907440030039010f0005050700c404010f5203101034100304c807980103410240500d9011403464500b0240012030000d40e10580d40c3d100c10001114000c649803800701c1c0050040c98045a03082e24200707555203040f0849454100ca8860401c60b503000170988001c841000034205d0308509141c000c1c0c01c20008507000511041c10103000c082d000d4041c15409041d160703910f110000521504010480721062812a0411840105000203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 267180080 1250 267178830 267178843
    0x60b070201090e0907030602030c0d0501080d080603011a0405071e0c0b060316170f06392205060301091d07140105031f0b0310061404050108040c09020c 67
    0x364003240550310001108044200080c0c810702c040c4018040203810750340c401c0001e400281401076095010f0042d01c440500f00d200d254003801881c0018400300094550080c4510f40092103a4041c1e41000620080104c0417032154101c030908490109103550f0f42041121007949e54400c22941d010100360149aa58104140007900741c01450790a2850346ca03030302419910182c000c450300740ca12906c502000404200d00c0003488910480d03065503180350404503000c0c80c0c134505031281c241c40a400c2e51034100071618640c00156803005d205d0000014040122000442d00800c11003042072580d030700c0158420700c429218103000c8c000050071f4079281d5846505680040404c2c6251081019421541082c00381c400030700d0b1002c80c0d40b4802c1c0080781e0b0100b80011540b80d00040c00303164240c101081c810005444c0301280c5000381c48043d00d043d48902c0c110721501c00e00c0055500001c01c0c00210440c441c0700c200b0a90442d4145c4000f07082c038035125207640c82c0c001c807081d18036071140c2c805510102d04400221070100d001d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 267181330 1250 267180080 267180083
    0x9050f1c0909090503160c0b0301080106090f0b031b0103021b0d090509040f0215070501020304060902240d0507051303060902040506010f0806100e100302120702060c0703030e10060b07 81
    0x545618030344850602c400c0b030342c00c0100500130341d109100e4030b649002410000804640300c3d41000f1219561040740560310780003070308000d9450351144014082c0c5a107030300c43c4d20b40390f8906000510100d044540070035103ea04a050001c070314203400c03410000d40d9000703804941d25040d1000140e1218990404c40036154402207a580340001d5405000098a1500002d40307800303a90025982c4a82d602950300300071007a03240c0e8020784445082070000f507020030400e00c041e520583c06400042195103180c070403c00f000300302c10b04180176144a000c0c01070200090070705a610580340a000014540c031201c80996060044400302090441000c07c08410400650031100000d0301c00e0b5814056510b494005442d620414103004000440c82070000d00280350101800880c240ca0b420401c03403610480000ca0501e000d43d20700000031940005145000031940e44103180d000c0c00314405030025003400d80c00c0c101d1078442d281c000350816454030020112481c0c14440324103c01c107a02c9040182540da402a0449900610030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 267182580 1250 267181330 267181337
    0xf070b0f0708010303140703120c02060f01050901061416050a0804090c030216080d09201f020c06072d14010603031418040207050606120f1009050f1c 66
    0x4607103000e024030721042c180c03941078640b000e0600d20080101855048140e0680421140c4012020a9003151090100204c940d40c0541075078070b05082c2c0c20301810810780c4a1401034807280010045a548124806103040d05200499034510180310480a41c2505020292640c051689501c040114040060045541c0810180440f40b091107042e27089010310300107540701e506d200712500c001490010003481d181c14a82c1d000510100242c0311a0717046040ea00d601c0640c03604103642604246041940c140341003076241d400001541e0220341c000d45504410083d64099500458150b080104002e40031000507016003203030000d0071001030150240c5100c28001c0c0c412003c00c20f1804c991200600031001a0398050711100c07500105010180e41940c40780e4586803203000382d083c0c3c1070310943d51400103080c010301800007080705007004010040071007100d4049440c140d2220182464001001c038003a426803091802c0001d00d00700909015040103185c0c82c0c1051140141200b01d00008040d6050382d090380904e95 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 267183830 1250 267182580 267182611
    0x2060a020702030a021002010e010507080709050319020d050307140312090a02090103120e04060b0406020c030d080a020a1e17071106043008240f0f04020f070b 70
    0x400040891007440d00294250b00820789920141c20075850307007014a1107074030000a00683e1400c41c0d9003115020748086000501140c240282507900a0303010f406000110040e24824000341d552003008080c0e0b41c4000d000b13440e10301d1203900303010003401a19006500b241d0f0740c1d00585002062140ca07a40007200c00c140b201124004a0210880012000003055002d058040c0c00c2e421074a68080055213603d10100f00700c56001e510105490b103001e5013000304030200c00c25448906152000c1d0500b0269070403503000b41c6c4910014201725500c02d040c05e8110801030030069486c3c6459000704c03a4559070020410003407050b03910300307442c55900c0f42d06c40c42180030200d030f448810f4542c03400c03c1303d00c411502001001581b00c1e01c04980480d000c8686021015514070603103110050707100480141108503080e0b003010514040400a905403c031000d1940c0d007505e41407020702d00381e4400005c4c4403c650340261900441a6592917a52900c8039070446000a44109125855144a00d403900841c20201c810b81c88018040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 267185080 1250 267183830 267183841
    0x30c06143103050a26030703090c050a0e0103020a090507050415050d0624020d120b04060e0903070516051c03200d091a0301060f0215011d061f0c0606030605010b0a0206 74
    0x4102d44e0013078501760702e141c50f58403441001c801409a54106541150040000141c1c81da10069440000c000b031010300710b01907156004104022209074490b41c0104c1c10300301040056a4000300326001e450f44d01011540401c01808111028001d514100340820b01e0400003041b01041e030840d0380c0384c0011074182035030044030710300080707895040845440300402e04080007001051402c0d00240c038188006400001da00d50760700000c81c030b03849059030000102d070000074901060100620141219580441e10218a01d1822005c50b01c2c0205241c08c00c40f86036500108030007014459580b84c0d075100501d6001c0440e000c0d015040544503601102080c0116260002c00034080d4120741e0141000112070000c1c50460380f03410016a07010361000c0803c411406503001420a0b0354480c40498043c0040300a408450050503c91000e02c11014001c1c9124214208500c00e00049181e41c5d8072000a1610307010610950170f00d81038020300040e0304020481424140003184d00b0020318058203481240740d007220400c1d01e48 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 267186330 1250 267185080 267185123
    0xb01020703080306120307060f020715050112061d013219020a09030501020703080f0708042307050303040305030901090e190c0e0d030306030c06143103050a 69
    0x90748401006000244000b655610f0316060651034000181c0550b0b00c1c00241d561248100ca02000020070026404943d02c01402014403c44288100c0824104010350410b901c41c1c0110034400802403526442d02d580380f140d071183c0b990300480b240142c00240600e001d6051401050130030605480403003034031040041e01d20740c40711240b0350248000341002524001c0d1b14a9010103035211009001c00d10090010020002d90248003c102c46806941d40403c14100b40303210390303079861000d042401041444024040410141490004081501e2003084142100528a40d041003800d82c060781e41400007050001c14004044010901010242c3e00c9090f01c030340b5440c4806c24a101910800702c10307500070f038185d100c0c981c959200d514510550300b401b85247c5038140014040f9909100c0440000b0380301c001c200104a02d41c42200040c00c803a08001c89049050003a245035802164060803030009021520403d41e00381c800002811050048800991078982c10f00c540d44602520084940c41350001034010fa5061 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 267187580 1250 267186330 267186343
    0x3091a0a11120c0c01020f12100b091305060111031b010b0102071d06030102090a140102120316081302061b0d0201021306180f060c0605100302030c1c060f0f0b0102 72
    0x3400000d00c840d0300c03000d82081d8903400404c41046159400c02503510300c80d00400251220501a02c1401c0c16440c03d0f01c0090003a1050754080440f444c0b0501202500e5540c59a40440120200f4000645a40d801004072203030303900d0f2032000030b00b404002003000001c3c0e8112500041c0071404e400a1002c0c1400318012695080c05101e402c0310b0303402982d0355101511110401e290050030042c005030031714030f14100040550281e50b0220096602c00c1c1c2c0e501c4010758040c0070040030349518040c050305500c0e00d9070a851503441c50800050411480340b0024005040d00d030b1000d0043c2d50041e00c03950b200c0880055000441104503000121440b458580381074292050080302c4106c0104141600c1c002d02d02181a136000c500080018803000132154041441c61034004c0d03220041010303036202c4022030b03c2030402030201c5202511076402c142f1754160903c05078a0000341d03400308400c20b80d880c07249408182c21b00c202c40a454007004041d5403c009503007410822941002e42d41841d078043c00c01c510500d08005a80c0c2c2d06 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 267188830 1250 267187580 267187597
    0xd3f0207080d0801050925050903010f050c162405040b0903090120010207121211030103020a060c031b03020106050909030711010813060501031208062e03091a0a11 72
    0x505000044c8017505058820741d4001c0f0303903400c401d82c104c2c10b8810359144003400320001c4000900041017003a41c07442c09010303806501922080401c1306090a114180d25446408040030b10350f51248200ca08110100802e484000b001c1c03d0b0100602c0c070000b001002608080e02d09a80049108020421002c0b010048800110050711040c0c00104400c00386000e4060b107243d0380509540c00e0000801082c045040f00180e010903554440da5010340c40710000c2100d500d0000302182c3c440510041c4010b84600281c401911001d08029140b0304107868203c0304181042089014015041c00040415805401c4282620710803903000e81c3ca1382c0c2d503108c1700340e982c0207078603019128035840000300c55554092080c0741e40020821401d4240b0328059218041a50401c1c1e0040390481c9004040030165a403000e9a03a40110049844000303c0b4400c83e0070b00d40301001445100384032089c403002c0c00030041c06540000c0702c05511940188550f0310032004c0841314901101c031007a0290a10b482c5031a000030b070504440850 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 267190080 1250 267188830 267188837
    0x311010518010804020a0e040c06030f0b03070905060607080f0903190206160c09110c1c020703080906040906150f02010204080d0e0a0b040b071a04020d3f0207080d 72
    0x341c0401004607441c800c06031041e0303040707030750408080b900b4044548090b106a019a1010b03451a240c01e80090840300d1545598801d50b00d030200c00c3d0103d0b500030911804641c202040400d1648519000034068800d00c60b00134071010001810104201640307020f040081400c81c03c0d80c0743e10300c100008130103034042000003d40c000020000008410180c8110a60349030046c0c4400b02d0041d1603408000c2110b6101e00d52010114010501d4604aa010001e112884005030b4060000700d000b000041d5507183d03580001802d01c00d0100b813290803621082c0c142e40c004d02010307506000b001d1740c8001e240703801c100c55102500010f80d00540510101e005008860864489200810340b10080305811184000d0060300540d1107603e41000084801020b8003900292103000c00840d40c8444520f0328015001c41c075080c080d145c0300e09a040002590740d120344480107039000207203140c42621852022141d040809040d00fa081c0058181c0c01004a4000c24501514007940807503140031f4690054541d9295191010b0001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 267191330 1250 267190080 267190117
    0x50a0623010306050406060302090a1416021203070c0c03060c02150c090f0f060d0b0307060915050306040209040e06011d040f020d210804030f050c0d05090105070204050109020403110105 82
    0x3d94a90026034014003800300040c14030703140d50020707440c844160b602c8811a9140c1c62019508002c400e5515000041c148180880103400301011307480ba040c4042a00d80214040001042c2e03e0084c008001010f502080c444002c03503ca240110090000311034020051280c207070030001080c20070824070b0140303580b800c50798140070b000300420404528000701950040109054403a183e21000f0107889454180400859148902024075190801d03d9000303404100e40c506c003c011203051081c41c800b004001c0d2501030b0f45c030b0b81c0f40f402140c0a0b1060010064100b40362880b00c1c403510300080b031418140c48003402c0305141c0002d800b00c10039245c0c0b82a10080c05556400041030300510302101d076a04101d04c00c0c0415542188182d6180040c044082441000309910004200803d130344003204030041c0a4600305541840072a441190703849624005050600c580003400000d90303070103001a00c003000ea0080080c04150f0b11a039a0001039007007884200c4c2d01a803280d03c0e42c040c0e503000743e0139140c01d0308549841051 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 267192580 1250 267191330 267191333
    0x2010912030c1d04060e090318010c080406080411090403080601030f02090f06070c030c0306140a1a15040801020a0309060f02040315051e130308060102060c070305030919050a06230103 81
    0x2141e90300008400d80c132995809001914419000c000d0740f107404048003568649081005c1c070104044501019810451503c05000003c0e015000390341c01c0d240c06203000f50389a1340d40e140c121272610300300303540a81c0040950100b10405034010302c40c0d48100000c2c2e0341880840050800f0400368054888402d5020000f45d481d40743c1403c1140107020702500501c42281681e0b0742e0f0722a0442c603c84c1d5007041d104207881703910050141400311030f40358100c040c20800b00686101200a0f21404822200c1c0600c47c28030a02d81d500c80d0b07441442920041e003d00c3c0001c6690b246040d1014000f8584484200c94040c1000e84800052801c1d109540c101d94000c4248040281e00b9040c1c4c030010007008022455200906103101001d60320a52000c1c8182050031100c6039000b202c2c10040c0002030028070043c1150703c884100030b1030949a43c192002c09605040c4a07440740c0790211028200141c0007104001103401c20440d80070f100000851010241c010798040044200c0b0760120030b29603940f065000c1060461100410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 267193830 1250 267192580 267192617
    0x60c030918011824030b010608072c1f03150f030b07050c0a0510050103110307150e030a1a01030c0b030105060a0f0203190305090d0e03060708071107030302010912030c 74
    0x1032200d061005001130146612109440308042ca420548443c000e14005001742500001101d401c40c849051104081200b003100001c00490006c0b01d69101c1040a0462495120a10540d000c07003c9042c00840c0c4007420391004004201c401001c80212122660014011403210034030010749411040c099101ea4400c807041e00c056004104440052213035019030400f05000b403000000c105904000410654510f0a240b01900392800e6114460f80283c002081100700b141a141901030f16401c0c0502c40760300c064006401d15480ca68040d00100388401896180044049640d0590784502d441014440d241c0701000e54a000900403260000c0c404c00502810034060030203020034030601c1c07040f00d00e0000404c1403110411a9141d4407c0825122000d000c0540410b01c0307540c445403100d14252102d62202400603079901070162142050145083c081000306126050241d01c000c2580100d505069403803800a000b4041458169401da000c1090140740d03900c0b0340900c0900241d5a980d030100545100c00c410f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 267195080 1250 267193830 267193841
    0xb1e180c12041b14100f020d080c0405030f0105010503060916031b083a0203090402030405010e0d052212060c0302160c09060504060b0301180605060c0309180118 71
    0x15200c00f140c1d00b5610001449103007002c0068002d18494444552001c024801a03110103200e440c24000c0c03a01418803d070b40d000820640c41e0141d4601a0f0160b0ac07103140b22035183c0700e035400558050140c00c4580340d80c01c5c415082396040f5102a0704503071f0b169a681d1092a100c82c0042110202c94180341760420101da800314030011440e5000012050382c44c3d803042c4007803a040e0103100242880207111082500d180082c10a6008032502c00300301081d802101d0705c005d449116004003248250743c044085000e0010035804005404008003c50700030900c1e00001602a4101c9031502c042405604903075103803848224001000c586004281c20011180c640d5050042d0601f584608200742c0d00707110070582d101d02c002c0503440d100d0103803c027031082504220032241503460365000030b401641061010802154400112411074413450044c1c070002c0760f00f00082014143e207901136544000c02040c8040c1c101d0010005041d511421501c500440c26800d50004c007440c000d129800f410105c030118108200d806400c903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 267196330 1250 267195080 267195083
    0x10b0a020114010905040506010503120d110c030408210403082a06010f0501090b0306010503040f0302030d0603061b020109112404060c1e020618040b1e180c1204 71
    0xc00d5482000d0b035200909202603000680d010b4950040c0814017809202c028050441034029001c04501080d000502e842490a0354802c59a10343c0c108510074609419101d9503204401a6a941c6075101c407803a03030701c42a01402c100d00c003943d40fa0000c01a100f03142100e08995200802030f09114081102005240381e21a510f00e54088881c1121350641051001d68040d11400c940b8450203070602c0d00042044800f0781142114260070400d001c02a030f0042c4c166a4000e61103c0f203141c2d914210310702207046002d414011140b180c14001c01004100c0150061061548a051401490b0707000c41e0b82242a22030482004e442d07001d03052402c1c60141400112040b00003440c075a69180803440301c4840825a200340d01803000501002c500004010005001c1c0103220b280c0c9508400240300380c1c00087c402c2c4914080d15200e00e9181000180b10344440d0405452108000c0c2450080300140f1100301031108078840c007a200d40941c00d0b1b400c0d01d006410050b01e002d0500070300724a04010342561000320040000e0030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 267197580 1250 267196330 267196333
    0x2091909021008180a0519050a06050c03010504180317150603131e03081906091508060105040c0e06161b03020a0605040303210f020d021c020909010b0a02 68
    0x41040582c44044018a00e91482e54490480c2d1800344d241c48101c240c2c0b03096205550b0400d0119501148001036920360422000c8802400d95200f441d04502c0c1003454503004054a050a040000e5104503001039412a501524140048210f003003030b04e050f400c404940100420210540e24840d0803044005c15440305044415465032143c03100020010b0f0000c40d0014034079450701d44407104001142044000c0d460340faa003411741065246e60007a040c0c000042003000c00001c0341301600c00f400307403a1b0480e01c014840e564003040313444171204c40040d004450b070003903200c0c07489404000585800c0c5841a42a4404a5664000005002c04c10000540d05c4241d10305241d82c102208031001c28080c00441452200c0f02c1143c041c0b21b451403041c400008030036802982481700600040001c41e4100c49034450440d07500760701520034144490490b00901c003d410109510388007180c0b80c401aa0503a00400303100c0e0740038134801132070f60320700104106030b1107a001600d40000c17600d03004109090303980c0c01620a2154500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 267198830 1250 267197580 267197591
    0x12303070b180f03120a08060a030b070c0b070806060a0c020a030b1008010e03071505060a0803031611010204080c011211030c03041109060f1002031207090e010909020919 75
    0x20310780d801608040300d00640a088048080700901e01010803801d441c5082d000390225400420717842003580a484a09000c7c04034403400207480c0d07070368880d06030041c662180310241c1e43d0902c2800200403040d00072003200c00101c4107011800c1b05000b6810140701c0e84000700b166103450030020080b16482510301049800410f40d240110025100646080c41240405945148180303400c124500b5900c8840c0c000100d50410441a004242c904a041c2e0408420f070700080b0f40e585070900440c136220030503404800309002c04800d110b86402508007840700e03980d1036910200307040452100b0342e00b00d1003548a80002548114407007c5154051075107160960f940c42400234494180c40d035070304a03d034000c40300b070218460000100800c004c103803402108851801d441c8669980b82c814003045800c0148000f017881a41c8500c90700454a01c00c01c02c0381e920301c00c070140d401100c0c14038400145c00b09020b8010b030b100688900d4000b14111905202c1c60390602d0b0000c0a040c801e072201c0c603150f41c080c0a107a01c49a1403540742c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 267200080 1250 267198830 267198839
    0x20a0506090a17160e0603152221030506090402210a0606090c021501051516050a060608030c0a030509060702040e0a02101407080a030b09070906020601050901230307 73
    0x906100703d003d505014090082c0a107190514114190300b00d50b840c0d20441c03003407000d6a00d002410b42802e80b24001e801d8030a0315501403001d00c0000c0c0a082e20750440812000004020012128400c249540c15402c0140e40d40030005800742c50046500c1a04140c800b000200076140911b4160603070b07503a02d03150428400303c9401785400c117120040260742a549800782000500c1e8a44680c14030802c1c584050305400d0044002c11030141e00c10712896220742c25600c840720031402403200715401c0f070012a0760703501d84620914145440309a14102aa21b40789881c0d0006083d89003c001c40b40340084072030150211703803aa9607041d00d00390045e8a146e034020506000940043e1640d00c03a0300c10140fa91401410760000a01c1000300c07601206203070900f0003c654400b602001a100161347c42d480d480070581c2d4452503180000c0300203099a054103a4000c0f000428403080b5500050701b04c040d00d072103a0076682c40d6070302d5000f4000090020f00c9420b420080b041c2682c800110201603ca4070184005c06035010241e84 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 267201330 1250 267200080 267200099
    0xc0b1302030d0906080f01060527100809061b0313260309010e0d0c021302071e05060a02071a071103030c040608010510022802040f020c19020a0506090a 67
    0x9004440000c900d00e10028011340350804407495019108109032000c96051401c0206280105080b0f0409009241e100a1000a460003c1d00451038054407641480e07040c144001c2200f0300980e0603510b24004c801c0840d5a880706144840c1034088030001c10740c9103803101d280d49031410f11800d4003511036007000200c80e4481940300741c2c81c0000c030000000b503948904109041b2400c490050320010b80f90fa100001c9400401c0d000360301e804000d50120303400c070071407030711032901802a22a5a60042c20301d92980c807299800300c0e1a003017221503140140e044030b402e60340f4299038a04900c40c0c3c3d0000380410480d51203210310b8110400c038075039200304140742041c1c0692182100394038641007919503d03095a00801e0901406920056075401002c08584c1d003150210300041c040d41301c5c8800240c802e400d80051030041d00c4082c030014030468440c1d018108106104e000d184d414001c0d000389010b1340c02d90049641c00f8014540201d424103549400404180c1050b05c0d00c01080b0726640901103043c0c124142c65800508000c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 267202580 1250 267201330 267201343
    0x816060f3e030a0504050f010506010e0112021603020304030302060112020f04090f02100906030e030301152f0601060e0103231e040c06020607052107090b0d060618060c0b130203 78
    0x90f14003180034200352801c1d40c184220405100a145e1400c0200301c0207a0f4848446641d1000a090100040e0001c030f458401a1044c1e042100b085100c0714040070070190b0000090007164081e80c02d445c403513601d8040b00d480c482000c0501960110503040002640d00d800da000d80c0c0803900c95010000380c03243c5540422401e00d90383c1d0411010a5800004010194040c003a61b006501c884003e98a958141400b295602071b002003000204400c0440b480144210062004061100d10000301c0301e085007000e155540700c4c42405214001280c610b41060554000d0140d90010400b8542d1000d22915405000b04481001041c00c041c4070000802c50300c0c070100d402c409900a5000304070030b001e028102031010b4940080035004d002044001c10602e000b601d444101d910450746001079652103600d4054085680d000c070f039000000702d0180045c1c00910407030658402c83c111812600e8101c002281c2c1e2010400b40700c0d5501c11039000c2005c1034080300000b03ca044400e80d0254860b225481d4070095500072a24206 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 267203830 1250 267202580 267202591
    0x70203070303022b090b070c0206070f110604030602040614041214010b1314150a14010504030c0b09010e01021b220e0a031704030c03050c01090816060f3e03 69
    0x942d5103210038240a1b03280318080d48600182880c5013807020682c007040036445010340240c041400d150420042103110150301980c400f00900b540d40f1203031a030410800035801407080b0004100e00d920b030030700c614107401d00f503e04440c00d0651a011002c0d160702c801c0002c07900c0d00c04015842d561003400310460780d2922680c0f03441e4104841c0c0010039402c0c0381c05041d40b170280540a02c656041140701882c11365030f80b02c0c1c03010541c0d1001c1c1404d000102c0c00700040e0f4180c00780d504001c5c0340f911422000700d4000c94040c0503203025074099840c00d040c01d40740c400590325100309010300381030800880507031011400d0940c04a00d82035490700c0c03404401c0000320701e800c01302d40c4861051075039500b10001640500da80a0460b04002da4100029009400c0c15034010b00760781520b8070000c0522402040c004810003083d4000b18a060f0000c0003507561b0900014030541010710010100d6216240002409041915101e1041c00402c1240c0082034400501c00d031400e585e140d01e80400441c007002d0032200c18010031358042c60291 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 267205080 1250 267203830 267203917
    0x110601081f1a0a080a02120a0b060d0323091f230f07030f1814040905030c060127020f0f09032a090a022b091403040e090607020307030302 61
    0x200b10074410010801c0302525014a264065131071040825540c501d00c0c0d40000082f6201101c24456180a403100455070b4002c42000c8401c1c9421035844040743d00400d1000b000b00c59004103000402c0314002c0b021046207504002404204d00c2d6070000b48142c6889060044400c0c4850a09642030042c50260b40306030402c40025007600409040240c2180e1009400c12100b03078041101410070038044c2106102903031051050351079016a005010080c01102c0e81c9480700d034140c40d02036031540c2d014440460781c95003003517011312204480b005c840203d100b504c61075040003081e5494400489244030a5070015035030240d0600405500c1001d1703030f0405051070b0754444404032030b14001c000c000c01c005540400400d10800e0301d00400c0f240b41100c0e110745400c4c0307106446c00103064480421080c41c2e0001c0007240c10060a0030aa0804404200c1c00000a441100c41c0c1030300850041d501c10f00c2d07298403400155007040150b0300c10b01102000038001c1e0094038105220504030071541209600c0090755281980100810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 267206330 1250 267205080 267205093
    0xc0204051311012601032102030403050c011b152009300a0501050106080106030608030306012102161401150b090102030f0427050709120204060506030106110601081f1a0a08 76
    0x704001600b50907d4034000385040c1450344d2203158484520081807810001c841030100c51440040ca42c2802043d0851035443c400520103d41c1e00091105080d214450b26480c04407882221580d41124030610f00035103062040054603e59103404201c00308020450046942109007411080051402403400b541c00822194500300c400b800c6054107810007030070103003880028010301a0000440e50803400c01c0ca0840b40221000070103601098030410380e440c075140006843d0740002d00c9101407140690003540265101c241511605080317940003001c1e0340c070b1f4080c00c1c001008070750030038805082c641c40c040c010b817454030104804058095205030006940c058240c100b0442c03203040b10300b504081c6400004100070b941004000944a20624030801d040785481070900402c644030350b08460300414000e4511a140c3d6100d060180c8803652440302400741d40f0851000040004002030586441c80f580403400190200200101c000340824a1800350303081c0340d0201400c120b86890780244014001600070f1b01d00d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 267207580 1250 267206330 267206363
    0xb0f09060432060108060612090c0307060e0a050a1d040302010f0f06150206040305180316090b1f09050f010e10050c01061710020a02120a0c020405131101260103 71
    0x611202c0503041504000e2074208000568552030205c414010b41da4065140507611001d85500d0089030113100d68150159520000f0a00d401950b4a0700010301143c00c0000691a4410b00ac00c520702031243c81002e11882c200d0417a98000450010303046030180c80041191010184180161101800c40a40c43e0780c1d0390004208121003072045c451008040d00c09042e0038107050b1802840c07800b40c2604004604c13003504815000d0385d000c102c0d800c01c001d189c0741c00f985096550b992400043c000f6090240c0203144000c0003140b2500001c0c05d50b082050319484507003015040c4803c1c800301d540626a0b0720705102d20441008040d030b6803c021504500c00596850fa0f441034103c1c1c103d82541c40b164082240e41c59900b00a030700002002c11320481c00c00d21034200580342d120b071100481c80e0a02412181d9804400015104c0ba6164840c20041ca00303402554144900e40f14071010f680c1e100ca0b01c00014000b121040f11401c6c1d00c2d03105c1c210100b820440700b40c06041841768214041e510040c280d0040307d520002060f84071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 267208830 1250 267207580 267207671
    0x40b0f0301060305011203171e01030804150f090603020f0c01290607231606050304020102070b0403080912030d0f05150306220c0905010312030509010b0f090604 71
    0x1805052008a00e441c1b400499602400d5401c2c1189100340e0000303054000740300c080e80c01360621000c10a03040c1b1103805583d030303007000c0115030b005020b500717510003500c8952201d207405410139034804685039503a40042860120110000e4004001507459440100a050b030805400d000c0c01d040380040f0084c034420b498054007840c544056803070400d40620300a0003904041881400f9402c0782500d02c040c15904607141c00c00090501d01c0c0342000034860109020302149141d1b1000145120740c1c400e800711103e080e1073301c3c1c0d400395500880c8801800c00c1b604010001640c1005081c0f2440014200b00316820103210560782815508405501409aa43c68040203603000011070f031039003032040903000341c10f80d801c10b44082e4082c203010a0200d92090b60702da60900400c056155680000d00c0c000d502040296107d2401e03460700e48540042c4400241443c0c080ba80c152010311541c0000c120003030006c24041c20000a0040380000240419400b5640340031102c030304c41d008001d4401041803541c0184aa040c03010702031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 267210080 1250 267208830 267208841
    0x90b192f0114011511190c0e130b06010f03110c0a0303110301030c030215040305010c0521090606010f0504150905030616050f1b070e01090b0402070203070b0f040b0f03010603 77
    0x42c003003010799001001000c0c1c4803950441e1200b840c0ca03015940c202d0240c035040c40e1165840b0700e09049403603940d82d1401e00040e0703120301003942d041c036204800315244c0751000c240d04460f81a000e02002c0c816800704034258010040508040c205080120b0380d48001568885590050a013120498200f44104010994140310300c0c5003641e00e45004500b19410354032000c0700c00d6214000207020740040c1a03001d1082849a050b1002036602100910151803140002000d0b5040800100c443c0040d140a485815002d010100d202d21b501e00b00405090350b8410046400030a1f0590900a1020801c0040303402401003038039440302e15058890300071481c40d1106041c503004000302103841d8401c00d4100c0001080d07000040b1545a5000c0301e0407525429003210502d040c00c2c880841d200103108060700099503040c00d00c03806040f03c40011f01000794040c071100b448160310801c44002e40c1030b0072501003885000c0444010340000d03114031300d54505050719104030300720542c03090300860100d04001c001005801ea140c00340 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 267211330 1250 267210080 267210101
    0x1020705030307050604030f090e010602011d060f06090721051b0f03070e0406150e19050a05101b0f051606050319020c01140103050c01090b192f01 65
    0x4600d0700c6004d4665544410010b0f000130300308410801e0204849204459200260101d90540e0306156513850001c1d00a00c9016000d511202d00203415454001011400c00c0c031401d524000c0c5205a074448080002d1104002c0a242c2840080741031603034580a940d88540d820503601000098a0a000071054454400107005900314141041040d01ca01210b0041d00d8010085003040c03030440542c400020f02400c0e035904400e0410300040000c070b4500703900c80304460b80c221007555040d1881d20301d001c44440d03991980c0500d90300200b428008004504208280158100c01894503802c00f0031618007440c0704c000311850584120030050307400300c1442020300958a9503488116441c098510300714001d0700e0b03800000d01003184410f030108905e0111025070100c42100422400800c11455000411180701e5405c3c041035803e0b1003000c4182055500640440e41030341d00083c10582001307640c41aa0581d405101c0300c807000c200c98080380562200f001c80c801d10307984024100714411680e03186501800c580300c842e43e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 267212580 1250 267211330 267211333
    0x5071404030c0321020d08060402091e01030506060f090d081207081e010e0c0d0e010c030204080c09010b03190603230c0306070509010c030c0209090a03120b01050405120a0c060e0102070503 83
    0x4e480345403070340004000c120312500d810920001e07074070240060020b0040801c0c1c560040c0912018507507600d09502c030500401e1007605e0401244e12034100b8001103002d5002c009210f80000c11980100f4039100003080709940c070842242d0714001c003070710150703161400c19a40300000c9a240e1041c446580c0c2e454180910111440015104079032511040d0707141030034040d10800011400040d80c11005095822440903002c840c4001c1c062074003a00002002540644185521401280c8001c9400d2a0080100c6d0488404030300450950f1039003000d004002d0101d41600c001142d407840004000f9003d0b11107002c96003412004803402d554803100c2542007003012641244a600721004011466400100380c5015640a103800d65200d003803071a09584500d10900080c0d4840002010004d00c50340008540107011b100359205402111041081010747e01079544083c0820f00a000c1401181054040340880100000c02c03988408255101c450b1082941d070003000000344031081400d83d035601000707071400a00e015030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 267213830 1250 267212580 267212633
    0x3031618060f0201150b0c0c01031a0609062709012124060906090b0d0b01090506060d09030305010503010b0307030b15060912030a0f031107030305071404030c03 71
    0xc50030030803900c14001d26090041d01d010590a152003580454200013201c0411518540c84010303894040c0c11120355107520b4407400c4140000707540309000c0d841d003001124020a0703048500e2004c0041e40d4001002c55038110105000396003640c800c20340d869a103401c42d000780001d007922020500001c1d04058000000c070244a400000d1914692111091050740140d10540340c020410303800590301c0689840454500d0038020045401c1c8116440101140d48005040000304928400d001c001d40c4e104001501c0d18211a0041052100c0b80e04070580c0301200410702c41ca485200c450700021240072050540010395554014440f0342803d200380c070201d0300214014040c00e4a165916415000d00400c107144c0c881035104c2c1c0d40b070952540000c0d10001c0d000104824044500502541c1d580c1e08680406c00000d554481c6e8126020f001c1c0c420317062003107412951725291011580741a006044054841070400104210b081400707505e490191025600c985601026689035040c80c551400b00f92004941890515 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 267215080 1250 267213830 267213857
    0xb040b030d0804060216050303090d0906091806030606030803041203051311151204060b010e0105090d020d060510060207080c0a06110a05070b1b0c09191805030316 72
    0x30341580c140800d01e05203882d40d85514251000e4002c8400d08402510080041d0080000c0800918070800c0880c0440711800803040040f12140c44500c5840049994900280440c40b2038102c51015191000e41c08105940d9981d1064100d820b9680705440b034001c04030034031080181d604024003a20441d440c05005a003030000c0030440c04100b0130002811072201640c0700c1c0403502d60440c2e100041e40b400f0320890316120301c009070840c038000446044500619100c0380700410740c0607a03400e018201042e9941401c0071009810301c164070203240c400340e0b8003c0c00ca844442c00240c00d8050030f880781c003490004103002c61414401920306001d5401c51700141d00040b11a0b4215203861030004110b440b01d180114003200003559190803c1d0f03440c04060168040d450000c078020840d030004011241c5001098140780c400669a01d48a10541e80042d50041185e004603490440d000f812919801c110540007829100e480300340d042030030440f01c0444141e04017208201070f40d04011700104420301182810200208007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 267216330 1250 267215080 267215083
    0x3010b040b0a062f0a050f0a031e030b090103031e020105130f020a08030f1b0f0a030e130204141504031101141b060f010915090c050c0d05030103060b040b03 69
    0x2a004020400403000e42003902503c0c144d012070542c0075400303103450781e100d0401c0c10b080c0c41d85d000e800c00b600c1c01d00c102c0402842c603c400040c2040030542551710868a00c030440440c0e907403c00900c294000b05610f81c85c0182a55540801c82c5008600c81e8940c03c090346c1d4a4503070040d180080c0c0c180c940a5900d00010416804c3d110b00000c0f0880e50301140b04d024606140c0b0005403c0206900081c0c49440302151025604c002e200042034014150b00050114968000031a95580d03c03802c076142c0c2a800c0301d140c5000007806054401c403d40ca0041140f08c1820000c440d03401242c101d984891000201d10030b0003174290400c402425001041094194509801d549655810901500d00300303040048099400c282c06a14906480310310380c0201101503d012031401031603803441c2c10340e0811550303c0351500000352645075108034468800c110400a201914000c8004c00406521740c8a0007400710801c54842d44090600001ca018619500e030350391254154104401211500341520f070156291030f0450655550 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 267217580 1250 267216330 267216349
    0x300712061d0412180603020408010612230106120b0118020901021b150c0105070e0f01020a200301150f08030702010c021009080d170a05040b060d14030d0b03010b040b 73
    0x400c030381c81032240d2100300c070704890a013103800044501c01c0640e040841c0c843c1c0c0c9a0018421078010300001d01103039403140c035403086120901000621035030103c02840071001004039511030640001000180269496002d07185501e602c0004039222142c610041c800300b05079504040a100c1c1c032420844c104030001c000030b940c5101c1d00c902d204403c0c030542440740c981e5603414040702c000030741a8051038544403811010342c060030701690480c000c584086084009070400180005079008140c2c0148402c200c503440d0402ca800b8041d0251901c00107550251031291024040c2030703240840600640092751410031402c00c40c403101d03009032109400030403098004d80e900081500a40d90111290300319412820000d80300d0714100d0344145501e00500c001910740980244030151503001507103403242d00d6602c000140c41100c00031600205010701200100d8140c0c20031240078005c40e8030544055001240c4145850b10356000700d01c45060840d210302088190303003070a0041c0c0721004800d032018000b8643e8030b00020311000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 267218830 1250 267217580 267217583
    0x12060305070e0c090a06210b01210207060e060103140705090c03070513030501270b040b19020408061617060405091f0c090b040803300712061d04 64
    0x2c50201040403807040d20122040090300074030907558103640780e0015001c1e181c1c04011502918216612990b1050503000d01c03203040d070050f9114601130494043c400300c0d46503001c82d40503c03a5801e218060020b40c1c240300c1c000c0044008801007026601d145000031028001d0300300c00625402841c0f08220b251200c0f15011707000365200701071903101d40d17070007004072494050b00c0c00d060800366060000100f803081c10740c005801712521052000001c5000b940032a0028159403009068400c10000a400f10710f6203494203800031880200072000300710048031401660450340010545400260502580300c01900c2d00c00c240d503000381400b003000a4000c0801d00b010030010300460080343c440380015000001072004881580111035901d1035503c0c1d40308500700500000304a2404585250804036020001105450445110313800852402c81030840b003503240308141400c3d017007824800411155204414001c0361081003580e9901844c00b03888801c50040d44c0b05a84000c2e002d12034400d282d03074004c1034605c0c00d0740d006 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 267220080 1250 267218830 267218849
    0x15080304140423040f0c0602030c07090f060b1c0501090c0c060b030c040204030b06040506041e0207170a05070b0f06030c0108040212010212010f0f060507110d02120d1206030507 78
    0x501c8540204400341440e0225842d0240f888010001080000d80b1008003050041d10001c8529403142c0082c1e03a02c0c89040c06501e040e51040728200146a110b40100243c41500040420701030f64030740080300960840500100c0d0b808055084401e00291440350301d00400901c00c00740300b4000c5e000350160110303c030180301074021600d507440a0b09544040086004440c00503004660700c1d9901c2c20212503041095546601c107030308103408648a8034060107404640503a0700c01c418a018002da5540000358070a0300100c0d038580c00ca0b441d004002c003c034006413030350820948901703a4614035458101307200c2500401d10361561054001344005034900094a1041d00b00c20708241c12240c55900020303400800e1911009980d6000040900799111a104482d04039a00b82c00c4504510b5142c62a00361500403500451001030f02c14484a0041001e110724a811940301424007880d4500e45d0300840ea0302d090a200d41186171348000020031001c1e901c0b0300411002814584200122411a510551100964030444441 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 267221330 1250 267220080 267220091
    0x807090c0f21140c0c12070c0e180a0305043201051b0f0f060a0207030e06030a091a0613050f04020103020c070e01182d0f021c150803041404 62
    0x141ca2660b015003e80340030002450001c0c83c1c00070f0b100c1d2459102d20310b41102405170700c1c840b030300c0c1c00800c50903641c2c2d0581c01140c040c00c142c00d214000c070706480010f00404400c2221052628800e0060000c0860a402603651641e00c9040207100404c1241c3e4400b043e444602100c25180001d030940750300582290241303001513a070769171081550107d0440940c0c180a034020400ea01c40400c20004000042c07106150680300f550780c0c3d44e10714004030700407a6005004203a24508100d0140b6144001303584c0b2507200310700003e20103e01d8849a45189030b00c0080151410b440e030178072025140c01c0d040080c28000f016001d220324505140c03480450380010300001c0c1891703000310708920500c00500145c00504804100380143c1e682d85c030b00030390500c41201d0400300006d10f41038160a1113039007028600340013201102400c4280511000340c00003060600448024140c1c24007448881c520b04225072200b559052001103215006000035412a4040c1c3e4070640c4150b00400041140d0084000201200001250700180 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 267222580 1250 267221330 267221387
    0x1302030703060315060302030114090c010f050417010e0c060a02030d020306060415030501090f0b0102060403120e0d181707030f0204061d090705040e070e0a0e070807090c0f 76
    0x50481e07030b00004e001074602071200c080301074590b01880c04c49000301c00900204481000085c06c10f18140d0b1042503540004205440035400b0301003a03a007201035454001c0c80c1542c0c84d01c040d4035200042280b13548594441d00042090901017140c2c1503d407000302d50003841e092a43c0c1002c0e50764880c1882c640c44054010000503140e0b03480e0420f03a4010202400070714900e81510400900801c001d00840b1042e07854031401c00f0710050248196071b9581410f030020400c9842d40c1c0c0b0281d031500001a07a6280d840d03180d480d5048003ca0503c0001c0000c4c25684a6601c3d5010030780520501e0750541c2c000581c088031a500620b40c411001461004a81c1c202015040b03006450000c2b40240441d9001a005410700c7c14081d4051a0000e46881c422800342007901d00d143d0700c072010041034500340c04080300c00d503010300d800b400303c4802500c841d074000c1413840000030703c060204034003030a16003035034010282500400006c00c0b8441c3d040c0035000700741c041403a11a40440800d41e0151400f4041181e07020003000c1181040c9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 267223830 1250 267222580 267222587
    0x60b0609060a0f1704020609120109060e0a0213051b0a020f0303040c060813020a14061201120209090106080a03030b0315010b04090b01050403050a030f0c0f0f060506030a0213020307 80
    0x600e00800030301066034510303021030040c020f10400c2c0c80ca0f00006581d80500100303c501d02200c0350159500500091038100d4410030005045540e4000900e55540c90705280b0002e00180301d08202c5072400c10240c4240142e50041000c0402c01c811014085420300c4200000b0f0b8111060400d05204c265008075101c07104014124a025100030086000b403100105103c24031240d050b0741c8040310300540c0e40460641e60300c6c01f2105125512071000750031044451051000b03815884003400b00d0140503242c82e080690111042403041020b91160019000c4010f01205504000d942c95a004106000a020341458131a1413030b039a4110140140c00c0550314442c890709540c0070320020440000b000030024032940c40d91441002c0f9402845050b103541d1806a00c1401035008405480c201c1c0c0c3c110000d001d038111240c4040e5010b00791800c510b0b0812407510140070001d0214205684114000d00b4200800052894140101c4070040e01c00381c0700350300c01c00e00c000060340da50022019075240e2410140e22a180d0300801c2c1c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 267225080 1250 267223830 267223837
    0xb070203040e010b030105090a1803050912010603060c0206070810031b031a0709172104050303070b070e040626160801020904113402090703020c070f08030403060b06 73
    0x1200718501da18000155150780c04061811f8aa0440c1c0c150016100e8046080c100e815405030603410380d200ca4950030110340540050b00c52814090042d443d00c401584000e0b0840301140c200722950b507031382c0044511980d030400201f584207410f41000c1026041103560348030000c420740300040c03004640c0c6098804d44400c1c105101c000b107034003a40b0f41c541c856003060302c0700301d00200315a440c0c0020300d100400180000a0342188800c030801c00c01801030640700c00010600300c0030350030360301080b14010400002c064030100000d180c46401513202c40402d0800c100010b102e03082c0d02100070310550602c1c00601140005c002c009810300c2401c444082c0180603c0860307401c0c40e080c4580b0300f83c803000f00040041c0c030540c19001401c00200880e0100144944508910414003032031001c2580c488504540c1c07524000c84120040032062440100291481540d0001e008031504a800c100000c1d00847c034140d2002c001c0040d94041c04561907003c00650070030f481c0555a0103184006441c0c15101c0440388943e49450046 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 267226330 1250 267225080 267225089
    0x420060d0903080711070b0405042c060103060e01140c0c0705121f140612010f110903010e0d0e10201501080a03020a110102150a0b0f1c0b07020304 65
    0x140041c401034180603040e00001c07515100070076015131000e0200000480c2003415144c003400e0607070415090206010051101688403045005041c402d014840c00b000b071600240a20140240481e41c11850f00500303079454110b4105140c0e0400c0d003046901c94854107081c0e40510240403103a154088240d03050314240c1315510454000761004903c2003446001703d403038400020a0b10744140c039051500c0059045424031a45840407210030745c040b514034542201a000c0710850b0b84004640c0d01c0c07035540c1c07100451305050a4000c1d03442000500c400c00342001e0007180c48450541e409440c20940650001e071101a035040610710824000c007d5411032400780c072010100508080350080925841e004256803070008003840f620400d255000020703414000141100c555a141e809441480000e0341c402c1214400c4034998ad065000d0358550f603000c0b458001030300344103008130709001c1088603804c800d000800c95000340c0300d400340700015101101034800200b5501c1c55130340005400d03daa0b4031901c0413429409960070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 267227580 1250 267226330 267226357
    0x22205130f0212250c0507060f0504031406010f09050603060402060d0609020f07030314070f050703090b0706141303080414010216060e060708011d07091205010603060b0603042006 79
    0x5002000d660b44070084004040e64280340d50b890740e010780a9907803e17810344005086d43c1c012001070100ba440b454110400c070026051444c10280c45e03507501c0c444100c0c5425901c440350310050041202c1020031101c10024280c0200c2001b03c0d00702207001c00e841e40e00081001c0e0003510001140440513501c2d5001000034401c01c4d80071502c0c0d10080021000320303030055405400290503c07441003000307901361188070f01640b06170f141c45034181d108038401c0d11103812242c002e9040c04805000080d8046008000705034061040000007808100180b003803251001c0030b400351a103a443ca030340c040002900101e825401a80004034906c424803a2131016000e4030890540040b1402404440020001190420603044d604001a1512a0703251641103c60350703000d00c10682007501001c011414004240c20664002401b0710b03000c5501c83c2c40d5510800c83c41c1c2c072400d040391141c1d90340004000744440d501c40c818140fa011a1520b03d54181034035009008400382100c80d5803007401030512111680c0e42c00842d2500d03114041c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 267228830 1250 267227580 267227617
    0x10c140304060c020a05040c02060114010c140c0a0801060f061b0204020f190f0e0409030915120605030105060a0e07020c09010b040e0702060702030a030b15070501022205130f02 78
    0x3000204035841c94081240184082a40030540d07250500488c45603540a50040005a280c0b10141545121101809041c080c0785504180030800c10110081c0c07176620074000304800720248062083c4900b684c1d00019235640f400005001e52008050010102c601c5072422800c500340107091034000d40341812009601510000e990224510030501405604501c0b44112103407060401c0181c036001c0c140c0034000c5c0080c000402c4203510349820b5220b0034400b8001e00e04000c0d120386500c50600b600300000c0d0304101088810703600070001c07001d0340148409814103500902090400b0b0010030907200b482e00500d260880e00c4400150360030310030441c2d8207000500510100095070f45841c83e00031303a403085c012084142c442c9000958207600004145001d258190700440c40c009846c074045005006090190740c2c403400103502ea1030308240c10310207020329a001c0c400042e41c4113034042e0008005500484000140c0005410801c1241e40d4a10b09810209404001148034180f51015500078401e125070404d1900124 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 267230080 1250 267228830 267228839
    0x11160b1c020c060402100e0904030c061404110325150210020403150c0813061104090e031206120604110a2105060703020c06010b09010212070f0203060112030509010c140304 76
    0x24440c1c1c000e6000303071042190320310641003c076110b24004507c250400841e00104000a21a00300d2142d00c5025440c000391090391110080d2124005940c15100c02c180000302c4c0c130191406000c21551046c06520111902d080f20040100c10307541441094031019104d00c0c00b44059000b402401b005119141c003c66440c3d403a40340c82c854481d01382c0d03500001c9918211004030743c503016600c410701903280e01951021303881165071808058003425103221501c290501001408103c00e000c0d903690504200302541c0c540c039000c1c00c7c5540102000b0300951040e010801102c034050b901050240c0c015030001860700c84014050042082424164080807410218084111071848103000c1d101260340300d0b01c01e841e0940c448540071000e034001d0541056a0747c000744c004011035100d2000a2030b03100018015203c008000c0c484880058000e00741c01e440395011107001d94210320f01408002c0c05808418503180f8101c5850300d0060a500800d04518184112001d400c82801280d000040c405480b12040700c1e55652035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 267231330 1250 267230080 267230083
    0x13090c03020306250504290d020a050c0c0a0b030a1802060706020a0e0618060913051e01050102060c04032a0602010e060615031306060e100611160b1c020c 68
    0x109030641908910300444040700d00d05c1807040b20201c9801a0000d041500c60940080000c501d400c002022035804109112115000c0e002400e9070f07410035262241c82e984d4170101642800301011a29103e0700106c801440303400c1c0c9980650303400c98000c2100040039140d21004800b070b003108a0700654810004904d18003000a9034004205c4270070142d8411642e04151000d022050140c4c2c1c880800c401c070041c4d401b480c1400c00c0005420341d0728004003044140c280a034501c9003112010b450284030140030049a500294000c281071380104000c1c40104214a418070000401c0e000d2070000504140c00b40b0350041c40180704140c180803030300700020021034050340e40501a00074518070343c80444d517001d40c8001a12914155405503003165000c880d0fa480c56680c2d4408003c1282c1229040311002c0e940d010115440720b0b00040d00344184482068408068103019002d0b040100310008a50982d01041020440c010421160421220001036113519102003a101103135041c151221014020310114070902d01010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 267232580 1250 267231330 267231361
    0xd020f0304060203071206060e1201140c0c120708090603060d1a090f03070c0608061c0f0231020d0e01092a0602190f020405190608030913090c03020306 67
    0x105e80c17590030504984030100c1d8140c3d11140b103050045a500d80c089005070600400c00c1c41c0d519a440000111070520b4403001e410310f802070300da54801c44804202d417a0306070301c10400442d0745414259014100b115954a90141d032182d00b42c9036005020100100e440c2c1e0b154003134030341561030307003d030819040c403e8682c1070100340001129041c50502c41e01c400306240d40c0c008000c0300d038503940098080344d00300d04040303082c0da20810251141c1c0d0052a0300070a00702401d091100f40ca030462040c0f1a90311908054010450392859001e1800440181b2030512031301d08002c04c594640c900c406410242e1186451221000280f0004802402039420701007803074100000c5c02c075250004002d88885002d040070355041134156140c00d0260b1005a40401300c0489005842101010384501c5070460000c03041c0c441e0701140903104280c03400c0ca104901d44081800c681c80d18082d11000c3d000741d00080d4100486900041c0b000d00706e0032048d00703400782c0d81c000304000d2280f40e85100000d19009801c0300d4280c117062540f10b08420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 267233830 1250 267232580 267232591
    0x30f06040c05040b090904020a0f060804031d0d1203110c010509010e0102090a03060e210a031b02100203040804080604141606090b0c2a01030f0903050f0d020f0304060203 75
    0x40c90800e001030140e000740b081e00c0940c0d4186136410704000703051041c0045094050816a4008200c1100040603404580d01c0340190005a94154540c04d00b85005444140d10000079040d0302040c0747c0c000d000e500c40c40b110504658008101d01c0031411036440a0707004021520750b4524602002030010040c9105400c1140942e281c80c00030800201400b169908074029910026405000b08400f000860701a4114100d911880400d445488da8107102e00c209035080512454440c0070041000f45166815100348001c00a101441a0440c00707070000080d255141c0d900c031011003560100103c0d040c04008002d660250118004851417410181480c0f80c40d00c54040e42c8a0403445089280007000d00030038901000c0780d035540c40703105ea490300b0106c0c2c0c00349540128a0066141c45608216070b808640700c43ca445051081080d422a82e801c00e02c00101a07400d0f0282260f0a2800c0900120000340d002c001c852024000005064484d800702c1c1e5204080d200300e1114805204000c005d01c414131105034015800391 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 267235080 1250 267233830 267233839
    0x30f05010f0f14010503061026010546080d0201050108100b06040905060619080106020c0d0c060305100e092406010c080901020703050a0507060908030f03011404060803030f06 77
    0x720303070700e810203620340e01e44800660004e201032002c5287c90030040040d844240d00781c1010b07001c8003142d141d5201c070420007103524088140540010070a0781042e448164a03c3c1d45100e400c094825408078540e011554000301c01c0c600544240b00d0600444003d42c0781c400340000c14142d07405515004002800b0305420301490215005008866080700001c1c4200340b186540a0102d6040500e0450014018140103001a401400400c01d4014501a072010705403141e150740c40c2c414003941032a900914020a5154032030250285024102c04071310200c070100d0481e401c41c50007242a070342e80c108140c1200b190343d222a01d0030b4192424080c800d08042040030041583c4c4100d144151598009123002c2c11042d10954003250101d03d8039808206032100a0868601c180100d0300403555a40e111890080e9910090300d8982141c2c40034000203502c90240001001c203000258184124040c4002c2c2c03600c03042c17241640803c00c0d5044480d02d44c40e1034200390b00400301d18007640c3e1a0300e010110f10b258050122507586c0314 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 267236330 1250 267235080 267235109
    0xf1215060303040f0e1e13050709090b15030a0503030403020105011e030f0b0a1d011b0302070c060f03110a031a0405101a0405060a020a0c0f0e06060a030f05010f 71
    0x40c1800402e881c1150101c3c03515000140c0362661203160608040c11003500c0304035146c10101c4910310781460600034522090001c2192001d8100503040a80c2c94104240c0a03040500600c04900342943c2540c11601c00100903518203141c03c0002c0c6810f2500c0c00c01071031404048200010f050301980007074101e84e03011040700c80040503040c40b071a103d04a80070040c030034826100010081001c04000c20382c800303d060800205101c01c540c0e1600104641d21a81c41e19070345503000300f2114505290054400c0c80341c0d040541c14040e640e0380c2c0b02c44614290180c03008114002c0000340c2136500c02c0d00050041e500d40c0c031640e81c0c0c813121000c00801800c0c019914011b6440302c0c1d1076100d03503400c1503c5500e20502c2401c1c002549141440c0d0540b45d00707000a00507080700d400910022403681ea50b08014603502c59981c001300301a140620340389003184090343c8881c40da84d2403824200b1000e40c1d402005070f0300500c11210103960b1180002d09030014420a107415210311310702400440c10640d0400c9035415031301c201802001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 267237580 1250 267236330 267236341
    0x50601060806010c11030c0415081e0d050a030b04020426070e0c0c0309030105010f0314010c050417030d0c0906021005090712020a0905070e090a021905090f1215 71
    0xc2102003600d0302030021300160808804140d000d801d20949010040903658040d0740a00002c0036030303580c5291075501000b110130030400850304002c6070000740849001a1041c0f00b25017401c07901c03001440c9182080c0040010410070032032082c0e00c5480c0114004004540311616000d8550344420048540d040341060417400f031020907000030348a0121084e1450a40351682c42d16131541c1c2a410085c0034005e03521081c440014280d5003802030314041c0c0400398090b032000385142440907444d440c00480300360300d0b4988624411401d03405012141070380c0400800544041c90000524174500c20746040b001c405150050310100d00ea40f0018000840707016608a55001400c20045412a03505444081c003d51154008000035010340401502c22400100b1481035541d5600c07805007038900807a02c0300b0001d800c0d0006003403140703404001c041d045180180c085061026a1914060452101403640240300c008100d01c2c14650780d281c00c3e4203c01001600f00c07280044441c17640355607150590042d14401500e0000030b10f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 267238830 1250 267237580 267237587
    0x100609060302072604030209010321110307111201050906180304061b0f0c08011b0f0e090a1b0302031008010b100302030403020717100b011412090a0b1305060106 71
    0x4880c140c0219400e4421014070407103c0d02d80306044c2d250340801200b03100c0000903a81c0e2190740d0340294080c0c201c0303260040b41042c6154801001c0c01d41c04051203482a0204102c8400002b0354000c0c690101b80031089110714000140b00a19070070f102c0216600380010404044000302329140a420b204204e41500100400e6440c0c40307000c1c9010321070011b5508030b015401d1307507890301202031454020fa0042180a000d80c95500c0c241d00c150700145001d03074403850740c40c0700b5006d0204c01022071041d0b0301e400300c8a01e8000070b0040403c050a503120380f186808202060558020f94005240006660049a00501d070782c0b01c06030103500110b03410242c401d1810f00016411106024080410a004015542e603104d00001903000790400390080d81180301e072109c0807506080c1c44190448420101004040700c280100c000f00c242e424402c00d681c100148201050003000d40501540c5d07540060444900341ea80d601351b1102d01d01241d00201078001000b1909011002011b980040c0f0100d0148041e00d0046e030b02d4000c10f4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 267240080 1250 267238830 267238837
    0x7170702010e1507240507080906060301090c0e19022a0604020604051509030d08010315140a2307080105030d09050904021216081b03010938100609060302 68
    0x14040c14004024920014540c04203085100241744551460b1100c00c1045000300c960484454000c5007a2406100d02c03400200300643e803060040b002442008610b640b20700340d24210b48642c8139409503a0b0702045c030b4121035000c0c50090400c42c0004544590b81c5c144485000340f000c0f8078420414690924882c450100032510034450754000d88050300d0f0070f2070007082c0050078104181020514006014600041da406d0041a5180c3c1c0b041d683c010807075047d0f0418007601382681210103000c0c2c2c07400d000180c2d0280c81071400307640304145020000c0d2489214865144151012600e030400700c400c241082401c4d60084c0c241e505844050b4225003455180e00d60540340c0c64098090740398080c000500040061400040c9082010310603c1a82da1190f9038000c100c500c42926003200489070440244140044030b0003030240c580b503400701c00a029000450303c0d1800300324450b60041c0e084a00000012640b4462001c1e003800b180d551042c00401c078034041302d1825034481c10780913f1001801072000051070350b100c0d0095 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 267241330 1250 267240080 267240109
    0x2040c05360301020405100f180f05040e010506010207150c08030f1503030f1c06090e01050403110c090a022101060504030b0f01030201050d090302010b03030c0f160f0e060607170702010e 82
    0x840215050700e079082d00c202403d60703d00303002c002c00400e2000580f0415002701d001404640300142e481d908080801007501e9141414100603894001001541d0381e00080030000c84401040744002c9076403072541110410b001150240030301000000388003110900307403110761003a500c56010818607040340f41010307140e114a0790900605d060a108150344103810f0301c082141078102444c000703101503a802c82c800c195410f8020348111659039000300030505070040c1e240c075074000b069070203442110202c50004045180c0985400c0f6100e9011910b4414420740d1441a03a01905031756541c072042d03944010003051680280021078100781c603040880e6003410b22500d4981680d40c140c48550401d100b6000d07140091200d08802d80c215900c41324003112949052000b0490648508060840040140f203101c0c500315020440b11070710010f14000b000007250043d82c15041d58141000e0110584501c00020060700690b1800390504a40e807c103035014140c0c400080441c940b00382c862090b003404c6501088640100d0582 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 267242580 1250 267241330 267241339
    0xd17061002030f1c0c030f0b0a050a061107030f0813060509100f0932060a05030414010915020d15180f060e091e0105090a02040c05360301020405 64
    0x5001d807440e03850b02404c850207101d00c10842c00628440c115050f12401213010380030990b5015031703225502080c0242900610280c41c0e90006a01e842c0118040c1d0b2034512419081040000d802c1c0000207050058500940e0001c500a410b035480b41026211640f09020382c60402888501c0091050b00803400d0b0b81c400540100010084080c003001915041e10740703090403041155119021580c448500c0101d18540f04100c0044030340040707040303207245000d4000103450bc109414444a88019440400c90b940710350310900c003542c45200504ca070f90142079000f4008200480c1c46107540207800b040c0e07010341400c1a220b24103004402d41250f100c0d929110a00614680303540c2c50541080c181c1e810342201e491310703402540002c1e00641c2e50050a03c00c0000350352283c034030740281d001c0d40740741c1d2400c0039004d403d804000001c000074205841c110380c1d600801c520007070040340c507946101d500e10700540644030210884404e00c99071401485e42c4070311100302422401502c00c50002c0c0704030035060520944098550240 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 267243830 1250 267242580 267242587
    0x61206090c0603091005012c010e012c04050303060901120c060f02120c0a030e180105040506010c02040c11210304061503170c01060b1206010c03030e0d1706100203 72
    0xa000036503000510b00000d0b40305641e17a0400c030030654402c00c1c0c001c1070140e0440340c015041c0e00f0b000341203902c1641105040368815006100c009580301d2481d0440e003180000342407000702149007607840000c6061035420b01e803504c001c1005000c800b0009600c144011101145035030380b01c000c20070080350014800b0313000f40d660300d1082c0b010764060459100c20050900440380c5101384443c01c0703000c940c0804080484d036000310f95008109504020f1046003918200c0d450074240710032100e2030010308014071641b03220301c0d1500003044040c0d01481015288a40140042c400b281e05407002411403034660040b05034900c01d4405401a000c41203c001d404d01c0403052040c0d10b941ca441e103c400292141f51003208044030042c0c4008005030042c51005008a103111541d40c9542d0444801800c6441503800a0202e003010060541c00340517803182d03d03500c03080c00d003050810300c20039050440051050300410178003440703401c10741001e250704051005503041441140c042c562307440c2410301000104149a00005d68410f0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 267245080 1250 267243830 267243853
    0x81e03190e030d060f0305061006020a030e06090a0608040c05030d0e0d0c210302070602010207021507051e010902151201230a0603050a0f0b0105030106120b031506120609 75
    0x6401184581c20705104481c1082d014100d0402203a95036440300c10403008041040041000a000b00c65021400842c8000c002c0c4c98960044d450351009100101000141c014480081d42c40e1402d503040c481c1c001d00900101511740401410308081940d00303543c00303003038454001440e1500280440810149580d01c08110340c00d0400d005c64920341c808201e034503401c0b0305808600020143c0130071011106806007400700600508004c2e081482c590011411640108514409a150403084540382c0107074000180d6903c10720b0426500703164041c140d25030b0414a981495480b05c1054020144450003140c4041c841c0f81801c00b240214400d58440c1e800c0031403030b9801001410b500680c44800300c5442d4000101d861922800a248100c0580280011170b80d07403814003c3d840618400c000305800120420808081c80c0000038009000c1446591304210b144030039420608495004001440d102500701c3c5c81d00240450300c0c00007074100f200c285010b80c0f047c8134561609040090001c0c003070403405001d0980b03071401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 267246330 1250 267245080 267245131
    0x150403050a050c0f06090a1208071b1a040311010e06060a05090709120503070606052e02010f14060f0109030b0a0902010302091810050409110906011407081e03 70
    0x20705003e07410700510701c115003000802c1c414280728001c502c02501c08070751145880d0a00e1140340c441070b0304100d03001040221080c1c102c1e981120000e180490b80744045070340d01d0704191b290350a800c81001824001c0a01c0304050300001035221a068800c0207010245d21110010368898045485641c084d8010400304445d00f8001d400c0d6803c040240360400c240358440e42100d03071106200310110342e0380c0d00004581c418441144100c4014020442d6015400b0003038265a4821117124150061070340c1001c100c02075081e0007507001e8203007111412410301000c404125813041006e4100c4038a070007004110505c80e0a584607070f85d171000740c80e031200500d141a1a05001d410082c040c14800300e0606500700050b43d2550f40d4002c6100e480b0400841264103885c060222040c019900e070b2107140214102140240040d41c1d00c080004600e01c29240c510ba0382d51907400403203401401c40003943d81d100740041c50a081c086844010080b529078804068407041400d118007071248012220b007001624044094003030600c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 267247580 1250 267246330 267246337
    0x2040903050903070b07021005040b0a0f020c1503010810050405030f0711060412030f0f020312060612014707020d020a181a03250f06030e150403050a05 67
    0xa18101d4246060b0001003441c0404540081d4001140403601070214540000003a50200b0b80b481d010303084c02e02e41040828140260b0b0020800c2c00002070086400900c204419001702c1e90041012040b40342d00b8003c208a071b8020f0088800500815002e41c0703111416009241c052503201005503e000035601d0b04010641014504440b00007004d4104038480e9a00c0029001a0081c134510003c1c1c2c00b020f140240005c00015401d400340400e01c1c0340703085030f140c001c420b50700c080032500e145000903a50300c00051018401c8100c10142c904000001003000040080180e545100151503148105034028200c24414022419042a00b9071504041281103400010b00798041c40904040561145135000480f030644030303008501000190304000764548454040e12100708074001c3c8440d03c0b900c00d500030036152103000f051319052074404921001e401081d502ca800040200c22541418545c49240040142640c2080e00c91075104009595a074118081d060b54010395260f03c4041c60111129030a41c2e5942 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 267248830 1250 267247580 267247583
    0x170601061d04020d0b2713060b0303030702030415180312020a0f0605220206160807050a0f020a05032406060409050c030708090303090606040911030a0f0627020409 72
    0x541c1d00c105809540756400903003c040502407000c522261403000b4058070800b0030706182940ba1040c1d004a4900e0010601c0319002690542103001c000041e084c108080c00710702820540501c400010090303081e27030101c054030680f08500108844030600c10707000c50b030340f0808807400c0c07070801d208010400000d0003400012004554600545951900645801c400342d81d4008040d91590f4541c010001e43d41030341540014060524a500c0d014400940c000c65450301400c0389104c260800801c41c0c07006e004002054540c6294000e04840380080945011202c152520300201c1c0a01641d44001c18a498017081000c8110315191980141f00c0c0103210301c1600440c06044560084030030400440c4800c080c0c0181031180d408206c60981c3ca0405580003821940006c0250805030400c2c4140500104080380440d0441c00440d03001c600c1c001142002d1020b451007010940c2d2600c11203023424108106840710900882c0202c46c00c12801183d400745101d05204044113040000c0d0f0b0f00301c44001840c041c0d00c9050b00c0c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 267250080 1250 267248830 267248867
    0x14090406060b0c06010f0801060b070209090a0807060902030606060c06150111070b0c0f01020c062a0c06070e040b010f08040501020f031f0510080a0b030c09130302060117060106 78
    0x9542c1d0400040b203540400c0c00400c075600408014889180101500001890984000c00007180740440f49801e602641c9802840341e8100e40204440d00020007601c072450350040c98444e0307240c10526000005009910040703000f07002c2c2c840000c0349440c200080d149004a00d0700074004594400d14024a0b010001800c10706003e440c104903103c000c4c0401110003c0c05441c40090750382d05030801120b00d02032041204c9011680100410724800d0300106005d900103c040c1d01400100000c400c403025100c805c0740b030b0f502d003844011a40c40c02c501c00c0021607a00a50094481c604140c05d18001e01054404100c0001d021842a03030700c01c91000e00c140c00181d4003c0c0510300050804842c1309101c000d690094650700f800c800401061000084800c075400014171084619507040d0717003031a80241807280002d185066055441c0760010503520113200116030840003d1044070540790071081103c106501a806400520640b4008185144500d81419170b8000c0c00c40146003da181080032a41d40031485c0740354040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 267251330 1250 267250080 267250091
    0x801050d0317090a03030605060403080a050f190f0807030603050d05090d02190303020d020303040c1a12010e01140f0f09100909050c011e0e10020f060408130e0114090406 75
    0x9242c04501c850241c51100e02924100510741001415200190013082c8201402c00041000400010450711803402e541040c41c0ca81c802c0b0b010307404c0719020705043c0111149040892001e07550b032140c10040c900c003e03500c80540607103d036081101110301c2c0d8003004246502c82c011880542c0e02640180c0000100140b00d0b40c518246075006c240d1001e903001900e555006003010501c10076406200300b12810445100940c00c1d89020b480744c140701341c150302c2603603954500282448191501c00d13003207800284842000c0422940d5451003c6a8810248503031148100010003004080ca05003211400240300203102000303880b0044104024107001a105e2020b8008203d8000381084a9020b0580d0782d50140c00a095450700a03c0050200c06203090761210103140c1c0c900c0c0480c0307960403d00291251809884400102c0e4000b20203903d800310052003200c45209440400c07041040010040c40e0380d01d003a500e80d503081079446801600c1e42c0320a020f0655200c404508007074149c100100319680c4035008140101c0d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 267252580 1250 267251330 267251357
    0x20a0611090a0e07020616021b0d0b10060807020703051216170904050a020301060f0c1b0e0114060f04060e060d02070f020405010608091905100c020a170a0801050d03 73
    0x407103031980000d440144a0081150301d43e01030281039400001c4646c0c0700c0341c05564030b4000b0345911400e11407400144054002c5c0070301d0744540400055482e840b850f4032f4180e003850300000c845142c00344034400c0043c01e07400018500c04d2000c41d040d000c0301d80c000b00401080c43c0c41c48240082d60810340303e034400c00484c0b0082e072020550501c3c100c000b0300304180005960303440c00c0d0107020503600300528000f04c01c0c0c0108010403c0d00e900000424040700c00d494400160049032400705078ae444002002541010700610101e2001a0400350302d040301e0b80003e02c41048a540000e120240c0650150740344803130f8042c04200b0101d0f0107800f41c000502c85c011f00b110715010700001e10b0744c101e80000000751103040b0340c0c0c01000304506180c890f02e40500b41320b00f880445868880c542540d52030040c140c480d046584944034070b0420000300251304100300441001d1205d0303040320400075510143c2c82c000f62103d000745414006071039042c0c81240c0341c100d60ba507200c966076800e2006011602d01c2e482e07001c40c20840341403c0c410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 267253830 1250 267252580 267252589
    0x120a031112070b01090f09080d0b0415151e020c06070507030c06030b04050f060a09090816080703021209060409020703020a060501030c081b0d060903090b191e020a061109 75
    0x25464400c98403043c041d41002025000c440d151000000d035149005a003801213aa0300c000d0703030704442c48500c02003980800200031902902030901c40c6201421410404280c030700e0100a118003040050307442002c0a0a241c10084018400740006030150700722614030400e81c00c084009013202806041100c103015903e40c3c0d0014030f0030745070344a1000203648860030001454180100398004034031010842d05801d1140c000380840503144940e040c7d040d6108020010044010160380500020070203100b4210070508003c0307501da00c0548124018040c0c403c00c41f0b50410182c050b00d0010002804480c10203040480b040020751202d80d0650130b500c01c00c50010300150407030003080d000c1c5100f14190101540ba002185160144200803440943e1007010344c035545444031414100b6968004c1d00c04541126141800d8400c02c8603900012882d100000311000c1040d044031384801c0c0c924541d0341f01c01000f08031001485110342510708542c01600040f05980224800703030000700940d468a0f00040c5004803400014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 267255080 1250 267253830 267253837
    0xf090d05070f0b25031202090d0602030a020403050c0913030f050d0213080d050c0c06031005030a050a02240702040f020d09050109060534030906020307031a120a031112 74
    0x3d00d00080009030655240248600600030400203148a03d414a82e60ba4003801c002403d0040c13101c0c60b0340c0440c1c0f0001940d90b030b00c0072003a001d030084401c560724100341e0881806513002e804144c4a1340b24120201c0c1c00e5007090f03000d1034030808424141c00e200b40d103250340490745071404011201c00c0040500c911100c059403032006024107c207502c0e491201618041566040c883c081e884101804030512010346002d50105411000c11800c82c1c8041d0386e40d54034807600f540110145c201c95003510031124030208110b000201944800e0080f204841c110050075811040100d05114100a081c41440303454018201500700e4440c0303100b80000036061120b4a0708900c100c45c0891810344490b0345503440c11051161710300c10780f03030000408a00c003504015000380c01c52480201040000481c000c0d0080b0f01403e2307101f603100408059119005650b6420600c50040c003500054088031050403203044048411300d0548050741a400405014010b4018170b910140e070f809515039201d43c40c600504000e2401b10300e46c0e1006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 267256330 1250 267255080 267255089
    0xc09031f053304020c0708011407030608010b01050d0c0e03060c0909220215040b0315130501080d030b030a0203030c06010e1609030803150a03150e01020f090d05070f 73
    0x10301d03840c0812048a00d014007100e002c540b01c0c40354032482640250200708150405054801603642c000600b442490700c10140e1008459520f004400c88400b0170000c00940100c0d0715a509014a07510740c0441c0d0300329054140740b80d0100d8030802100c4003c0707400341c0080c58100d00506100c001480d040340480d00745081116048101d41c0c0c0040d154026141007c003068100307100540030039522180d10044100303012030040c041e22440900d40c0c0e80085c040304004490141c090070305825100e003000c0641d01d002d40340220300707144075080e55000e043c0001110300c0340350b04030303690f42000b001c01282c1044140e0060250036001a0035000304006d41000d038800700000e1101000400003008c980d0b02d84a09001c00310f802524139401d594303100402002c80c55010103420b098a40010140703540e5180e9207004000301525100d5250030401e00b103000402d001c19a14203034941c2c0b500010034040d6103480c814072401c0388600b40c0c988480c11028018060b2504101c4002c4401506c1351088580241d22000a07010b0880716600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 267257580 1250 267256330 267256393
    0x40b06120c03070f09051e03100e030d1b090b030903130b0d05010602060408030c032203110c0a0b070f060e120304020f011422230a0b070203060c0903 66
    0x6200601e90711494484002c0040e2500820b00e0381094002419031448248801f02801d07480c0783c100380d40da0b0901809065418145040000001102004e03840c0d0f00324440101d0320a10f0022507600c1d1480d1402c1d06c0781420026540c19080e6420305640728a243c0018254221911040c0710906807812418003440142000c1c82085448406038072241054070740c160070140464000c102404006140c40007a40e8000945602c1c00e500e950b80c1100b400e108280c2400e4003000c08000b2070601040c5500103038a030000c1101d901c1550741c9102043c0620440345900d10031900340a900f049158046855120a02841440307684040380c0c0b82401c902d17075450311001c16080014110300006010862408030a081c040364801e0030144610b0203c0701d0704081074042c00381c08000344140444a541e000b07424003216005020705401e001c00d0079038000000e42e11841c42d44904d90050251300c20104100c3c03416001e0791b2501d44d0007401001140d6032081c0c0501981c010881aa0301441500c50a10030310303882e0040303919070010b03d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 267258830 1250 267257580 267257587
    0x403051908062e0503070e0904030e0901140307062006040b15091506030a06150c050105060901031205070f0b0c030910330902070b060102120405010806040b06120c 72
    0x401c03c100310500031200f01d01c0c0020310368503460f01c00361901240403516007800c080352a075442c004140c0b154005281a5a40968134104110030990005000322400e42c05440d2600035a0321007241440e11130000610342e9041c0c0c004d500801c465441011310004100280c810150040002e012144c5803403000d54040750809040d10070000480b11071400c01c044400201d421034030300d092030400c200d4550403940b0114044d020000010310992150f401010051030802081443e1480c0000300512004040608548039401e04001c100c49203482d450b8039060702d03040205146865103a40c0d00b03443e96801401c0441d00028645042c1010179150380056100d81000503500e41e491030324204082c141480d200c40d01c501d1034900f14041c4842c03825401d49811100300d40e50080d2520000202800284280b94061002c060000440804004101003150b001d0716007a0201c7c0d00c28000c4242d65140c03805035009a42c0014000c03c0000d0451030150410030b01c03101c000d0005403030000c2c0707005d032555415000ca031441200346000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 267260080 1250 267258830 267258841
    0x1c091701090b0127020726091201050601090e010b0a050c07090e0a0308060613170a05010203100e0603030301080d1b0807060c02070603020412061d0f0703020f01030509150403051908 80
    0x4c144030701d00040300940452070003046540f02c80e510f840420391144124511625040c3e2000600700b240c20400d4000e100358040c40c41904442e000e88001c480550000d01ea25500148040305980300d10f041c0c0c0d810849003801c0c8001c1500440302604487d01c0c0310310360b10808000080c51510351080c480480b0002c0c018041d8282c0b0b50030064844100946041e004920411641c1202c054a42240c8203031000b4010b0107111403042440c0e0342c43c00320300c1c507000b8109500c00000e0000c01302000c4d0202040701e2001031010f020b44c0d04c403420103440e030000344143c0c405a00072807100c1d480a403203030580401c180034504c0008510366103610342c2c1c2007540180e00100e43d8196200f4035080807903010801000205903525081d80703010f080150012029292660061065072620141240b009280c40780c0c1243d0361f40c0d10215140810074001c07860745c83c1c00d0b601c0140d001c0c00d0502c04040b525446401042d02c0b900e4010018030101c0e100403003a445161004000383c0800c5010302089200d000261400740300c3d61040d503910b803000c3c14607 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 267261330 1250 267260080 267260129
    0x2030a03050c180f01450e040b1b0319050109050c1c0b040e070603060803030408040e04030e0402030718120f021c0b040606081c091701090b01 63
    0x1401d2241c00c040140300420a030382c1820015106460191513200000d140030005803411880141006814200390104080507604800717604141100c1480800455005000c0240404658000c0b00c09403800c1ca000100400c45240c40e803a000091808445000040054480d407150012b5500c81107808160340e100503100d03018014180545212502044241422107003a5124825685011142c0c51a124a0340201d150b03035110a0320708a0280c13060041c0c0110340529922a90030780648004603241c5003010589410000540313210316440a03080d40b40074140324003040c185800a008400300702c0c1c420406102900d45002450150300076850724010249201c1c0707081d144600d203811030580305142095a0000c100d80c030032070002d85501900d03826500c07008401d4540d49401c480c2c002400040b101400d02003002034580c88001190358040070b48640ca00c40181d1800b02061040c3c151000988258050080a00055040c40510889400020503d925560f07809554000340e000c10700c84071040d0b103007410400307030b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 267262580 1250 267261330 267261341
    0x380907121a0a05070203091003060503030a03090b0903091e03210309010b0603090703060513050703050a110603061806030118050a0209130302030a05071a15041116060b03031902030a03 81
    0x4907030805100f80c0c076180c3d4000707541e03020344260382d032141c0c11004140414501907400312000d410050192070759400b0504001d4040c03c004842296450038400001e0640c12003c02030780c407100780c000d0006007018000f1802c0c8030b0f859901c0c520f05526000d100000405c3c24001c40103110029900ea402c283c580c039000c500c2c00d08403414500094003c900c10410080d0004c40800c094064a81c009800101a2525000e004250030001001026485001000300500074001104030485100c1c40b40e42c42040045400c3c40002d0005a5030141c2000010101906030002e4510403580044007600024410100096104112040c003c05076440d800c801800c10550034080501e5500040243c2c1b4485100400e5074000e541c1e104221a0008002c004501082001507100a694100142c0d6003581507a0a2100030076481c8440400c1880c030580c03525113208803006000b81036505180c3c1c1003503842a540600e86034070010b004155031450349400308201012000c2d51a203808000170b0085d50080da2180c8440d0b2010301142c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 267263830 1250 267262580 267262591
    0xb0105030706030618020c070509010f03110a0b1206150f0403060c030902060304030f0c0b010801020d050912090904060207021008011409040f11130606020a380907121a 74
    0x1810064140072030b2800106982000d00c1084d80140c7e20103607014000d04040264001580c0240c8210001480c22502103001094074040c0c005158007074001000c00400c0541c91064418148090191050500241001d268070000103085111000f07050704401c80d00703031b00500c00700c880c5040126050051080c944101ea03c0b1a00d036040401512440da0002030306404020301c01010880e143d9100d040481c882c0d110740f4241680235080d102c855865802c0741e4041d400c0300080d06010741c03904000071503c071030019644003071002000301103207040e95900030f01c280c0010003413054403080d03003c0014500507140c4101c84078161405da580d50707406504060f558085c0309e0703005142904c01d0094200b03000100e5150000508440c0e8400011120541c2c1c0b03001180c120503a03008140e200030f01d404c00c0050707500d4000c101481664440d51507900a8549082c0e00101200c0c170240b00c03612a0060f140c4d064213092030302089a048455a000c0f5030340340707a5038800002e442e06800801c96100100002c0303408070480a00990307030000d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 267265080 1250 267263830 267263837
    0x50705100c230409020318061302060a0e0103020c0313030c14030c010305070c0213051b0705030d090c09050108010c080114011707031d0f1c090911160b0105030706 72
    0xc5030380750004108240c0151810096040104a80745a06149045030003c040004055407646085582e921902075a42c4400007540200742c00a14000b11150703846c11242c0d070080001782440c4070304c02c0886079585200041c6040c1071b420004407a007840100301130a0300c00c0652202036440b90852500283c1c2e00c0c4aa407001102d1050b043c0c049400b07550115103520310803402c0c6400500c6a0b91100e0490f440d00c03c03e0300117034000400201e2000d01900d26004180701c0c1c45080e410311100810341d0603182e201c0c130a507131000c0c009800c1406001c4140b201c0390040c4103214010f01000c1e140c0b917128170f661011100280c2c490a2269034441008408035000041c15005014402e489440c20001c1c0001070018a102807040134910203410003c2c440601035801080c1294040703405c041c48101c02c0300c010395141e140c902c114040c1e00c510750800c0c0e10f09200c0302d00c8003030f00e50300e03a640c022400340b0b0803000c1c60262006102d41e0005100c00e001f12044080420131141c1c01c0c40c001c9010031042e5142009150602d00301e5040503082 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 267266187 1107 267265080 267265091
    0x1050103030201230412020a05060f01150318020409031b0605060301151a030601051b250f0302090405030706020f0c0105070221072105070510 63
    0x60324440e030000c0000001c0744c1101c0340b00c0009040c40090040440c80060005040c204002e4080021401181c0c0c901001e130343c0722070500710121001141c0c1e44e030b44001001900803003280d9901c520800e050030030224a1403030707414100c0001400040d00407038903502428100f51144070550401c1000c00c180d030441a081c0c2c5800380241100f502c480c0c1c801e40c01d02010008901d9204c0c443c1044440458010001e098203540703070350707640d0001484d0605100c000d028407c4490421607001c4400310440028140c607150408a49991400006051001d00d100500134098050f01c0304402c07050340c0d0104c88880c5542d80f640340081c690310503024010a420b0012032100020242540035010046901000740700303598a8900880e6524040d18101055115412042d110240c04000a08038140542c071140140716001c460724100fa1789c0c5039007002c001a070025202c014000144007803111712081040901c034 = true := by decide +kernel

theorem cover : BRFrame.Cov 267086330 267266187 := by
  have h0 := BRFrame.cov_init 267086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 267086330 ≤ n) (h2 : n < 267266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
