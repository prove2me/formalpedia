-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3245
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:05:34.793392+00:00
-- url     : https://prove2.me/submissions/1a876b0b-dacc-4d2b-ac63-434d29afdc7d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 583453237 ≤ n < 583633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 583454487 1250 583453237 583453267
    0x207030b0f060a09021804230103080304021504080304090b06161515030302010504020f010e010203040603051f032307061d180403081803041a0c10020f0a090b 70
    0x1481c141c1191000c1000448a403100d4540d5030052414060a40d01c4407060300d4201d081245080c0150f004d0b41c0303481c081c03040b001a20202c0100b154800010441180d0968036248215400244143d0f080800303a1006009405140002c0c4010441c410107951100e0400a2250660703440081d042c2c0716140030300485801c00741048a843e00594455903030407000c045011844064400038105855038660940d000041c96010342120744554804c561030482902c404005603250340e00304a4413401a4021700007489454004e6021541000e540d51b6400c040d451041c004034107003526034000702e9010082d800000f4224200a50020b81200c0800c040e0407107505014004000c0300480b40d0040600d00903010740080303525420120122000c103500001c01a1500d800d0141034800141c45c4a00403540300c1108070200c40020096800792160240082616074210448520580000c6d905241c80d02500078003000c0341e8201d100402800304903140c4e40e9100d0b1316584000d41505005c0d40030030200c000c1007100d000c04903a90 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 583455737 1250 583454487 583454491
    0x6160806040902031606050a08010801060317070f0c030f02010807020708031c1413121403180c030715030c0302043c0801021201051801090c1205010b0c0c010207030b 73
    0x141ca001403021041d0002a291000b040d0118000e005c461901150300c2d50300100030303e41e400c44c94445000d1640d0340c4500c18200c82140c400a85134100740706800c031035500b805c0010030040c0c3c00b8a01c01c11220000f621050088035080c3d104a85103101c540501003113507002a130007640701b00c040c00680141480c011203c0e40f42d00c00d11025121101e003000200482d990781e540501c5000d03021444400c081d141413507001c400da1801708000d80c3c503e56036070a08100d0510981c02d0541040c00e0144040c2075444101d0b0160300c00b4444040b240b803034010100c1441d5181c50801100300100f40c45100303480a002c0e0a0b501900f118444a03628040500402c0140102903004e41284014441911600958213001d0040d0085440d407140b654014030000400240540e8150098004c4070800e250140c61641d0380c000f000115500300e01600d481601c08401003010721260b52200c070000394113081c126150740c2e084194004542382600b03c0c6100304008100341e205039400304032000c0e01600a0004000325419500e81c0d003094200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 583456987 1250 583455737 583455739
    0xa02100503090c3f010b090403090902090a090c210c081303090509090f0c0901061209060605060705031201060f1403060a091a190b0a031808160506160806 68
    0x200304051448400c0c1500311804030000241c011001c00e0340310500e519500030301c0d01d8821740c00d0031295112880c024250134011503260300c0303607481a460280aa4080c0d0081c40069074004464200085d00c1805406058101c000f55910310940c0301141e0500c08480c0700c0c9020b04100240780414107280f40741c000c580c40ea080080b902d40d0f9241e5030400e00c0c0c120f40645c010b0300301a40110501091180d0034034009008119880840165950315040200b4080f150200348107080004100d010a0003c004240e842250380d0b60017004003007602601c400c08074016500446045490343d20000380c01c030b000a041012140501024030b03240210f4041c4020003000d410300e1000062803910000046800c5944440c6d40303078003c050103c02031151510b481c525604049540b0584c0d40207a00c8100000ca000c1c0c003583c900f0b41504c2584012a00301001d17110120300415007000d00328510f81c0b00d032211501190407600a4802030202c0880d5150400301450300a003000c1001e01300c01c1450f10600e40d80c01d512500b002030700f540b01e04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 583458237 1250 583456987 583456999
    0xe0706020a1b0f17010e060c220801020a1d0411070b0a2004061d0102030f1303020d0c051f0519022a010315030f02150c0106080a02100503090c 63
    0x14010705104a003a40e507000003c000700701d100c0000e500501c00c40b80d00c07108480c00d008002041036100f03d0f80c0c840d4000c40e00480110000c0010710303140c00b000201030a125400780c00b62085151500022800c9902c1885c40c840801d0707c00c0c5102070000c94500444141541c2540c06200c10007000200103003a015414000b4490b07641d9000094130b411465000f02c51100f40b0350f03070700d5119075410703110040d0a500c90302035400021020741c06070407590754014611900903c1a070080d441d0001086060039a50881c945401911b51000400005680d40714600c04056014101181c2c05074a40810060321002d0450780c0820031034013035000d40c1c0d40c5422a05031504a06002500d0100419448040781080d41c06000780341d15005c0d054141010303c1400ca0f41080e0101e00b0380b03080020803100ca01742504540503120040810b00741c02e0080c2c0050409141c0e44402c65182c0c5450f90030000000402c0d42940d15a03005110307907a008201030815807602a03500d031040800d500701030b807031400d140b05000d03150040b0b4102c0c940102 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 583459487 1250 583458237 583458263
    0x30406091703040303021903090b060103110d0e010b0117130f03030b0d0609200604091a130c020c0603150420040e040c060207150315090e030d0e0706020a 68
    0x40403100708032201d0350281900039580c0c646407401500035081741800c598502e0314500102c02e00350280c4641c2020b00d40110807486950359141c0110050b01403080050745140043c0446140c0d00024002c0c8810400a08004252040050001003030240e0a480d4001c09002030824040c00c1311900c205041016000000d40d01018034074141540680822520190021201e440813418808107504c108200c0b889407120501500345102c0304400d9450328910325a02c0b140802c02009004840c0d2b03c00c0f0050710030100c0b40c0e01d034400c8450000301c8546080d070280d941151a400c0345644c1a50600620080707050444800342541003000d0000c410b40288042240101e54be090702078101e007030b406107441a018014030590b5880d520f030a00c4a010030b60030f880c00c0301c240440600c0414458000b003412800d9482142c0d8240c511801002d081300985429079425001c10200030000c516002a400341703120b100085001542d035600e41c8014241101c0008d01580000d410108040c4052036001c00e485603480d402c503000d0b042c2c803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 583460737 1250 583459487 583459493
    0x7050c06040608040515160c02031606020601060206060a060e0402070201120216060f110901080403120f02092103090d06140103050604140a02221b02280803040609 72
    0x4052941940d40114046400140260300c0342e000361040c1c3c4a182500c58070300f2002d22640c0b02080c2910511079964284251200b214030400b00207094900040c00c5603101a0310b01070f800c1020321243c100d5030050708541d0050040903010060075402c01c03c2134442c0000b907031900600500800e820707411a0300c0b81d0780008840003960b210f040402c1d07450608020865940e446010100404030a504040312514181000120381007200e03c18240f060501c110032520f4444c42400444803004010011000d00081001010000b80710348a03403900c03000102c44c0180e50314549400c0100e68103800030064482d070550701c1d00d01c0318880302100399500d515007030340d10000300301461038000040d1400c4241e0640300c0c55240300002c140400025000d0080c0c1c01000503c003032810a0b0072054580700409000b0703410035005070621024501d030303040301001541c4140c00003442c2c003601d01c60900401506a0f100300140d0080500400881c106170042c09840300c1c1d80b039101543c004650701c00c0a1400002c10180c00c49907075000d50424 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 583461987 1250 583460737 583460743
    0xd060218130b041a09040609080403050f071703090d03110703050a0605041b1a1b1606140c15060102010e1c0306210204090201090f03031115010f0303050705 69
    0x2450400901e030301050000d20641400a21154a040b0710840c185086243c42c40300d40003144122000140003400942e0761510b4000280920340001c44200000b0040003012620601c049000140743d0030282c119a460b0001001342b14040140e001120340040004602d00e55512100c405060350500342405008840040c140c18101180e20140c401e006903480070081010a80c4082c3c4910f10404044003003411440140000c02100d004107450a040e0740c004201c2d1f2024132010701f0f03458607020f60342d0784040c12200c24103042840e061021280d10300d401d00140241074200000080074490148081c3c04c00440807201541c0740c607040b520700903c824000120303449900c00e40103450f8481d10f181c2144c0c40f40c81a0714084044891018610000078504034020840700c14451045200000b00c141e5141c060300785808010051000316403c80c18041d074881c0c00240340c0e20041d60b901c0114060b4a4030300000c0e100002507401c080d440c1c0140281140341a0051190420041e1703c01c040c0c9816240107502c070032852410901d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 583463237 1250 583461987 583462027
    0x32001050a08250302130602010501050303041205191a0711070909050c090702030d0c090e010608131707230a0803040305040f0b0304120801030c06120908030717150d0602 75
    0x40c401545114070340e115130107800901d004505001099a242c0c0e894204900b212000c2c025280e1682040108011030400c81d42c0000e00d4034090400e8408400d583c0d4082c030042ea5a80c00c048500b40c00000740030060b5908070040c20b90141d1207040884925404140ca00d031030303280e1170041440d803503594680101808010001c400c1c6158016040d171840f800c200c070000e0742e44d4000c164841001400c089000742e0f000d100324000c0c001c44060402c1c50103241d080140c142ca60301001080c2c00c5001d0180729201c1d0124051001701321030090344078107407076850143d420f101080c1001d00509005010b1140202c4440030130010f140c00c1ca540d04110820b403070340c40c0da1608840e00c3c80b0396400b200f45041840408103580c1176007030055010328070503009080c246925910540381c01c80f0904c80505171070100d240402c00036004241c0e41080201440c00016440313107599a102c3d254005550b00b80000700c0e14101e40c06842c010115150f0880030052140e5141c0002100245501a413860020302007a000b044600000302c440704008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 583464487 1250 583463237 583463281
    0xc101e020a1203090b010803040503030a05091c03080a242108030403020c010908150612010b03032a1c0338090a06050d0204090c0f0609032001050a08 66
    0x801d0784008031002409042054820b0b600b80285d000006082c3d5000400c413002c55202501860070b0054400040e03c2a070011441180c1015280b02400040c981102020030b03528400d883d400154100005141d0450b018140c680712521120500c81d221200c0c0400e00394101c401390070043c0048038502905100440580100402c030b043c1c08418001015004688a07441c2c40c800ea07a90481259654050340da101c48495100222040740c10204025080042000343d0740070546002241d0000100003081c61a0700a03e41c036032007482d10b07048441b07802208021300c0034071803001d50040c440b240b464004407801c5070078040340e101410354501542400030781803101d001e541541c0040c02e4100c41e091420f1294082403001015105c1c01c0c1d140001030b400e01291041409441000e0002001c0000541c00e101c000c1107100320998090021020000c2c03c0c010510110026000c1741e9550a0203610b180b0b845061054891000e80442c40101449801ea981c00800e90f214000c203403820202b181c444e500300d03e5240c40010712071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 583465737 1250 583464487 583464503
    0xb0d0c17011404050d0212070308070c1e110f12030307050a200a111903030e0a03060216050705030705060d020d15081501170a0b0709050a15020c101e020a 68
    0x700c18841c000c02c000320ba401040c3c091f0b5060310001120403d0a1150303e0340100800c107090003042ca1315224104204085203e040400c502c0c844d4080c810b40e0b10f05841402311b910f244240c00340b40031410450b2010002c43c03070644112200d90000c5900c0c94990000403c0002046008910107008620880015084200c1d03100d28071182520000325503200e00f4901c2040d0b4246036008541c0416080107012100d49050004221242c00d0840c3d0f000c842240e804411560710070030040c001b00100e80144014030f0015280c4a42c0380607006649000c900b02003a99222500c646c014110030819038560300b0858449004003100185c1d0b854518400500a0808401c260451140040f001c81d1302040043c10f0741c1c0b0160b450304a1642a81d0720412118609201c0b91038000301c1d080081c6180c001220385101c550090342509000c01c803651528042000000c00d0342c0210300b10303820042d105040c0f0b0f0b01440220032a0905403060403003000c60203405884a0809621016519a40c0031400c002d644203000c4130501c25444984 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 583466987 1250 583465737 583465741
    0xe010b040e07152d120b010e0a090c030e061509130b0f07051b03032221121b09080d2f120909060a03051002090a150807030b0d0c170114 60
    0x3008500050250700d2200d02c1c1c50301d083d2540d0300901070319823188001401000120b080c109440060b2001d400c0d08018592110060342451400b0b029003403048031240c3c004a07400c040c8004200d008100540714144200b041030103200401d5030414a01c0c0d100d12240400c900686a0020440b214070502e0f00120400440c0302031800a2640800218000d954409500c164080300a00454086a039103c000b032001c50349051000f00c091030050401510384a0381046110191640e400c0c0c0251058210341d06496502c51200c0786605800076411405401c00d00024240f40d0303151040640b4140002150780c0407480c489959640340220722801c80740004101007030729a40e100111303046501c0d8110080661141018400040c01400d081c1254400c817500903005045046400345030304000e51101ca405c5030012082840490450715080d400c85400729181d0b90301d2410310300150000d0483c0ca40200e154031a03840c1101c1c0300c0128041c0c000070070540701c200081c10f20715003412801a004040c403400c00d003150100001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 583468237 1250 583466987 583467077
    0x512090c0111030901020303060d0804080d0320090d020d05070825060c020901091107060614010908160308030903040f030c030b01050d03050d0e0a02040e010b040e0715 74
    0x2100c456412080e00d50700c51007079201401c60b4490140c207940c1401a8000c0c0300260141c035101c10458140c030700540080d8502501c070403425040088550190b008251180c580c2d0360019010300e8000416805010401e043c141001d0025001e05040a0f019110300141c0e2a0441070103000d0007984000c0244408859800324800d03002c4d44144580859110440d52a0743d00291041c001d80f02d1070345681d07000b40014231580c00e01741035500030054100205400c0000b48070240010f503070b601c01c2c90054072115000f403a0740c807201c400042c10500c5c03941000c807581d001840d0440206440d0841e101c10350307902c40700841e101d54801c0b450500e5806164018025404003520003c1404100c454034400e482c040d0b1403884240e82ca030b43c1400341e540461140140054410032508600350420380c040c0681e141088183c0340d140e40c90b500068161031204140d140c19941d0f41c40c007051646840d00c00d070303030aa1090101500407649030a00c81103034581c60b0700780a814040407020038a0031a20f141124442003112122001c20820303a01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 583469487 1250 583468237 583468243
    0x1406010f14041a060d0e060403051216020606040e01090c0b0703090803090306040609020409170415030b1e01020a120c060b04090f06020a0509130c02071d01090c051209 74
    0x100c52908100c005410800e40790400e03003d218a000b03403114489209400c88000d000e819840b401040344d811b6540e5101c1d022080c002d11496016601035920036480b542c0310500305071905c60140200c4281c03181c07041218040c070340105190307902c8170b030403500044c41c1036004881274090100000020005500d4020102e03081b0844ea014015041c000c1d0341e041001c03510703003070307601e540b40708928045078158455000500021400e420002c1280c5c4081d0021614414540e00c0c2d003000c1c1000018100d841c000864103106c0c0000120300c8070110070041c40c0501080c80c0500200d060750840081a07403040b0a02150003401e640200800c0450344c0e0700c0044207941c61040e20b4000d241c40c2d0340c0b178000c0b00c01c0360a0159030031403403420f40103040442d5040960858208501d80da000b000750b0081681e0000d00c5402d104414466039180e00307004040540c1c0c1c03408038201500c80340003800d25903244c0180700d60340395070700802c1000c084ca10341d4141912000840081d010036146400d65a0340a8a440e5507c112182c20411034144004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 583470737 1250 583469487 583469489
    0x12090303090d0504030c031707080a0206011e030206030f06190b0702090105040e060f071416020405010b040f0e060f131b02030306030a32030c0c01080606030406091406010f 76
    0x410342d07041109800c401c541610580c8401b602c031071818401400454031101d03490620300c00500106103000b0f5299036050103a04032080c4000981c200c903004102036400b40009944c00035a04c0c1c0400381041c219800600c41c4e000c0640452515442040000c0e19502c407951750a00d0340ca42d900310b110610390b03900d01d20b000c20303841114100d01402440300002030906181c0075603250005810043c120954580300440004035004126008004403503801c8414090010014440c3c1201e00d98900d201c100c20340180000d590040e0320890411008000402000c14140701d54825901e803102201c2540e1610700004042070301d06481c45a002226010b0a0b142d10303943d03403116002e10641c400410031040814400c0e0f0b00c07400304a07440f27501508106000c1d000503450802640c0c145070b1403180150035031a0204a825804a141039001c3d1941c03001801015010041026298600c0c0900e41034440d03140c074602055603800302800062009445011000c2005a481c42c1403101c210041c04544003981e440030111451009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 583471987 1250 583470737 583470751
    0xa03122702040b060309032106090a0e1e070602070b09031e1507050c150105100f090806010f03141b010c231b04050402060403020d050307050a0503030703050610121112090303 77
    0x8581c02000c202100d641070284528030040c00e10408bd601d00303450601601894401e48a0340c091600c00c0701c0c101c0c01e40c003450703040c445496004180c824140400a850601181c00400411206001a030103d54000035030342a00651410228041c0f100d50042601e090f001c5003803480e5050a060401c0003c99000e805840c042154008a50744460305c061b0940c00e208081c000c00d50400000000d090390140900018154030001c1d1400403141d540d1549014104042a00001c0510b0b01003c4100144640c52050f0341c450038440000d040074080fa103070042c1400c1412040507050010506c401000c3c010090b026040700d403074200030100d500130038280701a241c00e921404000c400014211040c5a030500e440f820744140d9001d0f01c402d14007821a000c21480490300c140c1103c4600c42003100000140d010300604480d64407401c02542c9034102414050706880c0010509800340c0103030140c0302e421503804071005840310082200061807140c41c0c45101558414422038015840c220b60521203800e400000840c49105 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 583473237 1250 583471987 583472017
    0x12010311212a01320414031c02101d0307050705040c03020a080408070512130504060e060904031d0301110c070e280f0e0a03122702040b06030903 64
    0x20755030341c1820302c99008894240c0091403064140c0e0110319407106205800d0f0001d00d400c400001c0340f1900010039405900044074102025102c00383c0380c1010003400b00d810f261040d8100701150048402596004107030101860a5110b5141c43c00c100e46921100d0403014500781941ea032401ca03410666595842403148500842c5481c0400300d24074828801c4d141201c81d40c1d079501140c1c0c0c41e65150f801031340c1c00145007924140141c40b0b8271442ca231400b400078890f001014a1200700b00d032901c003c0004035a01b43e031101090030b0b000c40c108039140d078400001e681d200f0f502d4240b00154078004071194035500001402c1c0c64040d8681410b0440300a040800b43c0000600034045076041d540b0740340074640105095804148030804040142094542e40f075402c0700030041c14200081c1e2881404514060340d01c0302c012034100c0d0304150b0005c410706911261700203150000326030603c030045e10704078450304c00032080c00e009101a00f003841900442d034880e00072a0a0740c400605903522400c0115079684c40307900c14000754070340e00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 583474487 1250 583473237 583473283
    0x50a0b0c070e0106050706020f0d0c2106060c141617060a0c1709150f010303020607021b01030b0a0b07050601081903020c040504020f030a060506151201031121 70
    0x802d50a58040c180d8829540c1d2605284050303071100301a4218070529541d5200511103500e80000342d00c01e100c10700300340d81c2d0f551481000c441c1d26219555203940145d5032075418036405014482c2c0014034102c882d41d01010740c003000c484031003000341400c0280300400044803a020380064211251401200b001001c2e105071102c0d03403031307000790f007011180c0980c411000300f50f4142c142e000040f0091522a480b0360050700b507411030b207a034040308455900102daa20b0210201c0c00014014180e04124181d801601c500080042851500c240031517158120803c034109600d1308000440c9441d486103540052400c2020749803200203c0c40c2294842e0001d000c0c5a00c0b510501603110302d040c0b00320302048886509500038000c0088840c0c148805440c00501c00c1e07030052044032840b40191000c0007540c43c01801444005010f0420b00100843c0e5152140d4030b50648000740b00c0d502690300a4210346044030b40c00400301c80e035904102c01141c0074119150700344440d00204190b508002201040c06032250000003041d944c02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 583475737 1250 583474487 583474499
    0x4150c060e0f0f071e0512070806010909030f05090a031b0305030c060105120a150b06160606031502070503041214031201050a0501050406120908090a0605070215120c090a050a0b0c07 80
    0x20300341000c04036118408405e0400040c10058100d01250a110042c1c1d0380e441c0e103c195640ca4801c0a03400580e0a507a1000e200c41459072003070000c890381c07105180080c41c000104000a0507070351580405070900ca044040002e039840b60040000003140e20800760703600c0302c03142d00c01e040c1c41d0314007441400d02540d1a8642d101d98984c020800c160215880b0b1010300c850501000e41c0c800615002d003585801c800f041104490601c0c0d03082201156610800000c150740d4250302c2c0030b80318109179103001c9684900501003074000550110503501550500c16240c0d1109005040041010303414240c1185103010000d0401a042044141c02d811f0b0744042ea610445181c1da0401100c19200c2d512845000039412109624016002e401180300a8010070003a8281602d5400080c84140c0c16803010001c0303440001c0c91000c504208000c0d55154200300e40316402d16010340c3c00c412101e1401400300708048000a80c1d145655205490400034080240c40802c0007500e401d0b5440b240c0d8480c1100c041903200b00d04001980e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 583476987 1250 583475737 583475759
    0xe01050603030712021e250f0b03040204110304150c0503061305090a020301062d050607080d0f020d050a0b1f2627010204150c060e0f0f07 61
    0x1a10029005510f4803507251070f85a56210401c0f8040d0460060400501d880b00078106680c0384900441c010700000c01030f01d02810000500c0210500710260807103010000420402c02c031200f1226900d030002da403960703a4400a0010100a041082c1da100e010040c40305001010794405c24941480d042003004010f0f4940030348003030001b11007065002c240047c0c801e0080e0b0840d080a038120b11404101c4903010003903800642951a03d400c1044880003110802c001c0503800b0072959800304030403000184150a11000c1042131142200160030064006006018600103038001880000d042004548514500e40b804c00540400e444201c40d5031b04010f0101d050b460407140c00c2d11031440340102e50840c0c00758180c06403245981c0181b81c41c1d2407986400308030b42d241d4a00716000d228421a4111200301c0c0140700d404495070990010f03400d00d0340e10600c001e015a4000080c3c000c408056814400e071101d6041c50004041c010f180c4540ba000e001d04a03010803041ca00281100c90203c504054440b1240c5502140407 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 583478237 1250 583476987 583476991
    0xf09104e270b0610030207060c0809120c0a0602090607050d0923090a05130609141905030301050108060d05030c060411030c0a050603040302280204061a19030f140603010e0105 77
    0x40b040050001c03802600e89648031907120f03501c3c4d003405401d0050300d032075a0782290320280d161404180c80f8820003010180a03c000c210b000b030400d460609140301030070300c142c0d10241f1010045ca03aa074005003022141e5594130554030515484002c0740c0058017071050041c110a030b60701c64280da1420781d0f12264006000001ca1070b40049020340071001c29603030840c5038806400f000d044000380f1070700030039480042a0a0300910320414000c11101c5c40d080c1c1a00883d600c7e00903111801a80e5142003c20403001a0b0f0200480e0704591702442e11103d40e455803000110540401031000300144400038485002c100d01040a501c02d500550000381f0694990701815180c00310340b0741103980b21802c95011b100a1a01d04080d5401c240244102c3c0c0306694681840201c200041c000c0c203007510b1035448020114513090107558050180e8210021181c03400300e03031200050042500e9180c000c40082e5208000324426800b40d400d0082d031110600c80010001e2002e6804003090718031600039420080c41203100c80c0140a558 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 583479487 1250 583478237 583478243
    0xc09051303120b04020f130602150106180510030b01180f030b1e040309140303070c030201050c150709030203010605041b080a0b03030f09104e27 64
    0xc120410340d40c110b94030051080e44226080e0760300800f9106407541e2014000c11004644400d503246034400143d20400c1140d03000720b0031580068500c181100950023030034111105400c0c100f244c001d141800c01c110039841d42080c0d80000509440b40c0c0803a5041e0000d81107117001307890788074603207400310043c1d00600024024820149640382e0f0420000d15402c0701c00f680098500d81100003004004403582003480143c9044c1d00003407051205009000501c170740b90404400c01c40040d40f5000742075070b83c00610401444081e05108011800014445003802a543c5c40844415542041d203401800545000c1407404181d000e1343c40c000c008a01400c080c8146410b80b80c045480d107400e0024928201c2d004031004180ea003c203501c815040000e40c50800180c00c0c011081803609807100d40040c14801c00c00c90081220040002490303141416451541c4400507031880e8050400701c00304280181600000000007020a10f42d05450300c2c4000040c40d40441c0d0b614866400d01c00400c801111001d2080c03035550710203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 583480737 1250 583479487 583479511
    0x121305180709170a02030a0c1a120c03060111010c0206150a0b0f0708041203020109060b04021207030527031207080f070516020405040c050a0f0324060e070c0c0905 72
    0x3800f541d600c0301c8074004241d101800325003003059258003007070070290200422260007140c05c1c000d11510803070101d40c034081c20030603440c40c2c1080000c00401141c4100544440c40d0810000082002a4415400081541203c9000703010303240462600964900c021910f62030406200707080b103000c03450068018000c8407200406107045c10003a01204401c1d030302885045130709000404c4005a20048408403260060007500005410a4281005030642d41102102441584100000c03404030303001021050300556145000143d42c0c0c1c4040008220f00b82d01d140c0c0081860000740c02c6004508000001d00383e01c0c203a20031400c4151a0360000f039900f510309480102c14016440c0008044a200320041c0113500c0071214116800381d41034010504482c0e0549066070030f540c0040d0148994280811100014070b8000c681ca442d251440c1c85a5249120044810030010a4500100183c3c0740c150098000740100240800030390426000c05401c641d4210f00480344041c201d00f001911602071701ca0584192020301e80 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 583481987 1250 583480737 583480739
    0x3020906190302040b0117010801050901051e070c060b0d0506011e030b01060e030703060c030b01020f1606030203060f1c0b0a0b01090b0a03151d06030105010323121305180709 77
    0x2040301802c184605c2d141001520b240c040b1441c00c1c0d000c442802000b5223800051142001c0b04e03600c1c00d4980c024500d50b203401c01c14648000b07400703926420b15031018043c54607490701c140901c3c1400c050414080c11603409a13070300380340c08180b200225607503040340c0d26030000ea4010b601900070007408404d070780310203040c107555600100105400b40c041c10300300850090076209a0354a0f60382c1c68049810740c40e0403400090345c03000c9140455804124226004110300001e01400350f0f1504001005580d80c056001010340110225249440307421081c101071a000701b600c0c82c002180d03d118080601c5054099030122101030201d0f6090080784103220f0029010307900c16020354240412103400da840009040100740c0d507011607608006020b03421101404a40c603261b034075002c521160150f02d5170050100c601c60b9142c00d00400000b540b410354403264080102890701140b004003451800e200706008000071086c0000b5a0644001e010350403c0e0075101e007100c440702209014240040507945c222100d401180031000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 583483237 1250 583481987 583481989
    0x1b03040305070f020a090c020c01020703051f0e0d05121b030a0e0a0c260303160c05160f261002030603010644070b03040c050603090703020906190302 66
    0x4000c2c04590302409240701d00c41001d40c00b01d968260746600ca1025aa565a146520b40740d05210020303281200b40b0092564a095850303403a194001651003441c0c0001e05e02070717605865101c0c0c10003a0a641311600b42c80100300310301c4003e004c40d888400300981c04103040001541c543c04440b1446074940880707980605580d10300c1043c030b000b000c8020580b2060b101c3e0000038400528421000e502034200024880349000f0344258403140ca845402c4c19400b982c000744204001c01d064540c1c0b060b03000f0700500d4070b00e13161003c030304040e818a2500c10104026180d5413102080130340f00403520780c0441d520940c0160500761101c200240c2505060401500d60708000d03116014a6815000703142c10100c000d00004155507a80d5612542c60040e60030ba03a920124210b07040a1840c1d0800150007500c0b0038a03030b07134002040709180e4503240d144078003503482038010202c089030500010034440000703040041c040942d40e04151481907910450340c40101d10070050000005c046007002c02e50304410303040f1445110b0f0342900303541c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 583484487 1250 583483237 583483247
    0xd0507030b0c120430140f040b0406022103042f060c150109060302030a06050411120a050705030d121e0c0f020105070504050105070803060a0302150a081b030403 71
    0x2d800045803000a1006808440c60310304a180124407420784144455501c0700410101c4040400d441d8072100b80810039501507820080310f02e5400d2840190340d80d1501255055982e50143e0b82002c110410b0200300402c80d55000548171010360b030340364820039404e801d100324801c540c07104a900400c0c40c0c20504c40e0805044000782d02514654001205080364440c81c80030808540102e484000c541d481411268003246801c00603a0252031000414010795045402190f618009040010140e903a540002024410400da00401e081f00040c001c407210b0340c0c00c041050b0f44594a84058805000d0503500044c1c900e400910080e000045032103800d15580895910300050112884482c54106042c2d0055140c40c046d114202c114100c0b5210048a00d00e4003c000f400c40b00005c03c8841808020070080c8541c1c0e030010160307114503503c800400c0e5030741e60f0b640c08582e020301d240e4802508900001003502c07141d1540e01c00740c9000c0081c2d64a00d1465980e040c191982d01c01c40c0c0c04901040d000400105020921807 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 583485737 1250 583484487 583484491
    0x709050d0311030a0c060608070806061e04140601110d2703050d050705070b0403050a0210180e090d02160306052806170307030801051210090602180d0507030b 70
    0x30304104240c40c02e8880c0450660b4490070284000a03031011510b0f0401c0741a103d030f00d026010742002005e1007810071a2559039180c0c05401c181c8104024040411a4190341d104440d201c04045e10500804a1a00b000310128006942013400305049000400c0d50302c0c070000d0740c0031822080b595a403d01c104501841c02e0303403283e1803003201c625058000c8048041001001041c41074600f550756166511400d00b041800c0c141c05400000000c10208010030101c1c4002400815130b0740c0458402503907004500c401d40d14200800c1c202d420740c024a0000182c1c0141e0215114842d080ca0f000355030b605001c10b84102d07111020022507180002c20302c90140302241881d80000d03481000b000c1e00103039000b4a951100503008103c030385902299107595050000140e0450b103c1d9414010400031410400e45036006000c00a0501a03d40190b080122074454401d080001110300203130502c0030025584c440c01c20001940c448130320074001151490008160342040d00b1b0b03d2030426085800b0388203550a56440302c260b0100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 583486987 1250 583485737 583485743
    0xf02060f07230c0607030c0f09050105210703050a0b030111071401020c0316020414061e03010b120a0203010e060c030114060f0c0c10140703030506040e012d050709050d 74
    0x1410b0340d800500d00d09900800c4900d1048005005502c0c01041c020305403003d00c40c103035007040849461403041a801c4414601503840034203010707441d41c200514074002c01c6010f20303421021600d000140406107800d540428001e01400b07805014400e102000e044c243e51810301c1c003101c0d12100b0009880441c0104e1405280640e403a0005450852408407062441d0081c0c1e401d5001002d40c5041c100451031b0500c03841d00340d1400c80c4145c64281c90f24200180d0318245601a540b00140001c0d2850103541d800e5100b04d52018004040300480b49014824507564821034800300d0196103096901c41c007112000955601c60380b0300d0303c60149943c1c204100e00800910307a6204e681c004205200301004101c40c42c01400c0c0782d55444006040e21400f544c200540b101224003600280100b18078140582507066044800243e05414040f41035124000428010f0104040c5400554a0400b803040e9144c158200e001080381a0000c0e15010705003000da80302207840582e00100032503540322003080141070211030150b400340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 583488237 1250 583486987 583487027
    0x40b090402041d070f0305060a03020d0303060b0a0e03011a0603040f0c050d0b0703050a06031106070c0302090f1801050709050d03120e06090d390f030f0f02060f07 72
    0x250715251101c1071220895400420304000d402c0051040d80206400d0310b19440d46021f200a0910304003140d003d132503500019008403441d80c26401814000d421840052082d482c0c81d550b100100800140100100c050443c41b84d4240940395050112010a81c0270034140140040e2850703c03550354006000c0181c590440b4118200709000480d543c80c4031002d041d150051484920520385020002c003152001400d0600052422a0034800b051581d000c1e424441e1003910201c0d0381d909039007480404c0c111940d10096014041004000280000041d0140a0506204a03107030024403540b481d4203854085802000045580c1e400704201d1421b00c060041c050300a00b400480307484841d10721010347d000c200c1c122085501c0081440f5100200b00031800920742180780002080803400030700000c64400c031946030001c4821801d0300710800d4084c550207854503480100803206004520b009804800304000220205103120b2514081c0703400410f1603481000c040742c602090750fa8408043d00c0362102c031441c51080034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 583489487 1250 583488237 583488239
    0x5091608100f060807120e0d030e0120040801050c040e0a05071b110102070f030b15150703030501060e0603041110271a0a120b0d151505060a05040b09040204 69
    0xc10441c1e0360300060310341a13a071031120340b90010000e003000d158071600b1182140303080c2032070040807030114081c51900d6080c680460740000c01ba441a014003200c20f107032464000360040308019a00b082004108851826000344123654401c225080140030b070344140d18510510400003079040d4802d0344040e512002c00e040400545061241c60148070070080f90071920155883c2d800c01c820341e0100044001044c40f0942620f040c1c0c1580d4a42d001d0301c00c05441e08113007007a40d44080007a960340755000d0765155a20880e00e0f03120340143c14018003a040030322456011901201641d5490300788841103d101c0d079042140070415000b04814058a0090040d101007000340200d071024411546092100b0b21980300643c409170070b41040c40070b0b192415035404040c03025408101c440c0c0030940001502e042d07c1d241031400140402c0d01008208070800c0a113004061000a034000200c10485912907100901e45c8084c4803051601c0d88240050780c0324440207000440c1007400100f00042264008050701800130744094149 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 583490737 1250 583489487 583489499
    0x5060d021612110f011b03090f1406010e0f01051e01030b19031403030403081b09130f050703060f05040c0e03030a0201060302011409010f0c050a0b0f07090509160810 73
    0xc50411040000080c038140001c42940d0f104101c1303501109240002000611480a0012180c0c00c508049070300303258481100f0814428001500d024142d0070940759101c0b025050709558542c0700900803112901614008580e0344c500c0c400560341602d802918607403003070000103520806100074012050400d901c601c1c5c44901602e03584a240d014040540c26003180d6801c51402c42c00000388005540c41940c014000c210110341c0c4010490b8000700d1160515001d090030140c004554884c510403150000092060104850050790000303d0003178032030900f00219100c59100301d050b11403901c2900c0301c0f00c20410084c8060302d410780c4104890b08060402d202003200850102e400c42e0019455040540d549820410640d604040017403820240400403034a02142000041c00c02080311074282d04000d401c80b074000401500304561840c0a8003d1000380303c500d0584a4001c4040007201c40c0e50011340c0f03920700043c0c2400c04c600c455000782a004104003d49040100440c0c0404004014041d002c004440008030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 583491987 1250 583490737 583490753
    0x30c0904060807080d1403040209060a0905040b0709060c0b0c090102010f09080904060509010b0d0c030e010207050d0917070b030901090c060e19080a171b1006060201020405060d0216 80
    0x207200340740140525a181a00352805d00302206a1041448524800d2881d182280021664025412240110395495410100e4840c981c1500620000e52400d000c2c44107100d01441c07681c0c81588907540d090129501c035a805c48018440f2040140b071400c480c404195400c01140250070703440c07410710000039520003a070040001d803145004180c401010000d210040d50034140580c0d000b500d004d0340e0f034003500c3d45441c0540700d00d4400c0f02c0101c18000d03a10381c0c030b00c0750307041c031070303000310451805240c02036456128509005880d9080840a80d000c500700d69400a0300038000880c0554071424580505034007440c002070311407240d0004040b542103541c8d40003414002503000c00428064006a07494103a400c070340e001440000790f2000791030051302d20286420001060001150100c9641c40b10340024003401121402099024400440921250f40c3d2040c54007180c0000b40030810821900092008a54511060707080f84034034083c0c203801105c00c01200040b41d09980042402c038074040f40700d4812131001d450b0064 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 583493237 1250 583491987 583491989
    0x41803030b0f13050a0c0f1b05030409060314100c1d030313060807020f03090a031104090c0b070b0c03040b22120306170607050412051c08040201021c0f05030c090406 73
    0x610b0384d50f81e001d000f1459058414126081c006050100c4c0101c07161201030445554540d40040c00c075003445540c0100071007442941c004261540e03090040c42e8480c50500c1308012503402c00400351103110490b07180310445010f41e11010000d603d801e0410722075107450913805805480c0d100d0701440104080300170140c0045803c001046aa5286241030400d808000c2c100301c40d030102c5107a90b0f8024441e4a1107aa10500d05004a0b40d0003580d80076602c0b00d10001c10003030b100800b000352070761000000000704c00c160701c8000c2003011f2040581000c265510441c0c880c040c0025903016018860880001d2580003054a20706450294024410000c40150ba1030040352503001c8603e40011780c68010401c007800400c10100c2c5080b21a0026004910300394200600c58020751151516419050b4690400d000041c44201c5844006450721620f492440001400b81441170741c007240117200c1d5070f620700c1c51410f0241d040074401c0b1040e0b986c0e0111010950303084910381c00240401500000400040c01d2955840c42000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 583494487 1250 583493237 583493269
    0x90a0b030c0306180106050f180a08030a02010f02071a0c1c090c1217090f18180f060a0902040204051c0311030f030c07030504051c05010b041803030b0f 67
    0x1d56030349040703014020705501c46003c0307910341110100103000039900035041c3c84c45400d002c0100c5483c1c0f088910761845034400030700140c0d0403003011b1300c01040100c400320050241180d01c3e00240103c00f09090345400302d200c4d809024000307413829920500082c0c18500c403950000c2c0c0454039503041808041c44000b00b81c2d08038640e4810b103603407200705004221100c1044c00082c0740b0b074a40416483e43d0351b01e580d00e01e512004d00070030707100c2400140600c50340d4542c2c9802d15405d8014000302d40481a40f4014880b091050701e002805140441011950303040000b208011403040d0310242017503403545d441780b5000d048500700480c1d000d502888045203a4a4200151119190401d2100c100d1101814068000e030b101c1d03050400280c104001c0b1840441003001180e0700603818115035179035109981001c130703101c1c040d82c2c1146a05c14140f5100c2801240401241801c0743c0c02000200015023301c0304110071a4810080042d545402c002140046030080e03101c008243c5026010b143c81903030820000c0d000c0d804005c540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 583495737 1250 583494487 583494511
    0x4050409081c06180209090f040c090f0b043210180203070e032a030106080105090f1b09040605060d06060617091203010b031008120d050901050103080f090a0b03 71
    0x20820884d802201c1c0640308418002140f03088294004505403060003000c911944d80c038903012500704552542850018440301e0030400034008101917100c080c14070750000794811400c0c0701c100d00c6101030010360f00d40c000c2e480c40c86101c0b4030300d80c805200e078014900500046039000503803000604451a13108004001d000c1850060f90703450490350180034080001900f81c041e0344801070003c030b070403008441c68025840040421204500050009025208031b802004c800e500f00000e010401e4000030b00300003110010401e030744594102400a41d5000725108059034800201d0f0b011902140341d03548250741004000e4400324182d0056141c00301a145268041c80c005605030505030010810801300c190882c88540c09422604078a01c003030622400180284003142c40d0010120382281580000c0c0c0b001006c80005035444a00c4407001403500b908200103034034562342450000b541d011010f02c81c45041c0c0c1e900900035420601c400c000080c0c9508000142500241c50940c04100a00080042d5100c0c140400741 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 583496987 1250 583495737 583495739
    0x10f0b0a0810080706111020180307080f060703020a140c030706060e06040e0604020d060c091a070b0f0f01060f1106010e01050307050d0305030705090d120305070f050f04050409081c06 81
    0x40d035482c0485940360810031f18584804160107401210003845104180b2a0384c68440c901c483c3c1c00300e120301945200c00c3d8140728001c00043d61000c0414040440104c8c0001e840003030f0f840c490154281c3c4244900c4500103500c1c81c0d49251304180100250001c4030351081201c0c20540749aa0f100d0896801d500060118006507041084d1803909018440c480c01c07a841c003030305150400e54017041000c000c0c194000c0007103841d4404440c0079440313030300d40400800c1d101880d511092004e429402c46540095800c0e52484454000180d4203c1500c10450056181030504056070b0b103028000c4071240000c00f100820003178649250407280300c040141a0290150300c0c55001d01d540b5290405140c803a896000e140601341000d99000440d0300901560b1b4000001d0078071541d65003400c0c0008040d80644040185a00c2d50180360310b1009034540e001c076110310744a0b1913104150509031020b481c4e80c0100c03c500104080204400d00060a10380c00080400d84504040da01704110f440b41180000703261070b00d940c0c0c21952120 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 583498237 1250 583496987 583497017
    0x7020f0606091b07110f0a0f120201030b060418140103030e09100f0f08010c020c01020a06020309030d090f0614010b0403150e061311060306010905100c02060a020312010f0b0a0810080706 82
    0x210105106c01c0b02d4035480b071480e007501850380c604d0f6031042104095000054905690180c2c00261003d00d000b00b032542e0761b40d03c0304c0e000401009541414000a032402c106041100340c00300301581643d4140d191400065203400800002e0b550040c10246031f8001c801002401d071110040001c0980420701c001001030b41030084607800c40d04007010700702c1107620810f00d0500c0c42e41c020542668903a0040350142ea00d540c0d010105207903104980027001101d14140c940303018401c241c08004070103071103040c0a0110150242d44a00d01c1c401c00e001c1c0d003448150030041000020244450a5078003d0702402c04078241c102070f80154289641100c100614a075000c50f56420880c001080c8180712004580b40350030750030000c0000b03108a140e8003c40d402010740e255801155805000c811800f940d00034561541c4403060a002034480e00003059040320106040008601660b4810140042e02e14000c8180d09000121004540200b8064080001c25020308d001007803c3c03c090103400b026180586800150f1b9170084 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 583499487 1250 583498237 583498249
    0x10120e010c08090114160203040305070b03060f03010b1e040603020a08030c070929030115240c0803040221030705030310090209030a03050d020417060105010807020f0606091b0711 79
    0x1006035825914214046100501160303209400205813088090340c10300343c3c441030345540300d2783d00081c1103449200400075401d25810002d41c4155004d80e518a9500c4c81a0241801c4c1c926221020f64081000c42c0a04580d8590000c070340c0907c1401040420350b165250049040c03501540c00001b03603500001140640c61100300414030040841e01c40410a414503419140d000304040c0c2070f860424007401c003902c501c079602504454002c04405512010003565602c03910408408909041a02d408c1042daa401007070240c002a102c0316081418a4510743c0d882d401c102011082d40c0107108110703501103004440e007d0403c01740c02e0061140c00196a80d090094104440400c00d40c082d08500d0b00420111040d9140403070503000340b56241c280075803607400c0e42e0000b0002c3e000715000300010340f107840301003520303031500250b044c3c100c3d04203807941101521070403412030301d660f480710744c017401580b010000c01c040c1d062020029500000302d050017844228803c211403103d902c1044c0c15180f82004a40740c1e0014035000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 583500737 1250 583499487 583499491
    0x21801090b060309071829030f030405180c07051504020310050412030c030b030109030c1a060a0e0c090d0f020a080c0117150301060816121110120e010c08 68
    0x442e4a2411407608454056580c000c6004010030901e0f00401200c02402036004080e9918a840c045441d4100c0c40295821440003095400e110f4450200c89056411004c0100d07015642d028121903864501300703060503a0000e001d014040325260070046080815818022001400303101324210720303682802d004041c13800300c804420700380d1078dc0f03040240030016070341484c0619450f00d03908012030101c010500c16402011080c450316019404e01104008055100ca14225280d00ca040b00d82451705964480c03050021040380c0c100d401000100b4107000c81d003285070490368070401903020076150664000104640d15002c2d441141c1d00701ca0900d8582c00c61500c405400003400b000401410022081c0c40001e0180301145c0f13442d40c0403400f88000c21000804070f008801182405002800540d035695100750ba80d000b119244601c03681c1e601000b24601c156010300d40f03c07107900072528511a201d01001c004d03403040349a0342d503814040807010782030f01e000944c05400c2c014850000005640070840901a14034000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 583501987 1250 583500737 583500739
    0x5060c031b031003020f010c020a080a020102060c03060d17091c060b0d12030f0e030a090303020d0206011805060d0605090d03180203060106180b030c030709140108160507021801090b 80
    0x180b08008110f18500008021070380c04542001042100750b00507900c0760b1209202070340144c81801d0110303283d000000e0600d50203200303034204d0380d0903690480340c110340e40000d5640f02d038041c488100d8040032401844960060389103100845280c03621000005595801017581c00c4185016074007420f013808114480c1c000009000e407640b01500314a0340d40c1291460301d01c09031105040e55010000100c0490b5806105552101400c90f5558011144041c00102039884114010f00c0f80d0716142c10303c80c1c400304117107048903900080d41052f820404e144501409005202c0c0360800c060101d40c0740464400d00031903016411402c040d125087e1440f0300203040c1e03203c5400c0104c8501c0c2145070701c401a24001806270449906140810a186041000c5a84c0914543c00001c0b44da001000740305450720b80340002e5005c2e2034283c8909032615914400d80e101383ea28a00d1607404140c1e090002000c00108041da0107403411070b480c2181c030b00103055000400c05000506060108011680140a5070549100c0d14038072070700c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 583503237 1250 583501987 583502041
    0x90302120d08190905010f0b0a06020d080a1a09280207020a030807061d01050601021e03031501180801020903060a0e0604111306090509060c030c04061b05060c03 71
    0x380402010b0a803030006440b08150802d44074003603081010543c40040790035030101c002d00c40641d49010700c101400b08a40594440e4846101c0054014000941c42212045944a25016035581c074070f07400007009940904558219032070031071b1a295851100181c03040d60b03141e10740c4801880540302c114203401d0f00c0a0b8000004e104000e500056615029100c00b240e520001c0360f6910f001d90300c0c1c8007025142c08203c10103154550300e850f501502064020600c10207080e400c4400039202d01248214004145100c0d241a80041011812618a90381100036501040c10408042000c41c0e440c00508242540b0011060354080755103a800c3c0707414408142c1190140b1414001a210003080a8507000c01400c003c2c146050b090b0700b036440b074951030303e8072410171000241003100540d5164014040c01c81260314040f035015800009065a41800a0303a0094401c02da000d805c207030030800182d401130b07940751080700740c1d00600c0304c0c0360005001000024071402003002c016842e4204803e106e0800640b0401d8403861038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 583504487 1250 583503237 583503253
    0x12090501050d090c09020f3604020901020f030f0c0f061015260a0c021c0f090909111302090f040507031503080a020f0319050705150709030212 63
    0x1a07072040a4590010110750002290700d010314107001c14a003151301c2044190300100350440101e002c1805820400350000003a244600c02994085044500c60f508405046139040b2805075402e05a0203001440410300440311401da504010b5031558101c600307020700c02000040c8544c4c00740024414010703a040c001c8000c02c82802c0c00c00504d001c160050041e40d60b030401040e00c02d8031803032007156070761042d41c0101d011044e02000e03869a801c002c40d00311105120a420102080c0215100007500403200f00540c40e0040c102070050011607a0004130340034181081415200416201c2003480744c4c107100d603c621004144031031402d0500c5220040488103d00c2d1510501003c5002c1c1c80c0c0c449803140809045400207030581d100501038004003a10258450f40c60101c40c030220400440030000d01042040380c00703c48400303070200c100350b950b0f225202282001c210010f5880c80094000c4015010192007141503c1020950705000e24a03a00200c0c0e5000004810000c10425414044c114070541003803400600514 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 583505737 1250 583504487 583504489
    0x1d06160b0a1811060c03040e04060c08150d351810020604081605370203030412170a090e0105060708180f0a0b090a0504020408060403050a02031213120905 68
    0x40020440b5003030103903070300084c4400d1040c418407c9078090f0810040303010842c242410048001d00300001c03020041000ca80220f02c65100c003030074107540d100c001000b00da1070080ca40d9900c1034904245480050b1403c503509032174504584020302d060311360034240c01641c03100b0921a40601c2c54028040d001e0213050b031268945542903010944961264004069641c0e5903d131543c106201407403200003a10314000c0800c294600220200300d01e00324101b580903070800e0710b0307440c1c0c1d04442001c442500070f6140c0d200b004101f00302c1455200400f440390260465055040d0000a01c154560104844600048002005020349101c10304803030301500d42928440e041490956442c00c5030301c20b0b50040c682c0903c42c80c050164554034060242d030bc80101900c42040c5680e50408155039070030400c0b466105040c0c0540205090900b8400d44e001c5400040040100d500c680d1815609070744100c1880045000411582510b0010b4100381805001045095600017400c1c0c1008000900090000e8003080070001080005d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 583506987 1250 583505737 583505753
    0x306010b0a08180c010c140d12060f23030c09070f18050d1e1a0a0c1806180305011a011d010c03080411040903080108010e0106081b01110601090504150c1d06160b0a18 73
    0x1c00300307400c2075812094cc000000245801844c401d40c0c1d900540107810494103562007003c880075040d546d220442645405000c80701c4014003802441c1e005080d24580c0c802003500d1500c60180c41c019a0b9444000e658540c55425605a0140b200e00e502d41c0e011083c03008200c041c3c800c020040c2028506503000729042000b62a0303800301c0d07100e01303000c00c0180604212040c1c080200000215070082c001c202c80409502c0200f0320800621200380800e0b240e034615031704500d856941c4500614165101480080c070f55400703459000c000341003950900b12041a002043d00c0d140b041c0344c5070902076252402c031585080350b03003030941c3d44011075079090f6418140708101d10080011080710400011190007448601c40004132074141001c80012410b100b50000040c9181403540114040c902891050201c00d050300d10110540c0c080f500300c18006001c0050007001c3c000c04400d502d001c060002d01d041c1c82c1025007201e421044420b484151201603164040c41144004d0740f003030344000700c9031381d205416100e003035240e0f111 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 583508237 1250 583506987 583507019
    0x1080f011a0c010b030f060709050612010614070f0c051018050f01030b0402041205120c12030a020441060f070503090306010b0a08180c010c140d12060f 67
    0x80c40100114840e90b11090079003000c10000310144c200c43c400c1510b4081a699144250f5104001c00c580c02d00105072410260100c64095544900036182c60f46070840c00c8940e84031100074000104401c0c0511000603c910345460b0b0100d010750121303e252414a810460f00c03014502d120310601c40580328039130400b851101c0120884204a40f1540340d05400780c0140d0142c43c2e214809503009100050101b4103a085440744540c0310702030000c8499080700076401c85000e20450100c04641d41c4981c4401100c0e050040055603c2000c40401505090b55000004008140d500c0030848503021131090010700c12183d840c805801b0b002c18145016191000045041481150000033001c10000390b100b081c4281081110700051001e011245a980d41d100c000405400c0b542d12500090305210104400f10500b41110300d403800314001510417142141c005661140c10300b0000c85400d0304030811425080c1c01402040e00c40010b640714a1294940c451150085515607000703588608200d100501890b140e00b03084e55 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 583509487 1250 583508237 583508279
    0x30506010f0518040501110408070f0b0c0307060504020f09280605010c02010c0f050f0d0210060302090c03070c050d05130909030207051507020301020414040e070e0a020a140c070501080f01 83
    0x10786152118203029016087c81d481010701c200c40010300140c45000002c0c03240c2258146605c0d1004952500c001c8021441031900b202040c5c0c0c000e20044002c1419a44244d800a1000f4160303401904060007280c00d410003121002041110400c5040c0b06807040c3c02d0032466000694010013007682484006031008001c00c0000c3d04121020395184100014030030881c002a42003c100c0312850210444990340300c405070300450041c010241340e9425000103000307000541e68010072840d02d81d0754030780c00300229400040644d4104104140c1c40c2002c02d405200c038031100ca8080e17403440d9982000d10b83c24006408940e00105180d80b800340c2110109a01090b014203550782182c0341c030003160302c00a03008010701036208060340c154400200040c2104640740070040107001690140452010020030703a448401c0c5210303a924207452900050343c01c103241d600070201c0750418100400110074400084041e50012806200d41d58400d4805000c00d60f00605030345d034813070000c01c41740380f0301e6042421104015014070408 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 583510737 1250 583509487 583509529
    0xe090403121508070801021306050c0607030905100c02010e0c03060f0c03072a02131503140f0f21030114010e06090d060b0f04021e1b06070504030506010f05 69
    0x1804068450b018900080c403c000c200c49a990301e4142e418000d60018014403a207450103080062582d001d44182d8513105807401c00760002d41c1c1c801c1d40c1a0060329404074110342c00d0050040c444ca00741c84c9440342ca0300141180c2c4c0002040010091240d24103200c800c01f0f580f10740e0003101000b020100014219500504e840690b68994854900c207544070740e1103000000000500c003040d101c60218a4401e410618004ca5446c20300383c000c000c0340001c46141800704d480000e030040701131010407031013005900030321021003c17200441c0b00c002d295414042d0000c07110005402c80c89841032a051103c02610800340e41d958005e00d5945800b401c00c880f8501e01d0303449411f01031400c058032150ba584209551901001030b011038940b0f0f00c2840c00800600b001c422a80c4a5000200e08044604261003516003401d016041441456050645048603400640c0c401c000308115840d025010401840070034016030300b5440e22074030340e82140b50076418620142c01602c200e06090748100155906d003045661154800041c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 583511987 1250 583510737 583510751
    0x3050f1321150914100f050112020105160c0b16050c030309360f0402010f0503011511010209060c03070c1a1c0e0601060207090f052802070609060b010e09040312 71
    0x48425030b440655103004140c061044041c0e080130945c1c1080480001c6c0700010800ca0b030306c0d40880e224641d2100b00203070004d1030900c6203004020b40f907618107443d03500641101c00800d6a4a0719032070300b07610035480162403101c800041030030440e04001c00d40274410100e024505284040001c036032141500a804010210034400401119442c1c0000742404405d84400c0445482c6c140340c1140d20b000103640c200e001039440f003a05e10030a8850010303039060710f500c0312000504181404d4112401c80c8100002035075554200000d803010761b1020f005100190741d5001464961206040c80c005041d45540900207205182c8842200c0c2c0081c90125070600a10848120b134180244041c440100805a210340d124412400080307038491300090300c04100d41e0301c0d15040c014071136505219001e50703005450b0702a24118401030b000300a900c80151048007a1700c01d100500703008c17441e00d40c1404e4481e03012040da245648e0322410445540d01503102e03411b20009452071001400c142c2d500038a07241d1101c400c1d040050351481 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 583513237 1250 583511987 583511993
    0x120f181c12030f050f1e010b0313051002040f1d0403090b0c2508100e0c010e180f0f06040b030a082d03010609080703080405060703050f13211509 64
    0x4405050320918a10801c11890203030070000c5c0000f000e0321680400c162000301400d40001c0703c00010306030b4105100e1141591035070318103074001d0700304c02d0000c8550340903010b00b0038035007102031016100600b0480d00d405000c0d8505101c545400504500300c0038502800f41c2000080b94000729240212018450400e40d9910240c204905000810100604421030700170314000c2d41d0310802c104407c1d0f4442d01c0075101080a4513410408840210301c03401c42a41200b40360104540c05034200d0110010040c00e8208403480050128486d000101c0d1001540b02c450014420b036458035107681c1d130b4071000c01e490800c031154400000030360783e10a8904c011701e0700c680010701048403c012000b40b00701c0303650350800c030524808600902206400034000e100010b000300390000703030300680040c0800880303401402c85490a07052205000719030340002010303001c0c4007041107911a44458000204100042007510320369031814040303200c421000116030781d01e68002e6501c00c400401c000c600b03030040d0000803102c00940700316a0302d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 583514487 1250 583513237 583513241
    0x51501050d0b13141005070305131a0601020102041d0a0c050c1902041b0804061823011b213305030105070804030e010c0b04080309120f181c1203 64
    0xc00c4610703490045e801c0c02108040300d600030b94000c035001e44051140e0341d0340c00c0d802800320b40340070b6001d8544440c0d0320925899940c844051600118107200141c80e060b201d42855406900c03010300d075002002540308001d1810014412008145044d1a040340303420502d414040c0e0b280100400340d00e4104070078140800315a20b55005c0c02d085210042003107501e1000f42e00c0078081e504100c03810340d1090b0030b18041400500f00661582c44550f4000c0c4000c546040000300b8030002416184020041e40da00c00e08604800d0540e102c1e058040c0c210303601d6031008200c0e0500035a40000710b00c50003d005007028140803002c04140214224400c090951169541440721900400205940120b4055103410b042c030034429840100c00344a10300a448100e43c03e06500d004403214003c40802801c0c1c5080b05020500040243c0c0095810950301d200700c886d800350b180b01c0b07000035602905203240b2600700080c0703105400b40084103059541c02c1c1100c10f50070f0a0746950350305003500300341d1500424012041303003051000b901036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 583515737 1250 583514487 583514513
    0x30f170a05040b03151f0305090706140c0a0507030f2105030a0209010302040312051207020f0c01031a0910061404050d06050618040809040f05250c0807051501050d0b13 74
    0x6c24018038000e40d0800c0101e8065182280000a0b05010000390b840c0c2000130070301c0444080303a40742250f0004d400b8030b800290304580000341242c0a09114207002c05c400b04010300c0558010003c0320311180c010703e41003609010b10b00c2c18010301c4000340040c04002c2d070000103403640461266400341e62000e6003801207000348640d8000030a82d0258050450742c0c42d45c404003815011384e13440d0603800b40d525510702c00e990301d1104009a2850750b22111203140346500c41c2c0c00a00078140d0003030349012225604000154004412600c072424142004000c000e9140d11090303958410146a1b4036910780b0b418a80480c0d000e412469003d44a140c840010454645410b0005c42d00903020b22801d905900f041d1508000592101e02002d1041c3d00300036032812007040a01c1454081c80030380c1040c03503440b003807101d45007000a21440c4040030320100d4552000400c111000500c00c3c2d03031142c0080c010110750355882c04c0780881c042e00b286000700b043d610420005034080b408a80c02648010f0f44402d0a24507180c004009000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 583516987 1250 583515737 583515739
    0x6010806151204120c0506060f0409291014150c070909050c0108060105180f040f0e1b03031b070b070b060102062404050a090507030f170a05040b0315 66
    0x9808150079003018042e8003a0b0f00c0b03840e503505840c0f480c40b400c075009048203a0151443e00001c0204080c1e18007003034160700051000e4404600f4040b40d07122a0740c10a030b103131405008102010000f42d151107a41c2038240d07126840300080000d03941000140704030b101e9507c4d60580101d0440340e00800324080541a00d20185500049840158851003c0c0d0080d12211004454911840300606903944c000c6180710310860b0182e603014100100b4600d5401701000341c2c0b80e555041002c400d08480183c80d00d00488802882d26040410001400c00d026890007d2000c452200b0601d81500b400d0a07980c0882100c801360b42c0000002132412500b01a90f04040d502e5004c0c01e140c0400081810800c105800300a114290980a56109a403070500c100304c81514039117508075000c40c0400240303540c0342690101c0c1e00181c01c440c00160702980c07036079058541070a0350000c0e1031404104490004101c3c0c482c0d030030061904912500c0307040408403440a4001d0140740203e40702c503c0007000140310090400c110500181d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 583518237 1250 583516987 583517029
    0x309080111160c03020d031e360506040902180d080a2003030f09010b010e15220305060103140a03094209061403040f0c030b0c250201020606010806 65
    0x171b428500541003103a0007000600c807064000c900c0407a0b5003c4c030740d6800ca0310100d801e513116048205400400d103c18224009214400190700450131780c480310040e01c094485a040180c1c0c41440d241d030085c0f4400002201441034500300c1518000481c03400544500b501c003414038291080340080c122404001c0aa0040400d200200c100801079510060781e07401303401c8040080004101c404011184d019070f01074075907007080030f0499a43d00840d010340280311812151644200b1804810710148000c0b146038810b0b40d499104070b0041c0107001b00720307102d4011140703400001c0c032072107410741d4014105114078400c542a05442c81c5030700720514440d0f100901850307007100140b8038a07480d500516509030880022400040c0301c4a00c041000d5004011244510144201c40f030708503519a0349109452201640440700b1160440000000400c1c2c8402140140c440d00c0c401600c8001c00416040c0d8a8080840414490112070060340540d802082c4035411000130301e010003007981c6040c04101c01c0b41d01d80250143c503034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 583519487 1250 583518237 583518259
    0x604030203070c06020c0f011d030303040c030201021c080a180204150e01051c1104090c08070303080f0609040b0705090d0b0108190804170a06020d02070309080111160c0302 76
    0x150340440240482c5126100e0100c2c16604c45108076520041b0400d407542150789005003200640c01030981c3d07154540042c40007011031414802003800c0d41c100740c4045a521002d0541442190380501c801e503100007000c10400b0981c4050107004010001c00341c00500d259a4500703592050300c0b10b40e5001e00039141c0141c018040d003423011413688840c2116200349201d2048940003c14113123000c04200400d018480c01900e02001142c07039481c6041c2a00782580c1c3d210395210401d0000070714030342840700241000c00152a0840c5141000b4102d0f69004081c485590002c104012103039031490251a0000c4c0c004802200c95540d60304140e03224802c100c68164400c60452250041004080c000d60590711002d09540b408401600ea04600c0031200790020f041d010207000601a102c0c9140e400800342c2c1082d000c407000e81d021522100c0881c0d101242e4160b4194000a5280030b05411007100c600070143c180080112000c0301070924540e0017510502c00c5505042802c2030240050318104070051900201503050300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 583520737 1250 583519487 583519493
    0x90302040908030f06030f150901090f0c06020c030a150b132405040e1917070b151005040501050a0504170f061008060103080703030f0e010e0f0309130207140604 71
    0x25420854544c1c0d0707008421000995141004a960980701c0540b00003880450315030b144114078244020010044c540d6144400c038007041710048102ca0846c010300c0c1c150361075070509000904084017541c00380e00a0348404075000000f4020040c0001c50800213000143c000c4040001606640280c0142000c07142000c48441d420f541c6485039840110f4020880c8215035a960148010389640303c9410415030850308464500c030390307070820500c95039210b1710864102510b5600301030816000320800b9100c9100210400007d000c01090340c0207411070440d09104041a1050000c169100724003c845c100900400c08c0c0b10303070b640958150b80c094003841c1600c0e41030b60005d2a40c1d5a513254061080c5110707200f10008504d0f000c018002d110140d0f450304010740a640c1c215100d0700d00c154400c04086040541d50421041178104078030809001c4240300c000490868400000d16142000317040d044540c1d50001c102d071503400e5030b8001c40d03111003050010002d83c940e0107a04080b00003005803900c000903030190900b00410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 583521987 1250 583520737 583520753
    0x10603060618180813080303040b061507050601090f06121506050607051c170907050a0f0608060d030c0f030324060c060b060c0d020f0106151d010903020409 69
    0x41da4004031001440405001450090f100e60034040e18000c01d1220b81e140101300444000c1c4001381c00f070764501c003601c1d9541c0116490f60340111001d84800d600c05c02840100d182c550584480038003400105030504206848264407010180310b09c2c13148583c1d0b461142c1d190002900403000902168400a03c0003189090030f102c0e1703c0ca80c1c0c4195022502c4d00402144900d090700c182e444098002004002410070a4680300c15003d0450020084c040c03503980c64030b8068020010144582c80700c1d40a03100c91b910700000e00c00c07400320707640000410b414900d206014166201c191140d201d8811070380c21120181500782a42c50031036070440540300300041c07004d0405058160300304030841a0b00800115550151841510100d03d03d4000c40c03000507190411500890126040f401c90540010021840e11141c40b060900e0004070712000400368002200141c1442c0082c480c0c41c008200301c4203404124005100300400d518110400c9290421804882180c01d0b40305038030004c040e6074050700802c00b9140fa810b00c0f0316 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 583523237 1250 583521987 583521989
    0x221b03080c0f0a03022802040906020c070905060609150c15011a0a0503070f030e030301120311060423030706021201091b0e010c050111030406090213150b1b0106030606 74
    0x240301c0c85602e00c5024007240018014075100c1e05540a0184030800009000d81010302d849410340c00a25000a0300159540780704a030b1080c1c0c404e690060355401114440c500706000d9a0110001034900000c00155440b003604644810310101c956005452018040700090b000715241014030341701f1000c264004102e0071003110b05172101c3c0b408440d04011302084d910414852503202e080000c1d02400400d0045020300300034605141380e41404524a000b4047c01071468009921080c0130004104403030062542180d4050701c84140100509038a14181d201d10341014400c040c410b0240030907110320b003003600c406d10545014640c021002d55450004200040302074030f00b801001105031422402c140d460f09501d070000e01c82420307521191503000c40c0800540b0050603400c402c0c0d4036035485602501e010489440114400d0b8881c1100250a03805c600502109616800c1041002707864452540c82014024024804079002c0b5070b8070342c0e0340340c200454000c80c0700702680d00e0b0f01643d030800401108101090300300314 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 583524487 1250 583523237 583523257
    0x1c020312070f03021606020a06022b051902180f03100c08010f05040212010510030e0a050706081e0105040b0d050f06010306050c0915090d0c030b0a0c08221b0308 71
    0x1c10350018480d0300c0d480701c0590b115071b0b005070b48100d403188000f4036a0380190140d5216142012221014003040c500f8407a2240c401c035510075a2281008410710b10032440c14418800c50100710b05008041d01b551400001030a4254810b1600c020140ca0719601044040503421042c40b0920142c0001c100262041100380a00f00741c104d4110004282418280f081d1800348884035461001c44c0d10b03000c207100034441070302a10810582c5030107116100c410204072503c032107407140d402002c000d4900301000f42244d801a0100d29a100d904000d85440c1c1002001075041d1041140c0006a0f98141d00010310058a82d420003040c5001e1000d28124000001c1a003034100d80c000c000501141ea1050010084d920840c10b00e55401100840040400340b400c03006040e0100000e403161010241d0f40d240c901241240ea401151608000030030171a89000714000e128042c4031a080850b52400d01444ed940386009842d02e600404500b0300c0541d040c020381c5a0140c06001d51018140040d03622803e00c60226400701c0018 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 583525737 1250 583524487 583524493
    0x1b070b01090f020304050307030804030908070303110105010b0a090b0906070b0a0f0b0f01090b030402030709050c030114040c090b070203010f0c0c030305010e010609050d05100c120f0504021c020312070f0302 91
    0x340016080b0f4001c4a219030307804005145000c0242e5029a00414041c2007a010008807400128103041d082100f9000380d0300a032036078000c0702c0c04040003a00390780c0b0580010000742014442098019084540041a5100d04008035204da2403032011461500a4640c06000c1d20509800d02c541c0d416998402d19604001000a005410b4a034040c450111300365a1036a0003d070050b0004c1211411510143d03400ca4801025281c1080e900d10124090302c10658a0709016680080108283e11100d0006101c21001703480501c0096080f400c060204116481450380b29400015281c0440da03080d4040049105950390070000d00602000040100340141c50440100e49402c001086904e040c0c01c0c080d04844442c3e903a043c005007000700380260000000301c11100c510801c8404a0500e0b0f040c012482007071051340d111235210003062086802d4600c59014500c8691600c42400302607101c409203101003004180f40c044000d0807910110b0b180c4900c4081c0700d14192000706040c41081042001c402c4054080c2d804c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 583526987 1250 583525737 583525751
    0x51e07261e01150b0301050d110301061d1305150406090c03051f050402060307050703091703030a0c080601141c060e06040c0504060e100e1201060f0603090503121b070b0109 76
    0x440740f071050f498028015121028801000649002c0318980300d0b445c42102c21000603200c01c4046420b5442d0ba801841c148210fa000d907240c4070b0740100c4076542c00b00042ca8240741410840c1c803030030703203034000c24072000d01040c81c03400050180941500a501d04552041c06039070219aa41005034840306024503202e0500501840c000105d011350265078000da800510300307890b540b42c5500c2030b1101d910071042102405035a8000150800c108494801240c02e01c00c05541d4074600031228000301c1d5a81c401c020b0030b1259200c18481303c1d0368003a07000000010b10003800c41e034410001e01c00d80c840c50b81e807401c11188282010804a4004800f01900d0b014803025641401001d00c681c005071040d000311300400c030014494000500151401071501503a880303403420406080d010040100d0401c004841191641369144d070b104010802030040d0a030000d081c00c1c40d04002d0514540c0e9260313224800c0590001d18a0044c03004501c22007a1829040803050080c492a599400746148c4202c42c20300902c034140b1010320300030f1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 583528237 1250 583526987 583527011
    0x741030a0509060c1c0903180b0306090c031510091806081e0604031b0c0b03092e1d012d0902090a020304060b030d0507051e07261e01 59
    0x44c5c90203001824410441301c10380110200c001d12141e00260108004c2c10301c0070000c100030003140000340c240000d816540f46011024000b40d160042d01c0c251020104000300a035106820710242030010048400041103180c45800703e940521035000140043c060b500e002417104140d600080850b0840b6090750280d1418a40302d0341c514007500310751503850300700000250000348900c000c503074284504d11402c0800d40091711303000000c10305500900b2420100106101001c402003180b624205414240480000c4001501d0140d00c802403a00407401c2c2d8490607501c0c2d1001541d01e540d1150182c00000308400302c0740751040d18003518406050700d40c02d0b070200c3c103074882d02c94180901d40d0465009000728600c0d455003c01500254401001a02c0c8240c2d51a005001903400703020180440b0496510b081d00c500785da00b4054103140d18040a1406c608601d03104031108038000c24042c084644030403809103007900c6001c40c0001084000044034542c001c000c4000ca5001101111510a5540500030441103002003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 583529487 1250 583528237 583528261
    0x51c08160b0c040b04050108041a0c030a0f050610030b0a090905034504090b040308010512060906060d030c1208010f0b18040b010207050402040b0408060741030a050906 74
    0x4004d801074a1420001445254000c290031500544203c0c610740c6488040e040124007030200780d5410100e84c1c3c0002c24048207849a00a070381003500002e40812942c1040d4002410b417143d560a02024036850300c05000d5240e8404a24400604d803104040c170000c4050300c3c10544a5006001000d805261344113064002500748070383c12240034075284a085180203001135900d44216a008940d406600e640040b000030794030210b070a014070700c04d1300c2e9180154184001c100d164050b400c612501540480308000e141c080010f14103810203030588050103401a103050440e0002c0030303001d000d80b030703a5a1180d500202940c041c0c201e43c102c5004251903102c85494120481a51003002d04010401151045241d4540b5003035000032290b001c14011074041958030800b2400341c0c0c0065004800d0403401040410800c0414040207030300a171907241a103d1860f0900b201d00d001040103901d0003140b0707048140958801ca25050002403ea64000915140d180c000807800207480b089136101c04a006030710100e14410031030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 583530737 1250 583529487 583529489
    0x4050708010f031b080d080a0614030304051905100e1c030210050c1b0703020a060320031009020f0702041409030d02090406030204140a18020a051c08160b0c04 70
    0x4910040822440d541300c10b004460344e4007220201e80d0490000041000042068040405840d21081600e18094070180111003041d4002d04071124001040c442590380842200c0a81d04d0031a2410110304402501c010f52140540156400460014200241035001003030140c144004440b02d52580324a400c0d00c03980e03a14403990040c05680b003007902440e10f07007054120943c85420231080c1410401d0980001a0700d00c00302c1405001a00400010710550921070710b040060955070800f03201142e80c0b00c0c100450f40c2d00e410711422078441c0210100b00c0b083c0f158610400205040e1506640344d468040d4583c030103038010740c0b08038481c1c2e140400d5195000038649244ac41108607402030b50800145d4000e14010354004200706501070f42c8c618012006907144d11034580d8104926589600f18601031124000315221940c808440034108100780005a540032004030a40d003041d5180f11109190055215a400700b241c0005c22200c804220011940e240121070001d280c010515404036840e07807980c00b0035170b11071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 583531987 1250 583530737 583530749
    0x303040b2410170c040515090105040501110304031a09100e0d0f0903020306010801050f0c190e030307020d26160b100f03110a05190303030f02070605150405070801 72
    0x1c528100700c00d40303040b400d44025400b95050042a4407102810780303020840807a00c080d50100c001c20180803034100040600300110040c00032900d440c600e10006402801144211410840c086681e1416100103000b03071001154409610212045542c00c090342200c000c9400242d80d01c00c6420384a50b85ca15405410399510341344000d003071200d0b4501000c40f00d0850152106081c01001000080103032000c02903c0d000b802d5038000007940781080e103804007402c0005444041c03a014240b040c0e01c200601e65100e41002e50b45801d101d000405440040303030540c014000065400042110103109000740380001118107145084c504403c1c000b030800c0c01c009402240c000300001070b00c030205507000882d516421070300000ca0f40b507540d120030381d107644500314206243c008840302c8142f505540340f030f41811856180900700c01c544100c45000344020040d506196440003408041e106c202079030700422a03504459409400c01c5050043340f45c09150080c40464201200307008070f10f00710002d840140b10b02c007014182e81c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 583533237 1250 583531987 583532041
    0x1406031006110c1c030306120507090c170720030f030411060f0f09090f01050108042031050c160326040201090e0c090d0c12050303040b 60
    0x1041007800c49080c5103010070103201c0c1c070940c0e00c00865035903841c1c131861039010707080071000030b6508618000b0103039041ca6003c0c0510038040d00d09100010ba0200700e00090b2003d1290004500301c103003c04980d0001c200c0400c881000380702d018031130b002e40c0c0420300f010301001c488030700304038070000c40365003aa03901c00c10700800828442840424006940b80b140c001d6400c1004001d9810510b4441206610358030014040c8501e40c40003030221100d042000180758001040c640310000380d0b00d044006040c41b031004000030f098a4440c030000240e099010300f4548054009000d803950708103660b480301d9416070034500c1940201800800d00c0803c1505004241c460941c3c0310b81241000c0e8084411407201000f070710b04800340a9040021500c402081c0c407080074000303042c6503410a60415000140a41029401405034080700404000150400c8411503403540e40030f41d0045060006414071040c0d5440d1034000d400c4000c1d419101609020001000c0c40c041d90040d207040100361205480010304080944c0a001c03506 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 583534487 1250 583533237 583533239
    0xb070c080c0604031106040b030c0d060905060d030c03090f08070602100c091205010b0409060902090f060f15070b180d030e0c0103021c06170c01020318120a05120414060310 76
    0x34075001101c4400810186c80207040c45e0300c0e128041c0e001d0300202c41007c41c001c80400ca807044403003240901c0b0018052140104918240000825064806110702600340000b9a07140c2c02014810180900180100303110000c8060f2145911501c600041c441d00700107109406004440c2c0349030344600d4660b1503080c2c8507002d4891400d0b60079040c4440704c04041d1019543c0d24400802515a40035403000704d40710386400104040710703204101e207502d00505120b00c3d02500d08100449600c43e464580d032510b80899241c8003507014030302d0b00407483c840e040c0e000300781403110810700180d00c0ca1100001e00f50b0a92030140c2d4046122200204c080343c5814580c501e0b2030303101046100542d40613500411102c28602d90180d042202e26201d10103403004c55000c48101003143d110203040c01c0c0140941c5500200c00d1020b107103417440c081c00c040044001c0310403072803242038200407002840104004984104ea8002c0c240c0b800d03405805180c006035040b0f44140b030b42136810400c0302c0380706103040400c6a2003444800141d0440c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 583535737 1250 583534487 583534493
    0xf0207050a09050702030f0c0d091d1b16060203070e060f04140a050d050a0506180c090c130f03020906040501031e11041a0f06040608070807020a0c0b070c080c060403 73
    0xa8400a01341d4030035404100081c03011349000000070180e030380061005140001c4401c0000740305a890b9445810340611400303821007014881d401c219088220050b02d40c1030384a001160340d1203481500003c601d14041031070329030108245600914401c040344d407102c10815480000b806207038421345012550303101d002c000a21410401c0e0040084014018000094060300c80c00420200d24411005407680c0d400001c03003804000d0100300c65980404c04049004407104c0c03c0300c810707a4400d46051140d00c95600c070b10000d0034100101c010343e40d03001d8421110440c00c43d61003000c00d049820074041640110100000074265090900907039040b00c2e88000140403001c0e1042c001200c4408e0024100ca10948924441005903100d004031036035404214410b003030f00c05002c400c02180c00060b50700366004200a000801649800504155018150342040d1140c0e68480f08100d00b4540d83ca14004c10000f00c54401140107281d40010300022803080d00c0382040103445207074240d524034544540c141c0c000300801c020300c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 583536987 1250 583535737 583535741
    0x121006050c120a170103080d0c0f0903060b0424060905010e0d0b0709150e041505091311090c0403021305010f18021908060109060f050901260a05070f0207050a09 71
    0xe0031025250402d1340b400c6140311403202000030b910030744d520940415100a104a580308490b08070085081100070b131030300d008002d00362940c90311000d0a101e40c0e070724110200f611660031100340349030700d1511084804004a00e02807004810300580340043e9121001042c036501904010424020003481d0114440395070f0f0b03c034000b00c24000d00c4041003140a5400084000c1110400c07049080b080c2c450b402c11040e050140021903200805c02500040c0c3d06d035040000d0380341c002c03c0741d40111410301c841561031a1428500300e01070107485000d0704200010300700040103a0f14005041a64800c82d0480c4490602c1c061450643d5828020035017907281d40442000545210300c13a10040ba01012005410801010710601261002c02e428202151b4000100881584d0050345d103c003900706410a40c905245d030010091043c01507800c024140805c910301401c4414186250703465a506007810700300980380c19140e8201800c1e0a0301c6001c085403d0141043c080c60002c2030f48801d6440103003025098610700040580 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 583538237 1250 583536987 583536997
    0x6030c020715050f0c0a0f0606061803080f22030303090c170d0e01030f050a0b0102211204020a0b030a0c0305130314030408090901030b0103170c1f0e03121006050c12 73
    0x12988600c0c500c00f0f001414038400d603407d081c0111f100141040c540440034060840d8500101c015550b0700c0e0040c03002461701e80550760709960680000742c880840b0100340703001c001801e44810184005400000800d076140c0c02c00c0c05028410b51b440151700760741e200110340410094007810400e0704502c4040160a12030807044005070703414500852a1442c6240c01001c980d400d079a0240d11940310020008d40b541c040002001041c0c03c95026442149000c4a14a040c0500c141c24143c807c01900400c0940d03890104980160460b03d00060b528113000704c0c504010143c0c0300d03114004c82d05017000540f0141c0d601403842c1e81c454064840100c40244159849800e91005108491100c0103001102254407480e0b42203010314410701d840c206550441c1401c1d40b00d4582c0481e421820f034400c0108122101000c1614441d41421740009230310311000440c140c0182407100032150482c0300108405075040e25260100e0b01454110255001f00c50721101c0c2224180700b1911412819803010036848100c07910340740100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 583539487 1250 583538237 583538257
    0x6080604140a050f46021323010b030408040e071e0302090306090304290f0301030804080606030a021c0201021f0204060311070308060105030c070210031e052a0409050106030c020715050f 82
    0x4c54420080141f00100d440d41983c0c0810999500e848426410031032800390302605240403410300754906a904c0b048184290f01846000554550111f07030450b002d00c015441080545045e20340c54410440010000c1d048004a43e11902c81e01000c107480e2040801202c0541e440110203140700b01e01070281200ba04900d00b40740004000801c0b00008011001001e1130285101c0c4202035565482c000100f45808400b40003035119800c01c02c5a070700107940d80060030030000700803000290890180d0005030700744080c0f0046484524482c103200250b2081076802001590640d0700c1c01c10203010304107903140e480c0c0544900280440d04c1c11001c20310942c06007000c0c660040103030786c01914005007540030540b00800b01c039408000c2034444101c07007000e00a940040c9003013544214200601c5c600b9403001031080c10041e09520702380f0504101d80d044660600c049030b000d4605028203000e25652110002c1c02000c4500c1e155006010b0790001060384080c2d000000310982d52a5240e130300700b4007100701c00d0b1a1980070207000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 583540737 1250 583539487 583539499
    0x1110092303070b0903100605031902040b03010f0b0a0e0c1b0f0d020106030303050606070209190b0d120212030f01090209220e1006080604140a050f4602 67
    0x2000103030380400c81007026002041c4915214021032040c189400003c0113011b40203030601400f48a9a280080c1d441041e01e00000590086012400860010a80c50f04140d801d07508000d00c507501c1e450b454102000130102a2020101d40d0340d1041d01e07011b49031050340c02d480306010030020925400c8003805003811904100303058480d00b0031001081c030300e411000c0c10b00c40c0c0541d444a4080051641622409a2148050b0381951504a0703030381c00204e100000814005942c041c080100d10042119806456949405040304011a5850400c0e90782001c150080d100107102c1c4201100840640c4001e40c5e00460010908021990034800564040c0d00030900a5030803140031441d180c94080103454200344240307100130005d5042d000304c0b0451f0400d03810310240300c201818420200020200016255406a040180c1001841c0c0d0b101c80c1034100a0380890152035846242506500034201103400c0e4100120200129401e01480f010705190000d0b041c000b1002c1a80c80f116252100c95961195005034402406 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 583541987 1250 583540737 583540799
    0xf1202032d370c03170c040902070308010e16020d0f0309080a0503161e03020d060302030109030f020706091401050a020c060c01020c010f0b09011206021213111009 72
    0x500064045070705000725010942c0c51907041100107051141c24482c1041c5040e5900301c2c9144c4000d8807078880e00f800720340b0240d01d4000103400c4150310006d1300c003e001d4041065650b5031301410010002202801f0700c114042d04100420322054440a44540e01c11454019042100c0b0103042a01d607030b40e03400820014036880b1440b10b000264030f503005008040f441e0b21181d403241050000c408200e40e400b0f02031410300c0098039402501190300300300c0300c3c0001e00070720700581d641075020022400703000194030080d0150b0030104c00754101070300314070301d5400784015900b11100180e07180d404036421072203071141030f84c1440014143c100079481103004003922039180c011100810042c2c00072030101e07400b483e54200c80340d6002c160b44151038400e024040e07103004842c500340840c1c0001d1000030141d9206200e5540810792100c0b29004002d00360b01607034640c50009042d0141481d0a982c4100100d00b1041c1c01c846d5041d00d400d0003203840c42c0551801b064543c2903551212001c0c242174580080310081c3d00401e08220179503103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 583543237 1250 583541987 583542007
    0x60904080c16030f150c090b0702060408010f1e020a0903110103021210050a1706060111120301060305010317031509060d1b03060b091e19090f1202032d 67
    0x1240b00c00652180c0783e0030911610301d0034559141154030b4400070482d4140380d03850305a66400120407081d00c1445d414203981b03402610002d80306100b20743c003035040e65080c801c4144a00c54154800c03018420030955142c078543c4040990f20481c40707a10030407404210f83c0c40042c03003c1240d46a40307000d8164181001480d01080e50b51800b03854800701d66415020f84496014001401c209101c40018540342c01e10460106900840d42c0d01c034100140311703a040100078000d20601c1c4604000d0404129032050900c1d659507115040203000d40024003041e6040003041e480c081c00d094030f16045a10038009010a0b50a4002c68810440305080240409501c241c00c26502008030380c2c0b02c40d4616180c1e081200c64080c42d46146003e13001e03203c0c94030482c2e03c20081c000c04c0104c15104100059041000c860790b90b9096561800c83c403046410000200c04a585490020030405c0001110600103030302403c0442e142e4411040c080340c0c0c0388103144a52904400500b14040d618138140b88895208404001032418450404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 583544487 1250 583543237 583543273
    0x6021308060f011518120c0e1006090e010311120f03041d010504050f0a090c09050108030c1204121e080c031b0a120e030a021c0302070e060904080c 65
    0x5191200e00d502d010004011100c41066083c0c1e031500380d03080400240038007465030017595006125826032000d00103424001c0004003803055002d005070303198042250415144020350004a4020500410100c0c140811107001460750f2504032540040c8140301644074074140a2040c41c464054030892040c1075903206030300b105002034400390034042c03015a140d602c091a205048041030744103e005601c0d00c0280055164280c00c62a400808004040781c9030155103010200089503074030040c021403600c0d002084030b04000c401016450190003c5502c2000c0074045014284207910409a8100c0c41300741c00d00000380a8010307040840f4000081501480640d00c4400c0c4541c400030a034009904001340d032490540c5081e80c0104540040b200178100b29015036120040981e07851643e80c14040e0450300c01c802581c04021003442c141e8050004100011880b019000b10900e40700c048000d40207203000428a540c00c0301c17043c1d108030f02c020188032480d1a15100c1510b144d00004901c4858003640202555403001c0c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 583545737 1250 583544487 583544491
    0x100902160519020114090603130510050408070b100605030601030f091b0510021b0d32072709080409060e07030f05040506010509190e28030801030602130806 69
    0x2580d81d803103401065200045c0030100e05d005100c1c0300d040510100b800d07919001c05690b0b03c101540380711021031501d0300705030340390105007840903004600308002c2008011901001e0581c40e4890f10030380201d915105010005405540502d50006105000094080d84250050a0b42203585d103000549580c0a441d459840948481c2c0301c2c1500c85503100400490400ca00110101c82e8a0f06c0a46111501a082d044541ca01031103400d100e503250507502c405101100128000b05920382030401c1110328501d015096440003280103500902070204000396146903111b170380c01306000c040c4d0f5030364100100940440003015040000c1d0b8016105000109801c0b01502c19180a801c1c4441c49950600d4280001020703520102e1100000030b003000305100000d480003c40c036045d03820844001d5003035903c3c0840d41c44403044072607036480454280107000b09950008110144100300c914580c800c0c42c10554001ca03003001d0094001000504500010070209007168041c16400545c00ca55442c1295a449c81e81d02e00402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 583546987 1250 583545737 583545763
    0x90f2d04060e0a0b0f06030c12180a1a09120304060e03040519030b06010c02180601050c0d030902030c01020c210c21010621030806040e01020c0a050d05031009021605 73
    0x14130a000f8200e8580801046400c800407074500786907160104030311001d0b00611103ca0410b10881300415009071900c2408904a903c070300c11a07400340d0702818109100601da00a844202d0b9407540410f40840d004103881d9064090b602c1c180d403540d140d650700c00d0b00400c0194680c1e03400b0b0005000114545c0d0780e8055040140c074030303406809a141d041d0b08029002c907001800711414411440714640043e102e240c00010b0034030310760800c0e0201d80e03505e07001038030140318100340d82c3d105000b40c0342440051901030744407003d043d000380c040304e000400f140d005a030380e101018107041d4840580360100790706c5041030300360b090b01c0c4c031806041e240303d0140c40d400315103103c1d002400d40c040901d101454103403800e024410507005020145012460081c079a00880307104c50340000c080d00300041007001445035240d6030080180840000021903440101d80d0441c1c0c0c44161015007280d0344d0044070104035075188501c0c00d4038084c0c55691061244d1a1801070404001d502004111004030701c44200000407400c00e000042c44041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 583548237 1250 583546987 583546991
    0x11416050106031401060905071b06060504020406031a09040506060d0c030f03050307020639070c0902070c06021f1a03060106050d0612200607080f090f2d04060e0a 72
    0x2e0201c000c17070a6401c0c1e038001c4a6064036210800466076845024110344140c661303102da07511009070520a024208e076800c00781c0c016000040010700315030b150b403200c4407180f006800884401190702c200440c884065502600c90781c0100085100352030300c01c1c45998a244142c1510341040c6da25500e049c0c501c1c002207030030740c08500040200010320307805001d9213621040800c0d04110200003284101a88041c080144040750100c0c101c11441e943c0520488032040d070000300102c00310303948a0620b4003a600048046071040d541c2320000800900008804540d403030394100041c40000c00c170502c100180445c898448160044400030841a182400309501034425940c8032542c4008071420031050703c0566128100343d5400c121224003140b01c1015081c8044540710b600d00c0055000e0ac001091030151820190407414002000c0001310b400400404011109a5542400070000020041c804400041e090311150950180070840364021280e20007040000703000060301611240d908654400c112003c600c06a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 583549487 1250 583548237 583548263
    0xa0e030c01110712080702070b0a18030f0302010c0206010b0702040b04060e070c02011812060203070c050f0d080109140402090703021603081b04030302100504020312030a050711010b01141605010603 87
    0x5420014084248001c0c1424001c03400d0846d40256190301520500c01c0c4168042401c000300c1e8454951800568070889000d121030303859003406c0b00000d40c040011009503103080b2010f140b550003c01d1480c1210340d9a04034a040041c29001e0101800307003214804da116642e203601003a1000000075007402402660754542082032184005030100112100348207240c0400d0350104241c500c040c8403481c0c1d083e80800c000d41c80392076043d030589000c000325000070100e0040c0131030507884039000144d0403000b804540c4c40500c2640d0754440d040c115100035a00603001404000081e0150405900c002d42109840c5001407a209105030054110185440e0490001c2c1c4c00406014440c48402078071017400c5540c1600034a40b0340b456030702940d5422040d1040c0140d07521000040c003950380a101c1c42050544400d11103940b4a0901c141c20000c05049881c6000b05000025080004c0e40510400782c1c0f008042c0c41d41007581c0e03000e894518164002541c10f0100b840210040d60000c3c500380140c00085124541e550082 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 583550737 1250 583549487 583549493
    0x190308040c050301020301050f060c0c03030a17220807050c09090a02030106170a020118030b01030309180c020c010e130f021b0d0c02060a020a05070602100b090408030a0e030c011107 80
    0x956420b41c0b200d40700b6801840144055a10007070400c400001c1160119592140e80c0384160409444c2280729615001c040b401ea000c0f1500000549040f55501e042270303445e941c60710040518044a001032140340100d030a0040b0024450708010304070707280500200c4030842d20f004005040d82c202100c07900c0a0340c03c0486002d0450800340140400340c504814000404680362010507621903060b24043c3c100803464140c0365000d580c064100d03003d1900801a100c856842342005030009245200d5820300d0301c0800e8a580c042805ca2180c0c80d406082035001c1d2a0327042101c80119480f04002501d160f0140408060b801e40c5180343c85100400d8600400140c4c0340d1049014404c002491141000810f40241c04030030b02c1c40d60701c40307030320140300354100c50040e29118041001c80c9844a40c070350090092050801c0850641d800064000207100b020b4030a210b01c1c808034090102400c1c0a40d002040400d06002060003041950420940382c0300c0b030800c40e030030030544030031490039150903146482d1f490100003244014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 583551987 1250 583550737 583550753
    0x20010c03150e460c0f050304020310020315030f0c0307060908060105060a031d0606091e130317150a0f03021e03070f060908010c0e09041419030804 65
    0x80019525824035803401c50304101c0f80c9010900790f891440c0209003614014180c00c1e40507920b03018a8071400001100460000004101002504000c610130317400f140c0300c0900c03c0c0e0450340300300d5000d005024a040c0300307502c02000e500040c02d00100808601d01002182c0c030b08001050824085a0040030051000c0741818204003040e003240c1c0800074004014040120000343e8641154001d40e00f030341d5500017100048000b0064415402c0c0f00c40216141c00d0202c000009003a401107000710381603a4242c84009600099603d40441e0041200031100003480010041501400c2c13540a400c0617000d4004103004940c1408003101d82c071700842030a9402608900700a059000501026003030b001110f802c58002400c1055640040710203150f4102083d401c40e2824445072004103144070f2144c540035203072080039050f000a80150080c0b90300c1d100450b9005440740c0000c60107454080c00c000c0042d00d41c0d8036801c1840c09482030198017407082904100ba10188011403644c1d584c041d03515040142454030341004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 583553237 1250 583551987 583551989
    0x1b041b0315141e040b041b0e061305040509070305070e070f0201140a051b1803120910120e030a0309021c05070b091203030103112d0120010c0315 64
    0x1500041c0c402202526141d1026088404a60509503400242403e001402901c8640e070526005410802c01d01020503070402c4513080045c3c03548031082140d0300c0e2421b104d42400362680054580745010020480e908060740b00c2038120f00603105840341e254403a11850f180c0303200c0f0b0307010311a12400403003000101c503071010280d241c42c1e400d4070080c40541c0034070140b030144810142070801016624804600a4000c03041040803080d250b015894a840c1f8000e56015808065842c01e402801511914440e1a10308000c960001000030803101c00c0e81c1c0c0c941402c5500c0e4420040c0314003400d903542c0d0301d81030301007040010701001c12080d42d01081c100141e00c144800d07004920340103044402c86c0081800040c41c0811031206803020698203507101c00807800040c0c1c0e40f0500da07155405901002001106102d414002d0314039180058402d40b80c81c0d100341402040350400104031040c00400500001102c1d072003075803201482464080801c0d82c9400d0101800e0848a011703a9480c0880d45c2cad40c1c400d0458a203c208500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 583554487 1250 583553237 583553249
    0x9061d03030f070c21030b03010c0305090106060c0b04030f05070822050612011707030c08071d1608070e0414010305060702030405060405040f14010e0f15031b041b0315 74
    0x45854252592494000c03030107003017001103c1004601d5184102d10942c003420880c03500a00901048441c03600280040c001038680a00d15405c100000c134030076010724000c100c00d55020209410b80d035903a80f0700301c0e0f266511402500c1044400c10000000c106a00c014003011080744c04030700e10142d0202c40f02c0501d60607039072200d40150014400800c400c9128a605811208601c0d1054079940094143c0d1341001ea03181c200400003010706c400403a804000103000425030b03001e44400e00c4d8000c1003954400e1000c100712b815400203440302c002d10042c1072180900325040705607403c1015000c1c00910006040d1050020800e04154500004200340101004080c2d081100742c000385191906003008100d05110703034024107004984418003031650034019809505c0e0428110001422541c4a2401d0001e01e003064880380303058107861000c01d0000c0c0c1c5040280c141c990000380180660301e4582c00507041445140145a44035940b100c100e0b589861006118402c0d030305595000403d00c1c1078205642018105800413 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 583555737 1250 583554487 583554497
    0x40b120610140a0818150f01120818130c0c020102100c0c08090d1209031b05061605010603080a0e1206060102031e0c1014060102011a0409061d03030f07 67
    0x40c20a1044085508100d8035260000c481d90751242c80200307074040a142640503110361b0211031a054101e240c1540075070515001a0016603807050b4041181d40c150b000503040304410449140041c00000c0a00441817026080d69820070004055100300c4041c01000c1000c01e4004000400f1980d052040c2c88140300800001c111034803600e80002c254924952004081440000341e40800d580c03016000f2404661024030000a5450004000c155503294803040300c40c0b48548548911500381003039140103840780070b4149401c080c0c1c258841c1e400400320311400d0351695603840012002c500010300070190000c0c503444c6d12242c010302d10705115500708801031003070741034109000384145603074084100e0714008001400d0001070180700c101440c05109075050408148284039842081841681112580c0c040c90000e501c181d589820041e8203075264160446a00240d020548003589130603071005400a000d084000b40c01c1ca40e68801d44e4082a510601021a41c804810400071900910126a01000a10780 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 583556987 1250 583555737 583555757
    0x30a050c0d110706200a030e1c031407031b0c0501090902070f020f03160f060305070302090a2108030f0109110a32030708180a02030304030215040b120610 68
    0xb64031008140907400070002a9900d0281310910400201d446030a0101a1045ca19407881d0140945208800d4075001e01540140300c0800e090400c0211403190705503e540a140003049402c0d4500d034881031084044c0040110044000c0b003004c0071182c2c1542c03040e00850302c2d8509140000d022300980e544400207050040200d103001580031b0442000d003543c1511210001269600000c0c00c01c10800c808040340e003103001c4001010b00f8191130b0042194a01d487c00c109545903d07008038241c0c4034004001e504604030440802180148031000c0d010207200c0580c1d2003d85805035a0001c2a0340282e400074a074480e440018000502035110f6428907841d038100040c42e09c00c0216001c0c0c134650708404c40c10440005101d5240220700030001143c1201d00300320056940e4038100902820f0400192250041191501120055100000707110f02e6a00c0d00107008500781403442e400c02407000c400c4820010031850030b001c00181c0d25580700141070034043c40700c00b001c454640017091140e8001c946150b00300304044010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 583558237 1250 583556987 583557017
    0x6020d0606110a030210090f240f0524120115030213050402211e0d0e03070b0d021b060112050c100e061602091009060f06021203070908030a050c0d 65
    0xb0b1072040c014028800414030f0001824440d108e888500c402512460a110780c440b000a1760261031851050030000030001c1c4540054080b0841c0c50841c0d0801c000324000034034007641c040003030502946010081500501c016650394560944120149900c0c010000410034001c601c0c0250003d806035070140002c0269141c19000100d200b580c041c00c0c030041484080c0c10445011043c4010b4110016228044082407001202030340c0c0c95901240000c0024030f01248001585008215402200d4a180100d4200f0a140408000950060400c420701f4083d82e0f038285600b02046c80305600030403035446104580e54030750174203d060440c0c4040207441382200c0381e240c9003c40e0300282d4100840209030b899035120011049a0325000003203242c003950001c00300e002c10900d010040c03e54000c1d0b030423485051100c59074500040720100c559000300009600005080440100d01c50065a400700e05481c0200d45540c0d01c144407819a4011240000000e00001e541c003011041004504445029803404858030303130f143c1b8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 583559487 1250 583558237 583558243
    0x305090d0c121412120a06050a06050306041404030f1206050a06020609060718060c060b1302130803040b120402011701030501091205030601120c020304051906030b0904080304030804020d06020d0606110a0302 91
    0x14800d41d20070305c5c00f0030105e51034442d80e50045c0007800300508881c44154807000e000e800c3d42c000304c401c9445107040417034080c0c00c800340d500114011545601c808000c10030200041d00c1007141c201c160502541d480c140020541d49021030310300100030b560098100b0781000b4440e14203180008113034406111900c1c803415410401580100200c50f180e01d40002c9840ba180340c40c2c00036208101c1c1040d8001e24010304428a0003440c1c0c018450b100b803401c0c010031129607506125480340114840c0309414002070000c0490032104240f801d61080c81450b03c0c0722054040d01c030501c041d90081e002600d26a56404603001003150a420a0640217140d00b803032401d52401d100001c0000d026a1195800c0a4417600103206850007001500c001e07000050104950340401e164203015004944101800681450326288480c00c050a10701d0003070b90016249883c0d41d896440a51b004070024108a8024202980d9000850003030320103800c44940310030000c04c1c49454010010301d0f0804100c00e1101540000e010080066000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 583560737 1250 583559487 583559497
    0x4080a020904150f0b01090f0e060603060301020720010207091b031a030102040b130906030b0103060207020a0e0c0306010215070f030f0906110c012004030305090d0c121412 76
    0x100c0e8596140d80c2d4500c0c20302c1e0f00344200c110415031241401515131428016401170f81c0461820f0360341e40c00841e6074200d007a000f015940b240549031030a5801107040e5041010041d98880000780000d407030101035603510580200b124030201903075035030307510080510b40e030600c030140007405e44903c00c0c00902944d04850305200c07210503d160a0540c0c030b07802c0c008070032840c1203460780350b5000500841d1070304e50b0391840f800140e1021a00c17504505d00c2c0040801e25502c180302c0c41040e6030b00484820380c5a0f0a41da141802944035050580c0d00c4001c4004c005031100140c0056031156848641c2c40d502c03420207100184c80c00140e03544500b41190483c041080d40d90b07003c5010003044072245000b05001300c0c0081d002000307001c2c04a0203460541080440c01480300020024601440d00308000c205100100004d013502c01d94003412078481e12400c00c820008644140302070006600000c0500c00004d105540e03100c89005558400020703072140c02c0c01c88061180700b04402941440c0070015200741d02040420348003038414 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 583561987 1250 583560737 583560739
    0x60712080601020a061505150412021210050a091b060e0d020109170d09060203090307050f0f09090f1002090325181b030b0f01030b040908030c03010509070504080a02 73
    0x4500014441c1c3c0c401c010030380d2501d4002c0030030402c4c05168080782e409072540380241030264090919403401300c0c4029040f00c0450340c05e6111590580141e0b800c0000c0006800c2081c17119125883c1d2418600403d8801c050155080b03040011380450300f850581c00300c0400f81008800c0c10b0400b0800c10842c1d070003e102140403102140d0340b2452090500c010780d01c00c070322600241c0c4030392140e2910358080c100001d03400c00340e850300d41c880b801d100d90340d014200d980340300b9040d0003070301034121540401484c181580c20501c0300d4802881603a07921802c2c408504d07070301000c841940e500c0d846541c01c0d0204442c180040c2820380040070013036107810b4400000c240c0e40c00303030040d854a0740c40c1918404c485201d10641800f000d404510f00d244c040ca1000310f0903c01074200140300300081d1041c00895080315000340708a50046001416403c002e941040055000302280351030b00e40c102e51221368140004070200c001b035105401213000941c80e54107120600070b10000c02008001132000400040c440c1d810001001b2680a034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 583563237 1250 583561987 583561997
    0x30e040c090b09061c0507020c190605030423103606021b10110c0a030809070f0306020712050c030708030406020d050f150102060c0901081308070b07030605060712 72
    0x30040c0225990f44170744000000c01e035526248411a42c00950031030360146000d5821102d80c0640001046035100c0c580b4140c001c20b12480004000c0745005030040c6601c10f0280540541e00c040041400c0980c030704450399a20960401740c004480b186240c490140c4440b07060841c0d40083d40b0301c0400e04d160a8030241c15403030300c03030080180800700021501200c0203e01180c002c0901501e00b02811555100c1511f032000c115810304680c00d03408203021044e42c8000b048800103180d010384070717241501d9824000d4102d0800b40580400401c91060700d07106407000f144945c03030059481401d401c00d200070035010310140d402c02808000b241d0001000200350b4203050b81000c080341c0e5030b40700c80c60b0600c000e00c51860800009410720b0704018406da5243c603524840c03008212450002c0419200490300d441301100d05820f010750920000c00d040d4410070440c2d0380b020101400c80c44c500c52603100c00381c9580001b001100e144128004001219626000d00720007051b040d034149080520030b50314131031140c10800166007000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 583564487 1250 583563237 583563247
    0x10080709090e1b0307120305070501050124050a020c06040602160e01150f030b182d13081c0c021213030b040320030d0b03030c070501080618070804030e040c090b 71
    0x20350300b0300030040101b0743c0e020066040d03001071501500d160003400003621107503c0e000c000140390040c02400c41103600300f01902402c42c50305500660325074111440003011403242106001140d158000140040c003000c0d00289816141d84a001c006202540c202c003d56850030300c0100070641d0010310030380da034410701e0900c0510304d80700820131001440035440240d400804409400b040901c6600102c0c0200d01392100b010750745410b040030721100e0350785181c00c019182d18040010600c50b801804807440e14460a42c2e50300d05081c20b05071290405243c1860058180e640231230703010145e010041801c0b00070b02070011038105640c65000109401c2c42d444090442d00602e4009802c042c814200e01c001d000040446d00760013003103200e0b2250381e5004982c0700c1c0649403a000083c0103500c4c2c0001942d282c14560b400501710326084c030004690610002d42110b80020105901855441020107c1c0344202c1c1b0a03917400415140c14200101807000b142d100c5401640381400030084c150380081e41c441980c6940c681c040e0340e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 583565737 1250 583564487 583564489
    0x6050a020312310f080c1509100b120a030e060702040e0607020c04060e04020409020d02091e010e04260f0f04050a15050706150510080709090e1b 64
    0x5100d6038111600c0c04030740e60100020440c2c1e9007400700d0001c8420b001d04400c5030003c120f091a000507070310080c00c9070103a9003854000500400090500c80b440b60141d40d0907401032245050f06807015940700255400504203160003614910500744850f0040b19002142c0d600c68418a07200c4903000c0c00a410030824240c040c0a5031103034000c9030581179000d01700300700401d092087c060b218501a240c00d0014081c44c0304d0480300303241c14020201a99400702101d82c941c0c6030340e400c0100a0052120403030f0081c030b050385a0409a2b6842c1c14851013140b00721406805004d02408403060340b20705030413058030140c100d824031011840141240d070001003945007561002094140001142c080c031203040140c00c20000c0d201c0d02080c103140c068000c5580a81c5c801190303d440320441d46214004001b610002007040c031021000c600103400026840341900c0c5110206500d0720081080c1c15142e0344020046010101404855644086010002c020182003009210410281107031564000040c4240d000142c440c007a80c3c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 583566987 1250 583565737 583565743
    0x12060f040b060a03080a12110c0c011b14030310300f2004291504030c171e1c0215011205070b071106030a0e010c02010e010b0a080706050a02 62
    0xd180c02111300ba032100003100000f040c1c20f4884c0305103181f0a04008141819070701d2803047c1c0d2000400d010191506046110045078403041c2d0712011445130060100c814041484214070481c006504005503035603160151500c1d401031007980c4903c607052010b900d900c0d2003c170750401e100070072211009400c02112490411185400301410081e1030b403001101080800d03110304880c1e440101c1d05a07801e219480300000c00345000c03034114409545a6950b625400503516145110364103003900d202ca01ea060507101c0d1503002e10036682d40c10241c900000ea52502e640d0800030049003800394503d84800703201c112103041094807500030000207004804651210741080b402070000804801e804c005d49411507135100007541e22030480d40c2c41030f905405a1180445c81695001c11101019006000c0d000417490103014017181e5400102030703004c2d0720381e5141c0d11210048280142011140140c0c0082a103205100682c0c0c04c59262856051068601582c00c2040010104540045480c681455070f1101c42103802603003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 583568237 1250 583566987 583566989
    0x90a0c09080d05250210110106120530070803060103060504150b090609032b020703050c150c010e0717010204050112240b0a02011b0516030216090b12060f040b060a 72
    0x1d80031b03042c441d07081e01099000c20015014003242000340702c01c17647c514488940f548484000fa001c1c0e005118047c0064038594400c1180461440301c4055185241400c5421a000b8140880d00c503000002803040941e40341c010200039103030840301000102484006a0710414082c40342c4445100080760142e6503070384090a60b04501806400e1310060005006450411a90311060b040303c102e100a03c10281840099100d0a4036407000081c442402c400c010440c036408104841e21842c4010444015071640c03e00075021680400c02c014511141845030301d80560600c00511082c6070320506c8100040e80e84002220402481c1e1200004d50303201100c031010103000d910300c1c140c2602202400c0003611104c02c5c401000441100d500800ca802180c040a640302c02c1d5000c06a00021414003036054100d0480f410040c00a200b40101c68084854500c034170a841d900740d1116644683e04d0b640003010b4145031418034504506c1070f02810441c5403004104110700400342016107040503590000c1d01c20b45850882c18 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 583569487 1250 583568237 583568239
    0x30307060903213911030403060e0f01110c0c040b040f2d0c0f050d062402241306020702040207111309050c0111010209090a0c09080d052502 62
    0x3062841c440410078090202004c140250625102e440d400702c1a484150304070105070f8030003c10b410a08480e0840c2d54584040340400d090200b0440080003a5041c4501ca450070b00c000c001d05103031400443d8490071071f0719190001e60341e940208101003018001107200100390780e04980014003000081d011070001c1540b102c901c41014501020344085a100600b410410403010a850014503102c07a910001e50b03278420940000306e4030440d1940801400b0300081c0c03801c5c02210b84002201e079039910741604100d80c0c40c075400d0004035050881d280406c1c1c1c14820400c001000104001d000444000300501c01980108450340e4000004800350030080c442c1c044a80c000e80090040d500d511223820110300c4500ca04413640d00c40e11818440c040c1c05070360b502452404940100151a52500607001507c3c89020040d61001c0c5550800c03125120b03965100b12103000d01118407001681c00c1c0f080d000500401043c2d00200840e07070000d003500c40d541307620008076501803c04140b10700e150802506590b02070b60344e05e5402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 583570737 1250 583569487 583569527
    0x319020a0c0b07021005070f1e0f030e1005120a022109010501260a03080c250b1b03010308090d0b1f0603020a020a2012011e0209030307060903 63
    0x9440342460b0081e1554600858415841000a00c0c003078810340300741c3d4030041c10302c480c0481d8000418641c2d0460f050314422002024401007807590b41100c1c030f9601040840102d105c015801c80c0d94140f521079134221350b0703040c20030f18a0003803415807850121340014250b068654000920f0884442e4030716848100c00c03006080d104403400c0940c0c0390b40c040c0c90240122400340b420180b00c02104159071084108070700022010b010004182e85084a03500030062849420b440304000f2519010703544000740107000d40c80780066080d40d040d481d02e80c10b5200b0107418102801d618030f10842036a04518101c030704495104281642d00d007555404a000e040e11580003410030f19044003001169001841002c10440c0d10700704441c0a552a070a0030b07000c0b40079803440c40005074000400c1100084001c40036514a130b00b4494208081c1510b00005160210390302d2020070b49945a645050150a80aa80115040703441405505001d044808243e485c0610360019001b00c0d21201c400b010306025042141000510b0021 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 583571987 1250 583570737 583570739
    0x60911210111090117180d0e030f061e04030903080d05040204290415090501230102071202060304110604080a1403040605070b0a0f0c0c030806030604050319020a0c 72
    0x2000800d0300c040d90800880e5082804080e101042c14088600c0d41e5016110b6014200040e000303044480801170003a440c190020b020444080000c101142247c0780555581000500c03c4c400e2504000580150461a0740f1039401d101019402a03242c130200c3c14580d4000500365541d0504580c12052503001400d0040005100389402c1ca903a0030051045000751001d01800e041010803030308500d1801c0d50701154050030106140c2614094100c520103112030420407003240d8542000c0b5040b03072003e034484012104400d2011401505030114080180424000f50500303a01d05003840c1c0071290300c0c000092280c0000000102080707205400880d49140c060407164850b0340320340308217039181001407060741d91103002c03e000c02000000008640c241c4500b40d548030b04010a030768807190781480180400f107565441e03e00010040c0402d110f08400309002d42d0314050b441c0c0c030301d080190485101401c106e000340c00c4134082001207034001045840425468507481c00fa40742c1e00303508a081c4130162100400ac4480810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 583573237 1250 583571987 583572019
    0x2030a200a1202120d0518010309050f0321060108061c0501050103241a040b0102030d0911040e0f1b22060e06030f0d080c070f0506040c21060911 64
    0x4840180b2030b01c00e840003254681c4030840d50307554009500c41c81001400c1040904c1d25466020103141080c0018180820402903541d501c500b06603c81d06404165440820f0344120640f400036191405141c5420300c01075401d00d000004d020140c000d040b04d0250588000c49642c0e0820110b80c0640a50810003c00095031285080481040c0074410030704011000312002d200341e600e07403180c42150450303071694042c1d5040c61000d00c0302400240701118150b0000784004464048503000c0c0710780b40c0c0e200c0d42f680c0e80d01da400681000b0486100380480703c0b0310f0740050b05600c000680000d182c80d01c003105800412a06068000140764031074400400d0720780710203410740c041200c1d03255000b040a0b10700c1451140d0055942209065031003c004105c01503a50000070240072840c0245901c503081030011202a00c1d00e14281c94820210040860442c1c032030784003400704020700100c04840c00140c8924000043d0a0031503011800082c0300290000d00401e42e10500303101003080300f08440c0900c0202820007a90080552 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 583574487 1250 583573237 583573259
    0x307050f0c060f07031a0f01021501060309061d0c040f0f020705030306040f09050604080c031201060e131a043b061501050421021504080114010302030a200a 69
    0x780700d0300c0c1c51543d0000420019402405100c114903100e031840f007440c0e600300d0108042c001104464a0540c0100c61112801c3c1c51a003140f03a0103070500e520081110720ac1440c1200c101c81e481a421940156201a013044400c0045146076280d136040b600801c086a5503520b034002011403d00c0018000d20014144041260110140d032290f035088a08002a0034000100700654072014001031103604100000b50001380c0090142c0100604d14080782e0601c8400120344450710cc01b80c1115000c01d01a00906100d4079001c0303098042e00c002058140310580c05103030b0107142800340b002c04a200c0e0341c0302c844000411440040100110750302c0595102103100007401e07914114004031900d01c460165500182d810080401c1d030740610316042c1d480515061502000c001131041840041d01441e844c800c02d1400740e80e54540701141080d50303980b4242d407039141c054090308607181c0010403007a01075568010001359801003504100306410070503200d54100500101007001d0441001203a00c10117100c0003003640d080315 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 583575737 1250 583574487 583574491
    0x70216061707030f0b1c1a0103120f090f0315050a0e19061b0e09010b0a1b050a021305010f05030c0609150f070f0b010b03040b010623030901020a14040e010504020307050f0c06 77
    0x640c7c1d08013a441652880750020300b409010242c0803840f0f15040f8036105118603034010212140c0e183c88800c081d180c500e00145500180c1c003e5480d00c421040f1702c401300c0003522410b03800c042d440d0001c110400b00350311002d0f201c221044a090840c0d8410f4070810a004480d080701101400206181c4403511080c01d0160420b644030140ca40a1aa10400850010444030881d0041d5440b602d61210f00c0d84401825042c0b10b080c00703c12142c034002c402e002001602c1e00c198607071522440e0a00480d0b950705050300c80210068070f5204d14801d500c4007a1814003915140102c0f51450020b0f01c1041c00c480c032078001c10301284100070410007050800920082400b0b8496002d554692040c0c0558070281d0762029440c086000a40d0007520707018000c001040304500880e209408152402d039070a411510b91060410503070811581c64089035000075011409a034013801c0c0d00000e401d101411400c1c1802e0a00d408132903201409034600456000010a880034080c0050301c00340070074207003220755805031890308903203500d01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 583576987 1250 583575737 583575743
    0x415081e1b0d06081e1b0a1d040302010506030a0b0609070e33071e05210c0105100e071d040204230a08031e0f03070216061707030f0b1c 60
    0x1200040d844008101759071640000103200100301c45904824401d081c2c40b01c00c07031541c0c0d010141701c100265041100004104441255206207180d1916040180c02e482000f0300c0303a07200c0d4000f20700f00c80c0080c0b05800f480f42c02120983c0c188405a81e00c17007040c0d40c00d004490b06550300144410303001440c4070790f5050b11181d14000c415034160f0720ba4020310f603203283d00903007800406400c0c3d80c101c0010049055051046000d001c0e0007120f1001107020421100030400048c4441811400503001603019000d0080b15004240800304800c850700c0e1a0040401c0710016050b4402c00130740254240c210345502c0c12582c43c40c2c500401c1155540d59600c20101d03030401e204074000c0c0750f000240200d00649420a1041d048a00c4000658600319181e0307010b5410400798420712040017800d0080c1c680508014014501c00e8003250014444036403503400310b800a080300d80c40a03081000c1000850303450725002061341e400400b0350401181c40c2448402010140000300c104903001a0080742c0322800042c00c80b60318031201c1c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 583578237 1250 583576987 583576993
    0x405151609090b0d0f022404030605010e01150f020a170301080d0e01020c01030209040213090b010210020a050a03111603023003010e06060706060b0415081e1b0d0608 73
    0xd80c802c030420640c0c400b920110b80c010420440e0001140da0032518124680c40104070050800007401c00300c05134080c101101030b0302c1c100440c1c1407042100c68882c44e40540341c1107000881b150714100c480c0d03401e11501c3e0240c404000d01042c0088902c1d00070400d05004a900440000382040c2502a007012130304244a10180c9109884444e00c940740218000d040944040e07021f03151307081d9503000540c081c0d40070010850300254200031034040201401c2c0b03400007500c000c89002c0f03921003800380020b1a001c0120541d207206441044494502a08881100e00d02c203424100442c00241c002d40d0078600380140e000101440c03100d4000c001c20180e02241c01260112052600c221178100f108c41c141606056041d01402000c08000501000420070718007640508000d104920704001c0e0b90f6a602659a60752040711010000b050a026905220307050703c210211070320304003c43d407818402d10079100b2520240b0601e0400303c1000b240c01c0840090344144000c1d1490070a82c0c0d6100c07800d0b13802004003440d2041d03502e0780c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 583579487 1250 583578237 583578239
    0x1020a080a0c021c051b15010501080f010323030a0e09010605040b030a05220c0518060303090d1506030b220c06030f0b100c021203210405151609 64
    0xc6010b1003200040d032000d0740100003d00d9a400481000e41042c0341e403030b080c07200c00d011344042c0c15140c5442184139502e0501030103400c1e000441c811000d91041c1c00c41810300c4075410410180d01000b4800d6411a5008041000300344801d40110b01c0301062500394586c907000016900701e1302908100d84407842c0e501a120654139130b0342e450342281c00d4080c0b8000c581a0701e4042000ca101e801442d008242c00500c50000181c5502085035447c0d00c00155441c11170301142c5150007000149416190400c000c00e402008248600d40301000903128803d1041c070f144507000765410034041c4180c681c804041007c00d180100603103501da0400b083c1440742180c10310209003150b03c2c208080b058070030440050b298440031840c005030505030242d000c0d0808800c1c040c0429654a1300c0c0241c0e40e00d24246880030800f50716010004081801440340140481410909551080205031000f0f030b40000c00401c3c85103504255410f40c0c64610b0030900740314403400444000355103081800f03445520151080c00740241030b1910900c035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 583580737 1250 583579487 583579501
    0x30308060f011b080310050604030c0905090316080a1211090a050f030307121412011806060f0311040b03040b01080f01053606090309040608190303110d020c01020a08 73
    0x39104400140307155143c485807560005031360002850b0010000f500c5045100e1300d4001055103500180e10a840d0000480001c0020605a10650341c2011105028514240300760710107018480e4684001016a00000b4542b505240704264552130481280407e00c00d100401c0b490000507006800c415200d6280e1080c0042c091501c840c0c1c680700c10b80050051030030004547c958504840780500344000340710003541c3c8580e030a07200000401183d0b040444151700e9504100080c1e140c0715541e810f036103920f4900001844160f40207101510b80000d01d103000315006202c1685417400d4012036200000e2080302205120400040031741160581d507601c0b08640301422642c011609a5109070b03401026201a600500300c00f261f0b124100305a440415607603241d01d051001d86900d00352003207400c60500d81000c0f03a044c3d401d180500400300101704060080c142e1004a003020034203840050b4004050581d12401c0c8804d10440900380da410030440b040440d110388001050328082c0d40216070020004e01144002406 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 583581987 1250 583580737 583580747
    0x507031d060f04020f01051e030a06080a0f0b060409050a060b030625030b180702010516050a091e0b0a0c06110c03030402040507090801090317011a0a120f06030308060f01 75
    0x4035080c40c120480c41c0f40c59640030301c511604c00300b034240d0410504000c03c6000001104810481c50600e240981d0313a4074103192034400f210300e181c001000729003015600c134000c00ca04071401c80107070382c101c108200161584000640100044c150060250080300c2c0d519081c0000342e4003100d0040420f400b9541a035031400c1001c0e00140e10b14148007640300540701034a280354441e500120180d44041c2610104218007035000031404e50441d441c00050b0344480801401c8100c0f0a0300502c1c145843c1800d40c2001e5807000f018002c9000b174001d654021140114040380320300040e07074a02c000d000100700c80d542d61601d0000100100240d00c1d040d05c0c1a4280000914600723250001c075100c4a201a000d5030071a169642000041d0001800075010040c2145011444003c00e2150028061094917061170307401c0f105032002c000240581c4444074091a05810b29851b800302000c07241d51400b00d245c60821180155140740003000545008210f4501c0c15002000f0160000b0000340500030440d003920b461b001070401160 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 583583237 1250 583581987 583581991
    0x2030a0c020705060a210e030705070b0f0901030b0609060c0322050f0904030e040c02030403060b030706020601062607110c0438100302070201090f030807080c100507031d06 76
    0x138020004100d1010f000b403044a0308055000300d5605c0280010386020b03003206544040c1010700300d1382c200040c4d40e81044802c00048000b864400c1c03c480c140302003240c4400b00c1e40260300716141031585507140c1400395950102160902e42004240b90b4445a1540f585070b600d030171660000420000560b285d00b5031040c031408001c120354000380302150000d10242401170048019100310203103c06210402803070355642c000c1c1250811030b80e00075900c0d14a1424400c040d2120900e9050181c2c000310802d000c2c445d804070780d40781520341600f40b03641c046c0e0028038880300340285181030314014030300f110500404e2a0b005145100d4440c11104032002201c1c8034040200712070007910720781c03800213007400113404034640002090071041004200e000f1403040f000c04210340158105100000a6000900d01c0856811146034009000c07064040040c41d070a50761105075910a06c2000f525242d0045180105502d041040c3c120703060f01d0100600890412a03409009403006484e0ba10104080a00d001c40d1400c001840c0c034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 583584487 1250 583583237 583583239
    0x20909130c140105090307170d0302070f0605040503070605340207060e03070512060a140f1f051c0309171c0216030804050a05100806010f2102030a0c020705 69
    0x14074024642115040320426001c0d02c24148a41807114910695051210070014143c0d0a0380500c100058070845042c0b411071110801030601c184013030000301d02082042288580e100c1e40018039a229418601e185000e2450000c00380c1d81044200200c0200289840a15a4100d07003c076005610f5400c1480c1c40210800d00c01006a1101702c0401c841440b130b440038605140b02906440095460700b020444c4880d8440220806034042c2080c4011f2460601c100ba4006000c21044003107402c041c5c00c4009440c20140000e4aa00b00300c82e510104400700c200b180c03000788402801240800100d1300240c4075860240b409502041d244a8006128643d412803800540d6518001e000b000407040c400d039001c1007200c000501181301e41d80b6849100741e01800c4500103940920141d0307844a20344420083d00c800c40b508203d000d501e8800207800c0c40360300805c40b1500007c09003090040ca800d1391008603284035600d6500981d0008846119003130495641c021030040c884a803051050900610701a43e4a82d407512802e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 583585737 1250 583584487 583584503
    0x305100e21040506121b04080d0503060f041b020c0316050d142a011d0103090f020337030503010b1e040f0503060603010b01050d0213120602090913 65
    0x40000610242040c99079640603060a04090700e880104069030800b008050504c001d4800f4880000300d4030340e84900010b02c041c0441e01d0507007007a100d2a295552648420180300000c400708219a844803805c1140351800382040190800040001440410110000016000320040c0f58924140070485002d0301c803030520120031662a240500c0b45c0f07a0045402070ba0085281011044a02401d02106102a289180211803119121124501940c00c21802414030031540340f07801d0304095166000301d13480000d00f0300003504401d40c00c1c0700e810259003c20081d0f05000e04045820762280f20210502d8045091040540e0a11520203c0c0c440440c4c0802c0507001c0b500c283300400091011200400011a84660749000312056480b004c1c101e4001d6000300200408049050003207040401c807007a40f0000440082c01034400c004000782c542c0c45001004008a5000100080c40550074106ca5005006e03000b030401c0700010a003042402504030040052040c03480c900400e41007904454a500000d42041d0a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 583586987 1250 583585737 583585753
    0x1030b09181203010f06090608040c0501031d070e0a0f0b030616050408060403020309041109090126071d090d1220070c080606010203180607030c0c0b040305100e 71
    0x8541c580840c408190024469072260110100c08103003d1802001d070f400490b0a03ca05000000d80b500d2601e810000c00c01c0b8101e400c1101081c80b48140504035042801c0000d24070103006801c2260f480000304031920384c480c500000071866444071403541700c1e100354030041048000f5842500306480c09a010a50305034081d01c0820243e400d81c5030141410b18040c1082c0e40b909640b4003c0c1030a01c0d10489050300543c101082e28180c0d2700f068061841070f450005081442c180c000c00004000c280c06020303072012801c16009005070b11540051040140e00101c0c02c071000b00d540d410300003042081341d0000ba01c60b42920340c08120601d0002590400241041e01c60311044244020410020300c1c41d540031900709100c0c0d0103c20032458400340140303402e50141c3c82222803a41444082c0d03140c00350244c0031504543c0100b0000001e40f91541c4220121788007101c0c05a40c8061500301280c01044000000c0d02018400e00c000500051705d80c002c0007100e02ca001502c0301041e4001d809400c5814881c8940c0c5130740c02a0b02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 583588237 1250 583586987 583587001
    0x140a08041e050a050703020112050402013e0109020301141618120b100e0c1b0c040516110106060905060a030e011a010212071a090304081603020f01030b09 68
    0x40c061042440c0c400c0440050241c0302d403442c11048180135075040d003050f1418070555910942020940100d44010b00c03040c1801d60008050405041e561440301204042c0b0240490551a01a1018591810328103200d84079102d02c0e0b0003070150000491003586409031030385000100e1002603200e10250340980c0842c410356401a1501c3c42c0309210598030612210011856007040030146078118000c40d1070705080d25008403800400d40907504114001c5c0c0016042007030b1791804402300d03001c040c5500142e00c019051140440d00d44130300040381e40c0d84141060b017040300620b41c00d0340501001e5400d640b0f1010100410603510300329001d50003840d000801d448424852400d00c507000389860711807440c000544440c440000782c03c6409400134065440300142441c030b8a584d04100841611803940c50712480c2c41c4103551000001082d080705003152060344800140c0c10b51080c41550000e10807102035848004e00d480c00c1b100c231004a4081248130b000d5940d040c00d40d0b540b00c1d210ba18010200a40400703c152135000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 583589487 1250 583588237 583588253
    0x100f0e030d0e130c230c03040308120f01050a1403010e0604030c0c060f080105120a0219051509061209070f0816080a030c080306190b0910020607020601091a041506140a0804 76
    0x10b021205a517010450030070a401c0070801000254000c40f07440b0744035143c032442880c580300041c0c40c41c0400e0070003a0041c4540e6a0700d098810440300075180b503400b200d2502000ca405054185408249409140104800c0c190400c1c038050006210b441d8079044c0d1600c0b0001510420650500040080c03580c0005015500f0008a28650301c1c407140d0844256502690001346194001200c0a0700150726100030042400c00071a001c480a030441c2a9500f0300300c0c200301150383c0b4010324070b8081c8001e51610101d16403201c14032018019143d0b48a000350072035110b4000b19075038040b1036810041c9500804000440c40700c01329050160725032641d2225144203003030300c80b01c1e500d80028100692000031494a446030715002041c410092035520396058031010300700c00300803450b0180791403001990803d0080251103540030903114152030202a0014004008070500b40941e03282240242e0070502e031102d419401d840d181c01c401c0445500e40c1d581103104d843c0c00784140450003085003120218010070003060000d07402ca = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 583590737 1250 583589487 583589537
    0x3090c0d0602070813050a05030309090f1b040b0a090e040506061e121605040902130f060e04050f06091917161a0c030105100f0e030d0e130c 62
    0x520000b50800020340c4502c8039a030301802503000000d40c0801c003000242000500b907001400e0460255040c204040d011400210004184843c02d8000d4800140c503124003004840303032108001061034403181c4070700324101282e00c41d8181101194820754009987c24580c40607a105d154031401814a83e00c4e4032052080100d84016050f20a500b101201c4a89445030062030b581c0c00545001010302d4242850200080111030b0020303030255040000300b8001d45c445a0310710407011000080012181c000c1850180140340ea504001d0000400350244028040005061600340c00c0d41001d4800300d0703c0340004c4907074900d400b00c08065100c2c00c05001b0404a0110081040030380d007071611490ad0103003207401c2c04442034180d01044071002e02d44420306640d814505181c0b0303030010302d400100785154184400510016130400d4080104607510892844485c03061669542d0320001408440861b004410050040c0701403a08040c0a411700020350503044019004540c0e0200c907035100c400c0c0803401d0180408411102c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 583591987 1250 583590737 583590743
    0x4031e052209110a0801170a08160501020d0b0306071d10020a080c0a05061f140613080c151215030a080a0e09090109020a0b0d0609020f0702040b0603090c0d 69
    0x18004000b601c0ba0040c0034000c000403800c1406551003500103009095100c0607000351808454140900d540c03104002041568160411082a214404003444295000004000800550011490000c6894150001c1d9030500c400c4058580559a24408455946003403003d40041e00400d50311306802d003400820203040000ca8070540312001c4c260b0301c900740180e00c07401e01d8000581c0a031142206101081c009290490051005da0040c40b120110303182d280c4110780184090791101b03c000d03144a68402d4101c42c0150010b4540c40e040da96074201c5561503442e844004c5009809400e01000d84154039000c4582500f0400302401840c1c440310745010f00c0d080600b03802d90b054440c40d42c3c2100418401400f41c90248500d03034034000300000100510182d8040900300c4555a810314030143d005a541901c9401070307076100c1d6003442d101c03c1d40c4000300001c2e14540d404440c0352440003948004092a94004000150003035500303026283c844424000c05100488203128240c004810340a0705150405203100e031180 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 583593237 1250 583591987 583592047
    0x11090d0602132d0611070608070e09100e0601030b211203040b01080c10020a0605060616050309092a0d110a0810050103051027090b04031e05 62
    0x502e8460003032900b180f090b00c0300c000d40c1e4000c00c15403c146480c0150700103040c0b41d00d010511150b2980d15659aa4243d0042c002840303809000684400e00c81e540c500c0ca0840001d007000310b94104000300d4a26003007030307004034903c1d4603d281c00a441075020b0f000305800018040c060660b800c052901070200e035070000702c043c00759000c0c220505003280c425101a41c081d82c003c03d0341e41ca41d545480c8126180044c01802c55029040705807402c10304038cc0128201141940010f40032620380d81e82c600190300b1b0301ca90041c104a1061005110301400000009010b25080980d8900001d845064040c407541070000c042d00070b403001401c4021030203490000a07000c0c448080c4004124540c0619400321590094035408000404006c00c026030788c41400c40301c800420302800d041100c1d090591401721116030501400041010042e11400611162141c80d070400300c02c0c41c030400980015103402c0b41446029034050700000c4041f541e800b0004582c000b02075107034440fa19643d10701007049500892400c1030441c8000844 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 583594487 1250 583593237 583593239
    0x5040216080301180b0a0b190c121106010f03050a0807030302040504090f210504060f120203090f060108030c0304060e040e0109060605030d0201050115050319020c070911090d060213 80
    0x6074020069400790611482000750044402e541c2400c0343e01044055200307000302042000551107110440351202e00c0460a18005a4603c005840204401c1d1000f021070140140302c44695601a032204900e0080742d09036007160b640e40c035103d251825180000340481d00500320f41c90024201200909019200b810090b051035500d40000381207500201c820b5404a078031000782000c102c40301030810704a5461070080140310750704507002001c80c0110302030203090210919800305068003502840b4140b03035404200b55584d18200d45400d440c0e5500521140b02c40c400c40c07002140c0d0603404015124940e1501c0015401d1518198041300c1c0d0350103044829810035902c4809084880b03003030188442582c02440082180744c5440145454482c280350054110391400f0700502a0400301c1200c0000701c100341c074180b603d944804440000c5240c0160340d5210462002400c100c0d881808201c0c1c1040310441d0b40c0400000d10f81801001d128812013814503030068040d41c4250000b8000d5000d002a40c6d503d0080306010307 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 583595737 1250 583594487 583594493
    0xb0708190507020312070c030c060203101e0f060f05120c0c010c03090309050d0206090409051c0c020310020a022d030a090504180308070c0303090c0b12010b0a0905040216 75
    0xd074016075007900160070008401101c1d20881c120550003000c1444c0569a14000f03481c014804101d0f0480100b4042c2c002020800310342601030120050060b0041d4111214010701100340001c6180c81032070008400c440300000e2090190100700110813060321082c0c5440300c03240c0c001c00303c1d000050020b44030350800e00450380500000d00c500000003a89840014a1191506028110100c1c0c1e40c0500d2040140308281001601c40d5000c6d9031068800f520003140a904a15000d410035000d007902006194103038003442d41c42c035408801d4441041c001d405842c2707280d4207819003034180e200d205982e80150740141010101d07644203070110104051003003040c64288001c142000e040da0700c03c4d41550b0019124841c284168900b910072001018055a940c0806000765074001d004008000e0040050080803c1c000e000d16000350041c0707160943c80405070824944072101100d00380c0011000500c040c1d20180007045154203071045aa01d0603540d00c660b40d59602e08010072001c1e601c1640e40f03110b0440c0b24825a800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 583596987 1250 583595737 583595741
    0x618010c0b090a03080f090d03180b040b150405060f09090c04060b041a0a0c02010c0602040503030703110c03070501022d060f0105031204030b040609110307030b0901180b070819 78
    0x500300442c06003e40c1146414028001c460241c00d07107102d480c0090030300110b40b00018030019000d50504022801540756920300813440383d10900135204004007003c0104102114000c10300c5640c01c106a07034403080c980807e21040701c0c411188140c11411515207000c041c41d00d6078100f0350201e036080071580000d8101c8013181c03c0c1c40c00d6501c081342c0c071600490207209003040381c210110032182d0917003040c0c01c0c100c1805004229148031b07500641403085101c90407081c04200d40440b40500340243c200c9542e086070b460010907403c02c006500701c2d9406005039103122031501145401c100d8405034020207104d1423a2000300300480703070b00300b030389034071011a424900312890306101640c03244060103800d55403507140c01d06040c02c000c0e0b11101101e0000701000140001604501680d8211b07802c00ca000030581c40c9440d052551000c000d180e103905106e104000405c2100c0950554400c20203400240246007005402c1d02c524861444002c0c03544803c400040e4901d4403c200160340040c001c0703450030b8a020b4122489007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 583598237 1250 583596987 583596991
    0x310030f050f012405010c050a2406080d030c050c150703090f0b090c0a0b190c06020313060f0b01080a0c0c02120a06112a0309060d060302100203090618010c0b 70
    0x1013900d95200400d60090904940ea00200801c1c2014800f40300c0d81d80c1d43c01c2e02c49e4210000141074086d25403c1850345034003d8060b442150b4501c504115180e10303070f01e1302940c0e00ba0b40244e0200190a081e0503022031482403003070702c843c600700070300400c4101c2c00031002c1c05099030010f01e500f00701035039050743c400829082c141c43c0060a0260309450203d0034622202402c044001281038014090480208031986080e021681e80e0a510240049140301050044600f01c1013001c002d00680d0010081c032003080b030084089100b040c03181030304001e400395041da080141c95000e012207000c6018800056070b50345098100c4082c4100c9031420317a02d419a0303036000945040c000d802c511416408000483c042140310302c0340030030034000140264207104950315000c04260001008190070740c2440c00215120100300f0a031411888020440354540c5041c2d00075000030080c07880103a11441c0c2c200c8e140c8030401d001008981c00260050142454428804010007c0c410140020341c100007070035000304081801b25025034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 583599487 1250 583598237 583598261
    0x160609060b130605030c1215060d0c06020c010e01030b1c0804090204081b0303070c06110f030d1a09010f050d050f150a1a0a18020405030a14120310030f050f01 70
    0x55040d00b000e0905d898001d14000d52401010141c40c08828a000052214428084445802d01c540c0d551000309030441610070004020311060540880c0c43c903004140501245020390312804000f001e2401141503e110005194000141080403584030200034034601d00e99000c0c6101526141e9140e41d000101d82c45a80b0001c0c440d0040107c0a03031000c201c51242c414990114003c60070406c1d00e8486011f50540c2d803080383c0901c40c00d44650640c152003801003050011000c4196915401e80d000d515002c2c4c080c9008001c42c04604104868482c0341840e20036040c2e540c101e40c0310707412a00300303402d00003130381c042000942e5244200044000d00541c00c00000010340d201c23151310142400d007a84aa070035140001d81034425807500f40c90089503078407040c0380d1000b1111403411050351106042081e0000f03108036000769800d07016240540051244042c2c0d10318070031072641c3c1240c036005841d000801107400161680412030080010030808200a115505c41c81070003101920382842440c241c5a0031180800203403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 583600737 1250 583599487 583599491
    0x7080f0c06071103030a09030e03160f1d0a02030903220911210705090d0b0612280c0e0f01050a14090406021605070f0e010b160609060b13 61
    0x815440401e11141c1c0d0028003900b045407900c5030701008262030340001408055807a82e00e500c0c0409240c810781e0015404400a416166008401c01c2800a2400a4007408080341c81004000a01000200c10103810020207141d02d18180c035800c4800c00a580f014000e40380500c8140319401c00780103103480000340e080248020f190b44a14001100c0190741302e84103010f200e104e050160720b40c41c81d501070b542c1c00805004401c0080a690b4403078191032038001c0b1310310f05030404001c0000004004d00d00c1c80d658090b02c411904074010385d00e4654041e030b4811f080b09000b200444140442d00c06c8203e268a5285814031610b034504403192900c403400072140b001c40b4501c031041d021000401150034550444006000144401d0407268660740c0414151003000e000104400d500082190403110741c00b5401c40495405000e884155607100e0000000420a0103601a000c104000019280f401d205c2101c1405004540d48490380c00c064039000004c00d00488207481c040c0d00e50440101558070101082e134108400d00c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 583601987 1250 583600737 583600747
    0x50610080f1e1f0909050307020108060a0b04080a1407060c112b12030510050105070804080604030206040506060901050907080403180f061107050a0302120a06050f01150e061e07080f 80
    0x21a62003c0c5041e0b00c140886031074443c280010401c04022070b000140c085c01c007050036441e40008075054109036803220960355004540450718401c00b1540224842c012400748501d441035407151500c0704502d00c51440132036080d41089001407a040c04a00100d000206601903401140c0300910943c1c201d600b10854000c11003080500300030346403080038020602442d00b0040c91038440003081c00c20503503000b032506000010901800f08056501190f001d480d0403410340742a400e0a15019550360000d944c04c40d001d000c4c4000080c610b080401c0e00a04807400141f4007a841c0c2c88061080c2ca0800d40900150b00b00a10f9100c041c01281048186000030021350000e102d00341e203042c038000e140300c00301010101950042c000070801d6958200e001c50580c1d404440382801e0410200303d29151030f140550040a443c00c110411501030f060301c03001070403280014120711059018000840c1c45d500703800c02c81c540c011406c1c081148646103503222100c8040881c4001480c043d0280c82d0004c0c00d4000410041c183c010000b8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 583603237 1250 583601987 583602031
    0x50c0d12170c091c0507030302030909013203031614010f152706031b050409050a060f11040e220c0e07050405190801050610080f1e 58
    0x41d42405014404070031426051001803161503200383c4001a00c10118100800f0b001d0300314000700e001c00e5902c0001c0712012652850080d440780c00854030684035800c44400003a51000740ba803104140303042c24400329260144000c85101c14169440d000d501844188079401032004074603100c004a80c0100f80300007400711030400c02425642c251008640c150700380118102d0141c0e00c88181c00650f1000031412201e0111a1f2140340800b010102c10002141002ca0002c144074000c1118a03010301501c40c01d5610b01c2c0c6400a000503210388000003040750b40b14074144004a10140d00204040c0581500820603002c0469450069080358000c070b0042002c0720103118024900070b002911401c004202d00d0310203106603d030000015914428102c004400200040440b48290300316000790400800c0c1c1030100c0d160042899016000d030061090961030100480c10724500300d584442d6101071540c0340c3d51141e4034000507100701c10001c0c068880b01d65840b00c070740020510041140744650450701d140300800501c45 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 583604487 1250 583603237 583603247
    0xe010e0615011b0203120a030c0e150d0b030f030c16080d021c0306050907030b010f021f02180d0803040b07090f03060e0f070f0323060105010c050c0d12 67
    0x10700001d010340500403140620740d820110000c80c07101c5800309190f964802d8000309003011182c1e03100c40d81c800400a07091024a4060b030005840e03801d2607440700d488008600a00011031072051508110000901c8007a494200c2a049010103440c0030f002d40710500000c1041c030345180c02003482e01d02e032900071000c0701940c1032104041100902101000303060012001f44041d4641d650f10032411200044200c5004409001ea0410001868094075005417843d0a800c010020001c20b41502d0002d85640004450b0610000303040c0008000c0660311503075200101c00020095021a98241d6900494400640e2980e28860010342407405044012790b42c0c03502d89015690000021b04980611844001c00d01158007425108010740354410000126010030058807440c5c0018441c04000510034400c2c0415403200100303d010480b8803d48030310350a80540d1074002402c5042044443e501d42c400d500400c915803040f0000c415481c050310a54607103039404400301340d134000020003d0b02c3c03840100074980c8000e503200c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 583605737 1250 583604487 583604491
    0x90e060a060f050a0203160b0106020f2b0201090803041415130b070c0c2c061c0312050f010303080a020a1706060d090506060a0f060507080a050d0e010e06 68
    0x1164194001801c101d0041c201800700340401040090104885034650b000b0011581001400303c00d80301d0512036442d040890100900654005004085900c5050704002425a80061000c00100d0880074800c85d500c80182001c0c03600005c664803840a440481c0518006500940c042e059100750700c2e80180c2134034500044441e405006c0303100c0100b00f02c03001051049100c5426401440f00c02642c441c1c3c1c00403901d07450948006401c140741e446002400280760350702c109200480c00904404044070342003c0075000400c0b2140c94100c1c2c0304820840d004035030b021034101c003248242451111011203202c0f00c0120750044810002085040c0014000d164020202c01d600040111080d4540180d03248010002c60b0200c0d945a456151100030440c141d981c082500d20002e41030308200724140c03250811645e00e10040da40035000e01603000b00460301c0c0b064403115034107071000d0707480e50740c544030482d529041d40341d004e280507100b00002442180b9441c503250041812003400c410003c00c6511502194509250300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 583606987 1250 583605737 583605739
    0x41116031709060a050414030a1205060a06050d0c050f16150606170c0c0a110f060c060106110c15030702060703060503210f160c0f030b011502010e010c090e06 70
    0x2007008101095400103880c83d030080c024a00171a80d510b40d81b500c0503c448941200b00410700010803811040c5901800384413111031540d1301401513894008c20f01c200c3d02011b00401000400030000c20300010400d03004102c0d181d020b441c1241c82c0860308224002560810951000000c90364001c00d428001007022040800000f08030400c5254980b03030014000036040c01800196168040000d5180300095003600c050244e91001c0d240e150320390b0314007071000e40c0d000c1680ca485210340a036180d20900344a411fa82400180c2c400070040c60b4200101611240308400907902188101c841c0c1c0c2000352a80014240304190400c00961a030510542c040d041c010000c1c18075041501e8064100410340d03001440c4422503248507626240c030300d02d2640c40c0d01c440c45480c460008103c00000c01071141c0071204108200c0d94000c40e55021999128900c0900b20102031201801d0318100ca00180100013104405d25101d00142c0000520702c00180442800d480c0e03814040404039012000410203841d84002a66100b40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 583608237 1250 583606987 583607027
    0x3070e010608010b0f03130c0801050c0c160303050a1d2707030b061804060e0903040302010807053916140f031506060c100c1215031104111603 63
    0x401c52084e40044c08003c000c402c2070200c150701c01003400b020009040140c01c603900240858903059001540950124841c1c40545c405c401c83d400349680cec01455076054079803640d00c2c2454002d0f481d50880d58081a444a8101601c040c808450b282d0303607504205c4038694507010320217415079084801c0641800020b054105150620301e40364540d40c1c600c07007180c8003494511601c901d99815540817400820790398004029121412040c0b140715030001000d0300480f4403d036245400b90b07580e580110380900036443c815400d01c4010f0110001030700712225800c0403408000c0542c0c295030210490300c0c9401802032900007069900301c01405051440004c4054612007a50030842d00000032012a590308010b90000c2d03200c020401c040340150396880c0480b00908281c000b100d110400c12664400200700c821207120103d2400000799240d1566405104072011000c0220400381303241d5229461042e098226155106903074416100e40b068900740030f00464031017014410b101005510b13028100c3c61100301880080e40c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 583609487 1250 583608237 583608247
    0xc090703050405250e0c0705190c0911090316060f050a052a030d0b030d1704121101060321050756010504020315190503070e010608010b 60
    0x41d40001c0c4001d05013144400940a00c05100c018403070342d51198001c00e610700314881c00c0c0300d000b210300e00180940500801c15940300020700700410340450b5106a0042c2002e44070001004a00003030b50214881d00c29902c00350f032422080c07800183c10013808403101022900a10010b01915074464041801c05200b81085407501d9500b010240c8180501040020720b900c1209500031028075500039280d0317084421080740d848800b089403030005030202120740c41c0288164205114201e1140300c1d004114000e6103c030380c1c9151219201d100168602e6134601080c80001c4500ca010020300740314440045008002c00d60b004094020502c04114460712084108041407000d00049055440c03942000300e42c44c4a580958840441102010792604101c8000d50004000003094504d000082580c0b440c0504104070f842e81e2580d0400042740801e0f1181c100d041c54908100e80c072807c001062444c0780001c6075400c40c0c080d541b4000a4030302002170304004002030149004100e00c0d40c00840582c09031550a041d01c1c182 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 583610737 1250 583609487 583609493
    0x12060301060b121e010608040b0601090501090b1602060f0a02070806060625080d0c0305060a06140708040302040911011107080a0209040602070b010806060a06140f2104050c0907030504 81
    0x140a0364101810ba40383c1807012500c2c805101d2803803422900c400740c03895010b43c0e40b004003500441040300c0c16201c1003811000224190f10981034032056460503103940ca195400e2008000154020034502140a1251050300002d40c0d10390b400b0302030108800244540d100c0c0300044c0203041c22080d9102d4601a80898240409650786138140c51010500100c1d11641d56100c0310351700c0c4500c0c00c40c103010307101200000d0881c0141e096504030039103002250301d0030700a94503040c05105060f00944104400540100d01001b0000e1421000304902d900414a9074209903d0703800140840b0301a94007101d04400c03240c2e81640c2c03941c2250810b26108003000142c139691380350003d05a1100402e09000740f040300c10300c00207804c2103002d60546950607000f0314121010340c3c45800312a61500260791080c89503604100000f8143d208556071038800c441e1071201d5041c1210f03140d9500700b9811220609103540c4040ac407440d22001c4502c00740340304500800003005280d103884284940c2040c081c14140405003008100004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 583611987 1250 583610737 583610759
    0x2a04050a08211e0d0c030e030c0a15060801020f0406030606081509040218180f071a0a020309090901020d050a0b100c0c1e18020a2307060207081206030106 68
    0x105404400c6a0341c4200c40c04426100080d00d04801810520114085005130b001d548541c64845007510f08005034002c14008644d0390003611180c05980e444240218001580d45400c0900c2001509001c201c0755180d2843d02e003aa001048015005c0748081002c001d1130707906010782401403905007068a92428600b03400902580d0283c081d0703000710b1542001c1811074860000864000300b078180841c0c0c0d1801c21400282c1082411058000a4803907121210822140480c850b01114001c81c03900d20b68180111100c0899040b00c1da0b1141540010300031040e0545130301c0615446440c60100059440c15040c0b840c0c1c040b00c002a00f0480c0b554a81350064103942c03100040a41062054148007940b82d00c00d10b45660b00c03850a8102040c98420641584041c5624010f00d0041d6032001006450480c4895074010490103080c0c200380000e001d481071410510a80d07500598840c105032020f51a28070380d915100280d0b40701c03440481d4201400101806640c420243d0260044c004a0091240d2071901401100d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 583613237 1250 583611987 583612033
    0x20625050a18120f140c0109050904020a03050d0206011806060804030c060609020c0304050301110307080103080a03111c0c020106230609030703141006031502032a04050a08 76
    0x20b1000b02038004a0416154009000801c6014041d5000705481d00c0d000e400b0b5400c400b011a900c0d042c1166100d20002c01141c4507a40d880103954500201d4604010801c4225002e0b00590300310800e160044081130b4180440380e208841a001002d06516003500c9151803820380388108043e41c5449414490355901c5501550026010b28218080e12181d061580080c170f1540d000c10704030303480041d541340181e6000c00170b4001c0b240114000c01000f000001030502512044a8450004e100d101c0180300284046002c0d10041100745000030750010110580016540320440c0c081d941521000526407070300c01d0b4040c2c042ca101d0241700a0001501d4001c2d280c0c0100940301c5c0c5019200b400c600c1e2407030192100c8080c1c0d698058000c0031a40c14540e60700301640c11b16418000c070011801740e00c640b45000711260041c841143d61210204502d081e00d400810020340000d000c5030350000c00d102c3c8202c0c0304580244014044294072894032381d9189001c08101140d280c07980312040d107800440641302c0007140780100803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 583614487 1250 583613237 583613257
    0x40c17070e0711071e05090903070b0403050d05090a11031f0f0f02040e04030809030307050f0d020403021806030106061107050402132705060603010b07020f040b060a02062505 77
    0x89654590031030030790b1003d5003100000c020340301c0c82c00c00080b07490707040c10b007010444120944040f2158540d0240510180103d4080205610400030100018000d4032181d510502919005080160301300c50701054410507200f401c0c00c0c1d40100281d80030b00169580f5429110f900310000e1510740b1940f611188a02001d42445026507600c40241143d00301c107400003040d115052500315038490322032280910744101a6003e5001805010002e91503c50001c105d9010754071036182c0d141400c5510010b02070651004070781e1000580c00b4080000162200f01c40f41c1541c610103242c0440c10318101050600b1500c01d94016810490078004070707221980b002c80e0000c01d41e44140c43c09a40c075444c0c1301e41c450000039207610036941903140300c00c070204082c00081e90450801200b1400c1c002505c804e01040038501080c0220101c00c1002c101c000014508031014440121000d0408207024010341c00146030340d045245002c01580004003000026901c4003084201c161090ba241c5c0d500c0f40300e41c1c1d8014410f0150440c64 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 583615737 1250 583614487 583614509
    0x6140f0405100506130e0a090308043806040b04020405010f0c050109170d0b010e010f110a0506150a051207060c060f0c0e0102100b1e1503090105040c1707 68
    0x1140340b81c1c0105403800302400b0040e00c0103a1310780c604018211402c03082e12030400d600d00420081016621036009005d0802d070150340700051500c8984136850000312080121101440e90850410010405031302443c2e8100800a0340d4400d04d040c10511090307a0222044900c40c610402c0240079581c0c20107440d84003004a40ba003000c6008007480c00c1070041c032081d08042e1044000105410070203a41c0002000c00310b410784010b0050b41500c00040d142112100c400a010030b42000051103001e10501002200c03c0346502152262051f41c0c5030142001000c3d0341d400b0060700340d2111111503003001b41110004050549814410300e4003c0d90003601d03006180038000400c07800002101c1803042c1c0d070300140c842e8a54000100b002456402c4040d0850302d0390072b1401e001d07000361402140724929038420f1612400000d0300200b0401c25510907408140d4407654280c0e03000840484085511000c40d020314800c999a4000284c80d040c203084c40c0a02e196154482007003040d60840c102c90701c54010502d03e049451302030207 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 583616987 1250 583615737 583615741
    0xf020d14040605090f120607090b0f0901030b0619260108071202010c0c0f091a0d021c0606092f07110109050603070c0b150109030213060e0a0e0106140f0405 69
    0x10340c0211710443c000e60700c0950f11020244007030f408a0200d028081640f1080340040d0340e4200c00d8624001d181d0401105407003070000c0e124550003608a8502044014096860041040c03040b400300b00101e203c0000050620340e91185c010401c6c07021001a2481c5411154150300d00038080340d6842e182d00445a0b070a09251540045901500040c51120703840911140515200c108000c2c0010b210b10482d0166400c080148610b5454421040640840985010b00d00c00c07194007401012461503040c2e01c0c0501c1c80b00d495a0124903a8800c88002d003400042c0494817a48901e10a42c010000c3c540f5005004441111441c0300d002c1c0a081302c0a1582c400c01d0000b162203403c005a88441c0240c0c41107401800000800c0040c0d540b0102400f603a5200e020140319075225403010144011421459a0124151340400d002500d86075024222170301c41c04d0341c0400d038a521106091260701c000c0d5828244a81c80d044400b401540a004030405841d41040387c000d501c0341400040c0304090b0b000441e900403540e0b100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 583618237 1250 583616987 583616989
    0x1060f0513150f1401031404051c050409060e060a06050408150615030c07060e060106170c0c031903050f1e1005060f070605010e1b0c07080a030f020d1404060509 71
    0x201e00c0003c1c1540880d04403207a944551046460201d080c07018002403500c1002c031a80000108140c0c011a00580240f55064805a42c100044840028402446010b0000050207402400707000060481c40c46038001d581080b6040c0211004590420800d119082c0802c3c016040c000030716281d4a40006928000d076114070004c0b40d00c2003010300c210078101c0000800c100d14010031388020f140c1c0c5d07842624208400610703607229580303440b03080c002e850000d4000f0542c00c84c4c4410a06c0020b800800f0302034154075211402c0c0500b480d44e4080420f02620206150341d00c2c0146406204159100142800b10010b51600168103400d044554680003140e541e4800030851032860214040064031020345000c1d074903034100b1003660054024030401c84034130741090004128626241c040c0d5014090b10f090005000c8620300c80300800f904007a507001d941c1d00c9403510004000000704480101103029840d00841105114002401c0c108141d116130f0901c01041c1080500c055000215011038107145010b50b102e400d608 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 583619487 1250 583618237 583618271
    0x17010b0327011104170a03020303060d15180309081507120e07031b0801020403050a030323070519030c0e010305070215040501020a03050615040905040c15090801060f0513 75
    0x181e9003903a618041a018141c0411401041900d090349a0703411854002140560344503030b420002801604140b010400c1400d1076003100d0701e0107205404600c03402450308207510440e0b80800c00c0c8000020600c0000e4145078021903a10058040c18019042c1d01402d20740380003400001030074501c100b000c0c6411f82081d250f03050344080640440c600565903407039968140b031805c0d50800307524403800440204e0001040c038814801c8070205c990040103010096220785054000340300480c1c034441d214201210b03200407800c414a01d80e104204507242c5c15150902118904088941c0c405d10f40c0c1032501d88001d110405811802c079441c420824030303011506e5078074810202d041101405091350160b4242c030a00040042c1900903114100c4c641e40c0410407542c40c64200600780d0051315500c0c1d03500c03404200074000564aa0005940300b0701400390f800ca400e556403525a40304c1d00300c4070340d00b001500c0000248840c2001f80540700c0100a015118a1003d05040000e040030010840107104141d6610725644c1c644414 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 583620737 1250 583619487 583619551
    0x30302070311131e0e0703033603080d06050d0b041209121a0906100e040206091203310b0c10090c0911070f0327090c17010b03 56
    0x110f0818000440b4030101140c030310682c0341080007220b013801c54001c80520005100c0c0110b94040d41e42c2c0b442c0c00e82008050550840c41403c9003980005500c4042c0c5e0300700400080c0c0001c0d44594401c41d9116802c1c0890000c54966811491241c4151450040403890101980703402903084031268030410800030050716442890381c0f0613001501c01d03002e102c050114149842c540c0741c3e094203000c041503503030484107525610221203c81361402804018801e90003c0701710541c0c8140b0141c00705250200160000301c1380d508003010320140307600010715590303107105042d041c1c92118918a03a800400020400b4060f01f00391900801c91a03500101d5001e002c598108090b8034007107880c4000b0000d00d01e1509008d1100000f80c02000c0300142441c0240a036000341d00210b07188035810203035000701c3c60a80da030100d0f04244082e10744032490300d024412082c83c00c110140c20700100708541c000a055120085c001d1326004020801000f00c101010042101e0070502c012694017a81071048000d004003000051504000e003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 583621987 1250 583620737 583620769
    0x1b0d1b0f110a1502070906150504060c060b03030d0501140904020f1e0d030314070206041a0a0f140a0606020f0c010c03050706050108031c0c0e06033408070801030302070311 76
    0xf0507106000c040c0d004142c020650712184030078406a0b466284048100000e07114803c0054410001040194450300000442c3c9109000116030807640d080020300c0c43c1c020415032a80d0a9840f0300401c024035100c12000c24180040d20356000034038190b00002c010060544002c0e015010b2586205407000c0118204141e0050040046113050300c04e00b00200146070790b4036801d11085241c000310f15030900010702c3c00e10540c0c2c8080d01c0b00700c0d400c444031004901e60f0068054242c190700c6c0d012656152541e40a04002c6060400310b10300d030362805c0201c040550f6581d510420035034121414810768520701145580f8230b04028204981142a40c0c41c0c103e50501c15034070090002440d02e000400c0c0020084002c0104c15131030001480e0051240c1040011101607401003008030b0942c003810550750518102a503070007881000c4c83c0e40c0000b01090800744001c194441c5801c801840440e20603c560850031702e0ba000704d540d103040c1c4025811985c000c0e50325500c0d80400b8091f000e00d0200d2034015651640c1e440f02c00e0350 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 583623237 1250 583621987 583622009
    0x907030606120308010f0b09150409050406090c12030e0d08091c020907050f0a031e1a0411030910020f0f0a020d02060a021305011101021b0d1b0f110a 66
    0x390b52000501180d04110086000956050001413030380c03030402036401568403403002285410034400c10070000c1c00b1843d010784841d4100340000510a80a07114a40c4554012407001c42c18481e1440c00c03282140241d0000e4003020441d15402001c00d0344580f050310900029031300d410b528405410500003600424a406038000040c5000340e03419031490250b040e149100f80c0345d130f400700d80b20b400701034441d40600441c9560f1042c05008640340c061103604100d0701d42c00d00b040c0c1b01030a20022444101a1810400111203141140c000320649007880d1140c107002c00744901e0602d04500b410402c094645081c0101000c12940208001c210501c0302030441c1d1341044400d0a2907500e503151180030392290100341c500340142c0a00300004090340044e008a0310b104041e88507241c0251305003401940d11580c400410200796500f031210944450f482a06400c030000b419008003c100903014000782100c0c40304030318050303204043c40d0380000500d6040f0701080740c1e9403200309110342c1107011000c0707072021400303500c0040b00c3c803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 583624487 1250 583623237 583623239
    0x702040612031101060e040f030c020d050601060c0b06090403050423091014030c06030126010c03150915032d0c150e03060c03060d14030901030606030e0d080907030606 74
    0x1540282c1e41030b071050348007402031226070340d075806074140d228003160023070079001c0610100400603108000808440f44000c05800380c14509481e19840d0080036004440411031405a42040c8030211040d07650111044070344001030325207650010020300a52083c0340d030340030000e031640704400c01200a80c03040c01005042d0038250310b420251158207032064407802c003410345440b040014ce400c02043d11b008480c8084c0446203540d18000c4150092115180c0c5619200000c0340c256100803020700a0903c8007610303903408619145093344152030f002e5983c0c45810300c80d180c241521041d2402402c00b004903600210080d00b03400054010b04284101305003092815070201518004120b005580f860645006190300c8182c140700a405440e8210780d05030030ba80c075500240000715501224401140d04c504060302d5802c48400507541c0d040c40801c01130f011303802e6400100b0010000e50781481140300422540c60305200310180080c4603032312503850074540303403c02011400182071600100102002154080c408010103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 583625737 1250 583624487 583624493
    0xd05030f0313060b0108060d140c1c02031608060703021b1c08010b0c06180115030b1906150f030e10061a0304051f09230f061306020702040612 63
    0x482d640e1603045580526003680754056500c200034041c40303840c0140c6884100c81e125120360301e6500c04080040194425000c03040302d56100e81602c1c0c4840d4020706032407040030400e4410181410a01d40c0341194065401408028544000858940003580d50070016900e041c0c4506046142400c920b1101052084c0810744040000100007600d0001c0f40d0359030f81800e0707600c900198540c0c0c4110802c0f051503520030ba01081c00c01040a42d03110000c16088000110036a08030003408100340743c1c4e80180d843e00800010841c00216111038100902140401003250a0600314400078500409250100b040007501841d1049400f03503010200003004141152900720540704140f01914190103404000e00e64440d0b10b03081c44810b00141d0f80695445000303046039010304403e603202a4181c8031522030954686803510082003255000d81c003000c207a500d001043c038a0041d641d51078081410a188901d42c0304004201020040c91403c9180b6031703200c200541e40307a545000240107840c141d0414440f14054000d02c1c410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 583626987 1250 583625737 583625761
    0x1021615080106030b030c12070509040f17030609160c050f030901030605060406171506120108160305210409020408010b100f082e09020a0201150f050d05030f03 71
    0x4034800c1503540d5812a80c03141e100710140d40030341c0a80d6802d940300340103582151500707030104d0005030106000c80c0c401c10b5590380050410341065506880d090740380d805e02002d0180310150545807080381d5403910300c3c50402c4408034035001c0005014805000c0402000680948500c11001d940c6801c10704803050461500600c5859500c880d400074003082c038003400010942055030a41d003ca60443e180c4499000d000d0700c05226400000b02803200d0340914184020b00b81c2c0c3d0f00c20180c24503c140b007403444240e40c14000722916180181281c5c0040041d590010000280001001c40c0400c071555612400e84030700301d41100c2c86004039080528420300202c0c000c40c02e9103055100b01444070307045800c01e200e4820080c090f1404034604030190300041c87c1340005401c507070307010012081910407d404844803545084582402d00c44c01d400c01c1d04c00d5070700010040caa2a509005600d44000040e0122820500e00402d102c40020f00340700f210b0107942034018200500c44248143c030342a458070707000503aa81ca00200c48590b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 583628237 1250 583626987 583627019
    0x303020406020f12041a040902041508010918020609030f0604050c0108060d1e020d0b070201052401023c0303010321120b1f0c060c05030402100c02010216 68
    0x6101e004168003488000003002448503d0030701c01c1a1500f42458801d46c81000801c2e5442d004990801c00000d91000c184020801050810343c18030510800030001042000f060388884005400c0100d02a40c10038400d585105565040710142e944501103000b0034140141c6508000e22800f40c4030402060020101e0981c155007001d9031a65290368940342003083e0b9076403124002d400c40d02030341c00029040281840d0400c01074001040444851019500c613211280704031805001130b5100c03000c1c4000d5001400e0101c0c040818040004036046c04040003e5541c207054038a00c1110b1010301d140300310302c0b40040070400d840001c0102141c488009032920742c0d59600a12045503c0c80c545c0a0a2130b50392810344d43d40440300b0859540c5010580803188001c0034051003160164071250341008880380c0d90a00d40c180a000030b0603295031070f00029505020b421039140d4402641845420002c220050b41c600d002100d01844074207242200c500c0700d00040746004020101c2d60f24070b140301c18000c143d28810801001d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 583629487 1250 583628237 583628249
    0x60f0f080c03060f161b0302030c0606010509030307020607110a030302030a02100b09070f140a090602070b12010326030c03060f04090c05040222090e06010b0a1e020a0f03030204 78
    0x1031040c00282007416034a58040313a6200a030701010300800c1200c101d048030a804800d0350301d00040b80365070f910940020000310740d8040340568800121001035020a010980e40040242001c504082207880481d48038031640d80001e100300310003c1c01e1000c00030403580c50500135102403d010503468070380c079000c0e68a41c050005040944214440303105101468020b1100980c005040c005242d210b900007690000f407a541507800f4013151012050014941c0400303040c8901c825520b0181582c40c046001e8248505504150459001000103040c0189041035490440307600203510030001061404413401c0d10b820303e4440c4000b4100005205e0071482c107801070b501454003202c2204080c071014040004071410040001c145480540c4200003602d89640a414a06140d070b08910009402e4400380103414100e40140720200d950f0f00103844030410402c00310380075120155290b403901c00c158001810300c94412240518002d0141040c00b001e600c01c0c08110421607204400080f4094a460083d000e50494002d034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 583630737 1250 583629487 583629493
    0x6030b040e19022803060e030910031b0203130b031e0103060b0a0506030f04061a15211b0f04030209150f0d0f0b070c0206030a060312050f1c060f0f08 66
    0xc14486104d801c00610760f03c0c01032041c0700c42d95280d03551b08805000020000c0c6464042030207004800d459105c00d8006458841d0780000342800500707580710740d41c0402e800b400b04541c0b0a20580d00d10b00703071041d640c5058603204000f440c0c80f0b40c0e90b008a50450a0010700390501908841c0000040000c40e40091b01039102c122150340700b141e155000d00106010844602200c0100c0c203010070b000c05c4a591180a1981e0200001d03014071040c0804a14284c104800030001a1000200303054506032800d9090644421035a20f10054280407021903c008240e00007800140340000b103403510484010111401968041d120900c0d61920055180c201e4002c0c0c02868003d010184c06c0041a2078822403420f41164080f00c0c22076038000b151120081c10314020706c14810b021414900f0310250703450704099072080c00808004245d260852a00d4201c541500b03200d5418010140702401043e480c1c0415207040340c0c01410044543c101c101c036214040c2c607081d441a4842014803a001c10f1a0010034040b000380d40c0c0c1c010407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 583631987 1250 583630737 583630759
    0x40b0301061b150902121e0105090114150604031703100803030c0a1d1206150307030809120114010b1305061e210a0212070e0a06030b040e1902 63
    0x1c00b400d50140d02c100500359a8809281000000396603c010800c0d030000e000400103440080d0110b103400c24040d568698151010b02c2d805864609000f03c0d075014444100901582484802c52105090050818562045001c1151800d034803190700f503900641d0090201c0e1025540c140c0d503541140c0c402c0d00c0c03040d8614084032020400340e6000080341d02039051224200e20304411701004407030000c0200d0125021a48100703000c0010303030764240c1c10164651660041d0555007018065040340422600c0c007103010b50440380041010442c00002d896800400342c50107040647c401e00c90324010041107601c600401524000810a070340018040c0018800b41c00c1051442629041044003d024840d0720010b580880701d503444001c0017140182820741400b1081c1440e4480c449000c0012880071074010f2100b03580416003454013149803501d1500106103003005000c1742e0180011031241052802040149503c900b000d10003030f201c2c1e0788005040c0c00810182d4081c3d041c41d500d0b41010080c1000c0aa100f1086040e03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 583633093 1106 583631987 583632017
    0x10e10022401060903030c0203010906090c2907080c12160b060f010c11031f050a0c1107060318020d0c0e160c0b090f03040b030106 58
    0x150910700c10403554104074401540680480e03051880040003829005045981502e8041c54100b00390206400032901421136104024001c03842c2c81c4181e0f00b8001428101c4042e46d00e0700000ea142c22009480c020740000c1c0c0f0703250004100800300802c0b40003604c0301008048400200080d6140b580c1084e011402a42024802c04d6461007210400c004100c100c40c03034640e04c40801c44051f6512442c00d000288100d848040c010620045801d01e82c0e030031341d02007040807022015900e050051501001c081d001130314040d0b0303d8502040c01d1018801c0346c01d00a900d5800806080c80042c0380103807820034114090908c84582d00c0410800ca100100035840e1801901e07130b0070f070040c009542c110f0300d010450501c01c50010a00e080c002944402c019860b5840045c0c1008107070090741c1c4001039200d107088181800e01202030380d01c8034400041e0000c3d403082a40007071412206507458842410f40007031 = true := by decide +kernel

theorem cover : BRFrame.Cov 583453237 583633093 := by
  have h0 := BRFrame.cov_init 583453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 583453237 ≤ n) (h2 : n < 583633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
