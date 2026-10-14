-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0443
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:50:36.916585+00:00
-- url     : https://prove2.me/submissions/06aab60c-db1e-490e-9323-bf2883d1b1cc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 79496404 ≤ n < 79676260 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 79497654 1250 79496404 79496407
    0x90c02032203030e040c0c0201032a0203070209100605030c070501020d050705030609070302090112020d06080604031d03060103150b03070e1905010b03090c011407050607052a0d2003 80
    0xc0c0348071107800ca1a07040380d009031520b075506030141d0140000e541b41001c0040200d0741d4100d41c5001035100e507204080f5081000781c00e402481201c00d4601035400300b1144840103034404910324056103806800b842c0c008695145400d0141d28281c80074065000c0204464a41c8402090315070a00500790104ca52201075440100700f0340c905168054015001514035031300400384080007413107640c003d01c21141103010503120901100700c1040303600e02a61080c1c4031031641079200c0500058010b010000503010b148242c0f204030004a41d0100f0502c04480140564425440b000c0104003140721580050f140011590000c5039909000b00441e00e092516070052803400c0340c041c10840e00d00d07102061120b2804501e141449141d80e540c030403015501080d00c034000c0c80d0f0030102006559601170f000d1034041181000c0303c03030300342405a1544c034201501203800307401088000507000b540b00203000b0b882401010003201144400340300b4950a648426074a80c1c1424000c039000a620340c48803425030090106015011039 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 79498904 1250 79497654 79497697
    0xc0111010207061404140c031f0b04181412040303081e0a0606020d02010207020f0d05120720010f0f030506062b05180a0f030327151401090c0203 64
    0x100d80000b04440551b10886226000d0384005008036080150030001002810a29004500240c045440d1003940317a0460b96201000348948480c0294190b10900801e48a101c00352400c0031284105054001c00031600400e40000800d0307039050556068a800d8a0402e038690750f034001d400d892183d220000540a01400e04012082c403064001c0b07400d4030095820344120458aa006a003030303006080000b503000f044078190f2103040c14040c4050010034010700860b0490130040b4007081c080e41c050401a901104075180c000f0404c00d51000a01c100c2100b842c0c107143c5016000801807420200c4280f5104043d1540d01141072a0340706400e403048680c100400fa210340c08441c03540140c61900d4070b10799001d0b60901c00040c4501075040003030440b01c0890b030041c00100c00160b88100c5c241514000c22810706542d41e42e658130300c84988003800c81900b4440088440c070100e900b020316262900e80c0d030901ca064100940129511920102355044413101e01e40801d244070088000d9081d8001c0840c01202041c04d140d41 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 79500154 1250 79498904 79498931
    0x31603050403320f190303060f06030b0301110309060f040c08030d0203010906050306040201090b03040c24021c02032b110a030501050105090d121206080d02060c070201020c011101020706 82
    0xa684860350103a04401621003035850344c80c0e60900a02005580103500203510404802d00502e828038800c2c81c000820325104c5000450044003074022500180da14501c40c040b174102489040c0c0342010b40d02c0722134110f00d0140c14060751804000c1401d0b040c3c00420b00401c01300540300085502a20901090b00d4032100a0b0005600a41091140c1d82a403030408000058a05020407928001c03a01a510291081d0500c640951a540080c01c01c0b180411601d400041c030405038039850006d40c00c0703c0107020a45200120003490700c4072989121540b141240c00c40110300390008121480c0021043c81c910f407203010702d880040e00407040048141d150b4202881c010101c1007081c000c241c0d50955480070000d0742d0701c0b02c0045445005e0b040d0855000341103604c1000104e0324403041a2000480c5180c0f003000405c0b44080102503034030b00e9210301000e6000b0000a040340e5018014640d1010312500002e003003000980000359030b4405440e82c07034180422183c090102c3c04007074040320b841540060040c482c003910f0468 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 79501404 1250 79500154 79500203
    0xa050702010e09041e0302070f0902070b060108070e0f130906090209070f090b0309100c0f09050114030411120303160f0f0206060108060a05042301120302031603050403 74
    0x500300e0010721040c1500d401c43c070b00b0410043c012604a001c101140402076404040c0200e400b4040c0e05500c142800050070004405180b4090a0140005602c81700149444942c4132805051981441114010405070f1a4405101458164120b07070400c240861070021440c0c84c60001c01140340f0500b00300d1041c1c1030002e1504810500b5209641441042c7d42d203900c00c0300c0b0541c05110300c3c0005103489104003d0114400301568209550703005603403440803401d0415044900e032140110105010015640b0301c01d0300610407200508d000c1c24000c1440024010110b000d1000a20003000301c003030066078942c141c9806400b2010680740400f100d51740d040ca4044041c80143d4603851100040140d121542d03986c0c032441804502d410039800604060b02c0d880d005680c4260028400d0750015144080040ca694a070300504000080445640d10000106c2d01d04180820058201c04c240450060300c0e500080d034004105ca14561150304070203461807103440c00716114803880d03101509208514098812000d000c88 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 79502654 1250 79501404 79501417
    0x2070204230708010b0712030b06070302010c0207060e0d061503080708040306050109140412021204030b01150c0308040602030703200903010c0e2206090c08070207050a0302092404020a05 82
    0x1070350300d10a645401c01280c0c400001d000c0d00e240b0b0341c03051004800068012038060b441191a05001c540850ba540c0403440c00c1d040380401b680140e4492000c0d03241075405001180c042c105074a468282001c6060200b142035610342d400400107a91030310080d0080e5041690b200185502550030356980d112820300300396680060001f0b40e4071034900703400010b4100c001c1c4a07001c40d41c00302c003500702c00d25030340d82e12082c0321410404019804d5004010b406a843d42e070003801000914422050403415504140690600d911407038140000e0010814a4401203600000d0007644964844005a41c81d0b90300c1c0c42c103c02600c00240786014807500b4079181c030704450000010740141d80c4194020000b600341d005d01101c3d03040400d0704884d0015110030140600054050b0070010f062042c500101e04a90784404030790480b5605040c8034000b4840a003400384090f8117009100041c0012103a4404c801d05507000606000d0b005000050b00130a41c1c0303c00c030580e407150b80c4100003007007004004544855181801424540c02103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 79503904 1250 79502654 79502711
    0x50a0b04090501120213020304050a0b2a0a08010e280509160302060301050d030315060806010f021209010f0e03011401052d01080403020a050601080d0305070f0f030b0402070204 78
    0x20b40040744030b0b010081072468054004000700b211182c081e504c4402540058410f80e60fa01031041907101048041c08094014280c106003407240403500904c4035030780749a05181028880c810030140c0c0d0700c035600c00c0c18103054a2001c08000080d0305c50001d50148440e503130f10740c04034a4071a40305110451102c1d5107d14481c13080d0005035001d00088010030340601c42d103404020341c04141807005100301d0400c141200009803013801d0010300342000b4078035007000c0040b0350700803000581200c08001055070307c01072908102040e400100450150740910202034080c2d0161a410001c00ca90515155445454008035051000d00200f02000001c5012009d1240c24002c03540200702804c004c070002c040703518242d03036a00742440011100c00720410045407402d6000d07000750704611a5110400204200303120341d0b8024007201004008005c0b05090180a540d0001c20000a21001282c0f131440039400001158400101d0700d40000c8100d40ea80c0010300038010300d00082d4000c2d140030701c8441d01c40103078179052800c040803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 79505154 1250 79503904 79503911
    0x803070c060c03170702011104080609010b030a0f0b04080417060a05071103030406020f04051807030f0209030c0927030403020301060902090a0902090a0b070503070201120e070e09010204050a0b0409 87
    0x1100710a44480c51192401800036074582c0040e4100c044902d42103400910620000c60000a00481d100701c5400c182c00200c0150011400e01c5441c0c4424840c1015030310042e4007815040a00d0348402c00c002d103001c080036061f080880d00060410034078104940181c14940a0004008885520345075105012207a210102d0f19150108040d0760144120788041040140214699602d50303032060007a41280700c0100ca80341080c00080b8042d5942402640b4080035008040010b20f00a00b0050594600120703201446204114a800d0758030045030040400b442528400a02d880740c4030800440b0800d9481504034480c503c40510246002000900c100c034000c4000740046511621982c0c208d220303052440354000381148081181c55540d401800300100004c01d8140d416039940303000f800035884030008890b0b503000054100115a00301c0e20868034051140400c010151040400d103a4640700c5014021180c8030010001d02118025011030b00a004050041e410f51030b91340e0000c0034181c000e03018092403a400c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 79506404 1250 79505154 79505159
    0x90501020303060d0813031410050105180103030309020d06020a02150903030f0f2a070201170603120708210105030706030b10110109020405040b0105044a06010803070c 74
    0x800010b40f0b004010041400c60035001d16512102c0301d0340070f146100300d450041b0000102183c21207041511210081d03000d441c42c23030705683c8944100c81050b0030451042e80c4c0d807443d000d0040c0c88000113506590749810001076615030b500000394600014680107001500008038414000d81c04600d0346072076050030306031080c0c1d42c440103040da45034081122614100b140b000c0000340011000780d1a903800c850804103681c0100700604409414031707542a0f0a10450200103105070171968450066103078121250521001402c280d00065122140ea002e03440912501203400e40a0003041270481e0460442d280b5580c0900e40e0003010380d50130f4842440303045d21030b0107a0722001409070700030700907801034200003013607080781d000800340580b260800800c20940c259664010000145c6036445010702450240c128007032150715200412007a03035a45408195982c0d00c0841d841c0c58000d103140c201006019401c0208205001c1c404810340110b003110010640c0c0c410003000290094010008000450151032824103458 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 79507654 1250 79506404 79506407
    0x6012f0c030a0f120c060c030501140609090411040e0f0f010e0609060105010507140d020604060c0309050c090a0209060409020c0c010c0201050a031d0109030e030c010806150304080d0516090501 85
    0x40c01e0035000f4003920f50a002040010b80d4040700b100d01d800050074070101c2c49000d525190225003070500c000d00440d580340c0c0180300c0307000300c088603440b445011984a4580700780304020a0b11030401810041880d4a5a602c26600c1e6480d5009543e0740f18150040391061031003804055030303481000655510a51a0001c00b801c281000b00b00184260428401482580d02e401c00460f00c50340f2040090715072034040034a111441000f4440200c82c448154018041414142401c9088800b40440384041c54541507580001400c0031036441a008012101201c442d6210070311a40a8840c4043e00d513405400014040b44580071075002d00190101441203600d00d03007800005540c000b01101019010800512803104598400c1c0c00152043c00001907108180014628003800d40e540b2001c00c0b40441c120f01c4000748541401c01911520010134a03040e065414100003242c0441104e00c54925140341c0000003500340240380c02100d101010440c01085503140c400c0042d004261180d07000f40010345040800180356 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 79508904 1250 79507654 79507663
    0x150509030d090308151507080703050d0501030b090705120d030203090307050303010b07060b03030301182a020c01021006060507031107080d090e0a09030518150c031b010207030903020906012f0c03 86
    0x261b03504501c80340340001c0c94850410b00c0e04610b030308804010040102544c40b8003140074160080d8442c4440c41d8880c00c02a85080c10079505802090080101e1034085104010000d0707418514040350a00603a46e450b4420f00c2802c505c42d008001d80248000000000d00b03420b00001820303414010b007010031000880c4010180ca80c402885140300c00a41541e0b10210311002c0e6100e060702100040c2c1c021404030744a2020a0003582928400000d42c21213408801c0b00d58050010034110014000c0c1040b10504044000d0454024801c000c0d0800000200c0103c080c00104606005030000b14106c600043c040c0300001c0007501107021304500048801d0110300c03440c3c10340c0100c0100301c2c0d1545030107007000e51980d640003618140840746540851b04050030700c15540410010320202044802035580c4152903103103044a4018a08048801d070320411180012030382c44905078013666411100f90381140c5803480100c2c1d50b841420340508040f925000e10300020365030f001004410b1581d0500b900c01d603035003c1040549a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 79510154 1250 79508904 79508929
    0x40303020d0f050c01060e1501030501080d050a02031c05150306060307140a0521010c2607030b10030b010e180103080901020a1a10050d150509030d09030815 69
    0x564040040c0d800303914028900310550000b203160107414075a0f048440c41c2074a200c2c0c0e010b80645042003040c420020401d00500d5823618080c2000d0040d540340030800c1c0c0d9100c8200e131a9500b0040c02007202881d46100303004403400c842c0040d600b4003400000103018001043c043e140e50303c22010640581c0c401e8103012440ca44075100c001c01500740705d45802c186c00060304c5074240060b4400d5060a020805554014000d00c100501c90514403400040030402402c46090468120910a040c0e00a41c001d210600800c01d551300c91015012040c0c844501c11f40c040c04060700c1c0585d10a404945030030a80e41d041c0e20820341c2c10026038405850425042c28084060281560091b500e6040e13170040c0081104c0000070450b801c010720480d041c803c1ca81d2203c52106200300c0558510301c1c0c4801c2413140348003103070400300d010b003204880c00c2400c0d0f00319550b603620384881d01d61650404e513220400280e00010034030581e01030360440001407004948920b001480d610040b40c2080b0602c43c20b0012203414100a0b948100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 79511404 1250 79510154 79510157
    0x5040e030306120304090e0307021305041e020402090a03050606130e0304061103220f09020406050313020d0c0605070605010e01141504030c140f030c010801060c08040909120f05040303 81
    0xc0c5032268000d0041d007401203111085184405c110004803980703e48144551051120017442d20380040d0b104000114440f00c4520802d82e0034041270001140300d000c190800c0d159801c2e250442c10031544003080c0a8021302401c15400300000800000f4484007180d0b0038031900080300c408e003881000582000483d400d0040074641580103201c207002c164021041d511103819840c08580c2400c8006102e041c405000c440015600001d001080200503e07506d81d800c0540700d400d1095052500f483c40041060000400180c03c405086880000f5512483e81d05029030707030021001c0d00001c0e102c88010703141d94008242245e2040c80c101c0001110200098194181c488018003c80d294081c02c08101d004250070003101010002004004005492480404010b00030020101c03080c1d0f4841080182e04990030801601030b0f08174846d02011b1741c5e80442c2d00390550b40b8904003042c04d0582400d11030040d0060760040e110440c9000b12020a11007028012581d0100075038985d001c0c0e031000241100c036402203120040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 79512654 1250 79511404 79511407
    0x10f080606091501050a030e01151503050105060904050402180702160f0503070b0f0c0619060b031003082508030108070602030406080a021803010906050a181e0219060908060105040e03 81
    0xf0407962060b030040c0240a01d82ca4041240d101c105161821200c80c030703c1d001005200d0101c1000340100e03105084504401e641010480c544c1340c071b0040340d114480c00d0456032195a880380010215501c0800004001103500c03000c2c1c1d624501400c01039998808204c074075040740111000043c08100004000c0c09aa1014001c0c002642c40c0500b010301c503420965005040d0a01400200c1c0343d000b08004441c405c4150352010070300044a1000c00c000c58003590070982c001d0754204204550540302d01410011254000d005036a641c45816403003203c98401c41c580242154211850010700c01a81c010714140c444036030640d0081c0b03588d41c80599582c440e41c482c003004130b400c080000340e10b80450b074050709050302d034281c0c020b0040c0b148000190031160000c0e0100d0300540d440c8244030700f80b41c0910441e003c4030f00c0700c90341c2660b02c0013a803a0a400400c5142c0d216107060240901c01c811034403000d0b503d00d2002c040a10080c2015103e20002c0c202c03203010f02030500d40c5d01c9085d00004a41c50540903002c211500c032006036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 79513904 1250 79512654 79512691
    0x1020a020c04050a1b05040306110c060718050307090915050702060c09030a080f070308060a2303071a0403052a010818070f1701020a0f0c030c0b010f08060609 70
    0x400500f030002c000134009540d0b45440d0742c10b02d01d500b1030303040200d0b410b41e142075031103040d850004100d581119890784100c400f84011000b9032400500107402c50800c5c2010711240c10302c45610240390300c4603000b60350180941d1000007641940f41d00005003c91003100d034000c080c41d044213404d0494008071a0200143d101c034001c680d040c03e41030028a01d100c00982070310140366098550740030952243c500406281400108001031603404081e10b41c10071000c44080c14103d02d0410b00140000b0700222014050700d0900722011039640030040130340107000010400000410440503084a5001444140d805014071440c004200300d0009080001c070704154910174445029500440e0460f0004000c8103095034101e06058500c803080245000500d8070044a8003518105448001850701c1c100c0003400a0f0700510040710060f8005500c503950480c2c5250018080b11a4202116101d40c00d0901500d0105c040e800800c6690440361081c00f558000d10483d056915000103000c2007400803506809680440b5020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 79515154 1250 79513904 79513909
    0xe130e010902030c0d110d170304030f120902010f030c030f050c130614030f06060714010e1b131806110301060801062613020405130c08070b09040906020d1b1101020a020c 75
    0x20b60387d24043c0880c0c0ba0340120b191401720043e0b000303440035000f09201d2100680d6095111400180144210030148080301060740003074030390000700c0000c4003030645606039080124400e601181100f00c41e00d8060040d400c12541d80d40c4030741d00c40e042d00c005044000e04041607003401841c82504407a21078407000d1071603440c900300b90303508907001c1c2040741c1c8035030200994001710304004c41904161501070000110140c0c23070000c1e180380c0425525501910071803d01465005c0e520707000800c26148210b24082902011101035605506507081300509040c03030004108101160003010710b043c0c42450319000c1699807116801d0f078482c04002c00b400c040c41c41d861810204071080c880700542081c0510802c1c420101917500240540b14100e94052528070b500c02e00c0700901907021842e50041900201a14201d400c02000b0012441028000d9000e2038840800100308462541119802e280f00c0c041000150000c4603001c01460308810042c00003104650700c0e0105100600c226200b528440c2c00501381c40030710303405 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 79516404 1250 79515154 79515169
    0x906090b040909020f0316080606010c050a080c010e06040b010806010e0112020f0a0b04090b0906010804020a230a060e130209011704150204060807020f1902010e130e010902030c0d11 80
    0x40481c5c00800c1c0144e420b009443c02c01805180c4480080181001400d10440c50300d0201e0003000e041c10480660b61510100304041030904020f9000050150b460494100c100d000d01b82c41f4102d440284942c404020903c030300310540e0340c10f9800c504140d1300240d071317540e450204c01e0400380500516014603d1a58006150480e200440144003815141c40381d6516034101841e60015803040b4400c640f200ba2a00c03a40c9401c15015500c40402d081000c080d003056004900740c131170a8010400e074007808494103000540d039601c82465140e801052044aa0340b503c2c401448008104105401600c00c0070207280c1c014400d00a8034800c84060f9a10b162400e02c440341e403100c200010b0025031f030b4280500305003020680c15000400c0a4140d175181d541150401e05c0b802450410358201e420300640105180060351180d41061f512100e03024601040e0b64442e40001603685043e48100882480c6018a21003189c00107400850360280200c0c01c0d1500c0b0f194000c240f01903000c04c03a8000b4036040070030981612038a407000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 79517654 1250 79516404 79516421
    0x620121603110109022d061314030625121506081303020303070e0a0506040803030415090c0302060a030e06070f121e0504050a1a221106210112030906090b0409 70
    0x4000d80e81d0b0101a80c0851f1b60f9500409051603e44234070007081c44082e521200705032044000782c008281c18580313031071025a03000b126512114400040c8010a40300c500c0384e031040c1241041c0034020090303007500203004020300d1554440c0901141d002e0000808a04e43c40f5003840c40c49425401075851a550601c0172a5410081d1911a61103400003901280b5511803102800207403000f0320045540c7e00f0f060038031440c420100507001c0001e40c1040201e40005042484260850f0307415903481c1e84488000c0c0d03040c0c01402500300c4058881c464201000301c0d450f448007882c1030500c070b50b441d21110300c0d05540001060301d01c10b0400382e1a41d00405214180c40150b0b50006a0050050003651038100d80b60703985501041c5115a080c22000aa42c00d10111603150243c40d80741417104c0d5001d0701004101c1d540d6404451a9030b01180c46001e02160b038595541419100702c1c105900000d050391507607114030400100c040d41d85030070350000314040c0d0046001400381d00c90304151a90410300605240c50000705a0250a040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 79518904 1250 79517654 79517719
    0x18021002150a0218060408190809040f0504020405010801020906030f0c040e0106020102041e030f0b04020604320105030f010e1308121b04062012160311010902 70
    0x510480340828041c2841d000d851215405030b6901140d080408810711100031941c45103404100410110200003a5548444000100c144420343c1600700344809018a1103015001810024029800030f090742c4032a200340d200b26020000c42c0d0b01c81c0040d600301d02138020819002070080000c01c2641c104000d0b482c1d4800c8800d402c03541341a071910854059200c0031790002c00580c1d004501071241d0001d1254049000b616484001800307807841e01c685102c0f0750014030103407140d510800840c003552034002c21140a4400450380e8442490080c0050458288030502d0303074210307540307041c0500a541c0b01d001140d001d0f441840040071144d090402c45040100090304800d608010b002d28000000c91610140481a07030030f0b560001d161a20f1440c07001004038030305420650341c40800007480056044460141c0a40300340c1c10318000c0740c4005a94600d401c65001d00503805140c04102d08654255618641d0459880380d55a220700da10803490044c26103804410003940a1407001000c4503c0702010103100f11102d11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 79520154 1250 79518904 79518913
    0xf0e0402041107080d111201031401111803070e101a0d1503110919020a090b0301030501090c080a0506010302012601140411030c07031b060c0c020901080118021002 72
    0x380010b03080360764000007040703c20a2021502c20340041d07451060300301d18051110b40c2d03440c1052039109002c0034801400020000e8a8000c0001d511100942c019507106d901d1164843c2d45054102421404408012003144030b0f204520b4046a40b40300e503110b01d40101070300c00440851a05150609280d000c40450f4013402c00c5003807100c099009002d0003261030705042800410026810b50170b010365250107070881e040c0941d19410a00c203035032944000c0c0d4142540548130040e00d5170030b112340031241c221361540a14840d49000c0004024024198051242148140e4940788000d41d01c0d092039407500e00d10030004c0d0560b0082401080554090030340c00030b22000c0b801044002c1c80702c04440012541003a00002c034551110b00210a05007810b20814500c280344d106128210324094002c2e52841c800c0f40300c000c040114000c9164600811000e00d0800d540d80000280803141c203d000003031214900300c40030f910500c586400007607009010310404d00050b00e01100c1102c200c1c495000c4c00741e81074154804e842180304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 79521404 1250 79520154 79520171
    0x3030a110a0b0103080a0906020303091b0a0b070813050a27060306020a0207030b13050c060d0905060a1b0809030a030905031b1c08071e0207090504030302120a05010f0e040204 77
    0x114060036020b917225100c455181c249041009104000c0b80d00700c601590f02c10018400503003c001122024284620034a9207244040f102203100010a5030104801000220f040000c10240d100030b810015808281103038903a03a038100300716080680d8421300340e05028400151507150802080100c0c2c90480003c0442c0d00c65603692182d040b80e000c401a00d0041c0c100c1501442000300380585140c2010300440f0b40e1286540680b12191514084031106226000006885000044d5a007115001071f80000540d02185400c41e0840d000c0d24080c005084150043c101124400b8040d101040c0a00701e048000c0d41400b00c00d00c0203170000c05481b00161000d00c018440e805040c448041c51548608490002d0302414000b415040300080741d0550220a020750329007003200e40c2e035014a91115a00e40d40b9110942102ca03e601a41000e9a58000700861400c000400c4189a0160028040d40a402503190f406a0300d825180341210b400703000704440c4012440007004000c2200701c14541141c00108001103050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 79522654 1250 79521404 79521413
    0x70209150105040f120506070302181e03060103050a0302061b040605030a06091509180201051e070b010b0a0f090e0a020714030301030b011508060f0904061b120606020a0203030a110a 80
    0x58150317010f204200301c0e6072100310422a040c070a00c0d8005c0520b041c01e50030f15017004800c2181c40180c0400303078000d040c00f40d1070075099060007204400c506000350540703020b075031241440344c1c0b10401d280c020340161048501084035a9400f5000c1c000c103016002e43d90b814982028003c40300d0754800303400c091280d519604003040d074421901c82c80d030000c94114284220703545000c80e884190b036400d07281c10740c0d00c048224900e40541d03040002c40d0784c01c030303881c0042c10000c04651320320020314060040c0250990380102d001140a08004000782640303403090700c50030f20004410303104a400702075602502c151101d2080110f02c401d0b101d60007a2440c07502c21070032100340c00c0e86200c800d861070b082640143c1e80c20010200400140401d8180e8074003003491032620b0000c602d42040854800d18001d6540390040200c1e00014003400102c1e880295004140c0c040c0c6201040310400c000e00b0030310905191900e5500d0000000340032400011040c10041e80640510306101c1881029180c60907001044900d9001e00a005c60008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 79523904 1250 79522654 79522679
    0x4050a06181a01060f090807060c020117190b030625140c0703062306061c0f0e06090a05070b180901120c0e010e0a09031b0606050405090307020915010504 68
    0xa02c07480c041c00c1d0566240c00700003800c030700103003400308240112a00180300403035020a030481640c0b201d0030f1598103840148012212400806010300c40c1d01e001800740f00c9292001c0000c13004240b0052000c1c4040e04900702059102c01080e01ca00a0294003072600c2c82072244582c1c403075099000a4140248440d41103c0007103280c1d0b11054080015420120b000c1c81040403070f20904030700d41c281c804200c11114001c00d90f0b0000c42e6001d0701081c414030010070b00108a00400401508040104405004144182564001400d81c80d820282d00d40038000005042c41340004501c0903040e000300c006c0c41c83e81c0c5040110700f015444003117043e21100c140b8001e41401c0e110254a140204030000c0c04c0b041c28029410808281e0446400114000410000403c040b1010742444e5800800507000010000814901901d01e010101d001441802d2039903620800c1c043d403a8804411220241c40501c6540d84410800f9243e01c560782c00254018101ca021449165002849001081041c1000d5140644803455224030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 79525154 1250 79523904 79523933
    0x403140c0705031002070503040b030603011b03140a0b06070206031510080a060e010506030105061605011805010b030c060304030516210f0309080901030902010306170607140304050a0618 82
    0x1540311850401060404101d01c4074040040e0344c0450800b0500d61310240c0f00e20607813180350f045640c0840450b0080e5800c0d8401b0410351645520f4100e801c00c0144041c000e0030542c04441000598070b0000340c600601c0313000d030000300003001b085a403410b00254200481307500090030000c0f0346955000003819907100c100e04002401c1d060303100e4500c5844c141e580841610250303084040182c80031300042019807500e20a803410348804132082500d0701440001c4801d9482c2c440707405010756080c031041081504070390244e00400e43c0501e009200c0b4650700000e0542e80c60345094000d40110f02040040c010910640141000d07a1400d50303070f801240c200c0c0c0c0740d007010100c0e00303900c1303294100d03011381424205600007100e00c049441d1400c0903c10000c46403180021070141d284642d05041c1c84a0b00e807811a03100c1d07440f02000c0d20b0844c07020b600e960309001286944c0d003c11a0400c010400b0403146913014100e40341500c0c813540e4000001d0614001607560170001c3c103e02d5104100340408206260009032501180120 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 79526404 1250 79525154 79525177
    0x6020c0102040503100903140d090615150503130b040203031201060e010806090f0105060d020412140f071404021605010e0c091501050318030403020a0b030a0606031a09040314 77
    0x88540c2040200345c00c048140e442807900c2c40c908584803001917003002c00005120403041c0850349030001d42c58000042d04014000500607407400c0b0300145010680300201c415286581c120ba501d4103000c160036503881c03200795020300441040c1e840210008184910840e4030074030160a032414141c250140b814941e42c2a044080810501c0c14040d0095034402851980300c0011220441c080c10100c00e4145404010b0190501548000803522124145601280d00070240c0c01c1501ca8442201e06114030380c044062020312003070041c072401302484400058008107441000b120446980f4010080100a5002da91071340e14030b04904011b1b80c00b04000707105403100b060b81135000e0107804075180204a002e03900244000c0b82007150034040603550744d002003905d5200520311001c9643c001c031448030b60300d5030082c0d900003544603807030307041c041107904a10001c0c5000d000c862005002150f02c038001542602c044045106400c4507070f1451a0140c50116225134009000303003040d02914212003140080c99001100514 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 79527654 1250 79526404 79526407
    0x90b0711060d021e16030315120b04020a0b0306130903030f050c0702030c090c070609020a082b0e1018050a0f06080c070323130311010305070e100f0c06020c0102 71
    0x4c00e202524111410b0125103a0507981c50f00400080301120310340c5410001e41010303590b0006420215840140b4806015903050010f40c1090300e01d08490604000c42c0d040f400b5041081c000590302540c402601c0c09110010055400c90544200f00c03001448044410707006c154036144078540d4011181b05082c00f400d0104d0209903103889600505107003003041030055002e0362000d820403003d042c02001361510780e035001c80045001500d90001038081415600195441c1c022502901c100401400040d001d441d18480203107001c0c020003c042d50004110000542c00210040341d0301161842008403601c1c001c04091046161615a008202c00500c503812134005501902030038480940c100c001c103580701c0c00001c1c80b01c1ca4401965002084c202048884290340802d0985081c25071100c8403c3e1060f0220700ca000d400310036920f040190380d0b99454100300b404079207480080b0743c241d80700315181462141c025003051003610f07800744100e0f01f203280551000c042008204038180003c02030300042403088200d00025 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 79528904 1250 79527654 79527667
    0x12070e0f090106020309121606030222080607120f0903020c030f0105010b0405040203040201110111030a1d1e03040b04080303040c0f0e040f02060f0c070f05010906090b0711060d02 79
    0x9036080c090031003103200310038000041001c50742c00030464000034402c0d6400810460340800702807819407a00b416a041554148002c10440e5159001d070641d111107020b2144090210040c00012490034090341500d0341140c0c00141c0c00c180200d00641008290200c0000d070b100c02d0009440031100600011401600034640305450342c6401c0010701280315182000700455454160300c41f01078400d5108403400381c1c1e001300000b425a03020b0002c1c502080001c03030003880384007840114042564400c88000103414a04945504c400b15001e800c9044980b8180081c0840031074007182100362020300707905020911080001242d015929000f0380300400140000316181e007824541160044820f03000b802e0b40c06d001907001c02151145050058000da0420442c101c0c80c5114004034600b44900f5050714a110800074154018075000908102120001e561809505407506c0046a42c06110b1080c400099100402030159202c280010034120b8070902c0c0c0c120fa800b4803000403e83c1504820042c021290380442c44 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 79530154 1250 79528904 79528909
    0x3060609031603062702040b040e0703061514010f0804060b0604170606030f10021c060806090d020c060a03050c040321020d090308030720010e030405030c0901060c030f0512070e 78
    0x15000b11201000802d105d803c0c1c070705603000e00d0406405010b417146864010a11681e20359a10031000001c20109590496490342071040180c4540e2170100000315090100055082c904040b802254074140d450017910620a0030403581040c0c0a4000d841d000d0741c55254041c29a554401000103021540c40d42d0100f85041e22000d082c04001001d21b4017a03003090914500c1484089810f03007100c8021640183c550220300d08203811100640d1451281c91300d804408109030b00001990382c800c5049108131520395480c0f440c126125640d5000e160782051081c0142081c0c41e00075004250300103a440609414180e8036100c480d811070510209656a01c00388004400040d030500c072008a0242c9400c0c800340e003e00c0e5542d090031911006029604200315005e00191220305010f400c01d0710001702009000c0040b101018079101e41c00391082c035209100e060300340d0307406040c85103069041310302c151a100c0c49124a910103a0381050824659000c102081003035400c0d900c80d00038054020380050b03a600105104500a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 79531404 1250 79530154 79530161
    0x20732040e0114090111190201020d150311010c020109091806020d0b1203090a0e0703020d09080d0b010e060d0203071701030b1504200c10050103320a03050306060903160306 76
    0x401e044c50f410300003609110a100e40c112424040c407090100f42440203c0c03c204e00a000e205100c0030610b040c01100c01660681d0040300069030b0007000802002c6a090740151801c281d214402030126050003c02c000c0c1000d980d200b064172080840d9411220009580c0700300490b800000d200b900d096555500c7d0740300c0d0400e01c08030842110800011480c141c0503000058804c01d01340f24656502d5122070008003041c1c86038054805000c1400300c01d00418105140c03a00c0c06801520700951040e1034501c00f40003d41c4516104a691034004e4031051424001c40072071070281d8402801f001c1444008140b505186020005150017180104403801d0b05044c01000740804107403540e00548107a080c5002003c4290312075482c4080c0ca20080b9a0075070714441c09003010306000b84400100051890000000240320075640c615480504640100c501c085074140030f03840d4115034148400555100944600020340628002c6030041002408182003092643c0003c0c83c1c01141100b02c1e40c4601440741c10000c000c0c02e0700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 79532654 1250 79531404 79531411
    0x219020a030203031f080f1b0604050a050d03141b010c030507172208030a05010503030406020a0b06010e0d0302030a020d0801060f2001050709060f020732040e0114 72
    0x2024040c600196100250340b800040d041e01c0e080040c82c68204407050100d0040f00003400c0c21001e85000f582c05009031512800b011070000000c14030002030007128900340d02228280d44e401083c02c09524100024040f110340441b600303c041c410b012040661460480020f8000c1540401c0e00b01c4000e803944241e0b0342912543d41502003814189414800070503000507840070041d0940a4840c0c0c644e490541c610361001a840c1030300c200c00d150980600500005500952080400420a0145990f284181035403446207214000058201e14050b8000558195205410000515007902190300c1d600c0081c0c030b500b100c0710080b000350384005000c5244070340500c0801050525403c201c00a585006005400116000d010307004200315070001010400071680014a03401144008014601d0145009003282c40300e40030f1400899401540c41040e5031002403414141c035100c13203403101c0d0101001c143d2410403075011400140300d01031070301c5141c683d101da08c13881c2c11004e03d5500201e09159000854400c004028 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 79533904 1250 79532654 79532657
    0x308070c09020a0e060304060b060a09030b06062b0209060d06060201051e060d0501110c061e04030e0108090c030a2603090a141507020705041d06040602130902030a0219 74
    0x41c0883c03055140c0100a0311107003031041d10540d60703a40e12407030194000c0115452181d880800800e0f451005a031145501c020f60388034840e00c4640b074070f40c2c800700442801040c44001c0da004603248002856100f40701950419000d0000240c2001c01c450300162050b000721b45600c3c0601c1c7c1d034000400c500c90b824050140c10440c3e0b0510310750291800310342c03408048002000c41e03000394000041c1c54100300c1c00b58082c41402c6005261141c0310b1940d0320006d40c0303c440989500d03014150031039a6a517441d811000090003194107480c0c554031a0b5480d00107680b2408010300d06010390082c107080202c0c9440034032020f159180b0a803694010140da02d4055050407507044007183ca03e04080c420040d9142000409031505a008407000030400c440913120752410941c01c1e03801c0b41d59100c0f070046c0301c0815000221842903900c116024400d407085600c020718070142406404649134010000700f00441c20744e6006000b0191144001c07241161500d90410a0768429140c003400564000f94140300000c201400c40c1320300425 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 79535154 1250 79533904 79533907
    0x3071209021f0504050402031f06170a180503120a0606020c0105090904060e0d08071205040f02010c0303060918050d0206070903110301180312050906060607030309080d0203010308070c0902 83
    0x64020982100007800140420b0300380484410915000d40141c80060074000c0c0190340e20314040c0c1c5858580c500411600b125013114035004241c0c5800b407992241d030602d02c0000c01e0034554403040381102402818095541d20014085c003440894010310080c1881503c02c144079529080500c1780d40111080382c0e11400031500000080c4c010b980e402002c40316260402c9030305019640f07940c1000d07001080b00d0b40310110544a10350b05542103940055072070b03104904645030041210203402000082d100101c8005280b454890000e9005602820101d943d080c081d10340003800503290743c52502200c200100ca03610f94009940180100481003200c082100417500c085d10107800c0804000c3c04604d8035001c01001491038200076440c544003503111000490b111600c10400c48001e0501400035001051100e0100342458009070f90540f0020b0700e2070040901601151500c400c2e52000c9004089680c2d00710b0b03205ca0200440c504e4140d86001841c0a540500511030f82c07aa02d030310340203030024910f03409803125500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 79536404 1250 79535154 79535171
    0x207050a05060714010e01181a010f061b080a090e0604060806010b181305061905030c01110a1a070206150105030c0a0c0b0c03060310140a090302071a030712 69
    0x11401d0075161050b50144002c004138004103130f000e0140c1060b9201c80d000398a007010845076a10b20182c0d15031024010600d01c141c501208880031350608003401032503060003401408201e02da00c200500803204000c0b12004003100345030b41e199900b5a000c40750810010b04615000d0041c1080c42030382c940c101e10100d50401c861880d0050b026242d0b0014441c14001e44408502d04048000d40d08001030660f0300103280c440d25440d4854818001d040c1036801c80d00071000040b51000d04000c202c201029920014014000e00d0fa00500442d08202064280149070098562140c005025101d10b5810302035039148000441c58a50340007894071400034030481c42c2802c92404500180d1304a000c403a0010b00148a182e0384111920003901e0b0004061401410545940300300700c3c18480c11302c040d60092108a0075907501c0784c4200042c2069031880c0020b5202c02400c100442d403981581d034401c00049200e401501e1001ba5a040c503140b04030030040c0100440c513000410880c441e0342c00b007021160340c0c010f030504101d07141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 79537654 1250 79536404 79536409
    0x30604110103050903131d0a1a04200415021203070807080a0207140705030106050312091c050f0a020103050604050405060412050408100204082413020402040302041406010207050a05 80
    0x10011a0506155448003c5113a05500f401104c0004200c814521401950780c4400b4001900c0944c14002c0065040c0229545500c1805140b4100008000c0b1403407800d001c1e402c200042c075103100384a26007407661060344984c909000c007030320081141c40c0c07003412100032000029040043c480d074007e044480810800040351781000010350001503926120301640d540400c010004d1043c550081d00762585124011300b5881c2c005246829648250001e0004039610418150b4880c00140400703950102400043d1180c02c1412040b6211426a101d402580265448140c280208a040d00c0301c560403c0d0441e40c190358050141940260054408200500d02034403001e0b25044003030001000d541d10315404034040c0b842042543e026043c040c058880d04a210780180e4000d61142c42542c07414000c14462103040202c07800c21784100c4900740000d03940c564401401a2403082d0f0910100c4e406036080c4008000342c0c5480c41000401c00380380c040e1102da42041c0b0006403801d002e07a4000381c895007480c6820710007034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 79538904 1250 79537654 79537673
    0x110904140603060703050705070606170c0411090405040f0c121103030307080106110a060608030a0908060106020307020d050118060b0405060d11040e0118030c0b01080304050109030807030c0f0b070905030604 91
    0x130035038078001443d91034007001152640300c0d06070064038150800d080416035102d41030500400300a510100c03101001c500d0248800e44000003020b040340346c014007500409040076081164040d203c3c2d82e40721507200803a51590900d1021b074108807590108007010758204034100c0581444040c01700d000f1404c0d440c01701402000403005008000800010804500031802c1c108041031520754460001c3c86a40e49030b4202e2036807500b00c0c000f250b0005280c0040007a482e080030404e1416506583d0203035160110980a03c213a80e06000801c481c1e40d961419a000402031406090345250320498010171181d4846080005807080540b401c1d10030350424092600040114203801c60b800700a4030b012031404014000c450050039040c10000e00360b002c01c4c1c00f400c10107600c00c2e00c1c155090321070381c4100d00f42d03600c4e205400e41e6405140100340c00320741c00840902c0460f90310320151926034031915045105c88001c0d554114241d002d41011205054040700307006500780c0000f17121016013800d40040c5114038090701c07540c013003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 79540154 1250 79538904 79538911
    0xf09080303010306020708070b040809040b0a031a061207060e010e12071e05030613020315040b0106051c0c020d02061509060f01021c020a061103040f06050604020d11090414060306 79
    0x101e0785d00041c46403c0100106c10390320640e800c62801c001c81d140906012401e540b08640a40c400c070700c0d290501c0c05a01c0e10340100c6040e240c01041c03807121804c1c4068204441380c005405140c0c0b0078001300c03103000c90132130400240c000f030185540c07038288042c11500098801c3c40c10354600340c071400e130042103426181d400040e020b0032a00d4078520000e101c030135800b862007050b0712a00030700e4140c0140020051080d20b03d0002d40e40c154401d40840c1e080700000b001c0080c00c100240c40c01022100b104004104c1d0520420140c00c0400d02d0307501c3c03000032206035040403007100c01000356900560040401d03504c015030148103071503029144504410248400c00001a0b0b01a401060240b02d10000e848401c06a407007045400340845811000701c1000c44260703c082d5581d03000e900d00300d54640c108504c82d040280c420054a025580c001c0d07a0382038455141e13403203070701420f401040749401c1582803200d1001d5810038002c0014159499084a03030744d10303a400a103c1170354054020300b401201c40300140041d585000941c1c0d41e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 79541404 1250 79540154 79540163
    0x501030645060509010e09030a080403020304050a03151d0c060c01020c1912020318040203040f05031927050603040602040b131701290d0f060204060f090803030103 72
    0x40100608140a403480808208000945004000c4451002164000d009503407003110101c4c0b2a81ea58611170130071110458002c01950014000240317018000c060032070b000303446070054a0038683c0360070100e100440c85070b005541240c0250011106041a40f0072000c188040c2c604001680c00c003034440342d6a4680d1040850b000321000030720021302210079816203030781b50f0003942900ca0300407205407845481400040c09690020300d05402e404491b000200302c810400c044000b9181c0c0401c03120400000f5040280140c40e078125045d180f00020328180010300038240000090310070030768540001400d4807041282c001030b100e6911181c1c04440c0d0303280f040c00200c0344200d4800d966940c55143c100040e0040c0e03407065042c850302149050000305405400c40654018074014482c4404203488582604d20648101100c584044c04209042c050304c441e81c9a1224040c024210f40c480a50b07455a5031003140c0020750301e180d80410b051051580c0810b0b000e070080d0361440d000b44d0890814011a03100e10040c1301c01003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 79542654 1250 79541404 79541459
    0x15100212130f0603020319050402090a020309010f050c180306012115060f1502010c08040210050702060c060a0b0a080303010e0703091203090c0b0c0a1e0503041e05010306 75
    0x40710452420540094100c2c090300c034195554468002d806500180c03201d84013090403000c840d07034998880c0303d02c030304c01ca400822810701c0d9220519a90000c1d0700141030010a55200d540710703101142207000d010700034414080800c0d03586000c40c5580c2c110000b0800d607507204c0c4d0005c6004015100b502d80c8042081010240c014050341d07800e251040341a5a040c3e031410025050900c009080710000d1501021901050004400414203d40c00c034221a08141440c000c0346441c0d000c5005403e04040d580d008000c41d05000d480c0019603000a0440d800c5102640d8543c1e10003020044002c121740038044154002351030103e440c905041d421516800140074010240c4910800601400d2007078010007001500240b0205043c49007841c001c001c0c0c48400070940c0c580c070600000040b0100214201c41c0c5c00a2642d0140200d14025564800c4880504076464914217200c1c910001145051000700001c0000d940318499070300344d00345a0b1005034401e42c4a0742c14146845000c0060140352802440d04030041c0581c00d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 79543904 1250 79542654 79542667
    0x5030f06030c0d0c09050c04120f02061e0306100306030b04030f0903080c030a1e020a11030312100801060b12070f090f0b040501020118020303071203060801020f0315100212 76
    0x3854a000b40120315803100e107100400d02840740451525056444025003401540c1c1e0b51480040c1c00d00c80c40c45040c810010f1441c2d04800324100c0c0d0400301c0c906100828003490610303441a00518031480c400142020354000041c0f0906280040c081010944c003414280b01541c03964486100500e00100050240264022421403443c403400c070250265500240359601c032540011510741c3ea0b001503202c1c034041444004458a503007403d9000390071000303095004002e03c1c40c543d030f10845e600c2e2070800e0498040c403080c01100000b01034801c000d1300c1100720385848052146410025401d41d240c650080c00f4850082080c0035003040c0003500b00d1741c400d070303d03080c04000d030241c15804072116003255000303c80301e209286020900c0e0a441c80100104c407801d9009000b5030a00e413011140340981264020349c10340c01005030310300080d010945162040d0b1542400244142e4505642d426607000c0c3e00c1c0310f600e00300f000080001030882040c1c0c514419000340c40300c0801d505801406540e41901d07134181c001c4654085080c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 79545154 1250 79543904 79543909
    0x1205030f0318060c070501050a050105060a0323070e090a091505180d050a020f0309061b030c030d1b05031005060306040b030a050a0332030414030703020601030201080603010204030305030f06 84
    0x5080e0700d03030782c44801c84400e490070034500022900b100c00304503495400d00000c41c80508017405800d060f1000280030030f2400243d000150000e028158112501520038640c5800c1c0c0c3d80c0703a000082c480c030310648501c6c4ac110b00000401c1080c41c0700410308580746151100e20780100741ca01d207100c840148160000203c43c0c84030340b184c500e80b004801940b8214400e203c41030290b6503204019049101c410b408483c000340e40c0c2d1000c0b58490062601458010605000c8640a03045041144818040c1c20054904d000b589280b141d0441e0310001d03514240d15100d000c55418002d840c581400e8040240c90820708600300b908075a903030050144141c9200e8400030000c81e040f135a4035406030111960040846400303a049141c02522001a840107502048005481a044030856503c07040c0031407047c045242d250401e107400c014240c0000d40f0640c0c44a01500c1c1c00d0781c00c540200014036040703010360020600e540c5103200040c1310581c004c0c0312900990042c84100000b0390050103503034112500740c0c04801f050756000701 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 79546404 1250 79545154 79545181
    0x103061a0306010f1b11090105030304030f0f06090b01061d10020d0f020c0406081b09060310150b0c010b040b010e130f02120c040303171302010e01120c03151205030f03 74
    0x542486022a8214542040003c0450030441042031f50304c0c8480b030b83d8510806031a03005911010348003160489000300040c2004840440c0f05100e81c0001501d0511500e407488a42001d1304082c0c0402d9000a0a030000b8402440380201407000b00c80d4403010305680c2e00c00940780e332508011503040c01605200309504038000c0c007819104001c054030400516a031040ba81c3c0d80c03407030095512180d60144003d440440e0411411962050070007070020001800313076000c214001c01c158040502030424100b0b01003510101b50000f0141c0e050075000205003092107008000840328440e9103076042c403040c0801401140c58031244071503101303c07400000aa0487d2000310348007a2080c1303218101e50050900400030010b000724050025030780280e4400c54040c4c0b13071b800d10000c1c0840c191001400850558140310042d8403807100740c40c0b85c11041c50005000819100d041c000d0707901200c065001302e615507000401144134103107094010150840f001c01c0d0b80d107850301d9841c0c0364030a5038030400d018000040013500301c151515 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 79547654 1250 79546404 79546427
    0x1a040e010b030118170f07140312070c0204051e1f0b07030503040308010b0c06061012060602010b01020d09150c02120307080d0b0d0c06030f090f110103061a0306010f 73
    0x400a004100414400b83d41081550f902101c0c20017009200400f01502c0034240c440d600d5034128420f140c44010341394880403402012001587d44002c101c030f4030090f00c05400c01c034011411515400c400081502c104019144020031014040c408045039000c0484460340341a001030002c0000300740a2210a0007004032201e90300092100d00c00081c03082d0070103130300c075006501c078501955424103a81d8a45400725414031890116800c5ea50100c00810030501d0405c0e418182c0706240d0501611040c0f444e1a104c003a04d85a52144e40544d559020a001350b58050190a001e40303c41d1800c084d00d54200b110000e03003004030341c46a9040047c2059280c04540b200400540201c0c0c1420403282c950500e80791a0303039254803020038030351001c0c1003c80e09025400c24000155000d58004104041c0781d040c080120014210b00708c1503111240c3354200040402c2900c41d207022000d01644e100d9460701c01c0c130b00014058500950200887c800880008045c0304400c0c016207400910910307100c50b01022a0104940300203110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 79548904 1250 79547654 79547659
    0x1509020d031b081309050f01030f03030b0103090609050106060201060b090612060303070209041401061403030a120f0f0e1605031506030313140a0605040f09020f0d060e0a0501091a040e010b 83
    0x284102d0411540c0ea01503003180d184503c181b00e96900c1d4110305a11590030300c402803918000c00708000c000b03400b98101c142101010324000494a40c10f844c0c10050b14084003007a29140d40d01e007001d2003420750a0050704c000d0050a04902d01e03104400c800305d0000c1c441c01042d140c901220710301060165905100300c03464240c00400c061070b1400c00b82415454a0b1091103047c44943c030700900021882c0c1c0220104540c1c0031b0090145040c500740300d40507103400c8060305048980d699a08141e0000e211140b041021000020340e0000b26558841950380c84c008112150321018002d03900f041000d6070f4009404805000c24048007445610b131000030a166010301c624010500c00900c801080d8407100c001e10101260341125619000e655030403060f1114440c074041d041c208070311550b043c0306c41180d54004002000007507035030f030707240505040c681000c0740c10355081120400e4210050000c8501980502405090340d404104541800b141c80e80d08111030404009000320b8840c11400c9034080294840f98458002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 79550154 1250 79548904 79548907
    0x6020d020f13060c0803071b14010b01031d120a050f0406081e0f0c070302100204060804150e0d030506030c04091101030f1a0f060c011401031509020d031b08 69
    0x8144800403500020801c550b4a48109400a8800e128004201055400c9203150b480c540345c0304c07012503500070080102801603085485600000e05001042c00072899440b0000458469150004091721208d1041418141102020760384801c0c0c0812408051212105040d980e08800801a01d80340105a4085080c4802050004199400108052080803400b1040702c5034040300c0d1030341b101070b50192065140402580f0025803c411304400400e41749000740110740c41282517100b064182ea00640090740040d0424040c80100110110345102c01050300800f402503100740225140d8816a00314160201920380010500c140c405012002c0d01b4407000d003060104030741d2424601c1c244a200d4803410b000911b01000813918209074420110301c00700181030340004400710313010003860b07000d50120340360302800030080b800343d1450900c1403000d040180c400d1000558558204600324803800003a45010508040010006a84140c4511880c2c1d03494103103031620606612440d425090000e00003086000c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 79551404 1250 79550154 79550167
    0x160804122303040b0403031404110420071406060607050303040303020307050d09030f0206150904020d1704080a020a05010906080601110f1b03070801090f0f060f0204090b03060c03070c0b0406020d02 87
    0x1100000313520070707400390301c080c4902540440001040901205e000e030000700c2c044840741d42072401b0307000940c074544038803080c3d040090000f03180c5080d6804105c0440d0750f50b07440800c4800e08201070001c183c0c49041110f8050a110803078440d503899203c002d00040400d9400000176446a01503001d40c1d460b00b4a5000c104112001454042e003560b158030660383c00351052000103155454507507a82d400041000d02000740585440d07007808600d1440c900100c414404040b8004103041c03004020304010502103008040c0980d050041c00781602e03082e00000c1c10410700c00303010f104850300224000c0d0810320a1074510200f1202c004107904000c5031180c290090700901c8407060000c038445511141c042030480640f07458a640d045000c3c22240c07a200010710940c4100d0345503000c1604d0b120b841c502107001d01d00115004008210000c200d0340503420940c0003541c1c4000c1c80c8014141003103440d900002943c8201e10710706184a01511181741c9480040c07003042d42c90005410030800360192298a90110000d43d141e21 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 79552654 1250 79551404 79551413
    0x40b2a010903030b0f18060f030607021b010305010f1403010e0f0a02010306090b010801060c05071e320d0602070c0303030204180515011d0907050316080412230304 72
    0x401d00e407041d0300003818164898201d01c0c0000868034001c400a05c480401020a62881c280d800f004103202d621507a040071400700c540b0280b000601c5010030394054803200d11354914408203050319a00c0d0030704040c80c2400600490b840d05030b00d0010b5800302441c922914000500003405020710312003810241c005c0301d98100171f6010008891000030b200740c074240036490b150b0140a080b5003454000c540060202c5004004890240c3c0f1002d21490042007680c2c01d41d80c440e5540502e840e1700100c41504002503801c00c10075407000e1400504200d03c90021001c00b146045003801d000d4011090b210b1040640a056608002c8164112031020390b01002c101907a503500d0a01800035041031207520b65445001d00300c4070b108603261158600c0741d81680812602690150700441303400e200144080c0105e0829421501960384203054075218907920369842d0f0341d9183c014000d035900e001c40b1104d40c082c000c802080c8000500800c40d00c080d070303c5091400381030b81c614105021042482c4000242001c100010601040c803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 79553904 1250 79552654 79552661
    0x4091401091506140312070311070605030703050c1204021c0b0a05060a050108090604060b0f0d12020f12160302120307020709050f010b07020405072703120804030203040b2a01 77
    0x8910030b00030890107a85001c0700b000f41d498501c41c640c2c15001a028024081c1c3d030074014215190103480e0070340d5191508030360907141043e280c0010001c11008002c01030f1165240c01015407081038609028104100401250191200548002e1194000e03100c141d1a2119a406085010303800c00d01004240c1000d08a01c0000d00b0281c4510740100d41000012805501850f2000d01401c40403008188542c0c07207450b080001c0030252011030380119000807514096660078014028540243e441c0c030790a0400b140c02916110001590500d00d4101200c216511a810303800c1e6071807000c10300200d00184074189000c03820310540441951504901000f8440c0e2a41d00048140a0f10805042000151941c8a448600d09030904c100a00d000040000b8801810b203074000940080e00c60404203408081e81130613114070002d0001c45081d08030003401c10800e03c00401d4600c80310b410142011005802d007524025101d12a42c00b452260b202c00003402084079040d001c484100d01900407902d07603181c0d04070940c507018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 79555154 1250 79553904 79553933
    0xa17090a0e06100c05060c07020d020603010b120a0510031b05180f28180b07050903011a0609061315080403080603010e072106020c010b1305090307020409140109 71
    0x2c1d21000d01100d0450301031440a10b8145e000300080c40942d81314040300396580e0000800300d0300440090388500c0180c61b020095806070a04041e41a1141c100602c0e100c44181c00400e200300081c100001e1107002360b1108114800d0b01c0c1c122103862882803c07102e20388114641079002580010750101e000c5610240f04074107900903003080100c18860303100c00101c47e00d0001043c0003449441079204811a00c1c144540c4001000383d1404020701d00e15145490740c1010600c11941c41c40070502c0014481c00500d02032040c100018899035001240c1d49505d40410010300078503501038081c840016441d560507610741c5080000b82001c41d0840160940b03a000184101130580f02100170540301c0000c55204d14040c060035040d00c80311002000303280d1410055005070501111001114030b1500340c01804140d050009040c0115a00004038940c40f03840180b0401c100640c0340f4558061503c1c0a0003c40c000c00b20480e0f038400d40499020034110050305003004410f40301010710350780350302e00401102041140d0a00d10b21 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 79556404 1250 79555154 79555159
    0x40b0406120c0e120f15100603050108070302120f0a11040501170606060d0e070b040e0601050307080c0307052101060801050312030a050c070f03030603020405060a0302030a17090a0e06 81
    0x980880c140c1c07881d064484107200c1c00e01240c80c0d8070589440d410814804a5844c0b00d81085810340e100d003d040e5130500010503100505045803100304261034480c1d5460b4002402c003440d00700981e40c0745c440b9050b2161520b01000303100c0c8140034581081100f04012941c2002303081802e0381c1d07040c0c40b12f141049241d1040e544a40c02a801d203000046c01a242d0000300c4800d00e52500609910b41d40e0000f000419032210903555107180c1c3d2038090703071131240b000c1284030702402500316003503904c1e030901c0890042c00e04c00070030340380c1080070400c104040d5545c0400c010303801012075034201d500c07525024010f40303590007880040c403080e011800b03600407404100c4140904844250f21070591a036212024151540c8034400c2c0d0036009030080007c121401407a6101c80d0344590080d141c141040041d0343c0b048000030818805600190300ea000030b000f949058440c03076401c034004641410b0620f01e180e003c6500c83c42d40e43d9000c0c0c8000e80482021400009210847c0c2d0b4000004082100c0161110400c10003075000303803409070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 79557654 1250 79556404 79556417
    0x709050f04060b03040303051015050c100e1c17070302090406063e0601030f12020304050109050f010905060c011a040902013015090516050f071403040b0406 69
    0x204604203481402d0543e0f42c003000325895607450391020380103010090305080908100c450002400c4046012480d0b00d24240d40c1c07200c3e0b07a2610800850701d80460310300000070840c6090b03040d01c0c8200c00012501c038050b4841841c07807000203450009481200541140f0b60307041d1500404c020107140d06a00821070040206d0b401c010b80c0352921000c9039040c0c3e81c91040301c0f5038025a001302010400109240f02108040b107070107a00f14034201d8856060100130fa004a4030711006070b0071002000100c401c0b1046a800c94030003141000e00e0b000008284100302c0c440c0c14055034200c0c4511240d43d02c030f42c4010002d010023504243c0ea405012003201e00800c000390760582001148406000140381500801000310b40596504c10759800100e4150f2048103409029840c500c1d1059065440c1602c5016801c200d60303020700040050380c504402030062314401420b0802003900341c4080c1600980000039504212259040700b41c4610213481e10b44050103c10445003681e100200d0002914849075004100f40d6105640c0c01e0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 79558904 1250 79557654 79557679
    0xc0a020d08090309011817030c07080f071502032803060504060b0409150801090606030b07110d1d04110901170f060d02040906020304050715020a030e060a050f03070905 74
    0x2112000c1e810b44054020307801c10000d44405602c50700c204026807002c4040045a0390340d500411b80900c41081c0020382d160400724004541c80802e00490f002810010041c0001d040e80303200d49921000c8a014903d2020344501007100503030720030001e40d0340c2000d408d20301e0741000811042480c02010030b041a500001d0500e98089107509081c003414049500c2030a11505040c10080c2046c09010441340304603d2940c5030800066580c0240142221240a140009000c0c0d045080000d60807400400c00d2080c001009180e004001001640a1104a00c4d20700340c040741c034560f40181307061024501140c1e4000d09241022441c420000c00816803003009803115800503c00050714803000c581190b40000703602540340000d03854100080700c0e4005034402400003a10000d04d40c1e80340102d800503181aa00ca910402c810b02058084481800c141030701d9000905d84a181994001c02112412120602070000454401d0000e8000c40680c2d1410002540154030f0b0328003c0002003284a6600c5000d21520070340b0b204 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 79560154 1250 79558904 79558907
    0x7080405060a0204080613030513141e01020a110a1d0919020d030e0409080d05040c05010203160609080409020a050c0705041404060b210a060f1406011b0b0c0a020d 72
    0x201c84c125030088000e42603a5071400e008403030b2030001c0d2206a0601c04204200104c003465525180064102c1c00d540e0350120f01c0c0c0c0800e102d04041e00c02541e158507601c18580000c0c5030380003e51820604d500841710441101e501e400310741010815801010311a5860b0070380900020102c400603c0f0301000d204a440c0c2c8101408441600005440042e402c417580c9030078207000c24807a108544000d40d000d84041246c1000340d8032071000341d2090a10f80031440d5200103100405c211040401300619091000b141840050040c0c481c81541041c00104425a80e4500c20200700c040c1060390020a00b0f90000c40d220300702000003404540c0f0085407640c1c1030003a0b2802242034a401c0c170400c0c03420702130381c0c418101e40c1d521540d56800900a036448145c1c002484400c6000c014000b000f46560300920501030b003110680c3c0d141c40d2081e1001030a002c1d035050b040801d011411495918215800142403a203a80d19941c444043c0e0341070740340000b0103011081c2110400056401500040020322202d0b4212214103032504230 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 79561404 1250 79560154 79560157
    0x6020a0618020d0201050309031e0405010e1009140103090204050705070215030415020a02030702030a03091d01030803040803040212010e0105370506040605040e010606180b0a050d0f0507080405060a02 88
    0x10001d501414aa10f081c002d5441344000c0c5600140c410110b82c58088012030500d21028401c0c3d00080c1d02100040511095034400480c04400d00151010b11a00000b41000f03071203642d0340c0c060400d900e85804000102c0da0312940041160366000381c420030040c01c183d100117003642c4c01080181e024a0703115110380c81ca01031080032240700e03640100040c0003002180800101940c4801140710031807200b0310004001da03805000150949120345c480304501f43c80c082c0c1000c00d03a2441928030070300c1c030403101c0100b0204042c0c200b100d85c056844031003961303666240e00c0010742d0010242c00c0c440c11503180c94074048401d041540304500a180307880312880e20b82d11003501c140d0607400c4100d00f40a491044082d00c2c506c0c110304e4100e207410650017000840c034680c0714000f245c111040c4c141700d01c0b000c2e07455540412919820640c9680d647d401d445c0e45511490a01030b2420f014800d44440b071040000014a0444416541e40480c074000e0b808001030051b03007801000103100d0b0f1010b94066a0030300810010812702d80040c130 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 79562654 1250 79561404 79561451
    0x30702090a050a0c1d27070f09080304050a09090804210b01050603090c010305180102070501020d060b040509220606230109151103120903030405010c02070509220204050106020a06 79
    0x702d95032129002c003801e010343d204506d00035045203035018126440380c04a030540380b88115000d6641c100c1e03a0b8100e050050010306242d0103821241c000700300c20300c80781e21100c20100a446030f80d10f010441d4110351400466034882e5a00001154030714a614102107500203440509080c010486608182d890b40304201661109803400689a403100b50024002d5001e41c0150760710080c0003000b8540305900d84a42402d9902001088403d030750700241034041f40c55036204000c05450340c0d0281c0b604140c10100410046040581004001040b80007010a4045030032002c03603030180e03c908144000c035541e0090340b0f04044980091004041c4c80c4c0760280680d40324a0048003102d2050b060514203480501042d100b950b540e8200000c2800308200e004400000301c0105400707810385800440c0e8034500750424a08461242d42c0e890704641100d2810406966901081d60700805004695180003104100c0c06440d10f94401c4029040b03810400002142a0003050300c56841e40500404e0140064910703d071428026180e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 79563904 1250 79562654 79562687
    0x726010527030406080109050a091b0e10060807050d020403020406030f03122913060f0e090307150f0b09280b06041e081c0f0f140c030702090a050a0c 66
    0x240100407d648039044150002c260860000b40c0d0039540c2c80380c0241ca40004c41401d10080f070114100b0102c3e042d4044c041d8410f240c40b011511030f6080031401422071030b0203407940c42048000310300420607030100d074121130085034020070400c865a560302d0421264100000150701045692044040f40c074950b004100720342240c1881c030400d62814201c030944444c0461034980c3c220710000d80d2070ba0268002c0c030944004e082c0880d0040703210752800c1c0b00950411002484c0c520190014001d48000460b800b40409002e01490780104907511080e1000000304900303c0f0b001d9110381c2c08000e000560f00c01c5203036480300c185039a10030b58103a01243e000764161101c4082494005904006c1004681c000c4546040b40001f0040d010503040d40c1d5109e00c41c070b8030300e803403101c030103159801ca840e0b400c4280c0290003000d4020b0503003000100f10000a00c003030b090113a440c080f0302100f000040c8c00c4001c14420b204941d075040e4001c0c902011401d0800210008080848183c1d22140c5451034101c000e900038921030030a82d181 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 79565154 1250 79563904 79563917
    0xc0e0405100513020d06080601030b06030307030e101103030a0515150403060209010302071208010e060f1c02030717060115020c030316060902040c03020702010e10020726010527030406 81
    0x1442e05201c0c80b1410720303040155107039007031207910506000c60141d1401440010014080d9504506200c4400d00e809442c840c1310703500405c80c08000a400c1418090340d444101d9800042081901060394075098033321481c0d4080c0000005c00c0341c29186540442d01421040c0c91401014641e801445602210404804001c40c024001080065610b400821a1090601d07000d401c0c0481039a444003170071030180000340840c0d0140010711040e0181003919511403070440f540032040341d01130701140304203002c2c040c0c3e41030512240060500b0b545041102d034005000100d055080f000c40901940c5d2105004e000e8105546c2086195081480c80021002c49034080100614035018411610040c440e00c10340044030002d844500e03100250380e451161039404801d80e02d02503a01c00c060300c00141949080301c0624411040c40d0684032543c0d80c00501740781503a031300003103034025130b007103008001e1002c0c82405804500e5070030070042000d0540c00e03861000d142c000040291b00c040031074800d91500d0340203501521000451 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 79566404 1250 79565154 79565159
    0x12050906220506070506040b070c02060403061a36010303050910031b03020d0e070305060a0e03130f050a0e06060a0f051309020415020703050606090405070f0305010c0e040510 77
    0x149294515410004284910551907035000070a6a503042604c0503242a04004208014000c0728200343e07501801c03d1405150088150340000c1c0f2901690001500c001d680c0ea402d00e0110a640a01a0390820024039031103207103400004410450b0980705142410011100d00d0341d00078046548000d040c0c0394540c803403605100488041c01900e060340100d40b42051346450746403031900c50400d00d0f0315080d5403035903016079142a8002d00030251040f0030140d02e080d0f4407109040001c1500402c105420a8841c21b0100703000350703208100761941c003132446241c5d442600c0c0e03e40080d0950080e400201110820f850b98000c5941c0d0f0700182c0070500003180c1c1d1541141003000141c0d9034900c103207100722980c0d02c1800c1c024200201c058120b82d4811054010111540c0c0c000b5042c014030101d0460300c1c94103401c038801403226504560707900d5184d0340041c011500500020b408101002001c0c44408094050050650005a607e003000d5001c0d0060869103000f08042c0200060142000c0c000c0340d20400000129000051 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 79567654 1250 79566404 79566427
    0x301091a0a0c2a0305070f060213050105091818070e01080609060103050d0e04061e0f0b0a12022803290102030901081b0d0605131e0203090a0b09010912050906 70
    0x101c1d4401c110b00304441049074100141c0d00900d6030300508d000d0b90005841d202c21601c40415141c41c1d4100034144032007071145a04954401d0310094580c2032411400d5000d441d5800756084201c0100c442c801c0794003c0c0000490180a500c9001e07049030b006c0b00840d074040d1910b800568864400f804040e010343c00030445078015a00a800d241e00600014000017082c0f039607507030138801890720640c4d85804188410010400340e43c1c50000c0b0406407100015040c54002686400f40c01c08a00c041c201d290590041409006816800420b05c0b94801d54529005400d42031600240141001d000305908441200020518041d00e0000c19202d007806800440c41c0ca5031050056070105401810b2010280c45554906504080345000c0c20115480440100d203281c2880200f04206da4a0300701420510320340078120001104604441039804130303555005903245c031840c4003103080c69111000640304001001c01e006401c801544580006d5010b45074001d00607070380c800215150300c9829500740d800301301801100c41700c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 79568904 1250 79567654 79567727
    0x302090303070b01030b040311010c050901031e020a020304091104051305060307080106150908060907050d050f0a030503040203150108030d020d140f0907171b0301091a0a0c 76
    0x22401000c880c101010b0766075a04005a00360000c035004420541440308040d0841058030100c901d44000784003450310707220010068040c1c0581c09041548407801e81600c1080c040084101340c0d0801d50a40d5648103421003c3d641e54024030820b031005207880810444859402c1c145c4090b110f00034440c1c00d0340c1d071204602401071301c03000d455070781d16000383e660004541c1001d1007604004c1c40c10341405c600002d0a80b1020340b5000755035220056581200741003040300d10010500710165001251103810404507800e201d454000c1402242040d84201070042c014180c11101440c400d900c22405c036a0140400d241101468000380f003024215401405844d104000a802a00d4840d1401c0400551038011301006d9107940320940d4030b0035003450720700309101c6401000e100b048080c01441d465144251440000e0308d544000584201c113038401f1107010030203543e5003034003d00d00b420b400501c82c0b10250441400040205c2081d0790344132403d4030388241d1603455030260801c2801074642948541c524100c0079111101c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 79570154 1250 79568904 79568917
    0x20c0d0507060b04050403020708010b01020f060708071808061902090d0803130503040902120603070f0308031009051504060807031709031c17010b070f1101050405100305040b06060f07030302 84
    0x80e11000603c1c400c3d122440b5131032103540203600405001d407400c00b00900310782415405a045412400c00172010520005031290000344038135010003540c1d1010003c84e41410f1070042d524400c181c6c0c0400040c15440040c11078011140082c40c0c02182010701d0f0980d04a02c01e09031102e4001d03608125410105010101940c0d1000e04034200340b00d03e0f00c0c035a4540381503a000381c00c40c1c01280c5c0d000c18803c0c000d0310142040c0794041c5003075008010321410074134081e403113081e1880020400e050000000300501c03072004205000f000c80c0d8905000e141030a083d1056000c0c42003070401d000340d1400e0f0000078100000078070720040340e0704540c0700c0c02100a07909d0100c2c034030741c8600503458040c40392551070030254401c0c0c0030001c09082a5510a000c05041d81d40d421150039041e8040000704109212180218803005030b01d00781c440d40303d1608004081c080005a8a03401583e005a60005d4005598194260140c101c244200d11172a0911881d130341d0501040300d680589400d400010805111400000c0d00940c020181e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 79571404 1250 79570154 79570163
    0x103051506190605030a060b03010503030706020703120501030f1703070e0d0f050d05040e1303050901030203040516090c080105042d0207020a270b060d09020d1b060909020c0d0507 79
    0x291a00c0310ba000d42900c2c400381d00420002e81d0000c00c0181d01d5016200c0d2102a100c2105032900d194940000241c0da40540e00b0007620040d030010f02031082501808d40d012651108600500180d80e40742490462091a0302c010740c0c03a81d0034000e60149030707440b01c0101e0748114050389a0140e01ea140000f44121401002d004440d5400d01202d05008100304000c0c1c00440e6125a42e02c41d030715400c00445006825015000c05001401c80c126040001c1d04441551440c007000e207001a140e82c0c440c1010303454241c4414100c00b00c1ca400007800300b200410b94002a02e00652900c0340380d80d0303982c5c1c0c3c0e0500c00bc0700c000c070f6804020a5824040c00f40c6020080b054142400044203025040541980010f800d40c24140d0280110340c881c1c0340d16510170500c0e0a1010f00985414404109021000012942038800e800e0b03242002580d03403508504554178500d51580c0c83d41c00608170305496481502e81100d100d202e0040350049281e9120004100d9143d000701c608028401000e0028078616100c107440b030350040d150464 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 79572654 1250 79571404 79571419
    0x91205130305150117070602030304200a0b090102010c020708030406050c100203090109060b0103090b0c0a030609020c0d020f0d120c0908030c010f0f150b03091501030b06090703050103051506 84
    0x71800400203d800f10880c0f903191180782d45014882002c4601c115118942030b002606c04000d002d40120559902681103840030302c1d40c0c2401441490144c12801c000d583c400030902c1d01141c3c000b0541c0181c40816801c1e0000c21002c0c1c644881680e50350b40d54421007009038000c100c284000c80c07007103021b02080b0084900716520b24024480040c140c4c3c00c101c554050583d0f4410342d0400b03021090081407042002800e0800484600c0d464495801d40010900e40700d4000000b540c99103188664800c03c002c02030300408540350b400884005482e941c10009620052203004003045510b032020540024204140e200c42100320381d021910000303083c0781444403050080c0c1040000d4506800e00041c000320402c40c000142e0701007141203880488036082d0070b10144a18010700596012900042402610881180340e5220303a034045a0b18905043c040000b2000442d40000108010300c2035015802940202e4070084a9607e4420850403135000f440007521682c4071103144032101c0340d001840342d00545c01a1151 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 79573904 1250 79572654 79572659
    0x20d050c09150415050d030c030e0607030e030f01060b07110a0e0711060a0506030c010513030206120f0603060720100e03090f060901090e1302100306030203010e0109120513 76
    0x500d1a07908407440b00320704401800d04025032510b071141207144400c915555000c02c0c10500410300344640244001c051000c00d880c0c820038180108040681030f480200040d0780c4042c80c0c58000d041100d1804880d0291080702035a82c18079006002d88025140c1ea9044241003001e6078680c118105410043c00da0081d64101020544060b5001c0140c8a031403181c40f007143d1030100c00002e42c0303000c070010040d410700d51928090008646c1c001c82d003103045410902e022501c505607103010300c0c01c00a840d44000d40c0003800080b8000c0404010380000d02c14041840852125038562007496159401111001c00060b05203184001c804003940504010b2400141180c008040c008211011161034032840304072940301140003485e0349810182110041c20940d0914103041450300080d000c40c0f05405105110701d203076000500e4603000110103d503030742d0f0024076504004844850141c014103441c041a8000c2d4242901003001c0c0a05000e1b01400356880358190a20103032445044030389400140c0300c00c01884010800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 79575154 1250 79573904 79573909
    0x6020d02070812090a2f0301090609020a060503010608160e03060a060504240603021b0a0f03030c030b0f0603091005240306040305030712020903030309100b03010207080304020d050c 80
    0x251501a00c207090240d551080d180e45100100380c01480c21806600c48046180001c00d032900da0414803001c5c21605920301b80300007101c1c402c50781c4030030ba003a050742c0b070301c500354040c0301064202d034040c1c80c0240c03002060941c0302c040480d050b1100b4080d90021a2644d0042141104080c00f20503a8401c2440d189850f8600f11000a0500c10b06440340000e2503115141400549864481c801104004050001c01403224281142c0c24070f080b44640e1082c9640481c0d0468081e80d410850044100b804064441d400114645040002060700c0c055000a2900c446801d049001e44601e00c6842c80051a080810704500d040104940c00200f516116010321400703c940800c036400f03502d01900380104502c1078902070801b084d004900d20119244a580300106100200740c105044a070446103031314002079100f140b00b03240d2029200b280c20f00c64061000000b04180b0900100e8020903146080100344284003c02080600341d00400310302a10039201040410018908803584041462288040c0c1d03440c030244900 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 79576404 1250 79575154 79575157
    0x507020303070c140402120a09030306030215030a0b0105070317270a12030510170c131a010504050f0f1801030b010e07091a0903070803160c0906080c0d06020d02 71
    0x40b02d48410060042c4000900160982d495182c1505c046090140c800d86941d15084058028020240c2c1c422102083c148a07800603800340d40c02030400881c014151020f003005901c00c50300c031f6180e075280000942183d84650100d60300c094150340c0d901c0c7d26000c081414880140060580341c805414080044400006410701d540e030b030842540a0900e032011410301d506550300303d850840406203003408100d008400c401a080039200418400f104058060f10854540300381c081e405544010340d4218065443c4072070700606076654000311141d5002501c040107550740d000f5805219400b9003a00762031009400d2243c50504104001081d44481140d9203601034101c80342a00b0944912181400601080b4081e00720290004082c0c83e21288462603d103035102c1d01c3d0340c6001186060440000c022070729503420031400c0c0280c24440262a0b50304e0907540c003d126180030711402c4408482c10315001640700180d101d004104c0749002e002c0e28442203503400300083c0c824034175001c868840d828030075010802154030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 79577654 1250 79576404 79576417
    0x9050a170106050301090807120201020706020f0315011110020c030f04060c0b0c031b0307170f10080604080909130c0909140604030f080c09041806060815060609010507020303 77
    0x8000003032500d03a6902081c25240c042d000140207a041c100c840d4001003401c800c8801968102c4003001300c0002c1c98204a001e40304894029018900200b040000540c8010040d8002d601c0300550210240c4e04000540d0302540d00c04d11030403650007400a4602510f120b8004019001d40c0c60160383c50108a030144048581082d08a0b10015086142031820013102800b8142c00944141e0603d086240001c407c903051b0b44071603c101e4410001002189116024a03030207103065400b8800c0c1c00007071420900800440300100c0381c0b01240c550366200010034150129900340955044941c9a01e002658401d01980d090302801c09101600310701500710200ba00f845100c03000d048036030f4020411021604041c3d2100301412503004440d0800c0c021711002035001008040d85a0b540c0c01c04950030b81e500f0b02c141c6d4940c016501c00c15042800c0240100710030b90a61800f1102610500382080f8482c2c0300c10402c3d07595591409050320f08040310340458101d14228000c0c02d0300c1c000514000d4981062039000c00c0c25a00001c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 79578904 1250 79577654 79577669
    0x30906010306150b090f0402070204090b0604060b0703021504020d020d080307020d09050d0f110a030507030212060609070c05010207120c030908010b13050603100203091c020601030c1509050a 84
    0x800103208100881c0111400e0022a03041045120705040c100401440f42500e8a4498031010140d44606e80301c0c0d0301030f56030f4183c00034410440ca1030b0504005182040c11101d140c40740d4540417002c607804d12680203692000d90036500401403500e400845400740c0344040c105a0388203101d1600f04005a4894144e0170307195202e00401504c9003800c03500a413800c040ca040720741c2401405401481140c50b104100c00724250800c0c40d641d005071003814055900f45082c0d60f0640c000c0c40c0420040148100001d060044034402d0300c120b905c0450710b104142d1200400e8a106034460031420100b8801031103964201e54403030051000618100150b6180443c90710801010004901600010000c2c9074100d41030340e00500303150000b4004084a02c00103040c0d143c950400320710080e41e8002040182d24104002090b16803101800c40d81da04051001c25a108050160b01c4601d100c3d8040f0440101c1c40494014100c940c0003140d80c00c041e0402c10000001c481c000320702c0c0200700320084001105d0341c41440040043c07515 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 79580154 1250 79578904 79578913
    0x140702150f1305010813081b120403110609090f0702120403060608150709091a040c05070b10060c0b04020d0606061206140901030825080405100c020904080a0905060309 74
    0xc0700b884a00740c1040b5807066051101401c03c000c00341d1000c0800c00d51166001020325500c040861500b440b1000035440d001407442001da8400c0031346030744802403003503a00414201c50007502c1d0104200841c80b98041340c03a008400071002c0348074103c15406040d0010a030b030040d2440324500242c0c0041a0304194816500c941d210001000783c000148018225410b00131800c81f101d1909a501a10841061140303191290355036840d80c1035020800c408001c4c180e8018424060380c4000c4200511980006206454121030032011411581c0c2d80d180701342c215160703070305c1d0041a400c280d1900c43d4050700c010401e9070800e080c2a01c5600007444d521841024107a10b0720303504c41c8000080740000484001c1d400514400b4000b900300f001c0c82e915103801d00d0450b0f40c0040400e544000e11003449c0c6980802c009109103041401140d0410460440040d000b681e1080c0d903c0140c00a28102c02c50325a540000c000e5003004210002c04c0105600f00300034490b40c2c001c1d040c00c2c1f450b199110086402a8404c980c0403606401c0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 79581404 1250 79580154 79580167
    0xc081207030507020c100e0d060608011401080d0905010c02040207140f0d030204080c090a0608030406020c040b04020a050d05041110030f051302090f1f03031806020706140702150f 79
    0x20140b18054102840c0c1c40106444501040424081004601e0080501913038243d83d81c0c150792803038140c08070154404400d000070766850404ad40644008180b100c240140e0070300228106d20300081521801082e90b4803650400d1800d001994400711040e410317a000b607020017541c004503140302c02c3c2080080a84000789a259222041141480344065110003003500400040110941c000741d0302142400403100c2d00e00940b203920b03000c401040f095100803002c0c00b0104000402c0c03a0041550170700908141d4090161aa22004220407481841d4042e40803034828000d140300c0710380c141e112551042c0702c1c40c00e041504000c100001d00242c1484130450010b51a40d40c641807001c00d42c0600c0b60408030320030711540b9000c400e50018400210060600c3c0b1900103e000240d8800340f0b10048036100700c1c0d503d90a100a94513130800507c1c0c04002484501c16141f01800001c0345480003d07a03034103c4035240d41d00311207000c0175501d1021b168000c3c0b03011303a4001e1401d1a000b0104003160000c000003c0141d46481e0b8a50 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 79582654 1250 79581404 79581407
    0x1c0f110402040b0417062406030c09030601030f0519080a030207050a1b180903020703030c0521090102010c090b0d0c030b090c1c05040206030a0203090115080d200309100c081207 78
    0x110004e1041401c440c2c86c4008a071f0701c01401c0342485465804803032103070b240d07a02c50001b840c40307000d40d090b001e60501c81c000001003400028418100344500030f405980003004082c00c04c00c0b180c1d00d66403004014a0301005070341140b510039806082a0351140301075620341030f01a11041c008540000580d4182a1204001c10101c51001c0c49841629400e86042c010151a910007a403111030300e102c0907007030280c0e810031007082040c113005074840719482c04002c80705003040c600410000d030001049580558a8682e440c10171502940c840c05c21100c0c2d44a20514201c0c112103520081d000d21603480050640b03482c1c90030301a9582286440c8101d0260b80071580301c075511588811108a0007520044e242c1c40c0c1024000941c441c602140d501c10703a0020050781e82e40300c12241500502e0509021002044103010229101c24049429440319200390303106210000c1e001d14041c0d07000b0b034040304030105a00c1000000490f051098411b00c0807960340c02c1410013001191619078403a07100c01c207882c010501c000200042c26 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 79583904 1250 79582654 79582663
    0x16030207063e010c0513060e060405091b04320a14060c15040219060801030b0408070f03030b01030b12030405041a0907020c010206070e130b041d0307021c0f110402040b0417 76
    0x5147c1031501c0c1c81c1c400c07030b41c002082c142d11a500030701d8001c2c410381c40040c0d00140c082c03000e2020075841c019415502d0383c1d100103103140e54000100401c0e945001c002040041c840c15800060464802440170309110310302200000da40b640d65041c01d0b08050309018a010100c002d008018203d0038148a008143c5010f1040114101c80d00300c0c0702a00c0694584240038250b8060100d60650313034401c0c218074050305c3e9400d01e10294058503030f0080031403070034008040400d5495081241c5505081c1c80a101106a042c20400e000c01c40c0900800c940e841800104054906a01302411202040340801416070b80c01011480b5080200d480784c0140e440b646c0030b203a031541d040241540c80201446d1a042d0340c07100e1000030b0030045660607d4420141c54150460050b95564000c040305090142e941030411400d90605440ba00080d200345d104001c170880743d071f003111420490101b02035400315940c40fa0040f03956400004011482140f90000d030b0a120104101508000600103029100300c4c0c161f1861203060443d160 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 79585154 1250 79583904 79583909
    0x5040611040e1f080d050c0a0f0609060b0307060c060b060403140a03020f06060604031b2601110903030702270430050d09021516030207063e010c0513 66
    0x120f030b100c100300310072880460109015202c03440d000340e0356020040503034a8042e070804e02030145001d4008860421240c1c0d07002c035003014450a4148804884d0b24200f54417212184070f1b10003c00d80c03040c005400902641d11103008401c004015605081d200d0315513540341040300c58400d01550041d8158420315404100c0c0c01d2000d0244c000400143c0303411303400b10b05540103610008000444c20105c0140e984600b0703190301c004d44042c6081d0964a0400440b0141c902944102001e055191034400f45036140050100d4102c00400380003146005030135802e001000138085007842000100c0540d0f41204000c40c00c4181c0924021010052107116982c117640d000200003080d80031025280044410441e0402c2c1910950103080c400002c8288007070010560840201c5981c030100080042c3d10310302e41c90110110320350b260003582100d0429448050584800401030701030340e114894141d581130100003004005442c4412004c01c0d500a000d5899041d0039070381500c982c800030900109030b132000e4500051140d0700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 79586404 1250 79585154 79585201
    0x1214010305060619060e060309030d0507021b0a03050601060804050304150201091101110709051806010b0d060b040303080105060a03060e1512030708030a050705190807090e01030b0a05040611040e 86
    0x41203490044040d0846000051047c0150790200004805660500554a01a6090105000603e0098002505c4461050300080648030081450300c072402c00c5451501500d40c0040209101e0342050000d507483c0c2e00042045035648001c01010602898000422110b0344040d00040741c1140285006120762181260360381c1045025646a8108507000441a040b601c0c08140025592103500b00b8a0004030070f0503104a061081c4000014a030310294024070941e03d5058080005c00e440d10303400c641e9803180e8840680016010300041c02146880b000820040c0a90b007070005585039202c07210312000e10100ca4140b50b00c014004649000d080600300002443d03038000c09146080c80f2541c442000340809000513403002d84d00c5000a10041c0030704115480e1400c044442d9040040070b4a00a0500800302c031003c000640c10200064500824200c0b581a01d0f40610392200036034030482c9000c0104802401a00c5d0240c64501421502c44444c1c0100302402710641c2200f16807a01e2a40740b007d81d8004e00c112503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 79587654 1250 79586404 79586449
    0x11010e0906030607030b010509030d08060a0603020313141c2309010c08220b070501060806240a2d080d0203040302010c11031e0f120a12140103050606 66
    0x45296000b00f08903a0100b0fa41c03d0000f0000c42a00040785c04c0d004940c02e1036017610074035080c0c5d82010380252005100e40c0b011600361340b08a4894074205c099000c2500c0e0540285a909031490020701900c100c40c0611200708100d900035078201d8424101800580c40c83c07408114003c40d500d00d104105050f0011002e405201d882c68085250002090004000d07000341c406440410b140e0f05800f080603494601c03690780c03120000300d1a2190640c80ca6680306042c100c560398600240050004004035050b4482c1502d0003458111204807480381710943e8100340e010ba400440020045405042d0f0030700d400801302d64000c440b060031054404864445440d804c400480d60006442c40d2081e03500000300c0c0c081d20f50a03e440001d20f946031418100a80003894a03d42c103018403968082c002c084514540040010030040310386d005013030340000d511418030038203584000030f08000e030360169800f030342e03421540c0002e20800158130102131a894a40c4071003a0801c036400e401200c1440294641000460120b0038501da412 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 79588904 1250 79587654 79587661
    0x60302120111040512011119110a2111010603050d030e0a110d03050f030703020a091d07030b01020a02030a050d02010507050c071401110618060c0406080c180d11010e09 74
    0xb03001e00d00603071150512480c0044501880c2c1d50081d00901209828480341d0b81d103400e16104540000340c0c00b09201000100c2015040c80d480f03000083c0580060b030004401c4451024040314004c0040d00244c0e002c042c044000303042e04580c0c0007480780b5402140100013a08845c02e244100a0950700c601051100ca544015a548041407600039403000700340e03044803208120011407070255014011141300c10039205003c030802030500d400d500100303246096641c0301c0840e03940f200040030301c0508a894503003044a101d40001e090034000d5001c49460031050040340c182d8600340e40000e2411f0500901201c090b009003408040c0c25409001d01341e0850140c0c00c0280c10803800010072a55070358640314009200301d05d45a80030b03080e401280301c07150650104003580c40c540380c001071004a00b800785090854504c90140014200c5480343c040c0c3c1d041d6039035a603c003940c540b0790b50340701c10342074218440b141103a006c1050340344095912485400c050a100e6010030400c2c3d03000c03000140040092202da28040c0e094401003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 79590154 1250 79588904 79588931
    0x160306050f06090301110d0b100306031a0615070602040e070906020a06020d0204030804030b0f0c09240405040608070905090a02060f070f02060301061706040603110d03110304090603021201 83
    0x407600c0840c019140c55407501c585500090141113582d09850044000180c003c08001c0f05400c0844212015030307070b0400b150300c211012012140d940c03001070140c11a00045075100e541b100b100f41e40240b4014001c00e0700b1848408081c0702d50f4407181c000c4451550003c1d0805c112394800b054268400b07407900f01204024a0103501a44860301c0d030790020300d800c0d40003940b881501c0e219410780e80516000540c40e901c0300d8482c0740c40c512620007501c6e03603604550707050300040c4041000340c200d81440030080c1c20440c20b1f82002029003410b008140102000d07107414440410540c48500c41c0c00028104032008081d90303440c164004c0c0c1100c80240c07090710b240d0001080103001d80c45e8134044503a41034803244030381c4c0e40390f0b00e9003480b075144601444000c2d070210001000144159000070386030071000c10b00310501c2041d1542000c2200305e074207a10005260340b1100030455002d01d80400b43c05402e90090500c0100c1c411a2090346040d84e0181d00105600ba94601052046d0b003805441502915040802001061604c211 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 79591404 1250 79590154 79590169
    0x1031d060c030c0f030a06050f0d0305180609030102030a050103031707020d080c0d0c11010c0513050105031306060e0f0105030102070b0a05070201152303061303030515090f16030605 80
    0x30855120002c0070032429058102110019140d5441440d02ca04082070480701400007403007070a00c907410303e4086518a10301801000365150340368864071f290030740f1080300700d40c2c4003100350391558052014425440d4644080c002907201d003507450b000290660651601504028200080071441581e441c10080025000141815521180e00786106182d49a100383c034018864500030041c3c060030311030314100c42a00110f55120340c141d000028000485039050450340c07409141c81d45040c00d90508410800c13075000e0002141c1129848d0411100c00300992281c1003917030b8059020100d21107a82d802c004242100d00002409001c2c02c030000d5180c6900c0b52101c1c01405c101070103402e01d16503510b01103400d4600035400300d880800310343c03910050141e98909002160100f0182140c04844054034506580b80104010348140200891207050b000c50b620102d008020090900b6854031003840c0c00079096496080381842040c0c40310800c4064a00301481000001e05075042c071091600300309052141e86c0e03940c0c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 79592654 1250 79591404 79591411
    0xc07050a0813051903030906020a05030f0c070308030118060506030c1b0705031516030b10030f020d05090f0d081003020d300207050d111903021c0201031d06 69
    0x40c0e5003502c640310b1441101c040e000c03907441943d00001054140c8041401c04000c8800c89001c5c1d220307012601d941d0101640c486c040418020410b0304104a54541003801c54090f100c40c402500807a04c0b10f54507a5100c28003070307000780c1151282140400c403040701311303189005401c050b20094807a0360842c109440fa0228501502c1e00d00b24003102c0d84601e800840d18100032402c0109402000c8031f04503000705040100d4200156880088850506042c11160707001e0300841d00100c40203841e00080841c0041b0840041a18045a0300380c65000c204042c1c0104007801001e02900c0079002900c030801e0401c0c07401c1e180030500a0340341c0c14050014100001c4080c10f00600080b0703074041c0c42d8616041c1c0945020040d80c0c01d8407000d8495000320110b066000d101b031641c0e00041540705c0c0c003107952880d1079000b00f280c06810000d006002c214950b860100c10704202c0c40c8032034001680c0e000701c4c40c016100d50000d40b0742c54601300360406800c4010100c0c0195039042c09410004400d010045940700101642d154690f94020f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 79593904 1250 79592654 79592663
    0x703051209100c0f03150501020607110c061201050907030b09070e030a120806010929071104090503030613110901050a09091109040c02010b03070302011101060b1804050c07050a 78
    0x24002500c0c90818888468461000030003080f0510701c14502030440c3c40307190901400070303103001d56588036a410200282c040d2103058008054560b104401112380c100401c00e6038806000700d4010002c17070f44a0001600519003a8061001207606060502c80a1040140504101418200100300c69120507140603000482e03450301803d1401c1c0640444e15020110030001c028102190007230319016441468940140d034260b96a8496a58510344548424850f86500d50350011040b2001203c080f01c000810f51180305000c2d4114440e1f200c0009021aa1741d128180d80e15040001080024640303050460381d01105040204400b0403049603d0341c4501400d00d0340c505000001070003d180c640141032500c014101308009111440c603500d05804290801d200c181c4c0210304143ca840d108a0040c01000310b203160290007050341b14034640044400c9114690ba10070555601c51011410411050040046c2044001e00940e8142ea100c140700441e00d0040140f00c058100b032088000007a00811240e2580b0b801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 79595154 1250 79593904 79593937
    0xd1e05240102031608091f050412020a03020d0510050a0e070905060a03080f07060b012c060c100905120301030b01090509010b0a14090105100e060304060f060b1806070305 75
    0x12200180d00d54441c102d409114110244d0b2000d00b0400702c10010010300105841011500900d074801401810200c02d541010860901c400d0142090268060f01d80030b000522105170955241c01041441901c044c00303a926030000311900c1c16556180c050290048a490000c10180d050302500030f0f150340c407a01901c00100d0311040482c00e03560704c00e00b01102442d00105c00c0c4d43c0d80e03107210703a032141d0551107024115041428081401040e602401d50510485102031034001091030f4000c0c084030b190f54112146a00a00510020000e101e04110380226030342d0540000031804180d00380b03946014524602062000e50400040c0001124040780d44c1c1110100d07200816151a1000f007a405082140e031001d801600356400010b91101c1c09880000708042600c03590781990301c65081c0030b000c241c0c0d0b1100c80046010385083d0007050821200441e8800d0146400050500740007003010107039512540704440b1030201144000d0541d40d84201060380040840e0340314500351441e0340182507401001c080022300b000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 79596404 1250 79595154 79595221
    0x303090d020f07180e070816090b130207020411030a06080c04150e0c0c010c120b0406060e0613030f0b01051203040609061101021e0301140103021c0c0c080d1e05 71
    0x2216041051045202c40907030b42c1e11607c421495907507040b400b201080000d1070500000c2d001055119030021000c000d08000c102c042250741120180d44400070480e081651004059072000b840d101850144940c0003003c540e4600d000c03200c519045502d12103510491038008049280d400c030014800440300f041c0400085a5103140102d0350394026800070520f2942890b1090a406134000c48442042e000154100540b0403c2010f110484000e4040c4138003145030716008103420b1400001a01c0003000d18000200e042e80c4a03628114100401e4100b120380f5851000180418a0302e00d61034a40d540142c8011410685044401020401640708880c00d0011505505003402000e4044500b842200c1c01460b90612074141c0341003c1c1d030b00034854017107200c01c540c410406961090089500c506010303c00c100303440c05c03002c019500910302200464140b144000001b000a2424006401c816400042c006032500120892208000c446e0366107a00c40ba2500c000c0120b09107810008080c01400d04502c40d02404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 79597654 1250 79596404 79596449
    0x150f1c020108041412030f0903120106030b0d06110301080c0102150402090c0d150501021c020a0b091c021506090105060a111905071e0302060706050c0409020a020303090d020f07 78
    0x16600b00c51900902911002c1c070020b0385d00c2e5004500400141980759001d540d001002520f0f0300801003044d25000b0b8080040214074880e8100c07107a20742c00244841a504455030b40c4004503081030711004602078010004000c6d01900740f2103402c110307900b070001d4840c414404d01e00d6480c0140080c0002d00c12500e11011880c80100306043d41d90b5000080e40402c5003c0c105820800500c0d0148509401885014003401038071810b1814288202c001d40c000b411800515507540c00c403a03400030510601445034624002d210010307102e00b26131010b40b54028244407a01e00d00c52040c1d0050080240e07000300280b9004001a440300c1046800c240054030f000034840e1a5000d842c3c1c01c04911440a880015070342c0080c0d824804003140d030804540107030610032104410401140c0000d450340c800603520820030311510012440f180c2201e80d01188088582d1b10b0103031962440300481e000f40742d401c07006a0010040000001c002c0001e40f801d11010b000410440c0810300708169241c1540c050140d00c00300450808001c0c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 79598904 1250 79597654 79597673
    0x902090403080703110a02010e062a070f061e060f061205041b2705070e010c08191e0806031e010b030618160f12020105070b150f1c02010804 62
    0x5d1040c1c40d500350769400c0490009018200102440c01c0c07031b005100201d200c2034210003504034a00140800d64511010200510300560403c0000382d444003085d400b5440010001e00c03494131464221005003615041d80641d000441c0e40315004043d250040301010f01c1030682206201044802c0305101203210b0340c99140115420403002201c401e503200c280030109000c05081b244241c012b5050092000e8100141d20300c1003a0b5909607007400104010700b0300074400394415400a43c0700c9000f400c500e49409001d0b1442241d15540b000f0920000e2400903008a2050640100052900d11485d01e10118288400042d8581d030200f00b5010358651810f00124042e0001c0d001000d83d44402810751361741d45414100480d9510300d40204107041c0c000c810055004003a112110f0301601c03040308400c0c811608016054220031003100050b41030140070310104001a400301100c5105440c03a22410712500d48100503c450055202c000034400d4030304070450800820351101c921406502480c01010644807810450f851 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 79600154 1250 79598904 79598921
    0x31c0b090a2304050601300b060315160e0301050601270315020a03060806090c0d1406040c0602060603011404080304081204060207020a270f11040909150902090403080703 75
    0x500318802d00700f2084c00f0f404105513040ba034895000c04251445c0044040d059040143c070070f130900c8040105200820450741949a1048014046907596002c501034403007801c100300c401c00c042e07200d22900014550f030b00c40c5404000310f0041d8002c1c0028180840013034814500007040e503400c080b4011106640c00c080e052000300550700500c80c1c20000c10205040c0000e5440309040c40e02083c1403200c00901070704d00041580c0f20f8502c03840a0072100100d5800c010300c00346003003030945055400310781400003240c041c00070f00c0c09588a1258001c41d5407030071302c01038180301005120341d1199241444511407000801c0e4480d502036880010640e580e9035601c0d1462041c0580d41882514010440400c01002860740c000c203010390080f0745070810981d443c240301d000d00410030340000300da40e840c490202e005455500201101c010344031000c51200115044080b590700143d210b04c1030961520400014001c00d031140b5480300c101c410040c04501c4003600804d00d00c0101030b0005080003808030006000d54420b41c4401c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 79601404 1250 79600154 79600211
    0x1204031a060f1801030c080d050d0203060120030d150b0405061617030a0b03030403150e251802070302071502070b1612020606030d0e0109030b0702031c0b090a 70
    0x1a81d641d018081c0c40201805d0200322485c0f8254030700418802c50005070035814115941c0d981d1715200c0076001c00c4010390000b41500d414003101205580503403402945104401d0b010200135511004102c40800c103075000341d60141c120031001c500500904c5094412101901e500369005581c0b1100c80440711a65004da01d000740440b990308446c400c1d01d0407000015402804044010301518ad201000c0545a201c0c034800200411001c030002c204d4500940c00c2140640030a00c01d48220f40b0b100080e03517003142d11032041003441150b145024047e000c081080f42604000c9254110b0801031240e40207961020f260080c0c41d0320840601d0b00d501c5643c801c00c464070140405600240d1122410004000498800041101c1b94003500031105445880024003901c00d280050003404030400445060320448200d080c4030f81007000e84540840072415215591780208041c1e801103940302a0000000207920354a4241903a5074104400441f9603901e004440f41c1204000c1ca00150006082c1c200c3d005e40c101342104100f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 79602654 1250 79601404 79601419
    0xc0d0302031b07080708010606050901120b030d05221206020304080d06030c0e09030a090e180303100302040b03060903120a270204050703020c1002030405010209060d0b031204031a060f 81
    0x11000d40429100d044880303001c2100c14286d1580300c890f09a5000340208000500180081d565640c42803052902c0744002420024541e80220080f0b8242442000781e5008914009420302258503115200c1d000c10501c04101803640382441d40d2600c19114010028000b1600803001c5403c1c0301400c8101e4129640560080104503503d2801c2ca201c054244a002071440d550000a10350a901004075800072900d552424949402c1001e060072070400600300b1105081b0309000c40803004010001075000742441202e48910070315510401c42034844954565000ba0040001d101008100000b601c007010154401050540e907402e60081c011704070340581d01c07446031006407842442c0007000140c032841c07802950240090b5490010607001d03485090100b0417207a0000710300f4660b0111560185401c20f100e10005031030000c49000144903030f0401c0015407072160b80c5400c01c0e0703c1803a0412101c82021400400c050800b8919107600c007070f00701c18040805210080341e001511aa0b0741c00031281c013442c00200783c4e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 79603904 1250 79602654 79602697
    0x1208030a0c0306150c1a0705090d0c0b0714060108010c0f080601020a020901061709010203090312040f02040e03040f09050c0306010323011403010f02071110090504050a091b0302030c0d030203 84
    0x1d00301610410b05079440d460306800b1481c0303401c00b1b14000c0d10800c85501c41c1441d044090060111551090005555610000c00c002c00c1d00ea81c904020000140100c0e003848800d0b00d083c00090410300180c0c441000c50780b42c050b104c400903412403e035101c1d91000342010f069a03503503100107038240510100002d511500b100000314240d0742100881c1809201501c1421071655450380c402c2c201d01c41511a260310780d0040c410101005541c41034207074400e214000c40c5860512603408a000d455034031282c01d0860304040340a01c5900102d0020f00003c03d5030310018805400d200410b5035081c88094030440c10551104000681803184884103104840c0f1106280c40f903603910300c001c507085012030885900c29400c00602e509000c09c50300a8400c401d8114080c1d189020300c00081240343c058a80d14401800410480011166660701c5070510401c0505404501c1104034a04035142414140e018144616402403c0c805602d0024440044d9001581d44110220b1241403d0f0710b0740c02a1040c656105655000c41e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 79605154 1250 79603904 79603907
    0x21507110d0b070305060a0812070302010216030203071b0308040302120109020d0605010602010b010804080307050a021908070b0609040506040b0a1116021011030f0d0e0a1a011208030a0c030615 85
    0x56203d008181d80400c90382c0c59000801c850344400d4410380820358072402c000c1200c02150b90090164a2003800010b260884289282c4104c000410042d000743e000424180d0034442c9499510420054504842744090704543e541750590184c0d01000e8000d081044030000108070035400002c0c4036070000e0201c1a14802450000e0140100740105030040d400d15006101950041007900d00440d84600d55a095a44000044849030030810b035050451141c1e00d01c4d01640500c416a0710300d00360042e49455034410450808070030003103014000c203002e00c249408000226001084142d0440d511451001c141d84405000e20040d10780041e85006450700029003512100e508101c00700d4881c8203450406a048110302d05980c0c90a484401041a400070083d5040e00018140100b100c5090700400140300c1c20120400f520745424200100c81e020349241d02002c1c1003003494055401087c0c00c1d03c0848158001c0c2e5034042039400040c0c240300030f40761110100a4594020f03000b000184c500d41a0015141490810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 79606404 1250 79605154 79605173
    0x1a09011209210309020f0d0606030b07110d0816030b0310020c030c3f0d021c0b0406060c0308130f030206040308070507020901060c0c18020a0219021507110d 69
    0x1060001082c140911001041c00b83c000d5038802900182060100011030080c00203810f0134000031201140d88040210002c2d0b000300b102401a00c4a590740d0f0044000710000502c2c004030040304806000380c990804c2414104d2801c090101c154034540490304464400129160403404010004407900214182c1e401c002c0020240c18002d0564007100c1e030166003401c00f40030032458807641c000e4054000f5403500005000503464055603450314600b40c03274070140d44074910480e00190005a183c0641c2101d00c9098441402190a800b200b104e08000082ca0840040c2030080021300090610840780001840000b88091200c41180c110303040e20030440d21031400a4596a04407030441c04980c0d1440841e83c51446481540d1b1580d0b4090314002c1c5990800c101074034810101d800885400c420304802190448a10507402002c403002c5801580725040d02e41c0103030402070f0203030342944d800103200900c2c0056034403001c0c94290b0a83e2124840e55503081800c0c83c03400c00d02c01855140c6c10008800c48032003040007810 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 79607654 1250 79606404 79606433
    0x16050415090c0f080609060d0b090c060a0507061d0601060f050415021f02070c03020f041b1107050402070510020703050705030a120e0102030601081605090901030503030708010f1a09011209 83
    0x292403501c517079100300420a01880640b605600300b070303140040704005140003003082d40000c005030882c1c03c0540100d0001d2600d0b44100d0b420400620003255480800c20680910b040c1d41c488808054007044030035503a00e5503004140700358820801103004103030015018004607000351541c0140644800ca40c188081d41d44c4030321003c01040019030944101c0e02c0c4505109807000b007544104541200752641d003c0211030302a820100c3d0344169200c0460240c45180300309101c00d41d500352203561130090f61a0f4003e00b8011190320a40c052401080a00001003000c80c81400b0b550880d04010f89905041c2411141e038080e0356001000fa200002d078021203d50408120300140511240c144205c00700110000c1c02c2c1d00040e208140418100c80114000f5440b03010700c14014002890038a0030002c00070000ba598800a80c0160740a40000052103141d0f0742c060308031800341101e41da40d006001d18101c5a0401e82c20003900b201507800c004209240f142c3e120b2080c0508403424584140041c100394100003030300d500c064 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 79608904 1250 79607654 79607657
    0x30917120601081501050d02040504050a0b041805070306050915040812060f06030402010c03050f07030c020312030108060103030503191406040c0f021005060301060e01030b0f060316050415090c0f 86
    0x110004019602c5070b00300318410782c0301c4e0a00c440741d40700f050015991a00040006803509409000c04a85a2a5480b80511952507543d01045503091501480103e80c072601c0d50281c4c4540d1110030101140e0009501d404490b482480040e059444181e101c0c10869400c81e400c108071849810f01040c8880c150182480e00321007d05001181c440c02c0030407a8901440a10a070000c01c05d100080256020b40100508607001741016450145050180302d0541c0c403551085000c142d40101880950504002c0803a0041d1300150061655040c00c0413070390b594605100c0101001000400038032031500b1040d800717043300040310341801384590040c502c0034481001c480250240b45003e00c2c044c9401d02c5141201041b080c00c1d00a0003078140781c50f01e0308014000040c40150190340b900400180307451100701c07185c000c60040c0b20684080c03c1025041ca18100058200b61180e8802100c2d502080d4040e030302c06040326402c9800007900341641003403022042440d4442c4081c24500822403080942100d040c10340140707103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 79610154 1250 79608904 79608937
    0x20a0207080601080a0f11120106080a0308011208070f061104061d0301060b04171203090105010f0902090303030a0203040201020f061f08150a0905031207030b040b09040b0c0a030917 80
    0x250045103036115817009014200100a006107008180d07240e9800610300b10240400c0c21401420341204d007901c2d0309900100c105da021000ea501451b611104d810f000d4120094480d503030900c03c0d1500029401880350203010b4594151080c4200000c41c0d101c2d140f103140f12690a62115521034000d042058110040100b0804520b0311807110714040c8201006c0d15a0f01d0070882c01c141c20920221a4405668200551442400f03a01070001b00c3d0079001c7d500c120700c60740c00400c59604040c0c5151220f5400d500c00e448090040c0b144020765600801a80c0d031049490200507125562400103c1c540312040c081c3c41c0043c052603041c400c0c1c52000d0b40c0c0d41000040000620a2010742e600c40c0c1e181d80c0e60381064188a45108000401e002c1d052a4001c1d400c0c0c240684101e07810000ea01600d502c0d1b18605648040100386e0380d240f5002e21381003501501d1003c007000c841640704d0340b41036203841c0c00e20680208242c0a000000030f03e1020307140250701451500760040603a600c030f0301c00d507900c80303d03160312140c80c0b036007004030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 79611404 1250 79610154 79610159
    0x4091e0507031e24090b011b0f030c031e030603110105072001091701021312050604020d020310060b090a0f031a040303060e09030702040b03010c050405060f0d020a0207080601 77
    0x90180904181011222104807015000f0000040299008030707410b8181c180d10703521980403c0040400500542c10b40095075514a10024040744154221550700707440c020300110200b010074040030325280e0076080030b40050586180c100c40c0111402000b60303c003000d0300725155042c2d03450b0f40503605680c07003110080e00100b10711006403014040c1c2440100011000c0140f061b8011003903540016110040c142840a1500c480c07140c4903400c000304803031503180c0d40410700030700e040e603000001401000e010040c28241000703505ea10740c41d0740300100042c3c020107000c064801151001c0100410b9503454000822410f521001c00c100e013079003d03440540c481d010045d000711311701080c079841004480d40140307410312110a05c2c0000411341e400a105600341640c8034000140041c0b2820403c0c868001800910303503c081900c100002c4641c4aa8910700982c17420314410328158105003200c09590086034025140c81c42200c00300c2c2280b0a01d86130000a60011944086050b000584102034072894000d8400303580c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 79612654 1250 79611404 79611407
    0x3140c040f0218010c0609060c170f0709050d0311030301091a032b02010b0d11011805100507050a0606060e03060108010203070203030402042a050a020f0304030c030308090304091e0507 81
    0x500da516085410140081490f10760150380800315162065402041c0145e040c0c55032400c0b0348103140c00360003141850b901e2043c0c00c0e98210b1260352202c2c00e080b20700340d1403e1002000f480d500003400742500a14100b0039503001d041c05007035031120614003082225a6981c48042482c05003c1e4410b051030b1480d12501512803e01c0c011640340081d140d4100303008400200c404c98544440c190181032002d5541e520307580340c207a89840305044512030082035901c0720301381c04d20f000403e428585084941e0203e08180240800d655544d4404103a40b842c2c40c2481d114481420900d0a03c4104140240520300e40440021010380106241035400703812426148281c1c1e82e410214283e00c0b0842e4504016001080060700524083c0c0c800025509401c0c02c4044105405d4100500040c0c010150340215001240d170540103070b8100120002e004581000d1400c1c0f61440da40c0032026162404010300344a41000011640d03041003040d1001404d400c2c4c0705002c034401c0608140c18401c0321140d21040141018001005903 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 79613904 1250 79612654 79612657
    0xa03030204260d030c110a03020307020f031902090c0f0d05061212030105011202040b1210060908101109090a02130609031e021210142a0d0603140c040f02 68
    0x7801104007410801000d850704500420714485040180400d819803400e9040f03080000310f980311b21032780045d0342c0c404903030042100031030007081c002d48a5800392002c10f48080070340e840d040303c455054620403116150232250038040d00403400704404030760011407019645181600903502991003504c1000c070302c000007140300340c4801c503600500c00d003c00c041004000743c0d44230b01da4283d00720099020040c00c041d101d17481c25802c0d9001402c8a001c0341c0b003d500703008404a14102e10301c0240303100c1c103080b00624900200c60340c0301e00c181400d00e01401d94403201544220741c0c60044602c00340c1d006007142043c0c03603c500414029084aa0082c010082824000ca00940a4611802602c1c0c2255440802c1500c540c85001c2c40f0b0004182280c110301d0000c1800c4d000e8a04101d8012280c110740408a402000411600c1c1c00071801810003a050015040c07a0081626092004480d44008960b40366140340024403603000e0041544020b0004584c1c01b00f03c21101c20211301d24000700c004513414000460014038941c00c0c0d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 79615154 1250 79613904 79613969
    0x3050903011a240a050c01020d020c01020d05061f030f06080f0303010303020601080c0109150c080d0209031b090c0a110601060503091009030504052209060c020d02010e0303040b04140a03030204 85
    0x1090b000c02c07050b601301c0d01680c090700c0c018003800000340c41d148030303500c0e110103a0b0001181c90a041e074010410803010a032500400e9030006050303503800c1425816004d03258075030b18100d01c040700b855503805060700441e46c50780050014041c07110849140744101100c840d0b6070350007403006900500540c0008510120701060a4542402c140d440c004c055050406864030040744482290600880c0c0a0400014800b40041c2042002c080401a22980002c05043c2405100d400018810302000d01a40051382c2c3c103040c00f60081509001d83d81c0340c0d4039034002529500139200321344080f80b159038000a00142c2c800015031050f60b0320001d842030704470195a02b006807940d400004001c2030082c4014025402c200c0192141010110040300203400c111420404607072400100b40e841c0768803141c03e4007072250108400f41c107100d031a1000308111444082003a4407408040e0006061040c0c000205085c40360220051380c402c041d00c1c090720944843c6140180c000e600c60710941c820f00c00c80e043c0388c12201c4d001030000d803103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 79616404 1250 79615154 79615219
    0x7050f0607020a0809030129101107030b22110406090b030c2215030b060306041a0414030c07050306060f150c030403080d0603020418080a0c03050903011a 68
    0x181c2496581c4d40319415044141681d42565a840b01e42e40798080260a00034140300040020600d42802410f01200b0a40c001c41c000a0045003498200c0903400001e90008070307a000794010115440b60340510306210701000c450780c0c220301c00054010900407401c68694040b42c04035070800c0315650300e8041c0070640d41d61856003035143e040710440200030b04102e45890100c1c1496191081002503100ca428200ea160300b500d41c100c6088413a0900401c0b140c04441c030f4018004600418035442c041d0b03560f0307090301c41e01c180641140344950007080c00c000d0070700d5856060700500400d40340c54200c960310081e40e8803a14440c1510030311444003c500320f810701c000411201c1e500648000003040041004085607441107090186520041200101294412001d807a4074100580082915032541c01000103403440024030202c0003042d401402c0c00030305500c003182c044a86a050440c3c02c08118101a81c4600481c000541c155007000c1c0e5031458000da030110b24096000480d20141a0315169111103500d903a4440c2c042d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 79617654 1250 79616404 79616413
    0x5010e090406150b04090608030309030a030c0302090418020915030a081303080c03070b010906060917011d030c07080321180a0308010503190503190302040504020f07050f060702 78
    0x961a0600c50502640a406400e011070420503000c0040300e40403042d03003c400710f140040350a00540e009401200003c2c51020300660460902e02d01c072603100d11550309000f0900d030f81d603600400c4860003a01a20440c032802441040804c044c4610443c80703100c1144100e1140d001c01002509280b501e03080080c000d50b0103002000c02e95116a00c0c40d81399440030259001080f11640000300203000500200701c926107071009903440d40c0031460f000c0d00540d0b060704000d0034035050204c00d00009512581c00c0d42155140040c900428240d030107094014039201000c0c802d0301254800180041500000400b55004e15000b220300c1d4599502c1800d41ba03000708102141700c184940c1080c0c0d81e0102c2d1101c401c2d081a001c5420307400301c2920818281c942410b05a045012442407401000545020b20603191400580d81989075008110b41c5c6840d1640700700c0c80e00c020100104c61058084034817990644001c0c0c40f000c1d00865460b1480544252a0340025000300d9141c0714801c3c0f02d2044c400e002c59518003501040d0002c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 79618904 1250 79617654 79617677
    0x10e011103060d15050901140a060303080403051804051609050126070918090317040f0303020a09051c0c0611101a030d031509060803040e090a020303030103050102120f010501 77
    0x1151009081d1004d60f001c80b81c1106048a818252080c18000e82001c4000600c08a65610039126820014400c0150381e16150003000869000b9500e039a02c0355062400356541e10080b401001c82c5502000051f40040c42c0100b003100e0750103403000d03c00702414070b5100c3c1410a9650001100c0e04d00c5c0300000c00140541c040c4035941e620a440c41c96540040d00d07030a25541407030f150719030708240314500c9024144260b00d5003180c1e018160000411050142e440c840b0f40c00514103030311031085400c2002d10003000c066002903454100e9202e45130fa0320141900800740000e8444480c001d06100280d50030948041c000c1640c0061464001c125451645021801610b0714800440c1024000e10343d4200303040c106068079142c60741907541480310550401d26a1400100c1440300d412407076179000d041e040344100e01e01d4605c007403100c0500041030ba8111800e6200c6503040f40d40b6850002d0401c2c07a0000000d4142c440400084200101900039020110910240950a585134404803601c1c0c1c4080c40785901041c1e42e040e69 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 79620154 1250 79618904 79618909
    0x30106081605040c09080d1805060a05031306110a021b010323040206040b1b060604180209150303070305040e0601090e04060b12030c010e010b100e01050c0709020406050309010e01110306 82
    0x44d0b120216810111401c80d6264181800d0515400c0b04000048500b501c3c05048171312000c1d5140640b00c01d444040c24a210750780d0251074cd10000d0702c01d502c245d41c104000c81c100280c41e04500c0303103042c40d600465110040401d010350b0710346038100c2d0403440010080c40001e141d4802c2c442c0030400d5003100011001c040c108001c10840c24000b40041c1d030000410000801c1d0314a82034024002440030110416401480540f030504000000e010244142d09059514104114008103a1542d5070120b90000f4291290514080414001c480c01a01070001240c4030092642090280049031480402c0c107c095550300011503901c20755000d0005443c0c2141c01050208035143c0c0300040485015002040001c1009040745c0746800c244900113250b9141e040742c007019442802803121107041903404080016840101801e8141054002410020041b031400b0300b150007003000000038220103070115034481c0c507580e000742650f01c00c4440c8072903076080100c104141d000500c9161324659400c0355650864840e5000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 79621404 1250 79620154 79620161
    0x405060103020904030315150305070201050f06102003030115020724050918060a0902030105130b01021204030b390f04050301020f0301091b020703030305040201090e070e03010608160504 82
    0xa0317080580c0c402081c61040102c01e868006808000b102126103030000400a0544000074445c0c802c690518003400000130501e1036240d000036003164651100050302508581050702d00c2d4501c1c0f00590b01c2000723081448400310055050324507100c0441c40200c82c48605907960f1065200e02c485003c502584603169260004454010a9103440d05501c1c04400d070340000c0c03800b41110381001d40c036680d0600f07109091410049500007045c1c603110640c00c0d585080300040304036a032850751002c08d40d00c42140d511a82e01c00c0c001402d07486500c07114691501d899081103ca528400c5030141c02558041c0b05c103225020000030020a0054400d031541d1030303c2c00f280d240e01b107913401c15102c249000c1c070140404600d42d40c0031300240c0391507180308110070780303d602d0080407009941454522504c08580816540c00300c03580455402d06991f05800e01080e80e40300d91004945030303079455012140e480101d105000c000d03a40301580c80c0410754214024040301da100c45505031a40302d0403002024a20000c0c4041060b030800341c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 79622654 1250 79621404 79621411
    0x703020d0e0312070801120c050f0f091302040f0212071107050a0e09070b0a0207060327051518070e060409080c03130f03030e06070f05120c011404050601030209 71
    0x800100c1c88841980d20185190481c10500001c0a01c03c41085800b50748400e000d401404000d500e074603100500d40301c0b124481120300885000d01d0074004c200042d130720388120180407010701900d5460310b4900106084c0580320341030000c0340f01d10300b401d02d86a202c60b0790b4000e0b1607003c0d60100801c592a200c10801784c980b401251503415a0380a007840c000f51540d520005030000b02129559246a850244081428071506401080c0c00c410b09002010780036500051060542d4018180081c261180034100b03003141071500e802c0141c0c101c1184000f41041804a48141e0001302c001202206890b05580130700c0203461000a1109030348030301020040101d405018640140020303200107055640c6403204005917201610035200d03030b400099203c041ea0040200d074001040107150a804140c00c541d0000e080f030342c60610061003032801041d0755052048034481046d2080c0d00c00221900c0f03201107001105290003006020340994a03100d03420400d8591454142d2040f607201e005020b0b960700b19820040c100e803018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 79623904 1250 79622654 79622677
    0x10050d02030a05010c05070209060d0b0f09010204031709030d0305010509070f110a0c0302150a02030f0702060c150106230d1509110423030a031b05060f0406180b070302 74
    0x64142c007002c40e60130310481e0035480703590b0703502543c960660061004a040181c10240910001284800807500014a5075001a400000d0010544a0400342c0d030181c052900301034015040d85c504001c00265810090810300da05806983c5090000c090580440d442481031940010064000400340d0748a803a010760003203030a081c00d8071110040180c0500e04100040e0443d240d0304000e80900135498015100c3c0c90310b0034800c0f00c0320701c1e0600038900251240200854100d0700c0801048400455844000b5141c0d4500410215807403040c001c891005021028420030f00410b52000762080303071801c2805402050440310419900c2e140510800e003004000950050030741c1e00003648041107140e0070f8000c131107070084100d6200d0b0b05c0358140078080041e01101c02d07034031005c1d01080c07104a600c3c0d1030100d40951559054100110322013050350303510064141e403810081c2280160420451289009050280200c0c083c1504111032807808080c00703032422821001800c0c0e038412900040c04d151294004081c10b4960 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 79625154 1250 79623904 79623913
    0x260712020904060f0806060102120322030c0203030a1d01020309010c12030908130501030f09030e010807020111040f03140307051209040204050d080901030b040b0607021314070c120810050d0203 85
    0x19000d0302a81020681c0001715190000340600807650390410012031101a40c2800343d1650a1024000c041c103107901a041c01e44005500780c20042c1400343e00042883c54014050b6540c8002c514001040d503040904250850503442e24110940c0d44000261905114186c45400b54000341d5118503c100014003100c408050b15031200300000360002014040e0f0000d004a0010141c1c1860000f5040d0344021311800040380c584440240481d600c091500190f0b4020300308160151155641240036121441070600002c80000e400580340040000d144216030080f110000c1054440d483d1646910407040003a055a105910510108020340003c094403d4010030044c9041da50368003052078560f404d401510f080ca00403400801c2540c240c081c10001034001c4800700b1003000410001200c5025008001c1d02501355582c040340d0146440d806415030241e16015602c5074603100c00001c000080c06801100d0503003481031484a11030050700384a024040c0c942c49914250b040805100c0300488020050364944203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 79626404 1250 79625154 79625159
    0x9060c080c0405130203061201061715040b0109020904110414090c03010e060909030408060a020406030b040504050d0311070b04121e0e040c05070c0303030506100e060d050402030f060726071202090406 88
    0x13023407140d22b00604a14688040700e40e00c0d0740b249400c00a11751203c912014202c0304210004d040112050306407078020b0001620761031184042002803c101149814031400010301148010f0380e541da07090b600c1402c8404050603900d030b0000d0900d9000c280b1071408003509e1f60000c0380356407070407000d240d512100000442e810203039030340c0d04503203010411f80e08907100540c002010300c88181c1c180244411602c00792018040f6003440d5684560f40c4920240c5902010369804031515184110300032a1021170304161016034600f001c0c106440114004d40e40707080400c90803654620b0520800402014030700c600d0b01ca410403889071400b8000580109094030041010822115000810619041000e58025540040d0031702e4050140b00c0c046103075200402c20f00440044081c1e0030384d00c1404440a8020f810000702e455203072807000c686481d45c04400360695014100800c04203981c0300380c01c3d108056000220629070000c0038a00040003006480040018000740124010400942c00411903d003001e0400560180e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 79627654 1250 79626404 79626439
    0x120507080a0807030c0c0506160504180501080606091006140f03070201060807091401120602090a0905060f1804060504030504080a0609060c0201021c05040206040909060c080c040513020306 83
    0x3884440c8100100c1c0b0100180050150701d4400c080c0d2020302d904040c038007030341252517082d9074220040c8843ca40600400c0002c40842c0300348161001001510788036000790b85a14001c101819003401464180d104001c009013252404642c6980500c2242590444072402c110b0203d17a0007840510001111038200b094078030212064000b1880ba8150350300008806050aa400341800d01c240e00140c546030400225141002c44000000d046659403544c8051f0030341649458000303400342e08034440e84444014000a82e2000d184c2201d031082e10b00b21806802e881d1329504014000540c0c01e40302c0321352880c190004002075075551046800c18040c0c1401e90a090ba1060294900718200700308440f100c1d150020701081240c9401551380d5200c0b50300080d820078980700680000307148169401d000303040d2920081429511050112806020b000e5400d02c0341043c281450805000d82c004403a00041d04040092600d1006005650542c0e400806c04240f590701c0d000c017007004c2c2d000944003683c005c1c40c5052604100717 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 79628904 1250 79627654 79627657
    0x7031412060a05040219030b0d08120f0a060b030c09010e03070b07051203010b031306060e0a020405030c030c01080604091406181203070c080703020102070f080301050a120f12050708 80
    0x2080c48a8a420315116040c0702200565902584c0034500602c03505a07140c02c2900c90211070318091a0000b100c8690b280001c5035000c0052003e13040c05c2c1b0004564145d640c04800080c03007840000c01e50141511003041207411a0190701c54214906028400300c1c3d03c3d0959040101034802c41450210801100310f40082e007040071aa010300e1510400040c06070411078144403410f0000d0045030110f003190f142010014040c4002402c41e80003040855012040000d0340c1d0210000e0184510808114030301406004025403107805154800d2180301210342c510f190000d000700038900c042e540da810380d449040600001e001c09920807901864003d8609030a00c100b00030040c0b06024061150103104803114040741401d21a190040b90404104100b0203150382080c410b0101a40c00340300d142c0c1c0c801c07281c28105d0090260035002005482c0c4142104144000b1501441c180c40084423220741032a980c140403100501d002c000201020027110220300801c1022850040201480c100349203081c2040e900c22419 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 79630154 1250 79628904 79628917
    0x10f030b1201020405030d05030402100c390b03060d020f0d170a09080a03051e04050909010c02060916031104021c02180a050102060a0b011211041e0b040308070314 72
    0xd42c0c3d07010408100e40c0ca0300300044041c012130307400c0442c654203041c6c002c640304c022410401002d100c0e10388085410803c103420005216000e80d8031800b107888184464000f5805003201c0050024000c48006c50461010382c00c4030b000c6c00008080c194440e030584e09006100c0444031080f64000d042c40c9580c0301180d640c42c50070304038240300f18600b40c0c3c496403030b8400307410410a900401000da205580c3c03000001d4100045540600110551035107c0072046101d0859102e190011500851030000340200d1040c150054002d6044039002e40301d5950325180a542e869032501a00420401c40c000d040003c10a40814490b21800c044d102525000d030301c58654001180c558803030801d155000030745440c4940700c044c2542d2140c00c1101c2019070180b421000079601c8402034140b1040c6541e484210503e680103045400180103070010900134000400b482e80e4864016201d80a1280c070a1114842c13040c8580c441001641c43c0f40410070f0070542103841d06190340d04140070032410302c082d440e01500f200030f00030043c1c102c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 79631404 1250 79630154 79630189
    0x7050406030b0f0f010602251a0a02011109060406031a10120506010203070b0f0604060e070c1b05030a0311010b0d060e010b030a0c06030b030304030b04080903060c18010f030b 77
    0x118100201d003500f1904005150b1004024640018004654042800495010450480c0300006038101c60444501c45c0e43d44038943c5500641c81560b80102008058a580c5103150000c1100e00090340d2140700c02c0c40b40519190384204100000e001050081e0f001e00c20020180c0e43d80401c1160603800704414810300e01114010030404881d05103065141e0180b298065001c3c0b02441c201103080d610758a1100024003d40e162602000004803162210b5016030020a409407021a107410b04003009090320406c02030640d541c020700c02007010507032081583e000850340c1c040e0003001c583c89251070484034152008084c121039500c4030381c1c0388001c8d40e9005407641900d0040e0f9002071026410f125981c2102c0340001c0070f5000e42c2190f0b008002160704410014125045401c010590544241c0024254815a000203011103002410700c07062140d00c5e400fa0800c414107030111503458881d045011954041c8003440c1182c4603400140c015194800c103514550185d144c1000300300c6000780c000080954101302c94094 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 79632654 1250 79631404 79631423
    0x1e01020c060a1e06050105070201030b0f040507030e19080304020d08040b0304110117061f0309080309030306010201140108030403120c050a0b100f050f09070c0c0303020706080106031406040506030705040603 91
    0x10385403180000c02070040003d22001c202c00e070b20706000640340d0300440002a05165549245245607103507000c003145e039400020403c11242c5041c2d50090001c204039826100700380310352442104c0000d941c2e848542c070306420a0100b07042d82c0d181d600b000074001ca414000c4030301c0102031100181c07400b5000d02850007030344550007850300c00890ba000101522103800d1088008441c42d014001d40361145201d04403140b988aa100940e600c10030800d502400d000ca00082c02d1031400010010100303404005140221800d80c0203000e6100000200480c0d4802070140c403845400800c004c100003034a1501000d6145007500304094140a242c541030308113805c02d68240ca08221450800214910f07000700c55001d4410410200d00190624020510b00c1c000035003058002c68203a804074820501851000c03402940c4007407452811512850000d450f5940741c03048101242c4542c002150300f5019009a0703111340340b20100d8003516501c0c0e10400001d04406001c2d56014080c3c7c48000c01d490301c0c0c0d80100d00285003e0307482079 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 79633904 1250 79632654 79632671
    0x12070905030d0503010605160204020906120114030c10121e090501060b03130311101506020601090504080a0804111002010e1e070506070c15030902040e070302031e01020c060a 77
    0x181032402c40001c0104204040005000a50f0420141c0750b0403400b10001e1000000c8a20124000788650658190702210202d10b004071106996400c1d8140e034052000e00d505401c01c0030a242d500c03101282e1880e40408594004942c4c18400d0340c002d09503502d504000308241408500e01212181c22985d20340d001606c039240d14060210900900d00244940c01540345145441000c1024900240800a08200d0400702e840941c0200f040b8038880d115551070308020121550307050004201e002c0c4500e10150040c800009209522442550711403074200314124030f8802e96035401c80360030710010401c8614005143c80c081c81c0d5115038240d000b410b80c0c2a000080d5050361301104603e000060007080b4400021079800e41041080400c00c0f4003103481c25a440b83c2c60381c0300e0745080f04070103c082d040550b0600c12041800c40b4203625411591400c2c3c001c0d14100120000486000d81b900c3d52400040d405610407240020340201000e8418188005400014200b03142480c500b07003482001e8805021143c0c030788080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 79635154 1250 79633904 79633909
    0x4020406200c10050a03020903070803120a02070b060d06020705010f0507020106080708030a03050c0c1603150b030d05030a02070506040f030e06041a09060c0a030815060903030414040212070905 85
    0x807414031031001002030082c0c0914400160b0444002210b001c2008404620b840c0814045c0d0140c403080400141a500465260310300550b9903041120007000300c4100e8000f0880121080c0708842e4203d410a190305000c0d5240000d00c59081d001e0030301240c2043d42000000c0101d0b90078072130000300b100e9191000c10b140c00c02190082c25140107070000101ca41044004025600b0004101c1e00608040e0801107403650718903030130b15114020b601019009000742d0690030582851241410181c0784a041e98920700041c001070f04080f2330401599a8069212501c0a00c40500a074095039000d00b0440b005441d02d50300f595064281070050303030129440708000e200c42003015000b82424104040c01d44509062520340414440b6200c9030703140784647c2010000b0300700443e44699048582d501002d100311090102c803440e0003800074400711805c1421402042d0031200915103179080340c04078000280112700b064240031b102981894030b124240e600079402c0060505a01007410304d04e105d2040340d120514510700e443c05 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 79636404 1250 79635154 79635197
    0xc0801030c081506190e0c030103030216051804060b1507020306010603020703050403140a0605090607030c020d1d04150b03070f02010203130809190906031e121d04020406 75
    0x124441e60044600c414000308100310441e80100100c410f00c0189003581020310032101c0a030001d84203590f0034410030000080c1f4000540c1203c2c0300340d080b0b81603452a54000751005c0310038064250711a9800840001d0082d04000480d0028060031000511603514000521f00505009041020030782c081500002d41c0707800e01026004203500e0405501e0101d40e650014203500c1540402081a51112806036510b03108100050030341c2d90015040005061003503403d0b44e03c90084801c4400070703081084c00100e451006c58000c0e01c1c44116120445140400c4564402c0c00170300036112600306941e10380c00038540034000004c10003402004100341d642d00700720300014035201340c105440c415603004009000031110408042c038011134100c00388644480c1c841c0e000400c004d03071132b001c0d4030b10400301c0150110320038419a0094003205e20a64044140b0601d001c0f0000d004084060301611050f014901c15018034001c904010b50100341301c071080501440c0030300180c1260402d0700007400050310400c03441c82a590901 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 79637654 1250 79636404 79636409
    0x303070306090b0d030c0b090102041505030f0612030a0302090613060503070f11060601050903030913150801090b070c0c0b040f050429040b0303090a0e090625030b0a090c0801030c 79
    0x71885150704e126a24060b004460821000f810504000300185100c1380070b5055901503c0d00e000c81c1203401c5088170b07000f400f80d0026280f00304081c03548070216000381342c10807070a90101d01480155050455228054000390402c951303040d0020020000034141e035440c03070482c1d4054946515610345034103100c84010720041200c03444105000c06a140c007003c003440002c1e000e078000d03424608140d64021090100741140101c218080e0400040c00c4140301640d031030b4000040d09450b510406d0300545c4d50741d14042c280c1d190b00e400501048161004501014401c1ea027405405000300303002003009540d003034000c142da80244d0041030f80038140d4500741722618050103895201c565203075028400402d106071000360700441140c40c40c4980c1c0c6d228062502070b28284191041c1100c001c005100c9107540c0d40c20b842c00b0003012181d032340e428003030080055210360840c420420545810001012a40e000d082e05500070401e02d000603512040d42503000070300342c4850081509011003507558000ca035265240c110348000d002e4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 79638904 1250 79637654 79637659
    0x703051b010c0507120305160f170a0503160504050a140114460309050c0316030f080f0307030e100b0310020d060803070f03020f0105070527030303070306090b 70
    0x140707100d0700800c4000130a04107445c2804150012040e6901d000d4800f4868000c1060010043d15094810712170401c0003e0300c0140120003001c6140711341241c03109075100b1000b0190205109102144080c00355000c820000400340c01c0035480d203034880340000d00c81c441c3c0d5800a0100c0071100b00318100b035603000c04074003101100d100740c0d2410702441c0c02030091520b403c0d88002075606d40c59544100f030a4404100149925009012010b40c0701c080788004000c1c040c90082074682e4405c0c83c401031194140050714806084c807117185001d4203421a503411000d01c1d058203050b079a441c6c0030320140c0898500308008600600458800003410020f5030b00482c2440c41220912991034981206c1c600c0d69100401c150000c402803100041c1d441009295000043c502e0b6085a501403001091000400c841510003d905034040c1d000c403002c040488007150f007642c04c215028400180c1c02c4c0711a84070700c4140001c41e080400840300407841d540740d5001203403450f0000c0340c403070000985919040000b404284902440c140c0309 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 79640154 1250 79638904 79638917
    0x10140306010e040303020c0a0206190305060609060a050313060c0e01020c120c060d020708070b0f0c04030302070b0903030d14011806050a03080c070801050106030504060b2409120703051b01 83
    0x10150980b4420074020005014580c001503c4510b0710b40900c403080c1e60302d40c000c02043c0c80e011506030301c030200101902400e01091421010498500d0300c1e4040d03821404006141610301a40901c1c1211140c00241c1801060f4003042036240000e40c0501440020083da0794440040002d1480024500404039425600560021600d445084804250324014210541c2c070981e445103d100080000d11a0100c080c010101c0440d1b03510801c24a000381e00e002e0800f5140a80207038a07080300c001c8051183d84002009030340700c081c0401a000440016141d01075009081c1c0342018400d0320008180d0300090789a0389001c40761401070180070844445450351500850301004001d0822010500c0003286000243c000c003000304100f41081c1c0f0030813040c000f41003c940280710301e5a64040107400b0b000d050343d04036001c90401e00d0030f008070b00700003964488c40c2441d040d800c030004240104040e0703103030f00c40000d15800c000c803c0400212002e0410140e8010752003030000344180c540d50250551181144250b03d03040104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 79641404 1250 79640154 79640159
    0x8180103050610030b03070b040e010e1b030703110f12010302030d05040609030b09011b02030702041b0f08060310020a0c140706080f0c0d0606020307061506092105061014030601 78
    0x4914842e83c211503c1401d000501c4c00e1408002450681d00743d0018401d4400001e011810b111040c0d4201e04030307900d5035080030845d2280b550064164058244103000d162040c40052030080c4a500200700a4150544103450300c84914254482a40007134101c0105c1c00c04e05004008600703003040704021060301e41c60114142030414100801001d451310015015907680d4021660204082d8408400945480070000803a6540c010181d00c94008040a034840c0d454080c0a5400284000329244160080d07541c3d8182da4a50b000c040e1802540038141039003510441d130214079813551500c01020030500750303125281c4120081c580100c94100e01c101100558010303134000c202d0ba940204500382c00c101c104190b440c055665140c1c045950160f91851954603043c8040043d001780c000c0018860366000303020500c1208400d8011080e010030710f200d010000340b000141040354103442c0131076144035000030b1003054500e42d190315041d18114051300c19010300c0381071488c10031681c90110321181d542c0c4415000741c03c0962 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 79642654 1250 79641404 79641409
    0x60c060708150303090f04020c01090f14070b0a030218030d0e040b0a0302090402010f0201020d11191d120106030503031f08010e03030a0c2601090c0e06040302121207081801030506 79
    0x105001d05004001b41c0700070300d45503512501920b0510301000b00030044815142000002c4003c070204c1076072102e05980740030300449404121f48040d9140d00384481d1401000c0030044000350b00150b101c0c590410486400300650b075090011030801e529550301c00700c40701110780c108011200c4080c503140c41051441d208100503200c80984a80c00340e02420502080d4041050690182c0b01e0076210038042407402e107000c90720680d524058110300380b1030780041150a215040a440b0700b50090035610315040848100c103901c8c604801102041c1d5000000421060303601d5454030304c1c5400a81c1d0540084d40109001c0012107103010f00c0354010032080c0009e0082001c00800c0c41d407a40301c060414460680c0398015800342c0c901814110124a13480c416410103001c10707050b965140d41f02800703424071700b9080c40c0403515040c0c4616510081640000c2c400c82ca000d28503800c1001703148001340713401e10b14000d0340b040c503000400150203812050301a86c0c4040c1c0e50302c900345855030450000e03010f041c140b601e40b40034021180c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 79643904 1250 79642654 79642657
    0x5040c0c110d0f050607050a0e040510140d06110406030c020a0c06080a0204030803070e0a0503010905030d0207050c0a0803040801050606121603020c0115050301060b0703050712030b060c060708150303 88
    0x981940c006264601c10f0801005030901020050041d03c1880c00340b068840d0720200400541c00b06039114070000084004001c1983e20980e00e07003040c8888040c003445580668075030841ca07210002c0500081c001e46d6510303403080d21100061130306a401c0210303080000c030790140aa0100e40d600b41c8090800c1444556568480c0541070194200700030728000002c08444155044401030340c0c1042104c0e4070307032274008030040051100c00d442a006101c40d03000001c3ca41814002d442c5d602d03500c0001b031820820f04101020007034116090603603031449590350543c52074517000349139009065240095580d0b1810550f1460a464010b880035006020421040e10b000440700c03007103074002c4441d003501c000f00201c20400b00d02901a0700882d0510f940380030b2003510425032601e40300e01104d409400a0001507601c0d0700b0320b1454040c0302c1d40500825805c128101c0041d0542803003060b4003d10b4100003904480c03c0000c190f040d0059544100c15500280905c000950490481980300801c240103048417076681d000700780c89 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 79645154 1250 79643904 79643933
    0x705120607080405070905090c0a0b040f03080c0102120117060f060f0121020d090506090106031a040c0b0a0305040b061207060f12090c030215180d0302210405040c0c 73
    0x10421000301090401501740034101c01040000003d21140c06e02004141e210f00c002e10b81030344503200c0070f00006040c5807803c054030125009007188940007851074840391071550140118070001e560030840140181c030500032207030180c01c20b881c00708400205483c003180f400a0250980718440503000400c0f9a5039500e071100c8080d01c1003842d007165040103624149841a0806c2440308503107001081141c0481540d44c004c0710a0340c0984100e0710251030b4104e02c5800c9030441c1c00040c0c089507103455a8580b100f03100004a8001d882100c0c3c2509940c1e480e440c9200b15004003101d01c0002c0d8030380302440309020300c1482c40383c1c000b1001c8441088400152050a41e1083c2c1441001c05104070000c5001d845030040c4800600002c0a030414400e03034030075281c1805100316900080b03218121004007006001c540009940c10003202e540c8101e5007014680400814980d2048110700f1403040c9405910710075802405114802e460b055544d882c1c0741413000300015a200c0806180c10440500c43c8100407030801100e0054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 79646404 1250 79645154 79645157
    0x609030c120703112a040b09151203070305130603050603070e100b181215130204090f110405010b0703051902070510021c030e06040210110d03050103050705120607 72
    0xb0b5610843c681659501c008003003650150086207580f502410710140c840c10b0420080e682d5002c08805a01044101c566100030960080c3c3c0000010780d070180300040303040b0300c100c004203c224644500c601181c515800803c00301d0001d4808503550031100f070713551407100c06000542001d03c020324091002c039070351788010300c54030b50400c180c90042420805004280c002500e1080c0030a82c0d03034240d0401318102031f00f804403e14040c581c202e1006400f0a0b001c038803a80c6106000c600000c55480d02425908446408a000c0e641705599060400010302031000450a051052012300c44c0c405022040008440c0141d210b86100b83c0100807060000c0d03800000c8941e0b117403c880180f4500340311002e0492815a40d60811900459066481400380341c002a080d116010a0032190500c041404003c800f40c82c1d4082e01180302d07602040c04100145050004215180c035545803022a09428100203803804d01d1038811180030a944030014002d0203418850030024200648502480c24a030b0300c4059078a6800405650 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 79647654 1250 79646404 79646407
    0x304051306121b05040e03130603050108070b0702010e0d0f050f06060310051012150e120d0c0201141005010e03010507050405011b020d0309230604180603230609030c12 74
    0x10000108003e00c00500070140c8100302a20041918030707038030361056480128900221000140051190141c541070700e00c5000584001c9150200710b6206030040c0404074148040c0d411070501d2911050386502d9140d00920001a108140d41006802d00070521030742005a04a4010006c0b5914006074941172103079192800200741d90f400d00e01a5010360136800602c89007000008440511000c8130101c03d03290b051a00c00c0103009000d900307e41da28072100220249400c401d2142520f04142640320502c41d1320307680004640c0310b9401e9501d42a182c400c0300c1c000c50052b03052006001ca542d0180e0b50000300e62066000f04031a082c1500c02500c0c6005a21505040001c00c8010161034008800d081011550140254003004014a4098240e0503c1c2c004d94207502404207031201c900500903a064030701031000e40114502414200103078582c07000740300b00003183c50710762000100296000c82d02d01440c003605884d07104100b000d520070900f0a1000350801c2501d034020301004903040c101051080c0c090080030a00c9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 79648904 1250 79647654 79647683
    0xf0e03041a0d020a020303040b01080a020a091e0507020106090c02010b0607260706050a05070c0c0303030506010201020705031206010e220507140d0b1f0801050607020102031902030405130612 84
    0x124052040d0b0030600d4009001040350460180c0003c080c6000f41e00c541030401051b83c03a5116a40c1c2d40c05203900103076024101c00c5003041034804036485240940c070980c1c850148070f400380c18484283c4809648075030040c2c1d942c03202000101d1230351042d0a801e100510081c08810680000603800707014030440034017140d0702001c100075070480d0141c90001c0003580b02611511101982020002090708a83c4018414108000a0000761040700386064055000c1e800035091800c6841c02c600070080144014107544d801c03c8000e0105108001030901507141038801c024500d41480014203000058902c14043c07002000a440702194600d455000e04625940c0028969520f0408445200c12004541001180051400b80204240e00860508a07041d1018044005c8420010166440040081001400110041c031252614500070072905005104690900307200200c003c4000521140d140c02603440042c1c10009070405c01801045031a041e075080100750702e4200440030001641c1c400420b50b50703065100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 79650154 1250 79648904 79648949
    0x60c030c0d05210103050a0f05011d011d1f050a1503050105060406060e130921020312070e060306010f03060e0c180306091e01020d0510090f0e0304 65
    0x9441000d000035044400c0500340900190060344403003615544041120752038000744a0341520b01e03040b00d5005008004d141d000f529082032400c50072000b16015525100189104201c103c4c8223aa1111400c000145984c882d05001f02175411882c4000f0383c1c1d07000000c0740356046c1c2d00014824416070340c0c7c0d40081404c1e5900060800100303240021100d08030001350b00401030140550145204071000d481c1041a151296029075580c0f021904c400d41c0125200282e6412018a40240710014030480c03480c404004049804040010203224850043c0e0001c102305103215206a0f0494001545080030030244800c0d030040395181c44004c28580c140b101c2504616440c03032280c0e00000003410b1051056519040c4108164044d91010301c1a00d41c1784464004c80105160210710b060141056034014104510409080c0c214480ca141e03481d000740d5424402130101d4030a0303010722032159411040030500305044c000c0b0f2030201c801045003580414a81804481100b5001088a0640310a022170008010803040c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 79651404 1250 79650154 79650157
    0xc0e0901050906091f03030f020609070b1801050702040c020a0309150504030305180a080303010503010c1b0204090f060c030b090901020a0e0402220305070e0612060105040203060a0512060f07031a060c03 89
    0x21217100c03044008000100f032580c4000750020b464059403c0e0368050300c3e00c101d5103035200042d00034078030194070400c055a08851584024203003100c0c1030418034200071083d00004c0854070100e60b0762002d0b800603100074041540c0040309c04040d00c3c3e8044040040c0c900100000c186028a00004042c058001424040c3d40315580c1c610301391b100b0081c20700303941646411404c1d449030003e1040b180690b0800c1111046c0354011401340a0140990a0240d5040900e408201c0503018051003a40c16000c0114000003040250003801898455500d010840340d0242080c0004918020080460307a4030502c104507115503c0380841090301c004480240c0c58030b000140ad000c10315010304c941442c241700c0180010400401146c100308032018100ca80d001030b52150f003400b00305515016134690030f4000f580180301a1030958040c54002802900b50241282c031381c1c000c13480314200a44030740b6156100000700701010a0382d495603544030603149000d02040804402c5400d101547c403018520810300800e402100440410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 79652654 1250 79651404 79651441
    0x20d0f0c02130e06181b04020405120106030b0114131508030c01061401090501050703031808070302010b03011b02280506190b0105070f022202040602010c0e090105090609 75
    0x404903016041224580001030040f400e03207400c42d0291400140d002d07091001c2040c1121540006417844018549980351662613400c40a94031613030034400450a6265034103455401d51510000203042401c1d410480304480050344481810302051000e004a40c88159000b00d04a00046c40407172001c0030514507050104c001d4000154511000c120701080010541100c2d08940c80560403a203c0c0c0700c60401100e0340b54090140710b010400401502000034403070b0b400000504461100002c442d4215039401405602c0020240d0042c0e444141c0301841c2e2030203100e00f0040b450b151400706010300d2011006500e4031058400c08001406105040401c49038804890300c2d881c2e408402c3c0c034298a0201001810a22003116280c001880d008000c50f0301c0d4002c0d000c6400440e00500c00801005842d802c200c1d242d11940d1b13801000f10038540c0206100d640c5800604054485130700081101109802c0c02031009205240492294505000401c950384407400f543d81c004c8000e5400c102180d84407040c9680108a00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 79653904 1250 79652654 79652659
    0x1110307090306050c09010c1202030903030a030209041a030c060a0e030d0305040b090307110f040f0509060109181109040804030b10050a060f0807051b0109060f060e0403020d0f0c02 80
    0x800c0040c255480301541007034a00c50304040269842d100700b40c4105000341012180450400b2810304003103500221085000c0085104881c07510320281d0119040d50000c0302440007094020840c04140d150a010751181c03034203000240013440c048500001e03500c1041d00f001c14003402e000101450750601c19802d1908588000d003c940652601180040c000e003c03c90701901c00c8a00c02011602181d40070040b104290f400c004000d40c4681040101301250704400c011540c07080da00c02840c080c442c2d080c0246481203510001500071503141c01881419170340c3c00409000c030b12440d40c4c00782e40010b00704126000080c405482d980310701d60f40c616200c01980f08981014260316040c804200003080c8401080d015504151030503016582d60f45825075142000200600202c2d0b24030000507161881200a0f040c51042c10440042e055056074800d4211480e4003070955800340c0b01c44000e0a007100c2c3e07001e047d0050901d8500c01d00e080c901500e00a40302d080c0c1c40b40c24000c21070700001c0c4210061044406d19220b6800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 79655154 1250 79653904 79653907
    0x50409020f0d0612050705040b06210a0e0a02010c1b030c0909030f05030906060904022202040503010c020a020108010909020d0b0a02030601112e0f0608030c10090213020306030111 79
    0x7151000403900280b914200030b07801c1600100e140030840402c4540268860001c0c8002801c0208000140510081e42d46e0400c2041c040000038881c0e21a00c138000c000d00841d07000403414151001340c159813009000c9200e0b1351001540c00c0c010b0b6842007640b08911b402403000c6003440720002284d00c000c41e2a03840a4007040b2280c3c0003007001d503030740ea0000741418480e49a200451441000903583d6000484001d1101e8200d0380014160742001154564403510050058804a489010b400e05510045130000d04182c1e01003410f0005050134410f13001400040d000a12200d0501d0b40000e140070014010400e0281e00d81040b0310840d280c00c2c4005c04102e60189118401e498054600c1e0002e42080b41c000c0d000030040c034bd03030803401d00c0b000c0b84102040c0543d8010080c216110941b44601d02c004895900003155100102c0480c22101d209a101501001300610380d1b5185c40b505051a00b0001d0b800710299034039144071400169114442e09541c0c4022900168483c1d0300d0100290061099540350511081d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 79656404 1250 79655154 79655167
    0x7060b030f1f0506010804020f060d0b03010606020a1103010e0304121e030804060518030301140a08070609030209090102131505160b090106060305130f0212150a0b0102030c07090c05040902 83
    0x44a0114280c02c4040d820401640d034900f0011201202c00307640103504008664814034075410004028050318140100110302c01001501080c2128210760010006070401480e0f4820008968001c200001c0103e0092202006100010b501c1e84114490b5008049149802a00300500000c2030103a0148c421003410b00032003d410080c1040d001120102c54581c074040000340103040c00ca8040200da1840c200450840e801c140000748151044941154889012803000a421200f00241c03809000300d81c2d1466691861403050103100d6201a003509090b90051001c144a0b8034400703005d0045a141c20342c21001c003d42144151020300c50140d842000d03001c030b043c042c004e21040d607120314054000b02c4020004a03542d007804a04540c0e0585c3d010704215075180003440491818074051282600050142410600052030f03d0316242c1d1440209800342d041c00c1c02c00000d4030052151613004182030002c7d514020716094241d440b0708160003201e00701030340d5481003124184100c05480c0500020602156102c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 79657654 1250 79656404 79656433
    0x1e120a0f0212030c03070e04090f1b0b030a1b0c2a09022809061403061801170606040c0507020918030d0902040c05040501200a080a08040506070203040b07060b030f 72
    0x5004440e006e011070407195031240582054440e501800c1e4002103410050b02c11030f50303000c035286c05891906107024a00a00400c900403400f0046005a45c0d030040025900200124152290780c00c002c26400c0c40f81e21805030011522200100e110800030b84ca052403294451403506000707c4083d0000d5800500c041144000850034040c080c138100847c440c1c214000d00c1c020801c44030f1003941c0c0102c1c40010182000e500078403100c5005541c10400080c1011200c40d80b0858040304840300360b010402c074010340d9444041c034410134004290406000d0358184100740000318054100d101e504402800f40c5803c0c07000516620b40c00b130a17140120248000c0d00d54603111348191001a000183c0103900c1076140c480c80030002805101100e04a4038103854003200a03c0701982000d0381211900501407034080d03524080002020345004241300c5500e6200c0c150700741410f0400502d018402071440c410365000700414001d1582c1d1200340c400c0694412000301d411030211010a0a10184070680c00c042d00c00c0304800040780 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 79658904 1250 79657654 79657657
    0xd0c03090308010b03070f0c060212070504090510030c03030503070e030715090f051c03030608010603060f0e0a03140a0e090406060312030b10030506180103051e120a0f0212030c 78
    0x103000c1e82c0c40b020141d8031014032480a00c01a28010041010740481c000c40a01641c030440046001e40c400504100401c01c02688209007102c1035800940300150034440c4468610410f81c10034403800b82d10341000e055658000141903240005001e000b40131000600c0140b00301402d030316546e806002d65825079903851107a800005520702101c04a12000408981c20b442070b610300048441c010f0030045032600d80c49040703083c007010781780035002c00d605e0b40000300d0214424091440218407a03500020444541c10058044a03012040200c43d0342062030018003003640643c518000d03003895503130300b65100000b0000799200e4022950943d00300c23541c1d400b04014004168082c1c41268001c1d81101d9218003413801c12000c480141d441c0d00d030300403402048070b508188030f0350025500c8500600480035020140000c0404000240d001b10350300d030310010048a22081c03080d04605026288401094000c3e03203c0080e00090060328001c0082201d4040214035080c0700704a20311103d00950f000c9503490910342e8000d14207 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 79660154 1250 79658904 79658921
    0x10603080c012306010509031509030403020109090209090601122304050106050904080304150b040207140708150c0c010b100909060b0a0f030b0a050618040f0e07060e0301020d0c03 79
    0x82d4a4400d24620703401c0741e0030180010f4680408900020b40c1c1d203030700540b00350700010496609407041882c0c0c4500207844407502801083d88030000c64484d4035610006100400641040f0b4509005019190040d250b48585982104090030310448062200c00e04000074079500c2c000904074580c05240c0101d05620700d400a000d40d01072002030150a4a440500c50184c0c0e040d1402025440100002400728005100c0034954996070540425851041701c0004e0a9030413011050320200c0c0409050a1400410030269000781511340103045286851000c0e42045a0000c241c038214480000f28400c000c002941711013103214000b00406031040745264014010141805011001c51914034007248041c084030907103000301c02d00c0e0ba90700642c00d605607049010b01484604103801c281d50f49400f0640b0f54541c00a0912224032600c600134500500d0f080109542251906042040c5410b15940c82a40c0c0420071070290303041820550007401c021070110b4028800c9003101103000d41b800b40b101800030390641090b10f5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 79661404 1250 79660154 79660177
    0x19022b1b050d06050307030203060a050901091a0601021507021f09060c050301031a24120609030c0601120317100e0a1d0607050904090c18150f030b01050103050c0c01060308 76
    0x43c81e466109041da102c2c500d00010354141d12040c00070b0b440c80b80d117401c032036413017456940003054680d8542d544040f804944000580602221402c01446503810408840310502581d0042a5800c24000203929940415117030240c000c1e030060b0880ca14541038101200c05588850b04120140382040000c01a81081c0002c50b01c6a19a103020296110489070080c0210025841d8121502c1074410215071410308198054100e01c401d0024500354400344111803081804038045c65545082103185400c0100507000340c2404400150f00c6400709500c003562840c0c0480700b5810702c1d42034070350440703c40066856903c40b21407001440108001c4030700f150803000e0808001c81802d04080c110618480d1144e00c12109400022024000c040325450590001510366010b440019105500d0340d11510540b040403d440c003d170b58485460204401d42482080000e02d02407000d483c5850940c0e07601c1240c0b00041c4922030400d40c480010800c0102103800b1101601c0d48039000301b181644c6c030b24081a0035001410400b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 79662654 1250 79661404 79661411
    0x80c03040e18010b03030301050409050a0f150b03010912030203100f03300e100309050615010e060a0c150209040c11120408030405120c130519022b1b050d 68
    0x2a00c140050103011404c0d84000c028509503030034002404028407100b681510b40c0d1151500040c081080c500c80e451103240180e0781691490b0800210000b5902006040c9001e13a24003100070340031524450202c0c480444034540580e480d207500741f020703460311030070742282c854181ca0410002c03c210201e222142c8954550300326406141e04503614099200300c611107080411050103041c00c0318900100a41e130300c204903003800107400e50719498045c44c1c248100c0b4403078001c010f10942c8a41540e002810340c1201c1c0340890318a8900b40b084507006104c06171440c40100b0182d4804030b00820601d00340c050b1402d64001800820500e48112001085da0f04086001400780c00390500c140036039140c210444080c0c420750300045280c94645070605c602c3c3e1856000240950044c0c0711000c5c0b450390b8921042001e039521410103e810705045948540c600003006801e10f0170352040040442000e6409500e80c2e071304030450b00301486210003000440140442c0a68112041c0132075000100340d81d040b6002c0d011901d21b410040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 79663904 1250 79662654 79662691
    0x7060603120e130507050a0f0212120103050106080105040519060b270708070c02010c08040b1204030306050d020d030c02180c180a0e01030206072409060c2a080c03040e 74
    0x10101c490645d019400604104a40b180391401400c3d004140007980c41207409031000000c455203690040c81c245062012210010010f2280902400c000b40c041103000300554101552815590365200030306080e115540f840940078070500b035101520b08038000d41072400d4510b800c00e0f4000c0c110810710003145600c045502041e001384c4035600c900d10035400c0c0e45071041010f480d40c0055488111a510807901a5010040415072120090203400306403d840080596800c16140180135140701c2e0700a24001d00c0c0c10341d002c401507941c3c00d105c600541e4140c100007542c1c3e900c60005c100c40c030841e82408502c1d503004406100b00a41344500800c46da04d4003e05013404942078404200000046115040e0304035100d000610161509400403c0348520030821405013211110140645c03586402e100300325140e0700c00c070a00c00e12600740180600d0100c1031603d811102282e0511841e00800b000c440545100070100039001c100b084412142804007403021030740c5407a035807108841d401038222122600c0317100c2090003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 79665154 1250 79663904 79663939
    0x3010c08060105161e030201020c06070c0804030b1816050307212307080105010e06090f0c0306030c0a15140f0301052b0501052a040b07060603120e 65
    0x1a809840c050b955545820030440d00450f41146019068a18805450b407100e100c1c14442c1c04071103206e209400260725013500400442c10180000c022900b1322075000f20402c002a900011681682d6100300001e0043d00e403542225410310361007502050511820100c82000d0311a5002c2d8012200c00b20100e40ea0305443e90b65207801d0301000c02458900520003402c07540060300100c0c60721600010050400d55040320204900c1c03400b080c591007900c45075503860060144849113143c040d401102500c01b000c0e00d0038030000390200842d000b000c1090b9800080041001d558003440301d4240031400a10f99405aa2203840d050402c04120400c000403421911032820a82c200c841514080a450315a050030760f860241880603049150f201c416070342030f15141c6070b015070503240328262015004000000e11450582c480d01803e03083e045108401e80f203052141c1c658040e42c2c0d4100c6043c0c81c4240d01071a1282020315085000d4220b6400003894800b000c2070301d200445d4001e20700104000102c0380d04124040c401d24 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 79666404 1250 79665154 79665167
    0x14060a06050112020901020a021c2607060c050d140f0601081905100510020d02160f050f040b040203070c0b1003020a0302100c05030a0201020d0b0306090a030c1401060b0903010c 78
    0x3900b404622a4451241500e1840e4080e000315441030040d504050541c0d4005080440211100b1000080c0c0d01d000303005002c810000c0701d100e20003c112030740441a0525000609010b02c040040c40103486500f000f0000c0c1c46002581c41d50380d09151b0901c1802002c900c0000301d41d00407588110b070a0852000146036600c01c0d4100ea00400d914060b590031512402c0c03555000d0075004002e00310052074042c1c000b42d144c4a1014000355a952a4040c058003001060001e04054080002c2412185101411f203c1800551b200c003003180e030115402510445000d02040141c0025002d060b445440070041102e01e982041c09c0b134503028411681e4421039503480300caa2501e0215400003a412482000c01400141000002c10360326810074103040c0300b0b140c810f070f0320f5610303550206c3c09280c0180d40100d003101321818140219905190100d0150406241071902d16603103842c2d40c107001d010000740081d1642400035000c450329038183c42030002e1000c3e984a507440341141d881004054081e600c1c0c041268299445500b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 79667654 1250 79666404 79666409
    0x10050402150706020702030d0806030d0c0c090f0603021807021501030f03051b0a05012c060a240608010e13030e040f02090d11240403030c1a0414060a06 67
    0x2003140c0000101c00201031419005140d084902560030054500035a400f003040000741d4142d0364910090b40741610505080a0f6034115180902404250b15400100038140b460145d5550b8800004c0140d4030b0b55881e0007900707981d403020b9000310704405d08031054003500056034418070250f0200c0d4048030b03a259020102c90402d100141c0f00c980b081e604800003910500040c54860400e4184d12b024070300490303200f802c100b03469034101c5240c0e6495208203184200303207944071203580701c40d41c40180c4412942c3d0b80d251150402002d00c6001d40d90354000b50502c80011904142d82c0200310000600c0c541c0300c05000d0400030080c000d40c042442102c000587e5540c1140d00508900e41c599580b4100000810600c0090484110840e695917001d01070f84400d0f86407001e0005203035019840c03509600d5002d80620100d0440220f038032103000d0640c164400b20b20581c40032242120f600d8907240d0040001d500304901d02c1c00208500d4181c03264803c050106115035a200744111a9114003039a42e141c5511840302c1c1212003230f1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 79668904 1250 79667654 79667659
    0x306010b040b090d0b090a05011a0109090e120409050108060604020c0c2202070507150206010e04290906060a0605030105130203040204060909050d080f0615030703062610050402 78
    0x822080c00300b40440d40141c40512000340030996138110f00c0d40c0c0c8442c1d40c0750448240c1c01c1c3da4404c91002d814003200340070702c0344810340c00d011071402c600608000910802050151044040d00e074580c613141150700308600c11039842c0c3c0d64900c0b0340b40e0b0386491110300038040030302c00c2624500ca4080850f2040c03510784200c61440aa0400500c20301e1150703000d0040003912064100d10002c5044459100040c49000070041284101c0c0a80030090030840c15680008494030316400b1548900018411450118541500560880c000c2c0c84000c845c001e05031514150100c40c205401c84030414403040039000a82640101000c0b1000d80e056600e60344120342a0009116107a07000c80340d406810b0340581541d0042d0b82040c005000842c5458851107018103a580101c82200c0c0d40c0c0c004450142a01e0b800024290060303014488564a07040550001e01c107a00c1180c1181e00c104400004a403615019a121100601507400c0c2000d50301d420000c0d000d4010007152520609001c1c02d00e1500b0303d0071417845550306c0785500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 79670154 1250 79668904 79668907
    0x1404140c0d03030c2001060303090b03010e01030b0903090616020102100905061305010e0d05070201170402030a12180303050a1d09010605090d06181e021e0d1509110306010b 76
    0x30b81c81c00c0703010b40a2029424180700421405003801c5820000c010340c90200c000021480c1031840ca4020480c101c154041c00c81c014007031005010411682c0901411a0340241c050003142d02c4029825095100d402d400030780c40700000542c840728801d10a8038040c118001d80940d150010b07242416802d803200c0c408000d0440d04200005030900f408a0355031201d2601640000031819410030b021460700402c40404400b02d40c002c50058110340e40300d8a100c0d20304012426040640c100760740480d9036a02004801411b540381c1d1f42001403071a20815503841c05403180028480d80595a00780034020740d005100741030015000b1175144042e10311481c0f140242d02c1e00640b00c0d5040b0707881d0010440d0103800c2101800da000304184815804130b81c40d80210003d038a0b151076105822001407034407841d1488222586403a40c0079007140340001d699044407543e003200110714070807407011f507110001d04c60b80c41d40c070030007814035200d1244403019042d10741c13001c80202c0c810700c150411003003000101070385d81074240b00300c06205130b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 79671404 1250 79670154 79670179
    0x50a1802011b060f0e0705060403050613020d020603040c03020f0a0806011203090e070206060301060e0903390105100806010506030a02130f09020a14040b04050f03030408011404140c 80
    0x85412000d811600c1194080c4202e0302d50307078543e400e0b035074160180b034603643e154185440c440e5028410803009101c1240c0007031501d80b56a4403036403100c00080030041e5984030b0180c40c0066440d00c4038100310362030780108110703941d20b814a07102d00201d582e40801e90184800c800c6e20030302c5080000c8900180c5459030300401072a0707e03001a481a070800c00c1c0d411010003010101c00500002506200c60084840390090708062a0850174103003100c2c1640e0005201214060900c00f586d000402140c2c403651158240310f2801843c500f080110520348080c0c0c0485d41074034801c0b58500141980b09070301030b000402d802d406550381c540714159503520a0007100d0340241d0410214950000550041070000f1031070701c000c804903582c0c9102070701110081c0e20282c00d00e42c0000d1b207485d210751b100311102da401c4400407100d400c0c60b04050b00d0000034001c5005030703402000080402d2003903036410802c0d04d0007000360702e0090000c4c006214240c2c00d01c0d641a2408c603090901c17983c08146400001c10850410308010303000210b44c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 79672654 1250 79671404 79671407
    0x705010510120b0a0e01060f06020607080103080414030f1207060510060807081005040c2d082206020d0204050901060f0203070305030403111e150c0f0a051308060a050a180201 77
    0xf00600b2480c80103544200a84003010280500002002071034400322010349049006400c18400500200800c2507503c01803000603c6081500c040e02c0c4043c440002c02010742000ca0310700414500400151b04c1008007819209110030b004102d0309216290501c80d41e00d52095401c010070040c00780c20080743c071074000500e0f03540c0300d5038109600031040704429002d542d81d400450201c400c1130303000400040300084215041c005000a4011581405103640030703803403240100400300c0c04041d00704146d095148580c5030130300700c260081340d820b107401ca4021569207103880c1e0314000a601c070744180f50040301407600014509010301c0b100c04a69140d50040c5103000542c1c0d404030740c01e9100402c101c0a01030039860b0904001b03010003201035912a030040b0150198004101d0502e8100011755203002d45a91204001c42484180d040d16040010702c012903440b0801048161014010007003010306a06043e000015030703001c0002c07954090a40e000c000c00c42910b502c2c1c107090980300d0b030540c15056255018090300055 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 79673904 1250 79672654 79672673
    0x3010b030c1c0b040c091103040506040311031b010b012a0602030a06150810050d020d080c0c090703020a0810050d0209071e080105041103011a0a0507140102070501051012 75
    0x240c1d00709880c11800c4920f0b0381c40c0d502d200d0050b50140d4682c3e40500c8203100c0121640b04045500f10303080540c5045140ca41da541e80d0782c03038008100804114000303080f03494404080044e40d405e90307401c1e000500c11400c0074459a00a140144c151400120801c105c1180c00031040010544941c10f20403003004000d06450b0030010794400b0f0464038545a4482d400144902c0e290392940a42c1035581d030f44101820048030140c0380402c3c1d03810080c41001401038801c0160f44400b9003010b419809003003203407123401500400d42002e13601c0c3c411131780214030202040a04c941c941c2c001d1000d812b490b15105d0490710b50540c070003c4448603001e169000f541c0303084420b0241c60540c1c0200c1d4007428a160085029102e0615480e400d00b01b079a04001244000005200618042c010342c040b42610740e036054219890180c0c3c05240c403011b90076484040c1c10005107125030522420072104030307503044880011141d0485903403034001c0d4032010080c3c0e015443c0070007140c0c01b0100c2c10803003011280d244200d100c0304803035600c030310b80c65 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 79675154 1250 79673904 79673929
    0xb070e01020307020a0e06010810050307030212010e0712051002030601140d060801060b0c010e0309010e0d03020705060304120806040614010e0a030c030501051b03070f110a050f01021803010b030c 86
    0x40d444144480001640c40302005d038090300002c6158155410030500262a504001e0240d040c0840400300c14011038400060381421240c04445101800c90440c03102c40c01040204803101c1240102c040126031301010807181d03c904c0c0c0c0709008558020210410725000c80c00165041c900096200003070714402008400902920440a02c0c009001682e400d4001c1c2110b2003a80030203400d48000c0740c00214464288121724482540402a41c40e28498000007409514001c00c82c0340704040d1122600140f51007000302002030300f0080e020603620b0a20303040c000c3c1210000c1d80c1c0c160009064400050701d40c2403a0240c1421503149652071000c62030194010344a00000c0715402d40c0010b240d440002c00704175400c2115000358040c0340005040d0030308061074151800000207445c0805c20400a01420651054414a41131070500e000500c01e030000030f2942c1003100c070741d40c060a10b1040010041070303440194010407451503004100240d644052043c1820b882c42c01c007020b540343d0040c40c4002d15908040018100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 79676260 1106 79675154 79675157
    0x1b021b0d020604050904050304030f05011a03011a1e1905100c0b0a020723070801060f0303020703080306030a050a0602190c1e0303020d09030e030c0405040b070e01 72
    0x1a216620459004d494920009000d101f8140150740c05140d0281e2203400529403810010301a0241110b543c400b40d034000f4011031756150521451072000e07802c6111100030440030301006080c40a444080081850003a001030a0350345003400304045850260528001d1400c0100f407001241c80c0407a03400904c42083e5000c0041600100003640c0456171501c0580d40c1c080302d140c0000035220303088e003041030b000a50080004c1084045802c80a90b04107200800c502541c038000344542c01003610025000d03800035141440498481002107902030005800c940d040c0116554240c640072501c40e09648056012407110701c2d444075031401000300351091402d200180a60703210505441000780c9002110710b282003920b01014020f4054a80c64080540100404402420b01410000703c55651a10074000c3c0b046c40e07a0302c1d19161040e03d018941040c42c0030029603c0400070341d090712501e0f41c60360 = true := by decide +kernel

theorem cover : BRFrame.Cov 79496404 79676260 := by
  have h0 := BRFrame.cov_init 79496404
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79496404 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 79496404 ≤ n) (h2 : n < 79676260) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
