-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2960
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:15:14.086739+00:00
-- url     : https://prove2.me/submissions/68175c1e-4d34-4e8d-bf29-b6ca28a47332

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 532194244 ≤ n < 532374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 532195494 1250 532194244 532194251
    0x4020f100206040b010f030302060c031e09030c1603081b0304170307060501320a1701050901050c1303020d11102d0f210c020a20030c060a12 62
    0x388030355001a0701c03449a80141c815255a0f626a18448000d840601c00500168801408a800205608001c50704000c0c11808c1d50906010060a03178800141140c01d248240c20104160401c14001d00504040e00102001c80c0701144c1103545002ea14020b0309009401c0e01540100803500740c00c10000c8030090000280c61070200c510306000d0310b07980e600105045940d0f0742040000111004001d001600d41072414141d407451069000602903c0c14001c4d408a500c001000000030f4410b000507400401f12011600100e203031300e01642c0007420344101615090542c11300b040381d040864407034a003050940c1d81c110340d0000a003900741000052440200c3c05103a000307000c18001c16801d600440c4003802e16840303d0700819400d86100c0200c01c4107400300070280100754081090750780325214000d02e010082558072400c2c0c0344407048000008940070b41d185400580e00c184100f605100303c000ca00e420000700d103555001c0d00d03011680800d4941408550300f42c01070a004c904e07201d402d401800400c0780d41a5500f0b080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 532196744 1250 532195494 532195519
    0xc09060a260a090606080307020d12030b090708070206181009030309060f020405031002120a0e0a0b1515041503090f3305040b0105210714030f07080d0804020f 70
    0x107400400180703d0813600341d854140b00140d5810040140c0e400c40d500208090600d01c407a0b00d407071a030b030f10740752108004150342c0748020364055940740150781c05401c5c0d6603100704044c0f45c5048042d01c0c11001400186000b1040c40400c0010000010540000010b0314000304404003d4607099015280c0808000d250505203600352000a00070ba01600403075904a0490b0920000f0100c030004030310903040c04e1060801d00ca40010a4110706030880c00150000d0b0045580c02c20701341c1c076072014070070080d00c961640800010111a003850964200300120b0000842585464a04002c01201480e80d5a40105140e1100001002e11134000800e0503915048000b5007205814098035110000711148102e410055400ca0000201c44074401e25100d107a02c02155901a402c000810850324608299540c11401d8045400c5011009000340700041800b6690017903641c4a00b020182454443e05040b45580c1c00b000c020044284001088200002d60703080101d0140c6542c008605002c0180140d16040300c040f9584 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 532197994 1250 532196744 532196761
    0x30207120c05070b1c0e30090405060f03060702060a06060e03031b030c0703150c0503010b030f04060b12013e0f040504090b0402040b040516031e05040302030a02060c09060a26 77
    0x1800e042c502c684a065187d81e000041d01c800c4212030f04c2c0c03095580c8024410700d4028141030b4051900703c44003e0609559000150000e0320f020720071280000160005414800048940d01511b00a4862428107400c820103000209613030b4003542c0c1e00c0d04040f0103102e0000125110034012568400070700d030b081d91440c03603c03401c3c175170551000860040e8100c0d2410000f58031a071310800a40e4141d030b42220f40745245031140740d040d001001011308261003c81d5907502c0300405655100b80d0034458040700c00007003411103000071000c65024004540c14042000c0c3c018100031280d1400140074800c0101701c09070386440350728000c0c0e00c55001e10b40129400c04c0c5090072000610444041d00303807040d48212070038080042d0400c01c2c44269801501c2820006944e89035a110107800380d004580d40344000381c10340d0000000e1025400c191174080c4c40a03009a000014010304999040c0601c0380c0c030003500c460847c0342c0111100840c000303201d07855448080088400650070500d5250325881001030703d4a4422440c1d00341030742ea = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 532199244 1250 532197994 532198003
    0x30c0b0c0d02011112100b0c010b010e1206040f1104020409061404200a050705070b04051009030f08091305151002010b030a03031812030207120c05070b1c0e 69
    0xc56544035014400c1e0319588140520f5010680d01803a20b414107180043c01280014050448000f51009001c0800c83c001214043c0036170003850310001c5880c2101000141c0441c8910324224012966075020919242d000552160410f90106170005080302c0c9041c001811603c0e81442e9900074000540081d1500907030304070905a0700c540c0b03400f0031000d41f040c0230081151000d0101c04000486842180030040060001d80820320503801c0c402e140014540d102401c2000740d4025400c3d0020200301440781b400c6c054200115014107007020b603c0142944c81d9602028951140104030f2600010300e982c058030750220007810b54070864000e01040c104115000da4040c41c28500d24020b01d980c03201d0b10080780c0305008101030440c01502509400087c1d0300d086004c0c1c03084a07211191500041c401000203001d54500c4a4185126900161103980a140002240d241b0400d0501080b03007400c544008038601107414000c658168290f150369204141481310030105042c503850a40d4600011003c0a0b100802e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 532200494 1250 532199244 532199257
    0xe0f060310152f06072a050102130b1e0d09050d03140a0204240306030f0b01031509020906120c03240a110403110d020603070e210a031206030c0b 64
    0x42e40c03001c030441d0048030010f02060703940340c6030303070740c0710601140307820780246295040348100400c1420700c00c03940024000c1c1036a0306a0110b407580c0d40001d882507400c2d5042da03484040c2c120111841d1502d2003440404102c19010750b81c00c0740b034440000301e82c00100e203164841102d55501a0503507601003810304001d0000c191600709004010941c3d0002520046030340700b1075080da81610b645c200c5580001c02071000d640c08039040c440600d5a00c00001c00814040c0680b0111203204076140c00390f960540c0b500030582e512440282c45003a00b8503a0311801a980c08520b298050f01c03e4488600901402c0750b410701e454021148950540189a08004101800c41198800340da007044080d680b0f840d4015401c045a0600c40240c040354814081400000c0c407441140c0c0444400610940c02c0c0d04494000903031651042c1c0b00200481c0c0b015a20f80d04908104150300c1004c3ca0038541c4c45002d0b6000307580c072a01c4080f90314000b81000312668806001ca0555403100c2d0103182c004590301e090a880307003c2c2504a60001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 532201744 1250 532200494 532200527
    0x190f0f061512051305030408070807050a030803010e07090b04140405100f030b0403050f1b10060b0315030a0506070201020703020f0a030c02040f0b030a03050a0e010e0f06031015 78
    0x4200070401e41c0001c8540071000d80d60395201011425880800707002400060500c49041c1c00307505044022440c10005000501010005031a51910345240a803400c181944018040c240404042004c984040181d90448051524942d21580c1da51421200341c1c5440e00030002d100800f0402003440d5041854000c00b440e000c0c2c80400c803d8a6401d25240322011901c2120200c3c50148030510014010a95240d0494070034201f05061000c0740f07040050680041005e81ca0b000c030000ea4440844004005140e060391303400d2800c00410313081002c00030403848000e04440c0c400101e082c2c8074200e0f40701009444a8941c1010680f0024103101f00001d01035400200140c00603c10301e40418501035000c50454895a410f44032030004141985c240f00c00342445200c02242c80740e44007082a13294030148649001a0301c2a84d07610383d03482c00100080c0001141091890400080142c0c0800b0340e1986415070f108050b00b1500340e0b44907620360b0140d9418840715044028244c001003682d0950f00c1d0000c1caca405216124 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 532202994 1250 532201744 532201751
    0x105040f0e0a030c03050d05240d0507150504090e0a1a091c0c020415060809030f16060e070303090e070503040b07032c0703060f05060d030503190f0f 66
    0x91618200507281e1000c00e61566411204052001034040d951080d04240320781001b80c00d0248001011080b6513040300c2c81d940328038941e1080741401c82a201c5040c0488011600821440344a0311402c1d40c07032075503014080e01c81516001c01c0c2c406030b0161041d14003c0149a00030f0194008801001d40c43d60040c03001280c00d420840701c01400344040b01e24042c8160994001032500e588404002c1401c1d41c03035004010244202a4000000350704d941c000c426110a08800f0b040c40e26140140c01882050000c190060319042800403190494101c0115103510200c0b0702c00688691f6642080001461a079400c0e0400c0c0c0309692000007090340081c0808203d4081c2c1281c800c05da0354003a0103176124403040318024030000f50003000850a1340617900000b110300d07901c00000004a00910015020300d414098074460303a0100504000704903040c020464400080c98013400f0900305140812042140da150060078000044001004496078031080c00090038455014089000c00c14412401003680031001d105107400c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 532204244 1250 532202994 532203011
    0x61b0708010f09210306090c021b030601060e120304080f24100b07060e031c050a06030c0513020d05040809040506010206060a050d0309052701210b07180608010504 72
    0x142d41c85465200f5800101d002240144000c1c100c0104000c6480c01c418599148000304048806116540208900b9002000955540807401e80c214101d840f01718840e82c8401c0051200550010a142e50b4520580d0182100720400d99032034114022500103103010b10881c28040d41c49003001030a42d80c443c04170300010180c800f0700c164a00703001b8000ca400842041c1c0644003044000c940e10010100c1c203000e560001000a0a00181401c0d0340c400904617038054110108030882c006035110702c0340c1119107120704101300d5107180c3d1040c0034096240700e080d225180d45052000b94049e9a01155500b00168030108510b2600d46003130203642e040806070501403072410000901075400024024002c82d402040031256625240c01c020781d0310b6450710100d0401802c0680060350303403903c04000d15a1008070009079440126041c12000e0004140d105d0842c2c070a20601420004150011003041e603038122510a9291f942c1600a54103030301c05440b0540001c0760f0903400201e040d44450f245c2c0c1a1070003294248251035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 532205494 1250 532204244 532204271
    0x160c1706090304050d1b0807050114070c030201050a0504030b010e040b09010b0d060c0512010e0417030c031302011b14010e0d0516021804050a020103050c1c0b061b070801 75
    0xc04460325107803a07104010510982c80d1503070544103443d01c0303120b003168000540da60901030401c0b29401482c007640301000902c05503070050481c2c600861a00b5800b41450284d03101c07004443d48520000c2e05114001484560103072081080300d0286811038082c0149507901d00302c2540008080307400780c1e91401d01501040b401d00c0c1c180070341408814001c25121240e4080d88031200101103005944052190401c10031100c85220a00b0318000c100c0d81140c03002030318060230300c150401d1480e0101c03c05880204100210140e4071401e680e000b4101c0300000000c48958030040e01c400d01c0001101101c41e541440c00003c00100c1000c024034090820b0003403040003003c000c0183e0751000c141000010074010701c41c003000b05291424519545000030001c070480c51050407040401102070314243d0300c64111105000542d6014040c0b1504a204400ca5500d0080030040602d40042c0f0724050244450700d64620020560f11281640c81200c880c54445609141c1f04401c3c0e681c0380312511600140b5400d1011050a40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 532206744 1250 532205494 532205503
    0xf0804060806010f0c1b08070801050402120f070b09040b090f190c0f05030417070c080106051801030b0a09050303090309041a010903030f020f0d030902010305061e0d020105160c17 79
    0x850389445030040c0d035405c0d54039041c003180105801d107444000c120340002c034004104003c0f0b000f80019000090305007010f00601810b19403020b501d0b0100e44c00f901d0400d4000134006548011251408a01c0c0d844a10000014000d482c4810403d68001c9c001010311501d0444244464000d00000002d08000f000c09900f410964124881c0340000c2a012445044800e00800045620600c284141c102107131401000b100030360082d4505441548c1020f1050000c80700900c110740141c50300b201d0108200405100407444111705000003800c0100100201d0b02c901d2040c0c22001d0111360240076240c59280180001d40d50303802084820f8400c605011516207a03000f080d560b02e0761114180c1d0768900a0b404d41d20b0944070343d49042200300440c0716030113101100344000e10401420700c001c4c2c2d034049440c200d2800010113413040035041920038110243d60341030300d40c2103540303201110500b5030740d51818002e0340c001030351a030080343d007903100106144c0070344020420507149100c01e58195a4040001c80300c10b1480b40d070344 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 532207994 1250 532206744 532206767
    0x2090414070522081902030d03050c270d08191713140703050303150303030603330901020415050c07050d020f10030c120b031b06070f080406080601 65
    0xc980100b188640c04030042c0600f21103514010141402c10780d03030b41825441c04072644400c08800340d6a480643c210f10f418841002c42040c0341c074084c000c90a00d20002c01c402e1064034500c401031500803100128a12040c0b488c8100700b98018503507060800542841c13180f5900c2000c404416501d80d040003182d20b40195100b5a011820521902603a40d46490400390713030b619004145e070807940d604640701d08400704020715400b951003500515240c0c106203c0000c0ba103254141e206209810074001c000d02078400080001c4100840c0d229016040d40ca054000c184500015040740100c50358001c00c89039200540042040b1895041e15610001d45194200c0b024014442e42d40da00e504034030400c01c03240c0f91498102d0111400203014509980301440003c220501d49180c13036002c251030761036420489800c00c22600c10f042c810f20003801001c085e10006500c403100f81c024652081041d98403004ca64890717001390b4000d44c1c2d2020740b04d107142c203d42c20f0420780d503085441000001100c100014205d94071070480b03c2030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 532209244 1250 532207994 532207997
    0x1d010b0406060207050d0807021e01080a0b061e1b01150b040308040306020f0f031510020d021f0f090302071a04050d0204050414071523041e0305100209041407 70
    0x1500e070400c01008219500c410042d500c0d00740a108c51009070303942d10f80c0701002d107083d0540031a801300e2202c005848403100a04911445203030070780034039403030305e8000841d54515a082140c9815400b0100300380d070603004281704800d41740e0070000c60100c0c9960540c0105031003c007501010400a40e50110160b003881280402494200240001c100185564016203070380411010010300340184c0e00c40c003001542003210011681c0e680101e04507800d041091030b041110401c1d2001e0702d0001d45103900a540c800104106581700400788180d006d40408a42c840600c5c0c41c190f86062102c43c5d101d050095030b8540c2d501031560b404550000e82000c11461004440c00c940c00a00800300040c4141c00f000001c200007002660b400b40e500501046040052054401910666004125130544008010a1542d100b080c4014805003c04c0c45c0d5400d25803031054030b089405025414281c1c0e910518041072591481e0b02c000e00780c2c49641c40250b00420700d900503010015040e2410840001c000360720060b01d55080d0340080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 532210494 1250 532209244 532209253
    0xc020703060f02090307030314070209071707090602031c060b040e01150c0c03020f030a0c03080415031e05101e06080c0909070302030604090b042d0c1806091d010b04060602 76
    0x40000d000e481d8046c09c40c13402e03040c1c150825096070041121000d08071290400180d030910060340242011072519004034051a25400309420844081c0d503a20656500c0601e4086080ca410400e01103600040c01409100c452552220b5942c0700440c03e1100030302a4031101964000b501100d10b2007000e00055a540200110341070794507640070712145100940380c1035098010102c0703610108a010403242e00540c400c10209a40d140350050a086c45080041004105070910402c1580014000c030540032402e2000da00250366140c0c1d0f0b800082681840e4809a401a25002103002c0e500c007c215102c1211820344a80d00c0390707540c1402c1001684200601d65a10201c50800304a11170b20a50203075503c0303035000e80001118210794503602603001d070442e01115800f16000c403646005110340c0c49840301c10321030410182c800040341e8070890300c0d54890003104280710841007000514420794010b48020007584204210b42d04c285c5400714076200070340c8800c02096091109600690410b44603510407110580d0140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 532211744 1250 532210494 532210499
    0x405040e0f0717031c0609020a0c060e0102040b03220f0b07180308030f07030608070803190e2d04020301090b09010512030a350406060806040305032205010c020703060f02090307 78
    0x12444034004000801202ea807110089007040488c030061054a450b52602030040055181603002ea9014815800e4a40d006010070891060300100744ca030061000c070040090802e40d01100001c9051420303000d05131710024201070f400d200c0d26502d4207001381455038400d011440d03a100017182d241d5030f0b07120052010314100000349880d07041410940d0041054980803940540d200c1c64649840c120380c1246940da000010010405a1214101390007400c031070800c50b40440200d000189901c195419200c08070070308050421201c014484e480b400c1e0400180215125611145820000e02c0400c61003070040d00c0c0d501c004103061400785000c42410031030f21b004524007001104100c401e00407c01c101740c9407091302c5018107036114802e0313403e115900b5100c803400c456140a041031800d4400f140d2040405401040134040031a50010450758400d140c600211003510b02e01c844259a540c9054010744207518000028001e140d0110742d18084a0103117030140885241c007103058007207218030b0308000d40c150f0148404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 532212994 1250 532211744 532211767
    0xe030403081b0a1b0f050307060203090127140301050601140412081603050c06011410140c07080601080f070815040f06050916060804030801030602030c0405040e0f071703 75
    0x5121007020b408080d54400b001a680304007516002201c00300403c284164184119108402c0c084010300e0b085005110103480c20b0400394891042c55580e41c100304246466250036245a46039000700c218000b0010480c1e40c0c0e918a10140d41034803c0d5040c0700e0b5007000d0106050358401c0d480c480611071a034020302e2800d07207440c07003000380c1d038045c0c0d10308541c0c05005000c00946480100703c100181070103501d03220703580c0f1541400942441416044a04000907a6050021a03284c0448100300c0c1c1e1010b08003000318a0a00721a00c0860244500707060381d600c102c18000c100319134042440c6040b0350200c0304603000c0780e42c03540d600341c2c036102540900d0403954080c80007a0315a589580d000c64229000c0d040280740303201540c54110a80d0341c100c402e01040da001c2901002c8210401795810010700d5130349806261402c0550340102800340c1803101402140e004000310348244030702d004407002410000d001f00000410400d105403203804071071800d5118000c0c06c000298a4034000c25035203c111441010714503006140d00c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 532214244 1250 532212994 532213027
    0x150506011407081201061803080d0f0f0603110a0506031302120f07031106190e12071d16050706020c0304150503092505040e0c0301050709090e03040308 67
    0x40a81045030340d000096010074060000c1280700e001d15400d079a14020310208550605044c1e101340200b00c2021040101014104104408ea0394024149aa6064507400000150407440022181c0358500010151b094031140d0140049910900e042040c162895040000e0210680f0030b076034000c0010800110702da00c120f1406030466200801101c00c0c3d00418541038601480c0f1003c4a456600c10740b001e005010320f512442c843c401c4101d626501d400101d50303440c0e1400103160b80382c00c00e00001010202040e6242c04800028480c100c046078a59680c524140e15801101c80c1082412a603150210321019440c0001001d140041e4480034545404c5d599840005e50008101c10b039107002c01c0c80081540341a107201221812031696809459062038000c06003450040150301b400310004405048562100c0310b12501119411100001d04207440d524017800d01244110481d410b5180408021f501600101d402d0140d0351941c204101440d140009035540380310720300020f052007000f40000c4054149609 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 532215494 1250 532214244 532214251
    0x30e01061502211608040e0903181908030a0e041805060402060310080d110d080609061003020d050c031f081504150e030d0b0103090804061103041e060e0d1505 70
    0xa0545400d500c41c804e0403071416141c400322900800010100f08a80302c680e40f0a40141d070210107503251564011a00b0501e8114003401d50045c0d01061640d041e0800c4406030f580101004c1041d2030b81d0350f1070b0782d40c010300304058411a64807031440e0004910a80582340101c190450740300c00100310381c1d103c903000c0250540004001c80c115180c000c20114600109002280155000307848562801d60712b400c880d4104284460305001f000003d20802000703645145145401050a582d007043c0110501c82c206c01900c5401d080f109210305001c00c2c4803c0b00702050056104000018103100030311555041c0f8440c158a0b84609400d40d4007085030b01030600090115283c1143c45000340341500c0440a00301c40c00c1e034940b00c0c0514000e400120307039100031601500840c0000002445d041101d010a40ea688085004500640c02003044549925500c2d203002c1049501401d400b0101c1208581c610845000740c0300640121400141510024402420000c00c2a01c41c079920102d2079001031803c07240040100f6006 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 532216744 1250 532215494 532215553
    0x21e1e030c0307030e04450206180315010602030d020a110a050109060b04060e1518010e040c06050a0c032a060b030c010f050d15050907030e01061502 66
    0x2045a608034000c2040181038aa1003925902c03403030070040e4100b000312448802d120358011501c184441901e15100031001032034003c484087d00f11501ca2003003243e042c42841c00213400410000e0400d000b00c0d4529914060710708114204c0c1c0c0799146690718550000402e01c282c5025074018860540d078a044c0340c000d02446031452505801c5244608003541c81d02d14016000c2d500d995450b410700701407085600908045440a803418402c4516086000c9952103000705000e03007050400c0008000f42c0d4600107504040500003402d051315517100d540c0315818030016201281c4032940c12000155950040c0d0a036080f91404c0d1f203c1c8504680075450540d00380c100400620802210741240803000a548404504524000c680005481d4549010702d480c00440c0d82c403031303410310443d000b080066aa001f82220b040c4907174080042482c41503400d8618120b61f00b50015039001090508010110354941c0c0030201705007900009200d01643c82c0641407d081c1c0b50580840140c008401d084008288020b282440c500344 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 532217994 1250 532216744 532216747
    0xc1401080a1806050115030b0f0a140f1207230f0909100c02030a030e010608030403200a17010f1505190f060e01090807121712100501021e1e03 63
    0x5035550f0002c40e60240c000c0080c59024180002d45294144102d00000350705030f46a01c035214462000401411141c401e06c4589071518100781000d40707844080e46036502000e45400d81c078034407214910f034480000e80240c800541e441040103200c1c0440000540140201a00c42151146e9110500c22424001044544644650a4600c8515105100d0380c0c0030381c1d90940c040c68481404040003008c0e540303251640c0006a04041741444640804000c990440b5403150a00a0300c2000750410030040d07880d10801c9600601d24200050304a4040d01d0500c1030401c684d008000229100ca20b10044505105103c04000f1281d1004c2c8854201008000a1580e014410103c241d6664018803507106854000d4000142c4030358407684076507000700405002d0204d0078090070700700b0b007801c0c00c140081d244500f0145c0301c0c04000c2ca00144404006c003c41d49940000c00e2102c2a80c0b409032072600c5100c81a00c40c1e28014403881002c0c0313141640d040d001c400320944281c05440c1502c0b04015030300d120150228001c81d180030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 532219244 1250 532217994 532218041
    0xc05190801030b07080405030c07060809070e19021b0715120507080408091309150c020d020a020d06020f2a2d010e060709090c030203010302030307030804030201021b07030c1401080a 80
    0x2800c0000c040105144d61f505134592500260550030100e090b0321014000700c000003841040c0400640707100841000b84301c01602c81c5a540f068000140840745001c032580640c4101003924004800300d60104005612682402c8204424940031908201ca1100000380e1020115001490a10080900f010018546545007000d6080c0c03100f1100c031090308442c030700038166011052910b50b0242020805d4180007500c160081b1100c080d40724040d05da40248108040300000007000126030549928a00071301c14113840e140c48100c01007850a421500382283c03010100100b00051001403800d4800d40d40c0043d2501c3e00300c00ba051003908540c0b04a80582039520340e10b0a00c014030080103803604c2050140e507200e007a50b10307100d8a0070403241c0d590141c004041c0100018405603c001003261691645440e140c4496552400c0c00c90090090560620140d08603100c0343d401c2d08030020300c25054a005801c014120f07682c1d0a40c1040b064101c6802da804a6582c0340090a100c030a64410a28100181c80c0703d11201e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 532220494 1250 532219244 532219267
    0x10e040f060302150901080414030f0c0a0203070b0f0a05030405031612090806040812040302100c0504060809030306180a0902040c270305060a110d0c05190801030b0708040503 77
    0x1500e1154110046658610800a5152104040204005280881e45401c003c3d000083c07000b94018000340c0303212003a0005000080c020000c03502d00754124400d858440e494900c6103034844100722411383c4a0302c600c1d100854015900421a0760003081c00b070701c1c80e2074641400400da40f00d030030040c0b054860380424400106807030300b184490401c161080c3e002c00090b94002c0c0014200b80c02d60b4115580d40d9004000b003000140c44002101c030304031600390f4000c250340d07100c0c42c0483c60401080c03c018201030400da00c2c0c54042c1d4015000d401603840c0c5450f18112036030b0b282d182c103070340b4007046030b00c16031002c00302c0d5a9103000d240004070306800001c046d10121b00012103802040544445219400000c1d59480780004241004001032000ca60b102d020701220351300d562592552150302a1441c1030301c540c0c0e5851340d11072840d01c074103c0b2030401401b034085c402550010303006083d5400400d090101c0c030f00f185464882d49480340c0318050599502c540c02c40700d161600142102d4100c0d00030000c0340c5502c01000400d1020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 532221744 1250 532220494 532220501
    0x11b0e0f031b1503131104020712080108070801181112150a0506010507020d020108060d15020a0e060f07081305090901090203070b0a120b1507060b030d0c0503090f010e04 75
    0x6903865500c20340d16000312051201d00c101856003400045404c1c0144580c076880100d000c02502e030030250000800d68140c00003030080c82a1000240691404031050800c284c002c04410304940c5000240c070542e6035950500781c2640e908403011064902c0065043c0005000700c0d84c04500440041c00c180001c1d03040045413403801e0144110000c2d03ca000404120740740c00c06014079684480d0a1a01c542070403500e5001c203c0241d0080e4001381032100b9000051034a854504480082e1504044450341103c0c40981c0040213512105000340021a1940c4a0811b81002c0c0c084030300340260038a60600c0c00390540c5800a40390000c4030407280a03507211070f0026495545021640c0505162030000a0303412952040500e401160ba1114854020130b12180d003903e5000400740b8800103c0110104a2400c5200080c0e131001103480001044000458100280f204590003000280010781c2213420491450400703985501d040280108903500800c507605950501000954201d1018102910520403a0740000e054 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 532222994 1250 532221744 532221763
    0xf2103041d09100c050306130f020f03090c041523060406030e061f030b091905060a1a0a090f060317130b0408032b020a08070f02011b0e0f03 62
    0x2501c800c809000c003000043c0401124000460010084600c00030b4019001340002007210b0322440c2264901080c0d41d81503000444a4811300034115a201d60051100300c4a80054030039819900c1500e00c811400d0815210342e08246010402003900036140141c0300d807100c200c105100d2580c4d03505d1981c04602e070311941c000e0800380080d91004501100d045044501d4414010481c0ca0050058000401c05014600c55001525008004203d103032f0740e0781c0d64003840d18000041c1c1c07406800f043c1e40044188100480d0703c6004040704601840070224121031400c1c0d580355020016030200d041c4000b00101314a69001100500342d03e880403036010390741e486954005002010040410800203262441d904e4a58283c002078514803086600381400c0c01c8096035603000c0c00d030341c00300d000c09501807481c4a40070140c0d607551124100c640039550382e5003440008001c200f0a0f1450b0b80440c0100792604089801030064180c03407612040d410040d071054407001ca5502e0700d0b0441c1950001c683d1a0800295101070100c0c145 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 532224244 1250 532222994 532223039
    0xe0411030604150c092306120a0b0a060f0f0e031f050106090f1a0c071707090609090b070e060c0604050c0108060a080a3309030e0f210304 61
    0xaa100d1180d0084150303804c1d401081e04101501e0340c24420510100700e410074100e0b1042c0040700418038a8089546031198005e0303846e10342560003c00030008003540080300013030720989139450290381d0750005407000c4400203c070700081100111031541c0d85100703406440724408020100c0e1003402c0c00300c80d00076012040e48891101d854855005100103500100d03081c00600044a181400914145001000d00340d8802030b0b1500c000d000580d4001e9140400000c030142061440443e8020b0078200102e07524100791055010050411600061607241445170200d610780000c05070510b5070700e80c84103e410310f4060b004181d00c83e13403c4c040c07003210800030045c00d0321640c4035100401d04204140700140c071020b030050002d4417402e05030505011100005c25602e000c2913100802c0031005014180015625841010307000382d4100d160004800c6901d150000c1d42c0c600d00a4a6840e22002480280941d01c5d40c007499840d00080c00b8044042009000401320048082034029681000e4a13000b514070301c2c0000c1c588548 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 532225494 1250 532224244 532224263
    0x2040f0b0a170a320726090c030f071802040e040204090303110f040806010e0405031b03040504110702090a050c1e0d021b070b19080402041103310206040e0411030604 73
    0xe007010390130b41800741c20000604000c06807000703000381411410704110318a84e076030300290082a9003500c01c0002143d99180141640c40c0b040721035034903a956041c3e610483d14910030307120039031076844514801c803001e0b9400c5c03114036102941c898080c0800380500040840c00c06603240b040f252510348540180c500d0900c040c20040d61686048022031602c0010303000600340e08800c400344070004a000045407480300380710b90080245004a00d1032401c6026580c05103821074104001d48042030908001080224401c4500114580b112221403084a40031101c805030010304024007015125120000c0e0006a505110541b40030703080701e01c410076a040641c0c4144420f00c085154410004140002c1c3e0103407168102c81c606003182e04203401d000c42280083c1c41c040c008078001103004d40d00c8940002602e01403070582c055503030604a0764030620740748560700c030102e0400c046905100340c01071454902c038040c2c004001d2400d09042604c0300c8100d1401520490740e00c5203140c414102920140318281c03040f400b880c41702 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 532226744 1250 532225494 532225571
    0x190507121817090f10021509010e0307060608060a0603080a0e040f02120613020c060f04051e101a0a0303050a1b080d0c170f1801020d02040f0b0a170a 66
    0x1160b800c8000c0b5071442108044d030708141081e800250140200e401c501fa440940c0c803003100c0745004009013624810540000a00320703050100542000e23084400f982d08444850f03641040e01d40441d0310602004103041c204104d110390f800e00c1583d1040350740600900c006201c1e0310303114401049a001101d5203411400060400c040752512012003550aa80c8c000d09620b02040001d0b810703150a4000c108003100c200c09808101030241c100281804500d21507031701c19100f007804038001d0b40e419840c850072004505001c256a480c60584a0304881901c010780b40881040c19640d040d2441d0308401e441204000c08080b41072842c895481d401c054083c01b40700803654503c2807544034819a14207460000074020300b0b0343c044c0c0080300c0c03062140d503024600e00c0f07801c2c02c2500c40c840400384000815040e00142e41c00841d00028055896006104951744d9000750710b146503803209600c0040c090904050081342c100302c3c10b5141c229208900580c0300c034070071a002400c0c1c056001d025903401c6c0c006104412003004a000d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 532227994 1250 532226744 532226749
    0x60b0102010516050313030329090705090d061a060f0705070b21091905150604060b04170703021f090509090c0f060904060b0319050712181709 63
    0x1640e0f000b8400c0f190103403001030822809031035840301034111032051075194040010b052280c0d100480c1c0c042c031840058400e8803000c02c9a0f0850844621042c80340c0c060901061034140074008945140901601420502c000e82e225000180b42c484408500340e0300040301c5011070b41c0d415000303011031085c124405481e0021800c0c41442c5c48199084804030110801c242d49220341d5000042e03600019240890b08030340d507190010b03410245520800e43d190f0304c49103408020000003040042e0402031001402000c1d9450000b04810b445151145a01d900030070442401695210002191031802c030804a032130060f981d90100315030910a1074844001036100c401c05036042d9005205800410003220240001e082091010b03460310307000349809103d61008008440c83e519038505654041d54010070802001c3c0e504e884010542e4001c44000c03d003001c820644043c810098490780e402004196541460031051101d001c00404408180240503036a0b42c05100000724440f804000c15020b40340400d4946100c4800e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 532229244 1250 532227994 532228001
    0x1422082103130c180b06040303120510030813030b09060402011e051e0406030b030d020709090212030c011e05040c05010c0609050d18080105090615060f030c09011d0a06051b0604060b010201 83
    0x1171a00c201000c00042002c281e01c21200c0c104240354520004240d01d814091010403c01540005c0a2800c00f08064a980d0040b960000440e030140e1030305980d07139413220101e13600d48030100d40090205884801d1240e004000c0c40180411100e24141145441d026044103207000b00781010000417560001814000164140102c1e080c54009400402d850f2828040203900c403c458000c1c0c001a9a070703000c1342800c5d0340d2004160b941070317021503043d01e5a07510000c3d04075019080000e031514005007402c0c84c8010900440c415144516000500c440300581410011100a84078070300c1036501645909401000c0381c0c082c0502c00c07201015844442c1c80d0740314409000c4c0c015006610122459140004101e041c10022400540c000140c0d0607071025010380348000b0349079002e0080c074a84410b0b000b10401c14207400c0c500c02801d07003d40913250251442202c1c421420000e10606400d0303040203d40104224141c00380d0007401440500700805020300c108115514a0080102d0b01900c585484250f0038003556020310 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 532230494 1250 532229244 532229261
    0x325140108060109093209120c0303060603062817070602070b090415081f0209060d0e010f090c051512040f031422082103130c18 57
    0x70320201d01e240c0240040d01398945403040000391a11005120b1148080318a200c24440e514000c81110800b200f546220364a01260510300c2445482d100d4032400700380074103640080401400a51842d610007090005a4101628440d000020740844172103801811820300034821044507400191441c00080c4006d011040b01800050340015109000640e03010078030b501510150034a059580041101141c000c0512140010003540c00010116440da00401e2610030100e00304e613043c0365240c50325500340485c490827407050b0703000d501000200078a0140350405c0c40c41c43d0761107000080c00c1c0d01411020080d00c005960860780900300d0b0f14180003920740703011181c00e0300c218a21081c0c1001d0043c403622021034001340003d0855064414518100740c400c05991641400c2030324215181c510544e200502e40903c1c0324409990f26180b0804910b0140004186000721b0705401410030500da000302c518a80d50014003903810010201c0b1844c004541000c90341802090580703526408015004221011540c420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 532231744 1250 532230494 532230497
    0x19061a010816081503030304051e011515110d050901080c0304020a3303061d041203020d1401121a040803040605070513180e0111070b0603251401 64
    0x1414007402018070844511030000b03074144034405032100c0c02501c0e0303a84002c20140c1e03030500c070000401c070030080080b600d000000200d80100968481c692095426120344054031002000c41d8503040007000c0d00320b10415000c0000b03091060b04800e190221504011030083e0413000305c0c0b000114040b155901c041c4d025484943da052013811810203900207480c0061741e1191480060304000c146100c2620350304c0e410004204075001120400400d107000e40985490f10907001c4815000003004104140f03016401d02c1154440180c1405600c100b1042c0d00075003107030340c49401c8155500700000040c504e40701014041d051f100040c4d6540307181c5242c01c280c668002d4042c0322083c00000c003440b0008002e0800d60360050741c0000017041d03a503200310007201c2c04d019003507040310301c2c0701c00c131100142112503640c901c05038000f201c00503c000a5482c044a003a40c400c0c1c10b07000301c40c06007001000c000c284035412140d0800402025114502c00140500300854519844a0900d01e0700010030840c2058140211180d940700303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 532232994 1250 532231744 532231757
    0xc040207020904061e05011202120f0606040e0c0306040c030b011a0f0f07050a0c05190509150102010e03040b0c0d0c0b06090a060503150a1116030f0219061a01 70
    0x81c1e010604112010308010f02050304c850b1350707035081d90100d0008201c1190b0400100195a0340e240303400030030f58031080e09078010007801e80300c0c0c141010080340d600280740b89130000b4415512900c1c00e1000902800b05952118090004d0b0207100e0b40e01400150300a501070404203040341e0540c00d0540740201e061384020302c40003840c40f90414036540d10701582c110402c280c0b2001e4a44241150400c490301c45e004001f803041c06030307410520070404c0b410300c180700790b5006449550f201031101201c0b0560092600802d580000750b0b80000d50184007040020321a8141072001041400101c03003032038039580041c1c00848880502040d8084500410444400019224501100c46c9115612030b1150080e024204034013413880a40003907030030209604441c008200140c02c036110041c4061402d1941501541d20b401c4c1c66003051960104501300300c00780c61421840402d0300500180720764058906122a080680650060610034a5800001400541007600540c804655074203541c2d54a0b60708c0700c00c4940300c3d052004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 532234244 1250 532232994 532233007
    0x12031710030b070804020d1403030f0609010501020712020d17031b0a0504060e030f030307050a0e0f180403030e0318031c1b0c0506210906160f111203090c0402 70
    0x38242c1c50140c02c02210700386500c480c1c40d02d0001c80c1c515091100050812000d100c034141070348000200540c41044050600a500e4540400f00200014280300720f5005902030001030080d01c02400652501c20706c01000b40020390490f96485500f82c0e40c060035010407038800300400c180010041c011202c814401c5c0700940c82c0005290003e882d13406140115410041c2c1900780c4140d9440c108009084960300b00100c035140d00e0056001800359006038017200000d03410401c080442d003400c80102d105500300030301d51400904202a99900e1000040c001d40030075446d0544401124403d200911044c542c03143c0700840081c14005040c034002a03941507100c4284640070300040c140e8400c29000c1524045488484001c105003007007101d00c18140c200a0303005500103a40c07849515001502a01d00c9201c0b010329500d50381d928a0a034441c0001c0711800714454102c0460700c9558426041030700c0c01e49890400c1c203088480f4501071881d102076240f4a41d1900703000818400412400c0080900b030490403078045d454000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 532235494 1250 532234244 532234253
    0x3060901020c0d08060d05070315060506190c1e0b04060501060806031c03020c010f0e070f080c06030430082d13020909151b070b070203041203171003 66
    0x41095840004110820313001c81c1003a542c5c041c00a400f20f8024080310084c9482e4200451000050300600e62854074041000420b820000140c0750900c0d081d0a0150035034519000c1520700a0b0090422a050390102e01e01590000d02001211813284c000c0341171440e103203861b280c050100c40701030308100240500982007003816580007903608984481711034140740c980c0a0310010341c003034010348401c82007950030000c64480a0b100c80c2d02c0a0703031801c4000c0440348600e960740d00080c0401041e008072a040e0300039000c4c0d500d983c20a4170085411520543c083c51807906044212124809403040f0407030b019403ca00c0900b407146e48801100d82001078111041040c1c02141c1440316441000c094284c1194000c2c0e00050360000f1041210181c55005025080d032490040007442d100e030404900d01c9610282c241c0403d4503450404a40501e0b0150351264524042168841c0c08040702c0c010008000c40c441088049032043d00c04950414040c030988a46a009040154002140c0c1004107410040391841d81c0800200c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 532236744 1250 532235494 532235503
    0x50114042403061512060b03040213110405121e0c01170a0b0303070f060c03060e0c0d0902120d03050c03100312020a06181a010308030a0b040207120e03060901020c 72
    0x20104414000c01c070414460141c0103410309900516801202000c403401c80358001140e0b0109484111003084007540310b00743c4e000280000e8a019412421950303803204000c840f5440030f0760400340c6003a924103050351040026200d2141d0030295105800c085029048440007000a4403088050000384c0140c6c26541c000030300d0300303d107800c0340c000740c000090100f141c800090b0f108850000c005000e8036034410383c600302480003c01d4480300301e074418900b0b4482d600951180c8610401d13244840c044ca40d65490b01c0302e051109812200c4001c000950b941a00c90050b40d449020002601800010b00608429508003800721940104058541c0d00c04004019a900c04010900241e82d8002c003a5202101001000c0749800420240102200e103480908251001e030303a44584c044a205031a100305000c014003e032070000c02c003031200070180702d418000f051011101ea044204c507908094401818810b00b926001861000004041c1c00b156025900524500b028010940e100d4840700080d03252200342a4819502c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 532237994 1250 532236744 532236779
    0xe030c010e060a18080f15090a080702130c0305010504140903030f101508010f090b0d1509060207200913110d0501140108072108180603010801020405011404 69
    0x2d410000b0002c622a0107042d0b996403030036000d602013001c640c480b00c2141c0e580a80e1b0b00c1d0b000c0c0134400c5949408842c1402a0041d00c940c0084025003149013035662070402503040030b01d080347e0280c0d50a040c0c104005151141c0e01c1001031035900826a94540414081111514040040000c0001c4100301070400000b007100c0d080b800d500c41d100c1095446014490f003104864000300034104403d000b034980f01e83e1000342d0034180c03041da040c1403003110b940310060000c581003500c1c03040d0000c0f4822903540c0403e5003900000380345a0031f1240420096903136580c4a04aa204801c212003c407000e58415400d0000040380c0e030451a001d07540c5070700070300b080e1068451941030010000e00c00c0c1481e0b59100e20988402a2582e0f00580c000700138000907a10390b5800c0c902100c02d002d0040140700d2400001002500b00c1d00300d0740c1038800681da14007400c0c0e00b40c5580d1410b602054282054110981c4000d855440d03c20086008120706000141c4403401c0c4030005042850078800d2104d504000d0006010308401c200c000d408 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 532239244 1250 532237994 532237999
    0xf0102071e05030d110706110c040c02010f0e07090c020d0c06090503040e09010507020f030f04031e0215071502031b0d0e03030106020c0114190f051303080a0e030c010e 74
    0x112031100850a0070855419001030b5010b0040300200c40c00d03540c0182d02c130480c030b900200561321284c0e04c2d80070848121800356008401c6074001840481c06040c00d40c03142400d0406480085160ba000005900503107504418181107a440030307070b04024000181c8070302095a42c10b0301c00f400c80c0e004107250092803505070f4500a843c2969036441241001070420894008212501243c000780c038041c03443c24000c04040350010003500610000c1080e420010080381c054804405020f030801e8150344134805815101d03224454240308011110340541d6811168400c401c2c40e00c500b40341c5d00c19452510520140059010203880341c014400d01c80d206940300c4260380700e4000204226102e560f6055014081c107002d0b08e156007540400800810400d42c0820b004a0803142a240d440c42c42e040288010840d2049007011003414140d49a20108548100d042e404040c016140c0f16003003051000a0040f0303c0d185030300407108524009041191180c0018404d41036100c11400741c6503118a10b40060301c5a8200d091a130b2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 532240494 1250 532239244 532239269
    0x22808071e180905150a15060807180302060c0d021b0102280209010315060602030711190e01080303010e0108190303020f0705190605180c01210f15050f010207 70
    0x600414564800c0f02200d800034110b0703100345100f202d85212100141e40c0045100d082c072003030355015600c21402d401210542d40c3c451407030359241901200c040b00d1000c00038880180700900040036980e50006070000500b03040c040d00c050b240b0b4a001070301d40716040340f1090300d00c2e05030306809226a8012411340707914500504c080700003104000c10303052880030442c4020750004180e400481408801600940e030716250340c0f03003040341584402d4183da8a00440e40010120f201041d1a50028200204c41920b90346022504649040e1039041e81200b13a1402d0308084003a51001c40100460b060340c11010307004000d80c0c40500030342ca03142d03c203941a19a039018013900741500010742d0f1004454200403903103403541020642d207210b6141c915a03407400319214800d485c004e0401001c03c83c008605400440070218404c000e00e00206e810005440404001c050312070001401d00e120f2780c0b048168054410545c00320b40300080d0071402c40c050007851004581065004101100c00c0d0562a6000904001508c2c0403d000e00c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 532241744 1250 532240494 532240529
    0x1c0804030f0e03060405010903180e150d050307031106010f0e1807080106231801090902180a1b02120409110f07030518030c010903020d022808071e 65
    0x50b1400007019900c150144220070402091150650010403114803d80e034050044003115600450001940110a0034280c207a0200f000503603860005c0b043d401c0017411601e41014a03449543c155000841d050340410800d00d002054131105008042c0540050810340e1417050400303050b61745c0c1010003001c20508000220f481351054104108400080c460040240006521441440c1a01040c2c29104a812036460581e5050303103410320035500c029000648030070b2240e1030b10a4400c098001c45d00c0590b000805480c01c11008040c240c00188540081080807034404900040001c40d410218406070464211000c2c00c0000103c0008841c21585000b07008514004040450b103540d204181e82182d10000c0010008101a0850003502c603400103001d159000300d40c501d003455214440300350a035000403142c0c482800180380c05c0d0a05821140040d11080024000c2200040349500f0010050011070540c403007000304002c00c000500292100b213400e200e0034074250489503990140c90140c0000c0f140380c1e0001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 532242994 1250 532241744 532241747
    0x103090506010603090b0f0705120a0603080d02090f030a0521040503030304112e0813020a090f0e0102090306130201020a0b01180c02160605030c0d1d1c0804030f 71
    0x1404015000820740c0c81c55651204082e005041d09801201c0c41e030780e8180024294900002114400c6900d51541403411094503506490078200030150885aa0b0b5000040301042e03940d00541a540240380d80141c1e105801d80c1040100180700711058445c1d4400040d02000520208020300c400700341c40c0b400080380d24012882c803154059330f04210303018400441044184030403017806ca080d41d801600d0030380d20320440141143c070b895490460095030311289081d1a9010b4443d074000c5500881c40b004000c40b102c413a03400140314441c283e220134503043e03d0707000359440305a01d1711841c0c41172030b10780000f10700d0500070002098482400a14030041d1302e24045940b8150390092100e151100e62040c0300103410740e1076527400301c50541c000c04500c14041c50326022540443c00001c0600b40d0705020503010301c1541c03920000f11f03825400208600c428900510280300219404c0c0511941030717000f446501d5600e0409504507252000c1c5180c1c2d0030144001030421400181c0004501d600b050701454a42030192403001c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 532244244 1250 532242994 532243001
    0x6130611070501020706050103060c05040614090f031b28170a05030408150c030103081614030a0309060e0601050a06030e0102090904030e090c0306010e191a07120305011208090103 79
    0x40c09000b40d4000034000080001c16031100f41aa4070a400c10094102e100c0d13022980740c049d50180c00d011940c4210200c081101c81e901400d004032009001e801c0100608001c2420715000d001c565480d00a003040c0261140741c401080109516001e45200d150030b4036044805c400c40a0344100d107441604c6900c54480075005110701e02c4616000300c2100d80c0c4954848000d6510484810304110340411540400e05000000c07084904a03034010706140c0c1000c0d24040580c1d5001e040850440d00c3c00c03a032400160b100942400a04021484c0d80c4000948840d01d0404105581c64054204041e4000d18010701c1940c0d0798200c00c40650301c9520700003410000304694a80248207190a1b1940040d1800400c41010b038000880c00100106a4004100b600c42d08620741f05404213607040c0340403c1c00c00301c00d946641000e50108480e00e00c001c0301d040440c2d58403002c52003484500750708842e14280024181c003d014003030504810280c40380c0713401c0000c5d624000c0890300001c0801380007001400c0014021640d82c0c400e41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 532245494 1250 532244244 532244257
    0x3080f040b0c070e010b0a080114240d05090a1a0a090203070e04030315062709060b09120a02061b150a0c0912080304060c120903021e06130611 63
    0x2040c0720740d209600070040e96203801e02d12402000700e41c6000045982e00c80401a0303804600d281c1c0303904000344d080040c0b11184400c10740b00e10350400301e43c1c12103070540180d41c5200c4011214648149559410b42014802900c20041260360700e944500140f000007081010102092007520190f0303003880d00e429a004024001ca100c01a5061058070030201e041281c0f0749032240201d1113610200f00815901c0c40450061030a0b1181801007003071000c1c0a2000740d400500c4c003148805014183d0708141d2225000782c1280c0703440d0043c401d40d0b0804140415503080c00c0c00b50454104400000741000080ca038000380880c415841c141c081d0f60a001e9069804240c100050440c2e0000307180d1002091a02c04021001010859603800014180080005241d100d0710104041c0c283c01034650303407440c1c0d6107071070722409814250a480200200318172802d94020083c8503030f0552500c00d501a00f900010079040c0940d80c91901212a5249c0201c0d00744131071000680c48500640d0780c0050082005402446d901e0300901401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 532246744 1250 532245494 532245509
    0x90213060b0f21101e050d080a140d060612050405120c030918011703031501030f06050d12030f15090c0215092b020a11041e060312020c010813051c0f080a0b01050403080f04 76
    0x440e0781780bc1880c458112400f03559807035580c1030b26100a55142e5098500c1640c02a044d900100c010460490086d070050040e6054003045074500804500420400020440f400340e400c40d05800600c124403448a8801c00452810700450035401c001ca45c198a2104500c3c0b00c906140ea920034a81d00e194507608844001d15008100c0803a0361100d0601c003aa015245651400091800115600280d81c1d07125040c8030f2802d0000a4070518101503219004001d4210b03104258803c4088061340401e0f08003500340305180e2080644846040304100c000711051261802a000c900d000c15084100da0000d0900d03001034101c0f142e0a404406e910114004040140d4001d00210300394003807032281002e54101d502268456440f030b0180d00441e14040381c90300b6480d041c003400101c5c03080102d116181307808010000342d0b026009640550142007080501d8040c4480c404002c1101016460007036078200c202c09500c14080002440400e6075540002c100740704a000061500102103800410404a00c007a1006130450f03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 532247994 1250 532246744 532246747
    0x1b0c1504093207090f230103110a0c060902030102041d160c1515090b03160e01050108090c0406091d0106030201120c140409090213060b0f21101e050d080a14 69
    0x10b400b50440c41e1b404003107104140d41c01018001540f54130900c14100859070440d1110708002990700110b40d845860441500c8c00c40d143c03245000036075404c0c0b006000500074441c400185c140740d0985c0300c000b41e0b001080c41e104100a01102003405410418800d0f182c4d0b0b1050144c0c010003918490b00c0014000c5490401d40e00040790f0012507040d00780e41c011307000c0d540704900b1540d00440144510801c08a10b001d0088580842ca00400c01035001d0060660010850004d440c0d1040400d0003040840d84c0c264098018035485074000981403d4040308a003507612141d000303002084c1140c001801045400924001c0d9596a038074044c022481110714a84101e5402000307a42d596640f0340600140081d400140e115200c4204ca00c01008103d2003820102c0f03001035031503810700c15030802070442e54100e90102ca84541140c0160f0604d01e0905e0700641c0b2550f00c00050240d40c0b801d08000f03007910200001c1840045000000038032030746e6203800031282c001b6400841d007584e82050344000c035220a111842c0d403408160 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 532249244 1250 532247994 532247999
    0x70606090e0c0619080c0409020f0d0b06031b03130b09160e100303050d06050303070b091e15040309030203060703140c09061b0c1504093207090f 64
    0x20070342103100305401c4a070884820040150400040f48108103044c052a0031500c01a8001d0b4083c07900964015070f000a29400c00d5a42c00c030001c1640e1011000308521140010400d03807140c0c0c0740c414040c0f52542507518600710300e480281011703c6043c0030000c1c003602502100048205801c1010130358059030004900140b4201038a0440c0c0d2a04800b4103143e195a2845001c281d80c0502e590052041d0101c03140e004405165882c06d4880d41d01c544001c59615444040208454804000421501e803141a1495251803e84060350401602400360300803072048a030034405c441d50000d00b90000d50320346103200c8120b0300e4038503040c1c0b01004160300081d014042d00b07003006000c0340c156001640480c00910032001c180c0d942c815404691080100c041d910940c10308c05042d240710800031351420519006e045946404007600024a0310340541101e004c400c4000405011007100ca0054411051007042c01003041c102c650020f00b032a4004007242e034403070490355000a65103441070203400024450080c28035229078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 532250494 1250 532249244 532249259
    0x160303171026010b0301360c0e07180b0a050d0b040501080d020105010806040c03030f0917010605040f05010b07080705010627050619180e070f0503060a02031003080f070606 76
    0x1103040100b4510b54a40004811142418050030103105c211415213113150014150024920f0000803028a15401400c188000118181030143c0a015000c1e5480140d251031a002840f201c80203070b0040c2505001801004a642c0c40d1080ea030408107281040e07600c0e2004121101c2c018070441034001d61050800000041c4041d01003218580680c4a03030080c49039a880e80c070010b035204004d80b001030400da41c101040004c40d2240d410740000c2c2500c0d10701155215528211700e0304042c102101c4841c2650368400411652800384502d45030041100350501c015031400c00c541e4400e002d1924090310111002800e00e08200c0203510103070280030325002a42000c0c159600f210f229070404942880d0451510010843c0b501d400354802d0300d5000c28180745c9481c42d042c41c8044103040100c600202080d6260f019103140d100c000d002180283c502d04c041c03c1e072124941070800d4988031010b800304501780d00c104180500480b2030380500044d40d40007600301d583ca1424a955400710b108102029000c00d00d003880c08182503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 532251744 1250 532250494 532250549
    0x101e020f12070906120603110603060301090609140d080f16021009060603290402040c0201111c1d0a03083d05100c060b0d140106081603031710 63
    0x4130010355070082c0c1001c003900258126011804050005400d13408030030160301d0510000d60740810040d00216147c9029500c3c401600e06520080b03030301240c2011400e0703034110200007464141e941d0b490140004d080c20b84c1c92201d8940041d02d405581c1460301c401d1030841d4020400300b03004030034244040000d07c035503041c40341c018031950200f00c4041104240d25541e021025858015994041c41c50407055200c6608000090184001601c195503e0b03c84d034940791f5066201400410f030030107103d0814444c81030b900d001250720413058090129a0401d28a14018000500c103c1281d49402c0900e4030380c498190000b408090b90030f01c10110705029000d410010400d948100300c2c503203404151100030391070f0302c100306000702c102903003000013a2180780340000720300356400542c200100034005151561480e00e07400c40a1400950200c2c01341c0d180c40c030400c0b501404100000da020040403141100350704550300205060303a11511046031109100c00f080b00c594180101100900c0c1c04021004d1003400d541401600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 532252994 1250 532251744 532251749
    0x4080d0f020c010f02031803070803040608040b06150703030207110d0f030e0906010c060519050c0406090e040818010201110c0f12070b010b07080c060a0509101e020f120709 76
    0x14061821682e40030350080c07008464074401034000c2c504180d0000000310700c0300c20030803038607038148242a40002d044006200810240c1440c0e81c034844585000e0914503000c401c0644154052403030554120002c15034071081e16980d5605180260340c4a400341002000c00c000f0000303455004007130002034000c00082011010b16144680c49555007864418104070794400704071016030100e40000f40c031200003015540042d501041c100001028403d50044e264100c2e43c04564080b96408001410b004154000b40100000c02c414400c08001e446e05650b0505240241601045000d003014414440c9078001e400901c42d100c517072a85191a4599211026654821480c2d110744a0044100317903121044890700303c8900315003220030174031036074a440b0001000d58010718090351100790510100c49140310034030030b090060000681c00700c2d55040000525040282a5800202c00d40c036044d44018980c1030707030114a0505100440044e1148503070b80d1010a40d102e1180164010300e0020200015203030092100d105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 532254244 1250 532252994 532252997
    0x8071704030c0e07020f0705030d050a090801060605071407030201021902040b030f10060f0803090d050a15050f060103020a081503071a04140307030c0909020a180b010e0301180f03030204080d0f 85
    0x302107181c00f07254641f0540d0040b40e8150b0041400c1c120030074082c1c00102030310013503860a61000c0c0d6484030b005003100c140d90803900c00148002007400034010103070384407580101004e001d4001c0303a14660001c0e5449030407106c2100c1c0c02c4102e0034a0000c0d590b81d0340c091203001c0b0000e01030314160390205203400d49814003114408100c80c0b4142021a05880480002d0309135003030640110300e020070010401c81d0224200c40c0454140c4142030069001400251008502808024010629041544040c80c81c844000c0915040500c14086036440b690701c01e04d130075001042d0200c0100c654070b003107000c42d08000369904210a01100000329a40c0c1c413142e0001003007280e8030740c03a220354101e05c0e80003091f80710142440040c05402c1501001e01c045109680103402a80c401071019043c55510240302210382c42c0680d541d030803280d6507000c4115558100c410108540c0c2d04038020480802409008a2031070702400c0060541c203811541e07001010300035412980640815011281a0b00340030300b0042640200411410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 532255494 1250 532254244 532254253
    0x9010305181e1c122f0d0b0409080d050c190507020901050901030203070b1305042d0e1f230714070b0105190e09160e0408071704030c0e0702 62
    0x31007444070b6003622030102c1d04540e03074560300c3c104c030310100d4014151200701004c203180840700780e440c00000300c0c09200074a007450524036110000700714154104d40c0301d425a03502a600305051800050081c000701e4504a001c07660005683d02c8400561881d0702a8107406044e804c4600104244550000f02500480c0c0c030840704c0381410380c5c03079205019803040203210094165204000c10300c034001007080a0698800c0d1601c042946030340da10005016140e0800700426591040620410944900300d400000d01800c1d44c41030248404086e80c15036105a500c10f41013881d190301c2c102d11603810183d0400514443c14143d4001200358203005d0200350f032400c1d01c4141c04158014260b201c600c0404044d240243d8002c40034540d90380c41e200c2801542e00141e00c4980703500d10b0942011400500100300e050142c0180b00042101c078880424080c07100b4416000440d02900c214200170005036248100c0e1542c7c1e92082e4144440000e40380d0303003501400389400080032031a4400f00401c1160412040c60f103d41c0700d580c00ca6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 532256744 1250 532255494 532255513
    0x102041701270807051203040614060d050309010f030b0409080c0d0c02010e04051806090c0406060c12210c081b120103030509032121010b09010305181e 67
    0x1001801c121482c8410085100002201040006000c0c002c4980103405460501700f000e4026020307948201c0301111400e941e40d00c2d44405030070012296600c640241c805084208180c1c84441d9a1300656070082c3c104040d0115002c009c0b407294011864084000e031050040403800d01c2d04443c1500600ca440c1c90a1260f103803112195449a4200040300d034043e100c0c60001000300b030500000cac0000a1000b548000c0028041310008410091203210b010020040c10341030f44402c0410081e40d0f01c1d6031110040001143e881320100ba0448030f16200ca64182c10000208042c9410300e00070240384d562003070300c1c992901c101c214095401401d441d1103488140460100c03640c0b58800c0b40344501449605c4044880013400610011b4068002480d04140007401c8400900a484407402032341e214502c900302600000c11502901240349240c000401c040c1c012072030310303903040907509003076405506113080c105911040414a20a210590010b40c07080ca6416102088a241a1801c41160019000d5042e1007000c006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 532257994 1250 532256744 532256771
    0x1503050708130f0305070503030f06030706050c0709020a0e060c0304090b01110a060f0216050a12020106230105070c0e150604081015090c08071103040b041707080102041701 76
    0x10380c85200c030080302c1260b4120680380c500752800c0d801c2c000c80502808200d90f502090741000503601c81c403124552058103261090901d070030b24103650721840600005102040c648540416200142d850048005031560966181102c0000060203030540144000a645902040202c01001900d60a003020300000400b60011034483c201c0a03c0032030f00383c000c102e6110000e400758118034041600b078a005800d000540038103810329141c0442c00c0342c1d17542c00b0348454002c1040e41800034a03254601c1c00208003541c50300300055058494011010040305500c8444003c036030144003644c28040d00319060320450ba45900801020803c00d0340c01d00d0070000fa2000c05101741c0740c2403048400b81c403804005030032040c40790f402c8071028024601c0c0600100401c0800452800c80c684075030300040d900b540c0e8000043c109010040e01d40351020901d91059001008103001800240c0c04032012a1505500c50b42d03c41c401082050500f0400d404c48000340d4000600052600034682c40d540800084100800001031000319 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 532259244 1250 532257994 532258007
    0x1c08010617100501080403020c0a12031209020604170313060305070206100303140d060b0304120f0c030206271b0a0611071a1b100524210715030507 65
    0x1600c0c02c201090440074002d95100700032490300548030740100c604945a4000060301c00c0c4454100148045000210704103141e0300c220074418402e24030004110383d1a658000ca001c501c1640581750703648040ca0054001d5076420000c03a080208811002109aa01d41d080100545002d031401c400500c80c08010423990300c3c186960404403540351721010701751a00c5468103440707500980301f19070b41c070b540e640b400003110300040c80114440d511070640740d101000c8071400a00301400f501012420881d0081c041d00009800080090f001580e82000d00030601c1c101d9403e815401c5016800625800b86a0400040c61500030040e40000c8044030f5400340d494130781c807003240c0e011b0450a003002c0581c04103004100b5010700c903c000c21905600c00321035141881400d282d00e0360180c80c00000b0788660007201141030002841c0b081c04e8008007020709061000d400b481c04841d05090700c03003220b0b1041c182c0017290740c100204004104001044035041e079003403a6071040c2e040b40c94000e481c10400400d0501e000075030200e20409 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 532260494 1250 532259244 532259251
    0x1030e0c0d0b060a030c181d0601030605180f0109030806030a0305031306060f030803060f0d02061210050a1e08060106021216081c1505130b031c08010617 68
    0x40080300c1c1d01c58140c03070701603201e8005030a25410000403031003c40821038031380510b000340c044044d03120310410f41000c80b4412107402040307002003805515140111603d0200d40c10781100c0d0008008601e87d201c0c0340501c00d1503940c48420040031b100780550f0700a04c00b41900f044800c1406619081415a11802803503210300342c1000040001f403081000580400c01c0400d24054540207140002d82a9102c000410681c01640c00c29500d504001c0b0400c031082c50034500080300c1c10300540c0c0c40c1e4160903699010400300e02403144c0ca881001c00301b038001980b20071342e00d800d4002003a000781004001c2c2e03510003121806680d0003003552510044018040707400c03580042c80c0c5040ba40301342d00800410305000c401c940181c002034064070b0b07004d00122040d00880c3c180700150911007040b401d0070950043e80c3e0030040461705a5803184a8401ca00c0d0b4003000380350307214200d4040d0b030314044a0104801086400107800c2004d080c145482c08220f0321a80d03000c09500056460580703440392a4420103001d6040701517000181203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 532261744 1250 532260494 532260499
    0x30b06040509130b04051b0d030c0b040609050d110f0a0201090b0a03111b0f0604020907031a0d060c0801090e060115360f03200a080f010b01030e0c 65
    0x208420403181c200242c21540c0103a510f004000060501d55410b03901c9642524190780c03592007004004181c5445025010a03003100302c80c07030110081030380c0d0b0103880c40c1668003000d41070315864400070f010300c5040e03008030070380b10750000540d083c400b807000015080b0301c0c0300c2e00140b0340d6111742240c410310900002a00051142c0585a0f06040c0e46070074454040c0360f01480c0204101a00d0300d070743c800c0c0364100e040603005038450149001c41203161010150302d0107000e0001e00c0899881502848090b84030b038514642c200c8101d24000c00e003a2540b144044a80445070340d4144c01c04000c281103024002030703911580030010540c0e035515159a986a0f00d8040d2000d12130780c03108a800140040200303494941e606540402507040100c0c0d40c11101c2003440781e0b402d50510f50600004051035841d0000440c61188025006150502d01c9207811900c400c07450340d552251003540c200c49552640b60669803154100b0041c4802000c0321691407440c4480ca01801d400d881c144c3c00f003070909003070b282c0c28540400c95860500b4007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 532262994 1250 532261744 532261747
    0x6091a0301031e080c0705180f18190605040b06120c0904060b210706020d1409010c0f110f10020a110f030307140601050d03020a0602030a110301150f030b06 69
    0x8507252000030440142011101090307000f052400140c80f4406071205007120710141007014030304014403020041000104a40c8558034007040003111109801e513401c1220a94034001c14010a106c0301c0c604100174902e00186c010482215042000b16041103103d1840741d02060a82d0b22491f003880380c4041c0c07000c181c01c0070740c029040406207810140c203420ba002c1d000e070301d01103580c0300614041601c4c22800040c84039407050002d4504860300040010200602152004000c00080080024001d0b054001c10181c420300c001010902da81c032648100c401e160700011082d00b03480061414a880580350100d40c6d00a500804c04882da610f05003c864002d03046035005031051070403555558000c04601c0080503400034001d000c280c11521b003000580f1026115004104464815a00d21031030503070146e002504c5a11140f410342e00099005c03580d840c10550007000980c03240c41b01c002c410f01519940c48000315901c004400040e8508001441005070413a68030703081d48204403ca012010383d249071a000d90030000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 532264244 1250 532262994 532262999
    0x20f190c0503030712110705010923150903070501050c0d150e13021503090f101a090a0e011b0f03060320011202070c03021002070501171f030b0106091a0301 69
    0x542140314101c110300e100090b110146d40c2681801d80207244107035202d80d5034400c900104a01454003c2008440604811621010340400d65942d50005001c0c0c0c2c503540003001040c0324010410940740c4055200d13009220900d89201041280c4d08140c550f5419942000040460004c1080014042e039041680181c1c003640c1e89640c1605400140b40e040380c101c0c000c0d45028441d202d40310302841c015800c040282040f681c400040c1e92034203800100040e98940780ca18014001c4406c20025201100300750780d008050340e0f03070028400050070001c56014141d400c1050f11200c1c03018490a00c0012116511440303074085080b10110200c07401800001d18881441d54208000d04120603080c08034441407500140b00034400c54120141e0700f21070030856100031000e4040c002c5207810148440c1401d100d100600c40d6a141500003001c0d40400152840c4001454010070703803000003401c003810914100130244030002c1c1e4900c1c4c6154568400d124020001d06482000f280703110341c07032110080c1c59a175640e45500f90390 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 532265494 1250 532264244 532264247
    0x605040f02131416021c21020301080303060906130c050d0507030c1d0604050d060506040c020d0813111c0b0105060c0307110a0519151416030e04020f190c05030307 72
    0x5290305003000030351003082140021095404801e50030103201da50f844018030f00d440e110f10f4507c241c1c4245840164014801407004407000002c0d6030b480441100c01e001c054a0360004505001c66a1078032071030450a158008062030340240c01449a807424010400841c0c0e18018102c2c1154524408000092000d0b01c40b155680200c13a001030900c03030020a00e924140d91000020a12a43c1d50801c4440c2c0e41c5070000c000c4589030920400410a00d00d0018001480c00008006c0107804018500f005141070702c5901414400034442031004d47d50040c0c079075504450f40b08114642220300c1070085588103000c0c000400d590070000f0503181d682c2032040c005c2d03060601565a520800e0301541000350040c4043d11b0004e8550b94900428026240860441007014104024a5030251030b02040409000301c80c1c1480e5640135000c8111407810b02448070314503210340c0c680350484080c41c014000943c01400855540c03c075032044d000900698000c100c441128039101c480990350507c540348054081d4105000188102c0d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 532266744 1250 532265494 532265521
    0xd050c1623010201021b070305070b0f0412050307060204030807060b0109150809030c01060f03061410050d0203010b060d020d0e0c060304080c0102041203050414010908030d09020d0605040f021314 86
    0x81c0380500000d401e00003100c4108481c608221003500e4103030f0111a01b04103015040c80088090107803500395510304218205a504507209900c90501240d0105144909010040c0255200154403020540d83c030759403400c0954160300413190a0f6040303450050b0801c800d44c05542e60318101c0d82c5c0104030404042107918180c81e05103004060490714081040b04540b2000c0a1043e01c02402c00d420120000c241181498070071540c906003440681040d040c1031080080d103020360361049506c11640c45155042d1403000c203014028480c4400c3e0031040100d8000c3c00c00000b50084c0855080c01d610030041142c0707000504c1e41e11410385400d1a00210304001003000324030950010040c455945001500d82076403041e0445610304680825400110082024011700d070a14131030141c51a02460300e0310303c560400001548a106441c4042152507641e07c801c000c540710401c620134026007181e001c1000d4541828808011603c04004911860890520342c15a20f40c40c4502c500482e10100c1d854115038130031003180c280 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 532267994 1250 532266744 532266809
    0x142409030102070c08061902090d2306070306140301050c16231507030b10030b010c0b0406051e040507030b0c091009080c0a05131109030d050c16 64
    0x654007080300801040784104120b0082410701c0046c40240350003003a00342c010f956440610011801000b00e401c1c03550365a215213840c241c1168038100b0004030703ca0080c4200c0c0c5140c0c4050a18014130080088068042e030224040740c18610030201c000d1616010142200c0040340e412910880510a4a0400040c0070f41c07041050320030040d0035024511141d1007160303c1080300400065034002e0703e4101c0e030102c40c81e10468119406040c2801001d1300040000d50741ca034141d004000f010f50b50041407070b00341c0c45001646241500402c0e11945414035082400c080c060865192003082014680000c28000b09401760b845240c121004d07013070040c1584e440040d500e038040c0c0340844e09603080c401f100c803032707500c03e810f00702150210f444040e04030745000800f5042080044c01d80b0702c2410003075001c0246413186100926100c01000000800d041c100c0001a8940901181e054042c030900501c401020340110085c030401d10145c044030f00d03260141d204848190058001d00380c4a00c100f8140c0c40340011030401c0c00c00c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 532269244 1250 532267994 532267999
    0xa061e061e0504090b041e0203160905010e01030e07050a1805090604030507080c1c020303071107230604090903080714090f090406090503130f0b12060105070302010e16142409 77
    0x11f10f12810700d43c49504541c8200101d103141d5000003408524010211061040c080d213040601c2c03158500700010300307090b42000505040c1a00c420300389108039014020303940030f0000180501070a54442c120808180d0a01ca44505100e141030301090a1500008d4600d03c240d0741a030380c0d24a42025592801c050303410048990003244111408134403000d82490520200c01e49580c001c54591410b100010070558a061014044c2d8002d44010700040d01144413401c2415005840180e41c2000781c000308000c0c0c03050343c0c00001450b1800410404056002780158056200c540c1c580310f486140c541070101c58490750624945c40040031004100c2403c2060480d6405401804001034101d02030315035500350343c0007401c0720090a400c0700090000b481c1c40d41c841c0010f1302032450740d5424030481c0540c1031900e84015120905200e0b0104618080500c00d4000c010104500310070f403141619401804e10058405000d03045400020403144601e42c1461315034820071000212210000040704090685d4075405205a1034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 532270494 1250 532269244 532269251
    0xf02180d060b09130204050601080402030c0609150a0206091513020405040204021e0a17311505180f0705090a090209040f03020c0d0b0f0a061e061e0504090b04 70
    0xc02d643e07950303240c141c45581480140c140207821841044101c1c1d1005086a05100740c1d40c0900c40582c80018042c0028141503d9840d030381c80e48030002a10701d22018455144245000404180080d404504c03103000f41d013100e040b50f50361401d04004c080010310858802d501d4140400085015207400d0300910780150018100601c1c20041c90140005172403c01c0307803c0c0d032130302000801114040d441842c20300e860251510b81e680d141407042180c051000814003007140d0340b42920601c0ca6521202c1c600a03c0c0692045100d84000c003802c45000203800d00301d804941c80d51440c8010149104041001c00403c40300c0d4018210341c40c20101013004400c0f02074041851a84e03030711068401078940d440f6903800341e8000c400412640c1058074000740f5107200d40c10f02c44d01807075060441c000041c4022800d0354102500242000080d036030854510001c0c4019400b800c1c85a00484941e0801d06900c1c00c00070030384c0c01a50700c00044005040845c10344c0c54100049100186007080304008500c8168802101003c000b04040b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 532271744 1250 532270494 532270511
    0x5041104150303080105030c0913060615020a0b010b0408030a200a0507140109121502070b04030c02010e040e030a0e06130602060a052505090d0204150503010f02180d06 74
    0x2800311154940e0003805039001d11414400e2507000260140107040407002418442e40d40404074041300e6000d0030b03202c044400200700008000e001d8101601524003407004250040004000a40d0341e4424501074850346182400856640c00c250b00b1038054894081c0214580751003000c0842c0c00e951903080c00c5020110102ca4480a5030090040c0c464040c0218014a445401c7c9800e000000d02054001810301c0301d00582040080002c0e0044040e03030381c0128124266080144200010f4860144002c0010030800104020590070102c1d045815000380d840383d811a00500c144000c6406520101030168020f11000410301d11915010f4861140648400c1c2403516000411421680a41024002d46c0001c0304002e2074010501c51194814054142c0780030b560302840307100091060481c0c2d84070030054009a0405551902c1e0280403000790b018204002d04440b08050104d0183c0c103000f058840e50a0a82681d840e14072402030ba2750b00c04030034502d0f00c0b0b0015100100940f401580c501103c002d92902400d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 532272994 1250 532271744 532271749
    0x90c030c1d0a1505041409040f08130f090603060b0d0803130302030d0c08091b100f0318080306011d1f1716090902130911040515070c0f1206050411 65
    0x103c2d03a100e0360036242d05880b14100944000300e211031800081c065400030007004049001910b08490441d0410020340d501c144846030a0074460103a00111018200c41000107030b010060307800303802201e000b2a4100300c40b03e039160070407228200d01100903000c1401440400c4001c6080940f240c0c10310300ca40102c0e0324004400c500181500c1481c8500340c041443c1e070b020060200011310802d180050743c0340d421002c4c060600000383d8580103201c40181000010464201064060740c880003c039080b0b071807000e6110342c851400c03c0066004855941c0080d00301d540d94600744228180800c0d9400e0700031700c0d0940c41c000c402c0d01900650b8002c1401d504203c01202408a01800310190901501045858000c900601c00c005400b5006076804480180d10420100d07240c0c245c00b4600c1810b651400001061f0820328101e01021740c0656084203601180300c00303001c1c03031042c0004000c013043d500c0b480080441320340c1d0f25034046404000d031049a20b026905024000001d8603580301607806485118900340c0054404007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 532274244 1250 532272994 532273019
    0xe040c05070f110315040614061005040e101e0303020c0a0e130303140703060609151d03071d040b0c0a020303011208210601082802070203030f0a0801090c030c1d0a 72
    0x500387d90703848d6640c91851021802402c1c49034001019550340700e0031142004014030341d110300c0c45543c5010f00c62501150070f1603000d00305a0001e020064500030192074034031020038000c80e0f62004070054030420300324001c64104100380f0422660100c5445600c0c1e9600c660b021400840b10804408040e5a001100420301400600900405099400152003401c1030006400400070f60482143c00c0141d04400120b6540034402d42d0080d10b4800004140812500220f85401001e0700100c5203050a01c280310500c003031920809100324094808880c06031030f401c01c011840d200e0503421070010703013040005025403490040407941d15841800906d03c4c16406500c4030701107003030070f280250303000462905000e420b691052020b03400c0000588415006001d01d1030301501203005e00312006000d5000b1500c8400d40d9014010303282000b4810811a549001440005000f900240140e1400740d1070302070040c514078400c7c82090380045640c0c840108040e00b03150300c14000219a150650f2044034000f010900d20b50303200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 532275494 1250 532274244 532274251
    0xe0d1b1407060e030606060702100c061b080a0c140f0418021c0e0d11011d0a02120c031207050a0f03050904270b09120304030e040c05070f110315 64
    0x30040c1090508210009088070b1003038983d42d00c40c0e40148140a4503503614000c071200395904a03a140303c0e588500310296005105d404d000780665292410304064856102160051140c00b0b036600e075079035039039000072000701c0c0c401c0c00011000500c404030031403240c00340c940180201d04454445508260380d440041d4402c00d50150304618068010404d500b02c02504500c600340280284070034003804280a11079683d50480b0300c82c1000300702840e40c04025640080d406950008144004c4414800304110b13126a00c1c885c60f00220f00034202042e1406541c2c03400300e8240458031004000d4030744400f19103181201508058403d035130368015030241000141c061244031055501c40c2d140c8036124072240c410401110b4000c500c1401c0c0c1c180c1402d0120006099541448801e50310043c140c4640d1030360b80d6220720785464070105005541e000000e000505030841000440e240040f601401200d000f458216500c5c050098000c00348903c1030f29520000d03009800d4201408400380484804805064243e6070000c1c068 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 532276744 1250 532275494 532275533
    0x1d010810110d020d0b1302121603020f0c060405060f1510051b07030c0b1c050a14180706090806070f030e0d050c0d0804031202090a0315020a090503010e0d1b 69
    0x20983d0403139a06001e5a811001a0301c0c906c110304010a070340c40303045e007001c0c0100f28800d800070709540084664020760540d21000300c0c0c40e1910f41c1f60079002e48c026036602025241070f0b0340c8d840f56800084089000300909403043c07010702031400c601000082403080490005901900340101808000c16854102403602190b10030f000007001c2282c950304180d8000c1d450364000c0701c07e070f4004202801d89001c40e00320031400f000f4607800c00605995000007800007030002503040c88008655400348612250b0400404403150110b0042c3d40c009561514141d41031800351080c1d08141c0c000070005a1070318010203070511380200604011640c55408486c84d0705000c04440b4040c041000820883e20a0700100b00c5400c070711405083c200f401c1d040a071800f8002c40c002d14900e80203c1d03000a0441d5181e100c10b900c401c001d59000124180c0103204000310000307074110b2074071031000580c0c106d400106494140218941d2540c1070010f07041d00c1150034000c07240403601c82c1e00f40401d40764150021002a030b290a590b08a401d0304e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 532277994 1250 532276744 532276751
    0xf110415091706100b090130020f0d0b09150f040e1609150f0b031b0a0e040f05150409050f03040308040518040b180a0b0703061d010810110d020d 64
    0x100d203c290600070b96040545c0c00c01042c805c4a4030303641c2110460340c2c42c0204000002480c0c00105d101c220581150042141c1c550010409650a4648070f000d84008070a080301404506003003014000388031000c580c00d1031a40d800703101548050400c0c81c40070640035009000890442c1508900ca40341645d00390402151541d000020000c0d01c50a10404081c890b81e00700c9008000e01d825851240444203019800b01118000045880c01142140d01d5a114401601654444240203009420010300c0522640502c0c140502140d07550400e100d46445040d0b084001c0b0918550b8205000c01008182c000b15040d228104a6664040003080500000c5128a440d03666030350800050103110302c180550901c0001c8403806000c005404481d566078010703840c0c25903542202d82c180450785401c4902c100500082e80301d17001e2284507507154020200b51001c1691520582181110581c400c002c2441a10540d8025007000d03074004060781c00c08480c000703404000500b0000040e424104070780c8804c00342d856240d41c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 532279244 1250 532277994 532278001
    0x2040510060f030501030b070513030506040302030901090512151f240f050a12060513090b0903070b040227090f280308060118180f110415091706 64
    0x340803a207004120701c0ca1a041c030182d499540c50b8951100094423480a008000c00d0400110a0048020b0021500901200d60b02d0400703003800303901c0340e0203c1440d9000514540d00410142405005446100300220040608500c0e070b15102c0390042001d03003801303180824040040c22031036042c050034000d442c1c03590a1402d041c000c00c12019880622458400c1440b24004a0f4401940c110040d11203c107201d060211070744644e0410301c8014a0356820050380a203140b5110b04007002d40c0d900c25504207105900a514a499901400c0d6030b074012100001c022503084e1000600509100d201110140c0c0303e5003502400d180804882610005c0232030350301c030b8583e01559290449a60420003c114516052105114008181c00da0207461480d040c003d014407a00901207245a40700302d00d141c1c0b0180f01c014910b030880e0b4842200071104810141c02e400110b0414000c10304115542c81018103007140c840c3ca00d80742c03034913105142145a40c401101b1017841409000080c08143c2d400003401d903005040007400aa16 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 532280494 1250 532279244 532279247
    0xf0301061715040507030f0804030c09020c0708030c0a0809030f0616090603090c060f020c040e0a060b09061c14061015020a050d1b02030d0c0209010905061f0c0204051006 75
    0x4840d4445940b61405200114401003010429079800012010680d845810903a0301c52007107a0004184c0030749035000080c3c01c103a50b4081e01c0c003404542c4c1a20350036503686410380e13a84d000340e809010150b0421030117280091801c400030040580050f0a5980750100385450f40d013010400c0b2004c0c0442010188a6103040f98010b41c918090802e506040001c11038540360100141414021141130082e6065101060707070003040881c0300004010700500c041658440e8058882110f0f4030215061401c1003900c1c2600c0c50f180d0020303846242c000c2d003040e9103030480700850800494061000d60341d10300d103d40d118100890500c0601c0c0f04108404000300c02e60b02e00400c281c8901070304110b600845d002882c0d184005040800c0101c014101031900881c1ca181e0301c01c550603800f0240c030b002541885403034040007000d80c1050307121042c28002c503500c0d401c07aa40c50412009650003115050b502580401c410014040205040300d0007880518001d164880554040b60031520240d5004074030309000c05c0108242d6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 532281744 1250 532280494 532280503
    0x15090519170106120b07020f06192901030c12110702090601020a171305131508030424050d05100305190209010e040f08120609100b0d0b0f03010617 65
    0x940e0020019141380c00c480016025071180010204007808011442d8644200301c031441400e45c1105a401906040c00f081020381d00b07000c0780c080e009044c84118200741c01010042155a502d0140400c1304c0c400060046009001498250b03040c03183c0b04030b050031150114860290204500760351281e6842a900400035900d070000c0c202170440d0b001c1c0d0340c40342c001a4a5503984100d0380c908500e082d165540d86c00c860b40e42107841d0300260b030403603015179010038200456084080101c2d01c40c3c40ca0703009503898940d015240e1045009101802d581c800148510381c6400b01c00c900c80741c642e860b040b81800c052620b02019900140d490a0903801880c4003030090050a0140c10704120b200040103a5495180e4041038185d1b005100d00e00001780001e00040901000b000707407150040d8400101d036a02c035074045000b54855000c0d56514043c40c010b20000304000c07031503407041058505100c120350a0290900c0d011014240403c40641c0042c0c4240101980b51030902a030800303800c5442242240310b00400a603440e0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 532282994 1250 532281744 532281779
    0x6070f030609023603010e010504140c01170703021201080f06060103051b0f0705011103160801030f122703060b040204030c050d05031c0e06100f15090519 68
    0xd0b01e00c100440f042d074028002a00340b603072030180150000b5150f20b0240c83e0090001100322a0154208000d00030035003810760086126600c51704c11901c0c80c000507107a40c1c0c0c0e1421149910b5010030386504200643c4080c0045240c0c0c00708061401524025108004202424081c2d0240b0b02030361102e001d00768134030b03c144401e50340034030b0038030301009607103480c4c01841c5c0200d0700c81c002100e80110000c0e9142003001810120b82607560064001c0c042c122542110560561088402c444003080450994052130300ca60030480c1200e0300142d0f4044e080800352501100041c0c1070040c18144885051488801880080c1007556003501000c150003281c07031170a00d0425600c0902040d403149104000c240300013010000c6100c2521005e41d81d000c000105480d100340b452041084049100c92180d0700811201030f59046056808030320303001c2e11030036200c0c0003000d485941c09004100780205541000e0206403101d010070a48000d407803803e240d00a0f5030304080b03588042600380320ee990101c054401c4c07040d040782c0d6611915 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 532284244 1250 532282994 532283009
    0x80702041b020d030e0c0312120a06030b061c23010608071a0f070b0103110109050f010927060305010f0b0d11010807030908030f0612150402060703090806070f0306 72
    0x140c0004641000f03444401221082081c140e5450803170701105000c12080c0c0b8041005030480c0d284504010030120143c00106403c502000710600150300701c255400707410116540001c648007161610001c004000707060b407100f0042c0140c00b50011003c100c13115800c00b5255000f1503072040031180455003e095410a400c042003da000c007008000d0445071604c44a041c41031000c0a17504c40100444515862040040141942500c00004000c0c0203180e01b83d025501403d80300e00e1001c55465003481204459444ca0744e000c80c0c2800c20810110404c20002044080e81c0c3d0f41c4680340d810410940d40c204c402e00c0c1c00644883c0c0d52007101122610075407003040d04d6500200c60344884401180d0342d01d000d501284101d036041055000c00b01c2c40181c085d400442010fa442048552070340703811561600d101c402102e80d5840b60210307101002e81c41401040e4440c18503003c00b085061540c568007440b02692042d00103c0030040d800c500020965800c2c000b9900907211a82c03003150844c2806002415101c05801400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 532285494 1250 532284244 532284281
    0x304030c02043e0c07150e040c0c0605090f1b0307050d050d05180409031e110706210501080a0b1e070f021e0114090d080417040801060308070204 64
    0x3d921061020108048802c14001442d08062640710780c0e640e4018004c884c0760a00c0f415001003400440c40c822980700c2c1300c26585002400301403004000584501d40620b07008501c05801e044082015a000941c0c0b0550040c00c445801380b40d00025481c1050750303882c00481c1203d0b100340403203038501804403c0085c94201c411010b0200c2e40d44941d0789482d08281e403001071000c0000c0c4861035003180000412030380e030001c0080000c0350042c100a003039081da071100d1012081e6045a50001c2d01c0c000c18104614071381d82070040042c1c5051072400d03a0740c81c0c90006020541500500031b0300d80e40f0b4aa003e0f40e0f02810400010b08000400d620380006500d5028004480605040101104c0f1080c0075010320b0f48169585044800c0c202e03404026130420000321842664100e881c000721300ca080c1c054010360031080400d030340400240c1d1120f0440b81c07071300c0c600e204040c006410140490080394007040811961021030a00c0c900c0d0594400009007103441c0c9074400c44100001050030425841c05225504080c2c21803603905 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 532286744 1250 532285494 532285541
    0x1f0221010602150901061805151203090f0406030204050a0b0310020304050c10200d021204050d060c1202030103050106030317070816020a0b0108010e210703030b150304030c0204 78
    0x2948601203c5103448141d0201c6002454094003508075800400c00040002c040503550345501014003409c483c10443c02c44507910005ca58284890450500c06220004e10f0038050008104180044604111070384036489d01400f101607601c622030f8602410101c24000b848420803824142070059040305203202d14418400c000c0401c0c40420280c5007010101d0b200f00261110910540c0d5104158080080c5086031100d01004640009403450080920340c003190801c50031080b04510902c40c9020b0309400c40e065400410000d215078109480e03001e810706060419090041000c4101d030826441900c0c0c507034488004105240d0045103c0c004007640c460424644d26140101401030b00001d054001491084181000c0c814800e00100b0505030380802c00c1580707560b54901c028064600403d040e25280915840303024004002c002c903601480013001c0c80c6042c14090b85050740102000e0036040d4002c8403030303015689400705c00303001540b1840c401e0b03d5080888005006000840b80550b222100402d06095079 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 532287994 1250 532286744 532286747
    0xf0608030f030c13350a17090607021003091a040b041103011517071509060e0d0804090504140705030705040203041e030206041a0609010b0c1f02210106 67
    0x201c0742e1062042002c1039407110601030105018110ba0300c9100d00300d41104217017421440d02c071010900c440050b03002540300c110303000c812034803800403800040103103060b113424260740c40000015102c0c490000b010a400c200154000c100345124243c502030009030750788030718000c100c4480c0c401000c0c01c51500f420070b00f0703280c9680c50100300203010300f02801038041d245980b1210341c0c0c2508100102c881d1080d8075680343da170390541050210a0080e082c651400f441d100464042c1050701441d440040c0c556800040f1441c01509860010b421000c0f40d07048001c03800c150011811410080c4001d128a400019191925003080c039103100c05016140159004510f00301309680d000580e00051341c40c2260016941c0c0c0710b42c0b43c400200e00f42e089101c0a6044000040300c203250300841c03614811401010000c0c242c00c440762102e0242d0804492305035100c80325100501001d004000600159032400040b55190348004910120040c1c4890810030b00980005551040c1904600c01480008a80140d000302c1d5040580 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 532289244 1250 532287994 532287997
    0xf050109030b04111207170316021504050405040809040f0b06041e080f0717030306010c12111f0b01020109050d2703030806090f060d290a0f0608030f 66
    0x1030910800d0402050520400c2e160810700400001c0c40036200105c956030550b1500b049100f40030150546034800000c101c8048111003c04200750100d00b072031400f6031308001d400c40d990048012061000d00021403d52120b2092900850042c0700594842005d40200000c2d50060800360303041a050005030f42203030b02c41809031810780d003070800000c940031680001ca4048807091341c0112001e10071090782102000c00480c0f824280c0301024a5820103d84180042e642e0384003e0300c0550000e1140603824011501c00c05810725801c00921b4a07031501201085620310381400502e4019900014000c0311440c5503103885121540c180a000a2000301499241c141d01e0b4000c5006650070311071400700307500c00d1750a01001c25165042e0344191800c20f07030b183c0c1001800c06000b00e41c8240900e42400102d2002c2c80215191489144002c24001c86142d444d0b8401400c584c000456070300c6101c070103aa164585110300e0704544034842c1140b000402d054080495002d40b0b4455100b903080d50410480d00030980101030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 532290494 1250 532289244 532289249
    0xf0c2101140d12080703020f040b030f01120c060e120303150f010c0308010506030711030a050a0e312003040c0f0b160c0905130605070503060609010c050109050d021005010f050109 79
    0xe241340f1507030f56081c064010344240540f01040c07100004000c1107401f4640b000c1c43c002c1221b10742820450781c881d00075103640100c1c480c0c003600540d1081c0c02003020910510070103100b082c0142c003881c0b10540b030038903013440c5400942d49400f030141003010460503400c200c00202c074040c109107400074105006440c050f01882060143c1c5014040000001c1c80250151507a01d034142c11180441359500b40780080200590031032000c4000083d9114440c1707000d480c00a440e03042c0320351f0550f6080d00142000a201e1000d0f0146040d030050782da10340b0700c80359150a208404945480c12448139941e40d190920b007a0241d2202da0f002030b15010030a090501216120300b003660394145d1040c0c800702942c2035a00740b6041c41c00550348440040c5003880c040001250458045900c2c080c458482031103181c5452000351081d003c2110001e40012050205110640c400c403500030b507460191000017218901c2c0d840791420a80000464009a40302102180141d2843d104190040940308034040c1001d0030100001e28000b040d2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 532291744 1250 532290494 532290497
    0xf040201020c010e0a051c050601150806040606050d05101a0a110105041211210406031a0306070c06020412050f0d02071d0c1903060f0608010b030f0c2101140d12 71
    0x1150b03c2c54400107c8000a0101500700044542540e0358610a03030070f0000c00100100094803920101c2e01e0b60510340514416240d0b1521081d040c814a1a210001014001c20001035841720440000f01c018048882400c400d02c5800740540e900300060014001c84012500120036a240800300070201c4c5140c040300708101c020786442c526006040708403d181c1124682c54010129080c9009000800248000d000b101e0181c0c40601940c0c517120440741807a440d070040e0b0303074042e0000000100302600c1040c140918500c00d88006091a44824800c0110441d5031412500d950240103d41c411400130055881c0c8a440c0b80b00401c4d01030304003018040042c07041c4600801111801c004103040d8200c901c01c3c1c07400814000ca41d1110707109a128018003811503449034540e100c1459401103021881403d007035044e1880036105a00c0c50700c07020805800441d00505a407080a018481c040c0041031018110788003030005407078545107505100502c04020107500e6440d02c9075070402240c10005042840751038903020170317 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 532292994 1250 532291744 532291759
    0x20f04110c030d050403090509040c1e0308030a02040f05030f030d020906040e070c0c1d0417041d010302130b092a04090f1a0618180f040201020c010e0a05 68
    0x1502001916402000c070a00040e010108011190710001d600840c03146004e6030f038003907039540d444041c00a00c03001580c1c041c0442e45118000e11105040b020001c01100c080001c85c504603a480d140d64500f900255062855182c00041c2040b00102014051001d45402c801400c4188840d00110f5600d200c1c00c209a40001d40101d070345121640e400c010b80740280900c9075102910320701501c005200d00701c035007422180050302040100b031281c00e459280d00078a00e81680341c119a00c868072002c0c2c0c0a44031a100300300010f0200004075201c3c076601c1072503211040001d42255103504610400c5050108a00048062464811a40304aa458605d4650041c8c0070030700881d1480000c1d01c6103040801001c459140ca2480020001000340c8503074080341d2108202141080034038403540e10a0610181102d00c10b41c098014040280c421410010302104410700a15180201c8101c0d030000d032610901303c4402c042c11001408210940d40c0510000e00340740c0c800d290144001c2c584100007a142200c500855005081 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 532294244 1250 532292994 532293011
    0x102071a042c1006020c0105090d0c08061b2505010b03010e0c010306090c02060f07111618051b0a05070609080406090b04361a1507020f04 61
    0x1448801c4078082d01d00c0244200c0d48446200000d4894000501050500e81c040d80c0000c0100780d4280301803096801982c01307001c84c0707501c0000440e00d9400590b002e5901540ca0100600000d841c07150a070010481c0c04007400d001d20b0107040d00b890785103110120052410b420801603034014030521940c03000200b1124512825001801c0c05401000c2038004560150718040c0c105040311000201c600612030241d030140600350710307200c840e01603604e500e10f8203000d64441c0010403041e000203018550300210601e8070b80c000a0f19070030b006242c4110a40c0b403117654920484140159040c0c06580e801c4014000310a00032414051100d00440740036110500380003401080c146007451150342210502c54110000b070107400311600b00800300f50310a11a41c40420b20405c40011041c5400c0292021204180000000034090305480705102451050b180c00c40616064180c80d0300341c10b44151880e44480881001d107002800060005d04042d4000040c16400188020001039035492281100d00710140c070f01140884 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 532295494 1250 532294244 532294289
    0x2402030a03050a1404031206170705040c110712140102030f011a07080d050108190803070804140d09033e030304030209010312030507030218011103270906040b010207 73
    0x210113240100350410000c1c8020300d5803002c1294034510411008011a0b580d4880c030400032005d2141031041600180300030081c61500b40c1c4200180340d41030a229986400442683d07003800d91940103031a440164800350401d004014002c00c150048100c000c5165040c40c101804008e40c051144500c0d403114815040b128107101d000f9510006c2e40400e0706038981c0448186900940000d000343d00c001d101e54030341c8860f016010b0001c1c40009400c94031161460b00ca100c1c044079148030090003540c1c501c00142c40300c3c600c81010000300c015004e0030350760381c5060b904502d8203c40c1c0c1d080030310703008c45440041940d801a1110000c1510440403003110384030a0106d682c00428110f005640c000f0b035000280e0f00000052001103c004a4001c03a90b036010089a5a00f45054080b030180c840c410160780c1031007031504100d50140300035075644403d94007124108098440c01e4000c0b4810440002c061551141d07009007d030070110341c11500400212000c1c40f5426041c0c2c0001d5455002c0d204800180b0003180035002c500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 532296744 1250 532295494 532295501
    0x180f0b10180f0f051009110405060d0906063c090c020313060810050402030402010e150c0105061008270a030c110108151302090d0605012402030a03050a 67
    0x4218054100003989440e1910780c00038018450b18041c0241001494202c0f00101c2c86964810440203516041071410070146c20003e007188005401c00b020100004a22030355000d01420b003503071000c3c1022070b00c56400c0c58050142c07a002d52001d2840700003961b4402e00c0102c2e04951141c0d081d1140d074842d500075000610700d215075055a000307800c030f14541110b00404036800f200030301c01001241f51042c041d40e0b40d04422150044100c43e010103001550300c0a10403407405070002c58105005241a80040801c000041c8000300c1c810601e181131300340010708030500b40d400e0242d0303944200c08840b044800ca02e408805860240d0040c1a1441d85490072291005220b2980e55810521803000c2214148800d51078054450300d00309109031100300703c0c9a4100315a600c240c0042d48182024913030104030b00c40d090305002d11a88813440c010541a000d000400c0340e40c652b2406104058002c1102140075450182c1644a4100100c4419100190a036070601c41580020071244540300c00d20b400100c81e5207000c14003004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 532297994 1250 532296744 532296749
    0x60f09020a09020c160608100e0f070e041509020418060803180a12050d1209050d080601021e0a02010e030303132010120b04020a02060118110a0503010603180f0b10 72
    0x80c1c005c01c000220700160710102c1548110202c19803a01c00c00e07103a040706140e40d18101d42c41002503080200090016200d0200c85200404c0030704041450039481c0300070311402600b904500da500c1c0d40410308100302210b00d50700c0000c0c9801c0603802c00c01c03582480e651035120300c0b0f10714119030098070b151011000b80d02e4a4424400816940142c00c07841071091410f5620f0389040300c0c14400140598040740d880d10721a128400740c41c1c0e0b000c0700801055070b50680a07100303940014a070070b06601411b8403107001d207503072581c4024240c521300d00600a01203103032002604e24044c41050070700950082c01005943c81041c1440d1340344a41044c0b4100131110581401c0038070350000b0036465049000c182a680200c3c1c1c200c820465400c04018040c0410107001c1d0070311089009000c01d5400590102004001c1641c1100404080d029004401300703020500f9030110b0515485200503000040000004001c815850701c18040c951a00c40c941d1207240f0f45a49a081a40040100240c00f01c207001020030a000d40b8801031100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 532299244 1250 532297994 532298023
    0x2120a020604110612070302130f08100f020405151905041206020304050a02100302090414190b060904021c060e0408030402061606150e060301050106090b031902040f03060f09020a09020c 82
    0x42d9440c00180040194109e05860405405028002300e800c4058851443c1640c1d107000080c29060945049800a0410000720141140c1e0070000400c4036210010120034203600310b000c983d520208000e107182c1d07145030703180c980c1c0030000c01780024881c0085036038800e10301e240c100801503200d0b100c90601a06040038101c00a51084081014201c15901600944035817a400c9800300610301d6001141e4403403800c1107400107a079440c03d00d0304207405a40f03a4004a00a503010307225600705004480032600700da00ca045500c950403011440954856904e0046030090303d0728104014407410690f5036100e10307000c0584024803c01010860403149007001c02c8041d0050382101c000c0c09101c500012104200e0001d00601d03012044c1070000420904050180038100d99141d07580f500307843d02d00203c00c03d09410140c503000d080380c0603114691140d0030070700207013010b450740e025400080d92542c5498000c882e00307601e003000c100b810001004056a940c42600f41280c00c0006e01599800d01130303a030542090f5100381c0380203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 532300494 1250 532299244 532299277
    0x1308010212060918061f03050304080105010f1e090b01020102120a020a0e180a050402030f0d080a05091501090c0c050105010f14011b0f020427020102120a0206041106 73
    0x610710008007036050080005503000e003400c0d2561940204244c0d400101d8800300d40c0b01c4004108440030010500c0182500c13400402101d0303490b40d841c030b0704550081d400811260344400050198205101e04400246000c52100450301d041a00559042c08584222840c0e207544405694107039000390110b41c1c501440c265002030b913140001810000790060311a440006540706032407882800c003a002c0140341e856801032008107a403030601050180c200100220f81500521800260121702000310041c40b10941c2c0303541c1c10070314203d2406002c891004069050f10750144942c1000c0304424801c6605443e2f0f2101c0c045001ca40342c0c1d00a075082a50f07a500144190320300750000400301c2d1007003010b1080d00c0d1000350708414000440c00450741c50382880c01c0d52007175204441341c280005e5060f2811003100c5201410104844200c5420045070f151700a400811031030f424100e171800c66905015510b00d00280d60010790400718000b400964848000340010000b04520000031202e6a50105580c0d0141403424601d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 532301744 1250 532300494 532300507
    0x608010e100504020703120f1a1201140f0402090601090b1b071e1d010503060a020304110618030f01020a200a020301021c0608010b0112151e05130605010801060513080102 75
    0x1455220341107c0a80d51a15101d800207070f4403c14000e580044d421403803050004280c0e101086082ca840340b0180642c0d40d6202e000044a2030f410760340038030968000c0d114941910b0540140120500005d00315810480039580034444143d0013000e9640000c03580348034007040d9018074126031510380305420060150380482d8005103104901c07422441541c818601b00407080250803001d00c0c15250a000e1140d0641011000500000650340030319801070007800d52111501c900d070042000da80c400c00c041c1204a0030440011881e0a0030084c030f2503000c02c090001c52903c100c0b5400144036080304080d80300303603080d18200c1c0c5c2d81c40e10081100050154000b0000c6643e61030484201100358884c401028009040180000d11400d0601c11501e151174181c546000c0c080704002064010011a2200400743d141c01e0408520000510504150310500380c20304e0000f103013408200102e41049080d211400307824803405000c1c0380d0f403007001141180d0050074000d4480c60408003040a512854010000c590310203c0c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 532302994 1250 532301744 532301747
    0x30b1005310305010f0203060a03020111070f0e04050d020607020322050a0b12010f060215040303140103060203151e010e060c03120a0b030102070c0b0903030705060406090302160608010e100504020703 88
    0x41002c0364824002009450140044201640000c81d012a40703d00d600100b0009540200745d00c0440400500582d03070301e191903002c90680c103419030304020502410201008204402000308800090741c07030009141c0d03441c6c4200c0c0255a44038081c840c00d285800c420b401401c20000483c040c004d030800503c1c00c0056622008074403103e800030b41842c010709868000004002000280900c10794501c2c0c1e0160100c2e242c40c0c900e00c801080003070021400c1550b1401c51071041807200c001d0321702071440b890340503969082c0108151b420700304806529100300e180300031b445100079480e003080030300040c20300f0100f0800c024140001c5950080006c140d805000008414070500c4d0141c40c2188108601c1c64100010b407940800e2500702e018552009041c02c0d01d43d44d0a00c01d124101c07028003000c20300101103924284450365a01d0408105543c21640300d6114134211003007607018480c0d0b00b000e0b44200c04602e0f880349080d00007400303100180f00f20a85d030304807070010400c000461941c034405010050001d55a41c0302a180 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 532304244 1250 532302994 532303087
    0xc0c020d080c0d0c03020d031d0f060702010507090b031329040b0109020a051e0409020a03050f011a03150d02090c0912030306030d1103070b0403180501030b1005 71
    0x1082c1e07015807602403024500841180c401950164020905d0707181d407480a40c000d020a20084001500300e4159480ca00740400140c20140c252a01412440c2132003135000c0d00f564001740820040c080d0500d010322a80c8010b405490740030300c1b560344010101c012802d004104e1260900300b501880282c0f51650700b511702592001e80168418034413a43c650f80e072080914200e0040070108000190200302132544c401c00303500c0c0e050780200c00110407480c00d50361f25400400c0340e202c0da005001103522881000b80e01700003602100d005200ca0214003141b11441d803540c48103440001c0c4910f9004201d80c1e4100e20035114400082c3c0d00583c0601044a1420000c0050703041c1e412181c500c901c1100750500c040140076010003036a0250a02400400d2120000141611401100b6150030150302c03042c0300060120303e15960850044c0c4c026100e003140c0e0f54409821003280826034111324141404d00200040d162540081d110740e403c0545051522742001d60403140300b003035007002a030a0101d1030780c8196031a1140300c00e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 532305494 1250 532304244 532304257
    0x40c2a02090906220201050706050402031614040b12060c030703150f051e1f020a0c060503160908101a040c20070f03020d150606030c0e0102011a040c0c020d08 70
    0x360100d1a000e11144c09001c200d286110090005e40b0501c541000140240c10564106200400750341341080001d12003569907045038400c0c26a21006081d88003281090310541420002c29103016010784280060341e03a440070060043e00390040000f0001d9142c5100780d0203001c0c4940100c81240c0c4c010350780c040c4007000c1c6146005451140c08030b40420f40c180c40300c1d5800c0520070640a8413030030041400300450105416190701602c00d6026240310400002d6142d41380030060409522440d490f410085060906000b014001c00d045c041e650005104489001408020075000d0510200301032001550304030400011410841e009401c0c1400a402641c05c21000301c3c4580360320122800c541440580942e9480c0c00e40310f000241e00f41c5c11011310150406c060f0141102c2c0c0170b620f070424000101e03e000011240e040d07201e20000f0b0f5944801040c040c1c0d0000002c29089001d1001748403069a4085400007614a51304083c4269628070840f08500c0c0038910441d1442d800408003861821070341400748090b84001d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 532306744 1250 532305494 532305511
    0xa060e030706060905060315091e06040c170619060801020d05041e030c020603060102010e061003030215010e0a0b0411040905150a23010e120318040c2a02090906 71
    0x210000c10184d034240710341440798800500500d0000e003091b0003071101c00c0019155605074000c3c101807440c0f202d0001c2401400004103801042c041c9024146400c008109800c403226051041515215030900050724a40240740a41c80c40c2180ea041d9401c03900419140d40034081c1540085074024944989900651040740116075100808562601c0d030f040400d90340d0700c010081240a0032190241c103200005d10f50114040c0000940200014120f81c9000400c0b280c8440c2159203d8060003055030500ca082c1802c01c0d4075900c000b070395041540300c0700340440081c4130b0302c800b556130485000039594641000e8000d418a469040e500d075218441100a001d0440d445201074a0704950003465080a0b843c0710100c400700111300103040c40340181c0b05030301403c411000d070400006c204110000d0f90348107042070030203140ba402150f40d40c0c045d080c024002e00e010b07140396200b1032a04080c0010950071108080544240e00700507034003813000411510340c0d4411200080e41241d41c00041040c45500000c6c464000d0612 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 532307994 1250 532306744 532306751
    0x150603150114150a02100207060f060e07120c090e0a092118060503040308090a17090909060613110c030a0201240f05120309031006050109052409030a060e030706 71
    0x20314074000b264880c00f070f415130060340100d401c01c48508141c0d0142012611814020664201d03050a40701981c200d40c00103600d1400326414000ca42e5001125070b03001418500041c0840d000340741000e483c0c20103030310801c1c9420017054002007002d000c503400508080da02241e82c14040d000380310303840981098400a2000304140c42d116180440c0c540c01028101c44041c1d5170585565540c0da02110404005020114181304208110340006c1802030514541d6a00340340982c2c840c10650100400034001404032134882d003020b0144030081c3c8130402034403070800a0080101d545103a86141080a1041a150116902001c501045215130640203041c541a20a600c41c0c032442001291125807122403240c2040e606003440100414142072440d2a152242038084c1d078209004100880d09000b130030000020400d54485043c00306681002c2008003500003994824600301c02d0000100d04200584090801100c02240704100b9903400c100d2580355652052040c4000088120450350341d40188404881d0300d420b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 532309244 1250 532307994 532308019
    0x1101060329011a091f020c04180c1e030f0c06030c051315050c060f06120708060604020c0f0d020105010f090902030a06240f150c05150603150114 64
    0xc240e00e0035050351070303540d094200f699101c4010b030f80c242e0054107116003084806080310700a201005951385100081e40103460b64070b29400401c411100d058208039200c10540901c40040303407480c208441520300030303a01000f109001035509642c040b45503100500401d82424210204024208060100c5551351002d120b5211000c10a440d01d01a80c2014907402100b4041000010440c4440c80002c51541c02d186141c01040c02001c1e00780b6404036504801c100b40030301404002d0811004c0700510f25040c201421410341850341c0c0c0c81c0c0b10342c00581000c1c81a074000c2910840c100c814442c00612007070400441d00c400080c88000ba010340300900c12201e20580e41100010489a84e004081c41558020060f0085051903a10f20008003001a141140c1200c00c00b4581d198402041c0c00d41301500300d41100321071f800c0c50700010f10841103810124108100700050804c0c001100040c500d039540e0910300740021190344520120b85030490511001030703183d00c0c5c04000220346800101108031030301c0c02d80e80302a6080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 532310494 1250 532309244 532309313
    0x90f0204030515041a06041407021608060106020714120607080405100507050301030305071104060603020c011116140f1006091425030902030102070b061c0b040209040311010603 78
    0x4800c89000d040c0d801c0c45e00208507044540701d8100d0303104900078800038100d048a20344183c440301c1140c640c4056480b120566070480c451800300001000c200f03008204543c103008000b511180300344680a400da504840100c016034640030001803850820003107030180c0c5408a0010140602507030166030030b004040c5400b1000400380a000c0c400d60705602e1307840c5075900c3c60340c04884c1588104825203488a51600041c170550300c1d03001d140010201c9a030050789459540030310a08488048142c1b10201d8010445062210300403524681001c0d00010426240091000301a05010742d8191707081d018020400c0307a000b030b5045640005c0a50b41c03005401c00c20300c402850307180f650302c04c240d81c455051141c2280780e01040f02100110f10005c40d4628003c221722001d81d011034203a801c1108101c1d11582c80c181007003800c0c20045291052a02c8900d070720f80d1060016141d001011b040504064028044003000409150060752466880220807008200c014ad0784d05010080c802c0701d12804071903a2042d0350485881 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 532311744 1250 532310494 532310533
    0xb06041203051c11090607053c07050d111c1b06020d08061002010e03040f030b2215060308190e060906030115020a02061209010506040615030903030204090f02040305 73
    0x2070480d0380c2c070500d045c0192041060350b81110f81c0071202e07440707119031100301c42c01c03011003249070703401402048552a1800c4880011034101083ca40782c3c1c65015003020405585c55003010840340c1d4000301019000c0c140000400d00c02c15010182e21041c910b071000d1481000280128100c450382a5200c0305802503c4142c12a00c0d2860000640c00103a078000118610749000c041c1c242940074240000140380e4003200c0d0940c11904298081192000894010010b00004440241c1d201e00400700c6280d4490100300e00040d26500345001810f40105843c10100c2400325600410280d5000980e040d212807080c106404448456040640001c070f0071542406c01e41000f809070f03031410000902c0b90742568240508003524400700d2004201b14441c403200b08001d81c440000400c0c12100d2000038060718036102818500b90342c0054020381c0281d1414904110040790507800f8522038011785808a890060760500310301074010340d080300014031b22b01403075540c600b403442d40140b007124851416203007400706908990856 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 532312994 1250 532311744 532311761
    0x21e0d0b0d02220e0703031106090604050703063b1c050f1e0a080403030c020d050d0b19060f02070909021f051c091e030905040b06041203051c 63
    0x203082c00541d600d0f8001032003901d00c44021540c40000b00e9503840400545000000c1d4815400305d0940c080d1001084070038058250710023074450003020141403039a03030030b07544050718072000d019139070340340d02d1500642580b8140c1030340c800750605640d0305a171000c00e403111854004000304032580b2a134084002020358a070092400603800b41c440e94109001814801c01030340c0800b0385c00882c3c02d56000e007014400108409015000503035035419515150914001d1700725943e00289205550061109107000d9500200301c0d032803071246010108400b4180d17000f04560190303244031310180c204a02c10109860b6804001106909400d50880c0c00095403580c48070100d4003800c4003c0d401c102498444d2400821b2104c03080e512034401e01d015480d084005005403900105403649100c51900e0302c0820b02800f00c8038845030072404ea40b544600429520303641c040c241d0910381c031946010b5a01c40104003840d85c0c0350003e460003041191103190515050785002440c1d540042d02002d810502c66403045540102c0307100d200c02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 532314244 1250 532312994 532312999
    0x11409010f060609090f020c01090c08120c06060105071b090e0d0e0a0e100e04050a030e040b011d0a081203010905070507080a120e01090f110d0c0e0703021e0d0b0d02 73
    0x8120304145000c0c5c05080b08185082138550200410481c0b800c0034452038085034080e0403900c0d510782c2003010071414032813010400301c10008140b04010f840ca8001c980349800403c00d0030216580c2e40d040c034008444206403148541208401107001440740f0703280c0c0084455114050558504d1540c031103044d5040d00c10007101c01d0b000b80400505002640407454025080191001540f44803650703242c442c08051030844044a064001c170048508060b0002c0030b085403403408550a02c010310032480002c143c84010b150b03250b003c0580c800200800d41765550180044d060ba0421f03504260b00309100c0105c0d0307070310a100e01800035103460000756a880c42a81695991a400754109140042160b005c48031100304500401070940d41784030f101041c0d0002d1040d103041c144125801c0d50005010304000803210b80780040d8034010601035003181e0000742c141c45100140c81040c0502644c948602c3c0085000340160652094040c0c0b9009208641c5045c040241040c0c000e134030342c14800004180c00780080311207269402074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 532315494 1250 532314244 532314257
    0x8090c1801090e07050a0303020c01022112040303110d0504110306010e0a15050d030c0201020d030e0c0603043e01020a03050306010f03090b1518040b0408070f05011409010f0606 78
    0x41141c00541002440300d112004407a010b61710f07007000401035001a4001c40260340290320000725940c0506c903558075161803440801c088040c20700c900c0c00c02c0c400c91040949501040d00042c00301400303940440908549138040300e8540708010413071030040506680c1035803002e00da084201c4041c500010000d05a405004800c580360300d81e8841d85c0007a09a803200c1c0d44600d40501c1e00441c1d5a110350b07600d11002800b039903e09071054903a0001904080f2400ca61508050038411450201c1c2e1000584403001c4200b80c50041e5030b543d45050400c003820103920416000045400400cac10141c14070054001e40c0075100111440120038001aa40d44c2c44050f40100404c0040c0006000d5601420443d01054580c2c100494151016550503c01c0003088030154512501c00a219003a401e096501030440500b842d99100541020348501f84010002072000f00382c9100080d01c5c030108a81e40c0c0d4080d84041c0c0c4580244107101510f81b8039944504200e859021540c60801c0010700101503000b810201c40307080e102c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 532316744 1250 532315494 532315499
    0x9170a091d1608042d03030f06030804121e060207020102070e091504111002100f0b0a091814070e0c0910081e0901021914030c13030b0708090c1801 65
    0xf40d9040714000c00c01d50304000da1071114005521085030100c50820b5401c07413421341c04440d01c1c0c0501101c43c040c0c54014881e142040502c0000c90903402c64081c2c3c0e00e55035001d00310f0035092401a5460028013180c0c0306c100100c00e0008200030781c0741c0140403441d20076002d940303220703845035282940c5150858120383c0e03540c021009180613080c040c8005421030701881c5e07004114041d480102e45010301c81411940140c0c0320f8502828045a1031042c0d01800c85041d0051040d0b0f4441d030700241056400d80142c1160710358420f06c104000d0754a12044e02e07816402115411300981681009480d02194443c20060310800310004a0710043c000c00c13540000b10003400c0903070700e1034005402c5800c08001040c0c40c071170b021141c42e00d482c007500c004c15040c8205019800960394103080b03140021004081c0140300103000641f6240d01c141c94441d404e49601c18000c4054903122416181e04149402083d4006042a800b140600a005610034846032150f01c00d402254003c400310028000712014040d44200c1c0d40c084180103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 532317994 1250 532316744 532316747
    0x1b0f1b020f01140a0801060e010e010c12051b0f010f1107060b0429030c061903051003080414010e121e211b0304050d0609170a091d16 59
    0x610603401c0c0185071060508014224401065000880f401c010502200041103170980c0900e940c50301d00300c01e18010800214041c0080c0010f0080d0720f0003131200a8030b0101c04411841070040d58030750700d00320300c0c500e262111040000d0f84031920550903060075420f003030003101420514003c903528004940704035880c041440c0c03140d0004001641c8200c1d4072640703c22a00b141d0920010003055141900d140079012009448101031500fa83d614050b40241401e219100d0034500c004800700c4c0e5203507603042c08034482d41d40001c0c62112940300e03040141405004074000c55100d00e000440b007070b4458280ca403031340301031040d00c00c2000c0003800004180d410ba00c80b0482e0034030714941085c1220007640c100121100f04080f000c007400a120f103900b90b91000e01c004541c0100ca000030786c4a08c0303000c030f4411020f58a031500740004100d603234034a02000b9041540390303541c0a0030010080d810304504514240407507110f90302c1ca90002c01040140c45401d144803814070b4640c02c048440308100e03004403e80e00625808441c1e0810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 532319244 1250 532317994 532318009
    0x80703031218060509010b090112050712030c020907030506010f11120d0603020901080f060f040b0411060706150611070b030106080c131206060905090d211b0f1b02 72
    0x841e900c1401120b07280ca40000c0d2035010310381c002d0f2000c0001060401685061201040f0161700c20a010748420340300c1c0300403d07008600003094556411000740014010b040c107541c2121a0100207400c0404941001400c3c0c0e4144d10a41c01244241c1c2d80030011022080300721000080e600405985810504110001d600d0000081c00c4030201043c01103070640d070301d40001e005548242d00c401c9580c3c00c00e4809001e469400c0c00016400001d0015000e454141510b4158a80000900050a14400c1d80c8051410396940d415940c8240c1c1c002c905001c2122294440e003500b20091042074049003800c0402d40d140c2e0000b15904059a03c00010507003580c0ca40f1108451550020700852450a410010942c0d0404119040f1018006601b100410300643d40340185c101d030b02a80c4102c14980c90441403000707040300803680f82d00f01a46450a101e40c1380e44070401620f410381080d01503a0b0107103014501080e6034038000d51043c906026841d8040c0d1260000c1c000d0320640704c590801d04c0d494420291030310041c0382921 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 532320494 1250 532319244 532319261
    0x170403200c041a0a050612010504051816051f1d0406080307050c010e150910050d0911030609010b09010b070c1d100503010e03090603061804030c0506010807030312 72
    0x841d0003030a120400301d401c5410346030f100c100c042d070400a11002400c05070800030003410180d40652410304010101041c1c0c0300d060081502ca19242c0303010515000c941c030210041c2d41a51815541e0a8012b00502c0c9012440c51150707038000d481c141a1b58801d102c4981081091551580b10b030200f80d01c841040742070301609810081e0b801617844c040800e0b180f00805c040e0503268880c3c001014800d6608001601c0444241e501c14400d40e07001e80803e6811108005a608864081c0d400280c5032800030016103c0c3c2c01444600d05140c2d2905403507400b480340d09419281603413415400d88005840b150ba44600341c0e0300201040307402100c140010042000600010a4618080e401001d0341700c4d101c890200d0389256842c1c010707404422101c1408504e928801510004180841c020800c1d4644110180e44038081c00c0205846a90040300041581d00c0e071030700c5a50700717084070051003c640c90301d858041c1c2145042c002c20f851900c9000b0000c159005c0c002082c10540f030701034440508049044500202800c0b00c213 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 532321744 1250 532320494 532320557
    0x4060e16021f18140d0306091104091e020a0309060f180f030210140103201c060902210d0206060a09020d0b0d031d01050909040f05190b0601170403 65
    0x19005080495070000d01c03003400b0b504e0346010709000548504010144d1310700c3c0c1c00c0300d203e09280000c21243c1c1411321084170200e400c283d00102d5400c2400780084c14403807a200141804034000100c414480d541742d40b10101281c401c4030100078003409804404200c1b03003048040c1680038810302c03041000c90b06407440345c18118400d204071144c1e4100e4400c074400f03807618000072020110f0b4010051080207080100c516035400740314011300e405003d4200240075030200d441286040704000c08080b083c88210303003200d0015034002d8981c0d40049541c00481e1507a50920070b40030364a008080300c152501e4400321f9894081c10005000d042c2690810300350000035403100500007551980c03649290025100d8100d01c00c1601e02986545000103017804054520407411a05c150404c4002c010499003981d030a5102a00180c10580503c0043d82d5403804601c1c08051036002c0328203074000c400180030040c0a10040c0e00c900001e030b803841184200c4031003440c0d503801d003628010081841024110401520170394403000d0303c8241c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 532322994 1250 532321744 532321781
    0x9040b090a15090b060108160f030209060310030b01051002030304030e280503010606052701030603240b09060102030702040c0e100207090e07030201051209030904060e16021f 77
    0x1581d2003030142d107007030b11400304001d0b1a0072242e03080c01050f040c03041d4407103006c0c00c0c40c5580c0d24201d010710288071140b5400d481840301003103440010b1440384d41a1811300e04082d1001c0c1e03a909050010000181880c0310031a8001c41d11400480c440c208584503000c0c04080d031b0000e504540382e50b6416904015105202074102c01010003c1d4099025100840041501071100d0044c55040005150940702180c05c01014000c04200da030509000002c1c68060204d41419011000110140100c01406050b480500312003049040f441000b03c00408a480c5c01c1020001081501e128400707018400c801102c0b000d0250f00103004050141c2040d0700003004146451401c0a4030302078510015800c5a05103504800580c0400010b10518405109030302008190600500030035145600003400740c441c8509001c02007030207202003241e40c10200141c9a0a100043c07092000315200d80e00200810720848500300e0b446c000619002c1d8890010610100c0300d0900c00b50fa00c51041c0050400c8041d0407461290303040c1108 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 532324244 1250 532322994 532323013
    0x807060609020d050901061401080c0d021306020c010c030e130b040608150906061518040c050702010f08070801050f03211e0412031d1320070209040b09 67
    0x2610502010301214040140c03074441c0740840a0403150010954103031685030240a1086007495014a00981003d1810b143d2640ea407003180406405650203410426001040100d50403400e030001405035805503080f02c41e18030108004654603c01e0450181c04076041d104840d6080c18641407054070030f8406440800d0704d107601c20106d000c0704c42560005000d90030816008217222401d2030407030b4110151030014200782c189207001445032815100c810340410800282040d9141581e0310181c000480100100140e603507801c4040c2c01540300f52012400107030502c0075100c00c1750140c000d080c080d00c129614a251070b030030030080c800c000001c1e2501a600d0300c2034491002e80300b82e02500040ba00b1000c05103441d12006c120525001c10b035096452403800d080c00340404c2c04000c90b840b07690002c0c0307901480c01508101041d6002d040b0301c0340c40420b2a40151002800941d80c4029070230202c01e003030000314000c01404401300144800d000300040290f1218010000c1004110300c0315141e90040d4201c07041d102c8030310 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 532325494 1250 532324244 532324253
    0x504060e060403020d03060b070203030a0804020d0b010b0405090703020c10021602060d0f0606050a0c20030d0f020c01030b131a13060f1d071d21060129070807 70
    0x2c407411001607004590002080d54103002e61001405d0407000a07080c4103d550000e6160b000c5d0b04064410400c00c00009020366a5002da5401459001440d500d5207503158030360b01e0f09552050042501852008001c1109075100f4402c03185455619001780032000f52210f0180c001c0c0d072094115000e00c00d0f54680304400359440b480184a64a5040030024113064403103c031105482d0399a000c4814020b044c0542000540c1080b9648000b80d0f05c089901c80c07503071405c2a418003401d07900318842d03098429180c6500400350069281131803409542c080380c80001d02400110b040da120011032a402250086420340b51180603002400600c02c044800c059040414000c02d00d065440d1303400b566016105c18040000c00d1340c80150b0800340060750b0b1849071201c00c844002d14941d0010303202d10200309041d01211540c424030f00c0f010a0070040200700740200b410715018500035401d40010046503004100c00020004011180054808030300e0400c1e0000010004130710440d80c20040d07080c2c800f16006c000010015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 532326744 1250 532325494 532325503
    0x5010522260a09080d02010e151317121008032b050903120604062d080f012003011508090c030d1106060f031c0c020a06020a12051306030504060e 64
    0xc2e4655506108280b0380f20308a442c0c100103d081d40e00703691500b4041e50040c40040307461405c413241c0d40140350641d12043d02201d07071512a01e1024080a400400e00122220351000030f260010b07802d003400c44162a0049808601501e620400c415070340204140300525140f80d042d42c0502e15a00103500c001860010454141c5c0d40841c0c030080d003034000141c3c2e04400c81d20801740d5a00428107603000c10a01d402c181808041c40e070380c50f00706081e5060820300710b045180415201030280408005440240e0b9440400e40c2c0600082036800d02102012882c000200c2e21800a032812184258903141c915030540c0b10076904640d0160906070b4070b00900345c402c2000d4508000c4100117010550b20454031490740b0340d81c1c504002c17002d0911440341c040b0b0720201c0140c0d580000e0300818400104048160030716480c6003900c002e28030800082d08160500c00014070f0940100e003402c11113004074601021224112000c03100b5125040140c11f660758051418881140f01c0c0d4445640076210b10400a600203041d050710340303030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 532327994 1250 532326744 532326757
    0x1b05010221071a0f090c0303090d0609120e0f011e11070807120b0c030402220906090809090609100306110d09050705190311060a090f030f0501052226 66
    0x8241c200038060700703034101321085070b200c41a080900101190000080d85a12481079114400d000c7d601140e410f11415920588505a00440207036617084d039031802806034030300d00c050b10307101c2c1000c181480f500d94094500207400c4504001100b060600420b03003503c2c103002c0104020740714032600e80041100b410420205000e4121440401964151803270f08851300078008201401c600c00910502005860344030b0064a0020904000d60541000000010051490030000f0f020b80b42041c1105040c041440b0040c46080400d0311a8002503880d4012312181e074006030368070704486044500401c08200a40d00500c1e03e0012405503600d04030390b0640503810f0764141442624103411031070382002940f406040760717880380d4402401c00090030301e5034846048a640624001e8010700c1c000601000b42d92041265801612007004441c40664403414030410303404007220300300d88540c078010200b448041d0f030a24a000c250a03503402e4080c2044259200800440e5007003c010343d4440ca020284001400300c0c014014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 532329244 1250 532327994 532328033
    0x10e0a030b0a050a0e030f0c011a1f11010903180509010e0c0304020402120c0d0506100203251e05070902040e16030e010e15010e10051c08030703091b0501022107 71
    0x48900c08490241e0031540c060514ac44050050b401e251034640340c05031160344490a0080f194103480403e8000d80785410202c00078100d651900c0d941c0420142c01046501c1c91045050311481b20356103c1052006446d400c3c00ba8900321140c0c140003030002c00143c001558003d1015102605048030308071000b00e02d0205840804038403201107122180084148200c41e4001d504440e690f110034101000a900ca1260540040130f000303180c0c001c010320814810810714100d41c015003054044c14078075070042408008090490304c2d401141c1000440100b14001c0d00e003540c2811140d0340704c5440e0780c3e003e0885600c61003000400d05481e40e45808003501d00b0b20680d001090243d003c0c08400120318000011424146c21180100000c4414041c8a022109508042d50820303202404001d022010080b10035110410007442200004100042664540c10003d4058420307400080e0099001d511210828268001d1130300603488000c500b03a03000e1228131403141074001001810f00c3c20502d13845070300e006c170b07082c0b0356044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 532330494 1250 532329244 532329247
    0xa020c0406060e13061401181805040c060302070201120f0932060c0703030504150f2c100b06090303040b04240207030312110a0e010e0a030b0a050a0e030f 68
    0x503080c10324000c1103c408001e42c1040241030b082c00c200c8001c240035890f4040c1023214001540100b824010b8000006e46580f039445a0107450a094200143c0b0040320200c681c0801444d00081d00303406402650441c0d58161155400301c21096400401040150101e1486548882818022540d0320a102d00c40d440ca910b20701520340306000200d03e8081640c0f260207072035441001004109a40d070000e480f140d99041c680894aa140c0e400c0c001c00c1c07001415410041d0515100000c00050820783c840c56000d0043d040360801d452099048000701061a2027150003a00480c04d0300e0000003c50307000c3c82c080300000b44400e04010300a400721307103590001e0300b041e6241c820001d0244154030203016903003c07121040c203c009289801410007901c45009200003011301240c1607445042042d141c0040c158802041241925680c600000610300c40f559031655000c19a019210b101a04202c04580d0030b0303e030001000e403c2604d0f0103500d5001860001e00c3d031410280e0711541c90320386641c00d00c024601c8240c50304105 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 532331744 1250 532330494 532330517
    0x91309030e0102070605030c0309070e1e07082406040f090911040902030a060e03210414030a0e06030c07120c0b0c090a03060905070801060810150e04080a020c040606 73
    0x1410120103032115a043d94000304041207990391080482e03a100303200f074143c281c1300d45840000d90315040040e0442195151030608110409644400c0d440e5001e803203c1202c06a522403003003c0d82c08a105440e003024281c1650103c40c00382459501d0b80b100e00202070301c2c15280641e02e4a000310b40e111242c010740c0c6a00e480f0f165203400d0141440d030032030035008201c40802c040e0781c0903800030340c0d82e61209000903d0980c4684141c80c800c002031059a2046401000c40c0d0700001c5a803440c008800c40440d0106e41113100c100103144030900002c151000c03012244c03510683c9800150412410340c00050028800d039030304201100000c4e80003044002e404829803078041c0403a03240e10703101c0d9202400401c00d030000742c02800715410316511845043c04807030300407600264460003414402d0804106230041c01c629030902c2000662010000b40c0d02c1021001d151301007010750b02180360312000f401d4521400c10000c088401203804990b2240017000c840301240102d9416854040c00300301030701c9803030b0301c20310101e148039590 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 532332994 1250 532331744 532331747
    0x607050f03040b18030d0905150f04122a1707050406031b140d0f020415030b180f0c0f060d050a05160c20150309010203040c050a030809060307030209130903 69
    0x7071804c2c0d4000318050202c460001d800104504a14482d03180b00f07101c17411008003559880e4086827072000c990050039035107036110065101c85c0204844219030400c1010700c940c10320107044100c2c0b4041d91011440302da00070303d800f01c80c0820014503409148a4061b6540024042d5500c6c40351304001d501c5280c408162101ca10079100d41144c09600000e01c4a012060a20160765904c1000300d890b80d00c00500e01c034800c02400410010050031107c1102c1080c540d4000c000d010202031820700c211141510411103d03070300143c003500c3e02f0704104036001c61b9001d1100c1c140c0503e0f00d000602d884000140c2618284241100308002b6214203a42c400343daaa40d58090042040340d10009925860444c05e11054158056403035048031030203241d1402000e003004115548640c0c034029010224500c070302400ea10f0341040c180c958000d40c0143c40458035110400800500c90a0040501088a0300300c00a00d060a0303804081c8410740c0d00040c01582013640c01c1081c0d14042d40c4e040200514080900360005074041305250 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 532334244 1250 532332994 532333027
    0x50a060b03070b0435010501150c1e0809060a08090d0507150e0321100e01050607030c03020703061a28052107030305120a1a0607050f03040b 62
    0xc00c1c0280c0001005000308185181103a007241d043d004807150005012603032901e182c100d100f03150000b00c0f5480354000c0c82c0005402842c181c0d1001041c1076084007245005866034409200002d00c2c0c0c14000d01c28488600c040104912251f0181d92818500070f407d1000981c50340c4401d2484022a0302c10040c040d16600c00c01651100c001d450074418076180c92500c0320300000310034030303081b00d800da0f1240c0308042d82080c01d0083e034030b120780e90165905200c84a91a07415844104650044c244592120009144881030270b085040320005804280382041c1a2011207496030715000507025031003440d400000052032032280700708840c041d01001403900300c00820440d6040a40700c641002e810603c0c4440d0142c00e00d03101322002c458007103600002844503008080008206105410700501030b24000000f89a00308005101140310041032041c550b07a42243c1d9021201d40100362072030328165954800c002d007000c41c000d00900740103008032071200c03e80a60552560348503810050099a0114240c0b400b6400c103803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 532335494 1250 532334244 532334261
    0x906070b0f070c020d0b040203150c09040b06120f07050c0307230d0206011517070801060908120a110f070b09010e0d020f220606030603031106040c05090c090d050a06 73
    0x28003050f000710541c000800003000b2100207081004807601040455a04200701d5410b015849035065440c03070050000170480d040892040e020f1070070405030b01d0842ca407081c201c0e804411000303008400c58580502e4012102001841c071000d1110401c00321021078400c00280008034802c01e00c5e5011052104125025411a90703151121640950301c0d52903090f070081415415180000d06540580480290803282c100410183e20381d031109410a00c10696800b45950741624046c1d1903200909a541c9001c0707644041d4000d142c0f00d02d0005100d021601845800d030801280b06400455140300c8402c95a1400c058403036000f81a20840043c9944165070486130424920f40100c8040c100b035012500030654520200c0c4a0b140324248504481400d032440350ae40c850307102da0307402080102c0d0784c8602c0050018030050005030045070b0102c1c5420306000300090042d01c60303a0700c00300c29aa641e103030409100c464138000d0010071031003905001601c1517840d048400384503d4080d030b008144444050070410100c4003c076 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 532336744 1250 532335494 532335497
    0x2030712090f03050a0c020402160302060f190207060f1e0b06070302031204140a08090108010b190c030302091e040507030902010807050706060e011806060806180402060906070b0f07 80
    0x9207004003003034400410415550301414059030310385c0c60f05d0040310703002d1b5051030007980240701140c21410940d60320007080c1403601c25000c035002c0d0f45510b481302c10b035020101c80c49030003075101d41c021020210150300170341a610301c54000464615100d140c1801030350182c1c840da440310310141100c8064003009005201c101c0d0400e451840c5001e07102d840003900c03849804044960021501d010504120321400090510340b09102610304560a910740b05072039600050b51280015070076400807031701d0168482100d00e028030074030181300c2901000c0016219248030741003c1d81855801e118044023504c810501c0d01e0b1070081c480d40040c079858040100011200081c0801c000c052078040c410380180d8009425641004260400319201c0d08546401809800c03980c10400080d024803000103030702c10210340340440c11440c15a0901501d910f850341210301d0102142d11030390008800107001c203a00742d203468207030300f260001d00a24a005000008100690b02075a02290106203100c1002401e45483c0d540c0ca421402a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 532337994 1250 532336744 532336751
    0xc0402030702010e060a11040501140712080109320402120d050417012003040f0f06050a050703140703110c1204051305010e041401021b07140f090a050613060902030712 74
    0x101c0700e04941f0307030040740540f41c18420395501556070089400e080c0d5140a80c0980c142940344040c41c0000c0c40c068080c4500d6a400d800c2c88000340c2802800340880000920600018260b504c0703030401c0c1c20340306401034400d07a0061011140341c2d0450b0002d1010400c1c03203c050315007a0380d4924000582851036207500103011564503200d480c009201100007444441c003805600c0584944540c10300c6850381140040c0240307a0a03503070105108200c602d80009116500c294000c02080d40e94140940960798881030300c840040c0200005801503010fa0720600c1050440d402490a1840c40f5501500c2d0404045518500070070102d020409071070100c001540c900d000510030310180d4544038800300601d5002d40300030a000840450610114401d5041c0d5928114000c1402d0008103016071468507010a40100805003050072204982820034200c1d02904c48005001c1d5003080d9110f084c01c60003004040c0c0aa9404464001c050030240d1044c0601d801a10101d040103030707241041600500f2403540c900801c09154103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 532339244 1250 532337994 532338011
    0xd03090609060c2f072619230a06020309071a0c010518030301060f26040204061205030315041515020c04051e0601030204170a1205190e030c0402030702010e060a 71
    0x2408240001264030803001c0702034510040c084140e00c01540d40c2c11202ca0700c00c0c0c22811a040c82c41505042c42d4900602340c2d201e55600c0301c09181c45038404000c6000c81e580c01081401d0001d400b907030046a100702800e00340c40d21152907001d0702c12007c0c1d010b080491403820206400001d09803e205064000f4810861421180555000962280814401c2c24140b00340320109000d160701821140c041061000036008402440000300b07290101d09603800d9010b1850201c1c08100c0d1800300490300d07552034101d0300450a580d500c07420444800040e10100350420788800c040c00c1c8401d0240b25140c080d105040c20400c1071003000038020310b8465104407851099052009105080204800d907154000d001540d14101d81e42e40b00040e00641306984c000c0d6100361020180800d12400490055005440381484211504200f402114140661840d04281c3e0a04400105c0d401380030704450543c1c200050155902003903054002400ca0b08119010000750f51a40d401917004201030141940c0300c2041d030402c2040c0e15 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 532340494 1250 532339244 532339337
    0x140708070509010306090204171203060102030423090702060702061005060702040906060e09010914070509060d0309120f031815210207050309011b050d03090609060c 73
    0x50050200300c148140001c4101403030348603400c0640a02582076007959120790f1414100b01c07040c8482640010f0303004140d4401e42e01c0c11044200d0380203003c16030055081c50700301701090b01005410351803107103100500c031001415038903a01000c51003440d045e0081c1046c0e280070311010b41441e900034407002805840030401d1019a444800b5a80201c4d01030f500003d14040500d07080c0c0007090b0725000920f4140350f0804202d0140303415003052404501ca9100070040341c0305101e44640d258105d000307842d48688001e0008042d42009990044164020300d0114002c82da200c030b641000d901c0c1210182e8100c0c0c031100c7c0d60340a05420201d113100440c201000400c2091920300d440c0e0021640b181c03070070108280d58450100c00403031400c01c003899542c8a8000c641c0c907a081d1414a640303a00040110707011805014500001340c442194201d00d0351781040207002da4105d80c900031401041e00d540222011956280521b01041d2284a4520402150385580c20030078120074400c045d00741e8800b46003060a141344008041c10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 532341744 1250 532340494 532340507
    0x1030b0103060c03021e0903010e03191b170706110304030215070225031a0112081c1d0715091712180f151614070f03061407 55
    0x5980086001406001500d002ca0291241c10b06d80301c41000744250241400302500028680d42c00220000c010b6038002698140c2c5a0082c0c3c076100e81c00c0300e8415041545280200c81c68a9580052104c4072400f01e0695600302d501440300040000a070300100d05201040407602c1840c280c01082500c0e18118542650025a9401c0d00c41c41401c0da0030349240404d40b094006c000d00c0e001504c083c884118851005249041350728802e200c150380380d14400c804017801d40c5142c0c40c0304e410307508002d40150f00780700c2d5515084000c4e440f20b40e50320748220b1074140d4582e8021081c40703016485440040b008001042007000c0900d0710300c094000f40000f010360b030480e458094100b45101e080f0b80280c040700b031054408039099820302c4030716503580c022440001062100c500c914050141040070413644d01381036920030024455001c8118810400d800b5040010180000c440720854401c144513040c0d500141840c000c805003000001e034066694000310a0b401d0007000583d01455030080000d88920906107800200200907 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 532342994 1250 532341744 532341749
    0x13050a090501180e0f0304060203030a2703140d11070c0504050606070b0604060306020304030906020f070659190509130b162d141b0102041d01030b01 66
    0x2e160b0394001451000c0c410f0050b4904005d40c0e80980340c03900e0f90341c200651a58400c80301034080c0344ca40091726100f0310462010180c0c56034170b0103011460002da9074081c0ca080040ea0030b5100040e90510000c0c06000d07a42c02261542c7c1c4035131121680340c0c4807900e4403900c034142c01e0700164030441c2004100720054036500c00b078903403446d0805400306040d1141d602050003055644c01c0640312070700000401c0140f6401100110444025900300c60001c02c5000540b0f8031090b0318007440d40015840d81020b00607658200d140002c600e21003074a10001000c0d000d82111a9031500f1100220500c0c00103482c0010400350604e400504099038400c01c04a018400381c261704e103079405401e2040994102241241d03005003000c030030650380031048002d981000340390304140c0a01a000744000400d41d40784d1030452001402547d51303559401400480321003180030141c500d07911800503044a001c0610103202030061019054034101000c4000598450510254008801c0c95402001340c940701c5000400000d000244410704 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 532344244 1250 532342994 532343039
    0xc230609060d020706060f1e0602060c071a041506080c0f0127120b06041514011209080415020a120302160203010207050f0c01030b010e1c050313050a090501 69
    0x507a1942c51512400a0140d803002824031450801d01044034241001c0300c00c241c0d00aa1400e1500080c0c0c01400342e0740000f9409074000581042009c0f60600203010050050248500f41c00c0010b66643c0003041d140481c01c49050710703000b80540d0020307041c00080c42180080c0800901038808021308601113460f08240b60500c030f04101424207104130750860803c0c05102c1d07060031400c10b059581d4411443c18a1510b600c1c096411500e10404984c080c035140c0b050401201100c24900322803481e1040c40000f124032260480e040c04480c7d441e034000c810061041918851141c0b01c1d41e40c5890500b0a8050400c0e00404075406560001c41045c000c240e82411180c510100340c80e015a561512203070624580d03c802c10b000b505907001185e21801c2050110382080800040780403148001c00490045090f1008407040d1030124030744002000f1181440540074a4106c10250b5500c0d0b11503060351020311b0740d4070a110f032040d14400d0400c203100300e1034400302c4000200300443c0d003806154104075000500c003124002925 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 532345494 1250 532344244 532344247
    0x20d0c1827062111010905010804020d0201050c0111030a0e0c0d08090a05060c01020a02101803030518060117060f0f0a0b0d1202031305030106060c080f12040c23060906 74
    0x701ca0342580c2c2c0041c4043d064901d05010081c20410043d681c4419051040700d01c052542c44034003065103d207401e1812030368169203448850303c86809100e4200b60340142641003200420030400703858824091102210f819030803681c1e480c43c140044c0d504a551a0408034400d030070008240b01a5503803819805022904080320a03a07690140c00024040b10856106c03a40250f0f02003405001000c040d800340140b00340503001d032508618030745003020440c3d1a4001d160000d200190100d000700703100c0e50109500501c1c4000c203503060b41003000085d180503001d0340840340c050160b2115107401e810506c10700350007040d00e100041c0c00d400c00387c49052a011000f0400030441d41d458001c0b443c03584e211140040c0c00c5411030401c0c15410681000251030381d206004c04900724075101e1b0005a41d040520480046500a954141107500d46644004440c1e01025891120500a109400d83ea00780a074850b80079900c5200382c205142e21708208003c2c02c0c0c0c410001e0301400c0001c1d0385480b095488180498013000302c12610070703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 532346744 1250 532345494 532345559
    0x10204030503120a150b030106080a050106020d0309060207080c01020a120c0504060809031b061f1212050c0d0c02100513060f0201090b0f2a160c030204020d0c18 71
    0x84c0e00800c0403d4818805000584001801503c1c840045060713500c15980c0000c00c0c6e440d20704003000c0c1c030401c0c8aa0320050303202d00052941503100e43c0c0805082c0340f0440c4050314200c9142c8540e03a040d048500e010425950003e0003070f41035500000ba01149034800c40080c008c407901d001001d400d0b80900d2048400780509400000c0000d9018000c07243c81c90740243c40761000748150141e203952582c0494030071a0b8181d03500324144d02411082246001c40c1d01f00003400001840c1307540da4000e900407441002c41440014410248007500500c28010001001c0e550b00040c840c00e801041402c0144003804010f019003000030042500404004500f9a98542031141e48032114001c200e00416101c2809002c650314041448200c081d5000050b0280c80c0300305c84880d00030410801c0f5000c4c0070b103c01d10840c0c00c0301e08004140c1201642e07000b14034200e0240c69070b000019074a4000c40c059a0103140b09803d01036aa441e00708020b900802140e4140d00070040b0904030904084081140d088800940c546013400c51440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 532347994 1250 532346744 532346761
    0x80d0e090601051209011a0d05100b010e120609070e010308180f030304031a010b2a011404050312010b0f090d150e0d0f0302090f040911060a1d0301020403050312 71
    0x44441c90004135041c1001458514000c40c000c00d000d183c20152101868035a00071451720259100000e070700304018003940c0c0c00c415117502c01050b41e80750107410301c101d1038155101940d842075114466484030001c0c3c000340c81e040071114207040d200c2d001403c50541d00c20040c008540c500e02a00e0241c25200040c02401c411800040c1d003501d1528016035040c8000074012040001044030500c48480c01e08400b90307240d8075590a078400d801494a200c11028448070101c0d059502e030a43c0e0007402c200c503000004d404031050400d0140f100100c400741c0b8661f00001300d500c0114040c0d84000d00414490f400c03c2c5c1803191241301c0c1100341c410322000c81d00c6003012401c61818465440d800041c185070514040100507560103000c1e490b58601c03910a0041000d103003418010301d020740203c40d90341200510900c0310780801010800180041c01d001d44010304661601151519804c00403c0c0f1905c2c07035201c004149100d0190002d000030300d00981c80c0a13900500041000072400001e40e1511104642440110750312000d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 532349244 1250 532347994 532347997
    0x103150306110403030e0d11090c0f21060a0807360c11031e1c0f150504091101033204110102010b0d06110409091506080d0e09060105 59
    0xc0034005600c0d1011038996460050b0003401140e201c1d03160014900d01100402c0000110301c1c7c0c011b00882300b80b036498015850289059940b01c5c0484080c0c6003482070040e0303503881c540c02c20101103464103106071031030035114001098194801c00c2100d030089101d080814031501c90445204941d00b64032400f2080d400f2415201c00d00055074400040b4040c0350f50503415020103002140c89030008170744105a040103070503020040369040c0703c51102ca21180034140b1120280c0c1d07800617007001144080003011034904a218000c0507240c04540401090010080d5000720500d0088d91020f4404c52420400c10300084010481e4850362138242400a014100c04408803001e07408480c0021042c640305102401030030a600742d41d4001c601940c2503001040e200e0307005900701c17802684516032091019170500001441e5801215002c070a44000a0400c0d95070f030380400a603143c061003115102c0d000c030401401841644030b100010a096002171500444164010f051102c0d032040300d5001e001640c1c001011640140b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 532350494 1250 532349244 532349249
    0x20a20100f03020412150c09150804020103090605040606050901050d11060a0201060b16150902060306040b0a1a041a090604092016140c0102030f0c0106051f0311031005010315 77
    0x104503200c400401c0c0f0703000d04008070508201c1c03401031a10b440d2041c7c152283e40c42409440b01801800812a00014196003e4400500481c101034840046c00d001a2070f80c010a40164403540c2c2c00303c2c07500d04000410a0011050708041d0140c4202c4407090301003141903961428211003134824640d03400e10304408a014000702c1e0824002030b00005030603001240030303038592181140141070040c001c01d1007540392019a841c252020794800000d0002c240c0710300d001d6003d0410f81c14014024104c0340d644481e00ca2740440030803001805401d000c64200218142e00d405030005d0b84000709142d00d8007000c034000a055014a00480c43c915540fa2001d607514060400450808503101a9640e00d07001502141c82c0b500c00c030400110390282e001c04420070002c0c4005014540840d050b00594107260661074000e80541211140306076542d00ca920001d40340d207030160f24a030040c01a42d107070b20141d19403000c0601643c0a204000108600410070050b1a212148452094031800d18000c141318070802c40c1e0902c0790210381c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 532351744 1250 532350494 532350509
    0xe040809090403050309210d0507110d0c0201081003170c210705010f0b0604180b04022809060507030f18090f0c020705090402060901050c030a020a20100f030204 71
    0x5040c40b007496000030146224140301c0c0121084001051240031440b94200d10750304200c881445095403001c126040968480010710b090030003043c036224100d20303100d260241d503404034001c440d4a10a5581c00001154403000707464014010514640d40d895501c0860f2440c01d000b0007021a418504140c00c0c0700d504610768008030400f81003600c0780703c824503548c408001100c4a611f4445540904a070900070071031185001000c141c00d1038502141d034a0380200e21021550b41aa8400b850091665140301900e04120281b19482480920082c0802c01e20481c42001c410301410000c200140c50f482022160ba085d0301d4a00503204000001044d11001e450803204411501c0407040851700c2c1056a1210030002180b54044c003065038940016038072841a40921900550244000f03005814050f0040506d000103142062030022000506400c0d030f00304119810040c0c100088800600082400c1c10151100b03851034009403103000300018903280e2600035040c0c00d000c4200e03c0741c0e0b140740c0247e041d5001007141 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 532352994 1250 532351744 532351759
    0xc16140a0507060801170c01140c060f010905010e10141f020c01091502070b090f0d110a090b010503070309032001021309110406030203042f030105061005040e040809 73
    0x407441c1090729203550f03000d03003400150300c03c00028214007480500400c550052014000501c11000115a40410320b0010101e002d41001210740c04d030020040d643c40380510b00000041541045124800d0f550180d1103496035140c150700340032402c1c10204030107049070480513031a0300c01e002070004140903c40c48850341500d40c00c0f081552507595004118041c51301c0090740d404a1042d2120b041540c1c1c200c1031415080180d120079414490861040028000b00d00e0050440d02030101c040e0000300000c0100c0801c4821000f0280d001e151814030710f501101070038019030240502000c84000801704d00006240c02d0030107440350740000a150154003856503c8d2426040701c241d031800d41040c0c60107075100360141400c40017070300d200091810481c03290380c83c81f00e8174005051429242040850280d000a4001d880c05286140c280d01c0201d80e0312464000215186000000658044101421100c000700258060300241105100096119044405540d82e80e043c2801c02c0e102c1e4240b00303165000d81c404640e0410304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 532354244 1250 532352994 532353013
    0x601230a200109051203070e060c030f03010f080d0f0c0204150807091505031203010302210712330903030b0409030203073509060c01110a020d080c1614 67
    0xc190040f6036904c0c0120202c1d9144002c0d401500d2840c407044424500240503480444078515190005003c104003050480e8117040744848000d00c550701c213a20060b4903100d400b20420034000144020340b4010b499081036003000e1010b2034060090b42c1418802482160743d82003e0745803404281d500340243c1500e000b220314144d00c1c3d0f220718000b00003007482d445c2d0f44880241d00081034a0005441c60b950040c5805c0113040d6440c5600340422080740c02801051304802080740c1070303401b1040001800501244a07840350041c041d0800a0085c01c0f100002109130070420403600306c1200401113030518441c07640e0f0001e40005182001c4004100303c05000c0d80c0039040c51030f0b40060650000181990502480c0e0003400c14035040c400d0120500d056000709100c1c201c03c05035031481d405480c054100800007070700240c5004202c0161508503901020350070000f40002c5030081010341d0400a049901303030182042500b40c1494056085c080c000c1858011031520343e0118501001101c0d4445624100e070303403007290302c41d24 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 532355494 1250 532354244 532354307
    0x6010e12101a0901030c0605070f14030403061b021c03090803100f17060a0f060b03040c09050604090228030b10060f0e0d032f01140601230a 62
    0x40c030610301d10b5034059038010030410314080c038034503040301d44c400010007800d442c0003000c0e103194021220a0350010440c00509010440b000c0c84003901c1031505000d96901c1e411494030504858558a188448100b0814070231021134002a440082004034100c0002c0b809c0100001c801500c00b13000b0041c4040c40c00b1007840040b00320350518100b56500e410000c4a044d40310546d030404064100d00c52081d582c000000710f00c4035580c2da40140c4440f9080d44e000320703110b901d0305d099104d2640155003c568100c0520400c01c06032550380b003003c1e0442c00031181405100c00c290001000105000450700903072850440400c0071410000ca100e00465001c1d48419152912120300c89a00c4490311804001c10406d00b1030a20b0284103903001c800e0b070030005000c0c541c5071049c0d44044402c01c400200780105621041e0483d01d019015550000f4500003900011440e00310035540c08a00074400b60000d4103020785100d007200c04d0525801900d54130510211065281d0112080c110b800b40300c206410000d0300d0302c40c01c2000e00c15 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 532356744 1250 532355494 532355501
    0x41704090c0c06061a0f0304020d0c03230111270306040804030302060f07050f0901090e0a20030402030703171e03060102191e210f121406010e1210 65
    0x28083d10b420072041c0e60f1505243d00088514180d009a107608003d4400d14000d00c4002c1d5400500113028042000c01c0d0765600706a03075100b034000380c42c0c499600e146024201c0300700030448100c5610070020700241148410361142c2e4060300742d1000d890905104800303c105483e08110b80300045c0201101d48070b04040c100100568030a0009800601a010000303c103442503404650103044207a45041c6000d4045211080c1da4000c20302890400c01200e00003c0d0f014981541a80109501c6c0d80009926030395000d46080180c80504500078840309104000240e540400c5441c200c1e500700480e19082d8145820080282c41604100c1002c000800020035400020748082d511612081c2c00311510b07070006006c0f840c100451240300500c0144811150507200d0a140d0100b04024450050108040f200d11500341c401c00c3c51403580c40c002221b4000501d65a64000c00d941418031030740b003042204560401004450002c000c1c500b42c144100c500d1100700c0d5496185500914045c140c041d218404185070450f000b4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 532357994 1250 532356744 532356767
    0x2811091219120f020304050607120302120c0c150415051b0307021e2a0307030f050d09050d0302060103110d0b1015030c1b1e1a070302030f041704090c 66
    0x3150f07403240304001400002243d050346c40003060142898041e03659001591481580c04d4201134080c04840200119040018051015a400f0316111a0244213092500000400c40e03070b0f003403a0a009200c049000807101c000340003207002c80070550b50f1b0b40f20340504c1112a00302510080c0000001004032440d80415018501c01030101601c5c500c0000020b000e540d03680c104070042e5030b2603080d04103840d042c442802c80704901401070242c030303d81942e0341c4440d6071414003c0390603100740e003008100790032a50f840b40e0307418050141120715480303009890320002e585083c140001454260b8000e4101a9540d1760003418601d95400301c050101442c00750003880f100c2400c0c0c441c0d8462101e802000440c1c4a0181c05401800c0d030165850074a011007091401c0744091031071000380c0d200030b28900800b03800001240c0d0105074901464204405200401d9640590800144a102094414000c0c0700a4071003401c4034076005030300581d040c5100029500b00c102284079551020710b0b0145410b12444540341c001042100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 532359244 1250 532357994 532357997
    0x90c05120c0102010b100e09070e03010e071802040303091a1207030c0e0102031905031008010606080f01050405130602071b0924030c0b0d02040905281109121912 71
    0x51705030a00c003181504039024030204101c0046541c0c1c5040c0700110551150003440d0135000c0843d8030f4007181c21158034a186900c01d4210300018401501668482c1d01c0d0305d20603410031860f0916545000300003401c50b00074407211307091200c605010500c920041d5002c0d03900d0140c032900c0301e0501080c040d00410710040010041010f46c00344052960011054820160345c1920f400515070100c00e080344c403944001c0c004d00a241008502140c0c41c1424031680000c0c00c50341d1a00002030905086d00212000141d128900c280d08200401c998021a00442101903600046c09030f01c54100e1f01d0401994080b001080d0000c0300c0c2c0741c00005440c00f660700b241414a90741e01c0d80002ea00e08003154410740320014000a403842c010500304000220a1000400303035841000001401c01d074894242406840302501c0b140c180107040c04140360002400c2010107250000d10303d04102100b100400400e2a01506c8422071054a4141104040c02c03800d0041c008100203100c80d1458040340d0385041918001d4008041d070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 532360494 1250 532359244 532359251
    0x301051008510901020a110303103507050109060309021c02011b0b01050411090112050601110105041208100303090b160506131509030909090c05120c010201 69
    0xc40848034801d05a110b800385003504200d4810101c4461142452030040e94110701e00c11900c0c480030300b4454051030141d010b0100260355100280b50050161011071582c407482e4000700300b4000074500c100c00c01d800b2950503100800c0c03071880010820b64030540c08086045220343e140d5915480301408a010030075201e0981b15580103584800045044550480000b500078840c0400b02076103100c0d2002d03440c6980c0c41454202c03909581b801d00e2011115810388219a107a84040043c42145058050b80070314036810189c5078140b040981c0003d182070b0402d100080302c5540d4002042c07003a4428010f030034400003400d00a02040c2420714014840b881e12180140c0010b000002050404610040c000c0c00c036030301070303030340001d1182072050700041c1350700024007500c50f0a0840700d40800560309003c503900ca00441e016001c601000c40c18200c20341403403100b590008070f160001c0e00000030380200206080c1c580d0300030005007510007850044c3c202e14003500310a921140a2880c66120346000a810603245801c0c1d0090 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 532361744 1250 532360494 532360513
    0x304031106070f0c08070f081206040b1c0b18030a020c0414040506010b0a050d090506070e0604260f1501061107031e02010309170a11070501050421020301051008 71
    0x4a54501520f80014000f03540c0c1d049590101380b40f00b0282003094010001c039680f0300c155940b11900e0780e114042e4030204030160001c10905140a00ca00d10155200360f40341059074090b0780004040c0ca00084005140340204000728400384084219201041140c00441c3c0e901d80c3c0b10003008e9580d1002d0141248100e040210720740c0504140b60383c150040754071900800342a42004440803498100c0c0600d08104102840240f6407140c5500884c000c031401070001e00000d04004070000c2c071004030601010300510041000304580140401500040e0b2140e1004103030034100c3c500e6041c2440e400024641040c4140408080d1404880700034a048804a46807589201e60200d600f6455540c0c0744009003c0c1c180c10001c942054071a4045039030200c1c4145400a1000070543d07036100d540c1705081420030b42080205000410740e81280300003101c8280030008010203490070000910502c5a4054035010401c02c0c0b0300d20f540301954200300846254020024091440c00c1c1014002000d01c502c29808107102d1091031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 532362994 1250 532361744 532361747
    0xc060d02041719020d0f0f060204080d110c0d02131401050306070c0515150405070801060e01180b130b0301090203060f0913030e0d02030f1b090106020601090504080d02030403110607 80
    0x1407850a40110f0b0a202d41d40149408200144c0b14541c2c065400240d0503035840009854814010481403040b0401038a590408070322525120b941181d1506010800e1180002c4110000d41d40703071500c1c01110040d02e54002840854000f944080c440740045060400000e5104400c9030158142ca100b98101c070720690300c490003100c3d094480394010b4107903001071054040d40311505881680c007600707035179480344d8044042000c50201c2d44100d55040c00112500010312465078032a803c40301600d401d03c3c180d280030801e08100201b44030f09104098400e900010200114580801014010710304030789920b440b582e403051110080c6d44201c1d416032180c4543d082004681c82d207150054081c50032609800c0340b544071658140c07070540600c0d500c241d2001c420501b4600698003040a6010b542842020f40364030100030314084c0c1105a1001600d21852100d0b00501080780c0c0080c6060450700080b002040079142c500f810441d604c243c0c40000714247c000402c09c000d02d504070729484100b03080b200c22219642c1c3d80500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 532364244 1250 532362994 532363003
    0xc030f03051302030f07030302060106090f050603060d080d140601110d0815030a03030f0608062e0f0e060a06021c050708090402030403120e030a0c0201110c060d020417 74
    0x4010400591214004900c640e100c203600525602003594028099000607141c2450581d036003202e0352021078203008041e418081140103110909020f10308505140480718101c031039008a074010a000700008045a440f00458861070360400c0c2a03a0303880e01d1411422000d08507082c030100a000e040c070041358195104800700c80010f08081d019201c043e0204004480e00c0c58044d11090860001c104600402e42d4248075411806200b038800050302d11031a070100e001d5903c60b46c041c480c00d070840c2c0e041142014a0340e50480c0d4100349111030070b4099180541841c91716103643c1060111003480310020654821400490f8040c680031610807201c00e03510b8100700c0e59803020350850b82508001081001c1101d02aa0161107160310a000310350800209501150498100711015000140c40400d07003500c6440c00d100304004684102d000c2c524000c1d040d1005440d00c890030308004c0c1003104088010346113280c14080340c00c0c00350000b0241a610340d08580002e000c0e4200b805200f111203035144020610340710004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 532365494 1250 532364244 532364267
    0x40c0b0a09030318090c03060602070b0403020307050d15050112060b030f12161b17060106090b0304061401060819060503061602100f1e090b01050f0f040510090c 71
    0x55524038800d05594044400f0100004e441e00c001300c0702000482c1208043c01104c804420580d0001a102e141c110028501202a0700c2440092000c01c01400541c5021440d181981c8c000d40b1005a840100e281014400c2c03192040940340c2840c1c44000b055514000d2000c10640340103000c184680030000041503102c025040548125a0005e0745184441c0c412402808076240b0b40304100922402070384030f52004c1d03003103800307045450f05104106011000d910105818031f8000307080100314942c141b410141410281d401552043c4402000040401041342c100c110011040d8030003070f00300c0d41c2d1203001600101c01a0780c0d982000e00b40096040300f004840c810350003120b90040003441c0da81c5404042006800d0ba0100117400c6000ea2440103c1c001e000f4000d80311007000c410000903604081090800e612008000946001410103041401158a01e8141815118107e41c8021b2580401001440c604183c0705080e402500304010010740d010402e000c60211500351505201c05002303404110b400c0711688 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 532366744 1250 532365494 532365497
    0x501060e03100b04020918041a010b0f031b0c0a2a050d03050c070605030105090f07051c1509090b06030d020331030b1e060319020402090405040803040c0b0a 69
    0x22007102c080750b20550070041d41100b028000501c4c15030f030355000ca101203030000008858154800203000810030100407408085801c103d90181d01e506091122010f84140c40340202a000c01001048010382201003c094143e64401c02e640d80b0280d460320103844460b48075094404145001c1c84000c44541c00309c0103049151544101d0b82803600f00350420001d422040b805604010342400f150502c44010481a4080c101c0c80d102e4944940c5024200020100e000701560b42d90203848042c816159004005d5841100036884e1100750452140075400052040c603a03007407955010404001400b0105a002d2010940145040380403640c901c4145507072074881d510030310b0060f80104038041300210401200c201d52012010502c02d034500b292401e40344000143c2051724100c05a0b010f201381002c11605c0460300c070401e07010b01d004618005000035181d6050129085100300e481043c641159507603812201c19580040c0200024140340c100400f82d90022039084807869491680855681040002d641202800b0b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 532367994 1250 532366744 532366753
    0x1c0c110106140613030c120b09010b091302131d0709060f0519030507032f03030406050f12010303170a09020904060e0102120f061005030613050702070b1602040501060e03 75
    0x14043c0300c039030380c080394200304840096000840080c0540922400901482100a03d40a000e00f03004144080c054818102607240c202111001c0e1140034540e503011112040022200000d40003081410ad80340d80e9a20180340f034044141030300c11409612120503c142003c4403d60707600e8070f48803c02c0720000c1c0640b405443c81c40c0750800251400380c1c0031920b031029220f0401072035aa00d94425150a0443c0c0044039490801c0008030200815440b15002c59184100f0500c0240d41c617801098503442640101c200f003103c00502c8008101c10302c011a8000d00d142d03400c940703696035641001007a40f280d80c40c608110451031004a4621030b07141c004c1c5945c10303400800c06056500e603551440014003409a9100c4595000d0003140114804800c550b4400c0c0c2c4070100d0361030a403a180042100044c0030500c4101882014014001103842d00501c400015020300f10004a81d182d024050b03140c00c0f850b45c003070146408000762040040503881c840d804142e01c00e480600841c0d80b5188240c42482a61003250f030142d10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 532369244 1250 532367994 532368029
    0x509060c0708070501020a092d090b03070f08030904050f0106080601050d090206181908030f09120d02010e0709060b1608041a1213030807080c1c0c110106 68
    0xa8100140410361050301810703d0b0044941c1d809003a6004240d01c0004501c202500b0130038441d503244800c031030003a00185159900d0140c2404001d0340c0f518010042c034a503403460090301d01d4504000c40b10140000341c049401981e0b648031880d540341e021030305d118001c5040c180462000303024106550705a031129104ca44c0f6565400c40111059000040d0743d0303048039241d04140c40581c03104002803003d007080d000b9040b10282d80005001e086d0744041403004c034442040c44200181d040110031b44684407111004103507030b5010b01c00020608908500200014003071000c1da00006a015880383c8600c1200000fa100a50754540d4420105da80382d200301e42c0c041c50100403182110b112815554103062182c0e90850030640c48800202c0c0403a1341e40000d43c100200012044c0c40140c001c0d0320b00e0341c4400c0302111506030820302d94004080c100f000d80b10030f06004c8501d000c11648030700700050703034000311064245c1141d41800500910141101c0300a11001c0341603a8400800041d060203450243c07014100506007458 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 532370494 1250 532369244 532369261
    0x60e070e150f0117040314031f0509070c020111030f0c0a111e09091e01090209060303040b0702060a0c020312030103060b090106021b03100f0c1202040f0e130b040318050103050906 79
    0xa0024800c40801102141002c1f850500070051405818050381ca100083e000b911003070460000d94210368880c520032000c1169803a4020032203409681c0c2032901940064451910501e5400381001c81000f0321408a01102e00d010700041a44400e809000132017228a4080300b84100300c5c103424125a00c0801d41d807841904c0b82400c81304aa00402c5000c120342e9404e14021585000b03541076010310f1040e07515100040b0039440e21029068020108401551401e031401030464071520540600074040c12001c52503203039290042c14001c01464010b402c2d118650301d9034280310450791090004480241c904084002e080c01c1401650307050710340c00e400903c2d90350b40020822000c80e000521860385845895100480c01c0d115006001c2401d5103408003064002601e00d015142506040c042d01c0d4145c4180070411190f6a003088200031101c0d00201c6480036100c9607207a4812100405000d00071100724024442016400188203010f000048206c44019849000441c01c0d20300c1a04e00b518a42d01600c007140021 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 532371744 1250 532370494 532370537
    0x512040201020c280914070309080c1921021b041d030705211602010507060e10060902090102030301090c0e190806060d080304030804060e070e150f01 66
    0x503005004450890012400142c0c240c09449030380d40b50052020010000501c084610710082d10780e50304103102194450f00e4108004a0041070b000c1055215100c082c01e00452000700c0d2111019a0241c5001070b01018100c1c0002001c2d03201180c4150007841850b960003400f180100c0d11308210350251030742004440a20710030f482da614505130b11607a5240c0d401d8517094600068000c100ca0744002d0f584440e410b0410600300010b0000a07040c11641c00c940d6030b042948802110315004c980040c0801e00045400100d405000b034034401001a454001d20ba444080b00148100340b01e0011030302400f920392203c4c90801680038120480740580d10902c0180401d42194000312070030344032450198804030003000052034811550080042c40c0c0c5060109002d014000d01c1566070069056419039104c20169031281c155100c010300240404c4600c50201e020400c40350010428160f0070412181010b0321455540340c244030a8400c0701002000000d0b103c0b090030031000c00c60019205071140c451200c0001d40707403080c0303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 532372994 1250 532371744 532371751
    0x60f0907090f050906060901030308070809010b04020711030c0103020915030c0c0303040b0108060f04031e090506040602010c1d1522031101020d0c1e050c0303070b071e0512 76
    0x890203224404180c02070603100d2110852a00080402c00d0705050214508080000c2c00d000e004e404d5a0300180b01298003d21600d802c03c80e035140040ca41d070340d8840340c5401072444000c03281c5e1090000560382c091206881d00b030031000c8800c80550740a40d030814015012485003200c0ca0f034108008106d100c948511920182d0380c421000084c03286851680e642090455004503001c072001e2580c00010300480104102c031540c03280c0100795000860406803030203003854070b0b850b250910900c0c12003180040342c0e12070a003a9000b000d0107004207480d15202c420203800703007866074181c400203001c5000040200c01072210485165902a02140380441070003030f440415441004007415480303a8080c2c80e29902c00c00e101c3c400080d4000c03110000c0b207103450701c00281082210083c03502049020f84914010a40c0e01d144803070304040460103540c005045152450410444400c03496050001240280601070030580c0030b44070303020315660400c01807000d0880c1410f01ca030618a074400620240030643d015031141d10701582 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 532374100 1106 532372994 532373011
    0xc07080d0509040c1701060f021504170901051204060f0b0609010e09060a080312101512050415180618050a1b1e060f050705060f 57
    0x1ca0091041c0144903584c1ca440b19410503004108091200580140b20080e56030b485101400e03c200d030b0f84983d8094080d94403030440303803c07008015510071640480310404901201c0040003140c0c000089550600c42d0070030565217140910f102483c803452041001140c0010020005419601e200358694003030242030182d900c0703903a00719128140090045d01d200c0e04d580d0301d00002410f40900c0c1d0744207060300e0200144c4240d4407003410411512507088071200c4d000741d036515410010704034003082d0310400161a1a400c06001510b036080b80303800900998115810600d80d900785000c446900f0040c079500e07403030501e100041140600400b007000301e05200402018945454017501e440002070020100001c1c41569000d040d142d07488203000d001c40b0743c0300c6070383c00401940c902c0243e0720a0207094007103035a580020701c01c58070800440b042d0b6584640900f1701e41d11911286108140042d0011a = true := by decide +kernel

theorem cover : BRFrame.Cov 532194244 532374100 := by
  have h0 := BRFrame.cov_init 532194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 532194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 532194244 ≤ n) (h2 : n < 532374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
