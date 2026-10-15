-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3951
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:08:54.166837+00:00
-- url     : https://prove2.me/submissions/9769e76d-0a65-4363-93df-eb76c5387c8a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 710431654 ≤ n < 710611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 710432904 1250 710431654 710431661
    0x501180b06071e0623011404110d0203100e0a05070305070c0f12050417060121050d030506150d090308090615090603030c011e1a0a0303080a0b0a12060b04 68
    0x46810003102c0e43d0000d400301c00c200c1c3c400c5503004100c1d40d0a84d00c101111000729001070407281d680e824620402254500814220b8421005003224401c502d04248000300010650032111241e80c414809a200c0c3c2d40c200409000c0800b940c00409203080060401c2404e95041d40142c0c0709800c00e840c00c01094541c0c0b8011602803541d03003c002e1043c104041e0b10404504010030340c0d51490010300d0071600d05912402c0d58210380c01e480f00100119405100180a644114014045e03061504095142d0a0526844440c1d5580311410b10b40141682c4001080f4940c0318071910300e2060140b18103035955501d4410941d0300500c04560b080e00054584804250355450120f1614092440c81982d509280c03e20001c004004c4009042542d1500c41086000400708082c000c47c40c40c4051400010754480d0802c01d00f4056550002c62404d5100e0000c0200c1169515084000152901450608095940d8685000080c013100d509968482c0c2c003844002005101c1e40404000030b44506000c0c007a0308100c5080c041038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 710434154 1250 710432904 710432917
    0x11010f0204050f0607170f0703080105031504080307110319170405060a0e010e0105090105040215070804060806060903010509060612120f13120f0b0106020f0a020f060d0501180b06 79
    0x2640480082443e03103816000b0700311150083c213000304e68041070309961105a10000014504210104110040c0740e0094105801400250080d091503070700c2604180c0075030001132000709048404008149010302c03e5124800f804c80034411643d45d0164812460034801c0020f540790002f0b81082c0850400000b8004803a010b1079004000f00415110942410058000d580c0010201c1d940d511511490703803401d001d070342d014a1841000003001d0a2500602540e01c03441100645444000c200d070000081402c003c81e4103c4080d46003c0f04a40c0303070130001825a210b0603601c243d0560a080500007421000300e24240a29000c907810012091588119601c500001c0040400b48070b041c480503540e030350170900800210184880c070000d45621200e203000e80c00d0349060103491300906509048100020a804140508040c0c00104440030307150641c16616840d558009000c0c124403120000135864100580d00c0d5025528418440c4d0b68540c040554901e00307588c1e0140c00d050401c0e0300900d550414004490301c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 710435404 1250 710434154 710434159
    0x50609150c03090d0c1a271c030e01080a27080c030c0c01030b0609091b1c050910061a0309120d050f0702010507050d11130611010f020405 61
    0x38554500454150040c82480080380010443d40c403050f9115420749030b40d18803540c8140505401c220080062540380c89008409071400c0000007885ca03107500c001b24240c0303184081c083c1801162401f00e4901010310040350801c0455503982c9040580080b00100903c000b0303616003089a584130b290f41c1c265045d00c0c0c2078030701450141c1c01880c2400503906c242c0800d1405035821525221300701c0b20131445d6074450b444400c01500000c18070031566a00d0b01441080c00f10854003582004151000681d88000107866407605807540132003085081c0e400f20980d40f09040e00360740c0c61702c030341014102070015000840348400e03c1e00800d0201887d10701c8501c41d400548d10034020003031360300100340039481440d8409040c0207241d200d081c4c1a1041e1b1910240104440d146801e000b0172982050b0443d4103901038045c00035025079041c0b10821840f15404420381d50201d00e40e040110b0000d9440e0800540c921500071540030001c1d0841e404504140c02c420032482890701e01d0001c0020700c04000955089000b00c0c02600e0307 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 710436654 1250 710435404 710435419
    0x140f0402030a0902010324180605180a0b0d0206121305060709081c021c03060b0d020a120c140f040816081b062703150603010f1103040f03020703080d15050609 70
    0x8c83c122240c1c0c1802c0100c5881d000801c65103901c00226440c001c00c81e22401001500300b004001c1c00b01e070050002600c0c1c15520f40f000c1c030459a000800c14050058850b1411a045000819001d103900c10920590742180c02d440460904e81002007800d0401d0143d20000c0c8940780703d400d05050400c000100c510b00d08c1d406400c0b0801042d009010116041c51703102c0c03c060700c8000c0444c441d44400000c00d9003c55103440140d0700c2004a0b005030003400e00840c01e04c406032801814810064200000c0381c0c04e9001000020f95440740b5004a1030f270360141d40c2082c3c039584202d40504464022100d2a81d05582484040b60004200101000308501d16000707400c0c0c0048061001d41000f0a030020149000c0c4080d21403609903001e540301081ca01000c00c000c000d15445400d0500186003000c0c801c18229545c0b4035130a000d0b00e840240718041724440a00024998114032010a083c0361090003201c0146d640014425031314000c030401d1101400c54240e200c6031140c5000c00000702894014100c2e144510050041c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 710437904 1250 710436654 710436659
    0x41502031c0b060c06090601051507020915040207060f0501050906030a1a06011707030b010f09050f0607050a0203030703020f330c090303130801140709140f0402030a0902010324 78
    0x5902500030032842d0350300040c00380684800d501c000d000c0300e44075500d080c004081a41c9003200b04000c804112031885820038040022030050303269904046d0303216a41c049622a44800c1301c0c0403400a200e94000075199a150100d001d6000c0c0301e80c0c00443c100e80b000c0310010740644614041544a41c0503440082600c0d82c1015541d070350046400b02158003403014100141c0c420500d01203d9034003401162010000b070380d210000e481540c0c0000c01c20b0911525440c11010711420000800e1951244000b03880c8905808284841002010041d40c030819a0241c02c0d42e07112a40d51501135640c1d502d448107000c141c002c80d003810f440300c2c0500c481d41d114800a840c040d20140410852080d80d0750000d400400380c07403810448070305c03551010030084c00861065000032215a00d042c10090031181c05082200d5074003640c10611400c190711107287c1e0151032403101c0b0741000702c28140004401d202401d01c1756401c1800402000801c5a141c1e0154161900030f0320240114004002c1080096100c0d5410000c50f01c0a030205 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 710439154 1250 710437904 710437957
    0x207091e112a011d0a020108070f12050a0207052409010b01081501032903010608060112030f0207050a0902070b1302031b0d1b2313020702010302090a0b04150203 71
    0x881101c15940d0000283c03890900c1076007001c2c9802854203131480c0d405240e448045580c071002e800e510403403a01d000102240c681c8001400c60000040360920340d5120b401181d00d00b0070b1a4121080950312108844420f0250218603820380208110480500b010100142c40c140060142c9020410705035501401c0d6030f90f00d911200c0c0d0310903440d0740c00e0400da035903801411000d01c01d41308403541000400080210070340d00d40400d07007541d400350410502c9810100c01080010001902c0840090b410708207058400c0260504074a0a400c5a010a5011450342c000007140f04095000b02095401270811820a5036602642d05030015210781c02501580328520381120b403400304200341c02480b0001c0071806c902c0707600c3e21042014100e0125009080710002d07801c01c460010200d49002c484440c55642e80019103d13000504401d54400721030302030940024440045a100b6811191000001041701015640316032604490760000e0190f8007481c10807034194012540000240d0314011031503071003d0040c2e00c0f03070030b05e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 710440404 1250 710439154 710439217
    0x509010602190b1509010b0d0c020a0f080703050d181e050601050111031e0909131104050a0b040207150b0402040321050c030a050a0201061410030c0207091e11 70
    0x7050b800682000c9443c4050780d03805600c50003040347e01c003046d0f114040b8800340800c480075032007a28150b601c029040b4001403100c004084810b40c201f45050b0f01c1f6035550a090700c1511541c41010700a41c6004401546a441d46400340c0160340503040750007051441c10101500100841406845540400b004020707a40c41040c1c0f0000f0901e400c01564101600784452080e0840444281c0480800210b4102928109003417016031140c540c805010002c81591540c0701d05207e405c41450155460704000b80800e80c4941220410500c080d1085646003424140f2111807503448404010ac00d081c031000d222145854000c0e50305894208072a042c41801c540050030900020340c00c40006c0c420180009062060180041c0406daa81d584030555500c100c200001e003107c0d0280c003c400c44020002c88015540c88030301032105807405034180012a400d025a041c3e2070105994001e00841e401c105048510790841200018880c0c030681040c090740d0440744620041d40110340c101c81c4841c440e05c050b540804140003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 710441654 1250 710440404 710440411
    0x3031706030717011d0313150c140307120201150504020d0f05010617010510050d020309010905070906030521091e0a142416031115010509010602190b 66
    0x307040b82e940c1907946a00c1d90b48030701c6081d51041507943d01d42021075015140038000455000b41c50140d031403c1d44072030311924429040e000d404905030304d41d807009502500410642003003503000461a4820f03070440d04896030700e900c00e0f002181d98005800c1940a07641c0140100b495400308030541c08586400c0c40705202c001d400c860b51200e4510b880e0030a42540e912117200c0e99018148d50f80c0d8005910501c4412880d41480691016000c0c1c118042a1751000d60320034155800c61032003050150b40c03500c40c0040c150140260708009007042c0601a00050b6248940d40000c00301ca03c214242e44240e546500c0c00d40e42c19003078080e0f00600c1101045010032a142866a403080503031400c10054854282e440840d40d50b10380781d0842d60000c07805810500861810701d03060340c6103090354964500303400e000780350b002c01e42d001c3c0141c85c00700c89a010f1840800c15024500385104d0780030100890b80c0ba1a454072004003030ba60207100c2c0c00d0065041c00d00200e40e0b541702080321150b80c081d0401055541145d55120440090001d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 710442904 1250 710441654 710441659
    0x30f08040b180307171908040503030105062b0b010207080601050d0303110c07060905090105040504030c06020a110312011d33060a02070303091e05130908030f010e1003031706 77
    0x10049000041c0c0a400051401801c05c102c0d2038460740f282d01e08030840029180044180700c0c0035001c0000060b0b00000300c030b0549409860f096111048031910400907200950108e03a054800680740751040c11560240140f03250036800c0320143d650700d0300026181d91080c040c946c0c00c429500022404640a9044103001e4a400411507141c8610901d08a090450701e1b000000003400c402d030200081d191541d030150161600300e9042107542030070781e00075101c000503040c0140344a8020808a05e59130055280c803039600b4841c0107a0341d035055801680c0c03000007001d000302c0d9419440d0b4010081641e01070190588a1905a2011140076805c10000000083c441e8131540b40503030003401c2e040d00345c0c4544018252a4101c2d0b00200145421860080e0440032642c00c00d42d0743c525543c3c440384424807000d00c0c41040382c0054031a107c01030448280080580480113010303090a0001080c40703c0c00402d120a04d0480380f02e0380702107683e910b542ea01002d11001c580f00180020b8400d405241c2c85442e0b6120554110200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 710444154 1250 710442904 710442907
    0x20a030209041101080f0721060902070303020304060c02010204050d1e080c010903020c040c050a0c0c0905010e010806011d241207090b0a060f0c030905180103030f08040b1803 77
    0x1294000750080400315000c8420b0203d414100c01c0e15600b00d00003d0b04903a0071103401480b46040417008040c0800350450390841044040b40d903500709a603500c0b0001a006a06040d5941c241d00d04025002c2c0d8825502241c1c510715110001410034418070980d01580c02c000d182104a0080d80c80c0c0016031442505555024094042060300103990b19000b4103420420f034001294030300c200e050203810308419038005805681001d000001c415400421181d47c04070717905001c01c1d0580709040020b144102078114202940c5800000715403008082c80090495513014212b0f10181c3e20f0b02c0da1040d182b0400da403072600d002da05c40d005c541c1d0842d2080c00e42300001404c0000216444007400007410080507089410440e803c00f01d07041c00110064041c0d603914820941c1e2400c1100e01d01031000b803100d100301030354104208003980c040f4109441100004001c0100030940342042041426800c3d40680a00c41180454003020b06c1005480c000c1c04014800c9400c02902c00c2c080c1d961003c801030020610010030a603000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 710445404 1250 710444154 710444159
    0x105060f0d05070c020102060f0615070312060f03051c0806040203090f010f0e250603050910020a020309130e060601200a0c0303020f0601080c01030f0e0303400807020a 74
    0x109225062203940544e840c03040d0300d640780c0006810701c034002e840612411151000c0045a4403101c1039180342040481906035100c015040c01c17140030250548080c2c0e064180200010308036a0780481c0c4058900407c15225151009044102544114034406001c5441000002c072285000d078041c6034008000307001d40c1e04c0c4175925410282190000003110a04507501c030b500c0054018100918000b201010b5080b040d4134b2070906000001c01e8080c41032400b05615040000d01021081c0806007000c000e00c1015902c1d5000e41201070740f40c0c0c0113850700c0d5000f003a04011801d8102c070a4041c0350802581c0c0d402522564860b500110342400244026503004800074201660035403003005410340d824040c2070a40241410340c07030024102299103180749000c7e400b100041c170800c20040350000c40c101c1c0900b00094440070303140201c0080e000405001a10703000110030403000c803100d1420792002402c1a41d000c91582d800941514002442103a501140b1a078060860700150b4440024084a170000305140030096 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 710446654 1250 710445404 710445427
    0xc071401031b1d0103020a0c0615050d03081b0403200303090a0b0d05010504050907290a1d03120f09040605040513030216031a06010909020c1b0303070b0105060f 71
    0x9035401201c5000585030448900403443d0001d04410000003460254901115240000c0c5814500b50000c0c10320f0341c1e00c0c0355940282c0d01c007604103401400c0180c120f03c8007032003030305001d414141c0031180751840391005e140c0c81856504a508440589a00903e4124024240700c4408041405555401d405100410098070350b6565100258010280076002655400c902c039012010354006070f10460140707082c1014802c81240200b411415618140001146003c01e06686003007605021550000030800080308407201c0e074044c002400c2c4080240764a6115510038060503581d88600d2103202501005022004040304840000e2248050040022580944800020b01101e10a1300d500011005141c0d601c2d00b01501804051414a80041040c00300c526648400b8904601d5003c1030818102034400036003241e000e0704d4090301400030640700315211900300c0a03455a4071100720030328258620002e504010f600d0300200b203400090b0b0140d0b480281c1c2e441d2000b40116034200801c51018000140900203960 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 710447904 1250 710446654 710446691
    0xc0b0f0405100f09110607031e02120307030b01020607090305030f0a02070906080f0d08040507050f01030e0601030320071409040c03050604080d050a02030402010804021912081e0c07140103 83
    0x43c002c00300000c0c612905280203e00300350121003060143e481441300d0404071750071104d400445428086c41040140000c0380883c2450010a4608050900401407140c1310b03a2507403103061422020f800f107814944504d0307000d440151880c40000e1441d402000a2a0b1100c41600606801001c50049615041c0c460701c4c04800d07616a43c0140f10385900028400401440801000c02c40044506003503116050a03100d49480f2a85401807030b000780303103102c4020070691095020045200da03480680303815586929005112003d03c085410f403800012904070000400031400504999030341d1402c240d03819641c1d052101c0603400502c01e071404400d080f0000082001804040d10851080c016259180440e40b03140d8100c1e0f40c0a0311803a00680b0610030040180d0304403480a40268040320301c1c00400d100031440e80400134081e088442d44001904c00c0000700300c40f11001d0400c2c654a18803c00002c0254207a440c0c0034000c05491207001e5004840410042102c1c80500c0c0c130104041c5008281030000b00c0300b02e2040f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 710449154 1250 710447904 710447921
    0xb040e10051609080d0e2b0b011e03060b010c120203030a1112370b0f191202031c08090106050f1008061804050a050d0c0b0f040510 58
    0x406031514208091945840195004407840d400d00c98a910f0900b0144c0340e550101a07143d00a0100c20f40c52900c6a540705180e20f502601151410441d00d105000e0140c04001504c0b01128203100100c004144c04120f0503400300d040c9040c0c450a480345245890300b001130058070b40064140110001c8981c085404140c24400e50320083d00207554909154800c1f8080311100d2000c1d0740ca031281480310401d4540f6424035182c2161a0030711000c440d001081440c1200411044200c141c442400c02d14004030300507401445100c101261129021000007060001c0c0700c4203c00020b0020944400c103201c2c2001c0d29100103203c030b001034210340e072103c003109000d5440f94034004082c020078540d4042000000003401040007404d0300361031240c02c10fa801300200d56071141002200050102b140000780030f07a200d1148480c81250a03d120241a080038202152150384003041a03401c2d0040300a841103a90080786142100d65010611508541e5035065851000c03074040d004641c940501046514502c1c0c4038000c1e1020b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 710450404 1250 710449154 710449183
    0x323040c0b122a040303180b13030b0a09052d0a030e1018140d020d261e0919080601090614060901030c0207030c140406051c060b040e 59
    0x599003801001c49808040000260101543d04045a4240c144503000d0b6130071281d26003428080004620080200c01c42140c0003141e403c03002091002d144055202c07003c04883c0509880f288527120145018150303403941d40d020700b9030b0380a4601c1203188811000307014154a0920300340442400203041250410216880a50002e90403503106082c3d8507000c821000e9607400741c00e09031110742104104040500d0a0310403a60841004480482d03191220703484100119401044410001c41601e80640c012140e186550401c04c84042407445000c1601d04031084061103800598041e001d585001106601440c0001d4211007550308400c440131500c550200500a10409060f05606000d40c200031181e07154806130701082d42c600610141d0301c40404660f1039010031311f40420328180c10a4181d2910407150b000030001440044c0001d04000d6103603550024400403201403010565507010060b083d89810031040981038000c904000056055010681d440070180c0049003c10a1000090502c1c80d003000402 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 710451654 1250 710450404 710450437
    0x150c0a0615031a0709090e030c01020318061810021b0109050c030d0e0d0f0c03050f160603050c03061908031b10200706020d060b18010323040c0b 64
    0x402c21160b001403100743c51107000ba0548601d04140000c11940c503c1c420b042e4425501d181c00e6107428418400c45010324040002559a820f00e50401c0c00405a41952010540112004039a0b66520f002502e1030341010140104091104013a4510003580301d000306a400f6407038030305c48010b880000e010324441640103201811440d441c6c2c100341402c01840c1050a0200594440784444998074450f800e015580c001030900043c40261a014a140f00c598001418a200f035003c900d030b41840001c2c902e0b080048403101042c41580e503400c15019a281a101103400540500c001642814494040c000c0700b244829020314032079a91701202e04581c0817454488001061070355440107100d08120904060b004446e08005882500415a1441c05602d0504002c03040c006052018814150169a18641942410003174603076030369050100c0d5480080390010110284171040e84560181c400e4401c1c820351b01465001200c14a0440664140020407c50b0007070110f0307030049400280403025080311901c803015403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 710452904 1250 710451654 710451659
    0xf06050a0801090b0307170102220f0815010605031308030a020405040b1504050d030207030c06080f070201051911040f140909060912030901090213060f080c150c0a0615 74
    0x901c8408142c100706203040c1040d04e03414007a180042ca200844801a4960325105d404420b424060b02c1440025503c400c004148a103450742e03079285035022500e1108034440295074900646450700000303107581c450420458010001d1a0003000256801303a60406400e8020661395210220340d0015141d1030380c0d55138041028803090400e0703c60005015011100603035100342c07804400c140c2c3e1159025141c0240414044042098002c1000c0780280d42c0c019a00700c1d58907207030342c0000d20400044801030309001011002c6510030740180316807401400340c41340003807140782100750000140c800300d8030f500091101040000380724842c100c240001b51083c00380903035820120030108000c161010701006d0407a0040230502104a10004042d01c0c06416484240d40300d589100f6414010030a282000e504808125101c5040c884180d1000c019a2515024030307480315125580566070b071142c90783c442d0f003106002440200d15030000e8080c0c02014100421100340c048169603420507101102507803070b41090351a405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 710454154 1250 710452904 710452907
    0x209070e030118171b15040201081f1a0f0309010204060f051801230c0a03020d020a17030405030c071206051e1308040503030a080105090711070e060a0f06050a 70
    0x320714040b1209410501418000d8840751341503c402190b1448240000410121500300d100194180c0345d00d0205546031000d1030407510011120807241240041e04074400100041c43c0905006000c901c2c00b10310002050030b004441500f002c074043c100340e030315909100e40008416104000d5101e800b22800141c1c030b0b2490040c1c06460b058042d0010b00500c4010300010500b1120a00b201c0e1390703601d013460301c5600381c0c02d0f820b11180c4464004050030600040020003001c0c00c840000c540c0195440307a403c6441007a030310340040f07032550309a0800070b08001800300c00e8042004c002019641082c001c805803440c2c01c070041d05079440c01ca0594480704d440074190340340106100851140c07540c02840581454550360741c042c000d0310080c1004092103018a0039540010900195900780c0c0d001e010003804590f41c400301c0d8940608402400d206542c46040954000b842042c41140c83c4089000c1c10002086e456050100095000780300a1407107402c00c0c8030400000302e4411a40218000b080706445d00303941ca400001c070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 710455404 1250 710454154 710454161
    0x2e0f030512070317070519081510050a120f0903020a0605010603020901120914060c09190803070b1f0306020a180807120303060302090126060603030d0c0203070209070e0301 76
    0x280c540d10301c501840008080f0350000000b04094000521943c069901c2ca2426611030107601d518040c4440340030140340919401c020070030700444d0b291007034001c0004003078100301c0c00840f8105614001003040c00001d5a9034000c0300b894650784080070020400c81d186058410072140d22001c140c0040e800b80201100307111031841064003400e81817178290700d000301c5400040c064020f40f410b000010b03070343ca070070150038040740c0e01c50b02e20800d082400b92005401d04104484035504183d64180c03141c410f10b6103045042c0340358440c0d041213820200245041c03020f035444000700b207880205042c484180d40e0078541510413202821002451080500603116000a8802026090804200424401e59881c28080d039030000501e0f00460f070310303061441441d407050701d01140134250560009400001c2080081841141003e051649220002ca014038044a14252682e174120944e01182c154104002c04502c214182d0031681604503a801164580104d580c04a641e00e06c0407202c1c540051001d0000e56114603084c003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 710456654 1250 710455404 710455423
    0x90809060c0c011d010f110f1506280501260a0504030f0f140a0512040f02090c0304030504052103070303090606062c01020f0f060f1e2e0f0305 63
    0x14a40b0f130b0b070103045030029021018440088040c861284103c0010940c2000b032110013050340c00c103640194210214065141d2015a042446240b08404c0f0000720640031100f014440500300d00020003515001c0151020314030000300485400b01000c0c1c265074448842d01d00c5024880c1a400004c8524042c01c00078050700429801e01c1c204410b12810303400a0b0391182c5441610b2580d1101c1c0c0e41e444480540c1a43c2138030940341205200c2c3c1001c02044144102002e405441500a58031f10311203544d0000050313031510080b5030040220b034007440706110382c4c107041c001c3c1071000c1d803804640c0400441c441099495508803410440009495802e850100b20480c044d2200401890401c0c1e2054040b4105103030300250010700009a0b445814401800346c0e208000c5d800c0c1100c0301c0d005441c40d405079039801e2030f2621011900f403100c0480960210b942d003082c1284401098106810f4a204da40b18040b174070750265013144e610b0109010030907050f4440c0300007400141c02031441108e070b040b55030302d1450002d08260061 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 710457904 1250 710456654 710456687
    0x314040b190204080d0c05100b1f0201060509011404060602010b0f011d090c130f05061206031509030a09080c181008030d020405090a061503090809060c0c01 69
    0x14080000d80c4800965005200c60301a030000c1c8002407280e200030700a40d80300d24003d10034205801145604805800c1c503103409201503600412005c0c0401e42681c00a01d01d090300500c4000e007805030f00100100c041020140e51001023421a990f000140f0500000c0c0c10034104190b6400010041d8901032007020010811400244003024070341c0b00190012816002c0c2a061003c40d50050b211496030000340400b05034014045030b50b0f03081114040445411081c043c10800f41d000e01c0106190691940650071544001d1030540707403904480c6801441c00e0081d117003d03003610661250000e02500b012002e44103000100042d034403104100401080ea90301580000b080e40c2224643c08150f0f00c070030380c01d0958400104800798003501c500b542c003d8072000c15030020f10710f0300000c42c141443c0801500204200c034422a080552a2640a0304c074003115001d1250740045500c3d0074003001400d00a4208460090040c9a21420040c508001c143c0e983d1007001c5032011030f0000c1c1960301c0c09680001300d448245d00c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 710459154 1250 710457904 710457941
    0x1120c08010f020415093b04080c16080a0821040503090f04060506120403053007182306040b03010e130c0b1602032e09080301090b0a0f030309030303 66
    0x301000814080c0408501c050800d5002c7c00c02100b041400301111306414120707500581d80d1034503007480714982c2c00503544e0701014082c1c8404954000030381e882000507290070b0350103026401d074240d441d5821540504103490040c54203a214031501c03092141440d100c4d601540142d03584061000c100a014440540001e11440c0b03070a5091099071104010f40b040c2c0d549240c00c0480c2500d8500b802d403078500078030800803180d11002800e1000955494184001950445d202c4801c41d1901a03080d1540700000b148400000c400e80010420110300841c0c00f181d50300d04000c4000d1042d25240841e1541e80203400003c50142c00200402c198005507003007030f40c4014800194046022195070381c01c0c0944103031103042030140e008151000080524035204070350590080c221000e640b044c145109540d880b424124150042e058040e08101c03280340540c0b80b10640c04003950b4507581c00c14100360010304c4602892034220100c01004507000c166180d03a040558041d44648030180d19501e001020784010441d8011180c12 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 710460404 1250 710459154 710459159
    0x170901140a0b030a052515080402010f180f080c0603040f0803100e01030f02090c03090c0108090f06090609060604020708030105040209010c02041b03150e01120c08010f02041509 78
    0x2008440c0d03402010222010668103107840000e03250103452072000e4918040d007510289100d281064004103003221100c603076146942c5100c2400000d00b0a050307030000c80c58010000b00150301c01c80710001d541800741404c641c8004404607065507075465802007854034040309410b1062440810030300a691100b1a0480c0c598903040e613400260590103c6c00030b15020010010a00507610706e00c3d04000f9101985081a0541c1c0d82d0030444140d070382c0c0301400c0c0e0080c41c0c440c011074484148042280d2140003400024100201c1c0b0700b00454400c100200001128040d001044902c3e24090014500420b840c40050003242407501c00e450a00320081d007a28816841049a240003426000c141c03030444008072401078071100c0c2c600c0162a44020798400039801450440c85d44c00e2003040d41d040c0c40303281c0c0c440d5404011640750010780d0b12140030180a1106107000d102c0042008900c00342007803030040e108102c1584003954032000e443c00d4900303241480c40103039004141840b0f40b00740f0f2601c2d82c0c0b10040d0751610500351403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 710461654 1250 710460404 710460431
    0xa030819021513020904111504152a30090e0712020306010203130305010c1b05030d0b0310050a060608090114010e07030902060c010b041103010305100f0603050a03170901 75
    0x1c143c07400034080c0741c0d10380002c2c090100c100450036640708090301202c01908100612501d5034401e001d1741c403da0300440b1450201500c070300c220807074100b2200311003420500086164543c014016808803050704051200c02d6507401e4103d081c007580003c0d51801c68681440c24006440218682c002c1e0741e01c010740408124500b0341c8801e5040c0301c826100b90040e034903251800105e09620801361544c0c0003801014000080050544c0848441c01c500d590f1480404400c01111405c030801c1c0300e01810a5005211910b024509603000c1258140018101d42c58066841c00d800144d0781d0894910848036954402044900d8100ca241540852214020403c82d540900d0181400c10180078207040d248000000441e114025485020a10f03002003005440d040d0785c0c0800c80c0600f10460300e0343d005a042142046007032a49070709890690703070700c80c0144c02074000e16180e540c0103080b51007c20b0f080eaa1900c0e030000c007090081c0450410a4003d588400354000487c0200b4807a0704040c100c0642071380b612403140070f1035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 710462904 1250 710461654 710461681
    0x10e0c03070c030c02122a0a03050c09100f0803090a05100f110709090804171204090b010909091115030108210408030c0303160507020114090a0308190215 68
    0x2d540350916aa40b94068000f01303000741ca51011803201341c0b181e10a829141c0e40e102400b0001201c1d02d280b2419450701c0c2c0810700c2144021844001c000358031602c40101c0178134100068551007000000080e5005907141c01a2074402001e611801d0944c100040155203410100401c4001d04810340b030f514203610700d002c1c0003050105141084010480020590610702c40d0900082c001401003500a2010580a08002800d03902c24030800160251001c800d20640502182140d0341d0080c1d01920b0313050529040c0b140e4060100a0002410041c010402190340b04135803280648007030092590007110318801c4107210558910860300310388100e044c401001048000a0300b0140150021081008421a00c0d00801d084c0915000300d01c940c000032074403a029000000141d03210314613109174a20241038114003a5420b11855802a000402c03c80451408005920041898500280c0078003145682c03501c4101060f042081031020300d141d03035015010342030340c104401c00c0c802411020480007814010301a00d8803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 710464154 1250 710462904 710462927
    0x306060212030411150c07080705031203220804030b0906060409111c0b0106030b031c1407020102150103032c030a020f030a0b0c040f091b05181503010e0c0307 70
    0xf80340707401c6614078081d01c60100303001d044407030905c400d034840c0c2a000050f519181c55004101c124420a4400a45031600003034501034041101d4806246498281c0d083c0101e148945411400000f01d070300002c0001c9508000b840110300505404120b410034140c81070410b00d001d00240e01c101e05010114021500d1003003c0d0410100031034004031401d0f014031650030745504c40f90002c1e000000750400040c1c00ca030950007003220154110b003510052002e152100c5c1c00c01c111684400d000429412801c01122440030003071074181d0050040b2694507581c2d52601e42210f6098004034002400207818990900106100c40100b54503000042e020311180300220f65501c1d140200680f0440110700da45805132002d001e0007654540194003035200d440c1940c135070300156100e44180240302d9818180011003680c18403410301032081e51190540d40c1d107100e110817255504209400008040020625901996000340c0e00080503a91081103442e07614081e8a2101060000c1000807111020010009031a600c01d0f5072801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 710465404 1250 710464154 710464163
    0x50703260a0f180f080309041103040c091116060b0109050a140d1a0106050405030c010e030a110121060302100203130603112a0f07080c0112141603060602120304 71
    0x8086041020303c1545840d0740d21152180c0d5000501017000500030008080128081d01e0034042150301a0f101c220520044071f000e0003426030418140a041582c2d00308111210040c0d00c058180f1458802c980304240e130089086072040d544004081103544c200a81c540101400ca4040a10350b00d002400c00d1401403042086106010b015030042c20040700503903c0c4215001803c0317001a560f12824058515881070090750f200b4411000c004009606c5440d10300e2595001030302030404c0e0045070740c4038182c09034005549814040c0f0b035202d600003140c00c21095040641350034804a00b0525600500c0903640140c2e40108c00c5420800121040c0200e1821001c11103569250001d01000001954100d07409199829400241c031182003c1c41945224824090728018034117640c00d0300d032112003069640126200c0c44803182c000c56003d20840d07006a014000901c110700001c1342c44070480d9161a03419004841808500c500e04000f0201c0c1a0705200d10000b07041203000403c50a101e040400c4418000240001c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 710466654 1250 710465404 710465417
    0x200a1d01140d24080c04090f030c030c051009031701060206011703070f0b07030b04090201023406020601170f06011a0702090a053408060a03050703260a0f 68
    0x240c0c41c00e102c0d0b1020441a00e1001c03240c45204a00b50084071005840c4201c000740d00c28400c1c2401541b400703220341900c0e01d5000c81202ca4041c00780c1d9050f10f40344d2101c0c0094041c002019403440c082a02031000000d88a4a1100002d01c0561443e010700003516075001c0420007410100103214107500011300e281950729564802c1c0f0210350081c01d0618500c103001c4010301c110a824841000c00c124455103a0080000e43c03400d01c583d401107814002160307080c0102a0069111086101211184915007101218141825104140d54140e803418685240d84154010384c8640c0c010400c40c0000c09096801c0303a1540d001d8051020041940f55455406000e09580c249208400005220720201280c64066001d00303100420314081c08144010002114041c203110070751140305040f81010148046164290b640d00003010700e0660341103c3e0200001c7c000391b044202050701201040341003140030001c6106000380003055101500080d9400040a01580e4280d024003060641582007c100c41e0000c041c0e28000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 710467904 1250 710466654 710466667
    0x30d0e1c2a1e03020106090b0d05070510120207140f0316080a1106090a0c080a05151302030a24052e1701020c0c2e03200a1d0114 57
    0x450403111551542c05120070100b030014101901034200e00122910700408100c0201c104042c81401c501482c0700410355000300409001c2e5180007810000603821038500410b99039400644201268003602c81507408403580352a102903002c0c00c018900342c14440101039810010385e40b1011100f16100040205049408144a468a80b08502c000e0380d1410410460f8075604140b03541e03e49444201d001a1055200128080744c00100090303001c05056202005008542c078004200c1c900d0440603064008900450002c0005070b0b4080040c0384516016107040080007161020401000582510400c0010f00b0001004200056240109010f9904d400b03038050b110454480840862840d03005508140c80050255000900c154098000040f4010032281340c8003200c1e00700000c182010410344140d10020301700ba00f40e007a00c0c14690040d20440e04000c107100b295901508c3d081c1c001c184403172000400206004814640c45117410310400c0a0301d5800403140e22041c0024108181d007803983ca26500002800c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 710469154 1250 710467904 710467913
    0x1820070218060414011532180a0605120f060105180f0901080307020a0b0306150a0302120c070515060f0105070228030c080f1b03030d0e1c2a 62
    0x303010100d45403000c0c2c442c4d543c0c458403240707100152041c09400050b440c1a11012080980e254484d0003601c90b240c04020381c24204011184d40d002c071010095507051000c602c45140c9a210040001c0c05a81c1c0b910b0307403500204007a801d82000024140c00309c08440c0d805000d400d9030032008403800402069164846d1002000200d40381c01420300308941c000028400000c0c85200c08000307040034500c00c81d449510700b50b4a100c55101030106507501640842851440044000c08200408040d0b405080250074920320b9040842c2419003111100c10381e103c00501c8804000382809a03800760152102140d506080000108030380710300034407025051210018800701995aa00703103800c4140f03c080316801003e00351070040042c3c2e04040c0710440311400c21500c0400d4606012a07514050440c4100400451280e00000800501001c407115054001003020542d21203445c09044800f4081c4801403007100b070052011440341c10350102c20820000804440a20361101a003038480090800701c0c034480001c0c06090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 710470404 1250 710469154 710469161
    0x90207020415060905040f0b1c051f060314030715021b01051311010212030402060f0d0c0e190e0115020708031204020a053718200702180604 62
    0x2200a091542c220300054030307640c0300a0107419524103440500188007040c104409a030311480c00e4a42c4040d11614400c00c1803d14014500c055004800320303860082d14058040c800c1d100c1001000706591240d03c188180300a1204101d4a00c440d04021440c05280d5100d0301e04c141b4080c0040c55440e0b40018001d040800e842501c0024540414020080c2d800c1c003092071080c4c48040c03001219841d48100b000e0100e5030020441401102d00d10700602d2540d9100c0d401c1244586c03044c80c4501b60010248040102c0ca01c1622132104650322a48461450020840c00c000c3c1100c0160784506540380d004409100c00120b190042d070440f0000f1000040301038081109a0500d4020b801c0010360f80300104c0c58442e06640101c0903800f440c000d417402c070000340e180c2090042c1c001040520b0410760003c00c0615207400442d403405002d070303170300318003018009512030041901e8150700081c0c007404542c40e01d030074280c000712100034500001c03503908007180740c07003980d03404213601c290b40d445c0c481101c00c0e06200141c0075854982 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 710471654 1250 710470404 710470421
    0x30e010b040204091d010902010512060102030d05270f121804051017060c030f060102120c100501090b0f01231303060c020a0201120c11010c020124050a0902070204 72
    0x401c15074840b500c1d100da00008005011501c0031002416080c0c805030901845804045a0180d462a1038020000c0c014502840d006c0c0c015030440c4410412a98105e44504c10280120b01c0715100640440f0151041c081056110030500a150403285641481c81c600060291322505400d400503141c2180c030110350040351a042d1102d41190030032013004074070441d0200c04000d940b40b400c2800d45a81c5070241c0c941d40c1e85001c540d8003080382402c1010840c80383c11181384a9100e8014030403610407000305803503890203402030b0141e40002d5000c050151041075041c0242405000058010000c4040400016802040b0012100e0601400c0c1707404454045040c07045c001c29a40b0b04400c55a1421018403100040c84544020740d0041e00e040401c01040e0305c0810002076080c0c0595411225105801441c8000c0180c10715080510207400310540020700d0a0240006001c025000040e244039030003004c17040e1140b001c080c00f90805091000344103580c3c5a0440d601940c2d01004010f03220b140310b10105009002c5803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 710472904 1250 710471654 710471659
    0x191505121b010e040623190e150d06063c030b0403140c160605120a0506040902030f0703031b1a070c06090b0406150308070803070e120c0910031101030e010b 69
    0x4124254400c408910721b800000c00703036440f1800c6650401c4292031041c1501034038028620a41c0071890520f071030301895045041c000d040c011260919070742c000c200c4601c0c0c0c2c401c02070106007000350306010b543d030b2015001801c43e491414500000751941c0c2503801855000007400c20021780049000e05200d001e511202c1806030078174903958001a440d00380d82e00a400807000026000310000701c1c2c80752060382a903202c00080c803240d10483d143d44010001034200209944c8d0059500c80c81000580d6040140780041d078100ca002d018250308500f40101461031460800341d42c0d00881c1c4034540000c44141021505128880a04419495074a011648550047e0014210504000750031044c007146041d007a0080344100303010010b04c02c8080340d03404c2e446d45030701c0f014013462000c1c4150740120360502e0080d90700c9134031840c100382152a843c0006902c514141c030055000d600c0482441c1032030070f1111030705410045401802c44d01d00d26543e01c400070061482a0f0f681003580b2201400c400c1c110940020b500700800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 710474154 1250 710472904 710472929
    0x1d030f0a02160303020a0203060c04050f0409061e0207140c060a0503100b0a170a052208070204060b03071d060301050d050a06061d0604020f07020603191505121b010e0406 75
    0x403400e0086d1340d03081041050f8400c1c0248004130301c070300300c11100315411100e006d400c040c540c600302c1d4108002411406c1007a50f03a5510390030031030311150b05030690356022040100010303143d407498103120b040140010131800242e4402031884c801c40c0e8485003565446180c0d403626542e41e503950841354481d4903003648040c8004101050003402136030800803203140c10741c4401040c00b0aa64409111003619415540d00c2d510860302d18002c491314400d2582c8140c00c6004428480c0340100c02d9010034210707850307a84a481000004800d11075144da1140d5001181000c0600a079906150a030015003944410b1207030034812180d082c0c0650802c102800820605500628204101940c1e88003620007541c0d0841e01140b0400103000040712803400b442900c0f840004a0070160600d0255401c5c840a0380c0003601c4100480d180088084100110340640840000200c0c1c019010515140500452404040310a040c68004145010a07000c240c03078402c040000901e00042160414008900203240580001a100d0345 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 710475404 1250 710474154 710474159
    0x201507110c0f180a0b090103150b151b01021308031b0105010e0a0e19030e030111070528050313140103021204060f09020a030c051f090603050a0b030610091d030f0a0216 74
    0x50346509c219102d0024000c0c080070010108001042c1c000260b002075107201442170004d40100b500c0e036842d80003241400146010034644c0164070141c0300754810070301d55100294985802140110803801031010500a10144d41042580301140400400300d00700e0582d62480442d401c24100311a00c9002c6000e450740c40b002109090041502d405911454060b600742045250404034007001c03114100c1e0000041d0803001060809802c5500d044000f594012141100c8a0701149003800103090000c000700c41c19181074079024080c03882c4c1149411480c1854814404403001d8109900c2c40c03680103501c1000060f8000c1d03070f01c189400410310000080d4022024410200420081414400a581c4203c80c202c1c10801030b2a01d60880d0000c1200d1100001c1c801c079000c0105034000d411075500140010340214440b4026030200345040000c45041800020500c42000391034250310407140c00c1c01070f44440030075410541c44855600d22420300060107141c40001c40141c5588248900c115001000801309200c0d03a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 710476654 1250 710475404 710475413
    0x2030f011e030b0a0203070905060c0303041208010323120f090a15020316031b050c0405070f05041a0904020304050f011803201507110c0f180a0b090103 67
    0x1090040030408000d560011246400700c0e41520110b07640030715155015915015400080d410207413985c0284503030b414010410b59919000307055840488401980c9034580382c181400d030107654a05030014805c01d180180041045001400d005040103454035074040400c00481d840e10003043d004007490040840d64103401002c0200600d0a0603040790349518660310317910390708813901c01c12040350090703402000010061103001801003041c0303000c2c0c01c044002248000001c7c00d038421240040380c5a800c040404005c616003480f41540040280c42c04409002c11158041d00340e100728000c0d00620310a042a0f00c0c14520900116030001c04050020f540364185482d00503520b680141c40e624a6500b409580c043e044c1d60800b03031402003038040d80d600340c1c90501e6244013210401c060741501140e00030840c0100e0144400390405000c1c00312583c640c1030701c03200481800e0800040158036031180401d0003040b510b55071100e007040c80c0740c0c481251040d9a62604100c6100800407000044c0d00600403000002c00d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 710477904 1250 710476654 710476681
    0x50f060a2d050c120307170a0b04110a0f0c0309061b050f010603050712170a02190318060302072003071205011e020c061506070204051003050f1f0c0507060203 70
    0x4000e03c00302c9402c00398000c03051089000c2152650002030f1107080c00006d03210719070340b8113030089110302000a400b00d801022409036602d0403000c1d01a000c001900e06840b50303010550100f0640640b03407448803c402603500a00f81c0c1110701c08d0400300300c0c909941304105400b580441c19225070210450301d015042045440c0a003070b0300c2c0b1003510300e80104000090209210b05c003500541c1c0d03015601640c01d01540342e261100d5000100018218410742c8070703185c01c004640c036440780707094001c2d1101044a400d03904003104485483e00040101401480664009007a0003030200381c807800c0c01c1c441002c0f14031340030200c2c4c40e02219520141c4a181400340d104103101c8194030152292034202d8004101040c113509001c2030741b140e1124103440b42e00c0b0000142101c09406021514000d005204d24030f1b10006400007000d03505c00750f0740d4480007107c00f032080041207130400c2080e0364102c82502030481d030343d04002207142d030001c02c40304403001a4444e00b403080c49511034412900c541d03074400f00840d143d003080503020448 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 710479154 1250 710477904 710477917
    0x10f020106050a0f060e06160602030415050f01090b04020c1b01180e010f0906360903110d08010e0106050d090605130203010b0303031003110d080c0a0606050f060a2d05 74
    0x42214039140d10b00c0c078200801160422340394204a450f071450320341e50f52002548010f005680180e4620707882c4c0000c110500070107018184046a030b401d1541000021412a2100d01045209910402141074140301c0801d0913500005207800001c004030f001c2005030750a02681c1840c1c26444500b8401041c884a0464094144c50302c100c001088544c60340e0420080f688940034130503000000345d1440311132a800320360003c0c1140f44030f0b80720705020f4000303120301c01070b41c42c8001d00f2404125800f000c09060b001c00c1001c8200300d2100d2920201651500a0040350080c06010701401c0001c0007608480e80650b0341c100364800f5030700030010006450310300d007841019588a030040384130b5400c2813044412450f00105580c010f0340d10b001100c0c2c49902d150344411800d80a034400c603030000c4607017901501007164003014188a280f02c01c040d14030740045e031030004112452500864850040310b500e9504a84580060352031240d1141001e200d200c1c45014800d0031005c10000440760310b144000d00e01080340c0d114014240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 710480404 1250 710479154 710479157
    0x402030a020f0a180503030403212a02090f010509040f030c0c0f2c01290a020705090112120f0210050114010f0215060f0d0510020403111e010f020106050a0f06 70
    0x2444c913120003c058417032180384009000c07040342018540e2036548002440500c0402800c1014086041c14841c0c5849001d03050840510400b201c1c150040d41041008980d1202038140ea5070b2203903040000040c17244001400190903040002c03001c508050084004550282d00940000d1003541d84141701e030845075090081c3c0882d0361501555001c0326940d20007072114100030509018a903030070720b10050305194410304585211084060b11104440209000340030030301c4035501601e08241007405010709401d060340044504002950040c0100d0301404207201c08031040d180030307410b12420410403440c1a45500301001d080e842c14000080c111030340c0000d40001502a00d03000d00c50b254400d07042e83c0b0758140c0c03807048150601c0c0c9000500f1500d0041c40702021044002e1048002402a031101c602d01001c805424081c0d542c0040c050003400458203140344551412101d40c5c040ca500d482a00210100102c16281445281c40318480e04500079001140a4070b0003501c14100503a0b5007031103e80e000102e200b0782e170 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 710481654 1250 710480404 710480447
    0x5120405061b19030b010c0c0306020d0b060708180612090a020108060d0b040b06030a0c06021b0603160804170a0c0c0504090b0f2a0703080702011a0402030a020f0a 72
    0x128454402d2050303030303525001241810411400b6141c01d13006455424801390400c007406403124001a40e85c44840c0245001b078100517202e18540b03124504444504100f18421034043c01040b000914142c01c50b001030502441c2c4140b0707000c041011032003a005261032500350a01c91400c1080b161000242d07440064001d030707a00301d00c545401040c041021212000036182003081c900007008120b03040c0c2219003048029040707a000c0102500e80781c2000b43e03507421a40044e0005403604c00314003a000580d140504048800610710305080b21440d050607800d00400c4248007050b000602030241d03041c422100d0080000c6050754903581d1840c0185030302540c01003250102c4c25040042040d050a120b4441855441401995a519454140345200c1001081141500e0143e104440480b000d210448940384076a00b00310f458442918001e440044003c140b1811685402e032980d000f1903c1202c0c80030342001c217030741c0140d0700c0c1c450040000207031240e000140380384507001804603142c030703801500c000f5040362408104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 710482904 1250 710481654 710481691
    0x50d060245220221040308040b060102060f0a1a0a09240305060117030903070b03010e07081012030905060711090c07080316200706020c04051003030f0512040506 71
    0x400204404145000c154030702d285081d900c04000e5004000e880e4075019400704000c04102d594145060440303040713000441c20780a2004008058a4080d04100b007400034200e540f4080100d21035401c40244103407030154441d030038405210745041848560781c0020713004100c103135107400e41000a000d08144140c15000c01c6140d45800e42e001d0314556043c0ca074028054200d5905e000c5901f004034000c05104076250104000c6824165420000f0100802014484503160742c50440718030000040144413801b03000c40e000400961031818070907d026900e09a010108290180c101160710964075007005400c00e40016158007400301c011003000b09401c08560542880c2e5a2510b580003500a074400241800424404035900c0d031012081c002d500029468040012098000f100c1c00c00090807104021940000d2800e01c171060b8180006002582e05590030303c01810808100b0740d200844c2c0c032004c0c2c00c01c28000751081e28288110100d990054031072502c582e807030a06047c01925800180c9445000340c43c100200d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 710484154 1250 710482904 710482909
    0x9041103090c0103180224030a060501030f0903020a02090c2502030d110c0609060d18052a060f04121a0f04020d11150a0302090f0307050d060245 64
    0x41c0c040400001c01700340c542044580c244422600244032807048998100c0a50480003a001d0285205086180c00401c4c0e0381d2418001400301c80b0341000c5000b00504001d45a8082a000107501300340c0c6034191001503d41c0d1302c4580d032250380e005407207100039104021098901450380586031850302c3d81c001c805659119143c014269402c1c01c03e81c42c0d8121721303041a91040c200307250800140140b01300140815103000e0a00c803180d4200c44100300001035210304240b03c0811302204120302c00c8888441005911050441514400740c9130030408218450b03d0001142025100c8290545c1d0040190404d2080c45080910741820191808140b01c40d04510300d60000744101808090180140c0c0c020b000240c0958a540300c2800f045481005190840703c051580c0c8600e4403014010f0448c1041950011b844c0c2a00c2d000b009844404180080d00c66440f00009019a03030b907207a500d21060303a00070401607544401c641190a40c0045940d0381c0304075000d40341c6801c445403d028410400a003003030300308904a03866004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 710485404 1250 710484154 710484161
    0x180309210f0d091202010c0b07030903030e3706061203021203061c0c0e01090204080606030f0d08040302010b030604060903030e01060b0a3902010207080114071409041103090c0103 79
    0x2c1d400042e0318902c10018840404000c01100380181b400d03009000c025280e00000305811b958440001cbe55958528040c1503240c4226060004040f006d81005c1c0c94884080b84a0103e4080f5407507000c950680000360011046680c08100da40070009000f0070f0b03502c5503802d1203252002d03002d50142c01002449013900400600302d901c00c1e10010803050450b00200e80710740d08120002c03400c030b4440d04048000700b042c03090909498001c00902c0000340c0c0e15810840101c2c00c100c00a0700041c044d510034000355240580200b12480d129089207000c11a40d80c039420228050000b56044503014007840c4280030600500c0d4010201c0036008ae101030100504055030942211001e100e40f10407281c0c140011800c2d24860b41425005558640041c28007400c1441003503080c01d20700401514885490b005003085580600400c001403410354002c100d4209101e000c0021a04010251410483d9520072040d880c1c0d031200c2611009070000d0b00401100c9094178031130b0410342c400c0d40c0312121031048140702c00c40c0b0740c883d00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 710486654 1250 710485404 710485423
    0xe0105040612062313230a1e0b120a020a0909051006140f010c0b07080709091e050c0f1c02040b0d201c0c0302190302070308100e180309210f 62
    0x49043c440d82206d1500c8070854000d040745401039201c400b5640c0340c1072002c0e00d13081760060a640004030455000e01b00543d4040c400780e11113003a0811141c1d1000f40e80c0e900312100c202e8500c0500801c0c0c1d0102c0713181a60624180080e24180700f403030413801044400b0800e200300500708007601d150380150380e00f0b00151107000307446000070510500400015040f500c62210540c01c180300b428030814460326005c203201528400c3d940345603040385010606802000318001c03250400e880e85022031800440701e400d0105072090000281886100342809052903015604941c000c140750f40400340c84c1c80c90212401d02030803004110003000652341c642c501201e0300d03080c03c0b60000000907840300e81d280003202180c006094840070500c141030b401d02ca03031000a114500c0c0b805151846aa0069862a451034040c4c078414014015070040c801c00b034018812180c1c0b01e10003a40002c00105000040103041c402e16146118400700b40f504100401e0210048510200c0c00b0075001918a040c2d550310701c81c00854682c1e8603200c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 710487904 1250 710486654 710486681
    0x5130f0e061012090503030402041d30030717060a0803091224011508041101031a060f0918060a050d03022406100e0105040612062313 59
    0x24010544030b00d8801242c0c0c02021507810148800704218000c4002c0760544401501c00c1e0b00f0010400045207854450341c0c08203142c04202c03080b01f0031056282c907a1001c0c505140707000f075003411300e4a00030130b10300c5406003150744110b00900343c1d40d26192100500c04038a01545449003182c44012641e00e19240812070140c4001e0001181072030420000c0103041200c2c1c00828101d401303900f940c454841244804821518041224514254036068440300d403142c0166510302004001c400b0f110006226407171554011200b4070700130464030700d030110084140d043c00404c5030344a44c0000e0002c2e0803c0d07410b805040b028100329004030f00f90185074a08546c41200f01ea100d0b6000d0301040301407080c2c3c03038003443d001c1e11140684115940301c1080c01c0c3c0b52060502ea030100310580e000c07071001c100441c0340040d0010100031182c80c000861101505c000307440c5020b00c0c000c2030b0522038110021400b91502e50b105200038400c1a8440344138440c882c0422281a10a4040038040e0383e1402c0c1d154040d01c058040e041c1001281d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 710489154 1250 710487904 710487929
    0x301060b03061905040903020f100621060e0601031203060e1003020907170c040f080307051011090d06021305010503090c0607020d02030609010605120109030503060402070314070305130f 82
    0x8503020094060f8401c4001c1001e500c1d80d00b400325803611244100026203110b50024465a012078100302c0c900043e02b4104c0c2074880c1801428040c0341004482c03902d0103006c3c0e1034a246d211005d031400034040c21410380c26180d5440b500303000109000c2c0003809254600b045840400845444156800300590100c031780c40b070a0300841d2001c00040c00c1a10f02c1c0f561120301403038a154007a02d40300c4045141402945d9550b5610f00200d0148002e51000134414000d10500000b940b4040c010f58070691a103102c0da03400880e07560303a43c010301c0c0081c0c1c05801726001e600700100f900c0c007a2286482e02034000c3d04101c00d84a5200340b00140030503035500410482e40141850b030b0050040e05008820000136904c00740040340c00603c4582000010b850800c41d40f8021103201001085040c00c0c00f0602640c0c0e0801114141203a04201c0b100002c250010216a0400820799015a4904c1d080c141512143d400302d01c800041d00d40019080d00303250b8803a01a00c095159446d440c190b0541c0c03401c405840425a00810805034030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 710490404 1250 710489154 710489161
    0x20c031e0705150309190f06050403140f040f05060307050d0e10020c0c01021002160b130f0804150e060a0c030c080415020105060301022505010207061803030b0301060b03 75
    0x40320012459000030030044a241e075440b08040703440291002c1100b403041201205004404c40d082c03241e03090520360441403118500c1d86440b0038582014401001e0083c9a568010605042c420001080c40c2d84c0d907030746056030754078030349442d41200d600620640b01d11a9003000041303801e00e0044201c0b4007031281640e6003428008013801c281b00500d084090180325200fa03407100020340b45203001401040003440c000d0100355450a00290600000c03641c600c100d50320401c031120785100640001e0003080d401c035001d9002c03940c465440d652148400b090207400d0501d10300b00714007000105401001a0782012002d071380c040441000035101141c0031640240c0c404000c2c820304402c14803034100c8080703a40c024545510750341119140c2d80a2503025400400c92480c0e541c14640300c09809026090f00045d00350002c5203846041c126500002011aa90800b01003c8442e00018403c003501611001a0019020841800c0102403200550b51b010002c401027070a060100039189410306ca00b00403100c0f40c2101c00d02e143d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 710491654 1250 710490404 710490433
    0x11a0703050f0d0f0b09100e1503031608030103170c07030b0a0f090b07020106050a05092805090c0a060807021f060e0405060a1512020f0a03050a050606040606020c03 73
    0x7080b22000428006061116403144202402000099856a540001c40403010310600c818003100400007030f10100503030410003170321049844940d4000788004622421a06040019046100f95100c003088074019081c0d040a00c0040300c000c40c1202d100e4645605215585130300048240142d68580d04e550704440020004103860311502c0c0ea00440b40e00000628140a03e0038200319000c50105807001c2c17503000100304844d40c0922501c8090a801c0718060700f603d1804001400905000f080301c1c00407040762142c142c001c107034440e40100340c11b110101401540341c203c01995440c0400e640040c0300e18100580080ca050140c100c1c64000d9103540d001e8186240c404420014003440b410b03090685070350f203800008145103c04c800d14015031145000d003041d82003040c281d4054441c0c3d80c40141d10488c810030100203281452008602540d4150344c02e103007010400001070b0803940640e1000c2c1160050079003541c10050013094075889170f00101c5042007455164007040340e95000c07040d10250035900840e000040030307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 710492904 1250 710491654 710491657
    0x1015150f122310061101023c03010306020703030515130515030f0f01060902091804170a050706151406070213020f1e210406090503030c0c06011a070305 67
    0x80181c0d003030019a202c980d641c41d100b5550308031503510302602910024000c03160f00c6140365031044a078030001d6003020303240380d814030721400044159014500305840c411400506611182980040d80c5021a02ca69490400c40082e610021044002034900f03000104400c8096902082c0c120000c2d2085205a8003007007000c005007009045a00c1072191082d403006155020030048140300076030b030040d11040d104171101600303489890300b045c4007880c014443c15109440c2c510405540c8951091040b0700d5840d68100340c6240d07200c0c0c20101076001000281e51003030b150001c00800d00c0d03a10803c020028000320305554100340b03003580a20b03882180d030241d02e020300703241c24009009580e0009000c2c24026001f402810100d0b48001160020b0708804a88405040c4050310700484c00c0799040303009450714140c4104000030003000c900000b020b8500c1d501240c18080c8035401a903207558003a04a03540e034240b04a1001064120f00303c5401c0358032034a0004540144000760700c8110711160901141810300955040c0c40c117 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 710494154 1250 710492904 710492921
    0x603090b0115170c040e01080705030d051c230f090c040b040209040f06030c08010905060c0c100603050304050a0803040b030601031112010e040311030a08010501030e1015150f12 78
    0x8004007030011012011211000300d00a000c6503100c4d0f9907803850702000d540207102c16400511250040c9004104585000c00c10315005401460302550302c80ca10403440000702c45104415001d42c2c504007052580100818485407a1800004041515525084111610702d402c071806a0f15410010900340582019081178440c410010310160500426202042c01c44a20101c02240f89446820030000c1c030980d6400900a89090303402805010000c0c0c5480355a104080c20301210b03e40300103510300c80c02d4002d1010705c1c142c000c028400d103e172aa982c10516601c0e0402c1c010f0ba8031a000c960000162070000004450484130020382880c00c6136110341c0158028a580c801186540e002040401050860309602a02800601104244074109800c0003270000386035031b044c1c414960003000f4840001d508a401241110000d282c0415149c400e17820303171400e0000c0007280c07074210340c01c05c55441420100310100c0c1040e1052121020300101c5400d8007140d80300e020712100c1011440480e80c10240d00740b10b0f00030159 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 710495404 1250 710494154 710494157
    0x70207050f0d080304050303040c2310111e0c04061202040c0c0506131104050403020a0212031e0301150306180e010615050c1006060e0103051521070603090b0115 71
    0x204102d00e91101c00c200e60084801b200c190304000100700070001500c4200003d441154942c125000d40c1d104442c5284800d400100c0c410021180d40555552007105036010342d1540c1030903150390781c60404001e8442e450214080b0f60358060b25003a00310605082c400c590840d01040e644000481c0d42d9009e100007403420300302c50410040c043c481840800e13000c204007801194840d00340c440300c0840b81070205d111803800300e04500ca0341c1840180b1002c643c3c00900300082030f0301240c0c2440180340280c902031452040781c404450716000380c03170ba0130442c0354814013640c121030303440030030004400741003c049040b1081c80c0240079016a83c5801c0035860b80c0181d0110074a245000000a881368584020a00700f00030304e42064005040083c4d000b1700410300744150381042c042c0320001e11a0314200b03003014241c2e0708401d4045040555820000d02c0948906468036119103010f070015146a8030400004062203644070181070070301c0b40101c0011003600c03e1091001c01900805000f0543c0d00b0f09010461402c14051800b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 710496654 1250 710495404 710495419
    0x5010827011b0903030e040614131b0309031709190609020a2706050102060a020903070f0e040210050a020601030f02030102090405250c080910110a0308011d070207050f 74
    0x10041c280640b000d04810982c07602c0340c0851641c0380003458400c01c00380c01030156044c40c10410148410b000c60803c604400c032180d2050001b813070b07414001450062003565076400d000d014411015056440758502038002e56030200d24158840d46071b16203160503036111013a94480d0b111b01c0e401c100c2049084501c144100c0b03000c202c1d4655030300050031075241c81c0c1083c41081c01202410300d400365840c9400c0e0200714442e6080c413a031850900081d440c1c0800034001c4e40d03503540008201d081c5a4042c464180a492409480a416600c501803c03043c540119412800b0399042c0d10307036054441c0a04141c81c4000c03d5a401003c5903070840d66075010850740d80340220307050b640901103022250380724010740384541110031620381c000c81c0b402d22480c00c10510040200034000e4044030200400d85070021145185003d42c4d00c201424001701c01240e07001d000d901817003014090f1940344001c040d40b00c08501e04a4070440a500c24070041d614903545c13103180c16a520309c05a0b00c0b450042000f424100681c1036010350050503803 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 710497904 1250 710496654 710496671
    0x2c0403031d0708010f0615080408030a0b030a060f0c05070c03080a030603140a050709020403020321041a07060b10050d05040804170c1806090a050a0902060705160501082701 76
    0xc1c0b61002c0ea4110b005503035161224a4604400e5110f204002c0c00000f81140300854030b0b00b4003510030800640701400554000000803440c1e081c54000300071209020307080301c046110300e007010780c01482e0804051529600b00181003040502c0707101915000c0b500014070740d45951441c0e889840b594480300140080c192102000030100e8038110303400c0c088003200c030081c0c0000d55251034101c0c10b2070180e80080c002648103200600261b10300247c44c86407460030021407002c1c106001c0014030180142e500ca040c031008640c4200c09040b401c403019000140c450001404143c02400801c1a8603d48150000000d40b0500442198146581000c8d8010f07000703010140c0340c41d0319102040210036017804210003a502203914091141441650b00d064040385000551850800c00c00148401c1c031701625120740d103a1a00c0214081a00700c1d4040350780d81da401003030756907180442d1601030703200d03221052050300c03540316050001100d50003204014070900d50891070580c0c036403008940c07800000d054082441d903990b80e588070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 710499154 1250 710497904 710497961
    0x5042301050601022b0305040534270b190f03050f030a020616050c0a03030b18090d03180b0a0212011a040b09010512040c2c040303 58
    0x412402500150000c11075160040001e49022004202441614141148005084100820210040d0082c90049070b29291401e2080ca0100c15110401000c407071404128102d46180d80551007041b60340c4441201240e81e09106100c3c000080410743c1410741e40b840c42c000c014025407242c0407803075006002107401c0c180d10310148801d10164118070b40c50b41424009009010040084544000758a0015440d00280c41c00003912204090f052200092260211040060085003501d100255802c00c851030340c0040e06004010780040004a4003420001640155100354649100d03c5294400000c00300d900c0c10010440c020003100c041c0741c0340b050000c00e040f8000b841c1d202f8100d0003040041d0000da1200001c511060000806a0007210544809200141c0000e400416102150724040196480f010480c006840782d1085c140b4400c2c0841c0000100010440c281c501c0ba8180c0d41891280c0012213410800303081c07181c03070b1044101c1c2906010300005d80020300c00d400a03540001e410300960481070300d4101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 710500404 1250 710499154 710499203
    0xf020c030d0c0f0b04050c280501050f120f04120e010c1e0f050c09010e01080c01080403090b0c0a050705062d071a01030302011406061207020c0a03080c010c0e060d0504 74
    0x3c04072226006040c20070324501e000008e4008120b0700380f41180082c0e03002c49080010008510500341808804120b1200c10084c0c1c4040d50100268001c2c0803a0034a06528410103070141200c08644060240c2c3c1034151181c03145880082010040c1c41c2e40d45020820384a00700094007141d000c96000c0c040c00900c000080c0c08401d01e80754140310350010305503413001344d0802c40b101405070800c02c6000300150041040c1d01d4006581e400308034080c01e000300c00d6241c50508849604043d00f046901c1440000d04525040300040d43c0c10600b405a029940460349071802c000d03952042d01707680b08651090603442040c1c0c044203809550000484807410b4600b03003503542d424a101401e0140800003810354001042810b80a00501c005988802020209890541c0010310350b40907a44680101c1403168000031103082c02046404403024004104800041d074a180480042d40103e5100c001e55003000703103021101c0e020b9094040c0501c0c00901c041e007024401d0b102e103401080014410380b040e447c42c1c3c0000503076022109 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 710501654 1250 710500404 710500411
    0xb270a081002070c12080706050901180503190e030706030f0204090606050c060c071a06010c05191b03030921081c0c0806030309011103071a01060f020c030d0c0f0b 72
    0x1c00503880c2c80140c1030259100c0060392200c007506003084002000607844000300c07464035074082d1000a4940b00c10101c00d005040006030700d0b0603090b007078002c501403200c0000a4198500a805800800711044804036841d00c044d0400b41e4165000400500c400750090300712010f11102c1403001414030b0303922030750030b81a9409075102e070011070720000e40100e40507030070b0212650050a203520031b4602402c0d81c3d1074014002e185079034944250030450126605d61f1040708030014450b00b01089554868072101500020b41c80d0703890842e91414103c4011848140b031031401c00490f90507403150301501c0d16003400c01c1d0640c41c050b4603004203660340b1003000c000951400003510714130b05231645050300d01a400c2200c00803500388090038000c3c080c80004102180d42e00000700c603040c080a01c1d00300034102c0401441499802805001012081c044c0004440d110b41e50003400e0480701243e54810740d2152070041070307803685a00c10055400d9006084100c03241030088600700e00480c49100003080d03400306070f21400c03810035069 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 710502904 1250 710501654 710501683
    0x121080d0e10020316141306020c211c021c030b09090c0d150608011e050c040803031f1d06030c06040e0a0b191508010b270a08 56
    0x946400d550301004102800c0b007100000403c6156003401c441101e502e92041c11050308104030340000304c1d52001c5840c240c0b14032004001000090a03100d5070065202c0106616035401508040d030000300d20b1181c107001c0080340100318050f00e44c030800d40c5406506402038202c074a0a511034001c229401d10340018a1010040031aa80060307074080da601002100c2d000074024101650000c141061160f0380c02c01c0d0300c410716521041c0201c4106d040742030f09002d012180c0c002221946070101e2035488000002d0300d941d10b60300070401000780c9e5440c8611103420380200d0141e50a41d070b005100160900e0565460b4007102c5925a201c6040c4603650000322500e4243c2c00c21421007020181c0c18000242001c0080c00b070011401c03960305062038140541558899801800254615203d515568507911500940c000c0303140c200500030714043d2601c2020031030200301c9206034000345000c8000610510b80070161082907408090001200b41c00800d001030031401855400d612641c00706000525030410803500300000c020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 710504154 1250 710502904 710502911
    0x108060901050f0705160c1802041d0106050a260109090c05030102030114040506131b120b18071101050916080f0d080a0b130b040c0f080121080d 64
    0x884510390030b445024001c0580c414442c1c0c203001340d080e00181030310130041140444071180ea41900340260364080c02c1d84000c103411605001d0303000c03180d42c2e60001e0050350341c040c104036032000203059100d000f10000d2148800080040c4600a02c46200d8448450b0100100380080b040c0400f44000b102c079880c1c04c0c0c0c481000181e84104110402104110007001003000b100218119803611041007078060b540280b29100340e07900c3d030004250365681240300f15401e0058504110351000ca80700303030041da000a102c442c086040402440b055a0250086c60061540a88610b8007001100950060024098140424801400c001402c40700e400d105841c0f19000c0c5800a01c0581c014604014090500e034000c1100d980116110303100d1003c0006003650000418a40409117541d1000c00400034414401c080d5840340c094461721030030340f40541008642c220111410405401d9801040c0c0e05414910007078401700c1c0d803030001045080200b0340007200c84015502400030312220741c0e5404070a03a22011628022595 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 710505404 1250 710504154 710504161
    0x50f03280e010b0d020102061611070b0a0210230403020a020432010312110708030703050a03050a0b031b010e031507090b1309020d24060e030c0901050402031806010806 74
    0x7424015203400400c240c505884105403600000c3d00c44400600c50710958843c0351819001a105003005070b091503442050380c49183c0c03104074102455100d0345a64005214071510444c180c207161083c850402000d480c0c04c15040c003941ea141e28080402803040d015402200e00300ea01607101d50140b15400b4680401c40701600c1c0c4200c44c0c1c0d8542e132440b00e000501c064560300c01400000d01c00c0000f03040303001071390900b02c524038101e0107446d1074030070f17160001d103481e02011504404064006000c1c2488031450b440030310059940760b05540489112240040d40356104048081d203104c80c0c02c98807150041c040c5005607200388507001107890402806450480c005c40381c0c00700040c859002c440305001d41900c0c020703940380680b500c5824000320071070300440c3c0303509174001410340d40c0c8202c40d40300c40c100034210445ca04c540c3e4203012100800e00b070144110400b040c02840328149500d0085149403002c3d0000300401096420441400000d4100910065804605041c921500b0000700981402003455100030003580c038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 710506654 1250 710505404 710505431
    0x10061a22080a23030a020c0d020a0519060314071e020102250606050306091b0d0609120206160f050706110408030307030b010305071e090f0f1703030601050f0328 71
    0x80803c240a6080c0c0040c81310381d40c0d96501140c041081e40d411190341c490f03041e031400092241c100540c0060703441940d064515454440c0a00441c00719041c45c0c8041040200003001144c2c4074800300d4810001501003020306040003c090035030450384a6a00c0010708100022412800d0f2205c0040603171000c0040035100820405180076180103000140e01034091800c0040e0441d41c1c036041ca64506142034807500c40082141c4800410f02000c60300004240b10341d250324104852604250680180103001e29030001f1000c416110300c810012149545602400b1100c0404840c5a00071090455085485054144003140034001500140c40c152001c1d5039030307003031103c0c0c041e0466001d002500c0c141414a010001c0541e0000761910820745441d00211980074052000c13116501250003140b0000300010002c500016080c00c000300352520010182513205040b10410f07a28001203074428000f94080000348411307001100a503400a220b0815a21904403004a2020403031702d40c01d2a60030903035103000041805 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 710507904 1250 710506654 710506703
    0x524220902040801180b01050603130b0709090509210f0f0d050610170705070f0605010f06020d08090309010f1b110a0504180b180a0510061a22080a 65
    0x2a170000c640d24642c01216030f40c649040a0504c1510302c0391101000003405103003842c0c14041d8160f40155464000c1c50815000b400c03012541c0202d03ca07840c60b050024900d5403000504001100d00c041c2c0610740002000c150800943c80b0060005a2000602c144012401d04002130300d1410300e000408602807030100240400c0010b9103503507400300040651403803030400b65441095000714991401c0c40d901d051509000c90707020071901c0c1c018000d030301c0c1c60000190002000301020070780d4070319402d4410740d8007049800c80311808169a0000c054004000345016507000e9651003190614500b06803003074404000300c1140c203000d880e0b410707101c10910b00b1021700c40d8038010080380042c100c00c0b5070130803107001590000713030b094a0080c100030006408a004240781c403c5080c0e4100a050b89a803c4030003022140c98003170f80350180760001d0948541000c00100703584da0014042240c5c00c2c100000c0e2030a0488140050901809000b081008204094004909408181f001c19083c9001d68669840d840205440c01d860 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 710509154 1250 710507904 710507921
    0x90607020d05090609180a0507020c01020c031018150c26040b042303070210110d0503041704062f0a030c0c08010203130c0524220902040801 62
    0x11500041403032001d00340c110b0281c0302086000d461107912410400007060280712090004020100064200f010f44140d41d00300e00e214644940c02c1c2c441c1c1410b298010b9a940701400040340d0305411043c0c190507108003540c092103280e61000204200031086407944445070b00050303020011142c449509042040c3c0043c082c0e009480480810303510b010b640c102d6000c5007000a0402014154080d02007002c2c40201c848002519401c2c560803040d2000146a85940f6400444101e0003103040d40341501105000f41000c00c08188a01c02601c0440c4055004542d1640000c00c1120740750f444103842000d44541c0009000070b0f01d404e07201e180318050b042c0740100514108120b1040100c0741c010940354078031b0300441c41e0503015526080a1414118a10340481c0c010001e40100c000303036101104221945041c0c4008615a40c042c3c0d65004a15855409004181c90380441340c05041008980c1203400311480b000030706000b4041c0c04900f1446082c07111100c401350f020743c4a07400868002c42c0034000c1e18020302c9036452 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 710510404 1250 710509154 710509157
    0x131b06080906060a0b03060a03050d030f050f0f0f040305071a0609060915040e010b09070903020111030c0a08030402041803050408070f050d0f030c0f0605040b090d170601090509040b090607 83
    0x41c0b03460084001040c00340140a041010003002c00442c0745915100106405035078040709071044001da0390301c010010402c800c0461070450420f40402d21010030212a81c1c0a4000900f5460072a547d04107010401e00e4050021410400100f000401040d40c031901407101050442c1e003485503081420800c108100c2c09425907100e1301100c01440140c8079040d42210b21104291004a11b0302c0c0640d0500d0700400f585141c6a42081400080118a82d4440c0c407040c2540e01c00d80318456000744011b4526542d0040c200122040c3e440080c841001c40c08903005598020303c010000b083d00e0500b40030010003021405070480210b00302284c02e0084613000c0c800c003000b51244454060804c0d1610700000c1130644425006040c1081662400080c907105440005803c0e40081c80a8490980ea24041004110413a400d0364038645242c00703d0741000001c20f2020840c034582e520440006040f0343c21045950028003c28103104640d440003603d6120418060300c030fa4080d100c8400640f8008201a0030310030000c10034070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 710511654 1250 710510404 710510413
    0x7060219030209012307020901090507031805060a090822170a0f020f010309081201090c4b020a0b0109060e1f090908070512030c070b131b060809 64
    0x90b461760300035400c03091003c415404036000000704001403001e2094a10294110004c01c0c0040f420807400c0d04441e0003030701142d504010340c0142a90061900e064500000d26035008540400c0a01031980c210300c0d070081c010a0020f190821800f014000765104d42d00001020300206030403c05030482c0030f24220411401d00103040c1540c65603a5001d0755500d0960000d1050911a0111036980d110398000e0320410740c08140342c1d60703641d04001046000b60091060001182c2810707140c0044038403030321010750403030110b40002401e000d0303015007200042c40c00301d070100d803901040500c0000c03a0900f0900390407000c469005013007540603905000d450a41e0503000b101d042c03030030442e04000d40c0d0840c00d85150702580ca40c000d2000d030f00260141001011240e0303c81b18006040c84040c00c20310106100030b000e403d2048040f29040c140300c070320141b9913010403690703100bd44005011240204014059156200004200b10b40c40210555150101c410044440014284e480d078428007003a030300030312002e821500c40303170092 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 710512904 1250 710511654 710511667
    0x9021003020301180504081306021506060712030519060906060e190501180e0103080306100827070801140609070e090c210109050a06060c0512031b070602190302 71
    0x40d201074200d0a10341c2c0d1304940d100c0000b42400f0014099507401e07004400d404048079503510340250340d80903460301e20403441705030b40c0410841e01e0500111024164800e2103e000308408200c160003c007801401740080500d488244407600402d481000e004c0d20845200080860401c031008007041c11400000d80541001c00084851950418913002210001d03e00081c1c003416401c841403061142d41c2c0000d030940c0101001004010500025601c07a06081d50907920a1618003011107013000f044d82e21214a40d0303149000e45c40d003904d40c80c00420701c8102c50b04846070740b581d46080074211000202c500160b109103105015040c43e080e840c8540124151a1611102c0300c4070300069008803020b064440c1c00c0300000340c4091603000007081902403124401882c1c0e10356075105080000350100b00e800d220320520303020001c01c03000d002d052480100c0b500b1000418251014150b641003940c00901251701c0342034241881c65119a20320014980f6a22903140943c956010005c100800c042400c0d8203001e060052001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 710514154 1250 710512904 710512919
    0xc0705010e0603010b0a05040b0301080a060b0402090109062303250f0207051c051f1d0a14150406200702012c0d0302011d060c2d04030609021003020301 67
    0x50f01d043d0b4043c0c0000999403d1800c2050742c5c2d80c030940d030141000c0b000200000440d00004030744410a41e0052500380304030710250080104078800e21010b00e000c50b0000d01c090100031306c04c01402121004885c01c001d8129040070140d10180c0048640040c0c40e6921400080020403c24014004180360b00f41041080d81502e0041c0d00d980c4c05000300d5014000c0341d0b554645688140c1c199001058100094a0388502c3c505000c0d03690a03080f201c1102038a051941105079840e000d0050848480c0c040050920395207144c0da0460481c13140c10158900744103480e0440d568100742892940100d01ca010005a51151b0071000d94443c003c8060400c40c2d0801404800050b0f6080854007030300c4640110001c0c1404015000700e201c080a42c8419a001010203480c1410107070158171120082545003510880b0460042209648250851304240c0c0c0040500c045140e1b00010201d815a2410a00d141c403c0e00518001511854005034015200241c035845e900c020750038082000260104945015480d560515a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 710515404 1250 710514154 710514157
    0x1801060305070b40150c02090604020c0d0f030c031b03180615032d0219030b040c0311010212090613032901120302061522020c0705010e06 61
    0x40494600c0c000802410113002d2100d0a000e200011080d503840d60308100390150710b1030031305a030007001c0d040380c07880031074640c281554450a82006a40e00400b800c0c65900b44070326050701800307a5170003a40a0200d642c039500305101c182038080c1a0790310020840494070700201614030300422007050500d800f000c088854000d040300207410302c044c280401c010701c01c045600080d0a41d1b00020382854500f43c112495410382c80381e03081c110b81c091800c030030446080d402c2c401c0d80c4005a200c0f41480300303200c2c0d986100508001d400b01c82d060714034414110106560b501c54020900303046804031741c00041d61f42e05104201c802c00003110a60028401401d00d0020108604081d12420725928803524011a00d4032443c0000308142016540c081900790406010070203030500010f034106414003082c4080008604155142ca99907102a09540145010b4807a500300c1070760fa81c40074002c43c3c0c0022020041071004980511501301b040c4501e0001030f03603800041c07002030a260258204a040100d07901071034035207075a090b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 710516654 1250 710515404 710515409
    0x7060f081021052506180b03060d050325060c020f0d080c04180903030e15041205070f11270115051905030907050406050d060c120204080105180106030507 68
    0xa070101211181d810f20a15008110031541000e2601089032100e842c40b030100d08040b95441e44400c2c1c2c0c081d84400d58400306c03140c0c0340111129001c0038000107a003490144040c0b514540100242c901d0241d0300342d070039031a401441001c20300203a8100035103c01c00c0550f12070700021100a00c054190304001c992019120905c3d11849810052038002003a000c1c00b100c400c44000380090300d107207400501c61060000240030803140030f9000c01d1400e20750b40102038000c640c0710b908242d003d0048560350742d82c0e0b940c3c03492050000095420428148181000505404510740050b0f0043c40611210400101004801e105100c100b400244400da400301c1039031f101c4041e00d0b0540d03005485444c110070003450211220b000b200b1900c0d07001e0f03c4810344038284542090040d801019203009540256480c1c0d0f0a202c01d94001e0710945030041d007513284240210300d803907100e00c00b660100e00d00114142640d034518402c4e42c02c15003000803141d5607101071196103040103622064080c00c0c8002401003501d551a0755803141d4051 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 710517904 1250 710516654 710516699
    0xc120a0504082728080105060904061e050c22121515121e0305040501050315040f151202100c0c0503010f1410033207060f0810 56
    0x904002c14a25401d461000f42c0440a4540c05540b10548085034112a08544400301140100381c04161908180201440b5070b0001e05200c0260700c665030385000403c0a640e4a0f0322006036440c00f9841d41c50fa80c041c4034040d0100000954450140f002d0020045c00818401300b008414500100f000528000280040d80d030004042070244e040004414040c041000203a6a0030354856004200e6103019070410825070301420b40c881c0400000b004407150300d801c0f41400380102c0c100340010001c40d84610700447c0d01c500540180b8081850a0300810305684c4000503611783c990712061540414200030102e41d00500c81550f5402490316641c0203c2c81c2844911201d404000c26424820148503140e00c0d544010180900204100c11315191480f004000311103003650b440d4080320201d0080040c10a2040651313801c409010102e104d00c10070402d10b40c540b02d0580c0c1c0d00030860001994441001d02540000b80b0701d03034555202131036400f2401000c9400040c00f845600402e03401c14084000b031040640c1410414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 710519154 1250 710517904 710517937
    0xf0102060a0f11040608180705030613060b03060411030c01140904050717041110022b0c1703100e13020d1106270d05191a0c120a050408 60
    0x1d0040744015101c60104039071100f400050003d452a48801510311800502060741c945500d4200550388a2180d8441c030359043d03018001107484851041d405000241c03044200242000ca20701c082414808219030035280c01403100c1a100300c5080500c80e420032400240390031051582c0c20003041c440ae000e068841030040b543c8400250030980141c265040803081200c80600603d0b141c5803516100303280309250303405031010048168003240005400c0a24603140c26a1000e10350340070340100d2540004800c0340c000c0055016114000c50701021818420f282d0003003009981c0c0c035000c06104110f030903503440300c0307082280e07041001280a040f1038402c1f146541200c00858a0078281400103c16800071001c0354420000501111110f036546a8a4065030880c580303c000305d003031002081220300a201000d400d075000216101078048615400450300ca01c2000f42c40c82c250701003001070780e086c0000c5034480860500051084800c0e403003061120340c481d401490501061a01c3c0c2d40d42c20560141c0c0c2d490140c0c1150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 710520404 1250 710519154 710519171
    0x9090903030209061c11041401030504022b1101022a010203090a140103050a0c020a141006030c18180803060a032916020a0b09030415110c0f0102060a 66
    0x7180e01100c480100c014082510303041c99444008004c1c000030300c0314000c00d1070300b2002034441907507605842c2103a2210350b10840a9a5407801580640001403080b644101c051001d120303003461103400422045900b035508540c017205494651210f40d80c41d5a0503040d0750103503440642a0750040c840038012070429038180401c940c2040140e1a6002c1d108010b1782c410302e04100851088460a1a215500000d036814003483e141da840000840348403100020040e00b2140a4102003915038040001d0756800314100c80415451002c010200c8000b500700321414a02d1040410482e010500b03022002ca10a481c00c00610181c0042c04400c40c45480c00188240008030018100713650320a035010045400c8014078807014440c0e20a255000d6682c803403488200245c00205058280c0c030030940414598607001081005503e03241d4081458000b420072926120402000c900c08a030940c0d15001c0311f500c3d031030b1100c182e10b1042d40e0906060031542c290b8052105000300d20300580c0d0004442c2e80020754000c0c006070194 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 710521654 1250 710520404 710520407
    0x201051b01020f0c100507050d0e0a0f050c01021e2805120c071409071b050a05011d010c14030903090904080702010e06040f03240504151b09090903 65
    0x400c12a1aa411544045203d091001c1d401c0d0040a94010110070b4a0f041607100c42060101d0b0703400d9618000146c002d01420782001d43c142c0c45005400390700021104101c0059845641d5659410710849041d0040c401d04952940c04001c0c00744100103d4412119860200000c03d0f40c421103103161688803105200f08902084031414031607004c541202c240d5080c400700c0c0428808952110303104101074401c0801c00500c17043c0c142803a0303000720340c014006901da03143e0a2080381c58075040c42001c201032424540600c0001c00401920b200305110b54004601540303501180310742980042c0519503642d0401c005100d04591251203516a4480d03488141e450b9103804036400d03d18050807040b035800110030401d020134481d080c0007030840710307100341da03121083c00100080c01880e008030300c100024018002400c0c40003580702811001c4081e86060002080942401000c084e240700352000d441000350b0b50f00240442c0710600480581142c8960320700003071441c20b00020050034180c41400c0409a07110350007001c15 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 710522904 1250 710521654 710521687
    0x702030306060313080c0a1101090b070b0604140907050103110a0206040b180304060314100e0a09032102031b0301060230040b040609050a0303050a030b03151303120b0a03020105 78
    0x303d40005019440b01040f150300c5a0b0ba50310607c090300c100c51407040c002c25035842115030702e0035038050050301c0c1d0074035170150707100e0031116405841e20b030303006440d0a0080040e9010800084c400c14090000b056041e00e401c0014045420150008119001c1004a011515000244241c000d607001d020301441d80c0e82c5898403350155812018082c9010028001074483c2c3e040e009215420040e0703c1c10a080d45071020303010302606507445030450304944c001c0040c1e00d042e0681d10003c2854040e042028a06440c414120200031b9a802c030382c40005d50101c2804040c0c131600c0ea041044c1007020040d545154144030010350340744240b40c03990381da40205031807c4001e01c80300f1460920600f03155110b16212034a528502d90243c0082c0980f40c005505500001000d18082d4035110440c1d0b05525504d29064040d00c0072009054003a03422a050320488041c054810a503103101882142281c0c001d0b00c43e0b03071032441c008003820507983c0c50101c1e5070b013400d0000c030385503541e03a802401700c0341d0908000740d80d25100149030190 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 710524154 1250 710522904 710522941
    0x150603210306051906020615030a080d090609030309060f050411210f150705071109090f0f010c1202310905040807062d0b060f07082107020303060603 66
    0x1080d402481a502e060459510a07905c494094513200c0d0358014060110450781c049142e80b5600a070080750100c0d0000008143c6010139440200e20b051244d00c0f16000d582c00038101b2030000350b60300954400e100292003900c03000315000c031080c8071600305512522030f440d690701c00c1644101d00c640c2c00d120b00704041040c2c8124900310f8000b1f0712492058045225121003c1d8444681c0d00300107080020000d82c4294115800d0700d0780701030303042d0880d80d000060010080004080251900c60b495000c9815a0308001500485180342c00205031284000c1008103d880094071100640340144821800000606030200e82c606103080310500c1c80d0b00c84c10402c0c1740c80059621a26440385060148401c2c45401c200a01d400d501501040c014806101704a1044070320b405100760069890400c9102c103510a130f000343c1105074000305070b6804c0c9242500e90002c15030000313030b00700e41c55000000c503121007600805d50400390581d5906c0c17418083c6007680020b5201e11004084e18460300001000030100311080d40d11460 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 710525404 1250 710524154 710524159
    0x1311120321070801150816200615031f0b0f090f070206060126091c091418010303030f1107060f1a03071a12070c15060321030605 57
    0xd05580a154407401c101e07042e15680c0000304101d00100300003040c82c0d02414255140d42c0c900d038a40c0d85551002c1400406503142d41c00b00031a449030345084002032403030955509010405010341d8284148140c07034060281038543d01a400603041d00c0c102120b0300b5200e9004a44034003021544c001c40784001040b000c043c1d049107a202c01d04809020381300380ca80c20303410300ca4001c41e0215203a9840341401912081e503030a985010a440714100d02d24a4609031007150340220954003190442e404d0f0b440040040c0d4075090f6100d002519080d001c00401c080301c0c45100038150240c0d107500c0c1c0301c144a84400d00084050001809040d212030807000d9281c5650b005682e00b4100d0703040303252201610b02c3c2820103400280124400c01e42041c51881d030100302850490000fa800400414000d440d0010b1034811151107210f03802145400e1051040d500c540d41f504038412031080e0f0b6284031a424a14201c0e6840b070361a02003200d51442c08400784005100854080ba00507840f0b1618103032000700d400210042d04142c0c00035078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 710526654 1250 710525404 710525437
    0x7110108010f0521070f080a052e020a020a0525151e02120703030204050414061c1b0623040602100b220e01060504020c060a020a0c05190b13111203 65
    0x503205000301d91034840c01d204900341c1341d000034250b0000c031200903981cad80300c02054144103001012205580c010612110640143c0303c120480d510346d02e00301071104944c0464100c0d48000070b5140004062004083c0030380c250415450310110320002d059000356201340e000e01e070350801401d0005000f0001121200c040c907100071798908a900d00140a50090700c9020700590408022240c01c40c4201c6c04030f48911000381402022080b883c9900010000741c04090390b0f1400d450105030b54160410440c05c01070b007910303228080408066102c21540340400c0c1a1040640c1081c8000c1c4805980401c0c90683d0b100344800204004c4031110000c0c801e0101c822141c2c0b08400c802010502d100e0440d00107040c0340308090700800089a585041c002a4401c5010041c1160002c0001440e5124a540548600301c100e152107417141c3c42c1607840501e0200922410b80072010751034202c1003040b0403001c1c5550b01c24800a01e040c1400059900c0340170744045400098811030f4000460140a6400c03c280c402d208481784650 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 710527904 1250 710526654 710526659
    0x9042003070f031104111603050306060412060605090916060509040f020c012a0504090f06080d05030a060f031101030c050d15050f0609061602130207110108010f0521070f 75
    0x11000c00c0100083d5020f582022900350850807480240c0d15010047c2a51180505490307804481e10f40c0014141d42d8004030611010400d942c0020840d00624400c1000148080c100700c20091000d07802071411f40346900c919013010038001d0402d800c504841040c10001c2d281d0310014005006008030110314031280d4404902140c200701c05420045640100e0511403512054001002c000e4640441c44000810b800704420010081243c0c05180c40f03142858000422035110f03903030b190800c8100f00218001a40200912a40035500d200f802d008011045640317000e03a295540e00504170403c60f00c2503061554070109040c90600910440c0c0040f40c10100030015008080d506110740c01540c0550750080b6440d0100d1000342c20500f0403108660030040c84a030074208462440d00d80050144422a006202003001c44038040b1180054151648149032030817441d00f80d240018903229050344243e6104011407800c120079120741201a8130000c007203610031034201078201d0580c0b0b801000c0c3e12034141043c401c00700 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 710529154 1250 710527904 710527913
    0x3020703050d1b0f02011a01140c011b090905060a09021c05091e070e0103140111070b060f0108160513050909010914060105060441030c09042003070f03 67
    0xc0700c3c9100702e80c9402401383c00c2e400c4100d0880705c5030302030b6802102c407507a80701c0003942c00b03a0040020780710311503c0d8500d0611002c070380c00c1c2134400c901e50074458814400f580c18002500305d140c420161210603000c0015140500000714480998440c8060311903000980680d140c2e03400f1031344d070740702032036000d084c00181001005035960340090303d00742111031200034505070740030408100740c0100c4c1e010b004040e071240d007581c45421002d45020206c98080d0b695441c1e400705402d0348030150454074050b00c0030440c0c074a401410b00c040e00c040000b101c0c1c1000444020040c044142d80c20208005041c0d1512036143c92030309a607610340001d250005540840742d40d0030011003040541010008a11a660340c050004090b031007190360310030a0289950084060106000c600018405820469040300c012440d9020041040300c05e507014001019500c0160502440641000c1003011008901600c419243d490305440b10a20920641c1111001000c000300b5030a065804001e1a0082c0918a0520481c0c9035030380382 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 710530404 1250 710529154 710529191
    0x6210d50090d050309100513030308060303120703051005182a030a050a0b090103050d0c0602040509070f1d060702210d020d0f0905180a020d0f0902040f060b0a03020703050d 76
    0x111b01c640a00c828400100d84548141c81c0240c0740c401161007070909603035054034170510080000703405d032009205900058020440302400f40420b602c0000303003420b0882200483c0782054101c4e40c051441e08040c0017864840418076076011003080b558071404403801142e0a2101d80c80c2040d0811904007206100814905a20190203114205000c2041110f18070a104141d0000d02c8060180d80200190031503d900a510950542c1d1040b0401441c040c0c403100010034100c4140c4003480000c0070b459002e01801d03000f050604c940c24560351208103406000001070841d1040040080c01b940b4100c00e003400c2250303400c0e0142003c0720b06a06070790200101c804002c1d0796220500d0b41800040d100b10305403580f00d0046206006643c0301900c022100c45039080c000d2040303007000d4001c00046608103c0381d4180300e0248220110460110b0011400c500107004000030780360450900154249400400c10150621204481c00c101e0307103080140c0c4a16640c00c09483c00c0c09110f10a458680c00d10000700d02540001c04d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 710531654 1250 710530404 710530417
    0x70804080c03120f061c030f030b1c0b07021c0507020411040e15011d040504050a05190302010b0a060512090a1b0305190b06210d50090d0503 62
    0x21945104d640c07070008000600b000102c584952a020035802c401103840f906544007080c40c1400c0c0403480000100200d00b10300c01001c0f120b00c2c0301443c90f000e0402c024061001581005183c401024600c3c01c1d400702c0035610100300d20300310034800b00182e240d045407203a0b00f001e06111801c0158948607542c0d100b40052030380b0110362480f2202ca52178519401da600820340d00f0014040302e4504480030350707102c05100003444060400d991034800d6500307460007d101002666103800c00c0c000c49074040b07001454060b080da200c90b860319109408864040c0035a41c0d000c6d058885100a40f80c14550a440300c000c15410b280401c0c40c0604200400400c6064030700c00b800c982d0040b20703c940e044a481612491454414001002006101c00b50090119081c0c1c40d103910001a41c1c1200c5180300548046881c08600c1c00241140e40c10200b40b40c100423901c0d44007842d04044000216880f01c03803050005060f40703120b40040b0b00d40c0c03040000128200441181521040e40c00000003d020610107242c1c90419035580d8100c171 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 710532904 1250 710531654 710531671
    0x60324111209120f0301092403030e010909050103050a02040504080d02030c070209070c02010e060d1d0a060b06071203110903101b0c050c040902180709080c0109060503070804080c0312 81
    0x250a82400035090ba048a59201001c1c4c41c032400c690a040030b4501030f0600c0000c00a60b1039251480401e003040351640c00c0d0040d03200e42c440704079042c0942d0002d0b02c1243d1640c002915a1f18041c010408038801041c5603600c035504a400044580e11441c00800d1307070040300001040d052001c810040c01c0300c00c1c8402001c9150003121800140d03540e02d08125401c11030410000d00003100c18031280c0c4142031000142012102c103080100c0d068241d6a42400041c0320244403920b01d40c8602c1c07100c001d02001e0f200b03829000d64182d40f01887c00e480394595191409407400d6200416940740c10138440351800380c040d0f44e20050000c0075140140c544264034009007211784502403000805a01e64001c0d18003c0da464050140c0c48070251200428142c100401480b0001d01071343c2040c0809611200c03568122911b510030826521201002410240300915210903c012681880302d040703c00e20005400c5010307690710504c146814901e981d101d140921350342c05140408926840701041580585c03041a20321445602075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 710534154 1250 710532904 710532913
    0x80c0906070c0609081e210922060801020a05032a0a05031503010c2712150f02092805040e0c040f0605011b03112d01060324111209 58
    0x6c40b1032489200e84200c04001540d801100004204480d50700c1c1c000034100394a83c09403c255000010502103a285500046802505071251180070010311805000d410440002c508104007820090035502c00501544c01c49007255000020520843e84122151504c00c1341c9151545006440541a0f8000340e846004003440c1c6007992585003814419401e9026aa03960801c480080c0c2401155001c2896060000d00500050125480d00070244240301d6500c103d1040c4100a440c010100c02c44021905c8000658010803400460b030340c0d90700b0000010103841c04101c3d190000170030a50440e030000c0d4000358019042c000f034114020070100f808030a03180700b80c07402d1008840410301d1b601280c01034018a80840d21842c1c2101a4070b625a150444041c071905140f4203c0704518840d03841c186d0000c60070040580400714074140003140d401700300d80541200000b40a140d0960307070340000d059500c40c0410303281d109106000c404800f0681001c000c0d4410008240c0ea80d9040321850210103104551040b2140304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 710535404 1250 710534154 710534173
    0x902030f0609030a0c1e0f0b1321022103100b040803390102030601091d282f070c05090c09030f01050609060a06080c0906070c060908 59
    0x101007440c6119a0440e0051490a0250300040e100d030001000151818402084c02e00c507101d0540b25130010301d501a248040c3d940c1c10034600801e80c441c00501000c0b099081c607031801e0018050045013090b0850662101000d584810401c80c641000e41071000300d81919201405141c0c00140002c50241c40310a00e003200309500d800385100e083c8501d10458805901c1007110b246040c140c80380400f4200303260000c10041d078a0f000150000a07225a840e40c0a07a540041402025a0050300a02c010305a40d213040c09500d900e54010154601c0044c0080c0c551990408410000140508003c110f0841d51a0400c04034005e185000400308042107010080746000610040c002074005c181c40b4825440000d00c0c0805081070f0600c101082c02a010700001402030001e4070040c0e4040c8550b880380c524040001916180210400460030400b80102e8064011204184241a8000505544041000e0140740d98800d2407005c14804d1007015000380c44d140150348042106640300340c4c500200c400c2c1d0421981c054030b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 710536654 1250 710535404 710535433
    0x90b0610020a0209070311030f190501082a121605010201021207030b0d15050a051008100b0a050a0602031803010612020d050709050a090c090605060703050d0e01060306090203 77
    0x4460180d60016910a8540d034005181041602c0c1d4800791a15000c030f00061440ca100c08550015500c80360368580e050200040040303040b407440300344180381c2021320143d45003604c5580c40c1c802c0300f08800403c1108410110b502400540c800c1d284050203410710038400020604e498807100342c031000d4800d084501500203042d40c81402522000700b4000000f210607100c5034010380050060001c10780d0010781d842c56600101c1c40040004030001045071004c81c1500d4400b900c40d048400061a515810390b0428090044120009080348014045200010104810000100041402d0380929407140180101060469000c000b40000c01c0410f10001c0c1c4c0040c050040500382c840f14085c00c80201d503510810b101500d000d4100d101c0442c0244141c030402a110b031880b000350f0300200d618506807600d07034103030804101030049003600030314841c601048990306010000f11a4030981744003038100f02c4080f8200354070038002d6011040207a0725000030400c0da41d59241440c080c0c0082c64040c0d2080c040d04500c0b00403107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 710537904 1250 710536654 710536669
    0x80304080d030516200f0a0b04060507020a20040204090603141603050c060a2d0e030a0c0e0c04090507082d0c0a03020904110903060106140412060e0a06090b06 70
    0x71010760303c5e201d0301041c1000a01c0c0d11410b107242c165a9a00c9828901e041341c15052107090707482406030704000e040d8a45402d000d41510710280081c81103500400803140402c0c003503032000c5607100101c1c1c1c03c6000703541203c0001d006405a6000350f0316842c580b4000008019100030344180c001d005009032100d812240d403082101107110f20000d40982c009200d258224a06000141010703a0a0701b840342e4982082100411740302101620421040320030140c20030320982000c011492544110001c04d000c20440d624003040c0c24440c8210041c04010f036002c20030800c28842618060003034400d0800452411031002070014000f80c401003048480d0341c5001c22000c002010407001210036412134196516000e207d400264006180311081550a00c01c161a950701d502503601d800710480b85454444140004060a00300c041e40400103000003240c0004a510f4241d058508031004212a81002007144c140a0041c0c44a96801e18039409010b818a00f00b01d0070f41c0c0315800403400f4058450650b40c0c6c950510110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 710539154 1250 710537904 710537941
    0x9091f060e070516080a090b070c090f1104090e070e070315061e080408040801020f0903250e04020103061802030a0606080105011218020619020f0d05070602030907080304080d0305 79
    0x139182403d902ca0f010841c5c1600402d80100349280100f4102c0d903549610405401201088a803050b00c41d0080000c20407e00500404c0c03003125004002c2e11103040102e03030a0340318a2298117020794442c40d05c04e214080520840c801070411000c515910f1421510080040c00303881c960907056060a00080fa2152113021140c4898a14104e2542d071484413a03020703070b085135005000321800c0d9010400468030300c03804e0018121201e9060003e6451341e40084c10503080600410a00100d4419100c80e80048100002404100c0d002d40001e290145c0f55800124080d01c0303640c00c25401200c415151011100e00c81d4010b610503800340e002007210036104c0300c0444820000b84516400034180031940760109015602c518541921400c090140115030fa0100d40c0a40044c0c1210594010315151500c2e0b8076010311091407225031a5010382034441c40900054a81d006800c009040c0560100c0020720b103140c1041100003400c501000c803602d80390340e405d09581d0340c904290190b000a0829000c110022041c8207049171 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 710540404 1250 710539154 710539177
    0xd0906081003150902150705060a0510030b13230f010504030e04020f0d0c02030a0909050423010b03060114040c0e060d0c12020a031a0306060f09091f060e0705 70
    0x22842c60740d01c48a1100180c0e03288542c0b520703612180031005980d400d440c0000403029004843c0c80f1343c00c60030114100307035004150355a60380c107000400000c3c0c820005640f059030781c0014190102d0703c0e40d60040182c00c021440043c142070145041401c0c420210701c14510440080003200d01000900c900c00d800e0b00c0c002d03100200880d0881e540c0800d80c2c17416802500410000408450a0040d00c0310254103646034010182c015804c001012070700aa4070100390805803110410510050521343d44e201d4070380310b000e4184010036a014000250070707282900071030803800005003110b504e540c60b5076594484d880341525003441246081c581c4162117015240504c0e294200812070385c14a01d1861500c4080d250342000d179010030001307003018800724030706201901828009550009904082030715803240d6998402405120b5400b43c1c081001030fa640800709480200e05803180406c0e41c843c107440030b1409211b20b20340000c605007146850390301c0e0200c0d8400012140b0383c1c0d0034192a900c07120b07070036503032407184100c8900e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 710541654 1250 710540404 710540431
    0xc051c030e0112140709060c15020a1205150102060901060501090e0408040f0603020d0c0504030b06040b04150603020304020906010f02060c032710050a02160b060f040203090d090608 80
    0x8011a00503203101040703040c181040c2510140203540401122010010300019130400f0b0140700741181c1c800d1204000d00f6050030725411000d80d03915500b00c8605610f1600748019000241026514811507a440d4055201c41c000d005034100f03200c40092141c0c41e030034203a0041c0700703060000c0c003a0841401134404807001a1130711141d585c05c2000d0341000c030400034420f403001c3c40d00b013000080c07175100e2000d003900400b51070b5801610f45203c020f0040544a2460410040103c140400d2000c0b41283c5541501704c0e01c2100e001808411140101d8043c0c20f0302c41c51694201d000d88030000d40c0c1c80d0950003d52103240f0031204211541e40f40e40054880e42917042243c40103038081d01c0020b18080a400c019604510711886c000008850101640300703503409030140e080b590b0031176a0507202c0e520b00e60250b243c12500c5004254289860395804c05516404140003421003c9518081502600d41140959182d680608150f65038901a010142e9840b9840818400aa1401800a00c4502c1520a140240f02040440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 710542904 1250 710541654 710541709
    0x38010e0a0315090203030c1510151b0602040f03031223040c150915030b131e020d0b09090706050a030209030f06070807031104030203190312020c0601030c05 69
    0x101c00102d030402d00340031040da8450745030300542e40070005006074144480c01400c8100a8012000403201c01601e40303845160000c905003c0303d02d1401108682800c5407170061010341240b01405c0340001d00d80b6001c1d200350700c005404240120941081001c0d0f90190321070070000281c4100d02801c48141c3c130500000c1182c0c011a40b8210010030003402d030072501841010008030b40700c1c40c01c80300c1ea92082d18464041750780b0034001c01c4040440c040f103221106050070204442040c100c0440c5040d03960042c4000c0d1159100381001105507080c6a4048d80351840b4021074407141e0708904100100300c600e00c0c2900c278804031800078400f1a00001d10006440c0b03e07985075414881b224609030003039002562140d525015007400c1c2020b00800700400d5110b98910303920f040700c3c0e0908000103030480c0c3c10440b070300c101c030710301008144003503100019007100c210803820a100c1c03e40f00c0341c2000c8500301c0340310048501150002a040104038000100c09040e40d0140b1400d840256440c010409082d1118031000320601100d20b02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 710544154 1250 710542904 710542913
    0x50604030f0f030909020409020432060307021f020c0c030a0f0b0406020405030a1506171c030209030604150b0f011d031e1e03090a150338010e0a03 65
    0xb210242032180c1000106503032940a01001e87c0c0150304000e007090b60114003080152035652451001d45c0d4120419908003d4000300c40c0140000e0001c0c00b40182000004070b90b1913442000f81410201c0000b1500c015070701c078120700b40d010794082030822179180700d003950720b20310f074a0080b83c12031142c1d60241590050090783d03903e108064500410540f2126424803000825880c20704c40008002c0c46409031110100d030f0b10302c0300803ca42854000c030b0743d0390200740c6134400c004000183c131203000c0c004145a2599403025104c200c01a00c1103240c150741500400d01803000700403243e22910100801400e00303020300f1001501b800a200c3c4840c80c920300184075500062280340010720f07800303d003c0d00501560004803244103920110030605100722040e034000341400c185800c5001d03030071700c041c00104003551900da89040090b50024840c00340c0400d20440c45801c00a4600942c070002c02d550909510b0400809071282500c4402c440340081006580701c0c108148441d07204400c0302c40c1d000320003400104400e095840c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 710545404 1250 710544154 710544173
    0xa03150e1e091f150902131a040f0e0711120a050c0709051017060601050304021219062403120f0c0b0411010f0206090c010c0302151f050604030f 64
    0x40340d0700c41c0920f0082c08441d5524620661240c1211140401c0c0c5680d0707070700c00b101016001e5100107400351041c045580d60500c00070341c10044412446000e140650243c2c1821a9881a540708001d284010500040d81c204004601071144525841d810303100e68651000030744441c514032400d8140c0400f0008038000e5400360018000d50f04820f8112801a5103460f4840111082560b140e0650104981c04004404a01c109144483c20f2030303000d0081400d00300006041b600002d0b20003840341e0a06e008181c0301860400c034007a8a03541800450401110900b40750000f080c0c41b01c8002c0c00d42c078102007814003192008000d5400c4035840840c0002a10708980115203031845403ca43c0c0411a04141180c003180d034240d440d038040d0b80034500c0301c0703407078005400050844040045580c081d500003000b088819440071400740210102801d01c2020f444061070101c0c2010340c00b070310640000310b00400707000d10b00c003014510001c582505001258419180d004000e01c0340614030005165184400010000446620 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 710546654 1250 710545404 710545411
    0x906011701020c0d050d0e0109080904270305120106180e0709050d06060f0f12060504020f03060702010c11031204060f150b030f1b2b020a03150e1e 65
    0x100050811071500d0b145802c1c09a0115204c0c000b8401041d0400c00700f80358800e47c0070320388181c0c4c001c21030b900e25651103800ca8011020f03010700c115a104580300a8160b140f11121400d400d0140c0c80203241c840b440d020b80710790020102000104004c40000c6030003401940040102d07000c14802e100300381d24000150ba529500105000b003048009540091561078004140145612070071011611500b40603010300e91a0855014842d84400c100c020485804200907020320b0039082400031696a40f2800407400f8143d01c407000300e8062284000b00300c001581175016090308034095507078200682030f081c0388659a0084200500c0d03034070310707900c0414005012a03111000e03600340360b04046441045030a001c1da00e03008603440100b080500208010020001000442c1d00010300709901c080408158020351039801410071440040e00b0780484009440c0c002c900807561220010b4003507598a03043c150040142040c0d401c07010708440c05030700100d0b280491f941e055108031203829881110840e14200c00d0701814004d07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 710547904 1250 710546654 710546699
    0xf030c12010f0c02031c06060503070509011b1103010c020f030a0e040e150906060105030114092a0d0b0906030c101206030309150e03030d09060e06091c08090601 71
    0x4440e054202102c50040c94070010564010b50707107943d2544065007040410019010007185861414024241c2110079250020010304c2c4c10b5448040000068405041c00c0c0141012601003010003001c00442c01022000e10500390000d0210001c0c018050b85da480d8003180d401c0d4540c005201c0c10b60300724440c819203004100c00400101d001641c401440b401d0442450010300080e00c064100501d0034010445290420420f107811441e541c5010160800045038074006486000c02d10081080760241c111740d68205041240310310a500891800009a94040c000045e1b0450514401e843c40346400c00409204200c050050010600c4850400c0010442a02580c1c2400300d007019242e9404000c0c8583c2d809580f0a4880400c90340c107100554074a00001004103040180c0c407420500151004070944200c88825803003c142121145050303c090701030007080c1c071001d1040300300304000c0070000148410846240d18035170b13100c101141c004980894044801e000d050307124000403c0310001303c0084007010a0300d0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 710549154 1250 710547904 710547911
    0x5040605071a01060c030207081606030c0215090336120f0d181e03030806030307140607030b091006082212090605270d1713050f030c1201 61
    0x3202e10140e2105000e0b005040002c5461000308209901003140c60080d0020340300074612880d50350300095916295000d800100f42d101c01c09500c07054000c00000c5600c070f80c81f001c43d02d002d181030030b103803596a04084055450009402100c00341c05a03601341c5080c0c111108502e240b50300110006202c044041105e40c028240f1920803040d503d66814012050000b49956a00104003101e01c1034511510041c0c00001345090103942c02c0b0080c0800340540c8049942c9400c1030401d66230340c400000d0450017015400307040440c0e241040c003240640414001c1c480e0035291010041c011682052141c1d80350101c601040300a1440b00900074203004804c482d0340819a0f441c0c115821440250480b0141c00402e0120383c40c83d0008800e1075600d40021040c0043d00e01450010306280091013036541e0300d4441c040040254030b00c2c00001900e6100c103822040700c1c0e50080b004420308001315219480e244c0c030200700399800543c42680402c062a06500c0e51040d210003c00501540d1088400c0204640701d00d80c0303800643d0360303 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 710550404 1250 710549154 710549183
    0x90f010507080f040f09180f0302010e0d031401140307060c02060d111209060606071b0806190b01021c1b020901090b01080906040f03080a0915020901020c0a060504060507 75
    0x800d40010b2403980c5140c091581c8452a25039460182c50507070b000501031b6400c1c68014442d0440484030440065009514030015030b4107810113a004140c0c01c0c18810050040100002c912501a00403814003580035100d003500303a076104a695041c4d2484017070568103400059041144ca817203001d01405040c0001d002518001184c00700340203c400d0b100380d0318010304021429840c1128800c0c2265403000c46039000e0482c031300d031401c00104603100d0f07028014004480b9102e0710304a0080c4104460161015508444660a000207849d1075039101e180d0b900382803410459035800342d500c089080c0c00724152900c6201d9501d81d0450007030b10340b09001029219544c50307403182c072030160352001030060007804408000607804404000060642500400e800195440700302444000f544020b03a140d2003a0309403801a030b4030384074241c8800c05410b0f428400740c0707600f84e6400c402802014940c010030300c0b03100903001c075160306030b4034401d0010321495485580c010440074081003001901a4008089161283c8100c418008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 710551654 1250 710550404 710550413
    0x7021002070303061d0709091508030c0106210209010357050603040f1a07030b0f01260a060b03151c080306040f0e06041209090b0105090f010507 64
    0x3084074805400284e202d01c010041000748a009483c10b4003540c020041c545084d40011306100810b128051240c0c1d41c8a004031041801c0b0084203000d014040c0a0700e944c0c04c4071207420303400b030304a602601040302c040b0354032440f040007000e00c0788018913130160640c1d0700c0e82c0c0f840e141c0089101d080c5201c291b0010444051080e02d4900403a01214070108401e8014500702407800354030180302c5290034462401d50000b090280d507660205595000b9440400414000064901208601c0040300d65a08000945090080c43c60f01500000b6400c074050750005600d840700307401100c91290840a0441082141c101030385031502001045a1240c1e544c0b01c045150f0380d84d1100c000f402e40c42201c5c10718065080702e10004103450700c0300c0b02c4028031191140c8140c6001951311403110394407000c0c0145205076a60b00c010324410b50300e60064140ca810303d40642c0c46616003802c020083c0913031075100c20f00049400a010803110300b1440b440035041c1d01a515581841e00d40400d00201c2040030203034606012080c059140043c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 710552904 1250 710551654 710551657
    0x602090d0203032b06080705120c1e01030b0f0d0f03181d01050301020702060a080a0b0d030e090a0203011a0918070906030b0a1503050a060f060324031a07021002 71
    0x101226840b80c180c0380182a8900007041e0b507141281d400900b04070b0f00700a9400e00143d01f0301658002c4031410301c1240f211001c80c1c40e124040151503000020119586070440240c24000d1511000b80c9044c00244805810403075001100d610042d8015043c0c0741960108000c140d101d14024842e003401d400141c4003180c180c2030002141e00c0240c01c403c0140b60351400300707140c007845801000194000c4d82012810760000f4118005c000ca8401007000c01d80c001822a0103503000030741442000b401d4003120f642e840c1401403026a02d4400103006070f0408020540101c0c0d14401c4034102c61042d84650481e1218620344242c42d846807013895171140c10b05810140320800d0340303449402140951903408085103012005800e40f510701035101d104020441042000494191040b00440c14528000449a03101c00e041e80043c03020fa000074120310b2011401203410368040c0c0c8050b50505280348002001071908401409082260000070703c2503034001d0f00c00c07607030031450207902c2c0c3c01c2030050040d11184a5803c0101040703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 710554154 1250 710552904 710552917
    0xe1002130503010605370506041202010e1815040b030118030f030e0d03051e04050d0306081b010804050a141c03141501112401060503130602090d020303 67
    0x5105004002a107400d210303070300080105480720302006c1042034521075030810b500320042c0b100c602c0960829024207449910006088020055071b10b81c1c1e100c5400100010580c08100e010400315034210340c09107040c4495020030400100000b9240da60960304071340380c0483c0c8080b16003041e01d0302d80040c0281d60a01441080101003404044420503604008242944840407081414540f4012100003000460f08000740701c440d0a01180907103543d03208051380c0450007007010703031069101c00f400100b01010803070903c00302c41c0d0f44e02031080a8a400305640c13100182030300841c07008090110180694002c04501d5405030148060b00d0705a905a180c1c078038001004118052140c010140146820340c60008140c2c8800311341c50b0401504001c801c098000c1100170344400710146120510001d103030720541204d50ba03a1303156401d4039400c402c14000303d01c1040b0b1104000405521003400030411511641c01c0c0d074825424034018003025140c5480c4c1c00c00a5202010554005507a4124140940c030104000c000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 710555404 1250 710554154 710554177
    0x110a020a0909110d03020615060c030a03062301080a0b0f060706021e0c1506041b180b12150307030803010806042d15020c0d120b040606080a0e1002 65
    0x490142e54902049402150034030f052042d004d416242012940c0040d50640c00b4040201040240c0062800078000c1d009108034000e540c440020070200141d4560010011100202c1c00901c0e10b500f410748400310a1a50f006641c001404580000d02d8500d00e034101c0401e410010300401b0070b652a90000c61f400c1d03804804180d880640020b00081c1ea0a03001e0303880b50101d00311010841c2003440ca20409902c0d07c943c1c0d20102241804400428015074595005d810811000c091281854192000180441201560141e05010780ca0b0700000da41510f0801c0712004c1c2c15060714403400340c2e20182000c05846880c071203903030140305684001c400910a1001540a00940c0c0001c01c0146003e00d0000c02044c04810b2450306990040c14803c50ba0700542c1c45e0112556020340780d0310f5130004040b030034802070142c4141c100310b5105401c0940c240c01d4010742801d0369103602c8801840500d14050500041c1c075118480d81d0001240e68001a10300141a840540300c01211016a00b2101201001c00240e130080c04c2c105c80c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 710556654 1250 710555404 710555411
    0xf030a05182706060f03040221070f05240f0c031e03040b090c030709090f02100c051006150f020307061a030d090308070b13050f011407030b03070303110a020a09 71
    0x1d0b10305410310420742d00000444055151003100c000e074106501028000038007845e1f009441240d2715680701c0c40c21540c01d114400b241c09165890408a048024600c1454001c49044501e0094a280e4030000300314085050401c070702d042c4c48101000300650007c00909031a0005200c124071002c89070480100d405008204e107910f80c241806c100c01c0b400806080c4008a41c4044649600ca843c08280242100c54143d4000746501150405079109492010001d40c00304002c800e040d40300780c00c0021082014003540c1200d05000b120f61040c1c0880300c050103042d451500110424001c2e0f031090040d4407981c082881034a0410f86107907a03140c107840700b00b0380f0340c18a6410000300e070b00c10741801c000c00b40d4416042e1820182145c65601c1c0e815180c81544000380c00300003c440000c1c110703079041c40000031a55009040740c0351103241c85140381c002c0001d000001000743c114008908c01c1486401340c0300c00d188000b800f030b0114518540c3c040da00c410880320360b64898000c4a404c00b003d6030340c02c03061000909940714080b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 710557904 1250 710556654 710556709
    0xe06190306291012020d0203040b090d020a032f0609060612010c2a020a18060f0e0a1d010905030c06010509040816051203071707020f030a0518 63
    0x1c4491510b00303400000941c0c101c0700d244441d0703140c04022001880c0741c2015800740f8003100d03004000c0c2c40b8170209205804d00010a001c10414465401b520600700d55007521712003032044008036220304010402400080c01da8298443d140340344849910841c544151049070304031401031081c1011011180741405030440010001c05007003070301d040b002e00015000200240d0b151464007801803801c6d100b4840703010440184500f98400d8115032054440e8005181918150b5035045494224201c40f5982890504141c00041c0d0021001401d100f0f0f150746d1102c3d00720640d6103a1009008250346143d4400c0713080040e440b00002c0e9420311139402c0c9680604081c42d9190104c44055183c6101a8080e90040c81842d00300808540314800751640000e074103200005140290604900e03050702d840031101c1c0e1090010511003a1a04412003000704245003038103440c25a90640b059032a0410800a0b00300394000f003095003580e40c0705030b0040c51401140d00030100141c005d0000304000140b40c01c2821030505a5468a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 710559154 1250 710557904 710557931
    0xc040e010c2709020c03070c0b03040c0503030f030103020108060a03061d06011a03040807062909070806130213031b18020333130b27010e06190306 65
    0x210160324a080c48a074802c480350340784964640080c458014500da000c203c00700207410a10417a00c0440e01722450020864441c1a00c0550b43c1c0181c608840071000014005120309012080e10031058203002c40700d041d0703860b640040d5541100108902d40c00341da1740d140071000440ca8441e4040d4103903441c644003440c90301c118165107400810b0b006405184404400340410b0041035080ba54083c1c0d001c0c80310781d12883c10345080ca001d4811000024144421a544c000050a1182c42401c440e18200d035460410b894580e4151040d000c1901e07415007210610074a9011940d03d41c00400f0140035040c403000d0340c1517076a15000410300041240414410038180308024585090403040700941400808500c0c50500e02e10550010b410b1305203030004181002c6181554511080c0c0080c20000050300c0900d00703030b51301c1c00310700020104040014070503405545092a200508505622494000340542d000703079003810044074106000a18060307120300380544654144141d103450400a40c4910720224440d00700303103117 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 710560404 1250 710559154 710559167
    0x9090b01091a0f0f0c060411041401030201140d02031512120a033c060b070b060d05120f040e06060f0711010e10120c0903080415020c040e010c 63
    0x44581082001d420601082007020140742200014011007543c1d81ca182c00105541e000d41c4200b16084030000c182c8101024010032000c0c80b5600c00c1c0f51402c1c4440c80c10003004125404000e031303400c6160071034006000650289085c400605890300900d818508480c4440341640e00c2204c1c00080c2c492024200c581500307000a05128402500d0040d2000c09903110104c06180a00c0050707400705a03c440c4007007030200400c42640034510721040035a142c0f6030084580341785900901040c0c0c64a5251a10004079080e8031426110404d80c0300c00c641318603803940303010400040e014000554440c004d0303440609203400140f000304000da2103504d880e0344862601000f014035240040850740561005c00512201c5610782048a0240703034090800780714445031000488005080700c40c0f40c2c4d005520800d4094240f0b4012500369108240e518062100180030201228507000c0c0748401010841e051005100740d000c24200710042c24003920456843c200d00f0400901940d651200c07105103070755550001c0c0310081e4401f0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 710561654 1250 710560404 710560421
    0xa031805060c190614070e01091710020d06050405040b15010f0f0f0207170312060301090c050d051011030f0f0709090b030c1005040f0603060312120e0d0909 69
    0x455030750400302c15204071615104040280304200c40b222400c0c00c01c01c144ca6114000d040c07034025914080b4500311401400704070b0513150150114910307010008568009144500071058010b025208020f0300305080310203500005020908540c95010205503500d4038440c56100782d01591703040c05581048030202843c4a02200010304009000f81d451005076000700040c170245003a4600045d1402c0600000ca00300880c07504040300154200d01080b88490000025002c15565502d0140380c98842e00e0401d801c035492a40d00030f156003500c0904210b40d180070094200001c2c0694280c07401542251502e4041b100085100c0480c4600403060040280a016100380d0004035101c15507203a081010010304860030500c580303596580c441c0711090480c2c0342400b001ca48404081c1500041d07000801c0050b2060300940100c03841403403a10800200540f081c011882160780008000c40e20500300242160303003054180100d07009585074082404c40c0d40b400c01c003450b030003003d9136901a402c078102407100c000d88141070b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 710562904 1250 710561654 710561659
    0x1014060a0f0807140f090a020d180b0c0310151205091504080906160b070f0f0804030f051c06051c02060409020702010e12071d07020c0d05010e0a031805 67
    0x903078040c050050006200b0003a0740140c66200c3e02e0519100019846803440300d2900d0704800d14800340003c8050701d801800030450900720502154172890071500151090f44009887c00c04020080b4105081301402980c00000b0310520b8441507440704201e1218050322501c090001d03004502031380c03040881c1e20589811100c0800039004001c05842d90004440c0081c0c4045e144030000190040d00780c0d181d500b200c440b205050f0740d003c4034a0450a0090340b1920448041d00030460a10315201c0c01441550008802c0d1102c0e11202625215500e046400c07600c031546032001c5c480100404480300e010300e294980d8280e41031802050590034401403040007581c1d055241c00107d07105402200690b128400c3c1c1c0c085d141c90500058035007181c3d00040f00d100509010480c1c02c943c00303001d00110200701284407000e5070012001c43c0781064401e400200d10380340803251000142c01c0041c0740741c501e241140c0003028807030140c0004900d00e03c002d00c2c1981466200b4600720041103030041e01e05003c018003142c50b00204000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 710564154 1250 710562904 710562929
    0x50610030b1e04030e06041509080d030b090a05060a0506120403020d14090d05030f03010f09050108030a090623030a1a0d0209011a0d050109050906250509031014060a 73
    0x10082e1030400541e015100a050003619070241c1c010703460f548213480003404241103840341c41441280150100909000d40480d5005860301007001c01d00074024088100b0001d00b820b4101e507100c1003490700800014148581c08040b24100041d56500c40e4041c10820b0068144145642440c3c9406441c2c061105140414807a000d4007503508400c0f00030568107890070a81d00d03a11000480d1078030500314030031030511506010380480007159244184030f0b00802d40b00b81c003108002a907224415075550740211940710000030103500c02401a2072080002955119401c8400c441d1441c0d0b150000c4641c0d0001c554040c00190740f4120560b50322100000c0040c00807059030b9110801ca0360f84c0100310205014060075043c2c8141d0165100d0100e030110840701448a0001c2c200550750311100d44070041d1170141e0701c101c0d561007100041100007558030f42441100b5600d840010b0281c0d1020810b4035140c0200c1d125075414004c2190b200c0c10540940203100140c91881001111b038a000300802400d05035079004200741000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 710565404 1250 710564154 710564191
    0x60703060b03010b0a020c06040306020a020d09030c140d05010f0b0f0109150311071b0509070305060f040506030c06040807030210082a1b070e13030203040306090f050610030b 77
    0x1a1900302d07410768000000c080ea9800e003c210903442d007400c8140c13607500402e000034004144076a540c007410f00000d548c0e0a841c92101e110130119400022404040c1800901034020840c4900c40607000582c0d00028080200c0d140040e1503071821204004038400f000ea4031521440c0240c0b0f051014212184000d003004611242400c0c89211101c054000751410301d0f031380348128924800042c0540310704551140902480c1100c40300c0e6074801e00082d100310790044242e90701043c8030070300a005491150700301806080746900d004c41000090715010300066014001c5a1003510b039034461000500150a08000500a0900d18418010011440b0084804000000041c041d816101203145400103034150a004002c44513102810bc640c07282d558900c0e00907004140000c0c00c1d04010800400b00c42718440c0000c080d030307601d50301c0031201c481c1c0e2800240160070820007400002d1503540b006900c0c0d401400c1da600e03024560307918070f441d0060940d20f10300b109003080b004204001c3d10700001d541c80717405140e000c11a4030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 710566654 1250 710565404 710565419
    0xb040308070209060d0807140618030d0b061b0102040e0c13030b100905040b0f01060302040612051b030405030301210f110118090e1005072c0a0306020a0206070306 72
    0x1680c04002d2183c0c0b01c9a01140c01507849258000450760450f610903603421452501d51b041c3e8030042c0d010034540c042e02000030700c0400003010301c450300b60a41001d1440d09007441c001500800010f003000e42d101905112015941403074500b09156204190001070f81c4508000d100c07204a6401420102100020410785201e42102030300041100c3e4807000f01c0c81945c450b0800c20300344a142e90403828015140004000074044001107050003040382018128080e40c07100b40071010303841140251404601c000300500d107101015440241d020060700c4858601c81065084a02070364000d4030140d402c0c4e44048010301018084085690a0a00055980740c00d884156140b40e1600300000c4080d11094548100e008940d0040085114200858101e200c40d103458403a59802810080e03c414140e21079150143c0f5514004d100719400f6080300e407211180f14030005080450000e81080d09041043c03404c070b6068050703c0d82f500e4140a903200b00005600c0740c100034002031620800030420300406003090f404020340c6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 710567904 1250 710566654 710566657
    0x10b0301091a070912030c020f1906050d061701060e070306180e1507020607020c0321210408031819110f030a080403030201111216030b04140a05010b040308 69
    0x514030004002c0e450791080c0003510800c04c0b5512403d1a0700785c05040d1410140c1c000718810242d4401c4400520b449690401e101c0032058501d07492a02c403d11032420700c403444c0200007500c61ba814040020800d280c56161868464003a0b004420700340c0e454240a100c602154911154003454502c8e0030810030b854000c1e440401c0044100301950103580341d0f00c0c40808002070000f1061b541c01c042e04600281051030000b5a10300e0100ca030700340180200c0b1002c0c1c145281c0410074070f400300070801c1c1c8643c2c5400741c0140c0c1d00303556202d407800110b40310721480c03010300c00c441080c0c54922460140c5070164032481e02075030340c0000c0c0c00ca0070b002d41880c3d04004650140104002070302e0103916003108184180009074408512550700c2c0c4920180d051081600e0842008407000c020029030b4829802403146540c807404484242c0224000146400d40d1000040c0d045034582c800001030942c0791902080304040c9801040483e09622441008617035080100003541c4c03524011a4010001062024501b0345140c4031550329 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 710569154 1250 710567904 710567933
    0xb160e0f040b0918010608012c0f060705090316061209083601020d170a1b0f09060206070509060309010b060c150601090f03020402070c180e010b030109 67
    0x151103110844562030321268081c06182c40d0103000840c1c2800e11650800e41407920021549040d03080000100300b034007040c001e190007108240622a04110520440c10b1401201d206401c0144540e8802d0501c8001c104152405804140c5a56a40d14004002d0504000c014010325480c0c06800c14100b2100d9848031a07090340517000e40740000d503c3c10510b07084205115086400143c808110500c02c281006042401851191480c030310303203018001c0006a80340d002210b080004141d82c60a0075000c41540c4881c2540000c14030800030300403040403107110030808511892000121803113420900a5041085100500141d0001342100e162001c80188184200c005140c002c060100c0072800d041402d400420700c0c100c0c000e12040d01c0340b400140b103907610017039882040700000111000c644954002c2c40e58a0655900c0149404000d040d0b80030700c8003950098504542103a58200c00040341302e62150840711409100301e0208030202c600001c00d003076030009651588240d00d4001100006520681c50002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 710570404 1250 710569154 710569159
    0x31504081e0a03140a09170307020c031e190b0115020c120619050402030c010c020613030309060f170105012604032109020906040e01091505040b160e 66
    0x540780d014040c0020488851080000d030722401103a80300d0301d1601500300c0c400031a1051910690f030b0752282e92420946501d0700010303190410140c10010001d510300000c40d440600c0d070044a505c000d20300302083c68440b80c02c5600c0c0c13409022000c03008005509000c900b8845030250007400d0205e50f00d8a840511a8062080d01c44506810b0070040c2d001d0b000340010050041d00407d4541006c2444401715120942105d01c40c44226040e45a1500d00c0c1c040c2c880c0d280501d070080d00070305883da490360040d5440c40c1c0018040c0da00c05414007910340010940c1c0400c101441c8030f03030f680745803c500d000c10242338a64150b40c5070040c012a102403d64043c0c06800f00e6045030305c2460b001d4400141d036860f5404102039403403609682501c0100700418590403000e41000740e0810345103101c0c10200400d604d0304990b00048029803101d00000407a0491600d90011b402c1c000c4003800000ba04183d03550347c44240d405818500014a881d1004c000030300c00440c80132940500e0b40c1000c000f8400780484010b00c40c500e04400b051 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 710571654 1250 710570404 710570407
    0x6470304020a0b122206021c05010501021209190e09070e060604120b0601090f12052b0c020a05031f06080c1005030a0b04240b040b0706090602120f010f0503150408 72
    0x117078000300c0404506041e030002421590751407801c2c4140828900c5031440100c0d14240000080c4552002880c0c2217409144407880741070450000c10000c82e9100080107141e440d01442020411032101806a409850400000c029903480c08180d00040c2c8801040c41c0c1c800c901c01d2004202c1402c101c040807100680c4000700c070b40d8541d960001644c011000c3e4020045209820402040d4400c42103040c9910600400466024030602003d010714071110a90501040e03660440b0a11003500402103004050310050102d801c05417100003080c50600f40c0d0f07a000c060000d002d0710501d90004148120405401c1c01009402e403a604800410501039415040c44100704c400000600ca40107035500001042d00000d01c284119480c0300c1c070005401408005401840104840000d041d0b82c0c101c0440d8210381040b40020305000b242c0d00c50100504078a001503c510f9020011070749031100c4800c0032481032950f050b52542c1075040407020781214020360410350090f40400800c8806a4030381d002c2d00da100e035008160a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 710572904 1250 710571654 710571691
    0xd0209090a05060108070e010905160e031002030702010605130204080c131416180503280203030409020310090209060d0905010902191806470304020a0b12 68
    0x40745411032081c80a001409000000310b0700341c00119201c011100701e491180e17100d98a0301c08220858100340e8821800e884c030188145645406001e038102c0703d003c01000c0d0780c5880c6064560030182e0340222084c00c0141d540304c8003804a403603d5158202c00001d030030300441c1454180381c04156100740c0d4003451881144044401003a0070b105801181e0544070b90050514107081004414110a0180400d800412000516090101c8080c81e07250100c8000400401780850b448040385000c1650072070840b003901c000c46000000d81c50810050004140d140d00043c0e42c2e1420212090b00e050854006440f0306004000c02d4005544600c183c3c3d40c4d802094000048071011460168010588044025088002d09040c001000c05400c40030b0b0459041c3d6248a0040c41c0010300e020840e0384a00800d040000d070148060309010820951716000c00030701c002000c2440c10200003070000702c0c01c500715020a007000405c2208508060810318014224200018100340349a816000a944024002000b6058a4401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 710574154 1250 710572904 710572921
    0x30504020a0807060306140f1e15120106090807120602090a081f0b1512040c080f010b010221071b180906150501080109050907030c0b0a021b0d0209 65
    0x81e8030081500004075810250384510103005814944540404000740c1c5941070780b42c1c1400028284400300c028103074800410300303d01c0940904d010b0b140c2c4035085400ca00b011b0102030f104100900414052030420310503036250503030040c4005000d402c80c12a541003a2000c0100701000c482c46001e20340c1c01a80940ca8482c02c0c00801c041e0091680500600e125100071800030f00064406005d05100621090140310444428415800c21f144071103003540c401000f0026030b40c0a08d0311002c2c0c10074030072042084801d513a86941854450680d180203002c1e50b449441000c650b07010000c4241c1a80c40002403030003940152100d441d54058141e024004d00070048400203c1c1c10543d888001034450200c90000500c400d8504500070407103200c04a1f0054a0035070913036502c020368044082260b00c16511049960f0130505a5001f5280142c2500341c80d00c01c050300400043d0040038210043d000d0705003401d846880c00800240350400b080b882d03c00c106400404a25240c481103121080740e034040e1210581070300c0d00c000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 710575404 1250 710574154 710574169
    0x6080d0c061b0e090a09230a06052e0f0605160c1508100506090d050a0615090e030903030306120c15120a0501060203040902090105040b030f060114030601020a0b2203030507020d1e03050402 83
    0x2340204500e141004000810084181c12001c02c10842c1c1c0101101200140a40c07100d0045d014500c481c940b201d0b01005500d1140780103103965501c10315625608202540c400da921a59604545035003407856511001c0545e0051803a540b041c5517030200b081c2e2618080c049078070351249408982c020000c69002d1002c0c80810419010300b903030320000800c507022760030050003040d80d054011b200b111810b015a0b00e04024001056403d00340d0014090751031529540c04020340c5680b030901c16407041c010b40c600f118903592030104c821030310301c064a005a030b00c0344890306081801c0c070000c01c032805881c40d05006004a907400810b540a6501c52034006a45000d081c00584e601d014036400f110703041c980002008260440e131403a050003000f003030300c0d00e400e04105c0c040c04da41e150004884503070040e07104ca10841c0c00b0030010b20807207810500c076829041c03802441c00b90f007001c48a0004019004031740c83d941800390702d560401c411031801605181c460305107441c0701c082c40c00202010074094109070b290404241590303960399 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 710576654 1250 710575404 710575423
    0x10302121c11070e0103020f040518010204030302061005041e0e032a0d05030f04151b030504140a0b0a0c030204170105061306080d0c061b0e090a0923 66
    0x2807030894100c11100007010200424041d0782d1500400c04009040c4200011550680790b0042a29440588250a0000030302c0010201903a4030480803088200341020b100800285001c1d6003c1c011624000c28646c2c035502c40b640c0541d00507481c140b00c0c03038024148a4407000020803511400b00c0c000805c1c82c0e000745140181c4c52907685111401c8400300102d0310004104c41e120003000151100d080e03d103e82600c9034042113400c0700075500c44200103000950584000c121a80e420306001400440021900d0b001000180c040c401003503480c01440280074240c51030142880f17404005207500ca446656080260300301a0802c4040d585842c407180b2228080d805480281503038280d00c40b18142c001c0030301030180005032182c502500d403da000d464036a86c64041c150554501d04010110031055600880f142c3c6810b120560380e041d942e0003083d0000b8030700d0307040107403101d420703519648462001c82c108100b47c4405003520030b40c203140c12031080000b081c2e2407e2040314039a41d002103a000000d0320802e0704107000c08 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 710577904 1250 710576654 710576683
    0x140909040308060f0a170f0f070314070902040e04060b1e040b0d080a05041a030103080a05070c0504060902040f15020d2d05310909020627010210020403030801030212 73
    0xc1e0f170003244c1d24000003a00d02c6900342400850300e0303481c105100d058503841c1201031010340f504519800c2c008500307183c04c60861444440125840540c0c1d0384400012600650061002050140c052006201c0e40b03010b50341d551b02c0200e544601c0500c0302502c000a00720001070850146807540001142540c0782c5882410490308080040c0d9110600c3c0b100410710362183c000c5412940c1083c2202503c050b60b035060320b06803988804000e21380680748100780c0d640d4002201c200c604491040c0042101e807034078003a1200502c08013401580303036402c002c291407a5000682084101c8985c5410030140740e603001078075002c14601420404250560031040e13001c5159180103070241d1140341c2e5141c0c4249903000d0010003800c10228034104248100800e10308001e41c20b07040180c06d0195a02041c003c0b40310a91002600f44d1006001c05d20b0007440e4002c10f80034072140c141440101021060f00911560140499000751503002011031805042d0b6078060250324040c00042d001c0c22540403041a80d020800001c176091400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 710579154 1250 710577904 710577919
    0x1120f091e051b060703210e0d0908030f0405040e0f0d0203030717130b07050d0e0a0b1e0a051909110a081f020304030c020604090c140909040308060f 66
    0x1280c2401845001e203908807124481d00c06031051003144125240c01e100c00051889103024580e840c202c89448a910015100906c011100050315001c1d10841d0078120090000c4c1044407401c40300a40780c0b0003076500880c1550006c100010708640800304442c02d42307508540001c0c05038000714a0b42d140203003a40079402d25104103480031490a0700040030b103124220b10303070351681d1001e200c100010300d05a080e1004003902c541d411200b000111041030ba02d074450140e00d0910709080074440240292140545a00c2d02c50300140c0d041d17002c0c042e1000742e07654000e0703900810f4102d034007581400f1003548200800d4280038541d540040b5010401a68032800c180080d00070600041126092034510003120440d224480d035900c1e180028559404a07005041e41c81000070048182e010f02010b20280d80000e10450411400307600005c0143d8814020b0310141211003c002014a80160007604800306020550405041400401e10f81da942e8016654841c0e810314101a0580701c1c0000325000070340c00e00c007a5030b00c43c0b80b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 710580404 1250 710579154 710579183
    0x100806070e061b0307020d0b1b0901021f110d02070c050102070807030f06020922050601032715020a080106030e0102070c12020a05060a0c0b0c0c0726150402010f03050601120f09 78
    0x2051000340f8009c0c24100441c0c041041035028002851069039001e6001d6001082c4902c64400407420041d100401104045102c2610090000b015840701e000c0024840d030104540c01805201420100600801e0000b4060f550500aa00303507a0815448010041c0c001d1195510030440503030182d44090350f0240c0b29050300d14401c000c1491402200500600711450240080d1141d03100b800350103100c00303031251940a0520300d010980240407500d0301c1556109504507120311b080c400c0340300400004280359903000700c550503c0300040c191584482d50ce00a80e00502604011511900e511002c461400c0d8142c40300e100329102080700c004050380043d81c4900d012401024082d00100f010a44500c100300000d903680e20042081024040c14501c0d18059024060a00c1070141c224503505440e051405d80c8001c1d002c84601d410303d0710110420744e41046520038207000455801450708001000390b42020321603480d240307000070f28014142c0381d013811a540b40e4840c83d88107400350b40400c10031604849118004032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 710581654 1250 710580404 710580413
    0x50f0c03190306050f03060c43050706020607140d0f060b0d061d011203051902150105040504030f05130f030c0f0e070503131505100806070e061b0307020d 68
    0x1148644c0740034241540300c1c0c1e805480c003c43c0c10b91084136017840039824441070304214a040d0880c001c0f44050300490705914845075002140c00700d04d58a441d442c980e01950b03186844d6040002aa101e04155441f00c1c5c20300021640081aa240107952510084e444d40ca032030200001031315094010400844c500200420b085880100416040e001342d2030a01c0320b1035645120300381a8401841c095082c615000040c410b10b0134207115404218000d2800b642070014140301a0b103001040c00020300907a102c0b9007100c00c0d011007c0040750041030110750030019881c1c50f44001e81400303c81c100c1a0100f21001400001942500921001400345c1c1c4207014038040e281c0c43c003100741040500401c81440c1da01c0f040042d1242c0c00381c800901c01d40e260741c0c480741235803502e080303141400718408e00c200c07500004803401010942007442110f20030219900c0c10f41000f4544205182009005007d290411084411103c01d070f031192800c1b22690303003420b0109003032460340012250540c0150b000007980480d42d41c805c0e00500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 710582904 1250 710581654 710581661
    0x17070f0f030c141b060a0c1b061e02030a0315120b061203041208090d060c03020d050901052a210702010c17010905040c03060f1401080607050f0c031903 67
    0xa4071450f4008207041d101001c07503559406a080e0b8042d40c0820305240a10340c10010007400c4284680d0510861520442d036800c2c1d1030050704041c42c0c0708050521400c0201e41d5100b01517103101d418103110140d605216000003501d03449800d0320117003450f07119400300c0241c1e5100c1d803907580200440811940031002e9460071216800c0140c034414801c0014520107035180c4e6001c01200d0895010740702c0f4001d08100b039a41d034519504600c0000c0d6000d0900f02c4108003203286c2e406040400c4a040d076005a5902e581c1a80004441001c0d00c9040b05038908000c100300f484016a0300448a80b05200c01034a035080560400c402d4400c0c05403544074070072100424005903070b8100344140901c00d01d030001d010812010070101c8011074160301110701e8805a000400107424640d00c0903030010700a046c200381c6252a602e400c0f0035074075031540030030440f5918411540d51107201090f05000d41034610107400c09080805006081d03000b400a11801c1801c006a91100480708004890300d40081c1e0405882415001c06c024006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 710584154 1250 710582904 710582927
    0x20a0b0c070f120e220e071d10050a0f05012303061201021b150915010506091207030b0109060e090a0b090304030b040b0105040e0d021f060b04180c05030417070f0f03 73
    0x5e29003803482c80c2406a2002c80da0301c0694800050b070380700f907802d41c0c58440c00d239200191084004640d074060206040d11000d135802c0103002500c64801055140800050480c407001000c908600c10340c0e1424034042d11000101c94101d0011241040c505542c09212030085c4070703003209c4e403003850440f988025041c000840c0c941070b98601d07140c152000f075490813144c54552008114005181e40b540d40140103915222016107500800a8040c0c105444070342c04a628028040e0401e07a80b01044074010410881c3d28050302014100705c0c00f48240358105036100b55038480800c10001c1580d06070000198500e5001c0080d64025500402c04c05c000341014101100c039084c0a0103024022824981e05c40e513070050000306080000300c2c56008003210790010a01d1825401c9000342d0404990b2030300030004030002104043c00c041d0000d450101c1ca2066050391607412600300d1264803081c84000d02c100404a070104101e21003141e05405c2c4180d0f20100791420005580c11110014078444071468000249a88101c420700c9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 710585404 1250 710584154 710584219
    0x3063307050f0d08070215150d0b060406050d020102070e0408090a06050a030f0504030e010f0210021b0d0c050a06020f0f0409090309051516140d020a0b0c070f120e 72
    0x8440d883c189088500403012280800580c3c01049031900107401c90911541c812044600340c03c1500c08070000940300c041d1340720140c500454050a1121600d064491100100000c1780c9295030340110381d0000c0c1d00c4080c0c6100d0b02d4034802c1124009014440c8010880b003809000505891f03015459440281c5035800c0110b041c000a803400c60b40100880c02ca114a9000e10703015100d0781c000c00501d400464045403440003c00860003605a054485840c1d03001408503c2d00b031520710303039446034603c458500d4480c1502c1c00404010642040001181e0049040c03540c8079006400540c0e2214500482c00482c490300d032a000c1070301c5001800059502217544991402482540c0303c11180b541c0304100720100d201142d1400d882c1d4010041019604051b0a1350300300503105400840249070050b000d541082c1901c5260800340c0c02400740d4108100310003181d964401c0f1041c0e002402c5c15010384458245040504d4010007851000302740c4500305004100d0b1000d0340400a20351486a01c039a03030418812032174150000f8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 710586654 1250 710585404 710585413
    0x9010f14150405010b0f030a14131a01060e090403180f050f0d03020d0e0f03121e031902090f040c050c011103060f010f11060f01140603063307050f 65
    0x900c41c500b5000d140c1c100e4120400352420480d00b540d80190b242d001130003600401c0d5072a05840c808280c5624403901c01e48291114031010211410030807061881d24a414202e4075500005202d240d800c200c8020300c0d050162800c0b800c1e07503203514090314031401598804001103254480010f40c4208540050306640c1d042c0c0d0148800c4482005110885440441c001c0160b0064800340b03038054840c00305c4410380400100050009a0440c0100e4240003007581c2202c5081400100c5003400f04480c0407000400d800803001c0380c690300c0c040300340443d03818031140300150494000a52490039612650110504a40240b0400800d13020080291181d0302c20b90151405500b00011114030440c8030007640d20581c0d001d0a5180101240b400448807041d10301e02c00028041840803041403000c1c20401e441c070860405a0500295040101d0003008450b04e40240d44103010030002c000c0c007915900780e160641e940e200b05900100c0031b00801081a22401c0800060310540460b003407003840f6000404e4680391980c601650b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 710587904 1250 710586654 710586691
    0x4180f06080a050a0308060d0f08030109050709080703030c0f060e06060a050d03020304030b090a0b0114190803070b07120c030207110901050607111c03081e01050a0b0309010f14 78
    0x7180c41d514842d601505a070400008880441c0c041e100b42544000000c0c48002c0c042d01da07688086100c200c2500c240d07100c100100050040d03038668407178107410400c50305008142074940108bc030340e11070803804014204040703250803008200118202c0341080b40c0c041418003c00848010003076980204941c00da01c40c501d90300000500d800c2410110100641540c041c40c0342500f5521028010f06003e80b40703511500c1044801030200b01c6d8010311501821040314200240602c050401850741e03006034007664031a40b00541080912000002c8582d90b03544480842e0250b0f86580040c1e0f038490b4441c4c407540600341803022074041594164018856148a40843c40c00381c4085000c0c0106900d0034022190051000c0098101080c4091064940f0481c0180300c9a108201d40d111b1540c81800c01c4402c4000c03421000c24086924400c820140305004510f110304015031420002171114640b80c450314000000010100301c49120031341040b601d1000c501e40a101034813400c090350306030f0101103407130708000f02454006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 710589154 1250 710587904 710587919
    0x1e0506010e0a081b0d020301110d0501140a030f1121070e09030301030228061205060405090d030c1b0302070f06020604030e0603131502030a140606071704180f06 71
    0x4070b003a00c0584009104120810300c11280068034410650b501c5440031a0310030059a0034055000881c0388545000d8031307403064a040105a490680004080c880501a0300344a511400402c400b01d1707401c01d000c4141011071341025a0018680c41003a90081880d20100141e101200c0596241804030f004403010f803541c1c0d01d207100509006031076000c103540042004001501d4480762410750890003c2d0350107200c0550050790321179480181e010a01290740342d0201641840184200c55200d94261024001d40c50400640d54036402e884003480d05050343c507055440c00912888503516443c0d08043c1c04510308072141800b035030f140500d00c10328000041c0d41e4004039203103101085d40c80c083c0c0c0e03060b10303415902c62a403002c010003a040213240607040a06d0000740d0001ca0310100c0461200240c4a50040c2d0701d0a00c1c03180d072000d68400900c001d070f02d00401e84c10312515803944001c4902c0039403c80201c08030346450500c0300d900c9200b107034808441d1140d000f0080440410b5540b2804441c841151f041014980ea00b22 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 710590404 1250 710589154 710589169
    0x30509030d0813080c070801023006280f0314010b0a15051b0a11010e0a0501080a020a090b0f030109051605180a05030f0a120809061302041e0506010e 66
    0x2c0f40f501c40c020310a0307541d00148404014000032202c820030b540d4941c3d141d8082500720b0f0801842d1203075818a80d1002108800c2903222100380c84642d0105890a180203030114400e060140001c0068900c2403520300280d40e483c08580c1d025002501981c1c0d8820740d00d040081c0080007003034051034203500e019511040c40c6042c9640350304403200701d805840440300c00344080e0349580000d80003142d00d4550b22070684000700140b100500c2c1038850100d034200c007155940010040e8065008003070113129607490038490b07682c005414580c01003407141c02690302e0038901e204480000d01c95000340340040d00481c101c00200b04440103181030352081d210400083e81c404a44c1007100c0402030440c40466000c000c0c2c00280308540005080a0300b0181040d640c0641c4ea1000ca807614141505072001500040c82030020401c4c00702d2455042c03601d80c40c0c81102c42c10140c11035a01c90304041d041e0202d40444849150854541d9001950b410040600741901402441c60310006407504a0310303540000c140d41500b01e601c1c9802e42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 710591654 1250 710590404 710590411
    0x709321917030a1b02010201020d0e0303090f03031519030b250f14070c03140a060605030d0917011104030c060e030105070503130c03050f011b0504030b040609021c030509030d08 78
    0x94446414400202c4201340001c51107405904554003000300c210049040d00034240c4642e445002540e9a2070305d1243c09007485204140e110350b0f80c10030000d1181c0c1208000c0075000704c2c10111409050440c00e0600421580340030b61004042d0086041006844007003e9001404d46040c003141074030089043d4401c03240e1014101c100b1000c980c04805018111840f0350143c050640b00300b5114090503100d4841c402141d80500c0d41601c10b520500744002000410700640008190036030043c070450750300407400341c1a540c55001e0340c0c170145000056482140300940040d6400042c241070182c1d0b0719100d0601c040c5a00c44d40c02a4400315001183d03044207030605105061140d02240d0311107046859161440500014030801580d0300c1c14071000100110310284400241c10f20f25600003e0048001c00031940540c00000c00320050040c1800104003081c040c420440d8003642c0300c0d0b8000341c240300c00e10004032240500301000002d241020450020550420005c001310207046044500d9140d004900311a080d0044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 710592904 1250 710591654 710591657
    0xc090b130e180f060702160506090613180c03050601210e030906030a0b1002060c120c0415030f060f030c031115030f01030b0709321917030a 62
    0x1100c0800503a102924510b42080114100b4402d90b1520b04010307292101c0030900301e4158018805100c6419010071480d25840c0317651655009507450300d0001541c5000d00c42c505d81c040e40c0c001030421042020504901d010701901040407102e000c4107841c41000380751005400000c2440d20005c18841d6004203138213800210866800d02030410390507807510190120018000c3d240c40706100c8540950b4030880030350b01c120180607002541000010801120441000110b02076401c072000f030090b50803410b000c0310550602c2641400a9855070803010b00c062080b60f1040c041c0024100260204c2607040d0070034a03014604a0040c0041512690070702c1ca0705041d44030081a140c000c890800004600b0b91206032010002002c20a040d245200c0540503a4030031102800c00d400040018070030480b100c1800c94120b9014580804503605104440c0020710001310f000d10101011500c26600c42c0510044a03040800900803064000764640000e104075000e01810007074801d00d82c0f5a4480420000589400850f81d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 710594154 1250 710592904 710592937
    0x9031b100309020103020f040905091603020907050702010e0a03140c4002160519080412151b1b02032104050301150608070306030b071b06050106030c090b 68
    0x810041e0020916207100724103268007400070000000d107403400b030401450003100114540ca0550784560404420041d08400c800e0100c10610150b16020034850b03016041d810700543d102c40600040e6802d40810107050340c0040d502c0004801c02a1012500c002c0c110000c040310040b515a004004001c40c0c00031455800c4c205401a90840d2000da00e09030081d0074070108100c070031000450401c006d0380c0c0b00350b0200c1401481c079007000081150411a120719800103c0c1c2200c0900091b5a5a085034071a42c424248400080c0a1002c180f045040aa0000140f0204c041100482001d01144410014400000400c00c001101e02e500b00700301407202001c50303005024107070300c0310500382d100314810098116201240090002003019202441a62102030010301e0480c0c00c9854044020b081c80b40081c1514105410814100002905554040d0700251941042c002003100f8000d207400e480446603000d40603e0811000184090309580280d00301e49681c4d403101509501c400723a884031403140c20300741078035409c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 710595404 1250 710594154 710594179
    0xa030e101e0e2b020f032e0c0903050703170403050d0356040203040c031b0f14040207050102120106110706081807120809031b 56
    0x1000c2484a0010406081c94850201c0034020020851074a20075807002c01d90b01c4015a0040c034021092074414030444100291031010000c0180c080300d001140240203400c0032021414541c0d0900c903166500c6404840d01984080310304104040c01e00300c1c0b0450071140d01c2c01c4c0100003018412013540041d2074010300103004080c65941c501120702d04900300c0360806c0c2410b001c003000140c0c090112099103560350b6004262000c1000d2444c0c11410070130a082180002c42c418503414001d4070404403519000f4201e11603000366400117a850b445e144903019640944000200420001ca0645050550740141081c103071030010040c4048000c0c0d407500a5400c05504171a0401c0810213940040030361003005440542004200d903540c60030398004068081c070416a000060010a90213085000340c01c04000003024014070380100a440e05101400c150101c0402d00800015408200109002000321034010072007144182400c01c026088503608a102c0d00403d100070b0045101c2414414074034400402c1c00f020081c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 710596654 1250 710595404 710595409
    0x1140d0825140304262113060801121103011e0203010e0a0e0303040609081e0901080703021c09020f10170609041e1b090204050307080a030203040e04080408012307020a030e 76
    0x1900203059003102e1040e10154141d84511b058511145c0a04540072911500c51f83d80d6007042094a40209007001f8046004102814510364003081d0a42c01c0010f6503540d1415102090160440c03628810801e000030260500c00100f42d8011030403134034142c2c16080300b07446416460003a15030b00c0031a100e09600600114001c41c003283d0101e03900301e1003004005e24062480056030200e07503c40000f803070b40b0710700400d03d17101ca9601301c200c03242e00c2412880c0452170100324180c44038000314075001c0f80a050756240c0b030303500442d240c14116158401000b01400c10004589400074001402415800b800d510300307001050791414840c0c0040e01030b550000803602d040005a10808030005943c2c400d442c0455075044541c0c030303130303140a10840150810203005665981071a061614000300c40c1c0c801c0b101c1d03501580e448008a070380030041d142075440b5001c140d40c09803207906003850540600d8007c40000d500e8194180d8258000c600b041c040b44042d110301d045c50b552803441c26a154040b405014010400309000c21080e407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 710597904 1250 710596654 710596709
    0xe0d17030705040302090a0501030204140906010b09010201020d0207241b05071e120212040e0604020703090807090c030f020715020a021509030a02070e01140d0825140304 75
    0x1d1516145042c190f80350000784080d101961200c994a81d03e60051096003050f0107800d41c0943d0000764940e2900b0804510b9a1703600052007801d10b001c0c03010a055115178070070740449100000102055403074081c5420050b403e0180c6082903e0120969114400d054035a805603180d251f4582d42c0c291480c10400c00107071188d0f8003002003100c0e620210040d400a9000d004da102e00d1081c01480c145c1c0c0705000441000c0d00d4031450704d8100d40400c03804c0c8030803c06800c074070f00780b55072106054601585036011807400344c031040c901b0307000040b290044900102c1c000c0c0043d400051014429034080c04065503040516003241305003e006050312450751050300c4007a5294008040a00d81c80c4111000c1d2020252032030300d140c20580d00074078140c200051303108a55504010030009000c01102d000199450b000814141c5e4540e0344206001e0f860900041c01400220400e03070307410010010340c8102d0407885120580440f02018012581c00540079440f5011000000544080e28255035030300600341c03540c0341070502030b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 710599154 1250 710597904 710597911
    0x1b1a071110020f1224180a09030512040605060f0a06121d0d030501051003060f122603061806010203160807020a060203032203121e060b07030e0d1703 66
    0x24480c0030410151844d15400c1e80501c034001d070011205600c2d90403899004890344100510b0300c00e88040985c5c1880d44a003210103030300020107240000342400386203000e0300d5500640044a201c550040b00700700600c001a00481c0c4508000c03140c0d4101d0101d031504002c01e07006240903080000320061028104200c0503400706e184c0c100509411044842d003004010f140001c40c07070040c00000c0d00c45c0c0040200303042500e10140c100e0150300742070101c10b09010319403071102e9192117550f40c81c032008503190b0180205801c42c1d64160040300083d001c10101401545940da205841450055034065007203004028054920790048505034040d600c0c004000c0c07051810481c2c181c4090320401c2c002c1140304011fa4503016410000c003142e80265442e4901680c2440c410385600b00c20b4608050090080c1c00080d512005c1c0454248641d100084c03035200e1068006032074a41c2060f000d10851400d0404115021504094043c051103550b81c500c466114800707005c4080d9603514000c107040c1801000020684002c40510390 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 710600404 1250 710599154 710599177
    0xc0a020c0d082d0d1a12031c0e030d05090c01141b100516090e0108120309030d0e0f0709151205150a0504020f0f030d0f1b1a07111002 59
    0x192581011a24450b0358004506940c820b603480340020319560003005c0e0320b80c403014110750680c10381c644416965100d20a13403a034444d04207038200c41c901c00c0b8010b650001a0000c203220072261601c2038228000c004000c00d882d000710912400c00e28108543c0304686807000100c2c41c480d0581400e00c1e401d111401681140103000c0940160025005642e600d403091900c1030041c0c003a0302c2a62154100e01804100360b0350404103403901c20301d00500c02130300c00041c0c460328000e0102d0130964170307600d0070381607411801280d009400c00380c03c00340080010390b00016451501d00100c41502e403242c1d0398030b2842c0200c0c1d08000000040e01c4201608020012034110514603903401b80003660605030300000d861280704402c54010440c02d99520601043d403c06080c0d20510344015075443d00c0c0c850f82c40001039918181c07440b03c070b0104504107030701f55122846410305001c81c3c4000d00c408000c030a0300c4d1900c600707600c0201000021040341c000c0002d000610402668071100d0542c0090009800c2c180e0019010b0351207081002e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 710601654 1250 710600404 710600467
    0xa030c09020304331d1b0a080d0c030e010e0301050907181a06091810060207060e090612010e01060305010207140106030b0c03100f0618050402040b0f030a090602030c0a020c0d08 78
    0x40b482d45d0a000d12074421070014088072824600d0003c00441e060340750410030559000341030480742d8582258421320760075010709103246a0580ea100484400c0741c00c0d80310079015400c000510002010001d4080c096801904c0b04803202e2440d48a01c0c8100c51449801c0a48203d00c000d00f44114104000103080c020000340162010214015a20030070f440d041c0c4d20800c44000410081048c16410302c4040090f001a00d886d046162007040001c07000e401c00b0f8101031003003121110480322610b01b58003140490b08404028404076559007000c0c0e000f9041800c040da4501c1c010010800030b10b806201c3c80041c0c991003c1550496100e00790b965030107030401000c000305450b409502081e4000d95040d0340d002130031595298030303041008603111500801941c0c4054050b500520041c84050b01c95819100102c07500d01c80940c680e030320075121001030400d01c6d00282100b4030010601103100d055000130050040c807a000c40704040040c1e002c0c480b9001d000d10f005801c01c0300c240821b10130640319000b451094480081c0ca035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 710602904 1250 710601654 710601701
    0x4060501290f221502010c0e040515130903180f0605030406020c06040c1d0c0405040e0709020a031b020a1101050711190602010b030a05030d0504020a030c0902030433 73
    0x1c0d24850210390640460810f0140e00700140a54048401201d10040c4024050f4500c1030502400d00501c0c0141c452143d070300d0b400000d1000030102d501d05046140180360030318202d1032110300002030841c07600640020b0180a80383c80305e16204071a00d8211031002058082003407030b01c0401c450540000d0411a52203400b082103503004a420441d10b4012401400082c1009240c002055800c3c00348131910181640c10104008994602c0300944040b21001c0d140441c1200c408500c05041040c0d40d0400c10000f8800700e00e444030b01e80c1c5135010f54180c050101480c1c2c0c01e41e420a0003a0707070b0b40b290500010328482d40440c07803900c42d520800c0a080a2441611201480b400d20800039070780c07a028580007100038005c800108101390b424042c241c0d0800c420b40290003424601c2e00c401d0b4891068042d11140c43d502e078000700d0219100c90394144000c40d0005030401a464030b0f0741e15100654810b480c10703194209001203000c0c859264452018610f507040c0000d0b6800740031100d01c9000b0300030342e0041c800003040380c4101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 710604154 1250 710602904 710602927
    0x307091d070305100f0b030616050f030a0504030e09040b13020f040f140a0c0207050d05030c0d1722060c02100207060f0c02060f010e06060403080c0604060501290f 72
    0x10142d840b07200545182d0714003822a1046030070003120540d4145c01e050a000c07040d240031072201d42150301c0d40b42c0c5c6050003a48806c262014458600349060500d0000100108940304c0c1d44050702070b5209540360110140c0582c100711a80c042070314054035034082c660100344552054400c03c0d007100d01c040c0030592500048800102210000c00d2005031050304c0c1d800b0b4159101e41c8581e4603901c900200c80411080072855002541d510483c081d0ba4010300802da0424144441081030701e000c0706003c2d0484400f414601c01c01810b070125004450080800e0401264031082043e407500d20034030340280030f1310084840b501d07810090802d0050b05803d50042010460740590140000c2400c00e020700d4011500d00504c0b54200d0841381e43d00c0d06103046402042c18403030703000b017000d10140c115020b12101c040f55803503840020f0401e200715030009088580004041d0305110020490030311960042f031013000716a07a14194042002c1070b14015262214407540100f008007801c81c050701d40c000100548a00340300c0580c05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 710605404 1250 710604154 710604163
    0x30503281803080a020a020705040506030f01060321030b060d0b0d0611070c1a070b0702070e0106210908090d1e0501090c080a02130c05070507060801150903020307091d 74
    0x30780001e1240075100a6062682140309a5044510000c04524002c0b000000a448100c1030146910403034441000c9005070743d003000004c45000714000204485039491a181002c501101c000c501141c5000e04c444000c10b00074414038100c10030260a0303911b00703c00900142c00509450814030fa006042c28413070f00c04a51544941680f80102c10070b800c3d41c894840c00d04503080742959000109041d140082c2013140803110707054a1995500410500450310f41030820381c1800341e01d400242d40801d07880c00001c3c05a6001d141392101103c51012038400ca8500c50011055411400b009001c10104001c06e00060901d605000003050043c1c0d081c20414220350007540032180340700d8050703651f69143c503e000c050041d540200d10017013800c000108410102640803503401e0550130b1141e5612542d84182c0d140a078003c1040700da03040c1c1d0220503901c0e072640320031010301258028001c0004422891205803042d5010758410300c03d50b5002401000300c0d40ca01945003000c2c01613903a60b0b800950b1a2015101803010402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 710606654 1250 710605404 710605421
    0x60f0c0304050a050d030606030f020f04091d01020f030709050f15030901110c0f0c0a0f03022202031e0c1201171207030203040513061202010c110a12140a03050328 72
    0x1031700403c0c1d0b00d08d020001011baa032483e0400d040103104000740c00e2000503a60480b011135150f0380000c21106c4801c4e2414104180201140c000c0b5400000c07140402581074000790b10a080b0b030b0315140d01e0941c8420500500e00c0010304a690030110b21000b80407203400303c0303000e1944121020700120300121100003040d4550030894402615030b020f01e01d02e042421080c00f107130301d120307105450b070b1411540780244400b01c401583c40301a0080600b040041c0100d0b08440f045c80c40d13149001350941d0b5034140750222040c4400340c64441518401c450000c240366280c03140803540d02e045416500703000d60b42003003480500c8420b1021074980c10300c554103808240e0b4042c1c07400f81511902a03009940c0701c2d1f1800041c050008040e448105160b0300d80304040c000c1c4009182c400089640a180c94034203d03425260420081079540307442c952000521000181c4070604442900c0303030b01c0c0300d68000803940400c00e00c0250360307408e0030300002d02003441400000c10241000c0c8121341011100c003002a101c45201d840c12046a2011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 710607904 1250 710606654 710606657
    0x110f0a06050904140f1f030204050103080304020f01030513020105090f0a08030403060b03010603032a0212100b042a0504050d060e0618030d02070f1b0512060f0c0304050a050d 77
    0x7103403291003460580300d4026402c072140161106403614411a141d0f03405c0082c4240c0005500c02d444101203040f0751801005180d010b44100401c0d61a030404000c0c0f60400c407000c902c1480c0030a01c0c030b100c5510a004950080003288101020740307403103500546403a00003860581d013002d01e11078000441d80c0d6040c0300100803d0900f001c0c0d0381e601d0841c101001991540700c4002d000782c0c1440b0702040000e9210300d01c0d05914441e04503038200404080b00191020301201e1001e9400002700200c0c20040d50041400c1074445014101080364062410900c02643c20300d05620050f68517140508550501aa2100b04a4411481c105241c03a446400056010303c4007407064500036503400c039444100d4000c00400d90013403002d030131090030140b44401156491049107030f103806164020a0210810010b9502d5051850b4082200500c0c0c000c0d0000440c00d0040b603215091191a018201c40e01c0024082810750090300d62003900500c540d510041140d661340094011280340c4a1746092001183c03091040341050a440d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 710609154 1250 710607904 710607907
    0xc0f081b1303080703111518031201080313060e060912030403050102030709051206040c060315080a080c0d1d0d141b0a061412091204080604170403050a110f0a0605 72
    0x150a00910321481c81030503044035405810b08280c850419265194000c0080341c4000703032300c000c070905507081d03001d0b034008070a00304041c03000402ca8001c04400340661003898080018060396074041200d1002e9031040580c0c2083c0c04000c0101c4600344940041184601c8801701c6e8580340e078990f00d16089038001ca5044000401104040c842c03850411901400072480000a11031070600f51103400b2154510f00c500c0d001c0c56500d034000004000604001e0004182035820341d000070659007000b03002640720034113842d15801081c421079201070049100d8100106a8200b8240c3ea01603201400300010840200781c801c40c0c40046000700c0f0800c04c2001c03000417000b40da002c180d1074441c4000d024003446c45400c0b601c140300300c4051400d400501c10040e2035001c00c00030102d00c080c3c4c0300c029101f82451420503070b1844040001030b001ca0b44420000303005008510400300130380401501240070800780114003000342190458501c20010408202104006000c01050103220741043d00c00a5002202030f4041400304c0c10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 710610404 1250 710609154 710609167
    0x2606091f090b063f19051005030a05010501080105060405100e0c0706111209030a0c032f030a080105190311010314070e010813030903120309050304090509010c0f081b130308 76
    0x41450b4813200c9000b40031001441824031a040c25400c0218103003110045980d200003a00c00043c403000d41009160240a50b0380f1460181040c030b001e40401d0061140c15230074038004c6117030350502d17208462013060741030080e184903401c09a0f200764618005d0308040050b201480464041041e91141e0503a10f00c540c22040d80d030b40c241c29039024100c0d0000340300030700030b8109009407025a500128004d98055141c60000c0044201c91100141e0120b031100f680c1c045011001034501d0801c00000034110340c20281c847e0181a0303a1034040040d400710803440440b401811150402c0040c2c94000104035a0005050120f00c3c107094040c5a510a04102d503044001780c0d01d0141c0d6052540c02010054005680105440750040581c8000d00078054600c0002c000c80404401030489074031a03400190100e40c040141d96640ba642c000c00c0002c0d0a0035030f0742030316035441c01c1c0d0283e500c9402240316200b01c40403611080001c1c0e441c0e40e0b0704c81032508240130040c80c9100410024840382100003480c8003451003102c2d545e88500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 710611510 1106 710610404 710610487
    0x10b030d090b0a1b05031b03040f06080c0904151a030912070203030c03030a0c0f051201060e0f030102130611030c0304050d032606091f090b06 63
    0x2070360031072903400c01c14044001c0041c07800c1040d40491020941049548a228500c0ad900352921130a20411070140280f071460b500a0303030441428100700000000c01e084e24101403040f07004a041c00d00900c010640c903a450081c11025030388040c25890264035590361520099103044100754003050764001c6640410464403041d02100507031303031a03003800000702014140619803c004a46551080c08060b0f1050b42a00d070300065044444109900e85030003520094a03102d01250010301c8030005401c9600c0c240000c005151020f4180480b00303151032402010741d4520a00d00e0b0047d0420084080071101c0002520300740c480407141c5154044540c034007a101140b0302001d818a19454a11002280790031244292055078161031240b55039440700403182c0070164413440030020750080d8209121185081d80048081d8202a00d070301e1500080b122a203074141400040609003c8100a0080400 = true := by decide +kernel

theorem cover : BRFrame.Cov 710431654 710611510 := by
  have h0 := BRFrame.cov_init 710431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 710431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 710431654 ≤ n) (h2 : n < 710611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
