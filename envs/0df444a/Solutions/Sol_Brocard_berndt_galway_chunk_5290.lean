-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5290
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:22:52.884795+00:00
-- url     : https://prove2.me/submissions/8438a022-a33d-4c8a-9887-1f03a0c6c035

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 951258992 ≤ n < 951438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 951260242 1250 951258992 951259007
    0x140c07020a08074104020306010e0307180e010e0709090302070b040f1a091e0f060d38010f0e04090f0204060603023405070e0609060607032102090604270606 69
    0x445c0603541c0400005d0107070b842408080340c403910243c261780e07855403214042401141c02c0d01202040314100400d080702c0d050b0520940e50365410641c040c2604038108509034000d030841c4801901140f10340c04022500d088404c0040004096070051440c401e40f400310840c0d00303220102000344180d00300f07100d12540e54588a01c0c4c0500f90200c1201400514092000076450004449041790030060105a032180450306507c21100b207540661182c0c400e6100d60320388070074011034100c06130451308803a1400d001c80d4021112220100c0d000d04110580300c00d00d030040f80c1242c140348400d64445001c0800b200540c1400d103ea00003500e0249020351405012082c4606541102010030010800b1010028801104886a034000540c42006ea80142c1e940358507801c2c0641c4291040c61240348080f01058ad607181200031500501e40c9502d94000a00011010035040c1c0504024094415020400040c2c00e5031010f00810141107030101d20050303104400c5000750002099000303110924a040e4044c403520383c10046 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 951261492 1250 951260242 951260369
    0xc090603110103090602041203020a0b01080a0f0b0910110702010e15091e090c03010609060512040b07021e160504051509090307081603020d03140c07020a0807 70
    0x24041284d05252400310002c2c407542d4421225001e001c0c1240017010381c0491140800b80c0104035030071050362614803042e11450010301c024059002c02d010b20f000140c0c1407403065032000d20356041d02c108429108480b4191401a064003a03074203000141c1c0350441da0044000c10010b8002c0c0caa6165907092307280340c13000500c00c00c1c0800e486134014044141c0f026002d008562035010000c0e0411005050080760b080f840d40007805140c011600710701c40032550f203114000342d90b076002001c09450f0040c0c40301e440c5c40f90716a4001e000d201c2103020311049011200100250840c0560420000340950a0250b50001020009401c0300e44524180b10501010035000302d5100e10041e000c840141c0340380c60302d0442a10b10b1041c1d0800825103c0081001d103c0302100c03107940171486019400703032500d034000301d0780c100e0403265080080e00c9c04404040100d105501d4100c00790441031b1000d051034440702e07101d28461b468a90140e10280c064001d0305540305c0746e61007207050341d02460320b07180e400510440c4d4104a010711011244 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 951262742 1250 951261492 951261497
    0x5030f1630020409090c1a09060a2708151b09010c060f0204030b0c19081506040e071e020303060f1309060905121e0a0302070b0703090c0906031101 65
    0x407685580540300d205070300104040081159a59a10030742c0c40d0151500c0c0e5000e44000c0c10409000401b2081c2d14481c1104510021206207040780c02d0081001640000c1039103001c20410301d841c0560502e406601400c241c40c00c1c021008040d10700b002d200d00d010710719020300c0369108d07d600903ca1900c0090041c413284400e404400c07a140c4a40c800100c4140556040c0503141ca030500c60071410080480e401001943e0140d00d41c55507035130b6401c0c1c4882c003d10403620b04a0700404480100010700d8442d005054202d054000e1074018510351200060b01c9400c1500014681e50310b51080c049003c0e041900500c80203005000c0051a8501a40283d228000103180c140140001d481d1716940c3e681d0540c5140110321000f500300141922414031342c0c020700128004440703a11410304240d80010790401900e4261241d44141c240c80f110403c00085180c104880c41d07001d15400340030003800a0001011140b00364000e030303070011340314200d4105030612841680c0080140751410b002800420210b800e04801440c0a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 951263992 1250 951262742 951262787
    0x24050d0f050312040303140c03040809040c1115010504060e010b1903110703050a08060109080c040b130507080f0a0c050f07020d050102180414130209040f050d05030f16 74
    0x24106036003103105070f06a0744152410081080b0400d03800d07078003c13800b0311000392008500e03a40300c0100030103d01c400c0e14054111181840340d0f4115140c95008510420813a240016902d6025407120f0b2600007081081052150100e006000600b007070700c42c0400424202d6039880c00380d4501001514184100c0d560743c400b510300c0b0989644814025000105010100c81d0895542c0c45135003402002e0f90081194003002070056000718806601c100400407c0c3ca068102408080101d0f0301000010420b01032401d03041400d01c166044400b40ca845000c0c4101c0c800c1c0c45408851500d901265000c0c1001050f004000b03203481c40000e680d691201c10343d04218040440d260350f500c42400004c10050201c60010280c0d070000075040c401c41e41d0701040b0301d81d100c401e480600040c8110000b03240e03002400c5802000352100030f4030003000343c81c08423912a04240651004968140642c480d00d0406e00c03020442c0c00850703000424804400180e407030141d4000c03103000d4901500c043c0f44400a04070424541c807040303641c036503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 951265242 1250 951263992 951264023
    0x7090f03020d11032e1103160e1302041701060303020309060703020c0d08030402011214160c0203100c0327240c02072606010618080f0a2307060302160b0a24050d 71
    0x140c000c0410901000b48407112b007280182202e4040e5105001e11030144100c1700c24001090014090032040c0ca6141e006103040501200030b220345500142c00660441c440c0000300c2d8010740b1040030605850b40110f81c41d551324606400090300301038151025081d19458001d1450610300401e0680d50026500201c10109100d110012102c0c00111800607502d030140b42d8001e054440c069001445018454800b841034041d094101658003811031600141c00742581c407074000050340c024010030711079240e03c0d040058022000750b190840d002580b0420241c0d01c248000e000c12081d0401142800c20705010000508000312001d9403224018030400051214071b6944980441c0700c4031181c1c000c0c01c4100c086840c01540074900c0c030303a50802c200060f5241031084005440c15400040305e058454007100017024450310344031045000b9071003202180c28060000c10140000741441c07603114011541144003160301d106100717210300c0d05003048010620007104500c0420107500c860501458081c0c00c04c541e0403101c1c21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 951266492 1250 951265242 951265247
    0xa03121b0b01090c120f06030b130201050d0b150403060203190908090111030f0d051906061407020f0901060c020a0b031009050a09050f0d0807090f03020d11032e110316 74
    0x5c052082d541c0c5052182410078040c02c0c0c1d00c02000c490080010b422603444070394210044926508000c0d001038000c10020030708a07525040032480c418061b00350803600300d0700210712001e50410342040f02c1c01900001031000d0050403080140c0f25a00001d01002030b500e20355039000480c0308000c1805d061020340d00b0100724040d0184152462044031803e01e80c0c0e1015800c1c00b0034000d180480d40b9002e40752000701000c2c044142481407000307a4845849402114200d00c1c441060ba40190500f242c1c810444e11030a0303102d0b21501405402040e194648120451907032041042600854100000d0040140108140c811000403c901281d81c1d4980005082e258040082c000d44501074000e01940705038199070008000c0080e40c00102e0365541d6074941c01307803075081c2d08a0703411440d440f584414260f415010f10252518643c08102c45107d1240c06a1840032080800d081c1001c1000c8144040d0a918504184004498240392620b00007002001088440498240300e130002401e164092060042004012030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 951267742 1250 951266492 951266507
    0x13060b0f13020705100203070503070c0c0302030d030507021e061501030e0109080406120c090312030e0f0c010201150305101e140a0f18061a0a03121b0b01090c 70
    0xa0024004000a90141d00d45101960142200300c540d4862052000c00309400c0f8030035680103101c1942c0e514910b440e1140c0032a00590070303150544212042060020040e541003104130000381d900c3d03e010642d03240c840c0006e402c00035030394145180c800f40340480032400d900c04200a13a01c40d0b003a41d000003c82049000480c0200300750074020305558a0000c428062094100c046d20407243d09940b002c4d00c6007070482c100340c15100d031801c022012803506081400003843d100c90003022101607150004000603203c40c058a8805076030308903c0030f81c202c8044a603407545d080c05a0340704403502980c136401c00f510316904c41d030b5541c0c22098110145552060f200c122625500c5248401c80506402808002c20154401d041c000c025111020b81034980f0000f9444a0860b00440c000036040c0b0402e5540e021540d100c0d8809000405032403000401c80300d520540c26035900c90484003450060301d105000540d403460150030301e100700031082c00d80340c401074403240055002c225503815500040c0b0041054112020300f60303601c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 951268992 1250 951267742 951267769
    0x7030e0714040b061e07060b19081e03030612070308070b012105031b07051206010e070e1e0a0b1204050606151602180907090b060313060b 61
    0x240035800c4001031441d10403948040300c420840d03040100402c10020403200f80304414004071110700c0c10450b00e20b10213994000c0c0c44000e0152002081601c10751000030b402c0f00000f0b80c107620355100c640003030001007410440640d603680c45101254840d01144240340d0713a070000420062048024200c484082e29040c40803200035948100f602d07458088900d40f41d11110001d0042446901c001000a0410001c440004131104e400c031000d54601070366030000700b0103541405426140d51151800018098a4a087c05214100e2140103001ca0b5418000d82055800024100c4010003d807140f40d50f009658003030000d2486507562454402e46280038000c01d19a4232540d203c810b0302600424030b50892100282000d125911039401c0d50b4196480c4000c00010b603910940d051025501409074403d0110001141283c043c00105900707152f100601401100b40001c1300c0c120155003000c1c00800c43c0c00214012120910400c41ea0a0708516001040240022512402a00315a103030400204503031185094503400c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 951270242 1250 951268992 951269021
    0x20304050601381b0f0d030606080a020318100212060604060e06070507030611030a0c17011e080a1b06030b011b1112010e1005040218091009050105100e04020d08030703 74
    0xc15030001c4d4016140d1080312030f0108107010340e00e00102014881d218400c00e41e015234403029015120064100000c0d040240652a5a20245040c0700c010300100403021000079500005030750703038100d200c0c100900d240c0030748500d00485003071000344155038001406202081d02640ea654441d041400c0542c60403d03154000351280b4940a4101d9601c0391180003507101e000c900c0d2060003000e13132603d0300f1524600e803640c0c0e0b64142c40302d860051144000e0840e20310350621440b4000d04016032a580400d0401c569018129020410314204801d4000d5030031400008103640d080400c0503116100011b0114405409070250800d07008600b28200030080710b41e114004400341103420001032680c0094001e001e8144180f000303200d20224070360044054090644196809800a8481029241d02681910015100c410300d406203040800940d4810300ca42840781d4013a5002050b070b424285c081d06510781d040c1c2c004180c81010ba60420002d600d600320030358001944024265640d90381c01c034040380200032a4445440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 951271492 1250 951270242 951270277
    0x16030c060509010b01080c0319020310030b2a0307020703060b0109080d020d02070b1309020c070803070b0411010302030405151b22050904120f020c0a030602030405060138 75
    0xb40d803005501500f4203080a80315211143c64405010701d50b40011100d0b02050070003a410b29200748541d4003d560000e00b0860726408140c1c4079914010800b0f8200c42240318010100c0c0203c1c0c02d10700c543c42c49145000180600340c6182080d01c0025250030701400054a620349500f1034014592142c01c40e0b8004003601c8091301d240691141c0001e40780c2038169000f200501c20700e40042940c1540d50115106250740c3d00c0108500d07031400d08002d0180d008000e04040c14001c203040054001c1c001c2c4000c040c081d110b0400c20b03000e440d05240050381d4150908220f4101441402008005840019401e41c5140e6181d0301000a64545085910315802c2660341aa409001705258007500b0124004130400c0002e1503610348601d4440c1c0a11001c010300715000350440c4042141d60385541d010302d014003a14030061040d43c0e03c21410740d000c00c0a072100d84c0d200b11410b5a0000401041c00002c3c048c6501500b84030030071500d481105e8419074140d101600c0720303407150031640b5a170440c003040d2203084850390f000c0c404400d807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 951272742 1250 951271492 951271501
    0x31e0509100f020c1c0803070f180b040b0d110a0e0a050405040809090c0d23100608060f120f03040e150d03030216020316140f0616030c0605 62
    0x400503008020418018581d58441e1908603004260703100b06502d80d607004200043c0360720100008180404410591814004641c10115100340003c5106440c1034982d07200103c050b0100030000c0c0d2201d00d40301e80d221034210091021801c49000c44003124134008400e5220409005658024100302100704000a130016804c4c14a81c2c10007504003048500320b810b000c080c0c0d81ca400380000d40d5411240140300040030040d09020b89840a0b406412000c046005410103811400c01c1c4102c6004642a1540c180d12031a07100c00c01e000303c80000e83c41003006401c14a400d144c00c0001d072241c80040c20b07040c4a11110300f180050742c0c0351624080e080c850140115200c1d50b00c21400a5141e43c814040c0c403001c06070000000312a807034011109114100064514104000a51001c400941010f54441c40c40210102a0005a40d0401c01d14903d26005014a408185004101d00d23002141041c103034080c0c001d40050301d802d41c0d00e8005076103000c45407035890340c40740500303140c102c6d0b181c40c9061b4001c04103850f090510 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 951273992 1250 951272742 951272747
    0x30203130e0a2301090507110f0c042706020c030903060411030c0603090312040c03080d1401050301060f0302040b0103020f03010b0310142107080709050f010b0702031504031e 77
    0xc41c003442d50541c08010b044040300340000b0140701c0308102c50002a0140041001800c51ba0043c3d510080c1440e1035480070300c0d4803444074202204c5034440c0d112640001020708880ca8035105803942a4001601c0301c01a84000100503981c3c0d00e01a00a88495408204d01c4001001401140c50a00e4004d003a6403442c40e242c43c04454101040107003c0c000c1c840c10b040041c2038100001200c1c010312200c4011802c00a01d4005d0101c1018010011110311000c5440080069480780c06040002c0726400040355068054047e000c03000780503803210348a03a040250810038074481151000940790141c402242162001006070b02911074102d50107140c0400000024a083c850009540a000d50803146060556284484840001d0380c01045521000440348656881c850030224482c03440d507801910b00d81580c40c2d0806041500b40e90284450640700d104008044020202c210f02520740e44802038200001d94000c00d940305000c4001d403200001940100d800d15018040401070400c610040784012004c1da07200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 951275242 1250 951273992 951274019
    0x3110c0604140f100513151b18030f05010b09010b0a02010506090c04150903021e0405130c0b0a09090f0e0105070816050d0e0703050c0306180c090403020313 69
    0x3915024845900814207410201d0f84640d0400c03810010300b01010100c0c0b400c1c000b01006000d8003580b111245038080081d416255401075440100300001d117000c40c080d948022400f80c00303c2034040200801a0400a100d909551f270b090b0b07900f204004104c840c07585001e40c01050311f00803da6018403090300020302d0400003001801d940c500c69001f0f00c250746600040c07240844007a0703848002da400500040c054041d0b6550030310003c400528010000740e55070b801248801c07100255486211440701582d80c860b0805000352500241da081444456070b40d03d86030308904c6890350040010641000038180f02161041d2000c00180c256144200244001014000c004021186c042c041550811000454032070044440d50721800004418040c0328100127011249079200151840000d9907402d140340f041d0a0802090000d94032036001031207080000b0041501e84000140032032001c0082442070081080b000c40c1c400c4d2928401c0c1d03121480c41e00d551500341d085025800d801e03440b918a904d40000c1800a9020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 951276492 1250 951275242 951275251
    0x16030314040b1f060203030103080a020a061109030d091211031509060a0f2f0717030a0b030a03090537050111010b0d020f0a05180f180c010e0103110c06 67
    0x1c01c003d4600c11508076110900b0300d10801016070410700042010030003174130060070a08100c6c0b058071440e5805503034034000c641c012103045205a80c040303900a5242001c00c017004d000952418099503051422449904541d40c030040181504103070006021700351401c0000d003184036580712144919150400446640e80340441ea12b400090420381c4000e0380d84254410900038504400007421520403054441c0d60030250300e61a600000f90421940000c12115650042e4103131412420640c0c2c0d082a00d9102c1c16030f1201d58071144203800021755200042c1e0840c144404498007500c0d5219080c1d00c0b840c03a0007295107108407203a40d680e2101603411008004c400c05030700f0b503042602e404520031001c801440c200d4400a1030705030820340101c107400144c505070848140145004215182480e120340102b444c411002c035040740140c1c8960184103003540d42480490340400210203050394441400c0040d0b64800f28400414140007401c840c811450f40301760411400c1c08543d280740c9a942c59586182669a41c0849 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 951277742 1250 951276492 951276511
    0xc070303020d0206071d2803030504080f0706050301090e030706020706020c0f030a02030a140c0a050715080c121506131a1809131209230616030314040b 67
    0x1400144006e00800b145d045d050912002c1031030780e200503024403200d401d9006011794502c40c2c0604c004c0080c0f041d588004003942c425907450303444510300404145400318601c41031030150000310052264179408000e5a044404c1000f0204107601449400d0b0f085125404001d02010300008208061143c241c00415007122010220b5041c140b03501d1509440e0701804083c800140c004200d1100501e1141181a5403150015021803500c4d6846215a1404021207011030381e6400c0b0031010401c04940392860b5441004c541440030080ca041c0e46141d0703051043d8903110b82030202000104030700d5007000742008920500500960381d45e4281014542d030110b0320344030b00d02e01c0c400820301c02e10101501c182a28910110f080c03201d07100203242c904005070864020b122400c2401105840360202d0384ca01c060510005481e1180e491300750804004000c54800c0c1c1005030060b4400e050145050340341c1e04101d03900b003c0309211a520944280c038040340030382121858000942903e000307000501c03880805c1c050003100740300c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 951278992 1250 951277742 951277753
    0x1c150e010e09060402030c210d0306150e1c110414060f06090609040915020403210f090b130302090a2a0f08072f1009080414060c070303020d02 63
    0xbaa000d540e0481250700a4043c0c10105a81400741804101c507094699103203102400e034000d0b98125032070210003400100000342c940004000c2c02100801c81c0680c021140381102c0340783c80d2100403e80b4031000304070102040c13082c418110144400a0725a4085090040090050b001c10301c1c2d0766910070200b6500b2911400240e602c80000d441c0c210b00703d400b1b010004d1f00540c20118810100700043c00307214000d40d00e001010404001d84206440104051441155005240b5030010450b0001002d00b0301e005c01030141c1600e9031070441c0e1b0040e441c4802c81d40510702c906d54230b030000c0312481f510b0030a641c0000c1d002a203200c14040c03002030a401582410114120780c003181c40d040c0804600c43d1444180c04800300e22008081305105110f4151658400f480381044050b101c2640e1103040c0222448461441301100c0ca003180010031018080400880070f104e000340701a44642d181d40990344113901c507010751840b03500d5000c110b5841e018242c507960b100d5001612a51075407410040d4884010320f01a50060088 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 951280242 1250 951278992 951279001
    0x2070302030d1b0b090f0d09091401271d0f0111040b070b060d23070503010227040908070c14040207030e04050703090501051303030e03030c1c150e010e 67
    0x20300010f008200104503100c3c4440c105031075072880408060448401801100318502030810200716a1405010710340d10501c829161046501c1181c2d008150320025a56580c0100300800342100c0e1109440300001034924641a142030500041c10203004400500c0c00641118000320070105000ca01411200c0c003d114440040724403905903c03440c0290750140400748020001b240340410416440302e0090b00b480d0581c441d6032580c816840250750041080400e64225214080c1c084c032420b001030005034025803c2c1f800b2903a01004c0e051103000104c0311040454000c020741d950b117030800d111894000c0781c070660b241d0f00c81c10100c98101d500c2c090302811042d01c0400b00d185041a10860382c1c40c0c0c3d00342d624003803402f207003208000180901901140c100760311480d0010102d8403e01c10103000e002c007a407500303144485902d006400d840c048850007880350028020000b40e01b80c08400c0703c20728900144024000e12100c0407100080800e461440ca803540c00402c02300e01c50203000e50b014181c818110400e480d6988 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 951281492 1250 951280242 951280247
    0x120311070f0618090513020f030f06070c0305070b0907050a1410030218180106021014010e090f0111070201031a010c02120c130b0a05031b100908060702070302030d 72
    0xc1500c40d0812050050078100902c912840030102501d010601c09250143d8440341e007030981c3c2e02600c844116465450316002186022580c6014090003076000c0c0040d024560300854072071000401100a004202410b0741c10103114001b03c079100c1364400440021424680344642da00e020314050b5500a07aa40c0c07401094031980c100c90050700358402080240b4032801c8160803400380d0481035022500316103582a42c0b08543d12000d2101400803c448070510300e41c9060402850940104e0440e500c041c6080d43e0a28075041a40b03005041d202409400155600c03028001450b004403081c030065154688920300205100e00b500801100707000b42e0b070500c6007001030f0141c3d1002030a10f0520f140490407400340400142050511610420000001e0718911156040800c181e000b05e13880102c6030642d0f0b828903440b240780591442014000550007406424080d21441d4001c85d410341400d44113400c030f84103003900540b203800502d000e841c580c1c09654507801d080c44041e5580ea4240400c901c03038042c40403050811417 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 951282742 1250 951281492 951281503
    0xb24010908030a030c0905030a05010c03290607080f1207090914130c1a04091104030b0c030c04030204060b0c0f010e030d02070812180c090f041103070f120311 70
    0x1c0e0800007962400300f050000760000c1214004810511080050004895405000000d1204e01550000c954071408840050440f08941c540003030003c8800c00060b0300074911a021600c0c0030b030a0742c4480e500c628505080445009101c401c0c0040e01002604100110ba040d5009010300465202c0b0f0200c4d90322030807c0300075112b540d01751340103d000450028005813a80d00c541007880303010310705050016807903110b900d00d40201d40324040c400a90000d010802d01e10310b07114404111903080ca415090504507500c1645402000d492013036810408404100403030724036030451b8010758ac001c004010300e0b41d5907480840c0e00d410001c0343c05000d00400c02d4030b05000b0018040c4061413282400074600d41160130050b14000e40202c4815120b0080c140b01c12028062510320302c0c2c1c06404003081d038821603011440e1303241c6000c4e07081000302c3c05440342401703000c03000701d010407116006540251480c00c3c3c42d6104001c00d103461003e40c0325000101c6605000200c0c60002051480c00b18000e503204440e407502509015030f00e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 951283992 1250 951282742 951282749
    0xc0a110103020a0c060b0a080d0207060815030303060108041712043c0c03050d0e03070b090306040206030649080301030b1f0311040b0d03140f04030b240109 69
    0x5640d4001c4d45001401e1644482c100c85401440d500207030342c50b40003080c0341c048405458005a4400c250034017480e41c115911540c040c2c500340c0c0c021024201741012036183c0c000506403a052210140100d020440000e03560700342c08020418154485018200010701400700b40c0c1c059421800d41c0d03400c2e5103003100355414240038005500c0029103d00a55980382c014000a01040d900740011281c0840058028040c10700c4060325680c400b06100da829041504080240d8002ea21000c000c002c003081c40d0300c02050196205404491041c3c0340d1b560400031030040fa10700c10070b06204086c5d000002201d18450490b51020202005128811040c07080d8400c600c400408400750108405000410009117550b0303695510481c8442c8025080380845034103c024035454004550311300401c980801682064815400340f07960490345041c2040352502c1c0030b800e0a01c9201d0740ba00d11400094115407600e803001c100c400031030348640000c1c442e24100003800d28090b006099508020310b00b459104003588244511401c2d07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 951285242 1250 951283992 951283997
    0x506180d1e230a11041e0b0901050916031a130c0e060909010e041a090304081c0c030f0203090612010e0a0203011505071b260105150609150c0a110103020a 68
    0x24010785440300c50307503810040c00d03d45c0d0042e210340f00340f14a0802c0c605826038800a484011a120303444008005c601d81050300030038019050442005a4620718100385222010203050003d445c0000c5110006041001d00d800364210789201e400311a1010180d01100b4035108560300c1035812006142080344e281308018038198442c2e201d00044c807000a40000c440d420500c03d06540844003095a48617100c0c02c4100c170310050a40000c5400c020904060100d05440303540b12000712400e4401d21000340004038a08009400c204225241090460007002201c2030700303100600c103a8495040e1030400f04141d009001c1d2102000201c0302159030f040c0b050007031324140c0300358400138240c1e1100b000c01107409400103a82900e064103183c5070440c1003051050f00401405e180728032400c1840e45c2007241100f03a001c100090600fa85088100329500401035045481000212413981d5680c6003000000c01e8146030389400f8080450018807224154130000c1c15242d140e1050309100480b14150740103400700d000c0c00990501 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 951286492 1250 951285242 951285253
    0x19081207111b131d0106060c050606040b1c0201090801020408031c09030c021302041802070506070c050c10020f0123010902070231110a0212040506180d1e23 69
    0x200141c00d40210070f8030810404c40200310f44402a415003946c01c664400d4000c40c3c0452000c070b00340102408041e034800420b0302c051055014602c0421030f10340d5820100c50760b5820f0221081c04580c42840100010044c901c025900e454543c20031984a62000841203101401c890b03070201d60700701ca40118140580c258540340e040c80310907002e110b0007491840c41a17001036803c200110346e0399840b40311140c00c14607a2400613150b90003071401614040d4060815010f0000c218003142c0000c90008006c081028161105482c03400c0401c0705919000b03c1c20000c1045508140c8541030710001c1c4e0380c0d20503407496850b1490310780f0f03681c6022240c00c0740b24442010b500034014a4003144003c0004040750300180390303201d1403010384040b001481d003104d070b4035001440c1e030100014060280f298100b0000c9180385035440e180d4a028075080c00070380c0070703c03498034200605141c08119084070390740d10200111954100316002d0010207103101e44202044028411030701110190955071249110249211480010000421 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 951287742 1250 951286492 951286519
    0x15010e07020d171b070609050309012705010e130e0607180e06040207080c150a0b04020a0507020d050c0303120a1103070f0c0507180b030d020102070519081207111b 72
    0x1414611a6030700131051200411604000540c248540c6a013680a08040c685410900b000109005000314000c0c0f07008079903c2c00c030160262810510000c462003401d00c1185158007101041142c841c2aa148900d9898010700d419242070110300548900ca039581c46500500101c0090700c0c00d1605800b41010b0307110303048002500b9040541c010f01e4214001c0c800a03040c4881c00c000f40749403030070000810508210741ca06100c90040d45019820401e0402c58055041200608004182c1d000305003020b886000c0c110040401c0c048140300c00480501d024003940d984501c01800d40802d143e054603070308034a500e490f1901ea2901075201c1603034040d0115984560031010240700c12683c0e070785129001d80701c81c05039800000b14061500011508601c03c564042102d524a404043c1005000718040e0190390040041c080012400701d814074500155450080d8500054200075041d400f801200751110800101407100b140d401041c003200107081c1e0411111040040700c44412443c00c640e000342c1e00248000004c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 951288992 1250 951287742 951287761
    0x3030f011703070b070c060605040b0f0409060e06072c060f0a03060b04091409030424021c0806040e0a1709010c0c060c0b1e0105040203070215010e07020d17 69
    0x180109100e5074202d0f0b040558548071111901000e032101400305100c01450800c0000314007603800100002c4604020680c62a401b15601e60040c04e14a48115a40c0010108000c1c01e98050300000040f01c0449c0d50a291481020709845100080041c0300385000681e41e00741403c000c1d480f21000005405982031500030710f41652503803c6041c4075420302d92640d001050b1100d0340400741004100b0760303001140289504843c0b049540c405842080c071600100700901800001c28503031540c04161980014003c40344250482c00d14003090030540c0403105241c5140c10640d400440d5038001d43c0100c80400c400207007400700ba903075140e2800c0300816041030700464bc41609402009001c0490042c180900620001ea0b203032644442150402004102c00d0100d42050001c01102158411401500d100c510f80d02110020b200c454140301740e5114680010008030710a10900041e00c040b000d81d9101c00d501d503125010304404139801c40300e10005110b01c07118419910f1007800c10343c4421080301001d4000ea01c40341942d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 951290242 1250 951288992 951289019
    0x9060f0d0207050109050d09140a1214121801050a02060a1505120d17100909060204052d1e0f030f0d0f0212190f030e0703110405070203030f01 63
    0x49444030350a02c00c45010500a0064084091150024200c0c980d00d50750080c00b507104941007940464030f00710742d12259446610703d0310240c0350503001e00120f4210902d0442da0900f101e040700a03082c001c0285200300245080045e05035a0050080d10f40d42d41c0121004503070741d0140c0c41c2e9130f10050b803220021030020015644000001a00e084055103215110004901c0219031310200f100e00d503104516596205030721014640c0c4c00340c5207081e801c0c960304007584040039019484c060411004e58a01c1208100865a411074004020240c40034071240702e0110600b0701c0042107051000c1621217000a02224039002400e454100340828081480c0000c00e0301f40054140b0440d110343e01842034001d80b14400c0340c00c0192030307240c4c0d149681d110340c005000b1030001d080c418034140aa07600301e0305201ea464500304d01c582010104496150400121481003011000760804000780300301070140683c00310900c41048050200324600340c8040c0020382b10701c403049030b40c1d03c000c0701c26041206074480184050b2000310003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 951291492 1250 951290242 951290257
    0x5100b1c09051e0a020918150a02040e0106120507020712140102040b0c06070f090303080f0604151403010501050a05030d08090c030d080f090106031112011104090c090b09060f 77
    0x85500f111035003070302c2e010403003081c0015001592181c00c511045107464168280d1003940688a074540000403c0c1c11030340c1c0d1400c14004204e86107000700080c0340385015410317038000f0030740395003108110b50355110301600342e55080b040c2007030450070320340090800c80c00000c050003140e070030a01d02c07010300c00540c41c0c8089000c0651012841d9540030040090301003102006045851000c01c0507000c0d034101510f0203440d08100340a0082402000801000030a0b040480241d1080300300256500e5913aa0324001002083c40700c001048031003640d0804180071a4107281c41c54950000e40007004280d890f10108480c0c2d1001c0d10943d940340d4040c441d000041840b44c980550008003e104403052042c3d4180000c0c100803900d204c000004845000b0800303c550319002c103c1e04140e540c8000c001c801e055454a171009510114000e0080c9400300001400c11401d5008031100203180e00141e440303d8a40e910300d00640a00c10030700000445a0300040380361880d801c221940350f1001041286842146030180070103420018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 951292742 1250 951291492 951291503
    0x121b10090503120408070639121d010c050318151216050910081806040b01170706021903030e060403020d1803021c080c070905100b1c09 60
    0x104005038540b403c124940c460094040346546882c2482d162501c0d00c503c035400141000b4074450010b0b100380306019003040101c01040605080a0b004031000041080c1ca8001030003500d81c200d2182d0160b600c0301e00d2b000d15144902c2d1081c00e00a8032001182c0c4c4442040000d8031580007040080c1c50820b052140f1a03007000b020b8600d4019a5440ca12514950001081006040f002000f040480d020001054102e40b4007420850700308a2403001046443d03c2022020080c882000e01003549000c900303c503035035892000800c0761210710307140c5482070900c0800e21407800c009070b07100e0078054400008240c02040c3c0b0003a0740149000452144001595012644c0585c18140d503548642010201401814030640c02a0000c00c0c3c8010701200082c5490f88244410000c424180030a00069591180400300b01146600c003021a60080c140202544a039460543c060701c00d1000005942c042038000d948504020a4020962070380c1c4c2c5e0f029900e034400c501d0a91071010300495283c02c8408981d104600b900d000d00b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 951293992 1250 951292742 951292757
    0x801052106010b1315050d1109120102250314130b04031a25080402030c19030c09090b06040915181403040b0301060c030c050d080105121b10 62
    0x500d406050150a800ca0100180001001d460441898403a80001d0003843c005544201400100070650300070242d0716010076441f800e00300c01c1c0e040017034190340d0340c8140200710805207d05008140c2c001d51010f80703d13081c0d8065030300708a1000b030001e5211303901040d055141c2c010024208400c2c800320794041c00400000407418007012681c00d40d488050301c041c6101c2c00c03401c4000b840d04820b941d10010000c0c40c00700b41c0d1005c0c0003400b0444420b8815050108050305080d0060703100c1c2d1000908061400e0f807050313000310100403031104071490101c1d510110f0f40100e61030041180c5402a080980307141d41800b82800603c40301050300c0f401c1a03400344060900421a801f0b14410075680d04040d03a4140c060b01029800b603280c41c0e030034130041d415800510780f4000300540ca06490000d000e1800c1c00305110741001d001600a8120505015520410410f603104060b1351010150040c042c1400c0000e0140701e000c0c031040c61518200c000300150240380250b048841003101e007d80005c0100425100e2691400c100e4036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 951295242 1250 951293992 951294049
    0xa2a150c0f1b0812071106012306070f050c10021b15090d08030109061d010603151208070b130b150102120c030306031c09120804081c090602010903080105 68
    0x40003a240c80210b903140003007917007417041008240703c180c0800484540c000d4401003021040010308102c000c100b40c0c1e1156185003540001440314041d07144050071b031003624510300b0104070020952084186046500a4100900740c00c102e9850400e0811312200d1450844038091500e0031100342240510b003c1101803410401c0004692a02054041143e0700c420200041c007030300d2101c4c00703107001800b4054056a06a6240d420010f907041e0180f241c0301c02d25544030000d050140c98400c0b10006016003552440105a0030f15050415502c49041500c0b42115000403407010310a070189199825080703200182c2640b01c41e440c3d0002060245c0030310741984038401210580300c0c050701c06050150030707200243d41ca0b45400c0c002c2c0350400c0c0c076421218580e005090301099070385130811407090a540050b109070f40030b07040070f2400584c144241e4015201c0e84c07082c004021203100743c4042401c520b17000340c1d40302c0300a9640c1d00403d03421380d40e9501d0010085041500103100605200c6283c40d10b050b03078040045c200511 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 951296492 1250 951295242 951295253
    0x1a07021c06141005060f031603180804050a050603190509011d210703230f040905040c0e010501020304030b0a0f0e0d0201062301050a2a150c0f1b 64
    0x7401c00884140510080800801c40c00c0c850f00720000b080161080c614103034844440300d9a921000301000a001e050b990182c00c458030035480801c00302c004021001100d0058200b20400d0781182c402c291081ea000400420702c0e040007010b60340504100c140e00c0180da106090074001034800145120619946e62019200e40308118440b5410103603084040e010b540f0300416130304c0c09105c21694440702c1070003c02c03003440000c1c0d2086c030780c11303038150b503c01070700d00304c40004412001600c41c0e0601041c4030307000400d010a60703402d2507019a0040348101040b0b04100d58600c40b03800880d0b0300f40700b100d0150b00140000c002155542d44825406061484001645c10080381000e0840d103002050041562041e5401e80810340c09215500144c84445076500451202104d40b0086240400a0701d0411201084003414240580c60f60803055100035051152060708183c04a84240d01c14801c1c0c90345803910400014960061241c1ca5a41f852130b51840c1c1035002c0d150782903c58828805a5448034081c0340e508070003085 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 951297742 1250 951296492 951296501
    0xc06060b091503060a0608070e03011416030908030619050604060201020a02100204030c170f1b0f0d02130e070b07050d031d071503151805011a07021c06 67
    0x65006403a0307140c407995000e0160300350551038003008040d07040090011a0707075880b6800c4112070462500001903034544a00b00d13142c200c01403e4540540c20000001e4400b041d14401901c5180203e2140710085101442201940c22801c40900500000c101203046824000d8181c02850845001c8891040c0e607040441d816901c030760b1003040140d60118919410aa043c002c003004074030104019030070207045850314003090000380b06028540030000b44244c0424070921089000040d034009603006d00c031071043c84607118480480c21720301ca100d8500c10184985840c070180c4854a802904001e00400141081e8004203d1040301d65204d1255050000c0c0460000300100b0b060751150f030107003501c4149450081c0940717111f06002c0c25909030386405800c1e0b042d000510309007156480c5c524003c010071140c50650080ca0940d80d071810804050f01c0101c3ca50b881025140c8106145400410481c0c0c0d8440c004005076010f0044c010743c080e01004144050718110354402e81048070403034682100c10495480400b245d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 951298992 1250 951297742 951297749
    0x15020102070203100608062404091e110a05030a05060f0717100501080c04051e0a090e0703150e0a080a0323061906020309120c0d080403110f0a14010c0606 68
    0x160f00e54a0a006c0203506010143d008800c143c2c40104039500c0000701580c0240f0340d002140241d5803842c4a5080c48a410107030f00c03482d03134000f03c076081821007410014400c1c190440440e015403070b4908001168100015640307601138202c400b030106511b4441c005441c14070301a20030010080c00c05190f034070f00315542210034098500e1445030038115103010300260a901c4000c10120140806100800180e04c0d440c1100710107e0078000d02114100044c40000c54440c115040042c1e02d51500f50391020340303000091070005990050030102850f801c0f551144082e5004000c2507811504502e049100140312400901070300e804905020035502d00c202450140c8001180840c2180900706007849801d05040300c03085044e40400c02c100300c07103605015005e5520301c17484400758019121018201c4d604e0200740000050800000c146001400b26402d20304580c1c2c009000a8404546c000102a05032401a001d9092481d0150507007a24500e0004036120b1111a40142d03414001c1960341c00740000d54501c1040040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 951300242 1250 951298992 951299023
    0x50f03031905151f0c050607020708060906060319061119110c1012060b040e101509030602070302011404031e030605330304030906030e03031015020102070203 70
    0x108511115000103a400107880d41c0324050440f902d031071160302c074240c1503080c4843e0300060000825003d41d08a0b040c0c0b034690409046c1e030040c3c0090104080d4049040713400c031840b81c81103550303585034644034a0f01c49005032005070f410780c004e102c6070b0f106100d0340b0342d81c0305a10f0244000081c1c40c03205650045d5141e20062612094949035030fa681c10460b00041c441d1462400b0350000d02107000940040341070030b4884000c1034144003072142000c0b071600413a08482c002e480c803003d00d42d8403540c1d642c4070001240401e0f04d031090a56180440800e0001c400c00a82c03019600590750080d101d072464a0f107000035882540d0680031552140b00e02d413601c0c1c042020f22400703107100360b440c0c9480e44100950403911240140342c0c04109410610108042d41c8c800f101c110f080c07880c080d884140d80b00700c3c0e4205410080e01c40f52111000e20040100414103801c61100700445081d51021321000d6003405116842e0b12007151b07042d900c505c40000c144002044100102071507009400014501095900040d1a0409a0441911 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 951301492 1250 951300242 951300271
    0xc09160e1f1e0305090601180e0a0c06031103070804020f0d0b091f020c2505130b04060f03150906390212270607080904060611030a0c050f0303 63
    0x1200a002c0c0610311210b0440d1a0810203030a1400c01c1c540c55007018485d00c10010701001a01103611540e078851410402914220b4451458070310b80300c0f40038401741c403440c00441d14140403903011141c040c0c220f07481031100d60b86000080d641c039800c000c030006107070074400d40141c2ca00c6031240000d52448826801504100014410f40b5030803440c074200d0070b4101130890707900c0b801403113051481440042c5d200b0200f0245240e21840b8003118040c080c4d480d02507800160320081005803550102560780c4120004001a1402c1c49070b00d0b01c03410b60351400100c500c0014080c00f1010380002c0300b0045548004140e42c03080b0004902102c41c11300150603504003024009200303018011403401403055600006200407140041e00142c40011117200705401810301c007550a0502c039131070743c2110600244411b03480d0b5000302069111503050615013040c0d004854902d005a141c9100419594051400250404100300080d85000030070b19045502c0c1204c2002201c59200d20382d8071160340740041c0080c44c452031071120f0700c82 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 951302742 1250 951301492 951301517
    0x507032306041b0c17130e09010f0507080a09140714010305010e04081e13061e14030a11210f180715050c0a030f020c09160e1f 56
    0x7040f9401c482c000c00044901c00c00040446802440d0b04e0202c41d0480903200310031035000020800c51107104031a920815450070041102e4007500301c004c0c01400d400000f0800d506602c3c1450046880035200c600c00f080040001880900b420381121880c603208106003d02c599414034110300d03000d699000001c6c1600303010044035065901d44101c43c01050391061790360aa041135240c20520744150450304c094041c1d15a110344040b02c00f2000c03a107669841c4413219140e41d564103801840003000c05002420301c4211540580614480e011a201d03003820503031640d2440e10350700c2c40c050050101d0016800301420a02c10580701100203881c0d038200b41220070440c00300345800d01002c040841e00800d55503140103203c0352030981c05000185142605c00038844800c10101921090711540a042d9904503244900d41000f000c140d409000b0300d000c03004517000c854a00c80000c0812208a03400c03948a1010310a144840c61800c1c401d514808051034040c02c0589400d0780800704000084c9194040c0000c2100450601c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 951303992 1250 951302742 951302749
    0x415050f03010b13090515070f14091e0102070b0d0b0a17030906030604060b1336050703020f0c0616080c0d150503010204060306150e0a090507032306 66
    0x820345035104030020012454180300083c01c403401c1e5501c068071117035a44804001c0005c00c2100001c0101302d5100c2920f00d10b01303824000c004100c1c0021000010b0300c481050800384500c44241c43c4203903030060440b124400031151b98001c0c50b111104203411403040107000948100d80b20003c0485a080c424049001c043d90700a1101180a40e801b00f0310849100d00001510040841940d404c045d04440c151f50381d440d4180041c0c080c1160b9000f0840c1000c00240f541c040d1003200c83c04208980c0c803030018444035041031161105184801c110585001034074603010f400b071754a035030000d0703132000041c00d00508080181260320019088400345c10040c0d4000018020060140c00320000244a10b14010750325141500c0c82c40c0c2c2600942d051a1b9046444140b0f0000e280e1074890210054180a0000c40d151640d440006000d05010300c80e03102d4400da5040b1100e2014880d00c00c8030301c250300161110003610b2422665400a0000030009e208140e56507100003603035030f2005005802c010301c0a50b004914244034041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 951305242 1250 951303992 951304009
    0x2011101021c0e071202060301230402040e04023f160807170105011a090a03051b0a1d040b19020a030609141b0c0102160b0f070804170a03020702041505 67
    0x141d552405e0081c81d240142d0719401140c3c15180411010302106111940c0d40c980d801c4148582e030b41c814004680880c0c820002c260b0300c0e21590007210911070281d00304840680c89035800b9214030a0305206006a1800007402503a1800b103200d000458401a40e0607800b2078131050190040c0d005508051000c00461840c48400c14480c0d030584e00800040d450f0200e421a00107a10304900700841e00811305962a0703866492036001182c2003815104007a210010300c10036080700038035181c482c00154001113000221034503082149590000d0a142e01d0b102d98480c1000648010031030028805a00b003500c01d03c81d49130002e014041059200442c03290b0a00d24800160340c810108603080c0311b8118104012840c41c21240c101140111904a40c2c94601c0d000c40c40c0603101e00e98070350b14200200e250413000c00c48602c60981c4220126500114603807501a4229101202070340c0103810410942d07540c01003a18000300070401944e0b02d00b401450407440e540400c2c19148640c105d001883e000c40d10411150808080c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 951306492 1250 951305242 951305249
    0x7110307030b0f1501020705270a0b04060b07050a0b04022e03051614090613080304090507141213120e010206060409030801122301020405010f09030f02011101021c0e07 74
    0x4c0da1100c4640310b4000039620b501d10b209480c4102c4000500f524400c0030442d0360700d00303103e091105411a20b00300114101030300f0801e01040c0154946280003a00450030801d88003065030110180c1a01183d68458843c0e028000e00140da000d02c0711080303804004040c0d01100103284880c1d101c41100c8504200142c11144018161412400c600800c0e44030300f036001d118003200312105480540c0b82c100354804201e944c020f43d011051040405000802c1382ca100101620495845a0f07050000d03560300d0380d0403034044208450700c0c0803d00c828032860000200711003030180d02128059940d21240082d80301d0310b11802e0b09120050105040480703000351944c3c14401598003100a841c1484801510780e0300410200c41481442c130140c503141c031a0400c100100100441c0d28841542001000d5041800d580c002e40c0144122070104d00e00e104034080403801204540102c3e508840e8000802d00540c0044d1500400c0c030a62101955007041108640b8000202c40c95a80c0c0b160400003804104040405240050030f80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 951307742 1250 951306492 951306511
    0x4030b0901180302031c06181a0a0e220206030a0e06010e06030d1b080703080a05060a0b0f1b010204060306050a0e100612060510030b09060409030f0507110307030b0f 73
    0x90304100480d40010854903c6c203212000400790444409160004141d181c110400f990f100b403455400c96041c60300448418040b0801d04207004010904112038104c0382d1052480384100100082d60401510400075000a418420a6820340d81c1d50300246c40740e0300c02c8441201e441e42d204050b80081008201050241040403d40d05182c1030620010f6591642e0b841c142c000c110816031303031340030b002040d81c4070441a039403000701e29441c0d58283c900036040308011202000c410380340c500000e01f03910b040c4108504661a92440d01c0c6000d500b000001c01c2984001d484482c512015540c9200d41c0d5002d20050004108a9400141050810382084a1100a07910441840150f00240500041c2543c4040d013140c0d454240070388009812040040a418294085a40080324401a4407841e416821601510408603500034082da500010401102c0045402800046040300c02d0b030f200346e00800c002c00c429401a4020803d851a4100180c601200d94004460220400c3d091000107482410301030b400c8546003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 951308992 1250 951307742 951307781
    0x7140c060306040e161d0a05040c03030c0204021e03010914151215040c0f090c0e091008060c07050d091a16151a0a0605040909050309030304030b0901 66
    0x1040000e0541c0805032196100f0b40e0755044101819808000705900364140f115245242d0740c0d6441e0780034920001c401444501d1583e040013a80c01d0324148541481294010740f8440701d182140c47c116110000c130381003241c102e6401c1080311550508682c80c0c00c120361111021507900e40c14030785106d054407400b2101162440c4613030144070420908a2503000c80000c2542e0f078004d100031841005182601c1c100c01700720482c41003001c0c40306101d000b0b52403c041c0d844844c2e81c4e455403542d501e00601298401d80b4810700241c02129451824588075403070355005109040e2902404d0703211402141050f00075110005650400200141009010f00856525080c0d84c241808542d2400c2d140300005207038020a82ca0309003000503044000302c0040401141e45801400480c0e00c01403080d0b41030b0003001070858004c2000061419a025850f0100c41c0c142518480e580c1d460901d4500303560040501002203040702c0500080c8403d030780584040018000a47c050500f01105050901c0940e084030b00c008000c40308111107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 951310242 1250 951308992 951309013
    0x408062701020a12111c050106140a0c060e01061701090b070c170307030f06030b0702070806151905030102220b030708040305070f020a0b04030221072d0306020714 72
    0x1c6400b01400b00d40c04d0010400d04040400d4803040d01c15203215501c10900c0548031410703000254090b80c1030760310a40750740441d1000882c22803034038090760b16040c000402c40c405800000d0f500340c10110700c001c41c0300300100e92076843c1c451010385100c0e41150340013503039540e034111418040d8182100303800440318246522400c409844000b500c141100000210010010100d04242c0c441e501070300c8240800001000b12036100c0c54030780341004007501d15100510500c1000300781000c02250300380c000c00000341c6480c00d00c02400203011801f01c0102400c607050200000000d1aa2020700042040f0016049070b044524610017081030340c0403403a081003000d08024010803040e00e070031800c020f8005030103041c140c0c0c8802042c90040340ca00285080250809500c40001070a41907090180040d24421640030150f0260740e6020b800002c00d000c070020b06513000b40c004000c5250510000080c1e940a00f624880c490a42030041c0014007065100300e0700e9a600244000520079482000701d040306032a00900720440d107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 951311492 1250 951310242 951310247
    0x160b04060212070c0504050c03070f0809060604090c091529031b1306020d020c03010e0601060f020a05030a1806184203060503121e0408062701020a 65
    0x40c0041c04030754802c002604810700c44141070500050000400c140a0351401f0503130103402d900142e5086010561101041050a001d0154280b01d45d4a40e80100841d0703545008000240800c100d042d941c051034150b0109000099000d801d6028003081ca100d92a00c1c03a1448021142210083c4865002d1703080c4e0102d9414181401100d801019125031140c10034203806000e242803145c5410680d40d17100d00640081c550f074000c500e0b5201000c09400f940c4040711414181801c0e2905000e08000301c0d0041c0005006003801501800300041c90741c81150040c1c0590f50b20780d403856210001e05c00200d8840c070205075108a14a00b064081c103141e190990040b1a9010200d2049496028503078251700c1c80d54004604d21914401c1400d072400c0d4000240290341d004d03640110f00084410f032080040d062801c0403500303003800500140c0071103105e01494034040c00103200121001c0d494460020b600c2e0108400a90990104100c0d40110b5408414084036454060f450f440e420b1441c0c0300100300c2e401840020981c54 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 951312742 1250 951311492 951311503
    0xc060705030a03020f040b0a080403030b0406030203030f031f120c12050c090c27090109050108031c02090409050c010f110712150920030c0603160e030708160b040602 73
    0x14100961070345091101c175410341c00381c1d07009258445004100c5005090f400740e0300b14040d07400381d1002c006802d0806c00380002c0e02c500d0301000e50103900400c40e041c01004080025079002000164802e84496003800710034812007a903120b1924a00c10175006002c1c01131046c04080182075443d03038441900855034030681c0396046249410310910760b00d00003540c002c01d0700044503030a03020303c952382001c1102214004100c0207500c4805003d0401600081038414040c41158140e6845074019814100c008000d0710001c02001001c003111602800007146c580c42e01d0084e481014400c00183c159003a40b50001400344041d5821101000980440e494100e100460b9810584030803000002c00c13520607042c910714070304c8000301d62800c0780d26010348982406042008501c11201018080241c4000c541c10141ea030120a1710f525030000d42080400c038041e2080d400c10495240706e081440943d4500000241410115400418903411400300c072640c1c0e94501d0300081c09010508860342c10281031800c000e50302c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 951313992 1250 951312742 951312757
    0x8070c0b0f0c121c150314010e0709021305060a111504060e01050105101412010905071716081312050a0e0406030c05010c1e050a0212030a0e04021303230c06070503 72
    0x941c0c41616003a0901d9400d10040a590420711080300d010407d5400d0b0b0003011010300c0400705014191004c9841c0089000b141c2107038404a120521440c03c040400210781c0c8041c40030414050007182c2c4a560b9407060000101c08405040f08408a140506100d020b03a803402c0211030880e40343c1001405180d840710b1070b8020092280c40c01c450145280c164070107003481001035028250982400010f0811002c1c1c021a00c10400c0ea5109840034007091100b0154010585c0c1800400c0c03c20000713080060700c1001f03800c0d400020351180f621540320545444440381103044030b84000400005a500900750000717192000a0004d480404c07409103940c07a40c03d2100107900406040040d04200d000c184070f801460701e40517520308407152030400340c00e14113507503101c01000c1d08a014250210b503000c07421034040241d920081c125214042081c944c1c00c10030000358482001d0704440742504030040701151551000c0100481148441100300d4140d504aa203010400340105100d01010000800058030100940d61138 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 951315242 1250 951313992 951314047
    0x302030906010e0a0e16030201090f0b120c190207142b020301061a0702190e04062a05040e090c0112091e050d030b0609060708070c0b0f0c12 62
    0x40c4d128400184003408070112800c0302c0748102403215040f50205503104040324400d0b00d0b050212907070361082d00c16502c154031800784111001e00c02c0340d0407541d5280c0101d5000615003401403030220160700c0300003400080c01c1c43c400140c0c8440c1c0284402c80b0604440b400d00300c01181c01c0303198500943c6200c2d0400c40050030141d80002c01200290440d202508800094050200d190800d200c00d0310020515401c0003500780d11801048060101000580302000181c90820b2031500751503580d034869401400c3c018458045800c1c62168074000342182490440000c02240d407000c0c1d8685c17820401070600140030300091150780181e40c0c03c2c4c10503a044840490150100400880c1d955800d050408401d50401019001181004004810080d021030422000302280d201049074420540911131540100300744207810880400c07074a070100303c02e08082e240c450321449180c03503110340b1404210b806130412015140300f0203000c03130b0040300d015003880721484880300c04403040d003010700b41c410740005800000ba41184 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 951316492 1250 951315242 951315269
    0x21305031c03152402150f0606130f0f030c051207170102070605013b060103020d0209040f02071e0803041103032712061b16120c030f030203090601 65
    0x1464003018543d0090921043c1c0310080302002d40e000c468034003c03200304401800f40906514030142c41c070941a00549a00007820080c1d6103200038020142d120b00140300000c01101000188010315802d004050941d4000034200a4994a080780441f001c64026612400000e94680d5203070350001a078408031150045041c1d40d080d02c280115009200752a00940010305100000c10a40c20441381c444000c110030602503110480241e42d411003401c1004004d20300a800b901003400c540c030a8000c0c02c01c9000c524001450010b2410006045032465284c02c0d107003a402140d640140b1410302a00c280300070030250b100a02414590b98001c8a00c0000c000a0114615003034a00081d00c0400039500e4160510024901041c2c2c4010409090180302a00511445d251007075003503460701c0802c04600402c42d0448425030011a4204480e0365080098000003803011180c0c1d0a010a54240c68002000c0082d04c031201c1c0f4254a0a00405600d00508100103240c010000d00094910014805045803c02d109800c2c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 951317742 1250 951316492 951316511
    0x50c0f010207081c2c090108010506010c1106041205060627010b0706060b0d14070201271a0a02040f14101220090301060e060a0e0603031903021305031c03 68
    0x200c50f007100419a9140f500102221070110b40100304111703c9450803a003181c10f0303a03a19580c01c0d090380e00c200c803a1400640c540403602d000698040d407604851200502d030031b04080d01d908415688202920f015207007a4080401e102050501440015140d00f4180c2580e8808040c0300d0265a607036418460841702001c002001405e100a55100e00f000d0b040e104030155407851402d5548005e8420954004101d80c041c0e001315044c0350051180041d191030110740858a8007054605588080e04447c040e10320302d0300c0c10010701181e406011300d1803188202c9240141c80300d080c501e03050700100058105101008998594a4065075000009820881980f8044a2030103040745958003800b80440c5042400750140001c1400b01185400307000d00b000107070000c00840e030360340c207030055031603002c0c0c4406400c4501d0400c207225821000103c294445806012a07281230007001c070116500d080401e4103c00258041684104c001901c2400740081c4400c0b0018046e00aa0390001c0c58600048408407003070656861048 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 951318992 1250 951317742 951317747
    0x601050102060432030c011d070e0a0f050f2401080a3611090c0f07030318080a030b0136081603121103070609050a050604050c0f010207081c 62
    0x360340700303101d60050020508290584c1070f582d411001045d01c2c0e65081140d0290280440521056039245000c0182003440c031b02046d079100700e500684200031464680c25201c5006001d406290b0040690b02c5485c3c1c003514203003001080602c0c4401085480b0388921445110f160307440038100c0e0300400c06c2403000a5258581d084045a01c501201811980400b6101241e88861640d18a071041c0c3c05245202c28031940c075000c03c240d00a045503034007928402032041002005440001c1c100d0b0502c00d04000592210b01451601c040c611081c2c102c03410b02c400600703185960f5141c000c0500d04442801c0111829104030601424401003084110303e0300c0c01c902c14092403061007180310000300541415110b10480a51354a200707503800c1d010981d001c4001801a0107140c0c03045400c14403100140c000f40d4101025503403204040c0c2507000041e41c40c3d1141c071212001046060081c1d038081c6116000503d045000c2100b0300044410f069140380c15500211420820704001083c141d01a0071070022a0b0050010700e00c05 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 951320242 1250 951318992 951319043
    0x10b070818030d05090315010803040329190b040203160e0f1203030103060b01090308070b0712050a090201110c030307122115140d060f0f090b0a0e06010501020604 72
    0x86505104003012104400c0d0030400420801d01c05509442007c100300b0034104414000b0b00c40c1c4591341c0d004110810124580101305624031000403545090b6510001d41c0d9000d200d02130f22000311001c580e0b04801c051481503c2614608002540c0560640c603004210450000300e40103006c0500000390801c80071641c40400044038020001c1c60201000c05c00f5490b10360f0783d0400d02040396054503200300c03040690b014140410459604c481d4051602c41255a6040c0d1800080c1412041c800d050444440c42e00c46c0f070043c0c500c00c04000c44001070140283c00010310350815003d41c80c3d15900900c0c00851282c4001c8200c0d0301868000100b8400d80e41c001c1003ca03203200003000c1804640d001051300d486404c10f00d40080d42d078034001040c00f40e525070f00e0b0b9048410980c1c5a5010b10b41c440308449400001403142c1d00898603148900d0301c0001e0f00a410000700064070140a422110342d01e0440820404031600d01c54803d00c0f1100390300504040d81000300203542c81d580a40040c14445036015230030003401d01d8842 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 951321492 1250 951320242 951320287
    0x51f2102030309120c0a1e23060c0c150a1b021c051c080708190605060a090518010308270604061e1706040e10090503030403090905010b0708 62
    0x401d5407103100002c1c07429105d10304001c0315803181620200006492681000490811614031000c005c2140340042940e1454030030810b4079205410321200300c0e01690f60f140a4a04010504090403a001900040183c4034108814140c40d8100a01c400340b000c60307018540c100c6555156109640c813444500005803030350701c111000c1c181c440e0b5101c016820410082003880220182139a8800a0700c0010740030b66441d0804c0f11070a00188400700002c0d421b070030b111922502282600400a1500d4070341c80480c0290340465260804110014401c02050071705005032314580c6e07030101403102a541980e51b480c8807481241210204500c02e080e500d405501a25030124940700010301c110790750350746d40c100904140110349134810340c6c040580310204250f0140e5039800e0000c8540b07426001c20fa6950741040700070840d107522414035102d0444002c40a054521480c3c0c00070740104001c40d140d140903d001803482425400101810342000c004110200c942d070b00740e40105074858800c544800340d640c060640642c0441 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 951322742 1250 951321492 951321499
    0x3090306070302041e0302060703082505030907080f031603121401090c080415110c01020705060f010602071a0306041e0902120c0102060c090a0810051f2102030309 72
    0x301807203903498155008004540c4612141d01844800500c441041410380c40083d4000d1000c0140740002442502c8040c0c3c0200494a190480c803842d91401002d91098807103100030030f100000340406090100210001032251000600c01011001a0585ca85c051400c00c00e03180c0c14081e08a00405015a141409030a007106080181004c00c80c008800f500080c80354030981468028101000c03032207044680e01c00e60b00043c3c00404d8a059030b0500005041c64600500700041c1031151100300c403020300050000e10b010310000e0000b4101000c8660000c0810f9012105541c008882001a04404c07004800d150740301d00222030301e9503100004580504400c400990500d4040340304920440d00c2035200e12001402541d800741c3d40c02010170295542c081d10201c44bc05a0b110764001400039144c00000c11001e000503228140141d610b1001c2c40c54040000078543c0d03059111b404020640110740b00c1e079080c80d0103a00a401d03020345424242018007a840e20007848040c0140d010605640f0300308201d0701e6119019 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 951323992 1250 951322742 951322753
    0xb040615050f10030b1906030513020f0d03030e030705100b1801090e1006030501090611031509040512070507150c0320010608030a21061d09010b030a0b0109050a050f0c070203030903 80
    0x2204141b9054015817021070725140c041800c1c40002d201a095469000e89982c2400d020350741000503c50296008404240d150308400c080c3c0c840034000340042a1060000380104913500401d1010355202915280c040c0c074000d00804607040701c580029046600c4020b0004c1c0503a0b950100310b0230705400d54000d040d80d50801c1e1001040000562040c504103024030b40422815aa180061086200544a6204880c88440c14a2840c035081c021180c00603c100c003241c0071455004d50403025a040030100703958a811000040055003000c1d401259030311120300c2d1000c008149698050221113001041c00703c070102804a00009500940c4680c01800800d001c076911441411001846041610181d80d42000e42c4c98042071070241601500d01511040114840d1410040500000040004062401d47d41d00e40c240500151002e0001440b5035029005c4802c945d8103001c008401c1d00c80142c41903070060b140800b04680c40850700b00d510b4000c89500c0b40aa07440038580002031030350041000c0d00da0300d401203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 951325242 1250 951323992 951324019
    0x906071e0203343204090b1b1603030e16030503040f050103060b03041b030b07030b09090604050c0f18010b030a06060206010602190c09090b040615050f10030b 70
    0x4041c050340c800d500450700031650742091402e03c00d030030343c030382c40341c084c084000183c0320f03503101c03030341242d40d1041d001c45401c924880c0c201400140a640075000d050b43e034003c1001c00c0c080c40c124480c0400380d0031410505c0c61440e01070300c0c0c0709092998801c024050109a41c2e41461404400280801ca103001c0b0f40344070840d031540d12414010340ba50303c603104d00341d0340c050340b190001202d501a00841007290f0f03840c1041030541c0e90f00c1d01e800007403481021348034100c8000d10b01c0100c005101003480c0e0b0b028610a90b00003030902c06400c184188003201628402c800e41c001020000060b0000034043d551100035206074040d4152000400c0c0d240d039146140000641c07501002068005140c005948110800300083c04200d6840f841070780c46203030a00422006801c8481005201c1804083c080c50403841000c00e40c0c3c0b40c03503403000c9400442c3d0740c0000486440180030103200900605001e0360b152000701d54110300300d140c50803000614515228000c0c600945460780071004aa000c0d500c001c500460180040c11000c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 951326492 1250 951325242 951325273
    0x1a0c040909030908061e0c090a0b070804050102011a060711040b030f010506030607081909110909010c030f0221100302040c0809060106020106060c0f061e200906071e0203 75
    0x8007400b13241000d1050f10000303501558401d0006506c0742d254101c418817910307000e40918850744100000d5401203944040000d001c1e64042c000d00c45940580c44042e21541408002829901d69070800102210682d001001c07030740c1c0754000c60304d909038842200d52040c401800410701401da00e41005625004003104600c1480040d000300e441510102c065503041d0356640342c15030b0140403d035030840807000310500312039541020b030703014064442c0034210343d1080841880020f520180101c61003e016512005c50000e110b07014010880c040f51000010350900403945640d034050140080d6840700c0c9482c030004100b425242c46203c0d4081c6030003030300c00c1c8298003110f0340142207014140c484200900c01c103800001d80c54410320400058400329130311354610309066100c407060310015a20684030300f42d844c228900f843e001c1021000a003000c0b4034000c101108148068006440704100740c001054080019040c907a075440304590038a9032140800448040103402034241e0780041c03500a40610401d44907502601 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 951327742 1250 951326492 951326507
    0xf080706020106050315040201230406110c0a240905030a03052a06040212100606020616030203091005190204080102030a0c1806120e19030215041a0c04090903 70
    0x40d036580081c00440c1d034660034183d0301d03002c85540361290409480030600541c41188c9401c0d83c03000d814807050785000b0048000c820381e0300650180000c034484a4020070340e0701c014880108402401c840411520703142110384912006807225810120461409591046004105a8004c0e00e4050104c4500c5021864058880e03840303c0128680d0910520111455807054800e04807481000c0c4060031080e242c56092000c40341c040020030104e4041c2d0309101c21a20010700c1410300a14040e030042c425400c00501c1802010090303002c810815004208101d1540f40000d2856035207425090005003603030750340901342101c80240c19548081d500016000980d240150041c60050402c0b96003000030241803030054440c18500703000514500f165402c20816107018803001d81000281210100ea0718000171545410f10078407103083d90800c0c2001403940185681000000104500e504081c01d40d400c150300d4020041c02d4042100c0002200000026105400b480c1601c00400820806000303801c0c4615010340040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 951328992 1250 951327742 951327749
    0xc020109170301031a01150309060e0f0105180111030121021c030e0a08061306150f0e07050a0518010318061e0c0f0315030b1602210a180f0807 63
    0x70380c0401c52170100d4010300c8816412108480b104403504190000150040c0c109040b040e1145580c80505043da01c40c180240504154620000140c0b8039090031040102d0b101800154180c0e0725021640c1c041010200c1241d046d1800c40000000c01c0014800d11050031404640c000d400088841c000b001942c00e00d00c091400b5413181e241c0c3c0440801034414410950305611072902103502000200b51851509003c014026020348004555480081d0749100e91402ca5841300c0016900c041d4100714802070801581e4210400c2c1c0707006468200320001c01001e40c05101c40c81001451011000f9019a000c0e6011504940e02e0300d03d0300008a0840c144440185080074400302154110100c1c0003c0300010f02c01e0000801d003e80b540d10b61300324810004c600422109041c40701c2a1041c000100c049601c445070b1610076424030300414551070700d1880007420407820400c141030420030311504041e10600300040c0c448240c81c0d480c021010b05c0329400c1e00010b200181c1e00040044210321800f0580c2000495648140d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 951330242 1250 951328992 951329003
    0x105090d050d320f0a1109042c100510030f02060d0212011412070f0b070515160906030b0f041a0910050a14062a01290102031c0c02010917030103 64
    0x541e079894050002d49000054000b15010f04001c600012301d8180c1c050440607032000d06652540d482041244182c64064095003580e9101c40d00302004412203020700341d4042c0b0f03c0b003061b9071000e01d1940c41a0044490501c000d00c1040007140000210b040c50b41910256208c80c5503c0240f03513034510716803207130841030b100c1240a0140420100280c682c0042c00c2d4080320301c020181c0303040e146003030846102904280822100c5000f0860a000c1070f1b40b9440700c03e0301815003181c0443e04900e9040c00034060304d105034404020305050507901c0b40203544058020102e0b507003d84010a0060b0006a000ca030300b41c0c0941015800891281400109584070081c80c06544090b80c1c0403544c0394488640c840e01100038039425902c0030301045a0007442503050310007400600003a000b89000480f51441509403507034594040d1070030b4030f044000550140f024910381b01005c07082c00070b9031508040a2454506d0300c902501d10b4070494680703200e0954140300754070143c00d20390810200380403d0a241b00c8180715510a00c03040d00d2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 951331492 1250 951330242 951330271
    0x15150503010e150901202203050d030c1704030c02030f0106180f0905030f2a0a02010c0201111e0606040606092d080309030105090d050d32 61
    0x9540c14140b04190b050000700009001c14240b40b12490341c6000010003120b03480d52580c12442400842c02c129802c04100c1c03108980d04c0320002106140b0180768a9042032010820702000c0010035001325014000001500e00880d042c0c0300c80340181c50280c41e105c00700c0b01600d600c000300000e2680c0141d41e0f017140b5100300d05030303190120080340040c261a514020f40c20381c40404111550599655844080c80c81c400c14808110460a034a07400d0668100b140701150b00c403400540c4144001d120044864903002c83c1d04908810b542a01c211951250903150013810301c44555070b60015a801103c50144c000c9983d030440710000d04415400380e032441c801c0031040c0140704440c00300d0202d01d000c0c02000142c03003130365444049440ca41030300828200c2d482c1c1160302c0e0401c05d2000c10202040c0600c91381d005440040010b40c0d032100d03d0707070906084507001010300c0e03015044034028600b88c81d80002110300c14007000300d001c00c071234030081000030303102002842010007411442c249954000444168510980880d1681c1c00c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 951332742 1250 951331492 951331499
    0x30e01080705040503120c0120072603041121010c02060105030114040321050a061509032a08011814060c12221518050312131515 57
    0xb6060301580c0213496160308000c40920101c3c9507000504148141e45001040c560410f800340c1c600d0400300071403038292010004412040c030258181d4411501d00000050003a0759100c3d41101203800b01400080150b0f201031a60714450303650798121118101c81d03000c80c0c0034145400c0034180c02400c1c0d5415a02c0980509800040c81e4901803103050140c030309010100c2c549640e6590f00300c03a05214a0300e240d440908100c22118002011b1280038416040c41200081440c142000e002c91007075002d412404008011405000064030b01d00b034a400c0c090403402c240d200140540c920076001a013030300800c04941c03804441034002804100c101403141e001c0c002080e030b0161540d014940b1580100c94040741040108890b005965250038042e03070041a23040490344440c40303501e022005d080048802c2d1901150100301c0489140688140c02d40c5a44500c5c1780f0b91103410a43d04d603034480c0143c0340b0402840c45524005050381c01d600c60540501980210500d02426000040c54002c01ca40c03540e802c0c58410510010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 951333992 1250 951332742 951332747
    0x5030c03060d170904150b07021203210708090c010e040c1211030f0c0307050a0c02120607020d02120403020f31021216020a121e080a0b0415090216020904030e010807 73
    0x107100745c1d400e0f2034805107042d0049d001e0000c16180d12101561501c002c00ca03c05015910384600c2403600d498021115250802d010014208200604202140d0300840c0d2002c820780e80201070036502c16420395021407090518001550003412180345a05c0090820942c0c100c4020844025489444c041c14404207988403c907031840c3c1d50204450040204108014240c5042e001c1d25001444a20081c00e044510750690b100b94144003081d1054400750303001510101425405004580500180100c018107080c0b464002610070a00300d00000e0259611a0344c40e2480c032000c1c54600030046d20f543c02d04512004140000009500401c4000d0700c1c44142c0c0081b0399000000c40d40c00c0e0380990254003c11810100303845000328a1030340c85200d1300703000c03030b00002c1003035840d0683d002c41710001c041d03c40c0c00940c54181c41c0c5c070f010b9030031500090348254508181d0000d01c039050004001615100340006842d40700152120004a1038100042e510010313800c01c0104042c0d01c0352442d210b00d02c00382e80300c60b101d8403001c005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 951335242 1250 951333992 951334031
    0x21e21251505071a060607060207030c031e020c15040816080706020705010c0b1513021e04060c1b030f0c05130923030904061205150705030c03060d170904 68
    0xc01d9441a4001c0c3c20184d1084113205803c0751006103032a01c1c2040b5580e512089074881c030b03001c41c003055030448038134241034015520100304511000001781d00035215000a440710148004144940b1400c076040402e15041c034165000f40842000321030f078201186900c0000c40000e4880d0880e244540140401c2491012440c04201c1e0010303151800e01590980d1104810100107004542071120212800d4943e0f1b070380e14861281540e8600010381e0350310800040400700521780507141070036004201c100409a070000500c1d81c42c031741008150302c66440701070041c950182d0340c1e80b0141000301c0103074040060280021039902122000c41e514141c5241c072501c800305481c0742807006480a0341e05c00d084445100d01d080d8010820840d102130340d14082d60140080c0850f55150480d04a002c8404d840400304001000101044030b0490340280551400380d400611510005102075000103010010914940350381310042d044644c04513080c0300d421b0480b0300c01c20060300304100240c450f07030400d140b010414003203210 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 951336492 1250 951335242 951335257
    0xe030c040f02090a0605091003020304170c1221092d1e01050a1808090114090301091407171c0c08070f021e21251505 52
    0x64814814a401000020200300591505290b02009a082d8aa680c00d101e08060700c000e840722610340e0003410900503a0640c640744042498410020301021614641030f00729065951020281d81c1d0300c050681c1414103a117200b010010b2203000c1203c18000f404c06a04c00003242071080740d8285659a8003130340d603554581e1214880d00b08400d0070500e5011408034180d03105400e0792405c680810078000c42d0301132007601601e2854501c1c0d544805010a14119000d2a40c000411401050b42c010703054481e4501c910444050505000032180700c465449285c208ad1001c000f4014001c100f503461b90f00302000c1e10b8503490600350741d5000b0310401003000d410b410350001b001d0107440c004107041d85a40160190340d5200000c0318081c88820b0710150300050f180300040101512954588001948520610149004a505144e102e141400101216444000e01c9201c01a14210b0741d48220290700070071803c0080340342c502c294003065a41c01316010319407403900104991420050080345d0901c034100311020f00a14a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 951337742 1250 951336492 951336499
    0x90b040c0306050906120313091b020102040506040b160b09010504032a060f09050a1a1e0a09021908010c0813050624130519090525090e03190e 63
    0x80843c5d003904042d0203c01001c000c50701140d02c0d146001c1440581462290300c1505616150303102c40043d00780c0b24111511142240c00203500b0103040000096181c022400b42d10004400842d501d034240d2042101501c455030071040503030180c00e0506c1e055000c0e20085600b900864400d49032400da58075421310b0054414050207814006800c0e65480c00003503d4070001c1c1c0b2899540b64070803080400c406100a8a500388142c11010304030f208202174010309040103007000515906114072405c0c0c2c81881111940c031040103903000455a04520000c0d105107000d40c9600c100351b00030a408140c5560561154030080c0303458896200da44d680301c06414006801010082080d04060301094004500550142194102000100d0094050004100c2d10100f14503204c5200d03840d0380501021114071045445d504840a00c01e00c400111501c0b1159a102440302d8401d1036480c04001070505001600f1641c0600440001404071503040d484541d0f6942201c48000b100c1c2010040c51440180901032644541c403014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 951338992 1250 951337742 951337759
    0xb070c061a061b0a0c0807081221040303090f060605040b060306060a0804080408030c01020405040b120d320d11120f060a0914071e1d03031201090b040c030605 70
    0x1180804001c544003c0c0210007480b0303003e5043c0008904c91558070140000700700030980365281003e910b02c0d103819400018542041081015120b8801c0119606040c00c16810305544d07071a1890110001e020304c802c06084a085e00c40d6031402c116140d0030003800c07601d00b101c052020211140c01c211051205440f640c0d48400c04104d00311619000f924160340c402c3c000c0c0d1000d8181991400101d065900412042050382d40c001000d0040c0d25091286021010060708c24020050074030f14640e6590010207146c4050111300b607090b02142c0081000d03000b0411100c0c004400c0d15006403183e00c09508031621002d001410700303100c43c1400c5406404e0f50507114980350088010f80398202600011200030f84181c1c1c00c00a04100480c0f0b0074440c1c002c400f00b41203211080e034228900040010310424800800840791103000081113085030340140c0046c82c6110b2030440110b00d40003440080c1c954843c00000c0d41d06086680700019060109a00c80070707611000340c1d414014100c60103000c8041352510b004440d48441d02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 951340242 1250 951338992 951339007
    0xc1905092a0f070f0218100302031e0d030e0c041d010c08061e0102030d1b0f020607050901050d0e01060e1008030313030804050c090c070204150e1803070b070c061a06 73
    0x10845094461380c0068190a03d24038034010f40304602c03400f22010601846424010800c6040c2000b844400856408403004070915071f100c03194071005010702900c10951203840c40c140d05030003886010b4008000030003c02c010f000d5005807901850800031b11070000d512b030044041c43c0300e000e600c050340f00741802002c2c1200c0004074021200c1c09070382840b007a030441c0310034019021600c056109403498000100201c903410403880c140186515840030100c021900b102084c0120250820240c0d0342c1480300f424010b0302c45600010000041810300c6500c807040d82041000201e0380f008203000780c000c10b03904007000100340d1600c05907680ca11050303540c50910480a001070001c28490200280c00a10420541c1c0c9400e9079600010110007059a80b0f0080030000500d502c114607051160511014028150410700ca152841040c5500c038000c2903045502080d2140005002e0284102c8808a80c8690550742908080078024003909071107402300c84e030602e860380445000b001c40d060b2200701720380102150700c0c0012 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 951341492 1250 951340242 951340253
    0xc0303050a020a050f210f0402030d020f0d030e0a0c060e15041508070c05010c09180e07051512010816060e03210d050f07020d110c1905092a0f07 64
    0x106d41d41d814040b10b40d60703809500b0501351045501034002803014840d91b040034010181402161035011044d90301440050110080100385194069105e0800040e04907009001600781007402e903008001e1a00c9420100e4910340021102841000035150b101e08100421a800c026110b24004d00800605e0850303c0c0c0f080500c11005198083d41038604202c1d00c2040d5079030542501c00382e1018002040c50780c1d40600082c80c2c80c00600ea1000140d078410720180301100c0359641c90328070f903004150060003a442c000c0613808089040f6004c080c1d010138200e0156075218051521150306401c40f40156440200009800e0300c40d840c801d83c020070080150540c041d01840a0300403000b501c05515500e4020f2112401c0c05403903211b00c1d445070f040d4401d031305110720b44524002d040c13100c0c00c03980c0b005001080602400d4907500260b400c2000a064464241e110751130310002c10086050340c40700381e1201c2c092003000420715080468200e08800980904036203818100030b159940260030000d040604284040c030301240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 951342742 1250 951341492 951341497
    0x10c0c1422050711191b0909120e041404060e0a02030a0f0317070e0f0f04060b04030b1305070e1e070c06063f23191e031e0c0303050a020a050f 63
    0x5050901b9100791039034515041d0280c0e9540300b0b05840d03460115801044540e007100c510554548101d800300402c80b0341b03480120501601601c00f401080d43c450030007400620407c4500c1145400800715692000649060340d00c0c40850780040700040c181c01002522010701c000c0c00da010f80c1890705c4081000310031400784854441c407914010381c404120001c0d54000e0300e9520814020f030900541c800d980d207055081183c644080982074071150341c0c40d058054085500454240b050b40e01403400c42e03a9031b454141d120300304400741a104680340500d000a1118481d0000441e681883c458002409582c0c0c5d2410310181c46801349100000028000d600113091303920b00408001c00c4103100e414009120f059889000900004501148034804194042411070f0f800701f00004181d0f08051100d09d41c03404684d103040c46038407940d004040714403c0000c48410075000d4034450481888050b0031380e1304400b8482009090503e080b00039030100c0d2410001ca480301003d402120103132001c1f0b440d003910b01a00d402c2c0c1c03000c0e42c1e1f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 951343992 1250 951342742 951342773
    0x510081207020a17100c1205061206040209040c031209090b0a08070b070c0b12010512120a030b0d05011a010f09050d17130b040311010c0c142205071119 67
    0x9001721240d00b80d400b851486007000f14021951010307440100c03600d41004640c030290602d0304c900e034524915038114100091003a403060b0305641c21303c442c0e1580c3c41d00031103042403900014090038100301001504e991090340c4004440800005000300350101d4184440c00c45a40100c01e005d42044900784112580b01d00200b0313600740306116a4505036034840c00300c00950000c010218008400328010045890084041c81c0c1840c2854080d0448070790110b05512544103164044040c580c980c02003d030b45969180042487c290420000d114010100302c404c40000c1800742207501140160380344012a500c68441c60054442c090249200004030780c889064003612141d41201d40304003017080c1d0540403800700c981e000a100344400f5a071200c1c00d52615800c03d041d0b21138520704211840d110400801c400380801c10440c4c1203100c0c4003032500041d00c04901024012030082481c0b0039000b070144907969a60340404c1c850551a80c0e102e19032840303c040340b41c5400c01c510304000304601540a2070042022041c105600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 951345242 1250 951343992 951344039
    0x1201030206160c080a03081806130206071e061d1009110a030b06010210110d2a0804020906030601120605060d020a0b130501050a021515040510081207020a 68
    0x2ca0703071950b80c0c201d40310440c0c0242c08207030002c44507902010303003020f159034102a020700307031200340c103450603150740d0742c02004103d1500c016448000109544601d0111a1002e03000804401000e0260180d01d00340d400860045940c03500e4a58448200070600c0030140e03d40c041c1001510000301114407440c042c054a49064031072005c81045441d441e03a031441c07403200440c0300d001d40041c2494042c002900300075400c44451030941c10800b80e010b651000200701c03080e0507031000e80000e2140c0e4800c020403910340000d51040e100d000f04120303400f08680120402c1e100710720840ea4200d0f140d0b0f0302030915868090a1080d0000302910088400000d00c0e0b5802c1140e0110001c0c0202928106a03000126a0b0078a540a038031320300740029258818020360b01c5404040c010a0805034a880051800250b03114028805a207006480f400071922002407070700c1034484071000800c240001e00745039050a054031308034030031041a40300c0c6185401988140406944141d900241f400070a94038124444c0c00721010076a44215 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 951346492 1250 951345242 951345277
    0xd1d0d02070b0a03150819110303030f0c0c07090e011e020c0604030507060209030d080f1b0d0207050c03010609020c0d030c1b02040e0a060c030e0303011203030b130c0c020a0504021201030206 84
    0x584480807c0071100c8101c0c4502ca2000700304050400041c00703103200b000315000740c000b001007084071b40e400840d481d00416070510351030b44d8031034070554941030100c190403800c044c44c20031205000e8244150804000b1100b144000d040c21080c110025049100e100c01100c03072900700c00001004a8054006000ba02e030090401500d48100c2400290400000000c00000f00701c040c0140710383c50030030b21005580040c1803082005128100903d120560182c1e407041c6104640010311442000014020a2803000d0060020300c40c658407088480c0181d001410740300d0442c81030000080000b4803c0c041d121444201c3c8c2c031140c200e402c00b203920303803040c80d0188000d0745c1142c3c079640b002c091500b00308080407005028000c00104010440d50050a9403901e0078800420361003480140304421041155008996150074009201002c810104a0041d070400ca08000c00b460042103d0400d500101c0d041506882126800420786e2500c08100c102c0c081c0d6040c503c00c0c0d45901c801840141007010003000128402c040c03592 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 951347742 1250 951346492 951346499
    0x120305091e070b0a051902010c090b090f0f0d0c0305060405010e1504121b151109060f13030b0106020d02010b0105161103010618020d0b03010203090d0f050d1d0d02070b0a0315 77
    0x6d40240607842100010b0390f5039000011229800f2a600d4094201c0304c036141d2034015100c002480900c20601418802c1010303400d825815580d40d0381d80340d0300303507400108602e58594a013000e689540d000c440035166075003040510b040004000c01ca0400d5120f025050003556126030b161401002c015400c20000d000c03042c502d00c2506a44103d405a14911488510380b840c0c00c0100d9078400c1c0c5002801c250312181c001e0042da4800d94403c000e9035416628000c0b4691504bd1180079042a84111b62025001a03c0100045100341d400b041c404c4013504150000e20541444000440e6944261026548400c220440d0364000900b405a0910070003030080002c00c48548808000b034602060204811449500003070700f1401c03908a00441403c144101c0086007145000c82c50310703440b0700c4d000749844108072581812010b224020010342c1c48106031200100101c0380717051034141d08101c0c800b40c40103541c4914214100601e10028550301500e43d114200c40c280302e107002c000da015007200351907032510300700814010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 951348992 1250 951347742 951347767
    0xb041101020328090503010510210c0b0315031b01080403091509050405060d080f03100e04030e0301050603120a05090604030f0f0b070309020a0e060d120305091e070b0a05 75
    0x803d00e111040003d0844925800140031000700b640f01d14083e9050604004814620b9981a001c171071a1a0f50091840c00c04a0741503548440d00000822006c4883ca010075211803603000386102d50502d0724900c0c0311070b8406040690b01c0170f28040c0c1042c807034030040740c1a201d544144000b41c0c00600c00d0030715801d181d403544881054009079015007400149a2001007081c1d241c513008054100030151405070034a9501d4841856900c224010340400000000200321029403103e403040c02000d0880500300c8500306403030020003072980ca4500034840d41c00c05001c2403003890041400300d40c4c00101d0f038100b0326042d881740307080c0d595802080b1000e0f40510b0522000010840680d12814454801c04188800d414189850341c41280c0c040d050804041c5404414030068903980303005410344216055182c0c0e56034850001500701f0413080c000400c841745034002c443c00c485e01604542d0098400320243c4030042c4030740c881c01c0c40072050100c852405900490040101142160091420780b03440e2900c20301e00148406107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 951350242 1250 951348992 951349027
    0xc090906020c0d08090d050909131e030c020438010c0c090f0e07080d05251209080102180904032c0f0d020d0605190f020403050c0a030b0411010203 65
    0x180c3c804120858200710180320284000398031901d003070030190304001965000c19584003000f00030400d140030b00c142c0d074010301000c150020581c3c0c2d90800030100d40c900c0c9207001400300d0311240b4202e0086040440c003d14903203003504000c500c04d00700d01440310814815050003802e1004004401d0602c04002c005001103041d07810904050182c4140115185c46081c03a40012a0700b100c44500060304031000c240704d01800420f1038501c442262034402d0b1200005000949000000000c0021140007400710a007041000d81c102c16803481d82d0f0702c030381000700c8d42d82d00f40500703070310620441c00b00c0d00704410b50300401d600c0e000002c59081070080c03418110b0b40c61110400c2160610580c40f11041500c11450341038145001034443c0d0101c10b060f180c0c42500796959022804000ea00d60300102015100c4000640c3c04048060841141c41c10710400d00ca10008181100001d501038081518180116851003c19003080e01e000780c02ca0703a001000c01391581d1603854016039840d1880c15a030450008014010014500c0d060 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 951351492 1250 951350242 951350263
    0x40213110a020c030c0a0b040603021c1e060b090604171207050f0f1614010c020310020a020c0a05091b120106260106050d1806110306120a0c090906020c 67
    0x103101e94840c80f81058a0412110107251007925074103428000108610141e900321001401c025888801811654000e07140c00c00541000030316040c00d01d00403881c01005403045409803801080320540b01c40c1181c03581c0c450310803600e8100c80204400c0040302030b1102900425401001a11b0303003070840e070035429481d0b03210300c1007940c0d583c0c4004800490340e0f070188552511170750440c004000f500320a8180e11820106480380c070303100700c007040c5020740c83c1d034041c107043c0454a600909a030003001404004200a400c040c450320018455403148460504091102c503040d6403008040b99240d94804002c480c055141c0645100c8400c428070020203140003942c0741034080c003081d0700c4d820101c088120701000b02c50b00c4003290100215403a00100072a503004012034440d00c01e21134000c00d24113142400351180340c414150041c03401c2d00c0c00140c1d141001e1414003460080b20708a40d400704010344800b08941e9a140004043c1c16071400e6002080041242e034040071180d44030303440240c1090001c04502c0d007050222038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 951352742 1250 951351492 951351497
    0x51813061509031e0318080d110106120b0c040306020711010f0f0804110f030708010b1518010813120e1201090b0c03070215010824010806040213110a 66
    0x2403003441500c4008051015106051038400112840d60f1100a0080f07500340a01e9102244c07940c03600305043c07150007031359802402c69400c55030341c82d982d140c0300da910000300a4030380c0040e1500301c0b5085244010b018080440740419049840030180b62903c62100340d016000c25000b80c03040000000007425400900385040c021140840711040640c0050540c0030340030906420400c05039030700e5402c0d54024003029005904400301c400e0001408003c50041012131404952500c10f00c80d00240100054114202152040e200990000c0c0c6480c2115514096150b45c1c0c2111004000c1031017055110310902ca911100b508003100042c01141c60f45001d82c500359601100003044114984130340e0800342c03180142000b2800c020400d20040e40c45400c0440d5018110031425071000000c1489107208001c00a52450f1048a004035941c0d0381120382e0340e0380401c1d1503488805280d1a9000c14a140c443c10750380c121800078000d80311581c1e840c1d00700940c046024681c4204070b03950380180108002e881001e061401003c1c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 951353992 1250 951352742 951352751
    0x180a0f020a090506061b030405041503050c0607030f0e0402160b07021501120201050c0f19031215060503040c0e01060207061403041101110c10051b010507050901051813 74
    0x340140107a0000c25048006801d0422060003065103030300c1d08540d9000c820920800361840103002042c118030984c0d0010b076001c0c2c1822881c0341c040e0154400030040381d1240048035443c203128400e010003070007844005400f14445070035100740c681c040c094004614000800045c40e004072205d1000c8401103c540c241e41c8110320808101d64240c040040300c4240200204504980d8507220054485149a0000030b04111011a10f0b95409608010091600710391005540290503d1802c109080315141c100b07a0010307807849140c0030140141c1c85034409040590000b501d26900700744081d1260341c0081d00860b524a41c8143c0044d03a074004100c040c1c041c0005602a0003c80d2410384010810000c0e1003542c09409810400d00000400050701c4843e035200a081082480152441d480c2c2040801e00403550000001182400d8050f4403100034269000c5c811703540c05800383e140c4e2886080319012541039001c01e03020495170515600a5001d04801c5039813030021000c8007050000718800700415030408a1850300d5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 951355242 1250 951353992 951354023
    0x151b010905150906060d021e031914070b0304050a0605040327061103090906010c020a08011b1d0a030809060705070b0a0e2215080a050a02090112020105070803180a 72
    0xf0302486401110403903030b1080c5000980c002900010f01104900c0124024823030b003003155102070040003480b02c00d10225510034456030600d41901e2070480c0b083c0810f80150840802c2c42a1402d00b901c0c003c98000c0001d00a13000581d8403940141005001507040c058240c624540d103880d9154203040017501154105610380ca05100517280c0505101d1425160b00281324014864490692269001e5400d03e0405a86d030042e0011508072022900100b100e94281700080c100c040013104042c4903012a992500c58108184200101c61300600395055806001d9020800c08266040003814035030380c001704040d280c030300c1d0f80c3d50341450400c181d407215800170780100b2451324580e0410621044600d00303461884844601031803000180e00304c10707462900d0507aa140791449a400080303c407401751221108842044000e030401076603803040940228070031000500041340726501c03681450344256040e141d050400116075506013241c1c100400c103034550510110400c101c0201007104201680c01070340c003000b04812 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 951356492 1250 951355242 951355261
    0x103020d1e1b0210020a0521100b280e122b14220303031406030304080a0f0f060903170c090907030906140c18151b01090515 55
    0x10010341442400e0980d908042c4503900820390988104404070010390300c1014140686031400b50140e620b221801d80b032540502c1d01d112403851401034014000c0b101c00e02d42d6500000c2c02510812401d0705140301640c205101310903480650100a0390740d82441d00c2c00d102c000011500365551500501c03000c3d8400c4903014494600c4240104000b9001a02c4850600040d9030290181d45441148114003000040a4146031501403040350607407440540d0304c03400e079540d0600030060205244200f812000e4200890480d2a001046030101c926810242c45141a42c3c0c6801c958044c400400f0b90710340380710f03000d00800106c01c2d100b056a1309200ba02c80c03e90030024400c000814072401040c00440034800c02081c0300c076035100b02c820356000c2c11500e808560041d00e40b0300403000e401c0f42c039080c16454200c1c40602c080242038102030541e90b940888218450342140003000f44162480e04059040403080182c1200f81c1c0382c601509966040e0f07140082450b501d035684080c42c1600c5601e40c0b0389541481014000c0b01074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 951357742 1250 951356492 951356501
    0xa140907230f01180906090515030d1b2904051c091a0c010c0207080d0e06040e090a0c06020a14061b18060d0906060b0f0d0b0103020d1e 60
    0x81104001d6800d01c1c4201d02040680d540401d03000d06001245541c9140124846180c1003d004c040f0420710405640301040b10140005442d0f0190000c2502240c0da900d040000d8105c40c03201c1156030b2003c1d04403a1000604079040000e8099030070311b01c0181c815449045030b014070808602c9800580f5120b26060030203070f043c0303a00740380070714a5244107a4000104a07071240c000e900f030782c2c050b03503103107566108900711180107100304400380d080d039401c03d240f21100603008a0020201c413410b4050300c49400c44158211035280301d4000856000030240810301c40c82e0500c19245605c40d2881c403c43e81e44080a45445e50040e800380c0c00b030001a484542c46800b0400008414007500d503101b40140801e0400c0050009490381d00c081240c10b44002194a00010070607165861030800c026104581d40c88039080350002405036100305440742401d142c00042d2a4071410111085403113503850103800e080a100000020301044519141015002c0c080d588000450b031007802c818582c0d140042080b50302e43c03100ca000b42d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 951358992 1250 951357742 951357779
    0xc0109082d0109030306080607030606271a0301053c010203090d080409111e0726090a0504050603100906060b0a09170c100302030a140907 61
    0x10021080240403000a1003594031001c0006078603510401c1074101c0c400d0800c1e01490005582003040003002c0c941c01da40003030280c5000e44c0c01c2e02c0080c0d54008060b019a0254030501c0000b0340e10580304601302620428408080303019020070700c42559100d44000e001e0410107114124810004010051fa16205103141101e03c8813440c011200c0e00c00140a04003941110015441040d00c00300202c1180c0c07083c02200c0c401d41c0000c1c10b0792800c200300d0602d5010398016004c1d0380d01980c41c0c102c8a07000010340000340c44d040f001c00b02001021554482650100303410900f000c941502800300d460268843e6100c0c4908441c4480462a40346d024440401c1003d5583e503209600075403515040c00819100458412200c100c20380000c80c1407052460050020265644440324005000c1003500310207900507400000c407801c1481c401a0584002c410589072894441d40a0780f054403162020040d5000390041d662116800d200010380d440c40c1c2e4a10104110110790a00302a00084010300c5500504084913098 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 951360242 1250 951358992 951358997
    0x2101090b010f05030f0a09062315030c01180807230d03092112020102030429060108091e030a14030f010b07020319080304030305060d02010c03050c030d0219020c01 72
    0x1480580307001d000b5100c040c5c030802184215000190054049400020710b4070380c041070801103806681211100000710182c40368600040c40040360b800c010740810811a40c4004014000800c5040c2c019200d5504110700300215500120001483c488140004001042d0389084019883e030341071909044a100351001c81d10491030000c040b004242c1c85402e032800e84115040082c0000f00310000c40c2d0350410b564030001c00818800c0020070020754190042c40c01030344600082d0b5000e04008a441028002c0b40c0d00302000800c00400192540d8811458541c000004000340c2d58101020860010384040c1980301d81c8481d40002030200d007140e44015020b11031207101c84a40d0942c1000f00c809600a0303011320610301061000f182c201d00b9580c0a20030480106144122201241186d05e0f14519070340013120280e010928002c00110142040403000c0d0440368146d4078190503401560302a11250801c461005151109101d8421451b501e84020540b000012200c1c01590018130720091034480200d445504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 951361492 1250 951360242 951360257
    0x102031201050909100513021512401b0e011a0f040f0311041107031206180f1109060703051602090c07050601090c0c060b03032101090b01 61
    0x103103a28825415200100c8954402d074540700c03541d616080c030340200d50030050301c1c140a0054000300801c0300c0c20420310a0b079418201c01c0c81e08921a1050144101050f01c40c10782900007513841c40550900003442c030301d8000c51410110714004020407070080340b0784500c02c2c14602c150441804618a404207100306000c0c81c2c16407545c1009440c003141079040c821440003030403070200c600c1e280184a01f40d03800c003920b0711104d9807120f65400801d128903405110036202100c0080808440d0700705401508440003140003050710702841c45e6412102d940300f20303880203c40307640d0358404125490100d199994010140c036001c110078032520091000c84110502c005160601001222216103414095407011a0141003640d1100c420202c030124020006000940c040480d0041000301c0300003402620403140030364125500c0340c0e20b91526004a403030040880c1c1c003040c1c2202403940000d010340c10506030420003500b50ba003407409486958800c034680742000c40300c3d11203a000500010140e40320f00300c4850000d182c1034a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 951362742 1250 951361492 951361507
    0x1e0806041b30050c0406030b0105041203260a0e070f260705030106030c0305010b0409030503060609150f030105010f020307080319091403130f030b010b070f0b0406050411010203 78
    0x1010b0500031140710003150003414203005844400c0301d40030b070450001c2c40148030381c2c6803400e0464103a5105004850109150001240255120b00b01361070a03500c003101280413480c0a03440c240d074500c070745820400012006031a40f100c03401d0000700c0e03e0700404030314401040d228602000c0e281810003603040780007460501c001c1040900528550002010000000503002c00d4590801c0303802c054890b000190958200389000080011032900c00080342c0c0104020084001d0800402003030341c1e45c80c18040c00240051003c1100c83c40c0c8400144442e51b001092054254414940b030701b140e80107200107140102011004001d1542c101c4244010412548081c500d8021603607200c064078080a00140c01040089042040d81129940b03c80c05080d002521840800344440306e050341c95002012075082450040d10019007101080045421f40b9401007400c40c1c00d0382400c20b018105d80001e44141d03103424070950102d010038504a40140594050800442d45144c2030800c040003c2c101100c41e811540100b0152 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 951363992 1250 951362742 951362747
    0x1c081806090d2306040b061008090606040c0e04060e041a070c0f0218090601061103090a03080a0e0d05011413150921050c010b0105070302030d0504031e0806041b 71
    0x30010a40c042014810a40820004290f0101210200c10365220341c0060105110078a8025845500111051071000e00708420441d00c6039010750309188103078042e50100306a868a50444081a0000d1504000460010b1f000400391050765100d040300f00280350a00c404d110112141c114441070311080d800e000d04103250010050300c002c030701c040c01c13124950071507208564400300200d43c000850310142c0d05030704110040c0c80e1254000c0c8070316000f241c2908081c1c2c03a500310110a98407600c1008008655240c9035403174110582e070100000c4d00030400d28408582c030a6a4503c400d200c1a80244000640303c45082000d82d107080c0d01a0101182c040100458800207035a001c1c40901515007030004031b44039489140001039003c20045d40e9070107540300d400760300d0350381d5100c0c000c1d28170041240001c6c00024280340c015a402c0c8034803240500180c00070802c3c80201c4155420440c2c111344685000304207014101050301c950b01400d44954001401d2109000080c600790007160000b02c0038491000140c0c1512102 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 951365242 1250 951363992 951364009
    0x50402040608220605150301200a030e010e010507020706030605040b0d021c0213021e0405060318030f0f1234140a0c03090b03010e0708061c08180609 66
    0x24880e09500701580100341514181e180103103da000303c090040703003080146c5141550182003240d000358039000c46916460401030343c0c5000d08511080e42031501e0785006085015060810049120b99201e02a40c00c10030024820380d849154150701030b041c80c606000000b020b49406600440c4070300d050081185950b1345d44c690320340c2c00f55811501d103101c000c2118094401031201c2d101c00381d40170200b1442c8610007020b44e0020550400703ea20f0f1b02c0400101c018031640c440c047e41c01a1504103406100081c61400e030401c201010010700d02c2120308101c51150340c090f00c0ea026a07021000c4003008501c809a00c2a00c000d40746c0c00144010200007d1171181412010a4a12502c2d5824034450140141c919038065031254070380290b924600342d0358116006002e0609006180d0450000f1002540040c0c000c0c0c684040c0c1c0d040c0d42c8890510411030b1210301c82156049409040d65511000100d048224100064011b011040c401d07005582c680c40480b0101202d112480d00d150b0141004024124459030384119 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 951366492 1250 951365242 951365251
    0xc0e090712030e0904030905040b0328020a0b0a02011a01050a1e14040801020405010912050304260102030f09062802070c080615032a221410050402040608 68
    0x11150045151801c0c00c845402c0b0308043d4642184404041c4800c0c0b5078000244420386130305443c10b201d400700c1c440500d82c0d40c000c00c0d003840b4030301d0302154864043c545101243c502017a000400e0300c0d81607a150011103c9952061004801523991051141900074501072800d51020003401e18a041282c00c0d50044e20703661082114622101580782d85c05541401004000c09903210707050f131561281c0d2140da03040d0003903100b4001d19004c182c8800c0005020100303800010191a404009142403a1074038005000540f80784105840d0441c01c0f0002c40380c540402d1014500c21402c0302458101d40c10700c664070b41d091420140021200b01460482c01030390142d00400300390070358000d640042c0d860500d410031402e5102103401c070800c0c0740941c8007800060030074482010ba0240003203055603401540380101d8801004041c11a01101e4111082d003182440c00c02180040704211540440d0401100991032088400356800d100c480b0b013a140602100c1c074000d1010001805042d01c04519082c01d0a1018144000062 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 951367742 1250 951366492 951366509
    0x1b0c020d0b0a0e0307031101150501140310031a0402150f070318120f05100b150c0f1e0f062503020d020d0f14060f01050a09080a0b01030c0e0907 64
    0x705802442a41c0a8a02084802d0a8036180c0ca403034640100000341a0202202c1f5609240803030b4101101b400307070602254816107404c425103a0015010456803c01050142d0440c1810350000104041c00d82550806440401909a5203402c0c03041041644402142000750318052000403414005002142e40e210b0b010b0a011442c00240c80b1070b11160070351034110092803014001d0000421454007240c4032014854000e4804042003803071020103d41c1c6500b1030550241204003400c441090b540010000342c0214400c4d100f44070081003045141c4902e115200303010740008180e09590391000d110703482e0303460455009443c0d9803c1c110101e2111200142035460701841803104506c9590080d030445621803100c410071b40d2a42d111a05000050200751a500c81c170900b428270340c3c03a544406007001441200000e0446480c14840801100c0e550000c05885080c05128680890300714070800a00034a6440f4a02c0c000043d03041d450301a100c1075283d448210481c12040038800e841ca0007240000c1a18240c2c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 951368992 1250 951367742 951367763
    0x706050a2007030825020307181401080609070911040501081003051506040b01030c080a0203060f040203090a031b05060103030507020126040c1202060702040e030702090702011b0c020d 81
    0x11040c20301048104901c603910b446624000000c100ca140040c1c81680400340c91030306a145082503583c00500318060003589a00450401d00071040310712081031103c4004100050401b12003135242c50701403001c0e005120182d202400b08030803080200500d0700034007074aa01c04d02111b5980050203880303000300d01465040c0900324001541b100100c0c18484000c5400c101224406007144070700e00107030113041d00c1441c0503a00301404015294001d0150350042e0f45141d41d000c9c03a0b941e4401148000350400350840358081c6101300f04d40c82c95034a600180d402001c0f40809002d0002643c50007411100e1540155007071007104450800102d00c001c1422030459070942842503070350042c0c2c40100d502c00c41e401c0030168452402d8900035041c0c0c05c0d2440c0c0038441c5208108c1848200d40710382049101c0d1011320380081d407103c41002100d006090581103907003010202e00c122820014240d0000702640c60455203040103039500e0451014580004040004511700303420490301c00811500460360307541d41c0e468060f080c500c59 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 951370242 1250 951368992 951369017
    0x51f030206091f0504030309062d09080109030201050f130b0a0506031014040209100f0611030706060b0a18030f02010f020c12030c06010f050d020111010204030204051905090706050a 80
    0x798218181c0000400c0885032040c520003d010300181c00500055002490521010034140d01411004916480d0f02c40d040c00e4034125102040012060401080308101d080c44c80002d00b040c0900840f0220780c400e40020403a490440b15400104030f009107145a0340c8034505000c404a4240381c090741d007100110901050710781d120800700f407402003802000c0500c185401c545160b060940140c2c0c40c001c500c01c456103201504c8101c03c03002181c1990088000700341c0464003c00180c0d0203203150180d40d60396501500d080c895242c80e910121581ca6101d05080c410000784282d82d50b0340501042c004014981c0442903840c01c648a5901c842004ca100a061114200c101000070b03008200c6c1c2440100010400d0341c01d9810400c10726126088031000c0e1007144517100c0081171042085400304142c4001611220b04505145c00440e400c90403040c0b112004c1d5801c10002c405615140250784c0301e225000d15144c00551050312480c02c4800003000103041c0c1d00450340a001140d8080c1c00c50f6101840c130b00d886070f41c5201 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 951371492 1250 951370242 951370249
    0x2010f03060b0f0d0b04050f060f0d140c191d0606160302101103060f090615121b07020a06030b1215070908061003061a09070e04051f03020609 63
    0x800d82001c0198100856112048460368009080c013000020082c0b0480c1c4840c02404162030b4280c9550307481030705950006000e404c0800d0310f4038621000810394450344440d41caa101c40039866140c8200031b50001300c041155400c01c04140f84221b11000c00528445281c102444040700001101d65096076540300440c080d83e86010549140c100300e000d43c0c1888540619010b90380d070208900b80440c0c0ca0801d44110300e02d6032803100303036071041038083c0c03014a050007030200b00f054118005012079030200100742c0301640c40100c071014140c4981030804541c52800c1082c03200600c000d686654a01403101084908010b807122280c1c1400c407012805c0c041408401303980018100c00013400200baa1f842541005800c070150030304014006c49d030326100d10032b00507107410250f61150b104a41c2120100d14a140c2000040d8056010b903071400c0001032034000900025000640b6407409a81150004a800740200c90710315080c401c0c00c0c0c025541080c0718844482481c42d5141d1011140b2011340300d80c20101d041d441f2600e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 951372742 1250 951371492 951371501
    0xb0a121203110a0315060908190609080a020a03080f07051c110c06010302120607020312040501140c090a0b0a0e0f0307080102031e060604060c110109081903020606100c02010f03 78
    0x601c20038580c0c40d0000c03080024001c1c00c6145c400001d1007540c560000d0300600802d00c10040e030321030f003000c0c01028108040c241040d540d44007040755556610240340b4081056040940f81d0b03020035a0107082c440d06541801414124040c2200000040301414401800c3d0064201c50f80c3c0034100140d4500d110401450400500c140203107040030407000944da0110040208d01c490680b4800c0702c829200c0e45580b4000c0766103400444458015030b004202120341e20300e6071b98146621610480000c10504606040c201075900709a0f04224024408262816030b4a4540190009801002505401e060794901c004290196901009006215000d00c0300d413507403000d0143c0380c080c06140300290b540c0e0900341c4600125a0715040c0c0100c1c85840c400c0030411038900303001294100d80e6a951088481c0b03880e601c503942ca10340c0c024662818801c0b0a06c0c0080c401c03000380140040c1c810704040d074140481c410304000c1c1c1050790041c0110311400ca01440508040d4000c1000b40a494080ca0904c400044410040d801070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 951373992 1250 951372742 951372761
    0x70308060603160305070c120302120c0406050307080406180809280b09060c060702280201080c0f090406030305180109030b0414070b0c0d0e30120d0209040b0a121203 73
    0x40e00c1110251230090780640003885e060185600100440e55660b41c03070341c0355014502480c00090300410105204520a03034245801ca401640001703450440003c1c100d07910340048000f1200c3e900080780c004203514201014020f021035408070039840301c40301031a0000d140510701510b0358002d80419149000c4c1c40b0f00080e0703030b0900c510508503042070801000103507035070015550140100c2ca00071040c5044020030385126410343d9041e101e0107103a4403089010f41450700440180ca080c0041840004865520303801294001c501a03166150b4500c00e040e070b201c0a080103e00c443d41031140c0e0440c20800214118041603116401c030248800d402c6500c0206402c040440d802440b01c25408034010f00c842001148545044503035440b000a01d108400c1408040c8016820620818070f0200e5100c01d164507550110b9142540d0700180c0c0d103843c0001d0010301c040d8118135100c070403180c2c0c08942d011141c2001d20803042d040c84119001155140390449100d40300740003d0005109440e850461407806009030080ca405 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 951375242 1250 951373992 951374003
    0x140f060906011418060d031403070c06150b0d05060102010e0706020d1706030a0f08160309051804021c032d02100b0604120c09060b070308060603160305070c 69
    0x260800c1065259545801e00801c800e0888408600e4114075242500c0c1003c004512510401030341c942e42040f104219410043d400e00151f1030311100c1d0244454001c43c4148219194030940e01c001d4108103046070800e00700e20b0742310200b0750400d0090400c0b01c3c080d2540f020710740c07a020135550340300d00040740504038140071500a442512804100c3c02d030007007a1140c0321040c81e501d80b020032422004080c41544240e03003054058000d00900e10104510302d00041d43d00e130141c08101d10700900c0d10f5402c111102d0300e880941c005640c03330303006000515255540c0e111700f15084440c100541072a0300051a0102c02c08414040043c1e9415240308050250600d111041c1240c1f001680c5464450301208480e015001c040005004007890750200d40702c144101d01c8d8610000c2e0455042a0074105004810340b003640e801d6513054226400012180070500501018140c500c40309030300c4184c02c0c500a005d140c4040c0517903101d02000d00401c034001000080d00d40201602c2d1401003210340f03d2030070035107141400202c082c11 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 951376492 1250 951375242 951375253
    0x606040e0c12060109050d030804020103060b0a0e130501030c05360a1803120f060906090b13140f0406090516061103030903030f22060c030f0203090703140f 69
    0x18080c81c1d00098003100c280e03036554129540d126001128001040e0140c2ca601c02c1440144c1030110f417150524039403051060600140c003030786408500032107802c480500750014255400904450500341c1da83c9000c00c0c030109043c00194110342e520030040d051070080c24020402c4410b030300150200304440c403c2c030040c01c80800a180012403074448200c41c0407a4060061414806031014010240380f142100d0760305039803000504400c030744186010740003107450111000d888400c04924921a4411100100392440000480c00e83d00b00c10b22250a46110b0803800c224030300000e40d400c5220a511066200381d0b00a801d00b015030344c515100d802070841d48006000780c0b0548100d05040d480701e810b90019600c180d01d500740e41207985a807842c3da03480100d54400640e0400c2c0b0100b0f1181070091702c2c1c42d411a111003019800c004c002c610305101c505003c0700548195882d42c0d00c444880b0b030148204849000001f500794610710301176020940d900302d44d11000b011040c0003290002d071400240071000080110605070381c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 951377742 1250 951376492 951376501
    0xd081e040c061d0a06201212090303010b070314040305030a08090606060f070b25170604090201050714030d110304021201021c0c0212070b0702250306050606040e 71
    0x14034041003401818042010f21484203c002d509200d04604610001c040140c0386081020880c0c0c00c034815209071496940900002a18103401e001294041400300c00303190f120304031307407444400703040010f420f04d261078108000620043c0c80e14030407103101039010706008510035007500000c20107110700d5001400d1400042080c20322181c0c41041a40501b030030301c00302d40c1544c4409081250510648101e901100c0e0100514030000310702c0725409078481450021565900040300080040c1d040c1c240d500b0000800c5080c84c202d00c03400c01078001d0b0700071005032010021100b40e54001b900d2882410006812451001500c9144460400071070781c6031385041e8401c0c172400d41c0103240c44103940c00540303040f8031a030300076000107805440c14400c1d11101f411603e0705104102c080094140180380401200c001c40c0520500d2140c0303101d0a100a050451142041700c41130300d41458001e0515a0000c5001030140014098185071440c200001c000c1c1c2e030700004006416160b0400240e02807180c0d1b070080c4030b804207160411 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 951378992 1250 951377742 951377753
    0x408031b16140d0e042f03090d02190b0a0e12070c05191a0c190605181209061306022a0a12060212101502030c0d081e04 53
    0x20103118801c2e00d09060401001c4901615111822094000152000901c800c14a05500080290203070307003400c2c104003012450b074281403400c2c88640341100c160010601091200030072032956802020700c05041400c1d040318151011880c041382c080d00e00c030039450214051641c680e000445009031001207a41c4403030b001c000440c8940025000b07841a80301040005000d0500b0001d51030381000b074902d003650107400c00b5030900c0c01141030a405e43d80c25205022558507084100410f0b40c0a503400d5082d141032148900e800c4003130310700091403105050b4141d507400c451b50400040522030082c120f41d40946440c0f142001c65140c0c0291103544c04e13407441d111000511644c0105070002ca41041161507000900d1600c0c9440c000301c00c2c100ca50381c010b05001c404001054902180c00243c074030400000d480c1c0940000c0c0e42e1000032040e83d40c90403045044200700a80019007246400310a103d0000d07608140e02c0d1040c0944031800d6800c0310051181140008044001687c607140b031000741c0c0445000c0a04040c01c1a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 951380242 1250 951378992 951379027
    0x302160311071d0112080f030705181c0201080631110403081213020d1406090c0a0504050c040b030703020a02010b04060e0a2007080715060e0408031b 66
    0x4088103030165501c0860f00c8810f0803150f494400c091145005680d01c0c011310381440c4104c00c3c5060b6500380d0140b06460103c50140300550180c641e03603036a503031600524245206c0c0041c60813000c500c14600618490541110900215503107902402e1002c1e041d512000494113035403013075110b8898415400449003010b92506811101541e50160410070490040d007686003d105900000c1e1001d1014060010214030000c060360b48169042210a000b21440c0d001c15501c5008040443d540c8011901500321403908210455100c0b07000030080101e0303442c400220320b440d80c49010300340c0900d80705c4000410400c14007089400510201070420390728500782200500030341215070144015404c00c14500621301d440c0c01074205071442c400a410213504e9400304a401000541c4000c202500d20000320a91042281d01910059029059003580c442c41450f2a00b00490200110101c9a2074000d05008075040e052910764080d0780015103a07030781e48600c9180048540712443d100001d020018a1407454601c80d0607 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 951381492 1250 951380242 951380267
    0x20c0d0c150504081e09090a0c0212132102060a090e01050a0b1b010e1605040f090b0105060a050c2a0301060b16060207080a0c0c0f0518060103021603 66
    0x4810700480700740c00446094520588010741850002d20030036544114002040406409601c2e80e113191840200128a8000084580c03840aa9944820800080d0140214240007403400c0d8903d1514442e54030a0345102075600501c0f0b5404c14402c012020900c1040150015030780003005031383c0300ca0803031200400e502e043d0301031548410b440c00000140340c1480a4032805072642d40754442e003002c1000c000c40740c02400c01080480c4039900c034014024402428046184021802c1e444564120700b0f003401d010a0350b9844000b0315103149010300c2600401c4070b103828103041d03403021507905999410403041290607000d040c82d1543c081c055580c0f0100050181c000549480c5c801c00b602e152060710120404d030072600c0c544224000b00e1070801c00136016419886011152a00c01c0701c0050030440c1d1901c6441b40c50700071003882000b24148030010303020701554405441c01401ca0a040441c0c0700d00f0701010403c0701f0807010030b8865001c16403000c40c0085c0e0082c2c050715001c001e80800b084044c0c08034100280300012201 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 951382742 1250 951381492 951381503
    0x1090c0e160306030b0703090201020c1504062d1103071407060e040b1011070b0c060709051905210604060b09090727150807150e01020d0c0501020c0d0c 67
    0x341101c150b0b000c1d0080004072030700300c3c240f04140d031340e240c4082d00078000c0000308078118060300402002c0c0f5503d0380f451240d1458007440701c5840700c0c1007041c05842c1c4044403410054181407200c80741494020958035110149003072a003892503042c02620b00e45507014186004110300c500c00b501c1600ba00d8006281012070721141d68131504800a00305010803661840541c035088a240074800f034005014061a1400740c20490803035003041c1e0740d00e0f000380d8960030950480c0401e8000c0001d202c1c4441e4041d50000140c642126002c5420308490340003e244a843d02c106030013a40ca00060300c601140d01025182402d080d00e090314443c1c6058602800240341c1c4003043c1e8030450301e42012418403800040c403041540e8100c0708440701c1011401d9800c42d4000220345c8003014940350510b0136800d42d00e100d000303801000c001c802040307901d00700080e001c0000041c4030001e00300f00070030040e90691ba81c009124140e504060802040d42800c608055000e1b108501c2c0541c07051186691f9036443c158495060a2513500a4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 951383992 1250 951382742 951382771
    0x2190809121603300e0f0a12030207052403070f02030904020d020309071e0303110a0606081c0338060c0c090f01050a2d03080405011d011b0501090c0e 66
    0x100903c5070000007490135203000079054a80c100080c180307903000b9145503c2c020300f42d0340003a41d100030b401405090381c0c00460068205045c00c2285080a1120344000130019448000b1702d80141c90b01e00c0d041c00002c1c650350410140e868511080340c002c0c81101e00381c00e00900290741e00c01550712544003a510517950310704644030b0b90720001540c00002448180031b010140b01080f21520315203003220020f030001403801c1c1e0760141c1c1d0650b0700000c00c54441e090042c104030340a814011034004d01c8190050803d44041c09041c14881c4050410030040041008525074240c00803d40e8101d40c0741e0311003903d0086e40d96810042c00900340b80c480c840000c407038070710a6044401c503080303507144100c2d94902c1c0c00078420140c0041e8144010300c00344003030661100500001180c2500d59485454402c0b0481f40540d109441d41d100c009000d1140c0d50b0b200040543d5903400000800748000c624000801c40c070401c00e4519181c000c07185660303003081000e40281040700e410155030143c0c1c070b4448241c401a09420b94400840e20b210 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 951385242 1250 951383992 951384053
    0xf070206090705010c02041104120221030901080c1309320601050f1608071103210f0d15081917090a1503090302190809121603 56
    0x11001d104524003405410078900e484010348030401050f10880c1e0040e125a18094040020030280000305035044201d2204901c3e401030150340120028191046001102050b4400c3c0d400011a414401d0a280c9001d0b107654101403c041400b42c0004100769842c5108001070016490b08400c142d00c83c00c0640000540d080b62030011584c040c044181c1684c102c0d00f00040c4250b0150b0060088080e03662080ca241c500888111185500c0c056421030f041b18000c26031105224031100c00002c503010a40007481c800e444e40042001c4174909480300f00000f0800284840c14031064070a450240107051401d025003503511400c450500700c24043c40d000e0744500c0022060600b401205000f80c640c008018013070000031001044407943c030001030030f40c00880c80030b00081e0102001c40d03138105449003a0780010b14080c2c245802418107400c0c801c0c0074052455100707254049002101115031549085070202c0f00b4010950076907060031082668460765400154002041c0030f4031102641e0214016005036409220 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 951386492 1250 951385242 951385247
    0x421060c0207030c15020a080f03040515010e0a0903050f040311090c0307050a031a0619030617031b010906050c04061103040f0b0702010c020307092003010608130c080a0b0f07 77
    0x3003c0c40040d0010468540420444d488070021840d070000600c141c0b83c49003856222004c1c0c5511005440008000000c1008140201403040c81100d40d110140250294075050103102e03510300180426204a03075030b1040004140c090011200c0000e003201043c0e403519524106180b440c1030349407015006c2c1e165400011503840722041101c0c071504190702c40500341705006608070010000c00301c5002c01440d612103280701d2941c5031405008054510844090600341005009061316440d611121513541344000000310a40080300351115400e90200c0c4640c81c5140320345103405000c21040140025140409100c0640c1c40d010061060319007648840d0007481200e84080c0e50303841144030381d40c007a540d070000030700c070f1149044024169130b4014580840d0180340e94002a0030014181c3c4440d40d01a40c465405147c5405450486105c4c00b038240c0b140d00359850090f0181102000500b0031014610000510080045480c611805048400d013250085020303868200046942a10340712109401c800000e0042403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 951387742 1250 951386492 951386503
    0x10090f05040b0121020a15030b01020d0f030f0906050708040210020d020c01050703120e0609010b090907090e03130608180d200f1c1e08010b0703050421060c02 70
    0x258403400d54007060380b8040b020401414110344e6031081e040e92a0303032100940d0382c119141010b005007080000048200c1c100140465014248150540d00701d046102150740e04582401c045219604001c80c0280c6003811302001003001030001007480d0701c2c01040c41a866809030315284114400c0d05c44219521a000e426655070096221103c01a405103400a1641d40f01d000030b0640300d4400e09001032850b1074001d160007500d840c1c0340c540c08268854401c000300303807009002e01c941c4d444040e1103c1000d07040804245485400c18021080c1584e00e40400741012002082103807080303ca00c5200044490701c945c3d000f804c1290603030700040e800e640c5181d500803405000c01e58130091902c607103030032901180c442640c110484650b28060028000c821074540e404200b4042407116640c003036500d0229106d805000742c452091003030039a5540c80d0b25240c030704a0f1070f00314030000e06551801192507105c0010349000c1350b552065400024203621045031070a9030200300e1403080f241ca4416103040c46080d04080040765100c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 951388992 1250 951387742 951387751
    0x501080705030f01060f11030d05070801120c09051803180906090c090f06040503120301091b0c2004061404270803250804110105030408040b0307120510090f05 70
    0x42d003c0c41c0100034090083c4500d900b8660942404036101000202c054119007040c842c034032240d5228400c0000e041d60180507140507001040391180803520580b14992448a20701440d001c0507512408038026003200304040d807401c00369070304681d83e0388420913418429031255040c05000d00300010115020745040d0b0b00d12480b4502503064941441d0000040000401c03801d400241c00100411011803183c40c1400b000c07003440f1810f81903135981c0d494925070400321580884ca50240da0211052561030700e070321190348490030750040c180d009000d010240300c11140c40740036941c0750700614204002482100d040d6884100010464013088018102d580c2049044100404a40402d07805154400060b100c000959000800500303c00c0f4868500e60760131700103100110501c00461407030802c10081014030f81049040c00021b1130701d1425420941e55030f241034016401200650000400084c0005205189114032094210824000ea0400d040c9010740c091540c010218143c1c100700540011500a01455004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 951390242 1250 951388992 951389011
    0x1050105030d0507241a03100c0e10031401180f2c0312010905160f092303070b0d0b030c090406051b0304060b0a06080f010905100f0f050108070503 65
    0x40c04c2a555a011564150080d004520380d000a9030000304096440391485500400810311190b1a8810400d840d00241c1c0380c8141040342000c80c810b510f1035014184200b0b40400360340707a40c0102c0c401e92040c3c002e048405d83d4080700c0030360840005801781e07414142c3e003070101c020201048a400f801c1400000d90740005c0031014070680d907406124101515000309900e482c9084180d81c00d082c064070190441c000280c1c002e640081c6c40310148202410861050355420145050243c1c02c0c0c2c401d5140504a0821403142104074082a801d441c450618040d124115000c02001c8e05c14481c0c892509203c0c41d08000322404856281c032204101c01d09002455814442005200d283c40b40d465560729006800e00403c01e0700303c6c583e03084100e000180640c1c065400355200b14030200d0002c82c400c0610040ca0301d164031040404c1014424400e40b0345950030003078155a140d041c00b1410b0fa40d503181c5071007031800c141d114489860f1007a00c0000e50b04007014864059460036610040351303841d044000c44032404180c842c00403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 951391492 1250 951390242 951390247
    0xb070b060f0303070605101d0f01181b090e0c04060203040b0c010e0d110c0409031b03091e0f090603021c06110d02030f16021b0a0504060b0a0201050105030d05 70
    0x30351418000000303219800500f1240740c07459550704e94041d03034001e5620741c407140214501840300700301d00d040c901d20100c0d0705041c40c68107141c1500d122404c43c030b062050402031801e03100c14204140058109011400206141c010110440c0800a006c601e03a0310500072100c51880c081152001110708940031555158003c40c201803d1540302c0307945a0241003807404542d44c0e410203010b0680c051004003982082a102c6000d01141040b01d18106421190464844c43c60010500002504459a0f1258000c81504002e4591030b0385001d8a5805841c2c1140d10341845e00701003001d200c0c40601609064407030000b0000c441e02d0b40c0c3d2041106542c10390000035840011300c0c00b50b4032110801080a00716138001d00020490b510325941100e142d510072500b080e42c0640020400043c41c1c0081010390b00290b0360380078404518410f900003911401304007031009840d4980580302e92269209142c110190400030810011959502000c1c140d66104100301c00141d400d20f8000a0645008101442c040c07149850b100d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 951392742 1250 951391492 951391501
    0x71a01080c06130e180c03010b0a030b060d02091302041d06040305070c0506160302160614070c0515031b0405130c0302210601020114060a090e0f0102070b100b070b 72
    0xb0250b0008107504a04065241d400075801a401c0c01c4540103091010380d58412000d200032060800401b007640d00d000b40c1c1400300c40311103501c4910145e401c82c0d8002d18220700d59141d030000141282c4520b20081d41c0081e55200f070100c1540401c0c00148424400c54080008220f44000340303102020b50800c1e0502a002540080c000c03c2c0100000c1410b50310440d80005483c1c1c550780019160b400000c4143c4600ea4508844410980c0400c2800c0700048500ca18240c070300d2074108001d10b0450001041c1c01d00d0000842c248082104090641010388001450080d2040170240c81d406144c00450740c032035400030114628488443d543d0221070540e60081c20407000c0040d2031071248007804481e91500d0425608000c2203205c1e0510740030b42d009044085141ca180c40c14240c1c002401d507280d41c02d01460384406442440810340ea100b00c603034210780140700b0126950b4520251642401b0161a02800035400042c070107040084451500e48102e20f10714090784215180c400c8919503010340700c4020020310403600800c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 951393992 1250 951392742 951392749
    0x2c010b03040f0501050c12010b120103122c040605011103090405041a090609010f02090d1e0c0803070b0f040201051602130c0201021201090902060a0c0201050d11071a01080c 76
    0xe69009001e100404049415030751600d08443d012103202c038954002042404048030003d1b04070703004041070b11801e070a0510790300900c81c2d2a5010b2000602d41c0b82000310304074500d8050142441102d5102e0f90841000c84010340001210000000041c89149084404900c9601807a40001d0300320b401e030011402c0183c0702c42848014000034205662240701c42504100030b804007680188144c518101901c89404c011040509480e202120b0b2200b280c0180444145a1140c7e5505140d617508452041c80081180024004401410030054140c2454050100e00c07441c0020081c406203220320315005c001e0303448000400c0080015a0300a000803810000c01021940c0d24038004015800101001011005449450103c1c0d5070b4405c4200540d4010030450742401049001c40e005041d030b07002c2032001c40c02e140e0000e0880e104955810041c0000c0085003c2903901c2030703003a00c1141c840c1d00c50801448504050856891304000800c88140007600c3e0f010859024004c41c50341205c1c190b0005201a460030002c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 951395242 1250 951393992 951393997
    0x210234172d0709060b070605272b0c0b06041b020106050f270a06030f03030b13140703181a040c0f0803091e030a08042c010b 55
    0x9a601c03548550000c2490307a011400c035041c1d035100480d04505490a09142000b903103520814920340740082c10442003090104640c2c0044c3d0000e40002c556580720180c1d40b4180c0031811a050301d5481c400728020140380015825240741003488003100b54210105030042c900c0e00c8441c510002036036031130410001880071008940210000340302094082c0d4491016100080b0300c41d9500050b912a03900304000d0400c810016002c91056030b43c600c00e00c2c1d415601c0103074030386001103400b10700b1a03440001c0c20400140c0d1000d03000c2d40c2e01c9071100d45407a1a90a004026101119429200b1403c502c0110a00e00141c8941e2624000c3d01c0e0342d0a030181c0d12080300b035004110b10041c54014074000102940018042c1245a00f50040f5140201060801d4103000c1465030b039542100200801d0028103000345140042075132141c00c002c55400c0c1021542205e56100440c43c684e03419054030821015a0801900d0005003082d91081c210740095009041040e2900701c0c0c00c00980b190001c0e16100600044124200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 951396492 1250 951395242 951395279
    0x6020a1b1401200d08060a1205030a1116030606060906051e0309030708070c0306110c0a061a130f11040302061c150e01140a03031704210234 62
    0x203041c0b0b10300b030f40403000300c0c10602ca0100310800551040104012842c2441c0303484007a00500c1202c1480140075901d160f6a072141c105e140f01404940c50b00c03c0d02e008000c108840c080c280c183c2101d12095940d2801e540908040e000d44c0010484400c0b010900314810000da5008a00d080f8200000040c4110f80001e160b102402055460000b003100310049000d4400906840303100e0303c1c2d500e00c02451402d00c40c00b100c161004a8480d4541048642030303c80340003810f02171141e08014000784a02038515400c416002e404a81900f142d1026084442800c107580088056146000180b00807000000134055500c65400300a62000060081e0700040f00c4101c0c0612508001440000e949100d0000c00c00000041c1d41c012051250315800611018000407a19408460155a00d8079000d0855401805a0441846001031120300c100040c0900990304407030b0b1007064042c100610a0031448030002d4550904508200b00b40400303041c42c9404d07101090707000050a410f00881da01050500c4044913100d1406503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 951397742 1250 951396492 951396527
    0x503090306070f08040308221a0106091a031e04030c0c060f0914040204080732150d1b0c02121b150c030f0d051302210304080706020a1b1401 62
    0x1c0c10070064407c0141040ca214052700c0d9205054064100300450048141c1211003004480982081207289c0304826210240c401c900082d08c071746d541034500b07000d1500743c07046030786044101e03090005044c1c00c152041c0c1001d002d074848603a100e03241c0806540101078401c1e200d0008000742c03407c00503c90542c001e0f01c075041d0020070141c60103660b0035580b886d002450b0004403483c081641ca4195840844020030301e420750780e00c441385400700c461000031042031014000d51082003001412580150980e80920418800c41030a1501c1880916008101d407a00c0e400172406802c1906445c03003141000111050200da40034044403911401c00c00f8404100c503001a18941140140311401c500401030000d00242002004815122100385c2459420b40c0d07400f0b071110307001c4070900b541031001d40c0703520322031850001c5000c42070b007202041082007070702c2c5100d65801003a03103001d07400c2c0214929502103001207540c2e020b60540f048030074079103882941c50a00d91003564a0f4110105640a96500442040c40b1920140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 951398992 1250 951397742 951397771
    0xe03060a0c14030c040f12110402031f030c0602120304050a020f0d0c091a01111015030f060603030224060f040e0d0c02120f07030602030408160503090306070f08040308 74
    0x4480b000744a42054a41c07000922010074244000803a121a04008143c2440103404108041c2c07190400710704540c0d0418000d940002c001034000300075030000741034a036030034201000c81d40e941c0c1000354500e17806002e03080044c0a046a490740900381c040660303010300c0d0008058100350030a9405c1101e0141c040420302c1d0098158400d00001c01c07803820b90340d001048641d2001c42e0b004000c1e13202034040e070045529141840003034910400317603442c0000c80281c0c0d51484000058603a5144030407402e08034a03a80000c12880f011a110010000300707801030b000302d0303200b41c0803510000505d1684d0014204429108804020002e00044076841c0940c10036601d401d025100180400b82402c286040c0b522282c20a808110404032590031410040302da034400c071a88801a0116000300c2c103c0d95103509581c807015041c1c42e000300c0820f040c40010412141080402c0d00e10409603802850002d840c1d8001c901030391311902504c40028541c40c0208040c1c200c111499482e0b2410f03941d40d03a41513548803c007825036101da8804 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 951400242 1250 951398992 951399017
    0xb0913030e04150510110c1002060711030409022701030209131127090606040f0603020c0c09040c0303030b09190207060f051f0b0901020d050c12030a0501050f010e03060a0c 76
    0x700000180c11845c0341c1c1d1110f26030a61070541503c2c040c4085100340c06400c40110685c20103078042500c980281152034024988140c4294503842c502442e040812118800160040603081d8610201d241214900d111881c542c142001941203005032041582c1041840703155010900495010001c1c42104281d61030400151159103909441e40b01d8546049800388180b0010900d0442d080d981e000004440d00d603d0681001128a00310915100d483c043c1600822440c502b0035042c4003600c02500c000e00135180c01c0c5071a0510041c0308640c2d101c01d0b00400c0c90319840b0065800d1404916101d0008540881d803820400c20495000394401001030b604680d60300030440207100035000b2103016000000c944c101d500c001a443c813464580a0380b1190304400c2c100455411640c0109548442c400e46003000c0340c039022681a09414400821490200803d00204101c45540c40ba40490706135501a00c88030303c0720343c1120040d504425641d0281e45d00d0b90001700010340e0001c03581c0040504500f18500142201c20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 951401492 1250 951400242 951400249
    0x13021503040302070f0b091e1c030c02040e030a08160c24092108040b06091b0a080103120c02090105090c070203120a030b011407060507030e060a0b0913030e041505 72
    0x1500d400007191810009804421458840000101c0c2103554400e01102c23225680081c2c40341e11a00201052070400802e50414180295002403540340c02820600c20000c0034900251a640190601b80104113003c0120b982401c622085003d502026100c0c4000c240890320392040e00324a140600180741190070b00b01080204030302441c80d17054030488003103100f5841c5c49040e088072030b14014580200a0030302c08210101d8841c1c0748040e04060140c69080071074070381c212000d40c000b221400c0c2041022000601030325656211b003001307040f03c0c00345404007460860318504031440c54503040040d50140016005000e00d140440701907030020b1078140214500300c8240d0100341400c11803003076101241004100b81c10055010700400705152000d1815058401c2066403420310350040142c041d104e15521400034007100d002e90701111004907440211011440c11048880c040d0401e039903164000e4600038040354070042c1000c215400140d1580715032707042c0e12040d0180300080048009120118070801d01c0090303e501d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 951402742 1250 951401492 951401519
    0x70b090a2402060c070b06040b0312070b1504020a0f1103210604180c1401050d09142a040f14070809063706080304090e061302150304030207 62
    0x261824952511101074600c06401d0110040034646080000c0085500003a0401081a4040c008031000240d83c0c4200020904d0000b640006c104903110001c0d868060008e15407083e0312880314404040e24030340c98902070200340e00031501c409000c6944111480003e5000e5090b04100c402d004040300c6c00c0810b10310403452a41c4a0303503844031031041d403a824031480381041d020b00440b60f040c2e24003c3d0720801c0507580d2244425030300e204c0c2428400f034002501c0a16803003070003100c20400c0c0d000001c1c00a458241400207600b000560100c800d44100c2040c0f400a2031080c99074100141c16103001c4c00e11144500920000c1c000c0784403070f0001e0642e01c000c2503010241c650100c60003035005076558416441c0032066645046409000d0701106c00d8048110605095011380c064940020b42c84407104181580400002919071070700718882900001c40c02050810f00380d4440a07800c80220700712503007621540d01d01302e6610b5050101941040c00020b20010540c1d407040110b070814424411a0201c1e03645140e5680520b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 951403992 1250 951402742 951402779
    0x4020315010f0e0121170c06070906020d02010b030c0d080d0e01090c0f0e2701050403120c031506080714130e01050118031205160c0303080c0a02070b090a 68
    0x40c0c0030381402c3c460710700c0220005002d0070010800d5004249002010038a01c12081d200a10541000500011120000054075000351034030f07044030b4450424081c041c00984c254000c610051080300000d4592030700c1402556545400074024003a0030006d00c051100b0781e00461015a681501002003410004061160f4482e10743c0010000801750350a00d080801c0310b1541d4080e01060760402810301c01e40303200700e40a039008a4078070822081905000302c010381450764150200700a520300000c0000b45900050140c0b2400c0c0d000e402000745000c1b000b004e4040b2400001060003c00e00640244469070003042440c1d0480458109a8103c010007545440c03a135210117015400c50040c0a020005080781c00000c5025000900302004184181c0c3c0d1001910381040c400541401413142c21106858061004c441c107205159151340c0c10400c050402040b04031561008070001100140091101040042500c5400415502920702e4601e03024620300b0640210041130392018400c1c50010310001418024102c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 951405242 1250 951403992 951404009
    0x2160501050f0610020c0904020f030109030909110a020a0609051504051c0815100e0d1a07020316331e0605010e0105030c07020d0b09010c0c08120402031501 69
    0x2640b801d54030b110700b01d6030050f000f41e0050300701c0707502d14603000e40109141c10810030540d20141c21350388900005000201d11329042d42c1651912700100d0138154800c500d41d0680f11003140034000111070f00ca032030700c9600c1403106440c0181c00c11170341c0200040e807940002070014011021105011b800c0340c0f1094010360180c4044560f58441906801414001d41d1209290750880c05c000c3e584e813600070b4000c000c2103000c00a041c42130303143c04040400b80e070150600c9108408064a44221101c552910030b0840070141d0000c0540d803070f500009010386200108032100104c02d9484e10442e06001c1c1d6403c40e0ba011121034035090100000311701e19182039007403a08a00b440001001280074802c040655400c250208408801c040c00c0030f80501103a6008189a01c4000080c600940d4a0340d40b1620003d0034050f04000a41c426284903156007030044403080380c0c2c00380030075070700030000f84244a0342035600110300040103045030414014000c0340c24080b58015070090000e41515041c010500c4110315420098000680c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 951406492 1250 951405242 951405251
    0xe12011b020606101b0201140f094b1309112e030f0606030603020307150804060e031b06091b13150f03050c012601090203090102160501 60
    0x89550402ca45900088141c1c0c0952101008141c020104e1042c407450114510004090208691086040c3c480d03820030380300e126031510700710030071005507030f0090a441d80303e81075040d00d14510008442501d1502c140030a245003003002d040484081700389014601d40381316080700000e130b2040d4803201c1150100e2446284002005821490000c0101d050809094000c103941c0c440e030023140c020500d003102000406564401080e406d000110040c040d826988840103040c0500001c0041d0143c0002d0140c9200f01c0698080c00e841c0c10a004111020040d02000544200d0116022480691195441800940c19030b451f04013078001c00c01035500d40700b034108000e90002c020858819814440782641d008032101e0f00b42611181c50000d00c80e2400070f03464079034150791044c2c03402c8110700300861480248515906001001d980c0c2c1021502d42642e42c4880317003c24000741440b500c00721141c190740311168030010305808503420007048034002d4000074054404d542d800c110b003003803007072400300c8140c0e01c584100004103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 951407742 1250 951406492 951406541
    0x807150f050c1b1201020702030606060f040503070305031201150207050112091208012c06040506180f01060f0504081e01020d0e0a0507150801032a03060b0307050f0d030e1201 77
    0x300c90b900ba003922900c5c0d1060140000598012504581001c8100c5a040c1c903562000c030f41461500c10365114035030500c41d00c68000b01700704011001d80812030031400d103442c8a81c0e8030f1010700b0b8a0741c0d1201407000140c004050600007980120301d42204888000c20004640b012a50303000b1711901d074410500d0105021100420503590010310080d0b0b8800078116407003a0444240784c000300c01e000038110b0751040740c44600090440d1546008036114159070001ca04403030800d4802581c10741c00038001c4070001141114007842c054050f0085408450b00d02005101d00040284111038102080c20721a4295400700041c60304482e49018103200020700c18044c201c01482441e00518008481c0e0103c0b01282d454020201e0307294110342e0b2641180d4000c0a02000020031000c610024511038503042c882c1c15401ea0044103000281d4440000540140c048030b41c415150420001c07440e00c1d407044542c3c414001100400000d100e8100c2c80a1200c01501d15003810b550740b2107803402c0d40c04034401c1c100e205455943c01d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 951408992 1250 951407742 951407749
    0x11d01020d0b03070605070b1f030f0c050102070b03010b0a02120a030621230309060a05090102010c080402030d0f020109020d05160f03050a0f021f02160807150f050c1b 74
    0x844450382c04600034140c061401e2406020f034010902c01400041042002480c40046130b140000500790b080d40c01e011440c1c903807030f24018000c5515800d64098001c41310114035035000088410650f001c0c0c540081c10b503860301000003295407042c1ca900d02140a0b5054400401082d40d01402014280381c40c0819400d00349074032040711012840801000040704040080828a8411205419911000e04100119400418918522914902e96001800040c1c0c001109030301401601040009900a00024845490031a5800001d850207589a0002510900d00350300481300c0154101807400003103641140c5400162491010110036510b5030410340003c007600d980040150050f0003a00c1c4100b03000b600390b4a5840c1d568a00c0a001001841c2d00d0b407040065507585d482952100380c40c020f05101c482480a0004d40380c6400040c80c2c004070841401c08034000802207500070640c0d02d284048800d44018140032a1080351965142c414020100005d948515051040f99412114202c151115420b05003e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 951410242 1250 951408992 951409001
    0x702030d020609101407030b0a080a08030a0c0c030f0e190f0801050705032406250b09120d2712021c0c06150807080f160f1205011d01020d 61
    0x4d03010807601c1d062002540400c40c00190b60040380ca85000590307042000041514182640c001d66998032a48006804209499004600c07401e20444107012081d900300098668a5901c0c1c0001c1c081490040c00107501e910562143c0003508008102d00c506040101c002c800c519182c1d004002c00c4940350006111487d801d0103444e810403003910f00a1301d1444e103240700d400007d4451a203216200401d1000d1a1650b60301c03003e545811641ea0b40c401c005d54441e505542c0200340e1800e01700d404c00700480001d0600180800d01085164039040000d10341003031300044200034285d040c2c2400e40302030510341600c0e02103841e6001d001640e11417206180707400c128403c042c0c034005070209043d900446580400400b10340c07003a02031078420b80c000004100d07207130407031141840e0314030a4100c1100740c402c03182c00060100000585032071004655045e14040c00d41240304041c0e28004d80140b01c011006281c00b0088a0803d20782d401c2c02600500000484242440e0b0000325840c2c03002e003000d01a900803030010340d503070807900c43c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 951411492 1250 951410242 951410263
    0x150306021809220312020a0f11010605011202092701060306051507260c1006050901081c0323061305010f05041109060703030227060412020102030702030d020609 71
    0x79500407524116500d0b40c20599120340f840c1c44031150a103400b08050040d246451040780104c0d081d5200c0c0780b9003400400c1c02c0001d58171800060810307802c5440c1602d0612448060325010b94603c07124505d54800e03807010350301c40345545030480c1820010241c0f00070b5088500035910030821602c1c0065141150080641d0a150404c03071049408682c1c4110f80c52801c400c0b03c40d41030384840791880c0712140c10300310501002d8200002a01d0385002a0f02042a00b020501d4880c00120301010032103603072110b0512245013824000d010041d070040151801174030003101560345d060307000c0c9000701e16007800441c824000c611410300c3c10201240141889a285000f1400e0b0000004070f4a04018a40c90050b107c2401c07091842424011541c80c1228004030f2105030460f20909405009141d6410313041c070b0020020341c4a200d80c0c000c0300c880c0300b003550310a100300c0b0005020b080b80104041d0603e82003020301c3c840320b0b22400c0120b0551000700100001624140080c00c0c1c611511340180a05151040c0c106003040d62160 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 951412742 1250 951411492 951411499
    0xa08041a0a050d180c030602040906080f120306210106030c0617060438031c0503070e010309060c0201060519051e010216080a050c0a060509040b041503060218 70
    0x10000c0042a8018240c0703c10114500d800703d0b010b00b5201c070070840400820005064503182000c04014004140c0052040310019a070030001c0c0c546d614590741d141d9032800c4403041641c20803003070181400314200165401100090600118110f00743c218018008920141c5242d82d4641c501002031044101c4107000821060030500211252034810040c0842e00074203003441213940b941251400c02890002403403d40c83c114002101c200f2001c18903400c032964420301d40c441c0c03181d84c0000401d4194074622404090440d140c05082da00d43d100182c0d80c824000f0710b00c504050342d511113480400d07800c1c001c100b009801c1d03800016416080405221110754980c561440305000b40004011640302d0b0703940952131481000c1d0b81300c600d001000040341080000c0d251600308a400303103004100d003000801c0c0980380b01e11030401c8402c004c1d14441405141c1c080b900c01c107400300d04240800c134507070f0500303408c107000403c001800014110900f05030201e00c0344154006541841c2d0201d0603000b079031048462114450f5084 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 951413992 1250 951412742 951412747
    0x70f0b010b1c110f0a0c0506070e03061b0904021602030610150e030115080607020c100e0402030612030d14010b120705070516120219081c050c0a08041a 67
    0x30503a41c80e612405424080d981c0e9683c2000b80c001d500070505580f4410498142281e1303406070040000c188000902050b02e240c02074001140d03030103001e000036500c6058041c02404d615920134080601d00b13000681c0c10a09040100203500080c3e403184000c0900f08c00b24214104044400c0c0141442c0c128018107025503600410018400b00703150412180045480349080b5a82d200010080703400b42600020350000d000614001182c0c1c050049038540c85200c9607800c0ba0703c00840c0100f0802c25070340c10203070307603001c60051810f030006414030f5002168001d0003d00700f0404808650111450342c3d1041c0c14a140f0250b690350002d214802010a003401024016966400c0c002c2e41c00300140002e20190081d400d00500042503c2084800e00092041400c80c2c8100901c0d540e5800c0048442e1101d20000c80c4910008100300b40711034800015402030325492001406110001d950865002c80c03d000380600b400014002000b01d60010004030046a2042c40c8042d1103618111141a8900c4041880403200005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 951415242 1250 951413992 951414007
    0x5160201051b0d061a091f08060103050c120708100b0c1207140102041d060303070506011511060a02040305070602060112060b0d05010903170a0902090a02130506070f0b010b 76
    0x1400750b0003030a01410480542c2d00c1200150722401070000e0340c03014400a4514a040b1070801c2854003a1410306400d44024a01502c1080c510b06412902c00b10040414010400724015501c2540600e5100180013540741c80e100d880d540000b6a020300303c4018000480000800100e0b0041260100042240ca80d0710380c20182080511034441045c841c3c0395904a40c0822204180035101d040c90355441010300086544548843c980c0fa04410208030030010302d507115020038054180041150540c0d0307040000341074240d0800d51030140c1c07113100000403020401e051086100d09038080c05840e00840e0602c4005941c0c920714544a810280c0d103502800540d08400d00421501c1050146620f10744c1e40100d00103a2180800001241042130f64806020303580b07010404010544c1084034480210601543d5021556940e03592400351825600002d40014003000030520302c5210f50040c0030407040d240551001692240c01043d0342ea0841c500035a042c0800922010620040c0a0014003521200231b586140219 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 951416492 1250 951415242 951415261
    0x20a1116090b1801090c0c0c1205010c11152805040209010f0605041502030d1103060922022e0207031b1a0c01060305030d06170706020a03110708100516020105 70
    0x1413003890b10a603180d44442c4d00c81b9100c0c1e0184280903078030045210395182c43e00c02a04a014039400119001c1d0728114600d01040d02a030310821989142100600801d10080d045880c3c4000103400b140c661000310600b94891148a106c04e90190001c5800060929043c010411102d6040c1d100006440340c101092002c243d2001c22075058a001d00707000a007115420008034910311a031180303c200310780740c04e040380c8103264007030000d5003c2c0c5d0044410f076819031940c43c500896002e481d0708100140d0024403a041c014100780c0c1c400440d01c1c030f43c82c80c080d034008000348124240540f00a0003034010b800400341030042042e0713010401e01031485552070040f8141085404801d40a940d4500f42c00b42c8000f141d0790381c00007004d42000010307560000c1a00c1d111228503848601402150142d198031340744014003202002380000303074401114115801442100c00719101070f16500041c0588403118001c804000c40c04090401081c040381e2026000040c00e49803044c080d5000e00890000300c421a4100700a1040020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 951417742 1250 951416492 951416539
    0x110c070e1614040806010b0a030b0301360b04050c01080f0709050904020619030c120b060703030510210204050f15010f05120405150603070b0706020a1116090b 70
    0x1e240d0030700e9501100c003490b0700201406160b01500d401e1260714000302c1c4410003440600600240c036101403200c0b4105104150907540340c07007948007003224004400c126540c0700c40e250605c80003240d01c802c0076101c8a611a07010100d8116010380381640b0040103074010b564000d0b400769104588010603c40c50404e40e00c001c0079606103205051246007258081025540c414017207880b01c2c120f002d004040e50580a502070050540c075a00000130032a80100004d554125000d80400e0440c0200020302e400c6495406800604015005054025141e440802c1c030350541540c00d2165040e160194103561f289204002c1a01d00040c69041d8424500303061182d542c074032140210071060242003202046440410840e030f103005001460700340416941c28003050041c04211040245020030100300c481e80c03400305056880c055403050f04000c000402c0a90041003c1e0f90140040543c11300d401d9098110356058180b50800c48980031180d0580c490b001c000b0300c54107105040485c0710990b61827905696a01080c403024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 951418992 1250 951417742 951417781
    0x503030103033b12010905100510081501050a05061207140c070303170f1303030b241314132f0c01050702060c1602040609110c070e 58
    0x4001c40c1c0d0001c80c81c460740c90742032405411090f0044040071001d0502c210300c411a1034940941000189402d1001c0180505040241c022004100b029034101c82c00000304030003088902100d000440c08a00f0140034415081c0f64603440c1c0c02c08000f13504180407c042c1408982c40244207280401150350000c106421183d03000c1c3c09410413000c0c80c00380082c10089489401240d02c070600915901004041d000101a01741e440007554042d000d90f910100c41c0100c40c1c060340c10752041c9001400000c0020302c2500000c180b060060010480806070344803440c0550360458903200d18000200b050054003544441c4100209880c40754102c41c68112408590700340c3c14840e09016240e203560751508100d102c195284c030800c0118003000302d0300d0351010080d980b81e004116141055403c103804120141d1000805074010400310440705d1500d240714000001090040800320380207901d803000041c6c1c003100c903c568294082841b501540da054503842c0c0c0c506200c0c45800542420040000381320461041402c4034490 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 951420242 1250 951418992 951418997
    0x33030c1909230f190204090903030e0a030905150c0706050910030506100513030c0909031e080601210c02010606020c010c0f0f0201110613122309010e030f0f0d0903050303010303 78
    0x4e80300c0c1c04016000d14010303035008020500014001851aa00f80e100e480310501a40d410400440303980301c0640c4884120001500060740d46900b40101e00e0281e40b243d0a12040c84002881c0116a803407140c00c240b041d510102c081000480c0e01000c904240750100d0703038101030b46410801850030b0000520003203c03054071401002804142010752000301d60815002d5900003500407110b99036204420050601440200c00094500803503141c114102c0010411800403a101e030610b9543d130b4401103800c6103044181442440300d9002040900010b441100e4100900798000f060403030510078003038a0710100e408680d04128008003510082103d0070007210b050b540c007446502c1c00c0581c1c1e000407070301c054110b080440d10b4050103041c0300a007c0001c3d250b1a0b154414600800200012101558640180c5c00250308000f4138031000c03d4506841c2d0002c1140c1001410101144500741c00803a00d80031440c43c44c5040d540c000d191390304035030f201000554520507280c608224070601750b0391400c0e264041071000605 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 951421492 1250 951420242 951420271
    0x8070e060316091a04290a0f0e04060621031409031b040902060d091a0906070f020f03040612110f041a1209100533030c190923 56
    0x43d4645003644204140e038014002d20054040e0503003815004c6c114a8040d01d500030414044005d4240300501d07034112101800a1400d00c2d252160785030f19490001c0007214100c0d9560300104594038500306560070b01c40990803c40004215140c0030f000400300080d6840341c003801b8404413010340e60000d01850600514800b00500c4a513640100e03000d01554403000b58480d40c04142e1030403c4d40755a008a03000342c0202ca100080ca09051342da41c00c801403e40b40126560886400160603034000c1c85110850010780c4110740d200c404181c003050850b0001c0d013103000000c2d42d55009030304a0074240034540301e8600700c180301032a2a00d0540b91040900c65841031501d016030641056140c0044034003642c000001e001045806d910345000410388861008441c009500d00e00b0021074010003409150000052a0002504640707126905804070310488441035a807600c6070003801c108545070240c0a51101000707000340301d0081c3c10400c0000c1521844882560701c00907200454041c460f01d00707040b5401c151081c203c80b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 951422742 1250 951421492 951421511
    0x203010f03170706110c15060d02010c050f0303010b0703030e2407050c030304030f02010e12030c0705070503030f04050901120503030a270b01061202030907031e0c08070e06031609 79
    0x202c1c5405280806081246041d042c03098001c089030040041789241310a4031000c800d1f4505d036000c008001d9038401d4100c40c9424224006502824111a15900603401c4501414003140c6407440d613031090b0003040700e584001c1440d8081503094000e010300c2a2241c80a00783c0d143d0103842c6000c0301c9201d50003540c9000c2e110004034120320700850803500c2001040c0203580d0ba80c549800c004c1e00f2090801480001503180200159007010040b9005e4202c00e03440a0051a5031075600030b40a503600803242c00c1d00e9502800000240c0340d81c0400c010080e062129102c241c44502c1c1000300040c40304141e10a003210f80c1e54610746d2002400220440303030f01000d51140020404040c5209100c0f0450070a044134200d802d4101441c14003188004ea0b604032041650360300400744a1207002c41c1a40030039900300c4601d611600307040c000034024404903031003590007003a910149160740d00c034200780c0c42d00c1d80e202d120250840722040c00034054001860741d20030703010303001440e22088501e08006840518403a03d00d95551310705600 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 951423992 1250 951422742 951422783
    0x3040e040b041b06020a0c090203070c03050a030b04020706090204050c0403080f18030a05010e0c1c060506040908030a05190219201b0a090c0f080a1d030903100203010f03 75
    0xc4544988240707003d03100c07500c0e104040c1d60b5a00078001a501c1e241c0060300010000d60078002c40e40300b012590756003044001755a60075240d54000d14100c80a042d158108041e49460b03d101500304680a68404918252140148800c503407015064800d000b01c01c000500c0810701c0e44003200c2c4444801c41d1100d43d18070a0440390004a2000c4505950500030310341e404c1c080c0101500301800400d4103078240ea0b0914141c40801c84a5590f451040b000c485443c500e10010880c154404c0e0391140c4040e04c0412080b26550741d000d122350040761103c054075620b5052043d902c03120610003d6071892040c045152140d0181d250707038003490321409441085480b03946240114408c2d406000c510b6810011204070304402c41c0110020845e407100f460080d003688000140100340d900541c00228039503120601d07491044203003100d000300002c0c21094587d49901180c410100c07174500600003441030788007850700c440c2c0310410942841c1c50f00b41c3c490308981c014401400a9811a01b105044a0f0302c0740d030213001c0300c58040d150f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 951425242 1250 951423992 951424013
    0x6040506030a0203100f0513150504021318020708031302030c090c071712040b13050a03110c120c010507020310020a080105030f0a15090206090405012603040e040b04 73
    0x4503802403808014480c5450954010358007a00d510b82103140f07420303100c3c501d40d0384100740c0d031080e2644845140c0705204500d0301d661104223a503410440410445880c0c9000c90140c1c0d10480389044c11a040c0f420401a12081c1c5080c903103030045c0f40384190703e01880d13503d80a1030750201810035441e85680d20443c00441d034080003140350b141c1d00502083c81e81e14140d980e002094011041c180c0e40d425180d0540e024405111040b01c610203108810298592102e40b01c0c1d0142090046c0103404e519050003104c00030034401c00110214a21a40e00c02c1108103801e420325040420f40318070035028070360307603400b40c10703881008542d803003030b0784028a000d5413514503c0c00080d00e051404444503880520000d00084415840003549050720340907401c59158500112390203030380e1903542d14040d080040410105c02d000f84280c00200701140010405810440d149002804036a02a80144070918204400d104030a08404855415140140c060b6060615045400c00c08400040000340341100c0c140000d8100320703442c503c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 951426492 1250 951425242 951425249
    0x9180e01050f01090609090f0807050f03040b0318010902011e180806150d050a0b07090b0a08090d2115030c14130902010e0919140613090b070c020604 66
    0xe210a0506036140b00341410280142c50b1510b081002c089110f000d640203c808240c0e020124022088140d22aa01141c0005800300d4070b43c01000d5039000324180420242001c0c140f2416401d030790b030912080020394441703542c000d958181d050540000145c1e0300701c00001c00f02454241403a90000c00d000080b0382e2048000e03c9000c88001c44880811070301c2000800342d2003000e015040c000401841c400f000040110514014100c1e80301c5a9800002018900e1041d040107035818558541c07512a8100300040e0428081ca9001600300300800c4170008040208064505403828030079000a580c015050201809421006d48161100710b105007400f84510180700854010303048041e443d4864040784250004a04a280700c2da22904100c8004021031142021446d4140c680e43c1a41c00c6410a02000940040044100e010305e481690f5406045000d040d40e14400d12107590b085113005010000b0724509086a0306500f45032000322000605040d645680018482c140200580c0030742c4009a45c6100d80e81 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 951427742 1250 951426492 951426521
    0x20d3209121305120a02131112041406060910090b061b060103030e01090f170c040510050114030106050f070f0609030804060b030c06040b0a05040312080f0106020c010918 75
    0xa540b122010a40760000075900300701c1d50066001e00c110035241e40e40720409006075001d4117100c81408121f030f0039030110755443c2c20040fa080c20302240758038415503040100c3d02510701038030000c400c0a00c41e1060102d5131748000103c4048403070382445d21243c0181c1409000b044c0c026039990482c21102c0d1340780b03401c0e00d01090481ca0320410414070f044456071107010a21044010812100d142d014541c001d00820095030903240b0185110b625151440044440d1150b10300664094900c0d50040f540311409a03074420001c01c039a0501040c030b00702c0010103100342082d2000c204541403005001d400d501c034044560031400301d07180c25240c980c10304203042a454003020050019290103180300800d0307004229030380326600840c2c0c1002a00782c4030052549031090700c00c03456800312080009104900441019104468142c070304582806d440b0341e9031100cad4010320025000030803c010100418058110404c5002d008144094802010008006851000c240c050210400204a0031240c01500c95000200381c09111 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 951428992 1250 951427742 951427747
    0x140433051b15090a0b010f0b0d1107020a270506030316170c010f180b010605180603010914090f060c031b1603021207260f03040303020d320912 63
    0x401c03c4640c1c0d601d511100b1100c50000000004403020040c01781c0048a4620f01b01e185860188051000201a0190340c808491020705c4003101680758203800d000545444400d0105000038400b040c0320000180c000e40355920b0401c801c01c2040d0300d010050f60b10034603408400744004411440c05a4459200c03614400c464034001c03491802a1205400107540351107503850400001022044440d100030750600d010f0102d0500100400c00703a0310502c02020b8451403c1202c4441081540021761268401e9001843c2c0c02e45400c0e40b004141038030301000f034220049130004c01400304003405040e02d501c001402a00d116402000182e410981d0b24001d000000329440403507510f0568580c1100c0394055108154018426404500010149102181d28050700091601222030760f0320401c0c006124542e04035007840c0014031000f1186800ca0018500030340c400d40b809078a031640040c15404039a00c201100e410200c88180f4910000c1000140700e0840300b01c1c1c08180c40c143e803005070981c64030803604519900c88500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 951430242 1250 951428992 951429001
    0xa0915021207111f210f0603030e04050606160803060d140f0f0d02070b0322052506091203090302370e01060f140433051b15 55
    0x101c030402c540c0e10b4412900720f5116008111004c900040d03400d9024003044104402c00882101642c940100240360705012542c42c0c4d05982c1310f81510502d500442c0850110030070030049152601485620441c03e5030b0290420505243d075140d03c0e1044000074006c41800000301d081a00c51500080e4070030780100c02c0e80c10b070100c951200c0d41e172541d00b15a882214050060180c11400010412004401c200da0003466240d0801c01c0d200358a600252800420190307036050106044244503504042d01d000d840508885c40c0880500c00e0008911480103022041c000c906001c4c0d5a04103540703a080d14003901507813841030141e24040c2c400c0c20240e00080d6100460307000c0407003000c8101c170340301c0091981d01c090003e5100001c6030014000c030392401900b4400078000c005025a82c41a800d04108103100c1c507043d403480620b5141004d860740142c1208240f4070501507007200c01e50030981d0b0394550022040f442010381600f180010054020001810011150b05501010b1074030104080080e40c91100da669140e82072 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 951431492 1250 951430242 951430253
    0x1e04090b04061b09050f030c10090510170106031d010e0105070323011509090c091403061302151c27050a020118150c11060a0915021207 60
    0x41101c040b298181031080c041421450072812400c041401d0f1a0710001900340000c1160342d0821001440c1c00d03205c0c1880303004041c4e440c25070354810049241c40b1016620704000030300000030001075840342130103412540018080349a004c00c5045078040d1600182c14107500e445002c08000c50f00c41a0070541c2000352000c044001076000b075000e8000c1d0f03201004102c4440074058440341c4401c000d600d521010b00010881d00709180030b401c105101030718056044503140c2d140b138402c94000c3c0e80e46000203545100280098080710000840d0368004600901052a20320b0500c0304c002000180240200c00c8a400e151040503054240d525180b5140c103400c81c1b5075413420900009140c08a1641e140480c54101c100729003460303202242500350000b011300781c20b20f62078005450902c4201c5824141480111001a0100b030101e010380104001c4d5980180b442c065003440303014440ca414031184940c00c03c0010014260f040203440d000c03111107507480180c8075019030040e400c000112000001400000920808010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 951432742 1250 951431492 951431513
    0x121407060912091d04020402030702030c06130218010b03070e0402040503010609090b0a06052103070b1501021e0d12090804060c0614072a050708010c0e0f0f1e0409 72
    0x1c40d10354800f088580d0300c414001000c00c4450300501d0b03c540c0140031501600b403640081d54082c0a40c01220319003c100b010740c034a8504121002c0d140000032440d1401107117008051146c004400c265240003c0d4100101c40340c01c0d110240c040c1c0d0500402c1001e154a681751030f0103441c001d0070002d008018066035032100c54040c06003d0300c1111404d00c44000690f248580307215210940d007000d4480e40a001d003000c0880300f10724004048000c148130500c030380301c00189158402441050208071412003484a4000a442c0200303451244052140606102002c0100014011240c0700c0601c2c1a180c2e502c0480142401015501001703009030300f001601041454100c0c00c4040c00070721654040100c807207010703070143d5200d10640b03032040051206022120032019001e100d01504c2204106101d502046540d020710744007840d400f0101c1079448404102035a81c0102c3c0d140d0b0b010b581038942550000d41900003507080d482c100b40a40c0310301c107040c0d200500b040303008411400a030b10190080003000b00e5828800b1068 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 951433992 1250 951432742 951432773
    0x1e03090301050c0c0d0807120f0219030c021902060d0608060603100c05030f0c120f22080403020d14070914010b09090a0216060504080406020c010c1214070609 70
    0x80d0700b40804182c40c8803090040780c6150755404060001c0e020040802c0361900c802415150802465060404840d010343c4a0250075640740d507001030f540c1c41c20050a40e21050400c484501385881c240d40e1a603410f4000c291003846407000498017548140701d2001505600401c240d41e294a850f00034042107150000804034082e000403411603100e003018006020507146406e0150700041c005001145843c04100c032084d81107003c0c481207a0030302c200b8a140244c0e4880403141c4040100061041c081081c000007034a02031400460a100d4480000c2c0d01c60945a01c242d21009029640503002541804a0340240140c00c00074601540c8103181e803602008040d24007015807840402c0480700020712905405c041b1a0307900c40142000740d013640c03462080002500194182c43c0758a10800d13140c000031788903201c1c0c984038511501c2c160348c4550802d20020300d8100010226414810380e0060000800c1c003498560304441d2003071401e0b00100f00d001c1070031040703402a04802010b560601c617481c0c08124001900d0000c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 951435242 1250 951433992 951433999
    0x40e0a0c051206150f010e04020a180504200703031b0216151211090406030303020d05090118080306031204060302121609031b0302090c04031104020306010516051e0309 74
    0x5003a0b205007400d403074200640321282c6050700b01d80842840e003450302c01140300b0300050414001c0c000e80c99011a080c1d03400300c8010400904a5000c0c180466860503111000c0c00060b1401c00c02c110140c51410081001c41464086223480440c41c01708040c400e03045011104060061484200c60445000e503403a980105d0300f4402c09a00754001c40c001e903080c14060100080c0350346014080e60f50071b080c203000b4890144101200001000902c0c0b95407110301402004510903500181d03122940c2081400f1203c0140010809034104000c42d40c0300303101040c1752a03010340c0046d0b90360303a6074030785500003403800200040848206a0228000500359090380c040e1400c13800b42030600d1810390b201030091000d00c843d81d0742000815442c034024004500c0f100c000c4e4080d4100009140421500c9400154001070211071180004078001010310420107601070404031042c0030780c1c040d811810700c1d5001801c0c41c054500c0608002101c0030100050003810011503211026184580ca8440401c8074840d03226403203103000c0740c003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 951436492 1250 951435242 951435259
    0x705071203030c05130b03091203011710094d090a0608031603090503011d070801090c170309120607030c02070302060d0b030a2f0108061e040e0a0c05 66
    0x7030303e07024004070b46a10943d50b02d0720035214103000008103a038102030031031540f034403030301d0030408a64402c0b0000354013a0613091010b2501003002229546402107401514824030300309500c00f0002200c10001c80401d0946500110285165111004010301403400c0354020f0701d1880c0e5801c0f2010400d0412500c80c0c40d096840560315581d515604c0203980c80ba00c07580c4035561081215507403800d10f00002041c4c151081ca841c080442c2e44100082c01e40728600c400a0340700390140200e0f42810307002c00415000305075401c001e200e002140e032181402c008042c0308900d0040b174910590300c0205818001c0b41c1d440a00104000300c282d0202c0c255a603905012aa0900032070b00c0c1290300301d0328500005003003040b03942c000c0005241c800810001405401c05a03903041d05445242c00340b40007d003500c0c0b01d001c00c1e01561580c04600041c0c442c0a260b14180302201c80d41840303108000d2003400c0c0c4440d0b00e0350604032145041000030181010100d4000c0203041c1c0599501d000f54640b81c0104040b03d00c10508880302103941c080d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 951437742 1250 951436492 951436511
    0x3051209061e090703020904050606010f02070e0c0f0408100e07090b09060f03011b020303041101030509031206030c0a0f0f0b190c0f06020304080306040c090803160602070507120303 80
    0x5039100025108680510340540441c100742c00302075400c070f9000b031112041c0c0304507503a698003251807040103882c12610740d04108100049540d104000c80100c0002e4402065940d10f000c50008d4000409001071340d8014001410745c80105038142110014104035007120031120725034400c40014015850321304041c0c06141d0b0300040c541d031a40110540c002d4000c0c900a9181c0b2a441000f01c00c04c400c0c2c0141380c1654035520300c500b210b80c00420286103000107030040d55882c54186840e04901c1c0800d8200380c10f2515100078003916034000001e0300c480ba030100d042110349840b80c000292401100e0340080c0e03800040e0450124428401c05500c100b205d01101100004039129240c03c0a5030050041c0051159106c1d4032240186104400c9040700600544000d404443c06403189401ea034412038003907a0242000003803080c141402d00c030f40c40414815250030000305007449051600d0740f26848034140c00103019045da0702404442d60403108491303480011070704101c1c0d40d00c81810245c0403014055010034070b0a0001c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 951438848 1106 951437742 951437761
    0x40b09180f07030c2102181e010201050109200f041206020c1c080a111c05011d010e06010311160507140d151e0603030512 54
    0x1c403080c41d14140282c283c2d01510000030401c121070443e940100100707110b401040fa001344015949032103400618102065850007103a1112411051072050014481001300e0148203070024070050303a0f291040005c549445c2560318070031070f51085e1003008051400003420500da011409074249620307180c1c07100c8024003185040710140d900107244030341d0040030402116104241414204110205980240220350150403862015166040800039148600a880041c83d00c1003612010740c1d041c40c0400007a000c2031080c00710088076080d000401401401c1c03c0c84c10f94941802c050425181c1400460081c40c0481550320091b0041c09840051009018041d042e41d010700003c00d500303170516080b1211501140c1c82c540c482c03201e10011700002000c03250010440c0c003e1400004046141d1041d600700302444261520a251a0810100c10580c1100140580f640f124441074440d50f130b0740c1c542 = true := by decide +kernel

theorem cover : BRFrame.Cov 951258992 951438848 := by
  have h0 := BRFrame.cov_init 951258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 951258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 951258992 ≤ n) (h2 : n < 951438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
