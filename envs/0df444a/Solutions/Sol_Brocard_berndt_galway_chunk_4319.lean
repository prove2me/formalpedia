-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4319
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:14:27.289332+00:00
-- url     : https://prove2.me/submissions/ee426655-d82a-42b7-967f-eb2fbbc30b1b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 776618705 ≤ n < 776798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 776619955 1250 776618705 776618707
    0x1106150d03391203150521030724020c19050f2a0405040b0408070302070306150302010f080723091e19080d0309060914010f0b0402160204020a090b 65
    0x1200b40b041540d00c2000008031400022000065040c0d4000d00400441080c035541c0300074068074010030010910740c02c500d42c10760403000070060643e100003032004115542c00340801a03041c1c0040e01060701c0031030303032031000342c45044c41400f60074501000802c00e180c090311101c51816488009050190074005d403c7c01240c01803040708038448281561a2040d000300d030008181206000c4103005000a0701c0085a0040224510b80001000140000f000d080340e00d000344103c0300503584030750b81c4004450302d84920324441c0559101c108110740c2d00c00c080004800c1989000011403c04100151941828010911880240f00700b414001500842a6031044000519080e503865249849a4903c92400c0c0d18900030600d286032805124127107200e00c3c00710b03100342c0c0044c402404501002c900401004900312031460f1142210030203d01221070308500c00d220319000140304041d1008400c00c40b01e1a0300d20b00e00032801031100100c5000d800c0d0041c8045d940503a80580e46187c05079003181d032480750741c00c0002d80e800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 776621205 1250 776619955 776620037
    0xc030e0d0b09010f0c051606090b0405060603100b01080411061c0203060a0609050109121505070503070908010b010f03020310050901030c0e0a0b0d150b060a1106150d03 74
    0x242180303001d4000c4604000800c90320844018a109903036035080440301003682080003094a600401c1d18000e1075000d000c000540c0c89130303591840c06d42c0100b80c03001c0d5010341c05101440114a030501400588620300b032010486507040344000b0308442401803010309264482c8401440e241c42c2e41c401c461081609074064800e552030892410002e4001fa01c50134040c404031880860618000c142000c2a5201611050f04003460300d801c0c00064010380408550308081020110500c1140380101c500501c1107407500b540302d00d072480000300900055440002c20340c0c144030001080d640c12120742e5040314020f20740981d51359a650100d100d0070350795920054111140000010900114080010545401c400ca04c0710b00d4450035290300035521480000d550080004101d0000141c40280b0b0782e400780d546040104007000108000f034041d400080c0c14901052140100d128180810b100003030344a54a0b408000d002800c12011410700fa03107000c001000d0191401203d20b8800b02840310320910001f40c0b2140880344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 776622455 1250 776621205 776621213
    0xf091905091e060c030c0307090504090b0a1b2c0d05070512070f05120a02090106080129090108060d0c0f03113c040f05010f0608070f0c030e0d 63
    0x2030100c07202c0a2440600d0420400610008a245401030000050060031901e456215001d00c0d0b101601500c11703c01e0f01d69002500c2d0b10307075025001041e401688030501601d011b41080054a100c11103071b142e810401100003901c80d4000701004826694100c0e04001e0019095482c0c581d4404801e1880d4040745405a0004208002415405980094404040190001c21910780d5640240541c02d261a62044140042c0c1008142500b0a81c1c9460849598409030b8011a240190a070005000a25150014405a2902c116042003044c02c5400707404200c9202c4886011800742107091410000302101046403030b954104d59985264004420202c0c50740e44030000d005050103072008039491070300c0c4072210720145040e2950925410010740680d0b15060b03100d07484800440c024200040e410300214000c215601d50707214402c01c135404040002031a50420300c0c124600c54050b03000d4020007002c801041021039024503211001451401c05064510043c40c040c0c03600410807403815085403400d0306070000e02c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 776623705 1250 776622455 776622463
    0x819020c010f06081e0d12090b1303030c1812060b030304060e03060703050c0a11070f0f03060b062503050d0504030c1b0620010b0d030f18050f09190509 67
    0x80b01c28401320b40300c46034455542c4101040b41514000301c1e8101c010003400450087c10070259420a0640008002c0800d5030380118803002640e0007205600508810b03010190144038080d4505000d0812009941003511021010803c5029a80c045c01c055001c50007081102d401440450078020190398441303843e408014126070120003041c3c8684a040301141c40a8024401d06000c0c000b801c00092502c00d500c1e400350f4003041c10b405460301e940b003904c40001c6d0504035504c0d500060440b80001549031840d41c00c203541a039502205241c400c6800f0414404803002600550142e6480d1842401040c00b050074195458000d561424250303d090500b044105540f00c000c503042d5600c151781c501400e224803082541e20011380e0003444040350380c00556100d0a107160a92511f0798038400c0000c2481c1c24008041420040b25190450126007112151030042d604008004642e6146040d01b00e01503242000250380750000b2030300a4010400c08021607001e108008984090100b0074600344418100200c20781e540f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 776624955 1250 776623705 776623709
    0xb03010204080601060c06110a0905120a06150815061f0309020d080309212203050a05010c090e070e060705030d0603080306130203040b041704080f0709050a0902010819020c010f06 79
    0xc080ca0207500b094000300038409d8408504169840b4092503041805010b032030820308291140c42e2003088179010008002e070207001286240d05c59580c4801d440c00e80762030f00c1d0141c0c1a850024030303500c03441004000c0e10341c00e02000c205440320315117486031003890038207034002d240c01c18000e07411012410000003172000171070003140140c503840c0c11a81d00007030012442c0c1c0c40080c0019541c80e01102005a105800760000c4d440200c50030b44905c002a103030381c80c0e40e041d2500d0244602290140d4448d2071071820581c100702e40500510300210f00a00a207401440281188014420070788a075602040d10011320004005580103502415030030400e068030380c02c004103260400c550040c42001c4000301c07640c0d40300d114002d490090354081c0140010f41c48682d640c8946640006078000500c8062000003160300c410854040501301300703c0a02082414001c810043d11f50080c48001001e05046d14500140d9100e01407660116082c40d0121455440800c280061320800e4011049582031005000e6a0340b926440581 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 776626205 1250 776624955 776624963
    0x40e0a1218080606120a03020a02061b03123c1504020c070e100b040e0c19081e0402010804030e061606020301080d09081020180f04060807090b03010204080601060c 72
    0x480c824210407030350313540c58101e8004005070800106d409c0181040310160510100030300c038420f40303c2c01045c1c001d03140d5004030021400045080307040c0005484049003140111f21503c0388480b002000d40030101583d01d4585800015030410f03000038100481c800080d05070210700402c150f44d1000d85420282e6507501501a27102904c00740d1003c20b0f49c60b06101484000c0740c4a0252003410545001c001004003070000788003800700941001400c9041c010880740100e8482e45d41c80f0030b917581c02d0100400d6144550054614054040e0206200240c0c3e00080e10750351040e49864260001990b100c04146180617500e224281001c8007600c1d802080900e401a50680d0701603811644100140c03030301190041d41920a0305520b40000050500c00380240e00a198001002c01c2d45035031400141114600c903070f0004035034410404c0c0b080700100701ca25220210200e400821603041c801c203070400c3c000b070303407125070030303c1070310308160355400000429142074050314010100354003910800d6a4840c8003a20314641d400b0125 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 776627455 1250 776626205 776626219
    0x40302031b16140a0b09181806010602030f070b0603012a02060f220809130f05090f100e0708030a1718030f030a0f110406020c040e0a1218080606 64
    0x1c54070f540514100401902c0080013042100d01d84028250584c0c4401c001380d420030000546007603e203171000300080c001c2541d41801e054800717200f1060b07420410103030070103011904108500c3c058440e100c401d503101260460002c4400f600c1e0303040040c0c01445060340b41070510304101100090000e5000314540220416001c1d54510781c1c8000398451208030882e01b02201243c459075202281180581d01e2018521651460303151031100d40c00200d0018011300480312080d1a6900009803415500845401c0303407810000b0200e41109800950f100c540500448032002d640760b1001740d003448104150402080300001381c9075107403c10800100000941844410201d4056022820345021102014100020103001d54140700c5842c15812541d80064410b84259496401e43c481c540200d00c109260303951203501e00d80e55240b4012010b030401d400e00e100140b1072468803105005041000c105d802c107044d48100c45100314980e20700182c6840596040010880460a102061031840000d5040c0a910211041c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 776628705 1250 776627455 776627459
    0x120e01020d090503100c050c01050a0f06050d020109030611120a050f090a08220518070311090f04050a02071209050310020403050309090a0216080304110402071703040302031b16 78
    0x3610701905038407616800d41d000c50b40d03417a00e00c600d1741d1202609420502c4c000c1d14000c10310301301d0307400c0d94410380304800342d43e5503454940c2c40440d2901c14240101015a070b200c00080160b00042d200414901c0041c0078152180f500401c403408483c203c80c0b01d90f0195100d40014200711102074001c0c14100c0702c5507503801600303011a8244030006030803070701c1d16407028074149802c20600448410301c00c8203400a0032510444c01c0891243e88402806d026000341e030f001001d540c60410300060a0301c907030f601e122081150400c041c3e010343d22013008a034003898050302c0103c0e0540761440560001d104e608809800081d101c459440050344c0540b02c800aca801c00c030100c0c2c904e02c0f030403104e0000724411440000c02a600070803e01d1098144000510391041c04c41400508000082d00c0059010700c01c07200840c1c00303540020400040110840f44070350010002c0d40c0031420940c1503a6041c0b180100f0f800032003504800070001404141c42042103546503402100c8418080c145501d5030f0b90f0342c0c00044045203c0c80b02d91900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 776629955 1250 776628705 776628707
    0x7031d0603190f180302010504060b0f011b05150c030f06060307170624040f0f06080112150c030b011b020a060c0615120320060f0a0207120e01020d 65
    0x141c0c2d019510b07940d82281d030a9004007081009007014824800600d4880707500074808900c03103080c400e04502a40011810389024a0711000301c420400b0407130b1240c1d00181100d99166808140382d5000d49030002c2d4064580d21505040c0e1602d2040b0310340503d4000030030108600c5410440146000c0d1441c103070015080d495400412486000407191500050884800642049251400789400840180c00404034104400c5400351040c110b80c11f10009802c001801c00502601c03d403160010704084004015841c1080b10040403440184a08003000300c00b29005814843c58080c1000c5441d95900b00f001820070b06540940904400390209010620700780c1d070410f94009003044c0010641d40180003070503e038140203082d60744000700f523020344006075a89400150301d180300d4012000780c880041407541d003040d64600240324102074600b20108040c030203010b0200d440001409500201c0e8035102c81115500e81020800070700034400d0182c080c2d10721a0004034100d0300000c03d032210510a0f801d81e018840700c998 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 776631205 1250 776629955 776629957
    0xf0e070305070f0b09040b18160e010507080706200c07030309051c0623090609120c060114040902090a0c1206062001060e040b0108060703050906070c0203100207031d06 74
    0x2050b0b0b80c083c001007010491728503140e44010070741031004000326004030040086024005046900710b0309048104d01900071b840c7c10602c1400740c14000d191480c545a210b0703a0324001c0340039155004299035110008513440a001d20748020070104195407054482040da9440d966884242c8015800700303110590105250914040f0510480c00941284007109015910300700240f20f10141c0007100040310380c040d0501130860245600070507183d001080b107800e003100074608115121a010080880411011940c00c0c004104e260440700054480030b0480030180c0810003810700007100960200b07041c010800c98002c55480280e0b03aa42982e69282d8411400250204541c44d03400b420000c00c01004c0c0840125444100240211b01590300224860752b68181c2c596440d8030903242194106040001880121030820449520124515061103541041c4a800e612030001810150410400c0780502c1c2c25910100041440d0400d01d50046617a090369003001410381080c001c82c54180c00320101400e50500c1d02030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 776632455 1250 776631205 776631209
    0x150606020d210e070f090c08010303030c05040e0a021206040c05070b0402120d110f0109021e0a0803041401090b0a0918060e130203010b0d0308060d05010f0e070305070f 74
    0x1800401c0140240c0380c00380d400181501d00c032400c82a9407102c0b030102c200203000740061006500e0040940c1c0d400c00c4800080c5400c282c116601c0e0910700700105020652000c2c40c4c5046030b0f0581400a404031146004449a105030341000c000c0012803c02c0c4001071030035074000c0440700f003079201d06003c030b40b00c42c0104000e07240b80880c0c050005106004640200d002e00c01d1044e00184000d00c251501e4138104181ca0034844444c000070b010031802c040440500c40c0a008813001000d00c01c00030061314005d81e001031500c0b11a08000d69506c911886483e60b141c0f41c20034294090036002080301c0e1165038031600e171012440c21400c003a00003903d0705000141c1705c5002064aa981a543d181c0c52480703170900c0c1c1c20990718000d00011109407500c0d03440001d248984112054007802e4600181418041c550040c035083d5408514050301851541c2181004130394800e10aa810040c200c500040025031800c160340074160402001c10070303d04d0950702c00d01072100001c02c02c0841c1e01c24001d03906019503400006c00b4520244c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 776633705 1250 776632455 776632457
    0x11040b0f130c0201020c150f13080d09151d0c030714040209030a06020a0503061c03090302060307121a09010e01080a0809010504090c03050a0b0a06120b18070903150606 74
    0x480c8a00c0c105110790000003542c1007910005081c0400b0908891629071a521001001700c0c902060144944050f40300580c01807120103600c441802954a4070054840c101c101542c0ca40d450b40c1001c104980c1a0403002e000c071700e5040510414110030113145428a0b1121901e600d40b18891002c0c1450801040c0c00080701d0010505440810601040c04003a601200255500d401405445000642544068090304c01e0715034445071286000b40034081c505800680d6501d02400800c0d440303000035030010700300f419645c4c15910700f501c9031150242640c0f16038010329032044190411000b680358040139102101c00b04000c40792448a41d076240c81070420140280070705001070308055950800310b6942c0004003a0441c042c0b4009140c20b981c0e0403c801260000c0000c800003907200e40510030100b06a008908012800700c619124042c1b8012018080c541d002c10149061034a920940f0915038402e810540190481e0f40906a5440c3c50030700108050114001200e2160032611510460b6109118090641d801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 776634955 1250 776633705 776633719
    0x304060606030605010323150901060e0f0105310b0c060f0a0e1c170a020d0606020d021005101a0c01060905040b18120a03060810021e030a0b090411040b0f 68
    0x22002201f41d1801c001040e800e0b03522603500030200e894440c0f4000321300911540e0354000c2548036060130000085c01d42d49070107041000034080485083c0740750110303403078400160100c450111101c0849101011740d60380000c61410000c2501c115200020510510803241c0c40c04003074841c0d80d0440c02c0e004680f2410300d50661540801c0c814003550450364030880d4500860b00f400b584560030418032100442c0c04481c1c00c07400580106003441c0d01505400b99070050005070012304551105c2c040c0080d610320020300344002c20b54580010441c07030310048000c28040c00c0565405a03000207154850012940310800c1c0c842c4a41c0fa028000458107090310a60f40159440a01c80d1540e8498510700600c03010313100300541d880c1c00f0f444d080058042261000301241d180c40d48021404624040d1142d0070070882002410080b80100070380707900d06107103048000c84080d5103d60f240e100e07265106510010300a1400c0351380c03c550302400b40000e0020580106400c0340c0111418001074900100388490556010105500002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 776636205 1250 776634955 776635001
    0x1e1b03050604081e04093206040b120f0705130b1f0e0301050906010503211b031c050604050a1802060d0e3004080a06021e03040606060306050103 64
    0xb03580e000600b04840b040e1103200024130f16980d81000e03030380981e01c002c0d14259681d4004800420225001d000c1030004500990f9041c40000c1c2444c004100030032040c030495480350000c40399603070000d0605200421f42c08896180b151a0b0060740d50b4041405007030720499150580045200160041214208014085404024461440d9100c001e1000a40401d00c41d8000d096560f5403000d118a5100d41c000f400109499450f0030107050400c1004011440021401c4015003201d072031540c102c0d408100503c8803e1540c0403082409401c502404800b07000100040e14003c1c00c0381e1041e080280a01021a410015a1512100e13502111a00700c9482035910105415801518001c0090000105100001700d0080208c00a15040c41c0e444005c034640500b07090036400421074190418041c1d2403a0301d45680c40d0500f4800095520280f13020000c045507000594a01a44020b001c0b034941c10440c004880e4482c03c061a012010380b0903400740c0c0c0000f92030700b030f00043d1641c46402000f8000c500041074110070380c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 776637455 1250 776636205 776636213
    0x111040807120f02030f070513020a21110a05250f02040f0e01061d060a0503060c0304110a030501020c060c0306010e0f0a0503160e01060503070503160c1e1b03050604 73
    0x110ba14058a021030300e40e086001503201884000c8108107110007500c0c5850400040003a4116150803045401c0e1040c0120000300d60440b07020011210300300e24040407201c14403001c202a04040e001d8000850010420300c294070b4014000d07107060064a00c0c2c104a2110142c0c0000d1105071441010307140c1c000c107018080260030a54041c00700f2584442d008540c86101c01190390035200aa0310542c52010881c80f1034201c4a2030b11406500690120b598401052400c00060381d180c1c80500368201d0540000040b800b0410428940b03510705a0181c540c21030f080d031303d0604600030f40048541d418140901000203603050060b00c101d0303110350b105869052007040b1040501c5401c0c95103518260300400803007400300c0c0f2960b0801800240541d44400c000015040c01c182070030810069000100784041441880340050300141629404024543d00c07600340d0000c084112406840150064189040503406004000b0800c6000380810300070003d498600c221036800d14402025488040e046810100c0410002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 776638705 1250 776637455 776637479
    0x504090903090f080714090108030406050c0a1b081e0303071107050604030f150c020309060723160e01080304060e030a150c0807081501030b0a0e010f080111040807 72
    0x24500034a010b1621940340d000c40c65507810150422445a484804100b112603050340e144160200b081c0d900d101d8030b51415030340a42da03001d2805480309105000c18814007000b020440c06440c69040540c580c1a00d0b03083c48403003804100c500602c10503014007030f01c031950340d903400d2040805c01703202c50019450341c0e42e02d041c100d03111020010440d280340a6540002400d40ea120003400c0610300920030300c81c0c031b00b04074500603002c494102d08900b40c1e5414803040c030b02101d4020055039222001a101c843c2d0300d1481c2d151107240e42071b100800c6e103004010b604018003110000644c05010b01d14401108029545440e4580c02e800c0091290f40401d9204000501801e48242c81c2842002c0b0003804079035600c182540d8460540002180c0100d18a5a842248400d55030010409400850f40c0c200310707030389081840d0a1034022050095250505481c0c100c1d850680d16142c1010700140443c3d5031114465865188642d9200704d2845842c46a608000c4501019910801100d0482d0a0203000b042d419250444210312 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 776639955 1250 776638705 776638721
    0x31403060117090f0d1704020603150607060e075102010902031b01050304021e0d031805100207031103160b0d11130e041b031b080d050409 61
    0x1041050801005410a182c007014082c4410801030311001d00000492450400c03040c40200c00c20a243c1e13282800041404809500190142c1d0455565034508414414040342140c407190820000243c40702130000c107a000f00360002c80081503428945c0da40c4410365414514546420301c054040c0244081042484050440c2c05101c60441484074428030125450307203000b41600e800340c1d445048140440c501405070811000300c3c10300c0710a940c0c001200081507404000c0c0028014031002b07804040e442072426071488501401003d04680c5640361500801c185c60000d20788582411070040856607180960b800c0c00d4480c0c4990080c01b06c030b0f203561160001c5001d0422001d0b0140130b800c0490b2284481c103414103000e88038501030549ea440914100d6412110306907521666650305001d2060391900c0316017080d04840031743c2c40d04100c43c1c0f21418501e40000140500c3c003034027402200300000308819071000c00c40c61102d0000c800c280a59070542c541d25000600c44030380009100708800d00400c0d4041c0c1c002c0c50 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 776641205 1250 776639955 776639957
    0x3060a0608180d0903050105160906030b030f06070e0406140f0d06060b041d0f07200106051905150901080103030f020a05010e030903010f02130302041e090b011d040314030601 77
    0x1a4400034441154248281d50740c00c03c001030300751003007881440400d000f0903400c40341e0354603040810a207484c0e0040030043d05e805101300701a2510003890b8550383c2040140c4c20100c0c03c4041d10b80c1030601d603c1c0940b414000380381130381c0030341d06005000484203d4415194201d070005810a1006061001040441c1c3d4659a048601d10703960b1601150007054040035102a0003849150305d9043e80f008005160300300000c20400c0d0300d000901c20403050315400080a01039640b064041c8595125900c0218050041908040d030024058280d4071003d5900c0c40c128411102c0036900e1015002d1000f58080d140d2003948610340c04100c941c0d0042002a1244a00d44145581e600c180c42c0000340642e02c450070f442c42594007070841e030300100d060a4145400e03c03600340003404000e001c40c41c1c4480c0071039011f10494980300282c4140e40d1400f400340c000317060b071056622102c40c1d00d1080007c040d40d490034415220080c0500d0310800070701500c0c002c2060066440602a45d0103486e814400c0346101c46010842e417004000c1d074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 776642455 1250 776641205 776641231
    0xa0e072301050715020c0d033e0418090606050307031106030a020c0a03080103061a010c12030b0d0606091d100905030906040e010e07020a0c09150b12180303060a0608 73
    0x444c0018061000d444070701d042402400c80d50010040c02000d980010201001150b81902c241c800081c01c2c40c0041c01d0b044040003048080300c204000740586004540c040ba4403510510350700390943d541540201e000502c03507070707082005039111414140d840040c0d020040601d01c41510129140c5070000203107a0041c144d5002500e05207075205d00d60b0901c06054001c4001c107071014014001c00c8098054040c5403d82c4180302d03010000c001c00002c0002101d000058084070f60301c1d00d0b48034540d00c0780e00500030300d5001a121114480d032520344240141180d20641100034a041015030361071800200c1c2c0b0594401d40c600801601e08503400b018010f0544240444442c80200300500c1c0da03481d04400fa2005000303000382020690f01d000c07055040c040008054204540107401c9800002e0481c0120070207480b202c0c080061210821200c111540819812101c03026001090011001c0d98501003070340700d20300340c0e0710321000c1d2140e520761980e417030106450456104101e048207112180c0314140701944455411501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 776643705 1250 776642455 776642483
    0xc3a021e091f09022a0f0c040e070f0e07020d0f0905010806030a0c0902121b121305030403060c110c0906010c150204060503040209070e03062205060a0e0723010507 72
    0x241c4102d900900c00031000070705c9483e4107a803240700320500034040c500c00805090300142d0404001c5d1a101c0f06629944141ea55017607400510b1002c00408001d0b100c0781d000303011000c0c3c64403503400d282c00c412901c040c0148103504062145602c109440d001e50102d40d1107103038000e0b0a060044d00d007000300030030242d01841560f00d01800700c0c20361181a00185040d1400580d55401e603840300d00c600b400240340590404800300e8085050703000c10300311088074109030701c9031000d6201c9811741e0400000c0160302030490704c0085400b209012035540004070428090320746d900910304d4071390032580b1032203400e000d9a07001e03001c1400101194041c500700c03e61b00740f1440e1407a080850410311401282c000741c0140e0006a408010003007141000c0724100c3d000382040c205080b03900c0c0300100080d9200c0700101610151000b035079004160401031000e06d90016482415030314903281c07090703e2000500b0380d80c0310340d801c6100340c1c5000175940c4160b0441540040007001c0c0c1014210180c0e0040d6000c0d880702008540c10003c82c1c1c14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 776644955 1250 776643705 776643719
    0x11d0f04060e01110c0106050a0513020a050f0703030209041a100f03060519030303060e0405031e070b040609030e0402070302031617040305010902010306170c3a021e091f 75
    0x100741e458000103c20940b85c50600a01a085035038a03000580506007940f814000744c0e0320038880305821016680f0160781c4c7c3c4034400040b50140152800803200210101d084801c1503016005805201816181003010200000c8102040c01701e4120b080d40100a0600e0b458402d4400d2221100c01a0039050102d051f96075040482c1050002140d0100800d6036124140100360b0700d030041c08001c041a6001c0401802d0645400303480c1d104009d94461650041c12010380809480821740e20341c00d8200007864400d140c113003440300141c01c0300c1e0812000110740d0a82a6007510303243c0f0070740c0d003450b41590046d801c0544003956181038064103030042c0c8a03080c822904e4403004083d600184090351180c0b0021607184010310024054440e103400141c000192180e003007509040005195440c850304440103984e000d40340900d95000407068034100e8907008951000b07a904c01c0a0f11500211764420f80b1404508508001210107444602d034220ba403003108100880c40d0352907803c403c81b9069000815201d5041d60398a8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 776646205 1250 776644955 776644961
    0x908011505132013090e060106051206030115080a110103020f091e0a0611120702090621010204080a05060610081b0d0203131202011b180302060d14011d0f04060e01 72
    0x4e11609006107060500021300580920001032510500074815941000409002c40c0510304203800c4010102700040ca00c0d5034250848c525213600f00c3d030302c02c501a40302c501e02071b215580300c68141c032104000740050100754824802c035000a140c80d240c1905010800080001e03100c45440c10904a03501c14055280c07991728501190000c24245e1502d80c08044001d2245051450385502200810401c0c00a1000b50f141c001209030701400490321100c400f41c00d18000454016500340603540c1e588003107008140fd0350009840c10307425002c0c204440315540e442c0108540303032a442d094180055844000705401205034443e074140010b08002c0300d42003540c1721042c242260411035002001d013400e0b8401d04180118517500c041c04015604c002d0020b45030406083c211710310a880c0810070450311240c0d40b48620300c844851400f940c0d0040c8000ea0b61041c200180d00035000000c800040f0b4441c202c00081d010307104201c1084030042d8055099015500c0c1400401040c20081068410940f11106902c041e0400e00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 776647455 1250 776646205 776646217
    0x20303090907080612031e030a0f061e1e090504140f1b01020d020601140415030804031106070c06050f0c0a0311071d0105040c030902030d09080115051320 68
    0x295903c14940703040c004100807190064600391203a0001c00c950b01007441c4000c03031414850b14030381e011036507a20303502c2c0d10000070000241c4d8418814501038001ca4101e8a03070403904440c10700c0d90300d1200103039281d41d140d10a102600320b900403500c0603030800b0480f03106503401c010317800b900030032a000b45007001540300e40c10040212038403030311a00007030584e40410200f52040e504400c000e10042c24071103070000d00a0358850040c0240d140340d45000305a298030356280c6e000183c001401030300500d0305503074a00c0c001102e074001d40021034000851024840c800d091000a5840c0c4540040e20700328050311b0200141d40742c1d4400900480c0006c001c0242010218040202e540071a00c02d40c0d40c40503c0e1200ca40c0203040c00c0090300310240c1e030b00c6608017040041340a031015605403901180e00040a101c1c482d0f09900030076042c10300a401d40900c2860700b81d000e4004480780d00304c4801c200240041881c0c442d0104c601e014038050382e40d02c000a18a05c01141c11294002c0c00041807607102a000130201c030705059050b400038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 776648705 1250 776647455 776647457
    0x3020d060b0a080d1706011704081c050a06090207080712140301060f02010f0c091802040f12120201021903020714011d2505060703030b1c1209030b01090207020303090907 75
    0xb861204000c150701030845184a441701c1c0114030242001400204240340305102c1101c1105840301040c03d20204204503016200210300b1503400d5802e440010f009004201d0708410103901d048070010b00b03049240221514140e102954a00d0401c160f03032011103228059000108022511030b0540c100840d000003580030b002e854407494264000014000d0139501c0e0421032090650030611400c1f18250403200c100300341c403c035240b9441040d60591703190009004070b502c00c004a118442000800c0d04510f041807485134042c054560030500904c80580c241e10802e0800c00b070b80c80081c030503088051320a50260104920618280d01c00c102e00410803400c0d1802c20103035030b0311036504407a5092100001c12a21082d40780c1200c40c56901c840b280c4280961004a11a0500a102c005190801c15100c1d600131040000000d080b5501f04564000210840d0b04101c0d04450800382c121007038034401d0081e01050202d991041c02209242c0c01c251004020b5001038104a070148003e1210306501e940e030b800182d1042c002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 776649955 1250 776648705 776648713
    0xd0b0a09090605070c021e0f03070f1a0a1409040b030607050a1b0807060203070504091103010906080c033711100c030212030402010c1a1005010504060903020d060b0a08 74
    0x201d41400b42c00ca41003c0e010b5420b02c0b40d5000c00303e00503110840c108041c444880102500041100c0c0030074011301c6040c1d05981c1c1070003440303404034050b491010781c4429103640580480255021402e00c800d9031080c4000100802c110b5804032000240440c02040b40e42c0c0094070105245041c4004603140c68401e442180105070301050070300c443c95102c0b80e481d80310011440004030042168035020341a1040090103011260004009002a40103104403001044c02d230382d0403c00f08000c5041c058a0360400e00505200b80d00b0a0070014400c0b00004085000d150000c01500e40c1030700b8500072030380036001002e40490310081400480100480c088203030b107105009a5601c60412108802c0102e0b02c2d05105400043c40160b4480c3e0b408030fa4002010a501940002c565540783c03036a00044c0c450f1002008020000d28901d8035030644071400e0b100e1540182600d40c013224143d6107500065860380140d0181200240b981d4404001500c0e100c2400403440c2d0013820002900c005070400b18680c1c1500b50440c0d0300c9540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 776651205 1250 776649955 776649971
    0x60c10050f0705130504090204150902090112020a1707211a040606090902071a092a0d03030908090603100f1a0d020d1b09051c03140d0b0a09 62
    0x2004001c66809803481c6483c0d0b01e45859007042c503982a0306070007a03a0041d40e84045090441d1102d5000407520b5600c210007020320b070b42d1468981e01039440a00414005140f00b0b12a40f0820003a00a60303d0301c031141d49540c40c2100c48107a81d0b141d50781c0000c2c209010420300290010f03242c6c0444c4100c01c03807403400d00f1000c1280208481400d1410a2000070300d4001c0e460704000f00051644101000d0640318000005070380c1d90560306008020303084005940c1354589902c0705101c1407000c0092945089648032620703240c800c0303045210480105d0600c03602034212108000180009204e940402aa00c1c403450323420342000b486c9000f1030403c1d0402c682400700c40060884c24041500d0f5042140010325030001c8054500d4140528140b0380c0c0604c403c007000150300403800c400c864280340c01503009054808c10402c10f22420010040c00c001c440c3c46051300400c42098407008004044541e15191901a15041800c0e494038410b0007407580110441c0e2485580d17180620b19079038030388281000816022601281c000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 776652455 1250 776651205 776651221
    0x1215050a050306010e07050a3513020a140109170304050a0806060a06050a11060c0d060e06090f04050a0c090c080702010e0d030e07031a0a0e03032202060c1005 70
    0x2000c0d5008988030340e000000410041003980329445d403040503807410300e4881d60840e1041d2000901400030061080b040d00d41c000000801261100118200083c0301c1d2032a151001301c0070b4105245e100294010307100080500c02a40700b046c10380704c1903506140100d44541d81d81c4c00d90354084000c90194485800000c0d0400044c980414141c0240c40d0080c080e18050812400240c0c04102900c40c110901c00e01180016a00340580b1840b94007003204801d64441d482c00d658107030704590041d142509001e280c8040801c0545036030102d54812040030b0f06208031904c64061092140c84001d10480302e5200e49025030b40000c62844501004000c0c03420003042921130b14a02602e1000000d04030b908582c50000c0d500200d50000034500b6601d002810300041c1043c40d22a140e0406203c1e82000d0f1251a0031400f0705520b102c1c58a1462007030304132507020410200c121140645900c41681c44003844c910400131108641d907003000d1249090310040000e0f00d000c4e44c0c03003071141c24000700300c84114a595442c01044155 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 776653705 1250 776652455 776652469
    0xf061221160c030b0726060103140f040c0f03020f060c0f031923160507090c020307330b060d09030807030b090108030f0d06032a0501052107121505 65
    0x3544070705168500c1c00145038034062002c0b000750f4045d56081b5103000b040341640654030070542e103517135245004031519160b4290503403014255012101f00325040000250244440d02190546e0741c001c002d01a4003880c42e00f0051290071000722040c0500490b207440300d095100304004d003030310399280004d12a00041c3e40390181203005034443c8040074280d004510b40d2603506c030300c00b101e00f00300d1100c43c1c8c056165000c0c18407910344141a0040c2c06220301d8807100b000400d0300003005e814000c3c801d00f100c034414003d64640700d1094140c400c0040030510510445084c070b600c00d80207241e81b0303500a8141410440703130100e088151000384001360301160b402000e200741e1680c140602005280306a500c0343c2c0039450122015074a1090b1a02805100300c040b810301410039054101d14001d503040407051644007844d040740b1007034401003415040c115040410008095010f4000e070b42d110f0100325030a00340d28900440212036458001c0c6050100580b0340311002c01c00c44603200d107100d0040340d000031802c4241003100340640 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 776654955 1250 776653705 776653711
    0x90e0112020109030b0a0e16030b150a0315141005042f0c01110406030501080723090402010c0f06060815090a030c170708030f061221160c030b 63
    0x36442091034280940d80181502c8100c940c84118801e40d65601a02030000b00340f0000d181256000d544540007681d1904a00101540e00807858820b0503102c002d6680308000c0050301c4039030451b0550000304041440304c204e2141000c140000499802106040a0a2550100c1c0d180505441c0c144007400142428852608449014030040080a0500c140c081c0c0c01201e5100031000150006440d141d19a402c2d00890032001001c0300c5d180e01d442d00e036003029024103000d0040400a100c2c00b40700017172481000d000010300c1600c502c0140007010801051200c0007100400503410312010380403910000e42411030390680503008903c002403035400e01050508210b08a0360000c0d42c4000700062152000010034142c2685506003002000020603151100f000030000c003100000380e20218410040c40140340007580708030000208040c01e66911410410110030303050140c081907124090011030180b40005580d02c0c0301c243c545007030419800b90812440c001c06001d046640500c10034080041044c4c0d00f000d1a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 776656205 1250 776654955 776654969
    0x90605030a0b15040b12010209012703060c031d07080105070201020403020a09090303230a050c0c1b120708031e0405060307031107020a1d0703110a030b0301110703090e01 75
    0x70300c0031944900e09071260140440e082140718a07002d900c2e6645650100342c02c070380041c02c580049100a00c42d00d0003500071178043e601180d0780005480c00c11030741c9524504044618521030f01528250b440744002411002a000705060341c03142883c66107941c2464005162102c03000806a003400d090b4500c3c02c2d1640507140030306584c01400b040c03006a860300b5006003075603841c1d840042c14090504086001c0d144002000001c452000800c048050841692512030b0282c00c60900c83c54031031104041c4980b080d4000c52941d908504002c15810000c1260030007409001401d400070744503446401c0341003a02d00c3c1e101004030380c00011142200ea0b011010204446200301c640380c2407528140115025200c014548030030150f981558001030a032681c10344603402c0c0c014014500103600e0302c500c07149100603081ca201c1c5110a0303400185002344240501b1120300084500c05007000800d61064001e80b03051009107a255488022180b141c2801c0c001526115009981e01c0749250b24044441d0f90b512010780000c0c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 776657455 1250 776656205 776656213
    0x305091c0f1b060c30051908070806090a060e07030e01201c1416030e0a08090d0c0801141006020703173106030f200705030c030f0409060503 62
    0x5556003200300a1a82500000c400c4170030301608244a41583d0b840c4008040f44903441200c01c05640e02101a080901000d02e8405686c2c190040070f03103001c0011640c0c04002520400022140d0421180c62900541c090401007040c0b038480a1400b41c0c0e610844246000aa44a24034000a20b09004040002c0450390400c42031900c5540e900c0260b11504164040305644603041d911141030aa100701d100c088200700310f10583c181140784001c01c049445d40540040d08100e50000a41804103241c0c0700d85901900c2c10307281074516007c1c0001c03034421450640303013101441ca002403448070078040c0240382500150701d0091840c0040c0c9802d600121500b080701150701c919024000207401100c1c7c00501c652801c1d003d41c688842ca2406c1c6281d0384a01542c11110a20030220040254600d00d6003040d5800e68800b8005c01d9195110f001c100c507a02e40ca10340e000f410300f9050240900b8240000e1031028003480c2a6444c1074060809030b865079001c3c000720700f256200010208150401e138490180a814114094 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 776658705 1250 776657455 776657459
    0x60f011103090d08190306060e2e030e030d0504060606020712320606031011120702012306030d031a210106141212070305091c0f1b 58
    0x20320760700e010340c002e081d00403002036001c407041c081c108003541d481e84419202c03412108040c44008014150390300c628000f1a022451402d141d140c2810544000452039001c00600c0c004482010100150500c188042c142da6030041c20000070140014407055010510209440c102440c00707104a602c940e20040440d040301d9001c0c03158180c001c10000c0543d4000007480300d542c40e1210310034425035071440080d0b481004460100031000c2c000c2039262050700300300c09640849620012071000d032000070326084071030681002080014024192010b4006000b44000540483d140f02401541d40d12807143c0300e42c0228000400400d03107420001d8104140c224039042c010800281035400d042d8400c50129840303070391408076031203c60401132038071112800c8000092004540d505107001c840729072078814900038040b180d040481c00c40000703825001c0400c590800c0b803402815490859007070700020680e0b0350014003007014038010f00c003074022000034a000d0081c04d5941950380c0350400310710212802202c2901410081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 776659955 1250 776658705 776658737
    0x8031215030f10021305061c0f0606020c0112020d050108070f0501020115271e110f04031212050a0615020606090c130314011d0708060a09060b0901030308060f01 71
    0x450341409000d00c03009a154071420110000c1117045401c615080b40d0042a40d046e10100300000e0065034a080c01d00300901c8503141125400d641c01e6002e040050383c400e10b4400d48a502c90100c0c000a0803041400604042000300130400741d07403080c1c2c8650302640c0964000e100f03406200300018000e050034002081000169420a905003029108181030281218030f9914052070550750f5140c0648010000c220105144041c0d4603410712003007451301801c0ca05800300d0380b4078404004440c0d904900d10407041c14946035503280404400c401e000d980810415640d8501001e0003070048034012055183d000c126141080c000d0615560903485c02821540300350103128846c2c42c0e0820584e00305c054031840e07965030030500c5808201000a40d0000300344a003036003a640321401041d84103944285101540402a5048005241d91200507010368200c2d600320001040031010365901040480d44074410105100c4001070016120810981c815408100c10008100b0039240c50b01c0355400704642401d00700c81130006490 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 776661205 1250 776659955 776659963
    0x120712030522060b10020d030605010509090115110102180f040911060c030c070f0806250302070311010f0f06090917030403021e0307020306010b12060d02010908031215030f 76
    0x40302c034050652100042c07090100a40042e2044a0013030302001d00e2a0212000030768480b418044140040d1420202041d00c3d8810411140c20841c003d101c80641c1e402c100b03a80003a40034448006052107030090141d080d0000030700140c900e14050070440a503411700b40040c4080c092000014510603460304036814000740d045140c4816540701551102d854040014100d0b1440c0300e600c4640c0da292188620000d00f10350400c1e203042c15030701e8040a464139621850100c0340d2054503524540c0d203022050040c103c5080c442e5019204030b50192130210310301e0440c4041c00d07086580f5071179100784041c4c9031448200c101c4c40768003a4400034281e2600400880d10740d40c03a90aa8918403411a24000a000010030207040c42044119039a2007070b54041a04095405d104590707176806003008902070b00403800001072040020080d98aa138001400c90303081583c0c2c58003000000a1014030480c14000119070109a049040000c1d0030048181400c40c40a800e1260410308d2a0450a51107032195000c18118281800042 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 776662455 1250 776661205 776661241
    0x603130f1b0f03060c0c0206030703090302120f0c2a1e15120603060103020d030f0c05030301060c0512031308160204180605181c050405031207120305 66
    0x10900c441451440d00307000c16400d075150504203110070040441c8846a5201000440344604070420040c044a90107030f4040800d044040e40c40903052001a03195406500082d0455111b44195514141c510810804607003000075144940d030300111355030741c500728108100b040320301d00180442c0c04074032010aa400c115916848003400383c01400d14454804658404104900b01c0c004c0001c600a41d9416015200d81c01070070b0410800c003040c601080481c2008520039043e40d0b00600074000100311a1400c2c0ca800c198100200300304410b1001d9040812414400741d4042c10490340d4805115204e07040141c9803e8840c440d90803904404c1052140b040c04d00d064000c42d141d80219001c0c1c891200c000c0c025100c01300840003941180c02c01121181083c0080006044540b0800d002c020503200c1e1406440d890f4007581404490340d103c800e840714200b2001a0f60844220f00b0318029103482e4880001c00d040103a0480c1401d50420f02050304810800f50140d114142001c52404121516044001140801c0c00c0c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 776663705 1250 776662455 776662463
    0x3050715030b03030c01050402130b09011a0c011a12070e130201050d051f0b03070f051b1603051e03070f0819090504050603070810020309070f0609060905060313 71
    0x318034500221402030304150700400d00101580d03140d02c8450f00c0c050103480d04507402ca100380200307980c1c03400340c00d000c0c4a544d8a060700a481d18410f0f03800d000005001c250482241c08010a0902503000c411109010f50030001c129103045c610381c45408400d002c00c4800000360092030f0b0300310304001d1000800b02110f282e0701c2400c0c900d280200340310a00050341e062181400001034a400c103c104207c1004004004100071100c030138000c2a1607440810440900007520301000003800709104c0c0b85164464070161800d01201086d0f14000041c0c03200b49132400c07003140b241864014000300100244681800509030310f420326418009901d140cad281280d148d200b01100188490046102c03d014001010243e81890745000c0021a0005007554060424082c0380300303051085040000240190074085404000c44114000400c1c181d003100c003611019400080880301e0a00c6040c00005801d500303555880014041a01c1c4c0f650302c1424880300910380f4001e030704500d02545082043c006d108034407419801c083c3da00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 776664955 1250 776663705 776663729
    0x9040917221d0a150312020d0206060411070b1005060c01050114190e100f0e06030d0207150509190e04061a1c11040c0e030105092803090b030c031f030507 68
    0x3411121131001079500080c1000c4540c100c0784200c15000074131100070211a800300c44459807001e0822059030400c05c904410038805000f41c10000d20145080c0e900004200d40c18959a81c0301d8010910a42280c800c08a1071380d10780c0010000207142912610340c80209860844a941302c41071980321000b018452110941a0f5800064410039155424000740505505184d007884d40d6071410881504152500d901c6170084034080e01c100b0f4000129902100c075105000c1d981c503a010401641d003904a045201e070070a051100480c940701c0100764010140002c0c101407a043e0926040a904880d03038005e0b03001400001e07150000b00e6030b0724100151a15400a07028000c54103651034980c0418030203440e840c0d0040c0c141720200e0841d40e0041064200c1110a500070041a07840b50442039940130301000d400c00c045455450410210250303104c80300700300d001c0c0c107106050580d5106003c003603501c100e404460049001c414440104400d0500928050103e00700340c01c0c081c116100c40b40c90798424031444101c0c0207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 776666205 1250 776664955 776664971
    0xd0807020a0c03061d0607140f04030c0905010f0b0c1002030a0b031f140c09060c031e04030b090a02090a020309160801090311070b09040917221d0a 65
    0x1208000140c90765078801c2c01a07150507035a103010405000d2103400c280c4107101048407400c075884001742a40c851119a500d03000c410f2007140001c242c950040f015200441c60800c404800b00344000007441c000c00c46c46600103010f6141083c0a180401550403900010408000084d64805c0c00a100c1e94110800d22005035281c0700c1c05141402456829031a0307405004052440010405001001d604a00ba500341805524144101101303a02e0081b1105102c150080c82080301178200500a4800310924904592400c0d64100280c8540c840002c1820764a1100080500810142000e926041f1180034024011082a075001600c0390324000e00040b102130f030120000308c0107081044102622000d103100d0100d140d484010090203445c0d02801503000c14003001c5000c0130500000380d200704451440540e54101041e482c100805482d098409448900b90b901203420b0b510b410700001d016540005140f42c0340c0e00074021b1201e40340c40b2540c0c00344490b900716025000150503034015032940035100e5075000034041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 776667455 1250 776666205 776666207
    0x901120605042c010603210306180209030c01450303110f1906110f040902090a09060614130e0c030103050f07150806030c120a0c090605030d0807 64
    0x9201c0e84510b038420b0030075030b481c15440c000710000d841116241c0040c1c610799444008007030986410740300c001c0800d00210383d100b40542040c0000801c00403d8600455030541d078402490282e00c401d540801100e50005080b0200d00e010024007a40c05800e003020011140e120b04621507241c5030ba9808012048018100a041d05400203d03060303119040c1c1088004d580c4070b080007410040810715002151041c46450704d4850350005807081200410651902c4082079581c1c0e80c4082d1034182001480d1500030710040c43d019907800c01400140c2a505001a260064201004162201c1d54000361046107000d80c14826268003011480310500c00b0f940e815900c00b20305962000700d80d0154441040300d0101e00c10b12141000d11001141280c0c003032000c454000c5e814055040c2c40c0d03420345c41040c222400d01620002d40301c0c05401d485603c0b110043c00d03500904101d0300442e0b1443d41c00c00c240da189412803a842d00c1003003400640e49024000000d02008a80d0a02005c0b940d01c0d80a5001c0e1024040784200040c115 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 776668705 1250 776667455 776667461
    0x80f0c030a0203060111070803090a0902040f210b0f0f070311031b070b010306091401020901120b121006060f02010b030709150f03050619140105040e0c0402030c030703110708090112 80
    0xa00b403170022640c0b44c964800d1070300d40381cad001803660750320038410a0030010f0803414500a075000c0d1501400c0000d1402d1500c021207800c9180e00c000d0300116903002181102092905a409103e081124441c1c0c1c441d140a2107040523852005001006040c6000c1c03114101c51000010340340d10081078030308115000401c0003056694001c83c900142001070010000c010420160010003040340304a400d0000c20141c50301882c240d0050b010018005403007101c00401d194500d41000c40140700c080c0c0715099001c840d035007160034604205214003501d6268101006200c5d03001250142d41030300d034030080100c0b0a4403800070781c907560284107502d41c0d5611f032148501c0c1599161540001003006580e500240c9a803894010340b61038048403508902e2035614a0340c107860b400350280e103603c400074518001d1706a0070407040000410392100c20325902d12800442c40e080d500c40c5e20045006000b40341c05a6202c1c940980002c1c140e4030031490042d404402400f0b94000601e94801b610350220090900c4c84010044020030801 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 776669955 1250 776668705 776668727
    0x30f06011d100210020d0209040b0303071721070c0b0603010e0717070803071b050f0d14033619090209012c150315091f0f06080f0c030a02030601 64
    0xaa62000031b80e03801e0744800d0f500601c40c2a806580501050b200d500415480e4003c11001801e408038101c954510f401802d0000c245a48060360144c90b019440d07031003a804460102c3d45400450905000c4005220940e00420b900c900b04800a00c40d690002d00c00c980c0720071084c8189a20115140c103425a40c61040c01110080c100d194102c9072104803a040c11802c1c0c0040e019011074400360300c64007152074200003096140c21200a0100541304000f5601d0200c01411450b000355140000c1c03008240761104c0306000381c4811204807582c81481402e98417100c1c440d4107443e14503c1002102c0018a01c80e8034039030f0010844454a10050315494260700507105030300002900301c0c0509c00d19240d07000500079020204d544841c191151140c401c02940010344601c07055401c408040c5407960981d80303030700d06076043c0c950102d50718690000601601004107602d901d40e82000f24445084803080c0040d0382d102c1c20056101c00c000502d14000e041011145000784405800031100b41e40000c00500d1136400b030210f25030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 776671205 1250 776669955 776669983
    0xb09041107060e0d0801080610031b03050303010b0c0c060a1b030c0213050412020721030201060f0f0602060f04020904031b021801050a05030106030b060103200a05030f06011d1002 79
    0x403103183d00e080d440e62240d2405030603401040980f4000b00b035503907000889510a040b049074203200c00d815611801d515040905403178803800403484001c000603d0602c0514003c000304403000d030716021038040c0d0500b80020f8241c01c50041109000f01020b0540c0410b41540e00074030700070802a00e03400c1d810112100ca18400019402c0003914241c440f0311581540300300d200b00c1c0070f10064220310029020490320342a0500c0340d0980302c0c40785c01d240c00c00201e1440756490540c0c403e00001910f40c0d0340d412401c075445110b61101600306220350041002030740500c0000d9008045800c41c0701c0ca498036034002481c0750f4003e04045c04001c115081c801e5140305190407000240c0e0004c100c4d04100230700c0c00f41036812040c00d0182e43d004820b00311000901341414060801074a50050002880e035031100c0045004055032072000f564003444000420102009400426110b80316079100d5980749014032220122105c09452241000390f8000001d04962204074420b601e80c00482d500304d0b8031019120100c1c608582213011381 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 776672455 1250 776671205 776671211
    0x30f04030b040c091404030f020c0d060902011b0b0a0902010e130506030c03120d1104050a120302061e07080a02131706061801090905011e0207061103010b0904110706 73
    0x40240812410300d20b00c22481480244011501e51070301000303640c0300501821803e519400030a00081c052100311402e000544125010407035080300107030009001203420b8440310b82d01c0c0202801e55078801d500e0b0078001d00100d8222110301c01a600c010030f0010082514241a5641c1d00748001c581c441c8180854111000f000c0e616a08140482c8400a01c0300b5102c1500c01c3c451210340305018280030401e42d859006803a111410294400c10308009403003c80b03c5102d03150010007010074140d40d00e000c1079000d4100d4001a0030761940d60310f0082e1604030040c021b400e00091083c225011160501019070740401c003864503c0040d110000000040d010748841c05070400201a030110306050307100361881c442003420f8100c40c081c0d00c8680a010707500d40d0181916282e12940d00051100d4480c503040100560711440000a0f0080001900e81c1049503010b01c480700960005419001c0c80035900034550101c4d1035854491455240c0104040349215584c6081d0060380c40b09003411104407174400381c0d184d1070340000c014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 776673705 1250 776672455 776672459
    0x303050901020a240f0c020a02091005030f1c02030f0d0e07090203090c130203070c0b10361a0f0607050313080d09080a080d0e0d08010f060c020a06030509030f04 71
    0x36030f804040751082c0000c4217207800d484001c0a8414000c0781500e108503006800c0f02c840c0c680900011000c01401d00080351400100001c090710300300036001d80c00800c00c026001181340b140b0300040103c0c0340f00c94841154410f2001303c858010703060889941e40e40310391703000980310408540c050504034143d10084680744084100580c83c440418807130b24050341203c1d81c5000120b41014070040f0700054071810700003418a2000400101414080c0340c010301c440c1007100c81c6a81e030b0103222030350076a00d020142440f24602c0600841c00403a241c0c0f8010700c036201006008948808a0360003d042c000f080d040e109403005008176106480c0da01c12190165002410340790b444c0b0b8151603c0f845681ca5106299081c4101507010300c0d018403403080d42c400e035a0181c0103800102c0042d01c9031304140c3c001000700a401aa00c0d5003048443d0402c02108c000d840c042e456641966141800410f003040342c40e031009043c0003521400100580d01c51140303a0503640349040c001a2501c0d22203405296028040307078510380034000600 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 776674955 1250 776673705 776673743
    0xf040504060b0a0b04082e051b0708130b030615031302060408011406120c0906040b1806010f1d04110403082d191d0d0b0402090f01050a0303050901020a 67
    0x10019a80e41b20100c984404109280e803841110007000c80712040c0d00d802d20f00c07060480a0b04a80d400c00340c40000c1e2031861120050700840c1b640003e00c05c4034485000500910030703030305141c00e02d002441202c0859003140b9168007c580e28600d4803140c81e10181002002a5000042c802d08a814580140c5229110f6840d041341074000d00c5901c1c0c522131035160050000300c3c00d10f008081141500e9210f40901500d83c01c0c1414000e01190141c10140d00c1500c4186400301501c904c0c00c040503541031940400c0c0281414070000d400f41001d55829000c002c812240134105c684144840e00300b0070b00694002801a80480304a581030042e41c0008000a000281c011090020011b004c4181d8070380040740001ca00e40848848103030720502502c040b20381e0b90202d803503155900031012982010038800250303503503581c07082c00076100711a0313010103c0f01071484105200650800014203a804002d40c2510105941824001400d00d6064440101000310024090301c0f2a4801e015a4051541c410312030b005500701101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 776676205 1250 776674955 776674957
    0x81807060903051e0a03030e010b04051e06100f140d110a1e08070c020d021f030f020702010e13020418023c130305060901051602010501050f040504060b0a0b 69
    0x11003a0b4581c4501030709804e20b0420a00000314941c591802032407111030030f940a6025000c0d80101809039540c039415441240c030346001d114401d00000c00b051140180100781c1c82e12200e0043d000358041d2259040c40384415030003441c40c050244e03032400d01c03915050007800c514103288a04440070b00801d040c20b1600542607040300140c041c04856880b0103408142c01c0d0702c04070b0404294048000002c0201012403000c600485075400624009480c010540d0000e03000729080351041d00160055130003409105003030b03da02d480744410030101c200055180900c20b80000742500c400d120f801d44204164407491801c0724070756045030001d1200d41800c4801264103c1d4a00c02500300c0c0d10381354008400314040e18000002c3d814148005841c111503c854844a40000c82090700044804006181d80584c040089101003081d24480d412003400420342c3d1a10803007007040351031a8640c1c82c040d0380c10030005016a0766005003184c1c00070000d9a0000c0c0540e10f508005010302140741041d90445000c1c1400315442c413140c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 776677455 1250 776676205 776676209
    0x607210f1104031205030603060712020706060f06090e06090103121b0606050a09050f0705090102150c04050f0a080303040b06210c03120c060411010203070b0f0609060607050d0818070609 82
    0x1c8000703484a2801308155134900c001c56000d030345500981c0000710b21502484100555000030240181410388130355500c000c0300c24035042515941c02242c002c02841da80400d082018101d40140e100b10350030a03102184590006000c010109001c10f00071003030551055500c900c0f6215540e01000900205081006c010000c5004090140b42c0640c4c02040d124410701405004013549281241c0580d1010002c407455000071819a045000c0e03820301c3c54000700c0b2002614080e500404100360358070310f0700c820030042103a0240300c1400340d140148100180c6501106480d03000b03421049600e215624800042c41c8103080070b1000c0ca0310a140080510217103000a0401d64481041d01110050314000078040b404d8020365810140c1e40e0312420000d0009911600008244241801164245111075481680300c1604443c9100040250703001c01940b490480c8150360419411760b402480c041ca65103a09403a407110b007001c00705014007000810340305500b04c0411803503014042c081c2d4400c581c40305401000200c00d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 776678705 1250 776677455 776677463
    0x1204031104201207080105010806060a0c03020708070e1501031509020a031d0c0108181b03211312200a0302220605032b050c19140607210f110403 64
    0x710001f2843e5400f41c40714a008520041c4081c3c10040003410458034040c525400b201107008007203001440c00d10400403200601000309103810f2620f0080c96140e40b0f41ca80300c540070b0402d03041c5071880c241c0d51541500d036015a01d15810169940601d42c2d420f402400200103010011403082c2000084240c2c0810205c1e0b58501c00d030b8136020241c8a030040c0203900b17000c40d921122a90030810102001c11502c4544030302014020341954444c000308600301110300100700b4a0307007041100103210b000054403800e128000d04860304045005e181d0b203886d004404031292100784202c0d180003035010410307511a20b004005590050100f12644040403007050000b0040c920303410182e00380080481c1618000c0b44460210030311400d11048850380c208848510400c403041102400000c00080480820a024808420310360360b2a003000f018261030300034451203555440c507901c1d412140500c601554000701410040e0201c80d001503035401d041c41c1c03400c0141414800c03864414034150390402080c140c0801307002103a0203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 776679955 1250 776678705 776678717
    0xe070807080c04260601080105090d0903170307020c19090605060702100503060d06090803040c06020118111305010e010305060601020a030806190506031003051204031104201207 78
    0x1840d40140c501d980d0030b5a980e60240d9042c0301c18050360004c1c4900c03071a018452154815503400321074840f400c055080e044111540d440c0e404121a00070b00b085141403820b140d01e4510f81c600c1c03640d16890000703100f1840d08102d00800201050755948208140302d580b6000410700e0306183c600c0044610040ca041c0704000f450707410404d0004072454002c4c25140314a8014202240e48010000d0444051b80024450f030fa020004103241d50100300544242404148038102c42030341d03800c00341012070480070194003040c116810600d01c0041c1403130201019000e25071000014900159040000748003400d500d03c0180400e151400000b85060221800f50403a03001d641034038440e85400004a88503940c1200c041c011988220202d4002e0510f228000031403602e0000d90303c2c21944541c00603c260740144c0704004c001c1d03035801080c010301c4414450020345034420004c071850076141da0741c1c540000c20102c01c0c0b60301c51941c89503505850001c00101000301c42c55112199a0b5007440c405826408406079035141c0081d003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 776681205 1250 776679955 776679961
    0x302030105072001060b19171005040f0c0c030f26180a080417010b06070302100f051e0c0c0a0c0602060f0f0c09012d030513020918160e0708 62
    0x5062152074141c0340c20791482880e140c0300309810304001d002c1c00e90030003c0000310350b00441d1001010300c995000701340c00400b10b02c0d20362800c0100000d453300306008644180c030380800a031701e542d04061515513007503060810ac5410140004d0070b4410712000c51681160180301501d0a00c10f10328000c85a11034010f107400ea40c0075082c10040503940b002c0d100300003004040c040006104110003454880000d2414400200f075101c14603000ca001a0091034080300560b0003010300806d043c0b142e00a80c02d20440b001d004010314a480ca007180492a07040050010100184020559a1a0074011280c400c4c1d81c00c412145503070514500811100f500703219020050003035101045034514202442401440c81841c1019151281707511075495a02c81d4592a0600c11424250f8540b1030b42e01e011055141c014142519684944940280940300014298041c0030780648044005a88208035039410408003002148002c0c070300c0c04c40d980340900716031240319100d0080c2c0000032070800709100c05100742d900e99608540f40e1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 776682455 1250 776681205 776681267
    0x2a080109140601080c0403060216032316020109090c020a0b1e061c02041418010e0d0503070216030623150f04020f04030507030302010c021222030203010507 69
    0x741c1403101c40d149941011000c50b075150301c103c8405070401100c1054529082d9a903860008a9010901807040081980390000505404c8a14482482c00f00301022543c03540c240c407002400d103e640e0b2a00c100c200c09050880569100e810410060305442000f00b01091021101039903c040b0709104880c0d050100d00000c510100f10019000d0f04200c9031031b940c0300d03074982800f04603400c2a80600500100c032a01800340260391a8022503602d1a804000103207a400c00d03200951100e5036051311042c660303041040501c069000007801e10300f940c46514020703403241c450305000c17400c0004e6100101401901c058000c01401040d5100c100d402e5007244100280440360781d00603542c00401c4a0703d220000040484413001d0401002400380c1d448001c0c801890440c00c440350702180d40280d0819500c0e680300f8a414000c05030244100151040140001d2200ca1240e01c0c03c0a840c3c421882050340145100c620079245414520103040550385c01002841585070441005003c10003e0a0325840070031604400c200603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 776683705 1250 776682455 776682461
    0x203070f1502030c21121501020f0d0203180402040e0c0903061e2403101d0303040206180409020d1101031b02030706051801180605060406272a080109 66
    0x5130183c0b9003c1c0200303800004c090118403180b410f0914140c403040001102020201341c84038070036200d8206c0c020184c1080400289001001c01c0d1210995010258a2800a40020960b020040303a012201241524100480c0107805a40d1268003040d0004052000b43c00004014050405081e001c4658030790743c0c1d030080414611940d0b80034280c4500c88021131455039088107240d18940d500010240c04521550200b40b400181420603c1c010b0b07a5081c00805504100511040181d4108020750841c24690002155446a00a1410038580c0e0b0714050009440d980c01c41c0542035002444800c105029003072006842c152610f0b214006441d0903481c2c0700366007050080c4280060594010340c1024680c4d6180c500030507010305030f84440e9006040000c511942402003491252911000000c94031041c41d095080d1007001c2e22151040e8101740042c400c10403801e01504a01403400d5000c01c5c000d1410404600034501c80181000350700010403e0420307004803401c0b0341110116035031125096039039003c2410032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 776684955 1250 776683705 776683717
    0x50a150614010f11060c0c1506031c02010902130f0e0109170a020a120c03021204180903050d1410051c0201030b19080d03060b120f0a02070203070f150203 68
    0x50984142904400c0394418416502002c103c2d05002103218002c5809600d010b0048690b5020810001841000110240031484a40300c0400700d0f050b25080090010f900c030f07030210090180c810000300240012920035045441c80039000340400c006555920001406059244130468407a07003490745a0f030080005200340364960360040d0042d6031079980d40a180080c0e500080303071101184111030008001c10210b002011484045494060401e0309618001c1e0a00d1105410145075010900c01040b5103000440106081180000001f136030034a42e00c0d05868500034070001514151501078990742151900b10301d2402488002c845141e41e668803c03c02c00c4901d003581d201c100d000880d10800c00194080c1d003000c0744040d40181070034081c10b51012010304000300390380900c0d0140d0002e0120f82c0c00725058488c580180100c180643d00c0c00701d4145285010300b02c0605491090849000061880c50f44d030381c1611000c030b60090030b840040313030784030003481e0004028010307490b095040081008502e400001100c80c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 776686205 1250 776684955 776684969
    0x1819090e010204052d040b0429031c020a0209070302220e01120f060209060c0d03060302090c030106170703021608030108010507051312151b0f021609050a06030609050a1506 76
    0x50340c04c003c00620000d0100e607060b803500036888401e030140103d10200d48004c01500c8080c0900e40c40216010185003500f600d00b0751640c112f02c800b140c2081c40d408a00042910b030103495041454441d50000c900074400c0c0c0c0e55a1100d1919031500c0d10320364561282080841da203610324212966280c41d80c040c0c103c007142c0300040c540300132240140c0008034260003609003883c0040c591420084824046030901526948150000ea0703074100500451505400541e005000c40003060300319814040701506180c451b8891141c0007540c0000101420b100340c0445a61356000e2008100402d42e03850426211b030020300580609500300000200c00c1c5101d2070948483c0e4010300300f00700a035803400d58103100306021000140e410403000400c00408603220701404000b2285854544100a4001ca0050003404000803032821500301c018035000c0c0216900b00201a904807050000b1207446100b1098000c0c88180d000600c0c250800c81c160003480400320b120030209025618913002c6503110559801200c10311b0046030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 776687455 1250 776686205 776686279
    0x12051f0911041404020435030f07110409020604060c0b011202010912050705091003060b0d05100b0d02030a0305090108160f03090f050a05030c0c01051819090e01020405 74
    0x800440c55500b12003104081d000614003603e900e81d0321111404600610404041d0303018460f24003030050240f42c1188201c40248d8105060b64850244c80c2c8a00ca002500442c038951405403e582e035603001c2c8420756801030001d50b0702c80d51090058282a1081000d6502c10145c1c0c000180442c05040c0511440b58141e4034024220f0900e81d4101d010b01703111174196100d20404030045056220a221a405000c1d050906581d441c614030300001030781c04007003226000c0c010000c0404001400060807040441000001040d5010000c02140c0300070849038000e580b40c81290700940c10300da0000018a1421030030f036a10b10041c2c0d580791081c10109044040140016200303d01009828441d51080c68424821a00040103012a88940d07160050004040e41d1641001444154642040080c510791500a00f0710358101114000e10402e4158003050050003000640034402d03e408110a0b200040e007803042c800c010100e100e5000b00d00075009400b445000d0b504a4070200d001c441e0408080f0300e07484c0c00302154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 776688705 1250 776687455 776687459
    0x5060402091906060201020d06050d0b0105060307110a080a0801080a050312060d06020d0b04050a06080303011401050c030a080412030516030b1c0605040213022812051f091104 77
    0x1001c03004200a000d00800b51030341500e000100864010000108040d41c005030b1511030301c00c106130440300300d94820b6102d0340302c82c1030450024000340101e034110b51003210001e40344d82d03c03c40c064603c072045114610a6004000c0381c1401c00503000d0142207104101d42c0e52140507070700c928002c4c0d5101107010001c1c01c958424429801610500ca0b03181d54082c81c0508880030100c12030703070b945084c1d170070501000e0b00c001e032145c00348041d600f0f191188503800782c0719420900145142203c000e4503440f040c05640e00d40f022805001002c1d0340510708503410482d80c4c004490b41e0710240300d001003880303100791400c88107240850052004207203c1d00400d8018001c0200c443c611005425090300207109c4030240703680040c48040f04801d0090003e00e030200c032070301036580412035260620400c250f0f5082090007a1400b441481448146030088441c2660541442803042c00e085a21406682809200f910411403c1c02c02041206c8030312060742c02c10701c43c200710400000d01500c0d8403405080d221044440407a4072800c0c081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 776689955 1250 776688705 776688709
    0x17070807120f050c1002011406010206010605040e27061801020a0f030c0c080f0a0801120803071d030d0918060e070c17030721110307110f0f0c040b010201060305060402 74
    0x100c400e05124004442d1900904801301e012135172042d03141c030090703552810401d0070814103540300c1d40d010500b440503004640c1802005402802180100c02c20518030307000080c040110503800c0e18070071401c0e0107840809640680c11540e2904100ca58204c0c04955441886e582c0105000b070b510201c419440d02640c1d071400180807001800e05003240070401c07004030000b9000c50100380c0206000d0b0f0300c0c88a016588c040c0d000c4050140501030384003112280451201c8800724030039400740c83d0400c1c4d462030910b015032040e490480701c070780006040c240d150180b4070541c0030b00d64002c0405012142d00744840c403071182c54410f050f000c58a0324803c0d00f003c0094480001c110600ca280490070840c411400f07074035002e90b03450b90b44410350030458000c40403d017032001c4884101c0191550002c004917941c8140805048520150160b02014040c0700600c8000101c00248850038400501c00e554441c0859a5048407807140c103aa0b41000218240600d01d404040c0b016944180501c00c133803600500103001c20348490342 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 776691205 1250 776689955 776689973
    0x150b0c06250f0306080a0516080a0c090b03011d030415020f03030103261c0501091e0c0c050a060501030c0e07090b1b2a031b060c01090516081c1b02040b04061707080712 74
    0x8263b54555a60b03001c038110345032004105045180d151006586550070320059071040c5110500c1c21080d907101c0c0d034000010100020480341074a52011811155a1101000311605036030061400b841d84d4002c24201600c420206560100c2c1280031010b00060340d80d004a40121180c0c1298a255003115103000070444425801650029915107004e0200c818a51103890403c184c40030115240d60710703100100180844040c50401401600c41200304d6400c10391400f608529803446101d0722004081400702107010f038032908800000b81101610800e80401d14840c00b011142d90091480088012001c0c409003000a10745070850030300c0f034280302d04944207400c01015401c90a0444881c2d03403074000600000d607007401a41d80902e604102c60440302e0601c2040c6040220302c40398120480c04550300c00c903506a0083c010808800100c10844a251300f030300210300135009014000d500075040180c001070040404404140060b920425a050386454030f0143d41c9903c02d612913452020100003041003c00c0d0049 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 776692455 1250 776691205 776691221
    0x60e011d01090504020708030a05180a12200c0a0f050303041a04090905060103031407021513030b16031506080712150b0c06250f0306080a0516080a0c09 67
    0x105005501a99820000d805d80e8010071040b55198004418804051483e003c0ea0b0303040100d100c08a000d91944000c015900c600341c08024100d0007810040c00b000b14059000c0e117642d0302600d40a200c0d428011400680e071403090306041d0380900d019480000701d048048942e401600c900601031481c081c81e1034160303031020b10200c03283c2800000400c0001b070030711418441e0020303c83c8144044d00315580345040240814111840d015000c2904008941c0140d90341c1003120340517056210a6a1903484840c40b900d81d5406a80005048072260024040c41c0b2404d840030112000041c1d50074008905560842d0742940007600c58900030413491404280d5081c0548820440708081a10005020342e814001018410320f640c400d140c65180012200c0440c1c0b8107100860380942004007410026900c403206003c255001001d40c810040300007001fa150920a410810042602408540e401308142c24280d07122080d401c1081d514001034500000c81c91000f0405404040d00441c952001c1460111349101801c148 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 776693705 1250 776692455 776692457
    0x150c16080a0c3e1f03061503050c0306040903020c1002061501020a080405010809160b07060e0f0a080a02152d010f03020d0c03060203040b01090b0a0803090d030e0307060216060e011d01 81
    0x1441c0d0a8800c041c0ea081340e90845669004108a46045880341960302c22140b1042050300b04001c102c2c10201840c1240d802c1017081d200003c0c0c11000b0b040403410300d0051200307242d0048001a507403002c1c0c0d030b00080d00750140e00c113402da116154070150016a550900b0000003440c00409000400082d8044c0613910b40c04480f1070282c5003c0c83d16500301d5600e0940b540c0050500407404210748050040078807c01d0f074800b1004c3d00406c411070700c1d054203c0d95012021001002c40400141d40604a4420700420340f51a1401d800c02100b03081c82808000603101d4040d1800351040078100310300c4c80d0080c0f01c0500d412a40c50b240040078440c255028001540401c19099031481c814480020004155200443c0f14074042c12a03c6259418903500d2015201388001851150300e60281c00e1021010120071a2203038a000ca654540400c414a02550800c4444050f43c2c0e2601a030b1400041c42500130408400010300e000c80002c2d040d850b100151490500c40c10560700091030300e01440c810200c3c0090102c1c0303500c41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 776694955 1250 776693705 776693719
    0x10c1b020303070807240b030a02091b04060903060c020102040e04080703050712080406060501110c13091a0f16051903110408010b030f150c16080a0c3e 67
    0xc0d40c4c480070b00c1070f8401d4208a03029102001301d0b000586003203417541601981c155042c8100241c1c8030010b82e4a080002d8007911446042c0c02283e06908060180c51100103110020754942d6501c12010702007000605c01a510f2034100b102c2c170500c80e4410b1085805a50504c008a05152141d40f650030407904400b0046062101c208a000081401194031814130000c540d1410300c6450207142c035105031411030341f18a0501c82d60540c079a20210b408506584001025522801c1c1406012440300c081e00345604003034504251f11440801e0040c446001c507100f80340092540090751038110110169003010040384002030024800c01c00c08074a004100c030440801071038045050020301c5c161901d564400c0e4030103985a9540c0e08a40d016007000c2c4803c08400b001e400141402415800082c0d03402c010040c18014541d00004e000b03a2040c18001e4440d0403d0342026445840710f070441c0c40540458030503c0c050f2009240c003580740391640b00c40314114154410010800056040030244003008001000200d80e10183c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 776696205 1250 776694955 776694967
    0x92304050304030816151e0621060f0c02030901091401021b0609090108242e080318150910350708070206070c020f0604180c020d02010c1b020303 64
    0x69800f007420300c004032645000810070098a84000e864103900e500c00c01c4141021010455004083d801c280f505560310728060b04061507180c07500041c1058150403d072f9a240003004c2d208694000041c18501500f81c171400c40e51610392003034200c296102241e00d8016401240c0a0340300c81c52a010405080c80003500441c2004489800240360480c00d8100c2d51082d4084131803a41410101400210a000d141a8140847c01d105410055119407031f911182510b255200d00c480703d00102000c18010088001901e44407240d5107a10646105400c221600c26a03032072658814100c012070464140c0f61000b03240b8003807259402c4003600e241100c880e0039840d48102210003846280b4860000e213441200510b068031510307000700050705c100b074098150740455121404001d40e840d000700104010f190101d80100e141145030b00080c20038413490b04075580018820001264181e003e400808480e85075800f6a40f02d05040e0b0b404a0885000c0d604220004802c815403985090304100b0a0b000c0e18001303030940303160003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 776697455 1250 776696205 776696213
    0x2040207150c0206060f0906120307080d0e2a040e190302060a0f06081906020421021f0e090a060812031005031f0f09020a092304050304030816 63
    0xe2038007501c40c440a0b190700826001030b5052001950015007181c0c894480a2500c02040500381d008220502910b44018003441c40c04040003520b0405900c981030565031120042024090808000c095159118092091805a040780440122440d0b0320041452501c0741c10100005070460540046c09405680c4140001e0f12920204205030b03800b83d0000e01590403c3e100b40310454804011045015152160500461001103402d590181204400c1d507465143d606080c0d00920460303001d48100909090040880f44000c0071411985000301c9440000d505824400708080000c100f5542c0001c04e4455064182d00e0941605600328405901c00100940c40700f00540c0340c03c0c10295500100800403040101c89040900d005000d0601900500100399034460108140e00300200340f000365070b4075404c04c4d0b03601c0c145076400114403640050883d1807040d81c0720031b800000c1c00519000c094a414800306024580308011541d40141d61260087d40317054611b0700c4038040f9400c2913000303074000c1402c455000c002c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 776698705 1250 776697455 776697473
    0x409080a051201080f0c1302161208151f020312010f050a140d0303090516090617120f0a05040f091d010e0c01030b0126010e07090807030f02040207 65
    0x319400e4039030035980c046025042c0450441640a54500e60105d5000d0b4211400410300c4141c1c204143d514a8500b690000710700041d00902c10700010251120819005014201403480001c1000d034480702c4280c3c49044000004d40810b0b281c0303e8004020000300f0501c826088661035941c1181d20549090800b004c1d82c00b0b110360000ea100311a491840001404140303080d04200e0010180b030134a8030b0260901c40046018100c0401000d010316030780368074007010b01034107010543c480454071860480070313502c508241d0010301d00f90060a0010441c0c40307018400303800004111514035180b009075820320109804a00241c1d21610f522410050180400641d00341c0c200e0100d4007810070040e002c0f4032322180c203200e0503001003040c0c3c080b4120b17814030320700c0516804041040400d6100a203000b10704000e80c0c200607201c18000c101142c4041c0c0940703448a450446184004d41a990031104120b800e841d50001201c4100d128010310809411103a003c1001681005030300031403a2014001502703004154544100c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 776699955 1250 776698705 776698717
    0x210912010f0906110a0c06021b0d1707030c17040501060506030903090405070c11100306052d0a06081f0f1401200a0201030b030f03070f15140a0b040908 67
    0x5842e07103408004080084500542c9001c1420495542c1815503401000b410401d0002c4013138126a13000580e00380c1c0460110101400780440c608540d003400781c84500810300500c407401409620b1140000c04d2425209024191440b5100e07940c038141929501703181d07607440c0c3c07028204032275039035844c200000d60741c880c40d018500c1510303250055500e90407036400b4003040e1080107284034200302c044803400740001c46000d40880402c0d4280e0380070701d01c00b8620b02d09800a01032504015884130ba4000003c4c084510807240300020108408240030b108052824007031102c80d54003c03000803c2c1d21100090700003103030807040c0c4034481c00e501100d242e40780d40316000000310b80950482c41010aa0a02c0e40460796080a00105404100c94014442031b040c90f0003d5101c0c18411002410117454065400d4259001c11000c40003104010a0b41e980741041d2031310114140e00440c2c00c445044640b0b42d0303c100d541041c8031390171000c1100e1504201c2680d43c1484c010007000b004614039805555020038a0100e12884c0c05000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 776701205 1250 776699955 776699981
    0x809040e010914010e16150e0613090f0203040f020108092b110a170c0a0c0b040e180a06050613050115090803040321110d0305010e0921091201 63
    0x344a074542030030300d0309448001d00b0369082548040740799103e01c010260002c00f15680787e50040704900010104441001c60481c2a0303071303c034401150003000d01680d9030544049400c48141088103c14907000407050b030004560150088001505040141d40500600c661149402c0192202058500e04001241c0310345150f41d0403449103540d4645115410401115580f0181c10050003c0411079851800107143d030b03001c1c901c1c0c10b03002040c6072042040070465082d0403540404080c0c1c410740c4800761404990007600c0b8514220342d101011500440b4071412030302444a0207000307041d00c61429120640a024041e09a0350444840c000c40314540303060303125a6000c0c20010044030301c20710380350b03038000c142118a0f0003400d80c5070030401040000441e80c03000890640300c5101041718403a000c0206440081c000300840080e80140319003511640d0341588500e05803004040c8001d8541c88002c055a070b10241c0040e00711101410142d0009000000301c060300c10194000d01d05040ca40004e607645007512018520300e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 776702455 1250 776701205 776701223
    0x60c0d0923060f0601031a04020c0115170106061704170702091303021e03041707150908060a0204051e15070c080c030109050304060311070b010608070e03060c070809040e0109 77
    0x40306007000f5040d490341256007460305020440c100d510321250a10780703a54003441690b00080304040d100c0290003401c485c10340c501003101400d81c0c841c4c108078400304203100c9285035440c2840c00708030075004c0e0140501454003248044020754a40d95000c1445001494503030060700144000330050342c0d109a2140302c0c00c080001c01c00132300d00905d00030b854140c01c0d001000820080002c00f00840c80004103071011580c25031048640380c000101075504040b100e8009142070300310007154001607030300524480d048400c08412203c85582d80d51480c001c074040d6000d090792100030600f42d80c0c21030b8a000b10003018001c1c0107080d680d00307101c030410110305a031040f03804a500381000c00041200047c18499016490402c0d0028403045039155651522446076004030b405140e0703207130003080c2304800c1d0350207886120f030f408100111a56140e0030007400d81e0300211381c0100011170b81c2060541c1821b011500d18018010383e80c41500706041d0385e4178102c040d00b2440c0c440703400603070b01c1c172252103004024010b90300c0a44c0038069039 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 776703705 1250 776702455 776702461
    0x150815150403140d08070e010315051504030c0b1e0304030207051e121603030c03022103181204051c0609081b0607021c02010e01050c0417060c0d092306 67
    0x60403e19104d022900b804904002c011100b0381050030228511070919001a0001049651449901c115042250002034800c484420406e182009109880c0240c401d5805142c4e5814540c0701407007411503400000c1c02c0302c03811164200b516130245410510074010b8404003a1140302103038612411103902c11a82c004140c020403141080301d403820480e60000f014011001c102007a4403c1d103845440300030304102c81001050141407090200310890b041400d1888414a01c2000d0016030382c2060329514603c01e1030203081508000d00050205202203200b20a0381010300c2c0004106030711941d4080d038551008205030304000504c040c0b290344035041c4555546034580c044100654204d05103007140c50210b51004092000e03264001441002040d00e03078082010007030510701c04078090445181e40b0980340d1f092a0500c030a40c0031910191041e01da11304e1805a8460900004654401d819a0480c4c03041e24100001042280c1d1030b000084018020a0841545048000b000c8141100c0c140015a290021014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 776704955 1250 776703705 776703743
    0xc0603140411060c030c0a1a060319060b01030e0f0609060c0301030b0c0a0302070807031707050720180123090402060315041d0c0307150815150403 65
    0xa50440302055201405149002d5442000d000000e400701d600c10303039000c41d0710302a054042084035181040f0308162900030140340b81100f0034a001107002142e10b40756800041031820001039030725041e007011806140c03404058442900030080881002e040503220400140700354010044100f091581400503c03252801640b00390402e10050700074103041c0b400304010000315000c20f0b81c1981109031061020303610031020500781c0c0240f00d071100007414894089643c0c0c043c140c00400f11a4200e500d840b030721404c0c0c0e030303180030443d100c1c851004000c0000319070384815181814141116820520050142ca00034002c101030700e41021801d034412040d10b80c0c48040480e41d4140700d04201030100041d110305000f41069400500c141c04014241196400201d500801e143d6540d004071488030622005800c80c0d0307480740100c1d40c8842c501d20000c1d02038407070b000c40020018500c3d2503400701c03c2d00940e01c0c1c51442d10303980030003c5140da82403c550b0303004200300781340300a2420010081004610509584500403100342d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 776706205 1250 776704955 776704961
    0x10b0a0e04051006060f08100302041e0e0303090721140304080c030c0607021e06030709140a031a1b0d0e010c1403070c061b080402011e02101a030a0c0603 68
    0x24500196007808800c11280c2d4024002c10321090700e0b03047c80d90940e42c03032400c045406031f0540d1010b0f5010b82401001d084030342e1a101500c204509554040c84070182c0125041e0340d0f4482039424004581c0940c8080040801e40041180b281c0d1b07580030f80c1081c410032034551700c1d9008072507800800b480d00005020014030000b0000b2800c0040142c000d81400c0840b0b00006159000e80d0b4000390040c0b208203035000703080624140301c40360441c00070b0045443e810403040051070f03030310140500b449501159078035280b98030700300203070b6821240d0041101032201042c14511100d04c01c0506a0104160041d00e607a582030b0280c7d000d454413426a200000d091445100c00c07500392500d0003448824445480010803003d06d80e003045940c410844c0c10048000001450501c1c010030014001000346800e030120394803c241d000000e40d010740c3c000d03a40d426440c1c940e0400e40390416600041080540d2081e03620015605198119500e82860280350560a01e20309002c04c6c2410078580040300c42558000081c08041c2c2c040c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 776707455 1250 776706205 776706223
    0x50411120114210307060f020903070f0b07060207020d122105100b0906043506090606100309120c0309090605060d1a06181507150905010b0a0e0405 65
    0x1c0206030518000004a4440150f142100001810f080080303060a54200110ba01642d44118100000c80d035503070102c0000c2d00b03e904024030074010000001341d085140d10352348043d83c580b800b9043c0b40106554605000f944400402c98200e01d20107504400300e150003507181c80b11003064550260222411a09540c02c01c1e26044911105142034240701c05003901c107003600203079541d400080c5d036604008000035046000c1c56104800c1081a0070b0050350758011700d0105919401d024408811100798601860340b20701048484074415403007030001404a1600040100701940c10b800d0001e40c0a034640c07503254440344100695400324a02800030004c041d400007402004100341c05d41000f0356400c00d4001074444c45541e49003000d10b52901c801d039044030342c9041c00380741540f001403545546904403a03207003c8810042c070b0617034858135200d50081115244001203a20341544800e46000b01a030251007103005286824058519641c0c842c80c07520191240d00d0b4180c00750545280c282445d250514000d86440211 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 776708705 1250 776707455 776707469
    0xf0e060306011d040b0603030409110d151a0f30060307060f0e120708070305010b150a120e12090906100207060c0321060504380a0504111201 62
    0x105141c3d900200309003c01c2d40081c3d0110b0b03001c005880c0c04000030b2641c00303140c010422151034426401c0b0062200001812165007400d02807090201c088070f8000780846500c5680c5240d600c034504038030342902c0340d00100450190750004505025402e80282c940c90f82c07104015002d5031240f0442c0204140c0c8404055012404400402480d401c149000700203444003404e40c000d000d14580310400c15500e070034001c0d039402c4080f0100c419081e600d005071950b0700d001e4030059500c0c0d443c12440c4091400c20344102c001d504d059440c8640f0704442c128080300c208070740b440aa40c0d0b003643c820fa025541300041c0003011030041003aa0761030f11008648104014404084c00c0c81740710f900c50b00c107440000c40d000f094100c00c03103007030303080c0445500c92900382a03400003121800e19019407280b040740040f05210368480000c2c0d4400751402c000c011116900c00c003401032800005015074a8526a040d07000c011980000c60b100d4015000d080c00d9555480460240c940b042c0e01c1221034840450340b40c04515020300250300510729 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 776709955 1250 776708705 776708729
    0xc0903050114041e0303110c060402150a051801030e0106082104050f0402130f0b0403121803110301060e1305012d0209010c2405010501050c100203040c0f0e06030601 73
    0x11130764400e61001d840c1440e01e134503c540391500000340b5009621801800040344c442c0b59903903003410304003a1900001c60b400c9200308170b85001108040041000c0da0b141d80c0e2152151880d2888031111020070946c4d0030089410103482d640b40e1051050280104001004c604009282256041c83d60014030944161080e945a005120420055507045085945010140d800603503a42c13441c251500c03485950f400218144170030040018a0b02c005000410840740110034003608410401c1d4101c0e0840000710f080e910150080c101440810301c8840c0b404042c0302c00800000d100c582c0e80d00000540d01c01103880103400301468a20301c05216082c098013140d2014104040c1a07203050440b8001d982100d11540e031140d542c0401c0321a040e234001e0042c20b00d01d41c0c000c028011612810030100c12500c6004035080300306403c04000041950151040c0e41c0004103d50103022003030b00409a000003508010030503a5040c03410400020b420440711068400340c2040c181000103442c108080c1440c00406078030045d08170036 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 776711205 1250 776709955 776709961
    0x8061507020901050904020f1509010f0c0b1b0c010606020a1a07050a111203010e040606050118180212010303020d0305010e04020a03020f03101b03060e010b031909060c0903050114 79
    0x2e120325803241900d0080b550201d0f1505c031741c00030030001d0311525003d9801c24940103000c403803240d515026046542d000d80e20340c000102c802e1001c403502c00166000600e4030b144032000c22280307080d11000020311307284a025a0306205032580d00c0f030f0035a1071642c801c40140c1c019040510a10200502421402c4507410714940241000b0a005020780304170002102001034004102e25420800d0000460300d6002302d48207030b1296102c28410901004c1510100d59403890600700082550107102c40c4040a0784200300c2ca064585040c1d80c1b41b901d2548072001280c1c070b642c20024810288040070584e030203903000341e00400d0308440880f40502154411b80011103006c01d01c1d000c00c4010b81d16900303040c064070b0b0b050b41c4140482c0140e0010a07c1c081f0a6502c01d0030707507401c100818a1005e581b202071450800195000c1c42071541d41c6402c05410082802412100c010410010f0350340039010003c80240c4203078810014182c115500c8820403500d01c7d60641002a08168080081c40001d02447c1c0d8052901c41c0b092100d41 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 776712455 1250 776711205 776711209
    0xd14060a0602250302030601140f030f030f090612150a08033a06030311010b0f15160c08010f0e0105190b030309041107030206090a150b0d120806150702 67
    0x404040c4100401e20310018694483c0d62241c0d0500005503406021203000c2d50b16810b03030500074084404030300c0c060b0042c54070201151800141000d0fa5603450b0b000345180c4140401c6000c110350052017102c6e0000c0d03041041e8954100401d0b482e5115010302c407600c4103088007210130005540200d900c080c3d5030f940240641035034a480403505101844a103010201d9a614035040d200d61100304040d540c0409240074400018580c101c44e01d1100300c1481c800030000024034204001d40b040b003030000d44d0b401080c0c0243d940b0981070040003c110743e0241644c00300c180303c1e05584120548507650001d035540e0351200c13aa103624000c24050804400305d80d900a001034600481c0e100c400c14400600d00350310079140c1c848440203450510494203100380c0a40240014031240001c030b20aa40172090480044c4070b5600000c00c1c400004c6045580203511015548004081c8001d00024094120780283d0069400c10040700182a601000d0401c10180c8c035442e01c1740c54140104250305800e000c46609070501000180016 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 776713705 1250 776712455 776712463
    0xb030c0306101503090b1005040c090b03010b0c0118050f0d1b06200412120306050d0f050106090e0a0303050f0105060a030518151614030402040c020a06020d14060a0602 74
    0xa500345640003403803d400c1072012409408078601c0070b401d141004043c071080724040345110301920001e490030301998840040481310b128080c454241d40f01401c0c030041c45490640c00040c040803c0e0315001080b51070b407103040000030021882044817241d02c0031155060440c0c040c003400141550500303042c41e0340b0620070079562030462400d500030040c580c2d4100c0342c1140d0707041c1c0c21158015800c0303414860f1a10788070301403001302c40d03075001d0140c44500c0140c40c6440d080b03129005020980320054030034242150183d0b551101a0342004c070071a041d54807280c000c94102418803507480121407820040403004100d04000e0100c2c5c0d8054041c0c0b410b400294018401ca80b205011240003400c103150000d0959a0091100e00c10742d26074031084020b02400b01c1c22840e001501611078000c45840050f030032045a03403103003641c0950008821039500081800014050710303140e4440c6800380e0a030b006854558110f5524003080364064034001c90744958901c00c64940740b42003d00c055100009803607080760700d820190042d541e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 776714955 1250 776713705 776713709
    0x120d0215131e02032d1501050a030222091a07141b0a1703040b07110c0f030a0b280908071106070605161202130e070c080301090b030c030610 62
    0x100e142c40040b020454908121300c444000c20400300b0751105d0740502410b01452118002941c01c0e1145c900f8503240049903440d03040c1200d00081c401c0e00d40526603424000c9050400c00c3e0011040003407481800c45540900859408610460114050003031000545940441c09080e081c00c00c8800070110700d44510b0601103c051010207d1394140c0e1815041d0080c0c503141c45243c0040103074501448415810709240c0165029600ca02d5003124281c0e24144115400c0c484038201c01c1d00c0da48800d199184900300702c002500c2482d00034064401e84003164540c10707410309013600d5101010702c0f914801c42c01840111030f030540b401e100d02d00512201c03c01d5150911701c0d000703146024061142621701200d06d95946801c40322903940c410400d00047c5031091101c0510804a01d035903010408903501d01000d60760901c00c44138113400e03041794003082031b0a0820424100800410400a10000401c1400842c516401139402400b1103200422811440b0080c5414042c1c00b0360750074001d900c0401408250600e691640341 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 776716205 1250 776714955 776714993
    0x21111c0305060307030f0501020a030e150c0706023105030d170a0e06040b040302061b270d06020705070f030221150405060402030705030304060504050906120d021513 73
    0x3a152a0040021308204140d80020005036224031030030300700441900a04440320054400f080250306003044170b6100c2004040ca0684603500b200007500700d00280d80540750190103100700500706200f441100342c82081421649604480001210950307124101d12500500002c0d80036200100d4000c0000d48807a0b034500c524240e40d003178030000401d040d2302c550140c04040c000f40120781440c10181041545c240040d43c0c25001801040000307100c4104400901988008000005140c140c1600301501e9242010a030a0350058480721010095034410310740c21040d50051200507610309292030034a140096a5104a414408075039082000d80d9459000d0b4100004141015610348921481241040c1e17840c0100d185441520b410300c07003805030000d80c8030320484c402d508945215440740101650b80c0514031500f000268100f100b0b02c10b0342496013080e50000409040407800300100182541000080c158a40040e800031540c02250b030349940e90a600581e01ba8002c207503007102c90712003941003103d6113003820b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 776717455 1250 776716205 776716211
    0x150c0306081b0d02030a0f0b010b03010e06040b19090e210a1101060302041103040605070305190c0207090504050303101205070b0702010c0c0f15030b03060601081321111c03 76
    0xda29915242180c0025944c0201607401021003440e00e10704140d0110419204404048004204240c2c054200c078141c600301000c000550751540100300c090000c1c2c1d02c50702d801c0311124000005213101011003e02912407101e001c40c020000c6031310240782c2a104004501c0c101f00c510340c52242c0702d00890171941c0b001c00d9890f201200010b411441070141c003090b0f01c02504146480000c886a50030031010790b000300e2041c3e109102e00d481d0700000300d098903c1511900700b640104041420791412691155070f5140460050700c1380c0f259228000d00c22204c04460684040d0400020442401200c00132400035003002014100c003e0344540742c02c3e54441050180200080000130395902b96800752058a24459100c2146a030203502d450313900d01659502d2250343c02030000841c07002c4489002c0c1c004d58140b00070240c0105629601c140c011a42c00c070b80501036080346054004003201181454542d4590a51030248405d1f800840500080c5240c0d910625400b803904808205002c450000b0540c084403c0245808 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 776718705 1250 776717455 776717503
    0xe07030b070c050316051c030c0e0907170c04140a1217090402130504050a0608100b041b0929120403030b0303160614060d03080c070b04150c030608 65
    0xd034698401c0011117a10b03002e030107083c1410002c000a0030b0b51000e200c03565aa062164401e001d8069550703d510700e102041c101d03980180141000800d02758886501d19002c209001c810400340824001030f01c1c054a00e02001805115980d41c0c0c40819407800d0b42035a030740002514045a4001d103801c1000000c10402c5080c28520f04c0021200c26596a180c0080c02159650071032a48028030034114851580074505103000180001003e10500c0c00b200c040d03801500200031140070182c020816110303031030350060307990780c0ca03248603c80008002e60455280e00d03001421400c20702d1340c5800c02600c0d14441e40c00300000c54484903150421040d02d40c0003110b4841d05c41307141c55a10702138010300f26401c0181d13054400426800d4840340208421040d00b8065070703081142c185600c0e1065484403007125601d0b08054103481c01e100103031286c46100e40c40202122200d0814595948165004c681900d0545400d0261a00c0110100852160442008850070200803151904600b144c451a001c1d4210400030b1078584a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 776719955 1250 776718705 776718713
    0x303091c03140c030403082a070218091f0b011b020d0203160513090b07120f0f0e0d300f021306020f07050d080f0909090d030e07030b070c 61
    0x558001000500b540e801c0d45403000304802c058000700c0b03055002070041008101c8410081140600c03c0c1300e5032100d400600e81c40042c2ea0310940c402c030b100301c1e0002d40070312030103884c0c1d034065940302d00030400d45002d0b04c480d08520b01e0360b1129401782c01001c3c031a54504a8450050380e080031000c0584a0710105542a8240f0740c0002050642c0c1c1d45c001070f400d8011419201744e003101c0414108140c500446014090907250200e01d0700312001400e000340410305840109000500600303807006540f010403004164403002c5954001500c4064030240132258444d40c03100300f2450180301c640121105444c007440e00404009804086100600b1401c3e4080014807650150034000c0d000b003803090b0212582036544d040c240c8402c56804100d445088018041c0e24044600100d01090300d00444000800302070546280d034070b890041d98401c5004041c3c0d9041000740c41442d885001c0d14a1042000102500c0100c8881a024080d50b1b00050411041c0d08404414400940c2ca4500c150f08030340300d49080c100444061034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 776721205 1250 776719955 776719961
    0x109031103030d0e03130819082512200a0b06040207140f12040b030105040515041401090612031b020d2a0e0603030a27060306030506090303091c03 65
    0x4812418035013051141003070044000300900d010b005141111010558820800b80c4400d964090482541d080301c24040c041600c43c40036020618828008000030f03c0850200d4070a1032405a00725600c5903200c1c0c440714200c0d02310800c3c4120201c91811118109120500c59032140c0e6414402840303042c007400411000e459a07070640340c1c4144e10400300034030701004c2100359546580130000745c1d42501c10380340801c61903403c40c01aa0100c601c1241e405e03045034241070411001e400c5c01011395038545400c03002810309541707a005070002c00d40800000502541024050320684403260041300d10b80055500319800030350300c0002a443d8284040401d920703500d1a02c000381ea00e07968164040d002001b89040003054096040303c11407401d01c0f211144c42400d50321041041a0b11080b03880344d515400a002200ca1540a407038600395a00350514030f03040c0c03400501c1c410248030b601e50b000480080c0c1d5600d800e00800000300625900040420025421850a0855140d441a4955804042c4100d02042c0301d1040d000750 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 776722455 1250 776721205 776721217
    0x130605010e090c10023301051f0305071421060307180b1c03020d12091e06110c010902030705060f1b01091a0717161d0303031f060806010903110303 65
    0x1d0000409613092079942a00e001c0c1b1242d0f154014854000005070914113001c031035415140700c46079441c207811041002d4000b008020030360300c1840700c03003440d503010a10010018040b40c8080030000c100f40c44a40ca00ca5411403000784024020340c41700c1d1050042c1048400c105500041c4100d0106400001001140b81508460f1644000001d604000703400c1603000b042d00c1d1800c50883d0742d010b00804a200c408c80549240b1a4040c001d540d0042d6096002c0c46d07201c010340c4035980a40c0010488020b00042882e065100309100903041e55034005080851805102c3c210041104507825400c18141d817850600610500400101c440440f90340003401c89003e4104240d4607802690515090408050245210701d00b26030280002d51420041d4854030020210b490050307100306540b627048080034605580244a006a01e44491801ca2004034599001c20041d8071400800005000b10101d24a41c00d450800342d421103014485100104011641d02c0841c40c0d080f0b0360400c1c400c0c0f44411411001c242540300d00c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 776723705 1250 776722455 776722483
    0x2509080709020c150c0a0309020105160506150301140c070f0c140a0e1b0c0102040302120a230c0105090f04020d0e0610241403130605010e090c1002 65
    0x500000100a022a805002080c6041d010303507600401424130500a550100d42050100c2c10038040030b20032604c40d921015043e841070400b6881d14075000701001100c20084400c960a51006040116038844000e20042c1048250300a00131004550221007640d00020002c0071900f2010408074144a00780c030041540c41d03004014a4110340c1c0300e10035001903985400d0703070500a00c0d8401c40001d000418401c400d02c2004000031060071204120101c0c5059805050400c030b40c0d6400703010110141e941c54410303000d0b01c40524003c041284003458000c0c0c400d10700174000c0300d0240300040b030017103001d00c0030480c0210300d4000d107071065954108000154000d51400941a00039102085071411260180c3c4040c05c111941400c0358603503500c050300020440094021504400c003071110000c0240c2d02c00320440c640101c0c4d400d04207401e901100d03000c81d441d0011500800810100601101480081e21503103024040a00c905a090f20341540d280395a8101590702600807100e0040703401006100f0b00c00541362004c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 776724955 1250 776723705 776723713
    0xf100c02120c01060e01050d1208060103150803091201060501090e0a0f0204061808030c0a020405060a0504140a0c080c0f071b06050706140f1b1c05040317250908 71
    0x21082c0305a0084c51a4094112401c01140c00446c0c140303020f4980803c4581c0c0140041d44c0c910b490541192a100058000c80c1850785032010b40300e40b11003604410000e0084800295280c2c040c00c010054078034585107036000c1c103901d1710105201d2a60f110390f4103c141d46001d1440c14407519012050002000540c003000c290600c08900030441940c84144c42c400c08040b111010001500c51405076202c0c4202c01045a0b603901c01400480141020340081d640500010500c03858159140c0106059541304a10000c0503040041046003601c00b9208a900c0c110203841c1045461510015600040c4280c160701c407c0020f020a41c0380c00c003d240c11142150b510118482500503a8400000d4240d400854084a510b403d10399907000d018650b0380c15920a81189000d00d00070303202c1080184101c071010340b215006c02401c022144042d11380c16035070080358584081c00502031800703046c0140170100d041c00703261042a240c024042c0c140140540c150030341c994040340c640410324844099911840540c482d620f1401 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 776726205 1250 776724955 776724967
    0xb132606071d010816030908090a030c0501080c270f0a06120e0f0304090b130507080a0f0209030c060d06030b090f0601050a0303090b0a051c090c080f100c0212 70
    0x1d031100d5440d5190703600d05454007042d1200d00042d00e280800700d50368017010900784640c2190300d01c86d801c1841c01e54029810686070043c3c00d0b010400d080890341060324010710030001049656444461103174040e440202850500c441c01d041d80280c010a8441c3d0001440c112904e04800d9860781f0310f14070302e903000812074900c15507900e01c05004001441c4126664614202650808180204181c10080c0304140514030305820850000d009141d10392035107402010200310b19145162600c60140250201d407190130702c2d407034603d000c407003900d1003540c02d004c81c42d0051080c0c44c010b4400040d407040407402140c603683c4801d101d11000000341a40e50000c3d109414400074009802c1d004900c440002d0380b101c054841c541e803950300b03010300c40c50140300c01000100e03c01420400044140c000d420704100310300c0c20500d0141d82400401107802c2c0c00340341800c0507072348075424010414049079010041180720003a011008002d845252568002d03000200419216004106c0603071013401003600c03d104001480e40c64072 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 776727455 1250 776726205 776726207
    0x120a11210411060a091203020307050d030f15060c0b150319020f030a020303040e090106090501091b02160e1b131a161202120d0902010201060b13260607 67
    0x2541910262040c0d40c04032481010b03410410121100e03904c00fa102c41e04220b260070460b54099242440c00d4003140020300282c40051010312065500c94200e035004916880b050300350f60202d9014600b030040d4024060000c000da00d40040e241d4500d160044c450019542d0303241d00d1415030103481c0f540140c3c10b0081c4805204011500450448046d0094800540c942c10b904241941e1344400400603615500502080040b4036803c1d04a81c1d0088030364001180c03140c1e0315418131090300d00c00e810000d000307070300d440080e980041c4032401c07801061904e1001300000124609000c01b4185913009181e000e8800c1c00028ac641c00041d40f0040402d54014a4980c1ea048028145268142503018044101c54142e039440c002000c031505682300c018015544107827000780b03070b612180303040e001d042c000c03003540140780f4004246200d203c050100c14240007030101b03022565200090841d0513581142d841460240003240041d0503590095042c0e441c06840310040000308091404528000c22300340403e032140d40d041000c0c407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 776728705 1250 776727455 776727517
    0x91d010b0319020f070308060a05030a0f1110092c06040c0311043b0f0402030c0306010e0a0f0501120f03090b0304050a0c120210080c07020d11010f05120a11 69
    0xe9000399102d90301f913100c00c0c0802240300418803c140e40743d03203e11340b41c40108080c030b04944206841861006641d40203030b8080340c0c5900c04424110042107101c42e04002090300340d550030307115620000124452402c03203220552010400b1f01043d010729901d40701502454060b500414120081d00001c0c0e0302c0382d0b42d4400c0c90105420b003031041050280442c81a0100c00403900440700d1107081e080088045540307075071098120903402030043e80d1500c200c1a03180c0050300c0c24410340d4040c0210543c40d08041c9400341c03050040c0d61002110018042c5098010815503101d160b088084540c4252540d00e0504642012900c09079035800200c16a18008180800c02c0701c00141100200d01c5580380c085036650302c5c607000300100e10140020390006024500740702c41c00d108083c45a0b03c01300c0306001c60b0030a002274001c522006480c1070201c03007003655a07011440960300404c2001d01203400f80360403881d2401ea40301480d080d00c800341243c280c0303c0d26136640740c0400c02c0354010344c0d046240b00c03070b6094802d5012501048807 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 776729955 1250 776728705 776728717
    0x711012004031704030c03020d020a05060c010509010606021912030b0a0f24051b070b0a0521070f0305190c020c041415060d14070c03091d010b0319020f 67
    0x402490f21040720841d68995095500b1240c0041c0c0070302c0130524503000c0c4034541c800c100c0100d0b80030440000105860755a04050711228051900019092400966190850b4481d0700b024080d58088081c52400c848504414449145e00c401c07204a0b1a07a4076006401500c1c603660071a078040580076004c1980720082c0150002c81d400116124101c2000b10300c440308562aa8603900002001008200e02d10100107100c418401200301c101c0d01e071b07599036400c081c809130020a20000001c0e000035421000122000780c21a6140110303210001506100b00060000510301c0304d040f050581700d00008103040c000e840c1e514102e1500303c03814400503142c00130080d150100021618421440e000b450f540440300320680b030b84164622040c0d00c420002c107000700a0260020700c0481c1240c1d440706150380182c807989840707c2c011020380c1c8070225a95202d14001d402c0d08001d800c591910340080c901802041d8010500d030b41101e0b10902c50750b50f240c403000303085a01c05120001c001c1c510747c00000c540446c43d00d84401810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 776731205 1250 776729955 776729963
    0x90403020a03090605030f2409011e050901080d0c0620070605090d09061d1e0111030705070312021501060f0908031e0318070603050703050f0609071101200403 70
    0x82d41989681066501c0e02040d02d250210803000c100081070f488000186000d21188c200400d14103509200c001400d802c8240c00c40105103442002c44101d18105102a03409040c04840b130310a82d40c14200354a030303200440205602001400c2c4005403d0200315484000000c0d10014a81001b980256048405034080881104e0070f40c50030000502d061004074800d16500616502d020740c03146000c4040fa8081840b4102c50b00c100b140c013003400b00c103586015880115100c01280300c82076006a0001410710103c20011000310307001000790200040000c152101503a138441c1c40d01e000c42401e03060491500f1946140d8002c3c0c1c1003040c00200d80580c00000c004002081941d43c0301034280c0b00c0082c1502c038003c80c00b91000948411069080343c080e0340b0b0107551301800902d000f845103d08400725602d09072140e4031100100369204140220185e043c01a20f600605000e2002510f041a60104449442c01803219081007510651050000400c0d0443d02044000c0c80c26402d41ca1355141351b00b40d0030341c01407200703c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 776732455 1250 776731205 776731217
    0x2090613140f030109020d1202010f0906061d10030b0c04030602030a0608070b0c030714030f1903051506090904060b1011100c080f070504120501091106040510110705090403020a03 79
    0x9100383c80c05016000f180c03503016000b40703c080c0e0745a4801c04188101d10380340c1d0655480e05c06441100b03000d4458441c4480c01040d002c20703806d240807842001c24411108044844030007008100b4016246030143d01280d900c42e0100380a540d4140c1c017001a0b005a81006100790300020070b00484842607000300d003d4540d802d0640d003901e0340d144c01d00c10940c400c0f00d01d2461550810f0003640701081c0c42d4034161076800f45c02d50680303250411083c0103030f02c190720031084100214030b194241c51500307516207d4903a1001c1d83c9d083c1903030120044400546107000ba010258410301055000400b04031180c0c0002c1c143d40c5010f4800e910311005401c02501c0f1001100340b43c07040780701e40a402504106a8001c09142100a031103090081c0c80d00e6100101242e4005c21804c1484401c00c000125030300e00b401001e40c0c0c0da000b2030000501c8001071a04030100703400009410320508051000703200941e40d0448200d09200b041c1030040a01e400c41881a0400c0d4481c3d1025500c03540810400003070540201e4000c41b02c42c4281d9030071f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 776733705 1250 776732455 776732479
    0xb1e0a05070c030320031e0609040c09150b0f0706050c0702010e0d110a06030f0b100f1206080a05060103050610030b04170c0d02030d0c0306080604060209061314 71
    0x18044400032100031001594220480c8040f078060fa200600310048115000700504640c8181c1c1d43e6680709481c0c2d2181c3c01e403c402c031000403001119919800c42800c0300c070034515007017546690f6502d0fa040e0252201c12030342d030992035540401080c1e80c08014400312190fa526800d20540803003e5070841d1000f030342c543e030a01e000280d28200792004c45088603416110030308001c0d115801d10200c20403a400071500c4800c60404080d03650388080c50b00c0e005003100e0f9404a11040700c4040803040d56202001e407400f5502c141c04030a90543c01490f140440c192600d814690360901c100c101d000340880d54031141c090f0180c030141e1803d108010501c1c5050300e00400480e807468031071130b94034401000360744800f0b060b0021040100740000e10200208955091b0b94203064180304102460300e0800c0c9040e00088050b82c4001903100e04c9102a01540000e113000e400e04000700b078640200240c60300c50003000240340d540e001800307034915568981a1103070b4441440101407443d4503490074034147d41040440b280300319a05022 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 776734955 1250 776733705 776733721
    0x304230a030f0909021c0504151107060b0907020604030e040f0e011407051e0a110d0f1b0b06040507021c02010f0b040506030d12240e0108030406050406120204030b1e 73
    0x3c561a60013000700ba06920051b1034180c000030140980201c50320071208036000028407980c019482d044804444840d500c8103207280040448130000d183e9806200a0750400a4143e00407801d00c0e07100d030705420540c84980220340001c0041008020160381d5501e403c00e03000d40024154404102c840100d84640003540302c114003038070a400750071003030b02801400300d00c0c2851505240d0040e10076002d03141000c1c002c0500400d1094102016900310300c00058000009402e0260311900c00d41094824003441039401c01603403079580910300c0040206010fa600c0b01c0104294510811108042103401c0c403c1641d8001e1100340240a0800e2030b8070511803906000c0c0d0715245161621505001d120001d00034141180008e500341c0b0703034904602c0c0c1c0100c1103646031090041c14207030300031190340250706030360a05003141007220207141410103030004e05e82d0b42c2c000c1c481482410b402a04490542c0d94605200403c05009110040641b00b81c2e00000c0c5000c8100040c011107041180d00f050150710f841c6040f1a6650314506 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 776736205 1250 776734955 776734957
    0x81204031a0105030a1e0605044d03030f0a0207080c040b1e0120010b130605030c130f0f2c0c0127080a140109080304230a030f090902 59
    0x18a41c1c1600310242c482d0000707041c0d086c1000341004c00460400360a401b91180011070320200c50544003440f02c001a61b5800d01448060556040d412004440c1c1c805251003d0101c0740b14207030b501c1d12600034066401d16950b0100182c43d203003100540069650708503044003c1d180d0009100d030241600c40c0c49584501860140140030f1100c20281c28414500c049540c1d400d12440c02d403504034180b0031500350b901c190200d2480c0d81e5582d4511080049030040e404014810741100070300000103070600e0600f0a101e00e680c041220440c9035011203051000d83e02c40342c2c068005000408859252a1030640304a441300416000149122100d9520404d00c2c01440c0503503c0c6920440c0c41031105070010050701d0615030048007485101000085c500c001d95819450061400c41c4c91f030008040c41d030000c00e201040000003030704500b030490701200900c815803155a82040900004d08020a60b50125400c1c0341280404142c0070000c0c10b4034011105910118200a00b00d010305030540e80c00128650000315201c540d41c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 776737455 1250 776736205 776736209
    0x60e0109170c07151710081b190320061c09080c060103200405070207061d090a050f01120b040303090303141003020909010204181802060d020301090c08130f0309081204031a01 77
    0x401810309429023118090400d0903520501794014240c04000701c0d80c01010700f401001d0344c420f1401e240c1c0060383d140d00340104421494002e00c84d0f041004024000000a143c0485607015440d000c6501c0741c0e10301d441d5100b070060007030754103282c0304100000040c4800b00711b486d50445050040e00001011000601c010f136030303080380c0280250780314610402040d445021458009121300c13402201002c0002d0008043c10015110b5050250300c0d0800c1c0300c582203081c02d8090050a50041750314502c007403590b51481c3c4503c0100050b082c10703130321030341c0e4014180a6000500440c1c1d02c0003902d152841d0a8410440b8074049001c140d00a8100741c0c000b4000c6641407003280e082d604000c0c0c042059072013669441e00581041d82c4400d81c2d03c07203041c01d014010784521001d00300c24094180096104d6040210000407940c11180c03480c2000300c1281072241c0b0710304011503103500603000a443c078601e02c924101910302071080c1d40541e6080c8249807103180428006c0b00900103481c0700b400e00024120b13408200841d1202c080c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 776738705 1250 776737455 776737469
    0x203100b03311a0a2d0b1813141204090b06120a0207060b0d2405090a020d2307060e24280215010503120301050922030309060e0109170c07151710 64
    0xc00102d0a0310301c001e101c00604600c6980c08500c1003ca440103542000c42b2000703041c800c24008102400b0342c3c81c00f40241d804410b01580c0716403c00b1b03407203404003494070b002800d2520b42980c0003410009000c120780040c500d840014001c0f00001e103441ca4072200030341a03150141e40310390303210b6032461404a190180d0f80c02400e000307000f89042101c5800b0420008150320b02205c07001550012985401498400c4207441d4404802900c805490244094181158070403154490155a2004005001a80c200c0c004020710300707000688400030324420000150001042d122040140d04105850079070006540d013420134103903403054083e60707100103140e03031181e1014943d141c0110500c010300640c10243c2455a1201c0501280445140b000003c0d683d0f680d044542640082d0b1120f030200300b44913132800340d10040d400c620300810070103405480307110001c92601e600d014040c00000d0100d4169100b0400000584243c40001c1c242d40c4076100040c02001d41418400e0700c860074880003070b80c1400300188081c229040d07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 776739955 1250 776738705 776738749
    0x50606190512150109060503060708040309090209061c0b01031104030b0604021c090c0e090d2109052407051206040203100b03311a0a2d0b 61
    0x8100c100a00312440c001000164415044042003c00350700702d48900803d642e80002403141d09040034141040d60060400092007409024440040ea01c41c1d0480c0481e06100c5006850b5111200001d00c0743c03141e12110310024014000c41102d01e40143d01000b620b4000342ca042112050030f4045030858059884040c0058044600080e8035051580080481072580030503420070441c1042c843e800c541c21a28107540c90210607030140a110304007002550002d1905000705840025036000500e405050b00966545100501c610751034000f094002c1d083e4954000c0030358020420f2070b081051203d10142c0c1810000020002140801d4002c000700c812040d0004c0800505a07203900a01001c0c1d030020306440b04003074281a00140c4000c0000c06140100c10112086042d41160700d50109c03688108440140c60802c0110428009091480ca00007140c0c050000c003802039954082d0807000301204071080342031081041c940c500c21210f0218080c0c09062040040044103001003d004c500e60b2044040a15045 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 776741205 1250 776739955 776739959
    0x9040207020d0512040501020c090609161e020604020418050a030e0a0b0403030519030e0309133209060712050a0e010f0603060501051008011a040801060605030405060619 75
    0x40540080094500103442900d034940c4907900c0314906020004401138941012400b4000d940e4103100310316400740201c54110b454100400065139012019001c044208040203142c1b400c02d010350000710751204900000d692003814840003079214103007290103e104e40e160046070390326074130666500c0b07403140d0304103008103180c0010360340171350301e51034000c040782d0f4007030030070600000c0369911000148003451007580d9180d141c1c005e844051100402c1c0041c840c0500d81003c4000841b440000203480c4001021103001244000d09c441030002040000305c005c0c41c0600c40001034001c0700c1e00c00c1101c007034040d501c58a50903c0c0d5800080980300d1000703840ca240058100000071580035225000310f500305a21090009041329001041d9084a045030044200325071252010024400c05100d014010142030350441c4407880005c80c010080340b814041c1c408070583d01d20180da00c084010090314050141d00f4000c1104a8460f030002c0c0094101305c074203d61f940300c5d8000152440c200480720510500c1d424010858148c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 776742455 1250 776741205 776741209
    0x5120a08190c0b0a02120a0b031902130501260105160c060b0d0c0807050d08190912050102120601020a031416150c020c06030412081b190906021209 65
    0x4660840715000c1003860102c880c04101d0704031406014030300168005903510200d891180701031b2001081200070500d000f070400002c0d20302140d15005003e40640d0f0071a400d0302e5100140f20100e007486c1d5095014a000000705a6514401d02d00d2003940c501d04000c5240b142c03402146080c0c400494080c0c03103544085000d078154a0044510010b524030600001c5030310140070340820804c0030b111a0a4079540303000d000803c081074042c0500e0002e801e040e10000c42c22071700340e10741102e14410940c0c91345108032155404810103100f00c80071000780002d010010605030300f0b418840d010303401c0703441400240003da80100d4076560000602000a903403545400c2c1c400c1d07040803440c0516030891040300140d1101d628400f0300040c0039008801e00d20703078800c4c00003400d484a1740c80240780103042202c44d0300a000820074400070841c0355010411514071444c0c40c40c16070b03a8581c500300c80100113034084000b41e5408144071405603008142e6461040e110b80d50008405e5032004102d80d00e00e800350b0b5401002e50200003644d524 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 776743705 1250 776742455 776742487
    0xf030c0c0f061006120f0c020703150e12030402061b010e0c0a03021011031306031b170a05090a060203070302070302160b0f1e040303020304210206030f0916060905120a08 75
    0x42c945280006e1114480b03402003003075443c442c200b200160007040060040004010584205600c80802005031401000c1040e6540004004c101660f8001100003411035840400f01c42d006c12503036103881c07a500030030f001042c064480c011925040b8050b0510020361410507155940c100c903002030501131896000101916030300d07110000183c003400700b089038004040e054841500203000300d59000544008030440418120300c0804800100b00840d549440007481c50f442c200d0300701485200c0082e00b82c41c0e110b10146056105200200304a0011040020043d055409015840e002c0d40948151101d1403a1200c40d4164501521040314014040800c21003410390250000a5400220746c0340d0352131000c0d50542c1a0029402100180e0000170284072081030309100c58081d502c072000c54500450103900003400f9000041a498900041c0e03000640c07071000802c5110354032006402c050700e00781d48545c0010b0900c100d40c02110302071103824996100328480001c0250110350820282410810b21007401710705 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 776744955 1250 776743705 776743727
    0x5150a0f020a060519060e0c0406052203080d0e0105010602120d0b0a030c0f060c21050d060906080c0603060a090b03030d0e060a11070b19020f030c0c0f061006 70
    0x318411090880300040e854420306008082e0805d01034031002a101c500e41c240c60054111030b55003444d01e000e0180d4504d40d50306590554165040c8141c4a051516249050203031030f0080c2149690303003c00c00414814850020b0040e0381c030300c0100f4050b44e0b43c83c0c600c0b00d003039810030312070100180e00c0300c21040d0744007880c00094906d144c601c1c0c0e00401c034200180700103080801980c005540000c0c0701d04c000c00c00703080f403e07840000801207400c0c00102c00c0c41d144c031120b59000700503110340c220034600585c03080c2c101d01c02c408840c0742085110041001585941c13520005185502980c5100d20a160708442c1c03d01e4600c043d244940c500903d28076555083c01100009040700804c0140c1610062001d4204144170b03025880190f001032008014074a400700310041603401c02140101c1001e0204a07241c042240100b546034450790700c00e03e003804000c600044078024070500141c1080707804080144404a5500c07401270869081c1181264880900c9061440e1941010740318070540c0c40b0349420400400d03001d4003030307001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 776746205 1250 776744955 776744957
    0x9050714031614120703080703083705070504211e03080402042d050c0405030f0a0b060f060703030c140c01091202060c040603020d1104180605150a0f 66
    0x41160602c1c14500d08801c0b29081800b448400c000f68014905140c424003040980301c4000b07019082c43d549400c40a4482e1302c90160404c42404002201d1300c414411402c030044007074845140c1c0c001e0101c0e5003450400ac4451803440c1904202c0854001407207a015103007558203900c04c0402040a00306101c081c40c49000046071303400455044a445084007200054119010b91039203c014078151042204451520700d8508020000c28111040b180c04804042c0c440b408480b400901d64503042c4042c44540030303680c80300b541842894000a49000e020841010042c4181c50340c1c1a5a1500c1c4100f04c4640440801950000310074080f075008241b280c0c1105000035802e0500c0c844440840d80303207260a9008003549966a034664158004104101c16084812400342c40500010f0820f0544200580700e0343c499541015001301e028001400d0a5000e061006a04a801640c1d191340f0899058401d0300207039112102c2b850000c000549080c40d41c0300000326031091443c80d141800007041601d0400020030024 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 776747455 1250 776746205 776746213
    0xf060a0b091201290414061306170a0314180d08160c031a04200312280306060c02090a02070606030506190e0604030807021f061401030905071403 64
    0x164424800c4c420100d10361102189201c0c003200038140c40e10003014a154a900075441c2010343c1c1001c0c064590700039008002203640701515002e100100d0003802c0c1d1030f003100e242d0401100c03014080060004005030f82c03510a468020010f112400494000d00581c0300440040c2c101c03542c424180e02d40200300341c042070300c41d00e6145c0c203101d80342e95000507101c0d11490841c0c1c3c201285409100303010100000071351401004202c10014a040d64699100a010300b00008000d0000700e011001c562303085c050307a00c1c0380c01c00411031511030720300368007118407081e410007a013510701d00c410031130140607210303014072010358480b03440c0c58903160600d5081c007850380d03030081001c808281d0030301802c0300080c41c1340500303070040d030241c07005110900f0462080302d800b910f0b0301480e0f04414602980410300c2640800c0c0603610a030903040c22030b800c1e030b900c960a9003042c0d5100b44040b81c0c41d02d000200b4451503900d41c0484160b605424203c030000c102c04c40191700716044240d003e4195070002d03500304004900c120481c3c440c1c2401406403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 776748705 1250 776747455 776747479
    0x115050a050c0102030c1e07020a17011d03090f09010e070f090305011803030b12070b0a020c030a06232e0b1c05060d0c1202061204030c0b0f060a0b09 66
    0x2607400ca170410780354504215000a9060300c0c20245500e14220080b0072510320707103003950540c00030f6609a01e500c50f807000b0750500c00e0800c1d594003007036011055800300038180300000780400317500c0b0740c0f0b82d8805030030b01d4440c0050b458520303443d00741258018140c40c1c1c00c80711401d00d40c8540c00b0a4444020031141c0c0810407880b0040440014020b00454070400701e4080111600c10b098500a0103075481520503c1c040c5200c42607411701004000354100c04c40d161484896500c1101c044100d06001c01e0302000780d014070036050304008001e00c9510a5002202e01401e000c02a02d842c550707000103901c143c981c0c0c408800100d02d01c2050b0301081000c0c07000301a14405001c4565a02c881e1140c51350000d1a07186540d1410120307000103074089005260b8080c900700c0d408120440c1e985e440044a000078068042e80c1d9100c90880c40454840740c1c102c5841c4014008003810074589031500801600321038108440301d0440001144001c601d448041e405001c000344800001400c00480d5002600620748055120702e1005032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 776749955 1250 776748705 776748727
    0x100b030c10022b1d13151505030606070b19060612230f1005040912030c0207060e011404090212040c0f080309040203130506160e090115050a05 63
    0x90341c1018211600585940c810325001049040c02d9141c1036240080a01040c840041e0700c01c1e2044c42c00400b0f1003045601e00c040300c0125041e0f654803070800c80400c0c41c00d500c0340403141901c032905d01140c44101c80320a9010503090105c500340001d46125070030a501b401608002004d901600c0d82c8949000c02c400c8030460130804040a07a0760075840701010600d000c02c0d44a82ca0490701842d0000d080d0600f080b103035155042851654100300800038010f0300d10350004038120400c6d09200200401c0010014841414030342070a0302641d1031000c1c1c180c0460b190501301000c10780041046004c65220345c6900541501801c0107451600500581c0054030b0070800000c59072844130700c083c2c000c4055074002105289003525105602c03241139001a41c41043c02402000f0500c070010440e024210b040d50b0142e2651140700c07004e881c480c8a01d40c01412409001c0404c5040205c11040710881150369030741c22035520820040c07001c0d140c02806a0145840c4103440120b4642c00b8800602c0045601d1521038a01200c00c2e903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 776751205 1250 776749955 776749969
    0xf0e071b030e03010b01080f0408030c0705100b2b0201031116051b18131401091a1b09092a090118080a060f020c07090b030f0a0302100b030c 62
    0x10088002c600081c0b40c4401d107003424850b01e01115800c2c01c02c0d1800e410404e0a403181c07080018002003902d440000029603c0c2d1841080d90783c403a0303100d000c885011f14821a1403001d80b070380d9240136008142c00c60a40800520382c4d0704804007013403400064510f5030700d2a00110080d0205080007001408204200d4a171071159412000c030060042019144d020b4540030704070950114420050321031401c0315101400a131110803641e4200403040002c0c0102003151501c0c80000d845140200b41c0395203840c60340390034030154080140800c200e00c006440700d9560781343c04c0d02a06190f643e50b44006c00040c027003031405042051400b80c00507007400401d0040e03000c0703903818402c640301c0d800a0ba0803400c020072000c42558010400c0e480384007449c001380007040d05001b003203940da441108019000988406d001149502180e040b1240c0c2e10141068402c0705840c1c40010000d80382401019000307101d02801690403031800315400145a516038003520a40c9441c2e80c440014008500805925010740f0880f03450035910b2072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 776752455 1250 776751205 776751257
    0x209092401150e0a14030c10170601050f04030609080d02130303110604020d02130617010204060e03010b060717090307090f361a011217040f0e07 64
    0x1020140c65581490380c042c2c044075080542005015002601c1682562103030303441400c0e0b440940800700c9090500340042e1420040c065669009501c221040f880d00d6407000b808060840c3e18010440380d91121401104c3c64441e1a04684c0e40f524203000c2480080c1180c1c0011407054090f00c4000e04000440605c2012a0321820ba00502203001460400400d9003040105c40c0080b01a03002c0c01c698649030700811350401d00004000e1091a60341409002d80010b80e10100c040d002c0301c5001c40ba40007000e9030041c000d5201d801a180410350b168042855440c05000e259000c40d00680f02e64144440707503495a0b6080e1004d8003030200944280b01141e4252003c00c0b0a40050103140d001080801091406000b240e0300400d50b24225085000d8543d80010f01e503190103841058030a0010781d4030701600b4020035850301c03c0d0100769040c034000d00000b1611103004010040c07034000d5035006801c5801d40704500c3c26104d02d1042c18081110042c1c10001c24038000f1800d60f028645060049440300c0d6468140c081003405 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 776753705 1250 776752455 776752513
    0x2e060306020d0902091503070501050c151014220c211401080303090703110d0209090a03020706050a120b13050f010305070909031403090a0b0907060e09040f020909 72
    0x81603c0415407610304d0003d508a94508076003c00c96050b0703800b1a4441185018050510a0000d0300d60000071040110403200a1034850307000040c06c0c070701d02d82c448041e0144103044e02c01485851003c078502e0001c5828100300381c9030303c2c0c406215072011a0b08010701040a121001d000081d55150302044140041c00046040340ca400540380001e80211550110181c00c40366860b8024003c004904800098050549800c440c41e00b00116104000400c40d100890000b0b401810314401d02c06012000121462068031940998030351703980b1110211440c1c020f942034400017681080c108041d03950603030300c200302e680c2c030107040761140070380303807001007040da8800d581c4e480580142000400904c40280180d002518520206205013401e50f1030003000407490b80c851800b400000008900755200801c19000316130ba011058107510b2510111450b00c40c80284602c1010600544510700d02d844d14818083c81141d0081100e445032069800b8070000402c01001800580700e441c5d20340002c50382400b0a04074440103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 776754955 1250 776753705 776753711
    0x204110f0a0305240f040504021207060306030210020d0818010f110d060503010b01090302011101020c0706020a06180804260f0102091e06070b040f0210120507022e060306020d 77
    0xc41c0080d045404d00300c03004044054900c1000b20200c0d41c4446551000020845000c142c43d251400052211020804015624403a002d00041e1031905a0400d00c1101d0080b584c4114403540420140d8913980e0440c08100012910380004900c044110040341c4298524800000e00c0c0e0100303203c1d40e003141c1895039040081c50010036807501c259000d00400c005080c003500284060003020300007816804443c00021305202c0b8055004200c001c096064070017103003120007151850340c1d80d210081c2d15208200c6003035809038103210315002c29040084401e987c8a501c40407aa182510b4210103100b00101195030380d00c0408210004480d0120400c00e00292401041c0010717503480c3d12a00300320300d40322440c0740c00c0441c8483e4203420303219660704c04c1038400c5d050700b10500c28050366030f07883d0410301140412002944160403c5040c5801c41d403041d01c00704540209582000a030700c0e480400d070307514089112200740150095131148940301c81e050401958900c08440818520703201d98916003643c0128507119451a9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 776756205 1250 776754955 776754961
    0x6011701240e060a030302120c03162d03050d0c020c12100e2b09181b0e030a03030c03090507091506110304060305070c0f060b09150604030204110f0a0305 68
    0x802111107a03040f2004642070640285566006034545a480c08030302040900404c02c592003140c10f0084030030144203d05042c1c41c00c2210b250403a14010540f401103040110620344000400402c00142c050381e401d511414104000a0488000741208281407000c501030b44600080d2511018148401d5080280103041034150803c54041103514a4003804a00d5006102d1100042d00c001c0c2030100f81d119800c2c840000401e820340540e9080c0040c0c5c0032512907882d0300d044d1840c0b508280e1000a00310821030001c020303540056002c599202c030355520b45605400a00010f40007a0107940010402140c500780814a200d407611a50300340085548450303000d070346a0030b2101030307414400c8031035010b0314a41c10203e483d0f0881d2554103680303001d58001e25092542c0e400229010030300400551b490f5580c06803d0b614035020750f00e00340c17020300b01d40128a40507114140100d48001d40680464074018030244c985400c080c40c580030480500481c0c030503806046802c03c007000c1c0711039043c801485d06106544020075070f42 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 776757455 1250 776756205 776756219
    0x60d09080d054c03050d02011505120d030b0310020f19212a050901020105010f120f140604030804050609030901120c0e0301020a0e210601170124 64
    0x90840003000d00c850f00c0b104041164240c2034503400d032000c14001a00c210180c005038050501060340d0805000d911550400954059054003c41c241030ba0403030400c144035554500f481164040031000d044103400004510f5026807080e8407020886034010119a800007448040800702d034011400d0710016040020b048a4031400d5a05e10180c1035901d190082590450f002d4070543c0c4c114000c00d018100d038452024102040c1c024000c41c40c4440ba041901d00003c01490000d05641d22060085016500700800055183c4070010040c04840b541c001b019401038041d90303803c3d200b1509550403100344010040d410003280c0d007002600d1045100c0d454418040c00d20307040c0320345828001090381640b42c1c003c211912480c1da2080c00030401032a41f5201140c2e29a0200069812000045140c0c2d09588041403900d445940907002c1c0d26180030a440720000b4101e8100284404280c4502c41c2e1541e5004000400501103203051881074010410000503030542c842031024503d40f10032202c0c541c3c40122440600c119 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 776758705 1250 776757455 776757481
    0xb0d140706080f07020307171201060f0f020f07150203190504032f0105070f021305013b0c1c0f0b0102010507020703110a0302190905070c11060d09080d05 68
    0x1000305100f40034070700948020358a20a803180101421a2800103c50b00003105050b0391030505131052841d0103603141d00c8001d005010344807462001840394041c1c40c50300d6002007840004540c0d44e80140000e20700b094074400305030303540100340d00442c0310402a0620380c20516000324070002180d51a2903a943c42d50404089541400d8480d00680e020355a94003200b1021448a003ca103800317003400303500c0384054240b0880d6203410044c069044544600c520000440580c0454141c0d080d450150300c980c46000d5110071748088820000c045c908a05d43d101c00c2084d0303650718881c0c0c0030010342056403500c5085096003031004c1044d48052221600d0b00900300c91404640186d042d01c00c07081c07008001074134003080c000356101001d2001800003244460b040c0c03020b40742d000000740a190040e08468022424142149103000b81d0b02c240b5216924100210708501d2261150a09154015254000d1900726204001e0385621082020800d107540300c0070b08000038800030250441d4001d01b0800521458402081916 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 776759955 1250 776758705 776758711
    0x1f08030310170d0c0606090e0c10140904020304060e120409051b0304061104050402131401050c1c0e21010b270903070804031b0e07120b0d14070608 65
    0x205905140b82d58104072000035000604240a01d4941c0c1c040c0c42e01c0c2461001403032640c04ca6075945e07051485210b10444001a4100c0c0c0341c00a5a40f440b001e018200c00f1511501c070102c0780b1406a008200c0c0b201e00d80f400744c01440c0c001d40590000140c011004039024030386000c140c1c496000c41c1005c1341c2007000550900c21158050395081105030301101d075402a203c01d20008000503c80381d03640d00c1d610303d81104801a2405860050320465031140c030700043d000510464070640c40705ca10744022001d45544258261502c540540000300115101aa066078402c1c0c0034081d02020001e07001c010b00d21a43c0d1b00c4900303690b510307100c0c40c00520307001c46014281c1c00c0d030302d244188074001c07103280382400c4600f501024031078410340707020017203900c01e0325107840c4c260640c030403804058840c00022902106200b152034030707032107601c0d80700c407800c100c0e01d2351180c2c1d84084103001c440707c001040c820409054141100d400000d510040201942e60300746160350380d150080b1400f10b03812003d50001c402070140715000000c3c690 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 776761205 1250 776759955 776759969
    0x1514040303051005100c2f0f15120714070303021206040524060d021b100e0c09040f0c0602010b13021303030e360711070308031f08030310 61
    0x5083c508010100c0e0014181005060800c000c01136048240700c1d40b40d5940100e0a01e05104004a050380c510862000b0a984421441188040544102841d003811035003024440c41c0e600c58200070755011025070601d0014070410a01156926040ca42d02c0c42c1402001c407144240c40c01a100d1110450007000600c00611241c010b92920007400700c480c810380c4144020702c0303060b085040f26510050204589000d9030200f050580e00102e00d061740c0604644101c01480e62440c100d41c901528105210256500c4208165454100345800265070801d5600325a00c00d00580c2059906022f9698800d0b040400d94003010040c0d42d581011070040c0780c2a01144c11442c0f080b401035003000784c400d5021007072160310300c801802d01c0803040124a49440b481550040d800c1d01c6070810141d000c0d64a1342e017a41d02080d08000002c0599040003650160103040036654081a04000703007409c2c0e0666440039815071001c0c0046009984144004ea40d42254080e030101400b02500074640786d0408501c444010081030b00506 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 776762455 1250 776761205 776761231
    0x70203210f0c030907050904060609051f030210030b031504110d02031c031107150623010c02040f020a09080705030a081c110c0a1103011512151404030305 68
    0x310040d610070641d50009100004a9944e46031403024a2502903154085d580107400d500c100018040d2a41c8100708940b4808400c0c4880d0b5a0702810750b1900750f0104039100d00d018274000a10240c01c2c4503860a2840d034007800d0004007222440c002a01e060420021a80007010390303001c2004104032268088505141036494254000030b9031f00007602c0311000c1007001500300c10808904041842904030490011550321000c0d07035611981800d03240d8103541100007102fa400d124001500e5004401c160040c1140400011864003500c0c00441c0c0501310900166806a1102001030300300384688014001016281c4a00303110f0b03032502c1700780ca0801d103540e40b0441c843d40242e00c1c07107408202e146080f02c1c890f50ba00c01c0032450007011910142d0081c07011644140c1d14000120320888907144c0003510004650040c3c00e0881103103080410142a1015014030281241440d6410015040c0c000d5012600520869101d00503da4004000007118101444600240d02840600091503050300c109500200740070071038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 776763705 1250 776762455 776762461
    0x909021c14060f1e100807172e030b130203010615050307180e010b0306040b0409020123070203030f120f0919020d050d03060807050118060c081207020321 68
    0x4003d6441882c195018203100c1d6540c2507a54044410402c0400d00140000c50050060500501e001c0c4112010000708804004200c0c0391a40540803a00c14025440c09001220900c203441e030080d5245400840c0c65501c590020000500c203c1406100d401400074044500c44107004040c06c1d141c00d607001d444290b0b41e00360845d01c0d10780e01500310b9a000d80b20b41810345410300a400c42d00e1400d03446a22000c040c054100011904c0c0840070000c5000c0c00088400b4811a40184208400c482c04414000c2c0071480c01400300301101d5130940130381941103180401b5410009141c0210303085a1000607240041d404c002080008a80450540e5030403041c503040c1d48840c0d10f450b482642d0f039140503c81032480d20008080c50380841da949021115050b42c414140d96011946d100081c0c0a0640ca0040300d40720302807803402140c00c1d4482c14031001840c000541c2c6060440c9010700c11b075491032071103400340d40b103003001c000201624814052041c0241c13480d0f40103541c1d910407642049440280c0c5050410942584030034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 776764955 1250 776763705 776763709
    0x31e05010e1c0e01050f0414030703060e0a0204051501020a0308060d0804080304050109120b04020418051b1023090109050d0809090f0103211e080906090706020304150909021c1406 79
    0x10b580030340d07042004234082e0f20f43c048002450f0000710341c00104201e003082940d584040003c10030b039103050300c26601400b4a4440810710b113070224140b01c0140c0103030300581d600d2000c01c0c410744019801c24805400301c3c0d6000130580303440f06107038800e400c1080d9940c070000d820455940c0c03001845008251a06a011404401da500d00c01900d20150001c1c4c421500e9800514101e6404030107900004d03031140c100c2da4000304078441035040c01e62803400e1134480d4554107180c03070415004000e0841200d00c0025801d0703528842c9000160541c00c140291410402c20250106142e1140c04881081d40d01802c01280c4400e03102041000b010002802810101c12003401080003c041054282d400d000010038006806962101283c2d240c10b943c400000392207000c44203d40d1207800040c0d450040c10010300751040b5688980c0029500c000c58030884c00103a204210420402c0ca610002d01d03140703586032801c0b5003407580e220141c0c8260381280d070b0004404609500b664000d2821449245050050780310000700614007240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 776766205 1250 776764955 776764957
    0x80108030d0c140301080d0f020c01050a03051e18010c03090309180e0102031e0f04020d1b2303011811130e0a0b041b031e05010e1c0e01050f 62
    0x403441d00000d4850340504415401152441c604803103000354a512507035504015a61407205817210f10100d81500303071408100e40b0118500b2055070b01a15400d217050070b00d020480040c18000e0a141c140e0100188060b1411008190b10380106a070550000800c610f880e09282111840040e074070901d4600007001e00003d03000748111085407800070b1001e908220080301e034406411950328280055200000b04005518808403500c442e114070007003c4041d5403a400d580c00c00550949010354040c259401c08030000d6543c1c41013003107500f41d0680341b004440d41d070002c0350b80c0c0e0f0505402c5242d02180d04524040d0600f0309100301300030558598090080707a002500c400c564403001c1c42c2400d0003515020f00c0c00031442c4c0343c0e0300145401c680d582c0c1103400007541400d2101c0c8402044e1400c5408803240005842e2001210121500b5603401c020521442200f07940350300e210383c41607402128207540f1035810900084042c014500c884590100c000040351144100900c03244102034202d042c840140986040c109040c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 776767455 1250 776766205 776766217
    0x61d0c0118050108150f13020c0c0402071709061603030504210917190b0708010f0e0c090d0b040c05010809190f0201020109020603070507120e0d0213060b07031e08010803 75
    0xd49218044000400300c0c070710b0321000c84069004503d0041f0807801c251940d00800340d0324040001c0d81c101c141c00000700401e0740b00d860700180c4500c0022204c02e041c03141d45002000442c5009040750b140c5880031244119000302c0341c03000c0e40800e40e0380040000744207040c8080001002d0720b2541d0303e08104403010240c81ca24142c058205148003401d0b0a203c11502000103c13001a114510128a40c40614100f01c211800716003010000f84107070f00010302c0f10002c80030801640c90741c040c0c000c6156901c0b4403804d0907402107894958086083e1180340d000c1080641d415000d1400358001010080c1030100141c1008405001410036500003211410301900500b0040e41c4594880070f046600013503400100d000d003d8410010f54403980000600c031109401100510b810340c0b15001076680d28034400c000792264401c0b10000d60b0000b01032801080145015500320f00d610111403400124903032103d00f409041d030800403080300441d01d6490302221201c00e03c50a044120140d282c03c7c0c0103917040c034040d00d072a80990307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 776768705 1250 776767455 776767471
    0x50f04020d032a110406050a061409271501020f0a0b040602211f0e0f190c020d020c030105060a120312051014042007061d0c0118050108 60
    0x12094500c041000c800f100c80603030035008801c40000396800c00080e4884280b403e58442c92601c0800030343c0f81404c8004a007201e0140c0c0b00d541d48070003003540e800c0c0140d100b40b9072298852100d001e0800e110704e070f0040e070044412690392229924a042c04816050300303070362040181958000c1841d90180c03000020b04100c2d503948a040c1c501c1030b0302c0e0307032038480c01038050b80140350b64518101c490603200a828221091180d030740d0985a056146040c60041e03480c003028003035803440301d041100043c42c804240c06003503000708424504070284121203440391304594802c1d91440042e041038000101c5194104100c01140500314002c209a051820003e45000c04c1442801f00c92101242041d06050041404509940d490102440140761000d80d080503092140070343c0038150601c02111009041510580100c0181c40041d01400c0c206031003209a9074004900446010344c49200c030040c80c1c0364494a0014000001009040c40070740742c8005400040c01104441041140d42410007140c0e9200d072070742e5000103030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 776769955 1250 776768705 776768717
    0xc0901030809011b02040f0903181511100947060d0c0303020a02120f0a02040f230a0b060a0f03270f0302011104050a0302091317040504050f04020d03 66
    0xc0090f100c1c5104c0e007804d80a5841460001402e140c0c03072090b00000011403283d901e01d000d0350110420320341e81d480c25000321080c0080ca03040800e84613018130204452001003400321401b079814072414400381e4400c2101200c0c103100008110104000840c02c4204401e810107008040310300101f0603e5000101524409004c5840c0c0c011480c6d5813500c0340c078400655040080d400d038071030720303401c2c007941d20303190036030b049000e4507012110300c61030100404e1103810350820302d000d07049400d00c40d000c000c003500b400180070100e580e070340360304080c03040d0640d01014000000c03030006412480c09104540881d403141d030103e40a44070810001d407000703501060360748880d603440c200003a012802d9511400300340321104020b901200007041d4001070160700d100c0e08028611942c000c0c88240d043c3d200b14145030045110300c54000481d1002440185031080b885540619800c0c4011003561240d01d03402180750000522050620000600b404903080c0f5010741507120b0440356400c44541015400300340b4540c440700e0044d0030088 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 776771205 1250 776769955 776769977
    0x406050916031d0105091203040f120306091a12060405030f031e0c0c010c0201061d09011b0c031b02010804080a0905030f070905010f080303011703130b07050c090103080901 76
    0x8001d0740700143d00b062000010a1000003042114002c0c402a10300c1c205074401d07280f09031041c83d0040203c2e0b209950048801140041555416039030600c01c0d00040706141c1c4406003c10380c20382c0c5205d4043c80360070000e0200030300d0300404240b12541100040741e8250350860300402000c41c0c0000b08469804c0c0c0009011135482c0e440046844c0c03c1d403544006e510600001d40148000444d000c005031240f090004003c1088002490381070703080300d0790780c4984040c0b030588241c500c203000b011000c12a4085044000441c20149109044821054640c0300001040e905039a0381c1c04c1c158042c0480c0705442910f503d19820031126000a0960760009100a041080001d0f81c25807092107105881d009040c06402c40b00802c903031142c03264640794a801030b03c805914101c00090420f100c103003100c040700e03100f0700a14a1070f403e1041103032020f1588685204c00344400c001210b142c0042109180003002002c0003584c4030078907860918104001012203605c00c411090050020072400000c40b80404824201090061 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 776772455 1250 776771205 776771207
    0x907020a020a0902040611070f0501030f02070f030816080c0301260106180e010b090a0b03190c090e0109170a0c1407170a0b010e04030504270b0406050916 68
    0x15400c884001c1d00680100c100003481c03607481d00908180d0710300742c0710850031018415107aa91103a843c401c480118451a2003085070b5400b951200703007078206c2c60070090314002e819101c0c94942240c00e68110001103040c1d08105030540c502d551000c1c510b96a282c019410304008403814094001801841002a0103240d5401c00c0b1000380c450001107001c00009011f4a60b5a12030341d840c0c88140c444c9000b64505194144642c01c1c2c0601c1110f00862000f040c10103551220112400280b2071095030719014401e0340d0083c1c400408084034245954400e820110313495003440001400d5070300c121241c0a15a040112550000e0750500301540da01c0071034541a0703228505010225444001c4d2000030f8590103903400790b12448100401d9081c00e13035009039150341d408800c2d40b035600e580300d02c0c203203010304000720b01401407107401803903109603070058021b181250030262104404003140320344101c0101040106183d01d10b10b4001d0780900740e0040c0c400c6408000d003620b0240854809500101203004000d0000c041c40005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 776773705 1250 776772455 776772463
    0x30b1312210509100f0b0d110d211206140108070504090603050307050606060306060d020304030e090a29030a081b0a08030a050a1b081b27060a020c090702 68
    0x281c000500184020304140d59019101c40c1c105124007403d03420840d0a40a4281c3c40c002d010310044081c00c000711404030354486a64400300001c015611903c0c4c152010007052015018201604204048410313110b50490054499030044000c40c0707856041c440300300702d5031403c1c11707100c4602c010a007010341d8159100f0900300ca0300d1040340c00948040785058404420b100002003c0c06416200c2c0007101c046490303e0040044a001c11285a544420f0401c111900da18858000d107421603ca41001c06805800c40c00140b0007500450300c0207100755441180641141040c0443d05407140301031007581c1382c42d5083c008a912090461006441c210000604040b402070205800440104400076102c000415180444041e401907411074502820070000c980401020301ca001340c100d200c00c030005904120824203540c0980c00a01c0c041200d004100380c0c0252040c001c00074040350715101c040c9640700810b281400405840b80782c030070340948024065601810f4000829428449088132100b03031650750343c00c0c01ca00d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 776774955 1250 776773705 776773757
    0x1504080c010902120a0c0b120c070606090207150f060503300f190801050105070209072304050a060c0809010c0503040803120a06150e060f0f0c0601030b1312 69
    0xe510100c00010b80540417840c001d040b4840c100000403c0d0f650f1901000d45d009024100704903030700e11404622444a840700514001d072180c20081402036951014030100d07008000242c030600d5455903200703544151b5100d08803428440c50340030001241090046580c0f080900c0c10710780f10750051a50a41245241c07881c421040d0724026509941d901080c0550145400c40c0b04000d0802001111008100c1e003d00c0d200d03416620107030740b80781c2401c81d503400700a1001c40140c00362052040c002041e0810445800001c2c81c0c00104400c0305540c0c6140009002c803c01c2d0350341c01442040004036a11000030b20604c11180f9440007440c1089150446062150951290341d010481c03030f02c070018520f12922040301c40d41e0303c42c00340503008000071946c511b5100001003100c0c01c03140c00605030441e250000c0c50300718043c0640c0390360020b0315400c1c940a2610004c15034080046400c2d1607218800400030454a141c1c10303a4000d184000c50026002c00390341d10744500401305a071405124500a888622104c06d241d82e540c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 776776205 1250 776774955 776774959
    0xa05030a080a03180b04060207081c0b03070909080702060702120d0810060507151e0609052d01140607020414090c0a0b1c020d061e05031504080c010902 67
    0x1210040300d1030300780740c0caa10200c1d00101280c2094046200e80c4030000440f105640c0100c503456042d5a10703907500300254042c0008441c0c01c4001d01c101d0b07105031001104030301c40350000c00380010101ca180c003c0520f05251a0b00032136009040085e40000280b0b0031007036900c1c05d60f042d903000b07488000c20320004210005103820700301070340b00b400400020b00d6031001c8483c0c02150989035010146440e504121424030035450301401c140a80b80348080f02d04038030b5004040441c040d4070000101d207640701400041c0c1e0b01c668410360f0708a480e0410b21800e081083c0c03c0c02c401090600b1040340c0001010540102c1c07030014400d444443d001c1000c0b1f8071490701c4000407900d40c43e9000b0300c1004410107103a04000000015941d08000e0321490890400c24104510f1b0f80d001d56040031020760600c885c404419080001000100841c3c81e0207029044d20386045000b103e000d081c070184220503581070382e00040320084496002601ca40d000c1c007001002110501031458216030000303400b83c0e5a4a40c1030316a03002d400e0100d4029 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 776777455 1250 776776205 776776213
    0x18050402160605100302060304150b060f130503030a090509091203040818120606210109120f03060501050412020105070506040b40020a03080f0a1b0c06030b0a0503 72
    0x9107010a0900c403120751140300c0c100070050380e100e540c0690048900c50200940140041010402046984800d4a65803128407001f1502d800c0c200302240440c0c10148002e901c019002c140c180741026500481c0b40584000c1d00214249040b02c1c034014800d22192092a024081c2a008582d840005215200900030b8081b903540d03a0781003502c0c0543c03c075400452020f00005104280e10f5803031415049c1d00c030303c0c94246401000d585d1107020070801481030011505001e4480210409131101c001c0c0101c01d15940685030900611310310b060068401d00c0301e9004130040500e41001408a6a00141a40c00b941c2c0c000760140b4400038580f005032030030300c503071800908030344640000c000411a020a845100701c1c2c401ca0220081c00e040c810540a0284031091492200c02c240c0884580801090a801100740024103007103201c1e0307590b00c0e5030300f603503012542d4040000c1c0002005c49640c0d42143e290b2004000004080c15450700300c0c1c030303003042610710750182c1c0e0209178550010304059510b24500d000a040c00030b05403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 776778705 1250 776777455 776777467
    0x120c0c010203101502010510050f011125060804051005070905060d1b050c070b0c120a08060306010e15090a061a1b0102070302030313030216030809090c09030a0318050402 75
    0x100f549242e02c04c46110b030711541c100a60710752040c05040d015a8262203890718040c01d110070030450b6150b180310503042101c0300d451094064000c0015900c140081c80b014200d5902590f40e03060b001200350046002e2088500030711001030400107005081105c010800107458907040b004039a10613050344402d61000c0089950403032050070b0762200303c407148088900c12030201285029202c0e4000c000808201d0340003060100104001e45004003031340040102170316590340000c00c2c80d6109800c01c040110004a0280402807036040400040c0c1c00b41c080072808001c680740908154204500c0c08441501400060000c1450500a90040400b50446151680d9000c0301039810b029290050f226494002c8040070307206448810620031954410f030142c1c084d518540c1c40324a4417071340d988505411401c500c12425858515030b224907034080038512850000e41c3c0c1d402e8007402c2000c40303400905402411103041004c0d19042c1e034001094411258181084003007081c101a008840c01e540b503200d20f810500018034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 776779955 1250 776778705 776778721
    0x3030c03040c0e160801091107030c06200c0d02060f0a1d01020f090a0f0302010c0803180a300f0c1505070e0310060e0406050c160b0601020c0312120c0c010203 70
    0x34070510081591171001580ea181a6542a1a080007200c11600020000100030a02c5420703c0b40300280114008103240b5074903504003030340030419503542c0c940b8000401c002e42a44010b020b465200d0101c1d00c000c0c03a0a00384034040c0109540302038002c40d120f99803200b4682c9500d1980810361014a400c0d00215103902d1001400044c1d6400401141c0c03140d58450f4000c03660510301060b040c29260180c4d15503078420000d80c0e43e107040741c3c000707410f581312028841d4450300c0d900700802104901d6841124145420810b80c0340604602d50b101c00140d03220302d03466880c81202d50f4050604028001c592800402e140102c0c284220000100344841c0105401c01c01000300c5250004006048040c040e011281144103800b401c030704480c501c1c00384107a03605803a0080f60228040e600003036001400340001a107000000300f103440b010800d542040362049085c000301701b8150b030140035a040d00d20341640a000b02c40720f90503034a041c52041c15a00030003a12440e02090900310804190349801d07010380021541c03400e02d001307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 776781205 1250 776779955 776779981
    0xb090c2118010605030f0319120905030a0905090f070e040e1c1806052a01090506060a0911030a0903020106080a24060e2e1404050106080903030c03040c0e 68
    0x84034280c1903080c480f000896080020307118040c0c4661401175800d00c0700c05045184004140040a0200490801c50301400c2c0d50714420701790094441d900442d5031300984c1c030000d00201802da0140d171007040300100700a5140b2940b90940c0d4000c2d41890302250640300314000400500c0c4202004002d071081100d442d140080b1a4601c600c18006074451803a0320340c1070012040c13418254050100054010300980d2958030034500c0c8160000c1664401c1d02210728240c03e140c1c21600501c1c0f007680d480d40001c0c00c0c047d05d0708020b01d0b134002401a0300b1050004a40428164595100c09414620000c1c1d64400f40c07000e062003948001c4c050f1001109440c40140103082c05140c81e12039601c00450501080e582d008070314141d200700c0b8102e400308012a4070780d664a2070075080d02620040c0c0c0781d01c20300040c4c41014010558807104405070107541101012111584284821200705030048010b010349a02800391030000002030b00e03800101c10b0a0103503a680d59103400500d050a9510403001c2e01145000e03c502011680 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 776782455 1250 776781205 776781241
    0x301020d14060405150d060e071d0f1b0403110a05060c070312090510080603070306020307050d0e0d020604150908040315141b0d020903030a0f0f030b090c21 69
    0x2102030001d03881e808a211545c4990700c0d605940b140c6120a00b00004c3e005030040e603044020202502c80565a58258025454140d050059400c010808010131041c0383d520054000d40c1d03403002151030800311346410741c151041e40800317404140480f2068440d9550b07104030101814000c1c0c032003601c50708d142c4800d40d900c1d50140070845407020510069001640300b00860812a80010001d8110414803081038501c00801341c000394060141d00008000b003406400194018206a5900c03543c076043c0000f03060858907107401c801840d4101c5201962840c0d0700041c00b0743c000303030400f0703090b41c138081070710745003c002c094131b4000a140000c041400028440001103001c2017050801d000d1120100064102d0000001168441c0d071050351595000f892000d005d020701180b9545602c0180f60842d4100042e2464206e03109910018900d103000744000781c0e01074440603031710700c583c00d09010300400c00c0d00040d404d00d001080400a00004a0765507000c0d40420403112600400d50020705032810700c441d41c07880c810100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 776783705 1250 776782455 776782459
    0x30d0206070f050c1504020d0b16020d09140609030f06090d09050303070c0b0a180e04032d0311041203090302032404060911100f080f01061d0301020d1406 68
    0x25070344002ca01c5000b581180c01d40c4107140080c140e005480c003a2030003061000b8000341d800c8140000540c00183c03105907028019094140c0e0f1204010510a00920b00b6244030100010003000d068100858405001880c0c06104110380039619000b83e607010034070708811040444414440c0c8812311068100200d4542c4034083c007a990328500c2e40d111400d040e601e03c00e02d20000c05a0200a0040200c1c84600001c0d107202121440d060b000e000462240b089051001e800642041d50310400b48400c164129139483c6058003030510f014883d5100e190342e80301c0300060005440a05031030711055501404a82d08860203032058038100d001d07440080c18014480e0a05020881c0240f01d20685900c00412504a0304480c2140d145008076a03076480e5516000307008200c0c02100d084000d8545e15155654040c0e2890344144180d95000c501c81113072074010b11068014103455141d649020041c4400391303000300c5005040382000d00c0d00d14051444070100340244034036080c100d84140383c803c440c0407111240021600034002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 776784955 1250 776783705 776783717
    0x80105010f05041d04031b050c040b0f030a03180b16020f0102011505120304271b091707091505030f030f1909180603020103140610140405030d020607 66
    0x103024000d460900c40c0e4010401d110f8810682c07107030524134294030554054402d141c0084081980c04062240c040d08807411036494201c40a103283c54107051141e0305068004880c2044a034240c000403a4543c00314a501604200800c211261080041e180f15070040c01d0714a440381c0d130760071500b259002010000300202d00c1804001580c400a41c414003a4401c1d44a2609514401916110410094440312000c0441070300007031000081400300400465401e9001d107071400c82201e490351101086450043c0020315444203903075407000c042d5000ca0944180c40c1201c1c2c04442e0203012004440c84d182d41030b48803580c170b603003400192009144081042011294191304071081d0080c42c03d1410703121700441310a04100705090240300300d0030880241003103001c51281007912400f03488840880070281d11030414003191391101020421541c2c540720b40f45210420101e105d00e20300380600000c445550b112086002c2000c5421b40c81400141c0e0400c8800412008045800341146000044d4852404480d41400310b00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 776786205 1250 776784955 776784977
    0xc0b011215050405030405010e0d140703230a020909030d0c0e030d080c030c090a21110409030e1009081e0d080907030b1306050f040506060f03060609180d08010501 72
    0x5660040b94007450b8054069420326041c00011550000d042e0401d541c1304181e00705035008110000f09074649640ba040140c16150304608000440342d02001c5072210342041400048100c0c2000310b0410b529590407a1141455142d13160400c2ca580107040040309581d2400808120480c0c0025a51140c214154166035038080c500c01c0584544c50110381c540c100b0101000000d040c1c142000041005180090528030450b45030300c0c20003a40040d11000d40804042c000e01c18050020604200700005c41c00c5900f808440c0855400601100b046102076006289030300d0b0502c0c800b401a154074000e017003558202c0d004920022a400e00300d42c14015010090701416141100440c0320340c0040e41708048100040c00701c14511750722055554030050000d80813030449048140064064001c142c081e440007214000542490b050040c101100a42040d1044400741c0e951005900c02141c030991000c03084646c6d01c103039941c039850a048080c0c150058006401840e0741180815040030719a4184c0d071081ea500f41c80f030741c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 776787455 1250 776786205 776786243
    0x21603020d0e0d141509070306111c0f0612150e0d0f050d0209090702030a17011206050406110c070806060f0105192307061112060607030c0b0112 64
    0x8003480d2940d9030483c041034a048041904801c600d61801603040440b4001c040c4185500c51024050f9603440294110072000c00c188041c43c0120004c82c0c0d900504903160540e503c09007949084407103180d1180c203440c0c2d00b0380401c90780f86901c113000900e445040103914400900e000051030f00901c0300050074600d4843c016441d90000075815954107000d40380e9888101100c80141c07807a421810715500392903000c011001450f294031400314000d11441d002141c4400007108054203403080b20529858492141004000075500c60344122a0a44c001e440003449071030314100724014041a04002802e1440001d00e448508000030f10388044035459025a64980c0300c140800101c00f0700ca0f1070150004400b8000c0d4800100c00d010304503420303007003810036540c0e039040481c00040e204000d030304d0700407505408a510002e00c8a2400390300c0700e1f490103115480c03500c008030220101041000e4603d502408022895604260041c41808601504210f22225660351450711103d0103083c55005c858450003401050750070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 776788705 1250 776787455 776787467
    0x316080a051b030c0705160801201b030c0307140f071a0a0e03070e0718050607030c15060f0f140307031127060405091203010306110d021603020d 64
    0x20b00103090300d070300180b4071000d9a07800541000d050003071402d00401210001079401c10001c0e8072150380300c00c400403203441c10b00c80301d08603071507111000b000b83c01c401c1282d00c0348404001225100d80c48001c0092800320b001790f205196000c3d50b004d5000900c0000741e61014010030141c2100030703020f01000ca800320320300c0c61803440e00e508091051000a030700d0051340c0800c0c1080e45c0e024018102d914031701507013140c0c1d841c000603241034036986c02152209035010521060170ba008a408006584454451107140c1c640300c081200d92240c03200240030402c80045c0c00e8204400442011030104a822007440001d807100503c0320300d10302da4441c070f003840360100c2c0c000914510031218048c00740300020081e003503c42c6940c079000801441140340a0707001c011480c5507075a0848000141500664580860940386800c0b410310044603405828864554030284205003000701c4241100c3c15242e1000003c81e1505420275915020301582800288250010540d4628a0a41c00c903e41c00076001c1e90031200e0000600800740c0350 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 776789955 1250 776788705 776788711
    0x5071509050f120a0e060702090a0b0405090d0212031005061b0118080d0b0102030d1401031e05030f0901091d04230307110d02040203010e19050f0f060f060316080a05 73
    0x110b20402d010084005010380d5517030100d02d2028180c40e14064017540051340b241ea007102e403040d01c0ca6840031581050708040c0304081d80803130b100c0000c1850207007003c4082c0d90351045884800300340300c00000050740d02d941c541c141d10040801510103a1114194503800a0f04602c0d088001c070550b282520440300ca05210b810078408a811180341460100320540d1100a051151001815031000304003a90005021f40b14101398642c0803c2c0d03620070380d419440d00c44001d51710311200c2c114202080f0207600101708003000300c51583c034442070f00980e00c098290042c1c2d2099a075900c00c1200803a060152174000d1030b0001078611032446241c00e84844049810750040881c0a101c030b001e80755100f400020001014003280c072400410003030405107200090b900040c142d0380260403508030038507590184500501514880603046a1000080c0810f01d40003540c100c02d000002c1c0031070080b0108102061198a900311008005080a0b1030141c1d64502800e103a0300c0014072011070000501c04c1030010b460f8407218810540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 776791205 1250 776789955 776789983
    0x4110d0c050909060f0307031509020f030309060a1803020d030309032003040501050d06261009050c01080720010501060f0203040807062604030909050a05060906090705071509050f 79
    0x2a10740300c113001e10240310050800141c0603c21004048007091801c2000400c001c02c240000c160440c8030f04c14400e030902c100300a507010741d20500420081c0c1d41c44005442c0e142d0031a14101040482200980c1c4038825154800794120380403070200d5050503403680004404a0080e2a035821000c00c8842c01030b20f07048121002225900700b0303c018080d079131040d001002101c400090119102d0740b00d984035030f1681030340d00d1408420340c5e0940c0030840703009c1e023402002c1d120b03001403008202204007900c5860b102c400a111813410482043c00007400503025603c040040090a030300e8600ca00e0703980b01158001c2c130b400e000c0e1002017040a04d004900900c00412901603a240700c0240001d82e14204060380ca514425402d156a40200680c94801c000e07880c241900c10381c0241d80d2400d030725141ca4182c00032914090412040c0608100800410f902c51400c240c0d001a010344030541c0907950108101d46a00510100805480b01c1080394100945250480c51744e850050065030309940d0701c900b91607070b1103c02000ea44 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 776792455 1250 776791205 776791219
    0x50906070f0e01080f09070f091505011701030f0201031103040308010f12020612180f030720061e0f04121202030c060a0c030b091603060b090a0e060f04110d0c0509 72
    0x3d8140d101c000c9051b41200035501114030389612200c801c4005001504421301c8250740d044214050300080400c0c1c3d000301001e08214040c4450b00c05a9915050140000f03030405000541a00441e4825030280203000d09445400f41c490a0515004151900070300c00e15081900c0d031100410b8008003540352031812903001b08200c0c50411000e0340c140c00b80030000e210001c8520105000d002c0745000348038260110310319001860741e907443c030315107030000c2150b0070072081c0d4010070140c3c2c03076425403141b104940d00d1855401640742c10b10002c1e802c00c0f2461140c080001c1c07000f0b9010400003422501c1031244814140700c0c0c4400c120308611038104030b96034051500c0d0311301681d1046012031000c1900e0303400714420700031074a0003148110b405404a41d04940c252080201c1c141142040000c540e4144550340140c00d091107500c1c5130035480740000c4d240074440e00400c2801d84000300810803a64510402c406004400f034014400c0c200a00c09060103a00007905480e0300504011109543e40d02c104221880b00b0700c003c0140e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 776793705 1250 776792455 776792461
    0x60f0d2901230a02280c0608151201140906090a0308040c051f020115060e100306030b01090b03160e040b0402121f180b010605070213050906070f0e0108 67
    0x11102c0c64034840e8410040d810360a02d01c4107041020005120920f15a00144a450714481c00750103640c3c2038140b07103c0390031100701441c0d00203004819504125a0149043d2205442d501e030805404800301c211660300c525403540250ba84401074104c04050b0003a00080c0c0304542c0c44040050321070070100c036249140d4010540075000a4018010300e074115005889058031f06860b0408a80a04107003134540901456101e40d021034950709000781c1c8000741c0c03621211181c07546054009082950b5102000f4800c0301b0300000301c08150711036440500210303003046c07840013256034441304c05005002580000b406401210141c864078146820b80da800c0701c50400c204103455032107032105040c10300043c0049030f000c07109144c210103100003003240000000c444d0703080c00c0712110741d4603450007142c410843c1041d0343c0551400380000b0442041da680d0443d101810001c3d47c4409600c0081e101d134850141255000b031808003840300d000d07030001e0b500e0301c11840c0d92201414044208402d658100501d000766001807119000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 776794955 1250 776793705 776793707
    0x503060904020d05030c06090a0b06030c100509220912080118230a0b0f120c04020f090d0c0504050105090423010f0c05070203070608010806040f03020c060f0d2901 72
    0x4400e01c404c1c020025a400c14044100080c14208281d0300700d40300354807441c0700d041030081705203509410017000ca0040014018020204a035070000e030480b8024808042105141c40c2c40b401401c4840c4841001054074500c1ca0a075002c00500e43c2100a072900618112841403a42c0500000e078140d031b10003108011300c05072000628000d008203500103c0b21090070b100780c140d2641d044583c00e01030cc4510703a000c10000010b02c00d1107031800c2010100b6110f03014103010941103d40100301c141105100380c401583d11002d18192005078860b000046400c0710a412180307003445641c400b072030140d0f041102e041c030050b641c50301080b0641c4810307240640010000786031414a07001704041880e220008100215000700100d600d5411070b00711010100209600042003003c5103428410100644254240625254100100c580d581c0100500c001c10b1a881c1100000c10306001300510382d001a80284404d598201c04402d081080d0440002d00c1100c60500010001c4117100c14140c0d09028494106151608a0880 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 776796205 1250 776794955 776794969
    0x3060315021305060d0c02010e06060a031b05030a081803161806090612050c06070506060603070921140106051e0d021513060f051603050c010f1b050306090402 70
    0x1544816070a00030b8000845449000240508a11101000650051144000e42981d481d8101c48502d071700034400b00000c41d80e603500700800341e0b908081070468044411568414501c030a810442c3e261040510f0002041407c600801032010000c202d82c500c24048000d050f47e64151413400305c00c0a1074080103100591044692144182d03030042c000c07a02c103544010500c00c568480d000080c00301c114507503200521a04000d02c3c15480c2c0207580b41c519150851f101d540e01c8400c003409240c030a400c008041445148101d511001400d117500703c0e000360030843c1c0c920080300344103520112202140450500c11859040c46150101e403c017030650080c00d080301c0c0d03001d4440c1c000f440c0200e031f120850903420000358841c00c0c203850503003100c01c106507034616a0325504001004581d01120030420312100004134290320409030764a5182450100618081903e400c0e40e190289841d003408a45c60021420b801844980140c2e0100b0340b00c8902d809500f00d0f1200884080c07104650f15038221600002140050038201 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 776797455 1250 776796205 776796217
    0xc080a03140901120603120e22200c070e010b1201060f021905060a140114132a0305010f050d120215011409060a122010020313060306031502 62
    0x413400322450030001030f00707404482c01034005941d00100000303a5209241c00281c5620851130031510000c01c90080085144003051304807400141d41d480d076210b0303401681891195030340040317180c14050700d40d5075511480f9910f80300e0b031240320400806040002010641d203c03c4030381500c088402490103a007815030a5540308454001c00c2d0451207501291100500c1d40164198003922450203400981000c111410960342c04680d12400c07612608010000c808084c50788002604043d9001c0c0c4141e540c0c80e580301c00620384402001c481030030512000c0c0121034506031a1080300080d8604103d2662a505480040c5015006007034010031038103004401316120031100f502c40102481200d441e981c0700e01080943c514281e10403031412400204240c11440d1038140035a00039402d80303915485a1a011400c1001e0980385005021251500300c03c0e070001210300001d01e82d4407405000e000c0700030100e4400075900d41c0100078490b00800d003540042a510f1290158030112070304504124220076103001c81e480298010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 776798561 1106 776797455 776797457
    0x2f07181103010e06011b12080a20310602150f0406050a0615020d03060e07080c0a030f0c050714071a0702010504120b040c080a03140901 60
    0x20001e907811075601d00b961204684406006031a00c010414a075800782030a464070b5014081e08606900590004d0b0350345043c59a0b80301183d00495284008442001d01ca00d507c13003101144540240030b114105510306800901681d004040c0f01e400e00400403406504600c080110303a0b01030052082c6003078812a120395600d802e100700c980c182001400200352560b20804682940ca1b10f0744650041c0c000401c14201e0030900260203540d4040780d01c0c00070700182c100080840d140c58000722142c080c1d009a2290780c4107844180352004243c018042101c10107680e20741c2d00400ca50300d03009507402200aa1102c0d035503140207040402840e0454403400d020355125180400c0f802128803041c1082603825540c403a120f000c0c0e80b0048aa6201d29801030300b140654a80c8a8148030f80036480d42c0c09244501c10f0a449580d84280380d0303841d06448075015000c224805200480e460847c001050b00c1c0cad0341 = true := by decide +kernel

theorem cover : BRFrame.Cov 776618705 776798561 := by
  have h0 := BRFrame.cov_init 776618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 776618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 776618705 ≤ n) (h2 : n < 776798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
