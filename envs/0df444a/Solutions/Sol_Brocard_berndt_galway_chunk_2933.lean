-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2933
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:10:44.527381+00:00
-- url     : https://prove2.me/submissions/613fec73-6254-4bf9-af3d-534fab8ff95e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 527338129 ≤ n < 527517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 527339379 1250 527338129 527338157
    0x3030f250503090f0c0a031b030b0a1b09050d0314070c0e04111c080315090109020d27021908190201030507080c030a0209040209040f0204080f0604020a15020309030f070501 76
    0x3450409038442d58200b0410030042c0085503020003403400350138034280f4003081d155276031340c03420544c400841d609605241d03290079480710600c506070104501d0030300d40751800c2c0b150300304800a00040d40d01d090080174460b0101c004c4140310504802c0d20700300c50f00a4156108180c2e0713034040305489901294225000e80828880d11018940080649503035161300070100040c1c0030a81c0c070010140d00c0a42354a0202107400c0d52040c00d5603602c0b0f1030718044c20a140e000b503180c510108080b020303505040380d05030b03030402c40180e50644c01e480d01d46050b04041d011284c0c0b082020000710180f680700c800b03400414040c00360520740b60585503524a502042803007070340c00f004561741c1c61104071960442136924503480c010810118149203c2500505015400244014a400341650004044901441000f14520380114040040c11780601c8a40404249880606120300d0a03600044d00340d0418085c80002940514201a081d0b00c03c0050768022000a422241d6a00e001441c8a0f5207150a00c500740c00241003054581c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 527340629 1250 527339379 527339383
    0x1b060b01120212010905070e03070906090b040204031a19090b1e0601091403010b0904061508060f04031d031006031203090c050d111806040506040e03030f250503090f 73
    0x310b000c032490fa07400a264282104807002d0070028141c1070800c42c0010854146940c14071610005000018000400c1c40c6030103424010780c0e403c0e80285100e0386c4184410404124095009201c0b07454640964520360354903080b03207010342c0c001c03245950341600e00007200c4104a075041400e4018202d403e196052400d246069190318801181c0c20790000340007540400c5087c820f100301044100f0020008140c241029000c115105412241038032802c0e180d171100840440c0c03400354800a0032007000500503616159030261083c08000d0002000c000c1454a901c0100c2c1d2031a009004402d0001e064400307210a921810000c0e288a0105554031804001921300450103403141424855201c020f01714201d10381010020081400307101502c400c14410720030100d660f80c054101400d00307805042d070f0074a41050014441100d50003000103000e5071500e22004407410001040c3e03580b1800b28401c82059988030302618403402c030013068620450300304c00c80c14483c9a41043c0a10703c42c004000c00c48850b403056019542d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 527341879 1250 527340629 527340637
    0xa02030702040b0d260c010c0e130203091509010906060e150306100314010222030b010902071a0907241112070311190c05040f15151b060b011202 64
    0x104031903021020081c4000e0113140c5c00d030580400300c44403414003405d03400080c00e6401080038540026500c80d503014883c13038607031400c0e20f44480400c811400c0d860200201d40c0e40700d66070044d09601000c0e00001820411094001031b010580c00001807140ca6690001c810684006503140360f52082401000364040c100040e0b240e102d0b12403100106052451a19603010721216003018030030a540801581074400750b002c0500040c0054242080f80062841c141b01c50020ba040e001030000034010401180400e4440348061442c24114141c450b581d120b1012061412400d94406a180e043e1099189564030345000101445a520b4482088c22410001c4658440b02245c500c144008030901ca00c02c04240b0900e0f10510080d8400c6c2100e24480b8094940516101c0303030001120755000781042404a424140518910480155018015984009005a01400c01e8060800c8803981a4148001c0340d120b03072042c6100c08038001c3c0044000a0b41c0c1840800b6040044070640440c0601c2101c02000c84188205c1d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 527343129 1250 527341879 527341883
    0x2a09050f040302030d09020a0f0e040c0f12031407060c0518150706050601111911091611120301170f030a08040210360803120109090201090b0a02030702040b0d 70
    0x69840d01c8800106817008043d2084140d0308900104804220710004581d000043c10222101010341e00c3e040ca491028100c0c141c02078038407100d072410300700141e01804030152000d5038181013014802040681901c200d0044c8140078103024240401c80c001150440c004011021018030400a44c1c0c043c0d0042c0301da0328911080403444000100200d134007003521948410380090051405030350501c03266000307078500714003410340703c010881262109040001d000342c4258401d0b000d46940c145440c0100c900e0004500302001c00f820f016110600d92119001441040d0302c1000c1143d4454807540c40e0311801003004007a5103488010302c81c0c0041030482000c0013040e40c01d0741340555100b8006035103136800c0c01030b4207080c0d10710041800801d0010710442c60400081b2040350402d5600e050000d8400700190b0100005940031201e26002040280d02c0442981030050540d50384078801f1810710f0300c52004030703202d00043c0e10410a00c280803030011030b0b42e0350100007010350900071503040c09485494020010201402070700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 527344379 1250 527343129 527343133
    0x270302010f090810020708040e0a0b011707080403110106080307061509050402060d0e010209060a0507030206075018040b06042303031b060a14070503042a09050f040302 74
    0x10000b613495035002440700500c2200c0c4542480d686905150b000101556501d01aa445114100d00303564400300010800580b0315144045040c008000b0340f20300b0b0043e101a04008100d441880801c01c00d402c035038024005041101e5903080641803520003005005070080b04116404070001c0e600380140101070040c2c2e00142004d180070b6054002c4001449480c5030003030b040d502488590350302c0d40e03a900500100e1000d510f0303c0d6512505840c0090428900030201010701207210380c000401e50060321a6020000280c41003201c1202950381a013226070b012044643d011114900f90801c0d030340160240140703214a600303014912101348100010744119032861504144188000c10043c01501070300c0c1461031407142015041c42c01c49000c241903a2000002c110311900c4e210810300c4110007000442e5000b1100c0108200070f400807010340c4a85000a4400300030014003201080034000034800200042c1c241c01801c4144030310010055010144603c18407200504e403100207640000000c0308140f24545c1640 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 527345629 1250 527344379 527344393
    0x2d010614031f06180506041508061303020c0a15080106020a0314030c09091005010909050c07110102070b13060305281e050406020304060c020f07050d03270302010f0908 74
    0x1480300e0034003500c8100b14082076100c110008240c58584038880801c1c00c2a580810289428070600003600d01d040302118001038005010070501d0000300b88107401440c1e40314102084c8640d424201d01d402c6180c4405c9900104038400001c41b000c19010b140d02003101602ca4104a03030f61101c003640c9a8842070780c09004982000c0c40782d812505a40015903219807038100ca0360404035800040345044c80700b200c030600040c603e40800d10031980c10400f010001c0494150074000e515108440071400d0141c03200080020010402441c0668002c0c0650740203807550002c1c55403116016402c1001039040343c840d00380417038035120118541c000201d200c00110003020039001040001904640000c0c08180d60310b8880760000b480002d03001e0075502525001c0d03400b40c10b0140c0c480c200b605104007201c010070b51035815540105440141c01402040c0300c41111421241d805500b451800d003556403040190640e9000301107440d0041402800020700300a99000f80e071401da51101140c010742c1c8540e454000ca00403a48482 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 527346879 1250 527345629 527345653
    0xf1b0e01050304080d050a0917040b04140604030b07020105070e06040302030a120504120303060e10030c03030516060903030510090c020309041a10170a050c040b0c2d01061403 77
    0x1c1e00554100744070792001d0703280001401445040755819035140760003a485410b181c0c24450713111300c020031512054185500d810b2622030032006a10880c440c03081403011403111010340781d0f6610180c03801141c0140e010300c4207180004c802030003050120303402800304400341002ca015081c881c080e207050745d038081c0040450000079282c00701c5010140c3c491b0380030800f0800c00400c6140303800100b800c0241c80390b180404e1080c02e01440c0c0306035900041c02031200000d18601000881c500c1d07504c8800712134141c2006540c80403c4650106070000b8000c01500450a103440b0800305075255015510580c940000d881c5481e40783c940c40c1080c1c03070600a80d200140d1003401550703500d180960040b080c8448a101003030b100000d600c00b107001014140c40c1c3e480440c1c0c060040c40100741d1445841c1d41e2040c00c8070701c03c008500c1d28009225441c091750207810744a03040403404020442040008004c0c0110101118090700d070741c5060414020001c460002507942460380006000c0c9029801c01120003005001c0c2c60f18181030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 527348129 1250 527346879 527346887
    0xf05060c070615050616021f0c050c090c0a050d0204050a030f030f0c0c0510180609060801080c2412010e0108010e0f0705090c13080c120d08041103100f0f1b0e01 71
    0x40c1b800740d0f4031070101d114810316441007140c0912407486585827502d004106091842c10030072141d6035180108115404c010914540d001228040009410099103900c0d1070400c1c180207014540100350402d10040300030091081d03c42c20414414441c0d83d03240210b0410001c22512500388450003080d4510021040c009480c0010b01d070410300300c05142c200340e060406d00300303030280c1c0c800381d8024008940c0440707060000c164490f100328007501440004040811110010481c0d9404801c000d20300c409209401003c01081e10381110781a401603408071201e561101c6214036000c2080c80307030740300540c03a0078034506800002090188605c2486009018002c0c50a014880320060003080606009003c00c45080c4401e0040f59800140c040c0310010300740c28900c081403114440030b2600205480c0d2080044c860b12030340c006900350b0301642c0301907103c135219681c00c0828a40443c520210900606100290362411501d50089400c0b030004982401010550500180341c1002d000c4000c0006080a640d20599409 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 527349379 1250 527348129 527348167
    0x9020d110301180b1b03010303050711010903060903090f090b03061815010e040507123903060207020a1706010909110a2403150504090f05060c0706150506 68
    0x302a001003000c20400f01d002d22180c1204008641554240007071000c03840b420f40c0031460f26088800d8403031641d415a10050943d0048403070085c41c406071490b0f81107150744151030310801503a102a00744010311070b602c0c01070508142405071580c50b094030f40000074031b000640580b800b0b450001d40501002d03210301514200c80c00300c90002e80a14410034a090000341c564006560080240c10b4802509051518000d410022551701a20071000c1c0300c400403002c1024050160425003601c40c1806004d9030102440c1c0005904603a1105543c0340317960004140403140d002410035038400c984140c1c0b49074503140d040d488600c1e00c2c510b042c0382e80e0140005001400450b40b203081c040780610080f0b18219070510019070507071115088812045003454148102e0802c0341d0040c458580c00e820140401c1211449045911802d407081e50b1043ea10b40b159842440405025000352540010540c0d18524025404807010740c080702081f260203142c03540400e41c0342505880942541c200038502e42c40c00309516102030341080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 527350629 1250 527349379 527349413
    0x3031a030607051b01231503011b0309050a140304170f15041b0b1902010614060d0f2d0b0a0e062116051c30050d050a09020d 55
    0x2d41c40c580c1440e14011b02e044010010381c0b40e00e48071043e1800c440b000242c88803100b5040e000e40e042c0300c0c8100300b8400041c03449800181515000982c40c4035070a02c00e2900c1aa02d102030550804001c40e0302e080c0d000400200240c0d003420b9106528407030310040340c6660744000d800c6c104c407581020f10b00b0245131441e04480c1da00039024000c00180795294040404842d101035120801c00d81c00011900d02d1406110b15034100150b07036000800181d8600040b00b00c48181500107248141000501865200c0b0144d00207000003041131810000d6012403000c01502d6941c07600843c0c62813808c60507035489100507000c0d20103c1080505040c07a007c0c0f4003540d003402c0c90310280c0001e51207000b0504403200b0608074114540540442d90003072410720300c04c80c0043c0b081c0c190ba42116004515044c504d4581901c804a02141154001243d40d07410f000d01c102c0240c440c103603413050f41c204001421049100b60b40b00014040c00c21815108000780d440b81c810b94030440b166070350002c1d08042400e0000c07000c40c20003014000012 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 527351879 1250 527350629 527350631
    0x90306041106071202010b040b06030907090c0311031509010503070f1e03080705160b070206031f1e0609060305060d020d02010e0607080c010b27041703010303031a030607051b01 78
    0xc0f031980c58041c615050320314000180e40d1200181c40600c3d00c3d00903010b0740c070420340d02e192030b50414401040c0c4034101d600403601c486881d51031480e2014480d81c03044003044062202e1a8907410309140003030b8101c004401e124450131403074002041502d40494104201c1d07210f0700c0040d04007880c094101e401071105c0e044002112152400001c0496540c0b0001c141041c800c1c409002481d800701d05407501c8184170b400c100000001031200d0001602d030242201c1d0010440028200c00f00e004090501e03030018076801050305501e480e000f5003030b07403180806260151180c0303403200e43c601174850404400700c890840f00280c1c40800300001c032000d41090340001012038010304d00507582143e1840030031160f5205110498612a001820a1a02400b072143d090070030030484a01a84034081c1a0b6905050319107040405808011008075003041510f200303503044100342e2005140c030b942e500d04014008108458050301c0c600d0230b2070769140c034902e00402d400b40325a189445441c1401802040c001e910300444010341381c15 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 527353129 1250 527351879 527351887
    0x12c0f04080702060a03020904110c0a02011d0406080615040b091321050a200304060809010e070e150409080a030f0e060a09030f08150d061b03051803090306041106 72
    0x144c1c44c1c001c0180001707906074401503921401c40c1c0621049602c94180555009000e200d1540840408a44640040d409203081900b00b044d1800d0031b06100d0300882d200364464644280009c108a002c19810702c906100170410510f02d900c1d03410300c019185026005a8407800384d42c000b030880070400c2002c550080c0030f038000d40b0328a407040f0b0049000082410f070042c04070b1000700b80c515415900001c0c0c0198141159903540d02c031600c900e1210ba0300d0140e4082c00f024030164900007181104250f025105071030421701190314480e40c170050200c00c00030a560116a0b5114042d4001003820203016052449901681440c40d002c003050301200104145c6806481e02900c40002d44075100081007114001c0c0705a0070002001007103841c003e00315541000410301400f4505040150080840f000c01d0000081a02c01003140c1a540c41c01100508426001c02251241e4680a40303d0551507400f9501c5806100d0303246072440c0c010081d06a4900484c00a941d00d0340c80580050001120b0508649400101401150034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 527354379 1250 527353129 527353133
    0x90a0e0f010f0608240105040c021204180e0d0801030b100504090b091507020a0602250f0203160b0910090b040308031909111002160b03012c0f040807 66
    0xb558800442d0301d4003180c0321001440103420178020307008103001c14401e220079a0300056001d440b840052113598403596035040c0d007402c028002d11403511908170f14410295226100c0240d8020601c1165001103c1071401d140301a04580006264a00f1003d0b07840700e401b182c0c6150b07900c09900b00002c10744d400e13111a1540001d07154a03280a0585090711030081e418203890010462850118a5a40c586840c2050024441103039004100b0f815805c0e007001303000da5240074800c0e0512000340b0205650504918004068041c400c140f0b00420440d4802c405075401003c076017054031036910301c900506503c0d000400484516283c900946150781280341044404680c0d40d03c030204203500641e1003a1000e44002042100c20a805c074444203041c001a00d04000d0b110352902c5102000f0034081100e8064070101c9040d0700098001c02242c4100c940108440c90b5240d02d40307002d036a05800a00c01d0a0a108035514840c000c0142c805110005070400003030f00900b65240034026078201e1000d0400d4801c41c20402503080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 527355629 1250 527354379 527354381
    0x30e04020c100b09040c0e07052506060e060a05040506120102041e06020105010605030a051015121116021309061103060f121c11010624050405090a0e0f01 68
    0x1e001c8003080180581252414074182030300e804100051158a103d0308020014101b0704080050b01c25030390100341d4a5503a0030058643d8031502c04013601c04000e20b107010403410640c0c1d2007001454400c000502000c1c0d5903160820040009640c801e900241021042c00107041650040b64070070f0005103031015180e1100c46607401c90f44550000300c4044001c0300201801c12074041480000c01541c4001c1140350302d03181300141035003c06080d2245040d1501c0209010140040140c07024000540350407081401c0014090107251038126510700d0107040200080d01058040d0542c1d50115086a80e40714020142e400c11640403a801c4513450516038601c0704030041441c500c1038140d82c0c0b17000c0945650380e04001c410030680c401e04800203480340c11641c400b070f283e41801080c5181c2440540841d41002141c542c020340d0303101102c4c50748001d1586480340000305465550441c21035540b005559501c480e022883c202d401c0e2199004040e000344505010602515041e40326800c000d56141c02da90f580c084540c0c00c14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 527356879 1250 527355629 527355637
    0x30109020904061d04021e0108060405061206191a0a151124090c0112052a0703033c020909040f0201020d0e01230f030a060f060c0506040f030e0402 65
    0x130300c12028142000218249465009040700d042d00096100c0903011000030a040001440c05000f55150000705080351544000360416a50850035242c0740c0c0341c0300b2180c4111000d002d051403c20b41c02c0c0280100780c040000c15644600101424610201c1d080420f0b400507c0c0451640c40104072a1340d0400d80c1010062220012219000303035040d4a050000701c42288452000d031600c141e40d0004666110981e801c0314420b1951000c1c6100428142d4a000c04c0d8070a100240d02005c41c40083c2e005200803280c8228014280144070707440810210782d42c040c5c0040410400e004058551600d011460401801c0204400c0c5c030042e688400340c5444c48403408910303000d00548088075000c9845203504210341e01440304040380c103814540444c0507100800000e20914000450740c00201c225142c0b06020300c440ca0440380021204c0c80159a00c0c1052501d110040940740b2420000c1d0500100c0820103500c20314800140c180c100b4010095612991204e101c20542004100d09101100c190408151160b002030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 527358129 1250 527356879 527356919
    0xa09050d0f1d0622140f010f120b10080405060109050103080d092d02010e0121050c0412030206160905010f0305090a060c030605010e040209180912120402030f0604050303010902090406 81
    0x31419103055004034410401941251090b0b001b03840161075643c0c041c10700003840341949000600c00004484610003031400c104880c0c3c00c0003682410206080d00b0919441c040e500c0b8608950a5030707659500e042c2160f80c00e000003072061408203c201e2207130480d034100100150003181c40f0149890000d0080001000f550803e07201e0075a0403101c0f13000e542e080100308031204002e080c00b0500d1070b190807558402d05440e960020040e6903a0001c90a14200e0b001960007815a9020f00030b1303222541d05011f0355076402207a100750f0b01d025045034800354a1041d241c081c00c0710410b841e0050b26005000041c2d000d881c004100e0501481101c0805000c112180554034180300c550714001001c6040c00e00040841886511a5024030300420400c180b680725034506800c1d610000340520403c1d281c6810080c14140302c1c9211401c159004100c0c00c00c0e03007002c0782e0118010b910031402c4400c6080a00c01c8aa103a5100310f402400742d81003440100705500c2c4940043c48000b4004000146051700c8102104a40040c2541 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 527359379 1250 527358129 527358187
    0xc0604201e0108071103040603091a011d01080705030c04090f0f080a090609080307122c09012103030506010c05060406061406070f02010e13050a09050d0f1d06 70
    0x901205581160f9040e41210180c945008201071408426a81e8442ca120380d10415a48000f424240540c601e10744803540c400c02074210702565200340741c11802c0440c0c14034504024620b0000a00307560005400e8049800240180005c0c0c0d2881c001c12004004480341521041054500400000d003d406880c0078244240051900c03160010380c014030344601d0b90050f9041c0300505905101108000046e00c10995025110000c82c1a150001f22840c10040070880e5403401480b48140459480c8402900c50072010b03120718000e40e903210201c580204480642c400e90400325140b03000171038400d03045a5403010040c181882400440d030369042c50310304211416600c441d41d0314400d0200452887c0e410341d684a048611606082190b00c4519100c1d41000b0001d06008a010302000340791100685d400140d1400a0100000d10b00740c242e820142882800071034060044881c0400e02c580030325a11540080700e03507104a003001184410b048120460241e207035201c10300380b200c041482c015103604040551030481c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 527360629 1250 527359379 527359429
    0x15150a0801140708150a09020f090307030c05030607050f090d0606080f03030604140f01170c210606010305010f230402042d0303210b030304060c0b010b0c060420 71
    0x220080000401901708000101500704080792075a8a41d1343e84103903124079000503582c0c60240541078643c0b0881c04a0707074150081c0d05000040c0710010a11504844040c3c0990340303240d540c000125070034402e80c0c0c40f414002c801807190034001c1c107000510f2482c1602c990000661240c45141e10387c41d0204101040050b40d0000042004c0c7e410700780203030145410540014030850070070840160000b1014003810000182d40b880c1200107440410100102c9903003d000c50b260035000c0f22158140c0c0034100f500358814401e80001c074000e54880e12405040354103070401d04008505080c0c1c1d4400d0a0075003003402103400070b6170136856496038940c1b00030300c028080060500302525401c900c2e400c0007036042490408564101d0410008280c12608042c06580c84040e44502d440f01420000010204080d000350107200205001c140183c0181010780307c2805510142c003140c0c2d91b40045000751285540160480d040500482c2c0000c1440040159007000b071700742030000e1047c1c8800f04031706c6501010000c0b001c40c8000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 527361879 1250 527360629 527360641
    0x10306031b050a050d0302030a18150c231b131b021002180d020607051e01060b04081b1c0f0201030f0b100509130608010b01030e15150a080114 63
    0x310f540100b4041e5542d40300e00d94241c03000303500d07130044112480902c15280c080301031540c41841d906d00a029806076040c4000d00c2014002d14000030014200c1d1007540d010303881415078000111301a6000b0584006080b00e48201015001d680410410190010b51f000906028056039020b4028420170f06c802004071000b004100919150040601105040c41005000d034004030360003400ca1404000c2da05d079000308226201240ca940305442e4060014010340a210030901c00c4054400e941c203941c540240b20003030326405061a81e01c41e41c03042c40060303400782000d100001a00b000c61402d200009001c19480a800e41d9116050401c20310304031422200f5800100c1150b0b014402c003915021994030800c05100a82e011030781058028000c08148140440e80d040c1c0755440054903140c0b0b40345044144106992a0315a501a20001e00710f10b002c6400d041d03000d00c200000203900b50314500060104051034641403202da1055160030b08d0709401058005020a1242007406510103541034070b14040e80c145402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 527363129 1250 527361879 527361889
    0x702010305060a03030e0f01090e100302090c12041203020c0304060203120a050412031109061204110405040b1302030307080307050a090806010f03060b0a12050d03060b190c02010306031b05 83
    0x51502d8440c0ba61507030240042035001d002c150382180260707280031240c5640d00c0188c0b402041031344520a459038190400c00d1003000440700c002100e00c2511880c4a580b9624124141402600850800c505401c0c0004020881414003010f03034044a0500602d004500c0c83d000d0309542c0030350000000740e4030000f018010745035803a8920b0740c441c1d5152010000c42c01d150f41e0b0201c140c90041405410140c49a0f460054030716100c0c11120f003ea8001c089070b82c0c4018103212920303908002c070b030705484400e03c1d0310704840c450602e03028940c891a8012118440390340c03910140780c410b41c540c103400d0360584024403a010011315014015409001141c40b0305440e110043d40c000c2c0140b03110780180800d40c1041004103d0388000e01000380aa130380c45140480e1000071100490380c0914164004103030040700400f018180301380401c030903040f0049654140641a2244820200c6108400440b44d00802b1518100c925500c902407104080388149004a003083d078035226a5201c08200042c00d46140400300100303e54648 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 527364379 1250 527363129 527363131
    0x10270516050a05010f0e0102070e011401110a03080115050405040f05011424071505041406070302040807030f0614090c0f0301060b1e0f03040501021801020105151210110702010305 79
    0x411229402d0709420040002c0400d20040d03106004e2001948103480581c1c001c0c4030100c064409554040082e46c0c2d14000000240c4200201c0342c08551010280c003211600400c14a03205a056140e080085e441c00401e03c0740018044d0a10007000028000424681c1c1c43e40030b0040c0607240c0310b001242d1035042a40b01e90900d1910321141d48521000c0070a210442d108045000300c98204034581d503101d02250924070300070384001c000051014a001c04001c100003081981c94143c62000307044400350ba452800c141c0481c416030003100f07a5688801010800516a8204020b829204150128400d000400d41001c0000309603102c10940d02b00c4609030030700781014480c0c507158407402c6000307029040ca065a207140c107104040036140204184082c1100340c0d5a48001c40301807001151500c0d17541d20305800c00c28001d400008030b20600d00e940b45c4031010958414080d0b42d0288071105845503038490350303608100c1030120070b0490b80c0f0303580078503900100350402b0751148409004003070941c1d0350380309541d100042c21100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 527365629 1250 527364379 527364389
    0x7020615061e03070c05031b070b1318020c010f0e060c04030c0e070c0b0108010c0305011202131a031e1e0a060b0d020901060509031e10270516 63
    0xd052060b0803103504064140519541050070040c0d42c0c1e140c40c60210b51002c92120003402c940700002c1c1c0541003880b42c0b03500c0c120143c20902640c5501d515031810700568855455444e00d4100c1219007448401c101074030640e604450700f8001413a0191030014903081d00d07581d00a1146155513141c00c40455041400a594403a04d0345500c2454070f400c2da61024644140d6000719650680d40500180c56940285034040c2460f400074170744200c035a0f480040c14060420041980002404e2900000e4611a0154919002c40d40101244450006e40d80260010844209403817490a81011000e80341e032403c2c45030b50000b0f0500d031401a03400340003414030352809510011403036040c0700120300030b600100f020510a015581c048808140d0010340c20000d05230040344070b4040c1d40044c403540002411500000103202144c000da080d509000110700d003c039811390301003840b02c680f50800c0c4404003410030640d100f0405c00c00602c4405030b031281e4120500724803041c030000459895001c42c03956051103c5940a0b000100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 527366879 1250 527365629 527365639
    0x2090405010b0111060c1b0304050a0e15030102040501050d0c03060306061401110309090105060c0f01020310031406040201080109090f211101150302060703120f0b0114040506190203070b07020615 86
    0xc200180d1b4403185105294400000050400c0449090030052007160002c00c1c004282c1d0b51f0f5162140c01c0031102c00c005881c0c0011344c41c44103618035124181802501d00300c0304140c4031141480004c500c6040981002d20340c1c0720825683d036102000284080c4107100143c01e60003140c3c10b106a1450014240c0c10b18840c0d400744582c000e000a4510b40d030340360703090b6055030707010795100b62030710700000c803492914820354800240b075400401004206a060307003210301101d0064000f40b00342c2e46c8000f441d40d1142c00940c2c0c007034001514800144030055954002c40e0407030f88241c012541102c0c0588684d800c8104141c2d82c2050201340e20142c507012076001040e01e0203000808000c01c0100018400c0c81144005484002e0090a0210b448403c3c180212402844d10000480501c100600c80030a18001e00c500084030303022420b00c00b02c0d40107001c802c00541e000e0303400c040d050510b040940341030000003100c003502c9401144001c01c040000159820741042c000c0103030780c0092005052900682c41d00d20024500c45000d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 527368129 1250 527366879 527366881
    0x130c0b1c0b0f01050f07060207050c0a1e060e03030409050a060609080714092e0e011a040b16020d081306080c0702090a0617060a05060405010302030307060c030902090405010b011106 80
    0x156070703214003402078042c02d0904603036404024043d496640034043c2c0103082d0520109040061240c0400c1d6652520422503905100c1516a9031080300b202a80c099104142c5820380c0074021140551307408001100000d00701c0e0704250395a8081e60035924100c40e03802e07217142ca0358001c102c8142c004001c180a442c584011306415802d01390217486040800311064404c4001c240030610458944070850a04c0180c401c03032981c10504020070300c0041c0824031903440c81040e18000001e50f03070219104592102a241d01c00c0303140c1403404800103103035008010b9040c1c80182800c001c1d0016a01c130302011142911507181141c6980611010381ca007100c42d5445041072082c410200f003000243d050454600304d5040ba80e00805440741102c0200812180c0c115210006110031060880c0d0742c00143d491091aa1078028410396481d03800f4001a41d03000e12000b50942c2c8280002800110181c1100019401926000900301411307000101440e4040e942510340f6551400840ca2035603014019001c0740331100002c00b0342d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 527369379 1250 527368129 527368151
    0x21914060915070804110607200102061003080c030f0a0908100c09120c080d020a021f09121703190e060f1803090d06020910090605030a05130c0b1c 65
    0x802d00b80284032408018901300010208003081c200a40420340150240e5216505450651720405c02c07140040c00030101641c0c542c40c6c1c1d40c400601c0900c140002d00440981c1451076540d415250480800e000359800180002000070080c01d000d445020750300c1e654009d607540b4040b4400c0c1400c1d21244441216414002034404440d0065240700c100c03a008840441013410714203005183d4203907904980c4041c0101060307000c129900045c0384a22500846011017101099400c91140003815014036000c01c080c6841004412010941c40341700c00e005000d5180403070403030300c0003900641c0304031030703400c2c0c104407520301c40e000686d076441000001801d42004101609004003030419205008000d0310358802e030840b110802c40000c2c0140c1c1d4480c0405007003c2203101a07850028080d42120160700e02400d109500c0070b8140e4403170700d191021075103152110351a54aa20501c0809007800903c50325050580f684040001081d14003160010180080301d07540303850b40500652100700c0107800014415051001200da = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 527370629 1250 527369379 527369413
    0x112110a05090f06030403321c0905010e280213020f0409230f06210102040e0c040512070e04030f0c0210020a030807111c021e030c06060d0f11010219140609 69
    0x410844203455008541021680c40c0141c10122b40051480d402c00c0c4949804800c0064800320032030104100540d1601c40c00f030380f0002c0c82d000307010280d4441031241c0d0078002d01403503500414010500e08005450a070700d4480b480c00769002c900300c0c0c07071411303948001200c00f030810801d040c6e81200000c1100610b030b003002c0340015031116040700c091620420102c001070000200b58119070060502032288001450145000c0305150450312680c0d00446c0a00800c840c80200440d400c002c2c1c0f042d007002103842da1207a48040b5200e44c8003001c9401481041000e601c05030f9624000207621f41c2d40d91340242200d0b2000c0c58010078112001d412181485a401d080c3c0032801030200b49901484420082503e0180c0d007000b04920f0b00c040c008080030f204071950008540c0500c040010080c100111080780c129498007030034041121102400608180d4226a54600161240302d500031107140510444148165201e000c0460f1549000d04440070140c05030b28002001c1c0500035260300000e080003825400500d00c1c1080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 527371879 1250 527370629 527370637
    0x40e060105190e03100f0b10020304030305031803070b0c1803010b030a1412040803070c080c09011403011407020a060b090412180308040e060112110a05090f0603040332 74
    0x9030601c88003404580c0f0a850802210301800800e100c103106845e5100d0055004042d42c1d50303d18041c54100d007910384450700000803174084981c5a0b84072031443d43ea0320345801082002d41000748150000304010008a2841d850880c0070381100d906060b9600c3c8030b40e24030b10f401408903545078004c2e41801490542607801080726840603401c0f4182c1b04108a42580c19820100001c4022084100108000c10b0700c110000c0601411481607950044042e11a00d210369281c665100c821341c860103210050041030003e0032031400784030300036001040712140410b406101b04030031182d100060b8416245401404039900070081006e03410754081d2500d04090f00c07443e04c21180031341d201c402c5c41040f502c80b41000c0214a1080002c60300403100f1612a500c4003c81034061405445441c005880010741d5502a10700707208101da50840000620300e001c4102c40144d41076006048540e41c09203546e80c00302003980303444004501c0745110703540d600032100e840c4030f000644c800200340c00c0c10421000c6204141d14410b072001c079 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 527373129 1250 527371879 527371927
    0x30623130b030a0501050108150a0605100c080c06012709020d03030c0c1b030c06020309180a02090409080304030915020d08061c0b0a0501080d0921020a030305040e060105 75
    0xc9205640507011034900f00070391030020301c9586004000a1801d001051440101c200781c1d408501d02c2c0c903202825015114903001e219800304420421220320360042d0201101544514841030a03d0040d4100d141446000d0b441000c5c1c600000040400403107680281668408002508000214843e00410a08110031030020180f50790b58010325107080c00342c07031242913041d031254040002e01000c0d0f0181d81000e0507440300312200c0b000d402000c5115800441910410000135150741000421442e02030004a80035261060310303a42000040040d4845003c5c06070702d1401841441d907207050500d001004590310768401781b4003044c4410f0040320140d0115031124a0000780c07400100e04c1d100c413400682c0684201c420721086000602003201000b4034841502e215498050b410415603036143c00a40c1c44100c1c0c445c0c1352002a030200001c0c031640e503001d009100d9082c0b84251585003000a41c0c0429075107400c47d00107070082030313011608000c50b02c0d0340b460580e4400300038a0b2076800c0c60320480c051014081c025403d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 527374379 1250 527373129 527373131
    0x90e0d090e0a0b0d0318061119060f060b090a1a030127382b060e060406050606120c0c1c030608060603011505090903040b0a03062313 59
    0x4581c0582071074105038180301000700850904d090f05d2070050300410140c13564002d1103200440001d640c80c02490303611070052604002d40740d03c100c119200381104180100440d0b4041c0d50f885460340310701080c03080314045c10100460321365582041c020040390a0043e4801100500c081c000010803074420300650f41100d5980307180014884103007810380e0104403aa100180b407549481e9a00c11505040304038280c0b03405140200c1070307030500e64000500000c52140300b150b0b0013034842d040d901c02d140762440011007411800300584c2d4003810b10381d40300700030380350300e124060300329441601440284510382c464560801c1040715034920b8003818403d101c25503807008109103903001021030002031414050002c40f41d4400b4181e10301a410940e900040c005100a015a00f0144503110001704207080511424420310070a00711001c4051400301002401c400c02031546c4000d020901c40043c04040000190005004644010815508251102044e8410300024030a07424450a408201381c407940681c2c01c100d5240c0d10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 527375629 1250 527374379 527374381
    0x90302011218030507060c0c231507030507181206050402240c0f0f060a0506010903080a030b0f040c0c020609041e0b030607090f0510030603051501090e0d090e 70
    0x20300840145108103030900c64203801811002019400801081d500707206d44020003d00c242002d00722042c43d082e5500400346e0443c41012030701e642000c44449400c1d41944c04035030f02d148c1c7c0403807007000c1d088041d104080802c0c1c6030000c1c060001c0c0c105601c45c040491004041c00702d04d02d0200c3d01d81c900115918042c041e5540d0300085015521a5030906500c0000c01c8643d10140d070441e1801441c0d5407000c0c850150b9402202c3c170426011001145c002010f000c00c100910554070341141d60030003400c02419a40c14010a0080000011040805401c040d0665180080d01d1711124090020b28451100c041e8852451702188058168005a80200c800c0c0c040c1c0d0520348841e445000f1400920702c0b440f44801c401840c103d103040b4460319812050b90200190180c0703941d5212950b0658004c0c1441c00740c007905481084051045040c05150031008500d10724010602c5503903615440c2c01c240b401134224194682c00001800307882443c2c020210b9040f030480003030500a90035030f4010305a070802d00680b12140c150790 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 527376879 1250 527375629 527375657
    0x53a1805101a060a02100b01052107030e0d0306091104081e16030c050307050105070203030f0901030f050a05040209010506040b0f070c080d05070309080a030c08030603010e1b010305011509030201 86
    0x50b45850924042d00c0155640704000001e5a0340b400310030f80030301c40d5042c04c2c542000e40d445142130b200042281c243d69103c144050355102980c03603000b0042d200701650b59103406686c0ca41003020041e000c0072078030001003c03800e1aa515060303030407040c818504c001003040308000c44500002c03c401718440000d81214031010090b6010300385101c140c00c1310a42c617500d840206c148261001280212036003101140d00403641d480040d19103006801019505800c01d100040703c5228101c01004144e005260024045540801d4038049520540b00070b08155541c5013000304600f410600b040c09890f0803078481c1d003401e2078640e0000c81441615011950f240010800c401000041501e05014110b42d01c140c4481030b401031002004c80d04410400d60001320104000100d084021803044010303501a0345050020b0010f0300d80d418035a20241c14160150350700d00301c0701c11241083c00900b04143d4624000825440c4c54000107040d03900607081101c000c00d21038039681c5416001650f15080b42d60a084c0807101c41e0300c0c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 527378129 1250 527376879 527376911
    0x7050f030a09020109180f1415010804030c080f07022106060409020112061707060c150c0e0409050c1203090f010e0102030c150117010506010807053a180510 69
    0x298806d8001054000810300c1c500c55a03013110307803a8809198100716a0441c00c207011511513065812a402c620101b100d40400c3d4410314465620600908102d04401c01c596540b610b1035004d240241d100302c0c0c0104620f02140344c00b040440001040000340110303c00c2c046100358590307001800c4d20b4450f95580b80c0c00401c590082c01ca003086d4400d2120304201e199902c2c1000d0604606884900c4800c1c01004000b00c0c605020b610449031480d00a0400300d43d0851140401004144a0030642d0900002050113082640e8a00a80c8055440b805c003401d4940b004000f4044000520074518510350014031014031607407592002a084041309107408560085120010b07401c2d842025071a04081c000c0d110010701c1110601c0f4424100c515034a1072011801055100608a0b0310644005000444540106070040d1013100a8402100c0c4903000c40c1080040c1113a410300101c145101c5104681c402c030300c04401c40320a02c6942c4070540000b801c2c202940e140e6588035114031000100c0800701c0e59540040c4025500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 527379379 1250 527378129 527378147
    0xc050909010e10020403020102070503121206040603120c02010206010f03202209050613080a142713020a09440d09050d02130207050102040308030f07050f030a090201 73
    0x18506843d0000a850714100113903000780004d1b805441414000280f40c100025000c03441020481d01c2400c00c82044c1c5000c500c10400307003030280e100b501c80c1d0010000c82c241c406603640c9a29291207081c0195035034800a420300c2816440718194a488100800226840c24803404042d80e864000a81541c1200d00003455540402c03402041003207001401c8801840560000035428003034411201c0300d40e07a1100711540100f00c144001d00290b02072040c040b4103800f40007404000500000241c5c2050041220702e405200240d4602000e00c1541c941c5100a060068a000407200f08901c00d5151415032131016001801921036900a021140314400340d1505001004002000b10031607005694200d89900c1d1620383d560070600c03158040e101c8031180c00b0b4003d05c00c0008840f005008145198015003c10110f078924102406420f45c0800120340014428030050029501c2003840da5181d080042204410791002082202803007000c015000075464040280c070743c440d03107a00c00031641d21076620040328900c1c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 527380629 1250 527379379 527379401
    0xc020d0b0108060a06120f060b0f040f0213080109020307230406090b090702060f0c070c0314010e10150302220603030e100c0c030f030512010b19020a0c05090901 71
    0x42140e0020400030b0001c1403d0f80100f0038040144445520f070000075114090080004000705400c4602c04001a0ba60304607100c0a00e0045c000030600c043c440119043c0d40700300c88034000241e4001010480030003c141c0f124040e044200007000b41c09581d90111f030384c0d04a18007580b400000c2018024152603641e180c9a0210b40010340140041943d411000000d000844100b910401c91640040e0f0102c4c800200c03148a104002e440e109151610000044543d02507042603401034026070b00440461a000a1007009c1d0001500020700800d440b19010b003800800043c0c420424140000c490a6811090134001500c0e01102c1d0380c1c04213416032030844245c1047c40c4545031500e00709203002083c0350f04100c81d45400c0900f941e000e1b920285601301150b240e40c0c440360080c00264030300010310200300300e41000b01c8031034400c3c14031900d044650000201c0042c8240d10081c9a01030000b141311005a900b801c804041140d0700007026140880e9440c1c1c0ca0400231130040e0303070188041c40d0000c0c0e41d04030f0942221910b40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 527381879 1250 527380629 527380643
    0x70809030709020c0c0901050105120a0b281724150d0605100902090d0f0204150e06040606080628050d0311120c10090c05130c0305010501020c010207060c020d 70
    0x80324083c44c980c07140000c1007074610828001c400096194002c1045441001c0544206256950385400750001410550039994000850f02013400200060311036041c400d40741c80c0070b6151031a2038a480845c0c4608102d10f40341c04c40e00151481d58008501a4101c8044484950181d05540e03400d00510341c103814048074150300801080e030060520045a0002e07001d4503c2a4088044a40705c540d004168450000880e4210f14100700d8038005c2048a0040310321544010b102041c104203166a094868481da007040a10030b0003801031050302c1c6420312514001340564181180c8034a8444e0010f1859248003840365200c4000d00d03c10b04d0a000071088080240c44004c12a44604005050090200c0f81b4040b01318280d10610652045140b81001914080442c80700104002c84409210710007420841030300301d501000904010034240c0d04d80340d81d200075220303500300016800300c4020b006050324018be2001c1d043d500015404091a42c0c0800d9403010f4850a0030016424000c0c1c1c400f240101c2d42100c0080c0017a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 527383129 1250 527381879 527381887
    0x411190e010e101d120a110d0206070b01170114060105070f080a05040302120109080405060f0405210615060f1315020114100e061314070302040602070f0b07080903070902 75
    0xb0b43c4d0400d10030020710400d0b8034840e07440d40d186024040400c02c074200c0041140d0209104100040c488000b0071074014014001c03415403295903001c2040c5030041b030411500310011a00501c424960800f1450020b21803100a200085208424209040018007440c0c10803070002002c806005503505980080c41e80101d03115954440b0b5000107006800c2030000324840c61600d1000d40d1031400c140078510516402c1200d0b689054500000c105007135000341a010181d82c4244400509139942401114048601e00312008100325078206941c18404014081e0002140511074244d0648901c401d4810310707042c042c092656140c0b10004408080025408880718070041240441925810340013049141c400708690000c2d900c4564035000d1600f102d008000440e0400000144503191105064441d03c7e040540010203490a154480c0007400440761030300400d4001400700100c030390400c599002440a1903560500310300f40020b030350580c0300c2e14401074030081001c50310041e142d03000d011043c0100f002100071995 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 527384379 1250 527383129 527383159
    0x4020f0607021806240301060509030a05010507020a030305060d0b0103170403140c15041a1b010f15050a1d09010e0d03091101110309040c020313030b01050411190e010e 74
    0x3d1503d040702d0b414002d00c04070412507480200c00407451400030303400132014210b0382440801c039401d2300180021039252040a480c04080303007080c40745a00940403940034082e45111170401406954014000c503028641940d140e001103960034000f14152540000181d22034101c2e0b1500200ca07029039000507182030000c240c0846104400a0214840380c800e03101c14100c0c8200100d81c0740c0f103004610030000964025124107150095240051100907851000d00107828280b03803481303084841c210804038556541e03a00c40050f915103503281d1070040208881d041145402e00100104070103184918101d114a4207000c14a28502900b00f032409425a00072141822803000c401400f402c1082c4040e0f69882a0320040e60f00b031351080070650300c200d04c100021444c018209080c0402080358580d450110300041c80119804007503584080001d40c01912003900c0e42d4142000c0000721202c105140340004403c11001c080340340f0000d00e0b0500741140e030030003503103040103400161440c4501c0c200c02c03644070034801c1441e50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 527385629 1250 527384379 527384419
    0xf052104050d1704080c0304230a0506090d0b04050c0d1203150e130c090c050703020c030105060904080d02091908010e0f250503161a070b04020f060702 67
    0x300c0385001d8412a110030740c54031402c0d542d0400030300c8440b00441d10400014040784c040001041501018002c9a107040c1e0341c0c03844104101051440541c440004d041a90f0161804001c0c10001d06411140f480c648500100001d000a941140080c02c41809400007030900c0030034040d0140054015011402204061900481c1c001c024120000400e142c0100d001040800b5011103080d504491380b01d6170076460340c107140e00707031000034090460b09000d800e40040707005400380c001c154441907640c94060f103620b140d240207400d09403a0346070350f03020b40c0c54401004825651218841d400c03a4100080b96611008136030750902078030900c07c40a400000c00080c1030740b0002001c2c8100b0803240031100070011144c0b1403200b00d4648c81c1d241c00800390303039018203419120440140350750450030f0a00604440c1082d51035001c00c0c1484981c8603600c446216021040100440c1c0d00e00b8010321a1040031718074a0a0f6060703035031010841000c0c01c0680078092185520400362101021540c0a0f60002d01c2101e00c0692100d880d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 527386879 1250 527385629 527385631
    0x1201030c0e0f011a0c031e04091a2b1b0306050a290301150b030106030c0c050307061814060601020c011701050d05071a040e1006020c010f0521 63
    0x10780000140000a10103204800e00c450586402c00391050400d0a5851011899000083e1400507400200610030b01031408000045a069944440640391480d14440304111201101c1e080011000762040c0086651030001d51321643c802d00b030410b42e0081c08421003411012075004020000c0c5071000d440b10b030501c0d400900d40122882660144510b5860030040025a10346c2c02025909190082404400c50303810a03280c2503e40d0080c00014810744441052240800385500801c8543c030004010700c490b55050050034400009030906400e8080c8030f42e103240e624882c680d0058030302c0707544002880810313152001c03000e015500840140030a02103416071a0301c40c002900c500f809442200d8000030554041c51580d800079503141d610710050307803a010078810083c41e05041100d980c051482d010507410313021100d840d500380e024845945c0300e0f030408200b0070b074000700500000e0450030003580400c100381d400182c2500001b420301c0c028000d81800789054489002da0251030040074031003107c2c58000f643c05550f00f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 527388129 1250 527386879 527386889
    0xa0b130204110f030609040501020f120f16140d1d030c0c0a050f1c02030307081801020303191805030a0f0207090204150f051c05070809010c02100b061201030c 70
    0x10444202e54500c6540d140c880d4503250901081c0074000140070b07242c500c8031680d006008100141c500180180b09400c10303401b00d854842451042410300c540206140ba5082c1d2110108011104141c08090080d003240d1501121002d40b4600040700c00c2c1c2c012086c0c010208459990b0300641003a4504c0c0b038003e88a4026045e01d07900391280d00000b414514042440b0300450704040c1c6000c030210f1920040c060344a104400031286502c0e55803070742c40141c90070001080140c1c0030344032158490b10000307445a40858098182c1c3d0440d8418801e04c0211041c1e03043d10078001e07008841c0001c8400342d007895480b001e1002080a400340c00f0124443d103e06811068541980242d83c2c02e03210b002d038454505608a02031406200350042c0c6c84c00d000c0401c207000340d402c01e250b0402c0e802d00a080096a50345100c100b0a100ca00079042c90710385e8140015580c10584180e044560000288200403042000035174a6150b5410210980e4071014030074100e03100c90084407c401c881c6502e040c00b40d032710b85c100442168918492 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 527389379 1250 527388129 527388131
    0x40606050405031c0807030209010c0f060518010b03030d020a0e100207260703060c050f0316090e090a110d06020c010509070b120609061513031401060e060907020a0b130204 76
    0x1c6100d1003c40c44035684601030036482d885c415032603d000890007500000c11a605000301204182c01040b40610a900d0307003803281d5030205186c5044080c00f1150390004001c040d807a8142a0300b403c0b55540030042d9240b117050488016214444044221040240001041d03004404030851000042e80030581d07500384e40b1700d0040e4807c999801c2c0720782007601d020749060700c1c0c0070740028005000040c041d4100404a038070720700e00300b8201507030810345039056401950509402c2440340030b544042ea40001c100030081800f20759a02c16480d0000030306484081400000784941080004048942c0c1c5103002c411010703030410421511600c070741d07600d04e00a04054441d90054444d01c1400905001d184046507061a003c01d0095a40d440d0b640c14844001c0000d410345602508421100606e42005130190600e04101c0d0a108001e0303142d0b082440d40003007002113084443c2d040900900818014242468001c0c600b900c811802e9502c40344100c0c20400c103400c1c01086440850300348140740030481d000880d9a4001c83d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 527390629 1250 527389379 527389393
    0x41a030411060a18050316030b0a0225050c0919151710060e070c031101110a0806042702060309010b18091203100504180b010b04180606081902070204060605040503 72
    0x5c00c040d41c841509100c010302c2e02c0c00304c0090001450740c404664100c81010b074058103040d02150b585e96901e661015000848005402c14400d1280412410018040584924002c0e040440154292945440d20003150644451002c110075802c0c0807041d0007808400e9074030020344d460041c2c1d1030715a4014541d12020b9824160301080d004080e4034110300910480c0c079080e0488405130b40540d00210380d00f0501c07000395600c0c02584001d0203401d0042c541c502c0783d507407a204140303004c00401c000c480c03100341c00e2003d421508903410900800080c6107039070b00f0f4049400c580c0700c2d500c080d00c060144c69019070b942c1e080011050071020103114241000e00034040e21094810320640c141c0e40745800e000480d10000d01d6440c0c040c0c01c00103400c243d8001da00c440c040c09181c007502d60441c0c0341c02050000030fa00c07008940340c00017400c024282d4000c2030030030304500b0580240441c501e0181c004143d610040c2501082c44044d0101c902e0740c03105603040303820203540500207002140c1d4840000d02690468414035001c1c0c040c45c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 527391879 1250 527390629 527390639
    0x630110414040605061b15040804060315050102100b04020f0d0c120207050a03030e03090a0b0c07060c050303060f0105040815060f0306160806010504090f020d060803041a030411060a18 81
    0x80a0101075460103005c0ea800c010b00c1c03d4855080502030040480740780255480b1040c200d401c01d44c030a116a0150140642e00c5281034001821a44202e000d202c150059000170700090381c0c0802c1d00003160b421504042601500000040c0082c0301d00d044860100d000041e4125013452150005040440e403615400401c9555001e202d040c3d1040c2c201c010081d03088102d074000003a009078400141c41981c10200c6c0d04000c40100490101019600b02e11040c6502040c2541090020014003000d0f0246103040d044200d102d07a0359580e00c1c00080c00b424480e1884800540c03a5034410f4094600400031310341140c001048400220642e00d03003e451082c00b030079030886082001e0030001041030041e20750403010300510b40d2181003120800c0d8003500060420208000004800038240035003500301420740801030f514a8101144011221039a01c440003541080c441000358150102c401c5403814100d080d540c0d584da54500e4022403045848450780d5005001003144140180d100c528860b5400c2050400d8500586a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 527393129 1250 527391879 527391881
    0x509060105071a0c090402030403080a050105032a03010e24181b04021b0f0d030504050304090c0509090a0510091b11070807060503040308070801063011041404 70
    0x4040c05080c3c00d602481c4601c803910301c0c0c102d440d800780c0601d0710f040c2080d0b00c01c40091305a81c0300342c50aa0006070303424113200c0300f4022403003000d0040c201180104424130004e020360860904101407078214508075001c1040c0c648080d000610f9000d4841c0648840000031500d441c20841011074482c454015a40050030b100d10300398102160026030b02c01081e1080109030703220f00c0d00b10b180074800c7d003094080c0300d0041e032664440815601c40d00188050000449150351140c505582a41e0311000c01d800c0400340b02c0030031400700480341580e44011340442d00301d0000400395103500c40c80d0b80756038008950008001c060802c0760b00150103030807160100c0400d01d9039081a50b056426484001000101008003148210f0040e620454109100384c283e81583c1e9031842e100d4148006580460041400001000b08043d800403081d0342c0200d280c00d00142c50b5040800c0108a1203081000d2003206e40221071000220b0100141c42c103168441610922541e0310701107a00040f50400c0c801c0c80c54218854414064914103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 527394379 1250 527393129 527393137
    0x70e070201060f1502010908030a060812030402010507021903080415120b031c1b050d020d090f050f010c052d0105010b03150d0503041e060305070804200306010f0509060105 76
    0x1080b124035811401d1001c48130f0394054416812065660380c2d0201000610500051807044002281c001010391418490300d0415541074040c010380d101c10020840180c1c2c0000661352144d40654002d8408114034030382650400391038000ad09064000300c0c5c0043c001c040c0a40f03822124505682c1c01450040003648070054072407194020b5450f80056815000d94101800c44030080e104a02e4004618178544210364007541102400303440682141016400d07041d010072100e140d841007441c00050342860318041c0c105032543c0e0b0107500d2040d0409602220260b104640d5140c070140c000c025a008800102551400f0740d40090208188105030a6420065941880b900e4100c0e098800b61610b103a4600103035208800b000000711f0340c801d1041c113107403010800070805480500060708a030901d180355023a007403114840e0341d40a403041509010070841c08079408503e041d0031603480f60f80050351400b58042e015013003039515445905440b90700c00000340c000c078070410507003200c038252030094090f200c040044a1500c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 527395629 1250 527394379 527394389
    0x1713060507031d0d021309020420190e0303030702060402030609011e0e030f0c010c090e060d030e011215030c0801151203030207020402030411040b0402162909070e07020106 76
    0x10000222042c3c02c44030600b4003400c00002c01c00c03000038039241d00084e001e075a00c0c4286144070396070b41c1c0d0a8003181070610522080511106d00b40100318050348070312170b46100340d62002070480a28181d403241d480c012001109941402000c1c0d03030301c030304d01071000966420080300d09138400e10070326002c143c6168043c4511105c00825949102c400712000078003802414801da403807001440100002e028208504024042810751030002191803c04044000c240014607041400101800400c0c00a00d903617041c50750112a906050a008003154100181c81070020b01007903100c15400d149000300101c0000c030100341920f00c9000110242600e9958480c03c940c4203c400450741026400240031090000700309c054481c0c031034540076203025815030100e401d0360025074003241c1c0e1b07082c0b00c1c282e82074501d4640600044048180c80460400e1a040700c04c050078028600090102d450008100c0301032100d641d03a560607001c0e44000c800c0c441c1810101182d5440c5640310b02410880d640c40444c44085c810700805c0103c41e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 527396879 1250 527395629 527395637
    0x90106150507020d050c0405091e1506010e041d0a020111010c2a21020d02150a09050715020a0b100e0402060c030d0c090f06180b03090a171306050703 66
    0xa4030b580c0c04e0000b10580400280c1d55845140e11207000f41d9904e005a034070950004025040707904c0e0307464240c48008580d040b40c60403078008444d0f040c14102d10800040d80000d003460001c40401030003000c90001c000459401d0100141c00480901c50417000a010002600c01c0e0381e07083c100b442c40d0408900301c40d0b03115401c40000344d9052441c01e1405180340040400c8040004800ca080650341d14460075070302e010854000e030003824501c1c0740400d4050103085601c24042c000350102000e172801003101300c4401446841c02950b1840301400307000302000880050003c5910700e101200c601500070b980c0c0e400c2d9000c107c58440d403100c00204403041c0c00c084142152002541c0040390f440729800c01c060344c3c20604108025110038801001d0705c0308580110a1813642d151114015103040051240202d41142c00c480c0501491b903c000614111407501d500440345440c109d2900ca4079018070243c101b45046502070905010f400180c01e030707c0d5040000f0701c0c02401a644514805990340c2040e281401254005800300d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 527398129 1250 527396879 527396887
    0x1150806090a0207020102100207051b01080915130b0406050109060510120507030f1b03050703200d0e033004050c01120b0a0e0f100308040b0c0c0d0b0901061505 71
    0x4410b60300038142c09441401650368155030410b410040740c1007180c040c1d0b0b0690118040d4038418848a001c112005000c0c03908202916100720229078400b02c907210395a90181682c0001c400000300740c448568031703500c0321340b001041c00c29080040140400380144914545003d20010305403a109203251402c4081e0340b1414030041c5400c2c0f20f240180002041b840905440d403151440a03140e40c0b0403201c2d80030040c80c200f00505980070000f0704541c0f0062114051500c0c0c5074944666407000d18030650cc03014000011030b0384a401e5044003018000519408085100206840011a80a05a05000c100390708282141303107072202d42840f80030700159030140481c1c00008070002d20703500c5410a56520a90717044007040001175038020481c030194541c451188014500103000c0c0c965400a034041e00070108512400c241c500759101c0e100f0b54803d510451924140000c0c483c90307500000d016200450000801c49403500c103142c01c15145030704e012144400c0075482d140020921490403c0011799070905541c9075414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 527399379 1250 527398129 527398141
    0x50123010f1d060408030304050606031605221104150f050306091f1509050a080c190e040c380c03040e090a050f0a0201020d030b0609180115080609 65
    0x10040382181040c48a039030760802d03529548400e0010b000619a4200540d920f00d0f26081ca1343c103100340a40f4080c8a40c100c1c1b41030100c1441c5d408444010b807002140c0c916000070300100c1c0458181c400c404403802260505041d00d985146103006003044820103d2038a61001030b81c60f0888a40c1015010300b4081141400419641e0800031750007a44980240d01007400c00c02c5840a50200c41c20992005c010008001c1072400070503880150580104010341b1940345d5076042c44009525501d001103124003c01120f9001c12444100e044e10000804007418403402c0f078101400d04110808441c000d07810900415082415042e0071100314500d800c542c8130451800f110b131103107104c440c2d9126104e10314081c44140000f1406070540112680604400030040c081c008040c0b900c50708001081c4018040c58000c1003100d00980d130041945411520a03240000d28081181c00141d001e00400c504035400c903100b140303007400500344070311410b0503950341540001d00c215002404030350042c01228984d0b000107000c408504 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 527400629 1250 527399379 527399387
    0x14030f030c0304080d090b1905040b0703050c041e05010311190302091909020d060819080901031d0109140f030f1303150b040b01050304080712020f070603050123010f 73
    0x908a48121304092070103203070205613001da51540800342c40b0600b40703106005410303070080800000080d6824091140c3c0c50705803108414800d000f00301d0403c0c96100ca0000e20011058800c48014100c5480e00d400150406905a0003810160182c240820301e0044491000c006000030b845444160000401034100b4940301200a90009050b498100007500051100d00707101ca0249805000301104c01a242d54080451906482031340e03000b11059002034140154034040400390780407843e08004000e0f41e440c0c0100040b0000c0156588941c17000c0b5110060181140703040d001155001d000d00d00c034011518140c90a652101c241406000f81503004025039400c02d41040301601224800116940a039681c0361140e01e180c090341d0a0300a02e82d03a903009071418524141c41420340e40e4100307107412404c41c034040d82c507090103105008ac05084000c43ca025055060300c2003000d458078549110a840c0084d9551501500ad0b01080c0101076081e10301a0600404071a41800c0300b00b4044140d64410803405102c03420341e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 527401879 1250 527400629 527400631
    0x40501080d0e030f190c0501091503021c05042a050105041a2a060a0b0901030605040f060213170a0206040e15031e190c14040e011814030f030c03 64
    0x690107000f840740c2c50100d0842417100c4114400c00e849451610112460f103e178400b505a0052030500c8840c2c0030034050400e170761060310304000c014100181d8411544090f0410240b072088072012890416080004024200e120a00fa440a80c00c0c0405030360782d05100302a40c00c0c0f0900640d40002c105100401c80f0500300c002c050303c800c3c5003240841c58107083e10710f20609151201c114246480c8804095031054108024803a840b0a00101c01c0040c00301030800149184018400603095a4440c0042002d000510300b002e0304c1507920000c11580c41062800034410111580314080c542001440c4001d01d4510102e000c10045078001d18241c40c03d4141070503513102c40009481d58044900300c4c50044039580b010043c8040c4101450701029011610841c42d51600311602881d1407446003044441d80021600348000e800c1c0e44440700f5026401c0c94140100c0e000705880d40352040d4641c2005042c10b40403011418100801c1c1c01441003980c1084221006652840f8126a42d2001c200410019503c0742c000c038055 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 527403129 1250 527401879 527401907
    0x1c060311040b0f0406080304080d0e030606100e132003011409070c0c030503180402070507060809190b01050f0904080a0c020d0f1a18030304060b0604030803071d040501080d 76
    0x34090851900202e01145d81541085005500002e402e2042010820501c4452001458400c43c60110040800d44460300501083c0c0590381403c20b418080b40901c5102c0802840500f46002031000c04001300d0143c2035009109000200d040404a80ca8003102c080740e050b18509072551903594504030070f0042002c8c00400c44c1c020130545513803080c00210310045c03180065000300015a22100c03586c0300d40c4040c3c1102d200701841544100811030010b103001c500c0101f100c0d05030034115400c2d640c0c541030a0500700494085160504c190ba0030100b002140d9844c2130594000342c0e0a59660f83c1c0308070600020b01c4003640c01521030304091010404152140c4840e06180e03102428000a01030f2030b03a0b450b00c400044d00b10880b6000004840300003480c01c2c180300389501a003c1c0110040d6078a01c0b00f003141d124403015002400640c0c0303c02410410340c640b01d045800440e448100c9546c2d902d026900148500d881003400c9880f10240717400b000c21403505002c0c09045c6c3e0b40700006084004c60307404c81500c441c5042c06030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 527404379 1250 527403129 527403139
    0xc0306030c1706060d1a0f07021c0f120e071211100c0f020d0f061407051c0b041d1b04060e0a0e010e07090c1106041110050403050a06021c060311040b 66
    0x4191410140311078264041d040042141255050111002e414601203400c02d0040a850009003010262f200082980c22262030814000070140240d02d03001418060344444c507280304161002803070f92100d00103d02a5402002e061109280341d90400107084007011290b000110a512000081081c04800383d001c14801851560a00380340ea0391a2408480404280d0700c082d80c4907283c10818824072412076104019107072a62034040400703c06141046400c100e41d10290741c0b00c18440c0207803036952060000f110900c2d401c429020802030196503034000c61003900c05126041100c1d0059007043d02400c0156000c50002c00d196a4400f16801d0040200301099034030356485026021140398180b1035407010b0b15140c81c000c180d9000200014000052840301020701d07501c0701c820840861142c401e410032a450495140103d44406d82045481d40141c1d00003820324054006030b4802c006943d8010a05618900b040e0106c1c1d0703501c543c82c1402c0314441d20019060170318514920b40030f8602070b488684400c00c0244 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 527405629 1250 527404379 527404403
    0x3080a090e180f121b0c03030c0607021b030a0305030403030216080a0207320d0812060f030a0201080c1b03040905010303021c09050d14010c0306030c1706060d 70
    0x30481e1003004103503001040350310184a4000301e0b0500b808040e2084a0354401048541d01034110800240314102e5552220040660001c050740010300c03080104d104010120f81d00c5180060500b40c68140036105140548900703510110350b510660040c403440d0000030003514402c0200d49041c2c656500081c0200d003007590800410b880710394421400d08040e805240a039488a10811000e80303403079696000740301052007074181e800c1c6829220448050480c0d01c124400145000040450400c0640c004010941ca901144a007200380403501074511812007200c8003200d0300042002d15403a0041104041d002945060008510b80325420080200340004141c1c0c014840c0000031140c00c50300103410804809455200400c01c0c540c1c10482004910381c01501c4130104915400003918080461190f540960510180b85061121183d029900d500d4150024044109240c6d40140101041d0204035030103291005c0c00f007401e80e14032a0380e402c00c4109400401041d2980010802828401c0d442110720100042c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 527406879 1250 527405629 527405639
    0x80c04120309033c06020714060f070c0f120e0d03020609060705030606030a0506010302070b0a090c0b041404020f040503030a020a11031b060a11011104030303050a020301050a03080a09 81
    0x5084041014000d9492000050552070f1220076100e616411102000d9800820b14005543c05011a14811655261510300700189040303800390051000180230104154583c030b06600c4041007082c0b00e4076100c081c40540d42e4404106440301c4541440c0644100b000c00313407200000302c2c0c91000c100340102e1401d003191501c0410f00001c4a80d80b000c07004400603005103040c000c040c4400c100854200384542001425842c3c941c3c0420308602004240300d81c0a03842d0808114164003035411100a03075081301d40d1542910300385c4e0304030028012801089440c480304102c0080c00703204201c1610240e0b1600f1082d060324030320441c00c01c40650402c8803e000d0042c001c010000d0240d800b080100f401500c143c01400c402c0b02c0300c0c2010144d88400b0385156001c0e4000b055480309060248442c25881d11040354000d8446000900450390684074811100d2598a000e4419001050070070152048230720a035010302081d9a036981d6130701a03000030700c503d1f42c0000b1421070510004803190080c1c014140d481ca400b44074030303940c1c1d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 527408129 1250 527406879 527406899
    0x1b0108100503060108030c06010b161205130902040329060d08040f06030605030d0c03020601150509090f060f04020421170d02180105072409051b0f03150403080c04 72
    0x170307444850301d40e03c00500c100c0c50410512000b0300428a243c07019040c003540c0750400c900d0003580c1d640284400c1c049850b1184c040d0060040c0d420709141c21010b070005940383d02c0410700950080c002034514900d000c480301351000341803220301610011462501859143c1c181801002c44000c8012506000c0500000c036001124501950081070710b9580403070894a400241802e00032031250510410103002e60f402c0c0403903000910340d41124070148164041c141700c2c00f011074a0f230040d1070b180740e4045a00e1040c48102038082d41312a0007400c003110b5001c8103000ca0002c100880c0303c1c0740300e080c00e443c98201c2d400241540c8403403243e001d18002d08051004026901d0410011b92104c0140310546502094000800b01400507807044080c00b0f00300145080c1c041d031100300f4480701c1d0402c002100d198007045444411a560400e046c80c0385c0c0002222040d60b40b0000c001500e0b021302603481d001da900c04820001519000074070b03440e98000c100310b550082e126038400f1038125100502c411082d074400c002c0040da82e442c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 527409379 1250 527408129 527408131
    0x1113020915090118060c0312230906011710090201270e01230d03030e07060201020d050a0b060304030302130e150111030f0904020c070504090804080601081b010810050306 75
    0x1500c2480c2d6840340740e400036100484a0304102c40103284444d09100940d040007680007020303010704018210380310480c07100d8085e0040d89500100e0800070980b035a02540d0109045005040c0001550707416070301e03180c0314506542151641d1040d81e10840400c0c00da000c10354841c04503d40189400c0007015100e030b034600307480034882060941c0c100301c40d60100251001711140c280549102c039000c2c150310000b1032020b19050612040c20b071080c54038403456003c05020b80d00c01903002c0d54182c243d5080943da000064002d422400014092500303040000c0d94020481c4240c1d0200c070002031000d401e644454904800940182084030340007420350f50003141880410744514401c0d04400e101003103541401000500d01c10051499074540c1d8000e20800c07916080f14070039211703882003d139001a220f404c0e0b65129850580c4540c0140e400a140288020900074040d0042c0140c844046c102d403210b90782c8107a92680c96103c1c041d05000d01c8050035500c0c10b2503129070b0f00700742c012860500d032900300c5403038030300082c2000c2c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 527410629 1250 527409379 527409409
    0x4090905030c071a09120a060608010e010b060405010921020603010b03070f090e01061b152909041e05010e06090d0e1c03020f0d0c060e0a11130209 65
    0x4000b14100c000d0701d41c02c00100010f40416101400d441c01119142d410500840400c2d80c403501d1031441588001c0c208121b40d4446a8220000340102c55036544100d00801403c1c01d103901c65402e180c0486407030304100040301c0031520b040e580c2d0f250780d500e41803e4010124840484000c01c141d005118009651044040c6010341031503100d00341d8030304110307001818105140318001b06101e06042d08010301449076603803604446550a046419003500300c15280003045012000f0b08401c40c0074a030108000302c0e580100040981c0750160800310005001c2045011032040640b6800415000010006600241502482800c0300e1540e03a21900c0c0c1e035289800c0d10500d6129200c640d102004101050600f0020381d044030300c2e107042c000c074244030f0880400d440803280210400112040445841010301c2080046240c000400c282c80c1c458030b92a50080503c0783e030003c207860050524890b844620030211f82d06c11900d0713001c2090030306084014280085000030040100d90164207000c1410309860300b8950a083c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 527411879 1250 527410629 527410633
    0x190b0319091b06110a06021e04030606060f02030421030e100f121119020304150206070207090e1009031124090604120e040b180912190e030304090905 66
    0x841d940e6005000c00c2c045034000da08103e681c2c207a10030150b40104010342c3d1550444009070751a0307225120500b40320040c031090611041c002400106003d00c3e030b448034050761841d50741e40c959023010400803a502d002d5401001380540b0510ba0000f04060781c2404034514920038103006444c1880e807070000b202c4001454603600815104208540c210b40d1002400350380715080c1e10100010480595a641a4060300012448844034184409201c5e4020030030b0713400620700e42d0349910f480d050003d8001c0d260181900d00380c0142c8980789020451030500c0c014020b059003560000c1200c3d6102c40100710113400c2a81042d03051040f05d084824507480c09110740041c1c0d0004416140f911b404140800da009880100001520b805c1241032000040301003c0e02c00f10881c82d468030f00200540f0344001802000c4112089500640d240034040d0280380d030184051050520106407420030491420210780352290601d0341c050345202c0504802442e018031101212040050100d0b030401e521490184200d6020a8041d6a55 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 527413129 1250 527411879 527411903
    0xd1205130b250f050a051b0616081e0402101809020403030e04050f0f0c040506120402120705030d0309050c0d05030909070201020901090905071e110c190b031909 71
    0x500411403801d06180c2c80e00803161400710784020540d008001700c0d002001000584240c102500d170154081c42e10102081d6015410b10000030103c140c2008111000b151403040080c0c42089289050061a00b40c00c821000b50b6603941e00700044400c6a41148003401910306034600d4100d64032070310101404160100690b85e606505000d42000c49072400c80f4402c0c0e0504041000c0803201390384d0940c204c01580f110240980303640d2402161405603030072464001001103050380c00c2d030b074500760128059030007a6803128149080340b22613512901c1d00d0180c40d0309503014041240e25644281d0220012600810503210101e14000009101984004017603c00e68004540c1140e02e150501c1001d82088450000f14a0088a000064113408071441042c1d00c09580354001a4402d00039840c40c8402e0404518400c0016011803028001e02502c0400042e1889041103400c40b0f410720000c40c04000c003d2144103206146010039080e05580000e003843c4201102080c007400d20042801750b1040244220001121 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 527414379 1250 527413129 527413171
    0x903020f0c060c07170717030406110607082d010b0712050421020103060e070306080106060e030307021011070305061504022503090b071110020d1205130b 68
    0x103841c112062042c49a84200312910420740006100003c442071880b844181d2926105007600f464201c1c0d10004940081000c181030b00300c4007000810035a05d543c0c5404e240311009005441d9607100807250380d030200b0403a002160300c02214481d040462091b400c8401c40c03040b10820790007550070003039210300c4418001040c41d404021a40700e901c1115281c601e803090030f051601e5400c039025030441079540c80c050484844d01c0156481b13500070308064014902c00c04414100ba1074010001c1c4160721880d1003651070003501103580b44c4610b00f040c00b485030040045080181540800c080c04103c0500c2c50188043c0c420070054040007480780e00b0040d07000d50b010b44042d14000c184132048040100c1028401d030302c1000b5115410200030b101041c21302240b01107030707000c0400789419543c18105801070780c0941c00104000040160503000003c0300e42094620300000d640d44102640da89032130030701c0007020444041089640c02003d41c012540408000341c440b01c0f20342c0342d0300c0b141801c00060341c07181580343d0a060824a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 527415629 1250 527414379 527414383
    0x316060516080106080403020109080f0304020a080319081005180a060f051c030e04050c0403110901050f0d11040906020702031603050d0e300d081b0c100903020f 71
    0xe88000d490380441c4440d5403003840101460b40502800062005003070214007414400d42c4880b4904d0b501c170504a50b40c1e0b030401070076041c503041210b04a126095441000c0350501e00070098408a200807400a110300c4807100b0145c0d40100001d00340c408525a01400042c180d560410410302c4402601c40900f10741030400b111010345041b608201c0080c042c03114104944c0c0c031006100c0e801c1c1440040742e5240880e60785030441d4844070074140103611506001c01d02c000070180b030f40204101d07486495410701c0d52201006100d50720100348507965005204c0590b102e03080c100268410000e40c0711700c103101514000b0340700040494509c3c039400d40e00b0541c0816807808604040080c400c4e00c100c0d164002da5100c0c9036a5459603203050140c00c11003048094180c41d206074a178040d0048528920342e907035030180318a486401840e41c0c4061108015882401254400c1c640a01c000d18014880144580c9160640b18030340d04590740804180300c542d2045070030002e80301c04184140e40100d48203902500241d006200502c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 527416879 1250 527415629 527415631
    0x3150a0b030106090b071a010b1306020606030d05130e010b03010302041812050a020c15030a0501060f020c100c0b51060f040b0c120f0a0804110303160605 68
    0x900e021030401c0180700a030b4104010004071864010210b6860380c40e454100002c800c0d0000c0890103168035000450800b84040c040d01c10748806c1d401d101c840a07510601266101030544040d23425400c80d805804803240f0840007000340d0410a809032840760340e240d0102060000036801240c0a003004001801149014003d8050540700d0344000e030402c3c10f41b40c86102a04241020810030300a000032640400390092201e200e90704402004503105c0e44401d40052006d07441203c0c00d080c9035203407a001042042c01204868540040341c0e00410b03103403908400744801d81800740103001c10311581520600000d80c05400302440b5580e2a24044940051180f040041160304c0100c05407507144110130040c00b000301c01c101300b0ba485010075078108c1c200801010900c140301d91550764412600000b4040349002000c40102030555481046400549508410005a014824500c80301080c100807410307160f4460300c0324940081c0110200c030529802c01c40002d207594004a070b460900c0b0713415404001848124030031a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 527418129 1250 527416879 527416889
    0x12141608220b1e040503100e0c0d0308090d02070b0d020d2c06010f0b120a020415090305060f040f0b06030f030a09061704050601030f0f0b010e04120906020316150203150a 75
    0x904e040608020000340c0381c50080c20541c00055592102035030030503003004400c1c4465006801c3c40c10b50301d100c0c00c004043c20b0088490390418491003000d030301c455200146502c100c8103014200c50400001c1ea4074100a94480c02c4406815920703552211400c44605201ca500d1500507403102c51000c243c200700300d083c078005a02c940800d072076400d0b04206031028001215800c1e003503a000000213669035503c20009000301d81100100094400c0311910142d04000f40b8030549028408484455660b900301c05002c0804450040605c1114001000000c2d403601c5419004140101a90100316609980c5440d41d0030443c170074000606040000c01c00103401422251f4201902c83c0841c40516280c2c503540d40c1d881042c800201075045000400041c003010340000c6000c903038007201c0d2520f2035940b040c060402e18026107083d100390f180081c50701e286074041d040440840719140c010b50b003080c01004e1224081e104059056424800c03030242c20030081007034801107108907250410946054020020b20007a5050390f041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 527419379 1250 527418129 527418187
    0x20322060f02150a020d1410030c090207050a0b060102152d1303050c1006080607030507020f0604022b050708010506030a0305040b03180a12141608220b 67
    0x440000183c05003d55801080007101683c2d6003000ca1043c0020256105080704070b400c501c044c815808036117026002264003d200388046181c03650300c18000ca2146440080169010808100025203c0746075160f001c0d1050060b900302041c1c410a50f036054104850301d50681a00340554400031048050440c05100d030031850345050f14002c1c15507600d80c0038803076014060200c0403500d0b680c0d8803020815006202c117800710501c079203955060007517910201921000040384c18000029401c40c40040e80003000d120a00041c907450320740b50248407404180c00700c403403450440b032880d25172040000e06403000020b100f1001806894680fa11443c2101e030081c0896219420000c0003e01080d071280940e01507450450390540e1780c4d01c506581490308885c03c00000f255000e06030f00403081c055500c28103c401e01081c0c881412240400d40f040c603d61250490f130400404c1c07002c01c08804604143d019086901c41c1c0c0c00041c6070319890018103070b24002c07aa80010066000010480d41c0e001181110943c3c0b4041303140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 527420629 1250 527419379 527419393
    0x20d0b100e030304030803040606050a0602073215040911070b06030f060f13200406050f1011030928050303190c020f040c0c170903060115020322060f02 67
    0x2001030b03120320131407001600050011011400307000c000d0340010f005150040c841980640d0310a4041c0d10303040d07148500000342004080c109117072035200c51001d0094031a419120420b420303000410422103c00ea00e1650a1030ac280700110745040c0511a0032200c126014003591241010301d4441040342d0000d00150294200e00200c02d503d801c0000d07980c0d0080c40c0d2220010701c0da940d40010f03502038012024081e040c5100c039901c61061a118401d007179218582903a051004548800c2488550b007800c2070700316003100c440030303c80c91000d10a0344025020312617641075a1800c0d203c0e00c00100050b88805270650484007130814000c0d242a01080f080040905401550408090001282d002854005150300b07000c1d403101000e0466554a606002101d00200100055090348800a0610741740d1002120b0001d03036100340c480c40a2008042d40c1403190010010b040384d030301b4840c901081409500a01065100c284050510300088030040c1c402e204188241026041c64040000c150514041c160015904046 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 527421879 1250 527420629 527420657
    0x40305070b1603050304050f060a05011d0405030a0c0602070807050c010207081b12031e030601020d0201140106051b01050c091003090f030f0908010e012a0e1909020d0b10 75
    0x5040031040580600300b04c0d0300d80e501c50501c0340c20007022140010a5000764410400b9a0040398411416a406140c000e000d07503050300420400d001040c5d030080c00d0795206000b013000c0c0c1441050242c075158419071000d810000a0381e00c040d40c0b600414021101c83e00954401c0c6081e51b07040003040002c1480b000100114440490301c0d100b031445103900540105c40c00b18080072030000030411030360b84100841100c1e581c00110040014640c005a440340c1c0140613031201b403c0158414002d5110017100f0780e041c03020a0f46040c0c8291015445000c4003622140c2810001101101c00c1c0700e01445429090481e85e61001488200000d920b03003c107007542414900726101002c510302004100c2000c1c2e040c10000240d411090003034903220582d0303228800719828a01494031260064001d148000020100c0010050300ca003203500b042030906095000194004480222a00d08072200c44c80c2c00e9600000d00348126180c0c01d1035130030b03039000241060320603488841c0400542010380301034810303020381c0c505040190880 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 527423129 1250 527421879 527421907
    0xb16060c09031a06040204030203060702011a010f080f06012a030f03050f0610120c0c0c060504082512052103071403180105040c0f08030310091e0204060302040305070b 74
    0x1100f040942403001000520f0584940e03040310040c640040894002d490510782c001e02800458004600b07490400c000ca58455010b100c07203440d1800c160700e50b2030a9546200c0c2207140100003c00e114100421181982c0501c000d040070200c59000e44401c7c00041b6800f130401401c480442e40c02d18041500d4142000480800c0001d026000003088882c0403901c0340c0c4c51000c81d25590074241c44881075140101da1040c080d000220404041d1040039001c8810342d0b0f070641521103009a00c06c1d9134040c0c010240c500e00b8045422941e040340070480061400d099110840c41c29148a007030012604d640c0407080c060180d60b0700c0e1514507551061010f44030700d0752500640c02405280340341180a040c2e00040041550a070a6134051920141b108000300518602414864000c088610820030001409000491001c80110450744a2a2810035001b825881c0085502c0100007049031f2408001c8501c00c650242a486d00050004017255903000d42c556040d4108130b410540d203940050180203040042d1800e10603c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 527424379 1250 527423129 527423153
    0xd0219030c02040f05010b09010e060903070e0403050705011407180b1905071e0b09061b0d1508030406030b0402031611030c06010602011b02060402090610090b16060c0903 75
    0x41440c00040c0e000451003c43c0240c0702a0412070300d181c1c00d1038000b040b0a00201c0140564002c241c2ea0464182110000d0001e0340c49540151501174020301820301c013242c032104040360060320074034140b03141030080e8440b1821100d07801c01c140c10081100c0d0500205070f40c004590000d840300c200e010200180b80610801e032511500315542002c01c8907401c3d43c0d0341c603030282c4161410f50341c01c560791140b8060001850210502c42c0241101c505c420300c3d01180c0c2c2c41d1000506140304014190f00d8292031441000000c1c896041074a202c56601e85a0320200f0541080c0a0442c0043c5003000045441300d043c030030090182d800030741110340a588103100b00b00151030100803100740c41c070003030510303003144e44040d083c2c14154450324101c1d41ca60300c984400000c6080c4d0540c012a1401c0310603020b0205c144a049040340c64034410b55010354803480e0440818503034944000c440d51240320908240c80c015564140b00c6000307030460303034031060284d170054001d0052200c00c0c0520070000689140503e0114203660b03807009180c05c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 527425629 1250 527424379 527424383
    0x9011e060f0306030f050f061803070209190f0506011407230a0818010e1002031e1b0a0c09060503100c02012702150a1b021903080307020d0219 63
    0x16880c40c607030707000c42d01a42c00301010b5504100c1d03000010b843c40c01c01139641e81100f4035038030591041c41c00182c083c20740800042c1c07400403102c02035854100c40382c00704a001c94010f0700d07170054501101400003c07664284a480e01803007d6080c04219450000000361000058800300900240d040240c100000ca04004007002c170b92140703100002d1144d070810403d140c400802801061050700181081d038218004c0c500050203582603854991070203d6a082c0003c00815807000c00142c0d10501c801e10140414003585840e500100160728240310201d200c4024444070a00080307425040608080103101e501036451000e00161001402078a1401e0080703655070f03510003944031855075035068201d01603100f9000701e6070304590829081c000300050400701d9060784521030101d2084580903103500c91000f0140540701c0703412054850304074000300c1c02202e20140c168020308070385c4903160369080240c050401d10b00001860081260b83d4481c03030800000391418072011b52980030355204c40e4805c4958040d1040c0b1a000796 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 527426879 1250 527425629 527425637
    0x3030a050c2d0c040b060d320a060f0b090105090f03070b0c011416080a020c03031008010b0d050712050a0203030f0a020706021b040c1829130909170307020304030209011e06 76
    0x1c84883c0c4100450b0ba002ca0006032509a641070440c0040c03c981c0c0b50050050849c20000e41340e9416405072003510610540d030a5200500c00c21701c41c0d40c040c001519062501900d80701415003a000001e003860002d8001c15100b407004144c1c80c04180342407084c0b44884403c450300d60a581042800740dc1100e841034900340400800c000041e950215030303015240000041b1b03003181d45031304041c0452450f03d8114003030010507601e40a5a0807032450600d800d2a240764016001d049010b08200102c014000c0c800c006446c1407144c41c1d01c00005071020002410780026004401d40c6941c1000c80003400c1c41d074198400003c551200003084000d100d60b01042911450032100015548021102602d4035000c001200403101018540021b54a20004c818081440d44031540c2451005030900080c2c40d0103280d00e5080c02c0b5500c51428032220b50740758800301d032490040295941c1d0008009090a0a900450b5900e0040c0c00200b410021070078201c200a005d0039403240307011690791044441b00c1c900002885100200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 527428129 1250 527426879 527426891
    0xf0e2d0c0609030a20011115070e0f1309110d1a060d0209040507050a0906141e060310180e032a0a081206030c03030a050c2d0c040b060d 60
    0x140c3c2d800c10680802c0317688051507a100c041d040b140c01408103000080700380802c140c444448424070002c82d441070341c03691901d8845d031240c4400a0865411450444107500704010402b01812950b94250341040d912500101113015099031812107078200b120001d060141202e40a94000201d42c80340140d411010400343c000c503552000005110f010a41801a4000310032500780030a00c400852041c0a480c0c05a6007040010f6488407035104030303031036803082c0460503118468045407844c21010912030680600c1c01100c51a48110008220341c0c801e40d280c1c0d480a0342000c08104403045607407000e000c5801100108081d81c041c54900e0f441348114185c0c00805501d10b00c1c0e50100020320705a180038000e03031104031100300e140d42c0f80c0748920758050740420800d544a000010500e140c0020b5410710014090003075810702201070020382e0389070003c1507541042d0041303028000e1b00d401d42c03070908007112260305122031204840c1456542050603a8800714010f82c100b002455258484904507140c000e22400c0002d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 527429379 1250 527428129 527428147
    0x80720160f0e161e050d05060a060c0f02060f1b0c010302070305030c07050f01110706050603060705071b1a04060305060d0c0b16060c05070201080106170a050a0f0e2d0c06 75
    0x340741309000505070a090302c0c0140344a1070f0301c4000740c0702d10052034404000c95240c0404110059000740304590000d0060311200c000603107840c1e5584180d500c06407075981001d0404410200799001924290301c80000b03a900700041c3c038010400310044000a003402c5183c070006031001051480000c051036642d50000811004006e000c01c920401c4600300002005408080c1100e12030940c0b204200703a4202e0b080c0000700f10580b07004113400d8066825a2030701ca04c2d2000a942d500c011043c81c14000c0e0442501010024514401c90360b002183d110259000d5900ca050070070150444101610440c01142e00f09220380006940724100b100340c442c0e0002550f101d90340106031100b0701014040080c00ba50429019007030705500080a8074240e8400d0304da00705030740c1e2540c900325078161046060b40c14012000300030440311a5a54000f43c0c0240c8002408a10031200614101c00e0702c41084010145034840114400d11000ea0306440038203002440c2d030b00e00c48900c481800e645d81e180004c0003074410400040d021003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 527430629 1250 527429379 527429387
    0x603151a0d0606051309060b070b06120d120507020f07030303022d0c0601170316020109030b13050c0609010e040b0109051e010e01030516080720160f0e16 68
    0x2401078001e03001c0c010700ba212800204607030400043d1400a0840840100300941140503100594603142d50f817a0078034100380c54030210a0b00162080740c000070b0b0700580070744030075041c052107050224648602c4d6401140300441c1c82100c000030300060440d0011444804840d001260a40807213030103180241c0c03107203d41c002c2c03214560705650300901c070441b16403070140011a1710400f07011040201001c0c1d4060b681e9800781c44148421302d005a542613002003164520b03184a80400084540c01850503400c0c2c02e881c0da40c0c80c1d6040c3d5007030f110946410410303499541001000c21800e002c51209031075240c1050001d0001034031450001080e2886541c8a80744c5440300d921801c000c200921000f402c003001d100c0e1000020000c4102c05c055240060125140d040c81c550080c0102d070300840d1518002031659103100c4048601b103070094115020000c90700b0304000074983c0c110000c40d00c441d1010290040d80e504444054207144241c0c0000e506030040c074010400e0180200509611400390b140850040f01003c100b11 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 527431879 1250 527430629 527430637
    0x2010816081b0c010f090218060108130809060a03020d0606020d0e0d11040216140111070602160813060e0a050306010b0309010603080406050c0607030b1507030215040501150603151a 80
    0x1003e03562070070001c0640780f00c5640241c9412802607400c01d48010b520074181c10609400c58019011030388000104000340e0445070070042c0c0d1405440003605120b1100002401d5520080c81a40040c0c1c011580c8a040745652056000400c540c1c00240f44645074010080c180d6040e4041d9140f007a1101450f00f424000d68040240c00700c40004e204541c0c810b45440d0040810600e00d01c20f540c40d0901e040751406481c014441d41186c254400c0320f482c1491050355902020b544241c4011102103034802106c40000c08001c080c0c01100c1104541c6002d03142000d40040544500303a55007841100035802c10043c5840126203d419034005c0c0e140c0565940d0f407595400c1c0544240d0340020090000060005585030b0310030042d100c9090504182e440c0b070f84620f0302c101d0549003485003156020520245052444120500402140d80300e4015507890100450303c0c0490100b0403201695540d440310110100d0318111080d48001d030100e41020000e10395000e4020003008103a004481020550601c600d22099441c0141c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 527433129 1250 527431879 527431897
    0x903030b041103091b0a090b0d061109030115380706090b09030337050c03090114130605040830060f010816030e0a03030902010816081b 60
    0x340b116007540a012101580200d6000c8082e002e0072140c141c00c00e101400d00607000400a0122200c28140b041c1d840060000d0b1a01d83d41c000b0142208400140580c06a040704450000b9115200c00182c403d0500f51119123030300c072501505c550340910402d03c06200d000320210707001802d0071580d1f20190701c8404a0701004070030755001c040461140100134890b00102d108078854180300e074054545002c41966800305503904003142c0101150942555140940300001b5034010038010840000843d40c1011210309507041511020000204103c0c24824001c1c00c400b150400c076801c49602d880d04440c0500c20b00101c00504054495002c1400c2c40f214505864540d82904507044201455042030081010000d144481d0603502c03000041161078040301d4040000d006860301242580c0d0002007500c0e001b0701210000c02e050fa5801d210342c51000c1005030a41c1c0600c2500c0014503802940009060204010503c82c81e094035940d4140111f580003100e15040000700082200401342d030564041e01d4010241c4c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 527434379 1250 527433129 527433131
    0xf031005060d091203091515050a0611190b130201090e0708151906080a0e030a02070608060f060406030b012a030809010903021207050102040b0d1a03010501050f01030903030b04 78
    0x142402202e50702a5425921070000c03030002d850280400d4040d101d0f24040a020014414140c50311031505400110b09060f06140c1414400d4484000036004682c50300203500094540c00502d01c0703000104400c100407012081d4a605918950b95168006040140041c00c1c407030101800b5801c59000f003490700701500c004a500c440c2072034030020081030314108482074981103070303c501c951000d8200981504000501170100520107420600700366810000509900071041c0c3e91200b11410210500142007007021a502400046241403001400d00002a00080c4200240c81c1c10005603a1020100ea007200e1140c00c0200c0d100c00e5010061714001c4403684481c40d01201002144140c05d0705802003841d240c0300f525108540d40b103040c4060f007241c0a42c0401400769101e03075400d10715030030b1031009002810300c940000740c502601c50648240b0303030704000c540e40001030b02c3d200d8051000d84031040b0441554019002001158901000114280c04114a442c18148e4030b4541a0525210350042d07a284100580 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 527435629 1250 527434379 527434387
    0x12010204260c010c03020c040e12030a050118060506041208070b150102070b12011e0b04140f030a020d02190321030b03030304050606060d02070b0f060a09060b0f03100506 75
    0x1401c101560540d5003400c45002d0541206550b602482d4032598042d0554028001030390039400f8031004140300691214035106644018070102d1f41440112f1044d0320b10038012600303500d0510304044090304409000c1c6030300e042030301c14000e40d121541503404450f030f040c3e140703401c0c0c124604111481d489040700c0501002400400c10410100c50409187c0440080c2d00300c580b07175980c600d00d51849008015501c0c001241220041182d174061a4150801008003180c21900680c0c84a441149512540c81040f842294a0103694a4603100050503500d4034182d000d000c0f003448039030000c0c0303c0c8114944000c1c414402c2c58a0220f04246003180d800181d0b9110000d45040c10385034541086e04c080380700c1c1c100d0000381088019045400d012003507034040d40c0d115004000130b0301e0310410003e941d0404c0b90f611580035424460351012030101ca0486009005100000003c0d04080c8240580450030f5001440140c2c1803920802c00ca070b401d5000c5840600c0481e000759202d445044442c12003030925880240c1c07058000c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 527436879 1250 527435629 527435669
    0x8030d06060206090a08040b070503091003050609180a060c1806080f010906050603071b02040f090b0703061d040510050708070e040b060301090b2b0b09190212010204 73
    0xe800541550080d4080b0342141d500c1803103a41e91420b801c03600425145081c841000710200f03060241201500c14000d0302e040801000c0412800c0c1c0d800968076000a449405000d0541060751446030050216000c00b840982440b22090f42c0c1e1a0720a0024002a950130f40340ca14144a1072030500c810050041e4514016995000206845030540d007417040f0006c00d90001408001e0b030701c64102200c1016082d2402d5594500701544c1c000d01c200311100701580e8900301540140e4030740c0300302d140b1014021070000b055690340c104129a03450040003401494038040061000f659070768000c01e04946540c075803641c2690b5914107141000e09440c0800111402d2100703010840f9000001d01d8441c03856a0349040f40e1207050001c0205850364000840e8014400304010701954000d60443c00e01c4040140001035040800300c1c3c00c6c8041480020201a403651862203001041440f00125030840600c5005010806030100c840458210b1908020311030018001865064030b020f40507503005007848d85292000301811 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 527438129 1250 527436879 527436881
    0x180715020601080d020d12020405090a06060e090f011401090e07020102030f0703020403030f08040812070207140f0306010b0a09180605040c030203070206071812062304050a06020f0408030d 83
    0x1010512016018a200101c0d2180340020064503050b40c41e0300401025010550a4a8042a03451000e80c40d9408000100c2d05850b0610068091121400001152860032400800350094074140034403495480c014851030f0104800d003241946d00f1042003141c14070080c070040c0c4140e801070740122140481041040162901036010318410b41030b01000344e0507551a2101182288124040100452500c4419180c2e1a2140000d950302510540c010752a040e803070965255510000c680c07890042e07200980511035202c1c15902d0301d09050083d51b00e030955041160000361100014010040811004200346c80d26920407a00c8000030110703e0504910b9101d4041190042c040d00e00400d0302583c100952078402c3c0e403092003140d1082050794054a815101d8480449410700d5440882120441c0304601044c521040140700e07000501c500000141d2282035000b540310f160240343e940340450001030410020500100344164000d80c014401a9988800c5010705c0c560b000365004088580300206400f0001030b19 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 527439379 1250 527438129 527438159
    0xf0b0604140f0105090601140a050a030e0a11010f030b03030306060d0908280809100c1e09050a1d070c0c0e010e0f0108010c090302150f1c20030f1807 66
    0x58905c1500c6503600ea00656410403654189a01e0031020400c2258441c854005040000c0362450045050070b9540300207441e00114000c00c2d5080801041c002c401c030342e0480d00100019a4134201130040800c84800070741ca90200230846d90280380c0c00503c8c1c4885d41603036442925030991108280e83ca41115140183c0410b26585c04010380400029001c9081ca0051001510a200c07100007020f04800480d6250041c150000302c241c00c1c499410051544008604016044183c0c10303680e0803800d074130b0501048034000c0c0540c40000c40107841c0794a640340d50000246164040001e00b00500452420301d41603002000a50054072144c80c902c0010510701c1426580074000e024000d0082505d980390701200b070880740c0302c03071080000c11440c02c020001401d08403c461071003600020002d04000000d400c140c103a03442a8442c5403120121102012107072a14401c0c030380c40d120700c010300b100074600c0c03640040f04510000c0c00b0100002c4800001455007a240e0381c000a80726401401e4651069881540c0e024806d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 527440629 1250 527439379 527439389
    0x1f030501090203040f1101090302061b100c020c01080705160c0509060f2b0b010605090112050103030503070c0f05070e16031104030305130806100e090a0f0b0604140f01 74
    0x4204400064920198000d90340115008410702c03242c01a144e0702d4003104070340b4000c00c17410321180c000300001684d80d220242980c2c0c403864210034070002c00d984009003001c2500300141951842c219810907a1607000814840402003030070001c0039074440c4a0152182d0103000707051001c1000064501c3c08002420b8245011210103550b0030070329407151020002101e8a0300e5003a0b8002424414070420b0828000d104032110407058601103e600c103e88406000500036080704010800010b980c03041c40d42d01094824070348921302020030555046580c011300911014103204100190302e003010050040410721410020b03400000c80f18441d9940b003200010030740c12220118810002c40b0302d41c4c4518080d0013034680c0100e10381151841d003411a82c0959654100c451210a0b50304175020204078000c0030041381e17000d14840b103070f500913003440d0501d50781421000920380c00c001d400805030354000403480102d40340c2e0b5903400040d00b0303840d5071020b0116008003031821000c1c1a03c040b820611a00d180c005500d80e040e14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 527441879 1250 527440629 527440631
    0x903030911041e201201050109050a0b0f03040611030f01140d0201213207110d03090302010b0315010f06050306092a0a021605031c110c1f03 62
    0x1242070822048034080c0e0a00c0c100c840da50031a00b50a02101c0d405845851003079a10701114804031050b0074055044400900700c0003d50400502556811039041c50040c60f00301c503034000302414491440c14900601890924280e030100c085010890b0307a40107400030b2141d03020070980300d1505840c0c00c00e42490031700c11421160b130f0520103082e10742400c8522a0403190180c4451640080340f40c1501500341025140b02c1740c45669564004026103c10300300004203080101c108124030649a51003101403001d04a2428008841603540b0312041c041383c40b01242035242070008159903a400c06070301400340b1040983c0c0c0340c00b40c0c03003421103d07400b41019141600c04018984c20115280c0106845d28170043c0c60340d81d8418140800112700204600308202c1b1180088000805440d140109038402d40090032650302513001418a00e90f5249005003210080070308a006041e8140c0014491004104150000e420001050340d100301d010f03010070190103101c00c05003910108180d1580b8074204012800401e800203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 527443129 1250 527441879 527441903
    0x703110c1201290a0b031f170105070e100503060406090c0201021b01111617030f09010c182903040c0611010b0a05060a23031005240906070609030309 66
    0x18150f0f00c1c107076001648081c00c1208114144032143c00d09420003030002c0c41594446942104c0b2021969212004186103c10392034a10241e940050a4440041c0f60b03608100000b40c01c00b030150b850030480d46c01c0036280c0c01e080c1d94a4617541c0108000e0185078101912450404061000d110f034150700400b00600840242d0901401c0000d40c1d81c00e0700c100310000d030b08114040c0503008058603040131085c000d0744250105c000750100c0b4107011821b6042100c122902070325103010407880c004203000300031050381240707008003039a402c0009404890515003d5610000f160380c064118409401c0304034200002c9140419481c1e103071a00d0040e140401c5802000c0005042e540b07071f03044102050141c030781e0031a070080c84804001e06190501c140f0340c002c0c42446040084c40b24000309016522004085200d603ca03141540d00d20300a0f4140300006201d0340300d540181c2c810350344407851403d415203440c4840c0d150031619594101240020700e0a01990350050319851900d4201001c040d090707484031040d184034141ca5444 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 527444379 1250 527443129 527443181
    0x1d01051503100e03040608071110050105120a03020d0503060109090516270909020f210f030c060604051b0d150f0506092b0f0c0e07050703110c1201 65
    0xe035083c400500c1c40d264003c0c0001e00c08140114140746e885000e41c6003048c460b400461841c4e02c0d00c0c2c855221400c2e0035540348014800b40c242240c14440001c83c800043c22425a01d590096855914512100c1044404808543d180e8400da04010040c00c03250810300030780c02e10b0103100300145003000c2c02501003241900c182c07400f0400224940d00c01240700031481030140c0b401c02d504019150300002240c0c0603c6c100c2d12080e040c2c0d560303c40c40d100e0003c0c034810075400300414403040d858103d810300c6035040c9070300078040350507e010000359a6920810550340420a030303c510301c0880701b42200ca00c1140000d03c011130b508060312002d43c8418008204d4604021240e9503400391410300f1025401450b4210204202002043c1011039100700c01081e401642c40c80c5104400786080500d01480c011160928490002010b0000c403a52031800742c45181340300400b84c2030420019105110764040101072021707500082868201c24005202c0d50040608440c0e0f98070070003d4901d00800018080c64900c0b0640040800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 527445629 1250 527444379 527444381
    0x315070206010b03100e0702060405010c0905240906040305100c0903021c051f0c08060a06270302030d0801080f0d02030318030903030d060e0703110307031d0105150310 74
    0x4052901500a080583d0a021211807698402044459031400488000031480c241e4680d00f40302c2c40d61031340074021031308151030100e0a40c2d1900c2c21080408c1507842c001d1002c1d03a200001c0000c015202c1c1c80b8a8981e01d0003101c0700c0c07001d0291404180d030142004c02c000040c05000708040a2000000c00d01300200312201e2010794aa280310700011307401c140041400802007101509150000e4000d00494007403404002d902c07041c850380148035a142c151154440030320f40d90055403503504144211180704406041480c014a26a041c5900f6000c2c1d141000401c00d13040d070702e2615400915006019a205c00e5280600940701c2c100a108064441c80703100c1490680c80e03804030b404038141e007883c1d01035880c0d9119035103402c54481d00100340307007514041000703104a00c1d9001c000610b503001001602084451900000b003038907100c014180000e041c2441c0020741480600012070b6801225410000354952000d01e00320703500c801d90401c0d6a460340c40c00c010f101410440b4000c8461140b000c070304540c150790080c81544 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 527446879 1250 527445629 527445631
    0xa08150f270307021203191e0e1c030527010e09071103030103060614010801060e06030403141201090b0609010903020f180103030e01020d0302090607151e0b0315 71
    0x29415501c0845400c04211001d0103140500d8081c1240e0070700005400040341501c4650f48540c15078000284060301e140d0081109000404908091458078a58551203030641d045142a01c204000c40020701c043e55552244c80421405000d501ba0382541702d46400750499029000390103e0164400b410070a00c0c84042009400c840183e480c01c000084c06c40030f21401a07405021842031006e03e10301c1c020300010820185001318042c0c8400310740c940c9420076020a03101400980c2d41004130b00f00043c0310b001e0b08480105040042920100c0d0390369500e0800301d441d0300d00d0000f01640a44001840480350102c524010305a034000101000540b4900301000103e00c921560701d404602043c2e4100054034000740f80350845140902401c241d8500d141e003d0b20400c030240c0040b400f10b64514540e03001035904009d40f07080880740781030440c988241c0c00d000400f90f0286c00303001000c10103030500c20118040c00b074000541c802c0200d200c4603403040e0076400c050044d03d40f08418a000e80700d200070508403042c20a01e15 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 527448129 1250 527446879 527446891
    0x20702010212091804060605100c0219150f020118050c01020f0c0a03020f1f0513080a020d15240614070b0601050c010e0706080403080a051b180a08150f 67
    0x40354601180b80c1302407a403010014010313629542d03910740009007500d441c0010345004c113495965414040c0780d44104008040036901044881c0e00d402014045850741404541c0b0034100381c03d092180f030000c150b0407800741648242820240c8005c1c0400341c01c11400040e400340c400401d800fa50075660b0001c2c28a6581c0e60780c50030196001406050030009424590364201000c800036004a0444004940348403158030055980e030006000010a2116040011039a601901000c1c01404580c00f00f5000030b0411004120064408116403900c3c201c0c81c491079004104200c1050700480c513400f0031100c10b070f036030348118490310001c150800608240040210100e601030f0f503000060035010344408004481c650081c01401990790342c6d44403d1980c456003000220024a01039132101020328081c5001091040080d100c3d021040c1808240662401d281c00704c55191122440040e8560b500e4200e4031012912076039509030028494800404d00c0c15010500300c4044000e01c07241410b5803564598160fa00c01d0450701c0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 527449379 1250 527448129 527448139
    0x3290f0601080c0a1806110d0504181805160602010c02031c020703020a060207050606010306090b09070e03030d02040807090e151b040b030709061101060e01030b04020a0b0c0102070201021209 84
    0xf030b12092480064102d003100c91510300c00c1640354095000361046560800e502040c00b5003003c081e200310070058015001c41070b117429400c01f447d14182400303184004c85801466600c81c800344040c945050080301b0013981200803100c5c240c10b080217003002c031681401100010b5080000100c14140000103c0e00c0c0d181510307041c00f502d4031040724020002d42203984110114043c03401c1c035101283d51030003d042c41501940103801c581c02d040c0c001400b00c07034017030380010302c4c00e81001c0a407000c913a9042e020907880720a80c105501c0704001240068118412401c80c149068070114000c101448009206416075061071020004c103090b80354502c2c0d030b8804400d6a201103400c940c0004400340d41040d0700d6008117144103070040c2002e8407500d0300074030764104448400c001000c01d00204580b980c0680034440040740c0500070001c4e03078104a20320800f00790500009d400070b05a000890115110000c81000404212569a88a042c03c8484501075072010703600b030f80180300b07082800500c40c0c20301c01250708090300203103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 527450629 1250 527449379 527449381
    0x16090816150e0303180a050d200109090e0a020415032607020409060203100b131a0708031602160b120a0f0507030204180605030c091003290f060108 65
    0x8000881541034045240801c22044402d60964a0810250000000c0040b0701d000d0180f908040c4403014141d0742c00148501d481c806444041031b40200c2c07000c8408024044140d0008030000103803010080d560201c03540c42c0c0b0b803407250303401c030b46001c1095a40c03984226130a2005401c51300c14400460f030b0340d0001420351020310107000c40c91079102c159201204406060241081821340025048407001d045c1990121303000000c00205101c5002404050001115002d04001109138440710038071a40c002c59044210f00301080b105c6c0b00f20007041e210b006601000060713a034540701008031005e03c0301840306009440f030150540c03e0042690b84070310646424610a41c1400c0c400c8886240c60301d000b40c11119501d60340d408109000c2c0e8540502c911a0310b03142ca0160f541c61904506050844d032404520360b01620308003050007507030380208004c00c0191048913002081c1d110200303d95981c80c455400100910003800749940311100b441d20300526007043d070500d0205a510359403500303100e01085030218005240d0307030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 527451879 1250 527450629 527450639
    0x15110708062809173601050d06090e011e110d0b062217030708030f1e0a050f0702031305010f021609050901060f080a0209060402070b16090816 63
    0x40d5000802c110301e490200d010319050720741c1e418490f50299210044c920001d803207909104802001010a94010248103078820b60341c00c1405020341004049041060028070f40c10420802d80240c809010300c1c200801a8103800c03030046008059604e400d04040114242254000c40b040c460040c03c0c42c80404200d2620305008060b000400c82c41c20001c0e0301c0f04040c89080c200e90018040b80702c0f00b4880c2d5000c4480141002d100d040d504c00f000b90300c032090380e0040040174001103c05040d690042c0448410340840e8a03007401c050340e5100b0080140810094903000c00100b90001e0b000640900c041c04080541501d840d54102d03201d11401001241801510500b003141c0d503c16940e403564800d0310300c15180c014000d8903ca900409065020385861900da40c03d00c003c4c0304007072013040c000344004031a494220340361100381030710b4012429001e4800e910040004117a511203404039242c031381d40409400041d250003601103c2046c03071510000c00080304075001041001001076011041c103c2500210303281403070a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 527453129 1250 527451879 527451931
    0x170c0907050a0e040f061203090918050703080a02120f030a05060405040f120509060a0810080102030403120c0504050405010e040b0901051b0c0312040b04030807090501050406030c02071511070806 86
    0x1e0000301e21702c103655000c0002c0c180b0f480440c6050710351190b66040c40a6141100c110241d4010f40d0403110b6400c1c01c1c2ca844c00006100203401c0b4200c039440001940c0790000900b0903030410402c003d250071920000100421141e01050046104508201040041e5100e800c1030008032002250010a81c011843c1e80d4404620505810f8141c0003d5141035403a084882012440640062814001040e6030005004620b40303c01c6010028049100007141180340644005040d4802c084150305103d40d40d5900107665880b6502b21070180c100139005001c1960342e40001906041c2c103c41c1a01d1511003180440c4d006001800360134000c02c0e2442000c03052081c1c6207a6100194803a2400c10503900c82041420840711402c424184114040c0d543c0c1c40c07840c6002c1c10301030800c00000b050542080006401805160b8000c002e44c1c003036411501d00024902c0d903000060745001800d82040e0389034000b00c014480c0c1e0f1907101030f125071a140041c080e0754045035181c1509582e44001d4501100d0444400b000380504405c07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 527454379 1250 527453129 527453141
    0x2010e060d090c090e1b0f010f0504031209081e0705060a0512010b07120315060e030a0b090304090f1808030619030302061608090c0613170c0907050a0e04 68
    0x81c5000039402aa940d54604541120303032003681c400d512200c005c0c507510424010b910029200c004149001160701c1d000030b101318108400316050044120030348984d80d02ca20140d40141d5800900e4564105011070098800d6696100c0c1050314450480d80003034400001e501a880c4800b05d00080400500b442d0130489181c0201e0715103402c0007002e20201240030010483c80d4020423000c3c10300e6654030303030504056003400c443d07143c01c40900d8100200a8250120601c40c10101d65242c070b4040201c40d0308030000b80c1000104e07100500501c81407014896482d0000c0010809c50710085c1c820407288240c081c84c007007503c0440e4072940500d00300c2801113001c1802c200095a100b00018907441c3c10010600030303a40c0e40304c2950400c0d40107a03c01d204011840384a0604060b0180c40d908000059103004180c0b40e9581803103c0405020304008145122101104020000a000302c515240f40e282c500000c3c0c1c07685c8008044101c0c2c071417070003c0080b401650045048916011165441080b11200c80c4248009061 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 527455629 1250 527454379 527454397
    0x30c090a0f02070804150f0507113001050708010503010e0303061903020901030501020406031401080604120e100e030615100e060706020a03140109020c1911060f030103051902010e06 80
    0x307001c100300b034005013103500240081d001d043c50f01d04d1003059140c401040b1081c0c0c1a84641440f00400c00100859916455041d055000b250309203142c00501c0c1079003035a1040f03405110043c43c0d9540752000c01c60b8042d00040e10034000f6540d050341300d81c0d840c81058280d032034007400005160010004100642403000c0d10a01d000e81604152018070b6030780c0d0114121101c00d0b4030170b80311654041820b0091039414000d117400d052140c05950010350400000c19120b00000d0310042401c0034290004c244a8020a0b4048610500408075041c1c24410319000d029100040032481c407900031400003520210003881022500740d006008030340c44481080c1b0a48441c511001c90b02d501c080c040c000440040c0b0781d400140031a031441d075004509108800c18140004406030003002066005100e19a12100c000030090112020640440d145103120304001080c200c400e01c032503400020000d649052603020702c000f941200d2041d021a1203001403880400c981c0980204002d00044003008508080d08d0b10401402401d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 527456879 1250 527455629 527455631
    0xa0c05040603150510020313290a0e030106060f03050903070b0f100f06030e0d020703030e040b1c0803040311010606210b0306010303120c0c020607081317010515030c090a0f 76
    0x11351030314001130325900301c512580011783c000100101d101c0d80404e0f00000038a50002044001142e140910302598030104003000c41c1c00c0c0120741e54000314803881c040180c0030005002007041640341c04009000d03107030001104003c2030400d00458101c050010498905a41103204003d40c3c0d101e0100c903c2c4526406040e941c4503003202403010032000b8000c03000000070310060720001030410f80380c2422401d242d000002c4c2c00540d0821039040010070b4200602c400840000c0b200010008603020003c0c51404000ca070000c00039802c42d03040002c1040c50402107010b14000d1304c54800100b03150b03d00301d00740e58007030180500203015a800d82d540d02d800b0103060101d15104000c00328141d40e050010a11b800070136801500020540030171411308003040e210354800c051451820450040c0707642c01040c0980305003000104054000a41e2213481e040708201e44000d86082c150b4080d60490000015000e40000c0d510300000d4040803103000141c0c0340008286219142c040c022401940d150b0a49000074a60020703020651 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 527458129 1250 527456879 527456921
    0xc060906050a0b12030724020a02160506120a1d0a0b06012d051305030a0516090606080103021005070516050907050301030201020615190303110c0613030b070201020d020d020702090a0c05040603 85
    0x91f528900103802c030171042da802064072104082c02503000060740da00081c080c03001000100710880d0310090059001c42c007a0404102610085071114040f12900e182c1c03801d5005200801d02045503894070240961003d81e606041c1c03030b849003a250800209020410802111003100c48540d07402034002d03200011403040201120395a031000310741040c40b482c41c210759541020740003081600d0402d42d00c00140068503170800c40c05040580c003902e038003818000070f48544445500c0c8a00c140c40750084401c2e043c1e1060944806a0b03a590303100702c8020850051921540c2e00000040f01e01d031003002034134100da030142c4c006c14141d01c40380c8807038010011607101c20750414030740c030384d46a1080100c0451070300840c800c1c3d803401e90500940540a06000845e00468840c0c4030400c50000b4610320f04d021031050b660070032048056511000020381c02482065041111940045181420b03407a0360750107010014000d40c1d1000c80b9558804012040328a04c240010110344180014020a84258444401d01c07190480d10042 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 527459379 1250 527458129 527458193
    0x21f050621060612010203070918020c0d091701230411120c0310061202011214180c010305010e01150228050f030306010c0b070c060906050a0b120307 66
    0x403641e80360034002580c2c2c0c0928284038603070601d0340d03070b03480071042200086066082c9520f00610a00d82485400007044520078083e41640c210750403200c04059030005c840c9035803608a00036280c42024441d07424004096200402110818095001c0d1151600c0700800c5002ca040c10b13015503801d01034800d88070b04641803d0000d05440348001004c80d1b141400090101d401c0f911704040c50900c02d00a010605414000208041866007484184035682404d0000007aa100c4e04004001c0180041041340d400c2a20280100381041c002e1f01d49401054100b038402001046005400341d481c288921045503c2c11001048400084180401061100d205945a03400b150368240a0802c503020311f910f045401004103070400004100302120100b00b200076508614000d030001e40701038031900000d48450114800a120903200c0e001050748107a1258080084011909240b402404100c400640c0340b0714054804d046882c02c1c1000c5200d000e030100040d8540301441c0c1c0c030311112404000c10510b0f180c05940c54014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 527460629 1250 527459379 527459419
    0x6020309101e2a020d0210050c1204090c1106010b0c010603050102040e09010c09140d0f0218040507090605150915030103120f08061305090304050d03020715021f0506 73
    0x181420780c41e9101d070040945459030f070082c251442c0c800e0150051251850006848031038810409070340440e0030104030415100309840c50702ca10708501c1c0f0540540040d4a2120915501600c1500c9080c141080078036002c81094403420a04080060981d101d03d004008002e5400b00600c103600c010000414000e60300d40e585805d9030041e4000c00c0748000c009041150482c824880c240c00c0c0b40b8140f510f900002d14042090295901d20801b440c02503020f029000b003881100810240074a601800001c6021071500415081490540c0c0850742d0740502200007940350b10300d01508068410007080000302c000d6100503c440d65124412036078005d400240d810240c00c60b094043c5000f18080e044240344c2c11282c41000304010700060a10083c800c0e45030900074036031100c04c0c1c0284040500e405c009200e8988a620b9403950045078407680d80107a59081c0d17042016800f280350720407201c00381c048090384d40c14440c061341c640b0848000400c1c034000364a0384141c90741c800d8005a070001c00180080c0e24840341400307008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 527461879 1250 527460629 527460677
    0x3054e0c010c0e040b010806180603070b0703110c1e091b04061106061e09090109050f070f0e090d0815180411122e0c030603020108090102040602030910 67
    0x740110b400880d10900c0c0b03090501038910031401c2442c18150314a4007174002070302044004075952701c4100700c0c1d0028075581c5081040304c010f440080c004585031002890003d00d54501071115024a02581d00b41d0300701410300350050602c940d10010301c501200058014400c088000501503002e2050644d0500c3da030041c841c000b40003800507582c6909100022940e00c42ca414000303040180902c0c1000380c041501e6000314010a10000c0031281c0c0309042d241c086449000d8280b200b130107440383c0540d064245074030000180304021038022048104d20b0710b03038490014007240c10455a0119503000324080303141d041c1c8281c902e40e034000c0c02c184060040b0809031001ca040c44030f40c985003518400c095000e10041c80464424807085480c11210743c5034002c18101616112035101000c80a602c0e01c9070403400d0303171a2403d0b100c51800c1c1c0040d8020000c101d5009401406050035100c2640400c41c507101240044006000300c4069400301c0d0011340c81c02c1402405e00595242080d1001c040004800c01d090030281c11356016 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 527463129 1250 527461879 527461901
    0x90b010303090f0b0f03190209030111130807030209060d0f0c0b0a080a021612030612051c0203070f1106040302060307020d0816090e0703110403054e0c01 68
    0x1c0c081c1ca0829a040300081119040144c01c400280200512542c5140849034007102d03100d116401d00046801c410b029000b6210308a5043d42854543c02d04d003d9a10060828248514012032009640d40d1440e45c90301d85a02000c0d401445000020380d107030401c11f081e005441c1c0b09004951031246a0f440700c04072650207401c2019003c06c0000e444110b5070740101500d4000089040842c0b50a4a1300a40410b200c2c4114004000079904e040c4a1021402544540003e100c0e100880001d615140342150b00c4012000d80384180800140741d607080c680c800403e5541c0954840100b405100340340c1c58003401d040c0360a01456006d10300b0000440142c9a40005d58052001d540081600501c2404090891440201080b5562a1400340c2c00e503e198002c0c0d0903011101c000203d1055030301d83c090210040c1112921038010a180080c000080180004414001c40e80e2034460300e0450b610031841e5420784010040c000440b0012545030340c0c88051041102c07040e40703501d40c0240c3c070780760041c0e4407142907800520302 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 527464379 1250 527463129 527463137
    0x607050607020105150d02040509010e07090204051c0c12060603170910080709030605060402090a300b010e06120d020c13060b03270604060f14010807090906090b010303 74
    0x9018403035409000d01d541001c002c000841c0305c8007038903000c2816030407040b01c0a4456920340000c18003c82d001c0d8041509082c040051700e1139aa01e0355400030280d40079104460060485122a0301252841c4a42503400c59001c16191025860102140d0030000200e00903074a05941d0030340000000c02d50104000924003800400e034841198000300072a000031100f190090041d001704110505520900c150103403603000000068640710704002c14024010000807540044002c1d00120307455800d422030305103246101c079051603d10140409011810a5800001d000741154401400010305600c001e5600c103001800c03580101c04207410b40d42c503050703214000601580180401c16207500b03100500c0716000050180c1800180d02c2c4c803000e29000d200080026440c0c03400b02e030020400340201c8071211107001d0700d8411a0001d0815050803c01400f90a48107040310303107071a440c82d00313180d008100c1c14107e8560f1320150144034600700d04c01001d40142002296419a654105400580a40c2c000c6010354000c0c1c0e6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 527465629 1250 527464379 527464381
    0x3190b031b041b0509101b030c0b1303300911040b0f030c0405071b080301050a21061107140102070b0606070c3f12030207020102060a0b0604030206070506 68
    0x7041c03004580c030081e022003c004605000049064104080f00c200200c291031110803240781c4e6408840c80c2d40249003444201c0704001c0303002c0501d9032019416044a004150a100544131b00681201c42e1550364402008108540c41a240f01e41e4200300c004440c01c844444072030328405250401c42140c5881c10201e504562258010032181801d20406060403025554218101700e10310009a403445480030441c401c40d2102c0000305014480d100144a040001440000700126460400100e410900a4038000d6181980c0000c144140500154048001d01008407400d03e81c1c1d02c070000540721840c8010114032040103541c0019018070b8282d284880c0c0c0c100010384404041c944620a84000350505220301030038002d100c08100280c1c020011102c1c11a034407451868410b1006005074030100b8094240c0b5607010810050f040d5501c1b002c0c43d858403e0100b58504281c10000390128043e620021b40103078040c03000100c0703600c266800429525402810f040c28260b9036400039906038403840c021200e43d00900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 527466879 1250 527465629 527465683
    0x1502070305160614370e0a03030c11030f15011e0b0d0b040902060406020f0d02060c090f0a0b03090706030506180c091914150f03190b03 60
    0x2001c20703902d40507440319070300e0341c50301e40780e00280003081c44001d02061150005002c441c10101c0a0a4060040c01880b541030007842080e4910200d404181c80c68040b644128800440385052000340e420703664161669550b402503615040104080c401006405204160010080c42c0013041342419100107c07490510720340c107000c0001d810204121841d0000142d040046c4070600c0b00d44150f0784404658580020344154140010b005440d40c480041c0d0014030000780843c403640e0200342c0c5101111880100c0d000d00b1002c60040703a595000b16084c5103125020f00140c210343ca0056213400c003500380108499181a00c40340780d041703664001d0b00c0d0104140c0c0302080802c40b0a0f0503010359039000d0801c542c1c602e81980000103111600e00024800c2009480c0000e402c1840d540d014150145500da84056103051034032080c026103111040d01ca42d52041d01804040f808601c1c0f0348040360b81003080d018000b0300f0b584492944500e800100041000030988845a82c101500c04101d642c0c6801d04e040b1403503075134210030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 527468129 1250 527466879 527466883
    0xf010c030b040603240f140402010e010f0915050f040608090609010b090402012a0302030405031203130b13080309030306130507271a0912161e1502070305 68
    0x315010500039400c02c401080407940c0c0e2030f520700c103401050945c201410b0800c1d0f9030320000d00b9503441a1100c1031400c0740c03415454420001e1f55100c1c9200381c966100c008500300040d0745e00d203400c0d40ca030f00009109070b00c240440f1800c9440c0291f02002810082d05080003910101041d8002d0f40000c03000032940c00070040210f908005594100f40820001c00c0194071103404180010001030019040c014034002802c80d43c50303411f414520749034003003000582c480380d1450025140c1d40700e8482c2c0d81c400c2c4a10303504410340703010704012070f40286401c0030110781c988204c0d80ca921050b07030024448581036007080707070800c0440c0740000194401c242a40c003440e600e141c03010401c20800084912250783c1031820b010008055005075100b03042d422410001d92040c6044000349020514036000b034040c001000c0500c00030f012842015002050007280da40011070105225240c1e0352881d10340102226408440410400c0100300c3c0800c2205003500711540310580315100e4590142041c250000107034065a420020f00c841 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 527469379 1250 527468129 527468141
    0x9091401060617043e0906060c06010909020d08030f040c090c020d080c1e040504060b0a2c040501080f060901020306060706021623061003030f03020c07080f010c03 72
    0x25810860012100c0e54400740c0703054801070004043d4418031108940001400e041150407a144410b910f04003130740b0b5001d81001600c0e6030005d030300582c3d0110109001e03181840c00e584403444200000c0c41240e1800d01c00c42c0c0038100504c030a07a0006803100703488c0c0c04140c20100641c070880904c4080d070200e0a00d46031400c040e80311395000c4903629140c18075448042c0d0f404070705541d4450041c5440030b16610f44554070011032045009180c00303003090020081c415481d20018204507030080703808010042e9190290041c40c40394400c1600064603080205c04650702d809100f506840412241010010402c00840d089860030f1300a806250700c041c501c440303c0c060402540703600c542003000a50135401c0401c04244107000b000b0004007010340115502c040d00700040340c003450051b0031500b02500c1c4070140492400800c1400b89690107400781e800010040481103400d601280d5040e69004100700e9203880486c000e4100703496803010f07030051610004603280c0c10019008103010180002801c403290540241c11114 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 527470629 1250 527469379 527469389
    0x103140c0603071e1107180f0e030a1d09040c1503060e070e0d08040b03071d030d030911040501170114060f120709091a06010309020a0b0a090909140106 67
    0x8010400c0081e10380d80044280c21042c0102011a5020130340c0f4020361340c15144090900300b0b8801c81c400059281d041408030802411801420000c00301e00c0e035403c1095580568250000e580200040c0100b0f502c1440c442064101e9100d801e02040040000582009016941550140352180040c844582d18041714102480541400c101c0c4034900300025040880040c0a08103001052034841101e460b040302c0b00e948141c0c02040d0647d901e40301d01d50480c1e10381054a007840096281c51508500c00c095071500602032400070006d201c0442c020f201200603102c4d48030121500e000c000c0165402c1d0312140501c1d03010f09154100740c0b40e40758009603e01c1c01c460824001c0c500b240c4548003803020783e0712491803101c0d2044040d00c2c8044002403446d60640f41c82c1d90380d80f003809243d14122080e0240446803d103060201403452602907142c07a900c0044090300c444400203903000b0480302d401c00025036100010204c8080078206261450341e1844a80100c81800c20145c07100b41402c8024819454284540d1000d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 527471879 1250 527470629 527470639
    0x210f0c03020313020f1c0c0608060607030e09060d0f38011a160b0610090806070309060e160504060e0108030a030207020f10020f060a060602030906130b030103140c 72
    0x12402510094403483d1004010780541003051400c02d19846035600b521300907902d02c0b03d00c0000740c10f5117004d4001e50303424418040012001800700340c3c0c620302202107800301038155484030070078038402040040003c030150006500000000d5a240042e030315000701c0c941a80140e06081e1840310f091480507410125220041e402c4910b08285a20700c45051682419030f03519050072141585503001180c0365104800b02120400c001540407400c204074401c1c100d100c3c0009460a0045219000094610003c50700945411781c00000009040341d101b07501c8183c4c0c0c240a92800700380b840d00c040e40766061007000314420301c204420450610590401c0c2c02207100800d503000048107690701d00f0450603103a01a4101b0a41015000641e030420755031001c2c1000b0460000903d101d42d10b5086150195544010568840c464010400021403c0e0064421602240e400c1e0b005580b40140c13402c20894145c0c454596542d1501d0f8480700070035009401005035004e14461482400b5690101c0181881d103400581030920807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 527473129 1250 527471879 527471881
    0x62802061015050306040e03040b04031101020c090115021c0906020c100504120501020d020d0b01120c0e10050f0412050f070f150c0506160315050619210f0c030203 72
    0x348501c80b0341400d0207800c0c1c5042500c84d01c5034000617029101c00818510144000305012178009071640040049a202d000c01e4505070f21604010380c0c46d1001c0c00c911940c447c190f5001040600c1880108212283c5c4130300c1542e280f000050003000610500506400c000f0712182c5042c070065404104840c00000c04441c1d0961621400c03070000d003144642c0c011640c1d590f80c02d0822408008007501620f004102a8000359190707010340d2400e000900b00d00c05000c0c00240e0120400343c86803101d01c2950200d2801e0703580d0030340f1030b2071800a01910b076001c4000038082040801c440100c1c440f40300003400140204400040342d46510b81401031810741d190a0b02003080c2c004e02010803a420152003c1d6003107801003180b0714222124a08150740c0b0080b000c102030410701a04041107509407040c60045038148107600d00300681d04850105040c110401d001c1d2b183c02407070400c040034103106462405580aa154500301c0b146054400400150000329090400032a8441c481164240142e000f072800c4a006131800f1421 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 527474379 1250 527473129 527473139
    0x513140a09050c0f0a020703060207110f100804120504050415062007050d030306050414011509081902030703080d1b1b02120102041710050a11030a0b0628020610 71
    0x807921030328001e103591510000361701e0a00c6000303200356030055401620440d101c07481ca0524004003500d0010712441443d11200d454603501d0a541040403c550541e101d003003603541c5d640e0b104440c03e40700404c2018010140400141d6a661380109916032018288002c0200d10f001c00c0074150240c9640851049000810120185400041c050045420031a21144044510706068000b050ba541200345c02c01c0c01c100174850f8020b170040c2d00c1c0e03040310404040c04200041d001030403903580d40d260141c401550441206c0c07500440402c55522110f9000805030b4200b04e5813686c5855550307104590055040f61034102404042140d0895a80618082d0402400721004204424070303000303d0000080c0f0406020081b4081244254191405040c0001211800c5005100f1440e6070301c1901072500d074000d0610000509804560150781c4a204481e03442d58155113076040c403000540b0003100c60b1500940103022070450070402884407850082c084150101c2140b1809000341840c0000f00b28844503880b880007040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 527475629 1250 527474379 527474401
    0x702031204051021020a1e1d0904020f03060720011b0810171609060b071205070b1006170708071202070c0303032f090607030513140a0905 61
    0x1c1c40c0c141c43d083e0301c54020b003c613070102e40c10300c01c610405140c80450030300c91a0b504038020900d04603030803042c0342940c5031115003100e144603100710600b260036400010544a0506128003a0054030090801018203041d0001c685400c4046171884005661401c004544000a050081d948a5640f000307208542000d0215002c180d100b4100f43c003004090700000e85a2525084008007400290f081652443c2c6e031006034a954a12a00c25115106011100025000e034075200e44012246144030003401e00c40a03031152402402000c0035002400000c1105c00006450152218441c02441c0201901541420f00c000c007071049403000d110642c1150317014000c2254001340c00c60360101c0d852070325183e5444500d000c2d1002e4081e0640082804c0040500401055010340001c0114101241c200c20408190309082c12041380030b100c1821404010040b220140c24210010403141c0d0280c00e150b4a4003d14030040500c101296010714a200d189e04402c0c2c6c41840c00c40c0800c0c0052420460074822400d000e10303411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 527476879 1250 527475629 527475649
    0x4030b2e0e010303260403050309070b042d0f120b010b122a030901061d0c1e0f03040615060309050312150d08030a05060a030b060409022103070203120405 68
    0x50280305c0d543c00c55040740142c109404242a03041c004081541c00c00b890054000c0c0c10a9445089a004080000c1070042900c401da030700f240c150003001160b9280b29000307445a2403880c0d03d5403149410f101c4006c205200c100f102080141490b1007490440702c11828252071900068010364404d6000300201000303560b4403030100790042c002050300e5001e0440b03920103850420120b03007408400364000c030411114000c10750000080b00c010740e19081c0040c50010242d54419800c42d01c80780100000e000458071086c4441076045041000b1041500d080e10700245180c154000700c40072508591502c040c0b1108840000609005001608003800084090b6a03500e0300c80c0245c804440c40342c80c0343c5000034104001102e0070459000d0242281018800c64207020141e50f00442e41d0300081810700c0046002400c180340180b08898001442c5810381d00d0715400c000140240c044244ea00c05818125506503a800c84905589481084000c1d0354507103aa205040c2000301c001c840c50b1680360700b8003003000343d51100344400c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 527478129 1250 527476879 527476883
    0xc040c0806010e0a08070605190801030515040606050a09020a0f020619051b1222320111070510020c150703090f110f0d170a0504030b2e0e0103 63
    0x50a0424031034400b107180b116403940022030031b100b4408005003c9030400e0007001d1b5106001092072008940304030039601403500b0b2200500030f50141c01c8031498402299541500184515400f066291765680040c0b2110810741003114030950002d02e61184680151054180b59070b1130000d4180f91030110280d04226140340c074a00301d40c0e512140001c0004400110b4210100d4134001800e4440c802292036240e00201111403040420300340d4100c1201502c04504641c095501412400c4d030f1944020745009007550f001940a4a20441031410002030002e005034007090941040345507c41401e414500c1c42d02c40d04031420b03c41648104803903140740102050051011000c06000340c465203a8520440041c00050300181c00300128400c08810400c0860501c041114110344201000c3c241d00100a5100741c00c100051118000fa14000b004011340030203010481b4007410b005060030781c0c0380c54038881070700200d4000b40c03642d4840d07403500382188150304c1c0d94250201c0840074642c0b1070709107020341c0890b10040c040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 527479379 1250 527478129 527478137
    0x905030c13020d0501140a120803070c051c03020d0f0e070317270907020c0102060a11040e040507150f0903021c050a11120c031b010c05030315030c040c080601 70
    0x60955200e10b81c0440c1c20501030350b0f004028a60717503080b007044550902d1003024030814903440700042c800f441c04030381a1003d0700880b481d40303580c451844c1900c0101103071300100d034203010300d68090601d40759102c48440c426135291000360343c1d00b0743d95050390b0403542e80c07250b850400351406460740741d400b0300002c2c00700a5952201d034166414180740580f0119009401024048525000c011000c45075020764000e40b240c010b540400300382d150003070282e032185010740c003d44c0180c0c040400980603042c80c5d00002211200e1411041c5441c0d00c0360028031604804079010f070760380d5206040c20400c2c242d43c2410004141c000e46458000c410003c000100810b03210321010384120350200d10200201240050810399590010803031780c140c0510702d07003a40c0200c050440c0354841c07410000780c24480c000116034030f1451038004000e0840901540d0790100d01400480307419040003075120140300000c00800003107014240c1c81c017445110042200401d803404610301105809541098001c00d01180c00c600b9a0390000c0382420 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 527480629 1250 527479379 527479399
    0xf130f080f0415020d0207050405070503040b040201030f0906050603070e0c0f0f090d05010e0106140a0b0d14040308040b0c070309170c0402160209060d020307050114041a0a0f0905030c 81
    0xd010700680c041e90b00107005a0851142003114503400065004005400f6025600002c0c0e403001008201d0301c08442d6032002c22410000a070001d221070181f913a0092050400003543e04007080040c0465051030003c480c016590018041c03a481c08015940050013040c003848614a859081243c56019000c414103400002290210444e00d42c1070548000c07040103081c1c10742c3c1c005241052406000c10401c0200954a032084c0483c0c030942d10740d00b1559119010740315003000e900d0f02c05c14010390ba10020020304020380c3c4640d0070064140d14804140103074002c1d511000203080034101203692080142401e49582020060b4900217908050a94121341ea0019040485200e00f60102e00304180210581d51241c40068012a0400f28518a200090003a00c90710300c5a924a0b091001d911a2080040e40c540c0c0404c004110561003140024807045004030040d003000e0ba9074200317603e5200448000d06a4810103c1c580401c1c41d48059521011141841c282103102c0c90300e80070a44800d010070086000f41c003504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 527481879 1250 527480629 527480647
    0xf010e090709031b031a0106020319090909050303250c030809190818011d1903201503070e01050d020c0303010b19020d12180b0a050f130f08 62
    0x42d803140001d6811400c80c4000c168102c018030b11800540c00304482003061172000240010100040d80e0580b90190011440c0070380112014545500d01c000303007004c1140c00301c1d0101c1c200b042d500441020301d101f0001540c80b820610b1030380c07010704415034a4445480280e0742d488100d907400400e0400c0c01e078060500d002d958884942c0706080150000503807840603c240250000c01110100030510020b0300d038441c83c010150000111090b00316150104020b030303105040c0400ba03140c003000e403050f010392401d01c00d52810360360f941c2c500d9020130800d821044000304003021115414140c2e10880c103980b68050640c44c5180c0711801070301550903c4681410442c0100e540c2c0f81182e5140d0444082d0300b4204100c940300c0d82e44800c4e4160b2540a079403201c11489032020462481400042c000d0303400b155a03104e8103600c5125006c0c402c002c0240240902c0e038202c080c424203000c103204038101805040c0c40701021030545400c1d44031486840020304484589286100c60f1004210341041c40110254051034071076444a4070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 527483129 1250 527481879 527481887
    0x42f0a03060509071701050a030c090b030a1407080601090902090a0506010201112b0905030412110409110f090114040e010f1409010c02030a050714010e0d030e0c0f010e0907 76
    0x6422958003d900c02040c0003c481d0031401c2c5e411101c850382d9400e10f0030303030f00c0d5400d10141120740d21004185030324902d42446007190b140c000624000c0080c007218501003c0d61a110a0700c1c02409446882d60010740060040c0901809403a0241c0b40086d010f110410f40e6601241203040000d0000300015a03c1001c16880c1e8400c1d000f0400c402d1003c5400c58540d000d0010b12000c403002e10341c007024a10144445200d940d1514010b01700c0094000c0c01650805280403104815010418021210700a90384032568041d41e8600c92200400e0242d4600143c0c2c94940c0180b110495840607540c0c4500308080040008012a801860400105a070040b441000560704e5601600720300c0f20f6640050704000d0491030340c0d50035a140034412442d49000f030010819080c0260703203900c101c00d03116000a004210346000b082205100c006641410f0000241411030000c11604148a840c69980007030f40751801c01442c00420001e00600f40170031a0944140c102100028101003100090070740680b02e0840001c03402802 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 527484379 1250 527483129 527483141
    0x90f182413060f0b120c0102070611030405090f01090b01030b09130c170a170403170304080c010c0203040f0b030c041e0305030711040501060305280b03071202042f0a03 74
    0x1010b0014007072402d8001e0400060140c8030007150048140710808004560001107079040c03c031341a00540007190509008940042408200b00c01c0340c41304120010b0725481e8002d10078810102c81c01520744d1941010030920079255084a20b03810141006940401903039100690707500700d5412281c40c3c841c00f00078a044610700e4403a9005401da15800d04407080204008180040e00f079110303c03800000d60740b00004c100402c1c0654000070b06001403413141240c04403070040045070050f0082a069003000800c0300c92a09454800d80490010780020800304030504c450403c040107428040e800900b10b20300720604203141d00036031040d504604102c01139a04101c0d042c1040c1800b46401c401542d0f81c0c0c2a80e41400f81d00c008010881500075442c0a00000b509031007881418001c0103d41c00034944030141c1c400c0640c14503540d00c1001c3c2e40f907079a0300b040060b943d02000080020031200a0781075440e4074078010003089451380a56130f5221030707645a0110811420b4a40e038604124444600e645401e4403140840043c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 527485629 1250 527484379 527484383
    0xd15021b0f0d030f0f1401060e0d0804030204050408070609110a0f031e02060f0f090108010f030f031d040911040501060509060d02071a0c070c05040b101d090f182413 73
    0x2252403690355121b0342c401507050583d102e64540314009400c90051207481110342401500d510304c144028001480c0c190000ca4000c1e00034a0558240300716525081d0482d88041c00441d580205420444014185000d038030008108407950114054995110711a4190614142040c1745142100a004550324441600c94500d50040e4564484a210f410300103d41c0c02888401d011030000c0000240c0700d074002c01d0840c140c07a40310b10301001100050b81c0035502108296401070841d135802810f070318551600c0c412000035034001c0c10343c41c000c1e401c860280421228186c0050003000783c200191030060b1560001c07603000700e9241c01c0c0140e8581c410300702522080c45072a01003410120140902a1000f010300181101074010301a05140c07954070410042200c0c1403564003030704018541e1a14040b41d02813800007103217a18100061241c01e0400c8006054000c4c1264000b20310248401807000075901b0b880100c00c009801002040c0070500b414001c18500f4540b200c01070f14180c140c0000d503030355082d0418288a55 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 527486879 1250 527485629 527485631
    0xf10090203070e0106050c06061509010f09090f0f2406051b01140109180c14060d0e061e010e06060c0c0a06030c020d0c0c03080304020d15021b0f0d030f0f 68
    0x151716901c00401690002180003001c1c0f08201c0810007510f00351f10407480341246100d4143c94007002c0001501e0300c03443c1c01c0c0c2101c240700002c540041e4000f054099484000101400002c0e02e0044480100031a00c0e082d200d80403020303602c0d4040c0e0300306140342c403000b00340d40c490f0400603101c960b20f0821004010080c42e00707086550824000031841c42c01e551916060720034405d014410305046143d03031841e4800c20300c0d024040406801c0c007001644c4c0111300350120154050a554076021040301580c0a44044c91040c810907441071081102d001035114092101e407080382407003c055450101e042e0060034016010520030040000d40d40182003081001c0140c80c0c034081c1c101d000803551900094010408840c1c4c1802601540c0c4941c40e0191260001c80f811585c00001c181095080da1100c00c104d4000402c102d82103e000805d036004504860742144107581c0b403580c05a034618002861742d80c1d80c3c020100c072141a42c05030241601400011038030703141280441c9800650702d80c2001a84014044001d41c41a03d9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 527488129 1250 527486879 527486881
    0x10603050601030b0106023c0106120303060e040803010303050a0c0219060f020705131a06130305010f05220203120a1805100903150b061b0606030f10090203070e 71
    0xc400840d0142c100ca024542c0760215a0343c8581c2a600c070300c101040c007080d850004c10303102140c42c1d000d69880300540c00203600c00f5404030f060040764219441500701100c0125060104d008041c2d00d0f014910140004c0320a458507418290303210500340c003041c000103041c00804030326000540c1c418200794540c0e940042c43c4a10a40c0040d41c41c404c05481405681c0000b90721003e60000710703000042100c22204c000c0c2c85000c10b0851002c1d050010a0507200b6074400224130300c000741c0c559840501510080c1035520800000520b5440d0540c02c45070850282d4a1041c289410450f4001c609030450350308034240c250300c16004c0e0041c80043e081c00c08004220a444202103030050304981d00106540d140d4080d0700c2d01000c8652590100800302c0b694081840006250712024400201e80082c1404140c412160228103003d071070300090900e070402e06d051104000ca43c040e40303240e164100001a0040400e4002d42002c940b0b260801e43c03140104210960140d0f1502854821034500304502e100030310040306500304d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 527489379 1250 527488129 527488133
    0xd05040b06040507030c140c0304080d0f1d0a0308090a05030601090209191527171605010e210d020f06010e13060c0e030106080102090112060f06031d010603 69
    0x42080a4807150b005519040010b20b03400c1c0030340701e44080041d03d0780342c00004c0281d40114408580c840780c0c8000c0e9a01060000244415081000902580b1280c507044c000300d6070000018425460f40c0c007241d0f1104080c903517030100c80e2a10300c0041e007504d41013103d01c0d80c2c541c00403000c1144100e566104e1501445110b000103640e40355a40640000c1798226000900e845481c202401b0485590003501281d00510810b80e13074ad1405802c1d0100380c0d9003650104c1d100d4400440040700500040c6c0c2c0a5045074401590400202d803040c80900c0348440129540c0d540d1504290000b01540b00c201d0300e19003e200401d02c4407a4010041d10764010100c01d68007140c2e500c110502c8000c0d213422103120110040c4c03040c1c60000c01c03801c00202c000c2d8402c0e5070b011070001d0401c00303a1711480003170020604c10000f408242d80030a542502e0a01800028003220030015980d00c0c012400140140d0780b031040d64004510300002840114134840c0c004049504514010801d510b50804458401c1c00940e21600300c1d40c40c1c070b000002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 527490629 1250 527489379 527489393
    0x3040515011512020c070b03060102070324051807030201050a02010e24130b040605131a011a07150b030c0604031407050103020a02100903091203031a04180b04080d0504 74
    0x414102d0350380c03108050303001481c010059008039a0790140c0c940004000344000003d250103150320503030520441b10515900d4485080b03406005035041c201d0b01045c1c0d902d0100c0c2201d40181a0401150103c240c002031200018036120200782c00300034100040001c814180c503200750030001b00540e1030420b0728170580300940300301c0f887c0c3c44c00c03640036914001000014a0a004030000c484215403c00b440350905d50b00d99540000500000b80b03621a0044280d1420001c0307207840d02c0e031160300302c2d0940542d0341d0307541406141d811100a40f05000c80c0d1000400c0004005a40c0b000e030004540d40d81c0c00c1c045100b10030b4000007402d01400440290700110041000800d00000818226040c003040c001d13645020b85460044059100b00d02c1040c01580c403959a00100d800540d00c00d0404034003c0c375029a001d62601000c2c2c141500c615029000213489000e05410110416103804960a08031800c0002d400303d8040301403603814a81001c0d0507690030b00d001a003444a2241200d02300b104a080400c40c610f480d1525030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 527491879 1250 527490629 527490659
    0x302090f04230115060203030103080a050f0f0c0604110a06050a141209100b040204050f13140a0204030606050609030d0f0903020d0b16080c0d09060e070f050909070e0c0304051501 79
    0xb06040d504051300290a600100440b07041c0c94024104900d4a05c00a50644481e032007900d000e00d90300000c00c400c0c0345100b0b41d8000307080045030000c05031045003000d090618a4204562100c0e119201c1c0b080100a0340f43c0090480d400c40b00b42d4202801d401454208107001401000301802a150701ca0701082080600454204180c1500c1d88003004141c4441e01400200c0c010350090542200d12000c0d00c030450300c2c1000100700c41880c100008100c00140451103944d5440582c2d8021691b17802240900070083d03203001c0d282c0902000d071903250900310100b00184d83d40884241c03010500c04160381038a0b00a2160030700501030b54015220400340012894616880401211104941043c08150000261249e108540210355800c49581002422802e9030b0040c10040d6003158070720ba48121a5a031a10f0900c410300082030b9040018003002d00d00004d01c842c40b0802016148240c21102081c014038a03074004903504000c1081005032240d980b498018038100190001000800544000241c0b2040381320320b030307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 527493129 1250 527491879 527491901
    0x2c0705030d03020c06010504090203010213301a10030c03080310120f12170c030a05180a0f020a17160602010c0503010b130f0810150302090f042301 65
    0x503074060048020481c12070064420694081d0032101c01005107185c141c00119456000400045c074002c80e03001d0601041c80564005594014070162b00b03102001481d5403144030360500c4c0d0213030082500c40ea0360700440c1140302100e0081641d0140c0030954a8000c40c13041c2e00503541c883c02c02c040d626100d003084805c0ea0411541e030800f5111903c400b003052800000180c038000c1e400b00c03c161a044107940d440c200c0300203003482041044004010320b8018000800308a010360284071126a690408c01c01220540320000c02178212130503518002110940d00180da540072a07002038188030310004034070018041c03001d15070207806011a00c0182d0402c459011801c5a0618507905801000c0e5580d035400344e00780c4440c60994808a107007400100025040c0ea8003c0904040c0440000d0b08130362207011000c110381a5801080c410f511011486680b10031074824002403449000040c1012844c542c0003682140006100340d90200b908408641000625050007480c08020584903801c84010304000d03000b4500ca00751 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 527494379 1250 527493129 527493133
    0x30c0a11040f0c020a0308150d03090311030c06030a020a02011b080901060608010b0403140127060b060909062e020c0a091116170f1b16092c070503 65
    0x41e03802d10030000d105030022040b498000d008450819203082c0c1e01d400c0e000b07140030404100c14541072110b5039404030700c80d06544a130700c41d6295242036040903260100c840020f107010342e00803507400c840c60359241e081c0c980c00300021a01607520703140f82e2000c9001d0500440c4100019070820402240142c0080348140700b01c02c0300c0c00801c207407030766000d08032840202840b039000c55400400051000c03a04000400314089000030011506110300c0c00711079841c2009040c007850740030417510301d10104540d501034080803000c101c4906003407000040014403500400f0b003990f07108400100d9480300c0c0c80002c070140c0c1103411315150f0001983c880145d02a4803890b00f100558403403100071002040000e82485041c1c3d40e4064219024204196041d40d10f071482030070403003030b951811000c056001250302d8038003e010020444a01701c2c0c40e244145810300808518021842c441e07000f101104800510700700740d04044803202403000c1012100b8000e000ca80001c4d45044800880200c500f84a046074001000803c8603010b800f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 527495629 1250 527494379 527494391
    0xf1c0e1c050a44070c0302030a0305071a01030503040611012307030b01080f06040e0a05031909080a02130c0e130c0807020703030c0b1009052a070c030f05030c0a1104 73
    0x40046940c0307800c40581c001808a6480780e5154030f5654060100d091040a0180b8240c2e2250002868800480c400720000b41000405004014449103008108a6071000d40d82c501d5066586282e206c1c0500d0241104014402c1c40c0d0a0550303500350804100c600c1071a8a03e0506407038010620004242101c008020038104074451846500c00c07c02c151080c01300c2401c0e0311558841c642048054152084940303828851440c0410104500348010031400c6101182c1200c20a5005000342842c2001d0340204060b4002452500240e120a40c0100f040381a0010000300c0420445094075248800c011181e008903c000078440c00001c151b02c00c45103178906d51503210403544d07004c10482c0d903283c0e00d000060001c1c0140a00304c001408940c51140c0082215000310b00c000c0c1c540b0300d403900f01c3c0c50807507200c0c07890340e031022080c81c0c0494021141e000c0710a00a280520340001c588422909514610008090039884051142840400d00541d2200c15104080e10758807896400c000d406d8004c100300e502c1c4110b16041d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 527496879 1250 527495629 527495693
    0x20a03061a0f0f0a050408060a0624050a2307080c100e100c03020f07060c120e1905030d020715240b0309010b09090f1c0e1c050a 57
    0x6400e490b0448031010740603242008400142209401088030101800070070311003c40d040e003091024034404c402c1c98000081c903a00c0d010380105480d150710840d040e205c603005016817881c1e5220048840c01042428008910344c0083d11110701040046400590800e000c0b07040300400000700010000c0102503000c0764040340300100c0c0c14045645420301d205a55200103402e602510503500305e0304280c040e600340141054038003080d280003035000103011540039a0b524080842d95801c8100004c403080c03203200030481c1d07500c2c5d83e400a03641d41413340e07001c401441c0810090700f088002c00c229028400d00d510300355160303071042c074003030700d440f00c1401c0003450160030454040c20300320710801d01181c42104075842801161400416401c0d6500280081d26071755200c0c4180c44054898503603560189a681004004c03d40c0d103148250f081c041b4408501d80500c0050405100c0c0d90740c0100001c80c82c0108580c0007100070643c0003402e01e10078180780010330030702410608106000e2a0800d202402001c00503100c40c2070300c80303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 527498129 1250 527496879 527496929
    0x10021f05010b041208070602070f0515090d03180804031410020f0306040203060d061b0f110a0b0606190e1804020312090303094f0903050d020a0306 65
    0x90050b0200c0c14414401080600d20880f028082d80303020359205071800360f443c0c54030030990340000410b42e02290a00e80b280100a820445680104906c80e500d03c0a4100301c285c070b64403030203840e03c02810141c6605400b42c614002c0662002e10311780c000617203695180d032031070040114100c0301d40800301406007203804401c1000d02e0013102d034040e400c040120b1642c1d540380d041000a400c05030496800182000780c1074000381c44c0b8031485403100b8402030000310107407029038014805035400540c10108072040e200a00005030000e041401c0075400385590303485076200008901035008000903101c1181010400d01c20051b004081d11075200e2040d00c4c120742c088a01703904500703010340075203009404da40700d24584003a0840b1032010303203c1030341c00500b079a180c0030f001800100b1004140001c50070401d04109055406108500a0500c1c60504c0c1c40c1c2070f400312504c5800401450b80c074000c40044545442c00003003018441d904071030f640c0b064450300315100d5114120040080c840ba002d50359005205100c00250b00d003039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 527499379 1250 527498129 527498131
    0xc010c03050c19080a09060f0906060f0e061e030a060e0d09080d030f0b030708030405180705030406050901060e1e0c04150e04061d090c01090617060f10021f05 70
    0x3c42e803045986203545001224040f100500f0810115540c02e40c0d400060303198080c06590003441c4001003220310702030518204440c020307030014001c072242e079008000d10005070000c0d0ba07201341c040b5413041010300700c40303051811290b049941a605002e42c42d0202c0070018180c0c070208004403424100d4884580f010f0040d80c10fa011405200c4250340222a080d800300d01ca90030a4441c0d00e51404d010a00d20b01c40c5020924013002c6801c581c145400224040c0194203190340c0356020752200a10300718aa0800c580040d00760322001d4005840c058603000042c00210017500a503005280c14280c1c440d05162040c0c007940e403004c00050400e000112072000c18031100340d18040da400d94203402250741d4a02d0030032405540a2a82200e50380d0410744079000010245005503c2e11440111440100360310303d010010f0600305010f003140706043c000d0300740b400d12600d5444003440d485244690418a00364a41c100013800d07518075104c1441d130007200440001e515a50100b0f514418540e41c4084c410740000003081e46042d508 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 527500629 1250 527499379 527499397
    0x10060f140f010804020f130609020d270807080903061303031b02070b0705011d010b150c280f030e0315060904020118090e03070c0e0411060c010b03030c010c03050c 72
    0xc0f440414003600e40303035514800a05005281409080c5040040800d4074003c0c1e10440e00369034003203014400078400e40541010308802211406d400d03a81c400300350030880742942018200c041301045400c1017000c0307a07046032016040107003240d606142400f03e615000d81c5042c2c0c00c500085c1050001000404c0059100c05080300075000b4115540c14151002c100d9002400295163340d200c40400c040c1100d00407030b42400429010001c20f49584140500c00c0e6040c0303001a02d00080d02c10051030780c00900100c2c00420022140d030111025412400f15444221001c01c0080d2040054096110030544c01c501404154401a4240d13420100f4085041c040883e088813255000000c401c002401503125803138425034000c200511641e0baa40b1101854101c411151101041c1d5000050607030a001c1400030003402004590b008000502d055510350780b42c41c03160412035000d03604c08186240281030079000054103940140850740c9454184881c01d003c0d101170260240803c3c03400f00820074504e480e00c11204054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 527501879 1250 527500629 527500637
    0x11120703091707140310090c360b01030b100c03080a15031209150f02010f0209030a12030b032b050a0c082803020703020705010207180e10060f140f01 66
    0x291801040344c44000d040b407242c42e403600541d250a1041c101902c61031a040340134040e1980300a0501c41c1341150100d58000030b4100724030340003404820000107502140040020720002c1141240f00d00140d01908408a42e260b0241c036110822034034540c4000d10028060180d569025281c5a9110900448443d20302007400b0a0404005101152034010210a03c07000c41c0b81121800756102c0008030070f4070081ea501e40c00940800341008125509000d00d0010140c10402180740071010340021341e4991540d030000380078210212040f00d1243c02580002401403000c4d0542d0703081040760942c0e48650341760002038850620b51070304101c60030384140300b602d070300c1d05840d00c81c006c00f03030f407140c40d905069004500c100d0040c1500180480800d6003000040c6a030242c69200582c861f0103e103806400c03c4c7e85a000541158000a020450b16000468240c0c0388200080006184090465a2030605224900101c0308600340807000519002e109207c20444441c0615540c4400c401420030050240c14400a4002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 527503129 1250 527501879 527501893
    0x1305010e060d111308030309010507051602010e0301060305030c2a0117130204090807110301090b061311210703020315060309010e06040606140f0901060f111207030917 74
    0x10781c15400403d103450700010440c1066240c84105404c5030042d000717805190404800d000390742100f401040e8000c015400d103181030280c8072109040e41030050380040c1c10800461044452504d0a6110170040d6400c001980d42e0b5090140000f5a240a503d202060725820b80d50600b45201e1803d858403400c09050359a814068528440c810b803484000d0001003d0310282c00d16000180e94500c0742c1103103288a052003039140c0040d03041800705202c6d062034031750003a4140b0b190240010001a80780d03038001012144601c0c110001c01c0000020100f0070101001918006480322441c0d505548aa001966110348400035a8070900202c069000036103600c8100c4070520a20170071854080e0145902801c0c400001401001031a0703e640303060f00580d4292002940c51109120039100ea040c11030719440f040e0b8074241c0700800c1344d01040207400148074420030480e1080e00c0d441a64469a104941d11401500312940d88c80a091103044503406004c044012900000c400608521402c64004c1c0048070000540b41c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 527504379 1250 527503129 527503147
    0xd020a0c0e180d030902040608010902010e1302042705011d06040230160302090f0d02030114070f021c1d040f09050f1005060a060c020d06111305010e06 67
    0x28500c4040c0c4600340e500901080c5502c108401c004001c401e5800b82d401144040c81ca0040c0000c40301035801640b40c59050006510260f47c015410944010007519850001d800c1d1481c02002809242c1105205502c122105c220005064103050421180d122040081da640e03501c50741d1144a071810743c0c0c8200000400001d13210724240d8080c01000742c880c0c90f6100410801e10810907005000340c1c2245255000b40e05025100d001050802c00e0448541011031802d0498000100c1610280410700e00c00d840310950601151820f400c100d01c07030f425180051700309040012014040e8082034250340018841c104e1005043d4091080002c1c01071070740d403a0714203010b80546000080030394949901d0313009038540000016200320740c0700b0000003a00902c090b05c0005840c030261402c01e0360700c184c40d510751307420202489402d035601d4005408481c03607030500c1a030201043c404074420070010b80340a0310340791412085109180d5080000c0145400c084001c62410381c03610011b41c1d4070301000303e949800880511901034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 527505629 1250 527504379 527504399
    0x2030124140901030603081b0c0a050d020f040207080313030305061903020d050f16170c090c070609050303040b0a181220010903090503070f0522020d1a030d020a0c 72
    0x8242d90113140226040d6100d407503a41d690382c80944580c03101c407400c0714100764210044c080c40044403400c481e00a02d051a110010f0324003445680c02901c0f410b08800a22100d030790720b5046690803580310101a0302e902d480c4c40303000c210412a0600350082418000040c2881c5015044032510020b482d0a220040b070458090000110940e54200ca4520940f0400b14580c0c80800c00421000420207181c45080d06014508100c8107000c0f032170484641c4002100c00c440c0d5038887c11690305c0b000002000b0b0300c0308a581000c07800703440f6034000a4001d01001091109000c00c114483c3e102d1381c0c0102007440301c5200c03408481405404480080e007030511810070042540e12414a4036032240d00d64815400b00094013003210b08580c003140d41100803480815040140c0e0506000b4a030040c90400421a806498000814101c4002d500f00340020b140d020138030b46004090b81d0541e01c901003203030000c20018090580c02a41c080e07081075090320900c580c0c0c80745994144000340b0003624942c03040040d44101d00c1c0021001c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 527506879 1250 527505629 527505637
    0x201121103070f180f0513112508040e100e070206180c09010803031608041104021c09050703170f0d09030e06191b0b0f0402041104090203012414 64
    0x1208101d000c80a40e0070308007407443c44c07201504855081c40344c07480c03401d0200701100031151300c04800076050800b0080840351340e0302601d80d031032051101c107241e9052803008410b0130005801e0050001d0701c0480d0120780c51119500152051000a204811032500d82c05010701d4030400716803500041c1e00c800b00060080300c2403c0e1642100c03c9000490341d0484141c0c000520214098109003402ea10100070054880b40b81d0441c892900018246489a4200381d02c0d50710780c5a1000d140c8a01841d00003600880c0284c0d1481c1540d03505502c040c0c00c215901061030491f444140501c4142d44134807040c107007020140841004c0310040c0740d007070100603d00894501d41101030045240282c0c01d020303810003040c02d191a0107000380f82d0603074400041c0d513644041c0c0ea00035000d1007214841d128103070316100d850000100d20700d050325042040d05a81d52001d070384038800100a450440161658410045070025009140350082c50607120380d2464482c043e13449014061110124401450000d4112041d80320b8214090000b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 527508129 1250 527506879 527506907
    0x60b0d0902040b060d0f051602120711040e0102130e1909060204051504032d11030c0301063c0515090604270614190312050403020112110307 62
    0x4140e4020f520009205504480101d500c1c00d51250042440010b0502c07645030300200c140c00500c1c5200082400035a14003402e8030011310301000041460902c5842c041115032068000e0087c40000c492112680c042d400038000186502c8082e200440d04900f001c1c4141c0c8140c103200510041c0c0c1621070b01ba1805000c1d0804241c80040d0708200129682c0c60702c0455420000c10b08180a40d21499072034031700d0a581c901c401000c50180303e601d01c068644401842074995a4004400d00c071881c031500000390508540c0c06000b681036192000005103d841d0140c011041a80007030300001d0b2410720071070412228041d0190052049e2280c10078270481c50b01e80c2d18420300300707082e103252400c00541c0004542142c0c825044100b810f007225213098400e81080c102050b000b00c0c4010188403c51409103048202807404601c24800c58010010300001249445e80e200296044102c40c1c601c610102d5015101e9402400142d0010303d40400c0c00815455a00801c14041c04c00a003403495507130345010460300d2542000314 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 527509379 1250 527508129 527508131
    0x501050307050a0504080a21030203040506130219080f100605030d0c080d02070f060b01051c05060d020306010f0620120f090d0b071b0c0506161e02010909060b0d090204 74
    0xc90075810402c1040a1184a11710342e00c0320791104e602408c1c0c1b5500d00403203041018010010800007960104000c0d4010545207442d6545d8040c610000300f512480d043e04050100d4100307400038045400041546e100c003422426145201000d034840416902d00d40126070b0142d1140340781980b11480740030b001044c00d0240c00703444d04280d0090100e906030380c420181900c080003001e00780811b000c8544074000c100c200c01d00b881341c540520580602540845805441000c0b41c0e1400020f5030740d161180510002e541c0202921655030311943c0c001303d92802c43c003a01000900402c07640070502010225000c4104a0701c0044c00f4899900d619041180e01180e1800c140c90000d00800840341c5482c01c44c81c1d000c40c1308000590740f81c9040900205202e0036095007001801c016004040072801c90300f400410307a401560419a00d41d194030881e82410060040140740a001e000d4002040b14041000c4229a1003641d0707481103940c0e80d4141506940d00781c010182c0b010300401425010600c2ea80c4081c11551001c0c00c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 527510629 1250 527509379 527509387
    0x408030c1204080405130504110d020112092d020109032a1409070e061204060e07060f0e06040f050402030402010903050616120c021f06050904080706150501050307050a05 75
    0x61000110301c41034404030346000f0042000c3c0040d25006082c0c0c1540c0c503000300c1c100054501074a8243c000c5c654003002c14020790010307220f402903901c991055400c0081101090014080600c0c00b000b8541414802000c90340d0030701c86820404586482c03500c28260141c0d80d9216690840e01c03104000314803908038a0750110040e0318000f1411a0090060040c452035460343c0551110a051107480140241008100040802b011040303550390f4003560f80415015900382090b0b40e82e07241c82002020003041181592240c00c80000d11294801c4031043c0f950007541d10301a000c032010080c0241070045006901d1302c980055014031540c00d165025541c003034014540315004aa49481d480c3c00d003581a51030001e0000080c00040b0700035002922020013a14504080000805290009460302c40c10702804541c00854140e0700b0461400c1d40281c0e000d440c00800c0d64046043c02d14100303160b135100c0e1000300d42d0035007042d200307100e8540744a6180e0220350040e11110f10310f5840d41d0045800d07502c400040001c0c800140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 527511879 1250 527510629 527510647
    0x30c0c1606030e0c031f02090a09020c01091a071d0315071d030307020a050d0f12020303070e04021201031e151a06070519060f0c08071b03080408030c 66
    0x11818014006614002001c02481103910b0500000c00c00784c80c0a0fa000c101c40500d000c101c0301c00109400100c0c07000503141c01105001078000042544000049800031501900100040d031110841d2403003060102051450704680030207140c401c07030382d260211304110441410410100c0400c502404000d0555200c000c0c0413149200e920310555400307001a420301c2140e0031140303512152080441e003c500441c145915540010190003060090900403c0320f02090f0303080205409044980c941d0040724030340300c2150050000d55942040320381d1800204003e40504581c1080d10031200d131120120b0a400340c984c21521070040704a03102c80c0340102207140b14001c1c000305940403070700040301d402000301003035115a071001001c1164102c16410301c02c0b44108840030001d02c1c0051050020014003032152620000e90030720000401041010002050902d05d61948256000009034407841c4a40c0300d0b000301080da01c004c145045d5a400000340401c0c2e042001c02d001c02e40c4000a0342d4400c100740d00c01442c0400314 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 527513129 1250 527511879 527511913
    0x9040602090d03200c03100f0902060d140a020403080712260f09031c0c03061208031b13120c03050d11060a0b100c020301090b100f050d08030c0c 64
    0x3000c040c0c0018411307000342c283c40700003442500b01040c0c500c401018010000800203488451154104902c25a219800c030304480301c1750050702d442078000381525201c040100030350000e840300625265144217038000041124450b4400d44040d40e81080005041c1032441c2e4880c41c244185d88043d0050251440d64400021110b10300070040c030407245084040f5007021240e42e015408040c20f00c0c00c09030410700c03c11103050743c0404c030945c07082d45980c4046002203107504241c0c01411a1b03008030300040c3d48410081c050004920095000d0f01d90306030105102406914010344130f02a10315401c048504400e0b080001e0080103281c042014080c2d9520f4105981da039903010720b4aa43c1e94003031004506107130410354520000f444815405000c01c2d0050000d485020700291912017000020414030401c8001c3c2007d64409600c48240780340d00540781d46543c01c14881d080903220841c4548080100c0d19000400c1034240681c520710305662080d102401c0d9100c02540c501640c0282e040c1029034445c0044c00f500a81030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 527514379 1250 527513129 527513149
    0x18030212070e06060901020d180b030109050121020901050d020a051306150804051f0212070203340201050715020f0a09090c0221040b03041203060812090904060209 72
    0x15810003044410324294155003030541c01800d0f90b100e80000c0c040070100340d8011403010000c0c000340c580b039648011644640a100c55990300200001d140200002c1000b20a039408641078440e40850781c07030203410701482050505e21400d0000e4109000200400160403c100d251007100d1004150b00f1060392100d0100d00d002c1c0c0c9040d40f148010340c9928082051a039a01440600e0361801e15040300586850345442e9940d881000070000c0c078000b0401d071b11248007502e905668440006d0f102d86043c60400c1c40b0002d580740c00c01c3c1d1402d40c04038041c0c0ca510110280c50050f05020801040280441510603001940d190f0001700701910194040b11051012401d584010311601c034408000903110f620300701d0002c02c84000c41e000584d8003890071418941a54000400a007139080c04051401110303442e02000102d401280c1c81036241650100501040048144a212801e1030720341e0101704590b542d6054603038030040b60b240030701130002c204008001c0b8100010680d50150003050050701d0080c01d400440c8003154 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 527515629 1250 527514379 527514409
    0x5061516020108180a0305180306180f0109110907020312010602011a092205030903121209061003060c02010603021e040b1f321803070f030201180302 66
    0x100c0600c240d08568100443d107400803107103440c0c0000e803d03520481c6941c6164008014040c4100030580f5000391007000790009159601038151100c0381484600013103400c0310034021a000d03009059131460005014890807c609400014805400f000c0809100721714001400400442c0010007420120101c4000303c18001c2c0101d900000780400e6080542c0aa4054a8201440341107800d0a003c2000c504031241c41c0d0005410350380002c0030070a0b2034501d03d9032103030031403403074160284141ca5044024494040c0800d000d102186030310366034800c0311058070390101300d03a00328058100400500c08203a01d503000b00407a1100d800000b40301c03071b05d179000107505203128000d0004005064091121701c1c10640a0078070202c4082d08d1003018100c1000f40105902c0c155950a401c00910003102c3d130030801613a8004c001100709048040c01d141611014030a00e40c42000019000b02000c000d100e80740c200020814101e62400c1c502c2d0601034150342c01114900c00405496540c4074485401101513590071004282c02c81c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 527516879 1250 527515629 527515657
    0x803092b0c0f170309060a0f110f0f0c03010501050d03110111040e0411100206060105090619051201140f0d05030d0e0102040501030b01050f04090921020d080603031c050615 76
    0x1610b050301c8400c554403c0da005540302e4205021000258442c003042e526001140c3c1840300803aa140f0104039010707400003041c24014406c1c4441910b0802c0042400d000148083c01503c00c00d41a00041c14241c42e028800d864200d440e042c56200804c1c418440c461021940100110700042421400d40301500150050410302c400d21080c4010030001c8003140044903010f440a010040766045c2c06511040d000b01042c0c103000c1c00150002d900d03a100c408441300c1c03040d03401100c2d10009025500403c540c00c4140c005c0009000380d40046941903e6242041038000010020f0103000540c1050280c246120101243c0c20309c410721109490b80d8186c001e002c88154550300040c2c8541c50701d800141510322040c4050f042c402d08000c12035003034010a041b101607480e005004a40d0500350303d4010160440000a211040d4445c5c091000c010381c00b01e181018486155075211854986030b041603200c1c0304508000c080312151a592005100c0d01d03401c903039844a4000c101c002b00c104090705021302540320303a410302440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 527517985 1106 527516879 527516909
    0xf040c0506090310090f0b18030d0b0414070c1b0f090b030c03120403110108150405061f050415020706092702040b0c06010803092b0c 59
    0x100b8115513040200c4803d6050aa000d80f2010f0700894410f117428011440c042001400203002548400255190a0781d41c4802c4c8010040c0d80110354016031200060558402c40c1c100c07544c4a03800c07a48950f8144051458811001401020308022203500c0000c148881034903d5600030684403100707000200012480002460b2140b0300604907450320418459500c4018080c0c0a441264451200c2448810a81c0700644003240221030701150304881048440c26450075030000340d08030001404414000840010071400030303401c446080c0c0814030014081001680c060f50010044203207201600c1032a0410200a03d0f692a910507035140c0f050443c22042d060800740c1410842000d801411035a9903914045488590488001115540290000014524008000c0b0b032900d18000f0300c1403601200003030081c000106072064251125102404000008410419403130261981940750303490 = true := by decide +kernel

theorem cover : BRFrame.Cov 527338129 527517985 := by
  have h0 := BRFrame.cov_init 527338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 527338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 527338129 ≤ n) (h2 : n < 527517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
