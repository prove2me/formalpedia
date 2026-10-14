-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3760
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:35:52.871035+00:00
-- url     : https://prove2.me/submissions/6d374bca-8b1f-477b-9285-58847e56e988

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 676079136 ≤ n < 676258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 676080386 1250 676079136 676079189
    0x914160f0f12060b0d060f06020d03150f030f020f01181208040509040c090f0207110616060f0e061e070f031b0c0501230601050a0302120115080a15 65
    0x10071001c2e000801c00b843d41d070103258640307a00501c8003150f483d040c01400650b48841214030012210b042d00036220043c68844110010402241881d0101000303031004508406108200c001075071065800000d860818010090310210780018103040210400340076608080b040f8a4a0490b40405203d20482d511443d10039218040c0b50000b41d009040f00d001c01c8140702c5140c2c5168201c030080a8100007010248074480240c0c030499102a260200d00c4080c05410300b46400140481070031491440701e026101d550300c8041c0c030300ca02442484952150783c1d0490742041400303050f42010f158034008070f203d00151252000e10000070308010601000c4a03006505600940011124105141c03c00f075003080c091001401420084400362070035032902e0a000e1a5241b00c816468091480c4000120b5545e240c3c4011101603119045c02020150244000380f1850842c00c00c41d0301a007804130754114021100c0c10b00411180b001012103025a09018030b00d800a485510444140d4503090b08200c03028aa06031046003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 676081636 1250 676080386 676080407
    0x81903201b0a1e0c0f050d020618030604110f010203090d030305040201200105010e061c14030409020f12070807050403060507201c05180d110a0914160f0f 68
    0x2107031070f5400300e403015000d07003c1501c0d5400c0e01c2140c0c0d0080103a100c0d01d20143d10100c3d401003d410440e0301d640240036162400103001c480340c42d03100341c14000b035022021a0415000380c03800c440003c0f805071496114501a000d44a070503800b8070086003000040000a80c580f030550340060185541c1d5804141564407569541c0152503a0201480c0d550070b0703523001e481c0280000d20410b2082c050200100b0701c51f1400d040301c49031209800c400c282500d0f8084d1a01300a1140e84c0c00000d41c288002c00c400610016140054030003464401401529141070500d854078078000103000100b082400300400c0455900070003a141030703c0d081b007000105a507a98600f034a0140080c0e40905908107030750050b90f0030400c000385884243c405208030008146481c0c40035100d5002d520100441e00300d201c0d09104490800000e81040b40d809508941003400700c0c2c00c0070030586502c60300b00d440b2654030b504100034060142008181c01c008010f48010b09000501c0005103100a404051410400c5841c41e407910184241403800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 676082886 1250 676081636 676081643
    0x303070c03032a050a0209100807090f0b041401030f060b04021209010c020718050c160507081501030809060306040e03030108011505060708090111030403081903201b0a 74
    0x490303078803410040d000c0046075003115082008144198240c0c43d01c1440b0080555011005100c3d101c80c650820290300c90081807446540c40400f80040c0189082105000914505800003541900c66011909940343c00300514000c60070030140c240250000040681185e03081050690340013002d26144024081c40411180d1260011402041b8000c4210300300d070003032460400070001d04c040c084040ea103d00442c82000e00c58248041c1c501c0d0042e566400c00c03580100c20411203854901c0c0712030f000040464521056442d94011481801606420442024036000c040c9480c4540d6166a071307111818400c114145010b5400800401c105031030f290081d042c0b4203000000d582d220b6031159050b500800d1b428051202e140600d0100188030b040c0801245d20143e0804000b500e0031034048019549001020050356480c4801c101c0007010130400c0300a85501c2d581174016071154010400d00030152004500c3e00004601c00fa2f00680000903a101280c1d415201c44c07101803c80c1148041e1281415074498029 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 676084136 1250 676082886 676082903
    0x60916030b040f02040512010b06030c07060b0612010e07030e0a111c050303070e12101112040302010b0a06031b08070909181209120809062a120c06010302040902030307 74
    0x3d200494880d00544103941c001e8440030a01407400c1607842c00e030303a80962929044081040072a0750144400020300c5007070301658020410140590204850b98464503990303100b80449401400b14061007100e2903080352041c60103004080b401318685482e10311380f000c0100740c0c403040c0080d1025034513601c0c640444001144142c91020034107080030741e103d0380300326038220025449a41184452070b00342c0e0307165a101c40c0d00008161a50705064184020050045004142c0805000305c0c8074160300d05c1310081c4075511039800842d44220380340601555110755000b00c801e0504040483c001017101015801030100d0351301e840b0b8226102c0200c29a08100d440e0080d111041c20b201d003e0030f015140560001440303200c0c01c510f01200764120011102d281d01030090010034043c100da900c01007440b40000c0d00301290003c001500c1c000e0a080b9104414050380140358101160351b50300440003501380900c034401c220288074940f03440250b46045d6182d0784140002480340366240b50410940d2410000d403030131940d215128 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 676085386 1250 676084136 676084151
    0x10608070c0c0e090a03020c0a0b030a0509070506031e01060e1003150801090f020a0506090d06090501021c0c090503010e1f0b0901031a01050f060a03020703021005010b0a110303060916030b04 84
    0x202920b8560151064015108c0e900001d001030402d02d010340221040c801a0700d0554507249a040003510002d0b003200c8461040d10004035041c2d507040b00131070040c0701d411000c1405c00c0c1c043e40702c1d000d8140141d0000c0107010003264003104035140e03079080c03007105030080c40c00044003030048048125146403504801280c2d80791079902c2e0104202d98100100d5140225003812084d540c2e4000c01c0311a21980482903048003100343e820f0001005500000e61451082c0c00241c20103500c100d101c0740e50600c4d02055900da64075180300c01007181d001120b900c0502801d500038080384d4503665189070344510f45001d0100c00c08c0109810610303075459910070074140a00a20340b4105503540e04003007690000c00d00c00f03550314400ca4000040d0710301d0001c101c2c500c980c04c0940b103507040541e44103054000790032003a8164103600401d5000070f403a24451040701d001e4072006c0589500c4141c90032004001c4040d9541c02c0f05198020024032100380d95403400c0c290b000300810691941ea007000942107001c0c120242907142c111b428a0784 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 676086636 1250 676085386 676085401
    0xe0901140601030c0309120908060a09050705130b04050f190b0603070e0319030e0118030308040b040807120302190903110909030f0a1d030a0b0a0b030a050712060b0108010608070c0c0e 81
    0x80d5421549103800704c40164035070004080c125044ccc200300030720662103039804000c142021070019031084e0700964001910400e450100341910404c0b03d40e1524648036104002d0005c00b0441e1070f00d001c03003101d030f0100052230103d0003184d440c1c41f028104005101001072040307025070f002c1041c04846000380c07a43c0d840700c00261a00bd8042000c449005011540b000b00300f031381301107003402b0440c11290966500c0000391101e4a814002c40c0c4003400c10360795075004020707060103e00c0100c000c00290388240d0380140c1d54030025847c007003543e82008120b010020040e0003080814030410784d008000b1000c940e040900e4403039100700d6245205003101010084000703c3c6640c01c1540220091501d28002003d00d01d038100c010081545035095554014802c05080c1c01080580c445d0341d02c400030421015003140d8200071207445441c0b03400400e03884090144501000001004468007900d280e0400a08015070a03504091003c0c0203048010200344c1046441e141700e00c18050b5290501f03009110640211056060055 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 676087886 1250 676086636 676086647
    0x90c03050607050c0a0b0c09030f0a11060f0405060309010207021807080112030f11030d06090501140f03070b03150901060c032c15220e0901140601030c030912 70
    0x12094036a40998000181490b014004846040003140c002c1c00d540c45d000c0c1d03030f0f22404000113000200701e07078000d126902094601300421045071002d40f0040000c0001c500d80710f0340c8402401d40342401400c0c180038951401440800f6034007500d108450540e2650740f120350325030090040080c06540050000c2420043c40d41d101d1a03580a15a1035851544e517a0305d0320046002a81807a20080019000c040c1c0c1070081480f40f6400344070100440185d0345006034648191058426680080821a80d6100104004007600d1030704c59504100b0788000d194a6807110000391196030510806484810020005903014480b01c5080c065400003130211b2001d586446000300090a204030860201e4442c8154418aa000e600b5610041700341c0e603001005006140203101d182da40500d0001c034401c4042c0302c40c041e000e0032201c0d60346d00d0004600711882224030301444000000c0010300b05803d540d01d44401035684907010701406502c00c60a00300841d03c00305185046000b4010084050010b00d0018200e4880640c4036 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 676089136 1250 676087886 676087889
    0x3040807120e0607110d0c150210060803160804090c050901020c0a03020a1202030307121806030b0102060121020d03020d020f011109040c0909050103030c200a050f060d090c 76
    0x20054003203030208820080e9040d80a480c0341e140d002109000e04000202026064000c04d2005001a00506c0385a40c07054541e60450700404601101240750104ca00d03070400c00189003907803000701800707010719240711252203114203010308058455020804046c401c0c80b00844000703052403102042030480e02c40006040d9041401c481d40140901183e51000d881c14024180c15680c005050303460051501070302d26011003c24404980501084c405500800c20401c54842005137035242c0244001c03d00d4400095035000360808000e041c90003c140038241da0000e00941075503840441c101140c0340d95412181c968480604c025031080758886004105540840c4078482e4400076000c40b00b0ba8400d0001d034030f007607904804103040c12540030302110405e45010703004030700c03e03d240e824000d0f41c0395111030301042130302d00036007003940880d103505483c80c1080450540712030210184078114901000c14000203c4003d020b10580e4403940c0c00e0749184c02d0540c1c50300308548603521140000c0003030031454581540840c005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 676090386 1250 676089136 676089143
    0x7080f040501171b0a1202030108060405160b0f0306060d36022b0b0f1e1306111615110307050f180616120302040b1b100203040807 58
    0xb01c140c1c600d0a00940144640540a185290200c4185601c0c4130382d01600024120f0b004c00c0500182c01c1000c042d00c0c801503019040340c0d4054041c0b8941030400c40e151054040c2d1404071540d550208009103020700c400c2d10801c050500240e41e03680c94040024006004141c641b07000d044c64004006825800c1100382c1020300c10305404c040000b10001a4188a4619081d002c3c0d0000791103410b000c4100c070380304000715101d91000d020824900b0152150540d1300c10480748802c000542000b8881742500441c500d01e0410356100401640c3c0c07a22540c5050342189a04008141170f40700d5a14020b0401000155003141c2c0c0e00c00c0044051441c0c500b040c50300c01d40214440702d40c40b482c0c03c0f40592040f0400741201e00c20005a20344500c2d1102241582c0256404034041c13013019041201d072203601d0307035400c0010900d81400e806c010008800c181402aa140d07040140d001c01e0500c1004100701e080c9803041561140b0052070103c09141c801e1920041c103104803d0980298244000100020085044080c0403440e01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 676091636 1250 676090386 676090397
    0x20d0c1202070302041a0f120d05030a020d0e0607031109011b02040e06091b03190212011503110909060106080601030c210603140105070e090a1404030504150e0d03050901020307080f040501 83
    0x79050f0034070042d0030b800308c0a2601e98004d0805000d910f40070f1030045030401c0c80490b00500c1d00008800000455800d0408100250425018885850361602882c81d807034440301c010303034a003024420020b4401840743c600c54800e107004020781320665440b0f0384aa0b02011400050f07950516160b4078040c0c81d40400a0142c0d10004900d441c1c100c01c1c00c00041c0002c0fa40f0900c09400042c1081342c00304240e081a034060200d096484960400e498094107003030000544c030030f201d0307441d0810280c0c0802200150080c2403440d00c0d40b203500100411688030f1030040c0c22040a0130f0000e011240c0000450780941c02c65002c0c4401d040030b011038029400035920440859002e5800a40802da54500f010f00747c41e0b0650703000c0300196603a0b0300400c20f4604601d20903005650810000b6410745c40410204200004640c02e4000c0f5601180420a900e40305502444800d180e15201e04001180c0d0b000544100d120080035003004400325100055034000c00c02c0300d80c4140c009901c06c0d103070280e14221100303591103802041d00050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 676092886 1250 676091636 676091659
    0x322060f030203011d06060705030d0609050c09031002090d02150a08011a030703110c060f042d2603190b040c02030a0c02040209120f0d020d0c1202070302041a 70
    0x184a0b1007520305840741040c207a0000100305c40340000910015080070b0740100100020000524100700030a00034201351004a60380c0d103000e80ca070080780c1c0d00407c3c06000c0392007000441c2c0180d6022490280c803408007000140c44c1e5011401083c60100101c100a4212050502d40701d4071101080141448640681c1c071042e0b0340c1e032240195003003c01c03451803140c90f148060010460701e500070340020740e0590099110340c0c2480340d0307041a03c0c42c02006586414452002d07000b031000340440d0138041210111a4800030502280f0f40b0050209004032100150601c1420745102c03042c2c0d9444001c0308511101d6003140b136140c6c2021141c640d0240c0d42c50a11000d1145840c58014030303424140240302c081d00d2030b90042d5061440800382616003205070b9200b26401503003000080c03411b5507202c44c80031050001078020218510030710000f510305051005000203650241c42030b403040c698440040d95940d0f034004801d10031805018016403038030416030070003503200f41403400300d0408211154600c01c601c2e208036a40160f0701e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 676094136 1250 676092886 676092917
    0x6090204030f050d0221030a020f0a030e0c010e06070816020a1d0604060f0302060717210c2503020708010906020c0c1002070b130b1209070b0408060117032206 70
    0x340400291b00b9030340002c4000382c6242125110296500c403004000140ca441c43c3c809404507294801803013030002ca569400300c11480c1d9410807011182c0c02c0e007820704102801d415400940240100c080050441d20006100302c9d6080380c0442d00c40c0080d9014000000d281c1d04c584102406500004000d003080c10003000056940c5814000e000031201d0841406c2046811502400b01651042000f510f1460420000000d41c0c1c8000c002402da080c00541c0b99a04401da060750307400d802c03101914100004009010085200001c80036079801c0546c40811410740384040c1c0383c03c3e410950b582c1d201104951820f2250002e03c0b0080e00100440103038403040d200e0389260b0904000e00c5c00c90340d03d28440160b0011b0824401003854000800c90141c00b0030b0000e0381e0668542e2080010b51241100c1d10041019000b440b4841004100a401800e043d0442a08007030602003150781e0340c0014862980344421030383e074540c50000c0500441d0858041420181521068811601340e50300b064810760300050720750107829000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 676095386 1250 676094136 676094143
    0x14060708130309060e010516080a090b0301081b1201060b070b0105101e140409020a11070b070b0709031a10050316030605070519110c010e101206090204030f050d02 72
    0x15242e150301e48126090a1520840d40704000072070441c14404200030300400804d414040c180250301c83c5c401c0558a0b000144010101d02050740704060f54401440144191580454480d4903461808422441c8042e00c00009418500544109507294a42040440c1d0303c50000010000c0c0d40c0105403600e03413640d80341d050004001003140d050300060104849010100c0346140e041c1801e1085191000b135004034a40514420f80c810b921024050781e00250003075000360401c0510000210200180560502d0306440c000c2c81c5c4258200100b114070103000082c9114041c00c4200041c41e00100460540c000c40f00040300b00c03400c2030300c490300b500040d4507000034140381c0080c000b04d6519084035140189440c50340d601d0301a0a02900c5c2406009081c0210010f104400a04605104e460369524901000c1b80710018180782c001c211240c10030540301034004980d00ca80c03440b50f500620034078080105400c80c0341048014203050300100c1d1070300d000040010601c60101c030100b03000703401801524001101014107a0340d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 676096636 1250 676095386 676095421
    0x405100503070e0910080102160c09090323040e150103060905070c171902030d06050324183c071203180306091110080112030c14060708 60
    0x681090b206040c141480840b40b9004809170321025056500c8005042c03d98110503900075071043c0d110081000d1000e0048800010b180c04202040401142d4070700030000465112414000d40c0c05e080c41c2200c891a03030003110700515040c0703a500c40e9401c1c0720032062000c42c0c900360740500203418600041440000741c820a40034107202c0c0c41c0e40340c00203060707520726441c0c01002c031509007a89014841240380702420103401120088039400703140e40710005250b040840b01766400c40360203070f44124001c4074100703001504405010180461441c50740d44010300e000420f0110303204010b290007609000080c0003a07904101c01c910015041100100c1d4100c085011114403a206404440e848800c04024046010b140700001502914103140c5402c2c08030400b15030343c070300d6034030403110a59141c086d41c007805907400c5010b03211881114004070b001c10440c0d00801d1100107000b607005079610500c240003014010b000c5403030f000d5441509c4000c55007072481f85540342c0c0d204031407030008102202d00081c0e440700c140c4144e59 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 676097886 1250 676096636 676096651
    0x3060c030b060d180209070306081c0e210a03110c1c06090507090203040b190b0a0501033809070903200a0b1207031d1b01230405100503 60
    0x609190056480310b000e0048130500c0380c088403142100001588440c200b492041c00e580c2c0300421070720f1801018074a4013035188244035000c41d8904403d24202d41c01500014904011124205503600c00d56801000d1144000e12400c9441032030701c040100368000144c0c201c2c44441d682500d0401d401d00c400e001802d04481490b0500f03020004442d000240d0030381c0a00724060040d4116041551521440c00480e4025a03090b6458000d590401031551f4400e20500ca602a04041c20b024065002c400304604d8070321802814181625104030700360440c80d03860601c03000560340d000526181a1f005061510314280740d0380f503014a88a800041200c1c1c012038000d0100e07a40f160550080d03101c3c9101c4401c0f40c81103802c0d41640800c0364a07000400f07240c0e14010300844c1ca00700404d82024142940007804540801c200326080e461107000760082c0f01c1010a80f100034005a00c45010b900c0307240320040783c1d8001c1d11004000e80c400000c00c510b9207250b244014005840c81510701c510300c085544429649800f0844004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 676099136 1250 676097886 676097899
    0x203182a190924080c030d030216060e010b030a0605040210020d20031b010c0e0a050a14030a050727200c28031b0b0f07090e040c03060c030b 62
    0x1085030240b164464030342c029500b62070341c02d0910012445496040180d020f00c0607035029050044403890140f02c0c0d86482500360074114548030300c4002440658004000c0900001e984401d003040040082d001180c0c100c0000702902c040f0701061801070010b2000f03480990040c4212014030039802d000081000740c444040d21100f0001c150070000104000c000d0207400b800d804144254a00390307560403000d8510400300d500100307131004001c0300108035040c2c01039064403a000601c8104019181c12480c0806d40d04200d4410b80c4d41160b640c04a0704c0c00a48a000a059204582d000910207584090020040c228138a047c0c2d089204800d121042c3c6480750030030403801c1c2c04d4801450200e4501c030010086170300800107941b00d540005001da08810b805060020510b40b411000e401003590240241c000c0140c0c03070907240890760480c1c40f040c0295200604c00c403101c0004071701141d91070340500300b81002400141d054403010301d03041c030700780a05c112644002c454090400100d01100e41c002e000e407400c0b030300f8081d184 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 676100386 1250 676099136 676099139
    0x720010f0e010605040b28030203150108160f05010c1704030b0603060a0203040213050411030f06160215040f0201090806280b0315190f050414070b0306040203182a19 73
    0x10f04440407c2d0001075100c112140c50010050318140b044070205411880503610541c176181c0c2d564248134000011074418008003000744111144e18a004041d20f10130320704134801c00780500e0201c8003110110b8030790300310b003c010400004000c81c1c44403d0303201e20001d6050b07034419110343c1e9001090340025540294400040c94200b03440200c15400b450f440350003403d81503140b168800c007190400032880e0550744075030030103001c01c1030164050745403200c01e500394030081c11002105000d00301307510030190005102118604196080d07a21900d800c0000c1c04400c816654641021010239900b0780e100b01300781840e10385171840c1000400c0d042c0300e0011981809400750122841284040515000003000300c81801c0d094a1031082c280502c0c03103482c1006c100908001071900303150410305099802c500d0b90200b198010082403181e07000c04800d076a000300c0261000360f101d440d001b5820411042c11041d8460a10401c250850403400c0100d0082c420903036185040400c170b043c0018802c40182c444406800e00040080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 676101636 1250 676100386 676100419
    0xc080708031e0a050106020d0f120b04020f0a0e030d0318151d0c0a092a03021204051b090108150a0e0708030c010c080f0720010f0e010605040b 63
    0x55510290303000b00c0070710340314040780380150306081907030140b5074580d880d401848815010064800009094142409440e00c8282c004021800506090070074a448441401032511180c0641d80c20469610b0150307210001e41400600301c010740d58409100b031060343c5d4182025800f138032a400032541c07a201c42600144132502d0305210403c0810380002c00c0c2c1d0b034a03003030081000c0f10905003030300c50550301c009800340600ea0020440340701c8894214061451410030802402e07550001044010205510449480c6101da40c4c103900a004480340307840c5011f038900402041200104c1d0380e10302c050303030100c0d0303130351446003410a10050607424014681d80b0781c80f490000c0c15502c40c4404450b841a1170503004148a0440301141c0d041066030f17840380325681e001184108a020007800341003910082464000707890314201d10701c82880710000d042c4005011003a08100907080415070310718020742c0858002c1c854801c41c050060b00403d80c01c0b85d8000349528046022034240b07003602a807022544020401c1c03548524501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 676102886 1250 676101636 676101653
    0x60315010804150203100302150306010c12020a02061b2103010b0706060f1508150f0f01030f0e0721050c01050319061e0509041a10050409050a0203010c0c0807 70
    0x1c0041c3c0d440392040c1d0318810001024001544942c55162800c4000d514602c14841c2003003110783c11081140061040000e02d90340000700741c01580d0032a051481d01a00010700b0303030602019a0000e50099000a488080451441c0780d8103180c4642c00d04032140307107442d403419681c40000f039036102d002800200010043e030207a03040a056000d000d2100012a02d6a650220700c408040e07030b00465407641c407611602e420a812000c1c40740d00035030b54216840d14902100000d881d2034441c00ba1184640a1980c1c4240c8591095000d001c001550080802000c0740d003038000e980c1c4030407030b03c034480c0f1080008180d0740907c0761402c58100c11a80c008014500034103550015241900000e2801c40c1c1800e103034190408035003440c006e43c801424001d0a00072440c04003000c15081d08816001140074495043c14400012001604482c4880e0721190356400c503241c1c3c1030030303444080456102030352043c2804040000d004020907003000b40d40c0308400802003280d0044050300c0140ca20322002d00305400600c051004a140342 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 676104136 1250 676102886 676102891
    0x12c07050c01060518070207051c02060703050f0c0105061f020616030b090c09090a02071511210f0a0b0a0b0c0c1c1101031803030f0e0609030c0c0603150108 69
    0x20700010848030348950205500a000004e241a03c0c0260402e10650035014459407010307080a5410b0b0914010401205205103d9000000e002e024000762041c1814850810740d05030071010580a540c0707107124100319000c0e00c01580d150b441040c00c215480007e03148850002009102600a0812941d40b01d002d007a150410368081c03802d02d80c60b600441e000c2e64641c80b011780700d410542c2c10b9907291000c05040c004d1400d8002d0480031440d10401c103007400701c1d256404251400509480204e015945031042086602440c1d40b01040f2b0182d00d1030140340184c415503401c2c071604500600880a950b9484800292101c841405411911000d400c0c004403640780001c04844141c0340c12681e101840c8804248000c0e80c89118207a4074001506140c02c0001031000c504c1805006d207014021146412a02e400101e40404001c0a25076901c0c510412654182c1206441c0b044810a880461805c040701c00e132a680306000348401406520100c08441c1342c01001e5900490f0355140c48020741c01c910005641c0740202 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 676105386 1250 676104136 676104157
    0xc0a090b1302040312020d050f0f07021807031a090f0106050d11030f01030201030c021204090b0307030f030206062107031518060225080d0506150a08012c0705 70
    0xc2a01c0c0e2505050395000600045100714080b1041034039488000303051000320781a4008000040125003070400e0290700f603e0024041c000700030b998a0807403001500c07001814005803881040d4000304410150154050380d0044512151103000740821010400705135811602071281920060042c031040344500050b021035151046c0010303100c10080744500702038204507180521005100018406c550745401040042c2d206c4d40005d00065030819020040d501a9006010250780d460a5912095504015607001550401e80c82029140103040094581d0400c55002d405071030f9406890042100494040076000d5280016001c142d0950395010514100b5614198070b05444002c03110081d030343d880d441890f01d441494016595101151131400c840b0401c1d0040a14076680c031091404100c03020b04a84032482c500340d00041a5543d200002c4040b070000c180120b568801141c1d5040c082c4c0c1010009060301c1022000c0000c403c0d0b084100c00c5a1880f143c0451354079805640401c03540c074000c50180114048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 676106636 1250 676105386 676105399
    0x11120903070506130c0602060f0601050c03092206080f030a05090a170c0a1a0f0a030204030803070c060b040506130b1f0816020a120c020d1a09010e0c0a090b 69
    0x200e41c0c03106850f041c4240e40500000d44200c680d1001c0050103e070308402403075180058002860103d003aa8101080185400c5c1441000202d100350352105004aa083c0c1000420250043c1000c40c04201d038050701c107120790030740d40c5024004109044002503000189034101e0040d0b29040c64148200ca80b50806040c0e10303040840711202040a101c21203802410340b1411000b812a41c40c0d000c100040480d81c0d0340131a179041203100800c0d61002e410000c9480454420303142c9644c0e1140e01404070000d12507540301074115003010041c0708005500031030355040079016035001e100c0c00c403201c8100011640b050344d4107503006003484d1085401f0b001d20b030820300c1d403c01c000f0420150201e955104058221900c2c0091000a04020801c031481c01d2001801060782464401000040c209513500e8005000140c40082480902803e900455032484000b12a2503401b0a040d12018949403040e42200815500b1a145501700701c906960041c0006420a20b910020003200b03041d413402058030300a050f080320054221a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 676107886 1250 676106636 676106647
    0x120d120902090108060a050f01140f03121c060614030a09140601060c0203191a09012007031101050609061509040908090a0806070504150c02030106180c0311120903 72
    0x2612080760038004c2252902400702031800d03000150403214024074440c1e5800c4414014003441501000701424100103450005858040c080083c1c68100c500800d00ca11400c0060300c0c0620341c040c02c0c80d00040c420100d00601c05141c0711041529075050a8210b240dc00768188002000707440c0701e821120005019801a6091280c118040380c01c24400b45c204070b0103c2c83d03802000d0f00b181010004a10110b0001c600300300800501e80e6400955440c8510641d0040c04490109495040c2988034658545d090500c141100d8450100304600390000c00041e400308400710004c0245040600440c3c3c031580c001040c040042d80d0710b41c100110701103440880b0503107560512400820b51507510410300c106002d9200e19455a85807010421032900300d030061949070700144184050a500b160944003918084070241c210240742c881e080364070703e5408c0300c080c0d410340c20884000b8030821640406201c802c10700c18140700f000c0c91b010050b03043d55003501003420110b400b08010114525507001c1c0300d0700541d9032030540b803508 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 676109136 1250 676107886 676107889
    0x12070503040f0b04050c1503100501080403090f03050607082214030c1203090d090303022a19031203020702010518360105120309040b010e150309010b120d120902 71
    0x208040360211003950000c0f1458a281c43c1c4803034050384c0111007c06841c81e600e04161501c04248844c4240e60510240402040400d40103001490280c00003501c0d40e07610315a2800c0c003907920141070712803001084000f4003182ca50403060644203104c000c25041d40f400c0c60b11a40e900b20310844046c5d5200e06601041c0492103000405114003c41e01101d41e20094172410903031011070408480703025400602c0185501040000d07000b1547d8900c060003000d40d0f0400300010540854600c1c1d9100b51980d001c107400144170289100680d07018140c83c020603840c030302082c010406504a2040c0f84001c0c0c08070f007042c401288d00c88481044998507090162200404002401050507070035200302c006201c409040a458290003607801071503005082c21695884c0c42c041c10b080064aa100711184507000b9511171410a407240d000d03a19111501c90098604100c04083c2c3c000002e440d0025a02c1080650900b250888039150865502c20881c0d02c0e24040c168504c90810282c88550406100308055519440c1e5907016 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 676110386 1250 676109136 676109153
    0x1e03060d0f05100608070305071202091305011d01050f0a27081e120702071d0601140c0a23030a080a090501060b0a03050f011412030f0a090609060512070503040f 71
    0x140180001410706c107003145409801c20142d40c1181101c09400e003594405661001da00f40d07005403602c250440c41c00c10900b0264054008400d40c002c0e00000c0300ca04002812055201c40d121f0031540c400d01c141c688500307003800161000c00d014010808484030000545031025044c80c3c0350b10344110310043c0340c030035040c050091010741c90003501c0e5041000318161140e20f06c640001d90f4084003500c0504046400e01d000722212924600180440d00450350009041341d005101403600c04400040303c585501e503064149070340e144160f2044814002120503444103235a240c1d00000c03400b600e00061410800c017000d04407480f42c0000c00a5000d5901c030141603001c140700b8030a840103400c0d412900355480110400150903941e02502120508942c00010000e40d032288258000740c081c1155002007018052032003501e58062121507162041300064070100040d008013042040b5a441c0d192600500e80c1d601060300c1c076014640b03c010311148000d0020754600e218800a640c814400e503124004401252206c400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 676111636 1250 676110386 676110389
    0x206070f09050307080313140102030a0318020405010308030604060609210507030c030305070b07021f051509010b1e0a051204030c05030309100501080d0c020d1e06021e03060d0f051006 81
    0x40783d4000190002c0307c52070396021400030300202501381d0030702500800002d42c2c81c450256000c040680e203220480d038403088a4030603000c071500203005021a585a0902103520b40c002d40358107104603e4142c000400b64000c1612034224bc001200c6180c034200b10103000c803011035108008440714090420007100140545a0003c0a5402540d4031900c4404600c1d040c0811080900f040d0155404510a510b03185004031001108814041010685031038005400c202c41c404042000d501115030000840c124548201528070280c2c070411038030341c14010032240782c218400c121180b400a603003004040c0b4450407070039081c0c0d00b05101c3d03d03003441814160b4075080e0071034005a6040c03e850700058100c0440e4003490180d1400341581d10302402c2000c8520001410380140003070700901650300c072800c00003400b01c00d00c01040d08007207603400317070313500340141d10f4100001d52000d41159106140001c10001c02c030826400d8900c5200e003d031410030800d400381c840381a040100b0008403030314454481044410489030142a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 676112886 1250 676111636 676111649
    0x304140a03120b1804120201020c0322050406050a0b03060d06291f11030403120f02011401030b07030f0b04060807030b060d050601051302300a0b010206070f09050307 73
    0x711802d469014000d4450b1010350302c0c4501e01050030600e80040181080782c01681c02100462003092022041e0b001e0b01503000d003c0c02e10302000c5900344000c2c0c0503240102605245910704072130683c450b070404c4100d500340d01800750420312180c0140480d004400040d80c02000062903405211a030f9900c40050700c3c81c88154541c051a06403500c2d20804804028800e4403004480c401c94400311943c001c10607480c210000c0e8200b088401150203000d005100b01e9024542102c0d280e86c00200588001e404981e503c0e881c10015860a00890101040316441c203050f20f038010840000303912100d8088000e03200080e4100e084941e101d0404001d07075203900c144401000702c40090082185107081c00a074007000100854051071405c058940014008250b0341e040d104121403c990300000b00c0c168800901450600c813444909040c2e114030310703020586003400342d140d611040ad9020307a508000d80c01511400391400740941e01502c00310309001d009080003014800145807004103159100300082c5886425800755 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 676114136 1250 676112886 676112897
    0x1060203031906030602040902040e0f0f070f0e121606050301080d0f2706020114090c040c12091a1501020d05180d11180708060603060a031a09010f0c0903080304140a03 74
    0x801891032f040842661103030780b1081c08461450320f110440d200d044000c00703040411440c241c034507001c0c9001e007119030b91080002e4081c20720442c0064501c0d54840b01840381e961060b500c0440003402c1c80c8628100c030305a42c910005400060551081980c5030304c5880400d6092002c402100c0f120b2030303010748201c640900c8240010280c6403400101900f142c01102d12580d04024900070440503050025421006203015100003610604e00340341107403080003100c0180751050500030f00b001888080c0340e03c10b0300780c29050a00e04994444003101620780d500320b8102070140c0c2095514021080c010000f41044100f40604030200e007250000107403007c5181b10741100d1200520002d55030a003022401c140310081d01500d04092030401c0803010b0a40c48005101d039100f140c000002800b140c6440e00c4a80081d54040c507502c080901c40c840e4048044000c85102009600e04410b02c2c013101ca15003d00d008500c00e640b02d81c0096411030700c81d0116544001c1c815244014000e840b1402140204014540e8900070799a5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 676115386 1250 676114136 676114139
    0x9050406142a0c0a05030304030203040f05010908100515100215070302070803040b0613090b2a0f07060b0a0305031305031c050d0f060f03020909060106020303190603060204090204 79
    0x6100404409008009640c1107200c82c1c030030107040c070381000d61010301007940e2645030700012000b24541014407070010040d020200a0004258000010740182c1740700c91040c6080316102d030011102404144114042ca5010003c5101155075540c8050b4201c00b8140b403080e06d08207140081840601d03c01000d20060344081801003038586440d0000343c103c1c02e03d240651502f0f0454a032010a404040c2c0301030813400e495000f0400640c2c0c0c040014070b1a14006d0307020301c5007841600780324940349000c849407005c40d02e4814258041c81180000000c1c2d500442003010b041146d04506500700703401c0b40c8000c0f038a480c2d8039000b05141c0c5c2d58421010009502c210015a522410000810807558650b03222070b0181d4405181501d160300e200034407500042d8589002a254410261080701030440b1158110846241c08004688a054861400145c038000c0c1d511590b02d890b00407000359982c030244646030060308140040303a10f4400c0171103e0701c5400440c10000c03a6042d2282c54079030883e400703a44a0310b4500d034001070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 676116636 1250 676115386 676115411
    0x201181511030a090515091305010302041a0a06140f07061d01140408091c0606050f06070b041209030605010f03031214040201030f020d060909030e1203040501081009050406 76
    0x1c100d401003942002542c1403c09454018040e66002d000d86885507190000702e02034503c4070400e9414590004084a1000344042c0c00780004140070300040e4060f40c03e220500e14040c014050107c2102030140640f804186030503401c48140d00280c00132034500c40308101460005031102c002c5d20302c09009410024800140c5651460131940e14550011282d04160150340311144600da5107a00540001d01c0396940c1050318000748281e102d0f006011310300160200440240b01069014000307076081580c000e0482044c03501080868001c44100400201d00c00c7c0c000340019982c0c01000e030044001e401c004c80c4c40e5440f03968910903280f00b41c11103919510580030410615512544040002c00050001c0056080d84c40b40d202905500402c040d043c19140c05401d170b41c06038141e04441215090020400489494246002c050126104150009941d251002c1d1103450b207800c50344402d01c5404004c42c81c143c0707003200540358848000c0c44200c04c24800d07803000401e0b0900d8095580300398400c4c0c40004034003c0510 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 676117886 1250 676116636 676116647
    0x31b26180321101805060d140105150111030405060c0307020603130302070b040617100b0f0310050f060706050415050702100f1b0c1e031d010c0809090402011815 71
    0x200003030300c1c3d0002c0f284100810364001c0c41090045803411004612035803550081010482540c40090001c1c2070205003080294040d0f0096004600c81002c810382031500c100111609101b032042e00302550070411080141d49000401000c0e05510042660b0030602c40d40c0016407181c008a8803401c00b81920360842c810140c1c10300c00c46000d0030131007103001d040c541011390007030040704000306121000d51a403020900c400d00509048000341000b0800903500c1e00c0d0989000e48c650820340c0c1131002a110318501003202e10707058030225042403016080608207052a142c09000d0704000e0821b07030b13402c1c0006000c1c042443c454012148241c046400514070400c0b40385c1003604913031819420341c494500d04008c03515903207904851581c14901c07a1410050707910310b604011258415440d103c0d401c6130100032600702010b401010a64041003e0002c4401c50032000c0d0056801c00c1d082040241074003005c1060f58042c2c03420440700b9810500614045412041860900c1150301090704021414a001520f2241d1264004d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 676119136 1250 676117886 676117891
    0xc030109031710030602040b04140f0d02010f0327122a08040807170f06060306070804240b031b09161e031b26180321 52
    0x154020821200a620020418115894030035088185040801e42c0407501400c41e10180d03821480865945540e10900c01d0300c1d038002c0c41040e0703420070120b0342a405460020020b00485401802c0d218a00c80b01e86e004545440740301c0182c0040c955540034003a0790b45101551082445014580755483c51160306104a20b01480007003d020089040c100c4030020b4000c40000d003240d45030003030b054007010307035440c14000c24011504440001d2042c4000052961704080024160381000801c1e00e090000001340030352070b00411101590964480008141c9048c440c5680350b600a015504c10400180070014542d145c241080c9002000d503141c002c90f00c11490306004090350841ca0b80c85280c01101414040740c1c207407100400d1844801d070500355422256000341000c2141e0480400915108003c560000c1e006003000d401407003401c50b1490110502e41d002c1c200c1a01c0301c80000303510340030040700860301891803100202440d00406d80c609001110341e00800c090401c058440c3c1e1b1204140c803082e034060b0110b4600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 676120386 1250 676119136 676119139
    0x30e030708220b0702030706030e1014010509090703081c060b0a020105060901050d0302060f04111203040342020f0708070209070c1226160e01020c060f1309090507080c 74
    0x200071244c01030703900084050845105040110300c2c0c45401079003030309202c00da81d000e41c110b9050904400041d42c020040505132241203503000c0c21074a580d14915a541301c030b80801404540104042c0303d85204608100311010042c410200d242c40e12030248004e6600403140c88030241c2c0d101c405005291520050603405000305427140032004459890003550b400010700312002d0401c040020609000c400c142c142000324021700100f000e69040e84800d0381c2c1f58404d01c1300365090340c10380c0102d0311610ba62071070700032903181c2914580c2c10410040c0581c8501d100310300f00d80481030380d081044209000303001014040060113003a0300e5840d00b060380103114104030300801c03100410440751025030000d01c107026a041c103401d4502e4441c5840031000000d00041000d07040f0241500401010882002d400181490255407282d40e402c00366030302c1c1b400580c0d403090300c003883c207a05c04420b000d6071401d40082806007a00c0450b480340300842c60340d940204c604232030310450180d0300c0c0d411030b41c814003107041c00b040716180f5241c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 676121636 1250 676120386 676120409
    0xc060210200a051e0304050615030c010c020f010207030c090204050a090203060607032001050a021801140415030f050c07031701181a03100b180f0106030e03070822 72
    0x1581c1c8407107a078910584941c2000d004021030700620821045100c420f0101e22000459520b0802d41842c940e0fa5200325601045981c01109015460901080c628101c42c0180c40300215101d0301e500708a148900d11444038114443ca040001c08100500500c000501244800507070344c900f0300e000d0141201140c0c00c0300103501e00400034030a064403040e00b100ca200340c15140480c40412100000b010035488442e503404698203080a10080030500d600030010183c412110f0402541180010755148281d030f00d124001080c1804100300854401c84844154040c91500003204c14208a00ba81100c1054511030410305003c11100c00300350f00101010040302c07152682c40700961401050982c0000051f018414a5484035080020101040c1205814000090a0714011383c94520000d0081003803c4020344141ca0090031808401066020580502c1800424440681c00c001c3c0640240c01a004401b113544400c0240c000403401c080c016011010790f80e0b404c0c104030003074030b00303031614041254006c41c00c82c41 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 676122886 1250 676121636 676121681
    0x3031d01051006030b15030a02030601080a0e0a03030509031e0c060f09030919030b07030504020f101b0f0b1905181e071d09010609051915030c060210 66
    0x2102c02c0d0454045402d10318010514002501c04100041b1080c5d14404600c4c40200070300030030304039540282d48a004c0c02e0703840030125a00c14203100d0a4071240080b80d11701d80c00c0a0720840c007280c03094102e41e40c050814000c591825940101c4a08060741c401080702451034003107444140702c1814001c2c150400c4681c08800300c0c608060390b0b0981c0303a200c1e994034144141c1e0000b00303080340c80b9401a1804d0056070009405401d0f45010300025000c4e000868040340303e445006401e10003441d02e408507400b04c403002e588088054a44002d00d800341e05502d00140c8000e101d14252000040000000d03610a201e03050203044000050040082130b1000502411103141c00001c0d034601c1098001071086812181d4101c000c40c4a405049640c101402500304c03881b40c6410a03440e07881e2540121056004414080003009480d41d240d49150440d241a140742080c600808a030190180d0660001450388a03941424a4026a039640304203440d9039513445940540c202010310301c1c0f03140c501c0c410404400450780aa4041a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 676124136 1250 676122886 676122901
    0x809030c09162f0a0c061b020405060a05031f050702060105150a090b270607021804031e0e03060f010501050f0c0109020307030620070507141c03031d0105 68
    0x250030700700c000040210a00ca44a40b0805002040c41e088011080b088281440f541d089500d44080c4032055841a400000c000740b4648101d40750008400c00e0307400c2c0688140240d08100107814081c050b20790100d00100c0c0482c42d81d40500180c100c404410341e8180716404540c141e407040e40d600030102015034120300c00401981e101e22040000d0905403105a560701c03001d0401c2500c1d01403036178001c1162640c0228002000b5000f50b1803603481c0240d0710000c07011030403009080186612964034025089400c0701c0340c129026801c0c020840e00244a803d048000c080525115441d40c080032852000040711f80c4021050ba08040c401590800842760019900390706110001e06240301c0e03c00d20000b03c03100040e491081910030751100505603401010b03180c00940d2820000045e060440700a24280d91214000e0f001c55085001c9401c6d00e5032000260144600e41400c851b005510810119004100000b225112207013400035400c402d44691030024007040c1400310b01000d440d80d032040101981c075040500910 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 676125386 1250 676124136 676124161
    0x10030b01050d021f1107080f1e0a0f0809040522080a02010e030705060a0c091226120f0106020a031d0117040602040501030c030204032a0b04030809030c09 68
    0x56820650750420001c0b1079101050520b100380020b0618403c4099030b151206500501c1c1c151104a07001c100c2d41c1d903d46030310300f090319202c030054140c031541d2010404030750002c0480c5034004000342e08030903111001440d88954111089100c41180e50100c00205211645803520406402c01c070030f000c82c00e121003222a0a51111003281002030510740c0c01042902074a4801d4011900c2c030390010f401d90784c60310810b1030465030720901a15074080103400d100301c0c0b04950380304400d6501201d00d81014003510f1402030b203074846404410000301880300b1518803480c41580d4981d0007881d504c1c1c0110300148051500038110f400c03c8030182c01400854000360142008280d000e00c000345501e44402e80180c004001d0348c0141d0b0049445502c07030f040f40311487c0c1044213024042e07000d401101ca081e2810703c408403c2007011412441103003c0140306418101c40103175176000301840100c203107074518060080103449116000c11741e0040e47c000c07a03a041c000a1101d26a05080c0800015508141c0d240d081505128041481c07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 676126636 1250 676125386 676125389
    0xf09120209091911030d0206040f24020313030f0e1e2b140d0f081003060e03071106040308041a09040c03060602060f1501051b060a021210030b01 64
    0x1040906030082000101c082c80104a810f5100b032882c011600a498580030700852482020b02c240074403460481c13038500220f12603100301d900c410403a80042c2070341e840600b0201d900000390030052002410f5401d07503485200541c0100061007842c940c607882450014060f07184e40104000f0070080300780001d965215940c1050101d600307040140f501c42070110204580c03200c1c0103550a200c0040c0814824201042c90401442600440d0002e14081301d4034855a1349183d40c0c0540c2000804650300100094071070006a40c209030131041013040140c5c0c039101c48003a40c0440309600001d810015446041100c403080300312000c102920550304141c90b68845040600442c8a511810b40030141d00700c1017222a4000caa55900c4010020060036400c140c00400510150140c080035200b03420103d90702c0c0083c0c0340e89903c01d1803100e03146800d801191004403126081004000d44000d0f98104d0400c02d103006000013881094401001622041490448022000050500300c10310b0358098050002c030740403d0301d050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 676127886 1250 676126636 676126639
    0x302042310030e03191103070807120e0d0b0603010b03060117010c11031e0421020901080115151704050c10180504050c0702030307140111041409180d02030304030f091202 75
    0x194651172003800343c5118003c00382c074500d40e0100058040070402040041d00203a070140c009003800b01d003082000e41d0000800781d04142d01c541000a203100090500b00055030001024001080580c02100424a800e07000e80040c03810328240c8480340300c5c1a0b001d11640c80c0e000b005240c6884805a40100e55841c2d20901c08050341c0c444a18036643d040902ca002150001c000600c80311050489200b2040b40d21003000000300d10450821000080b0002c0c14011039030705031140c0d000d20101920b81065005900100c03c4100f0a01019142c01e40060070328129070792103070340510094141000d6010420480c40005408001403000c542c80203081c000c0601004810360b00c054800084603200c031610b44046001e1444001d60502c0001441020018140319800e01026960000e000c040d644658441d01d170b00550103603442540c100214044a07181c006581c40c3c100d01c100c0c0c1e400c820580302203000380c2004105456240568000000e000415610082c207407500499450310801450520030080051003d800020703 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 676129136 1250 676127886 676127917
    0x10e071a0c150a0207151a09060109151e0801060207230a0b090a140f210a0b010609150906031e020313060501050301020c0d0f0302042310030e03 64
    0x2052050104090402c2820480e003469280c40d004028001a40c00a0001c07660304000d03001c08145011a401100085c440500c0c042c80804c1c0c011050104814004207139604100703889000160420800d90750281c40d00843e69840704e40f1030480d6080c540240d064160008001c806001006650750100c2c50000303603100c0300788540307200040c2d0a086115280f800300e4035910403002d420008502c110500101544031044d10100301e115510040b15481c81c0100c0391a58001a6403c0603101d03601c0c0032035192400c017120b900902900a080410310f0300d01005007800319031040903600103024040e000b03400440108034000141543c060040401400c01d01d503842030000341a1142d0300f4985c2004003a20300b1300ca44074080c81c2151030b450b200447c0c101071900c484040c0c0d0480e140100100d040e007010b000b26030b052412400144204405244e08849004409a25030700701682400040f80020340d4807500380d2001d41203054080701c4d1080408100201c0d01c81d075038940505180c050307501914140841551050a00407890 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 676130386 1250 676129136 676129147
    0xb09150f031903180513020301082b0507020a090e030307020f0a030c0b15041a130e0d300506090f07080105060a0201140c1e122403030703030c02010e071a 68
    0x200c40c0c0001150410340e4041307143c6c40005c00b103100b203074050340c12140340c481102c588440000703540e0380a05075842041500d40241c240d40c030b4054000c01c01031081d50b2000d0105a001c0c0d55901c00401210381d003071a40015500004140004c4550400a02824a000c0800380403c0030103035034050402400300d1002405e80801c600001c1410264100c82d010f10040030344103111403081c003140d0300a54040764105500c80d8401804000452440f44a8201d95240f240014003c08000f8541580e4a14507000307501007134071090180701c076030a02c10307940041800900300c004a8141801d0040040303008000702403040700e0030a98200441d040d030000d071043c1100c0090700c00c2c540d03c100c0440204d000d0407000070304802c003c00c0700090007034481c004d600a00340c00d00c0c2282da404c1c0c05100d20248040034460751800d8a4414010740c0030543c003000384400800c0c0103224401d100c0030050600040380c1035400144059011a50340c01c1c0c202031558081c015004110348080c0a8681e00b810203000952402c1214032803060804003241 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 676131636 1250 676130386 676130417
    0x14040b04060509040c050306090c090a0b06070c080a02031b0d030c03111608071d220b040809010311091c080c19120810030201050d0b09150f031903 65
    0x40701000c0d000161030500d4501e000d06042c4405000c03031141c03034004c0c41000001040c441001c01c118100d13100c014000c10b00c079103982e028840500740315000d0355072107d0100b240c040011008812900140ba07444080c0041500500405003401e850700c00700100d802040180d01d910b6079480ea611050359916040c400e041040606088505d066064000940f62003441a1080041c0f60b0400c82e004490b00d0b84221400702d61109000746d400500c680340644055016004108404100c050181501000e040e86076190200ba8613070105050040e203094400e40c0000581520039603141c09191480090040c1e46480c0c01c4002021a54481c0110044104140343c2100c080400c40008222180078940100700d407040284400c9111003c0d240707902c1160000640109949501d01a020580c89000d0810799001c0484c515001542d4940c058840d000145950340315409050f503491141e9805034070038012881c0310720445800d0041c90f80c00703111142d109a220011001e50a004083c40c844001c0d8140351072402040041c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 676132886 1250 676131636 676131641
    0xc160f0c0b040b131401020309100e1008060906031f090f0501020307030e250b030403233006040902030708011b09060309020a2903011d07020714040b04 67
    0x401140381c03410005800030390b883e1101c0c00b420b03071071034130001d000b0301c950380c0301c1c1a0015103155910450258006014010043c6094007165560300b203103040210341d051800b40003070b86900030f181e0101301144140e001d00c1b03003509082c0003065020034140c00404034059a00034020710621803034040880d10b41c0301c100c40d10400c40901c90602950f98410020341d04c9040198018002d0031062103001254840c6448401c96682d0648400c0401c2d40e90050fa001c030541440205020b0b035000500a90a104000244003a800b01c03846003100b114052a85241d2180e865889060164070051241d80180000040001d0f51101d440c00341d45c0c104204840c0001c1160307092003c01d052066030b5003c1145035203040c031014003a10302035051081c1902165100c5060b107440b10003e40403140c40c81c0d0b01940149251809001c88220b6584e8503003504c480903820a504002030407003000302da009800c401500b01c9c21200c149201c6c402088400d070031080ca40068a49141030070794000860507180e451360300c5a0786540c00304000b516142d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 676134136 1250 676132886 676132889
    0xc050d050f2401020a0f0c030303181703060409021305090f0d020312270c091e07080408190908010e030a080403030b01090f0306021c050c090904020406080a05060109050c160f0c 78
    0x104011691400c075040000499071f49220a6011a00f4540345424402007011f0300388186070311400c0d01d40b800e51800c0142c15181c2004100e00c0e00103a8552202c07026a0b02c0c25141c0100c00307507081003c03135180381100d2014144440c00c07540c0400755000c0540c0c03030721080d0044117031100e40c15481e00304892a44e4020342c0000701e0b020f6900d0759800a1401a0320922148041411030100505613960001502c0b00604031800c0d4802ca500404400728400115903c544110300d000c0c0c0290180250300d0400d042c09044104040082e2030242c0801c00306c0301c0820240c1420300507140743c0d004103405507051000b2181e015105a000800c010201a680c170310710b481c542c0c0580d490001402d09050080b0000e03440b8076001c4025802020304c0701d44204070300f442122984c0c2e40e000e150700c540c401c21289814901954148108004040c20480c0e0003921804c0100d040c890400400d600180510018607195251554200440e2405030030103441410401c1f140b22200c0405001504543d808200c000390400e81d401c01e0020741003203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 676135386 1250 676134136 676134143
    0x70602271c0203210c060709030c03060506040603020303210609040b01060c06090b01230f01050409090f0803131202160e0a0216110a0503031303240c050d050f2401020a 74
    0x1400380d4901361030103c1c0160000d44600c0381101c082d40c0301c0c000103451030301c110322005103c0810700500340b0028080307812143e00800050000300d503098032a070020703055410000f44800001003090030344104a0307010100c19000b00c0b081d11240f02070b003000d44803000e6802050152109000501254504100e219803022023801d401c80403890341561a0241c641d42c5145007040740001e01140e1100e070000b890003501501800740140c5400f4941890002d014001e44804082036502103807003600d1101141061000f9441980640c2c0e1500ca2200c4d140340c8441c3c860074183c1c0020031940911115035007881c51140a40c181c616001452040c0e9a82d1450840688070324042c1c29844a5002000e104200d440641180910021103400c4d2140352248141aa207000341000301e2080000b0503020000301c0c00c030051042e00340c040c10421000381e0002e40000750607208081d020f000001d0000840780c030500030318030840b03800010000d8031481d64240118001e9003230500020a42d40c840b401c500120480c1c0c0208049058140d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 676136636 1250 676135386 676135423
    0x160b042108040305150105270c0f130f080304030b01030813080a0f150b0604050d140a0305040f051f35091005070c06020d060b070602271c0203 63
    0xf03c0786851a11000320100700c42c41d0410300800447d1a29080040010701c0c180380c3d0080c4c0b1401e620350801c0c41150400b503c40529040f040208501d05070111300148232401101c81400d082c0c921b864031048400c01190310101c42900140001c1c000a804001c0c45411250007901c019240c00b030011268040c0e4075250702246052040d010140f04001140c60030118250185071402e00043d116103022041d030380c0007503035580c0c45441008203004528040c282d50301e005018210f0000351030b00960b1000c1ca80012a04190007050022504210651480da0f04001070013041d140240d94008080ea1560351610380c1c0074401c140001c030001c0000090104101245030484c0d90500d8480384078501e40b804901c1811b41d5444068007410f1490282240140169030040c107030795803105190846522020006d4018413040300d0340b23603151280001d440d021a40503000107030103800010b9842e40e0344441c2c20448011101c802419817564051100c680d90b404118004040c29585616181002072001138202000300340341c0f140f54003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 676137886 1250 676136636 676136639
    0x60411180f092508070e131d0604050c040c050301030308040609050102160c0806040f14031603030b3109050703060207050705101407060c02011803020d02160b04210804 74
    0x201d2040f40940d0400450800d0b03100c10800c05089036286421100d05010450030900c01c031041c10100801d4200c1800f40341700203800c00e01600003418806580d41f0914080d44800c00380428494240071f4440403100443e070407c140e2254072000740250105110141c240f02d000310002d020311207503030000341c04039a0080007150f5400304e4190706250002c2d0305406448501403102c0208000d44000750181c020342c0c0102a2000d018100e50707030442824000550003c00c0d000500036218003015000001482911070f860102d558642d0b00d060000e00e00410203981c4900d0302d11103c9403021510150119072000c1c1303001001c0ba030550503003001c0d0b203440960340c40202041e10001d07001003440310105824041ea8021502d405480303805282c200c61079488441e0340340361180c0400401c0c0005450f507020f03003603003d8580004600d2612040c0f9601a1150340b000c1a8090380005580d1902c0940c18003c45c1c200e15044468a26083e051031005096809603005c0d04020780f030a0300360360b1120928010603615441d440030015a803035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 676139136 1250 676137886 676137901
    0x1180c0521011701060302030c04020c1011190201021305040e010e15010509010e0915041106130f0f0803160206070c1202091b0306010c020109050a0f0509060411180f09 74
    0x40d50920455400f4980b821a0803858030040c001c800849400400401040c6088802c000c020350101d52400110b00c11800003c02c0c4060b14080c00d0412403903040c03500d846000007003600004146079114042164410040c2d00840d1610302140740559105403400200c0f82d0f10340d03003024010a01c80d40c042d5803d2040d01e02c907070382218051181d24103880059405070400d9030b07508522a00800180d490360b0a41d0420080b115a1481f2900d000d039005004561841c891607a800c0441d002c0d5102c000503084407a20742809101c51461040780030010f050900156031424905803140340c0301d018805522009103586044241950340d1682038950700f68200c81400200d960f5100080d00040a5030320480c0180d440b480040c41c00c58440b43d1030303031083c41e61000403071035036480000450b45800d208800b241407080c078000c041603075204c1020703000113020007600b400344bc18140000c00c040180e0040269210fa414100f940981d800e1f81c0090398141d0301221688500d00c101440040c901d2340c1d0004900d40c10251010820032035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 676140386 1250 676139136 676139197
    0x190f1203200c160302011407020609040203040302150f01060f030914011d010e060402150a11010c02150c030405150c0c1002090123090d0f0501050411100801180c05 72
    0x21182c01004688000c450320070800481c40d514400a4089107098403918031035605070008200342840141594038108a030f4000030200d80054400740d0050344680c0c00034a00e43d05001156822207104200c1200c0e6614002d4024100c10151401008141d05d80d6917103800c000d46480c008402c900c080d0300a000c00c0c8590b02400a6580b11800d08858a60825124085a040115416001d690082c100145410b60200d8100036a40482d400e442041140181408185400c0c030500c40324030507039406400000d140d66400800580040c040f00d0240da020403d11000400000f090740300390030207000081c020703503d2100c10002805909074510b4240604400700304041038a82c02054038641c03d8032507000700305100020381300761441d015a000e050300301008291b906141101c05684003074460560698031100e9a0303513450030f40750144d4080b6a03101d03408942d00c1d15440c06840c00c030b28001c9907142801c03080d0300d40310018115824900d1402e84540d03840f100148140d10400c212444901d1310b06c40c82980303580000c0300511 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 676141636 1250 676140386 676140397
    0x30609051501081807032a030305190207080a0b06030f03070605042d080d061d0a0b01050a0801120218090706200309090a021608040602190f120320 65
    0x1d610440011304860103500144065141c40000b00445429507030381d03007451141d00030743c21052244852110303110b034410400c00c40a14483e40e5501e8840f4124086150504800d031080e0b020341d00b11000070300282d5070009d6005044c1d41c01c80c6403c001615144003103400d051041160941f18000010540140000740d042540035510548010701d45184410200c05501204140c800c90f00e6500e00001c40400d1039200588a0400360030000103645560b8400502d078411044c14040c0001c0d48030f0100064220f481c41040f407a90401c0c01c1043c074284c00c070f40004102d240140140f10a10910508035419900c170100c091284109041003030726503081240c24250350751040c1c4242c400194004d04000380308041116841840d00741c0b03a00840c2890ba000040000135507004040f4880b07140d0034840310114609000300b4484050007040c942c0d54585c02c01400030b040421035840700459a5040b450b00001070315800c90740c09020b41015801c08000c0d5514011006040c802e180f0072403052414107185840c2c48414000e08 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 676142886 1250 676141636 676141639
    0xa1104121203050702030a080a1d0a020a0503060105060d0e120a020f01050c0c07170111121f180e16060e03071d16050903030403030c020f030c0a050f010306090515 72
    0x51038040ca10403403d81e041192910b005030814444001e4950240c0b010540000c070441012940a1101d1814140c0c80140c10101307140791711800440702541440f48454014141c01d501078010780d0704000c046480d901c15481d2680e801c694071300c145003c007841400800109201174000725a10688440001d5845407800400c034890751a003804514000c0740030b0115980f400454003c0c101d070900c1d04062591032241c4080820b419502e80e550702517032451403401440b00f03a420300840802c6048c100e5a0890f008011419a6100018800b0138491003080f040d0440b01c4035513501000c18480080340c80e20741414148030250403480400b07900440d0041e000110300ca004d02051b000c64150540d28007113940c0040c0c0550711044500c108a01040501c1c03407400d0027499214050903c10b180950140c08a8610b0340a43d0056000440c030848040c1140b90581208444000803030060141c416070300d0000b403891505110341c6108041d02100c505841c1d0098105030000e040100d0704014a00e00512162101005140c100707 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 676144136 1250 676142886 676142903
    0x210203010b04060806071133011e050603060f1201020c0d18050d02060f030405030912010b030615011101090b0a0e060709050906012c0109050d020906090a110412 71
    0x101c449051501c940c004030748a0b04020308035a116460242e90040c0d043d441425140200c40d01e010003400c0c4480711005000c002c018440c1104440107841d1794100341a0440c0b500c05c1c1e00301c0301c00c2240c189047c580c0b20642d542128800e55030389035140084d00507486010740725085030140702d503d1060f0006501500c104503054084e01e80c1c210088004032207409581500f01c2e240610200c1c24045ea0a1881d881c0d4039152001c2c140b40d1a00c3d44440303c50000d50070495080341c095100281c0c040300c5050404160a0607179a14000380316080c0f0784000030352a05001811103000400d01030301c0010704d80c4a0602e840003900158020030050385d16062601a0b24021190a0000e034200a04003141c10000140c180c8500c0c069650032051a040008109070310074007500090400034507407030300190b1200c5001d0380c00100e51410f00c3c0c00e000c00381e040005403055886c0d510062003100f0208812015894100c94580d0102c4102c5010070b09a40c1c0b051402300400241002141e0324102040c0414240c0b0600720703086095000e07041c030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 676145386 1250 676144136 676144151
    0x2040527010b090a1401020a020622060801060f0f02011d16050612040b131e0302160f050f13060303050a08010b13030b060a05090c120f0f07140421020301 68
    0x6906540c81440c072225049094294108501075440401c0b45c41e0300380500c183c1d03981c20050340000b4003a0300722081c0d5510444054010320072021b81d020300c5c5001407030f00e070030144040c0d8174207480600b845902c1050041440f002c00d00c06070604d4403c0d4000c40f00d60b040c00c0c4033414007010344c051280d518203a1a504c0c0840c2d1040c0e010115007880d0120030b5802d0b6072401001f03a02940e0720396484c017140c010042c1600107070a40710055980040c6145403000c40e10403808440f00076214041c10f00a191400e0500d51038070340405801c1c20b01907109012005404d80b101035483d02c03003500102e00858055148280706a0074140380c04004400c15502000400070a4500d41d0388414a90b00c460010340300380725140c02e60640132401401040010f9102c0c800c0c0b94440700c004c0010721207039501e5000c01c0c403040080701c0500240c4400995856a1402e0114590708819020405011807406070f000d40040d8401a000368180319400310300c61090354000c021140580340b1142c2d0004403001c00e14031006001c1890a08900c80d5003401c44 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 676146636 1250 676145386 676145399
    0x9171317010207021c050a022115060306070f090306060806011e120201120207170d0e06011d09030408030c160b1c0f060b16230d120204052701 63
    0x81d9035a654004101400c0c0340c03a071054802d82c04205c160b00b142c050003034a800c1130160b07641024440140780f0303c114918146150701c92850410301d0442102d0110200d0390148000303070b20000784203076109142d410321a140f9207403040140d0b11800c0c65440109020300f041000300b00c1c0d000c0451070b5812034507241026449103429030502c898094260080040054441c140b007405988070302894056a03800c076000628202164a40c0303004003000d5441075014401c0041c0d29180d05034a0b01c11520642001c001515040d4107000030115480d61552540d8040c003000008aa2000010300c1194000c00682040701e65944074452156180d1082e40c0212404004101c400507481501c030b030444207050b40c0c50905d00310040045010000030f11110b503100c003580e070ba94103001c1488020343c80104400303141040b040940b4203403464803040703403000d1041c00d403960301002240d008003682c000742c05030060241c1e00782911511001c40c0500000c1c0115400350350701411038058032080d0414a0a40c10102c07500b0100c1c1d06440e80c071001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 676147886 1250 676146636 676146641
    0x120507150f11160c140904081b070806060306070306060f0f02070f0303081f12080304020d332d0e0106260706050d0917131701 56
    0x2500540854446045640c0340c506507803203116040c20503a03000480c240041050452600848101920001c100441c1010300c8001d2506000420716455040d00040341d00b000304160780f00c06400101226804548221040c030194682d0500c0c1e50610300b10b405290351840c52995541d019201c0314040e028580200d481d842c0b0038080c0c04240d800f030b40c4640300f643d00e42010490302206a481d071042180203c42000c01d21920760300701030300254020b665407801d17810000c042d5425a030802c803044900c200e000004001e002c121581004050342c002c1803041d20303a03607507001003188001706c04070003000e1885030304002d4040c01c09209131082c407003010f1898009030b020400c2e0080840c2e800c02d1800c0c02c4000c80c0920310740f004c2d8100c039801c400e52150410104100031700388802802e6900e21b4120b40107480b94085c20102c03620300b0487d80f800c2d100283c0000c0ca82640703404030241540c49220740c0000340039180c0d110b00c414400d800d400c4a0707050800f841016950b0003920412005200c00e801030340701154000100024502050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 676149136 1250 676147886 676147897
    0x3030e09060901060c03110607210b030604290c0a1101090c0b1c02040801020c12070c03030509030a020d030809011503021c140f100509011e0b0a05031204031205 71
    0x141c5441c226908000c001e445207040c80c03604a01b001191641f400e000350040c441c031800751040da00e413106000000f02441c2e011526009142a250340360038900d2185542c005202600250003111080c0303855101010508501000c040410b0b0290641d07060120310324041c030081c07030341c01e265a07500303005000b076840c14a099414109001d0018440d10200b0720034400d0700c20052100240d1500c845200580907480001680c0203135115643d00d07540420704404041042c420310a05141c0001128940601c5076a012103001d101e000280070414045180c07034040d03d081120043d80c0d90000c21042d0100740c1450000c05605044402e03441550800a500200c02c11704080a4180c03540280088000e005800c200051707141e14400666072401d0040304840aa2800e0000340300c4011505d018115502d0340c80400426900090080d203e9680340c82007440386154071100d4030420f101c0708800428007444000008140200f90f80060742c0c507000c0c0b2100003482084e000010700880380b1608003810f012440810540b1180541e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 676150386 1250 676149136 676149139
    0x503040c0302060306130e01051503070602100507050d0207150b030d0819091b0509071d10030605060a0908160b071419081b030f0d0203090709050405030403030e0906 73
    0x4400040c00186002805145c0c8040b001d8403592410300070303400240c1a1014000143c0e00c80e5910410b2005040d96001da10650354010381c0244046454590000d40d114014401c3c150469550808601e08a2240040710500f100d00101551280201d0030305a4003460700e00b21108080c1d24004014101d4140411540c0880d0020749440e450b41c0e40701500f4400300e01d21b600c444801c407942d40740c0400c00502840080524011400314580c0b1050070b1034184012403002400400900030407141c80320107031040b0a9010100a0240c0c1c007070b20190b82c049400d4004c0c1005401c520b9100c40003007035150300325910403500304c1115640011900c0c007101c0d000f00781901000d240030b403055040d410000d0b0070110361181c40e01840714a1040444001e1440e20718400c0f9041107140d8100d0b0075400002d040c11860080c2d4809100d802c0b07005020754900400b41020011707a11403041c03203504490300400040c1d902c203402e20060004003541c0c1c105121910380340c40c0640e1039a105000440119280c41414100346c20408007151040c1d13070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 676151636 1250 676150386 676150403
    0x71806090603050c0702040908121311010521010b070203070f06050f030c0d0f02071101080705090d060204090204060215010e010609030b0423061006020c0603041211070e0412050304 80
    0x420000b240078010080821450354000c01c04500142c5580c840e08044501a001481d02d501d01c041d2003801e010f1010306000f22541c00a49064045040815007440ba4002420055500c0104000401e041d0441c4440ea0f528640041c00000319498150700415940e03100301c040d201c0180d00c5000e0a101c0002c24040c180000754144086105400c903100115042145001c01c84e080114040c8040c040e102c16003c0341c2d040d190045850707801c01800d258100c804100c24204170500b440d08000007010ba004000300d0390700c130300711002c2d010007403082990444000d0719001000f550354a844560103595400b0803c20403400c540d040300005403001807a121a81030703c09a0740d689802c0351854840c440301c03007005013064030f5409142d1b405503180b15803842c50654801030b8502800b641e2421103106503140032a40d00040564106502c130350020b070344440031294840d520010383c8400c11480c42e03040300c014100c9150401c1a2040001c040f0b110800341401c40e100d14424a840100ca0910401c103c4241c081130750002d05401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 676152886 1250 676151636 676151639
    0x6051611070618080f03040617060102060a0b010c020a080601050102070b2d27031006050d080a09080303040b01080106051c030e0310090b040203010e030a080a11070c0e07180609 78
    0xd10a1442425400d0b440030800000e40c0c848150f5400c00d034170403040722243e500008042040381d03000b989007410081800c11307100c8140342200010392038060040a00701c1e030070740c2d5142c0161240e000d41800c40d6626009803140b20f2454440b44841d6440000307004042c0035116460380010030309202000c80d40000040705440680b4000ba800304099010b00b032a949808a1060100040c08a080c25814401c060300244d11a804072110303040c5400c2a03904000d050381241062024840c5403686210340c2c00e02680440007540d9103064502c01c4411134803541042c00c4034000007050100340030031160543e06031407060008000c2a5079840070888c114205400c4940842d603a4481c0b2400f190044403d0600070310080c0035030b8903040075075100301c00f114902c00046900d44203707001c4c8415810f0903c80d0000d6001460020351409900c0b80000d07040c1800148100d80003510740c42c115180400d05001d41c3c5149600c2404429116250109201450785c100c0c0c0c002c000804000e280111046803640c11001c4404035181e4a843c04d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 676154136 1250 676152886 676152899
    0xc010608150106300c0c03140406090e0604020d050106020a1101020c01140315030304170c03030702010c0b0c0405030111041d01030b0118020403080a210e030d0f180605161107 77
    0x70014030315074030491640070003940c4c0d5129207000d0f5908030071165641c1090790209180250510b410018415940101408203001c0c4540103d031078425180381901c1c00940e0764680707000601a1203005a610511801c0c1000001c0c00d81d0005004518148100c030007001c2c000750719004a98400010f0840b030f0004001d0f070000400400c00500a54200c040501000c00804c2208040307490756000c1e501410b2102807003441e042403407009014034081d401044025618111280d000246844119500500748581000c007240342d0380000e804480c000d01d0050000c1c0704203a121410b000301c60b0014410680d04c1c40c10550001850b006852041d41038076401f28440c80e03140d0802c0170350220105103400a00700c4550030403021020a20f848040c0580160a13580c01520b14040c1c02142241c2c1000845200382500301a4011608900441903d03000c232139501c00060782018014110000d8407044803046d12407444a8407200c103100c5650090342c4542c55018400c41c0100001038101ca44140343d6000b8078013500259800c1c03119 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 676155386 1250 676154136 676154177
    0x702010e0d140109030e030f01050f0a2307210203160e04140a200403152d06030c082b02030c060901050f070e100c170c010608150106 59
    0x14a000b4642c0500d0800c6071500345003121058403054011480080c565542480d08010b0034008020180080c042400d2005003c0e0030f0352005440c12694a4447e0001e1601e01c1e000c00c02c0c081c1220803d00c4004450510305409800f80300460028110b0640c203825034004240c0d940200d0303005501103940030102200c01101100c180c02190300469000ea00ea0350321a01400c06040024000c0c8810a0009240310719000914000c88a0010021748144c0a200800100e011004100101c0503010700c0401c4030032004d100101c2118041c25100500d06030b5030700c841d1703400f030b01948200b060b01c3c071490b42004025207600c0c1081d0b4581080d0310110142c0100605000c85041c00b129900b415000313801180c1c204081c03186428103001088910180c180c0d074a400300f2460204008081d5000304440c02c2c68a849800710740804c139074000100d0840c0c140b04401191800308401c081c0905c2c180a1f50a5a0f6620b911401600b20302800513441038101910078040c0c000840107a4152b864100d440c0c54035042032100448414508 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 676156636 1250 676155386 676155409
    0x2030a0605090705060a0513120506180102040513020a020106050102010501050a0b070f050303091014043f0306050a0519030320070303030b12060403091809140c090901020702010e 79
    0x4680203c00d40010306840b0100a403402c2c40964683c00d4990040314010501c1080a81c02140100e400c10790f0faa01188002c22540e400840c00c1141400390603031aa0058003910981e4801504044a0880010f101c030065010380308a100a5009001c00c550f01c1c0012400c0c0c070f00a000d060740c4030100e04400c00603801f814004040b42032042044004658950716050700316001111991096042040d00c204070241034824607204440600c040541410591605841003084a00100074400d00c0d20680301c0100c541002c420040e100e9240220285180842c000c0180c0142c0c0f20702405220380f14400300b0a4605034081450b1380448403910ba00291030354030121180c203111031080c1c00c80e510f100c9480b142c2c2d4405001000240d1b000e83c0340400c044c50b4407400c1c0301d6491700b205c0540c0c5061b00300e10140000280c0c080340701411554880302d0010900550b4407150001d0108480060a0342c185503030040aa21000c504004013100c02c03030f022403240d0f8400003000e00303034840d1400080c0082d10410b0318a100b032804400515 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 676157886 1250 676156636 676156651
    0x8030a110106031a0f070507030c020f0d020a060f0f020109211701030b16050c100c0e04060f15020f06130c180b090601030b1f020a0b10150c02030a0605 67
    0x4a441c0c0da61036180f9011000c9030081c0c0b200d804c40c02081114a06806116004111490a14500031031a00c00522048007070034001d1240102480c80344443c1d44035007544481c07a4005220400c2107958840240980c01c0800b00d8202003030401b0007000c50b1078010310603411407581220000c0840075041c007554407269001c114801c18403100904100d040303a103101c00c0a01030b40c420f802071146806e001443c10340554840e0310722810804104544d00d4588000709115040070081040440c42040c03040c0180d50320b060159625410038640341001400450034141c200c203e40390212003800070440300c2e10884e2604a244500c80341940030300081580c111107541da0000081c050f810380c201b01038991040340240000d1001ca990f2280d1541c0714242c540c034000d040143c00120900381044008007190104d24091a410400742c074028071403200c103803041e00030700401841c1039000c606008a850f0620b205210504036020b00c1e03201e81940c40d06140c40602910307004680d01c1c3c0080c01080d901916690381005844018203c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 676159136 1250 676157886 676157891
    0x30901020c0d02030a020c04020a120f0612050109060c0c03021e1c020102030601120506101b020603130510020f0d051306060605070317011406160209010f08150108030a1101 76
    0x59501d010240805014400d10398003460303545030740100c02451f0411000140d40724910400c8105a416040368410b25450a85100030908003030a40c641d4004000e980e008101103100b0160000400c0010b611500c0c1c0383e44200300422030014151070888102002c0d20700180940c1c81a030035205401e2038001c400c42140050403c84022140b00f05000c003204a11002d5240580e4001c0240070311903800541084050411800130085840e080c00000c1c0c0d04800c0010705018031034001c00300344e010f803181c0c0740300c002954025003c1a034a050034002d0075038102911030706561034002c9014141220282c2d0088480c20b0b41020909801c25201519401c020300000d49402490000007046600051a500600004149949490392030305000e0802600d22440e000600407281d03422801807010f00740c450f180980115054413115284c441540d000c094040b05600082d41c0010004000507140c050030000d2001d036088a0b081d0707988107004891f4034610300e06c02c0c0150076903604140300700c21402e132140b80346000586480001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 676160386 1250 676159136 676159147
    0xe191509020d1b020304090902010509150406091d1501120603081b122d070501051806060a0501051c14060118321f08070c031403090102 60
    0x50a060442a40c400424a034001c100d03140d8803000d074403862241c0c0c8180c54101c01c0c2d600401100a40720320517402580600c6559551030b20039644602e089d148001c4010740080407034586028041400c1d08513101b0503000440d00f8801140c1900c40380c041c1044031040400048641e121280b6590700c9140145950703040160036034496031803007014004d010007075000c0e01605030340e503607042d89050a0860005071410254019298162003444907400c49a034418003442d1142d1480c3d44041400d200021880004007801011468000b8801306510450240b5805003c90a41d1041d201c03919840740c804480480e03005041100401055000318024900c805043c80c40c540282c0c1c4c44017040e0226450b00804201d01c0d90008104811542c002c0e01e40360f02d6200c8101c01c84191842c0c001c290070b4040b80c801e01c203281c00807500b01602e105490380305c2191844000500c00711100d41000512107400040c091020009624040800c24490017240400c030a42c0d016610174010941c018862146984054040800380d9400c008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 676161636 1250 676160386 676160411
    0xc050307180b0f0d20060708030f0a06030f03020102040801180f031d0a03050c1003020c03180109030609150b12191a07090e011401050304060f0905340e19 68
    0x100c6004c401e00c03032015624082c1c1c11410060303640c903500d282180252420042da50102c2d0b2803c064179806010300c0c04c0b10615649014250f006030466600080c2000c05010350340c020940c0640251065071100d1008100320316996090800748582d086019006201c0844008042445141520b480c01134205100ca0703600c1a50010803031000301580261080d0b0005416640e003481c2c08503040c40005424a0f00b0b44c1440341c0b241029441c0d108180b0006032004000000c905a070b401031445000854200c181088144224200354000d07028003603c04018900e410170160765482c001c603c0825040400300200200c0d40d21041034080070014400540fa45017241d444042d8069919005c00d10407603c56a685007070318078141143c14000411382205500e41c002c08003029090341e10009480d0b105030400f4011a503082907107040c00003050305540261030380c060082c1d008050140220356041240c900001c503140b501a60b01e80213001c80740c5000d20068072070a0004100c40020f4602003034048182046d00065032002e200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 676162886 1250 676161636 676161649
    0x50906090d06110c010b0a0803030f01050108091903090e0901060303050910030b060408010603050d110c0904031205010b1809010503030a1107090f0527060105010f1103030103050106030c050307180b0f 88
    0x30200f03da61b45400e00d880c428203040e204800241940310044d802c0d0308141900c0d0350030200502600d81000681d40c0050201c5c3d01c2081020080c3d10003d42580b80344d0454140100818600c3c001e050381c0c440000041016584144240070840e50166034050074034889408014401100b118514109038407035641591030381d04c0c20000e1005081d00800051601d10390b10700203050024500c2010103200340002825180c4001050010b113542040765409520f649034502a200500c0c50510400c0381031904002003030384a4041c0040040070404428041c3c010b098200f080f0240d6424051075416030424403420550502a42e042c900d02200b100640745440d1320b98a03220f04984189200e11410742e03e4a05010400540702e03011075101d00d910b01d4080c410300141125564500c810721540741003007148040f8072003203032080100b8495a0302e400140c0384e070795a490900314080c0c10305020030f45901d1681c02c0001050700d00021420119903404451042c0345c040e480c82c4a0003000c1d0540800d070003040c40300725031705030790340702c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 676164136 1250 676162886 676162897
    0x32a030d060b04050103200f0f0c0d030e060a111e0f120f010b070b041b080f030705010c0f1d0a2c060102010506010c08030402040b100c03020d050906090d0611 70
    0x5600300f511185800c00040036202a2204000300c0840c0041c880c143c144030208580d61a020b9603141c1c3ea40f070b43c46803a10310310f41c4a03241c1c08680b28010415040016681600031402c001e00305011600d15071181081c01045400980c0075428449003000a1140039000301d03c210440c40615103880d0810f0503080b05042d2692024180e41e030350384881d07010841d080228440c0c25014000030480b49007042c032695951126144041e0020b400c003207510074640442c0900039440c0700030b0034401c070555034480414039010743e480d00f014004540650a2012114580e0303c5008954100141c1d0344d50320316001024803032103c1e501040b0340d0f032070f4100302c495a01050040c0d01c2c0e1114011560405110900ca641d012401260320700c003c0d100e58110390510b824803601e60790058101c84942e030405081a607075100c62001600409040c207001d40c000c0c05e552a011602e03500140581000c60180c1c080e02e4146944030380440f0a4480c050031140e002e2014404a541407d000010f001841e2107004001415071515500c10440d4124 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 676165386 1250 676164136 676164149
    0x50f06271317030718030b0103110d2004110306090c0d06030b10090c0c0507050f2413060c020a090504060f060807080106120b010905190504080a0908032a030d06 71
    0x20a204c12035134085601c0c181d807159074580110f5a8250358480001d010184800761050112800d091401c0d5100c40e0400c10556218039080007020703c1c100031540300a10540903d100d0382c9000c981030340010007003048038803500004100c0c40355580d442c4201c4240c1c0c0c1084001103401c0c1d80d144000f0001401c03c1044600400034040c050f001c1070314142520081d140011070090401034226000b00000f88000303020030550340222a81d56000c0c4170440804d100c02c6143d48c0c80c01005500e2882c14000c13000c6d0200400031460300c03d40c04170016031640130648002403500c5000390400b8200c1000c0107120815440250461711a84001c035581c602c0740c04c11002d640701034200c0c1c03903250004841084110424407400c0000d1808540e40e541d44111521400c528000c14841d01046948490000708142d440e1000e2074000c15069504010300c4c2802c0c20034076020340082820501007500c023000804e03245070000075240d249009071480c03035042e42c1d0300844c2e051018445000700c2551005102411301c0495074040e100203400c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 676166636 1250 676165386 676165433
    0x7060504031d1e1203120c070b010e090606060307050904140709080106050f060d060f090506030c0a080c210a0317060906030a030305100306020301030501050f062713 73
    0x40b812400080180300c082d8148100c15012149004400422a0165810040f100d080c403c1c5100707a9514103501c111110699542c16800400c145003036030b030000d40341c00c5006240900350b580c1c8a05c12400000e000f6035034084554090000224685400030055501c00c0161415508120101d0081800da40d0031025000d6600b8400c41041030041c0d005040700c000700344540c000c0c00202d00c0d084c00700320304800040c035540c05101e00080100ea040c00e06e400c6a4001c00c10241d0070085140c3d00c00b01d4030000c103400da5100d4131a000380c0032006414500f04444105550140c40584800102d201c00c201480d0762540192040600300c1140d800c2e2034005010f00d600c2e05010b03032106c1c07003a219200441b0498103802000c091107107441e5424450203440000d111000c031645801c000031a03448000c40300380c880c11240d1000300014000400407082000c1904858001c880c40072081c9495126079017006140b0b0364100c0b03058414805074424410024140c071031113802c142c00e040c00702d10000c2d25072102011150b01101c113407034012 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 676167886 1250 676166636 676166657
    0x6050d080f071e0302100509061608100b03100609081b190503060c0a020115031211030415120e06240f0405070e1905032a030718060506090a031202030706050403 71
    0xf890780c040c03994800c10782005095540381400152b8141c8004200d0101004031400000d80305c544e0202c0454080c04000502030344900d40210703045410704071400b990000030f1641c5400210800300240c4801e011900740c050042c2c82c49a10144a0640d003090301000c980580410300003495101808001e0046156000341643c8030303842c4a000c1e0a41d10281c0d146070940c0c201d000200007091401d0a44501e26036189041880710b840c03802154a18000da40042c000208407455502c81b2035042054410716103c1d241043c400041c89a000c1c1c3d450310021558034800784001c03c40449030024000041e1040c0000400d640740c154444800f103412200222101c030003041581800d0309c2c80f840c3c0f0b08207140d0b0344185000700c0e090050074400800e40300c02c42210301103034040124084425600c001100181000d8001d021940c1130b0f5038404100290040c2028030809036458030101044a05002080f52003d007009030000c2d0441d0b185580e4940744212801d595802c601041c4058000981d0764000c45000314020b9072200b4607007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 676169136 1250 676167886 676167913
    0x30906150b030604110c0d0305190510050901061e120e0303010f0f0e130f03030617060f090d090e0402031603060c0906171f08010c02060a06050d080f071e0302 70
    0x1107003006025030000c402802a103503200ba0000724038081c540140b501027000c0d03c1d00a0301c281198100e4405040a90800040206000400500004030780c421206400b40d641d882c901030320754008516214a035800c2c201c4620300c0c414010200d00d038420800450000310340555036034a5055130000e070020417030389140e500700700482031307840d01b04102410316010882018200b051142c0c17000c0c40300120003800c003031044801100341800390348160001c0000d40c130300210781c1800c221a41d0700c0b03a0781115000c0c0030b08519008582403103000550981c002105803113104140d4281001c0d0070801400078401c981c503104e031400320314940240340b500c040254800c01d000714041030844000f40411034160081e10401c10966660800380a402091130380200c83c2e24242100440c44034454018206542c11928281d807d0540d4442e02c0e590020b8a41c0c400c1921035000c100c1c180d143c0c002c020225804140144c8224000c0c45240c517600005d600034002ca92013a4508440034180c10310743c0708085c0d05a44298003580008007010300d0b5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 676170386 1250 676169136 676169141
    0xa0308072f0c040b09010314030915090108090607120906020f0703020304080c1e2106100807050307030f0b07030603020310090210080108060c090f040f05012d06030906150b030604 79
    0x382080f10240041d254442c0070038091072052001602c000e10821a442482e201030045034400a4050080d00400c0c9040e81e48504591140c22041d0026120000003002e150012802e10301441c09561001800783d54440344074041c04d014682074079903903070030010104100e0326034004080d002e10a40145440c0c910348001141040c29030502d05004403000c2c1c0f500302801d4109803400c0444041124000443e055200041c44000e83c1e450701c50207e84130389401c1c031209006031a01c0004464000046880454541090580361480347c03000800864880c0e030300c1000030b800344103c580d004906190004010340c0c2d0f80c0000f4a815020032040c41a00c0e5900c80920a508103446a00b0203000141081c0180f540360050960b90741130010117a101d4100d01040404840c0d6441310b0b40c1218042c001c1042c00040f10449201009143c00e20070404800d00e10510807600140c91811050f00900102e00d0755a4545400b005401900d158481103d000e0b1f52600709244400700c01848802401101c00c0c005d840345050010b002c01c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 676171636 1250 676170386 676170403
    0xf04080f0d090608060a0b0c16030b0a0605010201020405030d030207020d1502030f01061e030e01020d290108040506070e1201091401180213092619110a0308072f 71
    0x1001308040030400c0903110300d01c0a0741101c41c000843ca82d90500002154140030218036400700403280709000200303020f451100349000701c5208808010781d580c2c80005a08034070480c804d1a4040e0490342542c100b01c0c0c007a50282031224000b030266180364003a940d41030703016224a06000c0c1425404010301c00c03030502d203880303060242015040045240e07481a84d1114034520441c511000c0507202c0510941440f030a40640e544010520010320100d15400222408078495922400001640301c2081c00c080d881201d1460140b0b400c40701900c0c9a407210f0303004a80e00365948800076000710035035007105c03280381c800d1148110707481c000e040c00c2c003080800400850948503c003011002c00709004c136090000d80d13185031004044d072030b0300540082c04040b1b52130407901040500b01d03c81614084007408000c1d00340d103800105170310030041c4280090310320001800d0b112410403184581003640480710b1500040d00070750703919800002e641801c41494425200d5039580012403810700c4060302014114403030000c0100714105 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 676172886 1250 676171636 676171649
    0xd0609031b3918050703090b0a110708071208010806010f170a0f030908190f0602030613020c0d0210020c060c0a09090212061f02120f04080f0d09 64
    0x40303009a612121201d181d07100c031518003110040d00e42c10703242c00307101032005942d480c0d5400b058006a80d04003480400d00306141c1010828244400200001d01c248185154243d1002400384503840b41c400b42402000500300421003400108584d0300894a001d0261417140c2c404c80c4028404030092170000d151071b2060b88a003149a00103c0180618210b6050000a40340303840902e18500c242100c509141071549a4003901c401942da00240c18543d211495a0070380c0d5160045508000c14412881903030803944a0140042c801e0700442000180140c0003140c002100030314404114451605120490740140c8002e101340d0320003440b10035080e07010310080f41d0000c6081d03411400d1007005c040d12525800c1c002d0080021250000390042d00c580640b24010150000c4142151950381004040041c0c000603a000c5115000302c14140040b9101c0c9c0070800d88030002ca501030200650301c444034060741e402400c1054220801440081003080e41001026072202c40100105810043c1c848050040c802640002c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 676174136 1250 676172886 676172927
    0x1091d010b1c03170f0717070504060c08070605150a050105070203100b060d0203190b0f0f010e01050714101107031d04091e061d07031b050d060903 65
    0x120980c2d00c07000c01c180401695281c403640200341d440d00b1510070102803c0e501c0c080f06410306011221100c2a03a062007400c481d00d680c42401180c04400030b00c0a81100c801d00020410081400800c0c440c0070b201a92a1251403a10b05211050750740c0c40940b48101c2d402012180c2c182043c40700b0b441c0892000d0300400003801c160303107840c0854003ca9100d1008000a031143d58803030f02205480e48904045a50081d6921030840d12820f00f4604a1068454404c02200803803c1c282c07034072042d19003488080b01c44440108604c84240300c04005641034120000300906004091044401086c0e09403246091401d601300036010451620342c2040c12a40f150500b07030710020f024000c60f000039030881d480111b112603200704c851504100388006805051404802013608407031000f21b80070181d0348440401784911403403003404600c1c0207240500c242c0c031070f0400c5101c550b0310411080010880128415418203c1c102030300e232641f41c4030b00214480d080e4584044402e03540d1211a85c0c14198447c4d0008190049441034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 676175386 1250 676174136 676174151
    0x1503101a0415120f030e01050a27050d05030705060708040b0c0f130816050303031504110906030712180305032212050d05090f0706110f010501091d01 66
    0x61405110a04081c01269904590250380d010001e04000800c400b14801d0b1542c0900d1800900280e00c60300224042400150903a000e9070080090740c0d410081c0355a04d4280c045250742541c4c40e8114426841501000401e010906440d2050400d081e0b6004030f0080d0b80d600001e20b012480c1100040c10801000261018031001030200c040f030304c0e001448503809a8039606403114074101c0f40b241d071803c0c02010b2400040060b84510214411241455400c1101c00040d520360900d601e0340b100702c2d0794170308100c4040c42000182c135050b4445070081d40080030207404d1005000108160707500a460908c007040401ea118440c40c0514020213020220202c8241c4442c611aa0007130030071300000d403006e0001c4658224000c0300509100c00d00c40c40c0740c1c2085601216041e95600580702da0f010721051883d4a00f89400205034120000da43d4415141071002044c0c598600001198a19015039020200b07004100d0300345400d010074001c03640644807a40000501c41c44526161800c502c1e100d00702942a41070844 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 676176636 1250 676175386 676175411
    0xc0b06040501030f0b040305280f02011a0111070e0a05060307060f050a03020313060606030c1106012405211501080f0a02130504021b150108060c18040203150310 71
    0x2040d07411194840c20020f16071b251854142d031140252250200c2c3c01c140b540d202c007065680c03280406495402c9840715850701894030400ca00b81c17600001c000801c1114002c10441d1540700f00d41d0300115070000c17030544408a49400e80030001701c605680c100c140d036445d0002c0c000d003850b05112040c010801418004c014050100c005032042c0201c11100382850b034048005050184200c126600300b590060f01000307000d447d0b0902400409425103001c00152410810036903c0701e00084260580b03014805100e0320058010350b2103801000580340e1400c10209001d0360696030410740c4009030348a840c13044c00d404d42c50309041d61200103511110380c038100102c00342403100e580320f40200036030040807107900940d90750115266080d15408a5003d01e4009100062407070752191211405030b9441068800e0725000e0340c0340d00582c501900c0078022002c2d5600700d000800c0800a9060090811700c00d08410601e06d0504000040d049801c2150f29402e1003800d03169004007850244096921541513400801041c20b9110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 676177886 1250 676176636 676176653
    0x609070312050a1215090c030e032712060f0c190804020f0d200d150b0f09010303020c040c022d010902030d0c1b06140d06150c0b0604050103 62
    0x24196402e21100041141010307200d904110450361002c0001e000c1c401c00e40c004102900c84034400c82041918080c110b0201900c0f81c09103641d81100d00009504080012130405c60a038000503c0f40303170300340120340100b50a885401540d071f0441d5800b80a41040c0c60b2041d4001041680200141c41c0b9500820807855400e221042c1e05640c1e182d20b240000e400c0d5a14404a920440081001c83d40240c1c002c40610801503027007000d1840440750703281d02601d005500e00340080c140591034003c02d00026221050080c4400398805051840020000d0700061512404110254405e0f0401e0780140c00001c0503c00754140350180d2303180340300341e48010812001d83d84480c80e1098164000c40c180d0824020505294003400d401041101f9001810780f00f095400001c05440029040b404444840c090b012032555240c1a01c90780007100c030161510b04850068010b14441d581c06120010381d500c0c3c2d030715408074403c6800d0214030200701140d111041034031840e0601c0100700b5001040075102c4d41c200300c0144001440c10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 676179136 1250 676177886 676177913
    0x50d110a081b0708030c0c1c0314160206070609230601050d06020d05100501110619020f0c060a0c03241509080609030406080a052e090e010203040506090703 69
    0x84030001402d08424086509060099004e550341d4480070031003650140300481d1410040304100c0da10000201c045d07111145444640720050040303804120310b14070036800c0d48000c10003000c060307484a40d0030350658001139441d04205400d540d00380c1c1d9442040c040000700c070320118840b91003060300c0300307540d43d59451503039a8030050003000c0c041c4118101d20420402c143e010b0310400c0130390340300074416854094101303107180115100f01d80c0011070031b2042c04103444020440c24007812060440c550000007040341031022b588203d030400c2c5207900c00c0100a605c032078203009042c0204400b00d008100a829013030000c040d40e64221910120010301561990740d060750759100400c446c00000300c1c0d04c041c01d000d03d0588612a0f2948205101d00881080003c5a08048010300c1a43e20075118107071551500360b0b940007264011101d8450074000c500c4400900000a03c03d6804008080b43c000700640d00c406440043c1c035410026240940e40220a10040090500120341d1103140c807801010420300d1034640b150500c400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 676180386 1250 676179136 676179157
    0x1404050109021c0e190f020907090f1203120903170c0406122703090602010f0c020d030b060f0a0e03070602120a0f0e060408160902040605090f03010204030f050d110a08 74
    0x16182248074554060080b03404d0803420b0305d250340620316941800b00421400030000c034411002c4600042d212801121401c06664080b031358160000c1c02c00c0c0000060300303032558066040c80751140710b03c1419240d07805510700b0b081c465580e08424500d00c56400010707100103081460f152100f803100f40003660b84118110387c84020001c010481d50480d409026407000780c2074552040d607603080c20100c18950481480c000301c0d034499008101e007510b00c08045080703940c2041d00d240144c205025032010944640c1164901c0b4000610b40303464050242600d18441d400b0000d0f00020484201c21003419107800d0181e440100803d0000e0090b0040303030500700401c0e210365410407060009420242c032a0710b105100502c40e211001d003485039103507104c1205039660200480e0b42000c03801c2015010941c49000d000740c0c0d0407100b00d5103a0908008403402085407103541c1d00da00369010341d808d000000200e840c0c10b00d00f01d078050250000d880d0030f0a103440300821040e540103445480e903021040320f50000e210318044403d1a0203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 676181636 1250 676180386 676180391
    0x90b010e1e0306090a031206050d02060a110106060c170c070303050d06032f010e06400503120304150c03200903010c020a0c03080c0f03041404050109021c 68
    0xd0071908031607194031005007030340c0602c02c120400202201c002000c28480740642c841005800710401080141c4e2241e024990b040842002d440e001414204058400f074005805c00c14080058070404074211041a80808006401c0c01030503014440c2c003001e02400c3c8005181c00c1458a03d01c0442c051381c6451a100040820000007148100780e05280c2c0030303101a540c01001c10007405640110360340034100075040c411600c0f6071078190b064a58081d055231340900e00080d01090500640c4030b16528698140b5080c0e00a04060100c0c007401804645002e1400c20031803030b03201c0300c020308040605180005003903a403000c0c031000700144000f2a06a0b180098240006100402e040081c401e0403800ba10b150b81d003134081c0c1c007003d00a5900300d07546100582241c680c190020440080ca604049917982c3d07030242c0280500c08440780070f00220351400e00400c0701d00303074103001c8030300050b2580c0500d49564410741c041c50740f2400745070301103410f442c007400f0306030050958000a5042207103201d05501c007041740d1840c0e81000f95 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 676182886 1250 676181636 676181659
    0xe1002210403321b0108160903020906030c030a05100c0219171908011e0e0f070e03120406080109060b09040b01090506040803090901060813030c050709022101090b010e 74
    0x1102482400d11a01da410150b03042c00383c050b00b030004da60f01c40344451400f04040341e00090105080406548a9690958819400c94035540900000b244040d16090b010f0040000e10142e5840400c04410800c5c8100c0042070722030844002401120601c0d4024421034003c1601d07405001700d03024001c0d81886c0c102c10f80790342160501603d840d413407284120644400c0c0f28800600c190f83d8200072018126640404024101d00d0080440000b401c0300340507019462485601151820024001c01a481502c6e0704200d0300c1c1254030000070386802a1214000180d100004d024480158010540350062101c0501841030f1400c010f840701c1c0ca030180070141d5004543d11511168640c0c410300c040340003003201038135a40d6120745456000d5160f5210000c000c0c001c99020000080701032080001c2c920408481e105010040c902e47d03011180520201390a6401d44904c61011901e540c0d94030040c0000d00d40e840d40c2c0010700c84000303c054078620059200400c400d1a1804042c01660032004c1050250400c030350154034203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 676184136 1250 676182886 676182953
    0xf061e03031e030702010b03010516030b030c06120709080a030f050703180b0a1704020109030209040524180c130b030a06060902070b0f04080403120e1002210403 71
    0x5004840c82e00d190155420400c0228402c11801540100e010364020f00494503034034141400c0c0c0343c082d1051301103480b0b003c040c4000c40f482544541c000001c004c082c4d5003004926400200240c100410540b1094440c00030321100e40c1e0010500d400a250711000307008000b45940f000340071b5403081c0c0a01018400002144020148a484500140d850803c1e040d90156240c1c10009845d40080b05d280c008183c0c125400d10500c80c64602e030900c925130594a09018a04590a004050001810032181480780c0210744403507a000c0f98240607248552141c4098030700e0700c480441070000c0101d40844054018410154694807041c00401c030b0000850380104100d00c5500100340381c440030ba00041e0159140c42d201050003041c50f001080400d0290500f078110b03458101c00f100c840c00056a005041120400081000a400d4950302521400506103802c961030007802096031500804401c0005812074110084403001d001041d02c0b0821584005600b007a007103644245000d0b075940203280c10455070800740000d4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 676185386 1250 676184136 676184143
    0x512010903050702010c0501230106170105090601030c05040312231e0a0e06032a0f0403030305040305071b0515070b040209090708030a0923030a12110a0b010e0f061e03 74
    0x40c40c06006141204402c485048842c540081c010713000040d051246029120440c030f03424cd416508020700e45045615210010340041490f0140030090160034000000412130f410546c500c940d48036120b00c1d5100d912003200c400d9180c0f100060104403030050001910b04800500090700910103204820782d1040505400d07142c0361192007225920440000c10410001c00322511043d0403413080050380c0f01e1645480c1691540d00540301c0003106600d0600c400c10120344241c001d030741c0080c0a070030700703501d811801d4440040300403100a00d1611124030007001c12031803c0c40504020429200038a040c180750407a500c0400e2100c01a0001c0c0c440c00c00800856481e800500c0104028141c80c011a0b580b0304000d140901044880e2081c000f5000504080f602c3c0350518007902d43c8101001005020803001c3c40d074482505440d507400f150b003045185424800180d2041114040300c0780160498000f03580340544401d58408020b0941e02203840035002e000058482134403180c5241c04202d110b01140652030302081c40c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 676186636 1250 676185386 676185401
    0x70203161704121109040f0b100f0605090312040f0b03040204110c0604030201050105090705071b2304060b130b0a12051017070303021c0c020303070b010512010903050702010c0501 79
    0x40d070100007000502c00d4000d03808042c00e248181141c2064125600030041601e0b002c4030301410001c041440c450016030501d039000d80c000380319001e040d0070700e071105900515440e40c4d410100101c1c0d00002c520f0034030301d82009924502d2491030822440d00d41406401004081c140c418081010070110204c0c0c1150b03100e400400c070101039840080e40b07817260240d04554800d400e440580155207020008281d9060030035903240700c0c05407511134924007a655600c0903903030180d858401085c0c0d0390000003c144840c40d91240700c1d1041d4a80041d0345410b00c450104011034003664850800d10700200715407066050b80812074412a0101311070540c43d51242d031004ea4480e4081884500418904010801381c040440c2c0d222042c0d91004141503800d03900428140e40e110f0490002801603030040e05c4144d00c03410485907507c180c0d1110b1030700c40000940755010134038641041804854100c40c0b500140311500b0300e004169400f900c864000c0c03100c406c040d180038000b48a5410040e041060340300c404420300c2000d4100c0d02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 676187886 1250 676186636 676186673
    0x216150e01030b27130b040f140607090f0b030103170307020a0c0f030b0105010c051c110f011a10050702010302160b0709031b0e0c0c120309011b030507020316 70
    0xb4803100032081c564843da518082480da1300030110110f100c5c01c1c10303408106500b580c00039060003551181d490b43c45108040080403540c2003450541100d110780d0501a4078002c40306611500d0489051003c0202d4070402a080102014030600040000c101c1001d02d01c0c0546050030440d596a07104c05030101c0c20803101e040d0190544040707442c000740c12003110301000c040700c0c01600080d901e42d0b2038000450b8440303085030000d01542e010244500c00d00107005003211403801241441c0200c0e00d5a030032a64103100e4855070301c4440380d43d0340328021908446210b8018045108523041d40c1c104424100c044c0c114040c1c100007038100740d0f0100e080140018040c10011390741c0d03045084034902d45019500105814440d0200b103488010103d000c2c8034050704014100e09460010420040554504a40c17641c0340d04200103010307451096910461a00f8078010045004408043c000f144880e01c114040f102d852a000580d010189050b081101e071642c04000d42e800c140601a9802c501754860034040b049610016441 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 676189136 1250 676187886 676187899
    0x2060c030c0f0a0c0e150415091509050c0a17090304031406070207090b03100f182117070c05280b0606030f1602030c0d0e010216150e01030b 62
    0x2030742d00e800003984001e8144944c004000194480d44101001c03842610b0020824020040c400814506604440301e64003c2d18650181745540d00e021200380c82e40c001580710700b000207103c107112100302030140342d9010f07140000306490070b40d0201c0018030f030100c00018000000c00007408107600c140103104440041d5003001101128a0120b06410340b03a01098983e4000f40c425240b0024240605000d840e4031402e004003c1c103c1c3c182d5656491018180310000303d01829582c01988103070380961020144a2401844880d4000c0c07000c41c41241ea04000c520308006004020720041d4412000f04100e03035101e85140380c00111032900c0e207019460403e10040721840502200c9215000c0c48040c00a100c03c0c500030b002040c0030b510380e1000d005061100b0355220340800c503445c0010f46221000700060780c115a40f40b0440e03103400c003440403103401c15100054900000d060244110b0045d80e040044582c0e8032880c01c041401d80f450443d83c003145400303110b122380030f0205070032903404d49030301a03408000201009082c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 676190386 1250 676189136 676189153
    0x212070b010602150606040618180923030a0f0c1205030a0606030908161703011d0604051e1b040821031504020f071a040c060c020d02060c030c 63
    0x40e801030009020341d2005205441ca41d644042032503190718001c42e0080e08051401d410700104842040d01c4040c507405001c060400050344503043c03844171b42c5001c3c5070403000541c46821f02c8e1040c0210140140044060314003070780814540804400c84804c010b4908003c200400312000a03500700e40e1015000e0020340d40526041102600030001307611070a0615001c11040f601c03071343c0543c1124030004001e40001400e22001c0040303590043e03c4280b0034003641d82c0c0030801f480300680380e400d94400d801070040c204e03010312150403c02001d490740b034129400312001c0c082d91600c07a0400420104605032600030b0002000819a280c5110802440390040d10070410760311502c03010250340c1d82d18070001042c281c0c02c403114074024004120080e00d0099041001c4150041420010040a5040801d070300c01c0300c5004000d10400550b044954507000d00010804d02c01c58a0a400d041c0000e007030380d500040602c06d06205250040c1e58518402e203000e50b046442070b440d00403520030b03e8654041c0680201c40e51103981c0a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 676191636 1250 676190386 676190393
    0x1115150109031b0501090605040308072604090906150503150a021603020f0f060f070804020a090f0c0905040e0a0204180b0702071707060503062403070315052e021207 73
    0x4074007054803006c0e01d40311006e80e620b4000325014800c61002500c0710300240524000242c03010a544040d030300c803414240c003032035003981c007020300d076100d0f0303004030303041669154aa0b0800015000380f01d150841408030312149894403000c81d442780400e5680740d8070b400c0e9400010324a6007541e4165035041c84210f00d400c0c041221480d0103540c0380403040c81140184128a5000301b0580c0009a440c4109081010b03030f02c40d40c4a41c141a030f8420405001280c1c0480da200003c95603d03558811505110074a85021801d408050000b40050040340c01440c06207003000481c41c020100042c0c01541b5640c166000241c2001e07099020000e03102003080140380d92111000e01c010030703078009040410f0342c010300703103035020104140c04503943c0e400c581c842c01c40805c01c107100081951506542d6216005108202920902d03032800d100000782c2c0c022104400030940d40c0d1302102c158569400440040c01c8181c400d100302d0680403030039250901440790702e14819100c00b2844511a403082c07040701100040d01e401651110b07a0f918 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 676192886 1250 676191636 676191683
    0x11a01110a080c0f0c0f18041e1101030e12090f01110d0302040e0c0301050307030f21051312020a0308090303070b0702101b09090c2d111515010903 65
    0x41055039035110310f28900c2c2c601e20b009000150820742c001d02038480f081c00000700207d41e010050081c0c0e92040040c0c1c040b4240d044800440d1400340c450310745d000401c0e11740030001d42100c5220440321829401860044068203a042c101e550700d01044940041e80d0440c1001210f40414a070f150b004940540c085101856804d038016105032000d103400a00f0031340d0f030f5001505e40d0f400b00b482529890b92210350204003048002c3c40540c5241c1c000d000461109081c525105c2403008981907210024100080c3c001014040c1c4200c42c003c1c01010a61400c07640840d00001c44080310f038000a0141b81000541301042c0d5000c10481d540e140d40164012854503204c0001394644c0e81540300f0f82021818054440040035040310050a80481030b21030458641c20451090002e042d9000380d0402d1102c056801c9121034601d00700c1c00f20840301c5080000c40216480300c01002800704039909111580242c4aa008946c402d0b40d002e82e21048008200c0c0900c542800100c1e034010aa50000e40080082c0c112610786002c0c45 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 676194136 1250 676192886 676192903
    0x10501091a0307050306040908120405060108011a06030603030408100f060b0901120f02040909150c0203040b22030f0303020c010e030f07060b0f150c0c0102011a01110a080c 76
    0xd803129140d0950750307000a0034203500d140355840050303020400104050b006001542d0015406040042d03a0714042d41ca826803680140195010300d110710003048100202000302c64050f0400b00c0c001d10201f804604406034001408914030711401d0084001000c070384042040d01d002b0604d0100725103201850812040092000001954135a8188040410b010b0100400c80b4010304040c0c2d91400396440d040c406000504005102025964080000180c072032070034099425440d0141100a283c071066103801030031912405c0c106429500140401c000c802e04100a8900301c00d146000300072600e9220304608e0420100303420080441c1c0c0c1c00465901850340c1540508801091100204a440c0d05441c503690303640201d220400140344100108000903032a600407500c0450301074210189004e640c0009044020458442c110500300031842c24810b50301040301005c8480c0a0000300302c004d202000d0f691205040d0382065041c0202c0701c84072400e40701c04002040d1030340d4024484a4a50354120200d82d2902c40c0d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 676195386 1250 676194136 676194139
    0x3031602010e010c0503010603021803010c11010b090402010e010507150c080105010f0c230a120512011421101a10031103181507030203040303050708090601140f0a09050105 76
    0x303010b200b41c07103494140f04060101031507440305070941e031034070384120701035400b400040040203403810100c0141c2c1c80c00d01070f003100c181c11900ca50580384407050400d400c4130300007024684110084014480580d0b004948000a00d07000e1900a1340c031985414402c0d81714441d031a1280f5110318268101e56103a602c4403005041e11000da8544000002d040000c841124200764007034880308101420500248802040600416132107090301c4403a02030792120051100110701d100d000c501c0014200d840c51607143c00c82405040c59110880c0e807200c215002c0740c8000ca01070401030741569200303400e0401240400903a50700c015500010700c000540282540103092000e40d50500070141020716900c001d0180c091a0321384607444070302c0780c00c681e103843d01052800c41d941515020382c000d0070b40a82003034805610b614810f140c2600c000d40d41c0d043c140303001411643d009084004204000062000b5104003050180c1140c0340d440d0900030042a0100190305d0000d542c58407a07001108280020b5216195004203048400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 676196636 1250 676195386 676195391
    0x204091415191509050a0f091101110f0a020603040602040905101a0406050f0a0908060c041d040807020d03140a170106030e0d050310270e121206030a050303160201 72
    0x220319001074140c5001540d040e0500f03400b0740090001c2ca07140d030b024980c01071021801054002183c1150300480d620b5110540b45001040103c1a441d40c01107400e641c140da50380010555607844030011515030416000c005e20407107000003c14240082d9406075405008410130401980c1000281c400720b040040c41410f001d1350200025943d640b01c80c50036035007191344545507245000034540108610b98010b60440052101003070002c10701140c00c1081e10720404040c3c0007556601c1c203182ca08140724010420398035410125030b00b08000102040103680340700d03606861041c0e0322001460181c4070182c5c01c0440c904908804180019001e9200300c8002d44031800f40030440180c1d880351400c030305a446500782040a54860150242401e1240e0010b561140084200c805250307103e0500598040d0084154160a2030030b4110005804a6104d400e0081801c03c00a01314480c114041c91042e025501030200c041d00520009502c0b41c6040c013403140303401c2e400b9040da562482c28105240c803409410741c11100561 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 676197886 1250 676196636 676196671
    0x40f02031f1d040c210c050303090a03020f1503240f060319020904021605010c090f0510050f0a0302300414010b130e160f030204091415 60
    0x1004462941d060b16844800c041c10b207038403030000d8601d507240508102e42c00d1204c4e00c000030781c046401146507032004400440b005114914103046560400c903800451090b0030070046030b0465034450212104695041e58040210408000041d02c4d403812101c1c44d0016440c00030400039400e061403001081074514017108030402034000300b40501c0042e2111600d03007080381040481d034101c130444060303034400c06c0ca1308000d4540204a40401c0580e0042e503192040f003c5401001400c202081c00340303040920aa280c0050801d00c0c1030b640104a081e1441031501821145044458281c031030f0046840e0390341c25645650740c070014214020020750024074146224400d201007402c80e44403d40602c42094401014815551203641310788200c94102d68014501c0c0d9680c1509245079140c8142d44120362101c0703000003452900c034110440c2000c1356140540600c0380c11020500c20b0b030114000f00d405807901541c000a02d40350b181303000e140d00004224044e40d1031245450100041041075241840b5181c01c000390712940 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 676199136 1250 676197886 676197931
    0xf0507020c0a1a0717070c0807061706090402040209060f03010308070b01060c15050a180b070e10021024090b0114070f0f050c10020601050901050307060c030815040f0203 75
    0x8a6104076611580a4100606004103940c5d40c240404161038070000c51404041c1d984100000900394888080c542060600f00b090301c1d0000404074107480051411000703850442d0006d0011200108028859a404204003007141c60340b005a600c100400301d0100d5481d42c4078100301505800250040b02c81740795000010500c188501c1d404c890003903100004221000c0551a450058503000b080c1d058055540e208054000e40784403001c00540e0f02035000d598141c240b2400040c00f402504811034054003034849450003081d0b000801444041114000003540c5210807045d4404211811a40514920800d00031a08840702d60014000b04000d89456450303540b2540c1000050051503806011224512030000104499022502202c3d100d0b0041d1010808090005a610044142242c00503840140180442e041204c01c450140208400406656180000047c0301c2415140000c0c00c000c40740c0045001c0d48129203540701802c000820500c03060f59008200340c001d400807185031403103088016448000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 676200386 1250 676199136 676199159
    0xd0209040e0a0b15060d020a0f0e090c04171905281e0212240f090a031d0411031905060a090b13050a0902091b0a0c0203010f0507020c0a 60
    0x203998440e0410f4440c1e41d600300140c0c0381541d01031185402a00402140244070450310003821022074613140d05111462200d0010f00801400c03a84600804991041c0400703900c03d0025241150f400c42c0740da9100340c404804090900290600010085001c00000010003001103200c4003d600050352205807002c48070344140c2041c1180001410301ca8201e45064400c0041303910541070303640060455040040c00f10702d12840c040030341c2c19030214010302e01c000c00072003290803803226003049004034084c1090402410321a20b41f00c030000c004061042c001940401c03d08450002c101e41900103000700a60a0110144101a401220744c4103800c628102811840c4000d803003454021940645000306540c101041e040c010005d0090035540150224042d085416042c020b85208507400f00005c69000000d20603c204104040c20180341c100026102110105030f00f802d0720054021031401d60005929400441c0c01080c40c02e03240000213003807030100840c040c0c001440050080095401071101303a55640490300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 676201636 1250 676200386 676200403
    0xa0308180105070f030b032d0c01030b091f0e040503030106080702030a0c080a09170a030e01080708060d021f03151a04140a0b030f090d090602060f100b0d0209040e 72
    0x1003000d415a81e40d0131031099001000f549405001c80f00f0841d405080c03400c0755041c0352050021080d201c2445801d1341c50a0099141c045c07001e0030144002102c3c0b400044802e0b000030550f03500042000c000004002001070080000d0181e4a0054168281403c0080d129402402401c000ca4108004610250300c0041140c03136030701c55592a41524a2a50f030707101c0b0a6403205003003c0400000c49404200b840c2240c101c03541410410000b070403107100500d400350102c001d40b095181032000e15002c0204075900114950740c003c401700d0799000c0c0c4d04858400160f0302c00c1d40301c0301c101030002c00801c003c02d0030740c1641c406904d40d0407001c000c0d4100d40e40e880155061251014080800c00024170041041000c801404081840000c00800364a901e42c46110405e0f00201c40700c100018244042c00b40c41e40b814040f00f240f0303010900d03190b0a858106a4040c0d0794075000b4015042261012001a03082120984504060300b2203c4116603540350216401d8060b4000100c450b02c43d1b8a03088481941d4400000d4110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 676202886 1250 676201636 676201651
    0x6090402030613080c03040b0409150509041e0f0f0b091204060302130b12041b12030c1106031005010e2407061503030807170c090d140a0308180105 65
    0x212941c1c0e00a0f454012400401d044810180522440c3e141c2c640078009030001e00042503003141c4452400b00d1900649810340119450182114000e0250391103c3c414958041c0c0c001d42001c0b20784160740f00700c002110100101070903040c0c07001550340801c400c488400e15001d00030260440c140e140c45002a441d1a6180e01501c0110000c0204220f003602030340240c1a07400d5841510519150b8a0040001ca44e00c411410440090380310100410880712500307107c6800c1d206c14014402604000020501039941c0e10301405108d00c51041e031041241d1681c00e901c0510010344015160308040c01c00f421191181c3c081c0c1e0380030445041460750300e1f0802224850054a032070410955009200e001c0c0d801a80c403030075041c0c600c9500c4d03a024041d01030007841e1107001180301e80d45800c41480c0000005000080c3e07044c44a0820405609204202d41e102007a101c41d81d00489180d08642450b00c0e092564101c03400c0100090f0141004c83c0b0181a0007081d0184161070b00031040318400c99090b0301a003214030448809 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 676204136 1250 676202886 676202893
    0xc1213110a14041a2b020d060225050307080d0f15060e030a1a07051209031c1b080c040306050a06150f080c0f0c06090a110303070c1e03080a0201140609040203 70
    0x545d07000da154a444c003130704d21940109020001040e000300760901c40b20700080d0b5099800054048407001b03141d80c00b0a084803061180c402c022032aa82d0310b0307181d100e460000707818401c1c0480ca00c4c08452456001100307100101384200800154a0302071241b000380380c03040700c0c08900c003014001c03030034140481c4850b819640f04144040c80c10607055005006000600740e1803c110007030100b00c0251013004c0c170950050345480c000715214691115445142a1500d190320003079401c1061300c0c82014009960608820058149045c06942e4492481c030b06000da9071000e842981000b050140004142e4010001c1c0c40300c0c9000305020003d2008140c2e00038114024540006102c000050350400481c80541a600e0b021707101c0364034200c5039501152a010054560f814030303401c4078159008001444400c100720640941c09941000030039200d51101c1031242c880d0007440d6504121001c5206000c541e168040c59104482d240c403408041c400038001c0c405416001c481102140101d1010b1900b68001403255a00a005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 676205386 1250 676204136 676204159
    0x31407030902120c01122a030510050604080a110105090307171014010b0706110d0b0102060601030c0f050306120105010305070f0812090616050f030d050c1213110a14041a 75
    0xc4c0d0006001c40082102801c82c80291f50005001c01c0300d1b29010328200d40d40101d21810400034000d03032044a03030b000c680f02c0c480801c000c11414001145d65142da0b904210007089401400006a50621030070044a9260203880c40215017000300c4100342c5242d542d01c10403240c041d0702104a0710300300d4500160b02442d100620004002c100c1403c4014805640700340e0011404801c00060710742140c0010034698130094a0313454200803944e040203159480032007460184640c2c03002c0000900b00d04003203e9500b08201000000840c9034031962580040c0d41084002008550303076034144192207145501900b103041074006400900200b0000f443c0c0000012a07400ca458130151a081144aa02c081c000a030410380b154458400b10320140004441c000800d0003869031440c0d000280707070032034100400310fa503104003e0014070740d00300c503811601d944207009265031450720001d8204081c203070904c0c2c07004991150444c4408109040310205484920b03e0558080c0410131042000c007140340800c42405421292004a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 676206636 1250 676205386 676205417
    0x50c0f0909070203123102060915041206020405090a060e0a020a0c020306090601080d170609040512040f1802210a02090a0e1f080a030807031407030902120c01 70
    0x122942059190045a1500c6680001c1703560881003202c800000e520046401c0c000395220004070b440c107040c2010b4070441c0743c5031580040c0d900d00942e241140145001510810513140160444028000303450301d89001100c580b03050000b95010340030b0076001300416008116000e07824004d0380280c030f0209000c400185d4800715100000e40120b0000400c12403611072400151302c00703100083c001e404903c050500e545c1005855031802003005000300801c444180c010030f500200d501282d0b0040400c0f11102204d45450519602c0e180b6284410380781c00724006000109220600b4000045075030441121800f01c00c000140c400300d000384262000680642d600d031141c2403a410303d20722b40c44103400d2001401c003440c1002040090880d904181034000ca908180301364614400302c0c1c41c1c48000c1f5803000e4080b980c00d2001c4641c80742c05102004003442000c8000c500614065048604039081c005050351440c41c0c80e4070004c024110502c0103a01401b1b00c04034000c005c0401141d021580348041c0c55507549940e8100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 676207886 1250 676206636 676206649
    0xb180c030712110705060105030d2d0c051507091505091012392003190503040c0b04050d0215120f160f0818010e070b0706050c0f09 58
    0x1040b204146941d81200004600d502000d01052400740c801408558101020315180c41e21050701c0c042800a40030410040744d001074408081e0021404250a81021210007658440c038007680080c928068510300075000c0841689003845071540e40d440002150b44d8900c030945100d010b5402c1c500058080260505504012582d081c00f00018606800940c4660340304030120340c20b05140035050300c3c0e80318414003010040000c210165245849084500c14240005417013089480150ba41c460000d88c41540000400c0c03003582d510b0340e03408141180d0910544802007242c0e00c01c40b002c59500c0346aa00100b0000c801c0001d0b41c094483c0502a01110275580e004c00040003442c071420500b1040401242d00c18a00c94440203005a102e007150358030070705140e03007080e0218150320710350820440707a022172a00c06980800300603041400080e10f404912000104540542408030045a1511400340c001078442501d0b0000e280f664003510081150741c03980c00801d01140320300000343d4071310602400003009915185 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 676209136 1250 676207886 676207907
    0x606050f0108010909030c051608071401050405210a06020715090b01050607140d0e0112051e060d0f0b06032803080702070e01060521070c11010207030f05010b180c0307 74
    0x203081694500d0520303554503203004004805401d0389a03444c081046503132b50401403140a00807030100d008904e0007050008029020381d10a103441200c402d10400040c0c03192140440e0b07007030101c605a030506d100506040e070195100c507800f15880170000c016110704064620407907040e10b60110021030a81d181c0742c10041907070070048040c0e803442d43c0d1461507ca41d203401c009101c4030143d42d86031030b5035100e02400003520703500c4940381d135602290500003040300c0740c00b400001e290941c0c82074400341c00320b441e408041011075401070001000705000c004000b09015240140910a407012822620030142d01c2100c2040e80310071800e825985010a120100064080c2852650007103c5204a550b007d0b500e0b0356682c814082a84481c000c10380006400c91421f0819081c21044a0719079410800c40c100842e00a0180300c5100300031b0080403003c20345120301e078828810b0340f004540180010400303402a04045000389181c2d545a0b06c2103660307a03041546100030801c0e8a00c40da6042c0c40041c00d6544428041d036140400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 676210386 1250 676209136 676209143
    0x515180106030f0e07080616140306131e1a04090b0a0f090f030e03070617040f0305090d0309090608010e0a0303020d11030103060509100b030304061103040b030903070606050f0108010909 82
    0x41c0c200344c200601e01084204028001a8020105814402d50f152150030300080f0441c1004140d1051742005000241125008101030741c3d20084421030484850091000c000070341052041103281034221282500001c913032800064400c40c0e0048440304000032520076040c01420b03400c4150007e0301d0091503a210a800c04405100854904126903545800d42c407000c0c42140032507000e600e810b490742420000c66000c2d000506003070081e003011085801c3c0d06400100010210300f9100300a10405100e2000c1c0c80f5524409060007100c244241780180c040e15241c0150210189815400281a0300500030440e001601c00301511440342c15450840181d4400009a402141c4401d8125640245040214001c4d4002c1c00005142c1c00c00d25502d50611240c56042c2030b08a00345204221143c0c1c0100441e82120154209403259410b803468142c02c40c011503001256050000c4108100703202d01000400703440388500001c00c034603a260f20802c4441142c0d889820b0009000000500400b401c1c0e0b408007150501 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 676211636 1250 676210386 676210391
    0x203061305010f08061e060d030201060306020408010b04110f04061107150503221e030e030708010b01020d140d02030c0c0a1b0b070b04260d0515180106030f 69
    0x403091100250340080c0d20030602e0300044602044004000c0c09019044010940c0000c1c1441d8680652540d4003009400b03584030b0302085608104045c000d5001d10011139004105645940d503400c082402004200c0013a0b000d64144800c42281050042c00c07900c0001c0c17a241ba1134285400d01c1e0f422110007550402c0680e0343d00c1140c07408902082040c01c040c0034500ca680e1041e640e40340c0200100c1000e000b04402c10038140d0441c0130300d0009030480642030301e007020140803100c80c80440e042c21170703034a644a00200e82600130040081030300041900100c008034401c0c1c0845010f004401d0040307944509a4144044d8254203000004542c4c02c0d030f400558000c3c0e405102c0608100e01c5078000da080c18005001140d440d400c00c60002096070002d0786c80401080c81e612210304041041d00c0b1500c4a080c01040286500760380036140c14034001c0c603418008020002c0d41155220351402c46d500c80205403d407130000d9841500020b1100303500d44460403511000700040c55404a1340307405000d9014100e08038540d0081078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 676212886 1250 676211636 676211659
    0xc0a08091e0601140d03080f0717041208090601061b15021315020a1a04050f07030825031d0f1207050a090903020a1b09060603050f0601020c030d03020306 68
    0x66000101c10364444410240001c3c0d4901681c0181c01100c0e111200d00500d076040150022035040307000961300500181c0114415607540004039911102405a40400c01040d030501c828004171401e40c08540c50035803640d4405444100c44071355a001d00344500e90000d1040b215518208540310400400705104060480780ca1074401901310036038004201d410340d145000182046208888950081303120080c0c00500700035105529500e00a4181c001040904048480401c080000401103040000b40d41001e40307440584900d004c0760145d101d400140e4440069060010709003448001000f085581612450000201442c0c0f83c200d0010751551540c0c001140c600307800399502c0381502c01100349600c901400483d41484200001440c3c1030300b002d055140380140c00c0c4006600042e0081c3c840e0f4101d20250318201c46500141150f507169000900c40e07608151002034000d402da04124015442e440d60b440c043c1d038841004a039145104030001d07505a0041001700034084c0694010f40d0043c4001d4202c84108 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 676214136 1250 676212886 676212913
    0x40b16140c061005010806030316020315091c02011109090406140c04050411070c0b0c030409150501020c01020d120e0106120f0314070b071d040507180506030c0a0809 73
    0x141c00101411000c0e41007207003008502403940400c08003a01c001d007024529800e2107804a540c80c00f508003009100c429132081141950b404000011020100341900321940c5040486107441e84c0e125104a00c0c0a04448441c40743d06006018881c00703481e00c50b500703500b415803400800409140c09801940d01650307e481c603501c0c2d100c00d221414403030004100e042da40c5601d00390a100072109806010002214140034620000ea00c68a01004030b901d196042c81e01c410b12800000c0c113621a617880342c00028604452406910000001c00044400076001e50307503081101070040e601c41140d0048a800620001160f003c009180c1d4450100e03d806000002865602c03400d5440d466071100d82c2c2911862114441481019404003101145c038122075089801c01101c0d42d564074207a00003078104428002e6669043c02d0031a4000120f0b10744042c020001d000c281400007018155a4082e4840303d1000c5840c00041b48504002c02182d0080031624a03440c41c08580d04022501050040d10302c2960b400780c4416016035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 676215386 1250 676214136 676214177
    0x412031b051506010909150504020f0d0f09021e01080604020307090803031f3f0605190e16050915130b010f0e01021903200a1406040b16 60
    0x26003107002c2601d0020f003402c0b000034025410f280d00240303209080101a21100320200c2d02082260001d80d009600d48040760419982c3d401011032200440d850409642d9110f907594004685460013a22a4000725200b000600d1508065029041c00305485d00b000c04c1043c1000d42c01582c4c401c14a103401b04500b0303154405d6a0855200303071900d50001280c0b008848a218402640500400b020030305802019a84801c0c969010301c00a5040d4180843c40302d005283c0060001a00d105075006508100c54549025a0220000021050440f41c0d00c1c1881074800b2200c00079070924808250b4407203c030b40d64548010401c031007800800d602081d90810419144030344500b0f0f4000c2d20000d9044002c2051f62411000510fa2400d00c0884800c010840b4201105640c020885400d000082d1402c3c2011a2560a050310001e40d4459180071900003004000070110020503040d01652240c3c5a680d2440f0091503a82e942c0c0100360390203045054000049085968003401c10300549100342803681582d046800510203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 676216636 1250 676215386 676215403
    0x40020f0318210309010b0409080a1106070e06031503060f15150a08132102060a06080d052808090c030a0c060311070b070504030c0b0412031b05 63
    0x2151602106024100d0411509036841c0e8600301c0040980c01000d254207040b01c03a20b050300c0451480c00001290040300300307400c440403450028205010b40f20451070300b052039034001046a00040c4c10000d00b00112080410b500703010382e50700d5450309400706043d01005920b600207442013185004c0307511120815102849007c2c4285000520070300c00e8580700b800c5441c807070a6003003240e00c030390818198008031300302120664004400303920308480590f841480d0b505509a0b000006040d4041c107424141d00050460b085081c2580303680e0aa0b20b41e520b90b6002d00095802c0742c0541c44141d0001c5404074000c80c412405483c2c012000400300417031130145141a24039460243c081c0f80050b01100402012185c03c10031000035442c158010000800340fa19111101c00c0c0c6070059004040e2500b040b0706065002100340ca28003500f006114500f821702c81400790480c2d001c1c0c8011680c801c03a06000140c1030f40800c05860868248003000d980b0760409950494100f03040142a00032413204c0c5540d0404100104140c50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 676217886 1250 676216636 676216657
    0x3e07060c05190c030c031d090a05160504080d0f12020c1c0c0b04020f0a05031203010609060203120105060a030906090302070302040f020c0a1118090604060b4002 71
    0x940d1601d000c440700000e4840064404148288240f190303001980c485030040a0035010301d001c43c40000f8208180c0c0315902081031580c6d10421801c1408102c0c02e05038802c50140010b1030084e50740c41d070340d030f1403e450500941c800e243c0c051300903070085885203028404030006c40c0c92030b00d07114513892228020b02040740c1001c0c0c0d201c18181d002d1648105510098205040480e440342085148000e00355191134122000410007070058000f2107080c01251286800440a805d004065a035011908070803600290024490000001c216180c0040d045001008848141c504e4108a4003980e00b010144281640300801080030503070755070f0000c1c003c03038603a1150241d0740d4401e0b030203407450f203246004101c2990031a0428114035032042146000c000070016440c91055130100044501c0c101200001f110b019610b00e902024030f4001c420050f14901c0401c01034841c900c25041000140840740a024010022100c01e42ca50480d00e02030100b081910036004031141107103103e480c10715030703038000f442c00340c1e0490320901 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 676219136 1250 676217886 676217897
    0x1b08190213060512070309080306120f01020703020610050f01050724020f0d06060809070e06030102211909080f070507170313090b091611060709030203013e07060c 72
    0x940311800c040e50b40c1901700f030940c0350902250398251a1605244030103000244642d46113080a00d890400b4403004030080c1044000f1134603a400b030300f8083c1d140c1508803a00d09410a050308003090300c1c82d105644071074806043c1d68807810200c07a640c40064200c00b403200c1405000000340308100302607807800180030130503080300d01c252100851080e18058440f550800340510800000700410b00000180d180101e410345c0c412541d054454102090091044500005044c00c4c98aa08240d10301c2100c1031134090b9180100e45004a400340c420031040300d03001040101250703001c00240c1d0705882c2d014054014180600151481c960760f4000902110500700301c042c803070b03810102d04071320045840400c05004004100e4140400c07201c0300005040386500030248240d001034446000015440745913940b9070039400908540711802e0841d0094031100703462104030f200e5800c0207014080b409450014400f821190b0415a03141201c44248402c1500d101c0d0b10304581d21805e2280c0400f003055800380c4001591580c072807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 676220386 1250 676219136 676219147
    0x10b1c181202010b010206070210090c1d010f0909020307060e030f0a0507081207021003020f16030201061a07020a060f0c1e030f050732011a041b081902130605 70
    0xb0b030954140800d4181503402c05010402c5058022400e2000000d40c2c060008907100c0c00d103010f0301c008005070030000459108000210b07202c0714a50b290b0b410303201441c480090541d41d40120b01d040c0c901c8032500941540110708104000c901950211140c03110041c00e9620309000d294042d407400c4916001600c00e07510201041000c01c030103010a012800020341524507001c5180c01007035201c282d55028404041e80050601c0c8894005420780d901d00308850108c43c00b6014504000b40039002d00c0c01501500e90040d1094003c08a0034000c489207203901500c0034103100d15000059500311010740c1003606000f030075581d46000503400b203000700c40ca2200e20900c0042714064180100141094003506091000810505001c071700d01c03076905a81d100402c600034956504800108507a14902040704c0e65a60812288030240509201c030210021402d4404100120655002c40005003210701c07140c000c180d5041c040b809039040900401c005444166001d0300c3c0803903030b810b9036400d8200d650045001400200e507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 676221636 1250 676220386 676220423
    0x5070b04060b040b010e0120010b0d03020a05010507030b030c0f0102030d060306090c0803030c0f0a050405150318010203060a09050603070e0910060605040b0d0c09031211010b09010b1c18 82
    0x103188820704e00b0310348100103107120000a0800c07031000d44040c40b00c0e44881e0001d02208400d402c0079108000142a400815000745000303950784c03010ba401104d055003403000040300188284200c07281c2070b400800420510700784030144071044055035155070450008000302c80311400035024560096102d14030021f600601030410400c3d80c070716900040c0076074208100303204100104009580d9015508102c0d03036982c80742d44030103681e948a29440140c1040b1014034011482e04a1400fa40c403d0309411801040715640360401400c07480116080ca5012107056814001e803042c0b40d10640d442807029003241e02054583c2c0c2561001c280803918150198418661031540680500800b40109060b0401034145230401010b61100d00034990318000b8203a5540350794100718880d980910041d034100d001c0100c1054041401080c08443c2100004135600f060940202070500d500049d04854540b0340740d80c20040201243c121090007480d0513007819489002c0842004400e84449071002d00c11044c03200b080c1581503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 676222886 1250 676221636 676221641
    0x90c0405010b0909060612071b060c0929030712020c0a050c1306060c32031e09060414060409020406031506030506010c0311070b04120614010f050d0305070b04060b04 73
    0x401ca06e01890b000d100503030400100e4151741d40c0058443c100100103e041d400c980c20b0f414040c003070240455003012010f07800c094220200c4d90596907a0b07503009020100c0c220b80b010101c503e03a140300002c43c50400000c1c10061081111000380e50102c0005460f00454603425444c0c9040b80400365201c2d000041b030300900c0d15006903021006910742c0c1042c0503179407801c600034150310955000030b8064001580c4120034504402d80c50640000c000d440b040c188803000c290b03076560740c000994404041041c0f0040100e0403aa03442601c4102c000100007a00d041c1c14801c00ea058be00c02d0b000840e800c220282710100b41d0201c3e9002910140c5819540010041d048511906110800f0b40c40708c0140f52402042c82540e03648545062400d0f0b030941058000c81140b617160904e005183e80c0885c2440d030001c0f40100340300740e0011451002501a020520410540301c0b0b4103846d0600c00e204010034a01d0224040001e1f00341990048c59850083c2003050a18042c4d840356a105c4204507400c90751076a0f100700a022601e010b1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 676224136 1250 676222886 676222891
    0x2040b09030d110d030908070503130806060d0c2c07030b1f0c0308070504050d14060903160f0f0b0a0504020411040515070f120210050702010510030b090c0405010b0909 74
    0x340f410080c4461210501525124070f107060008042d1101020070512200c0011a280b0316480001c0341d540b1362420007203000461803400303038403d1405000d020481500d08142c00708d040540101011465038900030400f03036454010032466821005003007402d41038081d0050b00b90310500d00b0380c034041081e0403458100803071789842e4606005256200b07016007029541c0b00a0650409506040414864941100a8406000b26840603038001b04c2d081c401010401001e22000c40015100201c2c0c07103d1312a00c2900d6224060b4440100495000d04881404980e0304141040c90b24018800303246081280c0e11a14940c220882c0d0a00030a92244107000c00c60615128080c0f60615680c8040d0034641410000340c6000c15070740c51500300c0d00010404000740048800c004600035400070f041c03607069034007200107034a400046408680b03151030400081c2000b401801020321440b07954403411001030940e9a410b03404075000d4000c0056104003030b01d0603c03584580c85024081d0400c154110784460307001d000c000f44610300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 676225386 1250 676224136 676224163
    0xf1005060103060f1202040e0105240a030b160306030b0f072012180603090c0108011208040302010f05131e050f0603040605040f05030f0426060117070902040b0903 72
    0x3810020450040c00301c0030fa01c00e8035405c21010f29034500500004020389660709140708254649000c1c45442404501145458142800d81480811402d010002100380d2840058a2683c01c080001c0340000024080e030480c0c0c54a090004003c0d40303d4443c10003001c021101506c40c8541d180c00c0c8024035070051f5081c04045121010703102840789800e0503540318000440308820a806c00324908841040300c600703c050084005c0c221980720b2400c0f50020b80da50015444050201d2074680000c0381d0062b4130038059401c103410040700e62802e0300c0c642c01140d0354a440184101001400d011141604081c140000000c0c60701180842600c15060710300094030219602c01c40c410121001100740544601c000c2d030380c1c06a000600042c04d07a41340c0c00e1041a00300032800080507404005140c0d084810004003400a4400d43c0354a0700040414000e943e82d0b03407854181200565002100420800c654084451029400703101a40c4400e507640c0750880990700540c0022007030710404a01105241020011030181044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 676226636 1250 676225386 676225391
    0xa0c061205070e010f020a05010e0a1e05070e04110d0f02090c1206060c070308030709036014061c03050f04050a0314012a08180f1005060103 62
    0x800c00c8003e040900b051816506104070344e10346940190003448102c03003454003c0024086956805150340c0c8030f4001a400310b41e940381c90340003c3d0303035020003002107907132035900c800182500c40c10849500940200104203d83c030440d8094500703c1e1340c171800700c2c080b20a41f25613400c2c0040710f06881044800c420003065402c071154148000d510b480d4204445641151003502c0700e50795180400d505e80c3c1080450703000900030113030000500c000c0355031020410f412640140d808640b000300744083710390003074080d8070000c4038040009a0101041c104010300f0400a40703500440c0d052234040509001ca50800b20391807402e981d550701e2a114040c918080721540b1140803120f415203160100807003090103000c4903000c0c0802c00d000c1040c0040400480445025080080260b05555a00e2505c031a800c1004541781109500f001c400d01400162034204030b00205640540081e5410440c4080307076510f000401692503e0940c1d181105192001d000b040007a84140c1c0184c5004c580b50000b203410380e0400707400a0304061 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 676227886 1250 676226636 676226641
    0x206070f0605150f0d05030c030a0917030a080106030510030b01060e01080a0b15072609030f0a110f060d110a090b1c0e031306020d0e0a0f050d0807050a0c061205 71
    0x10703a250300c40d40f40040202c603000c0b00e05d042800e2543c03440c0a5194040010305c0000342c00940a0340280071901101c080302480c4401403017a800e000d880e4000d14a407140869200c0780180003d6000760407007540210310750303c0380403a560360743c0b0380c480100c00030b92000020030f0300340900400c0740d60701c41c6032a584000c2080041c401c154264001c41c14030402103440b91604e15001c50401c08000346041e10340c0401c04800c0c0010040342068041950561201c120b00340b10b4031590840d5101c041c0003060b024142a04128050344800309542801007010440300c25a070700c00c10400826180701154400d41d003040f100b10080c42d4035010b14240c041c01010440c0c00030321079aa0280305042e221101f1072842c0d15070010200740429500d0388140d84900d54013404c0044183d040e820603010896071707800250f081c80c026083d84d58416654411090003c52041c500640d100c2080305c0391b0910103400c21030302d000345c3d103440340110a14040d140e03224a41002003004003201d000441007802c000043d170007610403e03e0000ea002c208040d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 676229136 1250 676227886 676227889
    0x50709320603100e04080316110745060e04080d0f110a0f03050601030606050d020708090d0c050a0e0f06210312090709090f110d0206070f060515 64
    0x351030100a48554030000c00250150200f90703020707000303010001400c49941014a05103a0380c1d04229000c41e10101c08440154840e4031800c0e91000380c10140c0c020703048440c10807242c031200b200303011103407410401075062107079441031810300d8590001c50400412840b1b152a102c110144c0d4515030001041750005400c0c840400c0128045800d4860710000018000c50b030801c0100c003801c20a82c48261540d40072900d010061b4000074441111398080c0d5040016994560054046800742d01400c0c00003a070501c4403002100250b1b00605d82d4a0080c0f20f01420000c5c2440010350510046404464100308d604042107141840f01d021f00c060580b6100301013641c6080708140040d00c6000704018402d14800302d4442c07000f01c90260f00d510310847c10303080d41d54030304401068204c4200c09a9480305680308041c800610850305106145000d40c0c01403151482000c641c840010040c0760030f40d55640100b840d03408900595401c802098154800ca030800450a80703800e11f6811100002c003010741da0000079a61082c1da = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 676230386 1250 676229136 676229219
    0x209041a100525030e0a0603480507050d02010605150315100207062303010e1009020a1106060916031a030d2a03080117030d050709 58
    0xc682191038480d03115107080044000800f000340314401c00b149290300c60b200b411352000003500032203000d6420913021961640304408460100b062124285920f4482000300604078020071400381c021041c2a8203111409213040d8084240070004003c600005000010418240584205410603000070031403d803410b40411400c5540c04038480e6640800000902000310f8903a11880310b41000d040000e4518140318080d58a42c9140501070101e0030046900280b11010043c1854280d00b10340003e0443e407907c4001e08404034054888008032000da0300200e0002d40c1d034070103003240c04415519207402c20b8150820703e00b00100504541e024141000810800c03800000c0505410740d180d10740003078400426061a400240c0311a000c1c0c0e0315020b8051012003480d4840000000c07401c10050f1300c03074400c414405085070725045800003004a46000700412440c03100ca0000030750010b5070030642e440c14040c60020310889a0458104010071001441030022035072480c844100440c0d8111414441ca100c0074041d01c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 676231636 1250 676230386 676230409
    0x4050112021b060f01061d0f012718091e0302070b07060c080105040b0a061101060f03120207050d0f020d03050708131403030c15040c050310020c0c010507020904030c080c030d0209041a 81
    0x2901000088d55800c2e40f04540341c800c1c1110b400140c180c040b21400310807201d11450711030100b03010b0280740042030044503841038401d0301e03038066805800c10511507403003640d05090f41400e405600139003200040f076070f0b01c000041c803c20707120f200000344109800d4000b814100060300218003843c42d182e900000c0c0d441d104c1000055409500340302c0402d140c4035507028054541031300100c03940c0410100000401c8a001d8030120020f02940965403c60740303ea091100c1e030002c2000151910030000010700250a044c0c003810100381c02454075030324015031a01c4002d01075002c180000e1281c410b40354204590186039200200344803046000e0b502c0c0c43e003030503d016034441c14041c80b00240040c10300864100445028007c00030308002d000c2e00d0b861002c03001c00d140290008050f042050103401109482503200d08100e804080e0300402c00c1c1e03442e07200ea4900300d4414040102c12202d510b030030088083c14030000c0000e00541c00058074056511202201404207031101c0c0f0340b0a10840c196051036029540c0d90603071362132 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 676232886 1250 676231636 676231639
    0x50105090415060b0f090405070302130b090d0f14060105010e03070b0f1308060a0c05041d0a0e1b030c181f051306060816020304050112021b060f01061d 67
    0x1420b9070b0b094410700700400095006042c0300200080c0281c000e0100030141c5032030b000858081086a4030b11109500303901c16903260400312010450140450111440a8246880e0181a070301781c03105075a403121002c0880c803030291000c102c80d400c001c041420422a841c0035100a01e402d9204400c6140429030380d0640380100c1500704030229441411101c03c2e420343c2c041110280b8070405040e610024682c4400d0300380c41c1450340742e090444540725180600221707412503000d6080709030304821100094080100241c0fa2601250301d4100b25a0805420070890128076280740300307401c0d03041025080603d45464101720754040d24000103040705010441c102141d002e200440c9000c10b4160440c4c00200f1000950001c0d07501c900f601400041d034600581c01041603800a4840801d2521003c51144800400419000060f03000304070034070040d403190031201c80035008060003605000ca0f20b01e40c00401d0001000b1000d80350702a0041114003014005000c0c0100303c1400d003040d0442c4061107a2002c0c1194140e82c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 676234136 1250 676232886 676232903
    0x30b0f1815010201091502070c08210c01090f0c060f0c0816150e100b06160602090f04021206090606070c05010e28030318050a050f180108010e100501050904 69
    0x101c1d031a4003c0d040b51103e142d000ca4403031800ca0581d41010002c2d0001081540c503144400310110300c020000891075084044034070704500125485011915940c0b10302c140c188a5500c0b10200300004490b4201c01d1591031140074124101070030900b006240d00e0085000030100f10070a80480c01140428088800750010024416601d994038240440071a8550116001e030350303d070140b00c5019900119501c441d0a90302c04090180313880000030450741c1c0c0244090000e094006040fa040020200c1e401450b9102028110385000c1f00d115000500320303005600c03c0c0480c0f1444104100140c075141010300e0780304000310b0b4028145906503c44140410320790180c00c0c103000c3c461000352582e0340d50391181048003010f24582d90700380ca5820326402900c03840380f06c100c3c0030441140080c10802510100c04007501c00c05007914180341c2c0307400100801203c41407065600141c900303041d110b4202c010006180a82400c00000c40c05c02210003420345490f44040e490050645820018400e980c1c800b006c1581050300310480 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 676235386 1250 676234136 676234171
    0x60d020c010902030f0a03030b1512060102010e0a030c020a05010c0b0a020313150b03100c050f0f0408031306120b130903030f1803110106050a031b080607030b0f18 72
    0x321030042c08035080180d454402c2e001d00c00c00349100040c0e80b00305680300f503a061243c801114180400340c100003411741200d11050186900c0588403461003070b40108144000f00e080200e04042ca410005d00503030035000100e18100103c103605103a0360213801007400380307800003410f403c0351120390030100d01030001100d558000022507045100001040081600030407c03215504668800100900c0c1c4840740070700a00030864926421900361103418901c500315180c05103030030760101000c852580b1180c990000c1804c10f1201089140d002c01c0905800302034a5a079094107820500c018058054244510441604044041256403038210310201c0c00c600061021540c40c1062805401400d8520013a00843e807400c0c1d418421701d40e580d50541d580e4cd0282d1108074450143c103d100342a5001800380c0c0303030030032044041000003074a20104400c1c9000c03091018103c01e6294420303035007000c00c04d40728100001e8441c294107150b482c00600e8400810811180c3c1c11030406100c50b14400144c00500c0c2010b1a501e0f40d030b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 676236636 1250 676235386 676235407
    0x903310608101a0702040c0f0801090b15130806150a05010c030e03010c0f03231f0b040b07030e060903070512010612050a26031f240809030405060d02 66
    0x1110151981e403001030b889016005940d889030f00204d106030b20960400d55a03031300b2103029018081300b00f11140d941f85041d038280900c0a01818080901c660404e6101032503c8500c2d034580c01401ca1401c0e40c54902c94000d26100b1290b181010240020715140310b80660310456685e280120780450700207091138011038809040544071800801101a019404c0c407803c00c48842d44078a4111905150341c80400c20035081480c15014001a00d407960142504840807072a806201d14140d5003900d070350400d18038215110341d0811019045a48113050b10b030300c081105e10400da044052042d4087d400d451840c10a00d90703200090b520300d40d40c0702e0030b4004c200d1a030141500c240c01390004400f4013245010307078102c140302d480c00f80d5440101800c1550f1040d28181e04154492104000c68818003001c1265421a140c0741045031002c0301d1040d1215441401060000361010105e0387c6000190000141090244002c50060300c1c1180040c00c901068004100c240700640e220019074001d213803038690050711181e6098 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 676237886 1250 676236636 676236661
    0x1020f0f1c051b0601060305010b12040206030411030712111e0111120a0c06050a020406080a0b0d0204110c01110301180e0a021903050f120904050901060e0903310608 73
    0x1110f2500042032460802c840040025028100c2d619903034100050381e0f07140f80c0310041e4010300c10034114114031200800e000d890482c01440c1c005004501c110143c045074400289010081e901c440ba0103055903d000f41881a43e041c865103411040d1000450351000804040b203a410824119040c00007207034800d405280c0030440c90040c9000c00d45403175a03d0400c000701808038213011034212015400d081c00604540c1e114020354007210803030b84034442a9107403c100b03840034080107802240c01c0850b81c01940d001da51113004641000281c00d0486070303a200c071650760f40c0c291019a501c84618090801c0108804014464400680000c101c80080d042c0c5e2070010560400154040c0658001042200c00400e50381c2c90001400305c07403103401100d0380c0a5001518036180c000d500014503602a082c40b8010761400c00b904a11740c404100800054203c1d110100e592102c442641c004039194004900100e0205140d0074441030f410404003c407580258075614100703414060301891080250700c10100c0c0f0724580b060b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 676239136 1250 676237886 676237897
    0xc1e03021608010f0f0606051603030906050c0301031e020f011404150e12010e0703060b030a0f05030a030605040e0712051501030f02040c084c0501020f0f1c05 70
    0x11001c50781e0710b40e8401c40305010304140c02202d4042d900e4000d088218034010b12402040b0b80c02e41d2151820a540040803c0120f09001400d81c103241c0c5422440d0f0000b846849a14803424406500584a5045003807021121139180300d000e100d4200410301c0c4002d1303910048100f50361002441c01c200894a03881084006000f940e1103030040350208420f001c403544c0c0203408a1405042a101c40d68203110b801d000509030f408061f2000910382080c141480402c41c0394200d02c10302c3c003000d41114118081517946010801d4400e50550340c940001c96074000c1140d1600440f4010070080b01c0034007000350403038a01c030b86400c42c0740301d00e1420715903102c0d50200f0032005000031000401480d41c040120b42c0c0d64186102c403181140c40c228410747c60040700480c01c1e40910946070289400b040800603940c4078000220380d003000d030515802000d04c2011321042c201c80082c95000000c1101903040351707480c0351000291034141603500d0354450f90040082000362070390010b00c034500c0410404c624060000164410341c0c1d9441603 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 676240386 1250 676239136 676239163
    0xc1c11030d0b19030b241e0a1a0301090903180e07020709020a020303060d0512040b27090c0702041e09140c0303090103020f3006010c1e0302 62
    0x8540d070300c1c4001895118441c00c000c02e50b068843c00320340c4424018001101d0000512004c0d0110204a400410401c0701c0da18400c42100f001086190f007000429502d40c600302c2200da00f8010240d0708940c201318202c6001003074030400350041680710b02c00012440c0414011402010760340d03041d081c14948503507c0d40100c40a140520000c0645803080080406001c9030000050301c2182d1001075032611510031110001c80c191301942c21900e40390b08011038090242c1094655100d000d20115940c152540100024169804203590700c0c4110300f580c5148556050016074440c912448507c11900c9002e45a40e1115011074120348d28621440080c0c018250340810010038640c02010901741c40342d990200b1030b404e0145d101480000741c0400c12980d10880000d0150301a0000e10883d94154025000740070524a802d1005042c0710200c049084152040b01a81a64000b050580381c004804400381a402c82020b00c0e000d40c49042d9902c526200c0d0b040c09503e1810031000d022800141032007444605181042d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 676241636 1250 676240386 676240393
    0xe130501060914010507030c0201050a1101020414120d140d0f0c1d09010b0a0309060f11040321140307020f01052406040e01060e06040b0c06070905060c1c11 69
    0x2141ca100428040940c02590a42c0803618400b40322036004606585d1034681c5607640d81c0790780d130040d801107030f0540003010220144014080c0d2071195003028001b40010308149000c0b54410385001d0100011504444034481481d002000946503540d48110959081c41c00e801317485036981c80802c4820001d040441205900c1c1e450309400000b0f59a22116001804036000c100c8000d0310846020040f0420080c46a108004401c01c000790080e8000d07001441502c3c001c90300025080e41344440344054a84529030340c588a0000101441000000c590100301c0b0ba0082e40c2144c0005498500030301050200f0148120740000400000c0741c0d14420010390101d400610028070407070030301038146031084483c0500c080154011038440003040c140308041e2022100303141c0d413032030440e4640a02034441083c10103d06400605c04c0001140500c1000300904000002c413000f040c1c039140c00031005100d080c1c0c540000d0310500c41040344860315038000501921030000c49640c3c15556010750801e481c511914901c1c001c1500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 676242886 1250 676241636 676241639
    0x7020708010e03030f011409060f0d02040516230403032322080f0c091012051b0904050c0108062209140607021b01050f0d1e0216030e130501 62
    0x2140480070b54005d000380f81e00410a81d888212611002c50034108441e0416500d0002443c0340c40e0466480c0d00201000d0718503c0d0768103443d00810182c030011144540948800f41205070351030342c00a104e40c40007101d00ca580102d0808040396006a00c5648030140800940d600c007010041c2d41c5030003d0300401d601d004078940c0c07802018090500240e04420302c10700d22150b400700054040e8007088071a408080ba001070701440c400740007041410500540000f000001c05000881c0000c1c2541043c401980144000c001c0902992001c0300085d5400d4034190207101c0c42410320000a200217403408507040d003402c00c1c05090b940c0c440490b60300021191000c001c10f034007000b2028003014591100030454081d2041320842054100150307030f1075100303481048c01644034490803460070341c401203c07800900e01490400e107810994000d0700c0d4590801140741c0000c1c2d03a00c002807027116a9100c1c01e100102c0400400350f0500540c03480403541c03201560405803d118844400ea4442c2e0707181c1849403600c2c10040410021035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 676244136 1250 676242886 676242911
    0xb0109060806130617010b04180303150918051c120228170f04030c02061305030307081b0601030b0c090121020c070b07051f14011e060309080406080702070801 70
    0x2174020344120342c40c65103440c03075248650030103000e0b503080c4213446102e2082042290707070100e00900e000f00300d409044001c201c012800d035003113024041138042840498241d200381130803c40e052805405200e05012414103607580702030381101c01119102031038180180c590b440e403207560744511110120445644144a401900c4503007103091810160b004c4c40c46200e0a96802440c044149000e50740175000c41c02c1c0d080d2480040c80c2c54070017081101c20702d150729104aa0b071000400d1031600410011500e004000c41c240a00b8103542000c0c01443c9100340042090754903503200e0114001c005849000e0525001a11110f242d000c1d40c08030381d501e0302988100c418014500000f10080d00001c0d02c030035441c0554940001c1c211051410740300e203190040080d01c0f082900503881c003561010b6641000c0459100c052220107a807400e60b500c1e000b05808000140c400724542c40c181016025500301c1c009043c03030300600002141d0003000340c8090340c60b075041c24202c84e1500001640392060315405020103600b000d2180014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 676245386 1250 676244136 676244159
    0x70b0a021603210e03060a0c0c08070b0f0c0307201f0614011e0806040f021201080601091505040506010912030207060917100506060d060b03060907030b01090608061306 74
    0x800302500f40da12000c1c1150002100e8a804040c2d00d5a450350000c400304803c43c110b1340c04854981034504140c03811440b65640d00c04070350420101074410840d40d42c100505100104143c40d8040d590011013441c41c40c00c200090100902a6400d01c000d020702d10003151320300c500b0071071300010888809484100c0e20301854204050200e6000322911000712200e40f4900794002c44030484110000c03035400204200142007210700c080f00808840e07000781c880a26000308240c920082c20500b004402005096051150f000d1521806a2050000e42d1611306040445078901c000c0109654040340c0115940c1c8920004a0721a5401e4005400000329400c00108040d0000785075800c480e01500e4840d1604d544a07104480f02003c0001e100341c40d0802c0740c801903400c5103580980d43c0708000811103401e0280c005c000320102e0706190080303a40000008280011480c286041c1b076480b000c54601403043d03001040000344825010b02c14001880031080205a455580d40c802d481d4003000c8250030051301c0e5980402e00704 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 676246636 1250 676245386 676245413
    0x51815160c050103050403080a0e03090a0602240106051c090209090703031b2111030c010903030638070834081608070b0703021e0c070b0a021603 64
    0x82a0490050000e815401303030140a10440d09620341039403954810507140c1c080c00102c401159a80401c02090805584260110000d40720035401051048420000ea503e080c000d941c201d00b11142050041041c40e500500b2640b00080310f1103405501e0348008490f6018200340900294400b8080d400c01001c03200025010007140d01a6036500c0d00c94a1464201d1003402404401910155000c102c40350002120070789940e80465500c0d0140c3d0390b0500160342d908540181c0a4043c0760b94650b6441010b26038140a80000785c1105049890001941001c0b108420121080702c20a6240308600c40c4039100c4000c00d40c1c200d603401054103940c0f010b550900034890041120040829030021040d41b620114009141111590218511345840c450140318096002d0210b4211410441040b07484005a07000004a020700455240035840350010f0301ca01d0289114840704802903441485048400107000039844115050040c0c10303035990000407402c80c01c28080c10b80d0724003148078001d000020003507944000d52 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 676247886 1250 676246636 676246643
    0x1d040201180e070e19030609150603050a060e0c1306090b01110c04050601120203010b090a06020d0e0f03070302030a11270a111b0d020f16033005180a050105181516 72
    0x81116027000e80412505a8000a89150310a001c0f0500244042c2d11041840d0710b02d00440700080700003800501081d18410490034440e8641004100d08082c41c043c003c00c2c1c0d90709003001001d07211680405651a016082c005104540302d001158050340a50b507032034840c00c0120400d40d03880da12030360b14081c168001d2402c0c50162002000c00203101d41701003801c400d00300309a640c0c81300581d0903104101403010b1400f1195403600843c5800001a036082040f280703814403458981c848848a40c0800c44500c0401041107003074180048042c000c000032546156100ca0500000904a0001003010b11180104003600c01d120440c030803c1a1541070001c1d640420003842e80c00ca560090301801c80700d0301c86405040c02d080813045000184001821254078080248541c6031402c64240c0924502c011032440002d060301152002601c4510420b8403040e40c0d54021065503603480152810000804600c5400f074210513103840304d0340400c440e60302e04107071140041018414079110307852021002c45241d171894085 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 676249136 1250 676247886 676247903
    0xe0106020f0c010905061c02091801141503040b190908070203011104080a02150c19030e010c110409051c1808010605281d040201180e070e19030609 65
    0x1074040c1d132199a1040503503002408181c00d0016555400d51001c580000c84a5541c0c0c0910849016031550000308001c48105480700d821545881c041c0c1050500c04005c1a001d00d1107404085c5524122600301c80c0c11039408a411240340e991065251204d800b00030140d80e05a0800b03c6890a1000400c00783c424907001700e00070400e0484071450500281304520400b1015000780d91118058039080e00104c01c40032001c810586011200010b940c1810b03104090002d403400706513016001e0550001c60001d4110003802c1c503851109090700d520390041c00e1055014403076929101540104903080c0141030310b20704017001240c3c01e81040d01004c2d01642e01c0c68820f04114000f048001800601400755008903103016180c001c6501e06c0003018040c00c820408070318a103840501d0006840c0e01c0351321000c82171140c44498400c56041c90b10005140e40421481441c0341d4003200e1090010784054641c068010100d0709000c10801c035500040340c10400103044000d0701c00b807480c03800414006240c0011440350312502c80d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 676250386 1250 676249136 676249153
    0x912040e04060e0f10020f070803040501150b0c030d1e050c0d0e0c09041118010b0d0f0504110f01020a150e0d0203040f18020d0203091005060a14190e0106020f 70
    0x3c06a030b603044400c901d645030344210441702900400f40c0c0140980e01603038032050f18000640d00c1c0c0c0c1c60360390310681c1d01311001e0395900c1c0d56501141800542c00302a155500c810391406080c281d42a46d05c2c090f00985004140d519100c241c1080290306040c80008640720083c4401d15249662400f190406240c49062600b02100c00500311004102c0410b0044010610300d80c0e5100c070f40340c542c074100000070010340001404d070360100f80001c4400c200e4000c02c0d45200d00741d40c400c116a8030340142c1d29001c0e00c1143c4c01e403e100a0200013410381c02c030b24403800010340ba0888082d82c81d000407441c000520310040d1100200c4108440f103c1e99a401c00c8600030321403012a01d00b8619047e00300d989104500c2110504a104c01c03090200303186c8000b0001c4141201c80e000350511a20340c4230306080342e1094071031a001d58451402c0c00c040700d4117800f4041c2d0194048034085040c0e840d041e410072890020038182ca1042a05054860318076140c810144007510102001340c10030f44e1900e4001c0e51b18103000403a09220b2080e22007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 676251636 1250 676250386 676250411
    0x316060e010f080103110d020310050601170105030a0b09031b070519060519020a120309030809060622020c060f1905060604090209030f0607090504110705030901080912040e0406 78
    0x16004078001540d2482c03016803170f580300d5811140c69110000c1d8400c0c0f1048031a03025a0701000004502e1041c000009102c0c2000f20004d40b54928036551500007900407070040150f654003080b40040e05400180707292059640c015400e00310700c90305100d0000906003d015000d070707481c0050004280c41042d40c0c2180603903040580440345081030f1040c040010f004000d03820b00015060352400d5041c5441c011a02c0383c22840e5100d0340040302d01d14443e0000b9554000002c20f250b4030440250704003000101400d010300f08a00420321800140da2920020703060340540460b14a62507048a208401240941da024148500a40500c0d5015141450f00550714250328075444aa4840c8500034140200b40b035192902c0c0c510020069000510500d03410f00501003580107c00044c020584900c14541d10586030302e00b040f04000c1100c2116408000c40017082c040c0000040b000000c4806807602403c003e1403642da0f403070f1582d240050031000d65410704070208e400182c22048070a100d00071445070001388101080c0e87c0703 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 676252886 1250 676251636 676251647
    0x120e12070611031201060c0c0302040f020a02100c050a051e04030308160302030702071401021f020c071217030408040b12040c0e070807030e030c0f030904061a0405040209010302090316060e01 84
    0x502030340304c1d2000000400c4203902405c07400e40f91a21400032075500d03c4d40c940000342211403072400b0f0040c542d0001482c004065041c40240180310030100d01300035008401c0302c01882401005800b80a0290006407603141c0c1d454601484070700310351b4103401991951a4a4010040d110540380c03020b0a03018401c440201600070300a80f4843d61096006004c694541075802070030260803034205040d0f028404681c0d011f810940c1030810307003003e950300c0580e07a800b44000c08c610b8000d007035100c500300a10019406d40060054020888040082c0f08429204e440328101200c1c0c0340b249038000e001e580f2000440d4130741c600422064904c117501841d0000d450075078030603420441040885000000840381c02c0003803a80c40c0294084210403490314102c0b070910950071140c034604403008825038010b0b8004940300389249003d016900c0944002c003008001401c0c182c000c0503080c01240901446942c012808802d44d92180d81076891108001381168001400b0407041007989809000740000240c041c106c11500e94020f1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 676254136 1250 676252886 676252897
    0x40f050a0f0e06090a090213090b1810020f22050a0b0708090d0519030c022b1103010b04090b041203020f0d020d09080c101b0903120e1207061103 64
    0x500a0b200ca0f6884000300019244020300fa0b041d400d64515001c8050707190320541580d0a4408040091104c1190410240354000100440384e07800f0000202d80b410b01c4045441072007000d0302940980c40b0908461703c85628080c1b01d0440f0411208e10005040c1c0d80380f11000a0220740c8180c80035041d84c2d496560350100d920031074001400c284000c011a505a080002042d80c0e641d0240003618403101e0b154070244501d040c2085c007640060492401d00c000c0d460044020040044019074046001481c080d2841d82d441c0050005005032815840b0803e598600707403c000b8502c0001081001a50340d58038021b01c0700301081e2416541000c804902c090028000e1007111a843e2241e1503183c1018071071402c0d240650302c218880c0003482d840d0280180042c20187c042d0101c81302c90005400c449204400b0b0300c00315001003804490381c941e0720903250411500000382005894205c4101140485000f400fa42c01d00151806541c208480348400e10901801144120a50700c0036030b02e4003070358002c0304021075803030051 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 676255386 1250 676254136 676254149
    0xf0a09060801230d020d02030f0f0105130506010608070203070b0708190603020a050d061d0a12180605280306060e04060b030a0c020a050109083103031d06040f050a0f 73
    0x507821586083c0b80901070011130920007820b0f10b040785850350101e0704020b40d650041c40030340c4c400c0515260070f4500f8001e00b80c2c00251000c0d50200a4000e032526a903401c01881003d0031b1052903804210603d03c2842141e02054201b10344d91b0107070a004600504c200c00032104d10b80c915610352503991040b5443d01034001102e4004001090090501c0100007030384141103000c5a60503900e4415042c0480840c84c00b0b4203482c0d0303020141030024154188484c0c0a401e1214010800c13441444040403002100321600c1692810f1420b1512813803000608540c0035400740034202c0010003404105200c9034107400400c1030390705650300c0303440ea80f41800521054074458012000980400d20000d07401030b48170f6000c0c12131041c881c4100c40070000305840b00b500b1100b403448140c488c00130018414109a2000300c440002108400c40c2da41510302c04030003a005c0e084203000c01030400280e1100b640c446c0011080907100c108006014a50312561100b550400245900c1000c0c0204030418000400c0d00101d01407000715600c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 676256636 1250 676255386 676255439
    0x92a0609050103092a09090f1a100e0705092206081504200603040b151008040f050c220b0906060d0c02031c020c0105010b0c10050c0f0a09060801 64
    0x40d45d000303140b40c400c0c09042014a05000201c0050100020301520311254095400d5204840b85418040c500400201c1f0102c201c0400c04d0600981e4100002c4010450311041c50251f9207071500c445c202c400303204580c0703120b601c96007050480e082c030811101340303035248442c44d201004801d5540d81d0060b11404028101c060700b40c0b0850001e000b15601c288024402c50030041213800213490a80001e045820580b0140d80941c807140070814035546210300102003550448143d020409600d90007405a4030081008208060500500c010801d0800480c01071003001007242511048803008103205618071400480050306140d41c81d0f4150800800d114050302e409030009140a03503e00031400a404030514032800c611040001d0b400c010700c40305001d1030340f40c1c1c80b00015030f0711590076409a003503880c10f070001c00c1c500008220030051104001082005034000b001e01007000d95402411220600410644e0300801600041c1144e2155118020b03800f502d509485208003642c0f29000c8040c1111020343c200782104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 676257886 1250 676256636 676256663
    0x510080d050903010912050a180b07020118261b03120a14130302040b0a0b1e0403050313080d0e030312060415030c23090406092a060905010309 63
    0x288900010460182c001d00007066200655840a21029100040d10000354022480c00007040d442040942d0003024041c00070001030415800d03103058802c05d41e00134140581007200c8440d401c146881c000003017801d1030110030300b40c5010240300e440540d90710803108a80654544440d0b540c1012080028080015004241a49008282c01e040c1e40c40180014140050100042c14000100c402415440c1c9800d00d620300103840e520600c4250381d503100005100e40b40c1ca81090114a10180544104040012017005840c00398200145188aa07030070161680c0000101c0852040e80032031604100d45481c01114044041180211100e00226984d154141c004000d00d03a0000c44a5601c3c98114034028000666102c4205010160100c241c0c81117440904030070081281d19003546c000c0c03403900c050301180e200c90002440040c007a481c2c0113000802c0190b840b40c450080c4201103020640490b240e0340d0040400d040e0181d1300e1002441817144000049034400e000c5800d5219018060318154005080410803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 676258992 1106 676257886 676257913
    0xc0f111503061f0327020a0e090d05180d03030608010c050403050a0f06021b070f140d02010332090706020109021c0204061a0c01051008 60
    0x480d060080101e1519103c071101440003d02c1d5801c8221554108258010048201c140110025050b280b02c0c9401c0c104100c0f900203402103540c01380099450749a1281d6150442d000200368008020845c4501d0181010700101b40c0007d410407074450b9510b003c40c6075084401402c0d0300081d2215420092110207205010350103000f403601c14030381400c0d80c446555609100c04002c002c0da46140c1c2580c00e00415605032601e8016000942c44002e481140d8603503218024081c6100504600ca00003500c2a0b4030003030718880c1c081c080c0846028000700e80042d401040c2034880c2e0196078151040c8400076101c43c00620070814800030b074011150401c001041d281c14003642040e4250384c5850500e0001d40da6102403140b2111001d8044140300141e8800308010b030002e54001400b122290300e640c0008036036600034000302641e02e8001c01460355000ca00808841a80c81a005a508400a6107641 = true := by decide +kernel

theorem cover : BRFrame.Cov 676079136 676258992 := by
  have h0 := BRFrame.cov_init 676079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 676079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 676079136 ≤ n) (h2 : n < 676258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
