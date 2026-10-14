-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3291
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:13:35.662923+00:00
-- url     : https://prove2.me/submissions/4daf8135-7aef-4c0a-ad19-ad5d2e68d49a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 591726618 ≤ n < 591906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 591727868 1250 591726618 591726623
    0x150f10030308061f0c11060931060602010b010806150a270f0521250302030f0d0801240e0f13020c19080306190e070c060c05030412050a020a020d050a0b01050d 70
    0x41c44250320404049c1d040c2c11030106402c4a1030b41d0016190342544404581c09548280003503511000341526941e44103c22650110045580017040b400503040a1103074018141c00b2006c6c03004110f100030303030b905040a421004010f00c840c0d1a0806448458840d4188502d206150003001185014087c0300466000707050300782c000305d00a01c0390601c0400f01284140c0c0c3d0350310341d921041c1c1c000d03004805a1400e001e109080010304006121031004490020710205050307001c0c5144580c0402c40750041c6140102200e1503080d1450100408501800015402d8000e050f05540c058003003020124003041940180202c240c0001c142c0d10921240d4049909039080510000c15030401040041d01500e410300c84c07500f09009a040d0036003c5511410307011142e403803d03a507030000301740d1b11090030003000790303e02a602080c042403030140e0440c00c0558442818040503845082880310108103403a0f842d01c204013240c0804c2c2c0040c1010700ca0b185508125455041500d02a074030f01120b00c0010649050010b1020041503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 591729118 1250 591727868 591727879
    0x30a0b0f03150a0c0c060f09050606101d0a090c020c0f0102153103020102071b03020108040204240b07060b030105040b040b06010c14150f10030308061f0c110609 71
    0x50754038580d0303c01800c0c1c1c8120710007072002c00601c40c4042503c3d4030400b048060301e17040c0040e2210460600c80c2c9091342c0140502d01c1000c9102e013501846500c42488012840800341c41c0c03806101d007400049101c0443e800020b10140b500e5082c14040380d000900e88001e070707419034000c194801198012078885d1801c055000c1030780078580104200c444044030000003014030800c403091542070010608030340c642280003600142e40109a10051214400e148000d030103503402030f01c8186107140d002a0644100a00c040e1007541d5501c104030303942516101c4842c80303840d141404800d55444103c04105500250740903200b09141c03180520031401d05110322800742d81c102a51404075038490b43c5521444100612040c1085201ca09410000380410b140300500e140c807401070089446400c8244546000003403100d4141070303440043c13000708071107102202c05994051502c040c0316030720600801d44544010805848a0320f240002401803640440759112007889035400d920902c100000700301c1140241d40e03910741d022 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 591730368 1250 591729118 591729121
    0xa0c12110c0d111c03090f1a0a03090c08161406030118060f060306170a02060a18050904030804030f080903090607030c0b15030c01181a0f030a0b0f0315 67
    0x280b8207002004a400c2c03050211201528842000c0b500800130101c190044a030803c16200406422000701800b80101311540074016240415184101c200421403940c02c40000441030503180c80380c0c01c020000f5412840b00c091583d981c803a5035030341d00101d4003403004030340c1c030300502054441c00b11040c007202610013000182103074204010700352150b54840e9600b50059950710b0020344480508007800044c80d090701d00241e107514100500c1014807070301522000e00c4e00005001310040c1c0d0707140c0548040103881e01c0c0513070ba10701d606070004101035550b4000c554009024410041010303800380c3c0240c804c0d4802d40e05c80144a1401c02c00340d41c144010385182d100c60b00f040c00b0403d814101103001c0d26840b40a80b424894018694032003000e05d11301603d00da0900080641410035900b01042140c17268035080c40e050244064440c031f000556035180c010014220000f4000204000c1d0500507118000070344840f6541d603051103500e440090085041103030003102203151080c88d40c980441c001c84840c1084a400045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 591731618 1250 591730368 591730393
    0xa030e030301034103070c06050a0c15020c01020409320c070c050d1406060109030201080a0e010615050c010c0503130b270313050d0206070818060a0c1211 68
    0x240350024a50341810b109030500c0304d18440c0c0105254000810034009076035070719624140b00302c0e0b07582c20b0b411a0081c400100044a00745500104143d15660407600c80b2654400c6a05181c000e4854000406030340e60010802050306801680801c000c548600e900c888080703800342510081241e040000103005107008001400303040303108001c080c01c600c200d10071007805440b0b13000501c800310f11101c15100514000c10075461810101f146941281c424241501040d180d640024410364008007182d850b681c42d0351004d03455550941241700036000f24140500c1c0400504002451600b1108540303d070340d8203040e0302c818054020801c0780d005042e1520b005034943c000d0340b80d4500e400c0e40034005580010a46148008101c601c0080011700400345000d5640c9800b070108005d907c120a070803980c4511300040b0381a00580d5490201d80721340790b10401c00c3e621081d4481c5480d00507203500403007903040b00d00080c1c913a8075140d0180020b84458850751103801070705c1d0120401c41e103408150020342c5044d401862001034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 591732868 1250 591731618 591731663
    0x3080601020106050a030b09120f430c0f120209101a04081b0d0b0901090602040e18010b0a2904090212250e0609030604080a030e03030103 61
    0x60189041c0004910a559040410051541c40d8016a040c000b410140400310205006c20700261202c000000d0404041c0c0420400c14450801007400c0d510b40d5440c00142e00c5200e02c81c0c0110070107140c0c0392010b500d11400384015101340e070240841d014948c0100101d040f00720490600240c0380c05500004403842e00b54203000c0d8910024109800140300c040340011099200c040b8185109070390613000d03071520714200700c0501e01442500e030700326a43c14800c01020390392242650000c12641204001295440d40090103004120550015009034000240455500070b40214a4080e0700c800100260b09407141c0101800c80b81d03100c84865000d4019541044050700e0392030b480c803000b0501c900440d1000b44641e0a040e07542c0c000e42c0301e841e0306900405c0550049d4030000f903c65202854203a003030801b0040d070000c2e00080f0708903003000f000c1c8000c44c0c4404a4540703501c5d0548400c80e0300902202d0503401c1905204200707401198885001a05100c1e00880c1440b011080e60304072a4400226220190300900340e09 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 591734118 1250 591732868 591732871
    0x114070c021f08012c04120f0207030215310e06010201141902040e090a020405060a0803040b13051305040c0f080304052b110f09040803071101061a13080c0109030308 73
    0x244010017040f1050215089a081500403482200700aa0b0070b0300040f030203450911041c400360f06540020000304050384800c030030310f215040c00800303c1d83e5880030200d045090740e101881d4110203580c002d4142c060948055003110903203201400c0c84c004c81c1d880c1001282030700e0180c40740504400c000c40129040182a0b032000046242e14078000d03003020b4851800b1420800c0455151501c0da102200903815410544a4140c00a106458080b00d181c04c1c1100e50740d803840303248504e0b1082d150006a404003c0078050380a0081d0030010000c0d505190070140160150405407400d0701d01c101400c20000c1d110340200324103c22201041c000d50304003460002000705422030044000000e031701c40100b01d40580d1480c2c910360480e510610b40d0041c180304081c1030080d21140012294010071022080c840070503402c400340d9910420618098000682d841c0a160250825901c0900d440102c244001c400f82c102e04040c05050103130100485c0000da858440c540d0f5120410816400b1890309207040c13000c0b0b0300c1500810b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 591735368 1250 591734118 591734159
    0xf06070801151d0f0d030e090703061a031f1d0622020f04031a090c100503130212010501080102040e0a0c0912081207090816030c14030114070c021f0801 67
    0x10215041800040341c005c80c000101180080c120541078013440c40c01c00441c2e6008000c0d4581080424180100b041104001100c84141c2d04004000034004001d00800c0251001c49489901c00d001c0da5400c00407404100f40001c0320061104c100011000d040c180204004004080030302a00341d401a047d050096210542418030390400701f1002c00418807402482402000e40d1054410524008201506200440b400c00340f00e07144070b002183d5180d50150580703420150901c0480107448991001a0b1815032801c0d83c0d118650802d03000103102e00c41075010340304031125030031100c0c0c2d169030b42c1c035242c0101c40b1040e44501c0400d0101c44140103800b07031408c6100026104003191464600c5000f80d00134921800c490007400174414440a10400409020401d010402401c1310004607056a907110b04a800b123018501c031042c40f100200c9101c5d6000d40281d030020090a07158038041c109400010411421140141d0164046440320001003580e04400c40e03c0d22025560396205900f081b0400390b00c0f07482e41d000c8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 591736618 1250 591735368 591735379
    0x16170610021011070203060703060e221211011d0303010308130812030a0b0613090507050d0501031101090f030b071b140109030e040903080411010306080f06070801151d 74
    0x502c1c40d01c030500d203d03040290003854616911140135104040c80c281000b001c0790101818048100718003034030b43c8070803600b00014801d40380603003440388030406000304900409031046224120041c1c1c0e054002a40300308294429009003c101c51100b0100607101e0085a4040f055201700010008a00840081c1603035201142010000a641303c040301e20b00010300040c0f071007c41001050144a0401c0d1080d40317003000c000c0c0e82203414a122000741888810441c81511007268580300024003440c400c030f0072142c0007200c01d1010803003035840307013040803a032601c4070700c6107000c503d4019000c41c190b0300d0b03500000e003100d60000200d04940e540c02d0084400f60b0311200860310300610502c040c070000307a4814a0355002c1001d036000094200e0f540c10000e0900c104080d1241c0154036040c00d04020039400b004540d031094106040000ca0700950f03004034020040ca030f102c0200d80c0505180d8905000010517120700803400c0d5641c800382662685034031086c504824500300080307425000b00d2145001d00c00280110044000d05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 591737868 1250 591736618 591736633
    0x40b07020c060c06090114071205070909020c010b040e011b0c0309030f0b0a0c0306050d1b09090f060e19020d050a0506010902130b03130201081306141617061002 71
    0x7181054120703010442c4540c11503010017100140034130a402d020040c0051040c16070a0080740644a0500c41c03560904140d15800020007250051504c40700405e060501150b40740503a41806008001c42c4170440c0c40750741401c01c2c2e211013440c14003545e1134a038005240280b8030307400a007041d80c404034200b2084041c4225440300101003001c01908910f4240200e20750017061503c42c20b40e008807000480514140341c9021428005038032a088240c135100d07030111040104a45d060344071483c0d2078040c0d10100c0030310700780a00002045660300d00500d1072489080103101c40409050304944485c982c4080f16840b0480341e4079000945004568122545d003d102a82c81a0005850b00e500b012400d170424180e01d900000d41d00340000000403040c0043c416a06420300f581400d48030310000d23039103d0b0806410002000d0101d42050391143e0b0690b8025400502081111969851000d54004c200c84200c54500005002d10405000b071440f050191000446a41c0d19a5404200814400c00b410010f0442c483c005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 591739118 1250 591737868 591737893
    0x17011103151233160909021b0106030f021014091c02040e16050103021801052503020114060306070e120c030f0729070f0807080703030501050a0f0e040b0702 69
    0x503090321214081e00400307400d4a00020140c06031060103051204d0000d22070024400140e400300c0c5140544540d00310141c6d6940303d40114000d14100740a80d01415480c00c80000100911714120301c0d8460310035502480100c5031303843c0994010001382030544050070100407010103850714840b03020500000181401d55040d194020038215051f04000301d030316501c42d5010103055515054444000e2509183c10341c542030007901122038038002031001134144036000c201c40120721306d044103160307403036405080b5a80300c0800380c02c000303000c0c04c60100d40c0c110011034200461524100420440d1003040c403a02d985450b0013543d42407000103032210345100464058003801c400c1c1a6000e001d100d01c41c058502c0103003200d50070052803c05a4050000d00c005681c142003481041301c10349400d503202c2c25000758048003198201d040c000554400d42c2002410303400d002039504101078055019905948068070150803142e200c038282b03182d42d1100d0250030200303120480040c0005043d036408903400030301481610403203082c0e407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 591740368 1250 591739118 591739153
    0x303020d18030806062104050c030f0309091012030e060f0a030605090601030c02070b0702060f0d020d0b04020309030d020d0b0607050a0605070804030e040c030b0604170111031512 79
    0x110700c480100c500c0c48107820a040d0700c2903e5036008182152283d160141c00158080c03400e9440038118000400f990006091002c1801040320501c030260036504038054580c4140e44030f40c00540c04920400404001c0341c400c49240101c00e0039141d01d0703483c100c0f41c0140d5403419075020300e1501441d5841b801c00c01c03004600b014400d028002c0190700e40c4001c581c3d48d05080800024020080140341010700e4100d03640e50403513002881d40d0866901e148490743da00c0d0341e400801c07801e07c101d04442c2032a500001e0303405020000c1d80d0040038544d940d81020480da0964504100603840103a40b4050280d10034000640b0300b102d00d0f8014420540c151000181c030025900201d05603821a0300207941b56003000304c0b140140421406001d034031255a28044009282565000d071049031700c8001d00c0d001341c0d9103014000721140a5130109006030802080d140e2166900c420784134480b0024031070384400703509004490320030500e20000d49005042200340c1c50200724500043c803442484081e24001540724041914902c282c03034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 591741618 1250 591740368 591740381
    0x160b1b0a080a0e0405011a1903180b090d0c11060d060519030215030613021c061509140609010c020a091418150718050913060c0503010605070f0303020d 67
    0x3603e502d406140b901c001c0004858059000c4041302400282c0c07078007102c505404840f504510790f07242082065508200300c00924401030104038260844410f00140b10506a0040c172130210201201c0c40b00d980303181e0884811400303200051004500301000440b91810300050b1402030030300000040c0b01341e5610700198404484a0030740084940005091040d4100390154080107240c58040506d1030034100f003c81c0c40d1707280380c0424144072580031400458031480760095080c2c80a50440a0140e070703843d00c0c4d00005900041c840c440209649000028508050303c142504082009100c0c600300f01c42440103440381c2c1d060101c1280e005c0107101005c01e04103d240b140c400a07440500d4207100d107103401002510f582240741c07070040030340c1c3c00084035110100700c0390a01644034003640707006000010358524415810b407031074206940c080c0084080202c00b1441c0740d1401c0702a0f00890301031040002c004da0640e400d220038040e40002030380400500000c14100c10880d07002e64881d1400529110b40c16001c40b080f14078 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 591742868 1250 591741618 591741637
    0x813061b02190b0402060711040f1406030f060112240b10030608030306040b040b0a030812010f0509010603020307051207030b03070602060c0409090f02030d0809160b1b0a08 76
    0x14120004024550411128129800500402d0414842c40d00c1d00c1c88607180007400248180340004001d8100141e401141845120103081403002445c00010000a04a8000d1901421920a0003c1d950f4a400100340d280c0c840fa50000d00042c0e420038000c00440d811264080e610260403001008051000f0004032001c1424800300041c0e28212404009400740041164401c040c10f283c4280301036100801100d403c07000442c0c0006150450b4800b040203000414004d0341c0c4072030080070000520005c0310041c40018034843ca440d241d40c1e01c4800d189500003107802151f07009400320006101040c0250300031a008100ba08000e41071606007030803191580e50844880000a0b00c1d90030705080c0d4201005240e010b8100d82c00035103a140f0b0201c95240030303400340d403050307050741501c0d12a0b140521101401300361003540c0145c20f5541042803ea005005824140e903840c0440c441c80801c194068002480c0406580141301d0303d0380703841d0805617595a00c00c4042280d6500b40600103080000664000080603a140c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 591744118 1250 591742868 591742901
    0x50102070206040f0e0f1501030c0918060612050f010605130e01260c060d021b030a031401090e0606060d3e0903030a0c03140f04090b03160501081306 66
    0x1030408a0320100305c1d201030030f0076a070030303490905200c00700c420031000d442c00ca0020318000490381002007084906901d254403143c03200c55003100300503080c60345400c010b05403681070b02d400c1140c2130120f80020454800f25007110501c81c1002c0180444e91180008100b05001c80307180300c210f940c443e5240e84111000383d0180304001040801c1c500d001200055040c90580c0e00c6000e010590300103c0820400d1143c000c6070a801c9600103441583c42d450001e014115001d080101c9858205100000e401481500303007441070700d000000005101c481900030851075011060141c8843d80328a014800762340c02120710441041d854610091031408001d4240002025110441d15280c42009403181d40501d6041c4c90b41000034100410880c03070314008100d850b641820315000c04411890308003210081043c80e1410850a80010203103903000c43c1c0c00142007640e01e9107000b040500c04600030941c1c0c58505044083c0310101c40b00f000c019660040c0d811561000364000c10072140003003235a0748411510440000100304 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 591745368 1250 591744118 591744149
    0x6010e0a050a0b01020a0311030c010e06090f060112030503150d211419030612030302040f0905280f0905070911030f150301090f0b06090c030c040302040905010207020604 75
    0x2812070107a16040240304200b00050049040000d4803020100300103414881258022180a0030420859902164400080041803950754610742c503100e045d51401c2080c410444446201007000c82c901d07040340c0e00c104d92103c00302074941c1e007510300d900024241041900d07080c040c140c00d070320b444804400702c500c07607110100050410090040307001c6400440f0300400600e1020100e041c62201c045a0550100e00141003902d255442c0c11406808240c00403030040c1d000c03111030b6040607055005002510b80c0904400740544e120700701c650440310704881305051007079092003010441c2100b02d0f1841c1445811a00490820b180040d04400ea905064040b5002d0380a203d081220302550300ca05508456044049451810039441c83c19011201420400c400c0040920f01050b03030ba02540b12526060380200302c4a072116032405c1984aa58046a03200c4c040d02807000040c458038200403c0701c0c4106041d00784d00303007003604580030704c0014164400c0407074031594200005030159440e600508001e018141181044 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 591746618 1250 591745368 591745381
    0x50406090b090907060905061b0109080a080a0506011b051c0e1504060c0b1e1006030c08061c050304030803010b07200907030509150406060f061106070e0a030506010e 73
    0x1080e030050001c0710f039420141090120a5000c805841100d0f0f0848046840e250038100e05c054010034006e020040c3e42c602b04e4400100700c1084080c103443c1e01c060b12080305a550752464141500c90445003180005d6841d1812100201c60880442e01d030750181c012074094140080f520003190020070050710208440b5021400945851444a0203244c52072a603076080518010303001d0409420036800400040b401d200240d9201c820f4904100c00c188a644080d0540c14108100101c000040c0110310000e4204090b940489000d001c00314000c11004d000d040ca4038588400712600c0c44d00504044805000030000040402c2c5101c0c0610b018040d502440ba0740c1340035a02d804010b001401c1c0c140100407410321620215691403001042d0302842d103090104a0759110000142807503ca00c48107401501214240002e211031030380440262029254205000394840b281900c2d084280012004180c0c0a03400190342240324604c0d1b0034517030401502d0840402d1700c0c6d0381c2c0d45080c420b00b60404905c4c80142c1082020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 591747868 1250 591746618 591746629
    0xf050f0105130204080d2105160908390910050a12110d0303020d090606030209280f0e0a150c0309050c0f220921091509050406090b 58
    0x100321409610440c03a00b86004e41c034a48640020f20003006000c0b009800380e110b07c0c44c1c80b0070001102c1d54020204150b00d029040555024008000c0c0d07000908144c4003c0791100340003070882c40076062170000320700b0340340c14640004840c0d4407000b410095011001c0d140900d52150102c441c0076040844d101c020450400e01807100001c410790008171490b80c040c2e440c0e000725000390441241102c1c00c4c0c3c5c001050031080d081c141e01921074000d01d00469841c1402d403609000c1c441c0e00000c03e60340300303e82409040d194103603001d00700c428440e460040c69640100e5a0403103101c0358021050810a000041039180c0901500c07410f048078204140c03070540070755488807810712052090350050982d9007420013614449403119980c0305401c0c104240a161020000303896035840604409480541c1d10403071070300d018861001c5020348a402000c51709040e01e480600007002403841c81460100c01d0355981d03a46d8524007411322295200c10b10f0084180251010040f54907100c038051080071300340c041e80c0407554101c170358140203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 591749118 1250 591747868 591747889
    0x51f0210090f050d0f08010312050909010905090105010609051507050109050715030608030301120311010b0405130203060c09030a170d050115020c2422080705030f010603050a150f050f0105 83
    0x1e040100340300545c64069042846181503035002a4054a1000010016149445600c800b03c2d4410190000050841041d4100c01c0c42070071407130003c0c08281d9840701c080d070f0300f0341c05402429400000c1009e840340b021001006050b10078024000495040c00b035440725410b015003a00454040c580c014070310040c0c16014040c00300201002802146998074089070b041f245c48500030010108420328120386400b00303003500030002c1303000c000308108000d007010313406205124000c503c124000d0040d1000203000901c60420f46d004100050702804040040d65140034a50003090104404a10140046120480d2600c50103018001120350b009024101da503010380b074a030401c862184030341c100c88690301c05812202c400210000c03408140315203803042030ba6171200c0e8800e00700309205026030107600002c490a00184070400ca4405034260342030400780b04840e13400d880352400084c10700e0f80203800004c000740010260540143c1d123114002009031a010001c1c0135500141d8485071310b510004010311241c80d0400481 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 591750368 1250 591749118 591749143
    0x15190e2d0721060e1501080102090a1211040914030c0c180420040605030f0102030a0b011706010503061c06050f13050712020d021503010f050a051f0210090f05 70
    0x11166148012000c80844031110001041c3d66250300c034042c0411410040d9481c2011103000b91501580c551100500030741000004903c02c40c8103e40000d00032650a10000c951500404c110042e40030380d07024480500807583c030407140303600c2c9560581d03c01c00c400e001078150407003da030207030124111000c200881c404019600c25014a102c1040c000007801009040719010284030142c0000500240081d000300096030046815000b100d255001d400010f40c0150b101d02e050490400a018040004454020302c81008540388528400401e10540c0548080c65001600a025500300081d01c002d803524074142010449059454109014a00803120040ca0b488071300115a5030112010303407241c0340d541c0c5d03d40c818046048010748049056480c0c5a000e0b04500303401810454405a05905400c003030392091040104084e140b210104880c1340205000003200c800500c0c046841c41000066580d03424100810303810751007502024600540709000d07107049140190324041400e00b45007070160800000c503016 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 591751618 1250 591750368 591750389
    0x906051002030a11010e190b010e09030f0f2802010615020a0605151206161805010302090a050405010602011e060e010618030c0e0915190e2d07 63
    0xa210300c40d9000003501da10f07030228585031581c2c0e03600089103401000181d0b88134109014860300300b04541c04041c00410258031500008401e03031703a25100c046520305e040c2c4010105400810400d544144140c014003000480041d2203854081e02d03520301c41c443c0f920318000d014622a412081401c098082c485c007401001c1600006003803090007003000391a1410204020170782c503501d40103d418171800030146401e48030013621030541015940415591001c0448a08080c407007100c801c0b0315103600c14812a1022040904038003012070400c00190003030741000b4a00b035088110243c001441d40d03124018240241560340002489040c40300c0c20350040100d003001c0400460420004004240c100a0020704440d010306d8140c0008004818544c2007404d254801b4110038030f05440803072040300314040b25018103001d40c1154080c822072214240d03142c408942148610300303018550f02c0049030940140880400c0e2605540101500000c00f84a00d0600c0401c00081054028150b05ea85401c00c0f40130044d2440c1402c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 591752868 1250 591751618 591751639
    0x90f0302160608010b0f0403050d030b1009050303040b0c1c11100506060a0c0f05010603030215070f1e0c05010e100506090112081b0d0f031b0207090e03040b040b04090605 75
    0x5010f4810701c018031a80802e107400140710318041944000395406164043c056a044d5070360000300038094801d02010072701c2603551249030003400e4080d5034030b04201c0340040c024606061400200c3c4045400a0700083d01b50b000e4100403410001c9007212488558810307803503128045ca0f003041002d1401c0100c08102c15002e14020900c0b180e6540c000030344a24012500d0712403180400f910700201a0281018020855802c080010007019008500c1c0d610b26810071191552990758428100d40004a040542e0045104000a5048815084120948104175040018080d0140c0e51800d085900c0ca0f18a88840c0d0000640b0301c04c10201030081c1c50b00710130708a86088095040c40e03c00c40c41101003010040524100040748101540f842401c0c0d20075002820980e8608201d06030b0142540c001c01c0400000685005940182c54181d8211104840c03804c0d8010054582406000d00c003c2c45014840f44d902d00c000d1000144420103a4024405040c40501380794441c2c0c548401c2000342d882a40001d4800da44002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 591754118 1250 591752868 591752879
    0x10c02070e10050d0b0a0f020f09010807021606080f06011e05070f080307021e010216030507051c050c070509010b09041a0907111009121101020904090f030216 70
    0x24951068075078000c0c0c50541600c9085a1480c0c18038a9448260401000503002041c03100c024000761081c040c3d0302d028042401d90710310917800c07441450313544e2601010901c459000e9511418040350700443c540101d0f0503031001d610042c01e20ec4515402040000d030020204820b0320041d283d0540c00040c2801c09100d0f04182c08000344d0301d1044809070808011000c0381070401d00a0714200c2c06042130b004900301c0e030b6030300b4032441c0203486011900d000d070308e0044c02114519401005108641140c4501800701445100c1941d048546030320100080d0b03040d2103100c4848500d00c4000724100d94913450760301e500c5e070764211a003d4030f4189502d40c2d00140c4200c00c0d0400401400b10100100d6001400c1203c1c0020180202c6030030141103c2e2840902e5041480e5500700328459400034818000c0d03c0543c41100c84000c0b04282d104166600c030035008200305610012500722a006a2031159100c041300005070a003030304d200109040340c0d41e01d0b006503004e44495a94a0a1540512455a50441100c0303984011800c20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 591755368 1250 591754118 591754123
    0x121e070e10180207170705010513080d0b0301020d0608060106080c0403120309020103090b0916090b0a03140f01050c1306080f04081b010f0603060e0708060f0714030709090c02010c02 80
    0x510031150b40500b0081c1500000e4515070494403a540c1c00440482a40d41d440750141040d045468111040d42c07801001c01c108001d8000c600300003d0340300010a01e444000c0c1c1c088000b0f40440c4400ba60191f4080c001c11001890078000e1b1000340003002c000700310944c50010010f144200140180480040c104018004500e03400c2c00601d0884460030013080031401480124003c005801c4081d025004100501c440b0600100d000410511000e8605001076200c140304422a210880103e81c44140f2550410000e401009035000400300603064401481000c03500f00d0956008a41d407040f10500000c4e000424407000305900050300003490a101d861505041228510742d010b440a0000302010942c18032007000c0c4a003d8070180ca49400a0200700c1070940c000c00a0141800115041403c1000006201030005a26403c5038035210091100d03403601d5801001015020702030b0010041c172240304000310400f0b04c0085014800690344e0748910f0b0b180122000c202c94076904490216414452920480e41d0300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 591756618 1250 591755368 591755401
    0x20a02040504020a0512010e01150612150305151603090b04110a09110c1212070507020a1d0703050109110a1808010c0f1e050f0702121e070e 62
    0x5840c0040d10b80c0700c600004202d0741080d4411680b0401400210407110411f42050005820b100002d00801040d854220805502400f03140001016a5020042d100e850b40000003204000c03460b440d4001d441c0d0720342a04094614200b001600040d10500025010b90300c00000e520003103260410041c071196130392034000100070308050402200200e01441a40d00c6202000060090050070007040c40100108000341d001728001ca201740c020038069000b41304884c400c4540d00ca01014003184150b440041c04c0d6826009200b091741c11050719040030480d0030b40586130b04106451640c65a400345800f1400400350f55058110003007803410200c081401d5240d0b0b82c00d481d90b4080900f000d0300c0a185500058010202c542d01c0862191b00f400808010070f0f800080b1080f1842869a560601107450340d841c1d80300c0000610079000041d0100252401d105589010b030001d10300c018000c030680e1501c0c45c9000c3c034000e00015070750300c0c101c401880b0000c0d0560402c1190018010480c55400a02d0107034011010180d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 591757868 1250 591756618 591756623
    0x40305030a0b0307090c0206090d02060c2b060311041b0e03010e0d0e19080703030e01030902031605031018080a020a0f06021206010804050d11030426011b020a 70
    0xc40480d5650941c0d40103860410005402c4481c4a65900c10301009061409260005400307001d000c941e044001051400d910b21081d00104055250303802d141038942e000154040300c0300c101d90026010b07618190034440f01601d030001c1c0841d1a9045091110240d910004003600c91840c1252a43c4c50118804850500c06924100716000d0030400d804280540b600580044050050011000d00c0b5500021032100803402030750050b1040320f244440452441c10fa00620049074440003041000170300c2005044c41d08001031501181e00c811ba640800c3c60203200d04c1508a4143d8070314001d0141c7e04040201900745d125072042800f00c2e54001c071607003000c3c1e0310405002d48400c50000b56031101d54000c20021070803560103401161094107508089009410194007828000ca011011410561043d503515024036044805414100180310040c1c900300940000140540400d02c40000c00b2489140744c1303920804441c95192025003a03130401800c55000955080c1d1013240c020030f403200a90300081c0e185013140d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 591759118 1250 591757868 591757877
    0x8030c0133050621090717031e16062a0f050f0706090b01031b0512061f0812071101030603080d09060b041a040509070b1c0b060c07060806180403 64
    0x1a0100054205031a44c1d954150354940c9000a100d50140c001401401b11285180841264403d020b40c0c80c1d16446608502d0f288448076101c10303500300541c00028902151078400c003210812803a591303802900c4002e190044100811807180303100b410800c004a40c0880c2c13602c1d00029010300e2920152090040900c100d010403400b1507024200f1040e544105101034110b0104903241d80d680c07801e02147c1500302c4440d03082c1404400300040701c1c2000d4801c04c0c3c0018240303020f400b00340d490b402c0800d121280d0209145460b01c00c80400500c3c07a00030300c00121040c0c80b180025a403041c080c14150303c080081441d84d8101403030001c2c02c0020a24260542d45000100e4502151246090415001400d83d40c0b500907449031038485001000c040840c44125031a00c180da06021175603810004a0311001d442c420045080c1c400c00c80ca4207500e0302c284850b01e00c0d590305a00020b0801039400803e02a8000b0301d0a0700c49a0f100490600041e80c1001d1400c1c4c4c02407003164084554500582c03d0002860003800003800d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 591760368 1250 591759118 591759127
    0x6040b0f0f0409060e150306010e0402040e07150e0411090a05060a0201090b18150402150702012006010e100b0f0c0c09040803010f06030203060906010806010908030c01330506 77
    0x80041c100300c1d001059150340600240e52200301d000e003500c5080d203e50880e84284801d0310542e060208009040320b1090b0400d5426a07140d03000e1202411406600c01079078020a48080390001c46c004042c90880041d6643c402480d210100b4030040b25456402c03200191000c0c0404001c0350740d00c000500640e64207075440d946681e00050305901500545200a005020080801001500035003402c00143c181008030b51f0710180b007850007000e242060f10701039080000031a480310805002030013000c8280c41031400b0440c140c0801c42c52102920710303544045c0140c0240c001005025014401d00342c20060003034001d00581d107094000c101c60b109203103002103400d00100780010700000c14400c9000c0300d2000703002c3c8107040c07500785400342990b4024042c5046200b40c00c1000309001c2d21078401e4912170000134200c1c0f061038594000650340e402c0010172107410000d100f000400c43d030300c081c0041d1a182c201d5000200b08286c080c4841c203c030245401c1405607040384440c25030a10b0103500507400c05c460007540d669684 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 591761618 1250 591760368 591760387
    0xb01030513020d211d0907020706050f070c09050604051b040608100503030a0e0103050907030809240a0f20100c030209040608160e010b030a0f0912030b01080606040b0f 74
    0xc80e040180b640c40718500107803c42c007000760817004800c10400c80c0510841840c0c000010400e0541d019155000140c2c040401404040d010f44000d001413003284c030541d420400150307103140c1545103d82001400544400030f000c2642081c2c000d40e074115960b200000c2c11485002c0c07139004180130303030300c941c8041042c94808100d40700880407908005d01000b400f0780c0c1e44c4104c9180b001d4000490700340a240002e28020003d00d006102042c00816242e02c20006490300042c0003c114030850f100d02824650180e0904c0030000000410061806120584503102e031150140005400d02c1c001d0b40c40008403c4124880d8000620085211005034005400000304901000000c90081c01421101b940007450041d003c01c0d89040000e40c0b00e8400f406060fa140d039287c6413504100045401e10400c4140003040c004586520041c0c1c005e4141d44800a00014015001c5d490300c4548203c1c000c0c200700440c2c0d40d54912511541e00141c4583c0c07254003912140e140a00d03141c3d015199101d1081480a61080031982c0c5a1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 591762868 1250 591761618 591761633
    0xf0b03060c160f05031c021c020904060b030103030c1203020421171b0f0118030c06110f040501030507021b011116170607020c090a0507110d03020901030b01030513020d 74
    0x4069000f448120100c0d2031460102d540343d001d03d130200000003080b40c10320082c41150003101d81da0b08256000450508001c40c0c0b21019410a40c0d0180c3c0c0507407142030110340300280d04040c43c006c1d8020764450440d40c0d290f040560355454802c0000d03040500420042c000c50030071611112806202c09410000c12029041c40e0441c12041c034608040d8800009081e10b00301c1115985421541001d0291040007000c40c2c0340724222117451110368600d00515404001082c040c8501813400c502030100403a048045501013100c5901403280a000344401050500032035a00d4401c682d1b1103a118001801c0003102519004502100e000c0014100100c0300d1117503490f4502400000718003030020082455546e00d40501d250540201070089505104900004907064800115101188809081040c20362900600340e405440700810038030a00044008420280100300603003511107000703940050b180d08000000409985e109444281054207000502440406170b01d190442140c3c103d520440314140d5140110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 591764118 1250 591762868 591762907
    0xf120307020a032a031101180906060c11010f200307200f06190e0a170607020d0e090f04030e09090a020316140d020a08100f0f0b03060c 60
    0x2900b000060710700004002c01c4c00415601c40000029543e0809015001c21a40d101d051101a00e2044407094450155015001d895000c1100810303094003961a624a2400d58031b81d40c0c05440010322407550503050110380c4444c21032600d001d182190045800312030041190583c0040104c569510a51100141c03100304202d481440e48a001961450414101d56101441070071025004840b03926005940d458140f00703c1e81104203802103200000300031002120980d0b803003500300d900310410b400c002c07940c800f02c1841580002c19480041c1071914014400a0821009416101c184401904545c806548605038603030720441020310a14155a1b41c241202d081504a01154211445109220b00101c0c00305150801d140240e0032504412130406119842c0b415038819000c040401501041107843e003e0501421103000500040003552148419410003505076802c3c3d0030140c5d101704103011745440380585100491102d804004494400021a0701c0d11401400004141c1d000100c04210702e18646a04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 591765368 1250 591764118 591764123
    0x402010e01022d010507020f0d0503070c08030a0f0c02010c05040b0906040e041a0603031204060903090b1801020106140a0b0714010c05070203061003020109060e27071206050f120307 80
    0xc094a400c28500d80402c0003aa0010f1154200800592a18000034032342502007541e40081c80421115841162540c1001d07007210100111002e0510201c1d08150103180507094901c8001010307540c0401c0784007140c40928081c025641090301864050b80c100d13040ea4121105041c03501e565001003000203046100d070382c0103d41c511003c0010300082c0f05181822949214440940342c045488440400d07540e401120024940d0710600e100180009100f50050070585119040002d105a210302001540d40c000c40d00244520400a050160703a6a09004010080100c000b03050110300e4210041440e000ca00d00034200d03d6039000a00c80c0411001101c3c051030b00d00c060001300a50395140100620301e50001d031040e40300e0300c2034a02044160500c001c0180443e030b8140c6410304428a8034a040d9072a8103000a001d5010650265844816042d8640007280d88507012840a0070700c0c0c2000007a04450740c00602421319031903c48248010f032202000c02c110250101c5214040b140a2440103165201e100c100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 591766618 1250 591765368 591765403
    0x6200102040f06021504170c011d010c09050f061206130207050c180f06090c090a0311030624190504020d0603030e1806060d09020918070603050f0402010e0102 70
    0x16180402c074076a906848041d0700342d440351010303c03a0748400e125050b203018107060030444003010450044c5009004200c0540700200d07401c030160020142c0c00c2e8194180c4c1ca102d944800950884e01e502a01c088040c080840e10402c449000c18045900c034064080e11449001d034150119003699940c4150491210003c0400d5640e208540380480c0c0f00c8610890150141d0118181010b11202c00c0070440d02c107c00d165450311180e0b0703a41c02007200703046020340950785d94202002314a02c29107a100150010310300460038082c82203040414903142c00d02c001c2c841c070402c6c3c90411703190790705030900c032084461000110f034501510344205100984e50b000c203034411a40180f001036141c4240d5090b8100b070003260f019488000c04400c01703c0506c40042e40800000d00403441e43c5001404a01c3c02c180604102280d0010014510186034080707022a6400c0da1401c000b940d100c520922400d004106401c040c0c003c0d1319040c000d0342081c6406840c502405031009062103e844214440e036442040488042000203c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 591767868 1250 591766618 591766627
    0x6090c03060c020616050724090c03020f0d0f061509050702010e011d030f030406020d02030711011a01080114040e01020d020702011206030203071806030605041a100303050406200102 80
    0x424200402100c035801002d806070344002010100c015103003004991751500d56034034007a001d50b1450616080000240900c04405040280308545c600c220703000f9034456003203540d80c80c0c2140100200021b4180442e03200b41c4000800c0800110707c0040300f5100f941c02040814412000a045015100150040d0001900d0003081150035581504060071244442000700700102541c3e4582c590300a8000c20400d099004210344248110208000c1d40d00a01841005040400f00e0059106a0f070081e6000f000003003800742d84d40c01d260740c288a03140004c84041000094810701d200040c4c21402c0c144586011007000d4801c00210351655000035400e2460600210340d04d204d01c4842ca0001d400c0600f0503400103040d840c2c00d9809442912412003500d40040c000c19466250242029102c5010400740510b685c0300e00300040000c1d400d02885000c0c40c401c0b00f80b440403580030302c03400001d0b84d0014040d14080108040800103e0b4105003184e0988006140c11040310410140580d9215a841c5884a580d880003a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 591769118 1250 591767868 591767873
    0xf090201090b0a030b130501030605060a0302030607181203091d0603060a0b0105120106090f050105041d0403020a0519020f0409020901030308102103080c13050d02300c01020d0206040b0406090c03 86
    0x7c0c04a41a41c0c42403c00f000b150711110207201544401c2e0100940560013080410a003500800b001091406a8040001b400b621102e440135480c00c011022000308800041c28000066100c4010070545e80000b0348120914201c0c0000f550f400d006007603c0c00b02583c4850500d00750344100c0444412420b04961207601e943d407464020081c1440c1d1080c40c04009c1e0400b8040b846620a43c200c404450311241620058024030f81c3c00398400b4400703031045003540703e4440241c001030000c0c000c1c4003100b00b610031000000740071030042c00341c0c0b02c0c80c19103c54416841c0286140059444418050650303805152804e1269a080d5102c00e101e21290411060070700380a2241000c080303074249255010f0f209036510702c1c107610364415290f0702d8019262036030410004050148091305110f4400c0024a000070011000c41602c10400303c030100c1041d41000314190440822000c4040421506c5d000020071320041202031b407410b000a4840001800080002d501240072030f0600400d078126501c91b940041d5100d04290352031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 591770368 1250 591769118 591769121
    0xa030515060c1f0b031c051303120f03020705032d0403200a050306011e170c01030605031b060711090106210c141b16090f090201090b0a030b13 63
    0xc24050600d81a0f50084895049280100d00314800050000c4c00956a8481c05103d002003002c00d900c100041400800c2c442011500080b000714014aa4000e800d00907910040880c106860441c2c245401000f8082c00030390f0001c1111003034201c2075030f0540f1078070f66246000950f4520078410f01c42c0d0103002c00c0c040103010502c9004000d82c8100c00034185251018414405a000785200301d036855000000100011000e0100c0c010b01c0d0040c000b1004c1c04c0c0307a12104825011600400f42518541c40709421000558140c1318010107030800718020464560301c1202c2510701c110082a05001d80740109507841003091a1000c0030811000401e020340c950307107445009009083e400c2c0c80d61402d110f4502c600c00c968803d440360321411080350340c0c0e00a140c2e412090120513030740885407440c40788004400c24070304000b0a10904a086002c1d414180c0c00503d4072150000740c0b92005038102400d445d2606200050380c0102031071040721100c41c0419218003072030f60140c008040784041d80741c11084480b520000440107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 591771618 1250 591770368 591770383
    0x140a030b0910030c06050a0e0324060d0c0510030e0f060609010b0403050304050f030c03011b020f01060e06041509061d01060e0f040e190605070806030f030a030515060c 74
    0x548560440355100b1920b4000008188009000003c110805014180c4a0700c003c00301100c0500703010821070545400301c1d14001816881c004482130709003c804101e00200040361b003160040301e0560407006c058444d4880a883c5108551003500d5000c0c07106034490094100740c1c0c10005080940d01c5036040c100c0a00d8442600702c5031036105580781e500100da0480c401c01a10240c0703800c1001135051600300000c0c04800c2078400300f81c40d072503c1402e1010b84299400d01402c40009a280f40c03021090306c0e020720107440c00101421016159040c0242440183c1c4080070455001d0401c6501040441111084520200c0c064105812007030602d00c020552014100041c0f48200010100c0d4071795a90302c0508a0b04610346414140d031224030100041c401e85080d4000904e18218038081d540b0070a01c1c000403030400c40d04174504950740d60302c0b0010480c80b20340200740540d1002c4250094085546c03d0100725480b880740f01000c80c18145d450000c04c812058024442c800d1400140c03001c5e83e42c074100c40c0b01ca0381c2c0e290b8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 591772868 1250 591771618 591771641
    0x912181e0915030507060f0e19090f020a08150409052e02091c0c0b0c0c040b01020106060912030207052107080c0a12050a1e0b011e03080a140a03 64
    0x400d00c0c00004000820800c104480d081300c0603081940c00d1800c100c404001141040c000c000c60100c4c802e800c0d56484c1000c0c1344440446007500900707880c0801d01c0341525500d070941d1411728814003403104c0450700110216030086214644c2c040080c06034000400a00d003150014201d44984194070000d4000080e02e04064032100f1030070f00c03140e08040d003990240d01c2070031000c07a00003100704603550300b001081d42c800034418441c201c5050b82c19150101150719070400b8255142542c040305100c20207003450311075001020b400380700078841c1c9414a0f00c040d00011161044d12140c42001211909141c802d02420000d024000c00000c1003210109245c0c005040703a5803400d0840c01403403130000b520780c800a1740f02c0505401a02805402d4034007030344111107941c2c819066401d4021541c00c2c000103804990055841c80202040401052440c1004000c214050b000f410b6103422000f250010405245030b01c2040700c1d80240050350328941c440d01207500405283e02c0d842e0003a0045a40e000070358158004012040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 591774118 1250 591772868 591772871
    0x10090507031110090e1015091809080a050d14070509091602190c03080706050405060108010c08040b0727140306100501030509162303010912181e09 65
    0x3010300b020002042900c0c4404008030f60190390800085044113000d0740d00041d08002c0c6211156504040c41d0307850700b10315011000948c01c240a00850118070940803a40140b00003c00400645a0303481c9081d02c5048100b1044c0100818048030b00030958000c00d035460041d890202d40b6040000015043c1e41009004900c250003100019001144040c2514101e1006a0050142803901011a01c084160a205a550074450003000c808a201c0c10004c1c20b4062003100002403520301824407504186060b00170a116904081c002e820702540003510f15001901300030f803100b00b03481d040c00640d00e104080100601540000c184008070312601c984210488128035605418601c2407403c0588400041754514880d0402800910441d480fa5001a9001020704120b80240c8002c070072040c100d2070b2960225111660742860110039000038901c040d08103005600074460618540d461641c84116490b480c400c01c407246c00401d0f00c945421000100411044030810064901404524400030250090040d0a13 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 591775368 1250 591774118 591774143
    0xd06030b010e070305040c0605030a020c06010b07051507020a0b150d0b0a1b120f0e190c091e0c090911180904021005031302060d1b0e10111009050703 66
    0x304c2c00703401018400c80d8400d880c070031200e0074004242d8190704040d19800b00d0710b50030300c011619080100503403406409525911171f25821503250480c03800526020001120308024240080d540d0005074421701e05a0200003082c0c0b40d900c07900c1c111541000c84544950044502004009018070055000d000d5042e00c0402e01113007401c0d4104030030700c00c840d81c0e42200080305101207842c0100310352b01004198607441d0021074290001c20402e803500800d1040b41c1d030160701008003102040030b0124020001e112903e001c3c040c00c0380f42c4c4008603040c10030610912565485506144000307100c1e18116019220800c0e0401c068210f0a000e00300070340018079505c4080c0c0304404e0040d818500413110621490707008100b1080d4950840c800c451039040504003400c030310000c0c3c4000c1d0050b81d4030409055203003c40480000c901c5030004422001c2c6c02140c50020074050910302078105a03e600248009000e904c0c105440c0b080d4020f205603180c82c60000100780018a0601610308009010031540c0c12a4002c90307454859 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 591776618 1250 591775368 591775381
    0x612060e0606100c06060305060f0109140f0604020726040306050603030c060402191a12071d0105070f020409140609010209030d030c020f0604050705120c0a1a0d06030b010e 76
    0x41d0101982e581d40d01010041e40c03d51000e03c1042c070403207524400c04022603440d84d40d5540c10b140070340c1075a4801e00c0c105000014041040c10b44240400420b4800e01c10301a0f0406050502d0341c10030191030740c0e0246130000740040074041e00102004076038003100100c0034401d5030402045610f030801e00040b00c01b9810413010444a280010641d541248100007174441c0c0d403126401c02c55040c01100b44030307000751594000010394016500b4421580d0303000d03406a0341d49842041800314810402005c49061088810049082c4490b8003050080d1141c2801c0003541c03a80d0034200b080c1d403c051000f0095201d0700304000c0030704000d085000d040b40a04d000045890326115040300e54280d010318071149805901081c0945405846a00858000d8101c2c0c0180ca2400f10300c41205410041c045030191200c1c0d002c98407c00540c1001c048007080086440043d1100700c0a40000880f80b000a1160a10103620030300c5028008003d001100e00e1441f000c4420414030303030381b882c100c80e25100034890402c1042024001411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 591777868 1250 591776618 591776623
    0x9060908010b03070e090a05010203090303040b160e1005120a0b150708030c0a0c0501020703030e0f07031a0601020f0a060903140f070209040303111215060a05040605030a0207060612060e 82
    0x10003240180507214203814030002d400240d500800065547c07050b04084004500700f80700a41c050b1011201660b81c81c581814118601c0f4030141000080c03080c2078494980041e80a107685001d80c10481c1d210700d018111070011901c9004c7e50520000c8081c3e09810310a480003103512075100028190381c031101400954000d822503020303085000c0c0001c07508100045001c280040140491a4a4100000b100c0581d071606422600b141e0b05c1103011903070380c40c010001c60300200258000c42c400e00300104116420f5903a00d12200004000b40100f903d200f401040c0d450307009100e07581104403403c007120410f610506008000e08401c2509801150750700b1000000b402c502e50460340c0500b01c40c0c0c40c00b07140420341c0d801d210803e240203005501301540c410f040c504d51449040205003c0d16421501c0d1804d040c94400c042e211020040c099104840800041c00700303035000025201154032070704005807030390b030303019260006071044010040420346044001b21300c492042258800280c06144104829075208080b180d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 591779118 1250 591777868 591777881
    0xc082203050f19060f140117101b120e0a050d14090a0b07060902060c150105040b0a0509091c091509060e150d050907051f0c020d1a070906090801 64
    0x799200c003540b424020807055040140c0d120508400050b0340c00c211500221100380030380002e817083c640340403455842e08c02044041c40001d000c990400c00300b40d641c01c00041c0c03000b030400d200c818002d800710850070410440d4000c1c060503007002c042e2101c120f114038090792134403581c0d41100089a04580204007004d004400d44030000805400320707505d281015160011034101c400100c41082c0c48a186130016202e4501511490780220010940040030f807a900312100e2058100d40d015a02d401740b0008240d44d007507928805c030703801681c04242c2a01c50040042c10869801c0714503015004d0605401000c0c2c0d03100a403041291a04001c14400c51001c0508036400040d510840c0001400c2c0d050000f03540c908174522652441060160900d480081d409a00c183c4070115030030082a084001d08000f82d04042c1c107242004242076111000c03810b44001d01504000340c51002030300a00804129204000305108030390030b403600c03d400c4a036032072a10010040030b0340014007c00c80010103903040040c41020501911 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 591780368 1250 591779118 591779143
    0x13050402010806210106030c083a020a1b140d050a11010201060515130b030108031206010c02030114040c090212011a1207030c080c09010f0c082203050f 67
    0xa03001a11000c0411456020502101051366003d40701c01c1810030003441031100843c0b091030341000d664070b40607000c0d051900880403440d83c51a1f0128800c0e0810002030805030328500c0c41c241510000201600702e01e00948104024580030350700c44401415408404104101c89941d4221240413281f0018054003110202c4020103039071006040000080b4101b0384004030301c0040c8000500281d0740c0e80042c030070301a9105011001072001404804a03400300d8503201c060011300c0b00052841d45046441544ca119100c0c00e0740c00d411910022800ca6031007100c0f030b900c010360014001d01c4004040c0888011041c01030303174101e90b10144020006130601c01402a40d043d400038200e40d08560381b820606c0c0e0030a0007007012a00680380304002c040c19280008028600494056600117005804010701504500001d441c00158480c01c5c0900111a82e00c0510500200300d240f0f0701c00c40c096264507040c1b4290003459903441d008028018042c1aa00300411140c007220702850460703200c0c080e1006900d841d000c400c6e612 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 591781618 1250 591780368 591780377
    0x51204050f0a080607110c0a0b0c06011203020d181716151709070e0106080a180b0408090f030102040b0a0212040509130302070e250306061d040b0d111305040201 71
    0x2d030140c0c0500100034484040100f540c3c0347c00300200c00100789910540141002e04400f180080d40700c0c03010880a8098042c2c0c6055140901858a020750349a141d0851071041114209101c0008040b4000480c004c4c028808070700307046040445400d8652414100c81c0e1022a103a1400059a064290304075260b5492030b1079088010004141c1111000e20080080b01c89104185000458125a40e41c072802070455550300042400d0640c00c40003607c0410b0a0318204441c02501603022510307555009030459403100b2515507680b1540301269000842c9041194107510101c2e000945505600041840700902c1d400e580300321038000d85032507040c0654001c0903003002503080003c46100800d014284002d000340102c1d2203075a50b42038010006201250b84024440c42d400081001840321503500c040701269050903c00c1c2c07030515000038009800030000c2910340e04003042c808000d46450b400704d030305c00c0c802502d540d0096520741003505407580c00660041c0a0034440d00a100c00d4007251165602440e030583d40d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 591782868 1250 591781618 591781621
    0x90909060b33070302030909040b04140303040c09020c0c0a03082119051b1303140a050d08060d061b08011508130c12030801030308071103030c070f051204050f0a0806 73
    0x4034034036a078020b120f0860035480304001c140340035540c20810758499072251541c0b032030b1440d252034401c8603540a0103030448558014018000060b000310111003c0c1c1d4030381f0900580354203407c60321a02d4510049900c80d0000c000c21004420311070854003c049401d41c0588168002071525040420450308035200f0400441d00c46000003048140c3e0849508142c3d0015001040d419000c10581c1503808552503111038280398400b0000c001c4110055844141c5070300151002c00d005031541034075003164002410411240d100054031a9a031b0b000c484400c207821480410851140021080c0d444a00310f403041c001c909010000200d05034400c0c2d44a118020f10f0341c0e81481602c0303000041d010269051803c84140d000310902080001c0c0451084072200e00035542d2803e254903609000c0c05020004d0306c000304105240203902ca1007400001220307001001500d9056480700b0f030b8185841c01c0059404001c2c65801219401c000300b18007074016109480080301c00f404511a40e900708034905196100301030841d00b0400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 591784118 1250 591782868 591782959
    0x20304030c0e0a02091e04060e04050c101211091201060605070b06060403020d0812060303090d030c140102130303110316020906220c1107030203030316090909060b 72
    0xa04560491202c120142c1012004000541c00740d46c25003022480b040102c68482d541d1030b1900840b0000c1503400f200312480c1c1459140e9540343c14030369a04c240581c0c1e0342007a22214501c1240b90b200c03c007010200c200035951451100200c5544600a00c910400444000d0000f01c40c0600c40d030002c58221b40c85141ca0906155141d51044000404540d4800d00620000002d615810180781000f84100545962012407101e600c0c180d080240070b090013030b84140324003071003500c5043c80098200d03014200054000094a0205000b0754070302038009480d4000301d00c04096103280301c201e00a60744680c44010064651400c2c40e0394070300030841d071a16042402d10251015090a10780140c01c001d0141412203549100100b00d440340c400d2212100e4030540c0c6003022050300d540b2108941120003039401400c491480c42e000607603a800040c080349418074810001403c114092090b02c0700a10104000b44214102c904001c0000c050003c502c1c0d00403a0000040310502c182083c101c1103911658901c00014000304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 591785368 1250 591784118 591784139
    0xf061c150e070807050c070f031b05030309040216140c0102210d1841071502031303050304090f1e02090a031a06031c05120703062112020304030c 64
    0x2a040c6400e00c081040280329903031b030500c00e0b0000f403c1840d6440a6039407030b6180401501c0c0b5200715443c000d4410040070701c1941c4d400b100b210204101120091780300c044070406410740032281e00004000c5824040052041c0a02041d4541c1c84042602543d10300c0000400c0c1480310007060200d01103c5d4410045e8030001c95099121412000c2c110400008a403070560350111003152240381d8004652600340f850786016021490022141d40c14480014003d80a40009980348814041c1c24100c040c0b002c40c0724030711442001a2620020401808220299282841900e9070301031301500100c81d0403e8000e403500101f034041c201940403240703c50101001c42c291b81800039000308013035940c010320104000010030112441c241103009202d0399040941002c000b01890108041c400701800038042c4108500160003005440c607203402c420300d00c0301a80d0341e04000c4006041039081400c0281703a1a1000f02c03002d0b034090264804500c540400d51484940140030b0b81c0da07002ea444010304400304180305210a5101c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 591786618 1250 591785368 591785371
    0x11119030f050702030105090717070501080f04170301150206060d11091803040b0d150303050714011103150406050109050f0423010b0c15150402090f061c150e0708 72
    0x3a1409904003003d6600180c2510416500c0214641c03042900f8030002120740c11010080080d24000d102481c40c1170000703000141c0090219003040804c0380090305000101501720201c1c18002000c603900e41e1515074154440c140001110010f00c5640d000805a0034902d40e034203032854000d0780e074200744003912080082100006020316a4072480341c1040554020800150000d40a100f00d42505c03007500003a100c04640c40181c80e0300c544c1a41c8035040000caa003000440350056001034012100000004909024000078508a01000c0000007041306090301c690500c12200d030111800c4c44007a542e1001100c804c076080c041e141d80110b0b10b2440f81041d06c0c066020750501107030f070920403241c41410b5081c2a03100c1d200f40d000070b2309100d00081440441c14103024081a01c1c1a500a01c040e60501c07000040140c080701c52054082c680c00140c011440ea10007000c4510400d001700005e9680c420058200e041002e0518180180f03420441d000c48451101c00d02041580d50800440c03409644215086814110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 591787868 1250 591786618 591786647
    0x120702090c07050a0501062606010e0c03041b06050406030b0f03030f1b0a0f12080c0a050f07020409240501080a02040209010903140109140a03020d080a0b0d06050601111903 76
    0x9050504c800070300c00307000701c06c000e01d51142240000c2050f90449400901c624910041c5ca8104800600c041c0311840c0e00e098201e2214001c07561260b603640b400c510807041c81a50b03c40710500e030308400100d013948203009109903609654140038411041090084001004100b01c2c2d06030014401194100b40a001400203044429441c400d1b4101010205003405400711b003c1d2004402140100b05128242118220580c0b0038600200300303207000c5801090781e00070600524200003000405c40589609041a0382d01c0c150028420000300826140c00c83e0b01c0500d10490680040e0380d0034808442903c1481954103d4591303002030129030180342d00300070080d0311194800e13051000030100407011035101180034808041131400020740004d5428031000c8400034003540310055005144c242c0020351301050030060800c1d141804000ca4132650384a03406400400126908280040b41090500801d45c200b5070040c142a204d0b490354481803142d494071652024800250301a15890a8000134890f540d000903030712 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 591789118 1250 591787868 591787873
    0x20a0e04110708041d0c0310050f0607050d020616020a030c02040207020307150503070e0a05031005220812010608040c0e060a1a09040b06090307090e070f0308040602120702090c0705 80
    0x40c0c503070750f95070301a003240d04000c115460300c04e003000000c2e58104020360003440403c00c4a0461400d02c001c40003030740c014001c041c000c0400c280320090548440054031141c942c40403d40f0340c401e0314500c00958618080703c280007a000c0202c4c81c0034805001148c09a540c1750955206080c41c0450340910000c0d6210a10890b0944200040000c51880070030040d05501d103035030369140c0c0d01c0c00d000d40028418401c0e44046071140d89214403c1200d6580043c12012649114034041515136480403050059000341c600c02d61600c040d00c20950400c08500020301c1c0703500650401501c6a622020101d0340e40c0030490300200b807044140700074000c1c0e554a411b00c640c4600010101e074150b94646e407520b00307049540c9903114180400810b02401c149401c0c000c0c45940e042c191412414060201d0000c0d40d115105c0c86a9044542d450a1100d03448406008800140c001000454042030740d17071a00c0c043c180c2c481d10402006019900d10110800740d80c0d000c40315115002010351000d902c99010041c079540c00000111400e2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 591790368 1250 591789118 591789127
    0x10e06070203012d02030f012c010612060b0c190c21120e0f061b030f121003020117061c0b01090c050310060c050a0503030c0301050a050301020a0e0411 67
    0x5903400d01804804168411180c81083c0301c1c000031903a01541040001c11341401031080000050048141a0449244c17000b00e0000300c00b1320b000440c1003003045103807448054040001090700e581144810419000072001002503603514002010140950028050140c002d06885000048a0304100b03400d01c1c084d24a110040c0c1e40c481c0480801c83d03000f401070354030442c00c40440b070034001115201300ea0880745082004490700d80310002200d40f01c204403036510840004c42d0240079002900c60309549141d090040740e9a445a1003500c451503000440c0d5404018251000a07035516000710364003084070ba040c2c446075103100c00059094502c0200030486500500442400f028051004d43c0074109540540641c0d00d442d41400c00c804151140b00d012101841010001e00c100c80344440141e00c1121440d1411005180d80e501d002810540300c640b000d4036a00c40401408800a840c00040d4103c0d0400c865040311103640d60107140c02c0c0e015004044011602013003c1d641203044c1134000340c040b510f0407e0b11500c5c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 591791618 1250 591790368 591790373
    0x70b091906031d01050f040201110114010b0903010b0d080301150512100503010606050703050d0504032007050405060d080a030b06160b0610180306020a0e1c05120307020705010e0607 80
    0xe101564041c800003500c410701c00707031400700074020500000e821100a22252900100744402c6a07000b0300700030304101c4103400c4103008210039804401010b411424411255944c0c4400c24aa44c0003811028800e51074000c0610440ca098604900820f0707102925506503071800b040d0758120401400c0d1441030000810810022401074803106100d040300c8042909098100811300d82159202e40000b024003208206850109801c102991441c1400e0540070a01d0b5a840c0b8040320b06084013501141081c02c042e0300703844246404143c400980c0c0040e00c04018a43e00c0404001510701186009010681d040008001003031003a0041100488050509842c14803207030065140a0100f00050700c0d005198400d12049140011800030803242514041100c1684003142009103c6a44802824943d0004100400602413180c000c1402c0d0010051030381b601448480030009411114215094080c0c5940007030344440d0442564041c0c0034136401411580d0501c2c005442a00008805075440002845803000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 591792868 1250 591791618 591791659
    0xd0b15150310080304050a03150b030a0804031208010b09040b4b01410307020d0201090503040521030c0f07210b060103020909010b0315040e070b09 65
    0x2080e0000209590349014155005403080302c1d0041e940c3c0360420081004241c0d54810004280c0f5000904802c004845002d00310080c019407003d01e802d801007024000c180030b20174020308101c901404000d144448411030490b1151824060800000401d001e080c65506040e400f116101c400a40140c22080b00d4287c0a2420070f01d10b8202c0c181c2480c003c0d0120141046100c0c0c5820b0004000032190003040844006019030303000d0307010082070407809010f40b4403007000b14070b0301207250804807020050120585c00c0d904142d4000c4270740e04050b00c102c00e94400c0c0d89105116051010707800c003000d141024141001c115040700328880f001c0d4414008501384800030001c1c00144088030314200203240540e204441c1c3c0313081c000702c0c0c0c4c4100111708444503c1051040719001c1902402e03032140d40095940e0722440103800a020340856280c000024078008215110110001e600907500144490200c000c44000c200a0300c6c0314045021f0307a504a0710042124450030b1002d410000d4008006c00d1005199452101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 591794118 1250 591792868 591792889
    0xe03030c100f0609090b01030f0503160807060605062109210a0e0901120b100315050901061a09060306010201020f030726160f02030906040306050a0e0307020d0b15 72
    0x100c103103070380b50015032151205101d10310042101e05014003036072101c0d840f1040c1000c014413001d00400d1640c250380081020600c02c4542c8032802030390420000c43c180c2001030003a002280201c4000b030ad05040030034145428410b0311881d0000440a40050900f4035107805070320800303400807045200d00c9105200c45007422140c01070f01214044e8003034940404c0400240350303180220400f809900110014800c4408031345114607840d4202e225007000d034807000c0c0300c803655039255031015010690b5144d0400d01800c96400842c000c41d150310080c4065500c0e641d024100390750b0b03000417201c5c1e203c0402c00074a2904050000c0d40c1d01c44030500005003886141840d94040341d100312124400100003901031104500310a00a026810140e80241614a081c2c0700b803100b61550750000c4010f00000c8001003903101c0c420021220300520103403440340c0b941d0b944e04c0c1c010b010b050190340c80a83c07181050020110f20f0400800d0b14225600144080a80707001a11803440014001c1e00802d011082007004800c19103600e244035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 591795368 1250 591794118 591794143
    0x402070602030a05130f120912050105071103030601020304120f0b18010f021321060f0c1b0c0b1b0604030507150504121b0b01090c09060509100e03030c 67
    0x160781c0c0e143c258910307000c481c001404a61a81d2540e90740c41d000c1505030200c07041241e88400e0791620019402d50584880b002640a61040382490451a08002c41074002500444640d21050640c0c440e035020300e61640000c0b940a401a03100744010031803074060108850031607000384817030070132000315403107a98804c941100d4601044050f0032a260305481c00740b29010145c0207484c1d0841c1450011140038003504100c0c0300f5505c801401104144040504520004000e82c0c8084208411303070b1900080300c00381603442c8038100480c50b0903a0b1804a0001d500340d11018139800102091480c0c2031660020a03a00b1140c00000400201100c2c0703480000c080185600580c02510b8841d1600701920f80f03085035041c1c0990b1030650b1401e120501000845c111500e1003151240d082c0010005c0e424050181c4141042c070001d8000b590020001480140c03540c8241040c05e2142d0f101340c101c41c0c5906050303c5a115800d491034105201c02c0c40f03100802d215000d50303806803c008094070300c2d0110204d501c49c80c010610817007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 591796618 1250 591795368 591795371
    0x207210f090b0412020f0f03010e070f121a07090b0a1707180e13050a140606060415030f0b041407081008100c05070b150a09290f04020706 61
    0x510448540004400d4001c0c00b0300c503910307803a16091103030282d40c442501e04000e00400c2005041d0500b07540e048a20901060041c000f00701081c0d05c4090f951ba03850240c45540e240905440c2c02207034407840c6a8440c10781c2c3c0d80012040d41040f48060a803024208003c04550802c09960030201d0f002180e08020000d071009980c4580010703680768039000040101603c03100074402c00300340920848029808402c00c81e030800d216283d503903444aa090f184e0410070740740100140240f55400d0108810002e09800c032070000002c45105503510001e00415111714012410200340c0b21135600d254a11a4100d140c002d04250400b28000862601207801d440012040d00a10961a0200000d15601442c040e90145a10500c108500d107080f0005403038420722355800b055140c842100c401c002d8014812075000c143d11a405e40e02d103262102c9400207041d94a070505204080703000f40019050f2807802002a01d08a07030701c14a4500191038024031a250b14211602d400450440c0e60718000d80d22880a840c415029460 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 591797868 1250 591796618 591796637
    0x50a0305030d1118040b040609021315030c0203030a18060507050d0f1104030308060a030b24040b100f110f071a0703050a080a0209030a06020c01050f040312020721 72
    0x245601640c3c242c0382c16032115081800071058020402655218100059030f000841a9099000c140074164581110014500004e66441d0003c0d141c0810005c541c0d000d00313101c3c040c04620b4001c4040d034454040c1d00d00181d20502c086220b43c0319a030b00041d80c0c041c041d56a0a0009400e949410a036001190141d000c1a00419041c40800e00c5000e031240200c440c20040080c07883d07652001440c0d00560001038108602180040c429882d207801203000b850b00908845a00e140c4020b2180404811880e0f0140d54090f040a00c10141000d004030700707100100a110305850901ca0300101c58442c1d815079200100302840600340c0030280284140d01c1c961a520002c1e20005081070180e0401c0741d03920300e42d1070f640cec5801c01c00000800d41c4582134074603c52052805841e00d4a03100d0b540c0d0003a0181c01c0b0f0043d45801005da18004118169008040c101c100100a00c0035035900600c0141c110002c079000307004140c03120310a510120103540108803d51149482c0400c5050090101411510003500400032804404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 591799118 1250 591797868 591797887
    0xa080c0609070305030d0f060305010e010204081b060301090506061303060b010f0206010e0105010c17040e04170c06040b130501061503360303112706120f10050a030503 74
    0x40055030240340d04008140e4145160344d01a500e00c611741840b02d0b5141e68021004040d101ca410120055030404002e0021088902049000790300078402c0030954032501920750020780b0b007481c600055400080101381960328200040d40a0027008000c03640c8010104218541c181104040401940c02080001303a0329448100140c51014006d00c4d21007950300000042081003610880706065820078688442003400c01e20741b082641e0035405c0700c2c65040e0303404540860440c03142c40c1040c1c031944c000c5443c02000b2112182d44a61031160205012050b0070010000340030804ca240010f0308241c2800c0c825200b0051a15940c1c21038520760800c201014008038012929503041c007400c4204104505200c8480b0040c030b045d00d0006447c150282c05050024001005050203030340003240444804003071f50307a9506480030012000c1b4501600c46545150590810180d052a4056a00c600a12215003078140c903031017880c0841c9034006250000f042513807103003c00c8584075242908000c522410055880d441100f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 591800368 1250 591799118 591799123
    0x40203010612081b150108030901083102010509030d111c0c140721020102070b04120b0603030d0c0206150d02010806010302180411070209010503010c0c080a09080a080c 74
    0xc2d03009103107510112081c0300c0402c04000884498660403102490a070480780d50050428041e4640a10700201000000400120100c01880c01d10300c240c0e1001d01d41c1c1e0320807500c81c6800b94040881900460010340780c024440c1c0c1c04492008882c014100346017007902030b00c0002c0c41c00a0b000318010008902d0040450f04075000c000c00c1034030b840744044101c0c0184d00c49000a061004108018022903642c00404034681c9040c800c030b02c0500400004490380006580441c0401c0307581d02c600300c2c010301c102000002c5901080c4256006d990003410506815145502c43c03001d001c0d806040c56616000420940403085003502c500050521585c010702503615024400c04100c00d020340c3c419004940c031003000c070010303039200c1c0f20f1b240c1c081000d00340141c0740d91441c1e000036640702d5245009600103152a40413140680c40cc009840c5c168070880d50140f40760380769418182601e04a40d002c0c00414008a25000055071640c00380442c501036292810020307a40c0c1c1503091401403004d03400c0d01c036100001040019080c05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 591801618 1250 591800368 591800381
    0x30b0a06090e0f0c1608090a0906140d08030c0c0f0106090501170303010f031502070609051c11030d020a0512070314060907020a11010c0203070810060819060902042304020301 77
    0x43e110851010300d0725402118a40c400c071000f982500004410420800ca030134030a481003450042c0c524003110b91200c01420081100d4016040b08090f40703100c80302a40f91101d00d9000160b0b00c81d25841c01c680313524010742c0036500b1802d00011103024858541000050912400004004103c0041842e52400d03001c40d040c100388050146880d04104014480b65108200c00c0048a50244882c0b40000d500750142c0024052900700418aa040403000024008000742c41c00c0303403003401c2d201e140b42800388035400d0b1001480901c1c0e641e05600244486400403149074007500c1303828003c0c10403a141411189030882490070440e40100801c1d940c0348040b0201c2c3d8100b40f40c962008054583d0b5105082c49240a5521544511b005088404103e03100b0b210342d102e05406100d196025081f42d000a449003085520f901d0b10096100d95580b61100c005000b2100003038003403456020700709510001305652103070005001d010500341e81040d00e4846064000c00000e0440c00b4a0b0b20943e0f84011600b0130703204140c2034585 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 591802868 1250 591801618 591801631
    0xe15060a08030f0a031e050403020c0a06090e0a0207051005010f09060b16060605060d1d160e0702010b100f0306140f0603040c0e161b15020a030b0a06090e 68
    0x10111414410010000119003000c0d16503c4810740b07420403010300b1000342115030004292103859224408518071036030000c602840c8039400b550342c0b044010342484010002481450001080440c04100741076000403c9900210020400743c90009561100d62400c1e400810013841140da4000401030030901406d81006440800c2091080034500b800b10403483c0558031a0310f100d002c16101e02401c10081d58400001044080e02d40b64540490f80803550080114104160b82c6107003444100c80b08d151f001c149885280c41101c0c00503403490400c551000d031320100404d1803081d5945c03019610400e580741d510f2510850f01d10350382c102015402000c004c0581c4d010341d10028100c480b9810540041d40c074810a101d02c0a0196042c54683e501d1341090b10080015600480d0f0b131821040921200030b00d1b100764107007100a1900c07900c002c0214030b00c1044c251900150060320075008540c05c0c205002c41500103090420281c42c0100f8003406150000700c90b20001c0d030051300801d54a0104010110b500325280d0303070201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 591804118 1250 591802868 591802879
    0xe031c110c01020d120f06030c14040b0a120b040507081b04150f090b0d021c1a040201050901200d030c0306060203130504050601123801021b03030d0e1506 68
    0x4c92043c3d0140c0080d1400c1050040d40d80c0750203104c5c00e01c82003035220000950304640c5070b010301680c2c5d00d102c404c08002c041007140668101070070f00c0340909148008030101d40015100c210804915102c1c4400c00f480540221100e0003013130000526240c0c2000024620221188070b11038000843e404c00048664601c00102d4401c80d094081044251002c00601254407141d80854100d48102c0090b0a03568448402903002c900e0a00c415090301b00007640d451002d02c2400300c40604213100703849800c6072000704c40c000d00140040018210551051415103040c80c681707000c003144c0d89590b016060420101140b1180000d90710b1001e40c200030b80c1802120000c01150014606e040104403000c42d4502003401018010350b1294007040143c2d00c6008420003200c2001030801c813000010384112100d0568148d0030f00e038004000000800c00c4105100da090f0080160002c10342000701c0b80f4003200c0c40710000c40c91a8580414402d0001148103401a026490300ca600500001c100000b21074149030f10103802ea80c02070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 591805368 1250 591804118 591804133
    0x9011d060f0c0c03040914060307060903111306030807050a02011d09040f0521070b070509061b010e030c0f010e15010b130302042d18030e031c110c0102 67
    0x100481d401542d0450050b25650750348890100c4030510310721584e80811000d514085130120076255002a180c0991800c400351001d050b070707c61341121812a107020281c1100310b0007101100030310389410300d0501038000c20b1001c651213550383c03503030300280d0402c00f01981c150700922265800c540c0d000703105080645404401c4001d43c1c01e9000858040c0c50001d200400084071140b124088c401c0400000172140001d01840100032095107402801c0d420032842242c03d5421074001c642024050000e603072181e0805803889040200082107403040f038400351800f035041d559a054894070400140000c0c030102034114020505800581c01941c21140c01d08859030064000c1c0024080300801950f0b25411034240b59909500e07100d500c812400340001503400203621516045980c40b03a4010780ca01c01c8540d034601140740012141141c0002c007034421090300b4070019100c0120010029000c0c2c0d083c4410103c01400b2a0181c0d03c021004c5946407040803c2c1c030011854914811076024020401d4941e103440c01e00c09030200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 591806618 1250 591805368 591805381
    0x4050303070e09160c0620040303020d02010204051e0a031707050708060601050910030e100921200703020909030c071202030606010c0201020c10050a09061b021504090509011d06 78
    0x1441102803581304004c0000c17000d80901840da0007484a111801020059555600a50400326402403104401501506844140950041c400d440840d04098030724800400c4803885100c80d0950409600d43c4002d0749000070010548040175000015000a4030603603403411410013920b04905a40703c42d4080d4014420000a6680700e415500500710585a02a001d4949201a0041d040201e00c44d0407500ca0481304c441c0024454010400700f9001d0504407800480e0707031641c008408036402081c80442c41c0c10041c038846482d90155040009181e50954480513180c1d80080c000c2c00c0141c408481582c408540649004414001c2c84001c0043c0d66802482071555400305c0c1d00c80000900050500039010b403080c065900074440f20051700d0005110300540945d055025046410510390440000c4000c2070101c1c0e03075030140c400858094602d03040c0c1820880c0c6642045491840c0d91411400d200050000246024580c012640151b5100c0c00114880b0300445c1c90200c1c000000340780e11070680c8014240401d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 591807868 1250 591806618 591806641
    0xa06111803031e091c0f020906191703091903020109050901060c0609060f0905060f18060103080306190608040614011503110913140603010c053004050303070e09 71
    0x2480c0e04038528441c4c480c070010001440710300982c2d04001048003000850400c00005501c11044a842200e4a25107a10341c0801d010000b26000c40394081a0107180081c80b14504403140d10090351208000c80346884001e001080c1c0c500c1140c1404004003c10384010720441da0400030401c003421003603d42e50f8440d031600c1402400d044003400050b09140d95041514240326850300200d41ca114030600600c4165031a00d05150b5071413080b20351042c0140c100000c505100440e00100f64030142c40760041c0b440f40d0071600c170688190b03c0038003800d91295407041c402100703180d40c410344030050001d501c1e07081d0b0600d41800c0440130789207010381e90814040041c0051121141c101096000102e9901e000039100e41c1c00300ca03107910307441508095940020303400d0400c3c1081c000c5800000c20326880c526400c00303d031159000d00d13003a0390b031600744000844c40c24810b815080500f02e4214421000207c00d0303031040c1d5415991501c46400540d42a00c054200008003d1010b40000d1034041c01101503800d1410351508850005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 591809118 1250 591807868 591807907
    0x31211030702102a080a0c09050102120c0703051c020106060206010b0d0b010e0a1503061e03120c021f030c0c150c05070b13031b0203120703020a0611180303 69
    0x501d035545041c03400d01410245020012000e0104000d400f94104d0700000c3c10000048894255050400c0344101510b4030a095a40480e038042c0c0082ca01840004803141490300f01001ca48818491020000003049041050780600c1808280343d10003080e010b80c000742582c5164215006543c401c2004014031030140c021515130f0030a03d031002170341030548001251003035004c41c01c2e6544950600740c080341c0c1c05140c10540990000c5502c2c100143e540c4c032030350407010004807038501030070105560041002c140f140c040c8540c425040e103819061288558000342c002001a40480000d80d0a1080102941d0f090b219011806000b4201294600c4480da41c5095114420482c24903841e21680d403103001c540250151030045500c905022000c1c0741c903403003850040850540c07c2d0006020341415003c208024480860201c0d005009040c441000120054841d480742c0021402c604c5501d001038046034141c400c283c1c6046c581c8203256500c54110380c411402c84541c883c490700c2078004002006120305201d0030b88 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 591810368 1250 591809118 591809143
    0x10215040506040b0414010608010c17010b070f15020a020c0a050303070c0620150405150c07080a0e040e0106050f040c080a0c1b0302060601080f010e1f0f03031211030702 75
    0x4130219034440c60000b450b4110182c42405660034040c02103401003041d040300341c0600b060790351843c075003136242950005220700b031150841403002002274501041c0c444a4100d8460b0090350501101d100500b9035504a9200391030110068020605402c400d14000120800810080300150f040503001e444050b00e90703455118290a000f903e00d90041c1c0314030b0141c0340316180500c14080e14008491194043e1109004450880e154000c10418210110a441060740a124440a03a5041c4502035544107650b0740003500e8181070121800c0c62045941da58080c007031541e0240c3c000030401624050620104099a48403244598181f101000303c00e50300401e070726800301a0240104600c00040820b40b600d0b200c049820240d58810003001003450740000e4680e00580c0b0a80e10000c1c540e82c0cbc3d81d24038103000400e0080c2c1106481c00c43c00329050002c2e01104188000c400c0090482440d0340701c1c250040548298011030100d02210282c015800d95071060389a00780d50116403914515110b04004d45840d21071105 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 591811618 1250 591810368 591810383
    0x3010e070e0f03191505070c0807060b09090c040507050c0a0611090d032a030f0e12010519110c0607140d05070305180a0201090909060b0406060e01021504050604 71
    0x249a680c402000802000c0c014060313032014001300d03142c20701200c000902a101440c0d66075007220284414400c062244a4594944402803855550501140c0c0003a4080c8c0f1aa5114030700c114081d950f00c04594020380e104c00080c100b8080d403c06200c1641c0c0001c00030b0381446030520001009802c01310b0004034140e44080c001070100207185080e10380c1d00400800c650441c1082642200705904000d81001c13500300001c25107104c102c8102c6450f4074051446008001420058840c05110300504144940120050200300c0120011100ba400c46008a42c07021440c1e81c1d52410704484001c51203042030704500c0100715031070801c82a040f0b40c0e0324500500400d0822140701c1c54000f0b00c1104205139001180307500810f11150070000c100130050b20066601c02c0d4014603103600c000d01560006841401c40e0340c181c482d005440e1030460789400038500d0041c2a0f598685070b1882003e80e03941da1150101408a41e1960b15a01d01e14500091074403021a102d070f00c000300d82c802480b01048002135142da1183c1c1c070490 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 591812868 1250 591811618 591811637
    0xe10092103170705031e0705070b0c090d030201020a0914061615090c142e1704050703060b0303070b011208042402010c050405090412050906030a02030906060603010e07 74
    0xc080703a0100c0001c00241104840341c042c48083c0b44d12800031030040c0600c1040c03004404600095100511040d1440780104004000c050300140d070f00c0c440181c4c40400580268202284480030a44212040c0c00460060f5400181d0441d0b19400c14550006401600308015111070081e01241a40c400c2d600f1b608820b216180350001048519042842c4814206400b8440b0710840c0c40c01018020b01030041d03003280130318043c0f00d00943c102010314180102411041c0d03808030040402050b07400944009020800030101800300c00310501d03150381c500480c41a4000c1004c0d616604010b03048071000383c07807648203410030444580400d11308010181542d07203817001143c1c12801e522b05840780e4815540070041d0050380d81100b401f45000d0702d480900306c4025800a0203000a10401111640700b0b5000d120740c00190100400c0110314498811201c0c01001d0500700d00e4114020005600764008a480441c501c0d000010004140800d1160359003060f0f054074007500f90f5040000c40c0090150082ca04c4040043c0102c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 591814118 1250 591812868 591812873
    0x10c0204050a090c0905070f050703080708040503040f031109090f070626010b09040e190b06030102220f0603270515010902071b060e010809120301060e100921 70
    0x2400f250110b9802529200116903850b0790001900c0101c40200109801100144100380900200c5030700c5030b4507654404c02565060b405541c203040190081d00c0d10b11082c040030507440100301d407000c0510300032840c045a10410004000003018000d01c01c42d0503400c100203c0e101c44a0020703071601555100e0034200001c0d44000b07030001c22643d820a0380c00f00300102000000d080031100005080e2008192011b0209240360843d01c1c3d80c4001c505040c4031003007000852013000c40d40180e0242e41241d8018005450300030340e1000a0b80d40c0b007000b1010070100d04008010420880b0344140103005116604040c494100d0460002c48030b141c80b220312450a1420380200000c00c10b007805200c1641010150302c2c105541c48000020081d000490216204180360125801480b441e5503100111082c581e00d12041c4604980111030803500a000004144140c40062441c141e03400e02641c00380407943c0d1054044000c6004001142070010860350900c28421401d02402201c0f2403055a24880d80402c0a414038251 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 591815368 1250 591814118 591814121
    0xc35042003150114040504050d0c030507080301030c0806010602060106080c030402061204120e030a0503090d0318060c0213020915090604090504081b190303050a0e1e0105011202010c0204050a 84
    0x1a0310032039140c0515620640e003400000341c000d040e280103c000048110441c01480102d4000b03650180040e4041d40d01d0180b40d522500014a000c1d110b071030120b09100040c3c2c0c820005401c281c000300c540c2000d0640500011030704001c00b600403c070a100801013540b41c00c50141c841d04002d0304131840300c14000001001d5480c1d820484038040c18001c0b60300d000b4a068206200410010f01c000300c0018599048481645000511004001e400a01551900442c84104007082c02c00c180100c0c24081000c0ea03c8030141d400498403001040c0e180c45404050203d032040205101248840c244194410b00055503240c0358442c40319104100140b1040e595a03020f00000c180d801117130312080180b0301b02010001000345403801ba040402004191202030b10110030303401d0301c1c1c0c502d83c40551142000b1407015404603219030410381d0011070000002501c0c22200d6502401c0c032010801180c00b0810000103405007400034030505006000407641e00c40d4031156680020451101404080d10580d1546c3c08595248101d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 591816618 1250 591815368 591815423
    0xe0402060702060c0106081b1513080307030e15030702060f0712020c0c1f1209080702060406020c1021050901020f131a0307080a02070302100c3504 65
    0x3c10349502c0c2d00342d100405010b44801d00800308507002d0710980e1b007008100c44071044113044000740111061044580e1040007500165806030000050400c00540c3c201c050000341740090107a03544000b850454424845044001500081c100c0c400304100701f03086070701098854000503000002e59542d2078040080303038070044034070b9174801003440010005510100010000d0000505494001032884000c0c4007864100900c20108088de856400c101d43c01d06003030b070000a60b240314481003400c0802d55004079140e90411340112015a101c008074266525202d00001c000c0c030241d10b002078144000c00010303203040c0a10107000c03e8660b103800100c0d07949802034042d0f84984a403a1043c03512801e0303030001040c60284038411800c039554003501183c0356103183d000301e0388220400d071038002140d16100183e80080d84602401d90850080322000c1640d550300c0e00440364014490798846110010090070680c020600c40305000c4400c00091410220700340c5104010340c041d030412010084510410460f4117800da5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 591817868 1250 591816618 591816623
    0xf09070e060301121502030f0c0a0504031b14030f0319020a0212070302010f0203040b0418021303060204182306011b050601032a090b0102070b1309050c03100e04020607 74
    0xc04400800e04c0b142c4054801c032445e0240c0c10f03101041601c0c22401081b840182c4259010852034000101c50110301e400402d1400420300d0001e240541c1c948074540030615030317031940112001d1070404000707482c3c021070802d1100328101d018088401400c1e150030343da0320900303010401da000c01100c0894068003e0220864064002d040034800e49045040750761260264041240410f02005400c00d40610020a0720141d9154602c082c0c6403500748582209404045804611141e400b00000c80300c2e803611010050040d0320500700036840b58100300ea40800f21b800305101d245100c1ca480306198010341046428050040a60790b8000c040e12660f0040314148000d4041c1c09403515012400020440b000603094101c0c2d010b4404c5100d18002036804d1480c04259144003401d02075010000d002c0100103030301c04004144140110781c04e44c0d540300800c45045c1c0002d10361650070015928204029005da0003001c0e4860840c043e07991035464a01405d034400d00030f5004440448c140c0c140014110b40302e03601119107058 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 591819118 1250 591817868 591817879
    0xc020a0213090615170a0506060d06110d0902120a020a051306050a0314011401061e030b1903020a050409020108040602071e080c2b0e03120a050a0813020f09070e 71
    0x60080d1500242c44078184158650f00b685c0d502c1c180d2040a010825540c00baa001e0040d0569072a0362080264130984c0700d105031044d90f643c2014683c1080c101006081603101c0700b01c00b1482d0481e0340101b0818a51164400525400024800d00165500188641501c4c000c40d00c0c242e401c41400c80100c000c21007600b0054000c1e90a80010041c0314496602001a81c0741c54002d11900100540c0b0b004820720030b128580106618000c0046040b5070103a249040c0c0045140000d034181c0e2240004410b4a010350900040d101a41c03424804e50803c000088068070f400d50342442031001035070000344003c5000b0406030045038003280880800c01101405e4042c0c00d4108281801c2d0703140c90401100c0c80e40207004140c02840b90403898036000d04072402d80032018000e1035070f11b4002d02e034940050702e80d40811201503615004030582c1c9014200b04001800000e940f03540c032940c855007004401750074800c02500d448516000b2060a00040c0d80d0540302e00c0080c00c094941c0e15013611600c8069a16001c0e16484a6006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 591820368 1250 591819118 591819131
    0x5040e010b03011107060609060302060a030b1906050d1d07120f0611030f0a14150a1a0304050708070513020730020c090c0d38040f0c020a02130906 65
    0x5113134000c00381000c18014130f010040c0f10354a8000720108c131114840250070640c02d00030301c100c0c140030b80c8c01100f60240c0a400e251800b2540401040c412546030071410100f1030100700055010201e104850803081080c0d6603280744504d2080d070a50303078405480741e20218802c00e00a6410894503190a221b9030f42d10610600c1681d1410360b000e8100c1d0011501103a20240080010340122464081c000e4082c00802503560603480d1003c209049201598086070440d5501c0400a00d0010541004d001064090081c070b46074245850511306001040d44428020742c8031410500c0503684005005807a0041e402c801a034560961030a0321001c42c40c0c0320070b2601c40e5048010725071008049138090343c0c20b0b82c00341d099501c1e24003601c040011004c001d98141621382c0c0705114a04c0170500c0b9900c4a000fa01c008000c000c0d04908000100000c240d50100542e0032101402d0500c28909041c040c141030703c100d003c01840205000d1f180290b5039420280081d200e0741d0a001c64910210304d95212a80440c0c101030f0500c40c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 591821618 1250 591820368 591820391
    0xd05070e190e0d080c030a021b01020c190c23131a150d05090a0b040507140909061f15031b0c05030a081e0403020606010e040608030405040e010b0301 66
    0x219080600c400076a2400c05414229001e0041150000310005480d1034100340c4411520b9281600014400c040b03ca07030030001104002080b100740c408103001c850015940b840c451820304d040c040341c2c1c24002518080240f170744000600411282c0b0940c2c283c5010300c02016502e440f010081c00e103000005402803a10b10369400c2140a9405c05087ca02e400f10416103103010700010311850501e05036101d03c82800900010708004599000140c125080c1c0040ba02280c20940790450400401d5030121802c3e80301d142c0800c11413070442c0d6a45000c07602211010020300d4000d01e003e407034540c018594a030a281e41b1207819400141108040d0240401e1010400c20f040c0f000070140003070280819059a0100d818010f90034036114103da2400181c3c004091400d0401c00c60003590071130000b40c0380090a20300207190380b0004403154110780c8224000d03801000f407401c0070700024211421005d601400345003000404e200c0810000200d030200e40d4250340001d22035203004901401045803000707035603140d400e12400809 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 591822868 1250 591821618 591821641
    0x61e14040b010b040605040b090a05031518010c08070f1106130b0105030604020d140102040902070c0e250e030a020a0915060201021603050a170a020c011103060a050d05070e 76
    0x1003284510303428075159032503070100005801980b280c1c40c0012002c01c070900c03c0e0100c07513001c0c01401001600e042820ba8a07100080c0c20031340e58016040304070301100c1c1040340742c200038481849004170120080041000210000740400d90003010041440039180031084407a03c41d408940c03038003203018261480c508013500740c0d200310404940c0035250780c00c44000100700f602d404549680107a0b80184100f0400780ca0391b40d40c00505803c1c4000b41d6072550b0a200005440040380001c0190920031120302200714100140449a088042d1044105002103044130705000d11b2110341c040070361001d04140c1d0410350707034400003494058004802074104142420000b80074410383c02418100c0380100c1000c06154a4010881c01c03401000000c101d100150100c500100780248010858503c02c0c3c0361583d03c0c004105040c6160310b0080d14aa4040d65000070100e1180a003845508107844d14080600e1860412200082e10208075000b554400e221021030402040410884070006114020107030f001031070f08414011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 591824118 1250 591822868 591822871
    0x504050d090501170f040512040b190804030e1203070512030105030d11151009021809100b0d0b040b030607030e0706082511070b1e040602030304061e14 67
    0x30082010303194041429030084105031400d00c0d02501c030320566982ca001c200b00d5444060025515405010021440e8051b00320091002d01b40120346903a492503042c1c601f401450000c1c2e81c60042000302e0b07081c0320000340d04c040c008010240860b041d80711b00c040764401608503c58180020400d204640d0749002641e40c29003d10704845086042d10015040300405441040d500344081c461600b14085e005980c650400d203003600002d02c4501110140d4803400c00c8403ca0740000f0040c0a40c50041061441c20710707041700c0499002c402e000c3e18440d003526044100c885030045518900f101d40e1100591052601c807a44241400300004003180d180d800c1203180a401402e1029000302caa001e80000072440502031821107025800007440f0340c4001042001c619601d0314404411002c004030404400612002081014098605007484666071754010401403145110320b10a2000341001340020490243c010083d6035101d83c21a102140040d0b850209020181d01550100c02c41441c03c032110940d0411040740c40e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 591825368 1250 591824118 591824143
    0x2071109090d02030f07060b0a0305010e010605100e010e15070c031403070218040c18020a20070e180111030403170906061201110a0f09140901030303180501050405 72
    0x905407610364012054a542580b203140c80982d20030003900d05500004802840780c2c5004500001d41d80000c00c0c0020310095260344143c62980d100d02c60030702d6040003846030300f00410302182e1415030003504080241c01c0d02e9005030441c0c144940c3c000114903a840d20040f2604024442d508070b581c0d200c40b454050300c0b0403180d00080e0340c1c240c08c200500303203080ba00008a510150300104025050b4644a00618903000000d1080350041c1c2c40201c00640c2d01003548800620100c0c640c1d026031039103e44076006184076204000c405481c070710b030b400713185508601003454410f8524481d08101140d6550309040801c00e809401c0f640d5562030034110610502180d000b031400340d0310aa503071040c20748880803045580e2000f0f542c03854107500301c1c802042035031918807401c2c403401c1c100200204940c00f1480a098980c1c00182040307001c54030020800e0602503000e040c40000c4d000d207207010080ea0052030f02152000805001c024285541c550420001d05c0c418203402c001154048024801484d00d45884d07600e80d42c059001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 591826618 1250 591825368 591825379
    0x317070627050706030612060c0e03060f072d1b050715120b090114010e040906060510020f210c100b040b030f1506010c0c1d18030901030e070504020711 67
    0x124070141700e80100011514003541d141050003071501c80a00801c1041e408206000303005012650945003801440e1040c4903211040c07c50317103048400030f0418100a415200c000340e0481c0c8000d41c0d8003544544207140016031410490000c940d42c000010f5100014010300207100303140000812540d184090b8214144075a01c1540c51051100790303a0980d1800030300c0300ea012003520b005010341c2e0101342c5a04569074051510209140310800418219080420151402c58542d88113115600300390560441c084010310052110105e40d404942d1540108901549990010700c0300c51002c0c0085070a42e50059044000c2d2103011031a18a088021700c07241807502d00513400c0540e030780c0c01468080741007025602410050580141124a0f688400c4401801c5605001e208180d0102042c0303440400000f60405500705007c003401400a14001c5030002c2c5000120300c54004000344282000c003d0710903c030001c1c2000306031102071200c61801d0094070341149401900c0810750310148560f08104804502c0706079807 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 591827868 1250 591826618 591826633
    0x8010606030c0507150b0103020409090b04110102060405070e1b0406031406040b0a1a0f0307051b06060d030c060608100c0306080106060225080a111207031707062705 73
    0x8066803c0c0c01442e10107803031020310369241c2c904441103401652242c1c00514005140030b86645075001195004401901c0141d6010101f10411484c0d5141c50305842c400d000030086446c2a0740c43c1560340000380513506030400c801006c290854504079510b8440c108071031489032610b45480c40100204100103070302d020341079403901148950416128584810001601d42541c450a08207510180c0c0100303480d44040c4a17003084010305004505010394003038900340d6203080c3c0e0340161408508040820300f50700495904000103014250f9039810440d042641c0c141042034034070b9014280368004002c5030340000d102d80905181e0f40821206903200c011540c0311500c0401c0070540340c000c01e03400c0b1025070094801590041d00003640d04503086241141d03401040388030b500d10b6600e501015051115000045590f94510395222a052400348111114045d800009184161454031010034515032000c25100d000301c0001c03030b101408005d400c110402044000c12109020303a0013400703000ea910b00503080d00c25010300d28 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 591829118 1250 591827868 591827891
    0x31c0513020a1a040504020a080115030e07140418140d0c0507090b1906020309041b0f050d09170904150e0601050f041e030209060a0303080a0207060b0a0801060603 72
    0x452400c48a801921072035105060208030b4820070408103c02c00394900c02e000c000742d40d50f0781e4002460012980d68800445501d0040300f4a0907445105000c414142030240c10350f174600c0c0009006c4111401c1056080710001e503280030800400100320426000100e880240052240f013040e400e003113812074030440b80e00c90303498075044410400713050300140b964010560401c40006641c0044101e80401403180c40c085002c14402d43e140c2c54076a2180000d42c00215030001c10746410322905a0042000d46200502e08200b01c00070082c8a410000c0001d0100108a007841c0400580c09010500d0b80f01c0140500d001081c6443d80140c1c001880140c0309600340041c100d42154260100c070202c2d0011800400144c40f420015a00340d00701494014480400f4080010080807540000f602195040d050480340d6045005125412400600050140c8020a01000042d9211103a075034003805190300180c03501d00d580b510101410751003494552202c2c220101258020065010700304513090340c4c07401c1040c2091107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 591830368 1250 591829118 591829141
    0x30c0f0b060307051806090907080703031701060e01120504170c2505030601031202011e0c1805030d08040f120f030b030a08030403080702070e0c04080601080316081b031c05 76
    0x1040d28803c117000120115105080c40c98095400401803003d64031519150005589810056482600001c401e8081c600c9041500e21500380034202500e440100400d44800107005180c41304100107800b0307030703d900160a2011020000da820341ca6580c00740d5560042c1d029040e600c0e031041d904000f140803c4178051902064140c80c203812100064050541d582c6142c80720402880c51000080079552100d066940072400c0f01025040140751b10b074001000546820000e0504441c200d1b000c504482c007010500c443d03980015480c82550080c5807054056480b49441c4d01c1005c0c82000c0100000000d007500084107800009610a11340319590400c120b01c50b0100f003640e00c20702e6000c00741c41c405040001c2000300b03100c2c02c840d41d4850628011038000541e50f42100312500b03401c407200c1181b240042030620040605106050040c100c8000650610150740e040401307201d2035420040001c100010f20320815468181c00c1c990306400c030820f0301e072660078200e03075480c4c40b0100700102407001d85864001148408803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 591831618 1250 591830368 591830389
    0x5010609060305281e060f1e11041401090801020403030203091c15050a020702090c0d0609060807050d0f0c0b040f170d0f02070e04080c0c010f05090d030c0f0b06030705 74
    0x524084440860312a01d4001c014620034800010525601503545d002c9001e41c007407480070b424002d01c0000d61104940d41034502e030303008880c2c0030352460800703d0b20480d810512068800395919000a101c8c2c10040703000688a41500e0f0340300001950000c0780c0003090640200190010102c151210040070b09406010001030811a00060030303c0b911040d40d12011202c1d501465004002402c018a00f092940004111602c1203400200c0e0005c0021828010f902a0080034020481101c0501080e800c0010395a201d090070b0250302d0040113020001000e105918403581d00150704038444241050b15142c114509a1190252010303e000714040065202040c1000035841d04865000c0d02051603c0c00c0308503070a580d510411021881241f42c0483da040340079061502842c400c29140e42c2c0c0e040c0c407000a0742040483c468403410301c1100840809280e800a00b00c950f0680e080b0783c544c03944052481e0039900004038120160401c44840144020000503409240c040d1078110103c40030742c1e94800c00c000041c84e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 591832868 1250 591831618 591831673
    0x40608010311010504170604110f0d0b09070e0106050903010b010e0303070609020a090c02010912090509010303080a0f051518062d1807090501081b03060d05010609060305 75
    0x214800100081200c18042040ca0001458000c1c40c0c02e0360b035102a58042c1040c0e04501441d0003031028041080381544a0b03200003a000d40707400c881860040700141c0e074030040c0007000e07001c2c5882c0d800051401800f80809009410700103000c0d205d03943c403400300030516041500b00d0340c069860709840c82c600e913004210003000c400380280250300d0030901d070340c0f5074018144407a4105d03000b01c0840404500c0c58024040c1401c4460280c1c00043d0880c040c0c10001c000045445802c0280b042808082c0015200c03d1101d0381541d400d070800d021151a0703094003a00902107507505252141c0b030002802080e032a100794407045088111410100302d441c240c21540e1a42d42540c840e07511100c964214111081d15002d00d19600348282c1e0080400c001c68ae01084411500400212a001c0d140c8100401280c010021030042c100078a00040c442c64251700c508030508803d20078440c440c4000c0009502595150803d1b9440f80d480780007840070340d5071b03640132002170f00c0c03107003c112014014400201984c2c0340c1110141718001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 591834118 1250 591832868 591832877
    0x90c031e07091e1806020301121a100b071a01030803011d0c16020d05070b070b0f06061b01092a05060c07030b100b2b05090703030e010509031f050702030406 69
    0x42d000c03543d0000a01d062500c281495010b402618085200c46c80a98001c00038001200c038004414030b400c0301600c2d00d4006071900c2e9104031050085130b03080012040c0c280c1301c030948842e42da001181803200d40c0e88446000c0c80b8004c82c40d2000401003181c1980510f040f5030b0200c03403001d11400842c5085140000456204481d40d4080c40a0ba42d001c2c0800410703c40139001a0212011064589407941804000c0c0c01c031280311070f40007500c04200440031307445d16403090082d03902c01181c4c04d155001460034411145d04030381d81022254070000c910701c00c2d406204041e90041c05495100e500c0200d8542e01070f4520b0142d14001a090300029880c00d161003207400b800076207000341201d5811039884400440011304182c0c000344035031202040c40d11401e0014814004040040700808011082d02c1e8080400302c126410020701f04005d02016190008940c0143c99060900708400300742240100d684d80110400b50754140b0840da034095900401344810341c1100b54500c4144185d03a42c8171016130303880c4124402c050008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 591835368 1250 591834118 591834161
    0x1207062a0e090c391002190c05190816050d0210060503030316030e0f0f06060a05010815030f0a11040c05040302090a050a0605060f0c06010603150608090c031e0709 72
    0x10042a0283d1414405604d859040380a44014140c0740a141c1e224808480b6800244011040d510040c440da42080510300145140c0d07007079a07000d80b10500900a0b600301112041c03810108021752050f00c807a01003d10308500c0148040c2081550b0341d0600d00180c015000342216061030000ca4040d5009441020700114595250703041c0703640e020f924040a0300c1c01c165544841205101e41400408110f8120000504031114040c0e800741c2403000c00380010384100700d00e0404108036608914a503500580010192002c0100756010900301000c04800d84498050740282c002004960480d0607c010003d40302002105405c01081d40c2038411408080e51002e031800005410344950340160740e2160302c905001c0760150381d950105a06070004610034031815030200d619030345500d04224541c010700181c81c00780b00c0d102051101c2c07401c0c021113000b0302c820011a00c0014904050800144483c2080035085a03409020710300c403200e0404501121428034000c0c140005606051383c0501601490340c1034444505 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 591836618 1250 591835368 591835417
    0x30610060c1109130303140105011e03060b0310031a090c060703171008010b09060a05061e0d0b010207080a020102061315060b090a05031207062a0e090c 67
    0x40e120040c0044407900501ea00035071494840c6a03e030b40c040d852958501800710054907000d010f507205071070600609a00c1c40300402c06607a02c81554414681c01848007142014a114201c0182915030800a80c6040001c00d00a541403070070511800c0b40d0203460050030242d0720740c44c1031030f003804185c40c82010f940c825924030f0f03401e280200c001d1180a20a06001c4410780c510b40c1c6000b0b40500031600300c1045d4861003020000c1110a01035a5100c0e03100316010502e070702d0500c0010f0b405a0003405640d000720004620030075503443c42d6164803400107007039005644a0740c0000440e0050050b0f10b20b02d80c014021603200240d0700d480002c44c16405035050b0003402e00d5942d425009401d42c0040c400580d405469060301c040340040710720031440a070003500245551100344005200c50440039500480c040c0d400414901003403000d000995622641c4041c0c049a1484030303801c10a854030410551000700020312a440500a4000e402440c26007000c0e21501d6240d511182006c40074000c0e8142c600c40c0b100381075401c031503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 591837868 1250 591836618 591836627
    0x2181006350a0c02160b031f06051201050103150b0d021c020406170714070618030905120a0503071e020a0f15052d130f140a0b0a0c06060b0703080a0b03061006 70
    0x340030003001042c52510239961b5181414488651146020644c0000c1c2e0880c01c8a80c00c1d01a80500005e080c14032082d0151442484d100d42e1500c41e6645c1c8140110740000306585a40440310a2508201038021000018140341e00a5100d44141c0021070222911100070030200404688030b2070311515808091451284501c4e46548203042c211220340d40c482406007240d500600030010a0f009503900003219081200b800b0a4402a010b990035650000c6007043c0066000011200516070243c00c004824180d030401000d002044178000354400201e050100c2c4135885e45040804a9903034125080e4500503022040c5d4107031080329909000705e940844155684825846091510620100c01a18221444442c0001880d46420800d02251017a1041200c0440b451034a01d00307110031603040001e64a400b108ca6920321903000c046091008031a112410301c5480d6010b01c0040c001c0e00b00f03181d500d40c518900107160300011034005010307501d02034640c441d500700046c1040c45120404507034041103050202c16079 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 591839118 1250 591837868 591837871
    0x160b0901030f020d09020a06110d260f04030e06091c051e0c03010609230919030f020d0903030504090f09020310020702181006350a0c02160b03 63
    0xd05164072011403200d048100d03c0140f00c0c41d1074010000403e80c219104201c030042007944140100090f030784100d80c04140204001e0b807100382a04101c1d610740c90f10f094000b080c0191020403602011140100700580100e4080d00e031046103e950f50b0802e10b1100002c003e854061401c246821103100300c15091501a50341c890349c1d03401d024604540c0c55052807a800c4c4082d00000c10701003102d81010598281604090184501034050483c080c0401c0c0300500e0600b020340204590401e0429507040407907004001031142d00f088804012444100004504000d4503807580121a0320051045140c0d8100c001e1065052000381c95056682c5c0340f4241c80e1415100c0900006075012070100d5641d41c1c40c5006980820420192401c400e03c050780303400b071600410a01c4c044416000600800040030407000d51001c403410029114142004400c007018000031b2403062207032003802403c0c407044114008607420382c440802d02c1810303003440902002c1d0050804980707902914a03038000001c414502071020155143c06103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 591840368 1250 591839118 591839137
    0x2604050c10050c01200304110607290c120114030309120c09070804051203130b0a090b0c28050c06010612060b04240e0301090c080f160b 60
    0x15020504150001044100d07124071020200b5000030303440c00c03241c200707000e081030049010451a10b041ca15032071341c00451000603c000c00c25030411000c00c425689040a907106207802c03e06107120b015001c0d13840c868188c51075803d4019214520005001805140d0032981d00c0066070804c01c006074600b09070400c140020100c0c20354907010a210180564517507802d403d1071903a0207001421103502d08000e200c03501070058101001c01141001b048089000002c03207420890000c0311555413a0b40b0000e95410f011000400142141002c501780044c0020b580c1182050601800c16515680c83e0003400c00054444e854040300c4295020f44001ca006140348000c00c541c4a050600c140b42008040800381421801d130880c4020456929003508240c0603845110060709024280c1c61600381840c1059203120700421402400c1c04640003400704a6209071503078054403030054024426482c02d4601415401024080c1914510072140c01c8500000c00143c4510510044400c94a40c0f0b1b0410b54400038aa0200181 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 591841618 1250 591840368 591840373
    0x607030804050c062b0501051018230a0e1e041e140c01051c05180d0f020606041a010f02010908030f16080f0c0904060e01080102031006260405 63
    0x784402c0d615138000a00343d180c0d144807803003102d18071140b40d15441d228110700103500f0361410005000b10b859400490400c0780c11801d20790706c900140050041c0382102a000180107a0700000e0100c0b5041190340005200710007203d40101554883d00c207070040020440f80e199281450180810140714142600f60b00f250040c5041620302d5426406505040c40340720b812a040d103d0750001e03c82164061145c0303080b02074240b0705289054600d4031010345001c0031500044505550744041a80303603004511250321409400281c48240c0c0d42c2940103404003e40342100c1d03000d80108000100c0602c1c040c4206030740511311181c2c3d070500c0340549004481d07810240070350f030081d50b50341d00c00807002c0303003d110195101d0300340c10aa0b40c01500e480300880725019095002407003844016018400c0792800740c043c1c90340c4520112030241e200c01f0741c1f400040190241d54024900031031240d002061b41c041c10740085200d40b900ba84454500c99031234004660004811405608101d8100e54002c1d913070240700b408a81081c060003c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 591842868 1250 591841618 591841633
    0xd020607020303070807020111120f0d02070609030806010207061815171005012006010b03100f03050d0809030a020c0f122415030a08130b04030b0420060703080405 72
    0x4246164130021050317a0700d01c0b0205800c011581c1c0051341c900c0c5180300c0b0024144021598400e0130b1140078500301411617000100e020008542d10354150341e8443e80000051010000c0350501601d0b51009860860042c0074500000c00d81500030400020a44500209018100d00d8104044840e0034840281d204219202c01580245042002410700424982d0003c4e01101d19020026045078007020649018800d0b9540782c0c107008001081e85030440381c000b01c1465480d9201140c142c5034560f690020f50403154101e0001c01840800107a031039280c1660380300e0030626142e44404666a004036600d035401a84015100d84580c2080c20498002d100c0c041d01f4440942100e019150600044100300c00c03a90180d1b09082007442000800c031600030070b6141809460032140b001081c0c44d117844e0500a00041c0000810040d043c07003054154004003040841d0070380b11500e07446e04d410108020382d03007034400302c0007030740400120025201d0301848488020100c0b481d01d440c0e582c0a9520190050058800740211034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 591844118 1250 591842868 591842873
    0x50309120304030b0c040f050f180403110102070503120105040b0312070f0804060e0f01111510080601060f170c0403151b051213020d020118050316060324050d020607 73
    0x401140a450400d840b06c1d00c3d00e0070311b40042c00f00780c2141c1c41240704026075040602c680c1c4440c2e4005440d1020650007120710307030317843c10299040503421031850b80c1584001608010301030302001070050b0341007090031810640d03610000c000030380f903100401a5142c0c01c80008265203400460040c03403140d2280221004a94081d00d4040ea150461f40c494008035a030300d2611409441c1018124005007000d092102403a21003405841d62264051140441d105249020400c4540240306c0c0700000c1200340111801d9613103481e4010002c14410f0301c0c06020454100e049106003604017805403244118031402410035246480d270703543d9409042c0301d070010140d8840441103174201d4044140895115500da1941d41c80580c26281038030400108100d1442c40f20183d00d0005980f0304410140903030302480c0005021000c0c030801d10003d09682d0145a140c0b103018400c00542c4c8450042c481198040e031020412801d07208820035031024403c03e240c4c1c80b084860414406468141884c00a590000d05428101390082c0e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 591845368 1250 591844118 591844133
    0x51b0106090c0c1118060d03030902030f0f0717490e060c060a0203071808100614100f0905210d050c0d031a0310060e100305030912030403 61
    0x480744000843c0110794070213201489454042011060f6184030950400c8400d5420a80340030b0803c610480301c40400d1f0042c1803083d0803840c0703407540082c1620700c464030400c51280d40c0d0725018446241c90090b20000140c0400301c001c01e80703a0300300400c003815003d202c4000341c070400c4d0800662480500c0381d60961f400ca0f400101400c014940402c0c452900131001c001c0040c001801c07811080b4414802000540c0e640742e03010548540084a80b02c0168903611010419100c100e04480c500f801e0010320030340044c901330300240e010703121807004008000054131a05c001d43d1203001e00001036088074078101851368503841000e00d9a403e00e0b00c1d240c117080198480c800900510421458003803055040100c04d15900002d0000002201035420140c3c501401c4400c4181c841402840b00001d1542d100c9138081c11000d039048011060300005c043e84c80b4500f012003103a004080500606000124540001c1c0e03030980580b080006a070b80000c019810001070b60108140f00041040c4030425010a200000004041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 591846618 1250 591845368 591845381
    0x70c0e1e04051605060a0c060b0105190203070317062101020d06230603100608060f0d1505150d0624180e0106050a030b0703110d0e1507051b010609 65
    0x1180900b0001c224100461102800303504480d1190008106c0d100c245a008000802042d500003404151544a1001030311180141d44c00c3e500c07050003a02c000a0410390100080c01d5240c4240c0f038401401d980400d8034880b40d941182c0711600102d88030000c00508007c0b03202c0041101907040003602d4403a030020b146042e0703103081c0e102c020500e002031040441a040070500034045031007030703800609624110412501c494010700c40c40c820310840f20042150703519010000d00400300d000d0602c0364030350140d00e80b4140d2000009450034141d8500300110360301d15481d02444d4079000e8024900b040640280d01c0e00c2004064088001085100200002d6000400b09000380020203a444160114050250540007510a990000d00007a4541182070005503641c60318641540d0700200021159503811400740c0c020304400240010186000c5250080f0311901d0300140c03200758010065403c5007600807158484c804044d5072480c0802c00c01d00c2020324804071a1070011404013404008140076a031104601d04581c3e2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 591847868 1250 591846618 591846623
    0x10b0402130509161b050102091f0e03150a0c0203070605040b1906080d110c04240503010b060d02160f030201060e13120305070903080d050109050903070c0e1e04 71
    0x52044081250340f40514400d42d01075411030841507010108030000788968106070511408122140340e9500b4000309505684a06001911484030b403171078040904000c2c00e070400d4410004a00003031009041c100072410180c40c13110741101002d0360f10b8101410010700380c0d000f0400110305c020b100781e402042e1207008a0703004500030740208049050103101042e480028040341c0c041e190030888100038594000452000c04941846c0c05941d2600206100d030600800307410455101341400384641146640d0407003062000d4501410b1803242e5030310700903d401d0361480d60041e070b44102c06110310b010a03440e07500141802100c258200d411002296901c0700e070401c0020381540140c1d500c00e41400081641c203135154114000d94031410304403051380d541410400c01001410205a00e907000704e10660300482d040d5020f540d02864180c0c0b1500382c400319a00802c8248075a904050610340802c52441010007194079003500303c42a03440140c02c0c4441c241c01c861000d08105400001c4050681500340991030240c012403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 591849118 1250 591847868 591847897
    0x201110a12020114070c0f0b18030f03060306061e01050f040e07030f0c0f020601050d050703080301030318140306070f020f0109050a150b01090902070f080f0a0f08070f1101060b13231c05010b0402 86
    0x780300d37051604d000c0004000d14010810401034005080301005c50f42d90828017403a01c29a5082950b25a0340140a2940407020490805c01480717000c1e44c1540040c0040c2c2903c0308108900c0004190850f00c00d9507d4100f040541c101c200140618241407a84030f5560f8050f408540b04140e41c1d40da04a0b07180d00c268000c1d000078500a0181210401c0d1070b65000c000e24010900105441c1c415000035200c500c060044000c1c0308031442d000407058001c0c4141100c410640008110f824068140607441c1e0070b0781c081c202c80084082c0c01d8800200d40f41d109007800800103a6400f99003600300b2034404000d40c0003002c1075580380c4522821000140002000b45804000711101585814450700f026181d01801c140c0030342072040071009c0125141e4881506d86d180c01d107914181c4410700c1181c00c400d006121075027110507009070008034001d8140c00d4400600c1164600100c03102481c0f0504601c3c2c0968241c0307103501d0750000c092490303001c0800480c0614100700e03000d000009100313940c96001801b03c1c0c1c8414022004030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 591850368 1250 591849118 591849121
    0x30c1005070b0f040840050102240414030c0703030e040506220f180c15080108030702010c0812090c012303040201110a12020114070c0f0b18030f03 65
    0x15403051a6500060b624401a005040a40d9428181d002e0482c041711070086448051001221b188000c09004001d03160816002032410324901c4411712034000c070350251041101212642c00114821884240003820f18455a1180d40e07030100b00c414115003003101e038402480030302c50ba20418440c0d00c00452281d1580180a08034805000c1035441c0202007500c10100441100c000d094a01d58002e0202c0720300348000f9a40c50486032000c000c12040706000480180200d13130008000c2e0709510402982c004c443c00d240e0300440c0311021a02c010090142e444182c2050204000550081004402c034500c100c01d40c030b0a002c070242e088400f07083d080340c001c1c004d41d001c2c851414441d40c1040c0502c1c96071994907001e0030107282a4904004510010388001c0c1000001201325012120601910180c540c1c0001242c1002544800c0280684a0158414040d82c1e001000c80c00540c014410800031a6010581502200f00354580100c400303130044c682c00582844005080301d4400c14002450010000c10105840303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 591851618 1250 591850368 591850373
    0x120c08010501030f090201020a0303110d02030903030402210703020607150e210708160215030c0406080f04020904120207050a12170408061902070c0e0402010206072c030c100507 78
    0x1a0b44c103880f403481a640c501094440542d030302203070b0007114581508000c2016603408010079014031480030440713050780c80401840b0985002100440c05940201c5520001c18100c0c0e0790108482c040a80941507540810010001414000094102d103401801140c410707080800703510041d20103145224141d600011110902000c0160740602007001d4150064140080c5950302c000c148200a1060650300007030722030310115500e00c0707030701c07411070090b20b800c2e5440b800c0901c4d2104841d0003c4c0110404030325114000b840305d007624031020b446030780c009125042944440d00c414030740c00e540c00360030800c6018002e0007042c00c0e100c1720070100082c00c108565095810090801340103003600035502da90315030b078200f20801140000251041d0030042d50420000d9240e90340310208000c2c0b15450000f010008007510000c3c010711030410080c402da0003a02552129036031580c00b10f41141800d1000c05280d0740c2902020441664402048003016014046403130042000c4009000c400c0f900a44000055001448104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 591852868 1250 591851618 591851621
    0x20406081510060207030201200706080108061e070804050120341e020d06020d05150913020117151309110f011b03030f0b090f010b030403120c0801050103 68
    0x500900403207241c2c1c102c83c10400000d4984019210190400c00304800c002014106da48070326810895180450300d005682c3d8001030148030b42442010341c24000d041c0002c0c100403001100320000d54040708030120780d5a6041c001e61300c00801420548003590395800340814900580e00403691254411412a01c0c0c089002c0340c820000e25500d941d84442c1d801c040050442140c0f50b0701c017070300d440e0f110195022141000110390521001810080c4d4041c1a03252030405000c0b00e90b00600140348410001d0001d5074030712507201c80045101d21540d030800300f52400201c0341d03400e44120701c04481c814036256015588558000040e00c10958100700c14440c0c800300038101c0d00c0d140e00c8403c070100c01c1d00c2d020701c002080b0392148aa4500040107240c0600e0080645007096841038400110359681604041c0041d003240c14014001c0c0710500c108500c2030b103414004031036890301400e80d5128103001c4040d100c00f60b007802c084000c19000a0b0080f014400500c040d02805c800d82c1c00b0f4120880700d940d03240304103503250400040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 591854118 1250 591852868 591852871
    0x7030f0902121b010e0916021510060306060509010c17120c0903070501020a200d02041d0709090809060705160e060102160b18030715020a060e01050610030b04090204060815 76
    0x1818840174958806894031103e41c1e2981c03000d00103a101040c800412016810910800d0127208401e9101080180200020b0f1042003510b000c1c3c0d900300000c544441c1e003034810344508614280468a11306240c0c00044018505410071203101072114100740e1062650000003005031602c0c184008007044c4658141001c210100040400340b006004540240d1181c05281c030f100001c0140c03070400148200c0c0030352141c03400c860f81c10354068400c0021b00d00b0010074002213a0002c0c01d50989009401c40000e4212142c045c05011b1a0018215883c01e1020000c000d525480001c0484003401100b00103502800c0300145c1c007005000303042c1029890300c0e001000a08100c0e05103140c004511107000240040170065007503800c1103c0307221500c40d4104003200001d1401c00d61b84d0240304807411181140d0380b80e0341e0110b0070452491064905001d017441c0c0c40e026900f66081280c1e4150040c1001d4000040a440303604484032081016100103614030141d00810250350840e004103d840d03200080341052585e6114916 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 591855368 1250 591854118 591854173
    0x7060c0e0a06050405192d050d05030703031d030a0e130501081014070f0f020f01020d0c080a0905191a0c09012717011401080109051002040501020607030f090212 71
    0x305200341060300141040b422207040c1c40707213001c001e1a08010810b60240480c040c000003041e017607809c070381403824507601c1c0d01c01641200000d082c0703403c238400c02c3c1c408143c1c2c3c014061340401850030700c0c0041070308554075402d80916603030002d0200b0500741121a18403803140a030010501030f0806031800001d41d070a9410341e0024a00b00c1a001041040301503020340000360f02c403018904074070903100342801241380c80440080001d00d54800501e2407000922944455075945054803110720310303034800d04500221002c1c080c01500a401c4800506007071120004605e100718400c0c00090b544407869017107043c2010040b58103200d9a000003428880668100303501104400c1c880011105804600c460b4100c80521403080c0072013080750107200f00800c2c40a410825116812240c00c660541e50380100e10b002c0c1000300002e980a00032000d02c800c0040440c02220250344043c3c00414094a610104900a100225400c03908c2c680e03491800d00144d68144868044014070740060445801d20300554100000b0036400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 591856618 1250 591855368 591855409
    0x7210c05130e061e010e060607120909060f050d030f0c0f03030501050f0f0d080d020f120417121603110a030f0e1b0f18010b1207030c0507060c0e0a06050405 69
    0x44000c0c800d0303807813890341034410780c00c2212440d84801000c0340d0140114800180354140085800720300550144403c421100400b006100320f0f9640c10f000c2c6005501801a150003130140c80707001001c03a0140e0b03603203050020103141815039902c4c0c0d070700c4075a0a02c258803000c6000a40b6407004000d03518007040e500c5004101140c6455044010701c00284218016a8004000f02c10200e0000e031515203940c140c0311940840481281d036803200868100c0c0c0003c0031101104c0c0c4594082d03103110b240c003c5100351000c00c101c0114020054540801e58075401e4200d9121404264a961041c158005100040c0003003020f50784020404e0380c4591029416039403101c2a0b070f0020f42c807030750010004264094400718200419100e00c00c844443c030012492205c490b014a80b81503c121b4000216010944d00030050903044141c03114581e01c2c0c0b0101102038881c050040b00c0003400911408003c20100e501c00c0c0d400c1d030031504002510030075180200b07142041c681d010b80c0c0421004101041141040c080403265069400d20 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 591857868 1250 591856618 591856651
    0x91e01171005040c0f030c0806131e0c09020d1b02010c02030706020d0f0203100e060108011d06221a1f1101060302040204090f0e07210c05130e06 64
    0x3011561521644041200341d621a00850305004c4046454005000010600744100b9128181041c540d81d00c0d2054038024030941000034600c110590103020b035984e1001a07480d200c156500d81c210850070801081d00c0424450800003200643d0b84000c0842c550213020124907441901c0f0ba0084140344011502d040d039040c4280000b88550120031280c1995100c0d600585030a00d03122560700819480c0d1900740c03440d10000c00c0c00241800700018034120366000010311903650b42c0d1001120200028030034584010390350b102c00120300c0c40b040c0d04564001000351640012403402074001c510410b20002d404052550703510340140c0d11150300018500035000342c1d216030710300171444c94a4100000840040040203c00f649280380c81ea002c0d000324004507001007065441c0c64481144200500d81c10303180203025032800649128880c804600324040b140c040160382d4400b00d401d404040075440741007048a110803000f40110b941da5070000230f2450034080400000d1025120204185450303009408468070050105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 591859118 1250 591857868 591857909
    0x15020c1f0f0c02280807030602370309080903072d140d0201090801050a02030a2901051605060112030f0203030f01050f0f03060a0b0f060c0316020f091e01 68
    0x110311098604a284005040301c000b11340d00030b00a00c20341c0088105000302800041845425005054440160040314a003000f0645410001c01c0020a184803004081083c011a0038020707844114000c1c0116030a500d48000360b0002424103c05403c0181c003510281604000501054681d031040c03215940090141f5040240e42c42040200340001c500c2250101128411a442004803070014842c5400070f01803130509411110103034104480c000c1e03080345004484c004401050009850514071000c00115645100e001160b407544030b14440340c0f001520022020001d80c04000f03440c001c090308004058854001c0c50024010540d020110f411540248103000c0002030100d455811140125001e035882184840894501d659641c1011781c076000b043d0802c15000079580010280120407940c07a609484500c042000c03900580072060515801802113405102403403220088580c001001d86100054010005116420864440210b104d08070007030b1900c0646210180c1c003501d00403003490025507108 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 591860368 1250 591859118 591859129
    0x1c0b040e0303181903090801290d02190f03051e30040603050601020c0108011a030c04050a030f050d030504021005030403110111120f0402060415020c1f0f0c02 70
    0x14042e4004140c04101c140f8410600300b004004141540b1010301050b261350402400034441845078002a5092400b0320310203e8142c1115083d245800341d605800001c414248090700491078400ca0304100000d8803040f0a1415444280080c412091001301c0d20b411442c1403400c1c000d14501c0300c00542c02c8000c51060410b804541030b09403070705d502e414a003d0701c440072000d80d56003107401041000390800a070219030941d154029078450002a002c449410741100e00440740084c007441400401510000d0f07003004040114003e5400152160b1035509254a560000340340c001642d0040317440101c460720590405c10240b24415040035581404c1100d4036240e0003046003c03001500403c00c2110005c001000c05000e10003413403641064030001c2092150f06a5200016408811411181c410100020354014404039075184210360251a1038100751501c00c112040c00005000034042d8080c2c80806042500c480c031554184907840500d82c04280136421003e03102c00303008402807080040c1044204056240d9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 591861618 1250 591860368 591860371
    0x1305060904031427010e1206070e030a02061602120102070803071b050a08030105041410091509090b060f03030901020604021201230109060509041a060103020f1c0b040e0303 76
    0x1605207082500c3c50316002c038a19204e040940080428055005403882503444003681d040b12007030301d8034440071401d0002c00541d45030300b2607040500e030b10100000311b0f41e900c0703540c4007455500c02034201d03440c00b94250b0000e50103401c102a40407010b09000c00328419440c01054410030890381c54001c5280181c0c40d00c541ca060301c002080002130003654940d06d281c00800c01443e40c1c0d925002002d4800c1c0d2a040d252030050355200380b040d14800d50800041305a4140c42c807020600941e41d9943c200c402e186000034140241010070018070505a4082001400c0b07507060260300e0402d1f2060200c0710261030800c080264040011280b50b0103540305011f21290b0b40d800140b680e42281e01100c0c001c601140041440c3d004d0003c0f1001114101003a8000241c800310082a50703050755002c00081c01615203613028001880310440b0003400c4880701040302c1404000d00c2c0d5245404c0001031402600d45403041c207002480381d00507100d42118a0500c000004010428812030701444001c5070300b0301c20212044082aaa07000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 591862868 1250 591861618 591861623
    0x30503010b03060a090509010b04050907210f0b07050a020d05040501050a08040c0b040b0316020a02030a240501030f02090106030c09140303071a0f0f010609091d03181305060904 78
    0x8008045282c5584d041c201340014002c5150a104074501111414045d1440418160083d82440042102050040b4217101510032840080024803502c005407155845c0c03407102038484c030290040007408200100d4845124ac000e41e280c041e60342c01c2c0c01c00700a142c1501048401c04001040c44244416079000e002c81d4460502440c11251a88031828004800c4901e540107003114a00023074001858801c4502962040700050402024842d44403800c0e601c4880740c080c004e51640004244400081c0c09054000040c00a0ba8203862140101202d460440d402a00b0a88a4002980300342045103040116180545000c2c5070a128903c031320040138041c0580c80c01b0304000301c81006071403a01c0f40c50400070784103066044840b403100d20007440c1d020124950140d442c134050210341d000180302d0058100d036250494089503a000c403420318240c400c000034079020f0200c683c1000d40d0504100c00180c200060a0055003405071910700319201010009028540425440c40a082c902040078a907110f0321415401074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 591864118 1250 591862868 591862889
    0xd080f010f2409150e01090504060303080c0f0d0908040e07031a010e04141515070201081501021501090606320703021213050f040b0901050411040b0301090c0305010b0703050301 78
    0x140080003e480070b1041da00442c0720001d0600c0741d4001c20342e000c0781c0010048001c1e00c40700700c3d558032074050005a904500014000c180080007280c1c1c0e0a58081c02095040c1c1a00d60703090629800001c00e50513030390080403e0310308030001300c1d040c030403a07420901564104e610341c01c0c200180c6200f88012080c4c1003454503802d05100118441e41465180e541010b500b241841e496440a8502110442c001400803145580a418140240b022901444003224101030b0141c55110147d503550310100303400300440036841c3c11401040c0c030260a1202d841c840702d02a012416010420300d060800040c28140c000958659082c2c4803204403201e82d0f840c11140042ca000140c200b40d403800182004e074074101c80d0000a0100302c00000303d101d400780340c180e87d280030f650044803500e003401503d40800c4244c0b607d43c14400d9001c129000100041c0c0f030190f10200d80c4040f00b50155041c141c2d00da2b5600d9264000741d0040a61a84072445001c605a0500c201c501501500c140d1600700b9080d0f846c000c0181c0014041c0c0e14010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 591865368 1250 591864118 591864179
    0xd2604022b140601080f0f0703020603130204090f050c0f01140d060b030403030b0301050a0522020103060815041e03090b0307031806090201022808090f030d080f010f 73
    0x1541c401281a41c0c0c0c00c804810b0100c000800103039640c040910032550107010b48544130600d600003281410301c20b110440280500c03800c6408006942d400600340d5101901c0303503810800162a00c2c010036482e9406600c10711044007d40c00c081c1c0c00e00b144060304c1c0f440b5001000d6800c05a0b0b8100401c078104000003506161180c0807848007400030300d0725810038428844040100010103038941c200c000480802e400900240d2519400001564410344071804007030f02805c41c2901322408400d1010781d0394014940410083e5a65804030308107031045900e40d06900410701000300340006085030402c80d18000c0b038030780c0c840610f5817402440240d80c0d00401c512940000041006036200384c01411551040704101507072000940b410300b0040040380000ca025020702c50761495080000d007252115503e10002003012100d02d0740e11017803d0340c0603542813540000528142c1c09075450030030000614003a030ba05d9001040c14043c0440806c1ca00507800072845800f032240034403400a10303c0356506440c1140c0e42c4031069 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 591866618 1250 591865368 591865429
    0x1009090905031b030316020106051e0a0e0a0e060609060105030408070c050312040312030c0f030908070803040803061c021003090f0b0a0b040606020f120a09080d260402 74
    0x42d44034102e075a180040c240310381003c48040c040011405180ba200e1141010604e0420981c2039810078030449030b01912040c100098200072031480540b0314802803911442580340e9140300715181c402d580400061340d8524140240c014200324280d0041d004a0b880021841d082c00020703c40d00c40244002c00c04280841c0c01000c0000010181c0041e100c000d00341c620180c0740b14030702c19054201c0d22050380c40ca041c901403e01c8150091003461440482c03030340c0d0307000940c0220b070703059001c0c1c0304001d802c42e1b0a20f0100004000314030600e01442c0158868002c4503941d04000c03081141665001603411601c11034000400300681c0c3d64500e0780072080c960308011403103443c05c0c1809040301d5468800580092003540030400801d81a602c2044024821a4104481a11003504030b035518018048188140d0016000c201440b031000094890301c0c4043c58494247c40d2109402820300503110190004107903624035a18085007144034205400340c0300c8000002624003074001902c40c640700740c40b8140290521010105 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 591867868 1250 591866618 591866623
    0x121104140d140d0203250c1a09062107050f0301120807050a111509150d020415030b031b090412030e0f0c1c0302150a0b090f151009090905 61
    0xa040b4440042e6000251820310217500c960140d500c1c2e04980f03800381d820340b00862410a00c140c40d243c22407000010702e400c01c0c400b090201c030448041e20003018180015600c65071040300270195107840b10810203d24100d1032060b214980c020309050140002800f8034400340a041d0103407030455442c40005001c640d1181041c480d10312071640d0140060058403980018001d194920307005030002914001940301038100c4119590164640055010107002c14850750000c224000d403a650401c2c24005160650720302c001034000c10004d00307a001003600c0b05940d1105240c18824101c0079258042900162407440303000400119000344002c01101345070045d0300305144a0b40c060460302c0c118a0480e041030011000482e52407141000f1944036010031580c912458001084001c07005030b0603001000d4465480e0013086c1c10f070b10001e08458040e070f510a0411116a0740741c8860740980d01011031540313207003080c81c0d500204501c046040303400b5019441c0c1010060340e00102078012502221000600380805160460 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 591869118 1250 591867868 591867893
    0xf0903190909050705180901060509130e0319020c012f0a1e06050619061112070c150f0206060f01110105100e0f070e01210c121104140d 60
    0x5900b0389408100010703030350040000c0104480c042c48102c1c80c030b0b448508100b0404824080c110006006004d180441c0c185039040d0303c3c1d40100e00c40d010602522071328401c0d165401008094144a10369503c6150309078060241410903d000e1070000070866010504544d03024510110121000f0101d5600540d4001800f1a5103000d03840068800200ca0b21044140c880010440a448072403811001c11f8991900c1901c0c64031100310027103034050191910000b074440d0040d03814007040e2b9010380c4042e09416088000140461440b0300c4800c2c55181c00c1040501c00e10041100c00c1c02440b1101d2501201e05400041a0703910890849406100065810040324402c80301c0c1c190303031190741c204002d20000100300d0400d80d06440c1110341d403c90640d0780c000056200301091340c8280205d00e0807500a00154402da403140030500000491050207000000c1000403940d0030b41c3c420300083d002030080603141c038030340c0104580390380c403034880a08003401d1015080d000349174042c200388160710b103000444c2008120303141c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 591870368 1250 591869118 591869129
    0x70201080c1e0c0c04091511070b040602040905130515060f060711090f040b0a050a0207050f07061b05060109200310030605130302060f04060204090e0309090f09031909 74
    0x141c2c18160101c1600b070b280d04028000d00090050034104d4800d401d05209400c6040d03085041d001d901c02c04182150010705140ca0b03100410f41003008480301142c510089070340a50711171240166521700e04003101040301d02c09424031151110210600c0d000c614006a2a40305400d8165021160348861000130700c00d001da1420582c01c2403012914109000c9a180b81c180d00050540c0e22100c0380e135034948114001301c1e0480b001844600c088000c07403001c9005901040c2d1000e2405030042c6007000766104c5070300e030000508031803400d81d00c0300d00180000c55200080d0b010140d000482d00195605580d5640e40314030050099601c01c0341c0c1c40c60350081d44d0515011410290902d59191175403410311003044d40c8811618002a44d82500301404140200210688140d0554056001d025980c40d1f0310141007410002420a0300d20301e800380404a40141103104e0201802e19000065076140400300038001da21034018519000060803a0800402071008011101c044012200c08001318101d00c01c00e80b101145600407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 591871618 1250 591870368 591870397
    0xf030608070603150b091302090105090a090506120610051e06120702070b07031403071206080f060f010e0103140a151a03010902010504260f0c01120b06070201080c 72
    0xc84903015071040d007251003a5042c00b41c91507182d046001c0c89104120490707070444000d02200b89098000e41c0505003109c4c051403c1440c004605000803545092904404109503a440500519281210300c14030000074030000b03030000d46403100d10400ca5101e144580c60242d40a1240e20300440031881d021030040e10010b00c0103031130300c283e00340361b40410000701c030f0348000740c0320304230000c102c1d81854420b90b1032065040da29002d0000b03400ca001c82c815000900083c040c40620700805510034810b009000140a01c0c0d4020b110cc0d40610000c1454038101501c41c2d411640b8000c0180b02c048144440b1605507038010345e01d0a010800003800601c1c140e420035000d0800c0b8101420000c52440c203800c9808881c01c0e11208041e07155403481014203e4140a40003030105404200410501c841c01d0100c01c81100b205540703141e948601079115080404405e1004000e812400740002d0f15a00b203d0f507800300c00041482040801040c40200d242d0344940d03a4080e040c080440005102c030142c0004460082c0c800419 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 591872868 1250 591871618 591871633
    0x1e0301061d06100e03030403120c060608010c180b0a20032209050f07080901090501020c010204030201091d040611160309050102100b0105041a210a0c0c030c030f030608 74
    0x1800400280180e90030741c441c1c08980e140b03d1070244105010f81d4001340090141d890145185c0d184010303101024468000c0c0b00c0b0035039904010581d140306610041102c0c0001241e5125201c100038070345490920100d034814a181030a201d05505002681c1c0d5604140c01d210881c0301c00c4200903d0510303c15240100c0c1e07888000343c4a2616403203a500c2c620301d1128010700e550003d03100c0100e0720907540100e483e450034031031000010320315070311550400e6040448580009460701b0700b03883d29420399114602101440e900000c0401c2196881203c20004003680c162040c440402c00c450381b0300103980500080c22480d150320a07a00c00030070400c22250b109403420088070f00c40d05d6034500034101d00c2d030070f10540340580144503007000d1000c094002d5208581c41651254609030a20f60307154483e8886840c1100300c52010b00003184403400280c5c0c516030140102c04441c007286810501c0c00b00307071901202c01c4c80420420ba0850000250403030203083c0d003d58903081401c070300d01e9140c00450061034180d1009416105012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 591874118 1250 591872868 591872909
    0x40b0301031a0f04030f0c1403041d06011e03020d0221070807030e0703081b010608030304350721050a090e04080901050706110f04170601051e030106 66
    0x70b000400303441040d009140540c0c4003a28075800840c1100c015020550220394644241d11070507003400318521030000d0200c01100088031070300e903811603000b1020b2217507891810510720603800c1e4180e03030241003442d14405d1800030b030500c81e26180c01200400c06040c0c0125070300089240607011780744c05c840c4405805c01d60320128042801903190a48070724011481c60008110350911902602400c03030032500c0200210352841d034030300c4141e0f40100d82d42002111035040711524001c080c050361006018000042d42c5909043c14802c1030000c240b1407900c03a80040b00a1424420100c0c0310204c5030000b03a0304510b07112100e6042c03d00c00540f442d0300701c1000f10351a030703103112169402001034207144840e50746880003e611076078900c1380100c094501a10709101484842c02d07541c4200000d2459904c52480030035001101201d203080c80c0c0200710041c90b006000b04050055089080c90720042d030080c0c2004040300c0d450000494040701090f080000210034800580c91262000d400c002c0c024000383c03800194526a02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 591875368 1250 591874118 591874133
    0x21207051e0c221401050f01120e010e010b010f0c0302120a0e0901060807140405090402040b0d050712290a1104080718050f04080f0d1805010e0c0406120602090303040b030103 77
    0x14003d044040e442d00206418410b09044401d050340c0b00503000c4111f0100003001501c68804000d400410192280d084071f140440030300419122240d44000452246040f80014102d130125110000807c0403d40a4002003603002070795182e841c00018020ba0f8036003c0080844982d03661340482c9420099400000450710760200c4041c0c0b00f00340d1943e80e2000c540340300b0203407030842c03185101e41c5a2048200300420058039295108071b290070402020042400490780d115400d20700994000c3c07920f1010081c01c031041c44920410450030404030311034024101203078804010088d41c09400f40c500103039102d40315201d00388600f040707a01518074102100c00d5a81d540e00e80000301c0700700500d194059400c02010a0350b00c043c0e07120141c05154040b1702c0fa400d060010354450419040406040b4415840340c09000304085842020b460940c0614004190300c4171041d420740c40c041e001c4050f50301031032501400300305240c0344001811032194800c1c0e016035140203640009107540202d0b005111184170000000082003c103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 591876618 1250 591875368 591875419
    0xf043309060e0105070206031605090a0e0415020903190c09240509130f02030319080601030e0c060f1e0f0d060b090a0b030a0905031306021207051e0c 66
    0x65550400801c202e00011100c40c020b560f03009400c103c003803001c01d0a41051007040785c0c0000321864102e050080350400a040e0320100d50111070070003401c40600050040c0141351424850144505519107074291010a9913a146250f21030b040c030014002c0c2c42c0c00c00408010b4100100144003043c092401c000080c0c601c100e0101103110000101d0030350005180c00c00c3e68850707104805c50a44040030a505458414116241302012681030204101381d0050111131602440c0004c0556200c9446162000000d02164460030180384030f6070219241e05c07600c2d0b6840003200c0701580041280780d01d07118016902000c0c49903d100d2b80b240320707101240304104101080060034007040815014001a0741c0e035240ea90a5100d8111100e41140e070b924000d00000c00140003d50300b20460b5140040c403000e0640310315007103404c020f81401d01c1d941c0150040000560420410620516414039507180450660b1025564892044003210315040c1c48080e4074142d005024841d00003801a0544c0c803064590310108110015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 591877868 1250 591876618 591876629
    0x60f0f062612030c160609030806091021140309101e0e0310060e161403131e0f0c08010e0c04150b27060f043309 50
    0x80d494041c0d20741d50840400c0c5404251501c05070002e00361414400c030503640300821050a0b10f0080211492802040c490f2119045c041e40d40010302100502d00205404405401c00384100089022300c404000c41c1a5a41c2c1158070348800034a8070441002046101541e09d0406090150200d0400103101000b000074240d100c811071390707015912240c038020741d0610403845420800440ba01d0a4410f014080c0081100d01c8e00024103c40250700303068090000d82d034140e08911850758a00c4180301101c0f5610940c280c0c10030b81820500b508590a114900c07450100030545c0c4110021380e0515401c2c40f0038204448102c040d0610051110901802c0608801480e070400b1120003a00c5c0c0d90018840300e06220b5004c200c20808068808170048808000107401860560368810300308190006000394004c0007065030301d058000c140b100d11a040d410310390320070300194558099a0308003d10980304031031804650a64030300d54410100341e04000d8001030030400c660381c0d041403520001211940c06070043c00b110704881 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 591879118 1250 591877868 591877889
    0x901030501052d0609250f0207060f02101109090a050405060114010f030e0313080a02090a050712110f0703020c100f09141306060504031527060f0f06 66
    0x305906a80010031103403d114481c40c1c01d107808910103291241301c5542282054010040e000f40051903030f101c2c10b0b0401803c0703012461841003251401d4040c85218000c1800d4103003000a240402d001030344580031a20200511070782c0d0f0450084640c4071505070b65950304054510102854015000d10080c40140d50554081c403c2600004107030b80700d90f10600c1d02d08030694400317000f120f9204e03040c5c0140c11607180d502c0407070209000c0b25095004005511005110000c001c00c80100d1a0051020444010701180151410002004141c2d274002058100360540001c0019082c89400103007201070046800984042d1400200c00c0145540012001c049407001c8540315003441d94404196078608070b8000c81808522440010010804821002d1541101c00342c401d42d4280344011102c02251100e8001c1004910040f6003802408003c191010702d0808802041104c1507102030a03a9100803284e5074105450b0041541c44100402c1d5040494070003001c0c8818040182d20307602400c041d04413402030030200d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 591880368 1250 591879118 591879151
    0xd1113151116060c050c031204030201120e0a0f050102040306110702040b010c05061521060f07020607120515041d0d0e0a140a0f03030e04060b0a0807030218090103050105 75
    0x5550106440c40b400c1c1245203544400340c9070010596000029200a803000c1c01250a9103044d51420310014401140f09050660350f07500310310002d060304040800324190207182a102203902d0a0020307011001030b4000581c2036030301880345400c07406403190741c000a0500e81803507104078141e00e400000d03011081c0708031403d00850018800441d03445201e600007511551010f800f0a00403450701d1005800350b10084d10403408910328401c407500000c8a00f40c82d184941c441020001480c0c0309103052a00840c691005c0d0025040070f80004003082c15001035500d40300e58075004201c01c116a1011790841d00e9000c2c005000c250700f1400b1f02031500d001e00d580300300310b8001c0c1000b90101d0361041021100703070640100b001c01740d2800c00c00c402c1210119180c10907082070010902107009046001a8001075201e540c40d4011b400d541802d00042e102ca0740e104904414041c84812880c907002550103920002c1460700680b60080c06a00e851b01d00100c075500c50704103d0b03c100104c140f0006401c8544039804202940d00e00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 591881618 1250 591880368 591880397
    0xf0c1208042f040e010e0a080903030f1209010501080a081e120406150503010603170309030903030c0a021c030c060b0411040e010e0f01030203060106050702030a0b01090c1808030d111315 82
    0x207807030110944020a801901000300010a0b020144c11840405001c433410301c91000f14070b043e1a400b01c06e024400c0da0a020402254500c00d000f80d07405021548041c0820700d4070b60b650740303995008415000805103101c0750b0804150451034142c50b1a129614800c101905250070258007c0c001840d02e0031400d07000300c10210301c0d410140981c40881c1c0d40041c2c5000e0b018000c43e002d1081d5007005e0034810460104021071042aa81003028100c0407101e517001d000720600d644100100c4020700e004510400b242101c4ca00081380d0841000c071842d40d00000c0c0803072041c6100303000038020520783c0090b101241e00400c01040a950f041b641d14160f80b00d01c030b01e501c00d60f1130b00728180d01104800d01c0025810750100d001442403e1203040642a2607102400b2507450f04030654606980d200260000c0c88000e076a0801150007691050b002c11803170400381c0e401c0d180c01e400d21359139903100d119403150801e20581303480991840b184110226064050400c84000c40c0c551500310001c05031844091000c0050741c400d000840 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 591882868 1250 591881618 591881621
    0x4091709040c0206060a17250f050f010f0c02040b130e010501050d0210052b051e2418040c06020f0309010801150509040905010209010f0c1208042f040e01 68
    0x250300050084001d00c5c94000c2158103450510422006401070000c82840b088c1045001c01240451815a07070400d1f040840001803991141d00c2944141030845040741582d80180d200780011718245003001c2205050700103c3c02904000f50b200e60010a841500c80c0c2081381a841140100743c0e03e0002c0c062640c2e18000c0100031001181d02035444294400381e000094080c074000d025550300784c58002c00300c44012590849155006c44c940346503036107030b6041006054840c514602d0100001031003081e24246286001841554040705021004002c80700410580c0d4001845800c0c042c5515240307400c0c502440c2c1220451028400c4401502c10003000d020b00701c41c04001e0f11801072061352010120703803070a02d901d10040c0d040c8140c00103100c001c00c290f0155403268002c03c1d0f84c2074055400542d071401030300c00040c1006403013803910041019040403440002e100c83c1a003a08030549150012040e29103081508801019404221003415050043e044201c5600142d0035601c0007103c0c01c11621701c00c107480a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 591884118 1250 591882868 591882871
    0x12152e0e0406030213053102121501090c11160602010509150408091201090c0e01060c050723030304060f0206060928020409020c070f051f0e04091709040c0206 70
    0x3903020350102c1d001c08400c8842d0b0320240d840342c41c40c02da42c0341c050642c60401803441c04882e848005010196047c0f01581451541320640441d0000104562286410411015034046c0207034202070340c03111000d03a0707410f100f407002e0003207080e080050b14050001d940061004894511138580075508140004d071145001084001d40220320305006100c5a42d159035401540e4040940c9aa102c03c1070303020344c00441d13424810300381840d204024100119062640e02c040755401680101d04004088400000150740403404200301c3e808100d00c4115026240c55231901c0c01d03070844c800c5416120204000801c03035401080000b50310385c00c3e0243d540907151041800310180088460300c16895102d00000b40d820090101c40450594030f020040c10307c0d8032502613000340e920250b010741042c2c0c04500c05002200b50070080b140204800c40e965a4028204000204040701000c422000e00183c4080c50106840d540c000b406029485460a8085400f40c041c65220350440d1299600a92800080b000007074000200107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 591885368 1250 591884118 591884123
    0xf01050403080a0b01170a092114072306010f060c030e0108190501081e0c01090501080703091b231f02030f03070201020c0d0512152e0e040603 63
    0x40b041c940e01c41208501502070020300034100143c0990b0030b900c09040840c1c29000e414001c1c030200380680a4240410501142142031801c8000000d403010000d400805140c103106d0b90409440c2c9401050500d0950405981495500040035000340d484a840200d21181039610f140300f00b001c119101c0c0011580480710841c000c02040110a110b80c00d03600a26409510103540c4542500750b00303224100782c007600c00c00e03889441194449221401614100c02c01d0888070003901e40100320244282000030052440361180e13605114231003004c11642d40c426002041036580013600220401e09501418400203080c0c40703100392070b02a201c038002d03050110106184011800810440303100c0c0c2e23900a002d00c02084001540103602c0100302101c4001c0780c1001440c13040100741c000585131694510780b01d0400c072040740c404040150401200c1800704c1d8030002ea681202c5698038000d442190728001c2030b10301c00038000124250000c4400c031250041c0e40554200c03280e01654507400038045c0042440b0a9a0450100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 591886618 1250 591885368 591885377
    0x17130810060e0c0705030c0d0e01091d04230a11100503161b050a0c030308010509010b1608160b04030e030a0309120501090b040807050714130f060b040b0702030f01050403 75
    0x800e10f800c03003440280074070b2406030041c0c030700d80300e04400703070b1403802102c04082d8012414001d00324480d50380240e20600204003040b040300f0352001002080c60f8440004100400030802140e040500110010103004e008032280701311480c90119082030582100c4000e2414031071581a46000512817054003964041c0c41c10020308130580140c40019640c103000b5401840f40d00f0050400740000c190f081054090b002c0c0610544c1d15214154100244036a40503003189004005d0480100000c005450840c0d1000d44000c042012292a47c90182d100c0d10884060a0508040c503543c5418011500c90050103584a03403101901041d81c01c6c1416121801c0c110041c01141c201c600401c50006040715201d00d86108400004501c06540d6070122016410b03181a21640d401040c000204541042a6800b03484800754050402d1a030800080c040510348103042c07220f40e02c03003100d035500214540024000d00b540340890b80e1501d0310741f918500b007500a010164828482c40d107108010910600c2201e00aa405070b1701c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 591887868 1250 591886618 591886621
    0x180603020612040203010f0609200705150705091809010608070503031e0c0a080a02010e06040b06010f110102030a02180409020303071b05180a1a0906040917130810060e 74
    0x1ca40d0b42d000c0b402002641c1654840011644480b2684141d0001d4500440001202c6101c1d448501e1440c101440342e180c1100100815004100300145a1a062040d8405070606070350700c800846007409550070490b0840e044400541078403040301e00c498030036001c0c0b0000b0098a42c1d01c022460b80c0c2c0745103204107501a0801c2100c81c1c0d80d120400c400413040600328481c0c506c0c10000307100213407620105a2013516200c0c404155241e48a90a001d010030360320380b080003481141410b4844500020b005460a81800060001c09191074000c6406400004810000311344034549800c140c00a580422100a04034044081d41d101030f1420703200e19041c50350041c00440c00c01c0d030255121040120f400f544003001d403c10390000201d5a482008409a0003810007854402d07040261540c4151107010750007410305043d00c85614507039202c640016034001e4089801040c1c05010342040c00c1440b44801195800c06000960110743e140840084012200c00608a5040e00030100150048443c42d004150b089103a280 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 591889118 1250 591887868 591887887
    0x8071a0c0f0f0f0c010504020a120c05040e2d1002211905010303023306010f0507050f060601021c09030f2117070c0206030604020c071e1806030206 65
    0x260803803024854400303103402c3c0c0600e03120006402070200200b039030b91904200300440c240039441070010701c400c2e045003000c2c2d00c940d52a5100300c80c07503000b1540155696004c80c1c108000800c082c5a01a5000c503150000b090300c1d906d000d15110015481259900c00c424191031188454403c0722050000850320000302d01e000c4038807180c0c92102600c4061240400045000180d500e8031509008501c81d400a105a402c1381c20100071021003c13099001d1060881100950760040300c072869400391092070075a008000e140416141800382d0440940a44110140c0c161081c0d130000d1200d0003400e0903021035500000d41c40d25403014044400304640050907908003000003604245100010522410403410701d10414003424202c040306884c0c0000160200c2d5050340c5407402d04810913044032551070104202145500030039050b10002c1e12441c0543d074001201c1000d1502404103502501c0481e080203c04801485040c0021086000b6031aa501c480900141205403c0c4aa6800c895001c0e20290800320301a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 591890368 1250 591889118 591889147
    0x501050f070f05070302090a0b01180b0a0c0212031b120325051b011e02030709030803040809061210050109050f0d240905060f060f0d0305090d08071a0c 67
    0xb440458070792003004400f0005070390b100044c42c4544028000000c8043c1c1c2c15000528045080e80020240300c00e5078803d0101d0540142200e03071002c1c0da8100b500f2240d0441c03011600f0000d1480a413040c43c000425100d907402d1103c602c4103001c8408500321140c514191032205007a100c2503e402049196000c030210760342400700040608007180b4185542403035100000303125104211001d08840d1b075074aa4107041003c0842c030040b000e803585040110b042d03107032402002d003400036103000140580ca0f02000040800000600312010030b07001905082d00d402d0301d6940d40310132050a0364001000c1031203c10208543d4801c98010007110401040007214581c2030f070a11900c44bc2c3d4510948050798255801c2501c0308001641900350844d00200141003040c0b400c0050800e60003030006902c0400400038825035a450a9804944441c211101a5540c0c45072405460301d209050750749410001044500c4184400c44025044540c05201c4a0b10000d00301c00d000a00080100e0f00c1c54090a030034080c4851030041d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 591891618 1250 591890368 591890393
    0x5060609031c0c02040212060330090a0b0f070c0905040b04021e0a06020f070905090c011b060c0519020f0d08060a0302060d02030703110c030a050702010509041803090501050f07 78
    0x80d0400401030001a0041741c1a60b00c06040a8603100d02c280c1840064101000800c01151100149074043d50b42d41a4001c0e110b46448180344c0d2000009c50320500c0b5540d1842c01000400d042c44400d41d81c0c841101c0344c42c5a81d040302400742d48942d1290000200120350340541807050754824600001c81d83c0e10750030440d0004880021141482d110b103101c6810740c03207072405074001d0309103a0000d0000607084900146020550340007120024280810b109d422030300060f4040c02000b00f4201b880342d070510b00000f003010240c1810302809013800d094000500f036410600514000c0d030707210481e64000070b00c00c0d4181c0e51101c2128140c40e10b039004001d00e910003442609400d8100000a00e242429507980d00000d5907030300065403103181c0e0f90b80042440052074141c424800103501c001d0849040c00d001d4084a6224040c1c01c910340c05010000a58004680c850b00032074030005402001008455011541d00ea100900300c0c000703e0101c0c0c0d05240208003076019506840011003035050161902d0b00c25544c00c0d02c6401c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 591892868 1250 591891618 591891673
    0x10305070c05060f04020319020a0e0c130905040c0b040b0304060b0616061b08091509070e090c190b0706021612021513030503280c0e03010506060903 66
    0x1c0e90445a000a01c24041240542c00781012010360341010b004050070011a01c1440d0b041c0700215840394010b0f200c0325401c20842c0e05840c010a560b0b41e500f550348182d885a188503507615407120b44041440200d41c3c0c010b0b4040c80c045d0340d000c10825260b504000d01480756001e6410010403d200080005505420245c1081c02c09001e4038108980e001a840700070410103011102142c481c000d102c24404803a82e95100701d90070380b80c1501141094071541e03071141660404044021040c1c0005200c40340c0c100801d030010102c1c04501941490400d09032a00c43e40f44505a901c41d007940c0705910081030045500006072054401d12500e0255150b4070302c402540842c10700042180c240d007841000c00c8508201d4100c60040c0d40250818440140c03902c3c0d1016001812004480c0c0140840408603520400b43c1c0c2c1c0c419240003d2020b00c0251540810b0310040030040444501e0421011a62082d8030041c14128140194000d11040d01c0302001c100c00c82c001c40c2001909540b04880108040381c1c6218606410344 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 591894118 1250 591892868 591892877
    0xc0509040b040608060a06061e05030103030f021c0f08090606060901050c12040f151407030318051e0d030e0d05070813120c091505090601020c0301050109060e0601050a090501030507 80
    0x41d071301c55005090036412a8040910395507810b0400090781c100319480c1000c6a1950029900d510400001e4204c2c081804080c0400c100c00000281c01802081100020040100f501e010030908440c0240035000c045c0c112000924500082103c4010003e0040d0003200010400780c18943c0240046405402c1394030300116502c0f960980c140145030000044c4090301280039942c80103418003142ca940c41203900660301c204000e200000759012101825510001c0c0e01d4500451040c02c09841e803100c64400250141850007144292240e8030b4402d02d0b03000b03050b610201602c0d504204200c06030f048036841002580181c1043d800103500394410401059064442c106503410070a40c950286102c11968204c1c0b01c543c0c0c92644802d0602c8085031300e0100500302201d00b404941e00d54400340f03c003029a403003203600905160012822a07802071003030644c0164050000c00866039202041070103000d00c2d10621240c1540c0c580400d01d154420411100154095204c6071805452700004400404000b00b0500800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 591895368 1250 591894118 591894131
    0x11030c0108041b0b0d060f0510051e0d0c1106150619170c0706060e0103110f06090d0b0a0c05130e07120608030c06010b032202030a02270601030c0509040b04 69
    0x113003d51014015840340a0800110242403607414102c0409640080384600b1051480c07030300255010040360b141d0005298485000e411151403210240030741c081c440c94841c2822010041b607035200304404000c100070011600503441e070409500c0002014162990024030030420945c81c1410740400880105042c5446d007401e49541651440d101030550320420064070000b900414050b8602600c070103082e07a158844500c1d451641c410417920b814920260040e22415689403c42c0c1d02d600580f9910040503090034800403ea28216440c808101c1e21103c0884c60103035018409440b0348142d82d00010000020300c25542801e0500317100c010018102c03820002022410b032513401c00380c003586c0001d2200340300031502c1c0d58031440e88500707008058010700b012020078810003a294004045200c0c210f8140f04401800031828008241000d001c020081c4d0004184860406101842000101440824460201c2c5500d03051f0044040e120101d00400c0004c205001460142c91b02e61f00444607001cac01003000600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 591896618 1250 591895368 591895379
    0x50a0209060a032c030d0501141f030f240e01060807230d060810050c0f0a17010f0305120c03031b0702040903051305060c06150d0f0b0411030c0108041b 67
    0x105541c41d004c00702c0e50800309100c2da241910780502405841d6000c14072840c100014085211842000300008012800d0300c444100c00d070280d400b01c4a002c107001c2c02030240203403a2100c24180303541c0b44000128038540035000940d18101c0d40c01076050710825503030032409031940c00c02201d04801c201a0502c0110004640b0010180c1d968001c10b4a05000ca50100e20103140011003810320902810b10700741c0500b45000c000912000b9012608000c0340c000d40d264135450148030454080c8070a00d0b050940046000010031001d810300d01031401c076442a41181c1c400000410700741c030a40940d600b10921a441400454bc102034000080020200700c1c00c0441d05240040e0006000d80303c0704141a40070901c00900070fa258a003203050080a48420b50386203160021403d0030f269144002804064028900d001c1a041580c60340302c0c003444107403c4040c42540402c1e070300b0a100c1d24030054601701c0c0c40414003811113041c0d050108000300d040405031200300715503a0b1503c03030500201d450f000d115440d09070b03d4004940c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 591897868 1250 591896618 591896681
    0xf120303011512091101140f040801320a0f0e15010905010819060209010212040605040e10080303040f0203010b2d030a2427020103050a0209060a03 65
    0x304424481046610584000a40f80c540010600601d40f42006a032001290442c16071441d01e56080ca0198803007243c03d4120807039401404c1010340c00040004001812403015000040c0c407080707801c03004002300e64000950003036020281a162141c030302d0318001010841d203135016902c0d00d030407801d0124258015074141c6050000d29180403200c01d00b441c006104020045c8901405894550000c002807250b0301d550220304001d18000800003500010b19000d264400d00000b00c5024000c0031881d00c0303175191030020b440c54101d40100803e0915080c001600d46c0c140c1511001140c00c0d8501441c0b8681b19a154036207080484002a81c040d900c98050100c2601c0702d41e0160034500e2600d08030141100400900410080310103030152180c1d00c1402e0607030204840b40d029000d00002c20382c5802243c030f0f40d6003260340542f07a00400c03007640c254143d00e07800b4615001898512114400d0381d042200d07a80b42c00d1658102d019414083e40c20002c103000700c0c49414000d500c000c140c1c080034050305070140100ea00102 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 591899118 1250 591897868 591897871
    0x6050903120f1b01050915040f050d0503160801060c060c0926010614100f020a061406010206060a03111c0c06030603020102100e0d0818060c090f0a050d020f120303 72
    0x101481002410710529403003d4100324000c443c00307000f88900d08090f01c2066540c02c905002014980b14134001c6030812400ba0500d401c2594400140d4020b003051120140541d002110504850b10b0b4a072004100b0b503210b81c1110741603404503120006115420f840b80401460060548024409008004520725117010015180307c5081e9900c030400c0543c0d10403240c01d54240e03a0248904922403c100101c2e5900c1ca006058410002c1c90080c2403030185420407842c00303100741c901400b0585080c06e400e04400482c50703141d20a12003a02210007503110001031110000b610310000e0040c03105e011503039000786002c40300d40401c1e862020015040041d15102d019461440e54090004a5680e50f010011940c06104a0f040504825801c000e00c01824070b00720b4894105100c1c120412001200090301070041070b030380340f1052007990100c60351454900801c25090740542501d900c01e400c0e100c009a180c2c035203005a081682e00182007114064442d500380010800140900f6503c00c01c0b400544003030182c00c10146 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 591900368 1250 591899118 591899137
    0x22109030a060b01030c180b0c0709111314010f0f030207050708070e0f01030807171605060105131e0c020304050306040c1e05011b050c0d1401050115090605090312 72
    0x1600501003c0050126968000341e2810700200c1205909413040c110b842e00c0880d00301c54442e075504e072060203215041c40b58580204007454600244040c1c01c1040300050710265148003503070f00c18141c8502c07002600000400040e07000589072141070714554401d40b52000134810300e0074054101206a80c1300d60504070036030010401d83c0c1c8541005c200b244080c40344160402030344003440c03806505541700d82401380308450700502090b6a0340342d014040740303084040b5003103810401c100c002103002c249042500d4140a01c01c1d10f00c1070a0300100c04030145024840c00030100e4807030900b07a1b150020b00c00500d018042141903201540070500c40050941c03828002148941d100c1d080303c0c00a2410641c0750140030344c400104051218105170b091206981000b08180482843d0309206500540381c0b0308a031402041c8503c440e04030f007881101108004110500b49a1180d440c40248000c0e81c880d48809010803890031050300103014844100601400340c402001d48460160943c0c441480d035030908e408940c08111070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 591901618 1250 591900368 591900371
    0x1c1404030b0a050708010b191814120f0d21020a02030301095a090b0a020702031507120501060c1101080c04061d030a03020d09080607022109030a06 65
    0x70000340410070f1044a41c45507982c18940003079410888000741038015082051541800d8a0302c4200540c040c565295408040c20403e10701039807110201c4440c21500c245541c0518190b5142c0048004003003000c159444401000301030145600800310356400b00c44000d11100c451240840c1e1b0700e80f445000400c41e00d070058000b16a25454a80d01d0b030115160b401e0f080c401c0d1060801c000c4400c2000012103020490000d02449502400122009101146540741c44100c0847e540405110201d07400100c0c0590040c140281d640da41c038007191040c0c0c401e001c0025407640100c0302d54840c00140601e00380d0445003500e402c004030400e81078031004131202030b04114007280c100c15001c010000300300b80070410080d01307103400d031814200499641c01c1802580103200c14000604e0803468440e60705c0d58079501407000102219508005414040c0d242c0040900b280c002500c00700010401c0d1000150050059501da4010010f405201c000c551480301c03844205407810100308070364011641d04004102c0054000d074070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 591902868 1250 591901618 591901621
    0x4110d0504050d170c1b0106140a06030e190f1208040c0b070317060d05100209011407050304032907120e070b09150c07030605040c1202031c1404030b 66
    0x340a0318001c0443c041030204280381d1081040c03225140030702e0350400c410306140b5841da220311038560500c0c480380781d00301d50540c40d00c2070001d0351174016090000c07100d03800c0c2c481021143e00d80108509840a80c401c0e2500790b031000d4601402c0c0480010802c4c21140180550306c40d0040659494085952050042c40000e0030002032109002460f46440010b110740044141352062a030340c043c200c0a9001c90086e0f9140404000507420f0320f5034850030b11101e5104007610048200454940029003216414a000984000e003c0c6402c42c41842103c50154000b8011401c0500c2e559440c0c1c1d0303904101202401e5040052030711440300b1510101d5030300910481e12070103101e20000304201c0440c0c1ca83c3c2c0c101413081c5d01c0410104004200c41d001c03900070310300070340b080d1301614034070040a030481c07203170340d03041915441121400020702c1480d0b40050b008510810211000301c0d92542840c80d1008032100103903050700326000440b913040c071828804c0940b90842c144042e01c2e0000e4040306446070041d50041d03d10111a80 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 591904118 1250 591902868 591902873
    0x212070f021819050f07080417121503030418050a0b040603030302030609090c0d0201050903011515020c0a030309060809100c0c15050403020307080a0912030f0e010f12020904110d0504 81
    0x10140789a4102c540d004002515200c007240c0c0c15144c000d001e0710180b110322070100f0b081c0b110800c00d640009d400004000e52300c2140c940c503030007060390441d03000c605004082d00300c94080ca0b012003194200c7d50540740300c2e4102c01042040000030312010301408003c03035031020602c01c207448601500c4011070098800507200d1420506102d28175100034078400e000d401c1201441c00f203039500413608240c1ca070280380c01600d8480400200c0d004102901100c0024551500001561a00c011221812420365425981c80545020500072004807501001b80030440890003840514400c8c81110b501242d120101e401c65000851040100d0705118202d40015120020a00920581c901e0920004a800340c0400282c074054030000d40301d0013100390080070503d0000d9050013003445180c0586c040d0080e4000740d50322502d1890080e14910407050000301203804e08150344803543c010035801d40c81020585801c5030800094040314001d62200710002d40c815a18100c24030900a5500a0030b50950104d9000601d0308060 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 591905368 1250 591904118 591904141
    0xb03040b2511010b0f091902220303090b041401080601210b0f0f060405150c0d0f030e030c1b0105120f0f0c031302041517011b020d0212070f0218 64
    0xa0055801119408541445031b00e924000c141d01001c00103600b42c40a0f003640c04070002c1e124484982e031070790740902e07865190b00300b0079140203003140e109480700103070326a66016010f014020f0303100b402400c07481114422899400390002d0340d0300c40d005240c290401895009420613140e0130b4486c3c180102d5450750340c20f40d14204a0302071048800d040314401c004480400000e00342e44104d010b007a020300c0d5512212080d19485c80b041d00e514030485415601034601c64000107180f41c0d00449441e00107402c0110401e01000c0100c21544030340d06420103003030513281e406010007010b01c0351480541003120410a0700410000105001d0080c14140405041401c02210341814240c02030000411010100140440c11100800382d4800d15415200401c2800c401c1d0710300507200700d40340c1c001d20b5003a8040398148a911819802658080c2110f0345090085070b00d448102e81d00d038040034150001da400045400c10031088070780589046485008802d403002455408200660120110341d610700a010b0b061002200f0034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 591906474 1106 591905368 591905381
    0x71506060315082503150c03050a0606080711031b030417010506010903170409050106121508030909091c09090c05130e040f050d05070308010f0b03040b251101 70
    0x101b06602c081c2c8206142c08000a01d410002030240d0040d01c210f9054603041c0d42c60a005070f0302c030181560703290614212307011584028099044a140141c0d112240c3c5039401001d1501c851420060200160500f044495140d040104200b00c0c0e99001c6c005004494002c42d06a900280c0b1354000801c0c0c1c80b803034210380d540b0b5080c08000301d0100d8014070080c00300103d00300c0c10404458840900c0031201030501901015070401c0140d149940782464015030400d40840c03d0350a0f1541e80c0401081401594503c1d07408600918020009200d0502c545c80c1b8010b103a04002e0b261640c407114401141502e401228662100744021905011341f07003050031081780e4003100701c0c0c0d180250254040c000360807d29003100020002c84c00401d849114503198002c84a000e10414255101c03a9a03e8015002c01003c01e00b00048840031200c2d01b03d10300e40740742110703401da4a9555212500000107800c0d03496 = true := by decide +kernel

theorem cover : BRFrame.Cov 591726618 591906474 := by
  have h0 := BRFrame.cov_init 591726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 591726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 591726618 ≤ n) (h2 : n < 591906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
