-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3058
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:32:21.231422+00:00
-- url     : https://prove2.me/submissions/29aeafd2-b3ad-4b76-a386-0aa792bc082e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 549820143 ≤ n < 550000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 549821393 1250 549820143 549820169
    0x90f080309010b090103020d110105160501020d0605030607020a0b1e10080601060507050a0f02010504120f0209090712170c06070206040309360b060c013617090406 72
    0x1001d1039400c550b0a8880f46010310f50b0a00104050703500d0720b1101c0d5a91360070984140c59500c4450040340c035031103000140b00c12900ca44441c00c051290560151900741c4078600c04001007a00d9200b050380c1d4410858244005a0120340c140b000680c01900054018240d00548003110603203079900301c40d00204031082d0001c02080d03d02006411010030400f4014421424902d20340100c40d1101030300c03002440c001030b002c0c17001c5c10703044411a4800c10854005110180400c4c80e030341c28500d8030344c00c0800d0003201688204580000315944090100b00d0104450094160036031a8447e9a586048049030358005604c18405002100c000c0e5004c0c0482440f0b070703403d6800341504d03107001c0ca8003804030440707500042042150f4030390030700200c1d40004141c41c1c0c040032801c41091145000d221a400340040024076a00310303401040d540c3d1905815000a80211140200c010f02c0d009800b03180c1206164118410842d5400c2c1031141c0c0c0030841d00035104070000c850f00c5425141000349404201035520541c4860121120 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 549822643 1250 549821393 549821401
    0xa0b0705010506180124020a0204180210030513200904230111160c05030f0d090e1b0a02070503010908030610080613020a0905091e070305130b0a090f0803 68
    0x4880d4800d031407136094011000e200c1d41801c82c03400c055081c070301d001e65071110f580c6c1c0200003c074001c004c00050640c0c001c00601842000d001c014101030b01008003240161420701c0718003540d0380240580c601ca00a034201e405e0a00e00162100301d00c0c000c40d0088160480741194011080c0d45401441600c81c902030100d8449036079140c110301d1076000030041d410882c0d92400e018071504d84408421102e810a02c800d80c0084030b6020b0034002c00d170700d01641c041941489440d844003442c00d400700d41800b00c3c0000703031207602020384c1e50b08250703070a20300484014030078903003c020300403040c0c00b840007602c00c204aa20440d81c0441d110030220382100d1000c0410f44080001208100541c50070718015001902d051130003658a082410204102801c030101d0310700f42d5074012070301c42c40d03491043c0701c601e0041000926044441c10110000c80107002c035081c4254506201400207500390f8001e0107071601400c0440e900d144816021303103e41002000161900c1ca0403038440f0702040110384000c0c9000c038694054034600350340b810 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 549823893 1250 549822643 549822649
    0xd0f0f1d1305040c12110d140d020d09050411030a020f07050a0609060e03070209071115010b19090602030901050f040305061e09070305061306060b0d020c2a0f0a0b0705010506 77
    0x4c00c3d60000704041c45441071000040c0340441c9210310003001b55403034144041146491900110404840d151a00c503d2048214031640000c18030f140c01c10540302c5150854840040c0020f8511560100d0204a81040840e41c03000e10781d80102450b1400500540c1420f240e50b6500d4281401207500391626510340c0154020701c000c51190b1052280f0000085141200b070b036010800402006207403000784500740c00408960340080c402031000c4502010a88070b00c2da150400750060307421004400e04140c10b440300100c4018020300d981c4040d500700743c00039824000785100440b00d039403141045c001c610304182320000002d8410000b15000f000000104c0d82d44000020480342c42840080543d10740f5848180c080000c1403011403203640004083c502501c698500d410424013408041c0e0000d40b045c180082d08420080b190b40c080c2c07039055050416030740508050703201813182803e000e09a019005c10b540c00c0484628019000c11070702074029005424140d40c422003003180750010321065446946031020014030346 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 549825143 1250 549823893 549823913
    0x528020705090f06010804051903180501090e010b0a050f030705120f07050a030b1216080f010b10030b010915112b0809010b130e0d0f0f1d130504 64
    0x8103884030a06490a0780fa6540d1000e80038144505004402001c602030200c280504800140000800b07003401d600c503c0e004007942c600c80c2c0c02107491561440085082d6206501d0841285c3d401d03005010301e81d0824100041c580e204801c2030007805401c001e01302c080440500514491144c5840309074641981d00c18080006a005014001c5440fa010402501c03a8100c0b007a40c1009015203000030354554128080798500400040c0c1c00e100c1d01c101101c60b0107000110b8240300540c1c0725001034918520f00d200300c03a1f099408190711568480104143c980155109a01c42c011344cc80c1403404994095035015003010260681c98140d0006030920542200305a0401488905005035251001d801c0c2c8800500e1000d90001385404007084900408100b4052094201d009501c030010500d030000303000d03460000000c00fa00603020480d8020142d40c0e8005602501110f900c2c80100d48401d041007031840c400b26050341c074450b030030340340824103030150f04440c0c4035840d4002e1034401145c5c000803a401c003170504401da1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 549826393 1250 549825143 549825149
    0xc05100605190b1c15080619050105010f0c033c1701030623090604030e010e0916030e0615030105062d010c0602031501140702091605280207 62
    0x98084507410407040f24080122500d4a0000803142548144807095001410001668000860348a44081503c91001ca58980030f1080444c10000c250040708482094500910820307021034040c41c0e2034201c66000740403943c0d05511030b14201c03100610080803040e9044001c40e402c40580c20040341e5104503140c081001d030f5925054204002045075510000d00a243d050000030012a11482040c0001c0340140070b00c3c000d0002c4887c1c0c19883d06c1e04a1080e036a1790000c803419400144a8000050554001c050300540c02c44081c2c003000242c0e852890040c81074560002d8032017010356a1484180b40c0c1c80900030f0030b002c0c0100c101e031000240e404000701030079980c0c0076100c01d2003a4030000088281b19440c41c0220340009942c1600042c924640005a0705500001c0010340150300010402001243d104141012140300343c0b2020111680c1428540301d5019984009404c40329407004a00740c26404018000782c0c0a0520b40640751400340c1d428041e20240f004070700340c000907050300d0205045405202c11009 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 549827643 1250 549826393 549826429
    0x100602070807140409020306090d0e0a030305031501050904180b090102040807170c09070c0b0705090609240a0801080f011802090a0f1a0109051512070c05100605 71
    0x4081d0601000c5034441c501445018801100810118540c0d2510740001c111320303400a00780c541c18540002d19070b0700e0354400c140c04000a400076032681c940b4036000b4030079800e4075050f40e140350840d5130756000c401c1011403076801e6505000301030010f0780d401d41d502d002d104050203101d080358507120300b030346080941023801801d892a0340c0d0051005000400000400404840c0305402440c040d16483c00c00500386260f26a09641000220301000300da83e80100c24075aa4a1150041d50b0240d078803030034100c9145c0a0b40340000e03407044040182982918082809030490504444040c00d0107410756950516544105d6200c0045922a401003104800034040c1c640020f84510007400120045039000c1030811940318020301c03558184004c148103d040e40c9c050007420009000801c440400c02f0501065074040344a4a40010030074a40441c041c10919480780c40c11402000041c00c0094a1b942c0f515610700060100c010007482c1d220090104008001102064402074400504c0d5400c010078041c07d00c6051a178912 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 549828893 1250 549827643 549827653
    0x915091401020a0804121e0c1a07050d0b030f0105070e0a1a0405090c1207030f060f05090103080c030f03150a060c1203050a091a0907050d0c030611160605100602 71
    0x1090784e401c16022540141d10401244041c41a49000e640014000d016108102d800340d5041c01140d8203e4080b0600c903002d600d01c00300c0b0f00f4144032402084001241c00c070000071824031054440c0b034040d4001440b004401826104001110801d083c01c50306c0c112032090000e40170f020a210141004041d1001070305a6812202d440984008070040310710840c0f01d041e0280c1000400215002050300030f0340c0d0307810300071940c420b40c506011034001c0103882078a9201011a140c64800541442d140780d0038000c03110701801c4003842d43e117140c0700c2c0380064000900c040750342d001c100311050b0341c4c480d10702c015480707040899082900302032840f007488107028541d00003105003c560314032840401c2e0740e61102e0303007095404d203408142c40c0c1d100303211840908407644000307101d00d460400c501110f0843c4410144101e05200884c0c10380380d03a80003000100c141c03050740680844001e00050020980d1508910000f0700007640f164940036035242e0703601c40310788401c000346d6409a903842400700d9000c00c840c1400040200e803008203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 549830143 1250 549828893 549828907
    0x30f01210503090616021206270a0f03030204050d0b0a06170604020f012609010b0406030818190b0912060709050d050a0c03030906030b010302071e0303091509140102 73
    0xc0c2e568401c0ca42224858803010403060150022038030580710555015101402010354001c92a85d10340040c1c3e1020301c810301103030020080304034104910010f50304150040182d100644c80f2891b80d807003100710641c209034003040b01141580700e140325520a68852528428549480d04400c411948607801c00010041402c0460940400c00203d2a42042e01200c072051180403080050b00c00704140c42c151113140131081105141180c80c204400e20460400c0000c0c0f2031000c00c5000c103c11030701c03540402001c031b1409021000060030904800f2114120113002c2080c1a00700380640c03c03800019a0081d0183c90700007603400954180240c0e0340c41e1000c920030040045081041d0b020305801c82c980540d5014080300e6161b0020b1101c1044440145a0030031002c900f0b007516810002e00034810750150401103800c003c641c00301540300e482180c1c1c80c590040c0c58003080860340717160190081d0f0444015004c0503100e004400200304100da11104a000e403072400158100c0c1b503e8692140c2e030041d06d0016903070348144415 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 549831393 1250 549830143 549830153
    0x18050112060f0f06060302070b09070302030619140a0b030c03070b041404061802120906070c0303020a05090406060201020a030c0315060c08071202062e0b0f040902030f0121 76
    0x2654900707a0062020918055194240c4000c20505004000d81810032000140103a015030042202500a401403002669900c080580d01d41c4648030003505540428000740c0500e900304800544400b0002d400316103028076103e403000b01c0700240e6410028542d503801e4030b0b00d28582001400d01d100c1d03050303002d0940c49203000e03040080e60280d40b052010b50390301d80c1d010824903690340c0e210700d0243c004603900d40543c411022480d0000d422a109988141d5511400705581e048001965486042c1950350b881c0280301e16a0102d01940060f04484240310051010210035569409840090040c40e800140c941840b004020184c803110440c81c0c0c203052415900c3c11400054150f494181c0d1040c1c105100d5603191881c01c07910620034240041c040e41d05145804038425404192180559030404004150045181d10115001d01c51b106290043c0b48525007040700f05086009020040c44401e51207041640c0d901104080e6482101e000080c0e04403500140300724a100461083c0d200d80300e460f00800c901c0e1a03690 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 549832643 1250 549831393 549831419
    0xa08090f0d0e2d06090301020c06010e0f07020604050c060d270b010b0408030d110403020613090f02180103150f060509090c0906041206060b040e0411091e060d1b180501 74
    0xf240c010100029070803141d4609404552400c43c49408484540da5216211403d021080e2030a8456020392408910703402d10000d08a03000d103030064080c00c0c800c41c020003082041d03800161a002d2494840d1050420b2140c51003140c0c40644190401101c80e0495240c20341e019030301600490141101440203100350311001040c1d80424601400c0054030459079099a102800382d03910003035105a00240e030011360032080c1f240303174219440d44406100e03102400310f010059028254076902d07080510f62100c031140d803103034000c00401111405d9240001e500e452030f16540e518030303404c00380100c0c1c80083c0c001500d00381203000380d034002c0c00c4041240c01e0161040006045108074030852200901c004089410701505501100051015121f91a41c5640c0c0301d0000e5950001110240d9404640017100c40141c1400c1030700604c141203d5025420500d081900340f10010800b42020790040c451030008000107030b155969850883c1c001100441280c5005003041d507403d4a00c90204140c0d040400401c4000c8000320 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 549833893 1250 549832643 549832729
    0xa030201051f051201021603090312020714090415050c070b0c0702090723040e01080d090e011502010f0c021c0906080a090f05070f060e0303030105060a08090f0d0e 72
    0x9040313104c6203070f07003500795001e8002e203582808001081e5003004100360700a00883e0849124a00c20040e045404034142d895640320b1107952a00b03800c40d01c1c0ca0555203807110351186d11522810001000c45120904841110700885907100c1101000546030107101c2c80040d0b40b40e00009040883d860f100307031540460320040c0041c0c07a40c018840e80144039516290700b0003440c0c00f002854007500b600c440da540f80c5d00d0f202480a2094072030500aa4843c0c6a0b401e02c9402403905a41100160032a180d29000b007400c4038280c0071f03600100310f540c0c43c48a02c0b08840d050140080c4030015600a04444029810b42004002d11a0b401c1c0140141e1400802c00c03a81c1080805030321a207802c000003a004410304001c00d4101014200500a008511020480c0484086030006481c03141e41c3d040046a52482030560301d101c00c0c0104c03540120288014143c45115200d44c9502c5034058003a52441b20b400307907a80d8507207600340050030081400081d90710610b00f0084a85e84038105110300000b0300c02186031442c2165482c9a07 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 549835143 1250 549833893 549833899
    0xa0e032101290729161d03070524040b04080c09150103091505041209080109080f0f090604090209041104032a17010b1003050907060804060b120a030201051f05 70
    0x2007901038210722070101c52081c02c1000d03601d50840d441c01e030040a41d0000d02c1180f44012408040508420480086030f0410351b42c0c000d00103090103410541008540000c1c1010400b10508a40004807803d41100c05400105160742c0c155864509182c0d490f82000b111002c80382c0105c08040810100200032090710a00c0f0400782000140e01e021801c0c4000520181040c0d09200c03030074a018042040341d18140c500e0200c416942d544070140c0c031040d00c13600341d409480380904088014400d0181c0c0302c62500081200002051143d03180492403404501c540d00542e00c96449030b0ba02145080075402d083c0640a00010842051450282541d41310810400400746003100310b00503012112910030b51407200005044202034490744c00039000b072240d02900d1000310480c061110f88041c0c4541c035000703000d16405199034002401016003030483c21030300d00c2030080065076900d84504e44081d2a84641000540003103e1401401040440c2d050103400d448002e4108110140c000d0105458100b8003004081921004c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 549836393 1250 549835143 549835163
    0x80d02030a06210302010c02061b0d022b05010518010b0703120623030106061704050c04020a0e190e01051504030b070f080a050f0a0e0321012907 64
    0x40a54800104500e80018803a40d03510b1500c2ca403e046020143c4100c14803c0d8001e0250721a600c804984841050303504406039106029200b012024440141580f039120007401420a0200340900c114031108403001c05040d070708004415081c2203980900d03405480c06803085002a00c01589990000780144181d0082c04004540074003090f100e0100031800d40c060000c14070101d03854100c4520b10103e87c00d9124000454100c4064207030074113003c0c407011200ea60301d4800f1010b044072206984084000c0044803140542104603110b039449101a00c1416610380d0342c90800035151041c040700c4685902d58450780101850200054203160008505480c000d865480b140c070841130403440741d800380b0b410003842c0000c031108009480780d0040d80000c2c0b0041582d24441543c65040c01c05c2c0446900b9100d01d049291030000145a0204541090600350500002c6a00e8000039007071014040c0d0742c000101c9800141c0a0042001c0d11200c1c50880b14003200b40b04c2d100164030207260303800d82c501c02c01000910a00754 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 549837643 1250 549836393 549836401
    0x22050c04150825060e01020a0b040516050d0c03060f06080114091203040f0f03050f0a031e0c09030f020f060a030b041a06030a0f0e0d090906080604080d0203 69
    0x5024040142201510500548024991140c039107400d6010b04421849400508a580100c900d900e8019840c001000704645051041c21541c0094007520f03035040d44680d10001001600300c50b115407046015134090541642d0f04030440003203000c164446440f550101102c00042484a042401102c0c1c5c02100080c19803019840030303000e041c5692100c0e401c1e511340500c0e4640c0c0c0c0b1f41b10b0003040c881c44d144020f495082e20354004c3c1440500040d00d001e0000d81700680b20000185c600c09006501d14002d04003170b800c0c481100c80e030520340d502c62106200001d031038524010390400c0312415141c05810421061000e018104001489580e4500c070181064410820840a540b9a221046400c00015140a0b80d90484480c0035002d800c60003450b40c000ca10b08101c041c0078407003120300301c1c4044800400d402e140d030311a03100c00b101134640c4426400680c1e6440004804085081208404145068484241e0145810341010031500300f0752104409410800c10400040c941408486c0c894014560060712901c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 549838893 1250 549837643 549837653
    0x406020c01140a080a240807060c120804110d0f03110f150417030403021b030c0d060c200705090a020301140607030201060b1b160b0a030e0a150e1522 66
    0x80c41485403514071b400c182454982d45902d0303100400e507a207142c01c4440c1555a07000403071303400301c0304400070f1300c8001105080303030103035118075005501b0600a0413025004000b101c006007076440c040c4801c841c040e0310700c050b000030503411001c0c83c00b407000c80c10094150414600c0881e03031688000d940704c4400c0c440290000e02000035150030302d00b02102d081e402a499152925001e9503d08542d03028641c441c51600340d040c1145400106c50905075000360004900400c2e41d540c07407001e004904280814004030188140c0042c0c5000e0350780c1100d004140051008501c1c0c201441600c41000d00f080000500400040c0898590414801c420b408242c81e2a9030f07030201401e0072401001980c01010417650b0001700c04119002d60f00d45046000b03e003005941258101c900750100821152081e0040d01409001c400c0207a4000e038000c94050080100b03403814000e840c1d484100090740400040ca035180da03591040b110000c02c10000c2000f0280b00c4141e485410044c50029961000003c000c415240200340707001002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 549840143 1250 549838893 549838901
    0x203180f060630030301081e010b03120a0302070f1214040e0f09100e030304110405090c010e0307031416080d0503010e0712020a090302090703140a020a03060503030a02030406020c01140a080a 84
    0x3c05030b056030f80300e51b1034141481c1c4540e41820548481140e10b40301c55014a0103120352021040010020001c010007002c9032034554106441440034181c0c20710000020941c1c03958035217440c602c00c9902d10f43c6660201c80151915940f07040f91280090203003c2031007402c0304145031a42001d680103c0d00c01c9542c0701d0120038582803107180141e400904081c4507604044000002d14040c910034070702c69441c40200c1c02800116071046600f4a8160700c086141501035000d00c490141554014065134031185d1240c4031180f8000c18140880700c2076201c001c0c4d0700000503810a00344c000d00f95081c00340a502d1f207034800003000340c00180180043c0c140310a01091186000710741001303a490380040306540700d9036032010103802c2c44500d100503402201176800040d200c07403080c0326402052617078074030800080c0c81c1c0759000d1000390452075055051603642c00002c51156000c1018000c500070a070f00950b545d80c20900c1c000d06100c01100c00c1418403503002e81600e1040311485c03d403809000146000301c1e01e80d540c0380701c20340a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 549841393 1250 549840143 549840229
    0x15100806060f0d0c0e07020d0807080f0406020d020a1d0303090102062d16120e0703080f0409060f0305011a060d0b180c0d1803020c19090203180f0606 66
    0x11840040001c3d00b0100140384078800c1149400b42e90300203880c2141a40c0b09c079402c03500200087c20350030001e80e034154080c040d0b0b03402a00501c001820000f00c541240f00700c1c1e01c202c1c25413011802030341c907400d00840e04915881408809170701540c00d040800001075511480170700001c0b00345200784a0800510740c070b1902d8640200300d4148104082c1030007080c00050b011401e081e08006410119042c007044010300444161020b020010880546503441e11304803500540003145080760b080000140840503400b801024010000000c1d50083c507510b0070508484640000741c03000648020401d02d80e9541c14140c40b20f03103005200100d0030300e40801c0000c6440c0e04000d50011101d910006104c0c80c0d003100c0c0040c080442c43d00904210086060704c184090796000000100180c7c40040303c000642000504115001901319a240b01c05840390700140c1660006c4902c0d1800206c0340c115410f120500f00203a1511510110282c512801e000021980103030004d1005441e60118002100d00701481c20101d03849 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 549842643 1250 549841393 549841403
    0x536041109040309030201120501260307140115081207080309010f0903030e0d0801080715050c03030c0a0f210c0e120303060f1807031a0301090515100806060f0d 71
    0x220319107840c0280850313105000503800241240c041d2403042520703100c0c040c143d0300e181202500d00400004c1645400d00003038640c401601040c00036000045103540d41c21080403440300042158624200d40c6442c561440e841b0707203420b9000b640006040c58076501118005500416495074075501e00c2040380c0503241c1c414107421950300d000000c2040c19803650101581501030801d41c1e0000d9481d060841d0091400e000d81030380303604540c8041080307403120701c45103607c5026410030f02d0802c1c2c0c0c524081c90554008850500404400080c50328083c1e62000001d02c030710409040610306c0c0c0e451031018036801c15500c0031054280350f584141055a80c000c41104e801e0140c0141030b80040300322510b036140c49810903185180603401c030041c00300340e900c0e20500f91321040c11003940ca94095074400c8001ca0190100d181c500c0368a90b90f42d50b402c9001d460a002d01c0440a0089000b4541e02e40c0e0041c042841c0900107142440d41201c01c40309103c408000b150003078220504941d440841640040000c0e41c9814007070008007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 549843893 1250 549842643 549842659
    0x4030e0d1109011203091401030e2b030c02031e0c01110403060c090b0d0b0f0a120c090501060e1306051f0207241b051605360411 57
    0x40100c0700d125a4001041074900005070b0342d80b0503248510702040103000300440c43c54031080c4902c0038420110422924149404900c5084110784c0b181803900300c0c10044815141070140b08040042d0a182d003c00011038902003020241d00c0781d00a48070302a40700600c110740400340919040d1800e00b001e8410725030441000b00080405010410030a51080c8400c03500a8184200c0e080c490b401840d0a008079145820060324101c03c0c92074507001025101c2e0156442411246052129110480f505015040d4807004250a1032281080042e106213176108060190521005122190f80f10b21004200001030f01c9118201035414002409480755411940d000750700502c401d40b02e00090b0b00c030000002004d400355901e868a07459000016a44194200d9a0b4030341c01816a080324030031803d843c5086003c00f80455000d495a4a503400c0c41075001007840e0f040c1800c5020301c01c40c40d0501030902811124407400c42500c101d50ba44d0108800a28100c1210b022003100003414460301000c4400005002003c0503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 549845143 1250 549843893 549843919
    0x41a07110d0e0102070b0301080c0909100906052509090207170711011407020a0512011b020d09050906131104080706050d060b03060906040b0f090a05070f0504060806010804030e 78
    0x2c140c0045490100c1c014801e5041c0000c84250346022039060383d074150090203401e0020360900140001c0500300390800c1c440c5510000c0d5403000c921587da1680c4c82034501280c02c1c202809004030b01190074500c43c1c11612840300001000c0e42140c00102250b030105009070f102c40540c184901604407117404202c4a003800150202045406907036424804401d8031262014601023804510600030058025000031070710300103100b035180c241d800c2c2040ba0305ca0400442c0001110010303080c144108101c041c0941c3c049101c09071408e030040000c4015107010741c1c481080d1b00c1c000300000c01140c02605410b24041c1daa040009508a038003017150090498481101c900980d200e0005000c0e501c1a00308850280c40c0100102da11501c000480303019403001001c204054a507070041100501c20402030ba6806020340000c400c8a44448504602c6000501c1c030000d000c3c90049005840c10b00601d24800c104401017006000c0680c10003055030700a2000e20303005046a48500d401e850354800d940c3c041c0d5100011642c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 549846393 1250 549845143 549845147
    0xe2703030402102c06091c0b1b0f09030f03070c150503070c0219120c090b0f060d0903020c04020304150c18060302030c16050303070215041a07110d 65
    0x65006900c20f5075241e051900d000800c0343c1c0881505080042a84580b00003010f49241c0c0750a400c0c9400000d12031490142c0030b00000c0c4088021703546c0d550103420319042c610140452443c4285d400342c04240b020580d01c000c080e54001740d01c9191905c4124482c042000001d60b1000c00c48511403440c42c1046036982c410a0402c1242c9608510410701c1180910341c141c520144583c050300d0040001d80c650a003c0d81513a0f08100324240b00740b00303040d0310030320b0442c0010720f03c03d03004c4040508034014542c4007082c2c0c0c240102501074840312071405000b40f00c0881e0a003030f00c0d215481241c60b0030661240020703030f041084c64101c0c01c250042e18a158000c2c004805e11041c0141368414074041e0b01800b404100036904504140d46495600c4640e2a08905220701007041d28040c2d002154844401d01c2d480f0f02d08005140120b10800303030240240c616500210030091030540400881c481c4590402401c1c2c2c0d03514269661840660300c4400c0111000d09030300100d103c00307005061001c0303906100e40c02d84248001c14440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 549847643 1250 549846393 549846397
    0x140705041113080a0b0c0304170f0c010e0601050a1503020f03040602030a1d070b0a091502030c12070f0609050f070e1005010c120e0d080f040906051206010e2703 71
    0x184114039000e80c2d800103111000000d19160965209400c44c100d6034850826403940d4000500030303550f614208403034070340090890006103000c2a4601005844000046a642c02c41d24009840c5e07880d980440010f11050340d40c61541c4040f54071552003002600034080301280a401040b0784d02500c4c075008020302040100301d0300550700c00d40725140108424000310300f000c501c46c103c03100c07182100e80020000340100a0074900500504810342800180282c0c2c0f82c400300c2500140c284171400580003ca800e691480b810300000703030401e1103988414100707101c03034841c00003403900217000402040e0780b40b6900c4c04208040c4841a2816210400c1da00d0641e0745034070210b103201003202d01d9160300801e840007142d00d6005c0c000d00070190790801a0525030740b001c054261400c214420a4962002c90805008001010340c0b000300301c003400d401d4056480380c2c50a1420700035600180c112500c034860044d84001d035004005026030445001c0b90fa0303142282ca0b440d0903c000c03002e07d40d44510b248030384070905001210300080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 549848893 1250 549847643 549847657
    0x702010c0b011d0a020304030c030305100b0c0d020f060403050f090109120515131e110a0b090a06050c030901081803040e0603100c080c0a0917010b0a0605090d1407050411 75
    0x8407028540e0320840044c1c02c07407008413401404103510803a00c0002c60b210390300203940400403000c4021416240c4849660f190419091200c040d400340c02102041c617814081d00260510440052400341810f503006411030265450003480030b1000f064681c50b580c40341100d88014002c0e402c0301810701d9034904015499207201c095140d450400c0c2008954075604070701c0c4207451603400c4484400107214001e12200c18000002050b280e6130700301d185031480c540d151807c007401402105505980e410542041c80380400781c90340306800b170090520151081d0b00d804002c80b00c05803070034a0044143d0ba00d1143c082801c1d06a000300810604c400708010607016050000c450141c4012801c03582c1c1c034910034036280251040c06000200282c030311404502007150741000f0384411703012410000020303070b202e02c05034000c0308124501031150382d1503442c0800a410444001c80c064419490b0080c0740100d5900880c01c89a00e80318001d010200060040600c0c400c280702460203041c3c0180240078510807042c1203034403504401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 549850143 1250 549848893 549848939
    0x120d090b06010206011d0a02070b09100b0a0b0f0903070f0602010f360314032409071e0512161101020301050109050904140f3403080702010c0b01 64
    0x3102240c0c6541c0005242c070304890411a0321804840c03845840c106400c1c020b852140001e80a200c9200001c0410850070311901c144001440031040f51030361308065a0301c1000c0c15028440140d414004180810111402d03010321041d20b90385c803240032004c80d207415001e03488240104c04102010031403e0303041d04140120304d9500c50170711482a5201440300700b0a200c9510b800581c0d900c0c00e014440100054440c1c9140d80642031040071030140222545860788100c1c0c10718088001008400e001c0d02d10000c6c2c0002103241a10f1000c050715102502400b949201132201524290064001214501c101e044039408200c8010800307540c20180c080710700c411403099a14000c43c100e1034070903400f0380d0140b003038a04983e01650b56402381803511042c4181c2260141080e100c04075014882501803504100306403407801d1940c01000e82e040d6251400c000340d411082000300c104420740d0611200c0b40c92403100c03015650072081140ea2903003e440185e51001c682c0000030291061480002601004040c019004a031f0003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 549851393 1250 549850143 549850163
    0x11280c181d0c010305040218100f080a111c02060705010e0d02150109090c0302090f0a0c020f0c060a0323041506060c0b430e0a031202120d09 62
    0x501e24100d0050440308180801e038400540703514990b12a80055400a0014000b24051401c03149840d158408c2110300441c22044150304005000705c0a2662000340402c10140c0514882c1d40d40b4010000c05e05842180709110030300c0e200c882c0802c5086a412103030b50081c40307587c1e9001c403454803c1c0a06032911003000d56014280080c02a103001150b000040d101c0100313110050781c20200b1040003002110700958040040400c08001a12010303065070182c45d290344006124902400183c1c15248550304a0045422a1000407040000060150401502203c01c20344403050700e0030442c01806015050004000003211369092190442c1e00395000798092500d054560818044401c1683e1591290000090350140c00102113000d014005410036117000721941314440f4984c94a110040c50090360941515114803a9042c900d1030f00c010003000ba01d400c0150180141701c0008044514601c40078068a0108410240d400d05c24848500015150058903848003940e0041c4001010b80350b00480b844084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 549852643 1250 549851393 549851411
    0x120501150806060d170d0606020a15021c021b01060303090602060c0a1b0f060509010609051302092418090625030c020a15140711280c18 60
    0x400e08500c03c01e0050900c0003648010f650b40141c204240d400004592424044203030000001c0c0038000040c0081d0b030040c41070b10001e0600078200c50100301c040518a204006601e00d10900041032000090b4a040040e00c5142440c109201c81e051501089910b501c0d00ca408070070503800600100035240c980c1d00310380075580d07240c0800460380708081d80301011070320312061a0200c031002e100c1c004280740f2030104183c2c91355450303540d4801d4800c10740c0c02c00b07010f94441c0701c01e1229001ca0f00c1101e80c07144454001c407949e031031160045014500050301c0c000b02d0801c41c1006482d07000030140e43d041c6d880c10140029120103080b10140d2401c05064496425138050100850114034481d24042c01c224210074802e20720240185041c0c00401d0011194003d5005542c0d441c00440e1003da40c000c0000c0300503501151282480705030555035040104140c00780701c490b003540046214005070503104540703840715070b030410005890700300080c05409000a100754540040403031020700182c04103800d0003852005101c2030781 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 549853893 1250 549852643 549852659
    0x1203122f0d061d0c07030207050409080c0d021f02160308061807050301051503040b01210813030c0e0c04091802060a1d030a0f060f06080a030e010813082212050115 72
    0x4030381107011b001680000c109100301c2c541b9a00c04c10b842c074418a680d40c5040070100c0803900f010903034004400540c201440c1c05050080e507030261220300c1030344201185054060340e0005100c007264680070b0200b0100600058880d11211492803100c0302c800b540c48082e1510810003072082d0300900901d4061000700c480c44c0c03918031224050306e0040b988650750b01c03c141e003440421240c4590300741a40b020042c0100708030000c20390b03880090500d039041902520041d821818100006d140340c0e44a03001154040d010803c0f1200703000c00740c80986078102004180c90b000000c078082001000c41011b94400c4002a0320340c11150010071641060942852192540c49200d040544502c442c1c00080c080380c0107205c0000c00174003941e121003a051340384940080e043d80c44080482c505140341504902040109180490541e0051405035212000b20311515800101e60b54260700c1d8020712170302c50b070f010700a0ba13184124521907850312405840c0c42d060040c580401c0d810518041c00054580b810309000328400852050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 549855143 1250 549853893 549853897
    0x839130e01030206031b1c0e06060603010e07050a0320030613200c100c111606140d09120306050406050a032109030206041203122f0d061d0c 62
    0x2030f80040c80f0b582950781d07480304080300f2402c3c0350103084910f80400158142c403681001e01d1500006881000543c5001420341d545030000c050b00a5100310340c284010801e98004065a030741c44411441c2560701ca60310030506602070884140a06030a880c64070501811882e030b24003961090000f100d103102000a40c145240440e47e0000041024807030540066404152400052090150306411107842d2205048520200d03101000f1000014119606240c0020010810180701340402040204500d2a2007006080c0e0449484005c7c07102d88003060086c140700c070607401b150344c85402401c034a10180d8a8a40100101140d0003071a100301d10380b50021031503040c10300c148820380358031990010790f4442c100d5401d0b02c0d00140c03c40c3d4608118500b10044016240d50002d80018a0240d220415041d20b03443e0207021030040800c0c01030020301d400403102c1940300c40b81e003001402c814091540030038030030300250381c4440c443d07030002420082c1400b600040c404226030001d2000c4480700c00c3c4405607220a081c0015074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 549856393 1250 549855143 549855149
    0x131b091a010c1119050d080301030b0717070809031b030301081614010507050708010f02070b0a05070e040e030d09050c12060c0d051e0a0c090602030a0839130e01 71
    0x3102c502c41d4803405400c0c10720703144030300c01c1c2110500d0304502c0c2c5c2c5200040c00e48031003040880300c44001100400421080e4100346400c860310b4105005480e03800040146840782c01801d40c0100302c55140400c2403984d00380211500e6500d070200c204130742142c1d040042d0792984280f160049602c256420800a00c40403420402a54800000100300d41581001180c140d084030600340e4880c00b490f180040c01c02d20900c80c82c420409100405030701ca11050804094050000f00b44989007030802081190b841d521441e80040760100700c0f00000c101045d54442841e500916140b10b16081ca41400303070003402000121b810702802c003150106c1e01284104070403526100191112441d029042c045041c543c0125008aa401032034201c41e1a0400d20a1740c2480d4404010ba515150442d912a40034400a40c040c100001400c01d034001546800840f40c8000c100ca130004152081c5211242141c00d56165483c841158402e0005002da521108030046440181d0111910901c0c00800020004102c0c200301412812 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 549857643 1250 549856393 549856403
    0x3020c030c0604031e120e1e0a1703040b060d031e080a0507020304050105030a0b04090f0b090705041b0c060b0d120921080304020f060c07030b0f0c03131b091a010c 72
    0x2421241140d000036280c0d1030302c42030860094150440034423580c4030b50748100c0703861140100b8048000b42404440e140c15051135003484801042048040b9510f20800c0341c000c030050710301c00c03c0500c017403d044444221140a5000c040e134006505811039601040aa0281400813000c10041d11090310690307480c89180310b43c50208105000043e01002c559004285e0070001800100c0c10b070340d032991007000040c40ea0034115140351004091100541040080e440900030035501000b61002d41c07100528032018441280d000c00194503c40381c10800039803c103401c02e01c0c015209051040b0281740018013400c0d03078a542c43c0000c610480028142800c243c00c00c10703041c00c840c0075202c001260740300e05403550310080003607801c100c4054030002c894417400020a8000d6200002e014203500303520303010081d00c8010740b40c104184002c505100000b10903800704d9070042d01c0d025441160124504d402654078007201e15259101180d04400604507516810080c0080b0031180c811b040506043c00540742d80c1d800d880b000e88 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 549858893 1250 549857643 549857657
    0x1215010b0c121306120504020112090809130b1003060b0405010f02030c060103080417031315170403030902090c120103080315061902010c091d0703020c030c0604031e 73
    0x1900400314000c00030340d00040180c581800c40c40d840102a03511100e400012400c11a904000c0d16034048a41c20103412100c0303041c0414102600001e2280d103031042540300050360754460104111100e401c5400c0c520015020841803901813040800030703c40f80e02142d0007209403030703500289240305e4802d680a451340810143c1c245170911004403111403484070b40d0b03015444100056520003a007040000d009600c41d41060b540d860624510041000036110b400d05203a00510080d0f0904860f80c40107816102c0c0d203440707090054085402202c032004402c101c450b654643d102400185541908842c00ca640241c55000ba80d844003680d00034a440345117901c071030300e2082c0c0c030050000501c3c2c08000c40c1c02140c0c1600510303c5042e00d50009585030300c000840780b500e0300d80c6000d001c030b02a020702400e0000c28444c2050141640f03041c01c9a15150589800400899440c60000302c035580aa0f06884507040c6400440761583c4446802d65541e001c1920107802080c00985101c842d00a82d20410300300020300c0e41c0702c00d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 549860143 1250 549858893 549858899
    0x503070f020406080a0f060e010b210c09010306140f01051c0201020f03042607050607060e010207150209030616120b030c3705061c090c090605121501 66
    0x35040303100d10049a000d03488980c00144184200965200c042c0a6000c81141002e0362078920f080769103107000c140160b410114080087d640d4442406604041c0a541824958101e85c006050119403080250700642500c00402401955441411000e170390403003200054440c0a00441240703030901c00d0540c01202d00400050180c1c500c4c44402400384103004940e00c54203c030304940d0840e001a00440e08485025103669101c40c0d1020703080b0300d0015180081c000803030a280108809102d541e402901854032149082d008440035411551441c1e00300e44842001d1010700201e00c060f45c82010740a00c284101d034007083e803611580807180051030701a00d0304540301002041c0c0c5c0f4003070203181081c40d0307040c015502480712a88170481d00703084800342c1c0340c2d480d0180072011142110b5090100c880c0e259021a0020070701540d105c8200301ea1a0031301025104462001c2120914007030304814000826461100d4030004000a0a400c45004e03a0421603042118070a41d41c40382e40e42d014402120080c0a400e50010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 549861393 1250 549860143 549860153
    0xc0f07060f0c0c03021603050a080c031303060614041401170304030204050a09120206010308251b08120705060c070512040f1a120a020a18030b06120307050307 70
    0xa000640c03050a0115100c2500c000390412601d000580101060001c0340706001c25506109007205080000381d17042c0b8450541c1c507280d50300c2c581c100c8020502180041c0123481d50200300103842d5050f006c00b80d44140c0319101d14140004c0c10b454031500e24000b1b003050321940d181c80c00e4094843c0e40c010610718440541e10f480d102a03420f4409c62000c40c62030100f0407011000d40c645d0b0040da071181200507404030f14003c0e14a000c01c0790700c480000c640d0454101800500c005001c00c1d00300c03501d0061300e452520b01001d00b0009201076403040c4200414484440010f0300c01d00428a80e100111960b91064400e5545500032032a018400c24000614607000040040c400c900c007035004d000306031f004c0c400700c446800c8130000500c1264010b410541c202e9002020410000903800c00285084000d82c110b1130a090317643c6c3c20343c4c800c00d1001d425845c02c280c02143c9014081d1007482d284040038031104c14062a240daa0134410b91044060396150700800101090120700c500000440301030720340c01801185000001d4642c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 549862643 1250 549861393 549861397
    0xc0f0f03120f090c19050d0803060f010507031d04061206140907050105121e010e010302150703120506011238090106050a03140103060b0f01030605011d1f0f020705010302030c0f 78
    0x40240c40c85c042c00e074045800d490f2902000349036803080c2c4c0078503902c2c10f052040110a804540b2201d0403c80c0401500c00040d80c00b01d6901c4100b4800e00c0d80d221b00000081c00a4040d103440e401140905980360741c2c000030300125404c50512441c5030f1441c090103848d00e54581e601c03074645004071404510100320303070b22070301422030101caa102a5070885c11034060806112084002020303489004e51606110040c0154034105c2c641d2005003208000315440c1c284255400380100c00c0281d0300d100116620720000d00c01d44d00500c051030000d02910010083c22290340b054240c4039074001209103500121250003210b56a181d590184155002070161041e0303803808100b1120b5a000c4581e4400305034407011080580001904d0305406907100718004121403d40c5028004800a508075103410107003400e0041106903000141c016405083c05082c40300b044200e404910700b820f40c4042c60b00d01404414581c50a554030000300b0400551943c03d49064617071740c1b00118240d00013660900641072080140b030041c6181000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 549863893 1250 549862643 549862669
    0xf0b0a05070c051f080f040b011502010e060c070b090303090307080c0708030a03020c010b19050d03110706030617070b0d05091905031b06040b0703020c0f0f03120f090c 74
    0x40d0003110b41d0f444001050010940c00400e500080e4040c50780454076402c0f511184c1e10000480740c1080d50b142a0f25035500402c018810880f4458510a0300c41030b19100390030480076899501c0841d0b4503828040c0300c100d01648080010390301c41c9094008030340c01c090007008990090200e4001141006050780701d02906501110581c45548a041d00004100205001030b0031b5903c4079841c0140c544c041000b1540c203650504685502c28981c00204000c01200c4400401c00e5070307005e4418000c400f0f0540746c2607030700601000c800021031003030310780c0020309a0703150b003040069841c0030171481c0310314800e00165035446c40c0e04d004030040c0403002c0c08800303a80c059950080e03601440310803c8801d0b07034201001c00b2802c02c10560058505420014214941248944a0820b4144890002c0c4040d00d8951198041d40030003401503000c05400154107144040c00b04480030141007a1416198031600700038046a507540710310900070795100300700001016044080e03220341c4a004403201418481192000300030b40640440303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 549865143 1250 549863893 549863903
    0x30312071e0f09090c020d08091510090e0a05060708060f1210051003021c110306070206012102031b010504080102130801060f0518090316050a0c0f0b0a0507 69
    0x8010050501c0403192001c15280e82511030581d601c80d0910010950034003500704034000c6041500750f10b5410750000d4001d504285515004a90f41c9500020a003044c240b080001080e04202081c049941c2c00e240c1090111040c2d801d0411a11014146641e1034a10212001e03003da000000024071050041c03c80f140c1c4498000d103840e9400d4040030010308010743d50146102c09610825040c00388012610079107402c0394600ca40010703a13070310716030000341514540c0c03c02c000b8140d014040c3c8010482c2c0880445a04407005007540e80310300d040703400250780e10002d105000340030b1411001040000310304048000c6c4ca5801401038205c40102000e1101800d041070249030401c80100000642d88000f0f201038140c03e01c2034280b00031040c1c03800410900350703440c85c0c1110059045054041000ea41c032070500b5102c101c00d141021000e5540c0407002420b601443c0080200f00c045200800b0402001003440302d80180315040b010f2050792240400b546420882c003039014601410080c0c102454083c3c4085c1610500c0f0f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 549866393 1250 549865143 549865157
    0x40305040312270b0d0209040207020402070f0605132001110319080f0c1e0c01060f384b03060616050a0f080d0f050603031207 56
    0x81e0b54a464000d030782c040240024100304007204680c80704401d075903c403c00c400c960b00c40440c10250101e20030310400b00003d903c0c40d030004d0a00c8403a1603a4054641a0b50001c10440d2204100e00f0000030000e01c28804032040751a0000080e10b010590800c00c0031503812121010003240c01500360f035000104443c825040c0011158440a940402c00090003a0008032082e00c031108000c400c0038003846805400180c14000140c10003441c07000780320981b1161050140110701042d010b40c031301007051080c03175014181542007000c00314481402802c03200403200080d600400200028404c01d200008100700f51040d01441800c09400c8081d250241903c0540d140000342260942c101c06420540e20f034401d5510321011a014500c1c0c802581880c440095115800528515100d0000341607803203000c00081501c100030141d4401d106040040e01140e5604c0700070303400c000c0190305041107640c0100703002c0b40d0082e00744180c910a000550040c90300030380303000d00250700746104142e0340f500c03103180186400b00300022 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 549867643 1250 549866393 549866399
    0x10b090a020901170c0304030e210d0806040b09040b0712020315151303261309111206241209072319090c050d0c0c1a04030504 56
    0x14499098051200380c400103903180d07242c03400908003c1500d10070310070000180c82000510039280c0201d0394429454074102c00300912a00c00185070480d402000905500c404041e903911300c800007021200312040d500d5055640d61404100001c2e40d10341080c103500090000007140002d4040c03021190080d41c2400d180b14070004141800049801c1114580c00407151505a81003a00f0301c0c40c4100001d1a00c41407031494003202405034401c0044502c00100509190001411442c21009a411041964a960503640c0485a200c07500311480c40c025401d02d01d1034141c0d00145038050300c1c01c8070400d00078013071240c0066807100e0070051821404e00004100300e00c08070700447c2500b035200091952003061190b180c4207003402e01c00b45e854074035180c000c42c5262910f010703101040010318640e40c3d100141202c280840203807056100614004542c000320801d03080c031030003090240c0c00074050085407660300d03c200a00300e040303c005c99452900040252000f070747c01c080200c081c40c3c80032046178403a00030b0406500e400d81d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 549868893 1250 549867643 549867649
    0x61e12020d02030a05060414040b070e0a1203020f0d020d12061a03071b03050d09020a08121b0607051b0a0209101401020d0e010309060e0a050d1101051003080c010b 72
    0x480400c1c01e00c0401c2e400410018111218400c550b04600c0c00d4800704104440c0e0b5020040d4083e000d0f1018001140d000005850346220b100c9000c030804000d05440c4d8110303691100904009890300c02240076000b2800108004100096001500240359000340302c2010034050503116040890303407410f40640c56510201e040b00d8200420800d00f00d11501060b07032442c0c06000104403074140720a11031a12a00305900c00030952240c240c2c0c0c85141c040c01d0010b0403021070b02c0082c600c000c4036070003204580103591076010a003840002411120403441503850303241c042415035940300c4030b045076510080381060003101c20305104c0d58040000c1c1d00313010301120020081d036000640c50300c1c0200c54241d03462030703003100601586840d84201100440b080c0020131181d0342000340500071603d98407409040565404001c8140844c1c1e4001c04041010b00c0182e4141e0038050422686030621340c0c1540d004110140000844560141725003480750812030510a8500d00355a03c03003036158080c240e0300415640303480000746556 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 549870143 1250 549868893 549868897
    0x3c100c0801060f0504031703060607020409050f010b0102060f04030513170601050a150f080a0f020c0d1e0503010515040b13080c010306030b06060c07081e0115061e1202 74
    0x15911034448030341c0b4001c00201400b8400b1440c100b0000d00740b004100190800d0404403011f1841c1c140c0546950320040812524003030381a02030b500c0b5040100b03801c00d2010201c0ca003d0301c1450311001740088800d0b600166a01e100aa80740320030074480ca4000750200344680007400001c000c0f485549603007999004065204440380100c2c1c01c0540054004214625040c0300703450080c02c0a03244002c0e402c5803110701403d401d47d02030324003050040c15400240c1410255104c07840c83c074698a41152210703848018242c0c0c1d41146442d5101080e400314107005200b44a04100c0441313152591003d00d903030b0810f0107004081040c1c0300b0110342d00f1000d010104460307607040080c009100c0d24018901e0020729105a886c5003c400001407418140f0300b01003880400d02c4ea50307403030750701480039680309542d0851130b0070f0140b520200360b001904501601c01c4080b10b007210090b04100500e5498000e0084070780d0701605c502d02007618032a582c08034001d00004210074000b514004c82d41601d034106154855600301d000c200766 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 549871393 1250 549870143 549870161
    0x10f080606040e010b030631110904020102010b06040605090a08060f01060c06021603180614071103030c01060e09160b0d0c02010605120a0506010803180d050102130e01083c10 77
    0x701d2010049a200400d02c4184206003840300c21808241074154440e20441c10303270b14501034010340c080d400040030359000b5001283c0010003e05010340e00c0e0b0340d0b040000c01c15040b821445205801e845800070310680b00081c0a4040c51104510318103d074a4000140c4803c460b12804480d1140c003031044013034002d403094803801c3c028040d49401c20360300b0301042c46059201d01c070b8200c1d000788078a849281c484240ce103010340e00d8003a488100040e42000d5100042c1c0386008616420701c6a609004000c5030304074500e1691400b0701c6a28088845200841ca0048015080c500460344410000d000418240c030554000c81c0142070540000a030203500c9a002c900082107080902409030b101c0c125070303c02c1003410401180103240d0305014504000f40e10018011020300080c4e111b104980c0c000307030401800701c2981110305c92907244141c40d000070340c0c41040300c4203840300b403082144a02440843c296078540d050125030120480b107808841180660003d4003100104803901c00c003502c500e42c3c0d40d03980d64510740314103520 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 549872643 1250 549871393 549871411
    0x1a01030b0105031006080706120e01020307030e0d08060102061b07020a0303031b02120313080c0102180405090102070b0604020a0c021c02041506091505070602120f010f080606040e010b0306 83
    0x410740c14481810b1510411100c2c2c440c03da86880b401704929100812040180c130010318080c000044401c0d8048050100300408240551000080c0590580c0550180070401150070954154141201040e40c18800c00c655080c0913800030340c00078840440c85007459407854141102c0034203040c0e0580215240d803c00d50000c80200f65254282c09803a180e214094001c0c0079107100a241c441c5103c0011700366400050b2001418611040b03040d0200b01910054506256040000310b440d40155401004003000010500c1c3c0514a400081500c90301e0600894007020b8212256200907119082440002d52140c0495010018685a0030006a5502c2a0315111402c031611145104000d1f00402c0b0032203d0483e039030b09218556510400c14240c011300c4071021102030710000c01303a03422035802c151840c0c40303031150040500e40300050300c44035200d800c04210f02a500703c407003a0201d681c03101c061002d900e1150180c5091644800c00142d07240c0741941210584200103800881d0410806000c0389c40c111007602c003464 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 549873893 1250 549872643 549872663
    0xe0303070c0605010b0403021f0c021c0c0603050f07200d1d1f05090a030b0903030f0705090a030b10120804061106190b0a050604061d0d02100c1a0103 66
    0x1800150f000b554050626021061301c0c1c18139650003d040345a0140066050880c41e0600c48400c90003103055455050b006051403071090721604070041c10070442c00048886401c03a0700003061451103403160314800d80c41c00001480070348074568256a200c040310074040c1d003540002c040741c01c484410b2042d00400c61103074907024194208250503951981038070b4480d40c01242e000075034818010030100034000e22803a90a01543d00c43c00d11022603170900c01d641001e8402c503480c0050001b50309001004511411404007101c0441c0c80d10101217645114083c040783e84211440740600200c1e5081c11102e41005905410464050b502c2c03000040d1181056026642014085010495103400c8901c81080c410100d024042c54a014040d40c0d034030012240380c80d07041c10342d69500b03484c4684802d08070002070700c2d00030b2919441f550b03100da0050078030700010b4440c208180c60742c915101c60304081100004841c0d00800c400c040701034803002181d001071b0b68134066460026149030111403407282545e550203035009105400c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 549875143 1250 549873893 549873917
    0xa05071215050f0f0c12070e130605100f02010b030f0309100201200702040b1206010504060501020a050a110a0b04030b010f0b0c100e011d07081507090e0a0e030307 72
    0x16107054200d194802400c02c801c00528400d81a0003561081100c1c203c485161510204130f01103004400a8802034040b1409000b6003a40051054503074240481c0c003003000303c0c42c410b000410b462951207403030340045587c801e88030003c1c010942400341130094800012000c41450000c1c1c41c1c404245418903a0380c0001500007024100010700302982a0180024003085140e4107002480161901240c0c00000f008110030046540700c3c8c00078002003400900a65074900484892600c4000a1180c103214600c1c0500005155001007480041d2a80040c007a0100c0c199503122540039802d102c4240d58001c09582001c2042000c48000d003029600800d10340c4001d40c10050045040711030380c0c002010415007480398401085d00014100c07a015013541d40894040142800a805003030507a01c19000c08a0303103c0143d00c02440010624211440c0000b1114400051082c0303001140098980c04c000507540e12050080451944250350440c003e801c4c001100d01d111840c0030300710b4105603605000900c40b48091 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 549876393 1250 549875143 549875153
    0x3060c2d091011060c07030e04021206040c0e0105031906050d0614070309210504050a0305010504110f01050a0c03180303020313050604081908040f0b071203020301050a03030e030a050712 82
    0x240c0c401030140c3c14000e408209030000c081d56a00c0085c100d507204040080c44100b014451404212640d402030f10039511200d0b404040120f00704101c0d46240258030b0130144c26016032003036100c20741d61071060b110180ba40e1503031099103003490340080740c00c404917465440010381c0d501c940710b91902840c000c110018140441700902058140f000d0f04110400d41030196010201e00180e44a48000100401c0c01e041008006002d4441e8003403580900d5001c51417800000074440c064010070321561103079180d1500710030a41c0803c62030340400e200c01400a64148003025082e80a00c9014880368042e0034a641b60307808820020140f540507810440040e00003043e0502c249545070000f90141c5011a8620b0034a82000031060380e5004450184015030a440515424071280004a5003c0c21035101011010f41c2c6403ca5802c03242c0c8200003c40c0c10b20413106140f05c0c0a4441d1096038140d80d0018584401c0c1441d40d20100d410110511095605000d1007280e04006801082100c7c002c0c400e2007000e424001e014108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 549877643 1250 549876393 549876409
    0x60106020f01060509011404020a0215090f062a0706020c01020f04060813080f1b0709060e0709030210050322120f020304031203181b2303060c2d09 65
    0xf06005045400c014082d024001c81041807c3c581a140143c50f581101030481c94031105c880310145100c1e40f0f205104101d1804216104e01103010030803201561264082142d5880d128031101d0b5030000d401c0404144018080c00504005000702000b60624000400da5422030b4840f0400d001d10b24030024042102c80d0b08294095400700d1800980341c0c0444e680d80f10104035107c1c02c00b0700355074000f000811035204484200d00d40c400011f558211013103ea11440e1f448011311081c02820b06524103200003c4807035110300c41e1071080d41ea0140c80030904000508040d2501c2d000500404103c03500c01140001704020000360884040c0110b0050014008100340170388030800c1c000500045410810090000c20350303600b0003048040c02d5182c0001c07480070704803514a0001c082000101f40c00030140104040d400350344600c000352103c0e00049071100800005004404021072907140d099005240014601c800f160090864004002c078003001803041448108140010304284064511001ca00d0007281e04003025 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 549878893 1250 549877643 549877649
    0x1210030b13050a12031104080307030801080a050a06050415020d0c09090e0c0d030c14030c010f02211f0603061505030f0f070c06050a020c0d05130311040e060106020f0106 75
    0x840c840d8010498a40b507807590b041070806031182c03200c0c200710b4100390f12940c80f41c0312622001c10700540700e944424459403203510040050f800031302b1000000c00c0c1000081449411760382d101e0020301c50800c0d5940c1724006400700500a4a006a0644034491480c440340000c2c06400310208000503104030043d006070a8910b00d801926072185400c0c01c0c2c0e85d00d03050020303001c41a6001103a584410543e10302d0112111501c0f480d005010020b041d00031040d440c0e0010140410b61002c00091007150b2003910340904a0250040d02d2403600c000c83c8800352508801c00c6201d40000b1907030f881d2021f5510707001900d501d10300540e101c03400083d83d5010030045e203809021120100b40c10b901e0143d103103041001c100c041a001c0500394102088405001c18001d038040e04c0e04c1500320341c2c0070009003c94039200d0050b0f0000c3d00301d0f06002a16005080c1c0b4082c0c20741c8101d0480705c08445030155002050b08503140c3c0c0702141c0b007100c0c0e0103810a6a40d1520f000340d4004010a5000304215801840c1124a03620814290340c1581c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 549880143 1250 549878893 549878911
    0x6032d0225140c0105120a1808040306050114010f0806030a12020c09150a030305160221100507021b040b0901080d140408033c040611190204020c031210030b 69
    0x4241e81d1030380e80007085075416000b110a407030702500c071f4490f044000c1001c1604441c00301e81c3c6c02c0440c810000310b04c0142c4103c0e40104c400f048075a9032100110400b8000c074000394005030506c0608a100c5010305d01068000b50041c08554003c1020b1b0740f1000303151020002071016a02c940700d100d040e40b4240e00c40d0b071343c0b16000c0b0703000c4030042da00c0c0301c04030b441400140001010b014005c10b400030002400b0b001807290540080080c581010030303081a18681c0307540c4008418038016441c0407601c4190500845014a0007540284001c410854061071401d004046480d03100c0d44400030360080daa5840303403080c0a4540032000e807081c80c4505901500d0f00c02c4241d045103100c00180020481302d080030080e1002400c0340210110555480b0000c0200d07180c0019220701c0d080140030490450702c0d1f907800600203452030343d12400b0300d0001c40c4600e036035a4205080f07070040d000e404c00e108800605054010305007031605802124180160030350308030442031085420f00d00c14003200034100180004056500d0f00040b2003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 549881393 1250 549880143 549880153
    0x5010302070c090e16120303050112150e03091f0306050d0c0b030403050913050103020102061e1f0e09030304061802011b020a0b0f0706050106032d022514 68
    0x2603403516603104603441810f040f15922110482115000c1c40039521589160082c0000140c40703c01c8541418541c201c2500000d1a010000c9800044144d078540032642090521514180003503014000d444041512005404240228005a11000e038040d03490124100225904815044010101c03503484c0d00481c4a01140f000000105244031228070030384210103007041e60f0b07075900e0400351000c2c412103411603000141520109003150180d030226058900c00d13030a544954407100c0b01d0840607420390354217801c7c4400320004644d540f010f0310b032140440056408010b11107540d6082d2100a620221143c00e46500300004100411105124120355400450340f030f020060002d0700001c104030203803a900b00d1444501540f1805556540792000e0052400c0c1b01d074541d503448034103d500196009000c084580364181800854400d00030300a108076480103900900c2c031401885180c40400a0080800030188e600b000780340645000c0c00714101180440c4c170100354040ea1141b902202a08440407032480d55000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 549882643 1250 549881393 549881407
    0xc03061506030c13050a0e10090204150e12010501081b0a06051c0e030c1f0504020f1e0306041406090f1e070506030726060d200d0309080705010302 65
    0x2840282c0750000e0704040c81030f031a100d0400c141404607405030040760b131022100000007400d2070000c00c003e2107015442029000c06a6480e0103106900640c082c0700c00d04402610011a030900c640b0382c0b0b91039044000c00d210390701c20000031403a08503042070f00091403d8106005031150142c1400300364400e072005490020043d481e00714006d0040c01055050341c9070504011440748003128a4001d0000500c2820980f5550324010f041e459a8102c44000400c0104d9401d0b030288408081d88100c1e4484d0b40c000e000c0781d55080300201002a1820341c008441d8094070308074918859501c0400c841c51080b4271910300c41c031886084041c4685840320082c5000c0c0c03158331003255680c031014082507800740940140d440c881002c180345043c60600c1700c19006140c000002100b040340e904c3e0300003a0380e5030001210f03044401c08210040c90001d10b1104a88150300241c019000c2400078404070b140c1c030f0303070781c1d1489a142c00018000e20018203600c5030b8140035000200001828090b00c10140300c054003d20302400c04515001e2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 549883893 1250 549882643 549882649
    0x702010207150c0c0b0315010207150c1b060302040317030402030c0f04020c100f18030c031d0d03020109140c01020c04090809060703020d030f020f030a09030504170c030615 76
    0x24014001200c0b820205003641c00d00600007403196540c08500c041c0060307252075100d1010b80044403e080b01500e100d803c600035500114803842030350359100da010321a10940c1c1d0140c450380760f1002c044410a4401107403889a8007035540980c054030850307501503600da1a40c2869a40b00840e200311103c1004104148401a60005078050450390143c541603400d10311035000400a00500400d4043c60107140c5000c8a070400581c848000140c06450800800391a08802c0c8180b403411710780100890490620b05002c240561071490f41e420f0f040d040d404502c03509a011504d10f10102008402507910b401921f070030050803400c05200208168000c11006441400003507070381e00f210f10760601690b41c2e021842c09000313113441140c0302803c025000c0d5988410b42c1c54020354406444e20314000192418084000003403aa00880f58903809200300301e8116220500e10000a2181c00000c4060180070000064840321880910300340c044114094512901c014051604201d03006049400c0364003856008000c0799 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 549885143 1250 549883893 549883903
    0x100c0806031e120a0305060a0b03010305120906091302030a11160308150409030906170f1f090609090b0105030f0d0804030c0203120307032d0b0d02060409020307090b07020102 77
    0x100c01d9103000b0140000c8842150a0640104041c0f41241c8009003e016580e0150480c600075181030710303030560a941e01c01621405000038040281250000c0a003038840c1282000a49038214000f03184c289000c50460010301d070707928120111030311241c002c810040000e000d4490b02010010080d1318078500010b0404005202032090001003e110050b0003084c24030001a61501042c58040d008100d801c14600780640243d100d481407000090701514005640f0f40d000f50f100d0300440540008054984030a0081f18610300c0960610712103003088840083c0352034031b90098400810150f0b900080c907644030b090071b404152058001c1800b03a40261307100e801c0b034000010042400c12541c0341c0320303140352264902141d0122160340080d5151149084003001a40580c00450080000e070b10100300f090899451001c0c2203007a40300b00302d00001d81003a10031104500d40c004201002c0d0080940716480101d0340011016000368000008113507002c406c0118190700300c4a000f001e0a113018410741007003090b5000035030311 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 549886393 1250 549885143 549885163
    0x1e1509080c10120203130b07020307050c010f110715030c11190203030c0609010c03060608060a05040c12051501030b03120421140f16120b1008030705100c080603 71
    0x40d0b85407421002a540b02e40f000343d240044029044d035581c205250070840c0d9001301c8100351740c01102080130a5034540000100c0303408943c03060251020030704910055414103818084035092140305040c40c4040c0f8420b00c07003000034010003c42080d0742400d00f0390080468a004982405100040012804540002440114085480168200b420400e00c003190860050260401482c41910140705004006400c0a41035a80d036a07400c002143d5103007411907112109481854002c200040c043c00541402c2c0c0103000d80c1d80c100d0400d05007a10f0300480c6030080f03a804854880c000140280504019a410700405080650072801408502c055120810041c440d504c40c0c0644542103840031040c0074056900c4000094000c810b002c1c004001d00c117002d455a00345020071940b4084c0c8002c03446d0800d80c506143c4251a40780e51991461409a603d441d07a0400192060140710004000041d5095041004004051065000d48a4268040800d0b400c0d100c0101904003409008003c00c8a9a00c001a2044e02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 549887643 1250 549886393 549886399
    0x6070201021c150b030702030304022e0806060c070f0305070807150c1509031707090b090915151207020a0f030509040609061508010e06030a12091e1509080c 69
    0x440d01d8403209250083c803a80c80701044110100400080c590080055803107640280c4440c888054040d0384206001e0094011100f00c0c02e1008070014400e200d1501035600c000003900e92458030301001074407440c040c0140c3c011401c0701703150401802000402e00c400d1004180150081c0942420304103903201c003c0c0d0f4001800200201c40303500d101031100415030210548500f10041100503a1030038000e2a070352021203144542c5c0e4807100030983c218821041c40341154a0180c00600301010366080000d040e40c0074040128121007510341040d5999850414200c01d03d1050702c01c0e030340f175072034820f90110484020138007015904140504408100c90071001c080055041c9041640d56094000280c010840794000c1c104036403a100d00407419400c04004440d460440743c40c0e040d82680c0c1c0700c0100103140d50072142c041d0185c1002032040300142103a08181840c0226080c440183d030740b12080c4425960701d0000c03084c1500e01c202d8007004801d0003403140720000266441c022182c81d0628901543d40e40040e069180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 549888893 1250 549887643 549887651
    0x2032a0619050a170106110f06070210090809040f0207151a04090501020d06060207050102070b1c021605030c06100b1e0a030f090f0201180806060618041d06070201021c 74
    0x54058424041390420510383c18006140756102c50340102540e07440c0885600354480c1513a440802480004c080344168071681c0180824024079490901900300c1010403200e031b00e81031001d03007000e0b030b030341d02400c1492080e00000607203130780250134081031404240000040030707440c048000100c1030b03003684100302110b0161000306100b000d6240850080c0328911501c0245407030a603003c9052640800c0c000100c5e0026804c031020241c072842c088007140700b10b00407a0b0038218200000000c160440c2c0240908035001c00805503c60401d840d02420f55210310a40500c980203034042020f031141981030400600000100207050292032101c00e20040001200b184545801040c08051140300741c0000369800a118018006510b0030329010f4070079030f01300304124049480166002d81c150b440b80c10050441301c164000b081c55031202c0c1306004169005000d4100c1700d10b054034000c4001d848601410724021130051148600f442d00d18000d40c1011030241007030301164010002000500f51414002c415000c05103130001e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 549890143 1250 549888893 549888907
    0x12080f030c0702031e1621050f0706050d2702010c02040e0a0807110906150c010b06030916060e0d02150724050108070e0a0504060902032a061905 64
    0xa801e034012000c1c02076151040301502095690244801460595031004a0303081c1612444205131601c0705c0d000303a440040002035a040390b030100d4469408100d01540c142d50f0700ca0404010039080208a40185c0c004c0380700051440900d40d070710700c2101c600c0703a054050103a2241e02c001015510340300180c4003a04200702c07008080b0a40d0303980d91003483c5041840048500802580ca040440b641042c4002d0b5034688542103586031b03500384401550700c200c0005102002030034076400103500355080850602d4196689900d1180d094460500443c021002c1000600d90000c6442481080c0340c01c07034205504000403c0310b1203407151915004411180c1d8100c402d80d5801c1010f00e00c40446000d80e54000e409400c04d0403c0190003034101000030181e03101000c00340244d0b80c0b10280160b5918480c842c2051038030b40c3c030001410000c00c0754451074200c0c0c460080800c8030781d080d40004c0e03d414040480c1d880c2c411007550241502d8a00010416003030203041c0d071050b0030b1481c120300719183c4c0d0315254100e0341840070001d140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 549891393 1250 549890143 549890161
    0x30516030b131803110a030801060c081c061403010b01140a02010216120810050a15050c160923040201030507180306050601271503150902070b0112080f03 68
    0xc0200710801810840d01012140c2411000940f04058020510003864031103007600100d1614070060305910343e892140d180000031513900d258984266000e40301030000f11030f20a400d40d85030003a14071030480400c215061502c01c10980316401c403903611030703850054000a039076007010182c1d00204d40380c050b0345c2d1a0300b02081c0a03030180c8104240c4542c0304480c4604041000222034800701d101d01d859440020395035070510424030140c400c2c02130701d611000d4001e04024101c210100c02000d0511850400c1c1001c16400c0403501e04515210003002001c04e0301c00a01c0205175512490171825080a08180ca110300309124105440014102a040503103a8001500c29130081d8803c503e801c2900e885400300c0c03960303400c00c51b0003800152a80360001d0084820100104024803130510b6441c03c40d8207400006240150300d82090707031500002d6081c5615060304101c08040408005c0040c0b0301d020003d603640c0710030310340400c040b00140c02280514203050aa0380102f0251810b450f04046c68000082d030760344030720303480e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 549892643 1250 549891393 549891409
    0x403050702042304081e040b0d050606040b0304062c011b0c03050409090f0f0c03020109090908090108070e040e06060316061707030b0a150809060105010c17040b0a080106090501030516030b 83
    0x310a01b0150020307000071144003400040003034a800170000c001c5600c0d824104000da01c01c41c803a030743c0744400500c04100440c2c4280c0c41002200700040b0060140c1422408840c02d030300c01101c0f00c544036591440c00f0b0b500702d00d1255010707410707d4451030600c003039455030b55014215000301c1c0600c00b035643e513904040d03007000003030f0300301c240000e80141107001000200e141160019955010482c0003541d040c20001d4580198020717a140f2036404000103050880c45001199003445c010b00031010040c042d0f030b10100b0f640b0b03203200305c00d42541c01d64050130303652901000b17140c980782c10f07042021010f010b2024104001c650142d4031000c80420140c000700180c0b00d000045014002080d2019032081c9903503800a80300490981c440d44c01c480c0b42e02ea0741802e03a82c080c04a0f844a00134441e0602140da64810b40300010042440140908144c40c8458101500d440e100500e94000c1c418250202c1c148000500019400401ca200181024a400d110501d03140c114403003a10782c48000c1c1c03400c0c5038030b5810034001075551040b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 549893893 1250 549892643 549892687
    0x1418030106150e03121215090711070b031605180301140103060c170723031314060c19030207150f0b0a12020d0c080105040305070204230408 62
    0x20080c0300c91070301c41a2000038007890490329000b052a88207940301c00e080c08101400b01d06040d950306410110200c540d41c0b048071004001004980010b07900300a40d81c0d07105c030018050209603407118045144c200319203207000d41e190400071034150705000308146132400d003c1075046442c15103003c9440345481403454150030480102075a055090450071032038000314040c1681203034001d1303109008041054606035505604401c810948403940c2000562281c010415480c080c001003040c03206c20907104800e4107140c0c1094601c000600c3c010f2040f4820b11000c400030081c20040315000d06194206003c0c1c5041a109024003c40e2100201050200503070080e819501d606400400881c01d100544010700007c190411f000c40007189403007207411541c1848010f1505a9030040305c19030501025070200001003920301421920900c82c42800314075140c0a01480340500d22a494903034940300130b44104415245200701e02982d54034a10000c0e056000d03000140383d003041c1c214282540e40c1c00c042ea02e001c52812000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 549895143 1250 549893893 549893899
    0x50f060d240b0304030e12120c0a0f050f0f0f06060103090c09020d0c020f0d020a1104021909060e010c05060412120e0a0501111c2c010b030d02060105011418 69
    0x207500080c090034944003d6100d01d02c245e844003240c406440401c02000240710907000e45a1101040714240c058010003800140351080480c0c210f0003082e03554ad4113600d58068101e0b00343c0c000b50782c00000010300b00688801042c684020b00038298000e010300746c3da610010841810180c0390495607080c0040302c640c040c0585076070a030540d90f616028422801502c1c000c3d140f50018480c4050b61903a48101207620b40c0445250750150003001159220010720100061040d80d2059003001006048014909c42c0329600760369882d0a0026450184040c1c01c070000101c00c0c0d81400744400482002a0000c04c0441d8025409208000c60340320102040f105a45411b030700c0c0300c0891902e0015030034a40c0c002607894100b0b02c610000d0145500d48000352140d40951684c070b21001012484821305203003560008003200700700b1800f805c1401041c07a040b80070344500d03100c50351990b59511084c40450405121095900059000038002545091700091940344140b006950000e40890400074480d030101301035500030001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 549896393 1250 549895143 549895211
    0x204050d06090305040b19020705030f07090b06090307060c0b150a0306020d090507081b040e060106050304060b090c18030a150902010207050405070206060a061806030e0a120513050f060d 82
    0x7e1503031111058000b0044d00c01510075003c00180500d400510208009030203405040131340d140c52071035006400e40c1d840d0305038099001e000c1c1614644040207420014035990340c6d40701c841e032101d081c010040c0340041c081040c02c1010300700000349921115110421a80e21150060b82c0b00e0081c040300d0010704500304024118040c204c0c0c00180d80c0000119200d10145821a0301c030045c3c800ca003000200c1701607440c09016908081c004104842c050030246034081e02566002c955a0803c0000405850080700c01b01580391003c05d1002ca08803242c540e0807030075401600142075602d09915240c0024500d4a400800107489020031001c691090100308024440078005204900300280041d4503010308030340c00c900407084d0341c100143d07080c4254119003e00100c0156080c115013809811000780590044405040c0302c1c0450410005101a210703040d060196030b5180d44402c1040030201400c17440303601803842100c4940d43c1c0303422582c7d40000c5400d03030005c0d4080003c1045c40d5003c01603a442c0d440020401d030301c00d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 549897643 1250 549896393 549896407
    0x1209040902091005032b0f140d0507030b0f1311070b01030c030201030e03071e03050f13080d050909241806010e010309150e0c060a050c0c040204050d06090305040b 72
    0x4200d5610040c2c550440c256170802802000c54407210001c1041c1110700e100846c0e0040d0824000c0c03c04078140c0b10079141c000c04a51120000008552180c1611107255036600100241c2d43d40c54403c000e603c0008031000e0b0340709044d000020303084688151f412003543c0d0759291014194040841103c039207030b611104c0041c041da0750f8100ba4171016100d11040c0d020a052464a007140c00340841194119a4891046d120030700d60748400440c1c086200c1812000d000c002c001c1d240c28094800c000e031250410030302440d10594145404c5500307040f80c2503030703507403e014080c003140a503039a03202c481c99030208800d095814106005815298200c4a04003840d401c050540302d080c050a492014052091100385c944000200c10280114111604104040d05035500702ca41c0c02481d407a0368200f101460858001c03100070240802c00204568001d144040105a0000e529440e00d42e0038020f03004d00120441d0214146498140070848890410700e00078081c0341d5a821240425024500380c0d005030940600013a16002d03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 549898893 1250 549897643 549897661
    0x30e0d0503060901050d0215030a020904181104060803090f06070b0f04030305090d0e1c1b030615081f1407080114030129010903140120040305120904090209 69
    0x402502c2040c029124000040381c10708080000d10101030340131b450740e48400d00281d0303e10b109410141c0407601d078a8080201c0300b456a03513800341180710088004000746409441c0f07040700c4800d44844419000310304140003088000008001e40c0d100c440140c44a00d608120300340014424821305c040206218a03442c2031101030036000000b28400c62081d1402c00082d11604c0319181e40701050282c04000074509240d82e00e140c100001003004c9034000300303075203841c80009548031581040b00400205080e5640001001444614010107242d000f101c500403a40c141030400356a1510030316042d0791106400e20024181c400380139880242221804041d001c0d15003010080104240741c00c0c840d0b400c10b800c0300305c152089441e06205401860660515000c6004020f6181032080790030419498140302c958580040410350710105104403da60300f0000031881203801601000c11310309800f1080e0700906110a000241c130000b104c204441e0320000b01601d810ba401e0005000e4100c00f50003c1d000030441c4103000141e8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 549900143 1250 549898893 549898897
    0x305070e041a04110a140906031302041e0507120e1c0513060509010908010c080703150803070506060a060804050a0b040602160c0f0504090c05090c19020c09100302030a03030c030e0d05 81
    0x4040f940c0c0307400c2e80c0041c01d418206a400347d20302ca10381c4a101000401c8010303498104030728401e1b102400c0401c4114500400720f820312240a5940071840c1c07a07004114840b0b500404008503401501800c010f5000d114a019580d185c0381c1c548a01181c2034030041140050040c810b42c1c2160300c0c103a0601d1119a112078004255403c0101e0784d40c045160044081000c0d1410f0007a811444025910314560750f480340400c9002e402040444034140c2403228003c52140b000f4402010714034041c4005202d94140b180911102042ca68000020401c00d04e05000000d0408640550055000754120708161114107010009214441d9101911a0701c0c00d4164200420900002c00b207070354000344039100350307039a03028442501d40c900802025502c0c07841e01844036160800c440c0e80c01c502e01a140c60300380807895000c000b0000030b1441d0100543c2c04200038038001d180a40d50305030f00110000c6c84680b01480e540c0400c0c1e641da1040c000a0602d5250300c103076150648650300249907071007918121080072051203070291503a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 549901393 1250 549900143 549900157
    0x9030a02030d03060f0e0f0a05101517010906061d0a0f080f0d0206091018080a08011404061a07052107060b0a0303140f04050604090507030b010305070e041a0411 71
    0x4000b10344400100c80d030030706c8032040c443c554642c0501e00c03030303511b0745465030051034010080442c1c61800d000200c2c40c54050491038205100f0364a544220007103441001d4119041644503000841c02c00509000595100c078a503003146905400344841d250090b000910918050340080c1d41c5040238580004464000041403032582d422001a1f130500c00040000700e813144012140c2004903400a1031354982110b1a502c0080d030a240300a0107400e245590f9995040355022072046800101b411006004820b51325a80a4250600300c0b020441540350400da9500801803c0141e50007200c0896075105204040c4000000500f400600808481c005003005503c0c1e0020f079016502c4503d010460516402c1480c480815a81c250b04d0344c07a04001d40c0e44c130001c0598454110b40c042d541d800c0c00000b07020f460341c1d805031000d0300c0c44140106140c500075400400322070324009001d04050610f4140b00520303802860480070518107640110781000c3c0c1a1400e4400d041d0030b5400e40e04a450008641c2000d00d0120190600f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 549902643 1250 549901393 549901409
    0x1504020906031b06070f1a060a0803070b01030f140d03020c070602061b0309070f03050703031106070c110f1302030103050105070f051c0f0f060303180e040809030a02030d0306 77
    0x320792100c80c10705a4a061040d5000701180101056241c2d5207000b1015050701803145d4488000700030703540e0717a10300031170b01a001d41d428601400003070007850301d03004400300003030f00081004500b44803140c3c5500b400d18806200c080d11450505030b0b00703800c1c0031241a520002c0003a0400707c1d0000c1112440040007540314550264550040c514041001440420707164014114003100c80c00d2509001c03132040041d4405030800c0c02920400000281e001000041da10041d8055001351074070380c1c9103040140c01050810303d01d01e0b813030b00990200041603402405110340f003500002e00d5007000c40c0c03d0380443c040d4004081055401528241e0310810034200350003c0d8140c0b031044009100e9900e48400503640c00f01400d20f8030f40400ca052000c586003c80210804000901c81040440d410009542403000c0b12901100f85010a441c0c840c2441859000f420001400300401c0c40803031040c2c0780a420015880d0040e000074880e01001804c010a55010445c0d04103003500141520b446200740d001c0500180074910035001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 549903893 1250 549902643 549902659
    0x90305010e071806050303030a1d060c0d060b030f160e0414160c050a08030405150106030e0607050903151f0e010612050f040210020a0c0f08061f0b0a0908150402 71
    0xf003035446034010882111405030042d030031501d414200c1009091040c1d24141d00158410700340a808004000b040d014002084066940300c0c500840e10041d200c9030380045072041020401d003d07101d8000345540d41c0c06841c880d01c540c002d2080103011100076401c6880681d20500701025848040316201e2050b000c0e8070903007a40c040345102ea1300b0544a900840f5030190441c1c02070b50344140480c3c02c64001b0341d0300ca88101e0580d501c42000c0743c20820509030a070460b00c00203580e4441c0491019040081c1c54010080d405d1a03411302d0b201800203540c8290300c03000f66501134003420100b41078181c0134200c800c240d20403600039114281c8034901070040c0ea10074800c07000014107640c21202c400e040d62090a02407030043c5003005403941c0325001c1c00010b1403605002c8085100f580d070110080b540000303190001e065000402d02e80b03031380b8003a002ca03e04000034007401000c00c1441107040000503070718030000c100c43c0c0c010700d071949804002000f91a1101b03164885140c900941039080604002c00a07642c2c800c910881e5480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 549905143 1250 549903893 549903929
    0x613060b0a091e0b1606232a0f0d02031e10060503010e040510050a150e06061e0d090f120e03060a05130c0e010608090307030806010f090305010e07 65
    0x203e40071440d011038802c200b01ca2809204400a10008002c0b5105440180c404030b2101d80c0d844c012503003c08606040c4070440c0600040b104468507069400501c200c040034003e0150ba0030600048015006281c881100050b4454094403030500756003036030380d582100f19101d240100c0722001c064200040007030b107003a07800c3c0012440308105451209940d030598072907086a081c4840178049070760240c800d903003a104140741010810342600900d480360f500180046040104500300d02c0d0308003045e03006a2482000e207810011140c461100390340d00311509050705800e8500000d00c107001403203585c0e61640c1c1142009070741c2e0244800441c100003602e1040d400c149200300701c5035080310850010481c09606402c1000414204140c0342c00058111000c0d00c0e29541502083d41e40725412849507101504d141010401044082d070092403051344442844099440c0c00d5160740c004000d14401441241840051a4000c240178410241c0b0006550b11070002c0200001d035400f0260f9400082c450120500d220180c10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 549906393 1250 549905143 549905159
    0x51903051204060918020c0a0f0203010c021b0405071e080103050c0904030f030903021f060e070507030507170409090b06040f0b01050412060f15060216050a0605030613060b0a09 78
    0x1c0b0101e44855480d8480700d800c2054000040c1160616010300c540c09200c40c02e40c0b800300f03002044002d48101e045c0f5015542901c107050070740b00510910801e5400421b01d501601c5600154a041e1705011640081c25a540d00410748442d1044030750a040c4a0003051000c041940144000381624007800480b20106c03d51401c0015000084400400044440030004400d43c0240c02a081c950304c03a00558034560440503085034403440081080c031560751078220410004138952480c0e90000c1e000e20b4494680f003c2030b113001d403151280e448010035119924900c0761200d9840020341c0c002c0c141c030050a11050101d810b040e409444151107141c840c80c40d00303d0b40720003107030580700c1d0598901040c0c446605107843c0c80b0744030503824540002503039015101d4844503590500b03403144134003481284882842803801c0c548000e00d0301c142c0d9240451020f010603000d2080e80e646100207821503249103401a82c907581da00104255000001544011500300807001ca58085d01902409a2007599558041c00c1d070354a90310 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 549907643 1250 549906393 549906397
    0x803100806010612020d140907030309050a06080402120109060c2a2004020f0f0a0909020708030610020312042307180e0a140a02010e0d0203150702070519030512 71
    0x35a5012602130030314040c442e03034140c005e440b00070a083c2c000035085142860700d204100c0f041350b054440e81c2010f0b42c01d0041607006000c00025050586005800a040c050083c100c62801fa1019101d1140120201c5c0111800d400c6035441d244c0c42241131050031110740d0003901c0221100020440400464600c2010120f44203a071050140c0000100407405140306401d40010840c1c000180c00c16000c001034221212804001d00e8400c0340c10b04038994a41d403610000303007c2e8034030341c12480e20603004220b44004600070000f640c3e08034030200d8032240c100078108000d0f8618850b0f2928200340c0c1042c0020003062001d46444e4401104604401107007041c2503450241d114403103030044600301d240401c064000c90080360300002c8180140f004480b00099103454014840480b490309410a1b03000c0d030150411540e103e06103048401081d11401c4482d219540080d0b101c0c1b4050f1084001c2481541c000f80d500c902c00c12207600182405040300111b251110104846904213000c2a0f48038403540c2c60340c3c6101240101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 549908893 1250 549907643 549907649
    0x1005030f0c040f06030503030c2d04031b050405040b090705041404230703080c012712091206020d0e03030108060c030403030609020d0f0c030c0e1c050a080310080601 73
    0x10240a00c00300d28001c100c003c0c4041c15500701050354914001c00081c1c1d040009501900e100c5110f81d0719508210030f458058800e100900f19100c00c52002c40300c04d6854a001d65040d29400480d01c17500c42800c2001ea0b02000300c070303030005510900300800d10080c002d0b01e0b00c06d00d002c0d00791001980d1000c0d80f01d505000541c3c4200c620f001a4010310000034003c07030840003aa1926902191002010310741124000d0715014154000b44c034400f0b80040c52a00d851b02c24811250141e0b9401c800c200c103410340d0b1004c0054883c101030f019202c24001da000710201c40c42580602c0c00303030919081c2e14142c1069030420000940280c401041054505030400305820000026a4100c2d190100140f0380c0f070303844034480041500050030032014141c5032100030540c1100c5001619030306003800360020300301a0f09070100381078030791224019007414984001c1d902e40030b90081250160b0740050703400210b0400945048060981c508030058043d00400ba0701d1810400310b00e0056002ea081860b080c0c42803500e58410301d40724003083c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 549910143 1250 549908893 549908923
    0x1303140f030306010c08030a020405030109150509072d0504021b19050601060c08070803040b0925171c0f140301060c021512040305030a0c080609130503070f0605100503 74
    0x2000313940011b10800029640000130500160410303a031200441c3c01c1d502042d20490380348001d0f4200c3c0d990800c2c04c1c0f01d03c5901c079103100c2c018442185000e0b041103030043c0740f01c03400e003048406185c801d200380800c0b105200102000f520071560f94840204241900c00108680032280c014900b20004010200254116494000c0e0140400380d20340101030f03c0b040c00146040710103207000e000d00400f1405200241d40f15a025080c03001041c40c00740195402c29030302a40c0900480c064a0a0f150719078030368074401007564040150034502490343c01d00207182c240c25000101960360a0002d40d0fa23855441040c0c030240020a86a00840200c4801640500c1c0000d00800c030002c0c1494082d04094a00348101340304d4011004181d51500c090300e210411200d0b0111402e50224100105110032030182d841260740c0c0144a00d048100390401c2c800142d0542c0c0007a2045040c200c00c213000c0c02c10321805104440082d64408142c8540070b00c0c07031504030003501c801c44900d0281212080c0014480c2408250108014041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 549911393 1250 549910143 549910157
    0x8180c1503041506080d080601030507080f1801020d0605090106020a050a030f030e16030b07050408070510020106080f010e0c090c0324060705030c0f07061b03051303140f03030601 79
    0x40040e035241500010801d55548400c042103280c80c01c1c4a01c503410140c108040070340300703000fa45a00130f000c0b0303640540440d040500e00010008516400903c40790098420f030039412080d00c0d420038905142d130a6011240c02944001200005074030241c0c07003002110300a98000c81d40360b82ea40341c21f9840740e800d41809411604807418160000b0312402d11070484800794100060300319180560180b078001c4070b440d0800f4640d131070354080c41404026040c0b01e5104104c0c4c944a4905800c01400c56110381c0507200d00350150b40420b0300c484545000b9049480a80b452104891403040e075207a00b030f4080e000e03e8031142c0e071f14010302028500a0030500c16280c4244c0c41c50445610750b07111023001c42c2d81186179080d041900300c00001900034075500d0000803d841c40c0280019500c804a00c148241400c0c503024040700a0381c0840010800c260304000c0420306625034103c800904407403420700307940ba84190520518258074818003c81040810a203010707811440e1000c940c103500d82d11181650341e00c02502c0084c00704800c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 549912643 1250 549911393 549911419
    0x180f1205090a06110c1e09361c0c1103190f03080a021e0f0d020a0801031103011a010c020f0a061809090b01150201180803010e0a0c0e0f010c0501050c070b0f0c0306060a0e1008180c 79
    0xf5048900754003006811110a5103241000800090dc009030855040c100644a1340906a001e503d2941003440b2000840c80c121054200d104e00740d180c002c40d20300d01e82001c1580e07968501c0b032106a03103034a124900305564a42041034018101d00007400102c80c0c1c01111b04907449582014030540c0c0910059061500710201c10074015220801022001c9038048200084c841443d1900d036100300c001e043d1520b60305020001d051036140f07404600e0b0042c042041c609124903001c1143d00c41280d045035404045045d81800001c0e0072409000b25440c0c3e01c0d0340000d21660402003041c4000214100c0c3c400b1441202e254685100403000c0d5035078000050006812034100900780c1c070300901c0e81d0142a005051000d44016a55a01405c1d11011989500d42002c0840d0010030b0280405030581e00060418400181d4542200c484103a4080609107038090400400c9850b000e0380200a0030b941c1f840d00a180511821840340000c1c1204001c03034400394018080c0f0006862610b001640000c00d14008048140c0340c05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 549913893 1250 549912643 549912653
    0x12021e030703030e120d0f0f11030306040b0d051b011e020d053405070b070b0c0304020607060e060703180f1205090a06110c1e09361c0c 60
    0x40f080e00c00b0390090480c541e00d00d006008114100c5680c03170790340fa0411f07030b00c1510601500500b000361360341040c8481401030780c14207a80071046980c0408101c90001d00c441385600452680904800003c2031442040e0004e124103101061a0300a403400340d0f90084550081c456642d815400000000c015a02803c010b0800314001c401a100641800c0f0070701403040c1c00001c1c002c036180c00d10310b2030680c500d034035180b044140306e002c0c04000050a00b1742540c0b45000215520408503100c010007020750840003002240440d130710300040790801c41c1c1041050044501c03044100d516240180c4000021915009803002008140030010603610b8200341d0308000364416031030710502980b800f40c1110403c0410441c6140c15520441c0380f102400c00c40e035500003e800c0c44e0688600e000c0a00c6042482844100860b07000c14000a04542c4444025942c2000340d03100e004500654841d40f01100566000e100d030125203925400c0c0c680c404964018045a080601003241c0511000052101200162410b1445400f01d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 549915143 1250 549913893 549913907
    0x203030706050a0b032b031521080304032705030a020603130204140123060d0c0905100c110a0e040b0417120405010e070b09040b0609040612021e03070303 68
    0x141c83d82ca02142d00040c10001a04101c1c641402c040441c03204559407640c00340d286034080e001d180604080100840358060610711411600c9800441d03c10090000305009000c50942181d0790f01031012512424149400f400b003140c11070f894180d505030402d001198071003ea19582c11030703e026014041045254091124030350000f4081401a54401844d80060b140c912030340d0203e001c526004178665040c4000000c1b450300c01d441e0203480303074500b0321000141d5607080100d445000b251070340000e6104c001c0700242c0b0150315540c48a039202d00380304900031400da00420f40c15000d5209902d101240f22954041001e03c7c80e140c000d48100c2d01c07444000400041040c10b080c1e80050040051501243c8400410300302d681c0420710000f0814036520503c030801600b40152411500400e015010345824800156018000c8601c414811a2140c0b403002d00b503103a03201202e6221170b0241c8103024588c1ca0f030a641451008a44e0201c0c080c2c0010b02e808800c0b40300806a518a00308001c024181440c595241250782c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 549916393 1250 549915143 549915151
    0xb1b0f040e0603070b0a0e1801030302010c0206131208041a010605030702070909050709021b0307061d0d2f010f02070c0e0c070f02040b0301050406050f01060c020306010b180a0801090506060d020303070605 90
    0x8000040014114a40300101c220700031480b0f81c0c000301f01885480390043410500082d03c40d101d5801c003400c03503c0000d0b1041e08880340081403807500101c0750303550f070030a2a000c0340260b06030203501c00e20030b001140290b407003801036104484075022107405039905c02024045899401c4041d0264100b5001401180803e4008107020165060b5803501010f0040c0301c1811948a030404a9105030f80c3c4100d98070041c98500d107480300b000800c0103031444606400015050b171014100c4649051040c01030009840500345542010b850904020803400c2e4a805012000358030400c001c6e52440151800001c880c070400d01d0091117008000501402c04402d6a11581c42d00d08541040340d100e901c40065140c0360b202481000e02c07541c0a003c02103080e003401c039102c401404040e04140c0c00c2280100700107025842c00107440341120201142d440d515440754141c007034928040c50145501045c00b0400050102d415041090503070301500984911391200c10400c43e85945851000350550800d02c9480c0214080d58402540 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 549917643 1250 549916393 549916399
    0x9020304080f040623040509182503021305062b1a10050906032a060403150c09060903030305090a08130311030309010801030b1b0f040e0603070b0a0e 66
    0xc000d0040d00c80005504160030080c005403440144c00000000758100c81041d0585d82d0f4000c2c03a080c101008204040f10091080000340c42a5031102200c5504000ca08900c2c0d1540b00700305000c2c507000365410f40c00c0c005803005a119042069040710700b040c0c18828180205030060050900714060701d2403100d00c58440380c44001c0c001800d41d40402265403003c41a1907010301403103031015440c080c00314402000d001c0d04850b00494005040101c2918002540e400020104004e040c6010f038441481e040f001a03400c0164010700c0211b80007003040f05600217030455040e84001400003851562003110300102c94415030000a9084008201080c003076802160132240000603103104000544032050158089542703035007101c000c00010002c0c0f105a1290a400c10300c100c003c1d40c03400d0040340000780548010f000142240d5880004500000c01d100401481c04806500d002d8841c1e440c80004a101d41051090a141a50000004005d03180c08588041a9080e00e1a5982084485c080490309c5e150404803240e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 549918893 1250 549917643 549917647
    0x60319030c0c060c02031006051311070819021c080a0c03020904060b0c010e010504081e070b0a1d03090a030303180507291602090a1e1517070902030408 67
    0x440c80c00c0b602e00d0040c0891340c98081030300b00e0b540305051410a807034090b25825458014180144da0700c080108036130300052040428201c420b100320b400f1078401c0c024020140c4100203103d41d030300001c0350b02e204070400075a000c3d1211090300b254900c00c803840e02c02c145000290200d0005001c00582d40c004841214540750040c20000002c0c0843c00702c900c25041007040510100c1d80700300040090064080700d0341400c1c02071009003800e0303554035518040c032091a0304000c20041e1021084110034255440d0b550020780340300c458100007000030010300d41e000c0102254803060254004055001080701c0031903502808039130b030365850340d00c04400610f4440000c100e805440c1c8102e0020400811801015201c0d16100c1910608416054035220800102480e8060024490251112000941d80d40c0b2950191aa000386958880c4401c0050481d00e80078100140038504526030b000083d4004c51180d95609100101d41d6100c000245158002021441ca00d5102003403d1103845003540295800910803a1068 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 549920143 1250 549918893 549918917
    0x60f090501090f0501050a11090f010e1302040509060109030b13050c0d06050f0a0c051806071e0b07030b2d040203010303020f06150901150e09070f03050f06031903 72
    0xc0c00e5961540b030079540d20034401403100a02c90284074458006117803410401490100510140c03143c00341564880c801d60404a200315540d01030119018404070044c8000564070406e00100000d41060248070301900100e000540d595006110400075a90096807003c281c0c1d66416643d4015100f200c0115680d0042134540040e42c0c984003a10305480340b0818000c105450203404103949400000d00c032a901c54204a140030031150880c04030b42074540460344900da0390103400701040c080d108040700106481c00500f0407009080c240108041058031859a0316010380b6801d8040b400d43e1114481c031035105601b9070809820410fa28040030300c2c45000005c0386071201003000010100c0e002648150300bd41c00080e1080e41e480000e200c09c5a20200c10b0000660026043c03010441c1c2c0c00050013208030f001d21340b401035015070307019141d41d400924004000d0704007450400c000400e50b41a03810280082814080803a0301c4035840c00b041c0b131154001800070841240d0741046124844842c071030960620104070f45075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 549921393 1250 549920143 549920153
    0x904020a051003140604052802040f030807120806060f0c07030f050c010206180703060c0201020706110405010207090504080a0e130c030902120f1c17150414070c060f09 74
    0x5500140b41518000b841018040e2110701650000709a1172096140c2410441d40d0582202d508035403d102c542d04103510121981c0d490024841d54004603104000c40d0400001c1120202c018a140740c071503c07850b24419141c02041e0749001c0140c98003540510b05000c0b607040210075401a0909441300e00440300155a03d46503900d6842a13000103480c03607000840004042d580410600d50044c10082e858096802161507032030b00c811080c00020100ca8030f030040700807224404d4068800700ca800c0305082124082003001e40301b43c0e90107849111f016000d01803000074803403500d1290611036a0041080d520b00280310404071003050610710f01507440610203803102d807031050900c180d100c4060181c400294441c654010880724080103040034a440c0c3c81104507001c10b00010a10300e4240104a040c1c01d030701008c40e60140e5000107141c000e280b40d500ca1100b000294034210524410005060700c1c2000a0907a1103002c0c80d001c18126844408120800344807800103030079612034280329018000c0001c034400300ea07541c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 549922643 1250 549921393 549921409
    0x512070e010216090e06130b060d06062111120c102102040906150237031709010204080616090b0c210301050a031e0c0e0114030303060105090904020a05 67
    0x1c080c480e9417901403c8066004128039500300e0740305410402010000c2d035442001e0640148464041c0007501000020403199400c1880600700351b070b032182c110300d16021000803041d41520701620f40f4010044038031450b080c00d41042c0d030a40f900f1000303011031404075414803d80340591050074040002540d00c1d4100b83c00d0034400818002c120000c050382da149810b42400c280c1d01c01d50031550300241401030300c0c0303401c035000035a1a16002e8500d450703042c041c5c00301441000c001c6004102d41540341000c043d000415601c04c60103c2045c56907200c1d0034040c0c0f00c035104107080380511702410204d40d00800100721200300c1c9000303004503851075261161000da01c5450300740c460b81007100c00e145c9662000320b000c4100342130040c104c2800020305040b5030841d0300d05000a840c4030080c0c80090040d41c031101e141801000340d0480e882400340c210303000ba00c07415583c9044410003102403042004400c60603000d1031061402200b240e006142c140c0d5907504003804002002020f44000e4000c83c1e02c00d0304250001444d8480040c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 549923893 1250 549922643 549922649
    0x1d011d0a031a09010c1e031d0c040e070b0a050c101103150103090b0a020c0a021c0201020d1d040f021c021317030d020a0c0b0f0a06060512070e010216 66
    0x400d070720b002600440e42a0007684082c1000480e41d0520070400c8100d42d1001075042006090402060040b0325940d080d030041c4004ca1444600b404182d9402815200010708402001826182009a0b222012082c3c0d00c4286601840c0c40040c070400c20944020312070005000c02c0c1c640942910800d06546014204480010f2240032503440f0100c1040200d0100034412200c3c08000e08091040c00d03004d69503c0c24145008010203081d5602041c101e03607208040010704041980540b400343e10410040d021115000e600070224014419010013819151082036500f41406400d190f0300b0076442000100006032010251150982d40d0a0050f6043c00e411070342c0100c0d0b0748100480041e560813080d51120b10740c05142d00000003040f40a140d401c4500301c00021101d080d1444440181c41c1d807a11300d400c441c510004030020b0581c400c824148480510341301c1c00c20b80500218681007104a954040640301c038013400c00151072030142d8400281d200c901444641c40750000520580b000704076400403840c07140550390 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 549925143 1250 549923893 549923903
    0x309010c0c080f060a05070206280204030f20011803020f0d120f08060402040b220806010303020709050a09051b130c050d0b0411070f0215281d011d0a03 67
    0x190034440010080d01c5015000021232020300614a0111314941102c041044d201c459000070780c188002c4d038644d80d819140915804010030f11180c1460500404443c82c441c0003840c820840c1c0040150766010b141e541401031544078061450f103286808210013517400300d03541c640041c1541a0000020039581802107105026203641c03250f900644801800c1d030200a088500480c8100010710102a129043d00c9d400c42100c440003003a0529821442c80c08a0990703c040c2c464811030001108058001c5040425141018810065992441150300903134a91940140c0503401c4914010041d0141071740c0100901c902424000c0c8482d1140d0690084844414030f800005d136000c1421a000300d624080e503c1800022503007400b0800380800c02c9600b03841420401070103800e00000300310854403101ca220784c49020052400c2d403140d03285400800310903c0300d03880c41401139110703080c001c40500a645110550090b00c590108464000c401941e808002c5c1d41d0060460081781d052000c19541c05210303801542c4a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 549926393 1250 549925143 549925153
    0x80406090c0b2712070e1503010903021c05070807020f120d0c0201080f2203030e0307200d05060117193503190f0f0203270309010c0c080f 61
    0x324005440740250415030702ca04c030303010001a00c480000595005844034010f280c00c198032464009103c060341ca001203071b059400d018900b014140c0229160071428078858544003042099042240d062203a010700500700c078400c1c00698050b040c4000740c0c1e03041130805407000c000d07100404140703464500c0c05255800040c1000400d001156800141c0750381114000d107803003000d03051110b4000900d0b0504600c1209a031041c8500300c092505c683c00014100e0107810a9035a1a41541028040001032196004080001d141d600e40d4504240b02417028054004010704400d900f002c40d20101140c201070200d009201350704080702150104910350f000c052190b20209924115a010b182e42404070b0036500e02a0b801c0803e2101c0d000c0721403001c49902c0b5070303001d0600c44943c0500c00154006d11348044480c0840d80340c807a40740e80c00099940210701651003020401e01001d4030301c45d032240303c0c403202041c02229001841a03840325401202e82c0707544a07105994a181298407176000c10314103503c85500e90038540c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 549927643 1250 549926393 549926437
    0x51e010506030c090f0723030c0301060801050f130518100207060b0303030f01140105070605151903080909040f0803160e01030603261e041e06080406090c0b 69
    0x704000f0f040c0480c0043d901c101042ca8004401e45210030014104c41c240b05482c81c50021000001d5041ca2208801040701c0c2c0d02c03410310191007003203078100340140004a20110004038142c6400c0d00e00d0160080001d140c1e895089048020744090700700900702181300c90240d101c5219800d4180900d01521211100040e00c403c814108041500d4210301c0c0c05000f40c00c00c00c1440281000c4284081c15144194045020541d0440c01203541d44100d04000c0d000d10324100c00d1083e1010030b50380c0031034499001c498005400701d09162115041c24a480010801c440c2000340b80541d041c160350081d40240a4075035a01880e0b031940f92410190f05c00c4403602c0c429030440041c00707400d42e00024817204602007840d0800c41141986c1c1c1d50701800c910125403401180c1840e034084181c070880030407640c54030400602e518403064202100711142c0c000d030040e00071032182852070a48220005031100d0880d14150341d040c42c5a00d650702c4d0b440052030208407e070b4489070245004240c80744d090004049420840a1003007280403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 549928893 1250 549927643 549927649
    0xf0304140a050d051209010e040c0c1401020316030e0a050a03020a03230304150b1009060201051503060408071704060e1309030e270a0c02070f0302011b051e010506 72
    0x400358000a00c07503c100c4106501240c2c0c00202d5058003070301001d0450340c070803040b40140c40151101c000340707502c14102018100303200c0d0b01210441c03410b4030683c0700244481d150070b01d0600381d0104440e0b00116080320402c42c00c009201b5003000b83c7e500030300810360781001203649a460401e15082c20176000351344186540401c0541c810b50f1820858500800f4840c4410400d113078036401d100143c00034055500211248030000920b40c02006020401400c40f0942d03140090f001d000c280c003601c43c080240d403074000094030010030342131128104540100903282c95980c90b501d81110b90816407095401e0550701c502800c2d4040040e0040020703000300e441d0b101c4001402000c00c000c0c1148840003800003800c0800e8040001c2e0007514100c540c1000303c3d868400c60480d048032800d0281c1e0000e800300f45112420501c9a030760b68580c4104440c00180e0b0035130340703400e459120b81030f00741e0301a100003800a01100c49000e100c0c0304000c0c9404215108109072440100004231400d1006007860100c2c0c02e5941d12803d01036145 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 549930143 1250 549928893 549928909
    0x109030b15120a020d1220060118020408070302010503090f03040602010204090615080420041404050f07060e240a0207061b0b0610050c030304150507080c0316020f030414 75
    0x140c0309800403e40003002d40d011804441c9190001095084d1000d84020024040c3d00d05040d00b0040c81c02e0340310310801c1045040d6589200384604255025124030400550006008460a40700741100800420340b541c0d00441d001ea02c018007114030b6008ac3d6424640402081c80208028141940096202ca007000701c80c004a41103948030701000d00f1464406503100e9002089103134010b0300480e00c44013034001c0401440c0b8611089064903841407507c60710b00d140511300d128260041c1c1c0954112070300c08010400302565030314140645001300d1807a04813400301e840c0140b082108045100310781e4040803c2184003048030f8000c03002400c00350300b11030401d0080c260f10003c080200003a030116160001c3c400c1e2180d201c080c4016024034014114070940002d02c43c01007044031001d5200000b12592464141050100c01401d008032a14840c180b0000c100074038482e54549020729407a000d030b9491070703d44180202818102c1142d03e410360091811281204e801440a0300c0140441910214846981c0d030400c0105 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 549931393 1250 549930143 549930169
    0x140f12120325030c1d120a031709032703101a040f06060507140304080312040606060203040b030c1b0706030e0f120f030901090f06090210031103060f0109030b15 71
    0x40c03808841e51140769110205e070502d982c444404110003911880400c0c0e45990300d102e960014480c001c2d6410416038000020b0082c4c00200e455540c041e1221000ba030b480744204014803030303c1240e0314402c061400e928550041d40c0d1380f00804484118200000c1d650944521802040390b03008100c14a010908140c0640d0010742c078010000c00030300e41040e030050103030300a40001030143c00010751003d0b02584100104d6000c0d0014400b100d0301c400100070600c42c410000c80e0100d0b02503090400000c0c041c0e00010a4078240e44401c03100d5821940c0b948000030309a0403031340c080303410001e60090002c0080000c0c4038a038060052035601064030714811b101d0b13904c1c120309440307180c10b00d5210888082e0304282c002c2c10388500c80d141340c2065603651603406003607001d404006c102404044152980c101041042c0c0e2240a005100ba0782c0c10200400c031030019030841d0740350900302c02503140410005440b49427000e2003007508d8205041c515940d0b510703600e5444903100101c079090040c1d01d002240000d0340c90131081000d01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 549932643 1250 549931393 549931397
    0x60705030c070605010b0904140108120c0f03032a0c030306042d0c030c0e0f090c040b160c2102040b0103020408120d05010f061215080a030c020a140f12120325 70
    0x219450f00c20b01903521000780040e000d80f82c400ac260340f84441c809004014ec14050401100d17100d05114599201002148191032007540101c440358520151a909541d12051444041c1d81582e481001f480040c060030b40e010100010307800d001505245095403201a01c222543d0002038081c0c028a001d8116808041a0001d00a54210303000d9180d590b0001d69610500942d498080c0d82c64000c0350301d1040c0201c1d0007076400c0e80c6000c42c104515520404d48030b203081e8028821424000c0e59450300c1d084841d01e010201004000c4035001c04090704040e00510706030403062400614181e5101c1096007082d800806010a08100240081c19016580a0309014101200c83d6085c090700e4404094508001480312452807629801e000c90701c80c500000c1580188006025034502c420700b4900149510240401240305650307201002c200301a8540101d22038030005441030745880520800c028403411084400b181c2071080c240400f213440c0c0c1c080080c50081607588007490034201c070114440c0c0082601d1011800b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 549933893 1250 549932643 549932681
    0x14060405060301090b06040e13031701140f01020c0d030302130501030b031f0912050d0f1b0c0c0909120e0d02060304060902120106060e010909020c060705030c070605010b0904 77
    0x211540d180c00803281194080c0d000055641030107000700d07051f8012a408211140052401c100003821034400c1800d082d84669200d06254214142c0149003560a000710f500b00340700000c4d4181c06051030026208500710500464203418841d5000491a08409800b1000a074000c22100305190103508014003828003400d040c4500404000403a43d6601020360741c0e51420040300e0840c4810803282d100f49641c1e42c1004400c180c1c3d54280720040c00d190f014445080700c4d1881c2c05d4001284200314031550809801a00c1208080c0c1a016030031038004000e04001c0d10000da51080004098040744500780400780f1625115000940801001d048245038043e45801445480702d4040160f076107c0840390f1169205200240d0100c50f400032480c990034140c1560f16a41ca001b4001c200b1b0341c0c10680411051a007607036480601030300c41d0814400d0313003d034001c6503041d0350000020400e080d000d040a554454401e84406007002c66a0701c2d900260b400a901c0f100c003540c000201c81c2850b082c1400385910b20b5400b4600c0039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 549935143 1250 549933893 549933899
    0x70e090c2103070b28090218010f0501030207060b0a080a0314031909230606040e071203031806060605030130030e031006080c0f031b151b0601140604 66
    0x42e842e4410303258024500c0520f400040c14402c82c601241e1130200c80c000314419090010030302c03000184680ca400b41d1240340031311583c1e02d090b0511400e07581070f50a0750041f64416881c0c000158080c0d003103074404aa2094446910710076603124899000002d060034002008000104d0030098006c0445c00302080b079a103c10003c2100d01817400c01d004084600050000421304640d007041c00c41803590b2500601408955442c24100000011303071540030b03400458041000c2e6040184450340d40885200d03881c5e441d061803009201203400ba030302407004a0703141920050603403000c0e6120421035445400050200e0004001400340700c20f8000010707140c0d43d1000700f04c801c106c1503d030000441e42514000a00308051343d022110710361002d100381c1902d4491804280030098881c048103071565898403540d40541e1a0000b41c407500d01d00028004601b4082220404101400c00c0c01c4c802201d0200710401680c041c1046079107100141d030381001c004800c10601a10480d410180d10190030300c55120040d20442040c0814 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 549936393 1250 549935143 549935209
    0x10f0e0708190b1008010509090d0c021009030803010f0905101202040b01050f0c100e0c0a090e03091002010509010f02190c0c03020901030309150801120f05070e090c 73
    0x41d90700641e8840c2091000c41c04045400d018000590455070040c0c140c0c890207090680000c0042e0690700100c60740d03c0903070340301c10745113540701c100c2d200480c00a0000054000582420400480010b00619021003e00d8581e2a0a100ca5100382e00c0161600c0e5038001c02c010f865000d01c40e860700203000d00302d00070815146c07000320603c456103800007178030480ea44c0e0000046a80a00110340c1011011810280c44a000032460350300c80007414020800c50741405121403103e003012031102400b101c010103042080c0c0c00c20351941c1c003c080402e810740d001c3c441042002400d5942d500507003080a03096002040500c2c10800d85802d65419400d852041801400b2004045112426200004009150852034003500e820104641b41480e40083d40010490001005266008040d84240d50142480480d02c05a00c8400c44101000744a03240c096900040c203000000d4200340036082c61400341c2c00701c40c80f01d52645c079280e00008051310000072076401400c00048500f440d58013488240c83c20440c1c8401c4200344c03690 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 549937643 1250 549936393 549936407
    0x3020109050111070509070509040e0d0c14070902030a090218010602060109020c1903091a1e03060607020a06020d1704170a02070b0304060b040608190813081203010f0e07 75
    0x268506102181c00c843c002c1c44820003c110013440010040708071802c01d01c1003d0304942c011480c0c0750185040481048204100003000250301035a5a01c41100c101d580c0c49400105100b20880300301c0340221480001c07580c05900266000342e070038030000501c3c0002c40c41044013114100460b1180d1003010801048220340110308a411614011b01c00340c0c0e01c0075101d42d0141400d40d40c00341031400380b02a540c800203140d0b100700300c2d100341c484210f58110a24075000391b96043d1f0062541950111a04a00b11400c866440b0003441d0440f80c0074051a040010b9540041c81c00c100a030443c40050707001d800b030085d03032a5106101c0010001c00800380011420a512502e0701e01021140ca0b404104002449140c40e920800a0900920401351030940300d05040c40c1210140011a150314411402c01d2000306205001041212000c00c4025142509404e00c3d620380340241c0101c0c07003d0843d03461800c0c0008040c00180b0211343d00244500a1940d298140b2003805c0003078036550013801500c0f2001082240c001e0300414 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 549938893 1250 549937643 549937649
    0x3010c020d1b0507030f060b0904050a080f0706051e01090b01120506210c0306071d010807110d02070302030f0a0c030308060a0b04080c10180909080c01110706050f0103020109 77
    0x500703111050414220401800b4900310018102c0c0318021002040c0301d90b01d0798545102d881808140881c18502d020054500016907002d00071380c01030594040000d02c500014544003454515850400a40361603220450300b04480302100104130300d20000d1254000c0c0c5855000d008242c0c81000300241b000002082150122281284240e07548080390655503111409141103020b40d091040d0000044919515201c10480745c43c0039208400c00310b03a18074003a80e2101c80c10116200e03061501084000119940e00c0082c0c85081070014181c80f8800c852803d00041a00780401d4000380303980c501c2c600c14545490303013540c1d00600d42d41040c0c080400191040350500100c03501340c900001075031110000100ca6404e0782d8405c44501100141c00a031050011850221004044a10600c0c0c0c2003841415140c400ca22003030413040c3c1f011501d040c003216182e07910100d540f50003541072078200151802e0715400c6510366500d226a13040040f40e041e04000117401880da2080d518440e590a5502d507070b0000e403015980740 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 549940143 1250 549938893 549938897
    0x40c05070b1015020a0c120210031521021302070b0c0a05093105010e060d0c05090a061a070f020108040f02102c090106140c1b0f03010c020d 62
    0x440481c2808180b0758045014003164003812510b204003803030103507442450f000b013210050f06140c070008600800012060285801a05000002c0380106c4100c0081201610745940310503e2000820034140d1a12a1491118054955903201003035004004071010381501544206004002d0500010041440700c3c0e0010011079009841d001c892101b03a4850040082190b080084110b01c0b44420740b00304421100290b50f11203c402c441400c45140c403d41d0000d010b046a501e10000c0440c01c0390074100c65581d81a0b008d03550390f884a5440d040041e41101d000d1324405003880c3c40341c405201c80914082c018a0030320700080c42a1030070403566528404403a8102d00130f4184401040010144071005030202c2000364010100e05074180c4010000d81064003031000c02400e11640c00c056500414100003603902c52800034801415a071030000100d07118010494040140c107030610000c4104d131410807072811102d411500c1e91040100700024000d0b18400007001c144240e050581070100590003003207d128098181c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 549941393 1250 549940143 549940163
    0x304030b060102490c03140d0510050103061d0115050f0a020f0d0f270305100e0c0901030803071404080703060e0105090f1c1404030302030d0b040c0507 67
    0x4000607800c200c1224070500b0305003840e49524090036400c2203000d804c585070442c2c0c1e1200c2294401e40840c2c04110321614004520350001e400046802044e428100034140d8440600c1c0031002004030058490689000d940031a114a05009960301809654040c000701d01100f1101c3c40e100c1120880408184240108014542c0e03414140178850801c40d0600c0240c480c1803640e6a8900400070f58401d01c1701480d0455009010004013114813403c0c100d82c0c078548a98950384598100004040d890b00214075151810a0b50200040060b070309120701c0c80c8182c804900043c5018200c0c00242c104007103440c0d4a4801c415280040c40002e80c83c80660760005105c0c0741c0340c00e200b1400104010035210303582203401d0300e105d01e2000204000568201640c030b41c840c60024401038884e80c00082d50780541d640b001d040e0380c01c400003500c4a0440792007a010f0400c480d01d001515515400c8420203140d100350000d50050300000b0300250500ca40d0f02038280300ca003003540c08200c41d1003190300040050145401c010018828 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 549942643 1250 549941393 549941401
    0x10050702090c181513090e15130209071d010f2a0203030d0213090902060f0307031506080402090f15010c05030d0c03091b05100e0d050a0813050307080304030b 70
    0x1440c80e540e06100800303000445042c809104c1c04031503400c0b02d400600b040a1602010603c0001c0380101c941a000800041011a08103000c007010014001d14102003000200d80e1103004d0390790040e01ea409440d264032500450aa100446403035003019950560501c054102101e10003a4015250448c0d001441e211029030078085040b210b00b07100040c4081e51601c80414403600031038056004081d540203500456070501d5680540c0c0050300c0a05c01c002c2d41c019000d010080301c0d07260490086901400900e070008250320a1000059610a241c00001c00203030140201300031402c041940f0390704142d1414610040e49800b00802c0c1e280c08042c603100d41045110340c40c035010003004205a1b82c550000d0442805544802d02c0010700900305140140c4003001006108034640882d60710900070340300050f0074076502040b49902615890424140c00e80c10004e00d5030f806011807000d000178040c041c032984085a4410703901c5006409013030550031503442034025201c00c004443c000011503046a80c021140d0400d41c1d9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 549943893 1250 549942643 549942667
    0x81003141519060f0503030d0203100e160e0105030f06010516051b010e0604082e0e100b010e030316170c07030606090504020f1306210210050702090c 66
    0xd100d001c00c20001c1d0346507003403100d6056040d0150003464810032040048583d2003e051030380d261144181901908100300040c81001180c00460b4010401501c1001056503607601645400f0202e4504049880103003260f0403c0b47d00450054403041c0c00d00e00075003107041441803840081805407200c0d040c0900020120460240700b0304020701517400070269840380303aa40c01002500030b08000ca090005c0c0f5109081e8165280c0001900d0542b10070340d00034807070b86004520880000043d000000d03800d4850008051a4000740e010703400b0040b440c0030203040648544c03150b000a440d2460f100742d0500a8800d010081790320004203451a030317000001090a00903050030031103441d5205d1580c0c00d81c40c074400600340002c0d000010b07101c800c030381c40740c4002c000e00c59551514104862040d50700035880250b01408545600d0700c1c0d00c5800e0ba101c0d0181c000038810b40c1d00c1901e6011440700e01194011100e500f40c0c5601585401240c05250b40b07501c1c2000780c40c111030381c0c0c001070a003400246910801200031840984201c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 549945143 1250 549943893 549943903
    0xc09090902210f0a030e0a08030310150c0c0306021c05060d020904060f06030305040303121823060106210501030530040303171f06050a14070614010608100314 70
    0xc8040c00586001080300d0900070103086c503650030b8074007c4c40502c200041c140c800208407403080d801030420450050500d600202c055000441c000104445c00100c0804508480030000c0211300c26a0010b1382e0300003100c040403036024521345121540d40382c8800c1000c1520b401a08052443d8100c6240c4126611480d0460042004640f00244903140080200800da007110051003540e0180e10340855491840e03401e2815203100b10310105e444042c0a529100050100c11007100300b250b09500380f1500c180603d02c00e440c00b0700980c4042c1c0050281d0020708200c40b00c001d8501c000c035107a148280520360658542540d80c0e07443d29684422080300040092000c0081e0785200c01c003000d01d80c1260f81c2c2d41c0c3d403410000c0c15108400300114004007807070041442c103940c6035410300d508003440440c209002d18040050710340da004219030300c09200200410390501c2c00d811008101961080200080c8203042200342210140141c0204090044000902c03030f90883c9410403000312940f280c004d180441c2280070300c030300744 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 549946393 1250 549945143 549945163
    0xf1c0c080703200703030b1c1e0f060f02090f0f030a1407150c1109070801050111070b160501050708010f0b0315030f07030314120a05070c150c0909090221 68
    0x840f401140302c0c01010390682006c85185402c50380d11003481c1c00d00514100b004941d110041a40c0760501680740c12064504265410a01407a01420240c03c651980c41c1900c1400710200303105503000078245058900102d004c1d440b41030540e20000340b0010900440d40c1c4121020f000340807200d0a0b081c20b86594002c0001c43c0261204100c5180e6030541c0b1f12020f85a1100c0d00c074203c448000d03040001c116401c0c4206078030305c2034090395100c14280c0d10303101c0155040c0c001851000d800b40120080469041c50450040c680e60307540488208500d080da00f01942140d901070800b404110401c2c00421507011042c00354003d58040e00005a43c0e51110640d4008014540450070380500402d03084106c070340b0000c140320089a020362152811203e43c0644186244100000503954007014004a2081d0390641c0c01194429030034204400840342d135881e0383da5040d8802c8800f00d0030f01e40721500f0240e1a58481c1e00714005140d125014090402d80c0c0d8000361018107100d040280003140b00d003405840c02020003c40301e107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 549947643 1250 549946393 549946451
    0xa020a090c021f15060323040b060904020f040608030909010819170d0c050c010608070501170a0e030403081b19031817070306060e060d0201140904020f1c0c080703 72
    0x1113950364103070140240c8890380c40705020681d642e292a0f007401c0e5030305942c0d203d25840350209106907116010400b41c220050000c4e40c1108202502100c282c6a03031044070f025200c1c140081d5142c032810760800c00c0e0146c2c140c210042a811103026a858102c1100f45110300c580d110405215890740c019020600d80549a0428101410510308082c2560080000c00d40a040308000748207654443d03c5c0103a03a4415445aa8002135900380c0c01d41a110311605403541090b9200400f007080c0b000c0303072406891a0010740054035a103000040b01c1100e06100201035040482140282100e076240080200c24111503c90282c01d120002c9043c6080011030700c400000741480b9404071010106403003d01d40d4402e03081c082190114507005021403014401505c4a01c01d48005100340303541c0400b507004540c0b014010054140082d0188844200da548034005800c0c0b1000e80400203458040050888000c0544003c20507855460700d510041401e91221229500544508002c030344900c00b4450314011301e4420b442601 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 549948893 1250 549947643 549947681
    0x60c070b040b07210b01030e071404020d11040306021209070b0301060f180f06020f06060a09020f1b010b1e100f1b0f03270e0601030b060c0a020a090c021f 68
    0x3481401340c0e80004100c68007a81c041095009a06110f59174003a14000d0500366011200c0d03002c007a00c0d00380c0003025240742143c80440da002d4103192074500b07074000b0340044540c1c64000c500480010f02928410307a00252a50042c001d661074113070068558070043c0203c000308000c0340102a85240582414241309180303901100b2031075503510034101048124040c02006000305402c081c03e401000862900844008095142d0f00d484e00e00c01400960102044644c2c6400a014080203038881c003002042c00103c02c000404e5400c1d011040009101160f904c207a0112116034a982d074a40760308803d0000c00b010360034101074070207000c142601c800b0080c030302c0841054034031742e14041005469114010b41e00e1080d219810b1007694144070301081200c0303400c0d20001b400b8a81041052025032400e550700b055060500003a8413982e1030225010ba8031690204c501b40c3d1011803000c00b1405c240400d0002454205000c0005604d0f07030710000e40387c59084607144d812820300700c055442000a980600c901c015007011100c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 549950143 1250 549948893 549948947
    0x3101707030308060607060e3405030705040b040b1e180103051005040615060201020d050c0901020d0c030513090507022e150b0a1205010f050d030f14040f0305060c070b040b07 77
    0x980014100c504089d141481c0e1038881580003625a81001a5507004029000c0c8030700300403e22000308510040c035a4002e40307450305a4065201d5208030506480c11107910702030804080705018001180c880400e403079003000030040000c036002080750380040e03014800c04155600d50b810024042c20b04006400f00680211000048680d015401451814402c1c2c0081c00282d555941d89400c0d8050342e03000b0313405a00300819a04076203103d4420010114481e080c69800d1615801c207581712030360181c1009080c02e0b078031000d01c1a01d580400200400c8035000344110f241e18404031044d0700d01c0c03480210b442d49a40c0c07034011003803003840e10300c5070b203c00f42180d101d0003a210032410304018071402014030428040c525081c008a1110300c050746900589801416143c0d0101c8a0f0703800712590381e4141355040401061000107a981e1090320006c000500900c50110611030540c2442c50600c100030f001401d030540200070b07800004002c02d180300d91040d007200d01d0807078695032a40165403004680d004901d0103d1174541503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 549951393 1250 549950143 549950173
    0x50a2003041202130902010804020d06020d0c0f1101091e050f01090f030f0c020307260a030306140f13050712020406080103140d0228060203101707030308060607060e 73
    0xb21602c40c000c903484d40c2c2d200010014202140c08480d00a400601440c000802505000060120040c4144401441e1007c02000541116110341c0740391b000400513042849650b42c450070210b10840c03000000c100c0b001c00b542d1056200000080c2c010340340c0401e0406041484010700c000c00085050340000e2001e03002d0f91030003090f0a4012501100420b8040040d20749242c490180c5200f050790160040400c01d040950002e04485c5c0e0700351120320080000d0503900321080034008041d01d6480390b28042200750511010840c02c048503000c05009840310059140b041c0d5440c264a038540c1e480d4400040e03a500c031201c088500c00f50368000d2400032800010b0000ea929230100260741281d008400403007030420400040c0740c45038080c41ca201e0069010a100c4600050492842c114880030300524243d440c0c0c3d40c0e507400c803e1341c2045070002c41c02c003000b0004001401c81c50503186148403210000c1c00342d0390f0171a9030140030b42ca40a00303400e0045030041402010800d0550003401c184680408485d44000c1107404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 549952643 1250 549951393 549951419
    0xe010e1b0f090f010e13030206070c140f0114010510050702131808030405010b01050705060f0c0d06080601150f0504031b181a121f0f0612051903050a200304 69
    0x34007000002000c000407204818200c2c86c01001da81903001d0b21490b1115402140c100c400c110f000e5a0b0090804070040e01d00d1000c10410841003010342c00840c8011107121101043c00059000300d0003980854aa4420390b9403080c1101c5c1850390484040710b88600d1003440740c000300245403408030034505410300082813001020255110b688030707030005d00c98000e18100440b10303030082c0b100003801640b101c4041a500109030f041f455020b480307402140c2c181196881e1071016a00c00e80d201c071030503030000c038014800a000038130000c080e040c09091070280e21418000c01441840381d4803024101c05100005001c00490100303480005000f1405251600f0b0080c0074000c00904001046000700c8802008100c0d0604041c12100003468150011300030210078881070700d0b0078104040280c4c00490b0b48503c05080444544038000241214043c2400b40004070300d4020318108140d0000104e501000c1c0740000042c0c0d01c034044901d007201920b0059009048050b41c2c0c124000c0c4000c0d441454040428007180c940c6c05501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 549953893 1250 549952643 549952649
    0x408100507090b0313050f03131703030426040302060a050405040b01031103190e0102130810050f0a0f0921091d0a0b0307081c030e010e1b0f090f01 65
    0x4082089890301070060320700c0b8003148580854500e0910000313103620704207000c00c2030707090150081c0ca0a02820381112411070b0b1000307640940481c01240c1c244441e01142c66001c44071000c4600a62135410503032070300c006a210301404050031007041404403099041d03d4007942c1c000e55015042d00d44032651228007a041d83c215026240c051840c00c484485558882d0098882981403500c4052654035050b400e40303a040043d0001d616003d4484801c040629400d00c010030403820110880c2c1c042c5403c1002045c10401c01d0107401c00b80354241b0701444110340400c11015044008404d0000b90310803c05c0382803000e841e200101030040101000e0b40200008191042e0f00d40c0718031540c0d01c201c01c03a201e04080741ca03025a0801d200c2c040d40340c0e01c005100c10010f076103c1c40340b40700c00400b1148299501e41d14145400101111080000c56030700542a000e50107020350011068a07000900514158500349690346035410b030380d211000e13004061841240c440c50441c005003440070308806603903d810000c0c0c44010400784 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 549955143 1250 549953893 549953923
    0x2a0a080a02070311030624030309061602090f04030522030b04060b040608122a060a14060f090624040e01050a06140a051305041a03070602010605060901180503030408 73
    0x801403140c82c5c030b0080340041c452502d01100000b104003956400104035041207049405100800c19034042d652164083c1820800e214600d10341401d4500c140a45003002900703071060942e176003060200194106040e191050b5002c4180d208c0013409041007503141070b5950000c0c1c040742c406000e1006211071504032405468040e5001c1c004a0b03640e0000d40c1c0e441d6114405000f07007103c00d100e00308440c14202c180c80b6800c44041c101c4039203c000d00c0310150074058141c2d6041e801c85d555100714411840715105182c4d02480448000e001180e4500204041c00c0000b4100c82c8280d0380b1003840d2407001e09200d0324142004038101c1d0703a511592560802800c0e00000e018281c81540000000141720f8030403030201e282020020b4480d420408005000d4680c4e4004a1040340e507103940c0d61011074a91990f1061388c090b20403420040d01307101e0f1000107050500b0041e410040c1164144042840039850b120220b61010b0401c0c03905440181d0f50708110408d008040d0400c540c14000012b000407900c0c80021032900840d464 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 549956393 1250 549955143 549955163
    0x260a08060906060f09040605030f070f05010804020a050105160804080a0b0108030a051b03040519180e0c0f030c0a0605070b0705040f05010302070203030918011a2a0a080a020703 78
    0x18010000c492404851050348018200b00031440046610094220017102800116266490b10002420540d040c541d007035069022220030007075a11140f1012005007802c1c01e0201503820140c0100719410100d004150520000048000586182110200031503400800d02a140c5480e8030a85450f03180c182410358810342030000128100b1000300071a4901d031301c603844851414803c00c01c2000c1809450080c581c05004c18400000c0a4452000380c1243c1590f0041d0180840c3c244960b10381000140f400b607812403460035800c43c600400c00103604580e1041180c240c041940071200080c0b904044540150b0021f038682c10004016070400e0103000514840d40440146954404044859000d103201d2184107041008041180707502a90050904500183c180e038039100e09440812608440030203034140d0342c150080100b110284489406205042e1520441d14240c0e40685540190040f940c002040e1440c003081c501d0410800c00c0500c0711b440e84101c0703003520744d42e00707030806500c5500512040e2124a2a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 549957643 1250 549956393 549956401
    0x3110d05010320030c0603070804030504030b041b1e0b161b032904021908061005030d05310f031b0905160305070509061303050d080415020304260a08 66
    0x80b4180c00e4801c0c01a21b5541550354821044841040161041d014000100004000700b01c544006610460144c00b40002e41c9102c1a8200700c202e4007603005001c0b48040d115503000e960081880300e4122407210500544801e0344060702c03445c1e040c1d908002008440c45009940c1c660841c1e0301d000d0f046a01480c04076109000712280443c115008152038440d40b441c0e080014011310740714080c01c1d0302e01001e08100c11510b0f02c620140349081d8059504900060161070b042040c1c1ca0708000c0c04411403414135256040c10304040181070140b43c0c0804075248103c5000c44c4d11000020400148014a030184c44619156500c0c05c1042c1c0d081d500d0101070030b43e07020010000c60b4008103401554001c4254516840b4030041d80d250442c0140005800c8000f0814208041410343c1e42d0000908040003040e11494500e6146141a83c40c180d8070890b007105101070300080201290341c50106c04a601c009040141c0d0f41da4641c54500d0060290400c00040c40c1042d030f2407003001c0d0386404050b00400c68107403145840342e29 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 549958893 1250 549957643 549957649
    0x100c0305192d140108010504020f12150405010e060705130e040819020a0605150a08010c0203091014120a0b0406080c060904060308040e1e04110103110d05010320 71
    0x990304802e0403008a00c080070000351008000001d41c0400c014000101510144120302200400b0380c46084142c1d107400a000c00c0d40381c02c2c40740c11f500d44411601002c0c0c411024602c5900c0c0c3d0b14860821407585e14210000d400e000e029000344d200c040141091714000e24140038050700c1900f001c200d401101030303180c00105140c2000441c0a0103503800138005800c0028107080c040005c3c1c03207200d0520440c02545292800074449014581c040d036600c1c03050b40540385a410030300c01d03a802c0da030f03200b1582603052041f2448459000f00447e09000010354134120303c1c070702c0c003241580c222142c0088030300c1d101000580f4449650341214454081e0100715000d00640c1b25450421041d01d00c103005280e400c1e00000c15078100c07890400000d0559510181000c80c1065680d02c54080b203401c00d0344540c800101c00010014020210503c8a55024034111002081e0400303440e214126480c40071140d05250f41c0315143c2e510580f101080d0f4888450442c130074402581c5030b2618242c400d580e403141840d190401c90684446103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 549960143 1250 549958893 549958901
    0x616091707171b131506050c12031b130f0b0324010e010503060f04050924010303051215060d0c08010501030204030807060209060903060703090302060c040b1b100c030519 75
    0x1030200900b4140f00c0a00c0c10030030a1050102c09844481c99460114214a04000c00f5201c01080b050700c0700c0c1d1321800d0802c081801c040311107034842c0607580100100a103010300003501600b00c1d080058182d413a45001c0c0c0d01c0044120094001281c0000300890000e0071074080d0000358441d4404038215584008030300d00980312448040748060126017540396041e03055110700050340d0700110043c43e84100d10118800301e0101d5070283d41c519a031303400c4040e030174200c000c0c0d800e40d800d22448800b60003100c0350324644009101c2d002e00c100c81100d44441c003011504004034200d0811a08500070030055440a240d0200380003001d80e820040080781141c0000640f960191003a2411250810142c03450320440d80e580c58003d501c4100129030001051080c010075440030004c951061080e910000b0b8000b01608010b0302d004d500614540258408210a100440c5e8810541d90040e0b40d100141040000201101e820101501070440c1000d103404241110954507400c0b140c0541100124000b034081c510001800703807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 549961393 1250 549960143 549960163
    0x5030106050a0c110d0503071b0302030a11010c06110703031a0303070f080c07170c0901050d030309020d211403100b0705150423060603061609170717 66
    0x41034042c030a1886441c019410500142d00c55048880702000710b0740051001d0981420549240e071000c40c100341001100804880949a908a0f06690501d1039000a0780c2d460000d00c01000003456a117210301c1640110100c1a00300e074444d2040c000090654103c564942001c2000e074006400d14103254800011150100103000c00600610320f801455105c3d8407005403001c0c01100c41d940c0c00c0010903079208060007210050001004001440390340030143c185002c4d00400e406101d43c41c038000400860351034400d112480b540c18103000c16002d50500004000100c22a800341082c980d130320382e0043c0768400184095003c1c0450b16074440c6e1032100490341080b804200e6219002c8000a070342400b880c010a40a003040301e1140d011501400304510340000c003404262412100040308191540729409101070360072040401d42c004010b00d19084001035a00c140240001904000c14004040031078440c50b0b004000d0306070280e138201480703446520a40e0311045481000300101140f13002e1a408203020074040c0d45 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 549962643 1250 549961393 549961397
    0x9130e010506040e0d05070503070b090124060806040e1c030c0912111504080109050705040b010507020f04052d0124020303160c0203010c0215060d17070311060f01050102070605030106 81
    0x5001781501d030684440d8090300050790148030070b00c611000110f100940d503202c0c1c114000007094a11820b81020149014410700d0301c0320180010302400204d42c0200e03020340c00501207030007084542044d64a54244000c120200c009054a440304549a64050300008524100d682d55803c001d41c1d16150000c103078031500c00088c0b045451500004a51a200416050120719004800e140696941000d800c459101030704940b01e4004502c10009880d084c400c1000110b400e003882c03807410042da030010703118020040b400b91180341d0381c001040c5240407902c0c80c5131341c0045400b14420070b00c030b80c03403030780f01504409200c2ca952160207082d00084040303000b054800040c1441d002141917444100480382c2a803042008502088540803054003da030b001d000c1c00d01142246d4000c0c1400c4060711004017021003004003854000c074507001580300041d07010781d100015030b80d110707420715203800080c9003c80c3e8140e03440c500d1107100c0c4906c2091141044207408114100d9030240c003241c000e00e60728041991240400d1040e000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 549963893 1250 549962643 549962653
    0xc0801080c2124040204060603110318160b030f070c020d060b01020c090103030c0c060e010c0f1502070c0609090908121f081e151b09130e010506040e 66
    0x81c0150150711041c596600c240650740d4004041242d25010803c800300c02d440d00045400344815420944143c2c00034141c10324041c009002d100e088888070744070180c68403c0184410114002105082c8031402c0d041020340002416266101a500015003090750904003030544040480c98035030140400e9403440e0350103450900d04040507200c0300000e100e04503105056004a203580b92070380e96645400d07400f03944607440380055149542096003028943e900040140031903e1241c0c085c580c3c00c5011015060761241e00d0a081c03129600c0d101002d0a190084001d000d0700102e00c0d84100710f101d40a100558809035103d1a14035543ca80c1e0303c0940e40300340c50140c24100104101003101000304002ca81c060480d061000b07490740c0c00212040e0681860b031001d005908551101040075000314084251498000000c0051a5210034585c88148002e0b01240d80d004d80158281c2c054007460050b14550300c0002c0c440c0f201e1401013081080503204009180d01e555103440e0000c1d07000d20306845070003841c40046000780 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 549965143 1250 549963893 549963919
    0x30a051e011802011b1407030b04050c010207060206010b18120c151c0f021c05100e0613020a120c03150b031006031d032107050304111009030204020a030c0801080c 72
    0xc0781710000d9a8055540b866131a00e811481c000400080000354854588841e0a24107070a00c00d04000341803038540e046401859040003443d50000b06141580d81d45101c2c90741c0d0b281080c412240c4050607903145900f00c4a20b20310755840b00e0000c642d4940800e401d0315001044202c1c144a1900382c0314a020101e803c410030034546481990541c407810755040941c0c001071034000c008140d441c1001c2d0300005210825102c1007045120612301242c4401001c02c48100340c0c150810320001100c071825a40e900c803c2c642d010a0814034039202d400d04283c07070903880404204a644048008000d008900065000c0b011004800240c403094901182d114a400003e082d04c0c5604040302207002c2d0a600300c0921819260003244052011f040c00105202c01e1015403641012005403460000528028208418050b06004000100d56010809a940042100c20080c01c420b2004156560f28990700060b41091011804142d40d0b60180d10400f8020010f89542c3c04682e41c90300006d9585001d0043d098009002090030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 549966393 1250 549965143 549965177
    0x20d02060403050a0909090c051c0308041509080408070f060c020f1207090612120e010804031412040b0a24060c081b03031e10050f030a051e01180201 66
    0x945144803103445c145164075940c0c82e4042c29115100020b8800a0000c0b0003000329103010303103088a143c502844d030301c079214030b42e0744003d09901402030004d0310440704000c00c1e17040741400354404130701142c1c4800d00d1070700d860303d074004955107514a0194151a885810001c11b1050044080940b0ba51b40107028150280d0f807c42445088a900c04403402e00d8414030001213400005070140700040c0c420f0084400f003800050520a003031080c86022201070121941c8603181990340108940d83c440d03050b0801d681100348041090700c051083e030100340c0d510904081440100f2441c0c0200320f02540b981c00e024804000d00070000402e0809210f0040c0107a1154801003100d00e000e0340324482d109004481ca1401d2103c1281d440340d005090010000198000108000c07000020b298003401b010078500100000740341c00150554960424003901c1e00c94180603591030440da5040104410f2603a0120945030b08050980c82a00e070541d00d0650903100e0f500740340100c010102200c04030b60a0f1a0141e662001b00b885080c42 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 549967643 1250 549966393 549966397
    0x1150f05041a041113090b091b071e122c0a18020a021504110409022d120a0b06040e0a05060f0105011d15030606091c12020d0206040305 60
    0x600c40e0a8810b124070070340d8903551880303180242c0500d0703848607544520030136010802c1780281e0003140c072075807071b10500ca1842c0d1507108110b0f07803040d003030b403130b450480c0e04581011b01190050520080c0601c6020914aa514140c01940d440181c440c1281c912084807a10060f18542502043d01c00000c1041c906081c8000307040c207650b0b2807080d001d03119004054840c00840200500e20b4464407455030000f035034041145e81041b440200d00d4803001c50703902600b091b42d1042400041900b5180c0720715100c001c5a030540d91560508462141b0a10070082501195070070380e440c04101e2030101c0d02c00c150280d0307511850100030401c000d00c0b50f440325507501e0f02d54500c0200030041c0404689103604d072040c0c1003000d0009500b0005540200c0540122000540c034001c0010703c582003014240840034920165800b01e5141c42c0c03695000f807802e480780c1c40d0300c1e540d4040205c0d641d401742c12480e0394000700f42014000804110107502c02c0e0039000f00100104188610000d82c1d841c85001c1454005034059030006000c2842080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 549968893 1250 549967643 549967661
    0x5031b1305120607080c0c0a0b150d0b060102100908030f070207030c060905042306010c02310e0c0a0b07060f050a020d0c110309040902030a05060405060901150f0504 73
    0x10051840e5101d501051048800041e084010381c0494140501c042c1c00a5099512200c00100203103824840d190315a15550305003001880124000c02003560844021030200c51810050001401e180c0d0354201955200c00603690103025001d0701c0014441c081da070340078160103103030041210b52458031001850310041c50300a0440c0c0442c05200700c0800012400420040203010a0b42d4034581c10b03060500300300c2103681e40d00904a640094010410240700b1501e05107510806c00d09100c404140c5034000300f103210b541e1082c80070800d46003100d040d6100c1a4041c0048000c00a00d204111440325020410780c0e40d803440784e28582c811001401000a10182070060100d03502c18078000c140140b92908490030b8607000c0e91191607594003c07034103c5402aa603c81c4003003660f400c5c50300030221214503003070f2500d80c0b240701d40450040703844002c441c00b59141004040081540007080ba202c2c1e14040c101241c8548055580704002e500341002c0000c0c036800d01e0010001c2c1d44181c005a29407a2a20f020040104083c070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 549970143 1250 549968893 549968917
    0x507140a060c090819170c2811090c0301121106040914100311130e030a0807110105060f010e030c0d031e0512040609151a090705031b 59
    0x1106500001c1d842d009000c0c280420b0b0300c07803610712424941e01c54204902d008010490400b00c1c480708021451101d070342e90303910310000321040e901d4204050250621b4000c550f180c41c51080d07040310b440b10020317808900000c54000e0300c43c250780038511400c0000c3e49c0010740f0782c0f402002d02440180065901000c0d400080c9108000c082100400d0f840810000c1d000303544040d805940d15031581056049a2620980c000140000361390340604603075840c0200e032650790240d07024201501c46440241d0f12607000c1e41100101e101103984070318080b04003c10b2244100e0710400001c0c410a8500c3c2c4140e4140030701805200000d2540148031450001110401c0200d100315601d482900c0d007580181d2610102c1c2d080c0c807406540c607112040c02c09010091441a441c0d021001c00c002008101060382c017802d040c6030800d5000d2070101b40070505040100110300281c0c9040c1a50b4a88010710004000c14115446211000e4a006105a075103060640e820300040b41c8412602214004103354020000f0040113a04501 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 549971393 1250 549970143 549970153
    0x201020403232a0918070303030e0718020406111f05060402070f060b0f0321070f0803010e16050301152001020a03020304052b032c16080d050714 64
    0x3d0203d02c0c03503070348550360248070814504541c9041c0f804e02c20595035010580f003145c01e800d0b05d051009180d841c0800d00c800b030b0800d070784c8105903d00348805004940081c10540400d20703030310441c203500305d0003503002d4440e078004180810b4482c3c4030150085a0000e00c102d060b090600d06811310314202c0b0191070010001c5078400d50030400c000c0052564441c5175020350151000240b901d402d14140841e40580f0b0854038480d40c0082180702c1220718900c0c41f00100000460610340354402460300400348002081c2c001d0104001100201e2120307010030f6035611507248026000710301d000380c0d03106030340503c001c3c02620341c849009030b04e945215002d025000708032100210308000c04401c0744005802c90b003241c1203140000342c0010078802030150402022540520001340041380007600d603078a07101041c4040c03444003415142d11500c00c04e91800402c0d0648600a620712040c407202204105072607906110300006800f169200214030640c1c00a9000394039030864032000d00d006465101c0103010b003841e00d4514424851 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 549972643 1250 549971393 549971413
    0x3130e060108160234060806150c0c03010615021207080d0b0f030d120b0f06030601081503061e07020d0e010507020307030204020d0207020907110c010e0d1a090d020102040323 77
    0x34000300400b02410045105e02d085400107440500c240d0f5a0344482c081010707040500215507100c850b10210400071005259554031a030b101c2030b003454401c41d2001d0385940780c900c0010747d0303190342d20035003001d42e0665007030b5141c480e4600400c1989004204000c0c00d8048140107042c4c030300c83c141e4001e100d0541d00030541c84480007201c0c00645042550781e407d00c0051f2108503070160301c6203036019104004008880d150125030f000c002003230150100400711410807034000c1c0880c149440c03100c0ca0041d6441c019055920b00d150140c00250211001800c1020045035500000e686501c0451420030101d070681c0c1f01c2c240c6042420044601c0c2c2c101010590341401040310000041e507071803000341003071001c1d900050307145c4850380100f00c0d4905004023110b050000b52581c090f60321070301048800c0c0300b100034201001c02e00985000710f0220031140700e004081c00c0400141c0b20740343c0365801c90306201d11048000c0341d20200442000b28240d000f0b034440108504611003442c000b459690720318440c0e1100313440454000c81c0e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 549973893 1250 549972643 549972673
    0xb0d0219051810051b01060503010b040204051c080408070303021b091b0307052a0f120901080a0915090c0f0302030c091f06050c070e01050117090705030109030203130e0601081602 79
    0x170314081d0411003a0342d5000204210f040070302a2035488003088604604081c600000308100004520044445062102070351040060003002c0da401307802500103e0720f050b03440e860060354034221260010400007070310f041c4100b140f604c1c00700c85100e10305c44504c820700d803a03078180e96204641000d031000d02804000d0003003225140790702070100c140c0e041c0750381071034040c5400c035000074148000035240c1002234002102c1001190200421150801400c1c0b80c8901d441e60b07140003400007401c0d51a0000c0c003440b20895015084800f541207407a809008002d18450203564058200900c0350074440250960480102403a0038900b41c402c3e268018140682d11141c1c8001a040341c1d15202c0c40c6d000440402c80200c0ca120301c084003005400090004400103144550400001a1003062108031410b400754580c000039000100500102c4001c0c4000740003441035600a26010b5204e030000100011204480b00000030031150303191603c0c1c056807040c1c4902d5841e890f403440d400c2c00e42078044142c1066205480c01480e20380 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 549975143 1250 549973893 549973927
    0x20723010222031101030c0215070e09040f020405090606030c04022508130608010b19021c0c0b090a08070f0f0f0b070e010f021207030201060b0d021905181005 70
    0x40780d0000d880d035006086103030130416680100e8810f810149800d881000c030940000314581d008044c09001d5419594020741102c400c000810803c2e00710101c1c109010070130406060000d6900c1c03007201e0a04c5140d9400c001507a41e000125071140e49a446403d800c4054105075000385042e80d03a0340da1030884080c107280d40000e02403c02104403030b044000500301c0071943d04254410041d05151a000c9465490004000c0040c000ea20b070481c860745110f9010181d0324002c110320740310b040b03a0401d040301c10100340501510f03104100c2400e40701801c5e420b0028801c1000481c0e0014865800380d1500d00703219080d250514822038504003101d10021800c15240820955200e501185214070014680c40ca00038200178171050010703018505120000ea8200401034010a01d168003041081d070305134131443e49050407405450140c1c07040c0b140080014543d50402155001041c0500b5140c242601903000064104c60f14481e0400741003848240c50b403100e02c0361920a04400201c2c400d45060350901104140c403e00c8a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 549976393 1250 549975143 549975187
    0xf1009020a05060c1f02070c1701020d05010e0604062103050313080705010504020117070804081309020301091a0105070b0c16051c0e01020304051509191e090207230102 74
    0x1a8040d2151061703000c50605190040304d9070940550405110f5030340d1180205142c015a407043c820741e03141300010f50b400d5064869170450190b05002d5035943d000505c8180d20700384d44042c0103a081c00360110301c078a9420b43da14450740c0b04c11030340e03914580c131030f2011540d603000501104201c03009032202d0700220b541140036025070340c001c0d400016142082c4c40054402e2206888100355100e50300c081159803600a0b10990b80503802c48540d590b24885402000001030741d03074100509281c408800403440707031465030002502060342807500c01c407030402000554450041d02002440800401c0014100141c441c02500445070005508114081c1c0c0e82d84041c2840505030307008400180c2185118202a4099036a04070104280099440c243c2010041104008051090125003400258481e0303a501c40c00901c0d015800040345040714242c4503421501002960300002c00d10240307501002c07136200f44d203100b00c8031882e0740201300f03450512441e84040e1030466429240704040d5800d00c180400d0a203032150150070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 549977643 1250 549976393 549976417
    0x80105010f0509010e04030c060f09050a02040e060c0708160f1103100e0312060a08061303080a05010b070605092505091303020705120a0501020f1b0f1009020a0506 72
    0x520341c1822a050391004460b401203114485150042000c0c0742c1110040340c2041c0c240c54800b910000c14140000581420030303000f5001c03498148a0000d02c9004101340b01d84031710071607041c000104c90281050ba51a010789803009880340410502d400035540304000d020803644910422500caa040d100e07401000705482d0141e40c0a400c1c1c40c00b14440f03150900030049040c0030604200310311070701d40c85150f030f9a01030098905522486400070841a94600d0380390b0000b0241082196203038503107081440000c10078007d045000c01e03d41c8002c119031451601407503043c0c65150000c2424140c0a4940380007522000d091034129005109512011403c10510851801810b0590300b42d00c170315000a112120300700030214050480180a200000f0f0b9011400700204c5101710303200e040e200d24200b0a64100003011800030002d602c000340304041e6924000c080c1070f070a0101c00c1040314a00c0a11911601e070300c1c810740900059003040813080c580000c203a000c41a02e82c00070341b5901000e41c417035002c00c2d00d990044510030780c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 549978893 1250 549977643 549977651
    0x1109010e0622111b150105150403051009052407140c1c18030f0602030c160c0905011e030308090a0218060f060711091b0d0603110102030a020c0d020301060506040801 73
    0x3083c40b95038200950418841802404103001c00258030003005c0c018041c261041c85008003000d600141001600c0c040c41c1c001c010b5a00a80800131031400030181d00208030362314040d0340c541850381d005500d1945082c40710b05c440507a59030745150044034541600304c06643c400f04140f02c0040c15400400c580c01c04128202100840308140c45170141642c1d030102400381d100e615605007880020284441c140029900040160b2691a441d0480740b0703501440c26220203510103544e410703042c4240e101d81a4103d414004040100f07980310541a03a002e01c2c0544094404070700030800b04000381c0304420159111000d081501ca41c2c0d01c8075400200790744022007039146009500001d02c052403400628075014090104d07502460003060782c0d98203c0b00d001070401103204c1d0201c44000380b0148403210985803c03014003446181d881800409480041005000a60300105240e40e2040254000800c4885600854000308050321401d4100402c142402004070303055520b4140000d043d4540e18081c1c07000e4601c00300085 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 549980143 1250 549978893 549978907
    0x11b110102060901181e0b04030c020a060801050315040302190b100b071e062007030806102304030209180c03010204030305030708040f120203071109010e062211 71
    0x2458182c0190040b11941d00d030026070040c1c0b240460309020700c0365018109143c02c2400f00d00c15504c0c45220308003e8544001036080000b010703405142c4001e21071080b1100d41e0000d031542800c036407c076000d010f05501540120721808a980d20880511f9215102e4030459548000301000300f42e40754000c540494043c0071032014031035445c0700c00d01c2d000b01500902000d039091a04584030781c0c5404280512080d4800d25040c0d02c0010b102054003c0d0359008030100700c6800c1da6400160f1040c41e46e118000a0740040c0d019000328641d4904500412502c10442e5a140c0243c6040e4a141c800d9003030103100d20b81c0f0380c1410000000162034170020617109500046403030390341c101801c204c141040c3c4101040b40c401d920401091001035001000d5a0308506e00d0f00c1c0c444041d0b6502c0c1307824007010f021750201925a008151035000001d6000005103e1760f8858800c0f41c00490004061292262007801403248407d204400500c541c1480e0701003030100300082c1c0d45603610100c0c02e95043d044841000a000e207031800040e0071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 549981393 1250 549980143 549980147
    0x50c0c030d09050d06060e07170708010509010b1b010903200d0519030e0a05010501150305010e040605132f0303120a1e0f050a06050d03080106030b011b1101 69
    0x40a0000016405000000251003004160181d140220391040905a2450341071107070326403028010f01505c0008411030305203044050135a4604410136400700d900b0000041d070881c420300c683c0e41240d1000d0000001c50f4281440d03500c80d90444421f40c003000e031140240440c030b48001d01805402c0707802916000c9000d070300401c401201807080344070300c54141e206500d100e480d25402002c0710641d07401e038022640301d0681c0d804210080c100c07c1104004a101d030072a0306c0240003041d030005049461411960112140060050b8251907003440b882502c40d8030348000402103440c0382c1000c2d6005441100ca0b8041c2c4485503100e01107950491407103241c0a040b2450f10045050803020140b40c10780803001107040202ca0810101c0f5010300416442c002c40e20343c82042044603004540c00c20104809101f840580348050100c0006c1c60111540340d21603003824000240c90402540f031250aa800d641d070100507a08080003a805406181c409504014410421511040310b17142d01c2e0311443e101d0621024201016000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 549982643 1250 549981393 549981403
    0x50903062d0c07060902010c022d030a0f020f0f150c071a0a0f020c040239070306050c090d0302010b030609010b221d07080106060c020105030705160c06050c 69
    0x40c11401020402d01c50941e4410007511152a0702c8200400c04e68400d1004803405042480300030740000000a4040f82d00f00442500d0403420007540c80700d10407545450405a852012000151a14000341800030260811464400352008041d0000e02d82c0000500807842c0d8400000d4089a4048040703003d040800c41400004010300103000303824200c26940108641501ca40191a41400708504198507014024000cd002441c2d00401c01c40d00e90b10204991054086c4032101800c030302c203112a06c1c0d0500d0401e030f401620090501c43c014010b80e415035691038001e03c0050031902440006109030380c00c9503107030072051803060310a07400480e00d0405c880c1854503104025118042d9641410603001c203d488555030140200140081e458205e09100b44080003001c0c10762168441925602e000d078105000000c00c04203d4400c503008204413565420110361104040e54028001441007010401c07207880380307010744900600b84140703030440302c03a030781e60032a020700154403030000700b6404180c0444101043c02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 549983893 1250 549982643 549982711
    0x15080a05060a0606090504150305030310030c1e061101092f0d081e091f0f030203150f13050412030e010203010b030109050c0d0c0206060a090e0c010f05090306 70
    0x2d002e00c2098144407000e0108440d42c043d86000d159940307206905640ca0403030040007180c010003074903580e007408030318100b030207101c0c0c0011381e1110610b00d8005160901d210304109401e028010700c1c41c6d020b0a0000440b120b190a4070b10f20043e40d2602e1a850110720007910016240d405042224070704c0001042483d08205403006807840760601c2314410012895900c1146e100c1403500e035049503a401644071085860041c1020281c10825100024059a190f01e03110761140409446041c1c000c25043c10441c01c1e0300c0115822558545044600640360900745c0940516801c020159a8050040c042001c11200112000d645112241010050640e01071055003002a007070b0700250700d15070400b04048000e20040c483c65006540d40d100140c601103144040e150302010004043c00000040d0702c00960394401901e00c248146426076002075645000d1007902e1400d078540014050080c40d81c0015aa2001c04210311000e00808201080c425503040c44141d100c1c078440103c0d1315289038003100d130190b014a286 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 549985143 1250 549983893 549983911
    0x210060501210e01060e01030825030e04050414010f050f220b040602210105011403011d0702032203050114101403100e030a030b0907050a0c0615080a0506 68
    0x200100d02665010b03246001e501d001000b01203000308112030798500600059201400c00c000c3c620000c401c00807980014211640e620318040b150075039070703144e04010700c024801c01804600a0480c1c41071900705030308a40d5103e402210354040445c504004d40c1d01351781d030703030b11489904540d10f40030400b1034070307204841a40040c0c040d4140c03481c2002c010458013242c4248034020f4004030260300010300300403664044955461001400c8902c1c22200381e910001424280a55070200d40c0341d20f4030400704030184054a040351081500000d80180c0356154032030010020700321504500007004615042c000524a040000d0344444206092a195003070050860302100c131216000c0303e107a030603c200600010104019201b1502450101c0e41c440000207181519400c01204480e08040ea145c0740c0c0c8001001801103141a071700c0901030000340108000c40d08004840c5580420014407150490394850390001e01078038807400c400100110042d58074210141241d12103607241e0700100311407042200c2405541e4101c00e00ca = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 549986393 1250 549985143 549985157
    0xd14011506091503020d0b040603080c010b0402031302010e0415080a0c090c0e1201020c060f07030b0d03051b010f141b0f040501050c0c04110c010e0c090a15150210060501 75
    0x446001401100301c1c0c24a80c08054020903810014003542c1d021744020347c00200b0401025a40c0d15100d0765603002400191040d51030705101110604190085a10410382801d82407048480f41d8015a8a0850ba4002c29007042e6240103070807851590000c11005001e1341801001130301032915104840000d1504003644103418011001c006a408c1002008001700440d01a0404000110507a0081c00b482500c80300502c100400d200780341495402440c050910399805020788104801840410f859250000b030000d8010040010801400c411108031a6003840001c00e080f4286040c24003500c0031742401815a09282c07040c800013604500405010464012000b4101545050120001e00942c0b240e181402400070340709100d25814020005107030002041004055041c10078044641c01004298050b0744c6050646c1c00c20103400100300f00311443c01400141c4a03560948035502a00201701c5d510040301d05010040ba0040c1d03014802901c285c0300740c0c01007642050846812003a2440c40d84120305200d95 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 549987643 1250 549986393 549986399
    0x90b010302131202030a060606080a050c070b0604150e090c010806120706210e1c090b1602031e0303070f09061b031e02010b041104230d1401150609 65
    0x1058040300c1240c020f59a010032000250020a0030709030b201000400131440c0030b0300032969035003000b42caa0144110300003c0040c0d40d2a0004a09144108180078101ca544000020740e0742c50241c000d0844120350740003c92280350f64244da620304d000c00781c0b24604142c0007800550762070b50340510a29401101110041c40741100b0400094032200300340a60780c20040e102c0d681540b1031500c40004412066812070401c00c080c9403007100380d1112162503c440300c010195a040080920940d003040a1300e001002c964544051100103044004045a08907094001c1c81070a07869040b0b00220100005a9880550303503038541100024400c040c461001414041480b42c02e208040d801507041e040300e480d8840c1c03000405880d0505840f0b07041004200070202504603080600954190415103001000380c5d005c1c00007101d03500e981c45190140c0c1c06104603081c103585850344003505001644410141c09844e25111141d42d44401c1703a040700c02c1c200c000850391203024208401a914003910700508691402218041c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 549988893 1250 549987643 549987667
    0x60b091e090f04020d080a030518030c0c060c1006150905031c11071e050102011103090a1203020c03072d020105031906050a030f0b1308040504270804090b010302 71
    0x5400b074441c88080008000260854842060103003249800c4068940c44000c821001405003804840401d001c200c041d84400140c08000251000a5164000b811030256050140021900402c00030100340c46003400388100484144507000c080d00044084800c1d0307110883c0050400f0440f44d0000740694060401343e910030000112042d50041c170fa14103032043c1c2802c414401d281481d00d4100541614080c07245502c280c0c54130405400301d91003070b0020710082c0038039010b52400380003c482c10b43e016005100f1040001d945c80f60003042c40d070b07031031f06006041105690303082e46503401108046075010248a0a810700081d1215014030a0940c065003140c00801030b80020b1240c0405801e61403d6440b85e001403042103820b4100c1c0e005890090030402007140d490074403862a1001c7c18060354900366020205262101404050701d4803a041649549001d181000344001000820092820312071252046c000000c6400e5100e21700f1317030040b00350540750703400d0894031070440e1b078184200e80c1854410815034035108 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 549990143 1250 549988893 549988909
    0x12070804030210030e0d200105040c1518120201120504150203060f03061e07080c3007030c0f0e0d02090709030f030c0b1302031b13060b091e 62
    0xb541030f40c404660b0714241e0b00a4001d0041c103058400326000349000ca541480c0e0040f2070300050b41c8a000c4a03002c0c250191980c03404c031041a603010b860f0010b0480f0a0015100d0946540100000782c90305d0441719000c00e039400070000c4140c00012400f459002d09106640e44000041b11102c0703583c20420650610382d4440c5175a002101c2500380c06600031000440d940d440a1110358598030140aa42c411f05d0030410680200c400b030500c0c8800390031030001084116110355001071041c011851a01d10344a0345000101000c10040c118007a19803c602820740006120746c8902e005030300d9901c000c1444050180080c0c4042c1d22010010100142c040458583d0b40c6c49004034600f05806440c184215200c80b00100c1e08010b0360303000503001e03844022944007096800105886540c0c02610f0750001520380402602d1445036883c0040d606521440004500180380e40302d6004282c00200703035079882c090092220050ba855a44500b560420202c2c00c06410f04201034005041c14245121241aa000400040c210 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 549991393 1250 549990143 549990149
    0x3050906101401080405030912010506130207030c0b0606041703070c0801110403170c060c040f090b0105030f090f07060201020409060e01150f03090614091c051909030f03050306010212070804 84
    0x4c0d01c0012509015082c0708031104110301034032054480310072a070f5080c0a40401e4428034050b241c1319090815216441c4280c07490180c1c140e035440a15000c9407104a400d52018081c1c0790f00440800c0000782c4c811030504501d5518010740081c0d500ca076928100761101c120039512128030f59040800f25000400214111b905907076120810005c50290602102444c3c02601c5e6001800e10410080c002d889031603001800854480001d20900340d07856035a408140c602651025010641c180017003103510000c0400264440709000444600444012180c8d2030702320a40c2c043c5001d80d60018042c80394109600484c005003404900c0c69849514140719074080c000c014004408006141d40007542061298001c90469a08850b0911105882c01c2c1071512000041c1c0305420f00340308e0012040c00e4280501030250b1601c030310340ca076141450b2503101e03541c103c1d418011540081203441c00000c000120a282884a40e6010340d4545481340781042c0007926040e008003e03040712901c203100c01c00019840c042100c041d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 549992643 1250 549991393 549991397
    0xb010903120507240219050901020706052115030c040902030304030210091206020405120a0c0302100e1203070203060c070b0403140f0c0604051b060f030702160603050906101401 78
    0x10301c80040c1008600b01340c080c0029401c80c541c0b005800000c610a40140100c0380b81c1406480380d503c107800040d00e080c411058000e02507000840c082048901481c0a0603410301103520340000c0f04500c18580010b00e90894482408012980e81c840146c00c080021914441b41554104043c1525030002556402036203c002d02c280c0541c05038000b0700340b080c040320004100c85035803114280c0051130100041e40060080300e0045010075103500c1c2c2d03610300003144d10403150407980c00c0d030800b030541e0280b080302d604901c08003007400f0030720442500f5a01c6100e043c034021210f0704055a100c0010744105800c04502401c0880325140910455001c0b03024000810b400c141d043c02c000140447c12000702c5524061001071414007000414501000380300400c0f2948501e200d2030a5582802028450352210440101501d801070010302c02400208805001950003014a0048406034014843c049071420656000140040c0e210400c2c412490010001c26410041500034213409500b003d02c0000d14040e41d10250341 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 549993893 1250 549992643 549992647
    0x1080f1506040e0a031e14190e37060503130309030b0f040302100501060507080d110708041406310e010b1804090f020d14031201090b0109031205 64
    0x8071035455600c1030140c41d45002c161000d00e5900c0c10060f000c0300e0204103104c460b22051322803400c0c0314821906004102d0b141d1041d44c2c1040200c103030180420103088101c10901081840290701c2da9070700ca44501185141190303036007840c0e500d903a444400501c0c015203901030350041c04050140c2500441907035440a134803030400c0024512401c04682c451410340c03001c0d0441c0141000d010000003c03442c1103104030b00070780880b0032100b01e024404003120750900c98000051024484800080c1c5504028100c803000700c000410f03110b80200c0e40c14842d500c6503104030380202d40000c04024030303403801030884101007041300c0b0f4a050000358007a0380280e1412003d40d40021440c10594250044c4000e0244094010550221002e607110300120000303030703c80030000300c0600c01c0724210703845840d0900420b10810391119003a0b94080540d030910151b040c803014204c0b43c08041d90510316401c00104040d18055592803915801075241100d038204550740320900c10b04210036108180003107011440310301800040c40c6022a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 549995143 1250 549993893 549993901
    0xa05090c18040617010b090108061605120c04061d1503040602120901050a060b0405030d0503090a080c07030209060d05120f0f03091b06040f060f0c02030102030a0f0501080f15 77
    0x1e22403007464036885a1042ca0401e0105101c8800462446003006110003009001d41020411048500900c6181c1d5650f002400107001050ba007000d401e10003585007070142c24259450014401080f040315045080e1101050820007241d2125084140000020710300e0b130a4440000414007120140c04698010381000000c94200724683e0f04452032104007541d0814139040c80a8180e02810054581c001050b003400000f182e0102c0c00d008448c11288010001c3c4241c4012a405071801e80000304070023400d009000102d408928a1001401512030020161030800e0440c41013000074800580002e0041204850f000001f6000081503515016074400d0700782c5031511189940d011380304021003260000004414032481e01c6d8000b46000140301038401e15800410f420050010f640100d01c00c1034a00040c040e0100401d50052a0000c400d414a00e001c03400c0000580200e400d9a000f590034520107070351400d040342c5111140c402ca602411100c1d018200540300c180e41c1a5071940411250811440f094002c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 549996393 1250 549995143 549995167
    0xc0801060c032006040b010302120c0303030a0c090807030305071a221b080105060a14090403080403023405060c071404060f0305030c060606070b0f0a0f0e03180a05090c 74
    0xb03c2c50744203403081180d18a15103072a152040180c01e00c0308a00425800b20300d941c00c490301080e51010448007074010343c1142d84410320f11000c1c20f4008040c400b48841c64102040c0c1140a01c100d01c0514004d40350b251366a6554a4820f151784aa610104801d01c0031405015102e8080e503107158084140301d0351102261020700b0301c5070110349140180342041100e4000010040819004280700d210222600066180c0c0d60700c0c3c4e00324100c113000d560f44c3d0040c4800e0010b00082d00801c1c090350000e00a10455a03000240c0b0700b519503540000c0100c1c3c5415046040d83c1c0c4a11049491b460007900c401d40d410b85c10b140ca905d09a55603003006004032940f000d400b228040ba03036100c43d8082d9004011801110040729500d0402030b860398000c50a005503402001e0000c0e20500301b010403688403c1e4005445522961104c01c04081880040e02e00140c1645032644440164640d000c2c03482d0b0441c4100c055a80c5500c0c0740301311402d680900d410030380074441d228001c02c00c07a070340c030745d00b4550201e40800c090395114a000c800c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 549997643 1250 549996393 549996437
    0xd0818130f0608030301030206120403110d050720030622060c0e011d1302071406040c080f010608060a090201050c010618050a05040c052211030a0c0801060c03 70
    0x40250001020103201148503015003001c1604081100100640350b00c034228291644824000a9007080040002012003c0900002a8024000d1602c40070a24601c030304035007044419521308000800100b8a48140400381109420711065000d2030504280050080390322800018285144204980800d5020042c00e000708016030ba40000104101c4c4c1c4500c8003c0e140c00303080800c007400611001c84100f01200300c1504540c0c0c1c0d804c020184002c407840324181201030340c40000115420700000d906140382c0c81007004464000ca101d044c00e50b0000b42800291b81c0360600290000000d41e0414404020a9602081d140d801418840022485032a580016074561040340e540c1200c940ca00040021040301100201c403844054400500c40703600d41080c0c2500352442610090902d1850035810811440c20201c01e60302d41c03000990f5049482544400c500840300700080180e400d403000420401044124401ca151541c81c80c2007002e035550400c080103040103141180201808810341102c5908084490 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 549998893 1250 549997643 549997687
    0x20f0d05121308061005060f040b18120111041509030b0f071209151e14090105090304063204140a0f060c08031803032d060d08 56
    0x21103a02040c1200070501990002c1800c00800c542008041488880403030781c0f40c0036a80042c0c1108001d8100401c00c2600c1c2e000240031344800e84100000543d0180400c0035111110b11a0007441c070380345a1005121200907180b40c0d420550f4900146121844501e0003a24151280882011030014800b417050f2034822458001170050260a002c03c0880a801d503041c600c1401166542410180b04094540613641c8140300184001c00100d4400e0103202c007680114201000f00e2058401c091507034103440c0486080b2506c004030050036004100044c502402001e810030f0140004629140c501180107041040403400000700b001105000816240c86804401c5058400070b9400d43d5907035104810000c1001c02040907000d404c40c100b0001300310307620540c0c80d0304888407911952101c800f6580e030402258802000010404c0640b44040f00c04042000914440d40c0d07807100c410b114000030760310504003051205a4803030304244441001050349039080320301a160f0348a000a602d4001c40018000020070a40c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 550000000 1107 549998893 549998903
    0x51c0303230703150b0c01090507170601120f080412120f1d01110f061e19050a02090d030915090b16150207030306141804020f0d 57
    0x30341044d00c00144071496401500e032a400c0550098009040d06006603568040b402c040110400819003d030554030254070744815125030b0300c0e541d5141409100785d24032400003080f04011105c80d880c8440c42d0701100d060384039030b158550694078840c044801d81d0b41074104044032400c140108846400c0358002d6841180045405580c0840c8070b0030340c800d0504002c404440151000320602c249550442d400300500300b40d080002e44801140280b10001000d940c2d44824002c600440c203001000240700b8160104590f56207254100090280001e46504410001a08030030164010030542c00d40b0b004031540864103660310421945030100d4001d02c0c611000c200300006030154026002c01c41c6512418080b0320710700300d8a0ad401c050341c101c0101100400c0d21a442400503006030070104040c00d01c103544a404c401240325142c21a24000303000a4045c0000d40050105501c480701e030740050603004 = true := by decide +kernel

theorem cover : BRFrame.Cov 549820143 550000000 := by
  have h0 := BRFrame.cov_init 549820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 549820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 549820143 ≤ n) (h2 : n < 550000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
