-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1223
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:50:53.781793+00:00
-- url     : https://prove2.me/submissions/d8bde9fa-e63a-4992-a629-21ef42f3c607

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 219784172 ≤ n < 219964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 219785422 1250 219784172 219784193
    0x103060b0415110d05220302090a09030806090f070507140102071209063e060408090f0105040e010e0c0c0307150b0415030b071107081608060103120e060403 69
    0x31142985112007030401601502e03c50000904002a030031902e4520282c64010048070450318031414000d2881000702d800004002d13042e0070280d0001e84402c200149207010764411044103000303403643d500d1640d80404025500508984501280c600c1d100401d1000d03000d50050f1000b03d10030000404180d07000b440050072a004640d0960340b03031070800340e0039004135000b400c4580942014500021805001150041402c0316400c010182c28030590010300103038049441075494451443c10f881060500b414041d0b407903040a600f80b40304070a45000755504d503000304100c5040fa01040b094255a03880c003124100c0c003e1000704801149401002100054641070000b4945a03100300403e0715070000d1114004101c50740c0c5c00c5243e0185145c5505000e000d011840080110395206014811079990640e0494450b41e90383c90b00c3d1220f1040010100c1c100c04040303481d0508500f00c412082c40c007a50743d80043c0c2d0f00d84003880003a00001c10031400510b003602c110b5420781c4140010340703003a1800341d03203035209070501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 219786672 1250 219785422 219785429
    0x10f080a09200a08030a02071a070501020d0906060b09091305150403050a080109091a10050a240305040b040611040e070f020f120a3e010e0615010503060103060b04 72
    0x1500d024040b45514500800c02502402d030b80d000940c01c004801001943d030b56176500460322090011144500916480c50441d004d00b5800b200035034032803c8241014002d40840501198242e007042c00110704a108007083d1200c6d41c42c010240041501c40c500d25812004034203106403020b0007058030303440501e048540c049003d035220b0340c1c840341c2d10441b80c24024400324041c2c0061340160305200c2402d0100310461000d866201c9603002000b4162280010325141c04410b40c42203070005856000007608200c0b41c403a5400283c8840d041703400349584c0c02c078210100c41c0b048400502c110034034400b140201d9901e600008445079200031346c5103480d0701c07080740d100004c400f10349078030010b4201042c0d07040045c0e043c002080000001c000410400e0360f1400c004041d4010168900c0400c00d03c41981c2c1402040824104070200c091001c420402c0309000d91030402504c2d10021101035800e0513a0051f1442c1c00040d258890390b44043e402412075000801140c0641c4064601410541c8039017000c035002c1e107804003d0008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 219787922 1250 219786672 219786713
    0x2010b030327030c1c2105030a0c0e040f0f0b060a080f1306140406150b0301090f020f070809010f0c02150705010b091810050c03011e03050303090607080f06010f080a09 74
    0x5c1da54903d40081e92560308510300d450f8503210002250710507044000d6981201d9075000c0400c217a0030182c1c00b02c4035000c2d09458150700500300040c2c545050f2481d0f04c4003409400d0000b00313100516041060000502c0b4252086000a030820b0000f82c5460740e43c7c80741604400d08000c41010042c403510340d5000c0c0da920102d4040c10450700010301040002601c62499006001c4c485101c0d1203203000185a11804140300e00b0042c1d03a1074071520030a420066040b1000d002e20032030001d850300020308084409030004801c645c08181c10300710102c0550b000e4052501080d90052510054a00120300c4081982190f0000c65203036413903c8410420307a54003000584103414040d12a4580c580d401002c52404600f0300d0f40b00000e0b45803400b846544060001181c6c1500c981d100e058216042100c2c198401412039800032700340740008410b00c0b40051000c9070740c5000300015901c0350482d0710f6424020020300c00a840307040c042a00440500c000600800e1810b03880001210300141515a946030400301001655601c02c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 219789172 1250 219787922 219787969
    0x302030c030d0204151e0f022b200304090b0406170604110d0309030b040807080403080a090f050d060507140c031b060112030507050a0c060f02010b030327030c 70
    0x44012a1740f9074400350441840c0c04143c6000600c0740e841800e0341c884800f420000c1c580c4c4140b003598001c101c40d1408003081c1c2c0c9402c003642d03081009011082400090080000c0e06c070490451817000f0709914a41c41c0060070041d47c035091505c443c0c0c10040c80e44280e4130fa001900d9150004003000c0c142042041c4103004006440d0302c1c900b502d4803150003503003603009a12940a100103280441e9101d515102a070b40e007e40500d0803911241460011400340090042400c040000e0102c10040c58070050601500191581c0e200207071600740c002034010503401060380226241d503a64000c0f070091380209420009030f013000c040c00012540b02042c2d540c888d118030410fa500c00540e4909019800c04e8490440000002400c49541003a000014403400300c3d50260401501080c0c42c1d092100500060100030340c07080c40c5500d0f0355552800500900c0300180e002016501c0c0134840001820003000712021140c10000792100008083c020542c00882e01000369010700c60349200c00c03256292501c402c0f20081c0c600c2d14051 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 219790422 1250 219789172 219789179
    0x110c0406080d080c041208031806070c0b0f01180513051b0a05090c0a2105010314101b0f0203070f0f0b130f02010311070209100620030d090302030c030d0204 69
    0x3d080c4034000d040c060450104020410a00c0950000c2005196008203507954a884800c2d9400c00e04552001c050014080c41060101081d004111264020b2040d02d1030841a580c01820001424091003a44190310102280c00070041c40c50340019032048074964270700801c0405484107490302d070300c4100c0320138400801012503800345080e2100c1002170100f00c0d0132128a2600d9051341d409400f801c0d070303010300b40220854420149004810001c6c042805044108642d603074034241f01048082640c2e100d5031034000e01d90004c54500036402411030b0703202a01101040c5200303280c000c0760f4504041c0f246a003140000e000c1d0f14001140141610145d50040c00d100300061781c41d007000e241000e409014403842d2032150044600060040040c0b01d02d81e502424000751440000010703164620600c100294000300640801c6205840014010709484182d56a0101e5440c0302c1603407145076054022176803081e801840407003c0320f03201e5002070446d14443d2041e2424114041c4030107166410030f0042040e81ca401103010b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 219791672 1250 219790422 219790427
    0xe01031b02060910180602130b07050717031305150405030709060501020d0519030f0914151311060915030c0405030c040b0907080604020f0d0902030c040506010906110c0406080d 78
    0x180b03501900d4400070001d00e125006000170050002100403d01c50700401c00210700182c0d001200000c103403a585040d500c0c1c0301031414580724406405028040303409070001c81044c2c840082683d0300219041000e50791242041c0402c0300e80d000d0721403032130908a4100030201d6661014007a040080007030314004100241000006420042300c030b04143c04100d030038492040000e000d500040078418403402d000545023040c0540c0406450f551030041e000000340c007285088013400041c02c0e0a40c40c0c81d03407485105078542034204e07081c2000a001c087c0440451111060442c9030881c0108892900108070383d159400d081c403900010340044915000e020f002040400060030188410550507100b00c904000002c82440001d01403c0084d15910801905800160403030300d86a040320060882e040c0d083d0f0300e40112408400c0030340005442203000740101040c140060805002d07050041c1016102d503c240b42c1008012a649000520004000c0c400c2c0c0140e00101d4035240303c1d1101910400c07018150140f58000003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 219792922 1250 219791672 219791683
    0x281707030c0b1c0b0a0306020a0c15060b090906030f07060c1a07140702040b0a150e0906031c05040905070e090f0c0414150a03020403140a020306070e01031b020609 72
    0x1000c0d15580c1006840c921450389140da2141c0f4030010400686140b41501183e090221504010112840002e8407260548c0000340c0580052103031001403003a04030090f00310309807040c0d0300c2121030226050041003a245001030980e0f40c0144042d048404034085264514503110386544608003061401080b04103209070300a007946c45904000c1e4604035800c0c8100010800404000c0382603290b86c0c0403d00318119030f0b59400540a01400904080d0701d01e0704e0750070100c4c0700c00241e80000e01082103000300b504a0304000541c039100e402c00034060328100010000c14400300c09400c040c0c8003081001c01010800d0500b40c450240501c040b5655103080c59440790074800c5022000d8600140990301404100504142404480aa0303c140b10000d568500c5c00022400040822864480a840100c0c0c070320910303945540035000310780c003541081000f6448810810784841c2050406901a00040300050205019996505d5012010701d8005200c4138044800310407a202c0804c50001a080341e014004130b190204803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 219794172 1250 219792922 219792929
    0xc030231061701060807050706140a0f1a19090204090b040507020303090c22060824010b04050103020f09060703020a0210030606051e090916031505281707030c 70
    0x2c040011a0011614a0604005100324410030140000003440300c5e2050041e200e425500000030700060701024494003d407101114802d070707050f2404000ca5020301e040c5c002c02c0d4065103222070b482d8480f07c07550184030420000c0342640c40d100220060000300340b001e9100500042c50104400504940c00340c00304002d40d407024100c0401c55005100340000b140380070941c10031144040b240d07607480741100803032082d245014002141c0c20b50f1800000203040400883d110301002e41d00f00c109154403070820340c0c0e41c02c6030f00c0a00501c6400c100610050080754000d500410a00039104142c505001490001070300300d502086013100140c0040c0c2d400300440c01c0408644103c2c030b42e182000e0003a1070801c1001422801190032044520010500400c82070251504a511000001d80420440c0c030b0b20001c42c8542010291020300020b240c980d4808001c58844490380c11342e2402400b0b041c0d9040d030000e500c1c180a032100503002c1100101e840c005542480441e1603028600c3d038030003500e2494074504101651041690 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 219795422 1250 219794172 219794177
    0x506040e1605031209090f150a0f080f0a0c0e1909050c0f0604210c05121c050906070201050904060e1f0504091109220602031906031101030c03023106 66
    0x7100030703000e0303440846c2164012841c0600c08802d0b0303281551040d407040201d181941251486202180d180038103412282a00c0541c401c44084807803020007507a640a40b003001602040202109101c43e0740205a0130350442200290007022901c5500800c044403000d6002b183d90358485203400045003041c0c803c005c02c404045a209d400d091400e49a890a2100101d190040c0000d050030301c0d04210790000700c40e000e0180540242400e4a80000c010340e00c049080c460200d0368103e0018030441441078003240c0c000c030030140145040c107106034015603154020501c3c060340a522141c02290000c0404c1c0359500c1055011002c0c1103400704104001800c04854003d035000364100200384000c00c0b621250312214490640d1402a00e07030303031098240c611003000d041c25900400c030404030301d080c8032080d00034501900901e03482e0250741c481480b405080b124248001030200116400d50030156000340d0020305a01c005013009450030314581401900d90026420745020820380079103040620124042040240c42c160 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 219796672 1250 219795422 219795427
    0x7120f06051009080d03021c0203010602030a020f03040303090e0c1c05100503070f0303050702030a0501020406170703051308030702030903100903111615121401050f030c060d0506040e16050312 85
    0x119000b03445d40d05110741d0350140b54001a401c01c2c11a6410f01e0f102030f09540040c00c54403561245002504d03135125810040051040c0c400201c0b0720600402100d0440c0c0c3c2c95158246030501e0861120b040840080c00720100000a00c910b40603802c008040145a50300c0c10000500c81c600340d08a468070340b420fa000b01c0e000c1d0303001c039009004a4407038002160540b0381604007180c55040e00d00c002480c0c800048070007400d1394004940045c00c1900400e102d8800d1700d8041d03100c2401d980b03100b0100d04175901119090491804103201c4404601e03a0310085400542ca8410b403072038400c3d102d0120307103041c1d66030400740002507a83c10514145580098038030304010942015010725060070401b400355080d580140344000c054041e202d152035020f445188a039440c6200141301c201100c0610125408007403054038042c158000400366540341c0400c2d40c0b10303031718002004107003410800542d40c0d00400c03004200d650000d40d5452000b10b5030804000b0044e040038901c0300610814284070501d42460340381001c2c2d44a1070b109 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 219797922 1250 219796672 219796679
    0xa03020606040e19060614101b050102090409050c100e0a031103190308060f0a060c080d060e190c020a0804150e06041701060b0c0c0907120f06051009 66
    0x41030391908030400b02d03004241d010030341903c142014881c0c2100700c5002034001c42c2004012040d004141240d501106400082a181062000c010524171038080003800380c4d00c0c0708031520203010a28603090300903000142080c91040114086400210b07058900f5400640c1602c903524003c11081010302d910718001c140182e44901094844296001c010003104203d18144045d407400c10a80c01807107040302d0161084055820041d02c40f001c15a155406100c41c0214800341e4200300c445102260075a42d144c0380c3c4000c150322001d14030b800c10b03144821006e40303130b010016140c0c03d808040d50107402501c000e0202c41540c1c05074101181c511520071030540d04009003200225160000f544c0840b95204520300210001d8031003100d00030940700b01294045d4001c5008200c401d5916450030030707040b101000b081000e4a4280317402090086480d403002c25840b60b8890308007400c2100e41d0740c0c2c200782c0724240840003c850500810548032828002180c940d0f603420100180d2601e031700e40d04110002402c01449a505 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 219799172 1250 219797922 219797927
    0x3041d1003050c100215070f1e08070507170706050f010e06010e0103020706021b0313050910030f030203120406050610080601080414070f1206111207030b01030e0f07030c080a03 78
    0xf0a0300550f10130542c0f03c8102c040c031802031010090b22250f0340ca03405007074030303000b0030280c80d605480b2060710000f40344002c0c2c6004682c42d00038161300ca03011a1aa80400c0c0d8424138101c9040c1e00102e011202c902c42030503120456070100000c3c00342c4500c1040046001e291048440300c0713402050b070200b40100001c1c010f100c4540d800902c9400842421300e009030381e9001d2420220f0182c0700b007414980c00607810070590400501d011004d8042200e0844910f4a0982e03580b04100300b00e40e0a0b03078404803403500c039442040080c004070708070143c09101c1d00559080c08280040842c00d800121810784400d503d41d001c1080d00d180207100e07140701c002d00b0f080c108c1e0ba50600c100000c100070310040008100750248a0400141c2404110031402069200c109201490f141c401094241c0d46488045072240c0c10240c01da042c8109180644030922551030f5120f200740c3e42c150b000c074054800c1d40d6010f814196187c0c51001d580b041404000507004280d0000c0040c2451480c00d0782c1d045070280e0110b4441c0c1c001c411000006035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 219800422 1250 219799172 219799183
    0x9170304030b2406070804050d151b022d060a0207050106090e0604060504020a0503030a2c03190303060b0d09051209010c1106090d240207020a030f031103041d100305 73
    0x10f0240c482d140c17102000e2505c64114481c5800c1154410502156071003003042001242c034400404400510800d9407100400f044030055900920150300b18540a05020b1070b090020b0f4002d0b26020744000d0111030340e2030380d2402c0c4071040d9031040e60f40b80c000910b0380a1100034080e80c0002d08280c0070130132038800a100c400341c4442014100824041d100e0001c0b83c20b66440c1d0201c00050701c03006081d00d50b0745005010242c102e0714001a8992451400d9400c1d81d03041040035905000d4500180141400c1440102100441010740b2821818540d0b20540800c2c43e510890281c00781203100040001c42d000242030030391410340301e910011100c1104010300c950b2a40c0c03002a1204996004070fa0f0180460f01030300050060050384841c580007210746c02e170b40e0244070b0095007141116080d9201c41ea900f403801c20829059120f48031010390403200202c0d0400004081006490b900d501a02d846403010420300062421540701b940308504549141511040e00d8034400c03806908410703440c1d100101c003403865403034a4492 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 219801672 1250 219800422 219800491
    0x60b100c03050904060e090102180d0503041509080102070c1415041701020912031b0303040b071124060102010b0a05030a0f021809011e1e0c09170304030b 68
    0x80f03050210707038980780c04c250040c0c40c0c007868480e03a510b011982e42e4000e40100c3e0301d4a0255001c12400c4420342011800c84594a401501440c179150501c10b200c292800650029010040b041c0c0380010626021320107404214820742d0003082c41c0340b8014031081144600e00c1d00d248507003c4003440c11504950081203608680264100301d21b50704034a042640203010308580c1d0f50304042c8508407885810b50200080040742040c034003120b601d1a0164000765a40000c4400400070000e440200c5c1c10349016002d418141a14103003140c425850550030300c0000440c0302003c2e00c04003001014804550303028040c4030902102654070a000d1440c0000213030781e07030807181c0d40600007078080b200080a42d01c80d04e04901080001c5014120241003002015008050040555143e0f080400011108003118040c4400d03029401d911035903844041990040100503002407d0140845a0000188030000d0003201c1c4113060002c000d036461318a10300f000400e82030000c0c640c3c030b1442900005900046202d01662510 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 219802922 1250 219801672 219801677
    0x1003020f0a121a0f010803070b06150a0309050c01020c030a12171f0e1306151502031e0705070b1c05090d3b190e04060b100c03 56
    0x100c66a1011440000003074000700d510002c00030004003440000405900444440301c0c026003240c2e6054842c580811003030290044a404c10000c2202281c41201035603048031000f442a40c85201291103a030107684407034402004030380ca4000c088184201031111403c000307400c2c0090690008004002601c0c5e22543c04000c000507640b4801da05520b21809015039094051203180c0344034145610390111811542c0320055107520110004105c0305450304000740504002051034007072409a0f501c460140c070040200d4080c038000280001045c0002550100803951a5000340d42d0351642e1a40407024a00e080103061000c400800c50720001a1000542d141142d08070407995854101c02880006102c55400c0c0342c00e401400e141c14800c00000120724800940030686074094408280e840b59a607802c1c012119074044420100c40f0100324492001c8082142001440c2018000000c40040650a00d64115002c5001514204404c100317091184880c4c4000441c2e00c8900d001c8440702c002c1c0b0617100d10400504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 219804172 1250 219802922 219802939
    0x1060501031a091e04140115061d031024050603040f1b05031204090c171311030607020a0201090803040b0d0b0d0c141e061602010504080f1014100302 66
    0x2c85106200328050003224006130b03d01c590406082600354200000f481c2d52545d440c0c80c620f003286500c212960b40c00c80d40c068507440d6200540c0c0700380b00742590f01c25010682500a14594155201c501d2144c0c8c0c421031030400070141d0300084450742c14403081003500111300940080083c440407d02c20003200b4402c07644440c017481c42c601c1c41c60000f10b40101c55405182c00d032140420000032008480082d10943c0e802e070300104000c0c003a80c50210b03169690340080c40d101c04a684049010054031510f65420f071409028208016200a40820b180880071906a00140c000742c0d0443d00f150b83c000316090050129800440c00c0c2800e10881003050312a002c0002c61140e40c84203012416210030592004268000d04444689940ea4030301241e41415072584074802c0d90260b40040100355074150200d078000d0003819075820044817804070303190084601d0741a418860103020011303403071400f00101441c40300c01c54042d001c10088449c00c84185c400824007925058100020881e02841d0303802c9000c2225011200e061 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 219805422 1250 219804172 219804181
    0x50903030708090315100e07030c17100b030408040608090607020303130c030b0a0605100314060607021503040c050102100920012a020a050306010302011205150402040e0901060501031a09 82
    0xc3c6031010810301e400e6085e46000c10840c1c44180e02c500b120841e404029034403480c0d0703200c0342d01301c044503018411200816014200c0c50948c0d00d50081c41d40d8800c100107041000d070740d11101490b00e5034000b11012904404001418411a540481c043ea04020000028585400c1c071100180d101e0100400c1c92040240d4400780c4030074000744007143c00086400203a944110304015142c0406000c00f0300420380203d89611214040078842c3c8103181c03d50303040c005102c1460b290801044983ea11100081c0c1c3e0005c006d0038001e034503030a40c00065011350f208001e003008507440d05001906009070385c07a102400625000d036120115025402224040c0220a40071051480044c0160380d81442c000d042d1418040c114410102050414000c5512500803181c154900340d48404041d80d0381c0c0c09000c000c2c0064100340d0380c0c14804d11540c01158001c0ca20701001458170550001090403a0881d0303224902041007c0c1c1407010045003031040c2c0300030342002e00c1d00344000c2400200d5a00000e1050101c41d00810100c40001c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 219806672 1250 219805422 219805429
    0x91e031109013f060b0a080607020a06050a0e1c1202070f060c14030a0e120c15040f05100209010e09072a170301060f030501060c080714011401140105090303070809 72
    0x18030110003001607800f800282814014010700c0880700c0140107804103000401d0081001800324491583c5500410420302c1d81da036000d0280002038a83c0e00803a442e036090300316000040c4200204094482100640d00c910080001c01003100248130303c91141c410040342001c10500801007142c1030300164085142c13700c000040707035406100348025500b400088140300068500340c0081c00050703000e208550f4444e400300c3c4050090b1240c1200e800941d07214026407410180301c103541640c041d0140c40300c80c440c4010389d202c00e410214089040c0b031015600042c0182c156801601210300f2240030781e4444080c0c5002d09002c0c00c50707811400c070741501e02510031950001c102ca41402a40c007a51200d1400d0f034560540d2145d840e0340e0400c0c050980841c2d1541c83c0124628401e10405040301c01c540d55005260740715403101a00d903802410140c4500c2940e81b051200f0030380c05d014030810f02c0d2125140f1041d540c503081c5480c03521b4800040f054100a82008414a10758000040d6002203402280040da60300410000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 219807922 1250 219806672 219806759
    0x4090207031211091206190903090b1c110a0c03080a020912030301090c050c060106050d0e031c0b010504050a05040e07030203060a0507080609060916091e03110901 72
    0x602c4519428010030040003141c200107440d08900541d0b280141000c0085496110003086a403918060b45e540207c540f070b250141c00400c0043e019041415070307542c8455600340b95a0042c03040c3d0b4030107440b12a02c103210481c6403090420048031840b2640c00c0500006004100e406101e0700601044000c00103e01c003850664100c0e000150014441c44c001c800140c5030365260340003485034a45040c540031850218030b0043c81140d040c3e910400103408182e09081c81507c0c282c204c481d01d0f00010f90794040744400c1034001c00050105a52040c0c0c141042c0e003c03000000141d49040c0c3c071190400c02d05200800c110b881e4009d040b0140c0300212000f0070703450340c1940800c6c98103a05500180d41841003800740001030000e948018001d81c0ca1f40ea464040b03030303100c10030300c040b80500740d483c1600034041c440040c040707102d68a01240c10b1212850300800c216a0341d001c180c00c0c2041c443c1c1001d0031048045003002008000035075a101001c00b96030442c25907141c0328071010700740c0008260003081c1c041c80942112001c000d000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 219809172 1250 219807922 219807947
    0x90f0c07110616030c121106040605090a150e0d03060b0d0f0908030f04030e0d020f0d0201120606020f060a0e071809080d1b020f0c01050d0b03070303170a050c0409020703 75
    0x3d04000300000c1c0e09005245682c1084141c84050081c01445c00940c40f80f0180c80072048286d0050166441d5030f40e81000404e4002c0c4000710714003c0441c100b001504a0485442c105402100424041506e00050707041551101d054014540707469400c100003c0540144e80460207541000134000380c004031694094000041c00074110b92000003084215401c40d81040e0140d8000d0b43c0301401045c908050082c1c4003507491010394000b10540103401c062600442241800c1d00c10700d0110b451090b034542610a640c80ba8100101513000104001084c400410216030b000d240a1002d10450410481840e101c0080c1d00a00c407001d100c48401c40c003025010740015900a0740308024940d1030301c03404035540003004001d03d540c0d4211400044001018030014039024403000000180446030402c100540e071680c401c090076405251101441105580e041c000040114000e840368800310017030036100240c14400620a4004a00c0c08061100042030381060301c00b6145950b0005a03a582c440c01c1c00c0d0b860011514 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 219810422 1250 219809172 219809197
    0xb1c050a0c030318060e0a0b0a0c2f0603040f0201111f0203060a1202130e070e0406090506010e01030c051509040c09171902100306030203031305090f0c071106 70
    0x70000401c06500031501d0b0012205101480000b40c2c8480080761540310f070084896004440c0a02844182280401040005103038202800c2000c4141d0358441c043c14036107401d90254244801c40b13601c0001c141810351144004992491551034503544500700000075110203810001c2d07819a509000504001c2c1903a200894040541d0719100c4031054030283d407040710038600035000200002040d071030000e009602e03a58024480b0030b401120a02c1103000304441d0706079441070310640000050340c1304500c00c0540030314002c0e040421401818100580b0300801a400503c01050b501c00420200d50040e80d540b0a032a000c6501001c1c221542c0b040c1402d50246121255000c0e1411010240b166040309140045802c1041014a107072440c420382d54692001c01c01d94080100d8040c100e000601c2c6c0040c4c00c0030b001085040000356591a50042842d6130030580362460300c00784452040c44245071020717259a00000107401541c3c94a80b104003910070f80a00c00c0010840e9000c0301000c0640da036a003080d1003600d007240 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 219811672 1250 219810422 219810443
    0x405090c0d0b1804051207111009050a08060105120f06070809010b09160305010602010204050f0f040f1e0605030c01050f3f01090515011206050402160203060a0b1c050a 74
    0x4402200541c0c190b508903414800c003419200504c0020040c3e0759450740007204070344070030601409d004240170a01c9120382007246144010440c0e984021178000540800801008a07604bc0018402802e042c001841066400103003c9003040038005000c80d0f201d80c240c90b00c0e07440c98032075400b298003500d80101000c0d07011312254200103a54038403542484d02101c1642d0f0912842e6a1140143c0c200d11883c05a650843c0702540000ca40b820141c5185958800c0500b0001d03866494040074012203000c00d01d00d41c19841c0c100b42e50b10180055009a2000c0c080440c040c0201892540018240344540d4801b030a4032100850083d01064410014450288512455010118102c100c805103103032111440200c03880182d00100b2a01c035a442203070300c90820150010305045090006490010400c0c0c3d03070011960712900c1c04516616540003038048802d4000484030b810f10a8810181440c000400c10131602e032400308034060030f40c0d920868244512005440e04101c2c4040c0c20300504103c0c0c0b000300174264024a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 219812922 1250 219811672 219811699
    0x20403020a0b1809090622140106030521030a1116110118050622091b09050d021813020303070c03060c3f0c02150c0405090c0d0b 57
    0x82d007000b40400380c0209010100c41260710308100f004842a501d41002d5441440004c01c0402c044025452500c0c000f43c20941c041102e968101a030300203507421412994403402c0030820004100b000203030348100607080d94609140d00c0324010003404000c250240413030300c5010f100951072006007110307040000c0c160201d12076100d50038400c408820004a49002980815a0003008280c07400c40c082940e9000f802c06180640300100c40e000319001301000010119248070009610035507101d5220148642e9412200d40103200c000902000281c2d4440d602804200904400503660310341103002c2503206801e103a8150304d0b0702e150f013050004404402905444002180380a112001c00984101c0e84103c1040c04000c4150400f1110381a2100e81e0b80b48421b03c0341c010b2150303503d1100240d10340a043d07404031442c256072442c44030180c41140b104500582c001e201044081041e041c00d0030b511100140602d45454a88000728540b0071000b061004400404181da80281023030750040c8403d5039004005c0c061a080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 219814172 1250 219812922 219812939
    0x190b030a0f0b100503060406020703020102040f0f24020d0f051603031d011407050c1f0509060f01050d06020c010605040203040b01240e0f01020f06011d10141003020403020a 76
    0x103018070180c2e005040007000400d010003007542141502d501801a004988455a84401030f422040040302507540902000c2210181680102c000740310281d035001283d4508182d142e8030040f40041100400000308000c8440c0d900081c005540c00b005192038803210550341030842e06070090049001c1180792140e031071002e055054115030380503034510348083d41001d500c003003007030032035807a034403040721014040d070009031003d014401500142480c0e1058881c15a50419140c03c0319254035420311480e5036800a003e210700c41003200640c06020600c05c006907504200000c1c804800d2944001c101d1a0000b814040303240342904161300814000c1c0c400d6480b41441c1c90420421030090043d9466040c0e0062080c400c91000c2a1400e8565141e40712454801491380c1448031b01200c1c03240303560652207008a644415001004860b008046403520203800b00d1400d06941c0c04484041c02814024825180c240926140a4202a02004102c41515080340003c109801034060b59102030350100407980001501c1f42c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 219815422 1250 219814172 219814193
    0xa060905100503011404020f0603100e2e080c0d11030a0609020118060e100309050a050c010f050906030f090a0501060308120601031521050102030a060e060d0506190b030a 75
    0x180b04030300911981107200900d0880240c01c540180d4080000c0003d000581010001141c00c0340200d05001c0070907498040d050517204081d904505820703080201c060494000d0403a42c140c6040c18440050b8861901c17120301e584440b100c8a85101d0810720509200f0040c1240322255200c4000d0141c40b400302e02c50410303400400007014103a010624940c58a06103c500c41481c8090360701a88402680401240030b00c401000441045030030b0556440e64500824000c1041180c0c0910900c014006038420f1380004016462074280700007031060600a10403155240020340e40d00c007504000d00c0c4d00503624442100d2400070641006482ca519109010051101e4103001b429001091600c0c54820385609004400311884810000502c040e40c040a128224901c1e500038000742010048a004500b541c4405007241c1c41501d0709600036a80701010050050a00101c41d4840000c64402c084291280c850300d450390b0005181517a121403d103480c01d400c01c15540040da50030303009403c07a0404480c902c1c00d04c1881 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 219816672 1250 219815422 219815429
    0x703030e03160b0d1410050916080a0207030324080106050105040806060d290108120406020a020114041d040c050f031e03040e09010c020601080d0c0204090809040c02030403150507090e0a06090510 86
    0x102080700c0015580341c55101d48800070710655072752b500699911000e400094008003411401c01d41c13036442d442543c0b0071840f00d291001000010703940c0000d00d810600b03421070f4002e621503418003000380000c001294003c82d520b40d0120094031108007079041031070441201300100c00540012401d149064120100541e02541a1040a000c0300d00f80d0303219121441e404c0c040d80c856480180d01182809005500c00d1110070303903260f00e455056080986074a0705540604440c905101141c840e00b0800040c801c1c8628802e0041c4000d5980158101c440750210351551354280b07601c41207050032150300900c850b042007101d008100c44d480615150500c1401140648071011510005204080010a240b80c01040140000d8059107841544400c04d83c01d010240c01450f80980d89114144035000194441d070151140180190f4040c1d603545045140c039445401d10300d03129103901842c010402c42e000d900441030750151440a082c55a15640780c3c1301d100007030700007604026581820882484640c2c00301d8103022056 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 219817922 1250 219816672 219816679
    0x12021305010806040b09060c030403030c0215090102090102010b0405010f031707050105070306080d08010f3303050403080c07050604060506030102191d120705010503090709020301080703030e03160b0d141005 91
    0x40c6c1d00e400d181075549078415905028a02000c001140c0028000d40c8010b1000c001c500513100d0807696041703e10001c44003100c50003120f940000f00c031503440d03a0a03c964a00420100d0b810003095041041180a04400e80002006850390614007690400c40c0002c0e558026801300007070001d480c0c40d04008000c1c0c40310380b03d089a03500c5014035040d070140c014441035068801d903000c007102c054980840268403080181030030f800079015000e506405140000b490b000d1050f5610045204c0c00c10f45401007040300014040c1481103410301c12400010b4012030156003003a0003180104503a1168400640207200300e00d51110490303014258040401d40081c40150703516075400810780461808414401000d0511590603110380054405000c5903011304046c5422540c918119804140c0703544441d000c07a40280c003d4102030b8415102001010f5000603d000340c81801c3d8040c02c1c0c1d03044002c0350750743c0060f0103004411035040b000c511411a0745480e44040300000d14446500d0440c200203440320402c42c002d00980e4003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 219819172 1250 219817922 219817943
    0x1e02252103091e05150a080705090103060e0c22120f030909050901140702011503020d0c03020d030e0f0409020616080903030a1d01030203060d0b04050304270b09101202130501080604 80
    0x611449100c11b4030601a02615405415900c000c002c640562040d00003d040c07555817070b0082040801b410b00d00c0d12540940782c0455441c0d10603d500b055841d844040301c2854120010240103c0202c0d8000802c52603000c00300703041c800b410380b030280c0e41c08406802071040c0c0ba1616081004c004415009a1040381c12840c00100b26216440100e0a81d100c134860710456000d441402c10050900c0340029000710300a40d04d40c1d0042d9141d41c001050302d86218015000910b020340d0b000c1315483e00c910b8000035034000722000c200c11800d550105030306000b82e207802207900e0019405003081c002c1c0036044920755940141034980d00c81804001800c2140c0c0005407652201100715024880d500a20031240aa04020248001e00503140c0e145100c2c01d00050044403640018480010043c1c54100522210b949104495071002c0d2001480e03401c1752501c10720315204003a0320080c04003aa14110007902900c420585880f010101c5001050340c001000400d80107551900c00009201d080218106000c2ca1045042a0f07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 219820422 1250 219819172 219819199
    0xf180a060516080313080c0d031b0f30020406020709150b0f0c1005010524220f030303020406091a0a0305071e02252103091e05 56
    0x4400c1d00030701400400d160502e1610001103043d62010307540c0403410522a1441801c940c0e01d000298000c20300100841e408488030081d42c0d0341500422031514000455104800e40ba5180140400040101d0300184804c1e114005100e0b030110049416240403180382c041c1c0702c0d00300c0c0e006078001e6007d8801e0100500561001040e040902c5c022030303000a01448001400c00e041c4230103001141d1119460403d80d40081040f2006500c05203d000040816920300003541d61508091103500c40c5540d68820541c0e484400d00204072440405985418040140e0a05800782112100160b60456009013650a03a00b000c00410540c0c943c0040058850035540c2d00829a600c1e410084980c1d9100c1049566140501070364884c0c038800d82c81903a001c0501c3c82e2038801090501004015441c01c2003d100042e007042c9200c01100035159a4482c000140f81d4040606920701010800f00070194010010400d0442e011751080c90f00c103082c2c6d04c0280ca4007000c07954110411602c182001c56061180d5401076612504d5003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 219821672 1250 219820422 219820427
    0x30b0a0e1909080406050a02030d181e0507060f110a0c050f060c0d0e0607020d060c02010b01020708070e090f19030f140702010309170703030506041401180905030f180a06 75
    0x310301943e40161000d061074100001500c0070340101e640da0045100c00e100c003200804032400380c0c1305001000d2441e4101d1900c2c509162482d4070031100841a043d001d80001c0000074000030700082107503451315000210b10020581101d4845403130542068501c140411138082c0520b44038001d040f0340089038002c44800403102801074170b006002e212046504582d10b0780301100e01941d0351801c00c50700104000c3c54010258005840c0c1c0c8106001500d50036610803100b50080d40910481d51018800d000800b091403801036400d5070340119000c0d0358040c0d1100d90102e15100401c205107400241c20405075881119030940420543d04801c4c0280c1c0006d0014021a800318020002c10b04030744602c2c11040d1070003000780c0041d0017a0619400499005407030170046900d421284000d041594803d540124283c1050740801c070a5401e101d035a114524043d6004019003514910050300c14141801c011601c4102c41c24420300394051940f83c0000702c1d9001500180b05803200d00c1005e440c01d011a01003175500c1d140e4404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 219822922 1250 219821672 219821681
    0x2031503160902090103180f0c0608060f04021c0617060705070b1602120c0a03090902030106023301060806030d09080c01030f0603020301060b030f0f040b0a05040201030b0a0e19 78
    0x4690a698000c1d5081c0321450080d0010301c003580040c10042100005140722101c1c05164a60649102c0041d80c402c01c02c020500300c0003030040c43e99240c1080d20b800c14100003a03c0e00400850603200303a0380065070707050058508044040f60310180c0f00411120b80d0341c1401c8060121480650000350041000103109540a441520500b5030090325a0f0781c1a958075410303130000c00580090307800798800c0d01e240b40030360300e1028020844048104058014414245005840402c0d80d07089154014014401031010381e500158280000101c4402e035051200002544000344441c014000f83c1e0299003000491055082142c650041809030115001007003855006c0707410070034a001d0013410383c1054007130600c658440e41000c6a1481e055400243c10790b40d03980041e0071540503a005c030240d548007008201a450f010f130314243d444513590b449025189440d42d2a24ad0b02100201b4503c90710360f50350b000c2001c1da407113640070320000301c00035040d841029100d6280c42c0024600315614680c0002d00e00007102c0d908001d015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 219824172 1250 219822922 219822943
    0x50108070302070c30080a0f050408120913020307020a03080a0923010e03041e06080c03010302060310030b09101a0a050402030a0b090c07031b0206031503030c0a050102031503 77
    0x11342071041c1499580110030f01c2c18894520310340c5d0507840d52030f09a18424003900e58103105140095848609003405802e41c6c005440c10424844113101c02c00001c9404074020552004011003140d4031130f800b0002a44c010b03d1001801d4072070b88040200001c4580018030051224020381354454180ea605c0500c4050325010302005103c00c1c07500f18800c024403c846941e07079408200380d002040520812510900c0c43d000b5500900c10305020760701d4810030803043d00e902d5026081c03e1030000c0301d03031a0010940d090740c4010300c4000c1c000d0f00000300140c6c00040c00322140d070155600021a0081d405c107041d00c156100001100c1ca00c82a01c3d0915140d005040d800346046964000f51418000f10301d0001000020f42009003e40380e5a41c4400307a0302c030181d0700e9104285c8602c060201e46501c2e40c6085c01c00500e00d00310030701c80440040b100000752000da41c03010b00b80e030707442103006c1c5000c82c1c1211844046403c0d4003c040c0c50000d14442c9109010800c0019009035104030307205e19144180850410400d680c486903400e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 219825422 1250 219824172 219824183
    0x101512150b0711030c1327031e031103070c0317060315090309040e070305010606031127150d051005010c030f0212041226040510120f050105010807030207 68
    0x14010003d48040d100070450711000341555001c06028002c103414407000c0c1c1018500c140d40c1d031026001c040401e40c090012152114404030f2511717056a0240c12115910480348990b010b41750407500551098000c0100a140c00030711360740740d003001d80b4041c19558141d00700301d0104031151a142031010300701441c28030841c401001400d20111040240184440217401c3c03400a0004002c0d10200c4d840d64046c840390840014001e088541c954240282111940d4020f40e04050070302c03200c0c224641c210415110490f00841c282c040c1522000007910781c200f111460140c00940359002c0f00b42405a410160000c003455400078800360781e48001b6542c0412150060030b010844054800340420300c1040d51a00744881401142e58010000c185819190459840400303508210500c0c1c004100030075100b070300000540b400a412034096080e1080c12400340340a09801500c10350400030004d0b104201d10310032581800801c00100030106d080c04081c01090240c0c9000c40c8210f004902818824422207003500e4011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 219826672 1250 219825422 219825427
    0x8060603160612060807060f271a0705010c050405040b0d020303030a050c130b0d0e0a0507050907031d0f15040308040b0408040e09010b01030e03070302060f101512150b 74
    0x8040d0355003042204043c10440e9160004910900e0400108002e8183d43d00c481e811a8501e40f001800304210494440c0b60038003803403034000c2e8448511480819039442e5400e20002e041020704d40b041a02418401510740d40c2007a01c0d02c090035403c20010002c1d80c0083c3c0c0d09111000c000000e00440d404102402509030b03004000040104401c0ea000c20b4026000b00d8295241c01403041c50001e02da00302da04849241c100c00983c0030314400722071160301c0c44021940094014500079844007515a070880c40f6590290601e01d000441c544d03c03c0d849009a50309040f0324081d80d01c11030b45465035403d403200c80b4640602c03410504801c40d007009000c41d4400d917031655542880307685650f1800c1c4c2885000c0c000315640e010901021480d1000c2808030f51140c10603000024495051100040a480f135681444290b41c1082299101080d03011843ca540145d000d2a26042a22040340c400c04c40c072225885480b0b90740d40b82210315009035120030204885814803400740040840500002c40b058282d00c50f806035074404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 219827922 1250 219826672 219826679
    0x71419023f090d030f08150d02010e0402040909142503201507050601210807020f0a030503071b1508091501080a05060c07020a0303110c13060806060316 67
    0x1000c281c15031500ca80020141410b2203a40407441801c03c54808a0204402101680c4200d51001c01c040e404144c2001e000701c500c0352040400c2c50f441e0024006410480071183d001015101c40e0111402400d044404201a029604120030ba24001d084a940c140c080d80b0901c0700e0800a2031804000b1140c0c54014018142c9940d860be541d10381a501115445401b000000c01c1a913520840030040c80e0680070304583d100390500d0440d051440503080644801215003034090071181650000f4690703a032105c16203941d84005e0001810364042e5030283c41d44018000e401100700702010024100140c401d88203440818103d041c602010881402030710300d0101854840403100b8403402c078684d00702001c0c400303a40c80711514180801406000742c1140925601410507001085820803600b0b0b4002840030240c0d040c048a540020004007071488003800300b00c00c500d240a0150300501148640c1c403c01441054030004082105014010314032507404940100400a1101d0030040b502021a00181828071b84803400c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 219829172 1250 219827922 219828013
    0x11d060103120807030908031312020a0b060d020409020904060b100e030a24050c040807060e0f15161208090c150c03040f0305030d0b0612040b07141902 67
    0x100403c000704158403206c07280c0101e000c407401940140e042c04591202805d85060242031004088215002c41d8041c5103080042441c0c0f50700b8a4100100722540b9414a101e4000070b0040e0070352a0010b540702d00307100d0a05c42044282e0f03010100f20281600d4614142c8044482a2141c2550021050b0550049101003002030401140c00c41b40000118042c1820038420760318400301c1e0345c201d999010035600041c0500c6204410030224004000c81c1c9841a00400c0b9080407a5080d070180c04202d006000500c800c059507081c020540d490120b40260f92058081c07203080c003a850402d403903c85808610500c0100c1c0681c10f000c0f890a20040000d00385c0110001030706202d60859004040040c2680814000424490710000340f413030040d03000e08015a2035140002c180c004885005001910490742006644c64211005417290b0707001c2e0308240d03044c40710b81e200c80c1c0c19106401c00300c8100800c3c500005d03900403208407005201d070b41010581e0803142c1f100d52082c4092510090503040d12000c080301c800c07180f007210 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 219830422 1250 219829172 219829187
    0x302010309080d05040b06040509030c0703170c15041a06030d08040204060503030c010f050a0603050d0507231608010e1b0a15021e0d2a14011d06010312 67
    0x1482648001c3c0b400b000c0b10782d040308464043d101150400d00d1036083c41200e140074021250040340202c060351034040c651841c4c954801551000420a01c085030b0684260b05c10141510b41d440c030640282c0d07401c0c10342255849101d4a00f04c82c00c03580458890401005410251510b6101b58030244c000c0400070000381081c2d07615100100f08990041e294500856251000e00c049c22041003041b002103400c009800400058410050078140403d10303212080000c43c600041c4000c10142d182007250f13a455007800c0a2030245c40701061241e2030105039142c002c0107c80007560080c090103911512141541380c40c01e0700e00365400184080c425a00550350202c00204614804038040b0b0002c1400c2403c80da60b0004642c404038207444e01d400358002e5050000b0748961007404030f5a5034a1100508400e0000d800e019100c01441d0300b0800c4007088440c0400414503102c480c42c04a56089150100e0740f0b00c2100c503050103410309800c0c0c0c0c04551410f4148440300328001501c24141c4c1d80c8210f00d0329250030090700071104d04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 219831672 1250 219830422 219830441
    0xf0a09060b060c010e0708010902062b020310031209060e100e12030903300a0203090a031b0e0402060405010f18081506010f1202090d02191410080103020103 69
    0x241e5503006480055031210001c05201c03285400200d6848030240010b828881240e00c04915641000600c0b001a65a41d00710b40b0769004c0201402941071004a6200ba00444482101d07034641c400000d000503a0500e2000100310780c4540140701030400d00d0310044902940e030f0f208190104a0340c10b908080361600c0091030390316a0407460310340e00740440e0700d0008081c0f9603101003c01c6207070400251049c0e0343c1410b0000c08019005842d0031682542d1085441f01c2c110b031905051041c901c00071880035010740c400c1c01100c0340038000400d4a1a41074590801d0300c91400d83c43c0c0c04203044200c2d40300010300074011a044174406c980040a06092900e040010b4403007800300000d50003009556492100302101407035035a0007400c64540200211412410750000a10b009841c09050000a40502030304a0b0310021002d164060b030301016072100003240c04100040400c14009612424410708281d420303c22181c6030007140c14601c0d030720184405c400244001200e5640108000913a03007401071000d54001e0700a0300c84c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 219832922 1250 219831672 219831683
    0x103080d0e07030809040b1f081005220b0f0d0f05120c15070507020904060b130e030c160303090e0709030b0a020702031002090a0e04051002300f0a09 66
    0x4220484129a0900b079036500100c90300300e00801c1400701c90915200e401150042601d0440400d070380c801c844040500490000e03400c000d4807100158103d503021240000030100645404032492800300202880a0401c1031400303554a8034400010500c0c04ca0081e0400110141803102c151005031a040c0c803407032110f4025215481088402d591800400008000c0001742001030541c0d9440e1020140595102908030800c100b014841140540d8441c641c803500310340d110100188491001001c603042e028089e500c00c4004d80ba0ac100464800310100c0100403001510007902c8609c0507206c42c0348d104115600000e80021821502844000d0720254400c1c2c025906003001598265a0b5599810b0800c0c00c641031103a85402140f40c4007113080800415800032424035080d810031080c04003080508905101c0e44014402c180d01080602c80d0074050140139504d00d280c1903590380360891402243e540585400258003081102040808030442601401515100419140d640b00e0b00c2400020b050400c4040c0d44 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 219834172 1250 219832922 219832931
    0x10507050f060c1c020f03010e150616030206250f0c08040311032413061104060c05060c0a0e01030507020f01060e061c08120907030c08151503060103080d 68
    0x115a44100020b030310a0f4142c0080e141e69112a90703590406440b4010903032101c0380180000300d0178141e0070017078030f0560740c0400400741e2651300ca100024418040c0030b5442c0d0000b03000a19146c078810206603610303029000e9000c4074041d481d03800b60116a0015000e269024a030b41d290f480c000f040c4140d01884481e03200c2c4c03912001218580d214001b107075000e540120355403d40040c03242e8140c1024002700c042020b0300d58008280041e5051460340d0324100411495145901c04110000c0020380d52003103804a40d81d41a96840355141d00000d010140c2c0d03400292014456900010040b0300000e04032001c0c0c000310b60300e4035031003041c00d8010b4000d040060310756030660040318110303110010f09104a500415480401c40d819040003814800e041000d158810300c0d2501d91040703078010403e82401c0f550441c111034505105a5241403056040c40b9460b00300078200f1840c03650003e47c80b46c0000b08040002007039800c140d041d48442501800380c000704860b59405801410040002c50441000b410b0100c58186001c40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 219835422 1250 219834172 219834193
    0x20303220b0d02070b090105100e070c0803090a020906030a150b010c0f03030c03051302010915030e03040b09181303110f01060801150503010506130f0f0e01020702040c020601060c0201050705 84
    0x4072540000600c1c40201e6408900c400a00c8060070400780c0020241008001c24200065032005600b9180945c4010003100004201c000d881958126002ca80080381e00780c4a0038002c04858981d00c1095080c4d200e46010300c0414010729010603074406140e404003a140000e80d1090100300030b0403040c0442c6051268804508001c41c03400320712803604500c0380c0c0d000200d01c120b184025080701e0001e04515000c18140e083c9c00d00507604200f40400382c402030420800380c0f1a005904a01811807104404128000401d000071762070100c0340909541c4da000c441008520082d00c8201c45042c1040f00d4141180c403505002402081c090140120740414140580747d1994624940e1400c2d91440e83c00b07004117a45d46c4840d118a421010314600103450110000d005d18200b07880005e1f19203150003480301d841640c40a601054a2031036100c18151002d0100a00441c42034505c0a4001e400141069015030304200c03c103099a40301050340b034142c450f40c5d201c09d10004000d400442d11358000c081e0071541d5105009540c5c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 219836672 1250 219835422 219835439
    0x11040504141204050604031115040e01061b02060d022a1e010525050c010f0b040b0d050304090b01090e091608060c1c02270a05090402030322 62
    0x440c8a01e01556200025041c20020503250045840381c068841d8000d10091100f99176444c1100c0440303800031529000f811590000480109402040c407a1581c00050001000700116180038101c92303071a200e084041101c8080c40c8100240f6410080d4489000c020380d04016543e0740c054164100075081500032800308a0b41020300645c1c00c0364615080e403001c2d000325103081d03100c4481c004002c2001300070b200e1418074001c10140f10110211204150000814040040348158152117402e108a0000e01440c0c070420112401800d21204d8680154207119649445042c04d4440c003801942c00f800440c03800c0c2c80c2c03c0c060001007000408681c10018034020018001101e400d4546c00f8000c0c080140024420441003081070810342e5100034060b40000c1c0800082202d80320a0315118823110400405444a80e080384000f4440d4241d220400c40310947e10701a021561261100d0031501900c1c144074041d11001040702104007210002c5d4513610401103035001e840d010507c60490700025880f00b81540c0c40da1070303c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 219837922 1250 219836672 219836681
    0x6100804060b0a09020c0f011118031c080601030b0d030e130603081308060702070609050f040f050708090f011401050d110d030201051f03031b03090807090e071505030f041104 77
    0x4141c010317004904504040c07824003409141144450003001714583e1664214031501403078402820b50741c40b80c40640c0642d181441030b5141c10035480180c2e18424002d01c40980140d4080d1140d50000e45805000c10490403c2d0880d06070b501d8042d203c2550051b42c1c2c6080154100326000a0b042c056280c0000000259054028010a00113030321810075081c01e0503011840c002008103a0702c215441010100000340c0c10501003019500c054440f20b2005151702c020073b01400d4944c05d005a4a8908402c100c0003550248032a4020398030034080d40c4120158510150076102d15000d0f0700b0036800182d00400c5103240010050402c07600c20b0f0f074000c20340d02081002501280304245c0950160b511502001030800440010000c1030155000e040324503411520014000341c034800310744d5607030000f1511000506024851b4040100074800840f880c40ba1110040300282c201c4960050713486c803601d00041031006d22001400a0101c95549241c2556034000c6200c8840c00c01030000d4440d000d13500446940e9880314040c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 219839172 1250 219837922 219837929
    0xc040e0c030c011e14090d0f14071809050f030a08040b060405070c03030506030a0c06050706050108031920100b0f03060415021e070501091a06100804060b0a 69
    0x3820501119500345070410002a56581c104013092280841d03d1040d00071030300d031140e00c1c4e1a02021028200d0903100091082d08000e56000e5a101d0458041200d0900a5100c8511400f000781c40c5d0700041e08040e664918034040d50039100300030a0052143c0e440341d03200c005402d000e0000c8450001940c40782d01d04640c802140440060203010420060003401d505103a000300f0107413020800d61034040c50052820b03600100080800d500c3d840801e08030707541003040c2c402c4243c009416918141d96035a019040c7c4e40b001200302c2d83d90b0304050002078441c801005a42c2e4440c00c1c070003c0b42820003204411201c071041e1030302d0214200001001141360034002c1065100f400410200010983c8620003007190505c2288100e500c25400070042100141d1101101e03100181d4803400541c030f5140b08441c9000d040034410100e81c14100206e0284140a415006902580d0060611000800d82a0480604520200c5115810140c8505030406947c440e01802394814001c9500003600d4000381d0028003030050f29031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 219840422 1250 219839172 219839201
    0xe0307080c0c0114041d04030c050d0203180307031a04080c011803141c0203090c040e15090d020c100504090203190501060e0d060902040204051f140405010507140c04 73
    0x282000310550b00710503034003010301601c0314685c109032a28400705800a1428155128248204041001c01d8028018a4516984881036603100003040500039a01d410003c0044540c101c00000100c1900740030807400107036500905c460316003182103e01c03c020300c03102a0003203071003035005c1144111900003846000710000f003000d010310002103141030003000008035124540d03038090104086c441078100d561000f18000d0301075602603140da4072920414180480e0780c00702d03608181005001d50b00200c2c003251240c0413458010b44440d840d00c40700c89180c0d84601040440d000b5034480c103901405894805608049540755140541c0781c03a458202c08000d07030300143c1e8403004d8586011558440100305000319809040306250114180413450006088455400310185c400d40e55114880290b465a0701140c014000180c006040094590803200356000180c03a480c0005281d100031001c45005002241c04941f016500c080c1406d030b458a0f0320041c140302c1c100075091486281004085da40f00c6028a001111810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 219841672 1250 219840422 219840433
    0x9060f07060b0a0b040e0f0901020d0c0e13020a091e030c0303080402100302031005010302130509010303090f050a120b09210403030e120a030c060b220b01080402010807030e0307080c 80
    0x1000e015810030f2941082101c210284014400c000c455560541d0140700b03000000401e445e0b4101ca43d009118850b180b0444509003220303020b046030004110040c200c81503030400b610034038150050341280100c8c0b0421000071680306042184450414490340f92240702d0441d080700550766608c0141d91401a4011404039400c0700c1040309610300040c19820007440c5040035403075031a2280c0707040e4429019003c0c0e2418035502059060f16001c45460b10406040c000c0c160290b10358580c1400f81100c0d800388110b69400055400200b220b0a1582c80300007102c00710841c22128018030350b201646010010a1000d041c4104004101000b03808180844000c00c00c074042d5075030701d0450400401410105600038022080c01c07141d07160591001603280007558041ca00b0300c17a02070702ca1500707001030507800608503407012031260a031034840300d90540c00404100f408000c0085080c0e8100642d45044100d401a000c18044070004400c0c5029400400b4840540307010340340307001c0495a81001640041407810302c9940300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 219842922 1250 219841672 219841691
    0xa05032e05070f030b010c0309050d0f1209150e060a030902030a0506070e011206081522060b0f03241302061c0506030a0f1b050414040501151202040209060f0706 71
    0xd8800e00c0c20050003864030565451840c0c5009d03040d850740388122405519552004409d100c202c03540100c2d85544001c08034400b10b26000300038503511030340c0243d25190406d40c481981e041c1c0142c80580c0d005002030152401d0091002e401c0d802018401c6050307030580143c258181c0054814004544141115110300e071001020600040c140b4001c0211403c5080c13801c0000d028401e070008803170315140d00b030345180c00d2281d5516401d1703000c40801090410042e60b0034001c034400c01000d074101d45180d190540300481c100044100f01a80d6400c1640380c000c0744083e1030030844002e0203004110b64084940301c0202d8518410307901082080d4040c54641d0300014440482450b5003403140200d036001441180104074500d5140c54181c011750404034001c010f2040c03030303070305420104109848034000c2800030004c0000160501800580f140122011501d81d440c2c004495602030b0701c11040740c251707031154090082c03550142d0f0a0000035440908000da2100742400f0b22800c1d0803c1f0b100400c1c41038496035011800a80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 219844172 1250 219842922 219842927
    0xa0201051f0302090103080c03120403092408270d0503041a040302100906110703020609100c020c0607080906040f0e070206160305130213020a08060a05032e05070f 72
    0x341c1e070310212142540c40382040580d0701c082003241580c2d00310402035a035102400030245144079a90610400302c1c101400c000074150040c09a0301265248620402016450000045540424100364020883da03002060048070300c940c0080c45903101104c0c959480140b04c0d541c0d0705d819402c1c800d00c0d00042000003000704201c280b0704000d048007910103882881d4180780c0e4000e511800300111000d0b00325500c01040c81401856005600c1d05124605002d95800c1142030094440c2011958418103100302001c1c01e00d52802c0b88230720144140c1d02c0c0d000d0301d0340c5035103041000b1507948207540a036007400080c451020035565600090001b0400f080040c0500e900e00f440f50b500c0290010411415900040200140f10142c0c0101c003400c0c50081c0380000317103036603040c1300d981c50704490740c002030b40100c0450160342244840c0d50081260801d1a00c444041d59601c004000080711240515a0950003501006c041008030003103010800001c40d03226030410f220381c070b4080110b400803120480050001c840c455460354 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 219845422 1250 219844172 219844201
    0xa0f060b0d0b090603151b190e030a080307030207080f0a23030c070b09210903010b0901080d03020903120c010b040c03020711120a0605040c03030f02070e0a05040305040302060a020105 81
    0x2c0c0a880f441c0044c503003e40041d0716510701c0181d41c45060072060000f2000b8900a0b4600404400344020940350b41d205011881d101c1c0181c04114007203281982101c14603d40041d82c2c84c0c80310383c40100d1902e1607550080450107504564003c1b1910b400501c8111480c4034400040c01e1608204d40d505407202d00d12292850f8050360701c03c641810318608005001d00c8001000490754038170f41040c9c80c900107441c0d00c0030540c43d0000000c0140443c041c031882d40b00905c001e07500104004d8100718002c0c446080000c04200500c0000e12905800c2c0d03024500b0794038044e000c2c0d00034146001c001429162000461820468154402560103440365524829203c03240742c64400c0060070ba140b881c0031810030303000c0c1d503481178403405450406100f41d11102050a43d408104071444515a00c85002d0110741070501d0010720030011030104501003a004e4102124031840014944121050025458802d03156408840000c10003c4d2080c2d04210b4200000f00140c0ca40f02c000308400c2416a00028007403902caa603185140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 219846672 1250 219845422 219845441
    0x70e0d020a081c1d151207030615020c090609070e0303072603010b0901030f0b060d02070b060102030f0a0c020102070308030f0601110c0102030d110405090f092808030a0f060b0d 78
    0x120707010b9102074100c0c00010032100c1c081400c2d80caa66203075040c403d84026a009604203d400401851b04005d540c681c5500b00800715079000a908090030440d50059803105014001190008035080000303c40f0b1400b00711440e004030303032414054003410142010900f146d0124405441c80704140c882e14440c8849018048040d9151041442c01c550501503404514442c4480807410103031148591341030040d90303500558154000501040d962004510004041d40085109031074441c10300b0001096540048100c4080b5112050301300d2a00b0044281030302c1442111405a045218500b408000a80c01100440c090b07800c00344000164600100018400003480c00984041c3c1c1040302074841a1340c002080da040c0180c00900868101d001d24039102c01070090f940038562003071224091080180c41c8140340d601a0440c00e0603200c030f801c40803d852090b01110107644000c1503040e03011001140c4d11102440c0c2005032004041071078200c840341c0d0b03415125239801c10354a8180000d070709185881c881c40b64201c203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 219847922 1250 219846672 219846677
    0x7080a050402090c0703090803030106090906050a0608060d05011103041a07230a0c170307081506040315140a0501080d090305101d01060e041106070b070e0d020a081c 73
    0xd501d8542e000c202901070244c03403402000300200d0540105401400404041d00a21046135103d603940d1000400c5080c0314840d86003940e280c0308009c01e66007080700000d8159409a19444600d85410040c0698640c3c0b244042d526556070344030100510401200842c05140652812000013004103409030648001030407180a00040d0f41a45e01805001950800c0c5480b2a0f5460f5445218200007038a0340c1c0c000d454020b020184140010b88402d24400280d405440e280da01c00170b2a40d1142041801444035052099004000f44002c00c00161442240b2012a54196022a156a080361040301000080c1d48241c00292180d0041c040784508100d01c11845c0298600004060716648031580c030380c006c1e07134a000e00300c1e91280c00b4280a07200046603c4600806a0003c009071691900100740c90710066034115540307400011182c10500d454015540125080300400b1600e8481100c00c1e9050f419500c035140d004100000b90b0350250343c0c1e5610010040001c000600410b20708880700c4102510381c0c01c401000d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 219849172 1250 219847922 219847931
    0x3190c0b151002010203070e090601111c0206010803210c4605090f0a0b0f04080105010501090605090d03180e160513350c03010e010204142103030103080307080a 71
    0x2015804080301c03c245000b40d42800740d035140c00d80104c038104030b081c40b05072031407044000045446041207642024200113908fd580d5998036402d04a84a12541b926007010a0036600600128070fa2641103d07004104010340d546480a290100ba83c2d95107000a0142c10b442031452a02080d20800402010f2080034047d01c048000001c03030150840c0180b215140c052240b0070749102860301d0f010307102400b5080d100f1806031244144800480e140d07204d0300810701294249000000d2070f5000b091b12109403403035510f400d41003503140302c140a100c1c40300c503100741c040000c05400d00045885442d01003000d88404a501b62841c503000120b00003001061441c0320400c6020001682141640b00c0c2500a4550440105282264144c1100c000c3c544484c0110602155130901410115000808500c070310401d500a000c0e0030040390425080340110b100b0104240500841100340385000c20035030129042d49840300c400010075689223865a0401d81044072490400004e00c40880d400c00f4100341d01840002c030500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 219850422 1250 219849172 219849181
    0x80c0904230f2202130908041a0f0415020705120102040905010b0c06280c0e010e0d08030c070519032d0504120204140405060a060605030903190c0b151002010203 71
    0x150340b070f02000030516400703095914160031541c0b6408141d80711030040000b400030110a041120303c03540b0a200740c15a00c0340a107494a015a4204152202410000981405c161a29244000d40c49800a030310b401c60180c0c400120b0140e64070000d100301214018001a201d82c1424490001c8482c1038102c4184402c0a22a06d03183d80380000395254009030780c0d0001074007082503080c2240d440c0700c888a40c100142c01c1000b0640c02d142d020701800c2c0c5282c002d03a50440c0521800051050503000c1890184c40720808000140328800d60000a00d81c80e07100300b040720341c40c00300c0714100a0503d000c0c803800ca001890129904240d0a040006044180c41c00007426441d04e602d46406003d5210340e2052000128400028809660382c40e030041d15000c00040000e103291400340381940c1c0b10842181ca0402e0686483d030081403841c480d00c00e0b01c2c070600b1020002c40c07502100b001c20140d00c0e41e440d03142104101203280d81c03c00191611154a010350725205050200004803c1000208000520702c101160320500401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 219851672 1250 219850422 219850441
    0x302060d0e0316050606011205040c03260403050309100f0503070c030c0501090c080d02070e180a051e010c0f170c0c010c0c0c080109080a080c0904230f 67
    0xd600e6042445000120041c200c48214254010414450029050f1950340c4051100c0414a284199401d80e10b01114000080c00c1008407101a64098801d10344160b080c0001004041c039115005090400701585070400e61403070318039900580003103610740c0000c54254500d00304109009a003106d030b0b00741102d0000304884000d0950100401d01401c01002212610525003c0c04a0071500c40d0084001c0c003550b00e46003000139841c4424418140c403071040950b207541c042d1000c560030f0181c400c3d1a00b90700b0140c0701c4201c8a26403000341502c104507070060382c41c0340c40000c81c01c01042e00c8902c0300a05d0100001d00c00b1454a003101d40709803205090000340099114006d6205542003000101210500250b4591140c40a09400340150941c0f1070343c68025081e079441d800103464140c1a10441d0708a0100303841d407a04509031000c0d02c0f0010034000e8140038842143e4028580d05a1000300c0403852800e01c00201c0014065a403451500780c61300c140c446003500302c44e1406081c1d43c0e005000c00c401040700e09141015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 219852922 1250 219851672 219851677
    0x92102090a050604020712080411060c1f181a01050a1a030916120615060806090405010e01151e060806040c090e181504050a03111e1f06030206 63
    0x1c07007039282d4403800940507031390b10342c180c54080d13030000c4d0101ca080351400c1e0f02400050b03081c1ca007942c2020001130140d08900d0002c1c1140d0341d032030580d0003a00d02903681e500d080da044088250399114554640001c00300c0c0d16260b0a40480544c010402607018031200181c08508140c187c000c2070060001c1c04041c40006c40002c6204d01c01c034010000f031036890399100341c1740d030404518032500d41b400111207000142000c10b41030001c5540d402540300704003c000d4003080308650400d0b84900300101d490b810005506240c140c04290b4414003c50010a802c6944e200349421240c011900c100c01302d000d060300340a9203407a444100c01c80410240d0b11202c15003003940c0905019002015144282e4440b000006c42c5031142542400802c2941c04440e07480c10044000c0042d0009510811000d1080400360004c1c20300c0001c205e0700585c0c100001d4000980c06440803580d003400804585403511404107a0900311140d47c2c40f003241101000081d00042c1c685803410340c2040014401e400009042c43e60520150740d80c03808 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 219854172 1250 219852922 219852931
    0x507180c1b0302031201030302060702010608190602090d051507080a0c0225030b011823061e031e0c030a1110020f0604060c080703020a080a0f02160309210209 70
    0x7030400a080c052404a1a6100c0c0501c1901280ba144000100700354001400700e001e008182c000348074591310788030241d55448030f4101a031080e907401920040400c050394020000c6002c05484907280c80c0141d00c0f03103440d00c200840c3c07480c0d401c149001000100daa00250b010b4010b41d0300d842c01d000d920350301800299a02001d4020f82c01e07401c40e25020b05404410281250003c5a1110320604250381d11460f0f9902d291101c85185551030610480c208241ca032100c9034034880e580c12681c000f158075401c00f4490007140e43c0f50628050034007107010700310540d001c001e06081201d180010500c0c03110340c085410300f0000403900b21802540719249043c005078030800340e401130070b0040d500003280d0314618030300701e2410440300c40401041c00781d0000d1106001642c0c0010505914680300d65540c0c0e203601104078100d1180301e080c46c0c0041c8035040426018041d80d0440c841207840c1c041701500b081082c80a058508841c0c08084010940b5250308000301e919005e4510310182652441800540303203600481c068800090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 219855422 1250 219854172 219854207
    0x12050706080a1a011218030e03060901150b03060a0b04142818020405040507050d060f0f050d11040609021e0a2a05190b18100c030212040507180c 64
    0x282d6400030255544030740c0906c61b04080c88a4240d480e420050200311040f1582c0d4040d015540010399000014090440c2c050740c08158000c02074a8400640c001e44c002501d85940900070700000221140d0700c01c06000a88102c2100000b84112841003090700c43c01c1c0d2108100d4090014a500001e02c00c81c0c01030411240304400d400b0341d41d0100340920b0000d00c1340c1d421882d4001d26280501200e5680140905a000000002003240c40c0d243c84e40c01c2080c400501c12a4910325006d0420f01050a10048000c038191145007060603813a480c1303001605880365500007041186c1c3c003284454203031045007048195004460049841c0000c4180020f00030044c0100140802c1e440c0310440701d5080c0c070031018014540d008030540b08405240708004101129642c2d013901c0481036003000c144041d00e03281ca1041d04000407002008810030440342c0341c01801221784658103140c0d0038007001828a1000a00a2050b0b00c6100074142c03003401d0000d440242c9480850300540c0c9850b000c0c066074000e0300604035035030000401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 219856672 1250 219855422 219855437
    0xb01080c130302030604030305010302012006010b0a180b1e03010b070f020a0b0414010e0906010801030209071b0f141908090f0310060f05030a03020714010912050706080a1a01 77
    0x41101d004003242603000a405114100401003410383c160712040c16030b4400d90703403000d6072254401140c43c14a800d00b041c032038581200004100d003c840c0c10050425010604008040c0c21650403540d049411503401310b8001480043e4036801c92075843c44040300900c1921455056504100c034030300c0307030380030381e48000306024442d500390015551096100001009448016903817283c803041416440740c1250441030110703110103c50f84076888e000000f14403650042c1d4403a02260700e190204603509402074030340400e010301d8010049c403110304440300c807051602814580302c040c031702403a16030010114144000c0042d00601c200301c0d101c00e94003010145aa4002004035203803110207001611f6050130010703069241c40340507144001500307143c001d10220b40607040c08104055490007070540703e892541004005800c0703c602030080d00d04501600021000616107040e0b007e440384910719010401e480213460303a0380030000030400e496010240325842000401e05001c82c1304240b4140001c01000302800c2d05001d0700313 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 219857922 1250 219856672 219856687
    0xb010f170a0507090806010f0612050411010305150a0e0610020120070c050604032303030702030f130b04080a0605060607080d0b04090204050a1a0d080405120f0a060f0f0b01080c 78
    0x10700c000001792001105a4545503540c178150100f403d8544103170008502002030501d450000b078440c00c5e11558101c002c4040d4104c08000450013040d00030441d0100408039004200541c88040078080036020001d040462410200100018035844150400c1160b0400040c03c010170780300d000d084075038400100005e440700d085150002d840b00e029006103820110102d400814087c0021201000121010095100d40200c46840e5207074481122004c001d070b842009103100b030cc00004020107810b801d403010400e00c5a220181d00c905030344a6800024507030b118000080600c8561301c0349a40000040b00c1051812a0656803000036018860a0f150155513078280c0c101c254031180c01a14960354001c00400041c9001c0c0e8ad194001c4c414055514241a104080c180403401c1955503280c0c00c607000101282003d182c00200300f5103842804800a0350f004824405410f10300c100503130150144152000314410404000795000c990150b0b03c401c2960b0300f400451903da9801030b2007641c102e62800c02003982d5200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 219859172 1250 219857922 219857927
    0xb0310060602070e0717390912031306053601120e010903050a0e0102060103020904290c0d0b061306031a060408010b0a0e0c0f180d060b010f170a0507 66
    0x9039850700e4450182500c04001d00240d021f41c0401058581041d03500c12a01030101003101000680c84034800e05c20100710181d140e1401100d5102041e07642d000f228601110301c8007002ea02220350380442c0110310046050708501032601d2810018111680003400708000300c40c0000520461001501d05105211411500100942d040845400520170090100c1c40e0070b0f00c0d004102d6404540f030200000c900c4200005550700c00b140107812a81c0007007202c0415150340d2580d40c0d142c902c041d680f04080c0000341d02ca6016030076030721190307220324511090030707480320101101102a5989140d400d40b16403410446001c180c40303a10300c0202030f5000c6180001e00345200341c100e201c5c5805485803450384030b1408100003604841c15000b5405d8501d09030740c2c0c40c03078503660380c00000711440040d215840d590000b8808030707401c010700c1c0e00501600003216a40d2581c8100060100701d001a800c6401d8031982d0316211412119600300301106040d810b18038003900a2100011307079010b41130380640f0b0b0400d46915580824070491 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 219860422 1250 219859172 219859187
    0x405240f011b0c060210021303060c0c0f11030705010e09040308071b21080709030605041a0a020a02120306030c121219030f020717070212030d0b0310060602070e07 72
    0x10ba000780180c40002504001125400078400c0000601ca80c4019017041d20740c4d4000d88034521712010014202504695681c0040c0034001ca0300b8040201800d14080454486c4200c000403d01440d55800890810010315007030560030780109040c001b07100f4100030075407252980c0b142c1c803030381503d0501000e84540204440127600c03500c18004001c0c00c0396059050080d44426030494807110220740818051000c4240c9217002c003141d4180210300441e2040001c0303183e580100e83e01510400010b2114042086005141007060381c010900300d6000c5504442c0300c1e010024005000441c0050b9801c40c80c0240c0001d9661415401d264010702e184000a4105c2e1401c0000048410004815903101c440e80140c0c844500106192440064204685e0b860f032591144200c5040a0700f28800c450040b040f545102c809902649049070030070b0b900846201e03c45402c0c0058056842e6242005c81da2442c07200030580b8145e0038001d508007043c6880010402c0b940c0025150084441d400b062031800c2d40c0b804020798154 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 219861672 1250 219860422 219860447
    0x80f01060b091c080c0f060a090b16030e0712061a0f060c01020d0203040b0403140a020a0602090d0512040911090303031302130507081e1018180c050405240f01 70
    0x40101043c051503948010034400c0300001c6d11000c0740e2a9a03500d03078400065401510000e000408048041294070b0007002c2c00400d204142c4c107011490f840f42040d80303031900140394804039241c200c9031802030400800c3d0186c0b460700e242020301302c8801c954900c00035002604154900b13120740300002e44030410389801c0d0103641c1c00d40707422901107480b441c007030a000405c0081103904034009101c1c0c111100403c19203d041d0350389070744958010103501145e5521a4029408043c40c19401590a04d00d4000100b0400038001c20300030300b01900d5211882c3c01120703001c1e0350b210350b540072403908203000650040d01c001081e00d1340101c805c0000d034490481030021440a402e0090f03111113450400040102c1640c101100c64003500c0740c030644030b41151044800c00c0c05100b05a4582f507220f090f20804000c1a04140c20030703400055103c1000a520480c1c0460240111500d802100c101e0032198041040d880e191207400d0344454500721007140e9401c0d41ea10100d00c2d00220054511132056034800d82456403003000400f002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 219862922 1250 219861672 219861683
    0x106050c1f02070b010e0408030c0304140a0507030b0610051e0721020c0409051b0102191109070e01020a030804170318010f0204050a060806030a05030a0801080f01060b091c 76
    0x4075164402880694070442d0241da1031841c01c8000944000b02c0002076104540000e0010304544403554441c09990002d0030583d101070324103c5007580100c1c14808000321034403500060061781c2c0380d271802510408004105074401c080d44480c0c18540e80d00041150b2461896242103100c10200380c800400f540640311029100104c09141c6030060089070042d0302c02c2c0c40d450f4084496500d41c04040100303030f65540320014107a030031841c1c04071034002c1c2d0800807100000e0705005480618813a4800c0c14000380c0c51100c00d84002c59288601100e9003085104540c114095280c9040a45204070003c1d585142003800101000180000101800400125000481e145000305941d9040900e1060095100c0310090031055117801030740c195285040c13089038200c03500079100006040c5455000da0324078800908864260140b4a403281c001030b4144010800420561030ba11859414030b20070314500340030358070b000500f60300d0b1600030310005036050140c800001e002c44800c0710910700d0341150420103420300b40c010b21 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 219864172 1250 219862922 219862963
    0xf0f0c120a021e0a02010e06060f060904061e06140306010503010b031b04030f03021510090b030c090a0606230d09031704111206010e060d0224031b120106050c 70
    0x10350f000260040108100f076a00031b1004900c40360030251601002e4410700c2d030004407100740c0840f82c14038101034120054010000030b0010360300d8001303200508846946040030369001e40140111500640200400d40ca8031000c5411890020300281040c030041c0546c050245002c0700044074000c0b003905026150f681021510340b120f23520b14103001c01e40d9a45104030058080e142e0518074000c400c1d1200d038459041c90007446403007850b00c2e0740c0d10000c02095a250350036000b030341c5101c14030761141d00802d4000c8150510008100385172200c002c08100305860540483c0310840e213000b02e0480450f081d00d103128008080001c40c10901d242c240d503075131412201085440184005c1105001140280c6002d40400740c40c404110060310710f4017034980200b401090300208814011407114100300700d4486107907101800c03054601901180d032100c0006049003c0e5400c1c540001045080c014010b140302e112011404c035039050400350f60964120403814002d440800c200403036001c6003200c1c104100c46d202070100e0b10041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 219865422 1250 219864172 219864217
    0x6012d0519050a0c02060901030b091302010e0d1a060a0302040c1d010f050418091403030402031c020a030c0302100e062d041b0905070203030f0f0c120a02 68
    0x604a8012440108100c004004038500082c062030896612081d04d0b5940340360b90005600b0010b198001000e1a4105030361042903441c2a100c8031042c03030062110500b08185241355200041c01c5005418019000e0891141c0300000204030603400e04900d00c0344c64140201d6680d03c0301060241a103030740041d5120341000c2a44040c9600140c2c076921500100c1400319502c0d41c1c0340b0041d5141c2d0600080c03440041c00c1000200144000441010300d0401d40e02e0001c11000503980380c490340a04015801c15040d04004103110452034200300014458035000c00c1e00d0f0b15080500300c081c2d00c48010300406001d20580110340000c142c801d00c44090b95040890007000b6048003096102e83c0d0300c8045a403840070100300c1146400c80c8001100701408902c0d04105208250b80729500e001402d500c0c2c0418492030020703048003142000c400e01429100b4030842c1d00a5849141143c0301d00040007000c1d0851090060748001d0042002d090360445065040f10b1510301200e132039847c0400024814040d000001115420480c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 219866672 1250 219865422 219865427
    0x30f0207080a0207050f060f0c030d11041e0f050108130507140906030604120507060207020a030b0402010824040b06120906060109090b100e03010b040603030503011a0c0606012d 78
    0x10035200c07980f41c2c2110703101034941c000d01c440c0da9028100c407544100103026120f042d1004a0091071042410b006a07400c000c2c03400d92400a40b0906840c0d00010100454280811403909000401d5000d1020321345800320b2600d0800c4159096500950303041004d02c00001d86502400c108100d007440e030050455101541d0f480c20401e402d05001c00241c0300c0c0305040003040e0740303150024065000342d030002d100c1e05903d001510180d40f1513200744070488840703400340900350242c0d40d80311191000307502807400840d5a00c0d0038800100b200c1001088800600c903000110014160401400800b44074180d90001700e164800e00020342d2405812020788401c805807080003d802408500703d0b004120a884011b00395441e542d124064400f41c112442d008944525005031280c032585504a44100c083d00000c0d103682c101020605490a0350803c1d008900f0000040101f030045444c41c3c040c4441441c001d074140b00e0054519a11031030090050340c1008200c043e901c045600f507080480d0f811400074140712004440030340c007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 219867922 1250 219866672 219866677
    0x302090a090c140c1b031e06182b210204030204050702060717040602121302150705120708041d070315050f090709090906092a0902030601030f020708 66
    0x110030000d003041c80364080c0308403d04190ba040c00d5001005d06406007403000c0481d840725140e20350799854484c56040c03265118001c903011380d188101002500080c07501030041035003185c000b60780d58038980c4159461039140c88590440602c100410300314200c0000390100c110340c40400e94908040405070680c4204825200c0d50091085034400c0d2030a0000b5500d04909036211002180c410300801c041c0e0a06450005c009030302d40b03a1152281c04010b0030001d40c04048240c203501121404040914813990605618061844610841c80d4150755480c2c540655a4a601d501c0010410310100710081504030402c003018083da40a0504d018050314500f5006590604130354050b2a6507010038a40301c500315a9203001e0b0864810380380c000d1301100762071252506110038000020824010421a400042a1180c807401145e24840c0516800b10318541c06003840040c00c80c520300581c2a4050b0055081860ba0100c804401100c210000050700d13650f44d42c0068018018400003041d482e4800269541003008a001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 219869172 1250 219867922 219867941
    0x1603080402030601150f030b041d10050a06030203031617030a0c080c0309070e060a08010c02030a090503030f09090a06091503020307090606080c0d060b07030504080c04090302060c070611120711030310050d030302090a09 96
    0x2f0140720f96200c2003900703421038115010280d050b4004000300c2c60014080c1d1036030400140309845da040800c0d90a41c84d81002d401c107480306040c0603240c60303041e0409a80083d2071034001029140680c61820041c003215a00c410b103108648408200900003880c2d070303680e80285002002a40000e000640ca410402900e03503001c0a0b61070f012031850700d4081414240002980d01c41c80c2d150b21135520300128001000500c0c1c0f80144102d000c592100c0d004102c0910901030640801030310311684404500754410903091070000d800c00200645022020401c09030b10280303094004150b001d0041d070310354a60b0500300141c4010742042044400000fa02001c00d54807a0050040b02c020310240c42c00040c80104000688900801c05070059100340c010910034140702006100c2d507440350750002240e90754080303e65080e400c01d2500d024000f50100c20412029080810030a0b0701d103050303000d14910f240440c2400c41b02c1c16640601e40c00b4032001c90518003094000ea044450801c4000d2803402500e59070460903000d03091004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 219870422 1250 219869172 219869203
    0xd060608010b04060903230a05030d23010e07180b09010e030303041109060f0a0803090f01080903030a091a1306060605040303050702090703021603080402030601150f030b041d 77
    0x10000540c00c0c0d10b040a80d015a20b50340d0302c80d46100d180da140d680c4c103188100c144841210a0b00000f00d0445d500708480d0000d14031400242d40c8840118036240304030340c0c03284202201144142454805000e102c107486044d652a0000c64829813918041122424040c40010104840400020a00500080240c000040b0980e90804c080b0100010b054072400285c40050240c10103ca01c03031759a2034240d0710b0075480700014081d000c0c03d41f06100002d10a6640d80d010301000d070400280d29506003040100886801d0080c204180f1900740f00030300c55a00d20004010709542a40e4a10f100c00304000f880041e52170500d0f45841440c00d0901c800d101140c41c0c0c3e121422a005440c2c00c2000501c03a000f0f00c1550100c0350941c4540d420082a0b4007807103941d841c01040142007540c02c011045a1144807070040c6442802580d4940c105d20b082d20503d450808d042e0000001c0115000452300b507107512180d2102800d0540c80c010404084103001318000d8440c1000f034954a03080301ca0203034400100040d01507110031407070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 219871672 1250 219870422 219870437
    0x80d0e03091306030c09020a0e1014160b13020310050703090210020607030f1803050f0405190905010b120a0e07030507061110090201051608040302093301020d0e060d020d0606 77
    0x240700e01b80403445680e40500c0031891302d01003070310303185005485642e10b41658107101c0240302c9901a0802d00d07a02103c900d0900400034010a01803082c8844201d510204129042022000d00d4000a50f45c0c1e82a900482d003264445d80002d40040c481e8020b01d80e46540130f00303e98484c2a81000203501d905c0212800c10001e481d0503400c1d52411818000d648690f05407500905140004c8d84007124035620900c3c25003051003040000140319180d07400d070041d500e43c03a64180d04045003014a07000c26200f040c3c1c846000d440081c805881d03200c0c0c3d616403568000180c280002514010a500c2c0ca060940a80c4098480e000c3d145001a41d10340102c00850050101016100e04c00d5010a10404480d034440020740003507003d1004106003c0041103e19001e40502c894504180c0e599000803150681201c00091004041c0e40c050b0705d0300b1070511804010340344140c48400c04c00304500000d546601031000241007104402c2c2003051503c511007111283e41e6050820341d0f407450540c00000181c03420b40714807000035000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 219872922 1250 219871672 219871679
    0x1101020c1507020d0c09090512040e010504020304060e1209100c0809060307020708060103080702041811061617130602060f07030f020d180302010b0d080d0e03091306030c 75
    0x46110300301040028444060350308180052025500140412a001040d01c84400d005c51601301240000f031002d00c00214903a0f00f01d250080c00c00c4210265013400c040e05120a200c15040f054a06040d0349058400503242d0341c55040c90f8000d02843d983d40701d1107004851442e81c0d1009101d0007040d4840042d260480001c0c40590304940382e040c503203c00351180b00e06000000c0d0928090780116000000f41c8100c4503210741328450642445800e920031a045900012401c003181098000c0f004c4a12045607401e03201a01e40d1611010741d100306564612810300021000f85c81040840e20112494000224000007148007112101940c004c803070300300c001600c0764000104a0301c00122140309112501c07080f0000d8603660390580c040c203100301c08001419003d02100c413804034980714442000310006190444038043d400d0107406c6580e80c0324024000e807407103048240032858110807070360964103030a00080c5060640d0103040c151f002d1644291b901001d040409402001160400c030f05880c05044a5007000ba03a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 219874172 1250 219872922 219872927
    0x20d0606031e020a0506030c092107060801210303110d02040302090105090c070b0703060b07032007061403060d141513120819060609061209020108010b0a1205040803041101 76
    0x40c00c0c20000d50002c0d4400c005d100b00c0c2031102c0650f4210381d000111740d0030490100000354440407018146c8040030070315001c6131800001084281c0081071541003083c07565040c40301e582203000080040421303110a242d624010103209030300603e100d00900302400c2c2c640803045030440181d489032105a2090154600110300340ca0903100d076500400d5245101032900d000d5507202070421000500c10300c28580d03039501c00110f41a0340c00082014a12135520702e0416408040100150008030b800404d007944008424030006821035190280d118004030700d0754581d40d5003c001682040e0b01400140701c0082c04c0f00c81041c21000050380501c90b1000350000381c45a88040d02d580101a6286000d00b405115140d46050140030f00e00d0133070014400110b281d40e5091482c03409050342c405502000004481c91001c01225038400d54900c1480007412043c41252074a80000b407210700180610103044400040d01c1c890a80122300490300940068010b1060385060f0521b0405074000f1a4283c68000c4400e403510901c0d031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 219875422 1250 219874172 219874223
    0xa110607021b0616031404180b040c170c0711030313031401090818123301120602031f0609030c0b0316030b040b030307050c01020d020a080a0e0d020d060603 69
    0x81c4e000302100c60000380d1012124105481d50340101294100401f1400e00a01c04861074902d06120b03010825010000611045405a0240070100200c10401120012440521035085100408100e03291001c509102864400101c1c580364140320004181404100766981c1201300d038080c1c04209044055201c18a09a64040d80c0007420464104000021f11700302844a41803448054815810600c120360214640004001861040a01600c80ba00c0008000030b41401e0400c1e40d40082030194507058400b11f07001d0444800600b0790341c000c00051300d0f0541c0c4194032401d030900003c0d03080130590350308000f40035a0080c0c0030070b848040c100c10300800e20825400c00c0700c1c0901a40000d850184506080840042c40020130141d40103441d800c420344a690100043d1002d030b4040d03000380c103081c290031002903d0000c0c0040201b0541d0451465040801d8142003500c0d240419820304401e141c017481d00203a510100d5200080d804010000b14005101c00b0b640103a00b03981c880e0542c81c4d190540d0030003000c80030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 219876672 1250 219875422 219875437
    0x182109090c0311030a0509070f0303120209040e070b0c07090c0c060e07090e010e0d0e0306010611070914070207050301020f0d02130b1617041401050a110607021b06 72
    0x51500204104110440d800751030300780c84619002403050a2541081001e50082d6030304e0842589030014041510024091030008000340311400b4492407075a90060b1044140004410f000d99004c150310a09032076a070004181203088000b40e035503040d1680d4103c6002c0d0810340d10b401e074a00c106200171501000e90720919001c20000d4460505004580d9203120181143c484080c490703004094000a8168042c080da0400b9110180040303185074030078420038a440c0c0c09006110401000482501041e1004541a41034a105140540b6984c0010030041d250040030340c000e101c00e5181c40c1c150811007405e103040c0c5006104179400e42e0201039468040600780d008103a42c041030120100130710756540e4a260f0048c4250307003448000d90455540c0f900604c180d500294803110341d5012a42c03d030001c01c80190103400c440c487c0002000e040508085059101c00d103e00f95840c140200003540c0e400f81400b900001a0400c01300e03048454910384090001e40303a0f00d40c001d000010201651054802b1b01d880015a9101c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 219877922 1250 219876672 219876677
    0xf0615030a02071b090b01020f0d2003090907050405030610060807050a020c030304060206010f0f0308070206030612010c091d090c01031d06040b04030e0f0d02040e010f1821 76
    0xc580341c0c0301c420070095009090031100e031411940c050f00911100c0070244002c00450310000768000b000c0340068102441a1002d8001d50003440c81081295000346040c4611400b07000054150501000c100d0726500ca5080d020342d000c0405000c010f00564450f0081c4162034068058031555126000c030240b17100000d005440110345002d0000d00c0107841503001d042c110712284101c5444d94400c50110703045a000e50050b0f40142c001000500002d1b90b4a0b1040d0000d1400901c98a902440c50300c032802107020304030009220300e80000c040380b0b899541c82260b0ba856452113000300540c440100c40030702451481d2180f038980d0960450102c0210400441d001c0c45841e01d24080c182c005013442c0110001d0007040d4002c84a10390381c0058401401c401c100152040d41b2a54041640b4146030a0141003204d40d0b00003641309844200007081c1d1a21840c0351000f00702e6050350b0108884503440c01c0c1e140549041045000f4162405500304d4084a28101c041080c6002d100c62101142d00e205074140000d181c109203401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 219879172 1250 219877922 219877927
    0x30d02090418170c12070b040b0123040207230604020a06020c0a1406120c03010806060d02030a0209040606090207030905040c090509040f020118080a02130204081e010605060705060f0615 82
    0x102d00d10801c0c024048071800400740c407901d004041c00c01c0816081880c082d207c0000315000c0004010181d52014050450411004007c800d4904035041c5c20070006145405540c01040d04010049404c2c4c01c98240c10000280f071082103007020f5200d6640204680c2a07201c1c00c100640051102c0c00401c0c80901e041c80a8a4411100c1c00c00111b082c400c00f0321084550019402c000115040e032443e850303139004881d0f20300c1e15903481d4584440070345030041c058403080c422a031a00203c03005a0f0000b07120341d01030391b040d03681030341c655502d050030307002030078a607000c0100540001548810580d2200003d029a241120100090318155a0440300c4101302d010300d940082c41c000110300403c55803e0342c000802c0c4149483c2e0300000c0c0d20003a605280149500c46402c59000003514411468036a01000da9988980411401c1c28500002255100c5800d403400404440442a1180c0711700290010409002d0240c005980c0341c0f03040c6043d583e034550455000f04c09103840804100140b401c49201180b000715104902e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 219880422 1250 219879172 219879203
    0x30a1e091412092404030b070504030c081203010306050a06030606060f080a0b091803071a0402030d030905060c130905010815100302030604150f060e070239060c030d02090418 77
    0x113a50352590411040801030a00c00000020200003415210728050760350141c5643c40e6107440c0d1030341046074014030030b20b80040714594007242e101c2050760304494102902069607210242200f0007865160400341909c1d0070624081421508100c4c40151000c6d603590340400750380c03100485011a10700f402e0480d8030047d40c1001c15501e50f040c545002e440f0f01004103503442d100c035513070310408090a0484000f490401080811056140a204800400030300342001d01c00d0340681c1d03658a880708001401040a0f100119101401080e1403a0101c040c001950041007030b0b50310b440106680d21100110341c252514444002040704040c40d1080d0202c81c2e014009101d917455039541c0380307052500e803011007565503900c40c500c1401c0300c081e000f20740082c00002c845c04a1828158030003410404501102583d6404c00147c0b41c0007500d40f11025032000845080007500c40e03541c1000504140b00d1990105054480820000310294042d8010300e2004000ca504100e419682d10309005094101d490207800e140820600c01c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 219881672 1250 219880422 219880459
    0x6042a02011d1c030203040512030405010501030c170c011b0c090f05100305030423060a09140117040f02040219020102030108011803050702040519020f0304050c0312030a1e09141209 80
    0x1507030010300c030350203451403060450049c81051b00f080f40c040c0d8240c0e46602c010403d00890384584009080b40a84016082c51030800c80380e940d5500c0c5040700d041080f04c5400c040e02901519900390007e5010180c54002c80d03584c24000090195000c800c8045850040405c00942e03240c5d103c40d04990380032002d5070a16141a9506034001c1300c81e6518440f00b0403900040e403c541d5154010301c9521610340710f16070307a181006e004048030100c40c64200d040c0304441c41c000001e1403100506ca036100d648000d011b91160540c0c8041800b07801034960010010145440380c000c00d039010f401540c140c07407100000304240441c48080720a118014500a800b02d8001c00503000035051a400440d4088003503401c0d00c01c0c6008401c0d40a08070f03484842c0c14000b0000100c12700042280602c008034228000320010a0f0020040c02e44d612140b001a100c1201366603507106602c0f001090b415079013018400f82c1804c00510704641031007083c1e181d102c5040b08090199075078900a004e07950040d140b1403540a80000151000e050301c6d0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 219882922 1250 219881672 219881677
    0xb06030f0304061403131515060302092d03030a1e05120f0405120f0a090902030903030117010e01110307080a0c051b010b060a0c120201110306042a02011d1c0302 71
    0x214480c40e04840a00021400000364418088500b1031f00080340e11000c0301c0340130b078503900741c00010406004100b840510b94412191200103403100c10b0034070b0112050148000d0f030942404403c0e4041c0004a034803104144c10020000c0c40340c54a0450308255485240201c81c24443c00c0b407064418440100440c50030302e0001e400c20b9210f4440c03c103c07411000d02150168040e049100d940c500c075440003481c0084180d003c02c0c904000d101c4083c046d811410410443e0341c0320700050140c5640e01e02e001200c510b03001425085004800310001c02001074880510410103a640b007100c810004c03450150100f0f416450611940301420400c0d80c4160030000350703000440080140d8100719529640300c10550f449661100020540c2d1605130f191074418440d50700d041300e0f4003802c41506105591500303180440c01c9a02004580c1e101c1000c032000190402171003811421640c00c038a60401d2a40700b40418040240c05500607209100d200c3c10b40c1e9030265080300d61540e6003a8801410a401e00070600405059010307030007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 219884172 1250 219882922 219882931
    0x2121305031315020c0607020901050405100902071101111614210a1e050c040f0204090c02060402030c0f03030f0a090503030703030f050c0a05030613060506070b06030f0304061403 79
    0x180c03407808803200402c0034091015000703108122182103140c2c011940410103c42c2288085d641c003400d042c07145e00082d904103414465180a6030312000007440600d0001f8000740500310010b4115118291030400070307541002c2140e0540416180740319048030490006500101c6480d90003000c1809003410380b4880552116509c0d9070700811401c8040012040c1c0480c0ca4110003d980f0081c1011101d0b42010b050110940002c12185444800000c3c04034001203035000202e00b06031030200c0c2c42032144441070003d01c960f60101c1ea40500d80b1600302c000c95800305186019a0084003200c80c1d1a02c83c0d000c02083c40c0c00008020740c140d10405c68030400110b41d20280c180d490075410031001c40c95846022030704550022908400080d81c0c0c05100209805038410950899503080d119030603c19840d40c050701910002c0c10b0345118951006541c11003000700d400500140c00d01800c50b0751070b850946046501101c0960720b42e4480c1c01440106038100700004180d404980317040d070315500c5d94072132070780c2c1d00c9501e600161 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 219885422 1250 219884172 219884183
    0xf040e0d0f02010e010f140105040203090d050906040f0e0a0b030c0f04051801050403051215060a2118050c1e0105070501090b0403050a0e0a0501090b0c01150806060a0603021213 78
    0x107484220800280b0030514020304501010950b044a18011f9400e61416003100e40300714414424880724003000207107481e06210605121b40e0310180c9000040780b41c0125070002c102c040701d4050110b5803481c0d000c0301901600d84910700348160601c00303081548800300c0fa1041c0d50040781505801e01301e490a82c11960300021098010510410003000607401e517402214140c000c140005143d45030714500c2d0004a030f0101c01048030792500c001c90000a4032a00c15000b141d0100030002d000301c21174920a144034401c0070507543d42004042c08540c040e8003d407070352440a071124062410540000d04001195002d440b40b41c90381e0000b40c0b070100c00103498540120409131495940e840d4040c001810030007215018500a845441e1139040788a40140130f803582001c034a0003906014000c1040d41d070417460704800e8a40e40d001c00f9032543d024042e0300e03005043c0d0b290f00300a4104500c1c030008d4050740c0802c115008900a6a42a016544402d401e5003a0f111b00b079840c42401d10003100196103618003080c01c11071030f441007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 219886672 1250 219885422 219885431
    0x1e0518040b03060a0b01020d08060306062e09050f01090f060c140307051006140102120c03090916180e011806030b070305011707030b0a0e120f090f040e0d0f0201 71
    0x400460f180580444803008404d90700c10300a0714541c0c0400c50004440c0c2a4a0301030040d162100c046903d4200c098416070082c4002585900c020124209081d820360318003040440040308400c004103580414407405010b60010607c40083c0c1d40b09250041c03c8e54064072080800d00e260070380442d1b151845440949102c04461400b030903541003440203004260090b00100701c0c401c0d20080354000c540050b8428a40043d401c2ca982d4a03d07600492800050b5050b81c140507111005401903905500c2103100c02c583c026594010450603400004540840001da591402040c1c1940c07451801c609005000e2111180b10030001000080c000c0c100d031004003440c0003000316116949903030384051188240c8880300820745810041c040c00002e000c1040000c2002d038020100301f480c54a8600e07840c08003801000c0f8458882c6041c4080000130020031054521404800d682c0310051024900c00350442e8400d00d100700032440d644200f034134040c00741469079407012029081d4140c03201000d542c10000c0822280c20765490703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 219887922 1250 219886672 219886691
    0x6031e030309081809010f030b241c05060901050c1b07180207050105150607030302031e04030f08010806040201051c0906110d050a020708090d08090901151e051804 72
    0x18500a080204100f11400c0f001641300000c10918510580011005d01e605032800c0011904080c06a50840181461002d07840804c00ba01c0000e95802c10320640c0000700c98a8a0381c26040c000624901c06008100707030740c000d40358884040c4c04e031201914611890902404044100c240c0030742903e00700c20201c01103400c1a03135140c410544404050403c1c0020b0f40d130104500007448028018154400a622000c0041c50600303030014480e070003443d0000d01016400310000d20851407214614050b0a89203908041a00d011f26004107004182c03105c100006400340000117020b40002034031030096905850702820485c00e803940000c20030800c031314952415203c5e0010b0700440d031144142c1100101200d10580d987ca002a04c880c2078680281020072036030303c108015000705004100745d42c410003003181c83c00302803c5503040c048001e0013070340407a13980b00c4502c4000084540c1c00c1104070380318906984584071154201d00f06e802c0800380030300b03010000c154108040c0300da28040a503001d62121008000013004000b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 219889172 1250 219887922 219887933
    0x5130204090c0f030b01021c0c0c0b1b0d020f0a030309080910030615080609130507081203041a1b0a120603050307030801051207050d03030b030a0606050a050406031e030309 76
    0x1000800e50b004140e01011214105506000c1d81c01050401c1c0024608001c00c000740c0e4441c40c071110011001c01c80210303800e00410410303203100b0004081c0d402d075254844100c03460400044400e0310300709200d031241c11900400940003184840d01c40c01e041014200780041900d0540c0035101d00d00c011181c0c0041005091440c1e510b94a42540120316a03400240b064140903024066084030142e0100b84654801045503950704c1008250340f000e1452a07080303500b68180342003440c00d003098000014034011140e4500e08154100c019500c220300030382e110540c404894050700003580041e6483d4070296400b103506803508071920001c0025550740c0c58500c1403c0d2100c03404800f04c1d0080e030000ca481e90800103015040c10340c070021190140004454600c5020581060155a80041d1086a0066112110600500d0b00950100c0e540c01005800e030360103003a40f40341c1440102000c0c01f4851141c0d01c40070011800e41018403400050703079031183c0c01d40c20000a0081d001055002da040c01c608044e1a1844d03000040c9 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 219890422 1250 219889172 219889181
    0xe040605040f140717010b0901030f110907030b0a0e010302031510080f03180108160318080f09010809010515010309021c0b010e011d04020d0f0b071d09010f0513020409 74
    0xe290002c3c0030042c5c20705100780d80351030304c410043c04281e040c140c1c046220390714403801d0390441c2e9000c3c010b8072a110712441e0849106403030001046e889420107080110b8590150130459103050112581c4400503120042041119001c0c00081d40603800740c1e6000d07002034000850f043d04a54800d4661450955420711705242604800f00c200903038101146000e0082c10b045500b941805090170590805d2801c0303000303440e0f0020030006180c105912f0300c840700d100a00901495891a410440c0715030b4800d841a03181469510107840c042c001005880054005507040c4074060042c100c1c41030280c2070701524401180541030a4000382e80c02005904003541c1c5480904c0c407004801e209682014a0350b16108243c2c4210b0310590002d010001031501e001d240c0c002900c829940158103c404540404103410301c054441e841c086c0040050b50300005008155810402c03120301940c2c10840d00420340d00c2d66080c410420003e10070854180e8800404ac411860861500410340f59511401400c017a500d801400649 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 219891672 1250 219890422 219890453
    0x60c1a091e071514040807090c1b03050405150d091211060402031f0207140c13060b030604020f0d061203080f040c0b03060a05030102040e0618010e040605040f 70
    0x181e00408011040c000320340300348072000c40701c0405040d00520b0901e0324a0418900801a4100034101124208440c104030555000d014144102c1c0c006c1500c4050920080105240c0781021450045020260702803000d40403800a5156465500f024940401e00c180d01600d80310181111809102d2035802881d01c3c418496032074011000300e001c0c0300601d031014040c1c1c0401c240074a4907412000402c00035880c000f504980148191400803040d040c0001480000c0c0600000140f1040d400c00704604504400140d90104c03160440d020340506034000d10703d004403006407250856142c82800041d5180ca0103034090100c04d5070360a0356600d0b00c0c0b0050812421642c01d0b400c1800320b12030724180c00090550201089a1040d20f8503041e0610b420543c07038000c4544680e128501c401140040015096101d80708228001c04015009640f61600c0d01d0b42002040022140d05018442c0103e58422098180f203045040b589104000c003590b850f65100c2c3c1001d440010300c1550320091b09490000000d4141400b000e24 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 219892922 1250 219891672 219891691
    0x30f0213050f151c0509030a0219020a05060c010606090b280e0909030c10020c1e030c0313090c020a020108040b250806090601030b030706120f020310141009060c1a 72
    0x45413480241045500140c1900e206074000d00c5040031860300050316441d1103148074801e040c03401180c800500c040c815908074a40280001c02d00e040c41c02815088401510415201c0f4010203441c1d4004031100e00541903950b01c110101018184400318200c4685d5800380c030341c50709500703107441d0002103000c0314020b4602880340c1c1d000213101100448280103a4902034605501546001075090b2090350398102440c103402c0508413010f114801b02d03c200200c4540ca1002c0042c0d0b80c031804c55042510f4440160b10581e9540c9040541d0307031202c1c510103c1d010b0012581611034245540b1903440d0503446610040413408240c44030461445102c8000408141c032800036680c083c0c03103281c0701060200c200001340026040c50300304038100c011aa000306540094440c1880d000000d038207403e0401020300081d031003094400d48008140120100450992029102000d25181d0800038080c10310807150f2070300710007100080760a0000c0c000c581c802c4400c2c001c80e07401900f445520901070380403481080f4050301c1040c80e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 219894172 1250 219892922 219892957
    0xb040c0513050105040b030609070e03120c01050c03040c0b031902040e1906030b06060d0f05151503010b160303021b0c040e060402240d05010312030f0213050f15 71
    0x44108401403000a80b42c20700c0c145007894a0840850858080035005521030101c240000b40e64070702c80e0500e0381918000504981000740000140e08160780098201106542000000756803010b0303d50480c0c1c00b582d4002c09800b90075151010100443d0409044076062001c2d1072105141c072070940c00640040d0941859000d224101700c0c21602c5404034a40b06a880a414400200046564000130607842801070718440e6848800d80e409000511850900c0e071045442c0c20284061205210410280094291240c44220213201d40103e8980001d110710a081102082400c0305162240a80502039200341005402c01d0704000f00910606402044200682c4c000003100407980f03494083e003521107020700003500c25801c182d008620400200f03407072940000c0042c111481c41d031a1900c01c860103c0d014000810085d61640b40041000c100c1081c68800a13081004070f40041440d4803c894030740440401e68625103281c0424400110064919203a00c40140031a031751311119044010100f03c80450300014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 219895422 1250 219894172 219894187
    0x15090601060e030f0a0201031a0603040b0402030105220f0f0609060507140c0c04090311120901020c06031515040b0c01051609030f080c030d0204030609020a0e190f0b040c05 76
    0x600d091810403440380b2a41c0040000301070300c000802c41c420191b80a2901091064160302e46880301c6004a082c141c01200000800040c40100c1c80e050f07000754421002400a0f46460303e682110441c201500010700b0900025900060030081e40202214441c601c0c241184000740c880f5011904040700079502c2c103450b10104240c05500c8060103041044234508241401c4071a802d82e03035101e841c030840b1802035994565140925029121044004600d070040340e10950340c624603140b560700b0031900540035104192036021a4502102501d10651440310182034580b00e00c0c0411071460000003882c0a034000030400401c0305034404006204c00c4400000115850410162130a0610b0402c01c48600300400b070081031001640c0d004141003503581260001d5240c0000441807811846100c12611115100190001c02c02603903400841c4800d0003114000d040c2a81c0b200c009000c92000c946800000c2400c4030114103a842030761080c6209079117601d0005150085002190840e9108410600800c90201d80c01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 219896672 1250 219895422 219895427
    0x120c1b1104060f060c060b0a08030f0a0f17190905240c0708040b070c090207030f0806090f010902160f0c051f0c2d0b0118180f03021509060106 63
    0x4400920b0283d04010849107000d82c0140445a0040d0040483d5218004501166140b10100002e03003c0182503030313680e41258590140e03e50142c0141404640300e0a041c400d4a4003940326414144145641080e0307903907502084031840131030404100c0c1004d0f960004234000c00e00c01c0060381c002c2c0b50f00c40e000c41882d04001d0744c60524188010407849102408018a40001d8902c1d0700351400c584840342d4030b07510b5003840e1070700008948082d00b00705c183c984041240d03010b0544c4900c0c406034002c82d940b034449407034030740c0700621400314030440f903c801d00102e100041090131007607401041d2540c69a002c4409000c079981d1484c1202284d05410ba40800c040501442a458a4113940e0b42080948504000342d25584c500035110b15210b10000c1c05882207146288000003441c0740341c0034107c000c00740000e25a01c1e0740c540f4040035802801400703614031816903015280e09042c17180b91007030038040c8954150030320316680d080b40d52401d04000320210300130f030340c0c1683d0800320501420340910800c1016082a41c10400700 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 219897922 1250 219896672 219896681
    0xb010b0309071a09090c0d0507031a01030b030c1003090c080c150c061302150a080a06050607080d020f07050d080703141e0c09190312090303120c1b1104 67
    0x15098655003256034030102ea1881c03c136208808269000704035a619840c5101d5a80200c1001c50704480c188000c201e502a40f55002002c0101c9401d002449441c41c0001141203c503070200c515090390029410302c2c070328074002400c42c211156610303000c50042e1896507800c0d50f01055900181c0c4c03542c01040141c082e4941500500076140c1c01d2404142041042d2120701d0b40c5400c0600105c4100728001d04800079500c8592282110015580c0307602d03034605091000801e2901c0854070090f00034584800810103103805012511402e400034001410300003039044100c0203520030300c0c01c0041d5050802c0090002601882400002260358841406604e0914005029a1036902e107907141c11910b502000400010b402e4200d07103000003002e5032581a6224001e192680c404c0d8881e5a030f0202031240e102c3c1d050084080a081920f00c0ba4141c0c415010704a0000d036104502400000c0c0480c080f155903107005550765010040402c001e241c407644688295482510160311090705403030b40d4404941d00303201030526005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 219899172 1250 219897922 219897929
    0x30105030105010b090d0f30020601051002100f0e0d08071409090f0402010207051e0a08011404170904060f03060c020a02060a0c0512030703060315020c0c040c0203070b010b030907 79
    0x4c4580340403600d80004d410030040000090043c03080c0c15100051090603c0c1031090040b84d03040c042080400c0c0c0c20000302050f04259940014459a00080b0b1a42801c04080cc3c040865170024654251700f080104003030040b82000031403040d900c0b0000300140c41c040062505000164803049141d040c0b080c0300070b04840544021042540003080729007016162410300a92116901680c1c0e0703030355111440100d080c02e40541c00319910641e1007040300c80d2004404000006550111200d08100781d907508100d00b0b0360f8031500949009140c00c2d0020300401c01410030101720071240d141c02c600d4810150001400c941c12500301c41c0d040c2a51030410700c20410030307100d00d95039440540014401e030041da5000a00c18422030a1000c10004424414000c018041203403818840001d100c031510303481c000500800400943c401074840f2071540c01d598219409500c2292007060351a006842d85111000c184005003418007521b10451100f00800303004140b00305070040c0a0000c0132000b60762410101445481c1420640 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 219900422 1250 219899172 219899189
    0x3020a02030a0507080c011401170606210a050f01051e06031e070504050a140f0103080403060515030d020a02010207050402090616112707110a110f03070b03010503010501 75
    0x80541452038001055410591091500e00e03900c900c035290000741e90150000e030510320340c280f1500c00240e1400719a45030594203489034880342c00e000a120243d4680c020740d21541c00858960319500440074400c6100c084901e10b100f12030400103182e441d2803800c2da03d0404110140d64490612074000898011403031441d15000310381102d42000c2001a44445115070440384040c2044200600882d05102000c01002c00500422140c600b0708040c40140c8400fa108400307050294000613070240140c3c28a078162074104030814105801c55413041e0040c40042c003030340b501d9685004000c480350390811001400c0155640642071085c0b11344006450003890f03400640c46540148414100307902d0720025921405080700c01d40c6040f020724148001012041104144c100c1c501d10305a07415560255402801c0c01204020310280380e6500e807085801c030703500f9551195150802c282d81c42c003040b241412024481c07070082a10804000400010340b810705103074031098941c2c07804001005280780c288a120300429181 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 219901672 1250 219900422 219900427
    0x1061e020303060108100f09020301140a03050a080313060e0c04200703050f0c0307031112070b040201300e0c0f0a050616020a0308040302030f0c010f0f021009030905100302 76
    0x400a5142d00005080700d040024040001c0d40d80814501d10380d00034903000007607074039994503a00846c0c081d6009026240f001c240941218805040c040750305800c03240c0100241424113020f50f50130800c1da0000d01031205034482601402c010810600c5001100b04040b070041000c445d401c01840b050b14000d0301110078a10a0005011b202d020203c111101d45606140540c0da518a0805406441c0244140d0801610012401004040e04140d000c00e541c403101086400c401d0780c40400344034034464a0402000c0311103031000300300194056200411b01c101452400d2083d0250003c00342000c0d06030072100540e042d1907907409000d221050281110713030a02514920351040c0001c010407090740f01d0384034582c000d4000169502a0b00003419024800341e50090144007805da40b0304241c01160442d00060b4401d000d0300681d400c202d000060130a20008068592082d01680007800303507018003281d020b586c10340c010807041e80d840d54014410095400e04c0307510751045c03041c20032042c001d00e0f0740710f81154424140f04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 219902922 1250 219901672 219901727
    0xf090e010e0c0a0b0c010f06060e0a140a09020d021207031b0216030209090f0609150105030a0309090b0409080c010515030d0210021b0d020f010c0c0c0509150907080106 74
    0xf041010340c20381c0c40b05440340d03680d10909801a8010500802d50442091610707201242e4607600c42d030041012603048070307030705040b0707894103103480c0c1e88400d01090a5108006681c10003859980390040c00303c80f8260f0b0001400c28070202c02042103050100c42100c00255108400400c0201200b00c0c0c104c403107040e10041a10600d001c0d03005003c01014040030340308074050f00010f02044000c0001480710700911050705c00c58140301610b29690b8041c00040349144c1b0360440049281c0c2000200884140d405688003900a480c25003514010644070318519005500e0742d4010340400c8602c0e00030071044d50040c00003c0d02e80b9243c440c1c09012035105c204944282c00508805220684c0001c407150764110882006070303907900040000c2c4880c52035900c0d000711070207800840d08005401040340c10032550f140c0300a100000d002c0d40111108030041c50700401d085001102840641400039000c4c0c0e200320003407070030b9400c0b0300f0744d03000503c000c0701c225030f414001007804d001070100d42d42c0f2080c421000140c07000c034030015150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 219904172 1250 219902922 219902929
    0x111070b0306060705070807080607090b0903100b010302091e0a09090807080c0a0c0801020c01060b03010b04030f02031516121103060904150e100e030903030a080a02040f090e010e0c 80
    0x4050b142c14401c6074042019810300106101d014001d043c000101c81e140d42d90398604070385883d4100c550b0340119001440005a001081d01221803810303009001d071503000784d0410801300411980c495241015400c0c802c015103502c40321079001c15050044404d015220040041050030308081d0070400809042002120000b6a5002650f40c3c0950000c005521703510004000c07450024011000b400c003042002c000030704180107500408045140000074441c56480b4000c51510744400e02c65009031450070401040400d401c01303010b20095200400703642c0000d60014402950802c103451000c421100c80d0b982c1440a500170384040b1100303c101505110150090341140b4070f50000508140c0101488030001c1d0411801600c1c801055035140c00801141d01c507240141d0b51740751601010310b0024582440010020800000da0302d110400600031880c0165100c02110080005400d0880d8940c0920020a061603104007220141662102c0040c91004c0d101b266802e454070145285c0f0a40c00c0144c4090081d103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 219905422 1250 219904172 219904177
    0x300e010606020a03081e041505160905010f0908031908100e0a0908070f0b0108150103150b060409020a020313442506090f0509040303090b0907050111070b 68
    0x1030b0107060041c1d846d84c85208003039180d0f0070403807122001c403400b9080101b003201031800d44c0340750402c4203c10403a560b00e890f040054620a40400f10104100c40403c0005610541c0703002d001c0c0f41c01c0c1c0303000780055984040080c61174100000e156986080c0011a0b42105d0b48204690340c4041e00c1c0e10f85c51040c0385072094102c48044003909007005540c4444692050050500484409690080c624420340e0100e043c400c559100038007551000e4080c0030800741e40703e0600139030513041e40d8100034074100c12443da14a043c0201065000705411600030b21000410800c944040c07e103411480d0043c5584158404c4004445015900000081034203a14101207280f10380c003803104141c0c1422090722044c07903150b042c1c103142c600c10008000107200704000e04d12500b002e09006204480d582558800d99a1918000c8c1c1d00c40e030781e501540902010100e81080580380824015400c94080e050000780d030010764458180d010811101c0c800c40e0340c0170700420851941e02101d00706120000d00c019004d11402c00e02d50080c1071 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 219906672 1250 219905422 219905443
    0x30a05030c160b07110f031504051c12020706150b0a0806060a05070f031b06090c051012051506040806060f030106140405040c1508010806090d0816300e01060602 71
    0x74114a2030510035156114000124a401070071918a003608023000101200110340803900350084c6011054085400811248d4108454a4050940040c03542106c000e42040000780da40d2a2192100c16420951000c14006000006841c0f86d0fa4003080300050115a00508901d0094004028500e201e503842010f994540307602c0700101007002100d0408403403054450203401112004842c03904200f00f850ba00804005106082a0100319503581c10441d1040030203090340e02003401d0480c2e002c06c40a45911444d80006000e6203405440032220101d14960010340103a02254000014000940b500080c0b04510700000c130020700c106800c0000b01c0241060702d09410340515202c0021404008071240c00002802d14030340c1d9090800c038680fa004041007828460005180698400f1460020303000c80c000034034440544030600f5540780e41007603000c91607a0303414a900300100100c0d880018800e0b0100c0051182c00044a43c01707100d007014411007191080c02099115a1404004000c010b0b004901820032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 219907922 1250 219906672 219906683
    0x20423010e01060801090c1205070905010201060b070305030c03100803030f1e0415020901090812040302130b09060d02132a05070b010509090a050f070e01140a090203090c030a05030c160b07 83
    0x4030601f0703000b40c69002008003a2106d282c01c010410102c1644075500400b00c0e0000d80c02480030300c0da2551301c0300317452085a60190008804000042540e04140000d5400c4440700112560040d42c50642c98155007041d16960304004001c41400400160b064000e007e0341d0032001400c00608065640307844190000c40302d0500e041d00800d01c0b02c0c4981c0945406401815040700340d400d100c2036111034900685c008d000c01c9114190b40710f80c2c0f01d16105030341b040c90380641c801b034104e54560b10340b90b003001100310401c1801c9034486281ca40b1840c01700f5a50241c84800b442070b050005500032034065030300311550b111040000b00041406000c012812245407103045440a949044d01c0e03448040395107003012a010000741c80744c031039507550259032400020000101c1e101c0d42140b04035030362204100c10040481d0300d84a0740c060f51111b014000146c4a6004540000300034086504035074505c400301f03091141c00c5000b81d91907000840c00c2c3c124032000b8403000c0128103056611410b0541800001c085500800030050107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 219909172 1250 219907922 219907931
    0xb0a0c120b0307030c0906030311120a050304240606020f0a02030c120304120302060118060e060415080a080c1504050d080907091b1d1e0d020423010e0106080109 71
    0x54800f0720040b0042c5400c11090480c0a8440020601500b06031100310006800c01d0b901c1d401c0550f000c00d880200e201d040384594680480710108403003a41000e00240c403824001c05c91031444440000d044a0046c00d030100100d03170382e464018042c0c2010301510681c065a00400022401645c022404020903141103c1c1c1503040003800d0651032840c040ca400c400c0100c8400c1102005164000400c54100c3d11103200c20003803c00301440d034105481c1c42c1d201e0165101d4110003c5116880c05070017040c0781d6440c0004223589160303075a1190b4a8880d4070b5005072402c5c10005250b60440d5018010518445100c0d1030b00d034220701b001d03940c25a49540c40090042000b14507000b0031401d29052010780c0060410074000d1001c0d601e0b0300d00f40030441560268542c003181e65a44201c0300b5200b90380661841040c0140010340350040141800341610700e43d44000d9000b032a0909080040c0e030b4510642021030542480c03c001203504005c0306030074101c1a0046546e03015040d004012240e0b00c900c4660550b01869400304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 219910422 1250 219909172 219909191
    0xc0a030f060207060e21040e0712090813090b09130b090c030307030f120e03160804050406080d200606010507020303070605010e070201061a0912070906030308040b0a0c12 75
    0x103000380100f01d8010102d07420032154030107001001951410030014028000c51130700c481c070700f540464483da20608112058810000f001d450041c0300c941c0c0c900c031044002140901d443da8038548a0360140c1c2d040b089841c4c02000a2148103402e1041e40480042034a00542c20f003404a1030b04008102e500d0014030403901c1c580020948001400007040b1510050210380c0c98102c10702d009017003da031900c803142c00500301c4103140b1090003150060200a00081d800f8501e000520b16030344035000398612007a640c070b1303404100010311a140e078890200142040b07409840780d155812401404080640300140303911041d100030302c400d1400454604d80000090a00030355a611502c0404e0440c05101070240401d0b141000000c0d81c0c80492400300e01c42c6603954000c003c01900c52041c0c07040801009810140ea150921041040d81000c080360001c80814404a6040c2551a14250103507440c50b0021000554000b05002c104070745170943d43d4011440d6078060114020030704c1e00411004265028402450701d4201d80e1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 219911672 1250 219910422 219910433
    0xc0a030f031205010b0d0b0609010905040c230405030106060f1e0c1406010614071a040303020c100b1009050924041d190803010e0c09040504061d0c0a030f 68
    0x42c0350b0701c503952100380400d40e5600c0c222102d540040759100e0a650900200b5038052808170112446e0078416101c2c0300c1c1c03903410070080c800200003125070b40b403c0c04030140e000000c070030300d140c0c14104004c88c40c0d40c2285d41d14100400c0c5802c1d119207601c403506003d0603000f41c1c140e00713070407143d400240c282d60701d14400116101901141d5a01041c840a03120b0f820180c41104854000300e0118140e070310f03c0d19076904010101c80240505d204422000c0c016040e60101c044400350f800d000c81c0e410a00900c0e01500341b011320001c3d00c0c03c041d11340110072112565030809032200d041580c1c0703407610305030f0703030300f060f9443c82e141030041454928000c200200f40ca84500c07051003141030504c4061000d64000c3c0c41003198820041c0600640c18480402c900d99100b2a8441c20b6598909554111005c1c4c0c019078084c11a482e0001d00e200c080005000c2c411a01e02c244003a500c3c070b0b25684a050b11503070049502003084e175112101944003418003410340c1c400303070003401507211191a803030510f0302240d501529a07000c4c1784445c2480d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 219912922 1250 219911672 219911687
    0x304080711060702060d0c230a0503060f030105010e15010203190302030a0f020a02030904051b0f03180d050a18060207051c020a0905190c140a0e030706050a0306080c0a030f03 77
    0xa40c04417010a482e0a140c0ea40e03445070b11400c034940c44019140c0380020b020a81000701d1130450522140400c0a070000300d20520140d90000c5002d060642d550791504002400d5a800340c01001c0451080c208110030410841040b00800748280050b620300101288070040c603410161059003850f0300000411801191640551541d4810303035000c64581c002c014000b901e80d4042d80000b17100c0c6040a002c140d0b40c5555100386503c850840e00540d02c0d04078004591748040c0c000a109038a450282c500c2194081c2041c001241d01003070355566907542304a0318001a0a8820000e48100064140311050000f9a00003907130f01c0c00d0314400c580340e03402001e00c18001801c160700038074000c0d0010164040052842059004903000e440140600303d0049502c1504004890390142130310005801d9a684090b014038490040040c02c0d15403074039050b64000640807070b14010b486c3c0d1007140041d134002103007820941e241c440d030006001d41d0b10107014400b9a000c00626440514003010f410810000c18072410035002d03406 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 219914172 1250 219912922 219912937
    0x30c0302031209010516050c0c01080414030a090e07080609040305090402040803120411010807270306091b0f030807121701090603020f010e130b03030d090b1b030408071106 76
    0x242d8021620704446580d02130103068174208251114160310601d0b0a01500c10f407005800401c00505001c0ca158004490000010b80f05440e030905c2107404201d84141400100f2085100791541003107503140c68203203083c00314010b00400820010b4814030246980307207900300c1c4d0000d03010702e8450744440000380010020300c20350b4003030222803000060380241c2c85145183e651103a405201018008040a001514507080446143c00040d14000e41f55821200d082107600e6810709140d508d08040383c980d55003070704481e1210710035030740c2c10402c22441d00940c1050726440302800145032508ac6142c5947d4507541c40d809943c4c0c005110a01c100d010703024040c8503500556002c44440603442c2103580d0707200c040c00200024013007a8041c42c4100107101d020350098a0483c0940000f03071111009040d0402c0c0400148200308109600d4082003241502e49802030241c1e03560180500c00459581c10480541700c142e48801c2e401800c1010140f0070400416290025566480c1d0444624611580d11100040b41c0b03210350301 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 219915422 1250 219914172 219914197
    0x8070210030e032d03071e030b0409050c130c0912020f1903032303071209240506150307050310080307081206010305040203100e10020c1606080f0103030c030203 71
    0xf105240f03099882030711880805924401013030018900a00301941c40304594080120303900c01009001c0c05c10003034040e401303a0310516000072180d40040024040d5151701406854981c0941010591403500031012200039030206e42c02c2050007002500a0078072072017449018008102c0304a05000e40d01c81001614283d00d0040040d900c0040c540000d000d03040e03441c0800d50001d80031360b01e040c4164052440800691b20080c46203402c503507a0220403181d4400c10070844010580342c0600c03800040c00e800410040b220032801504c2c118071105c031100121800100124441d9841420581104040200f106d400c5038083c0760040d42e035038910390a40b584136144d0380080440d00c030004000c1c050040c440007821a16240c000e000b00607403120b000450a1b10019107020b541608440700c80140e64000d42c0c030901c00804008181c07805080f01040c5442244c104010031103050b0041881124940d0700440207001510342414280e800c0d091034030340002044414000101403010305018039092600030806c1c3e82a240307a00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 219916672 1250 219915422 219915427
    0x140103140f06010e0606090102100e03030105190f050402030c0705120d0e0d0819110c16061809021e0d0e0f0a020105070b1b04030803090705090408070210030e03 71
    0x2480c040940d1990411890303024050741c0340112280d1000b065940c1266011500314a203074071450108015035005080c2c1c40e06622841c1ca4100740301c2c28900a40344001019130165441307601d818280040f00f680307410101d083c03075101c030390602580010704c82d6030303050312001d0354010b850740d41d0f1030b2a512003807081400107055846400c900c0c0140b204520004c1200340d0301548184045540c10000983d507810600f882c1012844035400151204c3d52005140070341c0489500c0841c0c0d1050381003442403940d020000398503950f08131103010440d00145801c1e90004061f989040e42403940e18129900900c8440d000d01003103607030001801140b0380c9880382c40210500300c0b00d0903a95514401034980e030040c20a0943e240c182e00a400d4040003101010075003002850b01038445614000c15552030382803c8100500811f541580d1034a10601c5030300c081c01400103148911801ca50324107100114524042c50340d44914812418032040000081ca40d00548500035416141c07551078800c100c80c190003400c0360781001451880301 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 219917922 1250 219916672 219916679
    0x11190207050a0e27060a11191e0801050913030c0c060509030c120d05130e0906041502030c0406030e010f021812011503030804050c031e011b140702041401 68
    0x2c12881401455041d1550a494110340c003003060340c0c045901d10240c51782200c000a026041150815a070341c05030780c40c1851601c9442c4207009094504c101d0420002030310194810322400c622030700b0f110b5440003810003070300ba036144c500001c407440802041e640b05404540f0a0750105401110103800c030503401410728072890345554008000760042d1400c144a440303080b449034114142243c15482c4080da05002c0c0c1503a8030709130426900d0750b00c85a40901a42c0345100005100401c1c40011405090f02e000540307000e003050708000d910a160020403c0b902d07881001408682d0307902404980844400741008103108444907141130050410900e18000c00d400004e51030144c546a810082c40000c0132159020f512102c0718000307088501c002c03421142010494070510101c0c0c069070031203500602c40d1085890700c1840c0d401003070803d0910040c203c500c0304030742d203801c1c2d10000c00e000d20600142d0120000a21001c0000000c068100e8040391090402d40084c968081d51119001000c2072110050030115a50390f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 219919172 1250 219917922 219917939
    0x3060402190f062a082a100b0102060711070e0403020c040905030d0608010614090408040801020705072103020d030e010b0d0f02010207331b061e11190207050a 70
    0x405180c030244001d070040d65090400740b0b410411344600d8000c201d007420014030840800f05401c1030403080c41e5040f504441d00d605940108050056001c01580114001c4942000039181460140005c024842e13030080c5028400c60000724032003180c09003001600d140d1603605040c0c4c14483e40c02e81c0250410b041550100034001c0c0003004204001c0748a0042020303603941c6e0240713422190640103035084242c990041c0c503c6403030110a41074105000c0ca42c85460300781d88003440ca007280c2c842c180484032900180c804004009140611304204040801d00003008072441c0d0b002500d174810070b441d04050550b01c054040c1c626000f50f2004050182c080c08025030704c541340c04d1004511600b180700b00d00600c603456011400f24151100c00c00c040b443c40300485400c00c2d4040302c40307c85000e0140400d080010300300301c41c0c4d501c8540300e021192540c0500300000d4010280681103d24040f9661026841c50600c1d4a0f95101c8040d00e085612690040c100510031040c8008200e08005040c1c1c800c69002410302804903003001e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 219920422 1250 219919172 219919187
    0x61a1206180f0f0106050a02071206110a080a0b06070b160207080307030801080111070c090506011211121b0d111201170708070b072901061706030c03060402190f06 72
    0x3c186034000f10103030380e291401c54640c8140203c5a0050304007000420080d01007104440b41180b050700041003000302440300041641040200700300165068050142400840c8610484018140c0e60390345040c01c1525500d00104014098004030000100d03c040418403d01440307018000b50740c1034940d91865400c00901c103178000e000381c28141d442c0681003030405200c882240c0550f42d011203075040403850688070000a0000404e214184407542d00204d070701240e1449201d94020025400b140c48002490a0420040c03009201e00c44080042001c02103120805043c6c5080010030320f40440c16680500040c001402240c2248480c000d65070001718036148a8002070b110301020300c08031040c440d6580700700c0790b80e0240361188000d081000c1014201040305c190f49440d0f0a0002c5200c0005004840302281480e14240c1c44030000a10004c40c1d1a020f0160800040e0000e0085008005148514001913280c100c0644002c1c8140c1e00210004e2240148510b0301006240d6030050001d900e60b11640a090790 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 219921672 1250 219920422 219920431
    0xc0504180308011211100201140117010b090c16020402071403030417030103200607152909272a0d050d050306120a0606030303061a1206180f 62
    0x11002c40021960303006021401400d80c0c5c02c09281c1910740c0c1144140001440a026803a0465485207522442d00d004ca18166009003251610201c80201c45440fa901b102d0f00480c040d0302c80ca01c40c00c2400907007044102030310034080911603511886a4140b002070001d2142c600f00078400b90020030f20b14030480c1c010003d10300c6036018191014241014003410320540c4401d00006003031504401c03880103000e034003010250300719001130601d62030000c0b42d8840007201c0022409401c4c400303880b014a03660107080c0220000590610b02c800644210810380018050003004044c040c0c2922007030300d008030b47c49407480c04103140c1c004d08050b11140b40c1401001c041000c80c1c03220200503412403054031400c03414039198040d90550420301402c014044e010045406900c043d002a070300001900c181840004140034900c01c4903c01d03900010403502d9860042c0543d4810703400400102e40d0000c0740d00c4c50802c9070301200d0005902d40f030700f03180725500c1400040c0104e000c81c1c4400c1c0b142d0074640811042020005070b0b0b9000f07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 219922922 1250 219921672 219921677
    0xa180504050706021507030203071b2a0b0702100e15040807171911060d020d05090c0306040f02270601140406021e071a030a140c070f0c05041803 64
    0xc0d0b00c800059a60b0001442c5c180d0f80c900f002c02c0050002440b070303030103103800101d10318102051030540240170f50384101c402020344112400300c0d004441c01d00081d0715000f00300c9041241441442c0350000c049003c0c09480c1000c0e0191a00200d000d4150b4800d0721007581400c0000d011520341012511404881d07042405200840d202c0d40501052740f0554160f007451040340c48000f880d15104018541180c80b2031000e0460b1405601c0c801817100303a82d480c01070402881c1010340161140f0300d200d41c06040d48e01c090400035071600a170012031a00e0b2801f003412503003da000701c1c1e00005400c00344081498109542e41003580e501c0c880e140d20350786403240050b2a0245809a94501902030654031b140c0d0305104c0c038403603007004d039011303510004900b621072022100072010f0105451407250b039400e454074a410f0103101c1d884041000020401c400c503052050221601151080000383c4c9844140300d815846050b80192102106606a400708400084044013501010308240540ca500f03a039564001060408120702 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 219924172 1250 219922922 219922933
    0x120501050306040c03021e060a03020901140412030807020f01150302011d092e03050a02010210090b0105371703091513030c06080f0a02090904060b0a18050405 70
    0x9181ca00000c0660040d9080350001d11010f255508000c0002c135200c0780140c0100d2600c198400c107070382d40c5000d050442074586015940300c2d2644001406d10481d80200c59071030900b40300911010940c0341c50301003000e40c142003002c4070b0b480302c000503842e0036070b00fa9a40341d607036007440d80b5100e41c010f00c010030004483c401c1e207402d540001070b550324002c012580312480360031019060015094000998002100020003601c044002c003400318110074140700f94200f500c041c0c0c04043c002c021540c0c100a1940380070030075823040050034159511721044104c103201d0b10780720b0900c2c01d650f00e41000b1a081c1052096115203a02d0403280650340100c9031441c01841800803122204007050303d0b00d4004000c882e628240240480b00c035041400058a01c2c2e007101d00c01108250b03400d4000310000303100301702c0c0d000900515201c1542c21714004a41d01103039400104281c02440c01448141c6050700c40e03443e002e270000c4e808040070680c3c1103980082001c4400e154009120080940300b803941010440c0d215a002c0c60180050740e8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 219925422 1250 219924172 219924179
    0x80d082502100c0c050d140d150f050303030727051201050901110c030304060c0509030a05030408122119060f03060c05040608070302090409021002010c0e010e0310020706020f0406120501 82
    0x2034190244100280090300030f42146d2100c584204800354202e800003080b1420821980d00034000c90b00f000c04000040d0100e003406004041d40d060500f001081708800a52641c600004018511075851300800c051480d0071540c0c500700240305e0b001ca0050000940120082c03031007500410701902040d136190f1020351824583d0031419a48070b046075000608480154619190b0340da0b01002012441c00030000c20030148070808a40e5030910010345071a0043d40110b4586081c1a42c0500b00f60101c548601181d108102d0b51801901c1e00b24030807400074071074054840c155038409940c03800807284442c00020b0307450000c0101c1c083e8403d0501c18103590107032508015120740004c0540b17043c4140d01420020907002000901014400e8000700350740440500003041c210f800303078042809a031440800f0b030003503510390000c00082603000e1b14601c00300000340307050212250b81d17a02182d01c60103400e8040d60101e0300040d040c014003200b50125103094602c400310a035515030342c50004105034554481c10483c80d06080000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 219926672 1250 219925422 219925427
    0x3041e0f060516051e0705070f06080708100b07050c03010203011205070e0906010e1509010b03071209080f0d0912020a140c130f0b210d020601080d082502100c 70
    0x81205550b911040d10300012017529111038241e0000c1550000000c01c036a100140f810300c154002000c031043d0a12580f81851406801428010040d50070003038000e0030000702c0301c000421401180c01c240309803071740c0e45918100a400c29505084507609980000700000d08051341c0200810f40c2c43c0604141e424003a242d40c0c0101031030743e0075038070814198881d500520491150000054109030800e4070140f07001e08510224140280981c44040d401c0700c04000c000901da00a034040d0703250745002404010041ca00e80c1d4001e6140241039800d5500440400c0c0015003118507801010344070b4000040513866481c991009607106940039007290f140b00d010308481c080007000074202c082611300420140d1880b001c0301d4190020440c40c44e00d03d400f1a2511441c04c0e590302c0d01d6041400c00c40307000d101e907050417000e85226840c2c0000e1070115821540120010001480f0100e26a14010010f03e0410038648800c20303205034502c0b00021650880c001c40d500454241c5d0000ac2ca40b01060b0204010b02c1034080b040f40c207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 219927922 1250 219926672 219926701
    0x30106050103090f14030c0d05030a060b090321130b03010311060a081504140702070303020f030a09180207080c06090d03050c0a0c08160809120109020105040b03041e0f0605 76
    0x44ca5020310344d01d0000055840c401000a0410040841e0f0400385840059864504491692001301e83c1c00020311000d10304a00464000d070100d040c01619100c0e40c0000729946d02034a6000d420710b1804449052041e11402086030f90071590180c8072008140c58a40e42002940288003c503401c0c0303909280580311381040e40c240d4102140079100c4044c0742c0d0741c941c0c0700d101d401400c007680c51344240d0b5403807441401c1010f10700c000d000b0307529507008010050551a01902e000ca001c000c1c1105640180000d0002a038008644e07c1910304405508040f05105841d1101034011400c2c001c1440a0200c0e02130b101410000d140c510070340703240301154441200c404068080790002d0310600200c501c100540c0c2c3d001b0380102c80d9642181d20900c40c035890b28901c48800e070034048a80400b103a20801c0000d11007405c3c07030207400e04640e00d5035100003000b2880c226800130741a40310b00c2c0701e0007004583c003000050034003444074000408c030f80440311009800c02d80c52034011841c40503114110784407450300002c20001002c5075038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 219929172 1250 219927922 219927941
    0x204051c0515090109020d052521020d050102030f07081005010c0305091f050c0f011a12120a05030412080105060a03020d0e1e0709020f0d05090313030b06030106050103 74
    0x500318030030380e41410465605000f07100d2180c07903489084400040e150300070401e4500c0d024002510b40021101e0404d085007250010070b52041c010344400f8001002c80c1c0002c9001104e4000d400c90760701d2141e2010928038540c941001c0d00c00d510220410400303003000809284201b103141d480c603c161350b80d072002d00c9000c030003801154005140310140d600000e01800090000c503500406981500c071005002400c0440302e00040b10014030301052102070f0310b108000311218217522100a06c040300081c00703603072511000005094400c00403055403448070300c42402601c0242d0035001c845660346100a0018006500558080701c50b00081160394a800344150210f9050f2007006003054a00424940203c0c040c1d000b015075101841d554010081d0069010010207889825000c0c0b8902c8034004464054201070055003e00383c5070340104040600c84084400f101c01c0000101400601d603281d5850041c41d501800303892320740c2d030f80c1d800c04044140112458010712900d0704400074449103840d8401142518804e07607 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 219930422 1250 219929172 219929183
    0xf0f030702040b0402090409030306080c1c11060c01050108010c090503010509060106050c0c09010810060f08030703120204080f0705120d0c0206210a0f05011208120a020c0102070302010204051c 85
    0x1840c00103103095004010b45034001030000d818160f0304d200140841e0001c820072004a552440d080007011018842d086000004840611004031010880c1e2500c0b920520001d240f10f402400690680c0d4444d402d4031003070803410000700305542e100c48200b4001c2c90046800008201005000200e520301401100c3c840c24070700c409400103074a048410f448580000d080303410035000e9a4803450060725a0703640503009004680007000141740069194048401a030003500518413141824818a04000103e44d152645880d00c7e840303e000700021100280580d8005400c50b00030348201f0012902c00240000c29168101c91941c03640700600da42c00c1d69062845600001b19604003010000b510303000019001d1074400e007144807402004126400040501203e501400607a5000200d00540071407191601400c8940c83e81412012152600215406a200300c10302040e00903001a18400381a0156030390007042c1402507480702454640640030f034229000d102e004004601c81c485111041c0d0f81d0541c400d58201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 219931672 1250 219930422 219930427
    0x91c1a0f01180e070b0d060e01140d030c030e09040803090607020c010c020409080c03030c031b0702010c0605061504180506041a0913020a0b070b0603011a010f0912080307020f0f03 79
    0xa11803501030200340f0750304405070141d0400003410303c0d82c00d4014030039029551000101c840c20070300401c0001c081a04000c00c507140d18030003000b00303850702c3c0c9c960103142d40c140c14070f4520701c1443d01c1c0858402c82c4040c03080f5000040c600034001004445405180103035201e8003074a4055a4512089035140d1400c40e81c14001600d0075403000240c21700350b000f50f0645010703a5a030f914100284c4a502c0c9035500035a25100b0b43da078000100800b00011038985408038441002007440e000301c51300000c000030b0b40150081d1903543d80304082407065540220314041403075007204154460f81d4030036406075507840c80c03010308030306d58100340015006203414401c401c460004021080d09a052110071300040e60301c014554030b500e984460740b4001590720581c99100401801310090354440c06071406440d0b804000c0d099500980c1044003109019181c2020070200141c28a000e03203101a4071034044918400c20b900084003401c0640c41102807000a0001718130607070035502150745500c907000701a07070341c1c0840004507100c43d0801d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 219932922 1250 219931672 219931709
    0x10504020f0d020409050303010803190f12050c13080d030c030e0303041b0b0f190f0903020f130e150609091f1d0f06070306080c06091c1a0f01 63
    0xc0c400041420f001600000d00901d0b80e588041c03455000f81c100240c03550012481000750801d01d4a9050809068034080800852407000900000d40740003401580d1910f81000840c50009001a250101039042a0f112444d070744100c020f84442106c0001070011f410b01240c2e0001c2c0f03000703004000b01415441e00440c9103603281e80703070318038101d881807481007980d095500000751010808020b01a84c0781d80160701c0d5560080d80c00c88800b500300702c000f03840c180100381d42160449904603422008407034055039050068050000010dc0d0403941ca13654a6016140c01c002880c0480000b6040e640314100800201d00c0b503c40b4820058003175030403071310340000380d01c1b20f010105666212203180c0e44040d80405c001c03901f9401030502901943d5102d0300208694088038180080034001c20030760750443d00a0400f00710050030a56a40c0c1c9440f09182410302904000940000c50384400b100e007003049803142040900c9011526146250a240d40510f502005206000c142c41424501c0a94100c4921100c8030b0301d420308 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 219934172 1250 219932922 219932929
    0x5060103110f090108060a05160206070309080f07081806070807060b0a0312030219030b0d03051303061104091103130b040c0503070b0c06090a121b050a06090303050603010504020f 79
    0x900c0e0107150b08101c5581851a1036201c6000300d5001c0d180a00241c40e25181c07041002044960003030807040384081124506172220307004a40c0c41d403c40d11900d40410140c04a01700300410f482055000c0e01821000500081031080c28005040c8100c003050070030340501d0415040158501401c040641076100030400d0100141182c0c2c800501084064860030680b940d0b42c4403d0140f1185030760800110341c0018040d050004000c291001e1000b07217040422407015a14049507000780d440354018180f101c0041c048601c0212200540c0055038070030380610001c070280000032026040740c0703c3d1141080c100b5a030980100c0258090342e21503454509001c403003407942d840b003d01405002c1c2058132402c9280401003400d803000d02500020706643c01000d40d44030040d5000902d0020300912065258100a12000008140301003100c00344901e4034198800d020781d8501a402902864402003446c8205d0340c610007008040d400c9500294060f441c100304c02c0e641c0c0800e150984004941c029400b4410700364140e224034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 219935422 1250 219934172 219934193
    0x60b041214010203011412011518020421030f030902090f0414150603120702240d1a0405010e040210050d0216060b12150a180203010f1a06040305060103 67
    0x40c000c52080092080204000b4226482a000074150b070080304120320442c204010800e03003a0b421038008109100c03000c02c60041c0c0f018103002c1e1700c5503d5140f080310700d1120b00c6901603401500d208071400d12080d5000c002c031118955846d00440110b981c0070040c200342030280c820a00300d0707a0050509440d83d51030b40030075031180100038030403550a1003101d208800d10504014560300c080c034084142080341090b00c101440c1461608400c405081b041081500507118158401c41814000307100b18850041005108064011440b8818007a8030304001c00200d00d01d03082004115a0b800d60f010045a40c032602d007452113640841d00030b90046c205c030324407580c8036118000414002d04080d40c0181012202c02450b8488448400d081d5512621402032002030b146c40f02e0a2051061180000e0041003c4202c21201954009084207070f002d940b00600c040542c032100001482c80d500030020003132842c4088481c401005540b40381c14050790b00000700354031030038000200da0940740c200b4000d007402d17803844e030310703965900d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 219936672 1250 219935422 219935459
    0x1202010f031b030b0a15020c09060411030705071209210327050a080604020d06090503161b0f05010e06090f030105010e0411030102040e0423030c0d0e0301060b04 71
    0x15075148440580107903001680b4519056a40d404101c000d012810841c0030f61403074000040c101d00070903503035031a00e40026581429440684240141399122000a401884070700710303406400e440001000300b850f52000c01061140d100d031a00c22003031a64007800b11007111240c055646141188120910340000d2450382454903880383c60701d0084401c4240c0d034282d01d0a0100300d014491074507600d05104a181c5038048034003a01080000f006185020740000d0310417602c400780035140a60313904410003171002c2402143c031b160380e03e00000707603c25419141104160065081100801c0d19100f070204044080260180483e04142d503031510758210501085400d40c40320b035600d5030200c021041010310f600c2c01c0c012a03000f420501c481901078a002d040640c0c20079280000380344264410442030140c2941403400ca5001030b00480000121000c0c1d42c3c4031181141100b44a441da40310200342103030390036000a0803401c014280e58030030180070704500a0500f6251a4000c088000c0024001400104030707002c01c42009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 219937922 1250 219936672 219936677
    0xa0303030509010623010210180b0c22030b060111031804090c030803040c06090e220510060f060206090d051e040e010302040b06070b01180905010e060702010c091202010f 75
    0x1c0c1d5946807048105201c4403122145c0861001307928816680501a035409403505c0b4074240950107150400113404000d4840050005520b800418103500d22007081d19403860300180342c0c2c0841060207881c41a440c1e100d1008541c00d40106001401070b512507038540c540e02034660000c41c00d0030b0101d0b000840c00b81c155811141c02a0361503c100700440d01506c00c00004600030a607441d41c034107280c20807441c010000d800a8052050702e17041000b02229030b80205901c02c05000401060b940100c5005600d4201c450020b40184140d9000d1300700129140e00c40c0017140c0c01c038442c0180ca20b035540340aa0b140c1e9070844205807150841101714008501840c000c212039010507035031480680820702440b5441e00310383c010940903c600700c010320860401d0700c590000f80c1000c4400c141000c596a4548006c0740050103001160700c040109042c0700032441c1c00101e40c0a521000a00c0117130302c811582c0750b458008035001001036007089403214215008110840603583e2001000d4120b15040e00113440e11500007403450304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 219939172 1250 219937922 219937931
    0x6010c03020a20030a0606030303060b04032f090423012901020c03070303020d020c012a02060904060902120703050412050903100518331801060305150a0501050a030303050901 77
    0x840e94203011030b1710814411600052064190306000701281d107250010140c2542c2080140081240c448503444c1c0e031752000342c0000031050304825840d080d402540d4625005007000c0700380010000517075418484040c40c0108240ba00c00c07070b0ba02003400d840307100907030000341c0410342d400300144006503d45510804040c0108d41ca002984004030f440c0041c598401d0f00180c02883d1070500542d41402202c0c140c2e90b09290449494002e0090740c4102070218981c2d041c1c5000300e062950031901d51100303880302e906000740100200345c1d4491850010358803d46001515004010000e50001d00038070409028981066514504200c14082611694840c507400e82c3e042c07080700e500c0030a6590714080d09104240c0c5403d8000703185608159249001200c100d03140b0100381c420014950b8800591441041c1d800004084010b40c507900b018a04402413920110344550130240040300348500014090001c5103807820b0350009548103924481100c400703000305680306130740042c2040400c0c861381065810001c0c2200004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 219940422 1250 219939172 219939233
    0x9020310030b09030a023009031e031c09080306150d0c2001060315021308060705031009050105030a030305090c0a0311130618090326010e06010c03020a 67
    0x102e403024112100c50103070f400003520300390680e4188403600c2500120310724003941204050113640406d0100001e14112a0085080c400c1a5020801480480c0c08141d000c251300b140410107540f030b030b40158548101805080c1030012140c000313204440c64281c20405d00350554480404220420016034154003544500b81b040f840b103070050b0b201e0551032303180366203032841c01c07500552100400c42d00da28103003406030b40762620800200e400944809040401c0420050b512a18000c03190140701040d00314250302c1c4558410003420350b0304140154007403041c0305002010700360b940c05020161038090141c00d8040d080110010001380c026001b03190800140410340b01500070b17200104203240d08a600030798130048482d84914441c00d00601d60607901c600d00d2402d05c140c50a085000380c01a00309070340310740c0e03007503a48411006040c4517200c01140c41c15070107084041350080300c004038044d9400303000d803829103061003010524642c044d07a544014198950050030714003210f611400400142503801480c20b941034850807 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 219941672 1250 219940422 219940433
    0x501050f071a01030b15010f031806060306060806090a05030a0509010512040501050103170412080904060e0106080714041409060303041203080405160f0e1005100509030c010302130902031003 84
    0x4160400b00101c02c200541c035508100e064000007030b0030110b54900903401d511450741d00c401f540c40200320504000c01c500c50410032058620240c00c07000341030f440c60030101004001143e042a0b08580ca00c0d011110b040c0c80d40b025503900c0d019005001001f03548208100caa459000340c01910314000141402814500c1c0c0015090340c003842194120345a035982c0005104100c015a40700f00343e5582211024100340c14461802c181080032040070b880c03500042014243c513903443e00484080c015400e000511540c5d1920090000d07102541e5240124140c00c0c218150032521205807002c4850f1aa10800429100418018414009071001da010300040001140342d180c0394004141040c8240d0b140c00c03040c0380038280182400c43d0804800c41d5450700240400c444900c2c24425000d0700c8010341503117416201e00c0c034103155195079a0700054001c14445840e046103034200f0083c0c660441d055041d18654854880110304900c5034007074220702004080018171890725551301650344224036007511041182c894450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 219942922 1250 219941672 219941693
    0x108240a1707090e07120609060e060f070206040b060f0d08040b041403011112130b07090305010c0f021c0507020a090209100e010e090915010602070602010b0303090a0501050f07 78
    0x480d000d05464030407600d00a0420904000b440c03880420040c09020040c055143c24103803007607020355003441d407140c03050200d0380c0c3c05a51742c1944070008001d6810030a200d40d440b10000c41d000f84109444000160110f4000700c1d000d0b1081e170380001d40d00c0c4c140c2d40d1882082001d40700070710035a070828410014100000c1d684002030001d0104483c01a44841c07402c480c00b281c08101c035030880d00a074101250ce80d402c18061090ba480300d1090411400a035650000b090b5403a81014005004220103d040c0065103400c00c070040244d030b015038028040040110f2042c0c400d070401100740c4006070300080c00a056841d800361444c0888442c2e2810600d400c0c0907070000703181d13080e240d040008090f0307001610a00601c0c1c40792048851800d83d05142c10303940f51610010b082821046c003130030300a04007403002942c0a10b00380410024189101104101d650712084006e5030303002540564130141d840c1565292203454000f054900120006150f004814100030045a450308486000203000340144a40400120000d48 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 219944172 1250 219942922 219942929
    0x106180e07050c06010b0c100e100b010c05031206040c030212070509040e070b130f120b190c030c0e030703080313140a050c090a0b090402090c30070207050108240a 72
    0x1c0176100c80007a840e00f402c0c100701060349144945022744e0130b6040100070807845030307415030b510002400d20394030750044c0da1900c0b00344c900614134000000c01001c0f080100c4203250084c1429201003200b101060000c0d000c030b1258109007100400d24400103100326200c1d0006041d207090203000402c80d036039540e10f00344ca46001500070b800c0801c40881c0540c44510706c0003e000080001180040c1114a072150103c403480b000c40e0042d005100d52000a803106246600c044075016180804105100c00b6801c011300500d4941500d00010710702030350201451400180103c03d2fa600400198519140c120600b40c0b46c0d40c0c2c048007224580490038941006c5002030102c80850740c001d2014080b09600641080380d200002082c1c1803c040c6081200031541d203c4d10101a030103617054030000c040c0d864403907014540c1d029040c1e040b1001070a8506005c901244112051412070000b4030000c0151258041a031703c0e56aa07009240c005109000010000d048584803606039500f205482e0010102c12000b1400c1d95610741c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 219945422 1250 219944172 219944189
    0x5120a0818070f1203030b0a030605150603060117090c0a03030801030b09120a0c030207090c0302040812030f1306090f0602040303022505040c0917070501080106180e07050c0601 78
    0x2040200c1c142003034020708103042200014120aa050040300c8200c072031640140111088a40f0685080602a91110801c9400204150007483c1d8920b082e8000c0e160480d4120003500c4405086c94003405c041007501d0080b1816107818920284114403000344039030043c4803111070703c6000104032981c1c464000d8071000e14020340d03070301c000c66055040c2000e280c040a41000720540c0002c2c4c19800058501003035a01060091400c000f03012400e003070403860601150410f421083ca0302460910154069000b01300b2210008161303521701214426001c3c8a000032034440401e100607000181c2070b4004021030060451180000150607c0030340c50788990504055012140c80358002000c4c03040c503804000820140120261800d4041085a000b910f019918468180100d031144040410f00f80111108009010b801e8120040b2102d020001643d400a07445006d000c10b80200c000700e1902d2186c07098900301501100307039a0780c20785407646840703a2100050003a01007240074080050b01c030301c05002881c000d18428 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 219946672 1250 219945422 219945437
    0xf070c151106060f01050702030a122001061409060a1703070b090f0a03030c02032203060e161503020f0a0c06050c09030601030b090c0307090203070210110702090405120a 75
    0xc0030344400c024424440c1c9a500c61010000035030340d803d80b2a849804280380140d00c40c0c2d401d1011a14003c2d141e44003c144c034201900b0b1510700b07503005100c2d02c2d14050b01030880785040b4a041040342250050b006078090880040c040881d00d04021520390342010016010301c42c103a42c2c0b1902101c40f260941c0c030340b02298000003400d40c2402103807502c0036040500c080181000c882000c0f14160350312503050009003856150051086418001e01c1034950310958a42402d804850100e003002094019000c1282c81900c0c000342000302d4200000d8000b0002d0300c400315918800e062046028004000c060b090003015000c001214007c00000701801d20124070b41c88201e0f0f0003407907103410806e607440100b542e0780b41941030000c4c610640d400144681117a4101800f00d2403501e8468003141410700c5180c1c0d658151084803400a86600e66038000d512915040d400d03280c1c5c1c8400d201e80d0f80203960200200a050040c1400401c016241000700c840d0020300c1131044505071058034a200b10b454010130034250204005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 219947922 1250 219946672 219946709
    0x50d05030f0105100c02010f05041e0503010f020c0607031104090618050a0c0e010509030c060a0c110603071409010e1c03031d03030115050d0911010f11060a020f070c 73
    0x201d640c0d10301400c002c60310340c3e40407103140c02e0080c11046051006410032038010384080159000b80b080f2406000c41041d01c0c14480c009041480340c82800740301e070f50b000f50718003200da410518107403081e551889080c80141085480b00041100944071690401d986148208000038130741100348602d40050a4100803a074819010b10b000000b102c0005101c43d14107030400040d4800558083c0c000306e8a032809090443c2c5412100340442c0c903000591100c40e400560020729040c400b9000000075807220310a88048804111700000c4c088180010b4442c1400300303078034840b1018144d00aa0207051004c406240c203946c0c940c214000905400b038004082619001042946018584e00d4010703e40702003e50801c82d0350301039100030300c983d60388414030602d45408012541b203003042e0f1080301112901070702180140500703030a500f000e212081d8030380f0300d060120f110300d4031581603030317000c0c094410b0400c4140e809840c10340d0f2200039540217036000e10b585450751081080720304d0016410740e180c240030b4002d060b40307402c80802 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 219949172 1250 219947922 219947941
    0x311010f1a0a05130e0f010e010e0f0d0c0b1503070603021b0a02060f030402031c02011a100903110102210405150708040b07080d0c020a03080a020406120b030a050d0503 74
    0x740c0581c14000d440a55007448141c80d0441e818582e0701c0075107000189105c0a0112508040e015102e0513540e500b451018404200c05400544501c0d410380140c0c0c088030003410000b6030340c004500545000c69030450910f004034a0707642000354008015080c03044c101030880c1c00242030030f1080d000000402c2c0d011842c00c1140c004010404040a4904000c010881c9150001400c50003100050600718000100140440d241071080c180241e841040031300701c9504a080181c003a040d880603c1000207441c4c42495040d1803d503642c0041e11200d40c50740b10826046442c2c6120014004030240c1c154410b540c0002c00724104c2070001e400707004580b1002510b8508210801000c1441c850110400007024070802010400701021901120224000c1990320b920601d0b051180e80952581c4d076030541e14003507400c6c803410740114484640d5071081e503030f40c1180d5403210340d0300c0100e005a0085400080c501c0e126120580340a40c03000d00d00c84401011a200c03c1074035030f5080e103044215454200024408004c1c0080c100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 219950422 1250 219949172 219949211
    0x5040f0b010f081b04020f070807060b0105030c030414120a0302030411030606010f0338030d030e101802040e0f0d02070e072304090b0111010e07030f0311010f 70
    0x3101d803072105002e482c00303080c01d55402007490701c0b03025140c11a0708101d0703070307680c030350454181c416504801c9445001c1e6043c0170100e5001044147c0e0701d80d0810b15182165272003a4103da10030303851140c1707141c21030b21680c1710a50a0f285403810000303a4414070a00c48051032400010348090403031135401580d00e20b49072030600c0448100d03442c1c1501079441203050110503030b00801c10a41030325187c98006003100d6640102003561426150300703000594140c0780d810214010008d03c0205200a804a88049045101c11022981100c408082c250030449140c580d0581c43c0d0080c0c282c034111215107801c10651070300042c3c200c80f24040514070541c00341a0000c0072140c06e008001c504445400a09401840e10b14030212541d4001c2401c0200184081c44410000d21302e01e000402e1200114065110303612240c0c1000100f0f22414542e005c21985048d980d802e400500039041d010b00302d14050301b0302c80d107180e40d1181c03244500c000403024810302c0c0003030002d8081c0c01d00c14001c40b5406200c0c00b00344441002c40b20100203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 219951672 1250 219950422 219950429
    0x2d03020c190b2503030204050108092a0102070806090c10080606070320120c2b0f020f06090604020108010501050705060105150d09052803090909030c02030105040f0b01 74
    0x1c0031500407548205080410100c115034030031400d196580408a00d103070a8040003440b14400903103440355181032592560141059070802c1c1c844030819200d0002066540100e6003c403007030072030031074060223048a06642402e01c407030040c012036096940b111800c0382003840460304480b2690112200e440203140c030118844410040b0b007009580d500304840441c242d07105800020301803040082a807041c20104145100c00e90940009840760f800036403901d060300743d1040070b85540a101e00180030507401008001c3c038804d00345540e1a030b080c40c400001d084d90700c182e01149600c258020b81c9400c4c294290180302d5940300341010fa0180c099440c00f403001400015040c1c01c9141080428040c5200290300042e1013030550740d00b10780c0240d204540079403044013841040c80e450b040c581094000c208101c00003c20310200c2f840c0604000403e445468411410554202c0c06000251240b030208141c0c511f0b81d02088080b4000e1a001240140c01d03000f00e42510001d40b41118200e281c4103600301808510b01655015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 219952922 1250 219951672 219951679
    0xa031505040210051206100e030303101e12110a1211011e1718030a08090709021905131d09100e0705210708030301090b012a2d03020c 59
    0x52074819111310440110040045e80960290000c3d07061f0300c1e005d290400c10221000301249c0e40c80c500071165100300651481842002c103c140c00c201d00c8a2140d12944007503600b0000040f000050640301d800311150030301040c907000b20040c50041124a070111076118003500a603403000300e903522140010200381801545070080c41c0c4444042101e10351040b02040c0701400880110200c0e11040c9503118100c007040010889440002400c41455130003803241441019040306803854940ea032602202a84500303041540b2501075401c090241c240a04007901461070a591010003042d1629000b03055080e810740c0040d0460180010080000030070450301049607500502072245200c10412940d444c41d00b40110380c030074152640409541c1841d081540082c69020084420f010380d1070b1606500e9900038054220711a080240c480e00700c0d40224281d41c0381d00f010402001e20b26200303150200c0c034002648400c4503048021119a20810030502c200b03103620010311043c8508841d41d142c0a854030403040b904070300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 219954172 1250 219952922 219952927
    0x20f0c0d030816030b04151e03030807050f041e0509100b1c090503041d010f060206070305071704051b0411030106080601021501060207051018140a03150504021005 72
    0x1a600105aa40004444800e010440030280d4140c0117080203070f601941140c0f41c00c0c00d0303080321010801d4900c02c03155100c01c10001858070000f8080080703418000900490440000f040c0c51030b00c81d0000713080300c0000b281003d050603190f18405a000218644000c071030f020040051101c0e14142e40c0454010700aa000c03003c4041c40c283c9c002505000c4c5500328400a071041040c508910901d07001000c0041d885000e41740d4031a11643d480f0000f1142c803040020000e802c80c00840e24510ba071389454140d8085070010840d542d107001d02240500401840755080000e4030000540164104a007640181e1084d409444002607001c143c508050800d59901d115505080340048001481821241134030014a0860b9242d522003006070b290084421000e984000550000219030703034042001815103108032000b001d03060104c0d100b100d4110398440301d4a10030078031900c10004443c0b14140032601600c0a0580340b419a6603440764080551050000414691954104821843e007a0b5200c0c0c925165810404e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 219955422 1250 219954172 219954199
    0x812041719030302130905040606091b0c0204110f0711121501120f0209100302030c0604081b010917030c0d0906090b130504050c0a0206060a1220040c020f0c 69
    0x1e044441d921015040c950b000403140303012034640301d0714000381941d290140560705151500b10024980342c0b0414007620710307052808a14940c24040d078402c0c19a25902e01c0f44190b02074081000403e550b50b11108925006c00c40b10a042824074040c2030001d01460440c0310901c0320303500b4804030301c482e060800da43d5085241011010400102d0b0b480c155400040c4552000a440c60074001c981d1100030041c0d8000f5588d400c101c104040300701040160fa1099060791710207000d200c00d1203000d0145000e0010150030820844455032031101d554001f00005140c07201040750340c0d49121a240c07500018084183c1c000003942001800c00300311810740c40780c0070324000309202c1c0303070070310042800c000c0d40154001540000f8034032074110010a07115025040007881001382c1d007002c0444a1140d0310400e02c010140c050000090350900e00300b40d44c981101c280b202140c02c40d000f141c1d04e643d9400c4500d0b00400c0700c0d0f111326840540c181c50b54819031500b0200354009000041c034511079286007480240045220b13214400781c20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 219956672 1250 219955422 219955453
    0x30e0609070e0c040f0e1b090a0605090f1306081509210d06121e0506060d0303230601021006050d150e1b0f0103110a0503040c08120417 60
    0x100e00700c1d50300750300540254440790268403862040d80e0003028001a040170100c0d445044841c0b003405040081c20281c075009001480900e6400b82c08800c40d0702c44000c820412690380580010007000500611100c00191a200002c24030000c4a650010941e0b0b00c8105001c601c90820203601d01d0007203090019840c0c130f815001255152002e0044035541c500d4160b5041410399100150340c01000e0509007842504c1d00d0b032036620b00700c0685c11400d540040b214015070b0708091030303120559a150f405c83e02521450361b41205001080210200490030155902d040c0b0042141250f442c2d0700c2c0e844149041400c605105000914200990b01e018400360700e803c070100000c0d9181c41c086c08569510044841d030708000324803410700509006698043d80cac003824400d4840c803200d0124512004000b181c031a0303803100c10007004604491400102034410b1030204242c00b502400f800c05107500030301c80c0400c900c109484091240c10701c1d006000d06c0c1d10004000c035090020014240c039000440303224400828030307a8101d1070003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 219957922 1250 219956672 219956683
    0xf1e0e01050c090415080d08060f01051819090e03090907260c1b0d030c09030b041707020310020c1b060904050901020f131a0702060d0b0301020706110703030e0609 72
    0x54504c1256074280d031207040b00340035084000414651095455030b00001030f0180100a0882c0d07444e2058201001290007503005100382c600c1a1020b031002a0004c04610a005800c2c2842075a180d520181e240006116101742c0180f2000151000142d9210b810400a21030f040b84080c0064040c408658030114151440301c45079044000c9040c0070344110381324030303c401701e00c1e100d45810220415138080107555540c100060803e1007189e036650411400841d454102c0c2c4050460100510072684003002c1030100d05800c80d4100388441095402d4680701c1c0c10b40c0081e1601212168081406401040700d039504401070250300c212808441c904964049240001070207441071001441c0302d150750300045040203400754107a9140c4072a02070203a985500d6000a01e840c02c0c3e2511541c001d165a03101410924150741c0291100d4990150020b810810b03084682c4010701200100e03540c15660170b0248501080f55406241c0e12083c40c2403c80341d80740c40b40d0800400766000d81c5442e40c010f62000042c008001000610f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 219959172 1250 219957922 219957937
    0x901090216031d120c1002030c0d11030d140103060608030a0503061309050111071412071202010e060c030f0a050708060103020912101e0603020a05090702010f1e0e01050c 75
    0x80450810038038003104101c44100f01001031300004a040101110394000030b04001800040b01e40b40380480f0186012a6288644205801c494105a4002d410980100b480403062104030084d01d06100300304210004445007100585c81c00401000100180151881000058405600076600c1c0210503c1d001d4620320010340f00c0c0b4000c083c03001441d60f0b4821150710655409074000700034045051010414000c0e60050b580030b6a1089802401011f02c900000c0e00c4401c0121800b14a41040240c0c0c0f560004442007003484001d6540b0307200399a210900522600b44034401125034992613040000014440000003403202c01981d2401003070186254000c064150f02000c00d2a015039160110f6022601c1c2b010007001e01d10482c40303400702c580394140ca00c0c0c11045002c1765000c80d205e001068100141c060382d205100103034009140e08030a01c2503003401c91600740c0c4030015000114115001282e480704442c0c048a141080016000d8000101e0a03d80905845404490300038840c9040081007070b411480f0300d54 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 219960422 1250 219959172 219959177
    0x30608060c160204093801030b06010c050d09030309091a04050604060302041b1b030f050a1b210f1b030c050f0705041503080712110109030e090109021603 68
    0x360714401000c64000c1d02c4090b580a841804100200e207408101d1150140405200f940891001c0441c0c2201082e640c0880e056610309400507407070342d1900ea0080030003520b1541002086041107010030f00c100a1101d00a07815520030180c0c41c80e6081c020301c100115040844640e09160203040400e050500030320310554101c2d00050030703031200700c00a001030415031310003500715060000454542006e070b0549041e000703568403a0214102c0540d106101d13482c1c0303100020041880048402202403107040038012089542c14a0f0304a4507090200103060010341400320349415050403600151f00046031150082100e5080c505500801404040c042c1911091000380710100032100c9014144520008a040d0346c01c54161a01800c8000710303280c07030341d00c68010385000c3da0038200060010044050404100ca070000c4020341052040d507220301a0001c4c640110040020801c0c62810310b2100f0703c1100034440c8a61030b0041155042c4e018000c40d0901607000c500c2051040c800060300009580320010240e0345031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 219961672 1250 219960422 219960427
    0xf090515090703062c0901050105060f0304020402040504060b0d06090204060e0111070506040e04050c0109050f0907020a02031c110c031e012304060506031f09020a090c0207050a06030608060c 84
    0xb2100320001d125507401044060050300f65945800c0c040c0144402008046070101003036170f91501814203a5000f840f409400517004c0142c056803080302c001944d08640b00510142c5415581c6000038150750741a001812500c600080d040d40220807807140c100144034404c000c1d810285080c00241400c203894107500e0600c8550880105881c40a002501c090301c0000d00706a1a1070300c806040c40340f00c0003120101c40900c6241984041980905465801c6640080003103540b1603100f4280607001c0d80241400c4103521480c3c056000603601403007056a52001c6081c01c80c0d031603d4403403004000007860016140e407604241051481c079100400c0064103080e20b1541c200d0139680d001500c50040c500f416803d0300c480711960180c0c000d0f8410001140c02680601001e01c116260401056219152441c182911810030707450180790f4004d60f040340e0700c003d00091860a01035136031483c96040e40c00702d800e1240147c2010005002500c0d1240302c4a010381100c2c6010055030303017422602a42c898010380010a4690701 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 219962922 1250 219961672 219961681
    0xa030f05090d050f0d020d1e030b06090301050708070f0903020d030507080d02040b070c05042d140c221805190c09050901060c020a0510020c0603100f09051509 70
    0x900c4034009a0641c003004540b000e420280d00d943d05c0d6800c41c0c40d0030005000d1003124945141c410082a024a40c6020f8885407018400b00e0943c002c001000040e60030010500000d54103030b5080c03051500c0b40c1960303198541580341100c802008401a0b00464041c408003907030131310240c2c40b030014a8923459850300304075607a85050700f00342c0a40e02601703140381001c6000090209080d0301107006480007078071071802c400b0740640b103008000642d18950404058203c3c11180c0d82114141d00040030181c81d420400001c40c1140200d0301c5000780011903c60000c11000200507254112040241c20307903c5075456400708403030401410840c00c2500048135044141c9490100d5408003418070b4043e40507513400002c10410707c3c0b919015003a52a180315491060f0440b4000141d180e0140c02401e220541c014403800c4c0c80d9081204012081c03140c00085800c510610000e01c01c5519403000031030140715048240c4c11210700d4015496401703003907034105941040c1814103001004928000103011100222558043c9994 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 219964028 1106 219962922 219962929
    0x3030f0b09060f12030d02041505040501020d050c07050a06030f2a0c1703010308030a0b1005042607090e0106080f06010501050706020904110307110a030f0509 70
    0xe640002600301c0c0352000600c0f0704848010800e2075040400324a2510303581085c07001c8903006074002030034403040780066180400c079482450018985820880004d48038a54444040107112000c51403850104007881460003030031002e800c8a25043e81c5400081c003901c8046500591a460400140406004a15008032a40c0c114002a8543c00000310484650303011348002d031003a000300c1d010b02c0080d1400000440c001e6009607030b40c584038100268a0821221013211261041c50329a502606854000066030300f112085190b88070084000840060700b0000c601c0c21020300d0090311070108007590241d000840d4001d50f03100030042c04e82c032884d11664841c0c2c58400718550740c2c0050010810303903101d00e000300210303445484054101844a40410146e07554524002c840420100c01c0018890344484071031120031040c4000c000304d0302151000760140e02031024540801200086940050300d = true := by decide +kernel

theorem cover : BRFrame.Cov 219784172 219964028 := by
  have h0 := BRFrame.cov_init 219784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 219784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 219784172 ≤ n) (h2 : n < 219964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
