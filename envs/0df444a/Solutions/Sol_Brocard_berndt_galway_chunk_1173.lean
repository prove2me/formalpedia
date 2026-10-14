-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1173
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:35:52.612564+00:00
-- url     : https://prove2.me/submissions/2b2bf7e5-685f-4839-a538-e90fc397abad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 210791366 ≤ n < 210971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 210792616 1250 210791366 210791393
    0xf090a0509150901090302150615030916030309090b0306150f03010b2806021c050306010509130b1503010311040203190f05101e05060a11010e0c151303060207 70
    0x44000b118030f1402092440c002c10f402a030070390250040015403404e0031124000f1900c160070050290710740c0401c1c900070f078096800040c400ca0240c4505580001c4009520040308010b5110395641d400d01d60800b400c4109441c40c82407258044d501c954284094210904003060303140e0790554690b40c1c0811000300080c0034214428006800909081100111603118440d1002000800500140107030340c68030300b00ea0310303107502c0103007003443c1c4002a007481202e10480003117411010501d040b03402d000d03414000500c0251918801c517061540e500302d0401508050034401701107190300c82840c0c150361564868400c100d00806078903104279400000038040d0b0861410814450304141020002c5003001103031000203080680d05a490b0b50302882c80000c07c0c42c0c0d0914008104041c0782240700300c0914000c144415504204032031018051803161300e2140f80300034490000d4a03001c90000345a0407181c03409114101d541315100d044561820480d4030b10002d12a80c0390001c6079032041e00140d940204d07040070400003560 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 210793866 1250 210792616 210792643
    0x2030708041b1809020a121113092406091505060309150c0310120203030a2307051501080d020d14070803070c0308090106060c0b09030f0a0903050c0f090a0509 70
    0x66420600f090719655020340c0c6441e109583c60400c00307442d1040201d1000300c1c11001007a08040d40c08048440c00d144070015007180308010041240b603025a99540f5140d06109040008403c0301d44800309210540200d40083c114480100005055450312141952003801128003541c00000842c9a040b01002000c00d0780301ca84e08010750900b00380b64107001ea40d006440035403102d1501032010815101031119281800d85c010001c0d0300d000c640e000d0a0f40c0600c0344100902c2031801c0000403188005e0706100801c0300718810b5003d0712403d010140c0b01c204168040c0c02440072039100b11001c07800a500054000b00103940d40c00d0a00c00c0c0000d03d0301d8a480e52055080040130710101000f0322103015084170842d0031440c03080e10f450101d542c44124450032507240c0c1c0f141d1000904e188032600301240403600d502e508401d80340c05032480c11401481120003548180352500001d141c14000f0020702c40c3c00e0110040d9203800300c0700015280c0d0990002000c0171000b07003045d00829034030000328540f58010010042c1000c070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 210795116 1250 210793866 210793889
    0x50109061511070b161415010e13051e12040303020703140c10030c030b0d050d030c11010c1701080708120d020c0a080306040b0d020d0308040f0501090c05011202030708041b 76
    0x10100300c3e00d0790103038443c5c11148208005142c09035208045001034145005a04000c441d07071a11203049403540b409005050b1440f556000d0300c0200c1d4041c0503c072581c0f52900342d00e80c00e4400e00000e00e40b07030001c845400d0340c611034203010a10010b540031a824086941000207400b40c001c800319041d050010082c2c0300341d80310b584807041031072454041d00316400d040c050362820404295920140b0107115810900208203820036400c02c4007075802a80b12400c10142841c05418040c2d800c0a0311303003114079224150001c1600c0500c001240110baa0b1880e01520010001e04642841e00b0005543c0d04000b000a4500b480c011501c0c5180c0800766044e12208a0601c1c12100109410300b0520402d920036602540a01c0c2491000580780c101082c00c6085a41e0113880c400e00d1020980701100c4044010f0000c450710707400740d828200410024021840034a00034072020701024540f00014082c1d8071380c84601c0ea5514014410425080e4001c2c03400da61040c0c0000b0511801c4588850a400100154014560900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 210796366 1250 210795116 210795127
    0x20d022205040c050301051006051c05091606050f0403030f0e09100905061207030b13170307020c090402031903030608010c020f01060e01050d1412071401050109061511070b 76
    0x90a0300003a00941c060300c1407140e0152290700341401d1f504201c84c00700c1300180407101002920f2240000f44076159949568130300c80c2d018404920141e58080d503a03164117a000c0c00e80c9410b42158020440020500c41c1070242c030300441c03072114840c6030182d07220240502592102c1012045d00559081c2d1203100000d098800c00d281c4031036107044418142c0255421286040000307061820968141d00c00316151000a18400d8a9a80d0710318164100a01d848424201d4410040008140300e40030136411008180302d64980c83e10350002803500045d0300d4000d20038599001400003684020500f02c6801c0900440d0040000150605a02400040d48801c410b51b20b4448029052a8040349401040c0407071030080c4112a650551045400d00c2030081a0740a02c8480c100000510410480517003200e842c4292200004030543d0f0345200d81045809861800650707907400300611080c403c0341e0140958400811003203040600781e41e14904524400418030481c0c2c1e08401c41940d0401c8060300038441c5182c80c55550 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 210797616 1250 210796366 210796429
    0x604050904030210060b3402030a031e03020717030612030408070305071a030601081b03040803040605060d050d030f02041e0612020c0c01030c0302070b0a02180d0b04020d02 76
    0xc45414032144c410314031705070000c40d50002030422144010340d0740c0680c41c45440c00c100e10314000209241c0318208200c1d20404100180c9060060700d2040b402602d90000c002c0900404003a002c0440c0b1031001054810809540094101940d10040d891580c807002d4685c2d40f5a404682d0003440040c07080c0441c4400709000450007000a018001c1d40d20801c1a5078075582e403200e09003000580d040b03c0c0000c58005000140c0310794400e00c00035038001c03100c00582036102c10a880d206681d910540e02560400340000c07c110170705c2000c1c041e40c2e401100907940c1120400c91a02d8090300c07042640315036000c0640303c800c10340580d140ea40654014113001080314000ba15505a0500d10600f984115000324207018140c11030300100d80f00703680380c10f008400078098020007500110018088040c065007411303824041d02c004904034101c0c0c0b62103024a40f000580d81c61a8460101504281009207480340240f02c01000000d422140d4454100c1e030b05441008890480c1e20028440b00c00850004414604012100206 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 210798866 1250 210797616 210797623
    0x8070c17090a0e1005030109110433060801060f120507052106030f03030103050c0d0606170606010e370b07060903080a0b030303130501020c24010b0a12090206040509040302 76
    0x202d510a0b1341000c140e80d40c405150981d800d468004c1d0040c898410100e80354103164010140348550301602e680d800b04169042d2501102e0704142111014040ca0113202c404d8104104034050b01090030841e0b8843d112010080c125075040d807403146e850f80c9410104214500800c1031380c00b40c85003956020300817030014030088803404040741c86038400c2c031550a0201030401c0200869060f07a800c08082c041c96414002031052141040d01e003103440301c0d600d10000825200200c0b4030400b40c91000c0250065041110004001696961009101d000758400e0034089103103c903400d1001443c40460a1126594a040c0412094699000c000140400550441006a2944424030441c8240c50708070035612041081000c4403032030800c440d0981d01c20008540702010389142004c0300303889140050300e4520100006418402c090001c40011848000e48070600c002c500003450140c5144001c0d11308007515800020400100700c509024415607a10b031007003d544807802117401804024007291080d0400f171a0003980e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 210800116 1250 210798866 210798871
    0xb0c010f06090608070e061c03031406010302041d10030b011d010b040b0d09140d1110050c0f0d090b04111c03050d0b010314090f060708070c17090a0e 66
    0x114500600401d01854501c2501c0581d10484d0052100604140c0717030102c0d8481c045d01c0c069212841e0300005003045030311a40c0d902d80310b01c241e5000c68100c140ca1080c1c0014070020303010905050060205100046c0311021050f4882c000c001190307001d03111807903141d220003407070781018100008510010503451140c0102d440c43c1c094151040590f42e0360380c1e00190a1b80114021815411030410460245955036003140c49442e00445403252140500418186090595110640407420000d10452400c8061106004000007400180940e00e8488400a8903100702480d44a8080003c940c11001c0d0501c0e0741715030282580818801d09900b03040c240250f03402c21342c880083c82071080d084240d0260f41e14042090050360300d511001d0038024030450140151076404032541c101503581c10307181d4020881c4180036000e01e4882e4058504811001c82c40303420300c50b00070700d0142840b40e03000c00c2c030504690001081080c07e800c01016013403100e2000440d9568410039502c15441105920b021030483c01a401460 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 210801366 1250 210800116 210800141
    0x20304051005040605031512010c0f020d020312010e0717010b090f100e060d090b0109020703020d08010e010e0a06090e0f0f0c06070b040203010605060304060213060804050a030e0a0b0c01 82
    0x4041d400c8411a400e214600407031000941c148049001141c1801b416500040010800e40e04030002e001144d003100c1803940c0b4000040d50103140100030700e80500211540450620195140144081c21228400750600c10b40d0724508071900000c01940c030540c440000e078508050312a00c00d503503030b642c0340440390007014000e4810a984080e542c0140b40c0002c401c13441802544a030654082c0c50406c1042d00e8200340000380300d16403603281600c00504445002c3d800380511000050300c95049042c004e180c0b801c0f40703a0f5481030029840044c8000c844084500d81100c19609820155036150380042c0040c2007503174040707950b076801c102a040d2400c1c008174040c01c00c0d4101100722424032042843c41c3d96907240d200111a0040000c00c282c00210f040790341200e9019001a002252041c1d440c40440d03102e500854080ea0141d502154841850b424488100004c3c1280d02c2d10503920304090715000d4560a0041000b02070048421500b14903480b0066440c0061031b03103503201512440454800d074080e0001401e1342c0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 210802616 1250 210801366 210801379
    0x40b0103020f09010303081308090301020f04030c0909030c111306170f0105070c0615120f1401061508040f1502040918030203040b1c060902120601020d052d0a02030405 74
    0xb4030603800e1643c0018101c80c2c00d0b0783c96000c02d40355072600c2d01254544400550360004d0401aa03601134030309000400100c182e03503490703903915441d42c204a546d000380381e001912a182444110350120b540b15265551598001e0a1034607a130356040c001030003415052581944150170301a000425500d038080e03481c68140e401c010703a83c031a10103900e554204d0303800319040004901c8141c03200b0301159642d071001214100880c0106501da468608c92421400c4c4600200c1d4038100c116550810000425400c0710480d000c0c800900905040002d07000c1884180d03201041000480310015045c441a180c120300c00640180e058800100c5d4044030b0710196000f8020b0f00c45641c20504d0055a00d03003494041d0507450f425070301841c2070500303082e042e0240340d003d643c5e55040d5800c400e1625842105902c112001041b82c04001030392000104044110340c0c40003010181950000145100700310317081000c40303d1034140000c03845203031a0700c4100c801c03c2003507000420142e00404184043e145400000601c01d0301d40440d140c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 210803866 1250 210802616 210802639
    0xf1803060a09140606030d050705150108030703020706020f0d110c0d0b181c0513090515011202031b0903010e0a0f0501060509100905060604030222060f03170c030f03040b010302 78
    0x5640c2d804251056900740d0320101c02d16007c03d1042c0080c018062042c42034070302078181d00c92406d0354000d0a030090040c40c3c000003030b18400c040e010005500188064001b6005e6040055112610b07514045511414442c202000281c2c503482445001d507850301c0200b040c0d420500a08054603203030000c450f440d0411003104d07500ca85002e00020382140c0046482000464108214000c030b803a40c019006903884c68840210104003403200d802954810044034001c41824000c56000400c032190034841000640e20420038005070b1540710b0845110100c140030304940e111500d00100f40189408100e840c4580105480c0c10200312211121400490050000f40841364490040000b510800d031040400c501e2003a40400c0455225041554000390041800d400d1a58a8000c54020302110f404400001030854018200b80c00034030555000c0c04040307020f11080760450303584904030301901400c45402540415601d000e20320070000c90300d5824040108540f40c0c00c0a24200444407028002248551602c056 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 210805116 1250 210803866 210803903
    0x908191107030f0f0206070c121502120a0914070f0806070306080d0807030b0a150201050a1109040207081b0a030905180f0907030203070b040e06150f1803060a09 71
    0x7116410381c0d4010645100700d0003941e85031031a107482d0507422600302c0c806005020100c1c804102e00e80c010010680098100046442c160f10705091a00c4081c1680e881032002d5079030f461603850070651000750718000041070511420520075800700490928240d200342c80c0c4c04290f00010884080450307131043c0890315144c079116815420398080740a85586644950740f1070400d20b20490440e07800001c0d80c10005044110000882c0700610785800c480c600c031b203003050240302055091180ea81d0002c43c25004019000800c05210120710070220b00d9807107107401140480c14010340000f03d518520214120f0b002d2089100c442d41c0d1610442002030f0085000d41d200040c050401c40307880c4c020030741015641c0c10183e0799640042d00811010f03003845628070602e040031006840400080b406006191000344e00d60b0b1501c04100c03111200204858041c649031040e080b40c0c07403092400d450001800820080c0c03541848240040d560111034a0143d16208a10620101c048030740e11820029000d60002c0202000516 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 210806366 1250 210805116 210805123
    0x705060406051611060f030412080405101112010303170a110f0f0d141005010203040e0106140d140402010305070c0c170c09040b0624030606030a09081911 68
    0x401c0001052042281c00d1040f001c80d240a05218401c1003409101021140810380d950000d20318104040800020321003485100030114050289629040303a80c2d2400e81d9171036440b403001031a031144079030704e9241d4074501c01d0b000010f441c51215883e0302c000f100d6a5a0500a0144202d40280c9030904031000c046032006001c0c1c0102154204030040f0700c0d141c4142c049144548d81c0c02016141404e480a1000299051301400380d0f00c0c10712041d403000705050421079100d03518050103900c0f45040d0351040004100d0580d180002c2411181d07141841520200c02d484001075520540c1d0214003150700c0c004038164014845214180224000e980401c441c3d9240a01a03070003110401c405001e010718004d0400800712a0060b038400400c0340d2050303c2c030000300b0b203010400c1004192000c444030080881080000d061008850f18175248d140303180d5002c024603568105c01c3c1d10000d06014003030305d070000004945c1070440e0003003507495a12a040994a044004c0a0320768030a1010698001951007080303240e1129001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 210807616 1250 210806366 210806369
    0x14030f060105070201210603060b01020d020606060729090c040203220501020d09050c09070c02090406240303020d020606010e01020d05030a090b04030c03020609010c080f0709080d030e07050604 85
    0x5590950050300c6000065803a6002103000300d0400c81c041e0250320360712203a41d584510780c1240080105d10311381180f5002c01540c0d01000c40c0d03030455104491a120f41940010040c0e00090241c8155039605218200910901940041a2249090540c1c080c0c40c040d05411010f124400f40300070384503c8100ba004110a03071000ba00c1074203035603240d00e40303061410b5401008035983c00e100380001071030000c4100700542914054113090301e094000c241001c03154100315880c203922205a28220001c2d004550005090300c5010348050681741d03443c1041e9009204585101000d409a0100c011a499503858025551900401707504014040c030350100701154082d84065a011505030060700182400c1c02c0d0443d5a030b04001c001d4491151204181c80200c1c07a90f0659500450196a42452020f03150802902d03141000d09100304c0e986c5018011031102d40d11800f0a9000030403401d030300b90750f80c0b5507101c1299002d045400c6040e013800354211001800f03406500030502041c2000a4641599a404c1080032034001c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 210808866 1250 210807616 210807631
    0x2703051b030a0f06050a150801061404060b22053c01080a020a0509040e030405190b0403030f12050708060307050d0822080a06050103020f060306010228211403 70
    0x44040f0f24000820315000150710208100000500300071503060074070642d055911200e4030ba592403d0a000007035450144814504041c0c9081c040d0790310706a61000c180c420038507a800511080d9070070441d207001003c041d400804001b0300c0740f160085100c60000f1003100100c6062000b00c8503103425007149031041031221515030140c54907443c41e5503010b01000039511415510040140070060034620ba078407440f0380c0085e44000d100550700d0303a05003800c0c014841b40a903281e048503110300b10300300b001e007a8400403981680d0b81860070610705d18414074240d80056406004c3c0c42c803542044204541c5c02d0f448480d6601c100000c0b0100c4454980d03c8040c80300b042483d14001d01416010849403080181c0b010410700107010b52503000c9585a1f846412508001c1240c01c1101d829403981c004100752f2810f820380080c14a0304030750540c0f95081842c0080c0d0740d14200da86106641c42e001000160142c9411444a6400d80104903106148501e18100c40d0112109040b600401d5009413404d840c030740c0c2030b01130301d00c641b00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 210810116 1250 210808866 210808883
    0x6080a0606020c09040204152d08060c0412020402040e090109030306060507020a120f050f010e060a0209010c030e01030f0e06010302090c070b040b13330507090302012703051b030a 79
    0x3d483d007e100181c8034107002d111a84500510000b80d45002d8090310085103000c008211030b11f40420b41c10400200f4a83c002045a44000107003c054400002100d0031075443c4942120075540390f20214020b809160700400d4008a000f0800010f6541074000e14405071080d42c0030030190380c4030710043e1218010040d01a404c010445421f102110440000b007290b1401400c01c00030030086907503030038940110031032203002e40d9464034200313105510100031843d00140d591100703504240c0d403c00000d110540010004e41081610a07000d90581d0090380080140d5149442c14000c90761200e86a82d0340c2d90382848100c3c060031074a000103d0240303a002c1607540d03182e408078001c2283e1b11107440700b17051030001030b112000c07880342e105071180050381c3d500401c0702c00320302c8012107038540303d0805618041c1d080249402c10514102820000340c19440000d03001030303d0342400d0100720b404035460403003c0000410b0041d00340001040380030081c03000010350409262034100d000325181c600da5040c151a0500008000d00d01d01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 210811366 1250 210810116 210810121
    0x1020321090709020307050414060a30020f040609050f09011203030e07090e0c01080702060105040e01060503060c07140106050604142806020f0f121b0706080a0606020c09 75
    0x100c40503285504400703480c08980d8240d49603156103040b07138801c0c1c401c0320200d400018104501192580507000342d030403c503002070421801d5003010701b404501644455420086080c0c412140702441c03a9108501002d403021907c0b210411500c0020350f019015030300c04a5004a0000b44515009987c0701c46884054000b5081c0d074603000c9124014541034104806042d2100e00d8a0701c003000401c0f00b0402028150004601c1101c800001804c202e10702440c03504101d100d800b044002600001d00c641143c0c400d6400084515019042c0c500512140c1c01030b0340d1500840b424828451091000b80c24250b0040ba12401101001d03241d0b2422038001c0e100d0a0b81088083c001084070822a91540e084040c1c0a05040703450600c4030114a44496508404440c00d03034000f00a0046546c1000362071008058032009000000764080324680c4c60f00b0a2410001880e00080d01e0042105108440c58600c06070000310b55506031500009005a02c080301d9481640c0c0c0361013000200c807403000501c90010003000d0600040354 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 210812616 1250 210811366 210811417
    0xb18060408070311061b07050a060201181106160c0501020c010c11060d090b0702100518150615040e0601030f02030c03061e1003090b060d050304090510180c020c010203 74
    0x104049450300d034014800c2c0044484050482d0000c0601c14450000d000260704010030000588001c2d0002411a0700d4803070851000c580420dc00245150840030010f104695840040c00d54496014109841c41d41c031891740c07041100303c400040544001b40c00365611618040011a4205002c00c8068800523480c50312070300c0b81c1041001010400700d0305601007a07204064454104040040d51b054006900c01103c22507501110302c034450308400c0c03020b8030119401c0c4080c0c0c015a64045401020180884400401c4890383e4030081580219422071210380c4850762007240e95070000d001c0710201d0120703040c440107203081035091085a208242006001d81551107040a1050b0002c2e4241c0320800c40c014a1006c2c84683d82e00e2400c1348202c0c2d00f6540c0455200468588440405401352040380241003070002c01e030000e90080f05031000d55050102c0024950707940d12000654800300d0b48000c10303074400c0c0107410621038081c0c1c102c4520748229400312419110341c03400480c0e80748114010501b11100d400c0805440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 210813866 1250 210812616 210812633
    0x210051303030509040b0a031103120c210c0a140c06040f0905150316030c0b0a0c150b0a060909150b1602060c070b03040b07020a0506070f11070b180604080703 70
    0x4c02d80043c000048801003040410b000d400d2a170001c1e00c419a4210302d04c0e149142c10800e100d00b203a06098100d00300500141c480e0f84d5014074011118070031145040304031270002d503102a5a0200d4107a02154a42e5a890034040c90048204c0c1d8922558002d03091701c1500c0381080e5007118122403810382d608920910b01807034031006280191040c0012294011a98032555007000709084041c46031000800052640c54001d4104015520840c031a507020301c000c0d1000c9401081c0c207070b1916005040041d81e182d0299204004040701250103500001d0101c002c1900c1c0d910070540000d5401c0b150080003620303484401007081c1c0c05280b081000c3c0010070059000e01302010003a130001c0c41e1010f00070b14103224141c00d14505080190308100110040401000140b04060a0341038012030580060311803072800f5194181c58034401000007040c8a1038a04c45101c0754170841561090350300f01425160324948400950940c1c4c0c0c002c03841d803120300c05000ca03d240c0d580391070401c44d000c891881004054491440d0b0b0340041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 210815116 1250 210813866 210813877
    0xa1b12090e0f060f0d0f0b01050307050a1a13080f0c04053301090e0a02070201090f060c1b030206030a1d1203010306110408030a0e03060703090b060f0f13020702100513030305 77
    0x40080d0b840041c200003886c0501d4400c001c0b1301c6846070050030b41c14202031600e04900f99018a00c101565402041080074206031480c04910481c180742e5120780c040003042110050354080e40d4240300d23886c000c461902c00445c00807441c120450f03041c000d90329509000015000f280801030341c03400744416410111598100b600b0312070501810010030303050f6500071441d0199821110300c5207091300080e40400310342e80070000700c0c041c0000b5a1243c0110f4203060004204c10b030303074000050400141113400c2080361f0048003104015075008020076941d00d0604410409400c2c0110075085c04035810111440c16580800d020f03002c01d6000001038107503131031603c800c1d016241580d000c03026241d08010200f48a901880208400f100e07030740310818500c0740c801c10705150100043c0000300f0145481440c10006180c0d002e00341e0007030390880d03440710721004001c0000d081c0405d00000950150303103102c5075221a09550090900c060017203a0724103100700d1030b410a84452040104407200841202c1e018030000f40914040d05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 210816366 1250 210815116 210815119
    0x403020d09151d1c020f01050703090e090718240503100209060c01050f09280f0201090504020409090b0c0a140a020703020901060519030b0102030f0a1b12090e0f060f 73
    0xd031001c3d0b184001c100e404419030221220204410924015810242e2110016000030700c1c1c411702d060a0341e10010944407a60049160000700b802c08607007100c0d0704001c3e403406090f640c8100c1c1c084456103250b50004001018401c02c1d45405510700300012091804254100d034405000b811082244442010080d0702003011540d020400340144a0114024810603209240b80c841c011a10b040c030740a2245480e402100d065040708156098220b48000450814045030303000300100c0c0c10007105d03c01680e441c045a0010b5400504c08200021104000e405c01d411081c00380c62514090b84503c1080c0c80113220f02c1030240e0224100040811045022800400520806d481961501522540005d02c50002a4400c1000a4010910003800701385280140150304060904114a8003c900040e4417401040c1002c101c0c2c01e000b081d0340c41c580b401408022841064074060072103000e000d103407540c404070285035804009010716901040d500583d9450f54040c001380031b00333510300381d0301c190070803000109102c0c031035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 210817616 1250 210816366 210816407
    0x703050d050a170109090510021911031c150605070f110d170a0e040c09091d0303041a0105010503100e040314030403020601061b020d06020307020f12030403020d0915 73
    0x2040181c3d80c1403103440c060050407070041a03803909400d20b01d2801030f01d10844038925204200c60400c80c980304034440c0603130502e0f0800030024010101101e086000c0c01d0780314a100382000c29007038010903203540300f5000500000c0480306d10580300c91007143e140c014200c00034140c9841c00040700124100e451016480d100c028811020030500b9954131101804400d20100500d20104400400399001032081380f480206403002c00c1980c3c910000140100071a1045103030b45030707540200004030000503440440c0300d280301045959030b0805140450030080e60403415030f0010001d02c004581584140100c0340034040781155804064140540c6220100c8090404c07014000300e000d4041b00c040d041c002661180d4003035009000e0940c90424064210030103040d507078440080c0c180e10b140061740c403015055141c42d00010016202c0d99200c201703030315100301080c0d500600e2080301e1202154000780c80095109600c01d6003650b0140c2164003003a906000e050080b00603454003050295401031050811510703206022080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 210818866 1250 210817616 210817637
    0x30905121237170a0b03150703020d110306040c03020a141305100507020a170d050705010b0a0e010303090501020a0807020d060b0604080f060906090c0118050402190f020703050d050a 80
    0x110009011514950804180300303410305043d500c084440150300c10302d180400d01255640307400198449400d803010081c0702c86844041480b00b4807a60540d00142c01000c0c0801c510b2201d0703400b0703030250f80040b5035040c8180c1c1844050940907200e0700a03188140c1c0c0b10344032103130f401c00034044101140d001120f644007240c009440002e1941d48000d031400d151074041c4c84240d914010b50050084a40690704000340c02000035900c0d03852080d0003da020014030407031074070703c0d202c074402d10300311380034154541c81540d0002550300049010030103d42c2d5141204c0c0f00741c0f1800303225651100166100c180004020b00540d00030f04c1264094102084482200c901c02c80000880d06100d40000d032454015401903c1305600171144101c1d9034500700049904280700200424142c03034408031890341c0701c00740034041b4108400c41c0e480010b0f50741300c41391090242c00c00802c295200d5030448402c006030325022215500003040c5490030101303140003250a10507240c01c2405048118503044054410f5444101031804000d00d00f0341 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 210820116 1250 210818866 210818947
    0x50705011506090510090b09010e03070305060a0b01110f0601090e0c0405010303030608010c020a1133180906090703021606023f010513180309051212 66
    0x140201602c1c40f510303280c03920340c03c040a009000001d458098103008182c03009110160380d81003581c000e11024a0101c801c60306010120341411180d920040843c855a030511090000b0390b007000c0708101007031303036405221031281441c65a01c4040391101d4010390803070801401069150341082c401d0741d90070350488040c0c0c42210085812a2002d0f4401e80000b50386101c241706188080c0106116901517100420390050300f52a11101c40c010740000502c51501c0e031048a40c000c0e110208046640d240c608030000d411316003501c040e07070361f801100d103078181c20502c00d4042418941460303418059803015000b121595540c1c40140c00940c400f940003070106020801540018400740003d10b0100300f5001c0303d1807400707001c0e0020920312645404000b004802046101d145415401030541110703411640a00200220768540c401030955103800340907150040014028542c2141c005030850b6000e481d0440a0038280064903140d62810810750b10024003001b2468010001010130900c0c04040502104585070340103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 210821366 1250 210820116 210820151
    0x30c0c030506040b0f01090209031b031606091a030112030309051c09180902010f12061206140108010b06180307082401060c0f02060d1d0109150c0f05070501 69
    0x40c3d044812840c0750040003139803c4a03601080c014407265606600700b5094000298a8180400f00d5078415409400e01c44816941000071030380440002801d405041d03201d81c401032843e60b441c091500440c0315400d50048410103a000c4904036000390f401056034810a9030102c0207403407400d2040d640380c4908440450418000104250003d90b10f40b944040645071400b84481407110318641100c00d40741080c0d880c00341c3d0300f15448018000c203d00d41809804080354808006117a107401c5a8100c640d840443d00400100354041410080f059881038080d0307903902c040c04c2c00d0f554090b443c16040a0148a07004100c448095000c1d403c04004065400241d11415010700d0201d0074122140240c100207807502450000d00c40580c0500020b2030080d01010440e1662007200310451402801280000342501c26400954070145201003810388050380f04000c0c9036040d02812582009880b1000c800d04180c000320b15074410b04820300304580b03e81404120b814016036198000c000203036800d540303c0c00103000c400c8490 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 210822616 1250 210821366 210821371
    0x60509012012010e0906010308072f010e0301050601090b090604080a03030209100f053c0d0612020904030c0203030c0a0501150909110f03070302030f1005100f03030c0c030506 77
    0x140751031034407075820b0b081c04000074206a0000d000c849007403060114002e0041070490640b0f0300070383d85a80d940598604240310341d030300220090368034480104044068005421024820009981d420034080101042608980c0280c07101c9010480c4504108841011f03000548066180185000c0c03e20740c1d503204c4181060708025089002a6000030812564034005114143d240c3c141d00d440e44001494410240c820b10641d10310b0010054292203401200710140411080191000048030741e0704205c65203483d007900910380d5507000758200300c030105112914030f29126400f50024044101c0b40c81c0d940301074070a40100c910a9030540010881c1c0554003104004050143c3d00c11000011229003603000202c00e00d801d5041100024200a0b5000100b0450f140b0308040b0312084942035225014031000034500300d10340d44000e405000304401030399804000310791060903600c40030381441036544030100d03c4c0c00c591143c019401880c080500074030100b80715217445410280700780d400390000c1f500d0b03454152504104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 210823866 1250 210822616 210822671
    0x18110d0501050411071509020a1206050406060503030f0d02070218040f03020c040b090f150d0b0906010b09090a020a05040918110f1806040207140708011103040f06050901 75
    0x5510040040f4180740c401c480600340c031441071a082c0002669203041d0307021141200c40304140c4909050041d9624201c4200040c0200305101200074a145060406018100d030305a6006150203000100f5040c0403003250b440e10141000703140b80960b92110f0070020340080c1e005a800480c904025101501d1101c0e070240294000c45a03a0140001071500900c7e00c06a03d4407540682c1c14505601c0f05038881000b42504044c44941c1802c03d95940f04c080c17101001030507120b80c0c1c0420840c99410601c07400013801c40c0141d041d030b0f040e526207a0f26500305207580d1281e29040ca41107180000007600d0640f45130b0140c0b000d928917240840c54a6a12807441040d14440301d641144d402c044003080d401c00c801803265000700101a20044030700304000c400180000412540c041102011000040540c0d42d250304071900194006c00302c3d280c0204101409540781c8440c003e942e025849c3c01007100190812034143ca204030760014164a0300c404a540d404041e01c0040d2901c4625900c8841750118580008440780a0000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 210825116 1250 210823866 210823871
    0x901182019090510060c02040c0c02041113140303040b0a03021318050a1104060f11030a020d0f080f0601110a0b07031a2e200304150503090718110d 65
    0x10b015858046800107003018104080a503030421903990401c2003402c0454048800141e0707010002c0c400c0d5003410710504025802450070b008506246d28203c05442d0040c11840300401326500c6021469400803040040b5a060740148070822107004010010121038140b480d002d400c14440c50fa106000d44071035008900a0204601403c50f0101548201c0d54002241c820920540365140c4541500c2e10540c003034281007200101c038181656000f001c12482225820048982d10034581800035103401130201c84000003600080418906c505c107011247c0035100b40b1b0701103040768480000544400c041401d409000d400341700d414902207080c42041c80e119072000d440108850662400b101d040902210740f80784070300541658100b100d001181500381031050000c8525010705404000c0d44c2c051280010b46800c8815081520600c3e5000b001a10803201044615150b04801d41c000b9213080c0030480c0c0910007503110110070070012400c100e00322210460359500051184070782001d8002d96006941e134080558 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 210826366 1250 210825116 210825119
    0x16020624011b03121103150f040209120705010906020f0601050d020d0f0b06120f030706020304080f04030809030d0f0f12020c0d020c0f01020703020607030503040602090d0f03080901182019 83
    0x110140101c18207403002c81710715072540c680304100380d98091445e204540551070150301040c1d02c0e103460b41103c00340000204001c4044046440c802c0d1f4031003080c080c0a0016103060300004a40d400050203a40c0100385078080d1003140e00305414013441c040194000e03a40a080c40140c1c0c2d02191280201c440240d000c1c010f0540342e882d01d0024440781411101c26880c0c10f900080c2c8224040341c010003070f00c07203255000d1005a0389031214100500c0134000c4441890350034500040020400c41440010860310300280e080d5400e0503003003034083c0c03101d25040600b00046070090741200001403003502045180180c00c8001030134401c0d9103948a00d881860303540d14002d41e0103428401c2c00e030314001d4074411030a4402d200501145003503a0100e000d50041180080c24003c0100210b4208003998058908021004d4100e402c0e500c504d00780942c1c80200103a00741c02003105200450030041042c0100108450702d510919003140d0295075004810700d50a030b043d601a485e040781d02c085039940702c1408007050300d6581030140c02d0707 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 210827616 1250 210826366 210826397
    0x1202030a0230010f0609030803062404080705180403030216051006030c05090423100908040303030e0d02060619030c06020706020d0f08150303070f080316020624011b03 74
    0x500040c4c02080e0820600030b02000000c0e80000d0741011340b98440241c584948a00000c00c007448045852040344991280221081c03200b41d8000d007080310030340812500e040e41d4800500c0740980135820308000301400e200004d030102e402030b0014216101c0e10711400c1003484182e20b4050401c0c3c02c0d4808092200c1d100d400420a00c01310314030b0f02024103021162844c640c02e141d5207401b0382c81d044003140740642e91034841c25285403000b0b00c40c0380e540e0100ca10090200c00898600080940d01c24041100030038a043d000b40080b00f80025012280403060f001081c003500c800d001c00400f40b0441d031000d00c40034000240400054102042d05009100f02d40003000042d003000e80182c03c01b038071006a01e041000c54044a00225030108003d40c0041c0d80405454103640240c02090643c81854805800303114071141e11410404188010740c868038068261400559405c0d80803038072043c09543c61100b60801d540c00c07102c503003000031020400b140305040084e40002401c0701710122020700c21055000c202c100c061403031003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 210828866 1250 210827616 210827707
    0x1709030316030b0303070303110f03070f081312030b060405060c0d17090c013e100608030f0d0e0d020a020916050a031a0307030f1104020306011202030a02 68
    0x40072030742410300c1a031a044011036039034005d4280140c1007588880940f000f5040c14012907403000e200268603680c900c0c040101502181b200e0a40c00b0028240d4400581241d03805402d52162552100120016410748201280507001c040101d5610150800c0300241a6580c82e004051028006001c0c107004617800802a00c041410908043c1c900c40560801603509408114140310f13240908141d0641d07050301140e00b0f40711840001e09810401d2440c08410f621400c2c050803003506940703108030f030801400c1c1030175901034554078030502c0500c0d40180a030f45030050307501c005410368038206d0100041c20301c0e40402c084d11700000041d4200c056040300000e41e05608200640641c0304a4a0141c070f032480480000003840e500c1140c800100b0141e42c3e1351b100046100500402c0c56040c801001c40d03052649a051850001040f1502150340000c01c42c4000c00b9402d01c4c0c000d50344201016142e840600c1c811540c0580039600040c801583c0c65420842007910703030a442c0e200c2d400702e4851304904504140a841403400c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 210830116 1250 210828866 210828901
    0x20904030e150d1b170406050a020f030403030b13020f040504020702060903010207080d11040f14010c05060712061a1911191101170a1d0604030c030f0306140405060117090303 77
    0x411601703c03482070301710001001039600580e00080015007680d442038200c009024400400145d0f1070f000007030205241e45900441c3e0317808000c41c0c4010203540c00d07a460b90200d10411a84a0b00d4880910082005281a601401503e800500010b1030841e1440000e82264001c83c2c1c03c40700e200c0e01140290315909a48a05240841c00034140d41c0f40a040203860410b00c40c1c244914184074442c1124080603034441c4013892001c039800700c1140d0080c104844060059040d400259460070300e44040001d440705400e90f01002c0e013003281c078428a07092050801040b0b000f2a0b11300c140a0008071001070b030350502d041098207002201300149007800621843d03c410000b18400e00c40c0d0422130120b1424803180c41d040040d5810403911800096035144440c038408101e40070b010b54000707a000300300820085c5a0001401c8604910943c2d6a42c01d40c5a000c07010703000c80700306000d03101e140d58400700101701e981420b6211540100341414050103210340415185075a11044401c400141c1000c020301c000e84403220304042 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 210831366 1250 210830116 210830171
    0x30c0204020a09060f2c01030e0109050c011403060f09060d1b1a070309230d080d06121119080a210504050114030c1908040b13020904030e150d 63
    0x2620902001b00c110765940700200c0c000703c201d501c1000b00368000e600000415000c00000d206184e070b113050003a1100030b07101c0c071030380890307400c49100b000c9000c1f01c012240701d858000c1c00074985401d040244554024024806ca400000320304241003c18100000c07410342c0d440c0f0244101e12207040c000000e0459052411aa051500502c2082c00098022a180080d0b81110108a0009200c80001c00d0350140b005200c0790402c90764400700090090700001800081c802920901145a440340766604030010524060070014030341d00f00c2110b0f444c060b902c10a00039050700c580c0155940f1348826904000b044081103485041c0380d0103540518452020700b10f03151440b410a142054a801d00292075030f450504402000d500000018014035601800d4900080c10711302590200c0503101c8000d4000c140541e030680e907200740e5030001784900072034101712885c03a0b40c05820321085440700d980566203900c1b0814501c0d4000c040f041c80d0241c40c0140006031002104603200481c02004030b40c50b1020300c244d08507858 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 210832616 1250 210831366 210831377
    0x302010906140307030e101401170a0203030d0b040f0608030c0d0228060e0105041406130f02040203090c100210150b0f1602060d050717040c050409030c0204020a09060f 74
    0x200a1803094070140c82e44880f144c02e02142c0305508248840c1000d200204141c4024239000f013050082110044140c1a01c00c16807490001003050310280c0e0b6240307210f11000b5815442000301c20390410564000c40000b400280c00407810407000740c81c0070169070080d0000700340d640c00402c0c4410300301800c1151011b04d01c4240090048070101c01c0b81210311b1080103000301040900c0150030010009c0c41da0110588035641c00c02040141002d00d010385804e150b020782c600c3c40e40f00300b5000c60b585040140302c82840a62001103440043d50546c00d20001e03404c020012400c902507201052402c2d100c454048140c100705a01034030001e1034140d8403008892400075185030032030340c600d002d01003442c40000b1070f0180c1060030344490f101c0412840c0524080303440300b40290000c5004c42d4240c52902e00b0340289000e1462031321010200c48c03107074460a480c028220b40150200d00c0c042d100304602d0401340d011040617802450040c0c0240c1a5401080c01da174010685400040c40f00d4804104550303002100f4030f000721452508 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 210833866 1250 210832616 210832637
    0x203032205130509060a0c0206070509030307060e060103051e07170c09091f090f02061b010204030303020909131109130f0503120907030819050d0e0a020a050f1c1703040c0302010906 80
    0xa684409c028100014010f00051403181030b41d0170020340b4901caa01140510034160305911103a1101028403040340c0342d03c1450070b00b0120010b04d008160f4005044002818120319240540d40c482200100e180401e00542020400d103864486000d0703c031340000c00003010144010509070100c02d42e1101c88005583ca00018140010a00c0b06507000c1c2c0d680441d84075884028201902c009415a4401c0d50010b62000400004040d010380143c039000604480d410000d542d03554400211400c4e841d4010003219a003800d884162501201d010f4102c00d810448104c504602d9403462408006101d080e24160300102d4201c8240b0032504215600c6006200540005403543d42d03010390f24050b13601d0002e90000141040c0021038410410f0321610401090280030000101049588480c608081640a4501c519000c103180c20800000088650044e15501c446c050140520900d5000320208441d80c42c0b0045485017808448005507010358080c15005039010300e14170014046904d5684600d00f4070808014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 210835116 1250 210833866 210833891
    0xa030504170f090904022b150608100e03040902070309091b020a1e0c1203080115090b030417040b0a090816060c020a0e01080f0c04090203032205130509060a 69
    0x3600d420b90f0050313071000703190340b510710004400a00383c1d0502049007404500e680640c81c0070915200e401c9005003484d150b00000000504283c8049008104103039200000599480c1d00300e5101c01c21001c10344007601e040c15104d1700d5920607079000303007800c1d00000c203290002e0040d002c06116900504c0140c00303114001307007a1131001a4440780c18003005458000005141c10802101028004400d80d1202d2000b40164032100003c111050f2104c00b640000c14050001c114002c61402c010040c2071552030715040d06103811400900b50b44010001c4402c1040d81c40203411100c1118054409401840c1c1d02e99125020075400424014550f4401801944a400c0c40c440c1424443d020006507402454624842500c60000c1100301d10782d07610100640000400000c0c0c0640c1c04200d0001d041c2403802900c2c02001c07100200820343e000080041d601d90410404150603012100360302008010302e001c140c01e0182e4410001d001004e0300044804540c2d00d0350200900c900090000d2030b4040126901001603012741030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 210836366 1250 210835116 210835147
    0xe0306040b070516060504080307021009080f0714060a020919030f1205070510051605070209070e01020715020a06050718090c02030c01181704080312100b0a03050417 73
    0x30031200a001c0c0010b404001e00c1501c0160304d00664100ca01400350742010316012492342d204665100044c05100f8006e0307286446809220303002600406d00da8205009501c101406610100d02101e01a2040e000c02c030010341c041c41420700c41d66003000c006840742000020710104404003211641c3ca1f048440303050000451602c00c001e030940c0c1043c1c3d149118000440300ba01c0c00d00c1106000381c454801c014a020401ca880d07005640300b00c120502240910f0f002c03001c10351b09402a4070300294803245103800254054032601c41e00c01880014411210319a07234402904a0400700c0e00001001608088404020301505004450300f000315032424801e2083c52503500b601d9440540070300c43d65140c56001c0003803da4420019a1441c1d554840208141600c1c0c12080a0040c0031510841303400000c108c071044200c881d003040e1030868800102031868801c218a111104020040209540103040d100c0401d00c42c6140020782100070858500140c2030406003014485d034452003c0d05481100100315170801c410460 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 210837616 1250 210836366 210836371
    0x909090a020423070507020f210d0f0503041e1202060f06011b02040f0b150c010506060903060403141605060a15141311120a0e01020403020d110a0b040f060e0306040b 73
    0x2841c0041c5c80780b1b658400070340308100120910794000766a00d00c102084541844914180e40c03d5001c8a07605901014282d0789c0154400109000c6503091002502049609611641420041542030000f80c01c5070f030744100c1c0340e840e0310300306005921220070403440d030100481081c0c0214003400c0920942101491118210f841c0c01c200034000c94481c0003c40603401d654004000d40c02c0000c007505103004c1c450300d00403e0b07500001d4103190250300b07000210b0070900b006001c90303022144c054040d01d010756079603c00740ca01000d01c2000401404003040745044000c040da110302400da2040d0080c140c00d04107441c0f004182d918880703460005014507441009401c031001405640c01101381c2c2c1d00c110b038802c410110002026412071018552070b00092800b019440c18101ca032160101c0942000000c040b0201d4508034022030000940014401c0c50300341c0031440e0781115422489005000710140c035200c507802d040030303040780e070100c030110b450203100b0700c50690071048500000005070001c10440c6007544540c0b0300c1c490003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 210838866 1250 210837616 210837631
    0x60819150b0408100f05061c05030d0f02030402090601140a0e031c0503060312030609010b22090501290f0a11010c090512010e100e030909090a020423 66
    0x488409003100301403000c1100080040900003915259a0304140d03031107160500031301c003100340ba000c10700c0d403400250700c12180643c0c0050480c20341e00803c800c0084c000c00260340c1c190340511042c0031595150101c0d0040c03007181040500c0168803030401e8070611046201c0a0300e600d051081000c02c444061110f0802d5031000c56180c0360581c1740d0515000401c0c10244000050740a903150b0004c05200c0d95040320041d80542c0080d01202e01411200e040d800b2140000d4606aa00c058240c00401880c0d05801c081d020030481c611140300741078035a100c1d020000c00e80f6400f8072030b00350705c8000402c641e00e1625035540b5240444044400840380d14076203c7d440384580c0d403005005081c0442d10443e0688610070091103261880b008100d40403003104081c201c0c0c481d61103840d00c540003003103455403411018012502e0100c05400100302100707401e54940302510454048917601c2c801813000c1c5181c0e40d03038145024001c0611070003a003460045401400140e410507420708600595160800c201c007034500700748030f03882b008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 210840116 1250 210838866 210838871
    0x70305040b06060a0e060309012007030f03050a0209120a0215210c070b190c0f02030304060f020d020f0705100506030a0b0603150702010f060618050103090204020d05091501060819 79
    0x70705203000c0d45d420820320b0300c1e5904000088104814414154401c40350001550702c2c0c10141443c80300200e60501c544440140020036118041c0c0c0c0c480d019410550700060180710250419503000049022074003210300321030103613021441c40c0c4194103158840f100c20600111300302e0710f0408081d00c60100c5030481940d101c5840ca0850000f41a496640c058a8441d5488481c03070b072440c103001c5004401c0103100105800c4040c40c1148094010303000e000c1c50700e40300005070003560560351180c1302c0100821000b00010f42c41034003000b2540001046100416007040d400300e00546403402420b00a1802201c400150042464030f0240b01312a0350006d08020016404910240039070780300404a400d00d60746800125084841c1c03c14007907110f03010341140351399400c092000c204c02030303694000b1221040c0c0f0800c2e04200e090016800c0c0b203a035200380c00c00218240003a001515210101c0300010480d0811904c40380700b50031445145e410300034250031460052806140030542800d1048644150880d501c200d440c900b035 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 210841366 1250 210840116 210840127
    0x2160e06030307050a030503090c100f030b0a051201060303031d0c131b200d090504020711180615040308041809021f02010f05010e06240f070605070305040b0606 71
    0xa40800441d00f80a5000050b600301c481c5600c1c000d4281d030425106820a40a00d015024080c2040ba8246403a440381f603540c1210201c034080b081d070007400011485ca0308906c1c15070011480d900c0380c4031211004010240001146440c50400070102d40c00040785816011540d8004e60780303482c00189211003a981220700f005c440c5034007062a03005200f1884038480f1003038901c522211242c0c000e00c2d810411000035640c03505005281e1080c1e61224889c14040c004101240c40c103000505141e4080d180c900d1207203605600007201d40c40014101e09200451030461a0b980d4100300f03050610340d500141400800d000d81d0304160440e80c2e030080e00d00070b5010716004c0d01d05610140c8088942c0c0c1d041690400c2d0054080e0240004c10f0b00c0030002a80c8920005016600348241000301c2e03240c91160724100c40104a4928658469004210600c0b0441480300c041c00020035558079802d420700014001d040380000c40a41d200e4451030120706880004203132400f414034100401020425054000354880e00842e4140e6540 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 210842616 1250 210841366 210841369
    0x307080703170d05010323060702060f0c1201231503010b0f0405040207120305070e0d12031103011e061b151d0a02030715090e0405100f02091002160e06 67
    0x14000c0c518040340c07513410000000706002d171941100075250b25041a0160710407550501c99600c0109562450060b4000e4001800400401ca401900300c0b08282c912032820101801044410400380c01c010070460b11040a0100c40510b103080d1500076006a50390b0a245001c00700e1183e69000500c21070840c3e94000610142c5000782000b110083d2000510031515048c290920440c0a000320010380082803504000c6221039028007a85181800018100fa81c1f440e01b81e43e60600140340513041c98281502c5010f81c4408000c2180618041e000e0400c8440340c038100c04c151005241015800081800380303060ba15101d030341c2c0c2e03070014030050b50b00180d441c02040240c1c24600010302680782400303615240800e241c002a840450141c080301e0013141143c0403640c480000e818001070020000d004500401010403840a84840107030744075024100340e48003010a29008420346d820340014410051380024034141ca4549000f0b00c0240449520040070070004000e49510361318046d01402c2c1803044114001a1036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 210843866 1250 210842616 210842663
    0xd17070e0402180f0103110d020d151509050108040309051908070605091906020a1506050306130b100501020709020d060f0b120702030306061801021c0216050307080703 74
    0x40e1100a401155114056103402e110510b50182261140340140d024010700d610030300808203400c030343c8280c0d5480c20b80969960130080d1b00c41e010103116281c96070412140e01580c1468030000301441c540c0444080000c0e2001401d010032a00000d062000302e009000c00709910281101c03c2d508141d03800101d4001621000806c000b050340b050146120380d600218030303d80d01c5400380000c2c540c00e40b540d130b40f04001c04210700c061588034042d403030050b4440a0386e54086402143d44082c10300407280d0004120744c880c0c011030b0401c0000c86554503100d01c400402410007c00401c01d6500c1280d01032020307500382c03e110000b5100d022a100c0c01c40a140c0120b13074262604801c3c0d112000400300a50751f0500d80355a00c120305a01e4010010b94030304608213400064149001000301c03840b40a0007030140303190040001054229048602c8414114030856001c03100c903410620726844d19034006d4000b030004841e061714402182413550402c5000303401101c01000200c000040c400162644081d0484c002ca01c68280d5811 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 210845116 1250 210843866 210843887
    0x1903121116060b1201060312140c07031101080906070c031101110d090c0602070b0405041508010e01090b1008030d09030314070e030d08040b04020d0303020409020a030b120d1707 78
    0x394040300c41010002c0d19071065015150990701c0344842a09135201e103080f640e075448060003240070700300c80116083c4600c0fa160740d07092100680b03900f0700a80011662a058a641045507164260741c0345c401e00e0342c0c0003450941d100740d034400145210300c2c0c02c3c40c00401180c0041700c000c0a21002906458071000290406c1105080c40c08240d070300c43d5000e100001c060a031104040e584036203412808242c0910201e4000103440c2c40e0040540f410386080103100c020011560042040211254007060441080c02800081c05615002007a43d4205003407400262801515280010f800000204800d0f80e0102c11b17984083c181d004001181e41c1241410b07809421001810360303013400b50104004a40787c00c18211010b16101f541100c904c406070300342c2034514031000e540c0030340642000000180145000c0b10321140d664070a05e0302504045d961542e903020b030380016108a02007501d42c0406c0405003415810822880a13030310042c000c10390000c101420781c0168024200340c4e81000c200280301c250141c108803c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 210846366 1250 210845116 210845137
    0x90d030908091305040c121205090109093209150c0405030f0d0f03021804020901030e030301120b1005060f0c160308190c0210031e0e070819031211 65
    0x2e4140940e1162400a01d01205c044540f10a10b01e8003140c003400b006030292480d50301c441481e80440851038195038980103070180c0b0381004146c100c04107820407107018641e4548200c10003010154140c03c40d01c281501881c0b80840e4100024042010040c000a00c2c480303080791002138000300c2e0321094441c0700c842c840c1c0d4010380d4261144017050200864001581d81b0141810b44c0c07482c048079040c1f10100e003684a1640402d44041081d031011101e460294014a40403070b05040020380040040101800c58203b40e004403079605442200c0030074802c1030300c41c40790710a10b8040b40540441c2840d001818900031044201860f11000c2207203141084c040000c001c244c5011301c00d4403015a0b692502d8a12030380a580031100980c0e50f115052101d60190030b24851650b03000300186c0d640c81e40398504a0040075920000402c4c429040d1740c60010302c034075200d00d0400307480101c05001c85900302a1807514140d21600c045410340c0359400740001083e0300168214040d025808041040c80f6498040140b46c05480281c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 210847616 1250 210846366 210846379
    0x6150a0305010903050307020d0f14030702010f0c020105060f180f060d060207121710290708071101080114040c03111206041b08010b0c01061d0405060f090d03090809 73
    0x301d0034145c02501840c81050694200c41141078001d00482d201002800c80c5004106014401030116151101440e4040c0f110f200020352a00d5000104007a1100d0084490140c2d5551051051508113281d01c04145e500c10356006240c0706017455107040200004210000c2c240d150008140541e64050841040c1908001f055451b005107003000030032807079840b41c20b9000c0741e01f920008043c00c1510603901d1064180305448401240340c0f40e1040401c0030040e1500002c40c011038505100150840b0152907c603009070b207680c0d240c04181c5000c89400201092450500403504010010700451108000f85200203680100e03104451130400c0d000781481410000b00030b00003190901d031904008294a204140c02c4074140890030704039030b101c15049003141000000036080c1c801072004140c40c90062800c10200c1c4000144503a07038a9120b0003c04d800d81d404010707021404140401d20204024090b0000308400c0908503900303140807420740e40c00c9100302c502c003410788440c1c3c0f44042c000404151800f041018010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 210848866 1250 210847616 210847631
    0x1080a05063c060a050a030f121b0b040b090303090304030314071502090315010b0a05161407030309060201061410140301080a02090a0c200f030a0908190506150a030501 74
    0xc0109000103e403c140101c41010000541d8a00312801404481e000721100d030b00d1080a444031801030002d1a08271050101d04406c03c103183c0c44612140080354000c424048141c1401d2070302152001026000030f0095005006007c00f080d03011080390b0071a5414282604040d20ba406030300c1c814003c2200c080c0c4264000480804602c03030f550010000311000318241c42030399903070f400b804206000a0141c0740200c070082c09000b28540c0240c00900e503030040010007a0403120185c0e9400d0900c41d4400d0521020740041d4010020103400040f02c40250400e40000c2c0503075070614032440010187d01074102d108000e80b01c1c2c00e881c1540907006040300c1401c4a48110b0356580c40d030b10011769690b074055040340030382011000910011401d1041004110150740c52001241004101c01049100941c201d02039018400030504403080070402803000b0750150700c561200f01d03d400b041c0c60420303802005412860440c940c419001402c00b05420398002d0504002c0b40d45100c1020120b401e480350341c2c2000f8401d43c070b001310 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 210850116 1250 210848866 210848971
    0x11214060f0103060c022e0605060d0b010906080603120307030f0e0c0102070603020f030a0902062b05070c0b0708100801150e1b040e0406020c0610060801080a0506 72
    0x245040c1c030300904c81030181d031400440c203e0f07036140025804010300d00c801080d641a24030368400001025407410380490143e0f100c0300041c010743e004081030141c41d07660303030b4103000c40b035070032092038002031010b81404e080d030780b81810102c1d031201c01c01400c242c00d082c00000060301e200d0082c1d02c09025841742c04410056010f11004103641c581c0007103191800b40c490000e001503d503100c0c0c0200e0f00080c1020002d0b90654440007000d002409061204980c010810300c4000000511282001605180702c60081c1c01c91854640d80320031a40302610100411900c101382101040c15540c555400160780c0c5401242d0b0740e685040b00741c0c0c00740141c03c103403480d501782001c5401c030005800d0481d003590101001c041e0261640011842e8800380c3c0311400501c40d5040c03108106894041c0b006503400f0b0701501003d4900408005a075040c102c0c00c0358989880f4490301707401c0c444136512004250151020000034040070710262030352583c03400000c014036014594000059541e5801a1603170152059003286016032890076030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 210851366 1250 210850116 210850141
    0x30f03130f030806040f1107110d021302041d010518060301061a1b03040f15050d021c0c030c1b05030c0d050a0206070302070b0703050402010e060418110c0601121406 73
    0x35134062003181814040e00e0600e909114841c07160f415940403514144075a601c0d20030500a40c01c4499000890454071000358a8028441503c0e4911080050382e4078148164009101360720407500e03080c06d05840c0180140d40750100000040902e90202001a0741d810000031302602031904000ea441d102c042c4840e182003c828050310315200360f481c200c4004d0100b070710420341e40c2c080c038030800b144140e1005040114190340301074101400d4007440c040d03141040104015041e40c0c0646040c01c5240c00d0318101400c0c0000c81c1c400d020300a08280703818400096510b4004146d058400d80d21285c003260742a02c0400c100c07080044465502c10701301a50600c0d10b0030180908940c01030400322016004820020340014400d1003151090703644941d0640c0280c941c2c0c44110003c00c4024400c80c14068070000c0741c4400d5503147d02400090080c1e040d0001c49284030031009080e034250800390341c900c29050205506030040450400e054900940c03081160344030340c2c10150203201112180b03031144c0c050b0000b840f54199080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 210852616 1250 210851366 210851371
    0x90f030a020f01050f040b131703100501020c090c09040b0406051206010e09161512140105040c0801030c0306020f1308061503030a08060f01020a060212010e090a05030f03130f0308 79
    0x41e4000c114035034541c503417041c025000302d078024003040454001514a07e4a100e0030a0700c103019014103200004c2d1224a03c940754800d44401300c0a0a10078010841c80d070341003154501d4200140c0318500182441c12500310940100c0941512868584803042c4040d243c561008005000c0244141030462002d940e41c0d803196800e000b8144403c4006000071840c9000040c8100241c0b2110128148c1a01e04211a42050010401481005075215445030040b40300c0c0202580014104500300071545000104000c03103803150034031010301401c8001000401d038209402c0080340c2e08038001503603a15071880c800c03129204042d030079110b0b100301d013001042440c40003516170310800600400d6008940d14500709a03403401219000800182c8840029000b41030100d190518098180104e81c451200d40d44e503481a42c02c07062618080982d584010081c031030062004175013140e0148068a692100b80e11b81f50388900c2481c0c1c262282d00800408900c80000e400c1004141c15005000146e050825150080c01200107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 210853866 1250 210852616 210852643
    0x1415010c0501020310090e06131b030213060608130c0509070318080c0705090606090f0f060f09031002040501050a030b0a051c050606010206070f0804050f070b070314030606040608090f030a02 84
    0x13001c1c107d840103200043c2c2d49000301e9140c00e0000050002d5580c600c400400700003542020003030894000016212407203030741d09881c05c0580c00307d9170714141040200f440f81e0040c14140e0350360001c0020b0700800e408160301d0007510415a011600d5986446060b80a4100308502c101040040d480e03a50074466540090410740070410309461031583d940c010403049200982d0307030540c45002045158441c0c0361101280c0e11540b0090035910102c011440011507030303045040b203a0361045c80021125124a4240115a03042c00d10718800c600309400c10000a10130300800d00709105140c1c0c0c3d2407503e80c090740c0d0004040c00800c4008e129404200c0c0403020110044000c5104a8440c410ac6010528660001c6451441244550368040b41c0114031001201c1c1c00001a209482724024014240044c0000b03001800180c05104c0ca1180e40740321918001b400c0182d800d0119041c10400d0041c400325503165000c81e022100c480c5882035240d110480e2083c108100200010b03a944400104222001d8000c02c002180d40349 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 210855116 1250 210853866 210853871
    0x5030a060e0711160b090907020a050d020a0611070b0c0307020102070f030306060f0903200114072103060810020a0e180a0e0f1903110a08030f09011415010c050102031009 75
    0xf401c1850604900c0b2600030802d185500340044c46c2c0318140042d0176070340081d292044940f013a00c00e8450303909281503205060016004502d00d0424080c582c0102c03001d001001c0c41061404e401070721000c8101e18041c08121b07983c1000800715006034400d40680d418030f074100030720404100c401c0c54050000c00340b500c03941006c24a10031a480450340945003034400c0b60b42290754040060800380e40c01c08408150b91f015418414032070b419040c40c44426028050302441040c10041310381c2d40414120000e680701d10b1800030581000c0091101383c5009c00e42402c003100540c030160b1107003507000055516107400c10445801c441da0807e002204d031031040100d800790303400e95000c0011a8224001c0394595035565450784541d8041034000b1440d00e080e8040038200c0740a07247c0b46141e040262041e50600c800000290384a50011040c090000d00090700c158100300e190000300440c2200d440c0050180100034001e030691001d00082c0c901d240d0281e58400f5056910600840d41c0389401c3c62804140c40300fa0180d120301a1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 210856366 1250 210855116 210855133
    0x3010312020d12050903040e040b0906160914010c140606040b0a0303140a0311040306140708010e27101b1103030a020711090a09020f0307050105040605030a060e0711 73
    0x50000c00c080345042c1c07450362801c0386004005407600181201915008207072108000c001414101c040d54a40075030300c034016800850511400c0240f030180050413001c1c03955112030714007540c3c80d040038000080381c17482094007140000d008016261345206000182040d01d90903d64a0303802004034401d84200d108a4041200324031220074001c1d040c1d0940001008602070100200100c11110f024251955491a02003040704007284071895a8101d5801101d03950340301c1d01c41d0901c22807519080d65011740c95282c00400c0350b240c98003201c5801000f0380f6200e000801a2091708102120071480ca214441f500c0407524060600010503000b40a40000c0c922000101600c207109540701e100030901c0c0300f01c0c0307200540c2151600d1410707500a52001500301e46500514800c2402c40c0c90b0001003502c284840c0100245005046c014003114038950021a4484d801c14071050040f07a0700282901c0c19a8218030b4095160740d10401100002e0080340c002480c00d90040082140701980458104800810041a5403041d07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 210857616 1250 210856366 210856403
    0x60708010f080312060607050106030506040303050a1406040905010b03070f0305060c04150813060908120a1b0c020402090306011e0617010b0a0e2d03030309030a03020901091a030103 80
    0x2107924059800705400812000c05040e4484265a8000800030456403408420b561940d0031600070390f1007111a5040101000241509485100e510810086041c400b18001c0c0b4003001c111350004002c64030441d503c80036482400390075030007160510000380c102e46030188c54004400050500303104c01c917840e00c60100080c1102c221842070741e0880d00303420201008002c07581429919020001c02d802400550881003d001c28506d0055031040c50041c80615074a54100307103601d980020040000340424101249035000480c1e9a030401c03401c0c82e142c5003c0b00e40e6005440090701900c01c1304240c6070306128482c00032410309080500c00003590807e820700c5074096034440050300c0f0007403001d1814000d501d140340100001c0b4090001090940c000303181468000c040d50000900704541075140104140078041c418980c405110790b1505010011001541107140c82c0740c9040d500e01c582c0c403001c0d08054010404e89030503406510400c01500c003400d51050000003003104400035070024031042d14560b000a160401c00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 210858866 1250 210857616 210857639
    0x70906060309080702120307051005010f060e0306011406070818030c101e11030a090f0b07050714040608030412120c051005150a0611010c020d080f0a06031406070801 73
    0x990f07a101d00380c40d08100181d003c00504080181c020301c1240030802000c030000d0424024070810721010700c40003603c0c2d410500b815100c0340303164100d0320503ca414010200207540000c1e00328110f0341114000007410703002d080810404d004158005000e03030b9001c41c203e0003441c40c4450800080c44103030110368100800b0350401182d82c1e00442c110001c2042100e80a203904583c000400500980c0d003494034050101101c1186190700248017007000039501c403020700091a004105200910200f039010382020400d844e1661114014400d00d001d8946888080043c2d46807030700010001c0403072100366615a41d60304010a10301c4010001140c0c01d0442100c1c095400d40174039001507045400c980148200f2500e03c2110b002090064141e07c1e907210700244104260f07072201d202070003502c0c003039850059401d2060011800d64011401c1d640654011501c80740899134048010307035000c103102d22079684645400355031000a00d140e4001401d090004840b0b59001c6800290300d50140981d50f4424596a03600d00c0100d02 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 210860116 1250 210858866 210858881
    0x20a110612040b0601020109020901090902030c010207080d1d300304030b162307050708070b03041e0213020405190602030f07030908100509060a09050705300709060603 74
    0x451540d4002040100300c3c400c1d207440d030064042c000081c3c4004c1d903400046109030700368482082d00e51900c014030114203007400300c0d05800c5400c2c0010074859080404441d1039030003100007007080012071141024840018000510380b04006840118256940e0020080c2034000080d81d0303480c103c982030503c522100010840342100d130041c010078815143c400c20f484e00c0c10112030a400400030b01c0c5006403a0000500d0302501c204c1070001d0349a84d100002d00d0042e00300b20150380445000d40002804010300110402200d900551051480450a1070040b414006814001e8042d400c014260860060b52016500400988500322040c83d015601550030b65410902c1c0d0040b8801038009101d40c10030145880090f2045602ca803c2030881107440303060340c0e480d00c401c00841c45040f546070700a1018007030091080d1a0403482c10b013018011400350b0384400d0360b0b6804500c1628007400c542d20520b03408030405501c0c140c400561543e00c421403404003c00c4c654030b007200e02545098900d403060000d400c3c0d019120740d04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 210861366 1250 210860116 210860137
    0x6030e0708030f030703020d0b090106020309011b2a0b0c0703020a050f131e1b23031303050f030702011b031a040e070e0c0705070f0605030a1a06040303020a1106 71
    0x2032840d51445003c9003c0e4200480840c405a12044081012b0303403100100e5001c0c029540c001c1d0780303808424000400742540c3c102d03685040c503041243e8902141207006c1e00a413131011140710bc000088400803034600e0b203001c0d0b071004c02c01c24070100341c036000c42c2004200d680481c0d008540030318200c0e844108101c6903a9070728290503400154200c20b201000038a80240c1d084030300000030b141840030f0345501d140c29940540b42d030b56481c1201040c0307160381c0e40e00030b032401640c4041c3e107a840c240d03402e256020451383e2001402d4030801c003602088200404d48181c046a001019020950751a410a90301c003a01a0440110b0030b1050240e404020f49954441c2c840c00c0311007912030180c00510180141440300511640c07a040c0c110740201c1304041024400361030468024400030002d250344080a0900d10300304242d41d0006231ba1403c40d280100300301e0341e0000580f42c00c4100304c000081d401c40b841c010070441d40c1c020040f49400105c085400428190003044036041280614500b149074150300d0300b044510b00c81c500400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 210862616 1250 210861366 210861397
    0xd0f170c07080c0126281404020a140a0611030d06030318081911040e0102030c0705060609040b060609040b030f0709060b070f032105190c2a0c05040606030e070803 72
    0x1d03180e02c82e401d908980b54141b0b001c10904004c040c00c90b0000c0d06d0351101f01c003509404c0c40f0284800c6044c020850b40080c0a00c0141c00c00c1107283c0d1780040c1e14850780f403161a0030081d0050382007141040c14412a84000da5180b0f04014481d982e1801421030504150004207040340340c0400515100081200320b0303203462685500b01035940300c0e41e404030070170b924246258015944041d0344010840900c01940900f80c0b0000145d00c03030f020340c60035a250050040c4050b014001103001d01001681c014103440e04041c00300c400c603440d02e6850011800801765144c1003a810320505030307202401d07100410707000c0550390600414004140c40e150422890312030324500600d6004c00504442c0428440c2408540381c07006500c003202c1c502c005100750000c1d184107860303850114150a2200181d41003610034480b030440a400e0412154201c56440784c0028110802070500780c1400d1040004c000c4030002003c085d00b002802001030036181c00c00100140052080d11296115070140400c0e1840008140c0e0030510040c13155 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 210863866 1250 210862616 210862621
    0x14010509120c030f03010f0302030f03070203030a030e010b040606080a0e070b09012001020711010f08070e0913020619080f010b04090c1b1505060d0f170c07080c0126 73
    0x1c0340003580b0503001c94080380014803030581c289103481c000b07500070030380020718206250071801010b04100003440e5001082d441080817400584010041d220075080300c0c20001407540c208a8400d000d400203080160b40a03203441e10100e0882d0f0807143c2180a08680382c4c04004c0080c0080004e07640c1c0b041c500401140301020300c040043d640c850074041035017000000c0c034a5401c0344500c1c2d0701801e9800009040b1030801d038959040e0b0165070320412030142101c0c64a000d41036030800000141030340480301948c40c054000c103c000350300c0c00120310710f400a04c1d5010f0b00d500d54540f03010b1240d052102106403035030001600b80010800181244202c241070355615070f20780c0d1425140c0120340005103041c00d080030912041c18080844907000000031541c0301e02510402c2000684860420120703440205042d20442094502d24086a130381c4040c036207003070ba000854016070454000000c1e0140240c0122854900c00d245002c50940300116003513000b65400c2c1c1f600901682d10091001c416000301c403601341902000c400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 210865116 1250 210863866 210863893
    0x903020402070804080607050d0f020a0807030f02090303070b010504050c2107020a021810050603090c01050711061603080105040c0c120c0b0c0a02190506010302090a022514010509 79
    0x101080b500c90703030400d482c1c01c0d62540041c1c1405011203030000820000b25580144238554019412401c4c0c44500840c0761025409003d420150701030060403c05585003240c2865420300d50456403000002800c80361550740070314041410700424003030540203900303100105d40b442c0003001c180c80d49100d03940280303640c00c0c02008110004240080042046100d40117000003da20b40310202e0003080c00c10212401c903460846203240e503c484030342c040c3e80900400c00c1044110040803a2601072a2000d2030066503500b1a4240f055050604101540e4013490004690415410041d03618020074441c0e01da103400e40ea40e400c204021104208402c501041c2c1000070b000001c1c072411400003c0300e4141c00e0405002800b9126800d00c0d0004036620407400c413002820900305501000741510f88000c4860b44041c041f0780e5510700d5110031040c031000340075035403000204ad1150010780589480405214210307507803c000b143c0c400c01c0e40c641c0d140d055a0250f00b0780903034503090030103001d19841002440000e0480c1d204454 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 210866366 1250 210865116 210865121
    0x6040c06180e070e1c0201080606130f061809110904020f0c06040b1f08030403170705010f0209040507050c06011502010902041b020d0503041707060605040f05040b01051009030204 79
    0x14468141d18807640100e000142001024002c0c1c8880c1e541e40020f01c9440300340140f4904440780440000300008060740140c0c0d02103940f55019078144c0b00540c542c408070109400d1904070383c102240b50034150b10702291603503120070f0a038600100c0b242c400c007402d5036078a640d0046501d440c2080155200c2017000e03400509154005016610715150081e00e0940700c55202400c2400648044600c0e00c0c01409001c2c4400c03400601140440801d040702d5421450710165540e80e10036448003c040380c2d008043c400d0850440806c2d01e00b07481d080f600910890000d540520021351103025140d1040c0d14023004541440e00c40c03820344c0c8080c00c800d0001d1085074244900c48403004400f52440b4110f6403500c05410058907180035144041143c0d2a5105c84214220b001a040517800500c44007009810301c200030109900c0c40d62000000c0c00c0300034882c2c0d10201070414601500300d6400240d009420101d0010344010194010b52080d40500400d000590702c0e00f003081031484600807100300040407114188090301c3c140d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 210867616 1250 210866366 210866387
    0x1030305070305040503032205030d120b041b020d031406010e0d020f151806090307090509160e091b0f0f040b041506170f04080d15090b03070806040c06 67
    0x9007003040c249945d42c00002d24692144280b03000440c015500c045e21112144018000307401d0480103415940d82c0c900b00144000c00e20f80b120143e15880b5410b107080c64449a000c4142c0030246035149881c9900f1120180da5001e2022801d40000d207031004400608407044d071810700500301651401d110101035000c02803070140c1c140c0b0981e4002d2615060106658400254a000070b00750312083d41c94040d003154510710016041d0009014000c1040440d03920b41d404101401650200d501c0054581c84501e1414905601000030300403046031403c01252803464480e40500c101a61021640114051085200003041d04081e06801842c50100d003d51480e0260940b285104003a10001d03803149010006000d5a09140d910017003903520288c140b00380390f800500d510403030358503241d000c2c00e031b0412541c0903084010003000900f41041c0410301f680462507680100581d03000443d034041c1c08070b481c1c418220081c00e100a00301e01c43c0c41801800160000c0118074688039503040800c3e01c250528045003694200c940 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 210868866 1250 210867616 210867623
    0x501120b1002010c080604022115030604030c05010b030715030f02130f0f09091104020702010314010915050a230114040914090c0d03031104081507030c090e0103030507 74
    0x2980014000ea841d58204100341c03005503800030526024040d006082844050841d41c092801080b003000c910000300c801e80c407860100484000e50341d079004801208110384011040d80350103403409000c14190701611003030055000d01c0c02040003120800c101980c84029224071048180501088100603020b0790040d01d0181c0800c82c090b00c1c0200300c07220203500a210750007042c0703883c080d400c060042c03805822481c40513064210f0204040f05054550000314141c0000c030510482e000541032045921030b401c44030780c0480802100e045035841e000c0c2c50000e404218040901c0f41100e50002a0074a060352180c5e0885030403461040550340140c2600c0501a0f410b1010b0f818804031107400c1501fa1701810052004100340070000610041d40840c41c03000000262994003140e000b11000421590351340d41c10031016a050800040501d102030b0301c0c542a000310707480343e9100c0c000c05007010860030f2400ea481d031050b2504e550070040070484541c1034484d00302500414031500100740047c00020300503801010007a00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 210870116 1250 210868866 210868871
    0xf090b06060a02190f05010b0303031504020313062c011a1e090405060609010605040b2215080415050f0c070203100509030c0715020a0305030402040b151b060103020109050112 77
    0x909070340200940071143d01260350b09915817040003405020311031900100c104402a616600744030152651808503070041511072640003000c90340c201c022200d000d04c05507201e1028409031140b0190034031641150160440b03100c2c026403418508540620481c190304d03600c9050790252009030000d000301d8298076403076807075501c00541e80185031765035440e20944554403580c0141110f181030824464000d0b03041c0e01045c20b00000340300074006640340901341c496804c2c0d0b840ba160088a105007003800c644d11554494840c22501494104d580c6600410545c0b00702c1c0a0b40f006001e143d4403503440c100304c407000c0b2443d0840600c20400f00c0c200040441c001c0c40340600040455804401d42581242207039000d23a01e0300d07150362000820852a800c103016400c024028400b0613200844d800c04040c1d280c4070482d100a04001000001074115035941e48040c1c14440041c040558034402c40080c0c0c041d550002240e10110300f051145084440317000a00309050301d60680d1a003034a00d20381401554142011400341069a4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 210871366 1250 210870116 210870133
    0x11209140303040b01030606060806060403030e150f0d0b0901050d0312090503040f0302100c0c170a1220060907031101111203010501140c0a030e010215040b01090f090b06060a02 78
    0x15041001d5401180941804c44071540344d49040b40880e001940b10b031060100c9441080025600c2c4019135040301e401d810410810008500029140d0301c000b4420251171102080040c06035560303801402e15110302403000c115034034100082015040c401d20800390b000f0740e15941d200020b0f10408990b847c00034106000b1034601a50b6a5840c1190030541080481c41c0d5190400c006520f4640b00c0c40c1c86400071804d2031040e1380d14039150062045001e0140400e000700074021701400c00c03400c0100e480c041e40c019500351031956040e44002c00d0910390080a05400391910524421203201284160140395603030b0060120603e1030384c540c035007641d1000215043c046000c2c4103140c2d240050121901d07600a1217881d07650303581002d0014101100150303041d101d4100a000e07144080e1b00005402200f81c1d050f040c07000e80902700d0710040340750030300f002d0300c8070120481401403204000e00e4269550603100c24150038801421030601910445a0802c4050440040c2c0c80109420b070a00500520151505205485050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 210872616 1250 210871366 210871403
    0x150306020c03130b09100512010303110703020301110306010807090e1603180501051801062919120b120c191d06040f050106090303122d0e0c011209 65
    0x840c0075a0004d05440b03000602805685040a0741c0407104060b81002030404980b01451010a2814000201030103516100c20815a900b008440c00655008009020080e01401c03008525003042c0d039000e0101d101c00c0c0c0410795641c041c0304410151560151408910f07581c01d101c41d20300d18902800c08080c076a9490010303895041c407482c00d1505600900000c281400c0a00d5030302c0e1100c6030343d0030f000507592412505100d904c20070041225480f0001d101200e00f101c0004d03210100f4031a09001072600708d00c85116145090308411118035060500c00100018a044000d00501c1c4060310314515140d044206441554641284619414803019450002c866294a640035051f102407204100c128100001c0014a18060103842c0241c0201da00510455162400240003100e0074040207003030204103c1425010b182c03a40c0724508403e043c2044052042246510003068000f00304070320141810102e000300c21071000202030484140c10303510711002c640070902440c0145072540003228801950106050340 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 210873866 1250 210872616 210872647
    0x10309060e0f1018030302091504080a05070902040e01060f120e010b090a020a0e0909010f0c050a110f1b12060a060e011202030309010f020a021909060603150306020c03 74
    0x1280c001008060102c00000c41034034011481c4911590181840c4803900c22840701c1140313a10140d4541005619880d0300c4000030b41e9a600325042c062285808100040c1c0c3c07080024040140c54051020385045d69150320072541a44100e001e000c0461081c1030040020b240b20742c039241d80d50020717032418090b0181591020702c09d0782e520081e0600c55079110800c508040c0b41c401e0070a0b4100d03203140300451078000910300c05000e03240c40c070200b680b00b014002e0004003159000c2d0002800220408407c0021030785a5201401e10340100b141d0400182c2842510000e8800002d02c0512006032080201012a1205450b542c01103544924541000c40d4101d40005c51201f00030682c0148481200402c0c00d070300703103071340f510220301d05a001035070042d0307a100c40d0030141c0c50110445048031801c2c03030404400f05070303008142d10302200550020741004481007900326a61640240400740e0310211014040296100c90490a1758a40321030607044100c24039040000400c00d600902034100c01c00b003a80c0c00d003080b004c4002407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 210875116 1250 210873866 210873881
    0x10e0f09070513050604030b01051504081f050702060f04020603090f0f01020901020f030a080403120b10110c010c030801091d0613050c062701120f0204050f030a02010c1101030906 79
    0x1040c400304699601c43c100c0c82601002d0001541c10720f081c1451078407000903c031010301c111802180d6401c041d0705c0b20b11482044801400f900011580d000d040c4800b44c8c5c00e00c03010f4181c24101e0030702d00b00214002c50b201240150080c810700c0e60004c656160ba400b001401e0340b025001500b0743c030405803e694414003d20a0744030700d01a003400103803240401c81c00641020100c100c47c0c400c13600204056160710b0b801c0090340360429010700d0b0048645004c420702500800581085c07a601000c2040321401081d88071511040c800b40110640e580c048001d030054404240809009020804000041c4500c0030380394807118a1035200d010b034080d003001d48400a030070550140d540003400080080c846080c0082001308010080041d10141e07d0310622002c1c2030503850351019a43c961060541d030340c400c103a10a4081d02c0300c3e0000c0030010800700349003000c0c420003948144600c9000303c2c8a080d0202d1140340214901c4034031501a100c0c624503448980c1c411884d44100d000c41814581d031806c244010411510a140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 210876366 1250 210875116 210875131
    0x1002030d0c081603060608130302120715060b0310031103011b0804121b060c0908060123030a0201020d1107030503031305060603060714090a051c03120209030309010e0f09 75
    0xb4190b00f00641032440207000040088103250030b107003080101c560f20407611580408081302c1d409010f00c403441c0072401c0008d059000015598042500c009218542c0f0161003c251064020801242d8031109070b043e900044a400a00092810b000c00108030441d8403222484002800005e45d625a04000b40351042d10781c07003043c00211890304020820294a5000c9040382840c01e10009005000e500d14030303010340c503110081c40c8540301e000a04819004202032b0b00580440e90944959684600003104003524640e01444415400c200c10de0300c2c0c0c1004200c2070b45d01a01a4040c0c450b40851241c00c0c1d8652400800b40c410314819018004041001400030b0340c0a8501c11440255260079030820707034a040c0028143d0342c8680c22210a0140054015200a0325004e0b0545555203d4400d400000d012022039841141c2103620a000f03a110143c107a0761a10321039229444080641c049101d1250490281c14009501030b441000507403a59030103030486181d0314800030b12000d5141c1a8501041000e4402d07076245 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 210877616 1250 210876366 210876377
    0x20a050303041706070c05120d090501050a0203190902061209030c070e061008191113080102040608091209130b0d06050f01120305030c0f070c08030a08180a021002030d0c 75
    0x420783c00f4000c0b907800800034035007440c0502007030b228240c4507a070001154581b0800000c49200c82c8d441c0707400030a05c0c10b802c400208124600410303104069403089030540d480b008074840350311000d01e0511030f403400c0540181191381820b800f0b5414001804d4050008220f91006021404d03044d1001c00c20b900140c5807140c8518068107203441031040018005054005000c5840304000d0704500b14044005a1003274004040341c0c1d030036202480f50b404d100e1006403a460300c521200110740e1020540080040324000e0362400181d55664071708548a84030280d4a0125103c1042000303c0c624000c0002c484119402ca40011a0510300c03002803c0c1c0100c1030720440300251150200000519038412007401070072074030312408403107981e640c004182d8400180307103522aa01c00700b40901282202d45c00d9662036a801485070038001d8880c3d0b0a165a81c0000901d0800545100c00144460f80080d03440004250200d00600c2c1c11702c03403030b07081081c0d19880441d01c204500c414010440b55580310700807a00b4a00c21900c40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 210878866 1250 210877616 210877649
    0x30b01030c0e01090203040b04020d06020d060e0f07050903060a110d1e0506040e030703081003080f0706060b1c091a01090b040b040b030319050f070c0503010c0e030d0309020a05030304 81
    0xd000b0701400507401800d08920501c02c200200f00c0810700c5aa0041c2c2c1180e01c05451000d5240210090060705d904d42c441502d0540045101060680d038980070303a00560501d074865403102d004a4003445204070443e007503040b20021410007200b80e003041280020780d0812904000b0111880e8040311aa0b91559141400580321810084d180d442250340004003640c0a00115609180a03592846145030060411100000040c1a0910015000c0c00b031340d0700800e4151380d00341809202c075094011010559140d072030701000140c0340282c10100c1d401382141400c142007410040c00080e004084c0e030f2005032119058040032070310030221410035502800e0904800140c800110017817004030341d58062990700580c500100861166400811b442c8024410703100401015200e901c100d4450150410340300403003802203040d0040001250301607050f80d034254000c010202c00c1c071004070750420705c0b0010144c1607040f242820814034480d42204201c94005048600259600e90220745185c0c4107901403901c40340054039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 210880116 1250 210878866 210878879
    0xa0507060c09260606061b070303020303040506010e0402010c0201030c05130303020d14040b0313021c061a011b080a0e0607080c0c060414130e030316080601091d040c030b01030c 78
    0x3901c8044003041d81c014003d00c010503103140c0d218405066a8843c001c00725064001481e81102c441490941e2000d40311010364915000c2d6481d0010f031800c44503800b443c0004200c18840000c001d2140350142d6842c0007a014035001980200b000345486410400100800280c0e002410000001103100f60300178180000c94030001081805004410520000b0810003009150280019030350045d014030f495403840f2900d440064000c0c5001114809889042c00c1c0d1b0301d003404000e601c4607071844a081c0340614142c801c01c004548101d000f80411210584261245d13000c07030f0003000135103400d00c25800d00c6030103070b10042e001800540082c01700b2148042d0004641c41d006506002c0f41c00c0103001aa0b40c1402c013810700350000c00c0350a5802001d4041c0001c1130b01801d003070016420030190400d002d419241e032424250b1010750b0234503410307a095001c03a81c550040f5a1320351054100404940c04101401b2000d01490458002c11070050400c0d55005200c000201c08207041a4096001b10f00ca02c038000b020310315081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 210881366 1250 210880116 210880139
    0x3092103090801021305330309060c07021e040e03040825050109060e040915021207050a1205130b0c040e07020115090f11040f05120d02120a0507060c09 67
    0x4206102c6a4014022034800b00101c20116094a4048803c41c42c1c0f0310860b05c0c0c808058a58440c00310150309051005075410710360f00c0040d4000d0072100c0c1134407015594440746040d14071132510000c1d0000d20b440001192504540765440189034001c0c000320f00b00c0301000c4081c2c60364101d60080340081c5c0200c00d01d055000110001d1641e1541c000f480d401c43e4601d4500083c0c4104124426201400440c040300d50903079880f94072103648117520441480c01401104c0c031341c400075004503005000311051480810344460003601610745140300c555034001000305008100001e8100600418034541c0c8600341c600000305411180303841040c600e8041519140b400310000380000d0054046429a49802d402d481481003404004050b20b134a6500420044010782084004103801c0b5048100e400c804140401c001403102e00540803071350211014000d034906c040c10203886220461034480564854000d07035035a01c4000c1c002e01448400d1b03050190401010b43c0707400003500c43c0001544001814032909001d1100f044 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 210882616 1250 210881366 210881369
    0x120090301320c0c03160201030c0c02090c07050c09070809070b04050a14120a080a020d0806100e0607050d0309120519080a0b030a0c0302090903120a090309210309 72
    0x80d84200c400005071120b41c800c1c10407541001c408030002c00145240000f2000c9410208480c01102d130381da80c61000d06048250b0b400300403400a402c000304010302503c10459800640d40042c030842c0755444541c543e8119601c08481120140120420200c00340e8034004042c0c030441c8a80c40e40107885c0707070075403889007130641c00d40080003122000c0c030051009480300490324090381c0d00000480c1c078801140002503030f8404840c01d0b00740548507480b0003208000c419000f410350004180c08417a10300b61095010b9030000800c07503800750080c14642c3c2c501f45075407003031521441f0104c024061a02d86000e50701d4650070900780c011000d01203520349542d14208071441181c3c80042000c2e10b0584d080408580540060040c3c108012040281c0800030440710780f015404184035043c0101219860980e40c41d00b40101505480140d00c0b6a0a810005600c507501004452900c0300c00344144182c1c3c1c0c0e03041e03181c4004090404068041000740000840c4208201082c107240c514410701d031165600c01c40c640240764005a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 210883866 1250 210882616 210882641
    0x132309060105100c0204021315030606020d0f0c0602030402010c0213090b0f0c0901230406021e07060503040b0a0908120a0c09050102151332010c0912050120090301 72
    0x5180b0602c05465104144044c902d81c121400350362071070040c1c24020600440d803c404041d940020313854031080c2d019849181103941c60340a44105111010701035444c100d40c2d00401000c550203a40d941e0001e0884e500543e8400d04c1414910030542c510f4000c81e40c03501c58416962038043c3d0740c1d05079400f40901c070281c0742e5000c2003641010404d803826403454950360207949005818010542107040309803002b01141d03031342c1c0c0b4400c821045d01c3e2980c0e003400960310080d45013080c00424a01450003280a80032a8510a43c1c00540710303e0320307507141d0340d40d004410f000041c0400607080d03441c00040d00003a4100001c1c0919100781c02541024202012400c0443c3c0103140c2c48014403200c44d100b0403841e41c010911220121007000c00700d04596030646450803200079814000c1040034110800003007183c0b408882800301d0840300032110b806d546064103500f290100383c00d00011402c0550704210024441245d0b0052074030810020881441c0c00416110003025203407415105080803032078203d141824800c2c0003020f141c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 210885116 1250 210883866 210883879
    0x301b0503010b0d0b0406090605070c02120f070e0a11040303050403020414090705040c02010e030304050a0c1e140607050d0210140408090d02010923010f0f0e132309060105 75
    0x24030340002c2c00703c0507401c00c014144114980001c060004541c054400503030840002d10440c40c9c8a0802441c240c0d0b802e9089101e8650f80d000c3c3c4081c0500020459034202c9044010136809042c9920541402d00c002c0c0035503e042e40341c14440c1741c610340300300140c401540f080d02d60b152154258410003058412500042b081c007030303540c010041048000110241207602c142c40000e600a059001207014001c242c0130601248000000c1c4002c00000040525038103024032036041e201078560f071020801c0d55120340304006100352210306001c0c03680070071048030031108010040d0340b420255507501d030b05101e50030703141501681244064610440d4540030341c10030001c10107248117562801e40e031805054040e02c00d62a01071450380202000b164001e60f6001c1c007800791101040381049254004401d01104004020300189150300300a54140c0036105118036124140c580f00d05034000300c0140f20507114000442600d140c1c550149000441428603142802c0d08203001c400034514120402d2443d224041e402a0b018a8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 210886366 1250 210885116 210885131
    0xb0f13050303091f05090607111f020c1905030a05060105090112020102030403170403021206070216030210120f0e1c261513020d0b01090f301b050301 66
    0x790360074144801010b840025030140f444c50002180c2c180240d01c401c40d04803000080600501c21b080700450b04580003103c0c203aa91403550113248030322500440e10480540d015000b10745040c5040b6400312019500d50220498056940e00024501a445403050302c1517000a0014089410310920460144c0550305407269103c041d40d0000f581d0707108910002c1c15181040b151041c1d0020705034201d030700039034004080c40e103401a000b0481c0e032200300603a0380c10050310030b90066140380301c0c852044104494000b020b8480c0404001c206450040484075a06803080e60b40f0100008841d40e0711803000c051000c0e60040440c3ca8002e450481084500c2c0c042c4000c0c00980c40200c583c9400a444610004c11140c1c180310607034544c0040c4207400b400c43c40c00140d05c66140c9021708400181e42d80a0010708003e0326041c0040d003020001541d4000050244686018107480c3c24401c00d444031200d1008440c0c0c03130035990b46c00c86000c40c8500d4500c0402d00221007081c0b03030008542e40c16140d00c0d40803002e010128002c01a14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 210887616 1250 210886366 210886369
    0x50708100b0f0c030915030f07170106050a11010203100302120601260705060d0b0f0a08100e07030b04030216060504080c12161e09020c0c040203060a0b0f1305030309 73
    0x107024542d20680e49410002c0d1444100e481441501d00040c0c000c0c260b101c000009100b10807142d04119517044d080042c580010300560301c03904d078011441110084200f42039007230140451b0310b81e0180030a0401d00486d25860100e0305400d00c019413142000244501d0344506602c10040c5500410070102e1040d480003005104200c1403a0501c0401c19440406a640c00300701c054841c20800c0c5c0b540066400800441c20030021900394020110250303044034407008000000d001c201032300066006004155121065010400c4a594031a2404080341005c656005540340c3c1c03000102101100c04a0044c0c026203c04101523041011820103088103080050a05080244082c3e9a01407181640c0c070442c02c0c070030700400d14202885046020766260700f002e140c06403111b003c501d8401039140800d1500191640004642084d4403e4070b0785400c210005d84000c2000400b000041d40000e00752a03802042003100240842c1404010030000100200064807244035815040307056040fa4011402034004004040b141e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 210888866 1250 210887616 210887639
    0x6030714010212030108161e0302060307030207020a0f06030506010c11090402120f01050403091d04290a050f01120f020112150b1b0304061205250305070810 69
    0x140c030000d200c24041a4a20030040385007100c41c50701c10281201c00000455041800b02d15054514030a051f00c52240d81d903110f0750701100500d02d40f20910725000c10010720041c5004402103130440f8480c0340c050f05052003500060307900055944100703161003044408000e02d0b0f070075006140c2c1c0100c00342000c1400c6109074480001c9000012034883c0f16402d000300040443d9522212016809045400c032460400060100ca000b040250740c142e0218226107000200140c0e080040d60b1031808488100c2c80944031540c6203440706144084402022901ca4400302902024400e814030032602038001286c81d04064246c11000c0c2d0040c0c0098240310300c5880f40402084142c2c140010359a0f0a20340f00c10420210803000d0700500251040d04220410f000000603842c102c4409420440d002c0c4103040f00c64200d6000d00d80d0717a40b003079124050209100400300907044001c0d80c020740e0700603041402c00d10300360180c40e902150480410400808a41c1e1801400402684043c44551280b8410308142d18039007000c04171880e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 210890116 1250 210888866 210888869
    0xa0b03030d0b0612070c03120e030901050313050102160303140103032007031b050405150a050111070510030f0b010207052b08070609050d03150b03090102070b041b0806060307 77
    0x920b4540d0904220707038458070111000040e02841905141c00d1180006020007413800060307000845c48149044080098810407224440c218015494003103c47e0054806400040403405002b20303e0081402103182030004141d0030325200002000d9994030b03e006011034000040881e1524081001480000c0d006505141c1d11000700e03c20740e9401c00b24480551030413944e900000d01800307040403003526403449808040d00790b070411941800b16907944151f042c00c009450f600c480e0f008840030000c1042c1e500403503034007003a10102e0003954012600e4a0200b0250082c030340040000aa03a1003000c040c0c021036105044001c1802d101030000b0624040c0001e030301044003290346100b424612002c21542d580d0a0b0070354261075100201ca80c540c0c0060070701900134107158200b83c0303041c00b9859000c850944a4400e600303202070208400c10101e030801d08100d1040e0001854142d403513500300842808182c4200304c2c0b504c668481c0e0700c01c000c00c0b1031881e0407002e8410300342e01030340003540001c082c0502a03a010505c1c1c030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 210891366 1250 210890116 210890137
    0x2030a0f020f0d27060801081b09010e090715020304090606050903100221010b03070e011701030b04060b0d050f0c0402091302090d0f060f06060816211103040b0a0b0303 74
    0x1074080c013540000c020128591103408105103e041800074041c0c0c0c202c904241200c0340c64050380d040f00241804400980701180c0c000e64004800001445041d0035059100d410070142000c0355003030b0361039002c0c810030180050380b1500547d0020030704000c09182c5014880c0a0301d150f103490741c100040c42c40401d590701c12550758040c110b42c000c6100075181c50040b404035404207640412081365651a100d003105a401524610009480340b0f0a009280d401209880c0d207480c60000410113507031854840045002e0702800c200c8256480c0e5000745482c0d07076000c1c1010503070f42c095000745c5090041d1428540ca0f0191080c88075010380d0061040410b142e440ca00e0006c00c1e038108260260366400200700042c034580301824003c1080d65010410401c0c824141c0c00b41c0d103803080e03000c010052030340c940c4004d403030519040700c5120070100c690006050f0b980c8078080304a9072000c0c2d600d0240316440c9800c802400d0325444402c0c0c0c48075800100070031003801001c8034a01d4101201d88020000c001c0c1f00700229482c3d1282140c500b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 210892616 1250 210891366 210891377
    0x160e0d03021b15030a05280603020a0b0f0a030e010b21010c020c060d0f020412080705010f0207080a0c020f1002030d0b060405011e0c020901030b010e0f060a06030903021002070302030a0f020f0d 85
    0x2d407d02901c8889010f94520000c5611501c0c03014640030740209083e0105034001c8240c11004241d01642e10304560440c09240811410706a0a40003100a8402807003002a00d5407540300f404400e480740914540d429101a402d2034520034161203d500b120502c600400441d4003c199001c4c0075104d40d02151000e0b04000000f144540d507658802c8041d108a074415104240003c100d03801380b03c0b91a010301f041521800c028071151110110140a070300030b0b02d2010b0807540040002c0340c0e1150049502c02c01a0344003070100c01600f060f00c8002040d025003180c1c03500140e0000196480421005c4c4100c06000008072152400c00d420f04000038100d050306112000c25803900211400b885000b0070840002c540d00401c60b815940c0c40340b40ca0341c1083c400f0f1295407140801040841c000b0348014411501c81c0d40302502c0d20f18500d140c40400c0307001e84007010081d001d41c018005a004400b074103000800d00c0d40e02079001559100c0803084002c001c1002000c4030021074020035051460318002103140c000545291420 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 210893866 1250 210892616 210892621
    0x9020922121808010204030b01091d06090f010c0c110622080d090501031802040f020705030c03040f0f060f030f0e010219031a09160e0d03021b15030a05 67
    0x118620000c4503500a0061501d281c1410102a4003510440380312450106100c001c2d55101140c40c241e000b240402002810408010700010b4560742c88500b65400e08049030000f091200109400c29600303071038210440d00040004122503100340122100b5800b00e2416052903155500c80c3d5a80c000c003103145511510703000030310320a003150a0248585100f0364250441c10145d4503103a1130340d548142c400f00b00114516130ba00003641c0d8003a1144c14030f0300300c001c40d80d140c440b60b00e40d080000800c0b20380481c071001c41d030a2145038081001040030748803c0b482d0300d000f5a07130365040c080258881e40c241e51240001c0d165060050000c0c6a102c071041c03290341c240e0301340441c210303001a00b681c1c05082c120500102c65840030814210480403441250079003000da80741084508070030600b41e500400800c40007a0008540008159500e82403420313610010214607000b9910101c0301c000811601070004150010380c4001c80c0000c0720001390980b0160503c08495508040d22040340c120010b00000b010344c80c4305641d4000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 210895116 1250 210893866 210893911
    0xb031b10030b030d080106090b030702100e101103090c03030c0a0602030a06030210080f060f010f05220b0310080606010915090b0408010e120909061302190305060310090209 76
    0x300300c0d40704024160350b00004e25010050984809124120000d040310303100050314820141224082c1030641d02801d0300c0200e10356070401600b400c0354507008511402005c0300c0500c1140c0704110310340340010040c96036414401c2c0c5040c501a140b05540344a81c1041080304560074000904180b0958080000741e01c1355074a0948000409940c0d0029411014201114500d1944103068500c12220380c1103000c9330307480d00700900120510442039980842c079282c0701c1180c001e010760081d01e401c95040c960b02c80380030002225094680519031251601017004001e10031a00240c01c03890000c0d04001000705070624000340020500540c0d071240d40b0384c42490100e400f14180c442c5003200d0151a0025480b90784550710f040c1c141c02040084140000c4ac02a00710800410b8122811280400c50092100c5040d4403003c00b007007000c1040c499500c0c041399080000c10010380c409840c1d00c0038040380d0303140000c907460114149414807050140c10b031402407506c0e1000300142c1d502e1402c10f41280c51002c0c0314112445028 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 210896366 1250 210895116 210895121
    0xc031b1c0903030f0905031b01020d2c0d090b030603150f0604200a1404030c030c030210210203070302090603010f03140303011505030c070b040c05040b031b1003 71
    0x32034116940c0000d10aa00100c405074000d9005244207076420030244ca80791aa043c11100b12010007012908108004803c2082015a005461070040001481c4c048a10101b03c100d40c600c0307010200c0001812120304202d9181080030701e0205a2707801800c45461038101c000c0a1110902444903941000700200d015500c041100d10840c1d01e0f400005d10301d60a0100065000582c1103c030180318030b00703000b444501001462001240c130f0303850301c280c6070801c03141031000d5680080e070a070b030038844850611002010a910750780d0180114040c00551031850f0440c0184944415041100e00500c4001e0080c8480e003039900103076203111205880016103c0c1c840d548124040c0c803655070200c0e23000f00d001c00081241958440d4090071648510b14621901070f20b070b285607850740800d125045000e81800322041c000ca02a4008650041003141528a00161641c8648100d2015a410396400c2c100d84001d0003130b402d1510071002d206108030000c1401440d2144c5810100170f0311a00e09004414800311134080600a4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 210897616 1250 210896366 210896377
    0x80d0f050f070b0115020703080f07110d0308040b160519030b0618120105060a060311070c081f020414010e0f09040b19060303080c1b100f140c031b 65
    0x1010a503030340b00c565080c0400d224000f030150580501c24070f00030f205020300019900341102d5010001c0b50408901620390403040e00205410341d4103480c042c402c820f250380c803c0b040b42c15151098503006110b041c141044420100001d0550700d01c00c02103544007103411b80050556900403400164500000c2c0048030460241003442102601704801145003d41d40561400e44110140c080e240e04241c0c0e9104c498031400d0795400c0d030764950800401c9506102c071500c030342c00044e09480b1510301c8a260030041c0d640c2c0309154410380d0144c01c058000395180c0554040018401d03c5d07030202c80300c0540c1401c0c20a0401e81a0704071a1910a043c829007217070ad2441d50325070790060b400c00d0400401074146440d01c0e040a0b0300002e400c4803025610045403c1d040d0040c941446410141c80d055500c95445582d28144600700380c0c00102169511601d04116540d040c07400c01150f86c00c84078040021810710b034503401d000c1c180d40940d5411500792040e0410400c0c1d158903402580c0c2c0c008013000c20200070f0f100f004090f422038800d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 210898866 1250 210897616 210897637
    0xe09010314150c0409050f0112080a0e0627030f0d051606060b09010807050309280209100f050a031101030c1101050106020102071a1b1308010515030d0801080d0f05 72
    0x111020860058504405442152805e040030301807a1b40d40d2500129819090041c4a0041d20305c04801011a124801605081c0341d0b03400d240080b03102c1c07440060111742107c038546038050304130070070044020381c2048080540801a0002d00018054070300240e190000801d001c1c0400c100464002d18607004e520031681829040703170007004025102c0d00115001e030300000102cad01251955010941c1648141d080700c0c40740c100b04026001e0b800400d0500c40c0560ba0044000410000e000001c1d00965a0492800d004221811801c003150389040221400040554072443c4119108002040030481d40a0031030205002441c0000e400724110740107842050b40c0c001900c0076503103000008968560154003d02d07071a4011041c80c40401c01c8045d0b99021400200c0e10001e010340103800c0726585105c0070014058a204841191001503110640d013403c4070801c4030046071010341c5521044c0d403070400b03014081c04084035180c07005d103c2d0305055985545032100708000702007180055507885560700c40c00c00da8640c0500b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 210900116 1250 210898866 210898903
    0x6040c0c150606031d070e100b0315030d02010b0f040c14040305010b01081005100c080c16091d07061803080d0219030501050109090e0c0d120e010e09010314 69
    0xc00c2403040c0148a1801200082417130b0800b0f600402c6200c5400400030340c10f04009002445c00e140c3c00000c0d04802410300581d10851720302c08201c40b01900702a6125002c4c1e40300500ad151403910030145040c81e02c1042c9000d59144c40040340325911080785103124190165070201d800c95203903504850b400c18194400c0038414001c10003104118041d00300b90702101003641c5400700342d00c03584800c10003c100342c8074072a40090500398225145005108440b00b8600070f088840c24802d0300144d0504200010804083d0724042c034005000f00602441010303900d009143c1b0000c105030700f81c007505903119414000d02e0140007030411b0500c08144402c440c0740142d54044074050310f40f080d150811020b900203c0489010141e0140c901c00c0c0e051080c402d443c12100c3c160768a030720391450310403e5802020740700c1c5082698081e5044182082d100c00c402c40740868402c800a09040c200302c10010403045002d0102810070654040c44d8595640d01c1c030016054a0700500c0032900c604841d01c02a28210034000003071018078 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 210901366 1250 210900116 210900143
    0x9110d0225031112030f0a0f0f021803070b0306030c011b150b01020c0405073e250e0711010b03070e090d0302090d120504030b0a05010302040e1506040c0c 68
    0x590011442c0c440c1c00f440400c6500d40d8100841d072400d40d000440d0300c0310500000c2000a030b2a1801d80e08207501c1140700305070015044d01007428200580e0700c07482c42040380c040301e280d1000032401d0070403d00005040c1003007013905500b403020000f51100c81c500300d02d604002c031004410701c161860680302c801455000c045000a00d1101c6a1a0003400f203d500c41070150203201010406814203010b076034810021551586481c008001ca56250100714082c08072031501010812008442040c083c04000844280202071200107512441d01000c12151a2800940021400c105015010004980104050911004a82c50340043e6401411108072555140c40303121030000740800c02c0711905005203a880255008105004130507000e1344100c1c80c0440d0482c15160000010a0040300c014907070940307504d80945482c0d41c0b5111101305c07400c240c035040d020a543d1001002113181ca88643c00703003040c17401e0181c440620000046c0282c0c1000034800c50081e91640340004100d03210744030144245500c10141a80c11 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 210902616 1250 210901366 210901373
    0xf01121407030b010503160f12110c010501080a0308010306020322060e0606040c09121a0903030105030d0c03020d0309020a0506070807050607020a080415091a070b0109110d0225 78
    0x210019211580400d1500b49140e1044d445070b4100c03071240e4405c160b480c82d442585a0111a2807452500380000c0081d03c00c8003a50000f118000d90f039030740e0580f50b00350707441c0c0b00412259421180c0c180e12400d030507400142c800001a0b0400322603811039400000c0181c9035503032514180840c3e20031692140004113060131000801240b640003400603002102214200d559000522045a11004005010641840c410840c101c54644640744040c4150101d804132401e03d10a250f168906441c0d017030f0350390801700040c045410200401401c0340458908248000d049890103511203244903880d03c10540c681c0714034010740d1542d041c40c1d001800054543c595801883c01d0610181d084002c0489580c003370400819002440000c0516000390400c0585103414030741442d410380302400844440c01d0010300040000c200f1301180d04105840c40b6805080d41c0c40c1500d1130305480c4c4c60016048640124502110310070401d1609081d256008a068001a9119058200c0c0a03420075400503900da44080500c81c9000c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 210903866 1250 210902616 210902651
    0x503220b150111100f1d1b030102070804050d11120a030306050d020a0e15100c03020f06010f1205010e100902150f0a080a0e06073207020f0112 63
    0x1c00d6000242458020400c004450703141c48000ea440c0c40307130b0081507903d124802982c4003c000854141000802841754504c0c841100a114a18013054001c0c05880060380011440d0040c144801c41c000c51500700e440e91481490700031405201e004030483e007002403c10810101066210000030715807051b002c00c4108040da0384034490030480000b4184640001c0a09003484a5240c00d60b00030059402c250070314040030b000d9078000300a51404102d0f2030101c58552600051740e1240c0381550342c1c1001d142e40c3c0d8100649401d000490030f102c0d50740420010801140c00030b22120076554502c014200089950030060301401071181c0740705c802d00901071000d0307044a039580308240c1507100740c401c071882c00495034030848240217000700e030010240d04001040507a48254a03199124071240000204c109848298074030b070000465100c1c000c281010b4080411600d0f004954510180d6010030403076003402d02145140d540140340c0028052400c0720030b601020303030062400519903088044104854000d19040c15070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 210905116 1250 210903866 210903871
    0xe15011403070501020f0601030204050c040e0109020403111903032105010b030a0c020312010612090f030c0308150f0402030a0204080d0203040f05040501050f0d080f1c0b060c0a030503220b 83
    0x10920900d0b4001038154004200350040c1e101d1a00030b000160300c0c580a210240c60014900c100c0c29800300000300d0b001054414681c060112014010b845a041d0301d002c04500c0154900548118140f0360304502c2c001040c409582520703418a0840040f048804090400107988910440340e6402c1000110301c60300210091841911090b42c01d00c0880c2d0f880c8406ea8480c8a008021900310f02124010302c1094021070340745003503110800b0000b07120800381d12900304d0b440c5450400c900140380d040003d018503900c00203907604a8040c0900381e800d86003440c00192124602c4414078050b54011001404003412581070f1801003840340191454440b44884c020744986c01401454400d04121101044a0401d07105203810f070780018004003403001d0b0800130004d4105608604454007282082004550031492010f04116000600f2502d82c031020b9220b0070064800705440350f4000c000c00c0c08200c52903400054009207240d09802d103265a5210b0b0040710b54406140c81c110700c50644107000000070801044042071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 210906366 1250 210905116 210905119
    0xf040b030d1812030212070201200102030a060e0112030c0203030d0507020304030b09030307050406120906020d0204080709090f03051b120304060b0d0c050402130914040201020f0d120e150114 84
    0x120a0307511050f511981540c682d8000e00164001c024070890141c48800070f005a5005040143c1d40b0803510944081d80941060b046255035000300620200758042c0c060078002d403203d04a05501d07036040410001c51140000e002508100071a0707076540941d1014001c40d40d40500e251024403003403031719020181d13890348070740b03c111149040100028140c0d2008010f4900a0200c0d0b82c500d4900b626015080701c20458008003012903d84d6500b242c000203006200501010a00c3c800150701e80c0e190450b00c40c1400c3c2203621401c0e03c40e08100745140090908860b0442180d418208170b6101e80c030100e00340200034000d0701c20b00d2081c42100a0002055010001781d4416440340f64144044d030110307414807500d00120799004104403800b001c207118034030706900030300755480b0040f01100c3d03801d69580259083d515108524140307120400103001c19964140f2040790481c00703060050107408040d000040011543d18401c181c0c00380d850030001100a01882100402091406404201e5031902c0596409002c45000c1c1d6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 210907616 1250 210906366 210906407
    0x40e0f09030316301508030702091314032802010b0f100201140a02090a0608040b040f020402040b1c060f05180702070305030406020607030b1c020f040b030d 69
    0x18980803002040300d214002400000000311040344080d070b19410744d07600345480e00306109680108070940c00154802403241c1c0402003107020412031081d2008030707290840e5076039407c20815a005601c9440c1201e8200c0440725051180c818941054400000e6030b8145100c0c0d4040003402d4006507070300c1c001d180d0464031180d008442043c2c0101c0c0a900700e803030071002c20360003a0011082c1c801ca85800d4161881424150001007403001c858010b10114441c1101c0c45003a0507030100c1c0b01d5409007080303200d4002a29440c1405400350800da11400c2500c01c00400c010300091480031340c4030864071190181c4004191080000b0740707408010004180c602000600c40365050301e041d00c0090300d0440e81c4680c00403281d010300800480485440c11091503c401484038003540700c0c80b240000012001c07c010401050316034050006800c0c405001820345906102151144e4103111000141003c43c0500b0340220340e040304c030b0b025422001c001203409040c01e194841d0381402143c1d141c000f166005005010103014441c201c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 210908866 1250 210907616 210907621
    0x309010f0b06090d060c120e03031008070506071b031a041205250f05060f07020d02010c1b050c04020d0c031d031204031209082208120a090506040e0f 66
    0x2d0106900a1006840c0e02c8002442202c0219502d5071003c080d003052864138807843e11004d022107058a12491808015500c00010480144681c1c0c0f9034034040c00104000d420894035003070025a10303010700d84014190aa0100c2a1109400301321952801150f100540300002c1c1041c0340300c00540c0d00c086506558094a2a001c4c8940f20310a40440d070003d5001a014480e007030404d40d40d000c1410400804590500c03071007034424041030007002400c2c2f00c0c0c8100200b11040c1d1601170310003410004004c82c1d031001c2d681015000e11040d13800162110581000c00c2c1d4008020116017040d500d085419003903103412910000d29031051302d2a541014039001c50380c1c0c40500480c0c1a0407080f40c2d95802c0c990f6494000d4006200310500501d800802682060191426455201600541c00101c2e0a0b10504907059240050341c070390a0061055024949070242c6103a100241c6001040303615140c10301810400d08000007081000503000c1c00c1d1a6001e008003504032070f01d0300d40b45c1e201000d10f6401650200d200d103001c3c000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 210910116 1250 210908866 210908869
    0x160314071209051e0109090b150706020310090911060307050d090302012304020d0f0f0b0a090605060619080702160305010902090f10060c03200109031101020a0e0607020f060309010f0b 81
    0x4144e9904079040c0e4411003583c0ca4000300d540203255200c1365551246074500940d49101c6481c02031b00905004141c0142c1c5d0b410030103025103025080d42c2c05090307198140400c43e80400c95401504803c0f400550f003880e42c950719080212494801d90043c1c5501510f00042001855815400407542c06006071041c131a1000c1c4500180001908075002548143c9403010b1b500000c900c0001e84c031040d446580e080c000340b1101d58030b117903102d40704550b101d00055855400c08107110302c0e030049540051050714500d180410a10529800c600020201d0041c489a44089901c1c80d20811281951a5103800c4d602c017450344914206000e00482c00080c0c0c03003001018003054071040c0f44000c00d03014074242d1001040c110300c4c1c11002d9450000c2c0f5001901401801b0f0700c1c00364004540510104442050000000c2e80c8200b450007400a203500e07025144160b1050042828254001d2022803550780308882513500c941492001400c11014100015000b110110602a0300310054001842c0360849050900c0070154410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 210911366 1250 210910116 210910159
    0x207060216080303060d0c0305071701060b031608181009060b060309071401141207020706030e03070b061201020721051c0b010e03010501140306060616031407120905 73
    0x6120b0b032a003040000ca1910b240c0f4941d0b500703000380320300b5003050346941c0d980340e032800d10300c1590040b24809143c00d2020b082d45000e10520015103030741840c1c6800c500388603010755155001c0b0f0030148140311952001c91031080d980040ca07840c10520b881210740c43c80003501c0e140050314030150200c407910308110504149182540580f481070340e034000208584d43c64151016021200e91040e00d06200351a40c03100c80c0d103e15507004101084040c134400b010f0b8203142a000341f5011044e48403030308051409a0340d2602d403402000b291500c58121145524030388400e0001984c0c0c114000ca40002988005650010810003082000140e14001901a844440080140d540b441000460148000e0742101c5c0d9594100f03d6000505002041c50208007958403540800d084440c01e0b00025850000500d1281043c0b03000c01042d9486442900c9031401e02203140740002c0501c0c0400c10050078030507001103601051040c04195000e21f40c021a60b1050b2107079040c0040c20000203400f17483d00416a8501007100c075215007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 210912616 1250 210911366 210911369
    0xb07140c0303030606250c0e060a0b030a020a02120a0801080708070503030a11010b040f0605030d0302040e01060e03240115051e090a0801050906060118030b0a0f09050a030207060216 80
    0x15002c0c51a41e81c0d0081002080e82c404488202200750300c0c0c141600000244e008580c80c0d922410004407100d0403c0741c1801c45082c010301103441115565010302502c4a6202542e82000f1072234400b50312200909016030821741940001d108a0401256040051707600c82e0040c0d04a4000e0300980ba62203232201ea80944422560144a805900810880111030700c1000f0b034500403900c8100011318620400d00003400e4400c010b100b00b00c20b503281d440c20303c0145004e200c0b4071301c00020390a0440c6454075000c841680e07800140b0a51040c070404a030941c0103510140600d03c6141c05070440c1c414107090b503940c8212580d00038080c0c0e542c0d201c100071009007001d0040c0e0454038200819240c011f40d519040100d03021540c0802007954020020000004d4108400d0081c5402200380c0d102501c80c0d85424000103258a04070400c80f80011302d1440d08202040c08540384580081503e035022501000c03090300b100c0a00180b8078010114414002640140355011850001380c5541e9400c2e12820045540c1c0743c032070380311607 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 210913866 1250 210912616 210912619
    0x50315072303040605040b130c1701020f030115081518040201110703140d0e100509010c020a0605090910060e0d050109170a032a08040203160b07140c 66
    0x50401251040d40209039421036004500030400068120384189070036a001650300b00c40498594042c8810021900c22081c2d00c0011110300e0b8010800701e1700c0b0310f1405036041c032404059130224007a02c0d01e844400c2d01180d01c016903030ba42c065503c0d65500e0420060410742c8590100198484001c14801500300480408822004150f29400803452030b070112591310162049050190b20350055051103024480c080003940207124200e480b018103500c00341800e41d042202c408000040140c0b2000d9a40c1562805222010380350498546482d5030059031400884400654024004d11000951b82e81c0440180380c080001d41d5466141d403522001541c0078005405000003158044205c14550309049400f0000980203000101d1416450b42703840c0810702681000c0d00b9185d00014104454607058040c43c0200d034419200014400525441c41c041401400115820010640301080640d0381c1000040c4000c00c00c03410001010f5910404200540c0c04004100d454840c1c2c12140c0072a00004513000608200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 210915116 1250 210913866 210913903
    0x60e010e060103091e0201021608070b0c0307080414030d0306030510241508010f03202206091104050603040b19110a030509061b0d0f050a14010503 65
    0x8004200000040041055042640d240311139400728246118030040c010f821104104010740700e000081c10200307148002c000014424034208160000040c0100459a107071540300d17100c00c1c2d00280a8118402d100000d4132240703011502294040b21500884140c48044048031015010036409030b081d6a92071001030030640000070340207950b000c160041a401020040d0322010300c1c42c0303504400c2e0f403001607400c00309411080c0400c042c0d14a80081c2014003414128607000f6441e03213103544800c540c8111a060f0301046e11040032410450300e500d61810315102d02c0041c1c480c441e40300b880c04400146020702c00d441420b4104590702c9212040385c004c44017030302c0020703041c80c2c03450f44c2d181c035041000c0703401414201c160b2507200f0b4810b00c010301920916000c9400002d0f03003940c400d400d01004094803c0505040a10380050303003440494504846c00042802c038000365103485466985204004040380799032220114200802c110503180e0960080000f81650000c03941c499807202c050680d180b0a12050806100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 210916366 1250 210915116 210915119
    0x1051005220b130e010504020405130510090804030b040506070f1407020f0109030807061e1a0f03160f15030501030503220f030305030f091605220504120f03060e01 72
    0x1100c0c1c0d00300e044510b40241070a203102101c6a840300849903402e03420805a555181070000f10f24041c010582c0100140705d41508400c156168a13444003a0f42d441c40343e500b6516150030003082030300c0050310002c50b00007420301074501d040c1c180341b1746418048804000040172085100000c60080301c854104880c2c541c1c10508129169080c032003c0c0a040716030741d052285918000002a044600800c11244180000f295045015070031441500443c916460460300740800350607494076402c614080c07054107c0d0b8000020712144c0100781400340c480308280007044000400b041040070400c08001301c81c60341c0d00640c070346601a08100c003252800c1c04002c020350020013012075805a020060007200c04440a6a02000c4c0d5800002d003082c0d01c56802100800c0001c4104a00c4408218401e43c0c09001040540150f45040350708851691003805000d1242142000148041d60342400340a01c06809c403104001c107041c0741c04d00ca07800c3c8441c802c054002030001000d1021443c4039004000c01c488840b1036008440c2d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 210917616 1250 210916366 210916429
    0x1050c161e080403052a1c1b290a0906120f1406190305100906020405120a020a06050c100e0309032e0605060a0309051e01051005 57
    0x1e6103115060818015110403402003882400240700440c4508010180d0124940324880380c110700c0011030f81d034555030a42c0b07a822078413582c8080700000040c6488038080c5440345054000c075100d0b014040030301c1c540e07a6004a40000f00035407844468000d40c600c41070024116844198902c200003030000026016401000110b00540b910b0910015041340806c4461604410104681b50700010480c418040e0080c00300b04d040c000cd40b1102400c1500020040a04517210aa500c41da4540228003003540c959402042c0801c45e410b84018020061241c0f2202207032480c100e64800b1444070580c460380840340001001c1307002d10301b10303050f2001036806060715070740800139400146000050103400e400100842c100c01d40d814000c501c03441820003400c9501c10030404140d90b0080c00301504040700d03850301100b0700983da82c20b403e03214214010f00e008104400c42e460502c1c20725200848280d10b00d91003a454138640301c1c064000600c2020780f41c2d41e040a10342e0303540802080700002c1360316001650101040e40d865 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 210918866 1250 210917616 210917633
    0x30418180209040201091502030316030b0a03110a030206070605091603030f0c0609050d0915050405010c140f0601030b070e0901180f0e03040803070c060509181504020d02090301050c16 81
    0x402c0c01414034904041c0d407002c4e800001f12a8481035001600700200300540c04074020700c01c074a01400341c90200000160100840e0944c5410b010281621500c0980082190340300c00440001d107901a14190f1039540918042c80580400d4820740128001c40c0d4204407104480b44624080343d80650303d108520390106030a4034080351888043d079030551144505004150104a16049034640c0e40c0d65042e0b06140407680944400b4140d031103002c1000400082095a900100e044002e94100064187c1c00e103006c020300f0b2030a0381901140701540500740000040c040461001c038403400c0c3e10b440b0041031040c804200038241d942401641c03507590244100103a2210316502018070045441e4000480d80315240040e80756070810350000c00fa070351001501c5c604014204042000501c2039040007424550f805000516680c65680982071140c004d000181c04054410000c001c01c90001d0000c641e03528211107484040c1d4007840205000758208000f1400002408044540c0d040020850041c5c900d103e075070300d100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 210920116 1250 210918866 210918871
    0xf060f09040b180402030606091b0903150705040e0921090a03061d160503071a07060c111b01020d050d11160c0e09070504050402011709030418180209 66
    0x40082d6a007651084a49401c2e0701c50304060700f14100e0080c649441e104061400c0001003a00e80290400700c00e01128000000c40780360102c0071000c400303860b108408041391402c800f2010707010342842a41d040c01000d44d0000c0003003050710703c480007480c0d4503944c1d83d0304680c2c0c81418001c805110481801009100d0a40101402e00420001e0041a440d41c1d00d803920400e403a9000c040c2e901ea12080440541d50010230070402c5200010607250242c0c1529010019440d1a12449058a0380301351203140c90b4162020030407180c0250380001d0030880340c0c00c0d5003401400b4808003403401c4018070407991208003200718010b240902040c1613009050212088000722040d03081100092040c60320745000203400860034000d04040000c00048070303000380c800d0800d10388500d460360141030103001400c14400c00410215551b41511000d039000706550702c5900c01222400488600503500b4080f890030b0100f8144040001d20860707402c2c0b100c00c20400040701c02c0c0000c442100c482000d0400c109240180142040104541e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 210921366 1250 210920116 210920119
    0xf050907030f090503030a0b01020106030b01030b040812070c17090307260303180c0111030316111006090c1d1512040c05010f08090a110301020c0706030203090c0f060f09 75
    0x1a0003407038202102e0a03240101011111500040b00b00003501e8414421000d004100344001e021481c40c64507075100944060001409400d6204000381c00c0c003a00c80100c40c0b61110803100c030380b2a45002a0000d1180d0031520044404484007016204c03d400b1000c260340700300030018082c08842e1710f0803e4820301d041d804404507078000034102114284010030b02c0698030801c854100041c88007003240d0000c1c144010220814140400da5500204002d4000181c2e540b1850480c880501c4a9480c03c0586040c06891030125640c42100c5601e034101d100c640200c002c40d10300500a10110401203829203c0c0d00c101182501c6442d680b403100c04c0036240c80042208100360001d038035440c00003c1d01150006030000c4900392403144d0002410409541c0c0005400b030840703418a0305052604108240d03a0f180c0e21000b8010301030303000e1855103074119139003035049840028910b0100c0d90090751b21032014010b500221030100c4d5900445140e0005810308507420103000400400344e030f180043c80e40362034a60380c01500cac186 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 210922616 1250 210921366 210921371
    0x3051005060a080703030806040e0303040519030c0f030c0b0a0b03100902060405060f0c0c04020906030c070512031009060503030a05070f0c0504090b180d02061305031201260102040f05090703 84
    0x8443c0402c0c000078000d14040d40c5c84554514000040c0001c0d070350001001141603100f00100301c04244041106000c600880710280694070b0507050881e422018000c018001011042e4000d04060700b12901a0106100d07498003404e603926000d40604580d043c000464254005040c5040c03400d40560040301501c0c03000b8944c03428603880300c020070800c0e0001c60803041c85010004080c22040000c004080030160b00301c806520f0b080ea01e801141c0b40d400003400174007400d05c021031b0340f07003c200c01030003800401401204020b490307103420340701c2c850310058500c0f4232041c80f4a401008105414040211040324803e503c0b840d1905055503540043e282800900342d0300070f10543e40c007040c9a40e0714020000c0d070f1805055040c0c900d00b412913080c250400b00d1811384180fa400604001c1d4190740120307981c0c1d0701244821251404402c130b802d003103085100c0e002d01c40382c0442d150130002c03d48a01c1c4001900345a111112540b00160f69101310500300d1080340501860303040042001c00c039928102d09041d9200c82c440c03902 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 210923866 1250 210922616 210922619
    0x1b0e010c021210090c09091104050606271002070b03010302060307090e09070e13020a09050a0b060f0c0708030c2d0f07060e0411040b03060111061302090f0103051005060a 75
    0x211400c0c0310030315680418250712245140c043c0178912003958040c041e0341008221031003080d601c81c0e01c00496007080034029503c072070001d951542e9080581e1511a0000002560a2044001071075206074001909114550b040c0c100101c592000039440142c0c0c1984144e5491642180c00300030301074100522100400c0030a403c0481e201300e0760400c10340640c046d80018000c5a040804a0b0148900103160508549000b0590005a5100382210044550107200050162500c44624000e0803a00525036003180c000503004040280410052217031960303600545144980710303515030752280f00c3c1e000f103a48144e002880b03500c80c01c0e0b060017940402d0140390383e45200e614003411800d814002d05066074440360b006100200240c5410a00100c00180103d400300071058003840c44c3c06407402640107a144070380303021000503200c0c0d000703000d29081d80e0072031b40851b00c2c01d1400200290444419001c128000c0070b40307a012402030f844150045040c0e0354048090449255050100001480002c00c0381d64400e00e500e00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 210925116 1250 210923866 210923899
    0x903021207170303010e07050f0702010c05190f17031e070201151e0501020303090a14160e0403020d031104051c0204020f0c06090c1012020906030a0605041b0e010c02 73
    0x42002c00300a02650302d0350316104d05600c43e4200140200300303205042040b803140d9a429030842e03075510390900b132110142c03201d41402c0c2d2034400b0036002c0600c04030508403281d044c0101e8410b80222513214100c0d0001844103601c12918900069410b01e44040400c4c0b8502612110b00014035071001040c0b00000c1d00482c00e51040800c3c2c0601c3d4004061040e0f152070300c01550540c5038442000d0f050078002180b460408601c9156075443c4020044c2a00511b402d44040202c0c0a21072428603c158030000c00d0383c02d455031034a1241c00d1040c0c504801510603940f2004005000c3c1c0140503a10003005441c40c03c0524000070b11103014000d00b00161420303a18140d0b40c00581c1c880c8058031100740f800f42d0035500c99008039402490f01d031000c1e04000e01648010401101540e580341c40304101100f914004072103929001241000e8050801d209906c04000710403c024032403d64040000c80300111420712006030380a60307805130420111086c0c4002004035451a885502031200d2102d014401b400808413582640ca = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 210926366 1250 210925116 210925139
    0xc03120103080d0516090618050d03170a05010302090621060405010209040e120f1606020a03051009050910021804060807050a150525140105180109030903021207 71
    0x1c01c122121800881c4044004250f4403401e40c0c40020009070a442d140000c030003605122261080e02c04000100c030340256000102d65607a07004103c040c00780341040300d0700c3c603024041030b908048a81441e00140c001964050003800b450b4101c0307070054203020060302c0b40001e04c45119080c030a000b4050f0b10344003608039600c1c000c0014505c182c3c00365000503103600c941e0b03040109948a440d00454030740d1010a404081c2c9640700c00701c2d0118442a050303075640d1034000407103824500d00c4150190030a4800b044c440180380c1c06401c158401c0c40185450400346880b400440101c0c1c0050340c01181a501441800c0340f12180b036030003030114004c142e0404000e000c1e00400501a640380c0c0e000506a038005040c10000341c01c001030f03001c002d07081040103603c0b0b044509400814500819200c15802c00c01c44240d000540300c1c1e04882e0041c01c0e04842c01c00d00545410300300d240070b854142c0c1c00e41c896a800d042480420307203062141d16103151f4140d450151840c91a000c00046040c60324240e04c0900a0a100041c0e040c0e800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 210927616 1250 210926366 210926369
    0xd060506180906061827070206010e010506030c0a080402030106051519050c101a0d05060708070f02030403020103050c190c11030706090e1f0f170d0c03050c031201 72
    0x41c0340d904184210030a00c4410540904254010301d818045800e0303d0385030100c0440c00704015590110071841054900076000200d0110710034050044c001e00190b0355011035103905070340207050699450390380c42050010a1004139100c100c00c0301d082c45100703000c52103040071301e41260004002141050319030000541200748043c0030007041400041e02d01c0e0000440e5240500101541002c40c10410080f102c15210000e5105409409581342031402c0701002d80e944d01c041d4140068070300d0f03407102403d01d0026900c210644070080482c05990010301801c0c411040400541c0499000e181094a10382c010340191101501030311500109010b82e40714044180f98110910081d41d0b80d012640030a414815044000c12444074001d41000e403003800780391b400c0800e83d011156000e155040641d14005000040c1400d4030440d001c203040002c0005641e002d45145a0a4941d081001c1072152040d007100d0b0303910100181c19101042e03e01c111400828001c0300a030040c0603020041d2440d11038001c40a202c026000d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 210928866 1250 210927616 210927637
    0x4050c120109031205010308093105041a07050a030c0519170c09150c030702190501020d11100203042a030c1e050f040e0106030b01171c050d060506 65
    0x11002100b043c10f90012030390055640f01c403002c110320350440c0c0350203130300b8401c40665a01071b00c6000c0f02c40b904100c8000b00500c941d60070200c02e0f110202c40202c400064001560103960788951419015030a583c6a140c00d4042c560303503110546080c1d0008400d401030160300c00008240102400051128020034030303410b20210a99681070001c0d12600c0f181c985590001c0c1c6078503a06c91080c806104192903a4800350380011242c07050a0b22102c98852203451442001070094200c0c002c80b0405001c0c4240f5040780c019510246c007501c042c2400d40c0012126484807800e094540c0d405446804074030882c40c0e0003160454010b0401c2c40303041960316689000d204540441028a600c02d400800c00d002c46038100d030b009003110b259001ca190102d803159054000301400388911070406400034408594650b4045030b0404041002800401e50701d08200f909040e09220380040203120340302217080c0200108095090300b4040e8108000821a0241100d00d6080380c2c18a010140d42c0e030001180760f90300e100241c010400c0703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 210930116 1250 210928866 210928871
    0x30c0c1b031406041101030908040504150306050109020f0d18050706090906090209030a23011a150a0206190f0f0b0301060603020319090807060501120b07020a1a04050c1201 76
    0x698600500401e0340b0041032805078110740c050200051200314034401c1e0450074a80804c41041c18106030b40b0074482c65001e00e601c14a84003102d40358601802c1c3c2401201d010f0b0301c007044940e90700c5490708241d1090413a042c00071401003085016504a42e40710a001503500901c1e180031011550b54545040c0040c0c10044c085008107074100b00000345402610094040b22109500308034031100820394854070002c00500d404420b80400b280f85a80303d406071403990441000340039200030104000d02036044048068081c0c09810900010482448201c800e2017801e80e00400305a83e80c10b015038002c805111506203044c5e15110707040300c0f02e00c0c1d502070301601c3c8416480010320005180d04040c01c49040341d00902c00d0600500800008490f400c2d8004070020300c80b000401c0c0c80201e890080580d125008008140c245031100100d004d01c5100c400da482c542c801c95511240e52074200e400c3c0e0343c0b03030322101d401041c200300207803207285c8040a03d0800341c21500c1703001112112100040010052030444040c03034450307076 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 210931366 1250 210930116 210930119
    0x306020f0304170901090303030e0c0a12290103081c050403081906150f0c080a02030406080c2a0a020a0b0918060f0d0f081303110f010807030c0c1b 65
    0x40040f5581e0310301e000c880c2c003407031a0102c10000680026614072028080c0b565450081404c3c0500f8804646403200003400c0c03005207521a002c14032403503a18801a0741c00307201d00407500f04420010300034a00301441349614424a078a19034980116030b1141010001e05148004482d21545880c0560742c025071098840f040c0a1408104407440401d80801100900d81411801c0259508070450002015080d150440c0340b000d16000030b070f550382078a02d001040944005003042300e4942c08405072040c8c8040d0b42d140140c9031034809402100380100e10800e036400d1152680400281e50320100180540041026034480107075603000030f210f02c40d0340ea1141d01e070b01000091104551a03d401042980f1056030302c079400742e04020000c41c030401c410440d07144c042c1040d0304400c000c0c00802c0036005803580d07000c100255100441c0408a0350001c0705d02c030854610001d034030520780c00e190a0908185030312040e510b103206940c3c1c81000f1006000a1000b003010710803031987d20000300d42d6006071504035591400d119101036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 210932616 1250 210931366 210931373
    0x30513080309040e190b0c0405031605040b01020307150216060509010501060f030e06040b040204021902030d0b06032208090a091505030105281506020a060c020d0504031b0306020f0304 81
    0x11381e210600d1070b40c40c3d048844a1104001c400407050b1409410000130003a5581c0c00342e040b0013078800c6401081c0d0600c110b400305103c503c0100e02003803d54101391401d0280905110069a90b40941400184860490180500010042d90180000010b16250611460301e1034071000e048602c26035120880340d440c0d00050141d80c0d00607040f00c1d81c104082c0340401c013090200010f1501c621000d41f0040c4034032800c0c0b02041c00e558464043e5403080e103103243c030f1031020618010042c0d500e510038042c0c02015418034401881620b412015644a402c1921001032580c2c8109902401c50151a0080324040c0c4240160071060b02d41c03020483c09000b20b800d001540c165200c09a560780c404030351001c2d1080c2e05103800c10040366640d0418801e100c0b541d214080b101900c844403680500780502407a80382d070810800000300d051b4001052806103004030b0b0108040014121300304d031241c41e69800c0320041340c001c100410004410740044030508060a0112000c01d480380e4a160036a4800400c80ac01d800c808828081030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 210933866 1250 210932616 210932621
    0x20a0305042604060e0402070602030f040308010e010e1f08060a0b090604060303091806090c050d05150a050d0215040915080105040506150f0a06030c020d0c020f090403051308030904 80
    0x4218246840c002d0300b0700c0392809503a54452400303681c04000c003002901001d525650103840406500810540d00c1e4a040012254845402c550540c0042c00c4500000f07100101d42a580307068440d10403080c0000c2e030b01ea4051142030800e001d81602800880301e00003503900301c00d0102c10700503d101d50010614440c510704008282c80058002072241e0724050040001070b82201c510022100d02021281416100150200043c9400c1e40400010ba080051541c420350303215006041c03c040307041041085850b41d003255018402d4000c41705400132902403040c041c42c40c15010011070244000e15100300ca42101a4401543c0c20030382c86440040d4603851b200c0000e2420510b0f1030060800600200000e10f0180ca400d03030703a901c010f403214040f04c1d8801c13039018070b90b03c0e80082801c03100d01c00381036029100da680d04010010000581000014010004c8607000c16120b5002684441d130000c10500c01c41280d803040004044000c0c004a00b404010044000c02c0016440010002c100354806540c80c0e00300001070000b03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 210935116 1250 210933866 210933893
    0x1050102210405010e0d0b0403050406030f02180105030907091503050129150702030312090c03150103150b0a0b0405040609140a15170a11030307020102060c0f0904020a030504 77
    0x496101d404101405181d840c1a101200c00074a80b04845003002404900e9003501c2d00f00c003034001481a4200420f240c1c21100402c12544140d03400c1214418100da55402c030f0140359201c00542e00200e920b030b856036100c3e101654006820409686c401681ca004100488003c10728540034001d481e4820818030500384030b60604100f290b20102090301d4001094540342000c18032140c40b07080b5a0a41a030001c030b20b00107039202d850780602126030f2881900d4440c20030380812100703149030f8400c26038003080a0074080780c90600c03220401e21401c1240d080d5a900c480104c4002c0548a606544070b021217040c2d43d42031003200050004807503b9a58a00707100070320090320f48035081220070900b0034410042d0300d43e482c2c89850703009455250015240340644a551001c0156078031001030540f09003121900d29501290032004103120350b0101c1655070711a414982c8902802c900680541c211100040401601e0700c001c06003c01007500807803401102ca4000340481c1c102a1700000002d0340c4004005c10007940c03050380702 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 210936366 1250 210935116 210935143
    0xa0309150503160c060209061204060608010b060f09030c19030b01061e05130503160e010f05010e120c13050103110d201c060e12030f041205091801050102 68
    0x246580f5001201d2038040c603440602c0c2080040c1807002d0300620109a06641c4c00f100d0040c062551400c42c84182040c0690646081c1c1300c2d989406000182c1030310520403401c0e001c8000d46124100f82c10405030062a4000b540d807250036008000444505d40d07200202d07546104160345c16100b48508604111602d520141c00c04414032450215000010000c0310706255003407414a40396582c0c1038159400340c056038141c2e20941c0c062042044100124260740048810303269101c80d2449646c3e40e4045003d0b118099200f41400325181c4241c0c00d02e541000302c907140b014001c2c04100d0b030740c002c021008140c1001c03120541203100da5035403005004204e2028420b48051100301d0b481038030144551180d070b923100d0001840c101a5800e08590881c40e032224106d1f90002d142d828210755601a8904180380a00603600e00f0a481c0d004460301190103503400300580b4000e0281c6500c1d00516a25940d8030007490290440090600000741b180d4006a5107664108000d210b00c0c1920102c0340d454a000a41f0f450001283c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 210937616 1250 210936366 210936377
    0x50301030b070f021e01021e090f06040e0f10080a030f0f03140c03090708010612110108040b0a110f0d0b03010c050403020303310306141b030402090c0c0a030915 71
    0x241065030300140054010241c20110944410f840e05540c3c02486510440c12080c0b003486400020188d0920240c10380d42e4040d504031342562901810081c56118074003401c100b204100000c40e071588106140c856000f08a41c03110020716407a03159042c980051020200c00080b84503c0c0006070641c03183c40c4480b01ca050f41020701076a0401001c0407030141008060307110030100440010501c000c20400f200c010701c0148000c100705500c807102d038400030220a6042d0350030120803078410603d5207e080c01c6441a900a01f8001a41e2a0b505241c0b024100c20940c1098200060000c5124841c015001b01301d007404906000480184d0041170600350360707205003400c06100b024842007000d6107010086507024010856204401401d60320030a0603c00d04c1c00048482c1e050281c0b02200f005003030380c46041045c1c0311002c054615a1030041c0d0401c00060009800c01c0060b00380081801410103684890b005170240110030f061011000e01f040c6059002c29080d0002880c0b51810403003441e8022010314041c0052500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 210938866 1250 210937616 210937637
    0xb09010b030a050a18050601030209011d0a090f06110903011103130308061903120912020a030308060f090a020703030e030304080307180909080a02061e01060e120607050301030b07 79
    0xc00481c0001420504250740325000070341034503100d03401240d074160442551124410507003031241e9103900074041240600341880012076100c04148ad45120441e450300d1030031090703030740144c7c96020742500382046a0709a20082c8140000d0700034094803801e1401c02c0b000c192500100d2040609480005089079206035003002800822070019100e100b845400d4202a04151540808a0350181c85902807445100101c1c401108003e00700c0b2601046c428603644505910b900c0310b09a10002520380c1c0c00139480040c050040000038042e460460b8085001081900741e031282c00041003041c07408036841d0301201d900048503810103400d840b138407040c101007400035400c516183d0381d222244d1001504840074080032000300300b86205490080c401070300c8441d4082c010a003462074501c040e03406c00c1c41000050700480001620100810000704070b445443e81d05880785901c0c140c415034001100801207900815222074440003038200300f042038000c0c0703d5a55907555941c59130500c8003030f4403006442c0604005010a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 210940116 1250 210938866 210938879
    0x91703041a070203090402070c090e060612010e0705010f0219031107091a040509030c031903050f040530040e0406061a0403060c05090913020a1a12041a0c09040b0901 73
    0x35505c03140416038005903544940e0510800480e201e520051519081c5a090002500302043d480c2c01180190b86404140c524000314900340ca0100907000082c0d406400c0c2007065610441001907009440d0055940d00c46607007011a00e10700c6168001e0f800700f40c00000c0c40180310030801400f0010711009600b040340b1100030248504008103e4000c0d4852500d43c000300c3c12154050046400b141142c03411250740b00201e50728201d03121200704000020030718080c005035002c003902c02c48610031944103010b45401c02000c9260380c0c090080c060742701410554600c0c01070f0807403007050051014046203680b482d0300f4034041c54404282c80f081e4100011021a01e00c8034520300400c1025541500d070301ca200840c50040c01e0a04841c2c60081641155103c140442405070000c2600c1c00c107481c10b8000d580c6907100f80c0d00e40c0d0a107800110038507056003002404001240c1c003170b05480340d40c0f41c005102d2180c1000b0044003002c4038055100548007c071071030380002421241854141304003c28048162600a0990316190 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 210941366 1250 210940116 210940123
    0x510090b03010b0a0e03070914060f01122004030516050f0a03031119110310150504050408090d03020304140409030909090606030203030409020c060c090d02060c01091703041a0702 79
    0x1003050751549001c15007194660085c1d4501c282c0c000050200c9a000c0d80c1c1e8444400a019030f071503a041018000740c00308025041c4103999072048641078580d06c070040c07000710800c0001c12820440400420b02c3c021101000701c5050010300040d40a41c0081c01105c48201c41c1143e19030840e44200e2007608010400c682a8030341074294022a40c250a211440341c1c14120414100769042c15002d60b00315010140c40100546c5445100c2517040c280e00720392600c400e81d52001c1c201d4034030700c1d50f07161001d552000401c040d140075040944e0040c0309880d034900f003031804000700758110007070081100582c002080a00c01201c060109640c02c44003183c003801055020b8801800302c1d882c3d405105201178541c41e145d030a000340303a0440001903502508690356144c0d0391101c18000d4100c010303200000e01031680810421618030b026288400402803e142017440365508000c0c282d803000c01e99079a59500c2c0d14460001c03600c0c242d010725009048800b00d554920349441d106a1440e02c5d03642d00c0300880d0502c030603c00040d5001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 210942616 1250 210941366 210941369
    0x109050a0b0405120a03060e060103050f01140607050a0c03020306130b24100302090a0b0301050f0622080606010e0603092d0111040e0f0f04030302130306090c0510090b0301 76
    0x10245801da500d42c0c0c20020b080c044c060502030644440010b0440000c3e516910860407290004440300b16a160100114143c0e101034900c001a504c140740140011303902d083c0c0f803820811000300300b5460000320b40d543c0e40c00e20000f41030903241d04c00009800c1096050510401d5804500c0803141c100c9018560751344074000c0c4002d8802c2c0040c00706200c02e0281802d44074000d12a48000420550f040c18048000801a40c40001030501071745040800003999415081628140c0b100200b10700700480803c02440301c01e804c6009801c2c0080f0006980044d150f4088150001818044002c2d00700d81c0340080c00980b0f510010095180200b030100b081059000f004508050150110303840c107403a802605003450340ca460f0b1082600c841d940707861050403411449400034411161283c64000c010355401d00006201001100d1003003851244400250000f8170950081038100d11510303404110540302d40356101140c07900b003402c0b12440300d100c40600a602c2c148c40411a000840c1c0307403540b106814905000100d000c107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 210943866 1250 210942616 210942623
    0x7020607080a0914100c0212180a0e0405070303020d050703080610050903030a020f120403030518011206081f05070903020f0a030501020c03030a0605010e06070209090f0d0e0906030109050a 83
    0x24001007150582c6035080b03060929081420004c01c40580c4182d140c4502d0780110440901d0b00e03010400300201e001286d8640c01c0711000c07415908140182e1036002d00d44c410113031202d900003000c100120b0320044058143e4042c900440062501905500e0086c2c43c2c60102002c0b0802c0c80b4051290000080e807142c4d0995005806031408403000a0045013503035680101100994540404245850041e5000669000d40b80c256011540700044500b002e46480c86140000340c0012001c003e215440a000c0c2e0b03ea1210307407011724014030b000c5900c2400f0022159150080404d42d0071a10780080c5800c1184004000b08004040c1007000d810080006060b407280762100a00400030001c0002043e900d4a45000046400500966a070b034140160640c90b9401100c0500301d06251030004146ca52090961150700b58014241c0b601c1c00c1c0040c0c0802c4604030004045540901c1075107a460310415050195202410740c035112081d05103401d80400c525010300a091500980c5021810b1340071440005529048030780 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 210945116 1250 210943866 210943877
    0x6010b03010b030c090d021e010e0a030b04080f040306060f080c01140306040e0a0f050a0b091f1d1218030111030703020a09170a230a020609040f060306050108070b0307020607 77
    0x2542c010402000b80307414003a42c440800c0041302a80a42d410323807074501803000daa84034026016a800c214828459010140410590400080010b2513010046c43e4001c082e40140303082645daa914401600e6042e0400d10145514203010803e8882c2004150f00c8080309003001d1801a50300d0180400600005007540c1c401c540300c064a018075803042c4036021840790080c0f901941e02c15a400d2540e516030701440c040301c4e03248461000501000021902610700076425181c41160b5090701e10410142c070341400740041c1b14400c0c610059944000300a100d0001130020107881c0c6401c0424460311080e06100b0070070740030340d0510100d98400809001243d81c0008241001a141c0021200071621240d80d9040784c1c1003049a03c01094034000001010b0500318070501124007802100e000c080202d0078400600340003503000380503010040c40d1010203030001840c007410000b40c0d200c0c5561100241e4005c4d90040e10074503503500c01071094290a1200801407c8422285803a5007000752000355280d000a00940c00c004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 210946366 1250 210945116 210945127
    0x11205070912060509070b030408070b071101150611010b1c08040e13020306060402091f1101060605031e0907090b0301020d0501140118180207060e0105041406010b03010b030c 77
    0x140103009280142c00c82c003100328072410b0a0f260400c01010b00b0b580d00340d5240701c0d1000020b103030000401207a10460380560182d0410b10701c1e1341c0e8003440040260902060106140f5030360945030003481fa01e4442d88414424901c182c1c0307000f8014042c510010110702d281d034100703843e007115600c0d249842c0c0303000440040b000d078000c082400c0281160255070440805140c1980511904414050314080240c0c002c9090b01c035103882d4001044102d00c42d0131b9819030000d00703041c00c0c80030081c110429407840c50280c3c100b1031030801c41c8000040c210352041d00003c02140c008000c0c01031280042d070030a4600e0219036010001401e2103017601782c2c1c880c254400c1c1c14031144c48451641194400b901541c1100e810054144100c1d611030fa4001c0c4032031010204907001542c0701210764aa4400c0a01c0701c0f048440007000c921145028000d140040d41c04554256400c6840310300c6261010401d00c5414420380c0a240c1d550f03410716100003068100302c41a03100070700c8041c0a1005108203031002c41280d4010145104c010b030f492 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 210947616 1250 210946366 210946381
    0x11401051203270607210804110907020c0a0815060a0e0f19020a0e040e071406070f140f10020309060628030803100e010806180f0f030a080601020606011205 69
    0x890f0320002c0d440e0040c20128a890400801c2100e00724001605060751030002e245040c200c9014004440180002080c0004111281410004183c0081a40c070684140c0352540c00070486000e00c5134031140643e400440895001a40c114005401103000c0382c0c41506940b406112034042000a00721004a9a103100414586401d1900c11b01202440382400d54803400140f0001d01841c0c3d12041306402a0b0420b1b14000700c10300045508001d40d135402c100c1d141540c0742d038401d120141e00111021941408509008070220728802004110407103848000c201120303884146608020f248850038105a006001b030101503840400c600380d0100382500c40702142600c071034410803040b1170142c620b0380405a031203000c020702100d400214402c03640120007540c45660390024110070724007482041c001da003000c00401e5540c044103c015582005100031503071402d4061030324901b0480400c0f1100c4681e400095031030801a0441961640a030003400901014608040080e1000c3d41c12042c02290503039900c001031a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 210948866 1250 210947616 210947677
    0x3100e0a050d12230f07030906150317040e0c0310230102010c050708030103060203060f120f010b0d030c03030c1202040803040806090106120b04030c060905011401051203 75
    0x6904181201c5a400201c0c41c09003140c403900c0001c031070003410070035058800d0140c0b6034001904148001c4141c4242d586101c85d10b117590300a08928101910340c041d1002158450144052402c0e01d0602c01500390b2641c600003a640140c0d15111b200d00d030040c44104a0320031081e440030f90091111103129a2a9100090040c01d0b0340641c01c0400c0c0d0703109405944003c0c640400e2003110403007007070b0020000c0b2031a48005852074002c0f0140100010380400052001941c41c0e0040c60b00310380c010b02685440402d880014128020701e410301c044980c0040e09003143c0c04024003442c140e120040d18070340c01104803520b000f4030f6400361140103410f01d900e4154041d0b01c54842da15000c0d0021040c58119202d94564030401e450390b00510941c0500e07c104000b2414a01042c41690225a0000d848409071280d50b59000001d4070000c0042d82070080000004010034118040c1c5d1007803501c40d0000047c02c1c8111241d031414140103801a5000381d07000342c00c0d160b0b81e0400104944040d401c8405802184846c8401104d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 210950116 1250 210948866 210948883
    0x504080714030f04060309030801050910060e04020408010207080315040203100303050a090f140406090e0601150908060411090a0b0f19080709020c060702011503120302280212070203100e 82
    0x800643c00a4005886545a0b20030351229220750744095103640d80340d0401508880c1603e01010141182c9020000d10340680c7c6800d44120000d040541450340e07400f1418220b0300301c0f403003e40f8401e000100304075850308801d40c1d2641c0f0800440b005c5081d403e00480c80b400010075400028140700002070b4040e0110301030018000109416028816103c1e1115030607141a281c1840450007942003440c081201c2045004441e0701445200c0204416868005088080381ea4500141e0600c1080c060100b50101c0074040c083c491030064000340c0b000ba14180078803100441c020300402c000392424003086401c1e0765481c1c2c18400c0310000c403021101103000d110600020381d00c0b07602c1540184904d5030f000610b03000035000307007225034040d000b540c4240c1e031464400c0c1c0c04d981442500d190441c941e03810603c00510301445240340003456180050030800722490f00c00c2c210b5800f60400340810240c94854503140d5042200080d488034031888035080a04036400300342c4d200140748074501d5407030311409401c1144204115048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 210951366 1250 210950116 210950137
    0xf0a080d2307231e1c060902041a03070918060801050a050423030708030a02270f2407141c030c0c0302061522060513050408071403 58
    0x90400d1040900704100403d5206000c1900c00c01125001c1080f000360380b11191020343c4003600d25010000960f003984000000c0d485010458088220300b2000c3c1324200240c010107400503680c60500d0548440d00641014102c9e081604100304402680d103c04608100d4000c91034645051112607000000740200b5004132030150300c1e04d07040000c0c0d080c103500500d0095028004041d40034119524040030f1441c42403032005141c1c010400741c00081c820900960b41708040e1140181800313a05940044641c400001c200b816526038022000c0c00e2034008200c0303840600c111071814062890382c0f08a00440b1190041d040704110204040e014881c070154074050001d41c2600b0340d803c80b40c14520104d65070601c1551500001e141030344150100c0d000340d1140c8070254240d001895a0307a120410994101c001c8a031941c0c21205102c6030181c030f501900d2030a00e0f038950004010071128107060608c0800e40703110b10b030410715508000501010480d1401101c16081d0081da440f074042c05d14000c5245980328508002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 210952616 1250 210951366 210951431
    0xf080604020f22080f060103080d291201180303020f071a0a050702060705160c03020901080706020c03060c0a08040c0302060706020403020f0102012c1504060e0f0a080d 74
    0x190961454402c011841460600c0c01c180010703211300b58140e80d243c51740319000282c2e00440060001c1510a400351401443c803d001044102d9551840300500000f00300926100c03050b40c420340030601d0412980408811581c00811032008901c40c1560a2084050b000c2c0038540c2c0040c80d08800d40e00581250402c03504204404000011002401c8c0380003000c40b2403491181c40c0401007a070f2140301090480c09400b040d07440c40c1c2440c0c0d01411041c1410305802d8202c41c0b00d80140d50000058031902403c0740200702030310140070310317510317025000c0d04202c80514068400d0300a081080600700c601000c2c0d810140742ca191184595546150070071403a645030b00040d601040c080749940402841ea0010300c15680b081c0c03508078000c981040160300340e5980c40c0c9110590860142c401001090b8007050b904016569801c54a0304017184d088224114002d807400c1eaa1980c4404070042d68034020450b548032000036500402d0f0300e4040e0788480c18180124104420100d0710f44180c1d2090703003002080401180041900c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 210953866 1250 210952616 210952627
    0x30210020c0a031b030905222c010504080307110f01020d1b020313090e032712150403050a0903021009060212090603221515150f080604020f 62
    0x42582c0c4000c000d00c1180010b0810201c2c0c004803881c841d4002400354140c0ba042809070502007084100444810b90010022240d80301d0381c04658103008a03014140850f0a0112540000306079028004020800981c00d0703040c0700038080010205001c070b039404415031805004441140c00c080d41010141510139006e036002103100e20010700300307602c541441c3d010700c1e80c0c0702c4607000000d809a031240074081144000001c0b004d410041c012040d004072611548410550b80303801d22100c400b00043c03101641804a900c080c0c007096600b0704125480400c0e02c000e90000b4010300b170302c06e07032203058010005000404210b004540e40c00401d00841c0450061a40103200903040f02c031313041c001007244656226840052140441813130300054020101c40344040c000d04041e1075a510810120955040c00d00f03460607002c40f8080c03500129401c80a6005411203150b80444d85044425420510000341d8126050400d0600420802d041d0081228108121a4140505d0307aa44000010b0001d005000c280000030400048 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 210955116 1250 210953866 210953887
    0xf030703050f0c01091401050a121b09140a05030a060903180b030f0c030105010504031b050411030a1407120507090806190e010209060a050f09100e040f14060d03021002 74
    0x440843c1d401c820b0340e64844083d5620030ba0030340003a00103003440c0030132020482d0036541881460101008a6045004603088008020707001040010050350780c0000c042d81d50501c03811284450b42d0500f20b804413205050942800b000a03101c514410005003e1640c440c1804105070154424400da40c0c00720424040c00c0341c6c1c0d2138002d030640e841219540f41041d4480005a1525640c0d02501e05a59040c3c0d9400d040c035003076079036030510004441c0710703080d92458001c0300180540d6140502c94a5120300c00c2c500340c49092410505060350312652440c50055860001c10103480d070b10120706441d0314113213100030841d40c98140c2c081e1003035011900310040328001c1c2402c11500000d05461054030b04044102004003440d00440207080340104800507501c90010003241140910520191204410584440d460445003100003800b8140c00d0303002802054001d13610f40c102d45818803900b689404206400e0000101443c042501d0200c020030305d034415100721500d581814802c102c0804a012911800c540e03034a00c550 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 210956366 1250 210955116 210955123
    0x606080706030902190305030d0e010f06060903050609060105180a1d06010602070b1201031b0918020a050607052a030a0f051608060c091314071d0f0f030703050f 71
    0x480685c001c050241035190584042d082c5001100c2d0004055424442e80a1250000d01103151a0846135904e81030f2038003e2150911540c03005000c15250041224a180b07400d84c1401c10042615030f00b6002080100200e44602e90452644181da400c071031459550201d14000604407024401c000c0c411b0005444018000001e140381030760182c1d000c40c0c44440d81c07521703500b210b8410742e4030503100c0b0070b0f00000400020724505000d0791300c5840001810720b03180d2140c040008451000b49000740c1c0701409845601503040864070711015003420303078080d850011323030780c48841d1b490001703a4005c5004003100103411003122000010b040891030040541d0b50281c6c5600f00094000c0b04188240c415001e01001c08034440d42034003c00017141c3c10703500a4900c43c0c1c0d9018901c0029000280c1640c5c0120010801d000c020200d807168064031026842800301c07e06004100801d000701d4460030741040340c080700d0038140715928510b4009541c007003292801104407610000c01e05260150380010154450b90b4040c581800010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 210957616 1250 210956366 210956381
    0x70309120b18030702010c12140d02031b04030320031c09050106050306131b09090b070e040209030304050603041506171203070c03080603120a2d05040b07060608070603 74
    0x484182e0101c08800c80d40390307164031514200a0104901060800001c0c140100a001402060800c80007145500c48644510b5000d00b982c000040ea00004111140f2120400005528a00c45d00682886d0959401034140000448120b460400c18030314a06441810800c4510915000d1f0109941410300030405d0090b0040340c004131415400c00301701090b20305001031040c0c840e00d0018242110b89065441e000701d045003460710b6415400a024010400d06018000e15042c14401c04a01d10702d440d049000800035003200c888107101d41c0c01000116080d0390000705440c1600c00407500260b0340d81761b40c40c1180300c406c1110b281d00020360400800040041c20490f00030b0600c00240240c03260500301c0003401c40203110031a11880461103000860780460701c00c10340c03254082c001900700d4a290501004214058110f0349030140041e000c2800460030380e201e503c5298132040410300c1c1c2000c0002805000c1c01a01480c00347e01417080000c01c1709010300907940c22810040c03a501094400203611442c004000d131144 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 210958866 1250 210957616 210957631
    0x20705010f092102120a051801020601230406170303100b04030b040305030403030b09010306201207051e0a08070306170a06150504111e0a0212070309120b 68
    0x804401160400e65800385903005640402c8144901e00003003d180c0c5125103d402d880214401c0803808401c41c00030100402140314641c90300c035119414040c0100ca4072320805511070464120301c00412000310101c0c4808003052807058103c0c8264004d0000c60005c0000d07038814604221000c44441031943c0210040d03024a400c8440c2402c00c0ea224400c6d400e0b9031095210040c0f03035000724000500441d20600185070001e100c0d10340480c01c00034180009070222000c1c0c006072281c9940d466a10b00c08599104550261203180301034605005c0c46200c607544202d030090901080c0030f400160090070214403426800c004500c40d444644800942200801e0010125004404240341007000309034560380301e00308404205a900280b41c00c210f507a6a0002500b0060060030424500580110329643e40d07026640c02010801c07506900c45110a03003001000e070340c0040c201c100c0c03903041128109450f40415808910300c00641410b5890126160881304030025600440710031843e5441c9408010900d200d15005140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 210960116 1250 210958866 210958871
    0x90e0a06330906080a111e0d0606090c020f03070209100503030307081609240e0315040203010f0c0903030c15060801020a110303240a080f03032a030112150c0302070501 74
    0x4403030a00301d80e00c60445d070001d40075121040b40300d41c036841d1080290070310441898802d889481840081030f59407200ca0300c100c602640340c070350070310024145110b02800c4000c584005c05654400070020360f1240704410001e801113800000007295190b03d003c18400502c0040d003100c0c0d0300e217803100f401002c0b031400f0786200c0c00b0590b07004144e002c61480765030320000341e5a4803400c0700782076220b600b80380740c80d848040600800e2102010174001641d405009000c172100142000c500c19241600c1010f0840d94000d5502c00c2d40307032910b0350300c102e010382c081d00c00011340c1c3d8141803e0030a4806800e20204000c0d00c4c8a00c050600d0800802107a400019009004030900c1a140c10401c050a1b01030f01e2388034002250300c00d44007180002c1010004440034408509143d0140c040c0070b03100d84610302942040240200101039610000030301c110503c2c1401a03140a20f8960310030074140c480032400c3d080390310041c802c12820315018100c4109000c4074004900c40c200b0040b0082221824142c00600a500004415160f551 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 210961366 1250 210960116 210960119
    0x60c0f0601080c0f0109090f0b1509090a050c0712020c0310141003030503220b09150f04261204320703060e030408100213090e0a06330906 61
    0x182074546a0301120146c42e070800040c00c00035000010025910000c8107140c440107103103155100d5002242488240804a42e0344403084c00c05c0c4850040007416030324001345000200b000b050f0910007554005070b8400d500894041e17030302d541246041440f000d81d036454002c008164110007400c0d800101c01040d00fa09240103660303032114180ca03002907488040c010a000f0400940307a2920140c5030001c601c0303005200f564003900c0d6120400c0d070802c105e8030038903280d0028041034801c54811012507448440d208075000140342a5407400510000b0f03196201490740050800b45115034000705a60f5508020600b400c03141c60b182c1068183d81c040740300880c1202c0391118109400d1402c0103c1c1440d2600203600600406181d40d840000410b41240c2e8012240010721021622410074040c1a500040c0c000740503031581c5200c982c0480d1450700d07030300c681d00c0a8501032894401020214500107400c3d0801c4000400400e08100c0e00e00120755217011211000e02c0614081481110040a10940314849801c00515 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 210962616 1250 210961366 210961369
    0x4183c02010206010306111315030e070602101503060203070e09090a20010c1703091c0c021e030328030504020a290403031e050306130209060c0f0601080c 68
    0x1104444010740107801000c01800412075030781141d9142140007038200e16061000720104c00484154000c0b220110740c8501c4110116414042c5180a88110020740711041c500040130355241034402d4903400b6030b52140c00c0301d4164840300581200468021038155034a183c500002000c0c0080380314914840e00304103000c00c1280000189940400d81d0103201048102426035181000328203003403001d0b04224030510740c0070000d005c0c8225042100d000001e02c036260f0802141c840e0829070307540108152103050305c0c0c10180c5290b101c000c40d03d4658040d01c0c809181d0360b00d104d11450042122850302c0e0035100005840301148214151071251645903c0403090803c2c108604030140c500540b0080d520640da80814010f5109090490040c001600b0069801032200001c0303c1e0150019031058010031114026185401040342c00c1103940c0d0003500e040c41c55898004001a11484482c03021201d456000c01c0034442929100b04407084001c04108440300d2001910704641d44032004d002d440605d003d04045284107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 210963866 1250 210962616 210962723
    0x515070303110c0a170906040e04150912030e0a0b1e1005030d0f050c06041a2a0912030304080903071a030402010c02030109020d050105150904050a020418 68
    0x104604101404c1d04800f26100c41410070362543d000c000c00882000614820303950a401040240410300c3d006800e441c103400d10b460701d030b04006801c9050508100c25200082c00c5500c81c040302075524100040c042402132034140c0742151f400304c000c048041c1e16050103200c135811415081c41200d0000803001d030b07a80d0000c03800c180140510640e81c0640c030243c12600180d00a980009140040e85052402c091140344014900042610181c84101030650110304e000ca4207194031b03a02c800c4d44100000c08408410440e03800d44800810b40325080008503e0140c0c0795164951f5220f04400c40d0222500c4e42010704020640d46d009034140c5120f403280c0d480010f00b480404440c1427085010618450559486030019101c0035034015040b0380c195682d401040043c2c0d81e01285090584c0250000209454440a2495044000e03400284901b8230b030b07402c202c0041d00000c0c10031180c030b5050f2404686802a60240c10852010200040c800c003540590079058155085242c0f81c0815030241d5154200d580207410602c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 210965116 1250 210963866 210963877
    0x10521120c0d0903080d0b012726061f0b030903041401020f03121803030a090615050a0302060c01061518090204050603060d02030718050402090106020c10110106051507030311 77
    0x14940c0305204d004081e06c0f5641c408044848181000b502c2e901820030140030110040920300322400c0d050500340b00c1c40c4280c1107040a900c0200ea41d8041e024040e42125945140003002c0100030490000c0c032000d502510320b020740042c284080e1440e1281847d4080540760380180c055a07083c3e92050001c0c0341c0719072000460381c0c2e5910140c005185860b0341e40d280e808158000521022a440d0349120702410490100004c61141c007403803500044101191600d0410f8400e008460048c604081406119940e209030200040382d5040700c1142c2e90b140014030140c0505803580c040000004504050541c075504a040e862403000b20380f0908488070f0304c541690040b03004500070987c000c03c0520000f07000b4140840c124500c1e42c0014201d0b80c20680d00c10b184803d0720701d0180030200441d180c10900045003464070420b4003605e2140080c1c20700816090126001e401d011060100300000c0200112000b50701f90711a4000e03140242110f40882e80786070b0481d20716403066004400183ca0b101d800d009131089d81d001c1c0d88 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 210966366 1250 210965116 210965123
    0x50f060c071703040206071e03081b0412020d02040905030c060c04060509010e03010608061302130504030503071d13020403150501030c062102030a0e12090108010521120c0d0903 78
    0x80000e002d1045058541000b0401c0342c204800308a000003041c541510050b01d810741004810b05003103546070040003800041c00d08410605001c941400b150040e00a0380c0560380004005c08188480b80005070008a0314640a50030910b02231500090281c08002000022611400c6580544400c06081d91501c04d5100b400d001801c00e01c10415158401c41820044100c020000b0500a4a9030005420001c040c4d03400d103861824110f001c011410582203c0c00c180d000d400c2c0803c501c0c0707000d45001c2d08622000307100b4010043c0d5000c00c49914480fa170140c00700010040c0045400003820441440203501502040d100091502c03041c071400704181c01290f058950201195500501d803020a82d40c1014070044a0a040002c0348003503d02011031010b10700c03411400c10041100c4d1143c809582c1010036244840c607000000b04400009a41c00800c080d0441d0403e44000300e00c42031084094081c500588140113550050018503e06441011b014025003964082522142d01c01c10740160740683c0c0510006 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 210967616 1250 210966366 210966383
    0x1e030705010e0103020d0609060914010e07030e0a0507030f0b1312050f040810020414091003150e030a0c030801050607150e032506060e0105090a0903020f0a050f060c07 74
    0x30300c86944642080c80840d1410304001d41071061564662081e20390340d1300401803883d5540313810007407003101c2d00440321000d55000e09601203506142d040009103400070520380a16840c1c02c01d030344510701c007003041c2640f0b40e0f0404181d1b0441c40d01c03450041c44086203100c0984000c0c0d101408210200c9642192104c0b041d803201414010048480090751280c0112601042068041c8000616001305101c9420f061041060040e611410845900b59807014004803900400002c420090b956010003640300c00e5075003181c0e220a0f81020405004041d25015005920f076000100c4c4040c2c1542d007055540d000b240c403985074202070703030b03210802d00c80d0f50701540c50003800c2640c403111700b01c480301c11070b9001214015603541036078902840c600900c940b400d40d00c07101010a00c0983c0850b000c0c05200d204840291410710001016945410f0008003020300152418002c2c1e551104028209070080110301c18044810003030310080b00380760605030788600007401040594007842e8005031603080410100c0f024213034812200b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 210968866 1250 210967616 210967619
    0x103080a080a02190c1103010c020a0501050a05060105070f0f0812060f01020c10050315060307020610140f060a020703060f0b0a05090c03070f050706021207030b03012d02070f0b01051e0307 83
    0x1101c281395000016222000101d485100c0758900380914400c4407402cad001001030800500d406801c56500074400c10006140409010340c40c2c0e0300104841181d5000802d0f00302003009801c00119128085070300070001540051111036995019820610030407003140c04400c0059002c0040e61a514951400b540c4a00c640b41040341e0a4003a5000d035400c1050208042d420540c400c000c50f240341c0c0150307600405641b01c01c0811580500c9504060302616800000c1c1c079100207081c01258250310f040440c0341c410b00000c0342105070f09100700160030045401000c00e2116003049003644000301040404940111030356000842d150900c820716600400545034100d1440d95140d1b002c448040d000d11900080010400081c000314405001414482121a401050500340714001404407804170000358081c2e418501080c2115140c1d06901c0300c410800051051a818440548002403140c0600100f0708080c140200c01400541009941680d5007a0342c07170384103028980d400d100c11040702000b9941c942c1c0036410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 210970116 1250 210968866 210968917
    0x40e0711062a0c01020706020705190f03111912110a08030a020702150f0a09060e0a060e0310090606030b011a1c021b0f12040e010e04030e0303030103080a080a02 71
    0x58010707982c1602c40034104555034004500703a9124131420740f0380039000f003001000d20805016030150b4031aa2a840943c0d20803566802d01c21a54100000d42441060342914810036001e0144055505100c044071003603201707515210324022828000080011480749140101350300c0080c0301007000740c0204505065549401d0001e002c0c0d4880d507070490b088600c0c04c00c214290a04ca4000d840c10340e4540704910f482d1109414000c107889010f41c0442d0400540e580c0b020700a0310784c0460305c010359800c0c0c5020919114400040703450100441910070b802890908054140800d070b0340590f0030340340301c0c0c2500c1c90f00d41d9071204401c20001c02e03450f001c101d250040203803180102450300780301c00441c01c07034a0160400101c1105a10703010759035801c5102c3c903007240c40c8010201034144540b0b21880c14800303429050038140180c0c0341c0140014001c120707501036500c0215003454026940315900c4080102241d59941c0c6a01d000e840b41e410266100b4003040c0001c0c04100c1d9000c050003070f900039500501d4207140c07108010b071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 210971223 1107 210970116 210970171
    0x2130f0c080f040615051002070f140102030a0503060406051807080601050a0507061e051603060503030403030c0813080d20060403090b0a14040e071106 67
    0x81c0c208403008440a420a80082e002040041e8241050780c40041d00d103069005103a10205584225141c02e60000b00c50056442c0001041d074030599800c41c500352440c041041601603042400a2000284a08007550b031201d4001c2021410707035a140c0104e040c92400d898182d1441a85100308200d154000d2842ea0b000102841c1c010300d030510924004000b4007542d1801041c854403a040281c04e544d1501190741e00d14501d800401560904040c0c203e4444202c403400c401180c1861000903051070b0201c03d40d030403250181c940003d0701c07466985551060f40300807006a2011840303500411401001c10101403c5141078031401e08040207828400780444004068004903032240d13040000290f44142010102e844030300c03000d91201c083c1c0c1c50030748020721b80c103030070b4902250081800200311414912450154450752264107041e0f4040120985460b822124800c4007403003030f82544640c41404 = true := by decide +kernel

theorem cover : BRFrame.Cov 210791366 210971223 := by
  have h0 := BRFrame.cov_init 210791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 210791366 ≤ n) (h2 : n < 210971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
