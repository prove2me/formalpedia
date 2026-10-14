-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2426
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:40:55.282032+00:00
-- url     : https://prove2.me/submissions/3c770be2-d40b-45ed-9c99-0ec737d7b51c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 436151079 ≤ n < 436330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 436152329 1250 436151079 436151081
    0x12060504060803071401020906040801090218091c0207030f030807020705032a061209030315010806460807090203070c031d03030d020304060507020a05070519091a03060a 75
    0x9481004a50361040001201040301d50103040180000d1780d00141c43c2284007070005102d034200341c20140c03480e5034440401045191a040401e48444c0c0c80c0c11004075850f243c82c44503140c5801c00c1c4460380d0b0100d1800c0d0b2581d00b07882408000051903001800800709491420000d120401c00c4400c0c101612503928089514a40064015800341d08111010015100b040e07a07034221516000d41250840024030943c58170030025070030944509a084004d60b100c2c503016181404890044041c10305020301442840b00c2034031440707401c0102000440103210202a40c070321032012040402000ca003c500c0c0c04040346003490003003040b80201d030000700490b80305c55110065901244819180d0801082944007040e0000e800380044144c440e000c14001d24020f5082c0c004241198000104045910307030010030442008454071442d501f010180c8018882e0300c40d5a504c0036075070941401064070807462001c542160081401e008000342c04101400d104aa8a190102c040d021022901620030701491001581842e01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 436153579 1250 436152329 436152341
    0xb041e1a071b150b010306090e0d090b0f03010509040f0c030b070f0302040b032a030f07080c0a0212090a08010e0d1e050d0b0a0504050711060702010603080f180a0612060504 76
    0x120307600c5070b1009910207a00f0000c0c6983c003d564141916000c00140900c0030348155040800c2d807030003800304488403400c006c1c080c0034a41c01c0a41c40c000c0a1141e03100e5544445c090303d05641c41078801204c00d03161070401906c0311445000c000c08441030080c02100b04108030702c00381d018141c00e480341000741c0402c04090f010307402030340280404c50301c2c14000180e00944001e4203890320001000364100000d41d01d04402c0c2c1581c404c40303005800c10302c4a03050201c91580803030016070000103482406c2c280010280001d446481e60304112001c0702f80860b842000b503031004035071001440744030003c02080c9859000c861700c405810f207402001c1352841005160232103040c0c60281682c215503440616003a201c10010005200041289800c9400b01c400851180ca61380b0425025000c10b407104c80c41906075070566490000700802000c216410304808000046020040e00c030234001200302240c48152040800340107508a00000368841400000000d54540220303041a0114101c1418040c1e50b84036000e000a07191 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 436154829 1250 436153579 436153583
    0x60705070f0b0a230408060a050124020a0b100510020c03010c09050a030803130b071806180b03091207080c06060406030b060607062d0501120b041e1a071b 68
    0x280820404042513100c2040d11400d900d041411700b07058071071002510300341c000c65402c2000c42e0b9460045c4640305141d8030300c41e03a0a800d07c00f03820b40c400c00c200e0300035121150304600400080205003c07e1141c8042c4030304501030702003d4004500e41d803500200954502200301224000d500c0c21729620074640c801c1d903400302030384d8002c0c10085415140d0303507070000d09500c0206482846405105035070002100310380040c2c0200e669a03070702c0c91004000000c68000d1101d580c005400d000c00341d045020110040c0703043c401205d0306001d03070b41d40701c2c5e8407030312a14109458070312159010400002d1031410040d000010f016070541400c00c03240d0b1035a400c010b02c0102c414a02014241c0b070700030800a17140d440c00000805805200d00c2c004140310079a01e404071a011403008629518100c8668a140703011202d1040c640148403000f007003424640304d91200b807090f882c05032002d46218100c0280b103200d45880c04040f511154080803806802c240410720071000742080d034508001583d404c404200c5081e803d1140c0702a25 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 436156079 1250 436154829 436154837
    0x304030b060a030c06110a05070906081e060a0b0a15020703140a0b060607030302090a060f0311031b0702060f070c030204050c0a0f0327060501031110090302041a060705070f0b0a 78
    0x5400c15805480e0755417072940706e1910788144491440000e000b0700182008001e003c0e0f021a0041c1030032483c600300359401c0c0e0364041c40c900d103003c01e240305500028901d4010001420001d80f000841307011690501240c0c2010b204400c15644855040740c2c002545002c5a02483c1e0312207000c6d5650000c50f8442010300006030400c1c80c054040b451510341800180207961090400520b00940780c00400d4251350240d11a07c0400c09480f000032606170540102c0e008410816149491740c0340c4400c01c03800c240c40f0303c0001600c0300c2d0013040c04401c541f60102101c002104a19070b054035541c40e8a841c4000341c2d0140000c070302483c2807201143c800420441540c5210049071a102448031070381030200c0c01040900080d070028010075400009040b815010000d855004038404140e640c11410400102d0135200354850040b00304032080749907550b12204120549904540c00b1031041d80501800403411f40041c915a8440c10001c1c0c101c0c100007000680364110369001c5c00b0000c3d40c0769a0100c148140c0940301060f8082 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 436157329 1250 436156079 436156103
    0x3150f0e07080c0705030f130e09010b010f09030203150a020714070602011109030c280b091f080a051906140a060f0c02060721181202060a1d030f0304030b060a03 71
    0x101406001801c661000d007030603c10a15078278002c1c40c614642c103941c1d0a0b0381d070350741d15100f10055a004641c0f000c0564a0304002e660b5615660229688258002d20580c03554848008103080442a40481d1200b940099040c020315060161b455115a02440348801541ca0069141d2a1001002c150382130240f00802070400580c1503030620604040903555156081703900d200c1e4607014201040b90b20090101882065207440c021801e2205d04c20000582c95078031240c4200091f512680200c110b5030050841402080075140e1070180000e2080012010306010f0a00034081520900760441d620403010460324100c4690740c6803419070308a00c10b040440002807198813244c016040210091a0b071134800c640542e04200b0020450843c000d5a0800c80c2c0090291600d800b5001e56500000f00900490300b410200245254006036244c8105046103044c0708011602100080201060a88256010f410b03118045c42000d0141d449500ca17000494440c103448001c0759050405042c4641540c2d0301c06544052 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 436158579 1250 436157329 436157347
    0x807050406060504180e0f030d0b0910050613031a16081504020702030715030506030f010e06190e10020316030e0a081c060b040504060b0a0e0103150f0e07080c070503 73
    0x11311400c2c8848003019845408156110310200700c1f541c4409994006103440e103020000000070f440880e03100034032480500060282a42e07419441d503040300e100305c90030f07603a030101140200004c03441a40007074143c401c840d0201d046150343c03000c000d104215140c803ca81c044914841503404031030944048480710700d14001c440c40c9040c04c0c0d0080c03a0030750005089950142d502c4801b884c00c804242d1002d00002c0c1c44005000e00ca080400c0729000b007010302d000034803400c01180c5410369540401040d4100280c1240c0182c01041c20f05e51007483e1400410086e100c0e86000c4840410203540140ea00800c4031240101500c02103200b0320541405600c2c203c081c00d148001034894040903045685c0020080e070b654111003103501458480c0c0e41c010580c4020350b94950340341000b08000c8400550001503040c4040280c42955580501e0070044e03030600b402c0000f0300000b4611000100d84050300302e11554100a0404182d00d003965850780d02ca24000e40c2d841c0f1007542c503a880d5906a00031010010803d80c414800400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 436159829 1250 436158579 436158599
    0x1206040308060604090e0c010201061a0313110402181011190302121c05010e04030c1407080d08010302211b19060f021501120b06061908010807050406060504 69
    0x600302d14020401c9040c203450701151000c6540d090b44500040d441004140c9040d40c082c0208030040c281c4041c0005103481c032491101d041c3c07000400c040402007030305034200308110141c2040c651008001c2c00442d260142400d951092080d020003561280b4030100a112202c0d01c1030f400e00c00740c1c0d08400302130400900014a4040c83e07060400c003c806500411000702c1002c080400504241510032618900040d4042030038011644107030002c0c218540007030104400f0a8204d500b0080711030344600c4800001d8030003901e09041c00c102d0f0f0800300c6036019a500e1341002079401141c0398140d034000c95000c0c032800c0c00c00036446401941791038482c2c40c5810041d9503002150300032030100340c4000c000e011001c0d4449280e00b0003001c90350035045440441c0754490517040d010750410814200b669210070b4590300c0c0d41400c03159420b0101041c2c00912000c6480002966615100d0175100a569000701c2202080052380c0050040c201c2402030200b10310a040d0001014601801202d044807910b8981d203107040e041401001c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 436161079 1250 436159829 436159831
    0xf05100501030b0604081518010605010f0c02040f060915050406060c0209040309050d06061412030409110409020c070e0c03040b0f0402010203070b040c06180503030405011b0b01061d1206040308 85
    0x25134040014040011540b00c2400084510a001090013071760b443c040562100c42c14940c118284141c0c50071200340300c166007180794a002410319040c810780700726040c8009005170030880183c40d806d40c1003c00004481d2529044040d2000b800c00c01120655100c40c1407200320b540e94800d074000030714410040d502600b00640242c1e0460b000b40750800040e03884a01140218071501000c50310a555007504014020341240b4011180404403542c20002c45002c20700c2c1d40c0e0b03010728000c0d01610381d0b65600301000505184116030081081c010195150308000781c6160b12407007944140c0e416070b4103500010308110101402c50b4419a401601c0590603159400071200907a0000d00490652008100c6075010031100700040d403090344510250207505003018402860b2481c50200c01c3c1061005003410f11080c1e90200507601940d00030b18000c2c1e1a0380c0c0300e19004940c0750345044041c03e102d41c03030400441d44d40d92000350560380b551101c2410132400c00e000e003409088441e8003007404c01034020b02c01190000c2d200b84811 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 436162329 1250 436161079 436161101
    0x50702071413051308041e081603060c121a0109050108040c03110a0e0f1524030c0f0c060403020105060a080303070f021c1706040509030a0f0c0b190f0510050103 71
    0x4c1c141c01c200310381d0348145c4c80d80960080c0e45103840c08200e400036aa05c03440d01c5809000c1060207802080203c4011025191440c040240059202d010303119926105203100385071808004010f201e500d04140e15529511240c50084d40011f8806101103041d501501000340202d038043d03151013000785942c40b2000142d101e01c85181e403068030001e0006881080104490041c10b840d5030f480c9080c10200c2c0200350100348001001d0080102c4d01070142244030b103601500d21100d600303084c680d4035910f507000c0307940300e220720301c0044280a408148081100f4000480c170740300301c0c8070790002c104984885040101e0220381c0d01c40c501065104000103100644a00c1001c3d070600d096004544200c1040c880c15802c4444807280c40001602c032190281a4242c0a0102c030307044581a5410031450828100880c2c0b0791143d42e80600c00c1c480100c00644504e8800e0344801d84240d00700c001c001d072604020303c04080321280c03181a80c2070181450b1705580441142e2181d18018404114804005850000103401801004044e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 436163579 1250 436162329 436162351
    0x92709020402270108090d080a0e0a0506040605060901050607080a0306180b18070906081305060403200c0105160c0503011107120807021504051f05070207141305 71
    0x4a440180c4460000e00910640340124400d0a200d40c840743c0c0382d1101c0c004089041203515000c2c0040c603400811a141121098509030b4401c0d0355440c0c05a001d4413040c03510031303080e1007586414030a11001042082c0914400c2c0340138070503a103500c000c21250f00030a000300341e80020200818000582c1202c020000c292207410041003c40da58010301ca00c40c0c07040e10761014102c4d00c4440c0070041d85400258034402c0041072015003410300308040001c280d00120b00816083c07000300008074095222200741c100e61785a01400700c588901d05480c008044800d80b602c900712075100300101100401000c50380c0d0302c000d10306940c0e01d4203000016650310000b09801406980841c40d040010400703440a003c3c0e0182004101c1610380d03988901d2a0442c2c03044420b1265204002082040c00f06007030b40452001062005280300c500d054646080c0181000890402e00e0700c10300441e0013801d12200203400041c4a00c080360203a40045564240c802c001881400c1e107194816010342c41042458a290300142c2c101f01c040f01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 436164829 1250 436163579 436163591
    0x80901050d140103060219030911060306010212210c0304030228080c0f0c0105040e060904020f1306030c170601090f1b05120a06030f02211207120927 66
    0x111880741c2c2e500a03001130311802e400045407803202ca018140c0000b8466246010000c098160301d81d9106880310902d0a481520004085001688200b00321000d44546414107079803452446000f10100c81701d1804105001c20f00c200140c400a0300000790fa03c0366406801a04039070b081284d4085280ca003000a4600c038000f4507111202103214100a4140280d14000030800483d034462401c0c80d12110860301410803400300400e00c101842c4081c070310780201041d5405c2e4115103551002403400c1d0004003440d9005101000c110400101d10303004074080302c2c040c600300b04400792142e0703007424000320030f5030304007001d51100004101160071580f00000800209c40000b0f000740c0602c2c0c0113a030b5808200b0284001540c00308034400000d2038a0300968208148400c10402e0614598400240e13200c402c10280c42109040211444403810550114a4514035416a01032880b01c12800800350090901550070b000e4200111910a0180003180c1c103503100c0c42002600f600110340c104403000c044c040602034030b0352141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 436166079 1250 436164829 436164851
    0x204050403021e0601140604180f1e020703030e2a0319031d0d0b0c090111010c091a0a020c15121015030b010e0103020d0e03030a140a09080901050d 65
    0x2c0300ba14080d00300c3c0d4018084951410f014100840c2c0c182e898244540c1c030801c000c00010904250b500240c2c01150000f24400080b605820001c000e400c01007030400e00c81055420044409900405205100303803402c0100c03d5a09001582e1280f03240816503072507414111a41c862a40b0030b80d0416100f80c000c085510543c10101400c0e043c608407502240400e454030410f08610548a42440454505070b5000b45d4045580e215040c001901510580724a000000d4180c4181d2040c0c81c2c40c280c61043e08002d10034045640c0000b080ea5002d80310700080004041c458841100010040355450b00c015401004076040e04d0f4100f00c0d440d9902901a4a1030302d042110070381c4022181000d61003030150701c1480c90200c6c9400c000780c64000103a007484007050701d003104c5041c1580c0c00110f804980c150030f01c0d006856001e009583d5000345010340c0000c04900c80403041011644094020780c2040b00c1030703510045291510f8240c4000c0da60100d10013005140c00303006601e0f6651152014000030392080501180740450700d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 436167329 1250 436166079 436166113
    0xe0601032423060a060c02010f0e042408150405060a0e031c0c0f0c0b1501090302060f04050f030304060903080a260a270f1a070e04050109020304020d020405040302 72
    0x94200802001d6140003042064070b0040300084c01052641816111111150300003882c3e0071840103d44240500c40043d5102030300c9543c0300c0b08050001c1150601d90b07070444510466880900c0c801d8684034400d40b1042d9a418501081c02801164000014442c986604540001404074100207100ca440103200700001d101c000d1030800401242d003800001e0b5020760003402000320b1501e4a145081c05800f01c0c254000907003841800c1c1d0702040c1c40e55000107040c20400120f510751060390000e94003a00104106000c100e0302c0c2c0042c012a0360403076141195240100134981c99004a101b2240440c80c64041040403484900c000d00000c030b0f0790b19006011440361102c1d60f0307840d2a1a00b030519440d02c880100700b6504010300c107540c1c4910380505d54803848000040217807102030110800500b8004076291100c01c12400341094400000703001c80455661604410042c80e007030400300414072039402c5c070703000103417001283c403c0784d000e150060300300c0c49256807a400f444050300020340110214400d00d80900013030503070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 436168579 1250 436167329 436167371
    0x5130b0105160602070c0909020603040f0c0b04060908010b040b0a030605061504060305061206011a070c03050d08160903082d1605010e07061b030e09070f030e06010324 74
    0x403503140140c4817066410114000c41d0039130865507420340341500000241c4d5400d41503940c00390b0700043c00203440c900340c500001040c0340d07035101d05005000400c012400642101d194001e441f514402001051101c03400c20050716801c07044560003044505091011a2042d000b043d4401c0000d458160b1402019100107242d9000c4c0c3d2050300000d990340240b01d19072810155850340407020304002c0c40113504118031111511342803070b035559507000006103505c200100f202c42e000095800c0420366808680700e607805040301300100c400c3c1c20076005850491034454002c0742250240e131341084e90182000040300080c011190764020212985009140a00300d1103240030003442c03080b440c0320840c0202d070180d142640c02e5a140941c01c010941003154180303c405d60040b41c0c080d580314680705541e24a18507041c240e402c00413601459810101840402081d183c000c03100d8807200041e0303a07003001000c9030f61601c2c58869101703000042c01600c14214540810045144c41080c2000720b01b40000c07060450446000d030401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 436169829 1250 436168579 436168583
    0x614090d0c05030618030d1e0204062601060207090f02090a0b130e04080304060903200a020a0603150510050d05010905090624010302180904060f0e010605130b010516 73
    0xa076154040c07000342000c0c80007680044081181c1c1000840b40b901e003c1d121300440710b5071142c281c0d5034103e00c25541c842d18500c0d42030010784039046503940d48402c1c000780742c21099490129290304643c20565502e000410650403a0416806048020f040105640c058040c81d0f86254416800340103a1480d1b03515944250000e11201e070f00380b50b6462142c02441041e1b5465403054800341a0001040b0104200c40304a903486580220005151a140d00d4107540a25030303451000ca1011845083c2c020510300002c909007014000c4441c41a52540c0724011410f03a1a00c0b940c40d00c0c5003403290410030007400c0c82040c210901199050843c02c040c2d2003003405040781c609030b0042101948843c180702d80080103200082e0041c2041d4030303862003602203040c5c0c0c0043d10680d143c8181090f1340000d0722031030585040c0703001803036100040501c030040c201402e0210262500607a04ca00d100d00d01081c000b0840f10501c20f840c00c0320400790601d41c8002942135288000c1c01038026190610804000c0d902580c0d0a410509020038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 436171079 1250 436169829 436169843
    0xf12020c0d0201050a02090319061413061407021f0e0d02010204031101050c07030f052b031a1804080c0a1202060c31080d09140f0a0614090d 62
    0x3060001c024290b560281180d800c442c4100500841c90700d0200f2819054007140c42c0704015480c180c0341c070100404001a42e4581c4a20340c1051044c03054030b0b000d00e00c54040c013502e0280708001c0c02d060644aa50b4080e0391420150b03105108000781190300340c010b2400c104a6400008402e85069611402c049511449000507540002e0070310030401100e904514005080c40c04509080b044000e080e0741d00654040905800e1040c5413803070030032004000d001c0d4610505e920b6850800c00f0900104844511002584086801c0a0400d0100d000d82181c09607000d00c028001c171801101043c240c94003090103401a2080c0e8010410200000d070100705c4401a10f1041c114542020000140241030010150040c100c2031800c00036a82c20100c0034010041c3d94082a01000726084540c000080c0b00003d544035003510b0040c0d16846503083c3d0000000350450340040e800c10f005044881c02c01810140141b01641d010f07410fa075050190340d00c5030302103103141c411a0011600d0110704000090a4003100d1504840703813 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 436172329 1250 436171079 436171093
    0x11010b1c03020f03040b030105150712030204030311010b01050f0a03060e13020312040e060402090f0a06090503010c0207080d05130315050406060905071706010c0605090a020f0618010f12020c 84
    0x5941084402c5100000308091070409046c05030b006110b100c18400c3c5841155294144104690343d04120b8402e42d030b104240c094a4100d010015010f504148420380c04600d40030001c1e4000d9906014207112098141d4800e4038100b241210040f50342c005090700402c140c0e55150126460790b80064080c06250000c20901403611544100351800c0260741104000810a100811100802c1c800701c40e0004001c490141e21003502e00042141007088001c0c41d6032080f940403000130080d07080300c452030944905070028483c01c07061502c00d91f170b40e040c9407098001c540d1160022031403841c031036400350151154034950540104e0750303074581004400c40300c080d00e852aa074841c14801002201c3c401c1100904d4002c0c0240503d02e010f06001e001401140403e0902d88400c0e07000403043e078465140098890351000c410402400d0905c80550b03200400d200c100d0203102045204040d514125054902d02c100d2201220103480c0008011a680340d0461424028040025103400150041e8000340c601100c07241c0c014151 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 436173579 1250 436172329 436172333
    0x3031805100603021f0212091201050f01080f0f0309040b040e0a03112b080405011503110306010801092001020a0f1401060b0f0a030209030c030d0c03121103010611010b1c 75
    0x21a521104000000c500404019170b80d1078010900401c0700c450021035544658494000c038450528060f691482c3c0d500e440c080201da000702e8110030341130701c0c065000c8a21038218500b01a07510540448032151551017888200c82d5071038141c000c0404402c02030300c081104250801500e19108480d40120f011a84105030340c01e00700c80c104480b521403c031451890b510100c03d281d04824a8030850044000c101904d00042c060100075001180316a451707019040704140d03282030800ca10401e840c1024031902030b600000451020500415911541004180f91621441000c00c041a400c0d155080d0560043c1c2844101007401c0304200d640c1d440c080c401c040c1000f0350340a405821100203420002034440b050110352440300814081c2c2d40b00300c050382401640c40b5a84000245480808200d043c0c0c18800d0320030a0000d581c1c000c4031406840e00c6a00c1c0c0344144884ac06580302a40d040e400b0003030305000d041c0300420103a48510030400300305106200002c1c0747d0f5950008240b00142500e85000c2400343d034142002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 436174829 1250 436173579 436173589
    0x3050a06110301031502030405210403140102093001020d02040905060d03050a03090507210b010609050f040b011b0b09070b1309090503040b0406031d010c020601030303180510060302 80
    0x400003540c6035007482c40d03040d55100905403040b6190394591540c0031001608014080021790b1518400090a031144848460451841d07881800308440400161740b2011401c0703814020f440c0d441d04002d166540e490f05540f0070121030540f1301c20303401a0036803103d0090030140e82807001b0404258207210141e174880c105000101035800c0540428041c2c507248011002295000050358035440403482c0101d0103450070f092103803030062903030000e45a03500c001c140103003c0348003102c001809a00c41c0c0b41c41030300e5130390f14031040e6071040b064403034103410190300022034029180640c0810419441410f10100c0c54107a14411a410304580c0c1088a59407112414803000c0c0d07200308000001418469445458600c07070050300d0700c00ca01d10f0b1282b01c16058640310342404000b81401a90058625514030503143c0c1d0345d4076001005051289016078845030301091800d42ca603010b000e040801e0070990003c0c4026480d5a60480043c00c109103014032642210a03003000142041c000e01c240784585c0100844c6072400d5004101c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 436176079 1250 436174829 436174841
    0x220c030b120c0a0e0a150e06030d170601030f0609021b0c030c0d080921030304020a060c03050a080709090609020306130236121b0907170415020403050a06 68
    0x5032a9840248000801c3c0e9500d03062005454102000301c5035034a4200d0703858060290080c514403815032800000c51440001e40314a0701c0765108030b00300c40c6c012500f800251201e14400b0045c880c110684030000b4182e5000e030304025044104002d001840b40e99449060040760031002da450000c3c20300c2840c0d419401000c00013460207460807000741c00009030420000c8c0d581c80c81504c00500c10311002c60f80078000e0342c0325a50880746500c10400048414040c990b02e6459a004680032071040030003220104070350384100c0080c070945a044c0c55052408400c280140c8501000500c00e03030820580c090086800003543c0100b500820b90b42d60056100c1c01c1410401c011903d9140300c104050744140301d016881c040104c100f41103d44030001c0110090750b140607090641211000581e001088908014200c0c24002070030024a002401d498001210410401c00142801c2e03403144001610502c0c5c440302c0321240105c031a0000d103c3c100f140c00181046803600281d8009a10a50b26504070310b4003102807081b030740608 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 436177329 1250 436176079 436176109
    0x807020411030c0406031d072c04030f05030603012a030b0f0f06030c0405270f0f180309030f010e070b1c0f09050f0102041401021b220c030b 62
    0x181e003145003d03003400c0c9090040348a00c0c420103890346217030b00384120000c20030b43c61b41d050482a110115210516882844120759030303461407500d50f60394401d004e10807007050340c01150f05a8620082844410080740d10303400141905078155aa0403212410800c18900a100d400d81c10156004c1030a0242000e4110b5001c1406180541d950542c0442301da9112007102040101c11601e05440b9120f20110300040c1c0103607001250000040d138a080ca0030b40b048100c0f2004210b0074081c494850b40ca5048055070003509032a640050701581000c152a07810f50b00700c00e910803d44004807410301d1401c00000b8034100d040039403c400c0f41d544803e1140144028031105000d030101e4801c2c5440c003640248031840800c10180d2202c1655a036151301c2d18041100d420000d07500d50044111074040c1000e4034540d00070350052140032a0145050038010095002182146d140c1039031110303c40c0c00100000a11441c4aa004003108843c001d01500d07100708541442400508907540d6030007d0401c202c10240665601c0300703040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 436178579 1250 436177329 436177361
    0x8060f040b0a03290405010209131e020c0a080f0301060201050c16150204122a08070306091106030f010f0504050c1909150503061306080307110112050408070204 71
    0x75120591180b110035002c0b03a40c050000c20f0b45841d40800c40151014a102c101c00900d60b100900040c0702c0c054019002120048910b41c48030440d00300b002c0d048810400c3e01903012411780c99038a01c081103690140015800000580d25840c80b690b0b11010700781d200903500005a803011005002c60f61303092060302d5104a00c0301d080c0349480303071f071450703003005da036a9103200070848240360390728804008064040d075000302264100028444d8030b5103820b0034020255800702c641000c5444090104000c0e02d4010b104807200c030300140c40780c14299181c0c080608440401a41e074103a48903050400c540b00c920040d4440c1303107a110b40004a5040c072036000c1030f4202652169104900781810700980044140c21203005844440c0002e08601c4101816618244240c0c4017458012140e03118505880e0008000c500c110811118103050b241c0c1503c3e0b08040324454003e2000070782c401d0200400041c4201c40d0f0049103c41410b20700121541540000c09807031088400f2a06800045031120443c1441d014044101ca201c1c21 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 436179829 1250 436178579 436178591
    0x915030f0f09031209160b0c011b0f0804060209090907060e0607030503061c063624060906061d010c17072306011505040b2a070608060f04 61
    0x482c00342d5034002c0c00c13001d64480743c009002c9102c010040120783e400704440d4142c00c4800da40c5a02d5001c40ea001282c441a455007464840b52103101a441d0590034110340780ca0314801034031206c1044a24a02c001c004a800702c0d8204498a6103179a020502c13031240b9402e0b0001c2035902d091010080c100b107000f18519024000a1200c9400a034100c4d09682d0320503015108204000524540c2802d12504080068003003450111140c440400640801a50304103200f4082003a01100d042e100c0d240810360006891001c400161103041141031030000040006200301180c551745401242c4115070b89a40484040b490b4039485541404179060681d21540090030003050786902900d44841da43c031100c1231a85007440000d00e00081202070070460040d00e0701c080f40302c91031956a503001641d4510a01030902044240f2682125081c440c2c400c4506079048011050305100c01c15444110075161241082d80c03c1c0c072481218282e040041003040000d0406589840080c00d0550030b2018080b0806800e42c0140e007004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 436181079 1250 436179829 436179841
    0x9050d0f050906030112060b0d080d0c17070f0203040f09050f15100e06220608012702030415090309030308130218071106040312051e0711030915030f0f 67
    0x1350303411110000400d030000d103802d15001000f0300070082da4503845001c0c40d1080040c841d024020b00a0344030b0880003005550101c61007914503502c13200800121009030000112014407411058000c0000c0d070048904060b11000c1c900411601d580100c0b40065441c000c000c000c0c0d0a140303103a90003001e0141d512142c0005100815035041c14071000d00d040c04120aa00741190316000200c45002256074100440c40140d455a030103070544911400b00020000300c0042400c0780106180c4034500c01080d010f50740140308c001d400019400c01002556840d4100000000025190066600b0076101782da8825555007580740140155074041c00d0440ca054030717604039100684030f12490350f03107055014440002a50742c0341c204880d00b0780b149000c19424007d48060008154001c4a0340100c114041000d2000380c4d07550301ca81c80a00c064917420020380d1492004204110300440c00242d054007034805491810070000c01184d0807040d40010300f41010030000030425200b203c01c00c2030f900090311b9075400d101c80c1808 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 436182329 1250 436181079 436181089
    0x30c030e0c0d170f0c010b03160e04020d0204060303360b16020d030507030f0e0d080313050609100f0204050121022a15040201050301091d0109050d0f0509 68
    0x2030001c0d6005460b210305002c1400341190361412001000c401d4140e84003040d03046040e041e005540d01319079542c00c0030381208092034041603100444a88202440b400c620b09003a0060051003c0c0c400d0780c0100f4415400d03400360b2241e008800145000c2d85a910507030400303120480c18458140c2191285c00c03041c04c40d4a00c0e80b440c0c0780b00b9070111001c80c00b01030740311a00030ac440c070000507a160002354000d25128a440404d034109000e050854045d072140280e40341ca1043c10b0790403034100c0c00f540350f1201041e0140d400084068010755000107005042c040082110381c3c45038641641501e511815a0114100195540d04c9015408802c15041e07400e50900d8900b40c006020f82100907500380800b902d1018110b10180c1c1603042d1141e0101c5041d040d00d07503541226250101c5d250115220426008884000c4a01c0094100c05405a641070f5189841c680ca003404410003400d03c508858004e0301c80c0c43e884c1e18001000d000750000c460040740540b103120300b641d00113060550803030002818000d0030300401600e6038070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 436183579 1250 436182329 436182343
    0xf0315030609070b03310506040c1a0910050d050f01081002190e1302070c0e09150105100c050f070f0e1603110f03100312090803030a0b040603120f030c030e 69
    0x50b1903414042480052015006080f16000006e8080c4241a110034440001041d5014074040c1e01e80800494071540200e10480c1a0f4260400c524420001d500c014140050710902104907441c003e070030081449030306020344034107981c0c030305107602803030010f12003150148040150884c040788118034200100814092900c1c60700d04503401d1007214618066607845400c0b4105500303500719021980c0368103525140180e86224080e84851032040e00008411510000340441c40c0224444480c4086c2c1c40d100030050b64484a958600400c030300c07034240c540011010045108030300c1145000e052813900303101c41140194026071104411000c00e205000a8a4070910120a005400e02e0003088a00410815108038440c885c07105070417200c000208162922032240180c03d41e4890f101440b41c6400c416401c40e400b214a02035555981c00400100d045000300703038448460058068008182c8540d651030307580c103071003d041d00e207008541010000780045900d4803a00702c10b040207040c100207501d00080740305e60383d2035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 436184829 1250 436183579 436183591
    0x102090f09060a15110606010306141003110d1415090417040b03180706030e070e0402040b0307030f061811010c050106080f0313120b0f0c0f0315030609070b03 70
    0x5640004200c2c1c50303e0303400216002c0c0401401118510841002c004d10300591081c003d01136010b4070300803c115611901440c0206d915030041e200c0780707161460401c16199145000c0405140c0d07a045170700035900d500002b411030300460300d0000a4040c2400981c254030a40280044c2034560040c50840301c560f203200410b0341194001a0350040400c0a1307030b01c82818411034001a11624012080240440c00a200001c4140008059854160343d0302c0e010703015a0300c01c3e2002c1405400a03003061052400360400c26520900003000402c400340d0700c2c40440d0804001b6042500c003c146034068805005241c0140c035200d0211541800c02e040d680c0e12101c40c0d1001e0880710340c0c100010964000700b840400d400c240082c01042059461042501040c16600d0b4002c0015109100ca02840040c516940c0c5105044c04e030f400209141d6141e0b070390741c1c0070b4800c100003e1402002d81c07000d00c081214085600007462244041340441e030181d9014804143c54410001c00301c00d240c1d800524180940c0102d00c1c15290098 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 436186079 1250 436184829 436184839
    0x3190603051e01150b0f07030e1e18070801060f0e0a140931021906020c040e0c0303040603020714010203070e1f0f260a0c030c0207030c060c03090b13060207080102090f 74
    0x87c1c030351900320f82c2c0000000c94254001c6281c09484003c40080380030401810b0111422050085070392038900400c0303411920900420548001003040600030741000c200c040c8507251600020b00d0f500002008400e241d0448203082c0318880113918241460001140c000300c0038046203448050200940c2d028a10381c4684d440300c2940620013404544590f841810419038801030100941c9c0c81d000c0080d41c030400030300c1951141c0c2c00c0c807000b055051001310701001c1030180034000d18a000e0512409038042d500032030040b602041c40000c88040500b080c4091409840f4960302c10450055200400900c0c0510117042010540c007004104002900075450114500040c20800c0a558070080b04407152801c0c49040005409105d042120803601944031041409994400b00000b03030500078201e0340c461550100400102800d01f09200e00d5000b214070a142501c6840c12001590312284020100e07006580c10b03981c20302c0c19200910200c0d8052001001400d00c040c021030810b1101c0001940402081d00954000c0f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 436187329 1250 436186079 436186087
    0x618010c0f080c0114060607020a1a07140a02130c020a140304051002010e0105150a06030f0225020a0b0f1c1d0609061b03190603051e01150b0f 63
    0x128020704014031072a00400080c1d01d40c1c9900c0070aa018020041484400a4800700003c0c80c6141c0340c015035045d96009803604216605050f81b226501c1d1f408590040c2d40c40c414410200094580010301c8103007811a0041e10141007144148000540a010721014980c20f1400c542d18507a40040c0c201c44142d0820655058001c40c0304000e410361085400c80d54015011410030000c603501500011303610b91440008001a0b40d42d19641c03100c403c2c070a01d609034130081c0703040100b003034520030b42014100c0140c10800602d041e080070b0722080c0d100315486882c84182c54003e0700354190326100d09000014000107030300038500b5540340b07107116241c46425081d01513480c0518180c5489103aa40c4155a00f205041c00d00c0300c99054000308680c4c0e98021115000144200f0000800707182000c5161000d540315180d0041c01c5840f19843d2070044c2e04070409480d1140d580d00380000c00b25404011411310142c1884101c02c035407914402c0c4a0942c0d450507080c515607107010004100103011070342100c8007520714541c182d4071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 436188579 1250 436187329 436187333
    0x304150e011701060c1e02030307031115150405090c0a180f0c1e030606050a030903021606030e0709090c1e0b0d050a0e06060f090613050f0601020105060618010c 71
    0xb1400d1800082407400381d00300000710304e0940004055080740d00507040410003401c402542c500b00b141e120b40003074054105000600009020300e005040c03080404065500d81110494a550261004c60b035120541142041442080c05d15108898000c0d2043c00034080c81c0040001052010f415441400c21000312a070070708030049455400440070340b1241d44140034004c200c91004040f088100c2d0030012000c4162001941540648105021070f843e548415041c201d90f01e00650060003d60f10640540c0901c1ea40e91411850303002007900600f541d5280002e89040050003686405403503041213504c9440c2003a14070100d5100c03034002c8201c03004000360307407410840000400c6a11605520130400d41001190003d54440c90341c002900c07515440804000720742e02984900d03982e072030566805070481c414113941006801c2034084258420800703008007059900c18540441221001c0301e601c0e440e501d407281400318035a428042d07141c2128081702c04500b803014244100c181e0a2541c41054148860307880c0801c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 436189829 1250 436188579 436188587
    0x3020a02011b0c0b0304020f01090e010909082a0105161e030b060f0d0c05090d021009150309020406060906050f03101a03070806062a0f0105041208090304150e01 71
    0xb1981d0742c05209150907554a0341c42c260950004d86080f88142094134080c000b5511a09080d4202d42032021080b40c0c03a4a005803200040001318020386c0c02c5101000400000b032543c03030b00c16084598400000c0780000c0030302070240c21184085d003101907034244500f1402e0460303030000002c2111a07030841100c00d2068403010a900030300c003400c0095001074000c0b41c1c0e44408e00340c500c050124075100c410180118070a400003142c4501c5841e0449600084d200d00410142c1054a509181410f01d42840244903440d0501e10140c400691031440000340c6448008046003064090080208410305000c0545d81c00d100b0050118001c06800342d000000c04000520343c80d4601010000408407512040380c0041411003444240e03008456000200f000b0358049156410014101e80c010030700a0b101c40c00c59419524064881c0e25588001d1710700307100f03403031401518100038400c40740200c1c03140000c09030706403003800003a200f114001c00540e05030704203020422903551400311a034100300301468011703801140c640041e1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 436191079 1250 436189829 436189877
    0xc0e010e040b03060925382205030c010507020607060915050412140d090c05040e030a1211030106081f08030307030f0e0304030209330108070c03020a0201 68
    0x1e941480b0f8a13051010060b8042450424100c55490f403000c440c4a484c51640070b00c3c0c0901c21311500142c00744522030f01004003058100f09103480c0400050300004030b8030703c4600d0740090303844074480c050045910190031190072a18004020907406401c01070000e40001e0700360b0080a41c007030302403100062060100f1140c2c1d40410082c0c2da10030903038070b641c60b0300c040154028101102d0480d94440c0b03d580314000d950088140404011524003c680307411000448840070300200401225030805d2420f0104081c1d4403030007440b0520018100842c2c80f80500303400104101321070107038003543e1490400c100c68011400d0044a055502d01d040c0070209889a51866001d80b88641050742040b0f690807020a4840001c070040d4007985113554148000101e45010a045410070070380e40b0082c4e40100406c00040c1855000e80d079004456808021003514805000c44440b43c0010700704011500d84402c603203c0e9a04000202d410400e40d1030078040317016041c2d501039511401c5040c007a05024060300c3c00080350035048080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 436192329 1250 436191079 436191101
    0xf0405032506240303031d0601080307060606090308070f0f0b0403020c0f01020c090f090f0f01022106030307060f0b060703020718020712081005040504030e0a0503010c0e010e04 78
    0x1900740e151180400707031007000010404039503242c107015025030301c002e051a00300f800d201607181c000d0101e03286a40550007007a540002c0000c0d4040000b00d12004071050042e180200342e40350240d5511646d615080341204e5484c0c2021041c03052107003051012408850945114a5118440400003061303401e0480340750800c86402400144610100010513601041c0f501c40f1b0281a152060820080b000680e11941381d604102d4209021030001500c44020000040d080705410003501c140c0b20881084504000c03e2400100aaa400040f91400c480f400240211710089500000806003400b000081c0c070781c403075110082e2610340c850b0725101a20465a00c0b400c1e50010081a10b0354442c41443c0c0652206650701c10004110a50402c400e04040c06000f220703110fa510418043d1200241c42061798200380142001c1170100380980045843d4075075100300c82c083c9010f5210a00005440c03c01c00009250715003003280a03074103106a029003a5002403d03460481000d0a004403400c07080c10118004000c80560 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 436193579 1250 436192329 436192357
    0xa33090e0a02070b0108011e09110d1b050d03120f0f06080d080108010911011d180a0c0201060503030405060d020c12091807090509072003041403070305060f040503 72
    0x1d100078207166500929169106142c0c0c66074582c2d079440c5241c201c5940700202204982c0321000c500020520b6403083d00250b108540e03042403820710b44040340c031158100c2800c49074481501448403490a11810000c0140003c0796029030846160340c0c01480400c100c00c5d0703145410744691980541e88900d80251071010003403602000701c1a51209519903030a0000300000c04107180340004110749006018504005410038154410340ca051001101c02084440c1000c2c00081c0e8452020400d1351201440401c42043c3c0d1140a12810158209021100540fa082d000c2da89800ca040105031008402d41b400c8034070441e89140c81d010034080d007074068800e0501c4652580240546411540314a0300607003c02d07081a5811038003403000da150381d01100c000fa035001c000300e414413004000928002180542c80406464503070301a48043e9001502a03d002941130590740000c80c050219a403509210414210101c0061801620755100c140c0c50740d80c05410a049882d00000007001d00c0f0040048540300204104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 436194829 1250 436193579 436193581
    0x9020d0201051c1e0c02070b040b03180d0f0905010f020d1112070606030308060a0e06090c07050d1e1418010c1a0a0b0a15030e1603110a33090e 63
    0x2402000c402c4401c0001d6031301850a40d0318050140300080400680d41040c08592a1a040240c000300303030380000345800e98100f0503074800c0c040c1c10820b102d001d5440000703480342001c1141c543c07000383c014002504407604109170035111b0381c911136000945d0200030401c0d051034014a07481403081400c040322104102c080182c00aa28401c001d5603902800c1201d0281d591800c1a4403007000b000f40000080c03180310800d403212400318580d40741081c03c0903040308907030a40c185002a10f96985040c00d0700f80400c0d101003032004100002e0302065044004a01c001d40c94140003002507650032041c03901171007142d00700100c0f40344d02031009079000307000140380c094105e4030803405c1e039001c84000350010004580348803c1604008455003207041a82c4004290399014003102000404e41d0070031401404d00c200d48e4242842a42c400392807e03405d100014001e58040c3c03900300c0c4024011400e0020031241c0380d00c94400c1c0c0c1d410801c02140c0c0103034052030590408034507101d038850321581202255904000c4d01700181c070402e880 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 436196079 1250 436194829 436194851
    0x2703030b030d090e060916050a05040e0115080f06030a0f050a050102030c030a0c02011a09042f01020c09040c06080a09051905100c0f0e04020f0703020105041509020d0201051c 77
    0x142d00021941d80318101244ca41e903200a0107605481501c1d03c40103c4510013900404074000c07000381074022458a8058101941c440c2064080d00b02a801001402080d00c030012065074070520b2640d05c0080307450426014100310300480d0307440842910182040f5154079210040002c10f025800140b900903000707640740d0402906907003156001b070b10304e140e0652808007800000f6006028035401c00309881d106070710071052001401201c503802001143c0c1c401ca0020070b0500e90b040b04031866600c840d4001040d480c04084000a03140c0b080b00e000882c864589003042200040556241c031095500900d05070429895040c1550098440500e000301030f409008010900380410407200025180108120359a8000600d125003c8903517451008002031307982c03e0364006040c0030303001100540d01c010740f00520300a040d2884e4000d5070801c1d078085005035114000e20042c00a00610200c10044d040010403411000e40d0000f0307040350110000a050050104504900c00884154000076499112043c8000300b00f103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 436197329 1250 436196079 436196087
    0x102030921030c0a1e020309030d0801080703080a1202030916090e1b01050d0614090939030109030215070509060403080d02040825092703030b030d 65
    0x845a8464030701c24030558444800e260005904001e0071021118515121a041045140d010807801030034010302d00807200301000303200100c3c2c544002660180d80c81d02821010103081412082e451410468004014007000ca80414100101c1e58004241c550361148203000b0f03102c420a042541400910210400541003400b0034507003d0400200f5070b82d40304a441e0401e14089642002e880b0f10aa4000d40c01aa00300700e44412019000405060003410031441c42c4119090715546c4d0850152000c100540b19414280740c100980c0111149025050303550525944060740d28284010f1b40b06101100100700f40d521001e0032107a41d6200c040c00921040c080341c20003a6944c1800380343d40e402800d00400280c035240c07060060703a44441c4014030071072405140d0345502c600758101c041ca40b0300c0940e08100005028404000080d2103000c010803002c6d4503c4040804260040c090303000b00a000c0c01c120100c120b040c550303103415408502c41c154840806060f42811002404815440c40e014450050705901c00c0f900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 436198579 1250 436197329 436197331
    0x71502070b0c160e0f070804140a1401061203050a080408040f0b03060337080d15140f090f1003020a061101050a0e030f1b0613050c040b1309020f040905010203 70
    0x224034080060700b079031604c0d0030f0f4088804a5050051240a07000b040140d0311900c45650420301a40d501c02010040034150340c10032107101c3c0c044440e40b61001096070180800c1c02040c00820128049c28400f0f84242c0f80680366204d00020360b0100001400080c040101107815200500408609000000d403102000d0406900507526203100c0d100e100141c02c80400c240e2804e44219121a8490507100584241180c041e804140c04a130810010b00c0b182010340080c0c0b00301842d081d05106100341551800204d0741d6400321a20741640103c10030040010743d5260b108107540c100300e80468030800f580c2c0c0c00464580c006a2500000d5000101140019415074007665800101044100810250f1110506102214049034250901b82c100344540784080d00d5900c00743c02d0324131041c2c0501e031581d40f80b6030722582811011200d00242e00b002d41108401d1003020003180080c544c00f0380317040088030065000200c4140d80c2001e00c2000688549145007151070f0f09103c400e1241d030141007408030322014134102d400303500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 436199829 1250 436198579 436198603
    0x804121e050c01200906070501020702060310032303090d02220510051c020609030f010510090c1d040f020d09060905060709152d0f110f071502070b0c 66
    0x800c14138812081018a0418101003912106092401c580b48080c0821038010840540305551300344618005030320380c6030041d4880d43c10f1100d5210741c0350651521100f840401c0301324402c07000c0381152000740c03400700004865a100307040310711180d071592070310008041c28500480f12109541044061881c10300b1500f0560107421100b0403910204d4442e820300c92150000504800d50f06561050300d40941170240c0244030090b009400d82c0ea04d1500d800d10030307003500c0d400e5030002002e03665090200100603076841158013580840c41d100d0502000600320200a2030304002d0280300d95a0b5101d5400d0501455045818504401c207051000c4000342c02c25100600c007030001940c41d4007816001421561141090713000f5605101c4441c202640600e0044030014445140340f01504083c40301800c1900e00b8050050018620f941c80002c401c2c0b2000009081a07200e4150011a5000e0103c10030554008560101540d86101c54000c0c541c071610b004078600300d5540c0c0145810130300040c2c0c101c2c40c2c0d0808140191828 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 436201079 1250 436199829 436199831
    0x5072d0605010e1803040b03100f0305071401030207110907050d0c0302190f1b050a020a032906030706080a0209060304080a03140606160212030a0f0815010804121e050c01 75
    0x10703031658225040084d100c04082c0c400e40040005000c143c556102464100d5850300044108076202c8580b04000c0715a07070801da03115401b51000300b0000d810b003081c500c00c07000b083c6420341c180700700f5985a011440d0031404a910941500001484d41449a400e0707030002c1402c401c0038030206140c10000f40007580a400581105044803282440707a41c011460340304515416030b14640c40280e0100c040d0500c040555044503240546070f03410700075980b071805280c040d50003a203000801c0f51b13800c01003100d10740c0750084c0549980d90a5003007101c0350f03030003050101c2210070504020800c0d59640c541c4034000d00c1118500343e4441d0b40072051202b400380000c0940b280080300d07141003220400e8010700030354089044030003940c064010040c00203801c08600403218aa403000c0d04400b1810148124141503400c4484680d0001d06600942680d080d0300c0040c894210392028100ca4030404031200003406000010005000303480302d046844441c40c82942204180d8032101046000d82c890644000c2060b8820741807400c040d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 436202329 1250 436201079 436201081
    0x40219090f06090e0a110715051501050904180c0b04050924040915050403031506110a030309021507150e0d20010b0d080903061605072d0605010e 64
    0x1c41c5240e0401561040e4480c00d0710945011181300300c4400007081d440e6681e84a808029034200c1020103405101d00c00c085440c040024255048211200188041d0070501e54040501699800c0000ca03850301c0c130243c50201c0e58078013524a02c00e011b100070000030700d2092140030014442a501d406401a15412103102446403240340d40390a0503200d420803016488400351a0106916042c1e005d0f080d0544108540e2044842180c000c504807402214154003194664040c2d03084030900e00500805854a800d009003400a000c50440c1e503260351104c02001d065480740e07010150358852000381c030510f950b40003403941c0715000c0c54001034551026107861500341c02c150302a05507080c00311301d03000402800e039542c080c840e01319410b1001c6042548a1159203550303075000342074036031180300200200d507018074411552002d0a8040c9031038a0300050946075000102c43c454031259621604640c046500103164506d0210410300f113100703910365242e040c007511410700304107403c000043c0c01840c1210703074071141c010752 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 436203579 1250 436202329 436202339
    0x8010f050f0702060c280801080c18130606050d030c02040606111f0b040204031a130f0f020103020909070201050f0907290403140a05071e0303110c04021909 69
    0x554074060b2460000758010000051182c140354002e03004203c16030b904040d16010200c5c10700c000242d990602c40000b02241c006003c01c040070000303140524010b558030140e14080c0c0001c05d81108000c3c1490108100c0c4003040001d0100c01c2c1c20000280800815074803003c2d40616014100c02440b8108038001c40c00c0c030100081c071030f0040b07c0d0300c40c3d901e0051002e4501269000c1071250500c20110301c1050103a9100c150b040701e600c403480900091445244515080d181c104868025400010300500850030b05c2250900012400100c05094030340c480c0000c41410b01a10069010340900361840d608501180d0030410110760541145005034800380d06100c0c50b8641d0250582c8405143c01001002c442054240554400c24007030b650300c1403000300181381041e440c0e9444048004039502c040030750b5406401c641c000c0c01002c0c4020341c01800e080980070003240c03482e040c0662110349440701805101c4441c010740704007041440711842d10748000380708550360b251001c150100c25440c4484000000c01d146000f00d2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 436204829 1250 436203579 436203601
    0x306050a020f040b070c1a0c011a1014090d060b0f0d050309010e15030a090506070806030c09060609281e120302070e01060e1c020904030f0c05030408010f05 69
    0x402d5141d031040910302410581c000d03240741c0c07003c00c0c11500445003510001d55000d400d034102e45034a002d903803080c0d512178980c2c109130f0a4810840103401a011100c084001c44e03078420f804000050324505040521030006080170754907003c0c49071095040b0321141c2a0100300281070307000c16442201107500d401c0b0078000c10140070700d89111600082c0654000c03c45c1012540c003506826120700c81c020030401e189000d03c001c2c5001a0429140780500580790554030301007003000c0c4403803a40407006103048a083d15080000030782c0c800741018018006c400100205031140c030f0f0307202244c090b58805484005002c4852411213410421020300c49802d200840000c58130081042c1c4a401e00f408205500031202d00701800244c1202e04030300104c0541c81102000241b80075050758050007098680c41c0c1c1d01c44459580c0c02d006030285040500004840300000003001a43e4941c1550b40050b0946082c0d80d000c8201c28050301c14a400480c003411030321000c90b000400840c15080030344070208010051003191a0207100381 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 436206079 1250 436204829 436204837
    0x71b031a0402031506060d0906020c06010501111c050405031e0715091502070510051305092401030b0406080a0227010b071a070305100803040b0d0e03040b0c070306050a02 75
    0x941c16000310707141c1308900546050341508001c0040c0043c3c03909000d800c40340101c0d1203211045940540100c0e000354500c009002a074010305c02800d050840b8007071120000d032104110000c5054580500c5c1c190311681c1d1041d400d44014100140840b40482d25a039000031640d0980707030081c02a4071074a08007046c0c41d0342c4c40d242035000380090344a056480381040702d410204940c241d1380804522030518006140ea40301d40080c808810262941d81d46e40300c1c14241800c41c00540e42016014110b88824819484404a241d2030b02c07140001880c0c0c520808000100c1c06000800745855220382085000f140019020490040b068800c4030181c034442182c407038224020386220701c0c0320980c1c503820b001040b440c7e001e4402000e65034814080d00c042140710b10030403040380c48142c441704002956070041180390b04101c0004405000c0e810019402c10340340551000d00c86c4641c88a112282d5101d4403071091007a130400c01d507000f03004218601c030340702c111045d20340f130361001140320503941c86042c0400b003172440702c41d07108507 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 436207329 1250 436206079 436206083
    0x30b0a06290c0a0203070308031801020f090402130807180e210703050f1b010b0d0203060627040b070906030209010c03030209010e03060c03010612021602090606071b031a04 76
    0x95500107002260100c215000001c2214040c01600b6900300182d5061208001071446141c2694481c1860107211015494110300c03101c191307204006240480101c031082c5d81c9060400c82e40541c2e1451801203440c414030036640041414814050b0100b2840c2c2c3c014148101160110802c201c941071151101795135601c0d9492507801c0b605001103400604e40400c0082111501a040c0f480c80d0540800312218154000d0000d01c444512610503400d0741c58081c000c010010b05c040700c01000481090300000c1d11241d000e030130b0503c55042c5004819400700302204d10354010310300a0b1500100e140070f04200c006440708032107010000703090034408242c060281c400d0b21410001a9640100740c1520780c0c5c241c009512034911a030510039982006500caa9040060714450319240020740d4495243c40c07805000761b01d24401c0040c040b40180041100010844000310300c09404603880d12181d12110085022445440e002801c000080c45842c4e98410515014400701c038414400700f45400d28441100b0700d0100103880c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 436208579 1250 436207329 436207379
    0x503031e06090105010302130f030302030a2709052205070501020c0303030106020a060b0f100329030c3a052a090402010203040803120103150903050d0908040906030b0a06 75
    0x504c1035510990280040015003084003151640f00c0101c001039840b2540101c0040e80000746212107203a00851401c41000c1c104a00b032900d000b1188407280c40701d502c0c0510b030700055a61000a0f2603500e11040e0741022210740d50711480420003802c0082c0c6884544c05058090320a4030b845c070003241070000c1228100d1f542e40d4040d01070b0781c01c103544120203049050102503012004800c28401a91080b1002e5664080f9440000340105a905d000c400302c0340506030110300443c80b0720401415140464402180c4000300e40070414805030b40340f110450130070002c50311040382c00074105030f1800e041d41200b007035180d00032001c03078510244502509070940c190441039014100100c4001a02d410100c0030550801d105005590a080e190141d03140b03150455031486480c42c4087c801082070103080d515000c9100a130100500c80600c2c0d545000d0564840d00c000c10020315926228401400440e0042d02c018001103402030041a03036900b07003007403010000d858046045190103000110225008103106000d003030000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 436209829 1250 436208579 436208581
    0x105070c12260f1b0418050615030907140f0d030f2706030b040209090c1804050403091706090705300304150e15030408070501090503031e0609 63
    0x403088030842c60b203815031415a01a459004102c03032818400b54410080700b030100038a40340150044c0c5040360b2103c0310707480011040006103c122440d49924245009180c004a600c0c1c903a036000c15501e04241e440b10ba4003100220600c2020710700070600004990100c02d0481c50322640782e082003245040c403c002c590010187c1c1042c030000c1d014540c24403c0d0b49050a11505c00e40d205000c805401d00d0340c01110191400003c024000c00d0307014480c5e810451800d480440c100038442001c10085a0091b00d0010000000b28104050240b10b501182c1c44810180c0b00f8440c1703007010f1801a001e5010342c0100d441745104202103555038440024000d118428110003400807601d40780510000e540203081c261018a079048c0c034030008104c0d1198820450105000030b50351946441852204401484196400c10100c1004d04681d60381c0c03a00b003202514003030304105070b803a211880c219020b0b05c15200d000b081c950070071840e0340034050003001451250761881049614000d5900d018111310408075400341d40918107030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 436211079 1250 436209829 436209863
    0x906050604230d060507030e0c090c03180109030315060e030a060c0e0a0e01050a05060a02030a1b021806091006021f0e1c0306090608061f05040f0204080105070c 71
    0x1488018020100c1001c003000b1202e6000858440c81c0359038415924640c0300d0042c0024580e0510030480d01000d5040034042000d9420000703009035001816044200c840070022600900400214001140c020b0700201b00d01c04142c54090013404030410310481c0c840304600009160360241e0700c908982c840042c09000c421607035554280c010080d6642e2001003248642c849040e545a01d030001010b000d400004032110343c9864200154844940c00907400740b1030503c00664000d4001068a14208a80c2446c840c1003c540340102150b18900c540a90701804150b010101c138030609944030300806056840b103a40e03940d04914042800103d10031000140c0c04442c1e40c884002501c030111441035143c000114010054001e22807800c407910700e00381d80a8003002c548000300f42d0140300741d10040840d040140101031518110305c3c1c1380d080c000e1240c60745c010002442590b5004074114407001c0c21004108010340d07180d20701010000d40003030040b112a90b1070007000c2220750340030307040350b40c90075a100d04602424440c0c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 436212329 1250 436211079 436211099
    0x206060904021c110d0c1a121519060e010905010219030315081203090d020606091801090804081612021012020d050c03220308070c110607050102040f0906050604 71
    0xf91000b644c4014401c22002610b60328040c065000d68000d11440c0700143c207001c25051500005200d00c42c0c5140c08005054568606030000381d4840d0204092102200b040c40115840c0201240b01c03151b41c0001d040301245050308205d04a049807020b0b0382d4400915222001a42c1d40c1092240c3c415102040c00e500342d002174481d4101c028401510034000d02255034a520107464681204011841c020001c8104030b41035000300070450085040344020900f500300000030981c0344c40007404008240341c48940c1100c1c299400d4002040c8294088041c907600c950f202030b810b8a4000170401e10301180302c0075400040300301c01e8504850740c69030020315030b030303080d05484000b56603001407200450b515a0702404103c204421354801e044c8584541c102069691400b1300d01c0e08110311903c1c0040000f8642040c920000c01d9100800560149550405600303c0c003d40c101585051224013810307501c9600021328604008064029004552011400d8007025450f004c0050a95005010f402c0c0c004000f030008000e00802 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 436213579 1250 436212329 436212379
    0xb0903031306051c090803010302270906011802030c0904090c0b07030f080109140a021b0a0f0b0711030d09020d02040507031a0604061b03090b030106080403020606090402 75
    0x100a044034a0300e010103858031888000742c0d1080d40801c1001c81c80c03070f190314404241c580c01094001400c0000b004a6505d4910070301060001034001e0701205048980241c10f0585840c100000c20381009031460603240ca0b9a40d15424000d103044020036105421400381e06001b40c0e40103006080040b410154010140310083c0344404055501000b01203001501900d52402881024040e9448021040030400c02600740441030744582c680c0d61405400c0410b164920547c10380107000c00d01c0140e5601000c4009003140000140074041a000701e0390000704100642c01070341e034100d11455000c080c96443c0403042d548080440c15510311500104810050504694012801e892004050b1312120b603440d000308080b91021a92803011a03a518070344030000e208820150149842164007901e010300700400280094100174010441c03000c44851541054040c950a5001e411402c0c5555100d41c1c1d03490f001800340009075001e8002d802401c001c00c0b4582000c80b5594030482d00904481c4810b41c055840e6204042 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 436214829 1250 436213579 436213597
    0x120b061c0f02090c0403020909010e060c0a020c1020010e011a0a060f0207170a02040609050108030421060c0f11061b032707090b0901140d1e08040e06030601050a0b 72
    0x40c05c110120051741c4940880d0700a06500d00001340700200007000383c0c6050406403202c840c0340802d20410900903030020700307581c0f0040250b89800744401c03003080680d4070700c1c0900604008480000300c40c00030100d055220b8103490354000c000307003c5003e245490754011203400300710942040703150030203025450054034004100044c43c4111490640c1d50892490401d00c00503030702100b0740028990f44150304c0d0600401d8054150802c0070001c5500d81808680c3d688510f00c101400361080c0c1d1501c1100540b00c0d00340071482038001c0803c0c4100800500c00421141307010910101041e000c10310103003030000000c2c0d0706100700c044840240c80603403c3c6103101002e40000303118024884800030b8410490040500320a440002070005081302c41c1050040815585560341840c02015007000410001c1d26400202400c030714150f83c500100c5003242411340200d41c11001004450542181e03510400030468010000c0b07509e00c0d4100c801a403280c0040688400081c82041e80c0485144d80501600c407004d00140b0700c0c01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 436216079 1250 436214829 436214851
    0xb0405100f090201080f0906061c020603011202180103080406110115060e030706210902060d15090c0c03020c09090106030b040501090b010807121b120b061c0f0209 72
    0x28a10003031410903100034240501540e5224024403045581145486400c11b895090310380c11880c00f041d180d903130382a0081ca030764031803104a800c4045c135540000420004c01e4000e4412aa20360b114841603842080d00311040340034540035902651030100401c03045060300da10206141c0340038900742c001c440c0751200040030140e9540c0c0d1030840800c00d06114500005000c60b880c0d018000b083c1104040c20101c090780a030301440380d00c00c0442c1d5860f6009800e03411030340d41c40d80300041d401c2680c008628140038650b59504050320b025032200300300345080969030884488400a01c440e59900c0e40c1110f14448013280203001d640b0441e40c41c00c40c2e1400101d500d900070380c1c4038000201103540340c488000310801613901b642e050b5500d05114044c0050085440c0c058035002000b8070405140c00300040b1442c11419014200119448203c007075140c02406800081c6032900105510503030301d09201d5003401e0b040d1151841090540c609181150f214900d01c1c01c000d4001c80310040d8991140c0a001f03100d50300801c0b900b490 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 436217329 1250 436216079 436216093
    0x14070606050405150423040f0602130b030912070506132618010903020303030c030712050a0e06010530011b09060e060702090a0e120a0c0201200a0b0405 67
    0x191076621610b4483c0b6210b04402d100c4031840001d010403104150701d0b4119520383c007880012684846c024031900144c1c08a0511040b54050500800a018481c3c000d04118007050f000100300350000b000e1401036044505032002012104000c004922440c0c60003031507900224005042004189110140d0502441e00301415081584410502c84801d4810b0303114020003003411815811070854921101b034081c02c008440c141560000303a074070b0000620025001c5c0c40040090301c0d20b4411400307020108803c1702c0c10f01c02414505401c3c1c3c064a04076455200c2c0344100310001070240b0349048443c100000b4000d80080d0102d0001c1009000904004ce404956490710301811048084050800402d0010b9962660090802e41d00501140c03800c0ea5492140100b4030800380507903900c031302c125001101c003400050380c00420b00c030140c00c1c00c9030b8160646204001140c02c80110b6000742c40042d80314404d03a0b4041000f20700c014000f14a90410302003100c282d02c800210300004c1c41c010300c2c0c00d4000d4050310850b910 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 436218579 1250 436217329 436217339
    0xe0315010807061d01080c07060b03011103040b10060f051b031201170102030103030206150d020a08030316022407090906090603150c270816051504030314070606 71
    0x20460280e00084a41d8414001000042d60103011444400801c4440060281644000906503503000c2c000c8260030342c000801c10108015544a12011a406002482081000440c10750a03800c22142910310880900005143c9a070811114050380c130140c9a04030800035002d021a92500b01051481c1150b80b80c3e04074a40e40501080a4115540b03103800f080305640c1000c100c5403002010321840c0155a0041c030042c0006600450080e40c040310070b100300d004281c1d0f624001220501c95810294100d4194800031031812000b0000314851381900b2042d0440c801000c504aa40341000d403800d8a0070004e00e03000c02c05000103001144d8000e00d4030729044405a441e1001c0400f140c09aa0200303801c136a84001c104208070a0725078158215451420800000e5800300c40900423744180c4003102e00700030024203541c08080e2121010240c083c7c83c080303481003400001ea000f0020b0307060242d280f140c901c10180000c00000d00080310152641682c80849070000c448907400b2541000600300da940b910380001040e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 436219829 1250 436218579 436218613
    0x30901060803040b030405160f030204050c091c201c051501120308220f020a1806030506060607170313060912080a02091507020f0402070b01080d0f0f0e03 68
    0x2015084804d42c40c0e55074206440c009182c802e004859071480d20500d80b0404c011103902188034210f80e010b0b200415a5654020701150a105890070700303500584404086114003802805901c069100e0344102e81e14803500b81d9803802602032425004e13400309050196010147d813400c800300c65113215000300e80b0340000c61124102450001d030001d0310413400130140d510626501096054008010b81c914452140f0001d5180140300f01e18403014200f0b242401c0b00c0e0045484249405000b800c005207446c0e240d0b1280110f074006424a4801502d013441008046134a40c0b602408480300160b020910303191840354100111300075003005140300c0c00540800c1b40003003c6202405031071500c174031494400703014188401c1d001d0304d035000141c180901e10348144800800c54580d0039440800c6070007100c0980d1100c1d40e42c40054000e40c85403a0b03041c1c0203400862100d04010500b207007079058905550643d503074072807a0441221013982040e600340016031051114118030b40106464211000050155003041c840c03101450 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 436221079 1250 436219829 436219837
    0x7121a0702030a090b0f1b07030c140a080d35010603020a03050a06210f150b1e0a060c0813030809030f03040b0301030b0c0c100606030b0f010212030901060803 70
    0x103000350300700046000c10305600035928405000c0721403005041c1a180a0039002c90b024a51003140305411140c2983d200304001c00c0084020340e031003030320780418545803007070103e030010204000790180300180b0002c105107030045210100c465043d641c1c003c00b12925000010403403182e00405c9040010107190101c44010040d0790740c00713040c0c1c5071000741c0e8980000d078009044a00040144031103514015040c000c042c0428a41c003901404040300000302112403c0c010704eaaa40500010840061584118003481194000c0304104200f1100c400083c04101d100020b106580c03100b05600030f0640c4000c0c08420b01030038501c015180111070450900131b05400e2103110030010340084d2810f02d00400e50048620b0108980000308815802950805181210031000740c041808002d00700414400003c0110b040602620b41c006040011100240698806240105101c0c010340000038184455081305040c903e228a603802c5040e40280010031030500c03402c0d032541001e02030044075500d0725400550148100064 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 436222329 1250 436221079 436221091
    0x60f202e0504030c1e050c04020c15090a020a05102c10030b0312090108040b070c05070e0a05010f0503030712120903020f070806190b0109090609150e060307121a 71
    0x2006103040c0e82c00d05e03031208482240300341000c002201d904800610041041c800124040d2805a21400720321003050800074001065002e10a0000c10000040c0e4001010020240240e681c00c2c0101c1c2c8400c188070155909160a40c0450b2045803003001500d00140103030f00c4409001c5007401071450084c0004c1c00c610304241d1680000c0d4507218814110304e003d0010804640741d800c076941c42c1080c240006000000c00a0000c1d0402069034000784001d80201d040294049d80103003640c0b0399a446110007101e14405580900f034a40c0f5000c0042050245402401e09541000b0020360424081c0d507a8100014600403d0703104003d081103000714a10124001c00400e60b00c26000b41c46600c107158091840c000d550751090865a2040051046c1d03200841101c0c50b004186c2c090119250f0407000042c3c0c0e840296900c031003402d43c50410300140d503500642c06110141e50391540c3c0440310366134130710f03040a814080c2e0b045989500210410031840705c60040701c0b011180310307429469460101400c4140130007011201 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 436223579 1250 436222329 436222337
    0x1803010b0a14130b0114030a0b060a0903050c09070507020607050c060d0603050c090411120c0303310506030c0a030b102a0f08030603030d06060f202e050403 69
    0x4840903454883d42810220340d0400041280e40c41c9180020700d0b010f180b2150311407940001010a6402c100c581081c3ca00d070a01801003070340c034103c0c128006c010310800d110541e45805040314002451600c910300c0da0086500340c4c2c60320b0410b803164081000640c0b043d1811032301c2c2d100f600441d80282c5c4800f00600206900300d0400508a07145051903824845c40e03405140c890201c1c0c07010880080e01881c0000c0c4a00c0c0c044d01c1d12a00c0c2d548002000f8602410050781e40d0b414440800d41c2c2d0b900d00030210300040507405050405a030750201040e081c40741e0f049070082c00c0e03000c041400010004601c640180014451502d000314084200c4d20200322441c4101c424000003800a60f01072090700107e0000e006c42c0b03c2c000301100c0640c02c4545981415a8007224000e1113124000b0224003565020421303a1181030005000304079407942c68034098140c0c40c0380240c48021072044004a04003a490304214000d11700204080c2500c090814007049109120383c41d50f5400d5100e0301511f0284032914031070780c1c1c0306134440e4407 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 436224829 1250 436223579 436223609
    0xb030f0c030d020304030b010918141612030f030b03070f0b30060105090609130608060601020d1205040807080d02030703110304080901121803020304030c090605061803010b0a 77
    0x107250518400c04903800540d882000100001031400d500c1c581140c55240300004c02c0385180c030030346801d00c00c020006010174000340565034402c507003c210840300e40681c9400c90070507540d44100e0904940075920240114100221810b0032038060382001203000d40080980390415102c14030284141d605810004020802003621104200092112400c811000110403c2e50724000700c1c10005060003000641002008142c1400a0300d814003a2124500020021040701d410800b07150014590341c41641950b10035400802c0071940040b44011400e25182c0e1811500038a500c0b01c40701400004e0030817034044174100f15440c040b60864000d44603c072600b14015959041440000741550b9001d05200714036403040040c00b000541685c2260803040c0e00f820602050341709071036490000c0c901451301d544688554030400301019804402001035921803c0e50761001510b91191004032030b503500896420942c01c01220b0540741485c101095803274401800852510451408030308000240d500089040c5080c078 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 436226079 1250 436224829 436224853
    0x7111e0d030204050a031401060911090301050c13030b06120d080106020601050a06080718051002010f180b0403050c01060f14100c0308010b090f030f0c09160816030b030f 75
    0x1200003841000c4030300d030541c100350400f0b0000b0b074091010f104c018641d03605a094501414000c0d00004000d041601d0f0401040080003c1c0000c3c41e4804031029129510304800515131100b0041a07403c000b40fa5140e1004050440d0340d8840030b04c002070034480c3c0c80050203903455910362003080500b00e58550740d5212813280d490320b0006440e0038010f0300142c0c40f590900d5010711920350f0006090f64064454540b03941480007241d01d0310360b5916940c1005401070100c07018002a65015000002e86c0c0707170344031801c01251000c100144110724510300010050b1002102080c0464816405000303080921030000900f0f41e6075482d88242c3c0102d0790722070300381960403000000c02441d0182d1151210404c80c10000b078070260a50b4020700d1080140288480210041402d070150303200ea03e00c81030300750703405002c0f6145031111449003a41c4e9502180480e200300700c828006026500451040e0f00d0512081d1920640380d12020301c00c203824031341d09282d8020185eaa40d0286ca440c2d070100412a4074030302500c09001000401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 436227329 1250 436226079 436226083
    0x90203070803030c0304110d2a050904080409020c030c0303010909150c0915090503010f050a0b030f060a0f0b0306070e040e0d0507022b0c081603110907111e 69
    0x41e030046030190024010000069090b00449a00a5001425030144401d0301d000481e91190050090510f4586954200213113025410003120f200c801480c0700300c00c0ea9140304011544e1022107004005080911040011140035005010b40c14000c8041c7c03030a05c00ca4042c40d130315503007090340010f11440d281c645040030321801844854a40c48501402e0048070130342074001d0009401841400c003003440041607204014443c401c0440508402402404000a41031054000c0c1a042d180294054030b0080308048a260003d05000196010310140015544629040700100310050700c00c02c1540d00d402c0304000503901806002d21031042c507201c0440d100f1004052000710344c00400d050a9503031066440707420088d0000243d60000d42c2c12100005139030028006240c0d10400710a40c0da4041e40709101e03840c1006202110034003921140c10469040344c10000c080c450500c1c1c10312002d4840c0e15105001680c5003801d902c0d26034000c036141003100c40b46105560140c40c04400040014050400c13407144000d031482 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 436228579 1250 436227329 436227343
    0x307020a050402070f0209041401091b15021011070b010b0c010e24040614090a11060403081b1e15010f0308040e09010b030d030b120a0b061002030f0d090203 69
    0x400c2e5011401c1c40d0480d41c5032003007040c14201c080d2044040318005400c20440301148002001500028090300d03819203041039200200107000d50340311025507004180034520607a1303440e103141c4a0703000b0240303920355146407002881e0b08034008200000070803800c0c010584010f03c56000380f12070b100159688004d084043d08540380b41e03084041c1904501a1086d80d0f03441034254100800c45040703085640d031180d00e1319900820303501c010314828a60300d0b070801001740c20216107140c4a50140041564500c22075082003468851800010500d5500344110300720420786194900320f2100c50002c40e01030000040c981d00071100007000110742540104007505001102114050042610b034125454042c1546e0350200280241c1c050301581d181100006011000250007500e02800e01800b40d4008072080c2800802805100d0f5186010f1800500030b201c10702d400080d04d96647d43c201e030708843c450b102c410030850f1142640756014210b210502c103140080b18600010034409200c00c0c00010b03030710310b03c0c4180360520170 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 436229829 1250 436228579 436228589
    0x60504090c140a180209030c0315010513090b0112081b0606120a05030403020402090109150503040b0f090d030b0a0b03010b071205040608041104110d0e010609020f09060a0c0b090307020a 82
    0x1010700c1c8200580644205134030304078415000c01585500c041b4021918010f0f41030300e801d5040c4a0304102c0303040c0d2032080d410340b4142c4100b80e070012002c1cae0100301600700381d504030000140030580420040080e05d800128038002c05125000803887d0140c0f85900285461240c074124141b9007000e400d0001c02e00d003440d10311000c550800b0142080b1003481d19070036201d009a204c06401960001385a001c03c1c0c0c0308490b50005045290025003501080000080440d0000c423802c407030001000303010070b90768070810300c090307114505100092806545c00d401c1117000d02109101a60000803201002c2050701c07410024602800005d6000c9440d59050700f8100b0000c100c0c0486030b01485810802401a60b92003141a5401034000c0511000d80f11a4400300d0003c21a03c0c6000030313000c201140004514846030406100205c0320070090100903217880b4000120b100d00b08034908401e10400c1071221504040c400362030740c0402400e0040500032180c48083705c100c022160f0020707503000015500110328001c4081384c0548 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 436231079 1250 436229829 436229839
    0x90c07051b0a051207140a0807030510050c270307080f0a0c0501111b030c0406030609030201060501020f032b110a09140d0206030612030f0903010513021f0201060504090c14 76
    0x1582405044c1e40b02e000d1401254025814201500c0b0b0940340c0a844a0090003100201c542046d50303424810f81b1008010b074880c410740d050a0104114102800658181d540300c0c41d03001144100c0201503040d112002c003140794141c0608400043e00b0307001403141000303082d000000341546103060f182c5482c030741540d604421b050002480036901c0041c1d0016005c620070305004090303004242200d000030301d00402100096030090800300c0110030801c26407c40d0082034880e400030b00002d40c5480040e0b885040d680d40d008a103034010310004a01d81c007510346005400790108a180c0422403544442026160010003100e1600e800280300403c1d01d0b881860080140503013143c1880402c0705100040381d17a660035030080d200b0500807001c00e1083c1e94480f240c0c00061a00001c4903a40e954035808103505821038000284079500c0c140004179030700c2b018601082866402084640803901203074118a803851400d0101045640e2100082041e40380c3c1d10403c10706a00074200c01d060285401c040c11041900c490b1414061 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 436232329 1250 436231079 436231099
    0x106060503010e1f06051803010c02061b120405071a030c1e090a180e19030513030c090204030c050d0f081c02040b030a0507050315090c07051b0a05 65
    0x46680602500d05480494104850984805101c5450500d18000d00c0b10a013801da000043e103c0e400100401c404040050084802da10781c50805080b50121002600560010800208078a1000c4204410f140b00c1092103401e117460302103803400102d0100c80480e00d40c0d10402041c801440c0e40d135500d0605401c2d00440500e18641200d0101c0c19008041d2260089a03240c42440c0c9140304003030a80e0740801015181110032599552259001c40c42d100850115916000d126850940c001c03d051a40b1112262180260700c240c0d9803c8805501289001e60381311000365000c4001400580f0b00c00042050810150311241982084800812a82c2c041403040d0003100c410310000d1841c8081080c0c041c1c000301210f46504455018460001081a44856641c03000401050014414015600440e08070008011030356a0385c105440501c010364000c8a801b03030020f0091124030384071100c1d942c00122541103500f096a15528107180c0303041d100224024901c280d036400240d003841c02c11a4000d0a0841d8003c4007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 436233579 1250 436232329 436232339
    0xa0f140307120e0d050102180114070b010308090a1701020a0329090a020f070804090f0c12050c040306020f22151d120303090c01030b0a0e190c1107080106 68
    0x4680c0202a900051142c022090b03100f50b503400c0211511306070028001d554802c0418030380c0f01003560000d011404035800541c0303241d00300c0174201a161a03036030111b00324000ba4216281e0100395046941040e1b480100f00c403000c100e081c3e08101d101d0401d59810300143c0c4507003080c50f01400343d50f81c208800001000310351440d110141885512010060203465039855915150030300300203849a082000802c810002d072203000c22990100510490b8880e400801c0401240503054050310000f41d20700000030080e061650f001c05090f803082d6005540401003d1a1503626683c48060b41c00c4042380601034140440e0700c01141c6004554165411a81c229a0a2070760801040192400c0d071000c0c080108007008813000c6400862815080c085500204044130560502d0380d16996a8821030f025901400380d001c041020b54003078094010350030b070007c092035102401c00720292104040203101008440301a1520f584101c0c4ea4440c1101c0300702e1640d00c0c030b884045440350441c03030000294050360b1a070b03160500400c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 436234829 1250 436233579 436233593
    0x90604211e12110a0605091e060114060a030207020406060c0210030b010503070f0c0209250f050f07020402070b01030b01140909070312140c010c080702030a020a021309050a0f140307 80
    0x10401850f41000f4a0b600c5a0942c200d02e130103e04000100380c3c510708000e115605d103001441d030114840c0c82000c8180b08080400103503d4920030321444e80d221f00f0a184014542c5000300c05844802d060b85001410141940c00080544649600900c085100f9919030015801d01c4002c44c15003400c3c60800740f0114460600090081c40004d0481d000c01940e54801402c451003550700c0300210b80c00034200c14190070f00100e0b0141e90700b48a1401a4180307000109441c0b601d0003501d940c5843e1130307182c03501c900740306400b4003180544c0d00c9658100e0b80726a00304402c1c400203402c04085070185004000d008117660401c441008100b4071100114031458107030040203450080040d1140549501000c03c805503140441f054230301d803103204803032120450301194240724104154041c0301c086000b070751201c00d552510391003a40c072480388854038401a0089005d00016017030070340f944000111144d400080b202142e494032030514080780c1c012030343c603090030303004005000b0841d1008124141c0840507610740b003000d0365101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 436236079 1250 436234829 436234853
    0x90c0b090102210d0203040602031008070f1203210b0111010204032447012003040b07050c030601062a060f02160c06140f090604211e 59
    0x809182007101080ca03403e0079105039008051064800d640780e0070715140c00000b94008840b910010412290001111180003440c0400c6641083c1100f01d1682080d0403d62100c0000c842a000d004c000c022942d010f65200742010102c0900b603200045500c02c41000600400b03840d1041c00d0f0780c0e0300521051010a8001039280011080700d48034184c180c071442011000b422020841c00c3c01e41e82d200d000029120000802415825014010581e01501c444030980180034000703050740c00501d07078003984000c000c005003000106641100807641010790300c0e249104140c0c400c0d00300b2142d94001d0000d0039520b042c10071640d405000d1500307100084c100c442c8059901154210040000c0e200400d06030018440240c0c0506402c45610100303641e11455519050a0507060301c104503a2511403420000b14a0b100c0e80700c0010050040302e60078680502c1c64240c1c40142c0003203207039980c0000100000034031a00800c140d24029441c001030400d141c8061300307020f6007a0740f5482c2c0c803030302d01892040c13008000365000c0a04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 436237329 1250 436236079 436236103
    0x8090606300102040e010f050d1509022425122a0c0e06011e110c04050a050906090c06030103080a1209030e030f0a0506071b050102030a090c0b090102 66
    0x11400c05030804010780046140203a01c0801035100190100340380303031081c510f1416121100d4504464035510070034080f64607080301026105d54000910258020b0071030f0040d2910314001400c0a40341313484403201943d0f204a50a100c1154080028801e0708400550942018500340000301d005141803501c40f4007641c0c280d58500300820200342035a08280a404501d24030760180280c9002036086c03185000340c3d031000c060141c2c02d0769410800000740c06600c512444101d0300a0080d01500e201d50a106c2510030341c5504080c0c00090190884100c4107844602c01d0b90310500004401060a0804540c56810000013412a4080e40c20a44603c0c0198036090116030441c0da02130f81407070b0707210780a1000b20741041280340350748045402c0508580a1562122440d00a160114103840f030141148110550300d0036030a10082a5400c01c1000450031b501810300c00700c0181d8102c6822440511031b40d0b490382280e108807622040c2d9982e4580f0b40e4184501c4510305030251041d0006c0a00e040d95150010b95102601702d44 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 436238579 1250 436237329 436237369
    0xf080607030e0f0303010b040612331208030a060e010e0c0a030e011b0f030608151803040602160501080702060609090c06040603140a0501030f140c10020d08090606 72
    0xc14061201e00308082084070343c12105403522561501480070071079103c1d120b89000202e103034107074840410f114031490101c0014140303e6004500081c3c00d00c040301100e0100d02c00071140c1c1140005c1c803501c1c03480342240384d18403e01c1016034030b16004420302c040b210103800c88040c0305403000041c80300641200c071440d0000401280302c0c1d251215541c044024101c40c5a40d10003a509147c1c0641c400030300c0c0741d5203850304d4000d5120540c003481e400008808881c150701c40d48070182e0144010364606121842d9468100b0f691233440706082007484040ca1450340503034030032401a80003207042901001d2400d8414041e18007403902c0c0b2001d040010000756a6440500784a210740b010304046541d04804000c06150750780003604540e11150380d80d0000d0001c00b02065003070411401480082ca003900940700d80d9040c1c9610103102141c200094491410b00c5043d11200d00b414412065806040d81d10014800008901980200b10ba040e048400400303d620150015541c2d600c035105102d10740ea280040b0142b030b0400070003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 436239829 1250 436238579 436238591
    0xa0510020315060d1b0302090d020f0d081b010e0105060d02220f0c11010908040b0a050403081812060103030f0f051207080612150703050430090f08060703 68
    0x2924100410680b045940c024400180c084010700e06402175030b0790045d15110040d20620b40c51003076050f07104621b0800c3d4040d40c00c01d120001440c0c8070303485804000740904040c40040e1241e485070416480f04082084000004403140da8030802405544880002c0340001e204504000020401200c52468003c0c4a01d4a0703c0b40c440000481c401c00c2da1840c029100180410b4920700b4054004020702681c0500041c0010340b101d9030a801405145501c0e580a48000e03c2e0903d41071850700349410180c440000c1120810000022484100103400013032200c048030102d0000300b004014865841e207185800a800180040020942003480961140c090342000365902c0718034802107451303200b489402c0100e515242d00703001e48980c1c0040441e21450b811386840c10100c034610815030361420801c03400307048118614001005e0501c00d812040d00180b04010411280d26442040d00007802400d040c0b0b21400207a02c42036500b01d9000c00340c60024030540600c803aa85081504864035020010311000525450320 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 436241079 1250 436239829 436239841
    0x18060d05070b0f190f1b1104140a150e0a0c0c15020a0e040915020a020307200a120c062105092107050c0d082203031d090711190b10080a05100203 64
    0x17003034111f03020001c008014800c3d00b582c001c1404001583c50400180c9402c8010f0040703803015695005490134100342034016550344400c071014140d40c2107000204000541064000740d0b05401004903450b52040c0076031a200c41031381c01080011000340240c411410120600c000c50704403280003001c034540034000340e40d0780d01014059285203c0c01c0c1c0c000b020703000c034141c0c4403007140455000c0b41c81780e4a089a00000c010307613030740180808443d072441c09010700001940c1004801d00500508914040c0240250312440c4c0c542020310854108450380d440581042e21001c6140300301412010100e0391441d2224100b0445071101e558644210810030b0161980e1540401400100c8094a65114013407010000741040800d1880b80150036100c00c40200c1c0700424000d4940340205840155101e010303162217a0356480e00740840341c548903109599640c1c000e20f17032210890000442910b42d10750080e4032484c00d9050021000440d80a0340d40400101d4000104500019001194207001d900207201e000d80c40340c6902d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 436242329 1250 436241079 436241093
    0x612070306052211030910090213020f030906100609120f050f030c120405090606030601170a020702120316080315130b0f18060d05070b0f190f1b 64
    0x2074201503800800000c40000f2082e074040780200c5400c6201040c40441e44030940c03c082c4c0d020546009070345070004509603803c0e501c581e201d144154001801c40002e072000c0c030b40d80390403640140c16102c1c51100c00030820500c0081000034642000100c0302c0a00301d0740c40c008000b070180c400c43c000d00b40303500c018103130220601040d0b11840d00e07829004400d0301e07003030904141c080f5540e90107151040d086000300303404100e88d036a03100c096804492001e0300e0803d180d41d03080c003041a59407000786070a0601c070859107140c0401160070304151150b00d0301407005a6071080c81c010010545025402e0158503402080342601c40d020344081d003205107070300085d0316071a078440f0701c0d403d038421f425502c040c0c1d00601c401c0c003080c9001c1d40b00d0700400a910002c3d158510701c0b410000038411810760502519a91220500c041209824140101015240217105035100a6220031301002c041d44103101c00b5000100119655180c1c00203150000201455801c040030b85904c10503026142712001c1001181c250310f1107000300207201017 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 436243579 1250 436242329 436242341
    0x60a03020f04082e060e0f1e24060316050708070501051f1403070b090301090c0e06100513031b09020d0911030a0203060610020705060a0504060f0e06120703 69
    0xf12000d886902c146100e008824140b8254840b403940410b040c03051000388580300b510152207070303010540216591043c92020221010b0030500801b00c07182d00315178000d031034011458010181900840c2c1d1102071036019a003040020302c1247d100c3c030010801c0c0807520721b0715241d41018000600740f640d224804d03030401c4c030440c0c098000d01400302e500b01000c10580041210404004600d1b0b0291924603075151240440045007500905400d80c0c1304160a002a002c0380b000341c00c00100c02000810001e1150f62684203102c0706501c508014000d01041c0505403406d03046000b01c030900c1b890100c0c1818029810000b82084a10001c0d00464406404130074620a50000c45c0c05007803000310035076480034a00724010003030510344019191a00c0c01c1101440c1032401047c060758494000f8020070341611000c1c10806002086410300d02036100d000310006180d15074070042c008c850045c0d1191900c9501c0c2400c0680030782445041c2c44104440d240d65110340e0750b1100183c5484452540081d50139544000090f001044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 436244829 1250 436243579 436243589
    0x702030705070e061509060a0315050406092009180406140906040302070902030610030203130501110c0d180e040312060902091f080105061303080706020403060c0e060a03020f04 78
    0xa40780049100e044440d00300c1e004844c2503409100c198000000e80780319010b010a4698400c2e010003071101418865044100010705107a45200c0ea83d543e540003070200c90703040c0c1c09807076116140d0307548107001c00c6d400010306040d011540540c1c0ca803000402c0000c1d2840701e9101c1c41d103182c009000210381407103e2580044142c18440c2044074a0303050222145503504006c0f101100140b0a0000107d20190240240c2c0d010344400350592001c400354400079806500000c001b80030f00503405c261100802c0d0240070f0881a40a1540295612804100c0701414004415000e0043c00b04030545070754a5000c40c049a41181d1480d0510801511940740494003a1490b000711503481d81482408034406485a0040003002c0c800c441070408080c600b015070509105440c0054040380c3c00303100401140c02c100c401010350a401c1068201090340340d0380c40c2c1856400c442016203c00780c0c0400d00b030080024610500e03198181d542410480b038810b40c00001d500c0e104140c0401c0405030046407604186a0003801d40300580 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 436246079 1250 436244829 436244833
    0xf0b040b040e12030903271306060818030706020f09011206050a0317090901060809070905060916050d02070606050a05031b010513050303160c06081b07020f060c010504170f0d050702030705 83
    0x24000c520012440c014243c1e40740c89142c02041410003852310b0700c00c2c1002c590480e2506034441e0303a00c09040e204110164001e88081c082003201d84000b034840d1005001d0300908039802d40d103406012000500090b0800881c1c0c550030b141010611180d551014141c048960018080c1c090000380110403070b180c050310490030340040c0140d0001c80c11540000030184214407070411949030b50b50740c1e92020306981055560765045841c8401103a1182450000c541c480d508608040340780480c5c7c00040c2013280e00248094502a0351030348240101d00d00030000b03a000345412401002e485030700921141600e02d84150f1039052010003e405080d1822545188004200040a494542d84060f0b800140303a24115400c507110b014810b004901d0600800d081c074000d9150200c111440c400c1c038661250654800542a170b40000d004983c01c450341e60390b030010a1119022400403e90382801d03d072042c0006070050482850341c00520880c9404419131050310030380c1c200040085611381394000c00782e041d48645071018040e8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 436247329 1250 436246079 436246117
    0x80a09020a150804021f1e05070507080105010518010617060a150305040204050f010303080103060e100f1d030a0e1306080604030c03090509010b040e07120f0b040b040e12030903 78
    0xd6508030b040c6511607802503e41002da80003581d46e40803005c0c100040c41c0e011501160b42d10300c1c4441086003003c0c451350351782811413410025031102858130749103078403501183c5c3d12240140401d0521211000f0b0017205002542e5940d410a03c0203480b008400300c0c2d050264010400090060392680c0407500200341e00a41c090040c11400001406400c08840a81c000c50a110104520306a4044001d040780d405543c1c2c10116403c654504001d44000c2040c050135119a500c482c100f00042d20400e140f201c003041000400c50b05c0240d2468111030b13940b80c920200d400901c50345a400b60400110781c89800c1c202c0d092050100a400381e48001d2405802401d0280309100130801019044405c03041e446000e42c4030311031929520020081015000d0007070502001c17041c01700700302d1000c02c0401c607034101d22a410084180014615004202e0301d00c40c1031001040e4407002d03000944e044c07500c5035201030300d825a000e0106040914003141d85419030304201011030400030000c0c0c1041c00910643c1e00600804110402e8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 436248579 1250 436247329 436247369
    0x612151807020a020103061202010806010804060207120906081b09040e01180f0507140f0d030215101802040f05101b0602030114030102030f07030c0c0203150f1006080a09020a 77
    0xf81e4510f109049003c03902d018400720b41c1c90000c3c5280907606505a407088180e40e1140d00450f6002d401030000c0f41c542e83c0038424500000c0307005c400a000812141d0300c2045403450702c1c0b00207150820151000f5072241c07288005c003103a40c0c28003003100e1103010141c4022401491403032090707006050000010501c00c011100034403c000000d00d0a03031070640240120360420352580300ca1200c4d12f404220541d40200c0c03410b5031080701c0c100304488008030386c081d005807074060f1050500c1a10502003200c1c0100000d40c2d07020309003c1d01d038440041d00640e80c1e0203d411030606040c0b441c00484103040e80942849802800f90207040ca40c850031200025200d608800e002c0600c01d898a40c0180d0802c0c014030307105c4001000c0c022840d060500c01c0d130b40314458904400409449459050f0020401d03c2140f00401c004074419001584041102084c4652083c4117803c892400005003103880c0f40c0036207482c0400d0b0801c1c0741040081e038420030b520b800003c000c0001900011070300c0094044600c941c41660222140c1a002003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 436249829 1250 436248579 436248583
    0x90803120114030706080f04060b06120a0f06050105031803040b0f0702090a0b060318011d0f0105011d01150e04090f0b07080610110c09011e05061215180702 69
    0x1c1281d00e0000907640d101e41c0607040613164000c0380203083c0003941a5000506c800404200c43e90000d016400000310b81e6180404500264007040594500300b0500d01803000a00c3e40d0b205000414800300001c2188030f0038080020036038423019045484000da003403200e0040c0601407080700d0003000030700c01c440d035144002103035203015070010719083c0d200c0c4807004002401c0c6c40c0c803401101c1042100400b01c625507034032004041929036a0b104801599036a2700f00c02c12041e207601e081104521000c070020084900034030900c0d400d6481c160040401660040502260750108181140c1501c95082c5802e151490110084a8114080010b50307401801e25507000103100303902000c02c81d1180100000c4000c1da40e124405c0d00c03034003000d50340140c003c28040341e071014581c410500c104074034801c1c50960f500318004d140000c8102600380c210302c02110503000080d00400315251140f000b0002521002d0808100407440b200c5400018041e182022041003104041c0d50380354044d2891031030100309000c55042c102d400039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 436251079 1250 436249829 436249831
    0x103031709031305040f090602031932070c051005011d0714130b040f1508060901060e2e121503020105091203161a0402010806060a09080312 62
    0xc2103803000306045800c040200da415001d14440450002c0ca08814080200040c04820750304a54403080c080c0082d207240000c501410501c080024400d107a103085400f00c944400c151480082c10380d4803d43c03050b840d00801c52212a030b00541250310390306e2090a503500700700080001c000d4003c122041c030200840d94011810380e84940d1402d80d524514021507031011701d00340e0302c1c100480c107401e50b00601c12100f032000301121074000d011481000d9071800d009440b0342103038001e818101940802807250080f900020f090484040c903100f5140d0070f0400228074881c10600400c002c01a070707400c044001d91190a69a41449400740540322200f491004100c41c541114130107100285100c201000c12450602950340050b140524445005145500544182d800400c403147c004107400e01c10b00c015041440a00302004003070341254400c0300185045003024030500c41d0305c075207159406d040c4030241c0d91061003194000020790f170781030751103070f5060056402066135407000c41c1da4480001c100040c8030f1904605 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 436252329 1250 436251079 436251107
    0x40f032a0b0a0801080609150a06051e030d05120109050c0c060411040b010c0302030f0a090503030a080f06123a0c05072705070306090204060305040327030f0206040905010303 77
    0x74010366210240785890300700c151f980109580c04150310103510311241202c42d41002070b80c80005001581d420110300209100300c41040800043c180b00380c80d5003800e1060401c80181803038072707504e003480606161128034410300951900c2941d0b500003445107003001044a0304017031440100e80e0070f840e151902d0707490400c2c2411290300803414202c04102075400b5400500c3d42c25410f03000740d402e1860001d00001c03150008480e91041000f030034800111500d0500040003214030307903640e0391001e1408a20340c42c03240b000580101d0007075110361424524404041410781030140500403002d004a0305980003210680441d0100700713000e4000030b02ca14000e81107043c0c04c0c1c00300d03c11425103080555904003020540075030041c0c1040c0380c601040380e4240052a9010650014484c24000745090b160305440d0120780182d00702d1400f080c1c0e500705101c02d05030010940d03070b128a06545d2500600520b51104241c8a00c5031100804113840c000d003180c115074a00d000e480c05883c600710304100540c2c2d20304000b82034003040b680d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 436253579 1250 436252329 436252337
    0xd030e0a12031821140d050615070302060103050106080607050f0c12040b130506190f0507050610050405151309060f020c0304031704061b060f24060203040f032a0b0a 73
    0x50201050292039508000006102000d05101b4841d1414028007001042941d01c9890840d110399004590f034003400c8600d00030f40c002c00b095811032500314211031f03ca4005104070740c050320401c80801c7e03000046801e00307817840d0012034646a240210502d407926040c45580840f8001c60086850400b076406001810b0400365010609590b80c400d21403180b00d80b114442214040c1c500c9580d007103004040303030001c20040b0f28040c0d02c0c0142c2d68544e5070400605072010100e4030303403282080000340303014011290001d02d02d0700e0301c1384100d8145001820f00c0e4401d11140340c1e1035455542d00402d20406511141c64284501001e5503195030740360825440e0b82c468001141e00c030010800c0448000c002e0b500745c4054a6060311410012080342440960260300307503204607010ba40710380c600441c0302224080d9a002d4112040e1056100243d00c1d64000e12106503004501194800e010820610600c0d04240c42200e81000d07002c46c0c4503000c6411300064044001c0c8104403451294400200113020310000c0c0340403103d0b551 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 436254829 1250 436253579 436253633
    0xb0a1206180b0d0b06040518010f0606110c09040b0603070302040e0f010c050c0607080a09050d02070806010501030c08010510110a05070302150a050d11090a0f05030d030e0a120318 79
    0x810065203483e4403c01030a0366182c10000790311401c1c603a00040e00080024030301610900030980e400d0030f540f0412180014030341c40740010400b2942261811410340c060a0151009d8612000452080c010082c40030700706252030404202d0946080c031040780990380291042c005680070440c0969114441c0003096215843e000446110600c24419200c90b0070717403807010b4001a2a1800100d8138080042c2102502a41d034041c2403000400400010b040c3c42115006818400e1422202c0790030000e05074403035818503040200d80000715901158a5055402c11941d0500d10f40082204455840030f0010110151040d10109424010005120000c83c0c0c0b08480643c2010b0404610000c01e0040041c60380c04681d003481100350307102d413640080c050740d4101c0114501f07010005c0700050030222140d00404200d0304120081c030550400740013040560308981820f008601c10f50962554030710201d0005802e40d2103ca10090030701d4440d40094400000100c010000107a550505070300304921400007000c612080e413 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 436256079 1250 436254829 436254851
    0x170a0201090b09010e07140105091c030906020d0215090f0303100e130206040501030b01031b0e04050a0507021f020f0a0509031c02060105060903120301120506130206040b0a120618 79
    0x1000320343d80380301a807024200140c47e01031810421200550064140202484020183e496042484034494000699028011202d040185c5030250300d400c16030446d0450400c1540403038000901540e070300500750901c03081c0d80e1030f40b07415810002c030f138550b221060200005105641500c11008419502c10348282c00c1c0030380342c402d10808030140707510300290004014081007001e9030203a80243c442d03100606011602c4000c661040400c001c500c5950703804500030031062a49810940314269000c61a50010408e40c1000a00a0342e991f455854100d1001106240e10404285940568424898101145844081c242d401070a5070300402c0d5464041e20079000c141c030800080300c070b03851003101454014100590902003031003500e5001028568152040300314441c5050342604c025402003100c6030324004040018a4018140380e03000d05040d1480c900b01e40d1040150340d4034011141203c6091056980d550050101540c40b401c002c030f8501c0b0b00e0782c42c2c030100044044003141001000a84c4010130006102c2c09 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 436257329 1250 436256079 436256081
    0x15070c1503050702063303010b12010203090c06070203070b030414010905010506010f080415020f0705060c0301050f030703110904150504050c10090b1603020a020a0b040e100b07030c170a0201090b0901 88
    0x18010313403410800300e8a1200c1141b100f11482c40c044800ba00206095649a003c0350742c408100403904150f279400000c00c500d402080c052100366070401c455030740c07800c0100d8000a948884901402e01c5042c0008041f070100181ca031203100040c01d502000340901506070421a008000440380300b4003042d8110039401c0b071188140340641c89180d205110824031f14400091100a40140040d000807000070015540440e004001542c0724807240c150440c0e40b5810001404442c0c40c030b04004a02903804241d00b0300005404414038042140b080d54031004603603581c2010414810f00580fa1f9807200d181800b071201340100407690b1841e01005840880e4140e020040844150300180300e510592041402400300e0000daa21004000724020b01c119042e522a50300041c00c105041d602c203d410100000303041000c2512010000d601484810600c0c084500d03052030502c561244020050400208582d80b40c200402607425840b00313001c0009072a12200348031400ba00910076034401303031400b00e85075000804000341 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 436258579 1250 436257329 436257361
    0x9040b0103032616090504020409020913020c150717090c010f1e0806030a060203070f0e0303070f060e010905010f0e060906041211071806090b0108010515070c150305070206 76
    0x910f83d403220359218151164004940094102000103003d40010f4a036a9800640064604030364016600d08914040000c84d400c1c2c04a40d0084a00510030307078400c2c010210740c6400465010900403d40e03078403075104991640d50610850b450b0982c240500c5201c0c00300085200c0c0003082a00c4800300080c03203031010b403101c1d009203400e4200c0700c40c00d5510340c55281c42994010303000240a01101c0300040a540d800040c0d810440da641c000503084070b0303d1915164400801c19030102d0a1f00a50f244c4040341c0c8600c01c0d00c2c195108003416032501c2d0f1904900e2803000b5441081c0a0750080005c2025240c0c44a800e0040d02c5c5051400e020361142c580451102040802e030300780160740c0442d1100e00f44400c00801e46000350042c140c6909806610b500241c0164091444058800010800600c0c1c40c04c00f8080411101130074101c0b410404040010312268442024002c1c03540031401c01162a42c59511303202e010036203e908079003201c01e581e2156020054141d00428001c1015409a881c240d490003208051801e03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 436259829 1250 436258579 436258637
    0x30f0301030b130816060209030d0e1008090c09060d0203010606020c0a05090c03070f0203071e1211070302060d1104090204080607050a0f050d0e16031202070302130b0301090209040b010303 83
    0x2420000c0c0f0342d82c000c5d035100c01035031207220f1030300035040590034000a400c00500e0018000881d081e0801c10003103103010100d544d04000541480049401c01c1101ca0b541c4400b1003040d00c1c094110807001c20742c25a84c4182042c009540140240a25a1104402500d800c03000d500240600d50302400401d00b4036101c5085031103003481008540c29603841403001c07140c0e0080c4481c56810b600040081340b01050094094415429407500b8021940016144c02d281c400354500c2c83c0b41c1080100d886404d030804001c1441d40c00c43c1c0d011140d09480300d0403603410f03034010121214600c081c50000600051440043d07000b40040b01d1100d8195030321669124026078551059400000000d19281c0d10b00500d58016005856a208469400103040b000d0b23000e00e916002d00e140c19144d906031108010020421141c40c1060002282d102922189140d80d022801217190302d00c0d00070b0701c1c2c0e80320a000c09048d2000d500081d00260000c085030820708060800040c9072200b03020a0303000480481c034084021551951640340d040d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 436261079 1250 436259829 436259843
    0x200c07081b030c0f010e0607030305090d030203010302010804021011010e06060406050a0302061c0f05070e1e0a230307240804081204050f1213080607022a03030f0301030b13 76
    0x82c0c010080014582c0c40c0e40c81d09041c41b01c4000f000c42e16848203800303840381c03c0c0310f900e00007841d090904210f460130400303000351010580100010710050364440da2550704541c0c1540c4443d03680c402103006071040300004240d51100e620b003181900c070002c00056014000c110940d801c05c035464444090000b12021404080e4110004104800c42c4040300d04855150140304800090f180c262443d560040d1901a5030a200058070240b424030703d441c101d2103010882c4801c10116102401800218090701c0c40782c495105c88000801c444266000ea0102e0300081070001400d1300c941540340c1c0543d08000300d00315a45000c051460390205d1400707028541680c080c89d008004207060000c4a00e2070a442d0800400c12501b9008411040702c20301d07401c00101d1409200c3c00b540503103a1940e0f200f1403402e0801039021501d56480481400002c980200703140340400700101011202c0315191020002c01c020111040c0c2d003500c0000b560301d0000f000c1c0805141078902c9150b00c030b91952a04d40010036450103e010180c441 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 436262329 1250 436261079 436261093
    0x6130501201f090803041a0a05190903020102071b0f0602061308090303130b04140d170304020a030f0807110409200a030c03050313120302060703200c07081b03 70
    0x6980d0702060510300003006401081c001e503d5031366140c01da002a1022140302d40c0318034012034980412070340c050703104101513010065881d1016000c1c1c100038440c1da40c580e41c01d0355000d00b142854401c3d01143c2e0496040b10380381540420895031088402c1031882031120f030040111000c0386203480424654040c1c0c4901c02200702c403801c0c80c0c4984040c0d600c030005859040c807042109000f0081c00001d0203000304018004251910714001c00c201e6880c40700180e11b1f1055914124031000038444001c02c640b06e1209084246e1296514400704180440e240c201519140b42d10303504104000400e8001c3c0041407080507190304501080b0148010b50b20b402c900142100c0030341380900d0900c241800c060500190080130040e0340c41e6240c41384610140250030030b5980d40c0000460081d21440801c40360000c140b1890500c1d13000d81140c6000b9103821015000000701a1101d0b100080d2803007032900c0c1812031004410003a40e4054042d08260703940d5051103108801e014041d44082c48400c10445c00d010344201901800b80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 436263579 1250 436262329 436262353
    0x12070e0604030b070f1e0903030f0c02010c060506030a02091807060309080304150605060a0507110616081e0a0e03010e0613110a080718050121020111010b0613050120 73
    0x10220148840320b0800a400c1491511581b010300514215080c54881442039411414014488021781441c1004c1c000012080320060760b215480d401c1c183e8002000166540b80c0d080000c1c1803586000c0d0281d400030504043c02590801c1d0011000100d14940442c0c0804d03907140d5043e42944c0b50340740080c0180c80d0510000b0041414218505e0142082d90000940303951201d00103403e071340007000c001c0d000410100b102130070442200b2244001003011211242000d01c8511080c5a1010000c0014100000458844030b040c807c180c2140c541e0515002e915107070400c0420013466072100e48070491082d0f0800108030103500000c5602030203040170b02030300d2004803d262150314080200118203900910f0800001402c88002c0c040072020341450308882003d0b90704205104103542c01038211101d042d060b5200b1183c03050403605240d02031542800d009040640c01c14065004020b00d2551035041303980000d8001424006034810341c1a1034098a541c0d14822500480880c1d042d820741c0c1d046401e03445040f003042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 436264829 1250 436263579 436263587
    0x20109030b090120120c0f0418020921061e0c1b0d0503091203090705270c04080f01052214030c10060501050a0e06130b12070e0604030b07 61
    0x9807000c03030b1000118140108010303003240910424051304080074003061181500d03001202c01500084596903c1c0e050212203001044184194415030303050400c001c2100444a440d41c064605d000350041c1680f605900b14903220030410403103080b013200350290030001034100c41401550345411410400a000075940e601c1171070340c103030301401c0c3c03403450461301340c2084209a204000b038900040881d40c0701912410060b000b00d217001000f00241c01d40c2c080520802c01c1c103d000107034020444078102d444c803807690085041c10070049090b400034004160000100200f800c240b40060003182c02050803100e1000c480c03800c5074229402a101c030070038621000440c3c0052150a251107501a008800f2041000d10969034a86543e111780140501608002901e400c0c6a500c1d1240c0001010203080031454a008000d00800d584418a41c0b0703440794601003142c095150314030f00410080d1109100c010350364000303800804680380c1c0407110400010307208401c00c115802e201d0140c5048980c002d95002203138460010a031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 436266079 1250 436264829 436264831
    0xe13030809030c0109050c010206010509090c2b1202060a1503060f1b0306080d0f05030a2c03030910020403171809070c020906040c020c06030604020c06040c06080112020109030b 78
    0x8881c1e2000b4055080040d01c00c0c414450070f1842040101490808803001a003040416480036100b95280c2c0104014414040f42103684940125464125581c08e064a544101180b45084030000e8210b001101080699041c82e40c842a55408481460341d030025440280c4a01101d82c1e8a40c1c06003c100f00005000e507089205861044880440e034020b00049460061030a030104100090712680104407c4000307112201e5442c600f407400700c02c90481e0440241603840042c000c0d01085070b81d1000380e48506001d0440e80049081c501c00005909581540c06035290070989883c500c03800f580c03040580f10b61641c402c030342c2207070f92042424844d895a40080c404a402c01c94000164961800e288106940d41c008014070480080d1500c080c0300540d801404484000200302c6406585409007004043d0b40000f0442c488250448880e40d0342d41d01d00000c00c000e4005c680040031984501c0003840204101454124240e80045d914020583e0703903011000c0c0404003c05002c0d011414421081c008583c000030b0711 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 436267329 1250 436266079 436266091
    0x22a010e0d0c030b04150605090f04030507030e0303040f080115050d0b07120513050f06090c040c1106010f15090608310b070f18050906030f01140703060e130308 71
    0xe4542540e1307481d804e030148000c03581181e0304003100f80002c0c0d40d00d5040c07040b0400742a05a5000341c0501d880d2004440c10080600060b09102c8085003081c1018403035040203003d204042d058a44441d61001e1402c60f8002c5030080894030750030003010303030303c00040d04a4070421920002c1c030500040846845030b50740000082c1030401000310321011440e8009590040701d01034040c548002e003000e0340714184035013494000c60104d0710f1908403e00b4005520400150030303100c4070084a0000c0d4209100c0300964202c0c1c2500d0a9440b1070040f80000070303060b80d03003a07042405c0303602043c0044810189031004480440140c080c610101c0c0110b00400c0c02d40000c5840f80c420f03401048000440f100b1030480c200e02c2c0e5502d281b021100c15000204004441d540015110f041443d2420038040d82074050000101b17001050243c5c0b400382c41580001211582c04100488402c41014004c0203079103186140ca50304240304036401e201080c10710000250001039520070901c01c0c200c485804107a072100350b400301c0d060075000c0c10b1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 436268579 1250 436267329 436267343
    0xc0307080f06072a05030901120c21020c0a08041d1003080d0605330909011211060c01050f0601081504201c06080a0b01060c06021306022a010e0d 64
    0x43c01300b1455800c0d24100300d06000760025070312404000c00040504405138079a0306424200b845a2812a81006901c03049403540303c5001501012101484028001c0c444c542c1041e200b03441c0820244484817000b401624941c00c1d41c49510180001d11940080c0240d401c08503900c00508104081007d2502402040821800208400c0c1d5103500040482c1c50201250079441080c600c1c61503115210354151011128904180d82011020350000740c80701d1052150040082c05000d19400300483d0071107501039040000c20b01912020321200560003008200c0724008440c07454030100f0055030140c2040e41c444d13440b42c00369030707008082242400064407000717542040e800060851074100c000c0da440071706005411202000901d910842d070200a64401e40d01211031900250410000700302014042070658200c1d04240d4480380003480c150300207202e10789410140c05c0080c00081030031680426440304400074800c0c2c80c0c01d0b100c01190807030f138105050035407a03010900064060380c2500300314543c24129805444 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 436269829 1250 436268579 436268627
    0x906011b050a08040e0703050105030115030303050c0904060b03010306230a2c010c0e0609061e0405030703060903030f0c2312011212020106080303060418060e0c0307080f0607 77
    0x1035419010740054000c845c159100b402006141c0e42c0c14801c01d40140030881c020f225003c03040c04080500001400040c003019103460000b12800d202d1011640e014030068010000306a07114203080d546c0d0800c0c0400c440e418180741605560720314010b0074100a50b0001c40101e15a259245104020070044020a41e5840360b02180d514107041080c0b4640302c2c0c0882d500103d922000820000d05001d80c2200481c1f04e0002030003110382c580c07106000d40f022144413020400050039503038120506801180c4c08207515205981020080194070b810030044148030307482c14042907080030590b0781a100020744000006025041c0701c04011513640b000ea03403032524060f03c689040804c0e01a00c81440090b040480949641c8400108100c0880b0409030074813914800ac100d1036081c25021a00d911000d46200d200ba51140b06100c4030503ca81c02141d844c40d0f100030b04000705150a0251511100200095813080c0280003000071000c0000c646102e207508080c01600055441c81d0040d290309081a880c1c00c07911124007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 436271079 1250 436269829 436269833
    0x606030403170903041e1a030c041e03120509150d090204060e150312030126030d0b04110408100207061d0a050d0509010507030c031119020f0906011b050a 68
    0x1206250080f24148081c40c2d40d54184401c0d00d12488542101806180e40c090f010051652810081d00c1410032100846549450310146008103000300d4024516550f2051404420454161000800c9038803445918443c08000c42c0265514040d0001c607d070040c0c98198004003040600b0020515480c0307040e80001d0080203900442c04070b6003990000034282c07144c1c00c18021030080c1004d030580105000c1340207001040d918107070302036540011710501800d004000c000c000c1802c0074044035201101400d08480c2c845500d20700e0f00000e0b00840c5000e9025070320304182c0c102407580240480e07060380c100c0703030040011440404001c0004e43c803400c403e540050b0744006009082004280c10028844900000e001404580c2001401c10704002090b03828020204003c08299030010140d6610540500308008030b12240d00303050355640190800c0990502a94480d40324140070021003890107402138030b103040c41c3e4403203a0a208041c58240c0340103001c140107540c40039038413240b0394400ca4450f104809640840e1815 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 436272329 1250 436271079 436271117
    0x309021c060204030221100b060f030403030b101404030209041103030f07060f1407080702010603050f03221406210a0f0f0917210106020102070215040e0606030403 72
    0x102000700c0e0300e150000fa0800c04d40c030300403616070030b00c0e418041d00203205040c807120185c3d40e8095059800b40310382c5030900743d080387d49d600082e42d900301200b51180d0b942c2e15261400500810b1510000c034800c031000345a600803184034005210300e03079144503070b0380349405d066400f0841c40e107200400031104020300b00300688141d1014005440001d0010041d00d407590950310b0041d06407042014003214040ca1b002007010340749400044c1e190001c02600b400c55168072030354001c81c00741070385c0e41000d0304510a032400b8000e940c1c000002000c0c230300e0021145924020341252005490105071181020503041414a00030f113182403001004414030300c07805000c044010301c21000c08054115149902d880d0b65120740c0c030400d4814040d1884c3c6000c40c8404014000d0a82d45404990300701058a14050b030001ca040e6903c51010802c4012407444480003140d6076a48000080c041e42c06074200b01e0051809107088105440354a00f507809407600c20084110950300d51091105603000100b0079401c01c07081b550404d080600c9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 436273579 1250 436272329 436272379
    0x22080403030908100207020d0b06030f07030b060a05098d180405030c011401060e0d02061606140c0a021b0a21030e011b0201030902 58
    0x426120345030340c0d51401c10004d08040c408a481480c0034010418600140c1d40c07140c0c0c18020b1644501c0320101901d801c004240f40401c5031802d607040380702d401004400e124124414a1140c1d038111101c049003034550702407148860301546c04400104200d206807241084c205c004c628481c1400780c40034000c00c5042045442c402002000e88a01104032000c1502c180c130624000c0d0f003032946440000c07030741490f40c176481088039845062501c90148924000c41c040d51040e42e019620b03c40e40c510880c450a203400c104c1d46039800048924003070b41c600403080362900d292a01040c100c0c1c2050702c2d00c40b040900031051000318404c0c00d008a0f44548200b0141c0c004042401c07546680b1409900c0000c0c00d8124880c00481006000e0404230800d4820f221801c074641d8002601c080d82010144102411840940800c0e0015140c0d0070030711500500e014103000c01c1402140c1090800d0080d5030f4400561030070001918840a201c2c141019000003d100c0c10165009400c04031101c0e10140000c55074604120000d14a204 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 436274829 1250 436273579 436273583
    0x1b06070c03020c0405061917010c0306080d08040602190815092205030d0f0203040201030b1e01030207391e051207080102180103320c0f2a1522080403 66
    0x9409a03080911102407103141112b4559080803c20070307007480d030441d9036106601900010425041d0001d01000100e4060b100d01d00d0515200043d40d8420382000b42c030715001203a10350392119602c210000c461908001040c0103031000c084881c004285e55a1090910350b2501046c2d42c40d2004205209a40e00c441c420203810b8002894016201c1c24a84001015034108030215032241c07969001d003c0104802640c3c2010040e42420010703941c200d580303481500c00c03081005881c01c4035500c1040001c2070000700c0c1c2068118010400d6007034401e880b0503200d000041410091109040034a0080c8614208101c10141100d04e80085542701075680060b60b003640d02c14000a240c1c0c02c00500c07051000d582500030b59900d03041048141003110411842030a00c4040000c0d103035911148800070482c06641c1c4403c89620b914150561a914082902c000c140303000d84071716a13101c1c0981c2207518203484d280030800020032441c1d81e542c40280d8440d00d903400e1940e007003035a5400f021010388c00441e0004d10f07004001c0c40114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 436276079 1250 436274829 436274849
    0x913050610030210020d051b0c06040801061802041a0c010212090c1e0618010c1208060918060f06010207170708150c16030e04021b06070c03020c04050619 68
    0x20b08510600502d040b190050005551202c50741c44000354115041e0389084400800a80080c1e8050011524101c600039136140c202c0303000140400c4400b81034020030141c90020710503858146103000140200d02c5240b1540780c07102510007060145110281c0140400016180007504000707040781401444941951610300d15231190480c0c102e14200292005140601c82080291302c0101401241441c85000b200d1180540000042c5031140e0003204d4010000343c005000d600c1006299002400000c0d083e02c90301e101c2e440c0800024100c014440908034110810005440a6251310a90504420010f4406030540c0944003002c40c1c244060020208000c07188cc4c01024030900d44000e0310b092001d200f420040700601d020400c0415440d042c11507400c5a0800c00c400c0d5041180d0800b210003840c140445580180002001c00350346d1001d4140703c0410001c0c606590454a542c041a5401e01e000c802c000c0250704647d0301d205007032405034020f640c0207901509a04984406004007203540c142600719107160 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 436277329 1250 436276079 436276111
    0x110607090618120807031e020106050102070905060607171c0207021c030507030c11120a02040501050a1d0603101e0b0901030215130513060303020c1503040209130506 73
    0x1942c0300061046004100e04034582460402d100c500c2c05520216000d040004c00250581c10180708540e4168403680d000143c080743c210801000740a00400c5c800c10780144611500400c4121441c4903182c041c880040c001031034000c1e507a0705e91007a4001c0f20035603001448103205402000b1710941c0708032004080030000580d10300e203500c104820116a120120a05650302e1001070029402504580245402d41400402c2d44094600340184000071032580c0d402407102561044400f0001620030030441c0f0840781808180c2e2a0000e2140c0e05205201c2c2c800c4c86015800d000c2020062148003079000031010301030310388000c124550002a550032500290b454100450301000c050703050710860f141080203d445406552454000500c05500741c0420740d02944002040030710f072404105d0513401481c1c00f415004001000e10b802100404140c4807c0e4050b005201c0595098030304800c0e41d401d5488004016800c2da25503400b8440c1821006003100840400310b03035400f0114904000b681d01c500c0d1850400014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 436278579 1250 436277329 436277339
    0x301060201150807050d1b030c0b040303030c11191106120108060c030103030806060d241404090206071202071e0906050303030f0601031e02130821120711060709 71
    0x1d110550340100f14981041005004642d146003000807a2600000d1032800c0300e403030028030403803403984d640000e1030082040c070002154001d52020b402101c0c000e4404000846007034500340d49180925524030300c55005040d13105d03a40c8000460651419020380b22011a52980f8404114154000e180200ba40c4084900401c40748204000039980206401000b0342194507545d409400328102501c41d5114401c081184c806801a0345c0c04282440b80d100c4401c051060310180211580443d4050300e4080000550304814a0400e03020700b490403540038100901d448070b29115198002040a4200110300900d5400949604140032800c0c01c4220302ca84c213074142d450226131101b107406540c017240c080d420034010455840241c2ca141a480700f03082c00d0203e0020500b4501704401b001400b8014502032011400c0302d1540c03621500782e0203880d69001160030701e0980c4031071442d134011149607407107402c14104241514403880b0103065401180506104400011400803541070030021170315800050340507181000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 436279829 1250 436278579 436278611
    0x703021c02030a0c0c08090d0f0b07031409011e020f090918070f0e0a0c09091812110304030312020d0e0604150e0c0108060f060c15090303010b041214030301060201 72
    0xc4c80c40114249088034445603507503500c10b0f0045250310303403003620800010030502c41c034050081d103501d40c0002881c110345401c2c18080c0080103c0c0801014403102140000d1809005104008840d54100100e42602c40300e04143d1000c1d40c002003092940707000c1807280c1d1100351240c0c5800c901801600c00030f07003180044510311603e41007980d0f01104d02d92001c0314080110743d03201606950008201c11000c594540329510070346124899902c244155807406c05030f800b0140007110b01c2114148100500c005000c1c59603402c03100c10585490483d02608104010000640242d0703c4095000d120040541810754900c4404102d41441140e50800d4010004001c10841c01d0701ca00b0940010b118003c1196140c0070300748550301d1800c1c01401d070500c00701c000440e103141c0c0c1342d04104140040c01000306640d010409480b544801c41201c00072500410100461a0f1140c040305686c16540e41c6180103003410b01d03044c8850110200620143c40c54614184e0018074400140000c5010380a00c0e000802c4031a06444192 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 436281079 1250 436279829 436279841
    0x30109080c011a0913020d1707020a09050115050c0c0613090c030c120c0201020d09122309010e06130905180a050727090f0605090a020f090703021c02030a 68
    0x1056000355614500c075511310b07211a4120801420305c0c000c0c92100d00c04141005007844010b030014561001d00480b5480c0b1034010320400d4804e559546080c1c0c0e90705010300036500280900c401d83d6019908903d04a841040a0001d1841c0c1600f01e03044441d17403002180140d0310448400519000c41c85092240301c0c12402082840541c0d03290410800218850003000a841f41c1a80005d0a8503026451100c6100350195035098100c5082000381000520313140c20080c0703050350f0038030101303401011a400707044a0000c643e00e44001c03558128a444a03090044514111002d00c0c258001c03820b02001e0030b9584504804005010b803000c00159a0904d1814195a840982c2444a040d0703c8600607070001900856200e00315135010007091031600840c0e803a4409964440482c617a203504c1c1c1130111003405070b5807800f580d0030390141e4070401c8251103d05446072245452100a90440254140714003a030038210b00c00c40d4064200e02d001414118a0340601c01180304140148004980120a01c400e2050341d00c215 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 436282329 1250 436281079 436281101
    0x8040218070e01090e090a0b090f100b0118031113020f03070e0a0f0b0d1503080f0301060914100e0301181b0501020f190201020c0a0605030f0a0203070504030f02030705030109080c01 80
    0x14600d1031506c902425a9118070b224018801da4060010440d45d080c10000920080d0a02c801d4424426296041a00401106903000c1c00200d0280b45031800a04009024054135049108031005c08000303c00e11500034001041c8113a0a50301300002c0202ca0490310240d1300401c1031303548001104003c3d108011022030f0540040425003181d20041101f1140181100d80a0603201008200d4181c81e41103c04042c02640c0f0250200030006111004214180020340c103823038007600e45204650700c84211950b035803c000c1d20305810540389405031414038001d03001e0700c021900c0280003040e64a015010001c240c010030104484080d468118156070102c8001c134007001c0c180c01e10060169200019495580300c0103000348200180130302d64075a0559209200d8020072031005440380001130743d41da0703009141d45d2084034200a107500e0300011071190105030086038092030070756441c2414a4290f0b140c1080c02e805103141203138103129100c00082c50b41c4080c000c51241034003d408180c1c60b00c6080c542a8299021250700c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 436283579 1250 436282329 436282349
    0x170103080c10110714120408030a0305070306031518020406090b0f0616170702040606051225050912010501081f050702190302010906050108032505030a08040218070e0109 75
    0x181d000190601c40a40d62002d070000c100701002c5c030f02c3e08100c60030181c070046d425001880004000c07403445c000000070440c00d04543c0c0d003084182e503003207000c400f151221b001c0103022103230003030344400c0314050b603081000031202560a40380d07004582d50015080312625031208042307a40341d4400540901e418200d03403254580945082e0f2400c0060a4401d4000e0507a5100820314484401746448990008040d00d08503540544100318494850700094226000039801d52241e4071402c0010b05203c91141d001498010b030940c078035481d1310b000b0b0415112500203005903600540304550b500c84100007400703290300a00c4040d0180170326400c81d0000050342c04660740e000b61500c0c103000c03d04c13101c0c50780010701c041484642e46540007101021f02d8100d001d0b0580748070150210303040c540042000f0a0200081440b842c0c4a0014101050240910740305644d401c0f07000b4200350030078084460104d00030207007180d0041c4014010f000b086081801f00081a0741a1506030000e1411038031040340c0e58001c900d0401515038011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 436284829 1250 436283579 436283591
    0x60a020f0d060f081510090504030c080c0309121507050a020a0204060b070501060f0f09050c16050d0f0c03021005040512040603060e060a1401030e010e0a0b16090f03080a170103080c10 81
    0x1e110034850047c480d984080c1c0c0c1c0c60700002c080c50712418003201d41075440200590395651507031002e5074a4109401d050701c01e0742100c04c81c0713140c500001550100b0008212a82c0c6060341c3e042d00556031a048010700000b540603031a902c800507560340c8501130140440c010080c3d1076041d5810701e0b80c21aa076940040381e03c0403d80d0070070b012034036034400741200b00d03030701480040b443c0d6031201c12070500c0d8041c0000d552401e0003801181010001c1c0440d854081c202c1c140d44601c0e15528a11086603060202900903004d43c00240b1001c03900b000700d4000540c4180160100c40c1e640d4041c07030b0301c00b0840e4401ea00200c0080d41c1d65005210b5588000e00b502d400100c01c5549581040c01d01000c10600c07001c8036803260616a6821411700c030b494080d0400020214144241c0d184a4403900303041e46000802c0702d003015007009032506580e0250003400d5900648940b1004000c02c1c0342183d4079030030903a02000042040c40389003805594000313200417030180a14415204107440307020003408107107804d942089018003141460 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 436286079 1250 436284829 436284841
    0x10608011b121107081b150c0412050703020a0303050d050915060904030c02061801030b100f1b12051c1407030213080a05010506090a050405060a020f0d060f0815 71
    0x40d414100500705582c0054903078600001c003003451051200c000c040e030708045110000b05c42c0d10451044040c0200c8155000741802c4014500f40190850311010034a000340018400c4202c1d000800d08040c1c412400c881440fa00d980008003500c010341d000720000f810005000002c043ca5000d041e810008000045c82ca51820141101e114074000340424040e1820a0016085c1031240010450658000c1c0c51160340c0d1003400fa29410320036451520501090400701012a17504183c00320b40070ba801280c1d030b800840c1514032803c6074210a2501c00300d410b070268158040104d0000d4ac0e41c00d80c24001602c589607544c6071070000c0251030180300c40d030620b05440e010307030280200340d500c2415620040624005035a6110701200740c455405642000c0380c40d01ca10b544000c1040015400180100d00843d43c82ea40c90b55000e0080080c1c0d00d04541c0201642c0104000c034010040701d4018103461202d54801e0360924001e00c0036142100d01710f60000f031701c48001c86400c025550040c041e000d48150162001c041d2403802c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 436287329 1250 436286079 436286087
    0x818010e1f1b172809060212030c030408160c0806040c06021c1404080f01051b0a050901030203041118101505030105130e070b0403020a090e0a060b0301110705010608011b 75
    0x5009500c014900001c241140000c1c03c4440081a03032600c0e50038081340302c20714000700361100901824000d031040c40c03807100d0148221026a0b00c29100d101100d4a999540d949100b580c3e00070078400420318040ca5414000283c800039904043c005180003807500b03203001c1c00e103252010001e07401a415508020130031a2280ca880310660008695403c0040d0041502c041c40f0209119903444034110b8040c02d03030030160106040d00080d024022685603c401c101d0344004004241c41144185d4006c5502000301aa055029801940e4818003a0320600948410900459100b45042c0e41c0003106803107001c10400b0f020181d008007409407000700381c020030502c55200003520900c41030040a01c02c030b425400d10802c00c04640c104440d40006d5038140c0d00101d039211803104041c1c200703000c03c0307100345001000030a1044840c81103240700c8550710010b0940c00c0080e11204000c10898407800e80554aa4108000f080c2c40403000701f04092280d0000201c070b518003ca16421103129a907148000b80c14440d000c0506a44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 436288579 1250 436287329 436287353
    0x30a021e18010c02010509040c1133040606030204050f04030206090304050d1103030432221a060a0c0c150f050c030c06010303030c1b0818010e1f1b 65
    0x10a00704800e25407061300050305c044c000c00300100d81c03007030070121805102d540c030000300d09150130010110b6290a2944d8500c1c0b000740308403803069aa5a0103031901542880c25140410b4116018141c0040d44070f403607030040340a46804456010308407101d5030601c001c0560403c0220741c846031240c05181080c0c202000506c0610b1000c6003e40603102d5100c4140b00c0b90fa0901c201e41c01011030070160f0034191100c05032070701680201c50074150981c04580441185042060044007030741c8404400c40702c1013509030002d030000c1174009104000500c04c2c10725404540c4a020060800998079182c010041d4441d10744695481e18a03000070802d2000c0c011440c0100340c1018054403031b40c00905049803115a4040001c1c518083c06802d51070510400e00004141074145d030291201c81510b640d40001005448440b0320f00c4600d2000c014001417003082000d80265401115a40c1a42c0500d0001a010300f0040024071a8400311000f0b81c2d104090000c1e00138541d080b50000c06510700c05050030a140101e5100e40d503103805 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 436289829 1250 436288579 436288627
    0x22103010b07030e030709150b1207050703030906050c04050a0803090d080703020f121201140d021302160b180604050d03020d0e031603030509071a070201050f030a021e 74
    0x40b4401c0101030065800090f00c8002038202c130825941c0d05010005419007495a1840441110002c140e2080200483d001551403507030002054655403021902c0f5480000300794101503480d08410002030321805998014405400419200ca00780b4041042c0151182d2108410b98020004d618903502c1d2640d078034444d071307800880854440d03410341400d07800e1202840b43c41c0940d0141d4400c5d062030b4070f1010041c280d5046140d0070300b0607a030380750280c3d80c10003541111f401d54054420300707045005140c01ca903c10031500e0310700c50160502ca0b00500d604038030000303d0000c40e0301c41d0115081003004030380100440daa000a0740000e0443c1c1c1445d0300e415403140c2856512104140d00090b0181c0001c5168104000c41c5104504480e5140c03e2a0701a041520803a401200040c2c02c2001040300c00310009a03c1045c1e4400b40301c850241941d0644001c06a40208000c0b41840b10130f0024501c0f4440c080c014501ca140701c41c0000d40e5410100c4914081401d0740402021004800c0c00000c018982240b00380765500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 436291079 1250 436289829 436289849
    0x10207050c130209181f06020a24060609081005010302060d0f0207081c0e0601080304090203040c33021501030b04020a150201060807050f150a1214060102210301 71
    0x200b442080029110300940b40780c00099482c1c28102e808024003146210ba2801d0b0b00c0310301140c40c500307120301d0000340740d02c21000141e10481c07000001c038800c01076411003030780d1001326580c110a44034000340070758045030b0084011440b00c000403c480c3d00c05101c130301c0081d030310703030704100032940c119800101d00f40102c40c6a102050707039800e407a0003e1000c0b50b0454071000d4000c9249500c81ca500081001e180c3c4050302d18441d0681802181c40310310f4070014a1034165200d00d00590300309420224a0790094100500c1510b00e100ba1a0000420414140c007881d001d00110b0b1040c0310225000350a0310140c1c0b8080c80b82000c43d4440c000a01c11000808201e906696000d500c621040c0c0319400092640140c1e40c1210030008a9070f40c441504540540c07003002115095000d03102d005a891040009000c01c0e00459a006207001070b00d0f21640080c40d008240d03600f182c1c10039107141ca04420070300381180c0b8000e182c00382114000c1d050107025030f0108400701c840441c0401c000125120144c03140703100d01061080740303400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 436292329 1250 436291079 436291099
    0xa0c1a0f0d06050a09020715060320130e2a0f04090f12030f0b04021602041808040305150105040b0a0306020f040b030a050a0c1103180105040e0412080702010207050c 73
    0xd141e0701e400c08001007030010b0401c15220f8490800000030b41c0206811981c804240b0040034254045000c0c0740101e1340c00c4040d21800c003145078201005200e45103a03165200348210000c400e24101d5100e0078540d02203000c02006800e034445412000780c44818400e44410b0651012090306039149001c6441c201c80595012907680c0b0180340c00101d40050560080c0741c100a40c3c8200051549a40b1110804055800600404602382d00380710491050707e034641c907140c0340e1040d81e0000d800d05170481103959100111104000e91541c64502258000c0d4004480355080502214020b07008008039078050300c8111010003607840c0010010b8400300b010720005101c0d41d00071401440c41c101101c2918000c0c1529141a5031380c1c680307503030100d00a000440782c600d8140c0c54444803180051180000c403d28604440065240000e00303c0c0048400841044090400c4010040490009030b51107105010b10b110381c075000c40c0340000303c20151040800602000441e0310502800f00890f03000200f041b0380300800d44921080c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 436293579 1250 436292329 436292347
    0x60906040306020315030d0e09011205070b03011e0e06090415060b040b19020c0108010e060409121e141213020303121006030b0901090f0b030f0a0c1a0f 67
    0x50380215800a840c95201000304041601c440103002281d650803401d03a0f56407008000f05543c40c00d510380185420901c0e040050200128004284841038094402c0300e48142c0e07a181d00c10130079031090700210039440642000181c02e0b424105164040c00041000e103440d80f80500100c0e505400c01000600315180040c066100800740c0c1d84a20050310040c800d5540e5603485200c0788036240c0c006055203150018400514501c540b0100d5104080c002c165102c402c1c2c0e03480d040031321166250150640394419a1040070400150300c03805904040c0000740c683c252442400d4083c004800380c0300c5c4401040c040a00c10302e90011a141084680b5062400c0741c86a541d00e0f020214440c8407440300000350184000a82c1c40003040d905c54285128a40b40c1205010304d641b614012003c1d1020340460981241ca060014480300c1c0403074000c01141d8902c0400000d00d20a14000030b85410002d050200700d580008485809001e480a07154020b0200c0c40ca070404804060446020306102d60360741d40f540c80308041862a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 436294829 1250 436293579 436293589
    0x8090103060906140111030301240905030d09090b01020a0b1303020c030601060206090f0d05040501110c180105030c01050304080a0f0207031202030409050703090c05041e09080a0813050a020609 85
    0x10b0301d064041004169101c100302e6540d01440600c0303501144030141d03e0784209100104881c10384007408032022020740a03e806880d07008001c4404800d1101503140441c142d10100300701c0c00c40c0e031102e99a80a00518001804048614450381c150440d0010004803010030080c0b411940c00c111840b2220f210700b035203810101d0800500d040301c168180140400050600e070300145050003041240141c40308660010400c580e5001104065004620b042c0001c018640c0500c0218001400900c20381d0303035907610400082c000d40500490704469020040040c0100c1c1000c00c03040403507540a00b0040e04c2d5003401e807510240c50040c007904030b04208480f0040c000d254800d10000001310744c083e03406246454030803030181d101d810501a44401900d0080000c0f8002d200e40910501c0c0c64015283c2c2420900b04020b00c405044100c080b40421541124441c904441d94405c1644290040071807644641c80c0b0140100810005010300e180042c104078290045100801c054a513642c3c100c600300d5603540e0507404a1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 436296079 1250 436294829 436294841
    0xc070e0a0f180203010e0703030e041a030f011a0102010903082205030307050307020c01080609070f050903030c151b0d020a1e030905070503010501081b0612041a090a02060708090103 80
    0x101416040040c1e01c101d002d1818140a98140708800a00c003141d20031005541d6107600d4840500003840c1c40180c0c0e10700e410240e1007280c40110403100c1d0103100300f68102081c035008144e1212945695140403d4025110f0760020952a00d8244001c0c0100106a00e000300f2107440a00120010315500c070801d1980c0602070701d1030380e2955021042da512840c25007030103031058104581c404050b0181414541c515803050306554851071008114560035220a00c0c01c075100540a030740300d424023000300320320102c6607010400341c010914844020510740b044d15210710700c1c42c3c00244c803111081c500c41900144d001d41d480d05541c6032070000700c4016100c034903111086510040d0f120084200e06655812084441d605820801d0200d00942c204c0e02c000d90360b90141402c0703600901c80c3c100260407035840881600303514215021400802000d0604010303130140d04030004042034500311074aa009120003611100c00d01c040c160b00c1411100030300b402c1c1c40190089040d42c8103c0703500501c0303c1c0d40061040c1c6580e00a074046 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 436297329 1250 436296079 436296101
    0xe060909010b07110402270a080609010c1106060a060f0504030219031e0305030604090302101401081002040303050a0503071b0506060102010b03010510120c090c080712020c070e0a 79
    0x48034550751032548a050394481481584c44000c03500000a090519008858202d2003070300140b13203a103200501404140b044107c00c140d001e03544a10004102070104105402490607000019071b162180d100500071f0058400e039000150000020031156030340f0310009008890281c1041c01503112121720880311031007145c000035400f50450301d804031210301264444043c1c9116045030042c1c078140c204c08900d0030100e880c3c0180041e00410015600d402e003500400521442401200c41903405000544142c5c1c00b0422141d552544110041241030420032001c11140a619030840c585411900c00800a1041a03c4801804000004541024860b000204450080a038070444108a51030095125103003501e0700c600660030f26900300410f140601c2014029000c20001405d0b03149400f036002038802c0b00b0351065070340c1c0180b280300280342d850b14003900110107001c1d80c42100301d03d01888050202090507290014191040c0001000d01c0d5000400d5000d0301e9150521241c01e95616201d400606920704031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 436298579 1250 436297329 436297339
    0x1d0c040e100e01082109060403050318030c0919050601091206050109050606090d0210111c090902120a0b04180c090f02160b06030a0b071215050109060e0609 69
    0x1000804079180034000c00341d603000c2036255207990340d980603035560303c03641640040100d514000c9408410003e60007001c01c40710191669003043d507a81c4a140c02d540002c00d01100b5a0159005000f00e40707414040c103c010368086581c1249420301c000e08040001034402c0c1c1e031000613500c070041901340e8045c03803104005044025000f9840065850000f01820080c8107840c41c850819001c604203203400400d8408000016154070b000404039000c01a000326500302c0c4d0428060108609819450184114080b509416682c55003400310715400800145640d40300341c2845205110385021801181800e80c0c0100e25180041440d80c03001c0c00080041c0900304ca1410300c0303d0030240c40c1c1c080204214049003140e01d140d1082014401d44000b90069105040202482d002d030000440001001007c0b0780d07070065070142c12203078050380d41d9441845d9a02c041e00c0500110300c20050700e40c0018a1400380d14a480f2504a02a000c140740c5800a050b070030300d602400080c040601541c140b07545030541074510001000f44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 436299829 1250 436298579 436298581
    0x50a0620030a0912140d020711120a03080606090d2a1d0105030a050c0d080f1201090e010c0801060e12060c0304021318020405061908010b01030f061d0c040e 69
    0x140c0d100144241c800445030004209005007210f40074405e44491417942c8421140761842c4c00480d00e000703501c4250121200c0c425805021003648070401520f54864012005000a10304c5060160001c98000c10061003003904100041090b15000b03618121140c1c0540c04440c10102081e8000c0518080315030a01500da02010026844080c140b02445244208070103501c00c0c1d0f202d9051584036003000c1c402400759407210f0b042e01c17250b0400007008240071340100f005c0350a00d00d15002040d1942c0c8003803640040c460a08006202d910001e2003490300c441050f6000304010300c0318490140c020303001481034500340320f1003011201140d120b03503c01c4484c03582c030130055a019143c0301410b070703031690401d41c0d040e8010700a1546580c0d114005115003032544c08099000048001181d08000103081c0091100340c20441c26000707988242c2c40078049201130f201d040d001060300300080c0b000508480424824245603400e100e020841c04003039020000f020030710411016255611800f01255510a45c2c1c03005140c508404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 436301079 1250 436299829 436299841
    0x50d1e05040c1a090303070b06060d06060806010305130515061c05061006170c0304020d0f050120090105030c0705010b090403050a090b09031e0709020d0f0b040504050a062003 77
    0xc400c030b10589050b510029805052503582c0310050156002094050b40108080d0003c03488082c1700691000005003920300d002642c202c5007003601d01552109012880001c1400303010368040c05000e030301c1402d8a81b1008020200e482c2c80340e0b01c0c0b402c0707940c20b513410382544049181ca03291944c002035120400605101041c0d0300e0300c2e14542c0e405044400c0c65481c1c600e4900030407240d22500d040c04e40c14540c3c8600ca4501d494107403a01c00a944007070003c0741d1045c3e00c7d000c0040058901500740c2ca035203005000014109151450f50340c4010182c80d0360350500d072010012020350f6070300b10b003e40f50040d90354030005844250919040e0300405101546c2507024010b501004200351307000c80101804001c95444050b01d65460328003002a0080b59401d80c0e051b00001203e485a81c071210104210b00040380889a00c0d40c1d5900300e0702c0c2264000380b080006203858034003c00010041d0701444802040c03c1d5070800c201d14280c0c5816031104a000b0004054640307075280c181e002c000a41a03c010000c035003040702d903070b81042 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 436302329 1250 436301079 436301093
    0xf0207090603080706060501080603060406150e0405160506090102190627170a090b0c010f1b030e030301030c060c06020702150a020c0a0f270609020913020307050d1e0504 75
    0x4038105e8010741046004034182d403240c09410302500d8041c00800c0c040e1200e94a2601820441c40403010220301158001500190654032a00031805000a802c0c41072400f1114411982d0581040340070b071004003c10401664009940301e4140b0403004105083c001e40d281c4030000e4500031541c0340f100d0103060010401086e01e41340f030f012041d110350144100800c01d0b18201c081401044420400b00d50801c0c001c00c84509008020130f40500c03810b0000820145030b03000031040300d102d0303c01c2e42182c19100120314605501441500d211010300001503041d50314658405c1c0000e00d01e40544020066400b100034100042601554206507000b0000c40c000710400d0000e4640e50041042140144105900501c0c40c2c1403010303070701095a4803900342c61004dd0070300884401d060142c0080d03024019044008400c840030700d11800002e440e410202580ea00325520410584c2a01c0d40d0030b500a4602c100144041d1a80060880c0d241c4603450101291550700c071450034080020a0030310914550610081000300981 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 436303579 1250 436302329 436302337
    0x20d050d0e0d030212010909050a060b0d0c0906141e0d05031201030503070c090207120f02031209061807060504090c03061e030506070e091302040e031605011802100f020709060308 79
    0x6117400302d80c83c1e0380c0e504c0f0070078280c56492070054123039000f040040021139030036084075150940282c180e045451280e0395014000700e45e60310601c901c1d41da544041c001d00c00803000c120341141040344e12110403400c004080d20703180f02c0b26202c14401c00207600d9410030000207105a4030318800c0003564000941c0d49082032902c90b44030007002c54210004a4001c55641d103c2e200b52180640c10400c106940005c4417010b1340c60381c6201d10b0140a40c0f10610110314070061200c8040d1091611030003820080c203140040500340a00f00482c05429000170005202e4903500c03100307450840d00c402c030000c0382e48501c811003076000f0000307600005400046812503207981c842500441048a108204591481e80c99100403903003654030003001c0c2e520042202c08203034080060035080c0e40b810b00090001a903402021101490742d1f018080c044101c02000c0110b406000d000e1281d5541c0c844c4a48200180d440c00f580003e020708410220701050010314404000708510800c5841d020b001140d1041084940700d0070100490b0300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 436304829 1250 436303579 436303597
    0xc0f041e08030c0c240703030b061b1b030c090c0d02071e02010909060b0a110708030a0807020c01020114011215050a0b030601050607031e02010b09070e1f020d050d0e0d0302 76
    0x2010a510f10459545c10030581a401208840e90505803a560114090204815002d80c080c00602046410055486039060f00d042d01800803c1c140c18006c5202c03202c0714075142518800e8014892901c00740e203036590100d60090540d80c0e510341c0c903800d2961050090184440142501c1e104aa440291256a4a6900741305000740c0f01c131840319a8804515082e10094050b44906030014420b4107180b0b400345c802d5884071380c10b02c42a64034003620b803000e0b80d00c4c5400c5114400009100902401040d9405010700c0000101c28030080c41003140300c00c1e00c009168410321130004190b42e40344049007403003107c41c008850600103c0d400d1200341802c036201005441150000c61190040e81d00010700ba19110301100c040a501d070f01c2d000400216940c1c514903820042100b4410365403500180c1d10595107040d2906d12070703101629042c01c0300110b00117124804070000c1c03404618503031541003205081c1d00019440d840c0c2c0054a0003030b80d90060080a0409428bd05c100000d80e40b103030190f0803407555003607000307800005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 436306079 1250 436304829 436304839
    0x2a0506061203180301090b070215100b0f0706180311010c0e09013003120e0309030a1202070b03010807031a1b0a0e1809060c0f041e08030c0c 62
    0x1446940400c8401500040003540d030b80c1c010444119610f142141201c0c2c50f02c0010000200900a134446001c20b107021558071005800c015000c000054081d030007103811042c01d00003540104e007411341d00740c030078030076003510017a540400300c0c00d44200041030f040802400c1c01c00222480302d000d50f1602806103074079000807a455501b010007000042d03104458400303100000a04105041c2d01c1c080f5080d0700701000343e00300001d03459030070002001c101001203e04541482941e030000c181501062032021501e07520b0305441c8036001009080003507540000d42036245030700080040f00c0704000c0a01070740341c20999071101c028024007200000303a07804003083d404103c82c007070380303541c5000031060404190103d02141c03c640c2103494000540d0f6408070718400361200d4151801d2452400005c100090740f680305400103002d820225004000c0296020320a10b42c010f400d044810b4148460812011b43c180290700504002240d80301d03072842203117100c01030307080180840c0003565a034a0041804944401c00010070600030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 436307329 1250 436306079 436306081
    0x6060408010c17070f0c0f1a0f070e060403051b0604090603050f0709050106120c020118050c03010b01020c010c0204050903041e090b0901030c0611100e070315060803070f032a0506 79
    0x5130003a200041c1e00d517411794a599110f10706640700354000c00000000d403120141020725444040d603002e09180141d1598000c81e8040c40c01e044000c01e40d1410880c041e003e0346041c401000014000500c60b18031040038040903010b10025004503283d4029075000b22007031400c040d00081070000110705280c143d01c00c40b041e5120252a088100140c41c000e118000011380c0030484001d001c0100d0b4007075501d41d0003038400032031a10500f039a02e2210358481e403c140c9003a0400f1500411502c0d091048d2916010217002a0240c81800800644a1000084080e0060340c40b4800107040c07038401e03c12079024040900d0f100c80d4100c2c100500d401684e0103401450121031900481c036510b40f4244d44042e040340e621084058081c0e040031400c451015000d01c04030400c5c440c03000390894120040c00b40d18244140d407001001828a035003020110200c03008102040e89190450034050002c02104460b007554101c003514800818030b15046880e5200c3e0985401c282c04501150103c01c0306810582e00c1550140c4203c0d809 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 436308579 1250 436307329 436307341
    0x807120b1302180d2102100606050901081b180d0b010303090302120304050319110d05011b030204080c09060310110301030309050306070c14120c0721050d03020306060408010c17 78
    0x5100016401030072000f540d245080c1002c02d403184228901744148166005007441c00d41180c01e50301141c1200d030201790041440040d65a020075100d902c400f01300086094111519010b0140d4410b04030030f4103000c101c10400841641b140c984c0c4d0a039042e401403580c0d0345980d503810010f00c51019404200e02c01e004820203501e0203071000007501d0071789070000c0150021080e070070340c2400c0741905120129441079100741c0c00305d0f06556150900c0a8907000b40000305412074090400d071301030000401401c040c148140020b000c501c8001480060054081d10382c04915124a40024908a07005452131001400e19100801c000d241d1009141201d1007910b5040140d9150010103844000841d003800001d8000044400421240402c20281c00007a01c10342d00c07185143c54490055a100c0003030080c1ca9400000108004940010301110141c080307280084501d00135070724a03446454080101d810150007001058003507588004580041a01c0790080080f9600c1410203002040b01406080304c82e081a00092a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 436309829 1250 436308579 436308589
    0x3040e10060f021504150905060f0112050a080d02040e0c0903060a05071704170c070f080f0307151b0e0a050411090904110a0e041407060807120b130218 67
    0x310b861030540140892250540d29440590f40c001d009032100360090500b42440440d0f840b4034031000d80104050110751410881d4a6100081a071040f915a06061488000b00f940803c01280195010f041180e844c0c58030181d041c00fa01407a0009441401004148041ca03184140100b42c0c1d60000d9040c0c03902d6540354a81e61040300e004036803075004100c1c2c82207182c02c50440880da45500c1481060941c81c181907901d001881d942100212080c10740c031a2605021403c0ba520000004050700402080b09901c000b20f80d1f42c0f00c1c040d07400c0040251400b1103090780c2c1c0610a401514400c4442c202c0030340c0d09808800010302a40c0c0752050301c0c1c06540300705008110740c10540289030300800c83e4081c0034070f8059010288540c03800000d0060b074400d0810741c0034050341d81d201041e1000074100b0081542c0c1070701300b074107029404c14201c0103103c103654000ea100700141d680000341103070310010a04018807083c2201e15030401401d124801c4540c421915007205500b4002a4040c042c40a540c003103141d01c0001220a0003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 436311079 1250 436309829 436309847
    0x17040812031012050f07170709050105030c0118032103150614090d080c0f0f0307020a090e0c18010f0603140a0c110111030a2301051c0503040e1006 65
    0x1000c8201c1010090043d50318403103000d40781c28840d004031007103950f100031300c9802c041060700102402c0e0380f42e200d9560303080c1040007044d0241034451020001540360400081d50f41000d80c00c000d043c4600e2202c0315141ca045440514011074104034020076142c034503402d0703020505484c03a9640100b4a4800c0002003003c900c0b02d0300069800079290443c1e800d031700e6104009103801100d0309950146402103100001042a400303000358412010080201c08074100350340d4140150500803a00d6a80103110150140e5100d402c4041140c682080004210f102c26111a0502001c00103040d041241042c80a020781554480d842c102c80145014102990b01d0f048110700f0b552468840c80d40186408000c142c41a416501ca0f0380714203080e04008103140140201c490940e0b9904000d05681c00000c0300b04100783c002030189640201c2004454003c1042c200301c03204000c4818011a03020314480321407a0340c0c091b520000103d2140d000b5045070784603a610445862942c2c8200e030403815000e440d5500280240c01b0722012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 436312329 1250 436311079 436311091
    0x308130c0512030f04080a020901081218060904020a0f090b070503042d030804060305060109030807031116030c03021002031e280314180307060f091704081203 70
    0x180324100d1030442000030820310080d150480e80001c101c0d00e211540c02c400100028070650001d02a10b061500412080d01016800208290011300c0107002100107541103909843e4085908000190040c001c0748090280282240d04075100040110300140c04ca5101c0c11240c10541d00c0e51621615282030704228000c0000090550344148401e100300c1d203030a4503104400c441c0440c8040304c0c103034110502400203501c0e8810f0f05c56440000d000e0000b01c1c1d050003501d074800c0081c2000c44040e49960307149011403042b480041c04100c041c030041c480d401d03c240800000d1007881c06222031000d03160308015031010f14912080b0302c20300302c814651035818004001e440d060000b20300c1c2804185205c01d0404032640c07080310120072441a0b20b10361513041e415600440c0c0f00c1e880b15a4006900112075941012004002d0544c2c0740180440c00e144030961000011240020343c000700104584e10803620100141c0822140103041ea001c84c400c0003955050b5801038001c03940c0300412205101c0030780c0c904080e141300c10307101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 436313579 1250 436312329 436312343
    0x60f010c021215010e0a0c1e0819050a06090605031501060f090e04030e01080601020c22291f0804030e12070f08010b0307080c010e06120403020604030813 68
    0x204401516011800c1010341c90500150f520418042180d0308401a0036040040f03840005014040c6040c501e11904001a0782410410001c0c6c030489000000c2d450b81c60340d813808100030300c40000e2050b40451131002e12810b00344c10601460a00c9502d000c0580024020060704c5032515400240b58a000111000b19211450f904202642000b904480f980e0400480d6000e21440c000300113098144036003681e100300d00980d10000381d240301400044c0aa0805060f5604542c8004084002940e981d071444040c0c00014400141821600c410000500300d0707034180780055500d04410300440c1020100f41500150100c0d5034044040311844a900c604d0f180114030030008000b4000107000030300a41d104078120000814401031020074800c42072600d1043c0c2c21420b0300091596040004082c02d008419021200300d0261100900b06403002d6a2048212038645c100190420080959180d100840d6540a82c0c1c48100082d4506410083d60302c140035141140004c034003000040340c2544000c0e91600e141d6200c030b0303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 436314829 1250 436313579 436313597
    0x1801050a050402130e070201090623161404030506010812270414090109020109060f0e0d0c03080310030c0e160309080d180b07080702100f090606031505060f01 70
    0x70a10009400400800c0c825100d2008007159164654250504c58441d990000c00c1010081c90484103942c0c1c0c21107024480550140031591480301110580e0780b103040380c0460103d070007001100b140c1160104036003100440e070005d4040103007c00030030345506a03017864040b1100750900600100c0030748616880d00403214410710383c1010002240c0001c1560380001000414400580c40f48c039040d4000075150400d05a664120050441d60040d2040008103000c2c103001515400c0c6840107811542411801440b60100380d07209000c12442d2035024014640002490740c5030314180c44031610040701d501040da0405a51240014a080e8284145101d20f224040401c0d403d503004c942600074003e502021078103e4414004103079150550701c1099031801c84191038410899190400608540b0041d000c2002c00020f8020807841c03d4000500340b01e01d10240d8070004002d00502c0c4210010207021400400b020304003c000030508c05540d1544864800c1c410b001c01443d00c038071041043c0032102042103804507100c0390b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 436316079 1250 436314829 436314839
    0x50a03150908040902030c130b090307091808030c0a030f0603020105070308070c02060a030b01080a051b0f0d050f04061505100e0d060507031e0603111324051801050a 73
    0xa00070706406803103060302d6030a1070f440345100c005036001120300138840d51010034411038211580d1402002000108501e901d84808c5e20b0100b40c07600e42d207000308088280c03a070486800d07403020441046452608503c159450781006581c0c440c440c0e20840e2860002810f20840d01103840d03040c850741d022603505844503443c081c01e5a5007580c4030500100007605100400031501301585500e80144020780d0300e55800560100d0441c00274010700409004020741920300820020071840c00c06d1506c2828042071807080d161158665100b007503201f8000300c0503420f410700041c003800040c41c400c000d018034845d42c814808001a504411201d0095200b02c2d540080f038500c5034420140500200100d01d200a0210035902c0313041d4507000180c400070348296001a5560250b04e10310810309242c1c00030328851103820b0000505d5030303c69000305003400f05141c1c031038420280d541d030b0b02840c0c03075000540d00f83d56172104103400144107402c0703880e040756441a640204032000d40103442c081c2015205059610040c08102c15034180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 436317329 1250 436316079 436316081
    0x60503060904030e0f0a0f061404080a030507022803030e0d1109070507080c070302090f1006050d06081e0d110712081201180c080c0703030c0e0d060204030c050a0315 73
    0x60140144c0007005000f1030b507070680741c10600d0006400180701d140c02d1f461502e07078020103c3c4c1030000d1749602408240401c0c03040c9500402c403000032a405140c9541c5400c030700e0001503a40d50744d8000109245089215001c3d0186c8207210f28400c0342c0c069155201040300003020f00443d000340c044000d14810070740c0300c065040e1030103400583d00910ac5207052800c1681c01e6032003a5583c0d201e107018280a82c01140308200711704e082082150310154032880d0310a941002480b00d80006428024281801000315a4100400d296030021005000c0401103414144501c0b019070302c120035110041e81940038031000c1461281c050700c6009400590840140045842d100303944211808001044500c4402085054a030f003c681140c140178164070403425160304040e9040c40200d80018074920280242c010030050910000f000b52141103415040c0414918804032003141c104000c1e070700c0309174480c109014410911205a015001392031080084038441074940003005820862844010314044151010318100301003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 436318579 1250 436317329 436317347
    0x200309090405061501140304260a0519020708030f0a0302191e030b0d15110328060f0303110a1e03080603070b271518040b0f1c0803040b070906050306090403 69
    0x384040080c0141203841d2003003c643c080d90b000000a480868100b23142005500f04030708610244c00140b0103f4a44282140c0300d00075158012144600440c002c0c03010f5001f501128091280c055104500000003880904100001500308d201d0f03102c100f005481443c000d102d00c8415180013021045080c409503505810004200005020140c03143e048800c144100c2000e0b6005400c3d516242028140710840c0241e100b11000030080c0041c141681000202d2007030304803505581d0103103481d2141ca4649070b03086290110100008048a1036240c04200d045051a00c00c02068403950350382d0000c1c0c40e4070381003558905c45401502d0071000d04220070b1841d4050038214a030519500d2000340d82076110000007400c82e41c81180000d480c1e080004400c425a000d400d2000c0c00800112000c029020b182c41c0231814004914400b036000c0e041ca400800f50440042d5030300e4042507400b010003039803854186018045410151811400708031000d9001c070301d540c0030f00b05883c401c850181c505407255a642d102100d603010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 436319829 1250 436318579 436318613
    0x1519090303090606060f0f030c09060c050102090a060f0e18070c020d05241e190b06040b04050a06020d05120402011707021f090201200309090405061501140304 70
    0x1a0302d521580c0001c085010343e80062500d40c071011800c0c09a003c02800400c1c8001d0840c0415162182d603900103500b00c00c0d00d0301629180d00c1c000080365a90315000c0d009201c1c0b19551680301d5001070340003d02c0b6a1180003040c41420b550355140c041c800100600c10150300307070076491004c03074038500001d0a51840781501c4c00500c0d000800282c0c1d030380c80503154036080096074003c03a864900c080e5503820140761a82036490300f001300501440300c06d0b103007081500400c0b88054548d02da0b070503d41c020700081d000c06801c1000c4c1c00c0c40040103240e03a00c2d9100601440c56225216050242005072000100c007800402c01511072100ba88640e4a0583c00f009a602c4010000304128144501c00c4160b020040107942c01600c030f1040b580051512450f0310a00c8691000b04030003801c0c1c528102500c040050740d1010855800d0034070140d10800c1c0c1c0c0740040b0080d0030360003150703442034005080c3d0b4104003d0100000781940180e944c02c00c8850340441005c01110745045001240c04507103401c00208000491000c01c1c8540c01c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 436321079 1250 436319829 436319831
    0x30c0d060f080c03060c030603061f09060801150807030c1a0403170304030305090c030c0d230a03030506060301030b0609041a2d090601031e12030c021519090303 71
    0x5a100d1a089401e0700c0c0d5a001440c850b448640103615a0800700700041c0c00012500d6a0350461070f0078400a036903160028205100104483d030008180e000547c0500082c12410340280035040c1c880d130526008102440c01c19140f04280c9800041d291400301e00a01926004034240060601388000c901c0c44030842006842c0040c400c000c00070100e0b45400b59030984d051101141a640c0c145420300406a48001e0080c1056401c8001108000d5500140c0124000c9003602d803040c0403503031800c2c0b105a11021500c4002030503d004480c00c441c41e40400c0300c11060303100b91001c1101c1d499200c00d1103c14042400001d101d9400440820014501201c900d030b031145c030410001400040c040082d5200d0384060360034034202c100300103051101040888100503511140301c100455481c8c2044800d540780b10602c00580005600f0181c00000c00c95500030b080800c1d0842c8080c8240c0650010003002800d48124100040c002c40c0101740c0740800764000280a50380220302000c0440b00b88558030002c02d9811402c03020301d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 436322329 1250 436321079 436321091
    0x212070c15080109150e0106030c021c02030304150b090105060f1e0c21030a0b0d0c0303180602061b031009090f0b090d120506060f07060c12020a05030c0d 68
    0x80d220540c0401d00c484165075401110b540f4000d0400e0035100000e4000d40aa603480703c007070041180d0360801074119042d914000ca00c3c1d025204040e0305024203001c1400c0450340c038185503100d0940000085000c2c61041c3e0014078170010035a000011107070710500103070380075a1441c010400c518254000d800102e882818503490f00100611812541080041c20421000080b6140720100d40034400c800c03a20444100c105403428000e40c580721640b0004000203949507850a001440d40c82e10000d07044032541c41080d80c1941d94481c100540086442005040c8418680707801068082c804645d441c000d03c1090051000c1400201000000d5040203014aa805080640c0007500c04038900070300c084280950001244003825082c48103080c0300042c05100540d100c503042c080e1b013540c0701c52900b4a1220700200052691107202c0043c5c210702c2506401e00d01094041459030a214150703200d28002d840649075982001155550901079003e41c0b200080800e005100188010381320900400c9030403400302c00050b131 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 436323579 1250 436322329 436322339
    0x10315110d0b0102010617070506030411060d020306190501170a11040f08010b010207032001020a02060a0806091518090f010e06010905070306260a0c0617060904030212070c 76
    0x26604224801a030345502c49034a09a01e503028420200600011101c42c01d80d00f0902c00d82507a02e00c150b20405028120010000d02400421000c151510000500d010b9503880c160380902d001c3e4200f03072060343c424048070042c003903078030f0305400c101c0c0888106850b840600b2030040c1285040e10030090091000e0394a43d00d03e4500004840001d0019100c400000c0020030f00b00071001d401c580d4000d00c11410b540c0601c0c1c05101041900e042d18810300282507428034090700c0800100d08100a21a000f50060b43c0484d21080090308203818a2099100740c82981d01ca07522102002030780c01c0100401c94001e400429410f8090310385040040e40110010700f02c07543c450204904500312141c20100800700d030440740040c40f4140d22030042c00c3c0c01680900e81401014142500701c050f459419411103000420b02c4244250f211051192a004070f4005045290b41d80d0b80b9a0050a1142070f000901030021000001502c2d40c81d212015a0140303825078014881c0c1c0c103803030340c003880740350301001054800803d44140020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 436324829 1250 436323579 436323611
    0xb040e011506030f0605010915050405040501260109110118050a03060c140301050112020a020a0209010b0c24010608100806090106060906020316020108070e06030406020403120512010315 82
    0x504440301e814400070301407511030020220f68600d031a0707034041820100104610b07a8854400d405072a860501c141c0d80341504102a544d52041c0e034003168002d400c00b800003402c14007841c010081c0c2802c03007019004024856010500b01c0b171048000800340050601c40c00032a500c036140903048480200c020851050322140002c903290519841210065291074818010a82c002c0740c1520001440e50380030b0440d4180400600f141100075001034000764049a40e09204c2c0c400c1001d6103860b9000340045a095840c0c8841300080d9011401514451042500441301034807101c0341d0301d0155003080c0c1e084040b6400c041c411181c000c1d001d00710b0a003e031140d0b90302180880301070207407038001c281e0300000044003440e01d079024208a11a41c4000d056400c184010005410380e03071600d072100c41c2e0910304004141d88805040e2404018405c2942d002603012040104014003a8020811740e070240c0220a6031804481c1c08403414441d0923042c49292803041c0c01000055a9518413041c0707107a900c40003040700780d0201d80c042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 436326079 1250 436324829 436324841
    0x308060d15020712080103030207030620031008010c0c02060f0a03420e0a0b1302210604090c0e2715010b04081b0a0504020307020a03170601120b040e01 67
    0x1c00000d03400110b5800f00b208184014650380100e0415004c0d540c51038170040e4440c41c080c03101070206030715500045101d5000d500e4a0b5820b5800600c010f850341440e443d0007846a6150058051646c0f03000720080c1c0d03481c01008ac680350254000c2c00d5500d8413030162070305101a002554030405054403442c243c190b41034a00c2042940106103098507100c008003c075849851600d105106101e0f203080c40d800d10051390f2050704030741e02442e40c44011841a0510300402d01d28038810b100c504034a4408038080c0314003585100020548082c89140d8980c548440d0100400c48070740b40c9000701101c06440e0704002185a8800745070f48405516194010040e61103543c0e4030906820010080360380103160950712000c0325500f00303400340c800010404d0400c4d0030800c1055890070541d148010300b542092414206540303c4807584041c01c00940f0079501c0381030017840070f95511031000f0101c01084107048802c41c9000f0405600d07100f844140c0d01c0c03c8240c0100401e1100402d40910300b503070002d444c1c4480c0361201000f4000c034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 436327329 1250 436326079 436326113
    0x20406150c0506070f1b020102150a0e121312060b0405040605090d080403050d0b060c03191d0a0302061b0601060801210209010b090102031c0209040c110a0308060d 72
    0x4070441c054a00075003040700060080042c4800c1c102c161010b0f50717006079900810142d070095030407440e0490005074030300101c0c4500100400110020042da510150b000055101d01c14400c9602d000d0700b0321182c7c80307a409050720b0726800c000300480030400c2540102441d2400c030b00440c00040c50b00004400314007601c6088400380c41c0180c8031414028085410409828558081c0c6813440140c1820740d00104240b08e400229112161294507690b60355036142c04031251803480208032030741c80110304441c84140c00800100b001184231002c1003e0f40c9180d6280036502e2901c000c103590200c034295400c115003070300500540100d10042c0c0d0080d500b2401c0400a060191070036441d10f180a40c50965a84c5d00d501c00c2e81c0255030b25480c404008c50043e152440740505541d92540c0158070f030200940100d10b14016031410319540c0064000d221042d074207650040c10303941c03405d40b030038040320320920415250910980080d203010b41c0582c031a1400300c2c3c480d0b400103801c16001048405800c60640f1079110803000c0c031200d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 436328579 1250 436327329 436327337
    0x40308090a0503030a1d010909090b0403030b01080f010b0307090b220603060e0406020304050109020d0f0b0604020301060f360f1502031605150403050306030d02030313030c02040615 80
    0x502074039141010000800e4100c1c01107280c4000004000d0000901c042c0080c01d042e1103019460035607005011560113400d80c01c0041100704c50504014083d074105640c00e8010030b00c2c0040944141d4400d07240349114190400f68081c0591030541451060b520040241040014000b000f141c0c083e010b500078007a160201c0b0042041d03200084e880260500280d00c8030b0f044c10320340035041000040d1424000c2d8001c1c0c2040005803a90f99604005014085009000f91b02c625148080030030008010314014100d03004807070548080e925001400100d10081c010701012400d80e400f0102c2240c0304c0c642c65418821048848075004c2c0c0300700321a40d515031003580d40b16034819032110709000b03440c050321001004140e034210211200c003000401070b40300c1c820040403501549510310107005110042003040000c0155504075100c42c5000d0a0052850700300342c40c0030744030740101400c04451a00c000250383c0036140300300301d102006509a0702942ca26281100032a0853740320240000c0041102400b54989007190312 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 436329829 1250 436328579 436328587
    0x31704020d1212060504061811130314061f0905130204020a1706030d090308030c130605041403011407050c1c050304211205040f170912010605060a0807090902040308 73
    0x1248900f44c4849400181c0601c2c81c0c480c0c100180e00104c48944211110480c001a66510903110740c0b03c54131510f0a400c0c6146134240000080106940e4986421070105c400c0d180c0c5515118101e546654a040700341c142e03c0b40c0300e0014001e000083d800503400c01c07034040707100c0b104000540c0850f081e60400080c10011440801c901d01032818140b95071940900c084000d03011080100c0c5024042070003234000a40784201c08800251920303004404c81d01609542949415040ea40c3c00c1c0003412135001d03020b00c08141c0c241b0a0140780d00d0405000d00c901401c001202080303580c0d20100110b4203a04400814070f05031207076410702c80310000e05041c0200da420081ea5030f15a24a81410500202c00e0050794000c40e13100c110842080040e4803d42903001c1080c8290040352035122130030010900720b007240c030262040e405480c0840d0401c0d05640100540c4005a64695110b00c800e132800d406c80780c0a20449812240421485110314401e8540e258403a00343c1c00c29a0385542c0710108103040742c10a420498610b0400a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 436330935 1106 436329829 436329857
    0x816020609061605040906080a11040203060307030b06010e06070c0510050712080414010f151a07020609030708070303020303071d0d11010324030204050c07031704020d12 75
    0x420602101303440d80349070b030746541008808074ac000166290440301030030301c1e0081e64800c01005014002d00303407968864080f8804010105030420142c5500590a0380e039050143c03040754055140101024108014800111800c810300820300100340312444c005004185034010301d54443c980281e40e03803600d1030a5500c03806c0d07800fa544015400d0950322402500950b00ca0300c00303500d0b030403212424036130f80700041c91004803881424428032208029a00c05030602c0e4000b0800700c0b0014040b100d0300e5640d45001814060150001ca00680002061000785984144c505075040a44207051f5852011400042c5c848111010700400034030b14038884880c141e000354010580110f100c0c15040182ea07401c144882000700a010807440f4a10300404203d0b00424030f000c0d5200e45a040c0c0b5988080201003600b006c070020024812607004d1020561070300080c02c1d1a1010721168030503258450080c8100d = true := by decide +kernel

theorem cover : BRFrame.Cov 436151079 436330935 := by
  have h0 := BRFrame.cov_init 436151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 436151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 436151079 ≤ n) (h2 : n < 436330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
