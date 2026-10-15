-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3893
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:59:11.180852+00:00
-- url     : https://prove2.me/submissions/8b912662-848f-4e12-b7bd-da802acd1622

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 700000000 ≤ n < 700179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 700001250 1250 700000000 700000031
    0x11031927050c0109060c02010206041407170615010207060207090209010c0203011b0f05160f0c0305101a01080105030d08101703090a0e09100f1103090c2d13 69
    0x40302200c41d50400c090304001907070468450703c014465402e00c5000b42540d540001c0d05c079000140010015450043c09400c02d450802801c0c0207040588110b040082c1506961030351204111000b0051211603001e4000f207510200740c1d04100c60a42d0001d08040d030525400348065000300b03011504005490141e200542c1d001d0164040080d80300e88040e60300e10070081d00610301001c440c9107405001e03040245a18000711902c0414003950004808500101989040c220b811010b510181491007a05445a507015140c4d0010380651034402044110b8180c801c01036684403001d2103440d0785504101c8500302a00d01420200758407070303811b150a4421075201d00344085050a1070941815582c0702140303025031030820000c0030000d490b944410390355a00d01419650381e01c0025042081d1810b441703044241d441c4505400c94100e4141a07072801d0307243d10300482c20a13074540f110103125100b4014203041d8072819400c2017506a0300340d424008040460346000503c40c00b0700c1980421440140d4554400400642 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 700002500 1250 700001250 700001321
    0x5030a030515041107030905010e0312031e040b0106170708010b090a09020c011e0b0303040501110f061810050709060e0d0b04260c0c040b040e0d030c03110319 70
    0x100804c0d19601e40c1c6031800c00502010710f98104c6414403175000c0c6545e9495030b0004d95104100084000300d80d0340e698400005004410849407152030140700000d00041050412100741130361066030b076100d44041c600b6560400c110050700e450000c14800401480005911402041064405400d0007210359880f03210208981c0540300400c0d2036551403541c40074010140303403141400c180402c000e002803045180080e0300d0b03103e10b1081a05200108001c286440030510920032000c07101010707184945864628181d287c00081d0120742580910501c0000d01c0901e41b0446000e1606991070b442400d0902000382c84c402c40d07800142d5480740100103080300040414500602c036a1080d52128650700c0f50a505160110314960b1340908000c007440f06500f8100c000402041901007140c001c030780c00c00c051000c14010040c03014507040e60b02510000d4508150103400500c80e21000d5070b0104424104a04456803501040d2141303004222820706002004042e41c02c001d40285202d05010703800042c0c01c480300e11052 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 700003750 1250 700002500 700002521
    0x70c171f0b01171602010f090b0703230a0b0418030c02090901020f13080f0a0b040303020f0d0912020709150504270317060d08070f110d0b0402040b060705030a03051504 74
    0x1250a034584d0340903038280515481d081c0841c2040c007a5804950310161003040080596003010f90350340c01c0340c0c04004c002d600c240799054024142961402e200b0f0305040540381c001415409141000025401c440711504200345640e0541d0b00d810044181d40c0c2007101105020341091013541d001d002003a000740c0e2280003042d0a075203403032519181c145000441e606051100251004c140c00c0007d050002c0346c407c2d5017103a4805e50520380182c0d82e5503040c1c98035001d4041c0e0f0310b078440c005e49030009007420402d103403500352030b4410b0a0302180c80055589500c0e8007518002582c01000308411001000704c0d0030306800a05c04034400d8060299030840d85a030908420341440d90980025000a14121070544042081231300840240c03401e00e807d483d0b03038650400601c5039900082643e441c41e41c0389402e02002c0c0041d00c807204001800d0000b15561428160845602541e060340314600e0b00c001501e00307281050880d101035602001450505041410681c0100700c000c04849100351110389400366590b1302c0c0306000461 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 700005000 1250 700003750 700003771
    0x171020040f031704081005090a080f091305150d08070203120703031a010c08090f030607260708060d1103120301030b06090408190c0602070c171f0b0117 67
    0x107203103041c10052022410240303a00303e07000704010700888030041000d41110021480210300b507100c0c200490303d408400c40025101903004118007900c080384a0007000000c4040720400429060039120b13500301e800c280d483c8080640400d0140d84241018040c0b4044180900050340c14000d19030086410060f030740c0b000385081d00d00003840e50105038151144134503101084a940c000345d980200003030116510144c0140181d000840d1400c5150340f22517400a83c40300c040c0c01d83c1c1c1c00d42003000010b4070742e80000500d806486c138104d40284042c00784079103c80c0b15083d10360715001141c58020500c1940e100004090f107948507250369a000c00d4a00308032105100c0345000c03440d90b5a6144d42400361303004c1d0b0090407151180085100340320114220200780d13000c40c845103041c40c6038050000000d0340c0041011800510042c000301d020014040c00c2c038414401c5420002c407000510184411031500c54a85010400c01210707101d17540c2443c4035242d03100ba85020810306101c80100c00382c3c0b1036000716400490306006003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 700006250 1250 700005000 700005029
    0x1d0f011704050601051009030507141f030b13091502030606040314060f0a0b0112021b0105011d010e2401110f0c100e03070b03060a0b07060507030617102004 69
    0x50500300710381103440b4142d1070015011f50039035862503150700a40c41211001c1c5003a2030242c1096403004180d900c54103070041d030b42008880b4140094003410840c422a031042c4444171519002880d00d02510071240c4c0d2103820519603031140e42c03c5d94000d42014081e19000001404040001020b28001034010380d64040203000c0c624000e0300448000500600360180700d8100841454140d0f0400003889c1c0071441054056212610b000b0040b9204603000960140d0798241400050039408020b500d80b800e0245607800c960b284e8a40320306001885050700c91251030b0700e5440001602c80d250210342e07080c0560500d0104070030b00410481c90301e8004042e1540c002600b04a240081602e00700d5040c010314160760a203452400c07815000681c50741444e1203140210030000002030f402d81e8541001c140a00301c101d4816888100600f07006005003001c490f50408689094404603000c0312110580072029102c500900c00c210305c481040015203101d89003509016103510346140c0200d01040500013508208800780304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 700007500 1250 700006250 700006259
    0x70303050904061a0313080c0d0c0212030903060106030e0a021324120312200409060b0717070303381c1410020d020301151d0f011704050601 62
    0x101c3d03032035900036001007058220744c0c81a01485015258045210465000a201c0c181407001c200e1081c0e006c1121280200b10f000c0e04500c1d0044e0071490000d0090b2008201c103001d03601107503980d10400304000e40c158070540040002900c07036041782400c1d00e001e400352a814429030307021400807402e030168004956166803c2e40b8007581280560702c0301000c56960103c0192620544500d01e18580344040e0400c102c0404c0f07081c0c0809541c2220b0011480015801c5c41c1c807200e20714811241d00039004100d515418600000b0348400e00b4401c0c0e50100c0d41000e2903100d802000404502e840d4091a0118181038a4000103030440d8901200320b46c09801d624810007030001500e403003400c0220014200c5103d2060206840343c000007980780b200010760710803072402b00c40c5215901549419a01a004017095000003511298a141c0360042c60403110801d040d00700e1a80c071000260381900006c1240050a03103140c00c501c078586400003080310310110604000c074070340d001d5001e507030320303001c02280c0a490b1540203000410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 700008750 1250 700007500 700007509
    0x8010c050306180103022b0b01090c110a02180702101b03061a0706021b03070819020607122c030c070608090a0204092d030e0103090c05130b030703030509 68
    0x5524200300300129920313606580c000350081c0d500d0702c8400c1074080b0f4a0540c065140c49600852a02c682000c0f06444035030350340e284003018010304821400090b4908880e10318582c80045d480030440e41c000c0c21648160b008900d90410018002c003035404512804c1c08541c0f8103076042c400c5048103000c40d05050400f02038200064103643d100e9000c1072000e109142020164a0781509455003590b00c0103016946070100d0301060004110748641c0c0400e0f00000485008001030302c1d005050400d910349070b10946014541040e43c64850494101000c9a400b0301c0011413000182e0102400b48000c1618030484404010140007200d444103003403905600018501aa81c2c2080214400500a5180c00e04031460070501c100d40341c880e8580000d0080d511a903000041004800d00c0011604585041ea451100c50010580c003200101d00c0650210303c51a0281c46154031a0013168902d541116408160703500d02005c0c4a1607000300e100050034030b030750351500d0391099a00b4002140154001e41ea01d5450316071450412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 700010000 1250 700008750 700008769
    0x901120809042c060c04061e0e100908100b090a090c0b0706060305010b030a082d0c0a030e030c0d031d0301050f150406051c020a0b03010617090c010804020909010608010c050306 78
    0x804501046c0420410300303034481e00300b042d0a4002e16240544c0403030003106540107101c1910540c1e001c800d0b034032a812090784c4030180340211503172081107404041d814800d20701260b40100380d581d040725a000000340860760b1500701707840c1e007485108207c10b07035903951081940d80c0c1c0009104503002d40c4c03208010010b010b000d000c1c1440035503088000e02688400d51b03803401000e106214240c01c4080034186150a041c002c4800d00d24140c541801c900c2d0740740c10840f0401e0f00d8001c603403c02c60110781c0e52241415941000034068003c1c510240c82c00755505119201a200300054040c00c00c011201b000740c00b940707924203000701400f4440111a42c5494180355541c80e85a4100509680c065032414104104990b26030310041d6910014003840403050104d400869803166442d00002c02c0c055000000041d40d0380d202e0094001d02507006056007180c2c0380c445103683c90341c81c00412039000520b40ca000c90058903081001c5c0750494050400012680c0d0f03034030f07120b42c2900d01c42d0900c1804a400441040100d09052010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 700011250 1250 700010000 700010011
    0xd030e0c09010f05012d0507060e0d0516060e100c080702031306030203070201020c0d050c070e060a060305180106090b0a060206091b180906150901120809042c06 71
    0x144441e560400645800140072441107904200c2540ca828040508901d1064002104016002c03004614803402400645c8290070480d43c00e0f10f0000d0029648101003241d00d1503182e1a91640e24204621910301c200440f046016a0702c20b070f9826915003140800c22418004003107400c00400c115040b04006002c500d00104144259042042260b22000e400f40c64441996198140140c42b510760b550120300a018880c5848005e104858803a500d260300f19003d080241c901d842110712594441643c04403d10042d01c3c86c40e000588440d05102c40b60003038101a50000c81070310018091b00413900c00d071b420760b80d072580000503455540114002604005010030044c00e642e00050103141006420b0316a214140591002030740c003400e40079661340e51007004100c1e42912401c0c0d087d0341c9003050520192940015a580007a003100c20055540c0c500341182518101c8203040c0c8038891205840e20386100c127501c00c102c1580c0c0b003982c41e04400aa0100b0048541111103051500a81da25a0072092850a6009440c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 700012500 1250 700011250 700011259
    0x213090e01050c0a050712170403021005011e030f080f03040b061003050601080f0c13270b03030a050918040b0f070908070b070609050f0307030215010f0e180d030e0c 73
    0x7051320034a421604031481e00341e0100c1c41c0d425000c00c02900300d8040300022a00c80c00602c0c2c083c00e1205040e40007a4214141d40c998404104903680c51505c80045002e04048054400100030100b01088100d0707448181640926211850040e64001c0d040159004440481d0111050740c00e001513801d003100042080390303040c02c08003d103040010000e0082000200211002e48454000403100f01d000d4069400190942294583e020348844009202003d20315412044080300014407145075014010004a00c2010740618542036408008079207580c80320403101d8200c03240d481c08500c042e0343c1440b484e206a0007050307061b685080003001d40d00b400c00050555010400e58100a10030342070045803601c00c440803090344941d50078803854003801401c0080e0300a0071500448145960758a03001c00144040c40c8039900381c9030f406c40820342c200400c501c00c3c000d824035204075900600004240f628542d1300100da000c0c000404620711030500c0e207081c200302c21000000ba150036401501c540304001009942074100c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 700013750 1250 700012500 700012507
    0x6020d081302060d1d10090512032a130b07120305060a210816051002130512100c2109050a11061608031617040311010213090e01050c 59
    0x400150003030088110382c01d21141e990402c9a0660310054000303040808075800c5da42800b01b0200040d00810128009a625008000300001d4841c410821a4442c084801d004240207484030312100c2c50210048261940843c10840401c1e0401d00860020050048041c13003035a884251825200c1c21422001c030070245400d00d41801050799480e032074541078941a000300c0d800d141501d004d1014040074020050090707200000c0c0d6205501c0e2a801801034980034904841c1020007034410341049100303044d001c1d02c441032031031824017507031900b4881d6601a910240488042c00a811030620443c0e5102150170040368603401000303210702a003031013030030304110060080191944a80b613071912044002c81c01000703031410110032001d075610711054030390088c100c18900c411900e0b14900304074164416541c15030840c00000111310305900c01d4020344042c000040d6a04150f889980c0c0584490340c81007040b1800b55000d006501101035400140401000c0d0a000400d038040d800c0040c908440700036080441005081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 700015000 1250 700013750 700013753
    0x11b0f020c091506030f070801050105030f06010c0f080310050102010f111804020c0f103204020301020f0a030b0f060c15062d0306071d0112140106020d0813 69
    0x2003401d400c4028107480e2800942e5070b20642007001e000c08030b4941c0d445a40130040c4100e44007181420743c80f40b4120b03210340c2100d980303580040d201400204c038402d0041c0030a00004a01c0c1d445207041c0c0704890705c10070b0310b031079490896a10140341d070b0421100c1050100c03207003034100150b60742400b0300d40609019402c00c000c154200c070400861803040d00f1300541c0d8240c00300c1010000b9241c41d81265510000c080a50308503850018510740ca031060543c00d000c00d9801e103070841c0c1d0b490500d14120550501031003c0386450101180440001003401041a40d146d542030224a44060380d80004109159683d603001030308000500c01c00444088514a0724001ca0040c08080d011000004560000402d001d0000d81e260355540002040c100c414a6503500c0712810341e244400517400ca4801f523000400c00c8050321038541da010012602c552044440d51060107200350b4225203035010b4441060030600110000c6020703070304030740e901c513a110302a4803150040e8440030320304d0b014940c000801a08540900d0a05142803410b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 700016250 1250 700015000 700015003
    0xc0b0906040618090c05131e0302010813082a06070e06030a02070204060e01031110020d12090f030e102d020307150518010504050d0e0a17011b0f02 65
    0x65010b0001072280030210402c400c11084102002069a40c40a100503049140c0c01041c540108140351010ba03001140132804a01070032681024600320404584101d2841e00111904c040c041d094464414140c01c2910100c1c40d0075004202040d4019a041520300644c0e80f4500240c0c0b045422000c01d8114030140005258400e225240d1980100c0315603407030703031a501c900b00000c1c800c2035030096110707280000014050013441c1d511130499005230b01b03d91180354078600303200902e50b000000034016085420940380441c0600303012541d20510040000c0c210b88217640b400c03001d00c0200c0c410f402251005c144a03206103020040c2c880b091080d850402c009505445074021000c1d0421042e0308581c20402a043c4058420400c2d5035026400100c1110215240032450f001841c054030440c1d10b4490030003e424010005000312030240d40d01c4002400504a40bc0b81240c610300c180714083d07408020701500003038001c0d030144d040c40700070001c000011303602e911005891502d00303156003c0e00070b0189048007030341110340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 700017500 1250 700016250 700016257
    0x19020a120c05160306051503031305090a0e030705010603062405010804082514150402120c0a0611010c030b0f10020304120318050301060b030109111b0105040c0b0906 73
    0x400e800c000040070301a15119007800180e0311001c001114480000050085c142c0021380a00740d08843d980c401d242041c103040c0c8a2050703a110385130003240d030b5000301b003a07042405005501070b201d5400015401c0381c03210034a040d58070421040d90f80fa07466072820700030300080384201549182c60740c078030039202680c0000e115141d0119108060522034500b00040c24040e40e0000c85008184021a4090010b603008901503090090101642c944d656143c00061140300014041140240000c02d21102c0d91140e08002c16035100c001c90318154000c904001955403603440800c8060310342507e400102d080440001401c40d82440300c500109400c080c8032459a403108040540b03454000d0700c8100c080904160160f2440c4140ea200c40649001c5011003024036501c603015040c860280250083d141d81da500406085e16101e0080303203186901040100158005503000c0700345034411000c0f280c1000b602c841102c0b0300030360030480782c0c07800d0b5110000c11017000000780c100d0001e000030744031040c1000061070210b4150700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 700018750 1250 700017500 700017533
    0xf1201061106070f030902060406170108070815090f0312013605151e03060c0f1c060305240f15010e04061503140f01031703150a030819020a 62
    0x1c090004131001c1c0c2c1300390406003075690094141d6588650700c90004040038020103c22071840050400441d04403008a62002141c40c1880240161480d49000301041d03007000e2f01c91031051068800c01d00002005102500380c4d0298032800190ba91314112010000d1615200c0702441041004400940c600010702c81d4210076030b02002c0005c09a94040001d81904d03a2007a1725503100c004103029016a094410285004440503800e64060b0f171600017440f001c90040210100d0822000d0014180b41c00e6007040400c0e410990340400714880b43d90762200340c00d00d8080d21110f040304200c03010003100d41030f01505880e0001c0a00c408803d139803608100044002102e19102410003c040c40b1411003550b80b508050041c02560080b040c07250350007003003c0c0003400e0880350300c2500c031003000008d10a400c0070030b04641204e420000079040050404540010750340020000b0900d6080c05440b100380c4c6d114585440b024510420004d9620040704100507585406061100110b41c0f2940040001901c2c00b410447e0383da = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 700020000 1250 700018750 700018757
    0x70303020901031d0c041a100503040f20100c0201080f09010603050609030d0b091b0a0324061e090b030a090503070f03090b0408150603030c01020f120106110607 71
    0x1001d01c01c004074080c0851402001c00500e00c2c107000103da40300401e4510050a080700d04101900d20805640d2034000c5064020b98003045111441442d00c0c011001103a0091140841c8a41031a450761114808028018a8480340318040c1440b1101d003008804242010700f5418602e89245103030740000c001000003030400207811a450701040040600750008005160702809684503480c1000d50766540c3d80000442025680c2400701320300c81c0d410241d903090f0094062101196141450104101440d448404003808144c0e8030a00c0601150b001040c401c52004c4808401131813030300e0800c00030705000381518207107120400078030440c40858011810100f15103032000010b407665510200d0100400c2007941c098060301000400340d0400c44c4c0a400c0b80752a91080d16482d5040e0349407066443e09000314080c01c3c00b1584a04080048206800d00f503070b510107001400c0740e10b0000d10000306402da07003041d60741e07078038481c000f050660ba0126520398403809004113240c06400e00214031005a030700d032806402d03507062 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 700021250 1250 700020000 700020007
    0x3150f1401030c110d021605060405130b03031303110310150302040b0a08012406030504172209020a0e0f03280215040e091c1809050103030e100e01020307030302 71
    0x1c0c020354044002003049800c1e980c40c030f0078043c0c000c1e40320a00e031b1031f00031035140520030080f4152419500341c609440010307100603101030000c0a400300500d4141c1600b9810302c0b05010f0001103008045540001c1d501c1696141c9240342e146003803514000515070241c1d1281c2c1000c03411200c09119041107011a80c0480700400d0341180000814026505904040d00d1542007516011100344003401103e890758504084910841d84c50b1403c42c211b800035500280031078100764600c0c0d600602400501740418030360030b005140c0d101d070034aa0155500c5030351112001355000309221810a400680c0035540b00015940b10062014540000c0c0c1c0340d07545594603241ea5078800d05420900f10320b40380e001e0a825806000728480d40040100d0260640140c03280070300d15201075000401c5004007040c0210510322012002c0804d480180d82558a140384900c0e2130360010450302e0000e60f07100240550350007540644c82d518810000e00c4280150311120900140505c1441c821510b0a80da00004a981c0b0542500d8010389 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 700022500 1250 700021250 700021271
    0xb0103061a071502040f0f0f0506070807080904240e1501140c03030403030603020406141e0609190302030616081b04123804120309021003150f140103 66
    0xb289091034030f9540d02840440c0105031143c1079075807035003507404001d50780790301555400c40c00c42c40d00510702034160080c000b80408800202100d000d844c034103105401241c1001100e01c003240417107951070414194001c0091145035103103c010400009022036842d140074500d4910b800301000ea40b254035081c1004034000500000c0802407080e81c950f0820803003503d07540e0415050050107400c1d5800b090b0320030340ca0301c1e030300195039011000803070b01004004d402c1086001c104030200c00d00340d8a45404c0340d041081000386066550380c00d90003020300d2003004030300c285050960050500d8110000d0810418421a10081c1c4c2c109801c50900c60b0702001c8a00c505400030f41e0100003a0300340c003455210050340425140d03460300708070b10030035140c0f61601421b07641d900080c0c00e4440d842c1c00e0091300003641d40f0303001c041000c540421044103034000022100d04020400300c545a010070b44109009408030002a99003121441c15405664000003c029105906908900b840401001e11241e08201380c14140c0c2e0740605c20 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 700023750 1250 700022500 700022513
    0xb0a050913061a030924061201150e0f0c030403140c0a121710150c020f060c0d030506030d0512070e1e01270e0c07021f030b0103061a07 60
    0x180a00740e22618032100040d03110f0f00f110303590030a03a40c0b10204d008030513010341e41010801c2040241c540344400410242c54600c144031080081c0c0e107141d00c484d501c5140d0070031b41d1011002d00c000200031004500c00d862a0107039411000310406018040745810400601000c654062203110700e60f540c5c844402c0d80d49481d00030b100e00d00034986400074240301c000c03c01d042840703030894012121400d0500910a1a5071010803030701c00c054a034014851141c01c0d8200b00b41038280300c3c2180c919054800792148144071947e01c0019825041a50303007072850b510000c181c52a0591500904d030700a14150010704a680564901600e0b03401901d008406001d1442c00280019104905c6041d101001800b54629006503030451403c4031160050300f40450038200c402500c4505400d0300700c3e0000c604262448034542000390b0008060009881840444414018100580d8800495420540d00010500b00314070b00050050192501d0b00d10050525240001c2080b0031600c1c10511100b10094542d42a910341c0e0368509075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 700025000 1250 700023750 700023761
    0xa020a09051003081c110a110c0109090f0f0f0b030d09030b0604050a0b13020306030f07031a0601051b030403020a09090b07030e03210f0c1305060d0b040906060f0b0a050913 76
    0x410415003040320100246e40400018103058181d590b42100c43d80c07145141950340c140c5414428001010300c002049000200d074002131a1601e140000b01c0c1c40940c41492009449840341c03180005590b606000c0d00e541b604000340003100c282c50a204201c41e00c0e684424825440c01000c46025540b0780000601c1903038207602a6445640c0100f1500c0b5404026008000030f42003112090b00920841001480c510000940c00301103a9204201c2100440c0001042024080c09000103040c02400e0008140c0e4003218014010840741d840011038580c0d2840c010001010000e510005001c2c1c907210000300481d81036000940d2004841c2004102144040d1625180d403003098121642850340c413288503105002d69200f68000e2040001d404195240d44404024504c1042c0102c1d001e424442020080350074908041c0c10001c3d903441001510038407080206090b02c648a13411a492581d5040c14401c1d101d0000b1803c0241204406c202d04105215402403c0c910400c0b1115209080d201c61040d8014280e8000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 700026250 1250 700025000 700025047
    0xd0c08160c0812070c060c03060e04120c2f0108040818030c060c0703050d08070801150903120201022d04030f060f021303030e2409210a020a0905100308 67
    0x46141340c031080042c120b4682050441d0494181681c020080f0722900505064901d81c40801050761074984d41c80100035178440c100d03424450544804004a00380520410340c0f03846000d0840301450103680d10055680014101d6410f0102d0841480041049582680c104a40b02940518620a281c0001e031078a40c0d500300b0035600040c00100007810410205410044a104070200c9100340006030054034001070072038076030300052070748001044898201d1840ca00d0480b2a8141b200f501500c0350bd804400c030401121803000750390002100840c504048803003c1201581c0302d000602c261881700103103400d110b1484041c180982d0143d0550510006030b01020000c940c00f5000c5503120784c0c55103c1050001d2900c410f8010540c0c030a110148e504104103c00e4400c804241407100c0c040c468903500400f07810094465405c4220f00260143d01e03191085c0411700f404110004200c000294810000303260321940000b41d4a500300024044030142215a01040c1c031b92291182d5103c2d1002c00f80b01c06110043c010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 700027500 1250 700026250 700026277
    0x18021c05150a09060308030f0a020c0a08030402010f090303080c180d03260c12041e0c170a08040b032a18040e07050418060509030d0c08160c08 63
    0x1e00c544103552a400ca68049426505990000d0f07498459104031106840041d110f06004c000086e80d064015050a43c042444030300103041004d0480903500e0141582c00489079403000000340019584c0218000a804030685000000203056550040025a0144c44c0413108180400c03001104425250116903100b8017a24003103000e546410010303d050010400348401c1200c1c0c1100b1400d078000303c0407451180c02c1c0000d42901e004845001d40e00400c0d401042500c480030031170b40c0358100000c0300e142d0406140c00b07420400c00b4141440155911004500540001903000014100004a0080c203803801c032200c0c00c41164690f503520030f81c0c0f5900a41c0424015803080c50003000c1800102c040c000d4000c40014a03030041c0d1403010704007840102c40326103c1c680126030000d20100300c5450650002181940604600d00f4482d115550314001d842c0c066071940000d4001103000050000740c2d109944d4010414581015030f414072140100310303621202c1c0c810342001190f01005003444018800c58107081d08122 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 700028750 1250 700027500 700027511
    0x30b030a0506250f0e0402040e04061d0102160f02061207030c08060a0503063409031406043f270803090f1305040b090d020718021c 58
    0x16205454180031504104414030789000f4250034100141c08074010022038448808029504a0545180c03454088030f5a2080e0200300c00b0800803011400940a640f00b00008180000c0c992040c0040703d820700c1d0101c00c0c81e841844240c582c09a401c01d01d02106422034016001c980c668000715026200b00c8206170290b0600d0400d00001c02e030b141c2c2c0504136012040d9545403143c0c4420041101a0300d240c410181d242e8080ca01044028000c0c2105911805001c018100320b031150420005001d40001665000706515034020030502c41784800781484580f00b040a44254035103641c0d01c0700070804001d12290383c80b001c0002d100c0c51400380f240442419402c00000e080c060b401c00300051000000c144c132074240b0b0761030100341d4a60068060011080d2a01c1101542c1030414a9041c40140c41546111550029600b202802403c0f49842000d010301d01440200712036250221540b4600700b03403d04080215802124104603110758190206000811480e004d40e40b000900039040d41100b190b1041003000740b520 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 700030000 1250 700028750 700028753
    0x5010b25080d0203190c080601050d020a02010914070306360302011112070f020d02060105061809010608010f0f0608040b091e0303010f09060509041101020a05010216110321030601030b030a 83
    0x211011640010178000030700c580d0580322800c440a01043d1611804141c0601c00e00680920540140c00c80b01c24030302c0001130464051301c03101c030b901c1c1540b4407400ba6508038040903c140030300ca01030111019044070034102460301c480140c210400307140f150f480071410546001f1013014402c5d0000e44c500381c6545902034175005014941600e6081c00ea90603000b00700202100e040da1781c0080b1740d0100c0071003290050301c110b81c078000501206034030020354100c2130924003000b40300a5690041c01030107001c840d610b400c2591b0400c0501051510180c1200000d210300300720411078158040c40c0075922a80c0710650717040d0360b00c0e51402e90b0314003468200003444c0d5461001040103c42e40020141d4104c0750003041c0400f540e6038901c8806d0840f44e650081540040e1958001008109014521002d103503040c811111610340f81c1c1c030350030f0880c0c01c45076504609040d1082d00c0f0b41440900d00c1d50b00b69400c01100500080803800c2e9003048034514000580b14000c10110005915078000e80c08400c0500026065070403201d410f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 700031250 1250 700030000 700030021
    0x302150c030f0a090506010302041806020301031a0702030f04050f040225031d0306040221060c090301110c0307110a15030b19062c1203070605010b25080d0203 70
    0x854001e940d000798240003d011240768040c100704a42c101d0054141c0e40d09540a20019140001c100710040d07000b00c020800103122032000710700840c0107031904485010b10607551514885e010382192700f15801403003444940c010440c111400c0354011504020000251008100640142c0201200303034110002c680011130319907800f81c004d5500c0f981c1d880c61003609408480107400321420316148c1680c0003000140040c20003801c0c90708800b10380147e6448200303401e0b40203450f040c811280306003074840120300580350342024040c010030801c003e615103007011004401c450b42c0340100e0780c0241540d0202d10407900386480d00000d45003c1d190000d0030114001c2d2078003014000d4404840010b0180032402104440c0506c01c41c4214141c45090340c403c12407041902914500c250880e0804100203010900c0d01d9031a521440300c1e1318150b0f01c11020310303122405401c11500b05d9105a0000300300860820044220b0700034009000e422420003102c00485200314200504036001d0048401d850300d1000041c42a040c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 700032500 1250 700031250 700031257
    0xb0a050618090601080921121008100912030b0a05090a0603021c0f02130b04051501030c1805131811120d2a020d120e0604140405040302150c 62
    0x295000b4400e62540801151a85001c4614005c0c9800a405100a45c65010304200007903a5212000d0b00300307410501d400e014048103440034669000040010410f2007000c0c40710f4001401d5070310042098240300d407602240640480001000c142e40c0710301c20019995040103060180201800d001054a07190214a005002d640800d91080150300c1c4140b0140f41964495629554880282c14000ba001e40c280154824500160b41b4a02d440308400d894907103880c800d061161108900746484c544c3c80c18005401c4840001e0250700300305001c1d000c040304500841d40c000840d603054503249c0c0200e0352080a00b00800c0c80d030344850011140c02c00e0703180500009505030a02032408031041020354041014a9659504486054001c609040509070701c401039440d40c1d007064001c120041c2c1c0011480d50016080803502001119400ba001a088900951103096030305008025600d1610b41030500104500c0e020503540c00c148556202c800050800d4400c4c40450f10414181d000c0440c64101090b045403280c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 700033750 1250 700032500 700032547
    0x130f0b040f020c03250506040c03030e0315010515040306021602041d060408030a06030821010510120222060903150203070c0f02011b080306030c0a08100b0a0506 71
    0x24200505241c80303621601c215070840181e4030095181000c4220391021440d41015000314044507000e0342d10120b00f041c40030300c0c0314030b114100c42c000941c111301d000380c030328980c414880e4002d601620a41c03501010f80809241034650031030303916200d4844584003940038400c580004200078008200c05191450545800c4c6c1d0721031080740c092102c60300c1e070700018649461109051445500c000b0200e000700388004001c5070011b1402c00c006c03503446e0321303504c40b114213500911180d861f4003809c990400c1e005200b03481c210301401d4115440c010020142c3c0e80208814843c0103448903003640003c0401d5520000b441448032150b040c03030b01c1c0382d40c595503036800307414010b452200f03032044401c40b01c55904030081407007181e100700b155031500c9284558a03152100100407060040b41031100540c4070b0700301d640c3c2885810286520405c0402d55900d001c0c41458280340314481c41d24001c19007044144171074800030421008042e0070500020700c1c1004840011880541540041e800500010b20042e0545013104000c0303d19 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 700035000 1250 700033750 700033759
    0x9010e030a0c0506010501020f030a0e190e040303240605131d0912040b0403060f20040503150f1f1a0c010c1806050a02010209040f0e060c0a020a11130f0b 68
    0x5d03aa00c50040e0b03114080f0b500580e51580007040101e080740d0040d8061180324401800e11074a0200711083c072841070501350424050b100d00030b01000105a41800f40c803500095500c50030103080403c0301c2d149410903143c000c038018008007107509040065000714070001468121222002e90f1404469025090800d0355001a10f00404101000098004084504561000c40b25620389842c1d5101c00005007841945a07214640b09c8881d0903050207074102e00d682c405820f50031130741c0d6140780504051426130280d0f142244090f9020400604d60004100c0a0f8001240d88490240503264490f20300400b0003074100340040501f0705100d03090100441e015007022001c41c0000c00084003101015544010103641202c4094540741d0107010b100e224801415010358180005818980320400041c19644107880720b0059903654148030040060801c000703600000000c002602c2c1c458240c034025101d110003075000c0c0c44552035821045964680e00380c030341a0524484803c0002ca0407015900000c0c00340c1c0c0c290507109 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 700036250 1250 700035000 700035013
    0xf06030903110105041410020403051902012f0c0913030c23010c030f1e0e010e010203040818100e04090c050301050717070207180b121203010305070905040807060509010e030a0c05 79
    0x40040300d108031411341e038100e0010b042001c141e506441d0140c000e03200880c100100c000c0039500c00d0502c0c0843f10390036103450703420048012444410914008500740d903548940381031018080070548000c880d40b0081c1e01860003210f0004641844140e41c2c2000920b070300c8200400b29900f00b0444190701c24580031303495a80c00c0c0540410034080609407202c4d222111940e03c100040001d10465035880013617000040c0c40003055010402c148182203030800c460603900300300c0004144a203d0018219a0312200b0200d0300030400348d100c0d01c0000d041c2205e00c40d8490003240d0b90b200301d8007800301c011030240c000c02008000b80040e181090700106419645000380c0d81404c81d850101d0b940300c2c004282a0259238403213090500c44201184200040c007810a002030300418001d1100140036824050b031012030030110240b56983d451441c0151402c41c45601940181d0b15143c00e00c00015401030032515050b81000d030215083c0c40740030a00d0b004000d0300000b51800d00c03001401100b0aa000340c0b000b00300d24020410780e0207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 700037500 1250 700036250 700036273
    0x200f1e1b06100e041109040c05031509072907030318060f060501140a1803050607090f09060311060307090906090c0909050411010f0507050106170d090f060309031101050414 76
    0x260303030f007038500902036100d0b88145840713410004c11442e841401018145501507482000c40d051041d40c29010002c0050b0b40e00300840050100060f4004100301d580201c501c0103111007410b001c20002458044c005c00008154042c0341c86030300701400b40c20f604492400312172154504140102002085480e5079828203400058070b600924640c40c103031400d149400e19026091204607803912482c040403050000b11800400465001c12401c0d00c20303c0700380c8035081980d044c1600c61025480503880b00100c641066011700018011006241c000d0506490b01620ba0311404000d51740c4081d030350060702060b0f152a1000910b100d00340c00000c2086403907142c1a0001c0d80303800e41c40060711400c540c0a0101600c9450391051548950400c0c40000e81030700d80241400600c1e07562a0079030340c2550040344a03d00303016581030000c000f07120000144010b402d02d001040c0c9011b425078511071403803081340e0915984914420030325004440c00d40c480c0700700c44002c014600d064981081d02855204a8100e10710400f5903005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 700038750 1250 700037500 700037519
    0x1a15040b0109060516050f0d1b150903020f010c02030a030c080c03040212070e1006091d04030513090f14071409040c030e10200f1e1b0610 61
    0x160040810b81d6100c0b5041c1c1004801d903082e80c40b560b200305040e12a442c00344041a8148030303100956105030081c00140000d20b80041a02d000c00800c0c014480540f0400e04c0000d60302c45609000520b00040412122143d050a0b4140f000502100d141d5508202c00c5000c420760100c0203101280c00354034200101d200d900421180240101c8031100c0d904000c00201d0094a01103c2040020100c282260a03039900d408a0706542e00007541c103c110072070f008106002a5810500034406801d0f00c6504c03c9441c0766442c118070114502500250510030002074152170800b412007814041d0002502c20b1100b45800c1d07000c00000d01c0313424644002e40e0801c40101e0222132040d21754610410380020712500340b240e8a030412000307048844140040c190380340b10340444c40c08180020400d440780c210002903d54561200c004034200500c5400e4402c900801c03c1e80b0f0300c030005106880080c0a80c003c0b0309004216609500c4aa116074881c04142108200301c0e0a00440f0006204d407080420b40866203040d640d942132038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 700040000 1250 700038750 700038761
    0x11709060a1109030606331e03040525080a1511090105120a060e0411090c1306030b0f030a0c06090f060f0e0a0509070f02060c0c0a17071a1504 63
    0x9034190030107004294980342007404047c03244038403030107a8419806007001146610400b06694a0800c01042c8030040000905c160076406110354400d518501d0582c1c0d9054849a00d807903804191020481d0b0f401829000c902c15102030408101207807641d54403820001c2c0e840000001401041d802d0410746544004480c080d6507070000103840b11420115000d00406902d00300800b4076140581e1070340c000030304500072061903010320700072940c4010307455050003400342da0300c001001c0200c2010308002c611414400390200780c5c101e0b080d42c50700042124401001030b030203640d801545603052280201c003000f80034121a1940841c0c19a84946400c0d942d0b640c11040e511046114200105040038032006070350340140709540892200410300d1000544030b03000114403940598400c0300142c144031407284100d80402203182c101d824030484a0919146e00c0790182e42e801d4545009020100980f481c0502801040079528625403060060740005480003c400d4a04030448500850000c21000b2400c541020b2058 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 700041250 1250 700040000 700040017
    0x20a0504150302010507050c100302090102060a090305031329220b1b0702130204061404080727020a0f08280b06090d06020307090b042102011709060a11 67
    0x8050649580c0041d1195084a00140e031f040c01500000c07800360780c0d40240065600f809440041c1c4904420340020f1400c2d03801804214035920702a0b18401094005003070f203a01c098002c0559800d0300607490b00c05000e9a032031210480f11090b07076402d08030b1004c01800051080c540740b00c082180c01198900068804610400902081400004118110102400c07516828018660340b0315005041e03011504404900240e009419070114040c015503902a540b100800f1881d110340d420241808140d503164200c0c0d00c1461090116505800742500304140980107441814000315200d109131000a0803078000c8101c220001031071500060070a507608241248050070b11910784403513106149102005001038001035a00030030030300c90341d402551945c58001005211320340158a900307108034060078410170790b0448122614148418044500c8034000a850508040d2541c1d108102600050303902d00b03a40b1018103160050a0200405c03240005000d50150070443c0080148160340d10b00000700380500d40d030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 700042500 1250 700041250 700041281
    0x90b090708191d031603032d020304020a051507050c1027120c08100e03070602030a1103040b18071d061201060e011523180418020a0504 60
    0x1502510140c0a6201c01c00c2e4007020300100c2c02440380701504903c1e40e00105061991700f04800c00c0001056454050003016407403658420989034a01e0600c120103520008110781001e601200003070070f540d03543e1043c00080901034082c0340030f121801c040000c90741c042d40c41590144280382001a140c144450f102c44d060398280e0741c4d4005251914100e803515005294556040500840007103801c25800e144088120b1017032507400d584c0c0349030036011418000c284002e014658a40190060039540100481d500c0c1036102200503520303540c0240c024002d0000c1c1e407142d84980700201c03c210402c03580c1031907640103203191100911244180e4400c40e554402c1409402c1c072000f0003119807030b001000b40e65215003010b070040000a80c100e165016900312041503008150b41031a10004100c200d00714103881d103100e100b600d0720520b00c484920000074006045510441c00c2a00001c40c0d018490050781041c7d12440c0041c814844054250444c84005041000c1030b03106410707003400012207160622603050081117039034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 700043750 1250 700042500 700042531
    0x5070309050f12011506031503053a0e01230405060702040f05070f26010b031e0103150b09090a11030f010513030f0807120f0e07090b090708 62
    0x7002d00014248a01445412800040301881074000a01501c03106007040698183c00328070300f1200605a400807032290450800828090001c02c0010a03002d80802440c40c0e00a20f002030200031807124810540000b0300954084911002180d000c01030604400c0266503070f01c0154258120340018003011001e61921600401c0100300c542041000350204078002080069040780f030700c0d00c0106965044840c080014140b003003006510350403180d0b05500300484c042c0402c028841e8118494070100601526a0100000c030004107070118003c8199001400703003801ca2442e582d60300d004440000340e010981c100c2804c00c6101c0900e4104010b22501c1400a2002041034064603248d0061459418841682500840440ca482c81000740141c80c00b0316078104000d164182e007401c0003004001da07074a150341005070340400c2c061095407200c4464011300c07060000161002d12000034000400860234400341c14010f001002404281680c001d44201200361003018031590341d05022a0714100454800e00c80c400700c1c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 700045000 1250 700043750 700043759
    0x160e040c022104050a1508060906060c0d02060601030e031e0304110d12020c0108071e050c10060504060510140705010b0406030b070e010806180a021308150705070309 73
    0x5400000440380140160b600756104070008200c08010704180180503500020100708034184402a000140005070740c1e0195107036045001031054030003030300e03603442400002c01080c3c680e5207800c100c1b212440d2090855074a8004134002944540c0b00719402030210b4907024915508000100481c0c1500b510110803070b11100e5030049500d1703d0b80020b44281da420040700c6540e0b80d070f51605100d03c081640103138100c410303d054041c0c0c001e2429801e80406130411603080c00f840103907038020004c0a031000e421381c46020700441c060f004a40a0203044c09010941c420300340c2886990364141d01600c00d460f021b0307400b400001d450b0f200348007198207025003040000d5081c03281d6586c1c6005002c0505241e912680020a072800440001001c0d01d040d03030004d95520000070244070041d500700c050860140e03c01e0030649401d240074800204021003001c0d1004000601400007601100075a045440034000d92069a505130386070100103995a034080d100c1e8068024040100c2c00b0300e405203060316000d60b41035540102c0c040c2172 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 700046250 1250 700045000 700045009
    0x331030e121e0106050a08100b0a0e221217010803131802090a030b01061b03020606010c1b03050303070f0905060706020705100903121a0d0b07090810060608160e 71
    0x300c030340309066561380c0c1c07004038166851020700d40081100e80c000f015110714203103200c802c443c07104160b0b901c1030712002001c00503103a508030140d0b84004c1810310100c3e40d161a01d00d088101c0a004401426a10300803000d0003e20303085035035441140c5410b001021240e894080e01ca6a9200b181071160780e10480040800500b00000c50020114406801c05030070050b4020104242c0c0b010354008813451604900148045e584c8015050300d5140314404401c24442e880e00d01030744500e0b000d046181001807a9400e40300f03000e5a83c010184801d40784d070780300862983c0d0342400c40d180c0c0c1007070360305500044045000301c00c0c0d50301c03071136481094400c0145039620f402c0407596914020b51001c0d00480d00c500071052200e24921041c420425002d0007a00c9840807045013218080446d429500c80104112030b05442c0c0c921501c906050302c801649c000e8032030300c245e2104581070b00c00d0841039103c0c0c8000d10802070982000610350b040082211400d480d402655264050131900c0d44131040400c000154441e4070700c18883c0792 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 700047500 1250 700046250 700046293
    0xb121c1106130f06050c0319150504021e0d0204240905271f060504030804092003070201092006030412050f0c0c1507020a09020331030e12 61
    0x8625100203a0040907030343c04058078403c54161384d501c280401042008c1c0101000c000c1c80700c03040d11040019036034108031800d070410035001d030301e018036400728440500c101c02c006038a05c00420031483c82d468030140340c44640690f02c58003804000390509003090341c14050940c104901d00f482500c80400907820013042c401c58030b80441d040311084040001c1004004031407c400c2d401080c0a20801c100e56400c51100300200c0c031154080ca0800c0001c220400101d9190f40c20b0360107640c10075030041192101d0018103205018052084500e41c0f000000f8001c0765501503201e1550070384260302d00b0320302151310301400e80c1d085080350440b50070100400003d40000c854544411032040e082c1007a605004031400c01e030b4400d41202c04807020551100c862442c482ca80700c0c11001004080600540c034107100c580c0030079085003a501c9030100083e0080b0103c0d80c5456104000d0051554034200c200080303119080911652403d46019004501103580c0b00e80d46007021203a045100c255100280070001030b0500d112802c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 700048750 1250 700047500 700047503
    0xf2d15030b19020703020f0c031606030908040509011e1a030c0304050f010608070801060b03060f120c04090b160807050306060a030b10050705150115030507030b121c110613 76
    0x250b0310b000c050003262240c4080c1c04141d020354028100fa9200d0072515140c8454508810f210391701850322a81d0040162080c4000c0d20800c0c83d01150441c040d00d44040180982c0d04402e41c004001000811400c40c8104600103030210500041b2816030340b002c00318201c51186078051040d00040000814005030803000b03580003845441101c0b1400c4d0b13158403203803c594442c1c02619058102e800e04201a000901a480252242c2d80d851491030130140c0000d90314840c54165140105000c03400c10300440800e10509030000e00c040e00a20401c0801e10b880c110144049600da440721005000382c1110340e1280c45c003d032044440d40c4400d861500c404007080050b40154203c50308143d203d95a0326000c1c0c90714101280c000100c3d4440ca0703110701d0649001d40c100841e080da10380340d80d03100d000100300614940380319041602042c100060141c0790b101e4214040d102202c034080d0401040113074000a1080000d07001a1030810300081000030300c51030030880d1052103003008020305510100206842d146003000004105 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 700050000 1250 700048750 700048771
    0xc03080c25080912010b0a1a0409021614210c0c0a0e2a030a090606080a050714010306180506031903030c0206070c05150a0f2d15030b 59
    0x841d24010a1503078058208003159000c001240c482c580d82048100c22244402000c000d00c10302c0d8020002c00c840e141c00b071044004110424000101480030382c000c0f00d0251403031140655903034201002500c0d981020210072a20101d034016084140704c3302140c07500800510a02c101d200310503044074803440d80c00009042c140c6000c3c80a95494655902d5051001824001700019242c908510a0140401009041c400103004402081086400c2e1411243e211000c1d0800140c2c0e10542d05062009060070782200c0070510a12407000140100003503142c048401410301300e004141154011000d0720614481c041c448130b0b440d00f403d0302c00c0880d42c000551169004c1c046442c0e80940d141c5180024a180c0000d40c086aa500c01d50b124107581400104d90200f104d0621600c000b1007030f900c1c540c1d01d0200e000c2071844503000d1004116074143d650440c1300348040d8035030240440000c15554420344c01503007405003114110320400344403280d014050030b45102400c500c0048103601d941c0310703401c4810000740400040b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 700051250 1250 700050000 700050037
    0x40b03070804050f03210109180b100f08030912010e0a0201030b0f09010f0e0a0501030812040501140a06090614101103040e13020f01020105160c020d08120f01060c03080c 75
    0x80203410809000030004403102c1b00d03803801380180c00304050081070300942034050a241c081d822840310144034200c0f450b4840d203103100355a0358201050f060800360f080320030600f5110400281c1c0090010281030007100031258031000501d40f1413081d08079940742c7e8901071203411101d0903402641c02a8400100c84001818a41840c51004000b0311014400d8200b0080c40202c010240014108440303019880b0515a600304100d505545481c00c15018035030365092100040030000c0d04001d42034125036031ba0008501400e80b9800c0c0800c0a002810b03ca0082c5001c81f850018006180700d41c114444501c00e101034941c4020182d80700084601c6c02222095141c00e00c010400080d0648822200f20321403954034038651650116481005040403090041e45e04581c10300050228034182032074810f410724042e06040d582040c0d01d1010420280f5150f2000d80410700200c0c03c00202200d620225120342c80b071560030101c0742c2c0c84560640b034101708000060000303104007002854001c40f1500400507001e219004842 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 700052500 1250 700051250 700051273
    0x1d0310020d020705070807030201090306020912070620070e040210050f040609050a0b07170d0b040e070504110403080a0513050303071101031d15040305070c06020115060302040b0307080405 83
    0x9907449408070054a42c0e0000c3c420050040901c0680c0184c4458800b5100c8549181c0000308041010700010700416030000320a207031035841c5d07a1900203400410050b108403d03036452025120f41411071515888280d03040c40010740003000714858081d1107070b05e0002d0030706484540902c098070342280c080109010081084501041004003d0f0004003060f0340c80400050805062020418450b0306c00701d00c00b041030150900056001c10000304115054218039140d4103008005400b5142d2030703441d03075001841c200504080d02008205407003a1101075400340b1039403a4010300020244664440503065200a22880030214443e00003050200000c0c4104010b0f50786400002c0d00b95800040201c0d20200514049009542c050048200e00700d40c1c905048005204445a1611407052500003a1071003202030001d01054050819202c2c0c1c3c6801c8000b40c100c1c2d03925104080c0c02070008100b1000340c1080d415000581d68400e0003240c06403181c03100102d08680350040141c035000c0e400703401114140214001ea29 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 700053750 1250 700052500 700052533
    0x40b030a0c090c0f0203180402040b0a0903050f190f061401241e081e0f010612020307050d090c17070906080a0302280203100506120d1d03 61
    0x118001e01a2a000032440d151240050480d0028080d141c240b007500c128113009550080305464028000f6000b00500808001c0010001d21442d00403041c00d440100b00201099030044680050b00d20039000c40f501c034012401d04951b101c1507249501c01d200207910540c0d000481c82c88800d00400e206040c00b00c0c2000c42d00e00030952044c4241c00800100c3c01c070202da0844104410f40c0d2400808060a1150208400100340700d520b0200e402908148103000b8003045076520f000001201012200210386d8150a090010406400c420321a0703400152140e4a0980050094402c0328082e080a4032142d24099100381c600000d0032201809032000e40c0f07009000100d895198044980312018200900001420080c0c00812074042d900a000240c0c060b402d4180020740000e2040404c030b5000c6c519a00c0101c8001184403c100320074002501402100c0e90056900141c1e04802e001c0c0c0b01c115210241c0f070062064050f61640711461010024070b13000c0c005180c0301c425481d116035000000c3c7c140d41c0865042071280 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 700055000 1250 700053750 700053763
    0x306010303030b030c0d020105030601110c060408070515030106080f07020c09040b011719080f1b030a1205060d110114070c030b09030304050d0e01110a2307080a11040b03 75
    0x503404640c642039400114134080c85400788040307003207507000103445413600000c1490000401190501c08001018900d001e02000b500c030520400514070303540d85031a10303c490345841c0d1510405003c0c00c00d411036214203441645c1506d05807407859940030f006035600c0814400d4000c02038003001c02c1d80298000c00c201600e6802107140705600521503040554901085005400e007800e4040382590010301c46000f25070700c1c0d02a203850142e0400d4203240c450003040000d00f124803485101c100d68900c0c1c03103500c0c3c1c45024048044c01483da48c90b291701c4524041200c01c10161070b401c80d01c2c59030040094002c42d0006903000031a080c003c07010314200b103080d030340d002c1d1080f0140c0c000d00b03040e02d0402c040f840820810801c02c48184e03022041c40007a508500b400d940e40703a507a8441c44c10300000d0200c0f02080c080c00f648181502d06901ca580c3d800c99901d0030380d174185030858210460803060040c241c01008141c040002034400121112403004141d00d50241e164031810440d0a80b103942e019131141680c0805a4040009 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 700056250 1250 700055000 700055003
    0x2060a1e1401080c0d20040b060a1d0d030f120f09060501030209070e0310050718030b16030209130f020d0516030e1603030f020f190c0b0301030809060f040503060103 73
    0x12051950402120600c1c0c1401e245684d841130035400980301c0040c0d03003441805108a0024034484043e02002c0c00940501200220140c110740085030301c0d81120b074880181001c569501d1039101c40e28180340c05001c110000d2600c080d0205698042d0440c0b003500c00d045d2282040d03541c3c0800100c4c410307800703e0001901c2e032011050b205142c5610050003949403c004c0300e5005841d0381000000340d900940401d80b2068589100400c140e52400000e0809002d101140185207002c0688021182c90340f52030494041d090f541040c041000038882030f100741c003a1003101e1059130300074035419280d000191b81da405403861410106801340c0a001c1c1c0c0008401a004c0c0e1030042c080088030000000103613400400b16125687c003844180d203c40011409800345d041d51009503600341c07602d5511103a0302c40c8203034038010016107005554031901d250800f00480092a140c200c82c400d084500c025503858942c0c4000740428003000e071410b402000309001c20300c2c0c101c0c02040030105100e10305003816a51400281898002d0b0300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 700057500 1250 700056250 700056281
    0x403020d06060b0d060806060613170f030304142104091d030d02030402010f030209060a0302212511070506071403040b03010e130b01090b031908070c0b040602060a1e 73
    0x5000c41c6d142480340b10b41c01039055542504041032102c000900c500306121b915500300520015003049903043c0311078680456160122562030400c2c2c9002c1400e14055840c0d80380901a00c1100407020728104003003074101e849100c0c0380b400d01e814a15820000c044e0101c0d030b00010ba0310340d40d00001e51801400900508191402d0060f00d07450640000751007104454109002c140c410401c50b0059038a00c6c1c00c0d203031710000c103150050700c442c254000100b1042555803092410b600d003004000040d400054000e08403000c0d8401c00300007080388807080d03580c4171325103111000c1e41e0070440c1c00b888107041a401810340300b40070320034540e03146112003903107400c2d9480350b00301c030011820010051000c90303488110140c00142e91022514518410b0b180d40c00001018050725000d16241c01d1030815035a0204a408851907003910940540034543c41c0684042e4070140080b10642c0081c000010071040d598103070ad040300d1032900600000c1d581c9a030000e0003060040c01552800e411404041b48641741d9205540e41142c41c0203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 700058750 1250 700057500 700057511
    0x9070f110f03120105060a05070f1a101802090f12030f04140301230f15040f0501051017040f080f0f1b0606010507060f0e031c05070309080403020d06060b0d 69
    0x40c0705070303c5100581055000d19410040404c03403a034050101c81d55a40c00814070507410000b86496800c0998400700c003103500181806001000c40460420f5013151151000484000d01c40302000c400d9014410749140c2c4650780c4440e004007410720b18110700c07100d0b6041090728500b2446882c40180e54015400080e901d507070103100318410741424070074001d403c502d030043d0314910139002500011090303005014600000f0410301044e01e804012802104400004001707001d480740c4102d0f0f07403000340424418148240c106140ac245064014104c2d1a032a1400d07090b038004640e03072a168030901c103000300411680340e0401c00c485a2501d4110003c1c0072a090161052039850b480c9551002c050b0740707400e0059200380c20440038081c00d41c0e00882169000dd6001001080c07100780ca010b0f40005162584141209000c00600c5140c030f071144034a03c082031f203a524400c02540e190315900300c2c11688a4403008210200030070052005d0b01e0149104a0010310070304001c03400c142c4078400801c4a4002e500d58202194a40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 700060000 1250 700058750 700058767
    0x30a0c030801050627220b03160b04120f0c142404060e0102100608011508011a0904020f030708061b0f09041503080427020909070f110f03 61
    0x10100328010007044840d10300b00205e84c1d103c40401070841011151105698500b42c802d0317283c4040d03170050114400c908590070b1080f590b20034041c180382c0a0062082c00b84950101440b07400d515900240c0d5100014503040a0403c00302e210042a07804081d035540d032a00e40c0610000303060922050140030b007010402c41c6d01c0704450900c0085a008542c01c400042000005ca005445090a58007142c201d0300c1c0c2400e81782d4900005078103280d055010411040e041000108113a00c0542110000542d42022441c400e595002c4d040d0885003940c442c0045901907034002641c1e450300009185c0c100e400146500c12681c03610001924201d9158080e804a4015004110207004051080016a602d0b03460f481e207000c41600c050a80b902c180707103032948200d0380d41c01c08030300b0b469013002d01e000610350252405598a071624a800380700601548501d08020300100d00c0c2c0361401c828000d44200d01d00180c490100c9407a4034609503401d403009050030081140e083c01c000303e54a03040003064540b544541c081e5a0b42d807081e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 700061250 1250 700060000 700060007
    0x10606030b0f1f0c02130614181f080a05060106020c040209090408030703062d060f1209050c0a230307030f080a020c10200106140d14030a0c03 63
    0x201c0e01c8440c410340e2000c10402c210344590605103c88075488090f070728180c44920007a0b030b0400e14000040e4014100300384200b0303500c0d00d551011b401d64801e80f200640d4900c41400700b000c60a1055130741c4100013020b002291408080d10510444021108001a500d41e211000a850000d03145001d80e100e074020401089043c0e0180054007460341c040d42d082d031401c0b2a43c0e010940030800503000410805000000845180c40307507010902810501084c0324101c54010020104001c849050a6100c00c0648000034910b004540e494600301d99a01c0d410201036240f40c010000b00180038040d140d0340140a60b0105a540f40d56814000d0300c00340c6220300f0036007083e007042c2840c400c11284a9010f648034000c01d00220f4810144130840c0c941c4681902d69505c1081c00c01c0341040c05841c2555004245104644003e82d08404000c881100e544500000c0b8440910310b031b4203032051841600d2600941c1444003049041c026601a0b43c0c0340900c68002c250b03204d0701034851440d4400a0180000784c0d19602d08020142e2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 700062500 1250 700061250 700061261
    0x30f030807180807180b0a120b070801180903090b030a0f0e0102030408031308090307060905120d14090402161a071706011d19060e0316060f140c01060603 68
    0x30020b11004510382407600007507880c000b6000390142680d1001c1da070003010364140c0011840c2a40030304400300e00703642c0310841030300b104500802310b901600480001d01020700c40d1492a04960300f04d030103050311075a1801400014150600e09404204a00002280118070200118080d06000c0e000299840d9608c100a0859201e01026042c9900400510021940c50310669800504615000d6225006071404c04094810250819003600510f03100245490300a0300c110b0880b0015034450014011300341c401c6441c1c4a41404190200ea000341c042c4042d517407810003801d49400050f00040c0341c200480000081c001d13403006c00300d03503030410180c1054030895241466504450b990809507080404075564aa21030401810a4100b00c100d007003a4000302c44a29103001d00c0c1d1000391520000402107009c14281017282c1c00340401282565640d81c0c51801c0000d0780c140101110080040c440741001800c640d13030003940c100c0300108815054400405a580b100030032a400c842c20001528510b421005000e891 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 700063750 1250 700062500 700062527
    0xa05100e031201050405071b050c0103180308070f09030510090314180409020402070b040308090601060f091701060b0d061e0b09040c050c0d0503010e1005031015030f030807 76
    0x100244a251901d80600450505590084030081346035078407030500301c48c480c07210503103c0515a00440907505102c1c3c0446d112803103072401c0e82d0920642e03072542c069444003c07420000030000b07500240000c49280c42011207544c40c2e60360380b510f407044654a403181d610b05170100d140412656502d0408804142c0c1001011008040301c910107402c001014401544c03003403001984074059511012804219511541210100c3c0c0d0b20000000d840e080600b4020304000b0110340c582c4040c8113a500210707040340622000c0888105541d5881d0230582070548103200c444044420b21140d40d01d8003001300c3e00c408030301e0152003017900020001034501e01c0c0090040b0202c1004c0002e61140320254800d00140c0b040d581100d000d52004e85001c140340c80d059804850707603c1031683c40d4a4138007502e105c1c01e0303802e60f000004504984019400407080d03211003010b000550b0a82c400c42d64183d20420020b900d00f2159013055010782c4802810510459603512119200c11004404400080502040020064000100704d000c80c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 700065000 1250 700063750 700063753
    0xf0e04030f0e0409080a17060307080718020903010e0f01140f010b0a02160f050405011a030f04050c1c0302060a0603081b0309190806070219030c0f050a05100e 70
    0x505140d200600440038141c03000040044615869125845580212240990102c0c03150798804807030600509458034520341310b180d240c0781000314440b4500000e600d02690b4602015005952403c0592007141c84880c8458954a809018100307603540c2c01c2c404c103610346010314054010200c1c00a042801c4900e5100d080814648071001c0c0030300c0b90024400c440c151000c80040136542c0c460302d0720581c9031454552101602e003082820200d41c00309040d000508a50003500c040c8031607621400600720600d00b030b008030b101001c0144002580d5014191081c0c2d08640207109446445181f07402040d05650883e00c0110300703680d40802d081c105a41082003c0d442035590100300b01c064259581d01070740f44598551441016150f5060902d4050140210b40e001d41c0d0040804000f40140e003250301074099188605c0382a0f0040d070000807007503070001c03d242d5041c0d081442108002c481030740d0113640c1484d0008050f903955140b03021900008008001818800e40540010039000c42c0c1c1700d00130701c155040e600490242e03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 700066250 1250 700065000 700065029
    0x10e1009050a150f05090705040e0307050c19030b09011401050d050a080a1716020c0901060e1c060c0c0c050616060c05220303030f0203010b0d2c01060f 67
    0x881e4011422003039441d0701910744207811003c644010003070002514500220b51a003000e0001824000410100311075050301e0a100341568184401d413640103a40c4080c0c82c0c0e4201440601d860300d03010780e6103100011106801c44456480351584110320400315509601c036950350b84004550821002040c0c0140f6003200d0300300031f0040a560300e07911184520b10051136448081340840c101c9005a80440700808844000c9400e440d0076800e40020000c41c00b0402c0242c080c038804a1980d081c0002c0c0c2d281628010740310342d1035102c10703c0144034010440010083c80c1e041d41024840000e029030042e00c5100300d061b501c0c0c000a4540d030400e01c0c60f129540d40081e228000030000c0c90103c8840749001c01d402c40e0441c4c030004000c111020b090f20a88030721204001462644208400118500400c3e08141c0b8003981e020001d460406002000700d203c00c0c042d69020708010301c00c0125507582604044c8500c070b100c811800c154500e0000b900218141c9400c86c203403d9451720401e02490341142402001401300c00c5c03203c01c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 700067500 1250 700066250 700066253
    0xc0a0f0b060a14040f02090d080318010507081b070606060e0f010504120609050708060903040303120501050a12020429010305090111030609071b03030b09072102160212010e1009 78
    0x1000f42107504500a0b5203400030041c041034142e041c0c421a0001900b000c0751034540c0d02d407005003540704075408405000005051a016441489441d01c9030f489500c030400241c40d0f401c4080e404112010b85548460010000500002c110f402800010105503c50b5500e1448050400c6680041810594100700090000700a1901080340d0440882d422032030000d8502005c0c00d005041c02803a4000620074800c0109025604000100800441340a9500c001c80c00c0326480341001520020302c242a231010000f8000c2c49100ca0740184018407910081c400917a845881f6170b28200c48000007030340744d00c04140360014442940c043c080d456110b6500002006072841584203040705000280140d80910003403000544224000c0d003085c0075450798045d40140b0b100007494002c01070480c0ca80400d02400d201030200717007101d02503000700c12043e0402040038203580302001480000c1d045014407a14011503180f5103c00f40e2900c2542d00d2165603803000204d543c4406c0c146e0b640ca00042e50f06a903000318540b001100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 700068750 1250 700067500 700067519
    0x30503181b010e010c241d030a271a120c040503010c0e0901170a0506040f03030b1906050a021e0d09060c0510021b0d0c031206060e12030c0a0f0b060a 66
    0x4084d81e403810090080003030711004100420282040408061f60043c20aa01e160000054640380103036075035600500d1004080d0168400751084040d0000d0603001c1c06205c488050000000001c26155081d42041e0040c00a603225407000d988103181d6400000d0103200d142020b026000b24043d8504001c0107141c9030317002251411105100300c00f23046010001c1000c02d180c0c180242ca01b0541c10000303ca04a003050308003441e5403801210100c0c042442c266012030302d8108507140b0741440c103d059100c3c80003460180c0503521903101c683e51070118010300d01c808001d0701007080c00164691980c00205092136444a004d004408035802003024441a1804140090800a803082504072f0500c405030711000c02c203516503242d045111070340e0400c0c001d09050041499120341d11ba681507010b0381c0c0e15548075807007081c03074812203805028040001d60030100707003082414002001041006110100c91800b0b00480f030003420b0061155080b50a186580c140c001804009012290015021904401081c3c506981c44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 700070000 1250 700068750 700068773
    0x30f010c0207050d03020a0f08090f0a03050d110f150f100b07030509030c06030103142509110f120a060602010212010e0403030b090c090301050f0105010c030503181b010e010c 77
    0x3c40c03280f068520031000b090302c24442503076a103038003000000e0007800350314250301260020503c2030701542c0084140309080c44e190b0440030480f904140601422042c188045074801c030481111926407161001c2101845401c10200c014580800f40c007611a041c44200d0b200b081d000540505000c105900091042410440440301450390600f0590f582d41512404039040040860505070701010110000083c410100e09a103c074100d0f88058408000c0c201d20003140140049003000c41d000032105003840a80d4141c1e1000a00000ca0f0303401508042d0540400c1c00c9a074019020a0348001803041480a621494000c0101500a80c0029401c0580e4000c450b9180c480510410b0300181046001ca0709040c065403095851250291210f541860b19024050031940f103c04258025883e0000040911030001c01141c160352050350303000c0368130505403800c81e03150f0030107450344514400a00750040d03801c2040014800748500700c03101e208841d01610014051210220f5018103101d030ba8201d41002031107580343c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 700071250 1250 700070000 700070009
    0x2f0903100c140a0e13092a090216020301020307090509010f050d030e01030207050a050706090b0c0c2107030b01060f110607110109082109071409191a030f010c0207 72
    0x341a207034844002d00300c4440440020544e0055640444030030444000d41146081c0c9003d0600703900580b003014402d60800c7c29010103849004411320003842518810340003024130103120304650301c011202d500000c0c04c9a00a85410010502c0f4001c10026070504031441801000010f07001c2c070340b007850320001c250743c0002e40d24010b041118005c3d000d8001c2c0c2c002d505546003580c0020844413440fa032841c29030740d01c3c070190242402050b9100d07400215440404210387c560220311020b0328020a1020900c010750064894802c1000e00c45542078540d0401006103100850140d50407a03025450180d000d4014040000010100484a02c00503010300c800203005402803070301c0c40c1a848003070940708414010511504018240ea40004080b00c0b1110001a04c0c0c41d0304030104403440d50350b01d86100190392520603224400c1c01021004a03850203180002d001c03984404c0d170304e0035101c580c01107010305001c454104164a0702c809511011100e141803c105000080c5200c000800c00e0035051345010f90b840c10300340f19 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 700072500 1250 700071250 700071287
    0x130f050a0807081902121c110c010203040b0a02121201301202100f020903060a090506040b0c040321080702010c0c1103030f040f06020d0216092f0903100c 68
    0x150002151103d45030036800c0c602d0302040e2103040d60319203907103144100543c0031f0700002a00a03031030403100c61001c251a8083c01058004610b03040c0340c4403641d4025003050b0700c10015070141a5010450f00003d030020541272038189044c205540c1400c0c45a16110f55910a5104a500f18081001c500e456901c6c1c2d17500d125005440400070b8418444221700c4e0030703036990030004214107152445410060540240811181c22029280242c0d1030380841d20884110680282c030503444a40854089003e550010750419081d246191030f2680740d0701c070070141020b072030405402010140800d0803860360100c603590300074840744000c4c05443e65900e40108401d00548001d085d003002c102c1e0340000c07030703408104841d5482130b003c0d6559180e03035640001160b1420176109900c0503000300c000e1142c900344003080c400109000c010494480c2820450b05400070551140040a492441400d0345132440c00b0001071a4031070f601d0784920303075030301e03490b04c1410f040070010480680705c581407260034403800b40c200c9002040307100d07403c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 700073750 1250 700072500 700072543
    0x50a0b0f040f1d012304030f120b030d0504090c0e032109030d080115020d09060c020315090c0f0a0f09020304080d090b01032102060c0a05130f050a080708 68
    0x44801800f4070b044901142c12011000703c001d11040d04001d0701e4400350250b88014043c0c000301c1201c100d84c211401000510110840d0418500403182802071040401e40050740700f80c1d03200482d14050744d1701d01c0c4101042010404010210043c00b035130305030a1031071400c441d0240c600383c0800e40d81e08075129441c401d10303641291500d04035414426201c603154002d0445070206014078000d08207810038015001c015042e2880f0101c02c50000504030403130a51680d80ca4812882d0031402c40d4500324010b0101d80c10302406039250003510b404070103d4010aa080040c08100e400a8200182c9042c1c6c214828081c04c00d503c42007001d204180c1108040350307902d810243c2d403603641d450040c001c0d00c6803c4400c41154902040c000c184400035288905030391290351328104040c545c0395402c045007150516803005a00880000d40f5821000d170103003440b0581800c00c3d50600e400000c0c40305c0c40d90126049030b80304100101e0300b000b1500e0102c40c140005c06001d406003030340604040c1603940710480d0404c491040d40250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 700075000 1250 700073750 700073771
    0x41203150e09100f0e01181509112d0a06090506030c090607030c0b0609010e16030e0102120405071203051803160308030f06010206130f080d060b0409050a0b0f04 71
    0x3e20040e02d2000805608001006900c0380c214010030b0517100e41d801d075620344a018400e9107807115118190540260a80802000c9440d4140140c01010700899940c0901024001e0603212a000c92012072409040081428030072407840a03440e94002805110b020051820001950007803d0b080c02c1e5a01900d0f0103036079a454411810307140c0302d034009413070308035500181c04030601d83c2c8150030f101034a1241c1e82030388860b1182c80c00c0101000003805000f450700c1c01c403000b056000c510089507070020100c0b8180482c0181580c00b0050880c1c1040000140b1070700b141040108101c41842501c000d4000c001d410121541c050703d00a0030b500941801501c03100c8010800c20035a0b600b0030220040c1c0d2030241031103e90301e07260324212106070000c1c0d400d0030769404050701241c0306600200d4031a219107051003402441c4c80803515061401004005c0507030b282402001070428103000e0b801480e0241596008947e540e074078000300402140c0e80140f00442c41442d00c1e440d01d01e903a448003420070300c15030221004103412045 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 700076250 1250 700075000 700075003
    0x130902030d0e3f0f060c0910030c11010203270d0e1302040306020415110a0b070e0a03020306040f121403011a0c0d11010609050c0703051608030906041203150e09 71
    0x1000c51520516000c900001d41d6800005002d48034000b02401781c40700340e00e8030002c80d030341c50040c200d0044d48040c5402c0b5454540e88640d002c030321180310f17074500a645480380340441c3e403c903131041d14a41c26040c46030702e85100292007925102e00302000080200540b0519040041148804040d0144184000c1e1020802410f407a0140e4001e107810903006c554859990340040c244041c41803008000c03038070030303502d00e9160396001c90340c3e100740c0d42c00400203915940d50850880b45064484030f500c0d4405605100400941c404025040c81544502c0030341c0004113403418440b00d4540740040741810031102180148100900f82d041c0d0713044400c000041c4140360314040f9441120f0081c000704021920580494820507035102c0212828007603c0c3d8002c000d841d8480d20040c0950300e00702c0340c801d8629420083d0f40c0000380b04034000c0299207000b201002011055a43e8440c0c59842680c24003410f61041080c0400c0c00b103940070100701d03400107007400c015198250200000002607031145218801c1d40c90b0008468640 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 700077500 1250 700076250 700076329
    0xa0c030e0a020603011a130e01240e0103050601111504021f0f080a1d011a04020a02070e090a080c100c0f02060f1012061b0e01080f06060702130902030d0e 68
    0x44a042d40015a840f000d1001c1400e500b4441c903200a5000f038400080170718424866800cad1446603aa00d80350355441c2c0015030103840b01a010904014540f00d0f03410701047c007801b40304158590076030070705000e041500411003c4001c0240410080d0500201590100d8014290140f4400c290401c11240d59070000c0340c000412b06203020f005000d00010310141d0411043d40140d10100c0d06001e0303c00c500c0800003e11049009190113000580d201c080c09002003c00d24a0b1164888944021a503444d241552294203603040601c078680305511240c14490010b4140c0526100303e500752901c1c840d4614845002990303501c1c003502d00c807141c140c2c2c58045506d80070350040020142c669802c0351188203203240707481c0c0000c000000194000514040d02c0c0507800b48202d440f04103003030b0b05030f4070a00ba80c0c883c48100390f6400c10107031207280d110300d0402c100720068030340080c40c05d41d16640200000380d030040d40c0141820030084c00704840402210340c0b44169a0b949411410444003401c484540403031170083c820701c01505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 700078750 1250 700077500 700077517
    0x2090603090606010909050c0405060c210301030b0105030102030c040608070915020703062307110a060c080108151b0d090c090e250e06060904050a0c030e0a020603011a 74
    0x610000070495030220000d40385000782070a90710200c29680d6070403410111001680c5e42c4c40584010042084145010305c080c0103465101400e454410720b0400c40c002528241c2580080d0990010004000b80a2446589030052809030001e500c2e516012003951081c2c0b1031400789009020020300425991172244180001400b400c21001c1e01802a118001e50f07a82040d1004a92113400d104075098075031405244592020141c4404443ca40c81c0c10130140c80c0c5130402002c84071309100d03600f01ea030007041036030060009041c002c9c3c485d0302c450350401d010030303040a00c2042010b00b048100c0c0180982080354040040b060884600d0140c0c5030505a001c0b407025005807600948400044100810100c0540c0e01109a1039164412645003a6070b00104100c0a966a083d01d40d330b4480c207050400c41b0340d0303450385803e0348068000e141510700104900058100e4070151403168526541d18140c0420f80e030544501c03041c56882e90b005145d843d055a00007001d52205000d0001d4624000444100307145c1c4140036561580e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 700080000 1250 700078750 700078759
    0x90112060b041d0c0d05060601140d0c050310150f0513050d080a0e12030a031109100c060b0f0d290c0c12041d220c0906090506030607030506040209 65
    0x14940102d0302003c210404841140310b016a80d050308051400400802003182d005010304119668400107450428442e022000e21420810119002d038a03944100707000308440342c54290b141e04210b41481b528241c9504460035849031160005480c5802604581c400061403621365615070958040d01d4007544254000e5401494902c1640100242e81018110f1044165645000f0b0701f842c0040100040310024400881d4104000405004d0700c0303900003140302000d9480c003500d082a43d401044400182e16031190000701030303e040e11f0407c402409aa0086c990840e104c0400300c070200006241c1500101c4010b10704582c191031181240038071441080802502034064550745044140d07503441da4811110009a80180b64444103032800b0001501c00713544035004c001e20100d404030510071440302c0203032000710f10210304182c00310714070407140c0e01034400e40c45030410349000e601e820802c10550355241c1103c1003041c104010807840e5200001c000f035000210349008201902d81d01e020500074802d01c1622500f0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 700081250 1250 700080000 700080011
    0x1c0f02031902030405040c0804060e0309010c03050304050a02090f16030c020c0f041b05041d0103150902040b0a08010e070b181302040f0b12161e0905060309010e0615090112060b04 79
    0x25820201484c27140d0702440d07041c498240020744480d120b108401d0710070f0110b842421a18042840356001d035038443e103ea400c44803800c1454002400c60038003110030781d1060042808001c8015540b40c0c00007410702a0381014090303101c035810007075210302500700d0362401042c510f034a40001c1d90300d5802941148460503502102014030301d04c000c000e030b4001d0090700c40840032072004440b212000501581265001800703040c40e41c90088074030011300700448040e40c0c0b25449421079403859540c2d1101070020108800001880840004002d08203e5107500a01c1900380a000221041090000c101d403049070481d014050440c14401d003800a01554016202006800c00003003100000c690003040880c04090704e190280c1d8919460b220b07814010b400e05400180c514841e0b887c20f002c00402d140a1710190309040090310b80302da000c00c1c2982c0080710400c42ca1b0391109001c100d1b000007440203581040c40e214480340311180540c041010140c06100b0115410044a258010310000d07610420711000d004209018 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 700082500 1250 700081250 700081271
    0xc10031e020a180509010905130210080712050c09041e0c0f140711100e15040306060b0c0703080306130212070e0604050d020607080c0d021c0f0203190203040504 71
    0xd410400c0010040340258006008000c914030f0700808031180100801d102da0b003011400000740074042d01c1020552800320405006a03121801c044610300c4903031b25600e980ca40180c00400442c40700341c0000d645803500041c070407441400d50403180e64540036140030a00b103122505082e00b0040440215000c01c1c41c0c46004096142d11642110440344907a60740b410040c1810b601164070b21914200a00544000d5a007041900b0116a03041c110707000d605103000b00c00b0707500d40415a000b1941031800b05c1c101780081c0230300030040903100d42809003020071071203403d250170025010395640306400080d00c0d0703020110004296544030300b129140503000200170764540e2124403010004120076500394021402071810000e450402406603402c45030018030100308038456400b8880c050748003190580700404108400501150300300250a0903030bd003540201201c000800182c0e012681311070500c81004060340c042c0c00310710381c00016504100c50800d424020141c1030a002c2c1c1c40d52107541d2100b5000740c1072414404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 700083750 1250 700082500 700082561
    0x30e0a060c0c0608090615060405150316030606080f150d050f010609020f0d0e01090605010b031e0412030e0c0306091b100f140c030711040e0f0c1003 66
    0xa80c8902ca410001c030311544909054850350000c8a901a1035031203000021046040c036110980d0f4881c015195614040d212404114a080c034002d280c4906000081402000880d00c505030040c8506841d041140a06150b0700824078140981040c03403500020740480d0040010032606118208003c3c030685d40b0302c04900d000c6445081c65094218154685140000c0d4404240201c941c030380d41d880c5035546811f400c1c0f402c07200184102d507510485996110091800143e1500c2410b001c0c1c00c1c8010300940305e280010070075145802074000018296a1130044c0030004100c62020460303030768113080c041030700c2000c1c0e200315140c00302100f24240c0c035100b40c2050001100d40416000700a154030406008040744c0c08003804400b01107510f43c140050200564401c50902c5214401151900d01d1544c134500988245145e1840d0440700040d41ca42e030318507003e0b0034249460301c56910750302d80200181ca40021448052500e540c68441107500070b852030f0005000c054420b600801c80e14905046aa0080c880d146614 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 700085000 1250 700083750 700083767
    0xc140906210102211b0a03090c15020c030d020312010302040b03031c1a01020a020d030e010c05030f13050f030d030209060c0f0c03160e1906050603070201050601201504030e0a06 78
    0x10041c1c05012001ca0017520103040110308501110030014a42103010070100c00802102d0002d8902d00802403010419207203d084403c0c6415195000b8181d5841e030030704140c100140952a081550301c2001443c40240c0340040300d0741125011100007800a00803004a801c602c6141c0c00c401804480042414039810035074084002020307005480084401400010390b51169680307800b1b5840711919032501e000a2040740d0f40d141201d0103140c079010310740042c0d0f14141385801080e80c5014075400813502210081007160325900a10741140c00e01c80807501031012a071200e01c940802410140c00090180c43d54a0384012503001d80c1e6120300321400c00c4010074600f0340380d40541807914841c2c001e40b07813030504610408102e1003c0d0780396494444203603256022020710312410600f000c52159207803680003074507503640d001861003401c950300046003510b04a800140b1140500c2810030740c01c0303581c02c9042d4000c1c10016049040716a0100c0034009916641016203020b20001a40e0703034888032460000c51565030010700c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 700086250 1250 700085000 700085047
    0x40503030d1b02190f06060b04080d02010b0406260c2d04050601390323040b1e0f0403030906020d0c0f0b070c05010e0a0c140906210102 60
    0x4040c2c1d1440c030007812030322104600342c000030151440c1d0a010109100e2601c20203010310491000695940d5440c1c00031643d0007640c42400150040190000010f80a0003001130080702140d04000250410500051000f048011101c02c80c10f004500411958100100c1d95114002440314001810602c030405800c0d48503400b10346074003501c420054644c02c00d402560301030507058607241005003050502c2041d501080400c4202e00080d0030762540a00e100800c60070980e4003c2da102ca200000c0740200c5078182c00c40c0b262420101108100c200500008102928048814030030180700c642c581c110003445c14056880610b544510003d0000101600300307118a00b140c9070f075025507003864920704003a0341c550480c400242c0349a0b00d44030500001b80000000342e0f80b02c1030600306004414441c0c0c880394212452114800e20380d034000081d82c03041c88005104e1500414030621190040b04005010503400c00c0060103490150141d141c030360303400164400880b8000602100210f482c4c54100340c0c1d901042d62420711 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 700087500 1250 700086250 700086281
    0x9140f0304060306082d151302030c03120f0d06050301060608041b05180c0c0d09050f060414010c1e0602090a05030a0c06110a020306090a12110a020d0305040503030d 73
    0x2c00080381240071480e2001a10348854016588a403c003400350342c503a41d802c0c0a0361174050491030700c69181f0f503051b0250040400c0c0c04080801c00140c07051524080b020700300984030368800c600e00c81140400e1003c940800b20001e11850b12002e19064803c043c0000790030165055003880d001042c0d0755881015540300f50300034058a01c020780c100500f00b802c0d40c01401943d8010788911100340a03003000308070031900709405420980c0b414500c69122810080386a064400182c0c070715004220614000103544a0008100e441500c0c151034000300901d0b0001c0028914107102e040003440c0184500301c08001c402c481e00c04a100011109803810800035445a145180714801204000c10a0304000505d224041d40c84020030000c10708112041d120855500803602c520320941e030511005890038040d1070300402516000f04001e0361640b0303021050265030741940c42002051a2002042100001c40341e00c031a405542c001108500c07801c04503201d10071604800d406100c0050144000c001551183c41258ac0c0600e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 700088750 1250 700087500 700087511
    0xb040501110f071704091d0606060c061b09090c0d270b060609060c03090906030102280203040b040e07020d030b030d050310080a08070507060305010b0d09140f03040603 74
    0x8800440c090707900504440c4509000c01c0c00044c001d088a6802a0103c0546906060352401c820060310702585007080300c00a15100e8180404041080541000e400ca4016003408400c544813640d505000700000000e458040d00c00c00702240c1e00341203c014100180c0f11004d00d182403885112141c1c040e03100c481c1e00030b1410fa114252101e00c0308400c00021080c44000c021004103444100c0281400b03004c8541c0603030104442d105982d226802003080e10a07240145845e52122002c200b4003850050070700c1e01903401000461030324044030403103214040103840c142407007480311141240b4501680d0132501006a00080100301070b100807490398440c5465a08681244640500c102c0640320710b211500d80541c812001c03480007a0003800074603846481c00c032003a2a40380e0307103504051070541e10800542d03140e04005492800d000081c050070014290a0400f84240d504d071844200503440340030705040c4c10070755070140e2100300005015030749035640c440811100000030498407175403240e0080c0b18600101b807410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 700090000 1250 700088750 700088771
    0x1806130312020a0b1504110c0c040f02030114010f03020705100e0c03070812300103140607120f0b04060e09010f0b0d02010315120606031e0b19180b040501 68
    0x641040d10560200b29002c0c1911025049005c031650709446982c003039141c0c0d00c03855940368140f0203056480064401440c0e10310b0201c061004a031010280d0102c01801080184410048a0184140c081342803804022001824200714000c3c02100801011405442c0f1a030031401002d411040c07804002c0402d03103030700c80075038403c2550340c80c1c00e40b0510700349030806005c0aa107000043e01a24040c000c4c101a0103132614181d410b01245811043c140035240701040051003032156141240d4800000e690003800c10742418880504207020002c0080340240e02e07090b91556000e40b5070080128484060810b0080a446601c0b001d041d402c01c6403610035540c40e00e03500718451820750040c000c2410b005003a03c1c41d041c40d16001180a0071050101000c002d080001c00a020b030060304507280310a0041900003251400c600d46607d40c043c001003440d90301c41072a130075071740842c60303011980e41c0152581505400041030f036001c0740090000c80030410365511950020380c1c203112192400303078070480c49803000304401e0441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 700091250 1250 700090000 700090003
    0x70b0601030c09060305090f010204030605010e0c0435010c03200403030c1e14060703060f0503060f100b0f180d05030d23130209090601060c0602180613031202 70
    0x40c0900c0d1000542c0d400c07001c011590090348911f81044207141070f03541142680d2105070a81c0d010340d0007281c059545d107004000c40c500c9030b000641c003c00880c0d001498585042a40d442601c440a0f40c942510510910074042e02d40995040000450000003404800d520b0107014000b02100038041c1c20a40500c140440b00d05200c2c0c0c1107805a036819120690544d4440e16245030030068415021200c40c135103400c0c8408111042044c56902c06080000d10851410580050540e041072340030411880b0300810a11242d070740410b145034400541d148401c01035a58100c90145442070390700040d00c480700006c0300101800c1c50310040110f051702103208090400300d0828007180d0100c200001d03180c0d13001488031a1540d400380d08a0320b08800280c080750082000b641d07203240c002e04140e503200840c055071601d1008509100c0100c650050003400a456651300d0044050006050f4210081209600141d440b0706030000082010b5050400303018a40c47e0303024100c202680382d246010548150500f0488a03250030710 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 700092500 1250 700091250 700091261
    0x501060827010902061207090518010608060d060c05070605060a03030e0d03111204081b060d11120a0e12040302030a031b0f081b160515040f030503070b060103 70
    0x159144410507446108110041c03080c40001c503040030b54a03060b18001594494015200b03192400708003840a08107110040c2c01544213a02203401174100440d000304415105240a045452a042c10101e47d80c551001a101e500041c030014a09490003180c0301d081e0f58007402a09100d80710b040100300c60740b02c000030001401501c1c440200000e540c4051550a8203080c0c00380400644207013010707122104580000d9042c00c0720101c0d03100300c0302c002250070410610100f122021024482c503031100c041c4441e00108409100d2070785080b01c80f03a00c800800d0506458007088a1021404514030742d200e080014118001e8441c091104c20940b1481c0344000c8001760000440c1e0441c1d9004000b00310980700d0303aa007501c0c21000120346801945e9008180700205800c0018204500d105a409030764822400c843c2d5011030b403044806001c6640144513890b05601c110860105484003111010040c0940700105840d13845503400c0700d1000708a00100008104000018005086c41011040e17078503505c0d500114116007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 700093750 1250 700092500 700092511
    0x5060705030711010908030a02010f05070305090d0e015405011404050907030903120c020a06020705070b07030e0411090607060b031903050702120a081801090504060806060405010608 80
    0x10001c010000c000f490031981a4800c01d018109280c015503038907400703030441c1c002d44000c3c0c2c0540d44580e20010401446d100301680082036040400c09800c08408565907401d00c80184002e200a20103001000d0b0701850300017411202e000303030021003980118085c02d0402c0706926120141030300076015aa81c85c050140342e02d003014685669503504c40c68071004480450005140b825141d50420010035542c0b101e00c1c4152241c4c0150f180401c0c04800340c68000c102d00c501d441c440d100e051520002040c3d0581c0032507007400c0c2c903030800d03030158641d01079050a5041100c654850b511890000400781c0415401010700b0003500011182008000c020b4640300d269482500c403d2948840d0800c280400a00702c4d90101d6079080000e8110ba21600d84851503601629003580207030041780c03010541400f10300e42410306c0440215018007500c1441603694074604540140581205c6810000c08010003507403080b0001001040010424030070300f0f42d9000c00359103821043e82c8003405141071000201d00a400341503146c2c0110b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 700095000 1250 700093750 700093753
    0x60f12080d0207020402090a03060b0f0405130f02041401030b1e01121407080d23090d0b1312050a020d030b13090503090405180d0813020114120a1505060705 69
    0x1801540c0c880000e40c000f034022640300d503003481803802c1900d52806200146d445040001107030a18401000040030200c480244201c0c205000c0003e241d503126043c9281e01d40c07010717610042400510020b0701400070b0050075400c0007a40b030000800c2c8500300080a000e000d044101d2480b02c20050044c0807190002d0040c24144040034100c00001030365031580120f0034041c3c0b0181d0741c240740c0300c0c00303210704004035603030f05500240c0400c401c1103480440c40340c141c100d0101d101e00b1034644901d02020403451140b920000c0d01c01900741d0002058000c800b1004032403103501100081e0384c41c44400000d0302d146c0241c1000d000610a100f4444c400c1400ba20500458850040c14900102c0540800c4806044040f5080300e46000c14010162940c80714041c440c068840748100031628600601c08a01e84003187e40340200704044001409070203a20360312542012502880c001079500ea144407940003e10800c600c0d58000e0507104108540d045080c0c0c0500b00f06103600c2a05c0e030881c0e03540c0c03003044042e015600c07016007903 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 700096250 1250 700095000 700095007
    0x7170f010305120a0210060803030a0605030601030c0303030e12040b07030806031609020310170d1e05180604120507090506060a0914031c05250b070305180a06060f1208 74
    0x4154100041c04024a0070b05c101d03070342c9a450342c40c04800d4604680c03108449600c0802400f04200c914020017002c0c1000f0350040c07006624580324141094818400034041c0355640002c248010b009005130314050301c030003102507035a80c0d0b920070802e040d900030003080d40080c003810042210345c500400c00070681c001124421183e42e0170028050020350000d0b002110316101c0c10800500217020a034a44030941801028040403220307110040c1c881504481085001c984480740075440e60340000030341d500440080020307050168000c021801510641d04103807808090303042201e04014000941205440084c0018440d58030b42c0c805000740c43c02000d0804001c12034644081c40001944400001e084000a04803995022035003081030454103601915070014100050310b54455440148804060314007001405c40c0805d1a107411030000c001034050410151190017140213607491124282142c1d60340015903070305604c1881c008000b06954030540c0141442c0d50030001c1c50758000241c11f288030b9004014140f4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 700097500 1250 700096250 700096273
    0x20a0b0a02070f140321010f0e0f0103030f030204030804090e010615410a031109060a080702011512050c090c0714160303030606020f0a021005090402070b07170f010305 74
    0x30030b050420084151001388200c1203049024884003201075081408503c155041c80800424230b00c01e41c0001041d1f007409030900160741500401641102c0d0145041a42ca01000c5800c5000e0320542d800a03110010200700420b56510b26800312000490080007000741a50340d00a4410803400728482d030021420541c1d54414968421124064a400f10b03458514902d1030204100e415801440072501c0c525800301d05801c1082c2c140c0305544c0c1402e150641c40c1c1c14000c2c01400103402d44121481001041800c801240089000750400302c942c4148140c1c50b111151100c565148d42c1d4036004040e1918862801c0001d80d60411107242406140d00d060840e20305203050f01d0f51075100100d40040786451080b110349540c400e01e1001000003071403103070b43c0200d801450a4002490f00b51491602c0903250051401800142d075000121072145182d4100701e91104002e40024000740a0301001501d85806134080282c80303548100300c040d0101321204008103079200e06110085403042400000c059a101c54200b00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 700098750 1250 700097500 700097513
    0x2010c0e220905060c190206060609010c03030b0a080f0c0405130b0601090815011d1315060b221e030809040207081b0d02030711100e06040303020a0b0a02070f 70
    0x1d6007079a00030020a070451030790340300351810008407070300c2d440203a0105804035910314585c2051001c6802d071009101c503040c088002515485070850b807034140500b070f0b42c1e0f00d0101402a0400503240c0802001644403aa8444400e600c5105402803140030307000f032071220351840c0307032a00c40c90f401a0319400401c44110500d45e2895032070030010f003401f4103011081c280014550000c2000b0066241604655081c40d40740440340e2400707525088440030700f00340d08401c000641140c20500c00c0f0b440d811140394108a00280d44400040007140c00503801c1c0c110010b0b0302e01d05500c54250310304600b180042c9400d00640d555018040c0d1581e6001c0c00054031085660420206240300c018002c000002071005185c0203903595516003941c054180003006000c0182003048880301030000c1000c010b55400a1841c1c85015910109082c0b1503a40751846a5007003030004411620a04600d0039042014055541e220744030300740a9510603400c441103900144110001e0a1103d46000fa03030a6542e029106800f00130980d030340c10 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 700100000 1250 700098750 700098799
    0x9060801080d0e040c11030d02040e060906060d090c21120203040810020c100614090c1309090507080f100606090303090b03070e1302091305070c1415150102010c0e 72
    0xa810004000d00091401d41c090008204238002a400107969901d8180c0d074000649008104030300c2070400b401081096215101155440c0151803000a100100d61070b05602920341d941001550040040c5a880e00e0515024080000c5010312492101c210081c181286d0368405d81c05200340755045410425940c01150300540804102d00040e42d140b07108101c1640d046600b15409200d1041502c40c15498034240329a82c1d40d0003029110410345020b030301141d5003240d0006c0d44583c41c0380b241d540c4c05074001c0c44810300c2198090020402501d4000c0a801d849a541d0050307040b51503441480c080f4001038103402460b404c411260b2548501034540c0c03038082c10708840d4000410366024403114805030313203071b5a413000051014071003c284016100c0e00c0034400e00007282070041c00b00c04130a10304810711500c540c000e0b03280e50601d13901052219039101750707140983c14004012200c1618143e03000600000100000f4a100864401c3e4003c00031811002c001f1901c0003000c0c0f1000b5000240042004d010821944d140b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 700101250 1250 700100000 700100021
    0x23010c05030f0f070201170c03160207051309120509010c0305090301020d0e0d03150b030402040e1c0e0906030604230102121f0807210c031209060801080d0e04 70
    0x1e0728185551445205100e42c0b0003e40c11004082c00160b11046607000b13a14030070240f0100c210145a41303803000455140c0e1001800b000c40014840310071021a910800080000d001d0141242c0003480448103904087c0845100c2205c006864801c100d8034940b15009590441d42c1c141c2d103200c20407140c0d0300c066034294001109541c06540800c40c800d041101c82c05130020101d043c200078500800380e003c008080365a40148500e0246441030100001070707412042d00e4009404490000e19891034508203898441c10001e40505141d25040da58400340d0008503070541c17204260380c0c0d40e80075035900c010141c83d0340040310020f03d5510302100894a4840104040740c551902c200014901540350802ea0540c2600303c41d2034030f000c4540c18010790170381d01844100b00140620001040f01ea4140303221405800150700040f50080340c60701d00d5605010015000400841d001482c107110103c45180040c62504030f405810040345000c030000440a0000442051180b8940d9503840040c04800411000c1e1520707411 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 700102500 1250 700101250 700101253
    0x903190513170708010501060918020d02071703040309051002030703140f0726040e0c0a0306030b010b12153001051314060f0c030406060312030c030623010c05 70
    0x4000c65822010b5426001141c5041e0051003064940030103642580d8050304048208140ca1204200d2120841c100301c0300103200d44d01c0583c481e80e90300c2d01d0300002d0280c204040c110400e141800c141e850400302c01180218005c0d51400c1780c0940fa1414041b14100c00d01c9003500689c410400d90001c07a12131000f4a804130400003000d0310b400210034010019401050f0240c03820070800c0d040e5650303070f08501d4a03402c5007240d82590f01d00f030500c0c218a60000000081c912030f4040400651241c000744030341d0080001c1d5030312000c4c050300755840f0a00500d203600108054842c02c0218070101ea4041c196401c91241010018440491b92030441c1c204080c5100ca41c4001e058140e0344c41280620b180280162841600003080302036800000381403020064000090244103500a032003400319527024a002070341c0c441226188190381340c8403441c0c110000c01d01c551001d0400c1d04085561140561f064018018014003580c2c01e100c980e48070781c051601031801109036040d008900120900b694010018141c040d4002e90 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 700103750 1250 700102500 700102537
    0x1c05060109080d022b1e02070513090312060b0a0507020117040f0201080f0f06010c0809040e06190b06040e040813030309090c050a02062404060f030b09031905 70
    0x12503071904400c8110b4001603003000785181c0b04c0d4240000c3c03000f078240d0344186901041049400203000e820101d10700c1b01c440ca8245000c14081e9000700710f404010200903240c0ca03d1986a00b0700c120003840890b000b05e00107040313440ea4286000b054000e0800740d60540d102a071810304600d500f55019400004200e0501c203086050102901d100c21070603100c0d0b07000e8030707682c1e200200c01d100040c6a50b000814004d11001c3d18000d00071201c600c130000e254002d02c00e090070700f0781e15080e007017a0555000e50020b441d030080c00c01454448415012400600414600d01e60b080d4145803090303e0001d5a45004c041a007110052004102804241c013006401501840d5418a0003010032020740650b03140f5013090340803e052082c2000814681d100310703138981621f46061802c0550040c0025241c0c1d00182400c08810b00d1411020030000e00301080c0f1801d540000e01c1000603e07171f10710300c0e0900c1160790312003a60280280d40c00a0000701c804406c48032040f8910780390f4181940350b01ea040d0f900303030000303101d555460718203d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 700105000 1250 700103750 700103759
    0x15070206180102270a2129070807110109030905040f09030203090d03050c0304081b0d11010e01260103110405070f0305040f0807200a05060d020d0f02040f17031c05060109 75
    0x80809400b2000d20b8604245501003820200d02d40003140942400c245803403081100f41d41600072507660092348501e000101501c0b50f943c00c55030721000c80305070039241d441c1a44080030140c120880c1030885500340c4007484540500f542c0d01c802c5481250000d40980c104000119140ca00070306202c04181c40390030f0040c2400f400d07411151558200da005900d641c3d0161050102d8028044480003400004603040719079040c440d6118890b01103840c050b1810320050720449000e6a0080805010032080f40421000c100700b6640e0714070352444203100030351302d15500c040c00c0201400c050155901c01c1c0801d848000e00d00300e401c40300b100240b00080084d500d24610b00c04100c00644004004c1802c0d03805003201048448008403850310b6524865000c51040c542c051040040b030304c07650260380d07100c000f111005840710000d040c890043c0c2650f0794078182c1c85100040c042440c122000d080c005482c800a803598009041c890203c0c0c3d00d12540010a15480d04001c4580c881d0690750013895000c034062400c1c40005544 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 700106250 1250 700105000 700105019
    0x60102062a090a240822031b0b1314010204032103110307090e09010c0e0f01090e0924010b0f09060702090106030f18080f03070215070206180102270a 66
    0x105840c44c0014080242c0000413543d0102c0b9540c1c202e41102c420f10010361281c3c8030740e0702203058400018103110090048290005c10245450303030341ea400c880744540e645802e41100d040a041d40e2821035002d184907180e0356030404144203403070649074004030021943d441e8121421220b512000c1910826840300e502c0c090440a01010390300641050311203104850408030a2142010000c00c480c0d141d0b03142c602002c03203040e070081c0a0b03000c2031030940b0706640301112100101c41043c500d805c44800302c641c060a2000d1400001204004504030f00b203100c4d0715000008d0100901c01e03080c86027211440c02480400c100280c40001043c402c8002040c41c1d150800940c04902808002d904c887d0120380ea071111f81e019601c141c0607288988400080c4901c1159042d512041180101000f0001d4160b0120001d01e0140c001c0001ea00821642d00b401030301b40c070382410006c2d61003a04403030b16143d40e5280c02204a40c140b05001ba101010302640344004100194400c0c65503000c10135000c0756100c032140c0c2d0001000c154 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 700107500 1250 700106250 700106279
    0xf0f060614100e0306011818110114070f030e0a150801080d0f090b0c030909180c12060f09031909030c080c090a020c1f0203060102062a090a 62
    0x5140080703108502640080145031040d00e002441800030303190355040d90f40d4000c80c81c541510004007200001e6911400e0040c0280b002d2109407104102600c041d1040c03208040e40c20704981d10036628003c038151603e0700c10840d80510b40000307001e05840510f803c0024000e40c0240ca002c034014042c5c003c420303541c02e1059024001c10a40c0700105071018018001540148018401c521250270000346065800800500e0302ca068821942c1400010032500c00e00c00c824007c803518060010000283c50804200c070141c0b00319031900100e818490040700d000c1034100030011001e00e00c03000b00682456582c3c480280d5407600700804c42c40c11804100007000300340d034404c05400e502c0300e059650288080e045140a2801c0f454075082656039034400901014950760740c80c02c41d58040130341c40015888640d1424401e01d006c4003400402d0341136449040c2c20705d0840540c0c1c05544900740c241e007100c3c0349440c0c01e407090010041c42c41040303190851040c1c84010a41d481d000600528002800c03841489aa0302c0c0c68178021a0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 700108750 1250 700107500 700107509
    0x31203090a0c1202010809160b09150a080a0b03010603030906030c030605031c0201050108060603060c0f0d0f090b0f06010815010908070b07050709150e04020d0b040503091212070f0f0606 82
    0xd10f000c400c004e6582c821aa90740c811141d8004050f95140c007001d02000c0801c3d44a2600380b01d400003510764890b151000310007400844981c0c103a407211828500506000c2d42210541c1e580b03407408806e9000d074a41400364504403a015220f0314070040c03e0081c11005000e5004204050548620000441d0348080100707040e4403800c841e000c600540d01000007820b584040e4442413003603202405002c02c650300401c0e0503801a0317124084990b0313411541c160302030390f0140d10070701c100e2580340c07209100784890640c202d900410701c5094502c0050f55030740c042c035614010580d8468001103c41001820628011708901c0c1001720505010b07a6166482200c1c0c1c1c500100358108100c180d034003150103010130004000300005088694028040102c11840300c0340001a40c0c4500c1d85681e00c4a004607065480f81c4036410318450304003440e021280382506180f60b40e94131031582280541105803d100203e100403544071041d80c42c2003000c0e4a040b07010344588041c0c44080c08240d0b0324590f00450f03440020b0003403041c41c0c000d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 700110000 1250 700108750 700108769
    0x40605150a032001050304050c0d0203100e0a1202010c09060e0301021312020f0d080306130f150609060c0c05190e1005190503100f060b0f27031203090a0c 68
    0x5030612200f0480f801c907803980302c0e040c048180300b404000395000c40c091114150a0314070800b40c8050380000380c0350890340c0606102c01841c14030700d200d101c480851600900c03800382008010b541008c21040342246e10304908000001d25190007841050720941040302c500a0007030000d8145034011600e1010690b040c1c2c0441090000300014800318205100181000c80c4219020792000340c0c9516400001c3c480184450321402c0f51540c01580c17607455a11412000700c069000f04118620102125044c3c4490f000c0c100200b001280006007941c40f440d031000c0e0281e480f40100e8070507031622050111421940800500704410500c0104080c40040d24092280200c421054003007882d007400e1096642c0161084c0d110651800400d02003600c00041d50100b0400c450701c005104a000b1303080030001d1881c0c0d0410010350000042c80c000a03c00e40c0302900c1d4002c116440c1c0c66010820b5445812000c0c112400c0540542080c080544241400c0e0b01451344820700501355100c03540683e4400300704410790b8001e4002c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 700111250 1250 700110000 700110023
    0x9050c0d0b24031f0f18030c0503040e09031c050601090603152c060d0209180a2f030304080705010c050c1801150825050c0303010603020301170a020603040605150a03 73
    0x40e11080c0a517165a02e00d50f001006014810038000000d04403941001d03060119044c80901040300400440340104001e0749002400d0411061035074607a400768540003140400c43d140d0320321400041c4200c0d8043d05c01615001d55030361a000050f40070701088107549441c41c00030040050503451a080d0305103800817551f00400e888a5082c01c10352140c401811081c01882c801c01100d0040e101c00c48016040110071041c05118501804400e00c1c11b110180010594281c02e202c00c80d10b216250250f1100140e040110100701c42d07580281a660b009503c6440c000b0750142c2e00401455004444040904e1b00580136260b214601c440803070340c000102030742d001c00c448100300108134003155205070f800c040f211403801042506240f1010f0025084c2195001010240810100300c1c090084085412501e20541070b240c49607510000603000350000d100e40f0346031500881110398608004529120582e9006220904541321070311000020240102680c5640403120b60b502c00c26a91510002d0045214041d91800e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 700112500 1250 700111250 700111303
    0x20601050f130e0124080607050903210a17040203030d090305040e01061808160b0c01020412080702030606011b03140403020402131503060b192109050c0d0b2403 71
    0x4945030345c3d540c00600c051043d000703111800021030282d800007251300c0c05903203c0b014100020b0404843c42000c04082510000c1003042030741e071102070240343c0180c2d00c4001101050703003c0781c03800c044210350003980364004000085c805c020f40e52003219403038001d1620900b000e4031083d89006000d001e802c801c0c04580640d810401081225200001401030314003e040d151000070b4080200c484240111460380c0300c08900303080141d00c2507054400810240e00c040c0307410a507d0511600c81c2d80031500c107038020700894000078002d5011324164140242030159a00d820001d0b903c04880001240070b144000b81c0c0c00700320000260742d60380050030a00240c034000301d02161a00703001c007007404170041b803000c00e0500706181009640706000560f03080301c201501d04070201171310706001c4501b40792030400107486d45618410344000c1101d035805110128460f00032201004280c500700210400d000343e0042c62041540c3c001012844051000441c0032507040d00d10b1300800d01c084c0000c4c1080c403140340202c0801c0030044904c0c07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 700113750 1250 700112500 700112531
    0x9010b070b0a0c0c14030c240f0405060a0504020102150702030d0b120a0f06060902190e0312030105010f0c1205090a05040b240403080a081e07020601050f130e01 71
    0x30b0b0003121841c02040907840c44240a0500d110b0703414094070b03840541c134802d1880e00050089544003800101502c0040c02803800d00e984641100718404010911400000c5080580c2d041190040703800c50002c0900c1c0d174405400d0f6014101c000d204038118002e681c807034181d40c2910590580210555005107898620560705403088804088a0911801c4605d0b034a5008040100f0b145c8400b40d00652104040000e030706203640074203a00e0b0b04c0a035a8501c0000d452840c0d80300c0b080904820040b0780d440483c044503400415603a031090070f1300100c1c02130301000104415030042c0c41101540605040844031000705840d5107904201e01e2240c840440c00c0026010017518003010403030040c1c181200c04001c8065080c1c04a0504039000c06103c01c22400e00039500c40500060050720019940071a80c0d82e6200c45a1200401184050350304a00c40283d965880810240f0401d105c0e201d09550360003040c3c56881c01c000c208501601c5054150000d410310005000d0001a000355601c00c0840701c0080340b00c621900d101c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 700115000 1250 700113750 700113773
    0x8240303041d070e0f0111011409010207120806060d0b2202041a030c03011a071b090c030912030506010c020a090b0109060c12141909050a08150c03041109010b07 71
    0x11000c22050701e40300c0040340d0705d1038510346607a4801e00c3c206e5100c55400b04008e005042d0320701032001c0c00c0718035010042400b00540040214620a1b030f000303440d00086030401d452404007602c1196005906103d12103e4a40c0c543c0001c1001c08020075038101c210300b42e007440c0c2c4261880071440c1c602540000d028009410340358007180b801c3c455509a103144d407400080741005408103001744a601c950307803a20b4061031a0342c04103840006401816400044280c504030711030f100b10511445000b14100910f600c2040d00a1252940240d00610000c0c0e070030150740300c2180103180003406241401242d4803030202586072400003c018204031a000075021085200242c40b103006035000f0f90070081e0002c0d030070b40003441e0601c0c0d4184031102d03410044400481c5503241003050080447c8000181c144000384024603a0011030002241c000740d031040404d5888003c074507110325444079441d41c0c6040080104000544000055070310902a08038503108405040000d13698101c00c1e84100d15807003000c00c40301e09024460351003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 700116250 1250 700115000 700115011
    0x40c030f0b0f06030408180a4e05010617010b030120041203120e06160905011b0809060408060a3206040f0615120204030308240303041d 60
    0x54105800800550fa80c44003c100403c56100407800c1c2c0b5201c0060442203c42910060032071a2480d281d2140a00c0a0446226482c0d400071a07420700b04500d0540c0300040032500300c0b8480140e00658100003c07085e038001038045920790b50328503001610114006414841d03109160012070340b82000e00406094491403180203c52621452108000e8201501118100d8460f8428030501c0080780c2021f8811001203a9503800407401e0100d200b91004010405070300c00c0c4501003102c100b034441041300b00d9a10206002d52800300d000c03144554101040741c006c082c28035128604042c40e140f10a0003007015a0000c0d4480c540700c2d808103041c0044040300c0c6c01076041000d4401d00c1e411140b080300d600440c9441410003001c5113200b4080104109440d00c5d000042814500501480559599111036480c0301000311980d0008440d54003204800710301e4002c4404913505541d03002d02e030361903800341540d254032144e43c440c40c103003001103182050340c0b800e0028200138105541070f06400c03100040c0940c26424000c0c034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 700117500 1250 700116250 700116259
    0x230d0902031c0912030c0506041a10060807030e01021e091008090d0503060d020414012111040b0d1406040308011e03080f071b0519060903080f040302040c030f0b 71
    0x202e4524266000b10250202d43d116580394070f0300c2005041c00c0d1410940c0440c094000e0044104000a01c03402c00c501608040c2e07480c1000c1413030707584e0040c1541c0000060042d07000050340c9001007042c0d503100703800c000c0c2240c0c4118001860a1081e10043c849150280302060240401142c6260549815040380b11040e039641800c40c154900310701116250441c142600003407000210104c0c02c151101040b440c081a400740c010030501001d5083c2540c0c902d024454821001c220100002442c1d154481c01c0300710303079070003000458814421070401020b130440d00c845179040500c2003070020100d4803101d00c4408612003107018000504190030001c142c003105801200c050324034a0203800d51594400080d0044a4008180a44440c861203501e00144510705029081081540e0210b50361481c51480704100c0d0313021264034005000e03500c00a0202407140c13080c0e2001c101e841c0004c1001c90350120042c4282040314078a140b074103403290b00013021100901a1180084d0380d580c01d42002d403005100340e4003075020844 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 700118750 1250 700117500 700117543
    0x80c15130308130c150302091206100b0a0c0b1e0f15040204080606010c020105090a0f0510020d02061603060b0d1a121b0d23012703230d090203 63
    0x101c45440004e8070f40300f9144000c0224007103040315031003a410344a507400c0050400c0002c98407083c40c02d40d00d00003900c02e228032010a080c0041d010a0380400c4915140143d11002498250b68aa180c244c030b900816042c0090b01d0304440007503a0881c207080034402c031151440450941449403404c1d403001c11001d0b03010300440c41044148600203000075001d9200d0030901e0542000c1c0d0700c03440121182c1c041c2400c916004030780c51801246500000d15104141e0b181580c4c40ca80c01c05408030101e03a0713044040c410b000503070005008141e40f110101110400c01603a0300700494401c0e40c3c0c810081c0b09900c14001d180d040c681d40c5c02d02640104444401e070b91410400c854845d4464244002c0310703190080500410b0301615907007400b0181d9103841e1000c540d0035802050341301c9a0540501440c0100f984000b610810354a4292224090150b07814905402c41e010440a4080303403c43d5400e540c483c2d141c810b1410030440038002c0180b05650400284004019080b000c124282140b042c5464030285445444580b400341 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 700120000 1250 700118750 700118753
    0xd05010e0d020708061b090f0301062705060d2604090c0f020601081903021203161214060402090f040c0e01020d05090f01180f030308061c0f080c1513030813 69
    0x9080d4246c0025500c48800e07910074401c4001800c12050f01500750b010b509010000031300400820003180119940507103840407a480035503040490b0000c4400c41d03030050400358107030007181d00300002188003840415204042500410304040390b400690124004c280c9481c0b80a42d4140d12004849402c2c5c0180024a040d50614602c1c3e91106940c8441e105030401840c000c0b000c0c14800c003c1070011000d1114003d41d40d04101c80c41700c85a4201c0700b203c6010440c469114103000f0300310b00c155140c800004415003160780710030341013102130350042040d5a40910301418415040e600e9104142d00040e95031900003035100400000780c1401b000d01050340c1030040070b00010034240c0302c0714034107001203000b480c1c40031120303140e400b0258107883c154101002c03041000d500441007540111516001e204112800b08260454000c0c21540080a1000074a00d4403c00515400112040c0c06000e0507000350055810003081025101c01e0500120b0b0466519440c0d00601418160094030241d0010905485200e004049 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 700121250 1250 700120000 700120021
    0x2030910080c0d0603080a030e070602070504230f062b02060d061a070c05040207031b052e0b040501060206190f090f0b01050109060c110d05010e0d02070806 69
    0xc1840e1414000700400140381c0c1400c00007182c1c08000118420010140c50b4140034183d0703003115078030790080381c500700c0144028080003a04600b00ca040364010a485400c00f414400602058100d80064244004000d10300c140d0f11b00d030482c4200b200c488440c080d890100c0821103051041660002c800c2c1c0b00c00c50b0000e5946552610410464060303e00035139410b200c2c00400000d10b4281d0140ba2f001e1402c44040800706048802484403a00070010100020f0f02c50302004201c3c403031103030001d02241185605624000b10100f0014075980102d00b44c41800d1680070507440351142500c40b0005240c00c44000c5e444c1903155101d620b0044809560401079581401d04c0a9501c1d8009480780c45058002c020300c6144000385c0d00202c0418503000010300c0248460301d0700c2e194043c2003800072030380d00000f4800030503507511441202007291416a50210413100a880d030480320080111860b03045002000d620001c00c07070900802e040c0c07442c0300d0014001c0301400b0200030f04128850300300304801e4104000713110705802e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 700122500 1250 700121250 700121269
    0x30d0504032609063118180507030b010f0806160320030c0a030e0114070c08090d08040602060a1a1009030215040312030b06120720060a0c0c051902060d060b070c06020309 75
    0xc030b41c6c00140014072001164510841030002400340c490741101104115215030018100c1d0703680340e14400b40c10b40b0b44d14001e0302c43d0303411503a00e01041d4011106040552280c0c000103408040700c0c101c08140c1102000602d940e5008556110040c0c000040c13418050b0380c10300c9120407440743c0030000c000801c01d40b801e001e051840502407400704488461200d05004800d0100d4014040080a0021550846c5403200c0030b5086841240013502800001800c000c6141c0103030030682c0c454407441c03007030b4400180070807503800c136a0360704c840400090b481c0110050301d44149e080199170f81516029200c0707140d49440c00ca001001083c9404050030705101c50b001c5c1c0c64030000d0307941801041c0711800580c0e85181c0700721400303041d0030722928040c403070351100c40c02102010030241d00407907140e01e0520240e401a00705607034254038228000c26613801250041695101c80940040041c03000f81030030714100b0000030460641b03000c6d40150303150a60018240040140c02500000100502d001039401d0480000020310f0f40035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 700123750 1250 700122500 700122539
    0x21f0807020f011b2a05010603120201180311160909120c0818040b040c080a0f0b0105090d03030e0607030c090905040206030a0f29030d05040326090631 67
    0x80b03017010400581d0101103020704100c002009051402001c1d09165001c0c100360720050b1080500d40c0c114540a0744107000d80301903120f041c5091103401c61603030390031140081c520524140354040d400c0000400c01998000300000c201d280d00104d040301e030b10f003005d80c0c101004404280a1105800c4548005000b40c015260300d20013082d80c1c1100c0d034940502040190071355580c00d5600038030f0300c00c0a0001d5904402c0c02801002d00c41000c1141c84405211042140c0c09000101c0c04945d080c00004040d00e014515800383e148a0f140c0450458100e10794603141001c02d580704d001003078a451403400c0050b8004001002484612803e1121f800c141e0040f130703214880a440101015100c02c06851040390355040003440184d01918100c6100106528140440325810554424040c5c1154410154454019a81034275000011400c05580019018070350303541450036009071a00500c0804910394032038010381044c110400c1d41038038030515070000c0c0402c240561801a04503c3c0320f0028030640b084a1507503015003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 700125000 1250 700123750 700123757
    0xf0d080a0b090a020711090c071401061203020d181a0d091205130902030402090f1b210f040816080d0608010b0328030309021f0807020f011b 62
    0x589034203145502910a03094880e8019002c08207000d0007800300e0303004000b4240540f40c240d201ca211001002603000d82900c0009208005100c1c210200301e4088611078220410000002c4c500e81d201c1d0003481d40030b0f034038100713034007503000881001c141540041014450703c800c120803010940c01c2245c41200c00b8801640d00315950310108040418107440d034031209003650481d0010840007009640201294424406001c05c00e080c8130000540084600a9a00455000700701820030398809410540d20b000040c12090428009890143d00c0c81120004010300040c0155017640c1d900c15101c1b01481820107810721418500d01401c2101048280707080e18003070b1500705483c002d50b100a04140906002e440c14421550b440c02c0400210b0000550191a5000003601954100e907012241e165216201c4144203007410085003041002078401ea110352840c601c020664450380700c000c0880c611107070710601000d011030032140a0210854040010b0080b4042c4c0100a000042c5005425800030340c1441c9800d091 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 700126250 1250 700125000 700125017
    0xf020304150c1a0c04050103060905090c150409020414330a02070e0a140f130b0a290f0f060f0903010908192d11031c060f05030f0d 58
    0x4010071010f550300100104001110142003401c00341101354094402c0d280031910b001d200180025547c0074007481800721101414800c0c03a0f00060104203442540e412000702400c11020a8203500d920161024205040d9850184000703101403100e40125840f030703603c41034080e0f20014070302004260b01c4500c119803000319548a0340724070380aa103090b8842e00010301c0d100300c5100308a80c0340307140e038000740741020008900c01c00c0352111000c1041c0390806803100070300702c40030240303c8010450503030b842500030b8001040022920786008441152031034640d640318012510f400240f000303203051071805d40000c1c2c0492b4010201440c1e00001111071107003203554404480c000c21200c405940a500003182180c001200076030351003044140301c0304200641c0d05da2000c03442201e800311008040942a25920140440000d050269000c0640d040b100b50072030000745201c10440c48400320707a07005140c07540d010303110808950309003441005404880542c200502a41c0098102c10a80c400001c0004805c200f5040c40f040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 700127500 1250 700126250 700126253
    0x50102090a080a0b0109022713060e090c01031a0f030106030c060c170a09090906060b1309180807020d111e090a0e030f0d0e0601030c05010f020304150c 67
    0x640590503405a201e4a44100001c0000001c1981c801e0030303110b0f0310710081a03a00d595981c0201e014013000c070351a18140740d0002e00319000d104490b5030035075001490f0843d000d5000c90345206440c41900301c041440c48040600c014030f41c0800c400302010760709003010b210381901e42c498021910320300b005c0c842c81517106c41a8001a524294846400341d5004004000034548560f40581454a030840c1100c148180b007980550241d191030558041600c035942da22905443e02c940d280c00341c0112001560220780c0e880c000180502120010888511202d0010701541c1c508811041260400301591000210700da0f00b013000660020f0407901015030440d81101131071400e043c02ca50341c0d020340382c48036005409081200e17140703a150000c04002040407940740b901d035582c90101c2c5054801781c83c06003080e035005102d10003072615200050600b100c9485400920003c0050100c1d24001e0f00b0ba0090310034000e02181031080d564400300f103c0010010380002c610701803510042004401ca00542d0004014040b4900310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 700128750 1250 700127500 700127503
    0x1c050108060c1608280809060604021803070f090b03030304022107080105070305010e01080d1d0f0409120305010b03040b19020c03120f0622090c030b0f040611030402030c010c05 78
    0x41543c0d41290869443d0180c1000003980c8442102844030015041c5004ca0f00325489002d401c0d1003414814090012a00c61800344000380d0410800c8440d40e071450002c6405a49042140310020000002c0c00000540740000e24070440d560154030030300a4000300308100258039850740e40350469041c0352a213400d8640000c0002e08150740c07078000514650a150500c944944c1c150001d074142e4888820f020350b1640d941680c6d55640d8400411075011030310580720341c1111082603d0f49400d0f458050000124019410700040860344000b030b04480c0d11743e101da0041400f40d03041c4105405000c0d0300e14586c1c1385003020b031101c4c00e005000400c4c05030311402c00344039118042c2e115015500e400303860300210790700c804032040400001881201c0400001030507200044661078041c007030400c06404040d0001c50215080607010141001c070340266507a0402982c008001806050b4442c070032036090004200505140c50903100742e80f20604060350140c02881400b001d40e034003054296483c0302c2400d000001981610380a07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 700130000 1250 700128750 700128787
    0x5011d060f0f0301031106030103032111070c030b010603090302030f090d0f05100f020313030e06040b0a0210050601050708030f0601090512010e0c090907051002070803030c1c050108060c 82
    0x540c503101000c02e0a100d280d0340640074506031381c480e12a820110000310144400c0e40002d200240000310190f01d00c800321804030342c0744001c100340c284000c26824086032002c8455400464101c1c0c03a031025080c1002480700400d901030162101c1e280c180500b11a541300213549008140003009242400500030038595240b60007544242e5100d9842600300c285410103540721210101c1c0000c5140c14400324500c6406544200c074440c441481203415200c03141c0c7c5044a031020703800325850300401c0c00c00c804210400088041e03c15220143c1c0140000308000301c0200940d200075180c04d06000301800104d0001e1082000d4986c000d500c00da88070389075542d02004962480580c2d0006810405401c031640100b603040d0003e140c40c01d0024112150000d0500034400d000c181207802280b6038214880c144043d181240b01c40c0b0b0481c03018412290001e890f4034182c1c0c210303881642d03007490403040092a201c0e40d0201d6220405011010b200030056989040422031b140c1d80000d0810078003881c001030500940c00f072510389 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 700131250 1250 700130000 700130017
    0x150b042705160806091b16060e01200a050304030302030c070c14011808100c120606020105060a12031e0c0503031e181513120810060905011d06 63
    0x80c4840d0400661012019980310b01400004502c2c9001540c28285007501a005090300000804034a800c41d8000c0115080840343d0210354260b0b545600205045004290040c59200000160030700142c407500c805001e44040f012a071101408001c0c1d240c0d4102c425a58400d803d42000b42c0d50340c0e0b628882e81c00c9441030442c01441e4903006500498944402901c15044000a80f50300c000007c07400b0309070080016500c240e0a855010894248a50640703170070610a40c07815042410b0022408800f440588025400c0540183c0d510030030000e0a1501110b00c800401a07034040e0841c46185440003410078090040c40004d80384000718074500c2034410260059610b401c03d040d40e442c0d007004581082000b0118103842e01e4250340c800451465003000035002c2440f54042d000301a10301680b10b840550100041070241c00c241407404a50102c1c007804210b60070743c2910364442030140781050306542800c240d034009030200300181005114a0342c03c6490b00181c4015201d40396070075400d0000090701449407012 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 700132500 1250 700131250 700131329
    0x17060a0207030324090621080a02031c0e060f09030a1d0604140f030c0604090b210d08090d020c01080415020a0c03031103040b07030906090c080a0204150b04 69
    0xc1040b04d00250075000d09440d503210041c8400350352604440340c182c0d0a1110841c45258039084000007668050051560b0106801038906042940d024a512010346080003509552903c01c008029041403021980c407031641c80c03210001e03007000b1540655a008a010311000e00040c01c03240c0400300c0100100240600e4000c0c04940d032540c44c2d000307a044111890140900070b03500000c102d282032a004c601d1700c0d084900a001c480c101031030140400c01405609540541140400c015211000042884807014107650380050548440000300108005802400301035607400c40426240341d40e80c04564510707100c1e001d20b000c00080d04c40c0d0610000040038101500030842c800500700c2e004c076800c2100d4510349070090720100700340d442c2e04258004902c02124018030701c200040008140c179000e0781c045014540201e00005501d90b051395003120804d1070313400c000c403507501030b500c04421481c0c103010f0602080d00d5000513251080c07511070328000500039401049501300c00710075042901410703600c2d00e60f0800c10445 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 700133750 1250 700132500 700132541
    0x170306030705041d06090703050a080f040b04060903120801030c0b0a02011b020d090e0f0f19091b0f05030a110d1b09060e070c02101413080717060a02070303 69
    0x890269021344d0041c0140c0c1c15008003000070301d4400d004528801129000340c00b40c03040c820703c0c1d42d40c0d20035580040e454800507101880003150003031542000e08050802901e600e102c850a40c184400e0082d0101000c2e410094044010b00c001150411004219600c0c03111450319a010b24000b80c1c007400b01c50b6411000a40559001908254002031030101c2004a0301c07080c141c2da40303c00c184c1c04e84110840d0801c25802d03815021070800080e00f0f4419501c0703100140c02d181c4c2400c841d0b54500035501e10140a80b0500445002c1d0028109402002002400c0720080000741c2498034001c02e441d581d603d5009054041040002c01258075202c86170500c44c1e900c0100170404414041c01118581c14a004d00200c1d01e2802c00013140d260540ca0340513010303546030b44813200c0d217880b564200800d10100c1010f04080220241412010b071000c20b01505001c00b0001e000e00c3c016091028080c50110b903a80045160351140c0000121500e0100b480b90304420340603405a652011400d058000d000324501c084082d19805 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 700135000 1250 700133750 700133771
    0xf1803050d062d050105070507120206040e090d030b0f030c040b0d0b010801050a11040608062e0206041101030b2107031a04120e1008190606050a120917030603070504 73
    0x6162600303d41c11075168a0b5062a200c6004440b1801840b100910550103013100380841c26900614401d45407000b044146041d4950000440d00d01c1b081d2091815a8011000001c40c684c05006000075000103407045400d4071150710000382d8034000440030074001e980d108040c2141d92070f5401c8021266801c51101f11555940d504118001c1c4821103400c40044c1c500380f900500e080c1c103842198103e03000c90380c40321459110326041010b144441004821007980786004000c20581d118a0b203070a0050a070040c15441c501428621828800010700034100752030301c2c00360140c0350798600303c3c1104003010030351100e4024580c9a03490300d842d50315080600034000e81e40c0844010310801e100184914410390505100c00c0d4100c400382c4409034404407084d48028190f6404204910800e01c00340d1090305041c08902c1544000580c00840d51540c2190300002c0c00062880900340d0043e020304020101e000040021103d180c4034414810a61074054082c80000000300b06c195800704010000740000420400904003c1c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 700136250 1250 700135000 700135049
    0x307150804050105010b0f180d05010e1f110f0d060e040f14010e060114010504030c1415040503030901030915050a050604110721110a05100f1803050d06 67
    0x456086030700f50300701800811820200400c1e10505404280314a0821b455007080072014050f00c411150041c0c0c5403541e46020030400d020f401c1c000e00d401c0300030746121112596100c00e1002280c45529502e030904102503422642c1100722543c2445c0903106548a0400000010107011594004403000700d208040c00240805078000d0301c0010300c617641ea01d40104010074280c2c00c0e16011b003102003d5802040041040148201180c0340904d4140b400c986071649a96844420241b41c1d04005c08015000101607028240150b501001d80c0c0b14121841c10a032030000002e0392480390b01c00a9041544800c039200800c22206e0003041c1c501c3d151a818010783c40c000c2c403a800203120440d401803007641810181d40030003070010704583c0c140750801603014005040d00d082641d0300f0005041d94082188909059054034428020220341d184100d000d804581f104c25150800c0d225070740c060b05686450418455041070308004004800340d0315040c0b580d1600c504040c210000e00031640011107103111506602011402c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 700137500 1250 700136250 700136267
    0xa050a11010f0e0d03180504050c0705010b18010b0d0f180210050c03030604090c05062115210f07080c090705032a07080d05071403070207090b030715 66
    0x8282d940b040e040003200c0d002c6800d61403024a503604120790040f1207010030721900381c03180c1e0040d40141a9413503a545001003021100d044072807003c40c040c04181c003001c100d028010740e2910881114000140403803c40612020768043c07140c803200c4840001c6410f0340703010a411042ca03016080c8010003400d03880740c0f030703001d102c401e81d900032840381c900080c40e00c060030702172401d03158090701600007142140d45c1c00f02484010501c41c1010b8035003c1102c04c0026951780d8620080c06042c1c10003040008a41c40d8031650580c00c2c41c043c00e15020800806091201912034064100305c040410a980c0041c0b14260200303428030005203004a4240110100480d90900000d01005102c00c2625802001c0c3c0d03850b00120743e0742c00b09032071084040340c40300c1c98441c084e42c00a6641c102150b4003500c0525100b06940d0302c0f00386500100c01c000b07800342c442c01007041664001e2440117080040f200c0c107515614214800944401d0b140c0202e0804a517140040c0303006403410896840270702200340182c1c50b2840584800303000100e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 700138750 1250 700137500 700137533
    0x2060a0c0b1018090f020301112805090402070f051b12060606030103081e0a090305010f06062a0b0406020c071e14010c02090a0e0c010503160e030a050a 67
    0x2400d990208030810003100d105001c41d43d0f12018030701d903c0c2c1c0481c0084050108140c1c00c0e148807903000743c1400540d8007032183da03408543d8440d10076030b1101d0001c00c00b078000c050054141d01c00a600b41e41104006d030410101c50704c490341260b00590b00d10700c0b46800d9400d08400c0401800c2c602c40c8244140c03100380345a9001e11303210402c4a0321900c02c2c0012402503071355002160280c2e0000c00600042000419820242c14417000100d09090340c4003141c28a041070f0381041000c040002d031001c0d02041808820b100d02050120307916400e01c88036080190103000e4180300e005918844500e1440c9a240083c40c4c40407040c8550700101005860809051400c0603400070b62000410b4081d48038001086030308071480e44640d0a900d001c402ca4035140c0b441d07280744181e20248950500c5000086900183c3d940302e0b00d00c0c45490086800104141404443ca281c1520030441c02e060000c00c0040c00f0503200c54011000e288a01840c2c81058030724044040707401d0040c19500100644101144401001001c51001013681c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 700140000 1250 700138750 700138763
    0x16080c1005090f0106030c1401170907031e17030606040512010b09010806070807080417190e01032903010605090f0f070912030f0203160305040f0509040510020306040902060a0c 78
    0x3040b203e038980303003207503c40d200c010b184075010201001107a0084441c201c600205051091b09411624940341d12a0021502000d280d04a00d100340208405540040611078060b2068200c48940390b41311146240d115201011805012000504640d204c80441d005000064001c080681001c3c00d228041c0504801c464442c520000000c550300c500000d00d1886060729690300403158490460981d40401c2c080d0003600c0c602c101d50707401642003580c03400170070402030500300110050030341e00002840c00c50300c20074081c10582801c00844032010f8550318800f220100314007032400301c00c074800000d004000e83e03400181c10011540c20032032010081140301d445250400c904a4440d91508011101040d250055171106400c9030300c1c02e00401d10a1100d98070000042c0112490060610607555900300d015104400140c400034040c006401d211007403200030003082e58080d6103414a82c2d034035500c801c58003040904003640030000580c60b40e11900200c00c03da8000d070810303030796004200d0001c05c220140320065401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 700141250 1250 700140000 700140013
    0x10f06030b2e0911130605030702010606020601081b0a0302031e1204030b0c2d0a17010501091518030b0105040e1506100c0b0a0507080c0403050316080c100509 70
    0x6040d20380e10360b08500322054100900850610300c24600816000c4450755100310309100c0586540309074a802000b0f0246a00e699403603241c2000020b003900c0e0329070042c2d82107401401c01000712441c0081d601c1600719060074207010b807031096004180702034556400a903051083d042c000c513008041c40410300c03520400714203030f915034007030507648800c58400c502c00204403c03540320010703a46403040000741c16a41d03080381b42c4000d001c081c020748910350001d80c4081c00c03080e0300014500c154142c002c2c0240205007000c55440d0328941c5480000703402c0d41c895105212442a0711170090105a105034820031440b980a091001c1003601d90800042c14602401483d02481c9001c905100c08800000e0b9501c403a100c3c070ba0f0800141e03a0b820f0a005040803a18402c00a010189180700d00040101c01c800340300704240c2d0400074a030310f01150010a505408ac01052503400d0800051021400100c11604034403108a117202c611103480c80c0c00540c610800341c2d05170380b42c001ca1041c21040341003908254004d40304c40045840 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 700142500 1250 700141250 700141291
    0x3041203090b0702091305150106030510090b09011e0b0414040c210e030403020d080309010b0a0b030f0c07081602242d0c01060501020d031a0111010f06030b 69
    0x742c034840c4010180d070000402000074010b050b040b102c08401031095050b994401c800480d40a5414000c2e0040c5001c261110304200c0003201c054a41002899000f20902ca20203000001c02c0341d102060281c0120110b06002c00f0b40a002442c2c91200141480160140c3e15940c4140140050b91240955440380382421400e00c41c10748221200703040c042c4004d2040e0003406090316240e0007402c00c1e03150440035004c24007000000d40d07644440204560300400c84a60b40c0d141142e045401c45540d83c0c141440b540c1c01e008148201a00740e0181c0754045078a0101022603154040b00b12968000e00e00020101100001d4200f003803000060401c8200b8425203504440c0f0802e0340300b40c0d2090074905800503003a031060141400e09000700c1090034440099002c440300d000540407400c16103a100c00c0c0c80d00301903911050100180d5a0400640007000351318601080030510783c0301e060249a1662207502c0c10001c06c8801c251390050207611120040030501001c1094541c0d9150404900c2d8046905804030f83c10b016500c00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 700143750 1250 700142500 700142519
    0x23006060423070309061b080f0c04060c0b060f120f010608120a080a06051f020f060709063b01020c0402070b0601080c0c01050711010c020106061b0201110304120309 73
    0x101c07841d014008111a0740f400d804030024800e10b0700507a040c549561190000b81041a800506070985a882039510314100210345a215030142043e01c2e240c8040008120507544500c110010990140100c00d160311030f80c0c002201452401c3c0d56a0b40500642414042d2450000b0000c440c080e44800900c0403035564103043d621049107603400840400b0800c143e208a40c440d84401e64000d185100c0003c0a50700c803000300340c01489080c1080280c0c03a60460380440d26030100038004c140c0352010003d2072585845103000344028842d219103801d016050205c1d071120025076040807603100d0b040c02c3d1401ea0144c80c201d1300d0f0420b485021194090300410010710301c0350415000b100c000c6034101c02141110f841791001143d4a00c0000c107005903070300062210b003c2a520070b01030300d40140080d80d6100d48010b0104400e0f030031654110b5070042513a00d000400c000c8036800000d2810540c1501e020640a45418001a205550024000c91190000040200d0292014104081c481d80266500b850700da4031000c460 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 700145000 1250 700143750 700143791
    0x120210080106020d0f030f0e03120a150909060f110405010f02030403080403081c1407030623130b030a1202070b130e0c07060515090a02070f0230060604 67
    0x4006801851301036090a0040003c014144040c5c580040c0c0485400035210850300c254240d07210540002640700e211041c0380d00e21603082504802e040000c51082210103107844040c0c4215403000d900c0301c068506105565100c080310100d01d40c0e091010509462200c3c502d940a80105800b0445c4139405100c80e42c4004143c40940c0d50281d0114074040c2142c65400a64008400b084200903910244200d03100c8a403b501120340ca07400c0074000207090012001c0c083c0e4849801640802c5500580c407903501c400b608084152403000d170341d00011040c410201002801441c0016601881148246010015084405410759880d0b07800d41d520300e41c565148020500c80d05080002d5105400d04c2401080c00080a0300d8004044044052505c3c520b40d45090a03500d04903614405500e400d25590b4107802c080d00400e910030700a05045180c80000c6da24013404519080c0b01034000c0030a014106124040030402050b80d40c03600b01c40500e80041c03030044a550714821205940218140f6420130404903042900 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 700146250 1250 700145000 700145009
    0x40606080f010b1e28082802012106030503030a0e060408031807050d1a01050a120b06060705070305060103110301020910110a0b070c0c15050703080a0908041202100801 74
    0x1540c5902c4c503814203c002818020b804c2e65880540160702d814004910f1800e80c0c0c0310015174003000a0305203801690b03404c164039000030b4031081c122080142440c4e00b01c04101d00700240d09007005130b1003202e1401d80541361912b0003aa41030303ca14140c004802c0c054004081d610a0b241c10700280304c114154001380c3d495140030390300240401c1d000e00204042608144842d1450304c150310460761100d81d104001035001e08020001d948031002422041d42d41c44034128900d0150030280d610b1601c1da854041d542004943e5404040c003030900351008038040f81d90f50b500f03c4003916000022602e400351a41400e0751100000c1c40111501c160094403a070490030103000380c0d000d5000090034011048140300d42a43c51002240503810540a03080c003402c00241e00e403040d076009183c15559000102070318039220b9485000d5801c104900c0035298027560f21030303a1003001c032180e04d6030629241601c0c2e00e401c1c040d40007810b541e030402000d901d004500401c0090f9020040c41e03043d8000c607040c80c1c082041c1803059410107000e01030b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 700147500 1250 700146250 700146259
    0x2090f1b04062109030e0d0f0501021204030e121002090307051809060708061c020f090f06010e0103110318030c070305010f050109021309050705220501090602030a35040606080f010b 80
    0xe1104030703031810b1069883c81d00e0213a030100b45401d202e6a04c90b2b08a82c4140000c03a0350600741c03000d200074580d00060381e403a03410040d5601d00160342d040044540e109400c2200921664001422500c0740e1030134040e0000501c0e001e04621902d01304004485040a8100c8000e0400d108400015010354031844a035402841e0160030069022014801e04941049440c0166048040c3d941c83c0380007910340c1120a0320495034034803c283d050401c000014184500e109405040600f00385006441803203a60443c2d40000f041014554161301c51620103065004110306e812443c0104030000040c008190859014440d8222082105a8a40054000300d0040ca01038140d410a00d440c240051003003944100c0c1c029580e814400c2c28851095481d000c2052020600414088013603800c100550300b021409024000500146082c170803030117002005585001d10104010100c200c0240944c5c00e40c120320317400500b5402c51601649080d041c048c01a1540e44541d0b61184100e21100079802070600c40c02c3c074603040040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 700148750 1250 700147500 700147517
    0x3160e100c020906011b0b06130b01020304090c0c2003010f020a0f12060506040f08010c08040f080307170115020f07080703020402090a0f150f0c02090f1b0406210903 73
    0x4007032000381c8000030607050511081c1042105081412182880d000e4442d40ca0707c0c080d49000c006116488900d0f032401c0290318100403c0058507138012007074400341d540c00342d40043e100c9909103044905c091607803406007592001848a00c001030402d554200000c82c268000c2c400c0040045000081b07110714259030b00040c10500300141154492009c80001c101007540c04544540c903640000e040303500a134080f9842d00840c02007044000340c00e0051034803c06250902c542d592070030f80c86440b4a000120001010f240c00000043c10301f9000360a01403541c1610b090600d11507858098103800d0100003070395078015201d1080241400b4100040071019241100c0141800303a1130342e428013010703421014101d54003150648010840c0c990840b040070051000040c072107184d0f8803406c0050b005412131030f0811f00708140c1441210160301c540ca04590060984440003200750b0382e101c100010301c403080da620845c0190001c0c4c0014642d0703110185002071450380c10408880d00c0111100c804840035403030000d01040c03449 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 700150000 1250 700148750 700148753
    0x152a020603070e040605041805100504082a0307030306031b0609140402090d0c061202030f16020c0307030309171501031b0f060302072102060c031b03160e100c 70
    0x30300f101c40c501c800140002c40e400da1520001020b88240f100c8103400011040600010720000b040086400c9015050030445414161074011441c468520348040e0000100a460804d6100000c2d420f9610810015079032105401c1c60010064107082c80161082070b00528406014070681c3c83c03c104883c2c4545408a020b880d10000f2001c111400c50130365803043e8240b040d110030fa01c8070419020300707074481d01c0d0320f0641c141030020160001c0180d160b010003c40c4144108014000c481000642240b034800c0c0022004d1a4508100d18003c0d080502c02d40501502e0000820103420407a12425210088150001c400c004c0040c1c0e561a95200060b46136610000c0c01000810088415210340c0d19450650284640c1c85241002e01c1101960206002070340c0018081d00380507a146240316150034400f00031550002e0688020740c0d8400c00b4200407001f00c8000041045244c1000c000110100c40d003031b190b074592821a030480141603101c8444c90105014420807152881d140a44421880190b2a030080300d0110303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 700151250 1250 700150000 700150007
    0xc090106110f0609160602070608060607060f1802010e010309110f0d0c0b0d0c030608060420040c020a0b01140d0611040b0403050f0c04022a010204152a02060307 71
    0x704180c00e00501034079600e00d42c040d10521410784582103100c004c0c00129292401c600700c0302e205900c502c0c00c641009105004250f171210545070000f404850b40e6894141c2c034244180148200d01800072980d14040c44d00c1c0d132000304150f404008a000b42c80b8840c001d1903e200550586881081c014890041c0d8003200400c1d241071440c8138030701d00c806030820086090725a5100801c40003500044c81099001c26040248001c5000e4a0000e100e01d24041c805285011580f90b655000032b80000d220141401e040d00d00308000c0b4405503c040c1e0300910901c004030a0b03c00103500d83c5118801030350221160000400e209805a09186906001030080ca07521041074940b100244101009030100f44010000013401040342d0003e4005503001d00d016280c0324a19004c1c540c03600070300301ca01e60700450042c4100c40f42c2c0a803811003030314200d07003001d000c003001c8128030700305402441150801000714541c501d40e0140c9903072040c8541c0096045080840c1564038040000c40171010224009500500410004481611 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 700152500 1250 700151250 700151267
    0x60b070212100c020f1c08070e01121533180e010308120f011a0c010f02030106030209030d05030f040f030309050a060c03061a0d090c0e0f180c090106 66
    0x104102503903111410b071008041500c20200d101c00040c2d201041c801d0445a050104035001501448242554485010b010300700707000042c140400c0c00100280c4080c240d0050a00703070340941c11201c080001607107500703103000b84100c240030b600c0411583c40101940380d000301544009200f407840a040d541c600d00c003821101e40c00205910b82c02c005060034009807a000d0340680d980a107100f03581080e2076880d43c2c1c41550300000014801100105440300400c0094040d484150072841c0403d411030760381e2040c902c803e000d084203006168410741300100020f42c45a2560140050311000c40980d00748120b030303c00460b000d000c150b45100071000003101040028040c50356080d0300c10711034100411030340c4094581c51305008094105444c110346401c00d00e010300c0c0d811310942014020042c802c000202e846080d812041c042c08281e010311a540310360384424402e0170b6014500508840d03c080ba440c0c0303080c020306024010103881800940d8040039004140d0200403520f036201f102d01901052003a803824404032050700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 700153750 1250 700152500 700152529
    0xc0302040e0f060a08060708040b0906041a06220507020d0f0210020702130e010c0206071704060e0c19050f0a05010c0f021f08040b01050603013c0305150a060b0702 72
    0x50400300001104174003032140d03d226454984440007545068280800720481c010702107a85600a0420440050800d88030703c1d00c02d5017196195080d036030340e05011400a164030b130700b000c4c19444071005071002d2002d590022403003003019900351440b0000d004010b4505d408503104400c050703000300030b00c0c9800412a502402849000420352402c1420458406040b81c40e0302044082c1a5111980b180710103070104041a00180030303181001400c1000c2c1d0544c0e5494001920003808152207122540c0820301c05c02c40c010415000601e640540060520b03003403c1d05c0034621906000ba002c0c42e18042c124035080481d1000c4800c107071218480340c030480c0d441c8001c1500010040380c0c411544002c002c120f41008060140302c2c0b030135445203951410641032003a10824140e100b40e00c9400d00f0401440700c402a045c1d10456001404580e40f010b140c03001c0b04500011408860201c50060010000180300c1c0000f92083c0f09001110541070644a1076120415522503000e40b0481601c01c200010060816034025809030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 700155000 1250 700153750 700153759
    0x1050403020603070e18060307090915051f0605030c031306110f040e1503120d091703010e070201110a0c030203070206030a020c1b1c050a021306090c0302040e0f06 72
    0x1034403540010300c56001076554000042a030314451000c0d00302403049602d828610000e1440a1510100181e620b40e120b02901306025200d440a1040200654034290411032103401030006103000d91a00b9100541e518001451500318980061030500030703821a0f02a000c002c840d0751031070780d40185115450000a0003141d0701580c417410300d13000d040c410f0042e045030030001501c150356901c0c0c5400081c2c4014090058004030b040308200302c0d86036400003442030a0311079140c0041d0f203400444a0000041c00510400341c441c030b0000002c0784180e488040214142d0700e110804100e1500c484600b2422189194403c03070048408008004485008080d004071840c0300b481207030720700001c9502151882d0001e0b0f0b95040425000b10319072412039030600208207440b800318501010003104a00180e00202da980a10742d084170359044140c01c0c0802071040c40da030700d138001c2c0049c00241081540c000081074544501041a480d0aa0560a4a01c02d00844e4100d03421183e0200054032007859200c00c0b007002a040980c007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 700156250 1250 700155000 700155007
    0x6150703230723010c02060c070b19020703033206040e070b04142d060313060c1e090b030121140601080d14031501031e05150301290105 60
    0x24003003101e500400e103004102c900c1003141042d043d03420b507014842c080055400c000e041183c0456200180d40c2040d8120601c01910784503544002031613028a01d880322104d00000e850720500d60140c001d60510314404900140c04010107941a845949805514154840c0720000c1151454542c01129803c2c0c0b040080c1c80200d5a0381e042d411065119074482c1c20b200c0940369940d01d1a180c0802004c004480b100c04206543c540c052200c0c000c008ec040b0514441c19010011400d040c0c40c04c0717000d1300d40c19403000742007010000721880588040c5004000a1200c0320540c144047c0c2445402c40b0403c66030f504e680075003142d0078102008011a4035065895084c095a150307080418400503205003130300c02c41400b030002d55061030042070603c0d0041d0040410300c59221404100601080c02310b9030b0046050340c410740704d2403403000124040c2c4810300208444844146090741c507806070340d00c030a020303000c3c0f00c0029580380014030605081c2e641a120981145822008400708162065114070a158051420600c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 700157500 1250 700156250 700156253
    0x150b04080327040608070305011b05031f050904260a0f050c0a08040b0703030606020303070e040c02120c0c09061f2d08010e0604060f050402160203010c0206061507032307 75
    0x440d0400d1703000050a511100f000c10501c4030a129070703085a078804944501000b071000000c0c040e4030015008100000d0071322800d23460440405a0720018000062054a140c1010306142804020391804e00040c40e44462400ca8824110021100112030948900008030034000c025180350700b0000c444902e5019030000040040d002100a001404601110a88171b22150170020101c0e05a40c100320b040d503104006001440d500400c25001c02d0340111000715001ca44c21000b01d09100741a81e90206802003c10800b0405c000421034a40c10700e01036408880503507d0808015982c500f11003004025054100703d244000e100d280d0007844992101031246d10342440132009849040c80700300a20005074030000503c08031001030380c2907410040450341440700504048103580403c00c0b5103d201e101d60b5001800207005220100203003081500140200509500c02d14007940711002107501e80d125003d07103034110001c84044000d0b50f6a09405580d0302030890000004050601060100b451680509008860 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 700158750 1250 700157500 700157509
    0x10e04110a11060f061f0e0306010602100e03040e010e04051e03130803120f0603071e0603150b03060103021e03100e0c0a05030f2701150b04080327 65
    0x10400c807a9a481030141da80107061414440c0262400304041c01c100c09102003680c8006000c01229103425240c0d00d1607006107070544078084074040054050281c0c10000800070340210300c000781180b0724001804581e0403050031a031179100d0740c001c00b40c0200c1d20b20300600c0001c41c4418016449441030040792484074401120500c6900c40c03e1203201960f00006221000c1204482000b0007003040b01c00844c248030209451140121000300003582c207080a070005000b03682d082062400610070100c00382e1812100d0840da400d500094003400e00030030304100c0c06003a010b1a00900f40c0884048030712603400e44d2110380c01100a540610341d826061100920414980d9030094011401100001541e441e12494210f4400d8a0301005011400313080c0280400001203410008803035010700d920300d01c80705035510341c0038015203205415500d003e08141c1e0780401d80c00003015486510440712007101c03a04100c0d42c4604000c4207204a0041c003c003500b0620440d4070b100250b440716180b1446003000c420a2020314004107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 700160000 1250 700158750 700158757
    0x3030136140f1012080f22030c0e150d2103050f0f0903040909110414090f0c010504032406031406010801090c06080601120c050909130b060909030705010f020307110714010e0411 78
    0xb41f01502c1010400c00c104095215003c0060901102d40c15592804101c01741c94500000001402006850b1019040000051280a44000b44541c9450502130050003c009013412100595585d0152010400c64102c4001c00340c46400e08900551130b19081c45203c3c005003ea4100c200c944118683c440c4010f541c5901030080407404c21040d180c0c161807e111024074240b00304010b030a00781c0000d0001c4500da41d101049909503900044808903140010031a50400da41101d0445911803506e04007104000210b44003628107160b80d800c851803640ca40388107900301c2d46543d0300248240c400010811119000c0c0780306582c8810305060a80714424940c00707840c296081d50758400d0000c3d038001281b034420b180409040b6000360003080e80002012083d51540c040c068054152481100000009020ba0104008447c0b009174480020301200d4033405c1410040e40040c0c0b0244007081035001000d0400e580000c0010071210305004d0304000c59400c600660b07040c50481140c07600305407101500c80308600d001740103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 700161250 1250 700160000 700160047
    0x140304052706010e060f070201050906030403020a02031c0903231f110c0a0206090d0606030c030c05030d021b06090a08070e0903030136140f1012080f 66
    0x9030380003107864408400321440000d0150f414007100080c9180d1a4880e04141d81461800b201d000741e0b220705600058540d4080c0d4012280e02200001c20007007090750125404401d84d1094049503004140d1600b010112602100741c0800240301017010004580d11060006215810b90720060000d2807040340c2508054401200100f6044c0a001c074060814042c0315400314540c00030b6240d0705108900c60360070345958582202900c06d0354045070b511803540c1e80c500d11640c5550b2010007040600e40e01d00d0494441a039521040c0d624010001d000606030070301281d400c1c154540b0303030b0142050200b000080d040c401e01e4000c196401c00030501624409840d01d0780004040c0025030000c03c07946107400704020000c1001030031800990020700040180c840d2030541c1d400400c6038844944050416a900c1c0808444050341c958500c2c0d003404801c0c10001c9495546034014011049110225542d11002c030200c41c141d881013902c0e4400c443d031500301068106001d880d0800b403040840b4a403203041c141040c91841200ba0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 700162500 1250 700161250 700161289
    0x40501050f0a0e2a061803010c0c050c040c05040503010f06090b040902100c08070f0308150406082503080f1b010b06040302190f06120506030a05030714030405 70
    0x140155141105482940b0158048061110380e900c1000b45403294122000121454950081400d601611074480482800c01520031521550007a0300301142141650046010b54a40905994554808c24804001c02d03000380042174160080410b100051032900066007c000c414030011450343d50a0241e60350300142c820340070401c0380c20304251500316001d0a07004d038030852905090b2001a1100d2407100b02c6007410782060124414a0b00b00340c04c0900c41c03550020410403400345000c08043c0c1081205004407155810f0064000b6a1001d10084500d9402200d1460707001108a111400400000c603a10f00d0a40f5040501c00350359940f501b03eaa00019004895850086040e044400800d410310101c906c48400070f018040b406004030760684190700029001380c40355404c00381d0075841c003200306c070050004000d030010781d5039a1000106800007a041084056060001041c424600000c0341880180c01a000d035107800810f9945016115aa1158040f14042030200168036034861035050b004808140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 700163750 1250 700162500 700162511
    0x40b181e010f0b030c010f0f111c0305131e030e1806090a021206011214070203030a1a09010e060d05010e0c13050f150a05130207050606061615090209040501 69
    0x10070745400c3c0e5030301e0803809000364002c1c07080c5a141da900c0b103030040c1c1c11b4495080c404060050b10608541c090010000c4220a1240e00700c0784120580381a0b2840706140959002c01c080d0712062455038040c078601201170490515542400d1403260440e030100b440600c41c0c20082c1c00740c0102c2c03002c00e860100400c14186020380150030844030b4206808410b40c02020080b08514101c03c12204030801d41000c0c102e0740c10030111544141100b40d41c0e9000070383c01c4000c80c6480e0014941000000d582c0c1d403007255012440703804c08000599110401e03003540700007103004004070302d268200342c0b00072070143c00103003a40c0c0e0040d03110102101003802849410f4100c980b0901400000030014140898552616808900c0501c0d00003000014403202ca44640c0040f2441114118540346000084a540144c1c0100b50302c0031120304982040c09442c0d000300384451040059070304903554401008481d006209404900c0030701c5010583c00110719100341d10f0b80ca0b01b12000081d04540c0e9401040006000301c40032605a0b6480 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 700165000 1250 700163750 700163771
    0x5010305120a05030f130b1008101a19150207091a1e010504080f0615060304021509040624120c020d052a160e040b181e01 54
    0x288859205110312500c0341c0d290191880b0014450f200060466000000580204140c2c000c5841001c01e41d54128600380307540d0621000710404a500c1d84903002683c031584404030b8801e400c074000d40503201651010b0043c41002d080500640c0020240c12081100b60070310003007080c0c5c0c0c030903842c0c078014565640108002c0b41003d1007081151400e40c0056643ca002c00b442545a0f45c8011f203c4892448051502e40210854030060f01c8034000d9402254460148270161160b11000041c95171283c20345042802283c2c81450502807076120641c0c1c00fa400100c1e00c1ca0b01502907840c20018030700604041d01c001015540d03011722100c04101103510381444020107d036070700280d0380b01c2c42c0c152081e80f00b07a604106015864a0195070f5040c002c20740010711101080c6440d40c81140b455401c03159511103203001c0030b0004854003a48030768140c65580d9000048410101d88021039603d281c1c4115400784600c01c19494840321421a007810040e52401391050502c0c10a030b540140c0c13024400d184101c0004a601c00c041c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 700166250 1250 700165000 700165003
    0x20a1d070801050a03320d12060815040c03060606030c030b0306010f14060c060112120e0a0501110a0f0b06033003040f05061905010501051c0216020a0905010305 71
    0xc0d050508102509005120f10b0362040520000c0f05c2d030100c044441040c0c0050380d20008140c0c901032424007020380c650315061a40c0442c2c1e00c1c032407503040e0741c0c0c0207988401c011441d401c90320301c0e001c0c400c025488003e814500030301201c40310303401502455504099a42d25a200c1081d01c2103500010300282c1c9419080500c1c5415000700264944120003802481d1704040d90204180000c0c030540141c0c0c10408031400f020f850304800c99544584000580b1059a15040e80748179001951004a4201840c0840c070001c4c0d62159000100d41000144405001440d0100441700402044010802d80c000c1075107080024514000d4000d086104840300c0c04c0c0c40c6010b40c2018100722005d010b010300703100900848101d2101c08500d14a1826180b41503d80720340390b509114412444c915402062407140d003052018031a06260084004c7c030840200f07001a80e29680116494083c04080149003181c1c129142007009543d0090b00c0900388034000701e90010010f800041015110343d000003411030b603440040c01403100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 700167500 1250 700166250 700166309
    0x1060f0816020a0204020315060d0e06101a07060f14040201020c010203070b0a0908040807091a040b22020f1305040e07120b090307060c17070f0207061b020a 69
    0x100e0004040d6415149030001e034031040180c3c0c0081c41150b0000000b91004046107480c1d0002c040075000503200d000d0038602c10014100c500340d18a10348202da00041740d8618246401e81692040c1d0003242c00c008212841019070b810903403044070900e0300e421000d09050280e00c100c52107691502e5103040c2078101400064100fa620310901411034204022140114503406205500403680b40000540c1e40001d091161040c043d82e04020964041d03088000740140e215000311410042461017a0400e101c500c04000407200c86c0e60030290015010b10034010441500100b0104140591201519220a01442105c180e10003104801c140b84804005d000b241418450100303107a44e000010b08000303003003185408001500c8500101010701801c0002c005040c1882982c0c0c3c80781c3d00c0b0800344400303004070801130204000c01344e070410214580030000d8040c1d80301d0b000c01c4c0e41c05400c503005050010f040941c00c6130401d58610701f0000b106400d40740b080c010380700c51180340010704919203100c041c85d645124200c00d084 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 700168750 1250 700167500 700167511
    0xf0509010b0d05090a1406061302030c1e0706050c0307270306050402040e0d11060f100b0c0102090411041502070e16180f1a0a0f0f0e0901030c170313062601060f08 72
    0xad10500800c1600744c1d0440894141040304003401205030080c02c03403a0490712585000400300c905042c00e014855003000c0c0030394081c3d18a6120030f60518020980701006050661a5401d80340d03609408002054281c1d01ca5038100e070003e04081034040100e5100c1c1c0c85c0001440038100081e88001c1c0400c0d040009200494201074140c1151210382000e42058601c0905030042c1403211000203a549501da03006d50441e480c1b240064001d000402d142d00260805800511921040021103140303100f3740f510206125003034a500c0e000f4201151200c4134074812040d4808009418407420743d18103084000c24160010040c070343c5402d60040142001c56802c1079001c1c01c030700da0781d0748081804010803a036000300c080b51002080d450800d44509019500311641d4042c054120b401042c1341d4008024010041300140685040b9001400103100281c42c1039500c0c4145000e4a5101c606010300348151407050b22181e01601a1480c0049400c2c0c685103a080008400e0344094041941829250320f20754101e0300d03d5a200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 700170000 1250 700168750 700168789
    0x1031211010e0c0310140c0306190608010f060c0b0403050c070b030c030a140705071b0b0c15100f05040c0302040e0f010801061710050702010e070305070f0509010b0d05090a140606 79
    0x1b811490044004800902401d0082c00c0200000b695a211300004540c0030a07044c05900c1140e64030704024000143c2030085070a80c031415075000c59081c2c010740402c00b0082c1c0c0800542080d0b030321030310100c40c1d64109480d409014000c8100000b04103104c3c6000e94020000422015a6401c0447c25002100c0e20042405058602e030782c108940039820005407401c1c550011040848031031070369540c10300365543e600880032402c004103460300f5142c00000c0994418103a9145400107845482c03d80c0d00d8003000d88184d000a845840c4140098201504810480406030601500f0241c550002d030140c07507000c4480e1104c4401c050010082d0180c02d0007400700608400352510250740d0000512a240c404403458100100d4a03607010808140c800d6010700c140b030f03c8081c00e03260f0340b0b500c0e890200d80309d144902c076490360f1b486030402c0490b8a02d48900c01c2412105081c541a292182d0310444101400c402400e20515014010b440380105222408860f0740ca2040005400d031031501d2002c12058484801404070030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 700171250 1250 700170000 700170011
    0xa32190b0109090c170c0703081f141503181207110f0f060f1e04080307030c050c090a09021017221b080f031201031211010e0c0310 58
    0x1a42c00424040541d850800701203103c42500724141c9984d10442d00e80c50b101e403600b8080205000c0c000000d000d280d40300313a513001216168443c1c0100d641890240700310740c03001d2031402000520146042903507414005006024100e4040540b118250800c460f8006403c180c1001001102c0f4280450b00d40781c9a0301490b40c1c101185c2ea1120304a540c1d400311002d014141000c415092952004841070300c81030010031850b9a80124480130b0070b00d0700503504d0032800f800c0c2042d4001e01a400071065505a03480fa400445c1070100350b0301c04860203c0e4900b010b603500d0041701c980c01c4858689400c920b224081d01c03000829010700510520501c10340104000d01041304a01c10315048103032400555800c00381d8000c00c1451405070b1010440b03a810700001c001c1c085a03111159641c0502c0b080342c81c508030703060354040d12047d02c1a605241e449200382c1a003200207a00d04001800011340b800b047c62414140361405e42806141c12003104d003121400003050700c0c3c903484002443d40c54501003205410102c2940018441d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 700172500 1250 700171250 700171271
    0x170d020d050a021e160b0a030c0c1509080c0304090615030c08040b0c0c030705010501170303010b030a11040b0c01090203010c0e0603190207020306010f0e0c03040302060a3219 77
    0x48034095060744038040764100c00841d01d144e104200310f9070407807031000c0d41440e041d0345d0f2040ea80d41d56000c030034100082400c1c002e0b4540c0c032a0203518140c03400c94110b0600c1c0065804260702200400080034102e4003404180214a0f05040400241000d84551080024602c1c145004104459000d8502c2810035092406600125034800119904142d008001403084e4850f158100301d68050010008400c2c84003080990501c581500014101c4030302c5c480054400300c031145007640f03e1000f4001c1c8400540300304041880b001040c0c1c0307e2071a80c01e41404107420710340c890340d2004441d4072081d0407251a80d158402034081d45800c0c460800b001c0030034104030115001450214206002c020401000580e070f203200e070001d04803030b50106c4000741e80c02011f46a84d0b60311825003124602280c0200d144422082c0000380000c5115003c590080303405400401d640e503902030789031024102542c0c1c0c3c4007845480f0245e41814869244901000c044a11049040ba04e00900e150815403c140c0704170f0006802c280c045c01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 700173750 1250 700172500 700172503
    0x702030304050106091b120e120403140a0203031b011506030f050606090a030206091309080301060f05030c1801020f011a01180b03011e080607030b0325060c0c170d020d050a02 77
    0x2000c60850f400d140310030b20807c1e005038008114000c02050203000c1ca00c46a41c14120324401002601c0c410710940c134000a4088040b40d0b120090240290598030411900c0d81c50114450808034001d800b0002003020543d061403a020100503034411404241c40e4039040040e01958050564000d1050369007074103011032140060000700072071002a00a6900043d0440aa22800030589961508103c28440c0c0c141620701310903194024481c4030000b0f0030381031640007058490780c120382c011000390b40400d007000700003903032090080c420303090032819803180305600e0002d40c100380075003240c0100d240b200e0ba010086500003d80f20740880c4080312501c80c500c12050202d90707071041c162419540900e8203289841021240a00e00c079400c0d400c14112841507030108085c0507856007190401c85816070035100106008940304c1c0f501494124002010b00d044401401741c148128410b441c01400740d0072040e42d05580b4401030ba108038028981e2002e98101e010035142c0300350100240a0b003030707065140c01454071104402c001e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 700175000 1250 700173750 700173791
    0x2d020603010b07030210180201020d0c0c03080d02090d0302030c011404050604030324030507051c0210050307031107060c020c030604050309041a031b0108101202090a0212070203030405010609 84
    0x3480b510380c01080001c24588204505c01203202000001c2240c12491401104174000080080740148100010446545c1c8141983c5405c2584048804031641c10b60303031201081e030081e20010403016428401ea0010303544007a10095101c1c06078001e1551101c2203e03c850079200c0e1800c02610201141c01400300103007001a2469000d9050302e800100820b00d507202c46025500c03190b4000100c811620080700f8080089024022100212421413070500c2c8590760818400b05200081d40c4640307104241d807803030360003100215480300017442c00003100c04c160380c0c030700c0c0c002d401c035040546006a4404c08408415010080380446100407002480545020390719640d481c8164029140101d449aa140d00c00c6448251850702c80b1000505032140001004040c40003941c7c01c1d66682c1c0012856004500110100c0301e102060310315460f0007045c111061740034030240c49005003015854503420030040760380d5183c02d803c0034010041c0d0750103143e8900380313400d100707003543c0c3c20380c220359480c910300004000c0042018424 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 700176250 1250 700175000 700175009
    0x30a0c0f06050a14070507080a140606090105010c03031a1801030c1d1515030f0901050127051e040c080f01140105011803061a130b01170a090507032d02060301 70
    0x44503501c1175540f0300541414007a5100070f0252042440304010000083c4a480d41143c80c8400c54180e81e0380c0100f04041c144003882041d0200f08000d6170307a004244640c1101c20703419000c005084c06185158040380c4114560b03900030f01440c0c82000180100180348a0010082c80c0d00106040301d08150034502d41100c2c0d01500384603507503004801c808181e4403122041201c4800076841c1c0303901e038900900880c1c54102c0c2241d00c0e001d29480c1c00004a440b00e22403a03104010203070194440c03a00c08011a141008080142c1592070708040d9444201916807103046c1103114038450030f0701e60801d6240114880c80d002d41d40402c0c14044e41440412079006d0209003c16044940074645050811030886504483e80b8503500301400035030400d807010b40b0002da00241d022078801c040e81c4c221800070b000e504210484841c41c042c54006000364034039000500d0800a44c54001003100c2000840c1680b81c1c0d13605140c2384065000300c1e078020500300c000d603104010102d01c8501c14a182043c41d1180e090340e000550b84d00c0305000c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 700177500 1250 700176250 700176287
    0x515120109060504030f030b1522080106060504080706170601120e0706090f1d070e0120070e0a0c0f0f020f06090a050f12071709030a0c0f06050a 64
    0x8145590000d4101074095a0011402c225500309402d000b420040c0c60341c00a0003081c02c0c1a00300415003800243c0c1d120305000b4074559801d211160180b14909490030040c11321500d1040004070b00e4140078400c5c01c0c004c00341c5445490340e9501d030600a604140c110390005060100c5440b841450400165220740d01010928081c0341100e0104c154a0041c0310f070202d20481e03071042d01c80203d030190b0800c08103420345440b0780d200c903034a560720085400362042407850307800c41640c03441c04a0300c41802010341038013039003050418440070740d00c003040004800e041980e401c4d11948403420410400c0368000115410a50780751050082400588010301856420ae02007000c110905481d0030030303035109114064a22040c0030030b54a06007800c60900b07035a0420720005641c14007510545030400100055074030b101c40401c08103c0e00300445616600e00c400d1605484100d020801c104982003070b51300340405e10b50588034003424010380741000d8040c4180c0015801c00710070301c1010040502c119400540b0804c200c0803062 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 700178750 1250 700177500 700177519
    0x3010f060e010206450a032a020f0d0f1520160606080307080304020f030705090c0d110a12060503300f0f030702060901090f080c0c09010609030b0a0515 67
    0xd070000c49045c4010018240481d000c5c1103042030b64010903900040c50081d039410701600054a01c0c041010304201c10100030050f4411900014101f588801100e608000c20307d4044000b15258850b0500c04984110340c1c502c000b0000003000d1249105211810f4003651030a440e11100f0061240184992501c4031581d40b9940074030000c00179282c0110014056250607a030700c800d01894415040c2c2c205a40c102c0c440d003103401c950b4081d4140003550900b1180010b10b030000d0741c1c841d07102c00100c0b43d10088107495030b25110b5920003007440c01c807401059000341c56a02c0c5801d4204a600000032600d250300014801d0300b142d5059480c03c1d1080d41e0003c034000c0501140701c406600a40105103070722860b41d60160200740418811641010720000c2c2d40315a01c0768003500c0d03480d51421000ca08a0b01c81e040c005090303900f058140c03408241d034003000d001e068a24408a078511000d410000c2c2114100b40c4c4070100017460350405008115090b10b609800c409030703842c02d00c001e04062000c0e840760400002114061441d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 700179856 1106 700178750 700178821
    0x3080a09081002031015030f090b25120f020c010509030a0801090c020607030f020d060b130f08062d071206060503190b01031103010f060e010206 64
    0x196190285d080c00d0054007042541c1160301642050ba54060f00381806110380310780001d032402180c40b241c041c40c0610030402d14144071400d0803030b0042c003903c00501d81030300f00d002c65440d0b00440da008100c0440d05400d0030300030b0042c03030500e40140d800d0000f030001044d1b000c0010004610265138841da16071301e88002006a41c952070521005a00850006180701e109510090341c0710740011015141c0400b4500034002d5400c01c3e0802c081c02400000d10012842c60010a0001010802e04583c40d441ca8442c105031034200062030007070048580d64a0050b40a600c001d508490240c020201c065800c0c40c410051a042022030710415062401c2400301d50207001e80c05482c4140303000c04540308000c0e6044048000380c0062840c680c1490307205c6a10444200c181e002440c042c041020039004001d243c08030050416040e048881e06540090080c0326480a0b160f100c1941d1113100074419503898011b = true := by decide +kernel

theorem cover : BRFrame.Cov 700000000 700179856 := by
  have h0 := BRFrame.cov_init 700000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 700000000 ≤ n) (h2 : n < 700179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
