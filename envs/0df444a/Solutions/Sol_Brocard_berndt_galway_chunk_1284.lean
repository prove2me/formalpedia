-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1284
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:09:51.714584+00:00
-- url     : https://prove2.me/submissions/2ac2122c-7a94-471d-b59b-f014941a1020

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 230755395 ≤ n < 230935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 230756645 1250 230755395 230755403
    0x6030a09020414040303200403080a09030221010f020c06070c02010e040e010905060612060109051906060e15031b070804081504030915122d02120108011a010807020712 74
    0x70f4107007403134100282955000c14000c000c010103800d00d01c2c008403000b400c8078101c13600101d40c1901c13116552b600301c03094402580081d500c6034000c90941c0c41c800601d84468040310103000208a14825803018100368014403507020070300c0d04400c0016251034010340052076200d2052424820b42e0000400080865494414042090795a81e5403001003040410015800242c22503a02c418000c5414409564240500070010015290008a402c140500c2f0f090a08034002c41c000340469900d401c80240342e09494640f80344548c21615581d406215070404990046c0700f022141721070040d40000024141d8060135048803601d0081000150055044c41140b58a0400c0020040d00342010304000b4000380d16900050405e000503480c0e0741c3c541d50481d240b09614004800045907003040c1d41a202c80a0110203886017200d42601c00c032064104071369005000c41d07107804610354616600c464445080341c15096603400c0f005d65890610354158001c3c4a140e0344070209204071a105511000c40304c050070b001400c212 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 230757895 1250 230756645 230756681
    0x1d040507200705090a11160305040f0905160c0201020d050703090302090703020c15091504150507030e0706050403020d0803060a2103030b03060403080a020a02010f1b02010c1d06030a090204 83
    0x1c4044c1c0740054409401003500e080a1040030015004a491845030445403a079021160b4104002c00d0300480070780c3c0040c00c40c4680307076110716079401c1c054000d80070841c2d0b00003e25030303c607440046484c000c2805040f0f050f01a4000c00d00400b030380c0d4040d95190b0101405805000250b8400001a5101d0441d24460b0034155405a182c1003100c6600d4506040000580994111a410042c013400300140560007a14071405410f1552594141072364038800105001110a0400c0d041140741c98158108580c503e07145021610030b2659120100c1c0d860181d03001c020b50240c241c03810b41011500d01009190400001004070901c1c1c3d070b44441424600074000200e00d06003803050812018941c151041044503602940900f656150aa40c0200803030001009581d03102d41c00b08922003454070035402881842200042001101042c1c120f03000c0c00c0c591a00210019802c102490312200e20482c144440024450450326413401c0c59820042a508018185c40580d50b030f0b00d21050144c0e84038000c150303035540702c58004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 230759145 1250 230757895 230757899
    0x7030e0f101506051c1a03030c010911010203070c170321100b040b03040f14151f081921080402100305011409060a030804170d1d0405072007 62
    0x2903441c0007560300440034444c040c083c00310400034051614030034460756880002d2807400d1214186407121403c070b0403074040c400420305440d4560b0561002d500b0600400c40d1180c481d15503001240c1c2d03849070940040c0071b034400d00d00812101c0a944080d100400b8140c050f80e0814802403000d807040d8500200341400c0400f60028030103c0c0c00107240100c083c04801c0c1080d40341500b042c498140c58400074000030003882442c01c94800340146485980c00035851841660351404a4240748a8003200c01e48012525109a4820001e91000566020225490074010b0300e41313019400c0b034042003100c0840054400c81a000034000c1408003000c040b40a6107003540711102d10381081d0040c0110111544145800d040c43d000042c04640070404018440170800c680303114060b80c4100100304282450b42c001000c034080440c01003003001c5c5822103a07404010401c21520200d01d40c0001310384900c0038500d8800e42c40401000044c0d2410540c014551103032490038610003e90b80c01d00440542040e83c444041030f90421002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 230760395 1250 230759145 230759171
    0xe120412050a0204050408031b0403030806060a030e030f04090f0c08010b0d0f0507050a11010b0604091806091113090213110c071e0b1309090f05161406030f07030e0f10 74
    0x23801d1101c1c214109002c0c100f508559001c0c200e40c0015210354400e23f8041240d05020344a40c1060080110010a594844a000c1c0c076034055500309001c0d8503000c41c1815003080e1038000520600c60b40ca107065603551860b07480c1040c00221640040418903519455161111240c26903018031030060195986080d134030441c0240040010358103145042d01c50741004107100c1c2da0350300c07102998140d0341a258000b880001414240401c002029001003041d4107082100051102e903030010056503030181c07a030ba114119620480021200c042100951211080c5042c200a0f02103500c200b1120800f00c41c1e80c0d21341072032003a2040c82c0c442c0c240d0040005003620814900100d0340500d40c2001069260000e506201008070141c024a909008100e00030365121384c070f602441102c4c00359554907034008099409402c00c20f40785641540060103031402100941d42c440e00d040c00c18204403131181c90000100e01c6281c4900d2b02c101d01a1034403134a07600803480341c49070500d0502e00c20b0082c124509455200000e454071000a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 230761645 1250 230760395 230760421
    0xc0708070c0e061f0f090f0b030105010e03070609090b011209050601032001120c02191109071103090d1103030f031801020c100c1b0b0a0e120412050a020405040803 72
    0x403440c000c4d604101030040b219004c00f024040d02d40c03642450a05107181c88070449042056074003070a61008040000594240003e009505a54003a41e54030045070030441170680c5c80b01c4900c00d00e000113410755010041d506035a80f10f406546014034060908954800c141c0041d00d440754030980c0c5a0304030b00e004004000a0080e140c00d44844018152005051000081d00d664401e246210310151580c580e074560030308c24008840540118920400c0c0c0e250681054912502c041c00d042e8040c20b4118045202e80f401841e6244000b021000118607121446040c414050b16159080340c440d024001c07240c4c039968042c0094050340100680807900c0e403800643d91480a4591203403107900c0d901c108012421040013084102c088a0451000b182099101004031807910b0010b03000314612828142c0744041101010390030340103000202041c0110701207060302c291260102048911009007c04c02040f04182c19100388034514003c0c81640c0881609030040f0341910000c403822145083c001080040c0440d00b42 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 230762895 1250 230761645 230761651
    0xd030e0405181e07030c0b0703180b07080c0c060307030b0118030201020a200402031806060301151202030f0d0e0a0e0408040603021612091401050315090c0708070c0e 73
    0xd000c0c0d207102d0302d110301d050301c51003401041d080f0b100b882d8200400c030540c10400b0100031a84100c070420710a030340b85201c1d8200d070003030b8a04030300190b404102829101000d0110034195000300c6807052420a00f541c07541070742e51007007001c529503001d45c400e40301131030780c903c07010710321604164402080c403100b075000040103503a800600c40345038010180d081c00540d0b80091880301c031550124520108400200c180900d02c1e0461a0180d400780c0004108400500038406442c070505141c1c044907c0da444000805080c3c9450300307031451951201c2401003000150100c0b289802c1170014080d1090801e0010040f414105009405c42c04681043d146813000d081400c0e02400a000e071075041d01d054100f40d540d00f074441c800c5124042c2095004925904000180d16440700c3c203691061484a407880c06035800340c10101503224402406865144000e4079500075800c407445501d20010607100a4420f00030030240c400058000e02118a044c0b0017000000d03490801085198080c038600c0340700b5031034517103440112003000b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 230764145 1250 230762895 230762911
    0x5070c081605120a0206100905040533100518100b07081209070302040e010b0904060f060302300a03053a0903030509030406092306030a140109020c060402010c0503160c05040e0705030712020f0d030e0405 89
    0x1b010480b00c017020107002d4003474a04081c1242d9031281c440c00d01c405140210015000303a43d02c04000d222803074100203650000c483c4291428480c0044400c1107500b201c07040e080740c40d0010512000140001c3e2254800c1a642a01241c0040c1558880d0040303101c8031010360b00e00d02200140840007201380001410041f224860344018201c0d0007103540d00130080d000e0f5282e0305800045c100880c92812030011701e032110a100c40c40f0f100312072421000045020b400c1c0380100740c010034600000303d0741489002c812035007510040d840308030314240361204e201030803402401064140040c078142040c02c0d0f03484e1801980500700061002c24000c1c1080c500c1414080b040c2d210343c42052041050308880c0c078010800c15441902424417a580c01d1032401c050742180706158013240c0c00808000e03801c0820030f802d004c070030944406a40c01c001c2c2111005496030b0b11a040d0103155819440844100038170003600c7c1030b0740d000a00c00b5010550041040010854a004070360041300446c0080030400614202449126804200d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 230765395 1250 230764145 230764189
    0x5130801020405120d210605040203040f030816050f0c01110301081c021603020d030c121101050f07080f0a06090908030a05070c081605120a02061009050405331005 72
    0x2504064042104c03419001c04841c1d40007603591b90a801076010800420b80031b40155a80c1c50305150030065088405400c50104180a012a10f84825404542c0c0c40f40c800362681071400104106111203074110340700517003141d907e4403a0028800c0480700958001d051400c002c04a090000b0411007040242490400442d803080615898401110f03080c4000c41ea0140c40781c08400e00d440c24101c0b076011810a01800c1c11190041405440e90b000701001900d0030a0002009240c40b0350082100c00541912540000f0b25000d0204d9200030740c048209400c11040f020001b403c5944800b41c5054889132101543d0125010040185611181c09500d070f00003454a0700030310101060303860312850b0040c01180e4440c1036840004900700a010040c8503171107480049002d840c2c0302c2c4000000d685800484110000c00049000001c00011714084c0c28040c60f4008042d050100106088100c0c43c1d1450034030348101c4044900b002410312540703409a02480802a0110407503040c2003c9c0b00c255843c1141001031030070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 230766645 1250 230765395 230765413
    0x5030c0301030f0503360102011811010c12080a14160f03060f0801060305010605060c100b1f080123011d010302090307080a06050c0a020d0f0513080102040512 70
    0x911404590640b640b007011102003088600303110380f45000f15544000e1345c60388a0742c280054aa0300c008180000b80c1e0001c0010203042a4004a0981c5c034140352a00b407150030340c2d0403600043c0d03164480e16000e0034185006280c4c01c411b1740310090000ad09040b007002003170100d07083c03242c0994070340194400b0808034003003211141403038140c0b0244040c0849103082040f203440701301031489119400080c0205010b106404a407600d804c80103009244501c402c84484d0b180840019031410040e054074003038001440505000201d00d240781c0d01070541811260b82c030040c1c81146103048680d010008a41458603641d0405540c10000110110400100140c0d0b1003c1c4400064501ea81d01c0b1140c801d01480c5071903c142000350781c0005134041d002d41c1c040c107607060080c3c500220ba003000004003103101c0350050100307000c29107a0881b000514441c0c03151140058200050100e007642c083c00860021f0394542c9840c51604c0c0b490010000340540316005103455940001e01008680345c110704d402003982c1c03948003400400e8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 230767895 1250 230766645 230766661
    0xe0403080f07090b0721090b0f13030210050304030f091203030e01020d0222050a14040902030c10030c0e040510060809030d0c05071b0308090d140712050d0503 70
    0x180018840c1841c25440c8000070207551080c500d100060100c0802203481d00c00d0303841d04c529020106520100e684c45040718000b40984905914001c072507101c4166454903020402040440d402a4140b41024089244c00401610760556848080d5404c1d503629850382010300c2c00030700b00e13007002c13400e075082080e8031074140106684115a07a0f9516414100000d60211180c0c0403400390150714440f140301341c804207983c0940001d4101c1843c0c1c1600c2080c500c0d000c00e4503042086803480a5008038590349070244503c2c20182440e81c40f4403840ca0009045640000784103000a07001c40c10401c45400081e101c00c442c0c0011170304000100b03d070a100702c5080c401483c0071030503400a240540b08440800000002050003450140126143d1004030301c41400000d145103c090309680c8101800c0320b0103050003250076103059a10403400141e9a01456043c42c100c400c00c10000410074103d03040c3c034641210300c01b5458801d070421107000180045503508401c40f101d424490306242c20408114180841002085115 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 230769145 1250 230767895 230767907
    0x90708060f030a0507060801170723040906150501020d0507210c0b07092c070509060c031605160806060d0c08030a2d0923030709050609010e0403 64
    0x8580c080d9108000072031038600007803400000283c0980240601c0d28042500d6a1140d201343c10380e40c82480c0740c0da00b503182096455544500f48668030407030009024004101c1100701101c0100500144089490400c0361540c030304035002002c5090000b4020380301080996014400c402c40100c080c1403113070402c0b03981d40741d140c07610381840807000d8040d0103645800f403201e01030021080301035041a000c0020b072900700406041226503001e41c10151005040d10219003805c1f4503005200c0414148403201601c40c44801c2e01d064100e20a400e034031280c02d11804102c41c10410180030050150210040055580c0c01c046003880300440b03119000500584003400500e00010f070540c2c1000003610707500d1600003103040c019000d00107904806201d000002d40040c9103507105002e40102043c1058000360b0602504181d001c6480c0345250170046012180c04002c44038855040185001c180b1210803511140070000070f003000095008000c240380d8880510030141450b8202e9805843d582810000f02e0405403006411 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 230770395 1250 230769145 230769151
    0xb04060e0406090507031b050108060604080a0b1b27010302070812072105071403090c060702060409150303180302010c140a0507080705040e03090109030f050a02060d1a090708 77
    0x11043d11045400108541009803500171034202c04400716a80040c4244809108103216407070009240350003190032464120100c1d02241d41c660010f100d0380c0d200b43d8510241500003000110181002e0843cac030101075110300101191401410410100011802540c40c4e0344561025541003510601c92840054940741c00c03504454196030903030070b00350b8a0354000c80310380b10a4a176042030300000c070b1000180065181c1050380100c413982c03142d20601190400e4001035000888000e180f0b41d0bc03c041005450034283d004100b20382c00582031601d03040c2c645807804240d8800ba4205803200220035010030a259120340c0420345140000346214030783e45103400080030a50f403000003a01c1440c4013100340880c0201081094016030b40003060380c070559076070413a0310b80300e2a071807058074029802e15204684c0000d01000301e500703a03181615031501e1b02c0d09540307506191100c000e100300e070203124500c10080941d490030054156034031010300101d50307168281034130424000400609401014004140b0004940080316030354 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 230771645 1250 230770395 230770403
    0x9050c0703021f060504060b070b06030a0b0105040908040506040e180a030210050a0b040606020d0311030105033d020a0e01020c0307030201050c01140a020304060b0109030b01180e031308010b04060e04 88
    0x10300b00c00f200008030024603d5034440c0342c0c028544240001d5049000002d84502d50003645420540e5076950281602c82000e030000400300d501f450014041481c2c1640701c1405103000d805828103280e10756003c1001e9038003d40003030310b0307200b102d4081080c40c429a001000388500c40e0000b8000c046050b03540655241810940e80b0b170450780303a400054260000f0791003040300d000014802d2110380d64400d4041d448403042c005d4800081c1c1030000341741002a400b4100c078100c51000d00180030b04000601d8203140b080302c62800d108054840c0344070004500d10315079032140c80c414000780107036100045000034007503132203a01c075540c10b5400800704043e031507038081085412241c081c00c0a66030360149404050041c00010010320005010605214848406601541c850f5104000402912160740015561341e140c510005161800c000014060b40f42031283c000c2035200d0160000c14040e002c1c0359083c1c2150480300c18000014010b450400000c0d500340508100b064060307070100070560612079420701c14100140058 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 230772895 1250 230771645 230771683
    0x150a0203060d05010903090510110715020f060708090d0c050d081005100206010905150a090c0926060703290d02090103030908120405060307030b0d0510020409050c070302 75
    0x604a52200e00b200210254000000c0011854074640a080d800c154058107005d440141c22017030761039002d04078003510303041d800008014240c540214130020140c0b140c5c500007140076280340e0910800741004240d00030006519090841d00d054001149891480150407040005140000c00491804a40c0a450360010b142402060307230351401c840102200c1c1d5122607001800580c10702c0c0820303404603046060320040d000c00d2005446075070292015414400c0755940c8014290802c10004e080d6038000703103001c40f9500b4424811651001200310590061444248120f03080858020300081401055400350440c1810052014040080114a0848142907020f003074541e0384103081795101070701c0c0d4103410750042c00d2840d6581c40b8500241580900d2007807850b00c6c46000612180c240c03140007541c042c0c600281c400e500b59994400200c1c00b0b072041c00401a0440081c846c048003043c3c0501c0803100d00e04000b503025079103514000c3c2d85000c607900180321240c41103052242d500020390210300e03c419aa10030ba072007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 230774145 1250 230772895 230772901
    0x4030905091509070e040b0301020405030715110a140609010507080714040e2a03070e01030f0902041109210309060a110604030c060b090601090512010905010207140708150a0203 78
    0x6546020b03032500d4820b521403550020004415840340456180503800d48060021407000c00c103060913802140543d81c0d00d40c204940c02d000030b038404011005d160300d99244c200c51300803850b2903590070211030250136580c54120007a81070b886002003188942080180300208003500c1d000d02e00816000d0302038003240410250740e00c0c200e5030001c450306580c0600f10140c10804107003442c0f0b05030084004413006031405002d4403111000758140d6103041e01c0c0301c1c903407076100e0fa45002c020380011001000c40558081c01c0541c1e5501110258507140300325040065039010711a50f84e08440308000d401c010079081c000240142021200b01d04402000340c5440190942e08280c03551101607042d500408152103640252241d80c0c208400d06600002050645002e80380c2040a120003d003804020711040343c0d036a0201d02c030400201f1080c01d0140c103110a4641d04e1000103183c000d595202401e81e8031000e4103568440054403409180723082402024024113020000300a1300708003e070001900300e0000e1018451540c04000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 230775395 1250 230774145 230774161
    0x61418060d0b0c0d151d0705040501081803071b050d03021f02070212031e04080d18050a06080603070b030910090c1d0403030608010c0c060f1119080903030403090509 73
    0x2900d0461409603000d026000400c00d4040c100f07804da101c0c10021224104034108644101b0b204180520b407182d0b80d051800c1e0400c001944d03010006810820030954a11000d0210a824800351002520a02007642001c0c809401203031801c01c2074201e1441080004c40e1000000e4001a440d004040d1840440c1c42412501e03052100070b001d00b102c0030350007604280c0c0303040c5038200200003002e41c120804408007030200c00c44580c0810303010b5405000f0781c0394050f040160400740a0103144200b0341540401b28101515080031440d105c001e50700c8079001c20b252405211180c90300b4050034024204042e00e460651908807101070b61000c0030880c4081c0725640303c2c00e603420b100712820200090540706150070550101c0210032515110125401d6000a02d8503002003000001801043e2600c07070f40d50f903110403500140d200c143c01400ca000d004d085095503040044400c00b407050142078030514440306e801c00c0e10b044040140c548100100b1103062608104100000203400c400c1c3c80c800d03a0300656844a5541c0d44802d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 230776645 1250 230775395 230775397
    0x902040e06010308070b0c0301060807050c120c010204030303060512031605151302030c0f01020705042304060207050d02010606050706050604020c010e0607021b090721061418060d0b0c 81
    0x1109600c1c0558000401031211600082080761302c04c0c500c6203440da40b4850040c1e1940420b0003161b000400e0344003c190124400e0001c0e18008860400340c0b9140c0019a001180300c0d40302c0c0c422006143d401050420915400d881a00010801541c0311404018035a078240e450348140c40250300d1701a0410015028080300700880b0b0010019002100b80c1d5050099061403184100e0300124400c0c4036607201c81d80b10781400700c098030054106030024900c1c6401c001c2004003828140110601903101644a000b904011802090155009a00040e0344250300c2c148942003640481c091425a81400c0301003100640c04400c07100328541220000400740c44140005010b0311030080c21800300d40c02c043c2d1500541501240c0203000d01c00366000ca810034188098890f44420300892811b600114000c00250402e000c0c02c0c94485c03c4012201c02e45a00c150a100e000031101c03550807400d90140b0105ca1850181880d00c500e03240c03200f501d02e41c4240e030725181c00041c1d014420804000c055131031200c040b0380e003016424 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 230777895 1250 230776645 230776661
    0x50103080a031e0c170606130e2e0e1b030601030b04090b0a1b0e0108040605042907020c04090f0609050115170706030207020a0e0405070b0a020f0105060109050a09090204 75
    0x18001380800c0a0000005100b2080c0380307040b96201c4103400c0440e200d4682801101c400d020317907410000c100c81ca0f000f00340c801c4070001495401010170b09500603820600c054004c181111004c9040301010b400c0031104400910300801b440c0442c42d09080d04046042004240d0703500160901c4c02145980002d004280600380e40ea100401d100041e00a200c06142e03142c001c02040c417400800c064040b6540da44c120b400401d030004883c0410403941c0484e020415582010340d0043c01351510404801c803980320580c9172001c0154a030880089607040c0800315905003d00f18121004460a201e00c25182d02c0d070301ca0300f100c1103000522180d61210410100002900b02c4140109154183c01d107141e5a40e00568224a5071001034409000c2c0650100d4998003a100341d4020580150004501d07500309050180003d9010f081911148103070b0b680010501d040b031004040d0400310303074064441008800f50060a42c0d501403d600d05110700607000b400300d80c0343d10401da81100c0700c01d40049000452400424020a107130303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 230779145 1250 230777895 230777951
    0x8011703040b040602010f0c05180103090812190c03050c040611070503030a020307020306060405010f0e0703090803100312080106080a0f021e040608100806040b07020309030105010801050613050103080a03 90
    0x40f50002e000ca8043d440000d444055050038400c11010507030031121481004200383c00c0d046c41d100180c8007544254080030802c3d01c214021490100e0300b8414180301071044070503502080c9598116041040c59018a02e800c80480c101400300e030410b058084242e0003a40101070070022440250f510315941000320341c1c014100602560fa90300d0504400a46036400386005074040d01c52140450501e05280c0708060481d8105d842c0000c00034100f070f07403218034181c010b0407071810592540d69240104618200a500403a40c540b11070001626518000060262100492060107440300040003c40d80201083c2d60194410800040740002d4440860081c040c49041707102e0002080d01001d0582c42d21001001035848980701c6010f16a00c0303403200a22003e05000d101115080080440c00041c442d141c81500134800c0e0066134244041c4502007070848009030300444543c0c1d1607a00784a0103080005001042c0b40e42450140919819a10f9000303a5208120301c000c02c2654807034001d4a1030109182c1e204010982c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 230780395 1250 230779145 230779147
    0x2a04090503040f140a0306020a020f01020307050301030b010503010c0e09061203040b0c1e0a0b060612040b040605060f2407120f02010515010806010305180a050304031a040308011703040b 82
    0x400e00300030341d4a0304240070b99420640c1802001c95409841400e000015400902403a0120309658801d006500300520700401d500c00d122118072064001c1c00610f1054020f87e403099207940c50741c100240001410380c040c0d40a03034507102d4521b000e181c4c481c2e03170381d031090409448a41480d01d400c408110002d03200c407600c0c401c81c000803a0100341201407500802c50004840c0498440310304d900c42001900c0010140c03045c07d07520070070341140044d03140e0b8202503002000405190400176092032503c4821000c682c121010110002004104401441107980049094071007141e60072810340420b41581034500c4800c0b40c00c901c181c00c540074064010440304040d41c0080d4210700340ca0040d101416040015034042d0140d400c0000280300c0722984506001103d50580d9000b000c3c3d03c1c0c2c40c006400030000604040b402c80c000074805480d204c82006545035a910440045a40f0762460904405a22400c0201a00000ae8205000120b58411100e0b815990100c00c1c480d9140203810203a869841240c0c05102c0c0340070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 230781645 1250 230780395 230780411
    0xc060307082e180506011103070f170a050a0f02010b010522150206010305061b03010e07020a120504050118050a0312030902270f040b0a090501060807120219082a04 72
    0x440c3c01040360300c00d41105414025500d9500055515a5040420096940c41444040080717042c082c3c000300f086008031400a84021020300d50b92a6078041700c03212001c100002145031040da4071050303140036070352144020400300e18482d00080940c81007041e02452040c251030070f4203c0b0041111505c0c014410000b02400c01c03c140d40380a51106400d1006807003600603c000900b442c3c000360b801070308282480f10503520b1a07085c0303240148003600140c203140c00c52090101e520001098a44070f1803401095460300764850303107440c00040c04402a403001c50542e1071801001c0145440300d068600640354000403100f02551a00c0c0c0442c014003d035031b006540311031600042c1410b02d9081c10302d0044103100b0036400006a40c1d01d8032010710031000781c0e0010103940003200000c000b03491580c440300d40e5a1040c000813450a40c0c80e444989400c003250010000c9000f98189a421890300070081044011013500c00a5401e10b4070003460748409000b00c800d10140094001c0c0d00924165261304103071440c004104001001d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 230782895 1250 230781645 230781659
    0x1e0204030c030b01060e150d090c06050d0c0504080d05030903071a010906060c030206060f0d0606140a08070b0306090628080c04020903120a03090b070c050c060307082e 74
    0x403445100550306004070f42c0012454911030900840180d9000d440100c080684910031121644100c40c00140c4540d194402d000003020403110800030012941ca0a4a4a1454100070f044035411154801070103401c000c01c020080021840200c0c0c00c034282803258599542014860640c402c5c80b0300140300e40400d0303003d450b03c80403d210080c165104180d0130451241c0350807054070898460b0402401503440400041d00b139150103400007140c8400a0b00100d10840107039502c80c10744580c1d400060010525004c0341020f410041c100070300811000d00107040452415090b03442c2840060080e60045020b840040c00d140c072001d218000d50409610100114a2000c2c00e0aa00c023001e40554560790061201014843c5000c6c026200c0c964401401703820204454400044598030201d0315a0601d5106c0042c1c4020403020501d030340c440c95031904c440e11411034500d0711310700700039511841501c034840030700905c68501c0d40540c100e0350060503080034004050f0340c6504903190104d03e0420916280484002050305 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 230784145 1250 230782895 230782913
    0x13021c020703141c0903030e0111042c04060c0509060708030f101809021908060f09150c0306120f0a140111090d0807120f021b01080601031e020403 65
    0xd0390181d500c6240745000c81c0800705440c4250384d0031443d040c01e546044515034044d90f201c109103521074100060404c00041d2001d09682c00e2000e44200c5c40004201040324086043c243e0341c1c1107085100300d05040d00414202090440701a1000e017419070b50b00302c0400101c0c0624110364101c00014100d94030303a01c00345440c0480342c0c001c0304c4840c409044100420902c0500800040c19180d280c10410b440600b0500300c0c100400e0307120700507688100072440c0e03003041000d01c442c0c110203031241d04e014010529118090f540070810103009080541e110105a95100e001d1101e0603400180340104581e030390b201c650005202404074030000c40070703010300300580001070000200501c840b486485403110008078040220301300c0700d0742006120681c10410031041186490200c0707564082c440c04046080603860703143c1220300c800d14a140c03c0407a03607100b01c1e560350310340410042d050303017042814801c000146000000c202ca0f002820310750600d42c035121541002c2c4a03246090340c42031544103085482d590b5030708001e511 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 230785395 1250 230784145 230784157
    0x403090f0b04060f0207060203090409050109020d0803160503060102030a030905210406020118080706150801020c010c03050f041a090102040306021c0605120a0b060f090403020a0302071d01030213021c02 89
    0x400c001c03005482c4290300206c1c0c40401c030f034038070340195041406c248240000b91403129000c851a5503200089401640c4201442910034010303611146c907440c1c00961400d02d005c0c0754030380100f40700c02802085010784c0d0000883e1540d20f00c519021070481780c28a0002c2c40c0c680148907500c1e0904d900e00b104021004081d02804c111000c6034000e001005118003280c2d803441100b400a098001c0400440010450681150726002c540102c6480896940c2c0e0310359089030401c4000640c96519107420f02d650591500415410900140440d98039013060f5440d00320000d030400f010302004810300700040d031601c0294103540c015500311300290354407001181102c080000721007080da50103240100100d003500b008403480d007601c21410004c000c080c1031610380403202607005240540c07008000d41514603176201c10300c100e4010f501ca50003c014907001460041d0400003560841a8500d0005007c0c0e115090310718595811280c0595540c00d2a00c408142c50001e07210300000b00000d50806d0002d115025015401004c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 230786645 1250 230785395 230785397
    0x7230d0306051c060e03071203020c2a1e04091b060305010e0c0c0a06090809090c03100b030a0f181a010f0b09130c0513050306010510080403090f0b0406 67
    0x4035298450040003c06150700145421001100e440d1000052180d4000d640341100b1000700d03401c10403155202c00d10301c1c94802c0d014001903000b090300303140f903042002050708032500c19102c054000c55022500ca401050700c803446118440503010464042003e005d40b49000c400500144080719203414000303008020364408483c6011b41002c0003610602c41d206240c1a2031100404d000182c660754040c0156420680092400b4082e06642c000010704d01d2059000c001c0c45422000e45900680c0100400d15500400c1c0290107581081084030b84241c110300c0f04c0560354004001600d1307448840000e401031101c039a046080c80d2078a0f4042408144c039030b09101c0020711800c20139281c05440740350a01c00d00f03003c1c42005c4207419204018001a0340160107000b81c003138003818011100503500c40c040c0a4403401024000410000902115505c9011105030041e080503001000c0315498800851003210321590208100300100d0040340815129050103002401c020b6040300c030458880ba54482c0560052103408 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 230787895 1250 230786645 230786651
    0x9010e07150503182b020606030c060406050703051b010917040509010b030604021c050612010603021809160902090117090a02010f0e03010504111206100b07230d03 72
    0x5440900208000321804240d40342c5056403119508030f111130340c1c24803808010380030380461204074a21002d1721842035180d6151821909405041c040c3c10118060030950003500130311949400c58031441c086030102c1b0071510701560b54001e030b814115142d00803168075480a90801c0400f0405c003074150400700006010714a02100c0c6040c055078203201c2d11845c86125000b11103c001001581600e90146601c0306001d8000341c03a1500c3d20031070030301c100b182007000501e255940c0103000003070a101800d00d41c4d441ca2880208009820f54001038640400454620a10344070240000c680d201c06014004a01082d00d6411010341c0c0c80d04501406074021900c680c0c001207d20501d80f911900d51000c850281517208081c0988c445160011a0885c0e80007081c50240070680841c595030740c070244903151141c1e001c2c0f4481c000064650f010050b0400040340510041e5001800380070100c902800560110303500b00d50180d80d10700840c50311078280c941238081070b0611340980d0030218418502103001070b88800155410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 230789145 1250 230787895 230787899
    0x1a03040c06081603180501050f041707050c13060f0306020909062e05040522050705030c04090b0319060902090a051303031d120d060602012003130b09010e07 69
    0x44810b28002c681032070070f030b49041d0000488030340203a00c02ca4644103603402c80c00b080c401c16240c440c01d64805946002c01c80e03021100300420700000c045246242281ca41145207008540d482c0c0ca0b58412022090314400c1980c640c1d00b21005480754000b000400302d03100c00303d41e4070381e43e410a13000173740058407074502840b0350000154192130300c03c1e4540300060403184007400910542da1264021621101c6071001d00ac810400451030740d481d00038407030002030100e80440301c1c148078440110031342c1d6029103040305000d01070040c01540d55000c402e0380c0c10349609000000345074003102c002a1504140c08503c02c0b604002c002402c4c140721064003e1001c50b0300276106130200b074840148030400c032103003182c402c1c040280000c9284000382c4641c02c071650b9801c0c444018182c0d42c00402089041000000d0b001103070a000143e80038807074625000e43c100501a50000f0441d180c08074841d4204e1046450b141c031510b450000c0082c1d9605044980d01d45582c1e00030b003402509207407000c1c22a008080d0700c0c100c0b005600c5480341c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 230790395 1250 230789145 230789147
    0x606120e010b0108071b061b14071a09010204410f01030e070b03070804051009170307170a1d0a020a05061b030708071106090d1104061a03040c06 64
    0x1400c42e000c001a51440e02a42d07808404480fa8064215410118000300422074081002030042d42408401d800302c0000c540c1d600748010306080410400d01c01c200c4d0060101c2030100b440c8040c0a00c2d50705482c1c0e2201c92a039620744a9074020b10960b000000788206001d043e4041c4400a40c143d11300024400b80c581015051441624460442c1c054041d4800c2036400c0110340c6512a40001c11060600000c48040a03118000c0380701c030380c04c21a045400924001d0411084c020b04112204406d003480c50100600d022030f8031001d00244508002c65802c050002c0440d130328520030f9003040c4880000c060411030a00701303c480310380a08981070b02c407544080b8161040401c1400802c100104941c0100703c0d0a81d2850001800a150440c0482c503d08020703c81c1c0f0316600765828001882c260f40f180000c1e641d03514503032034014011200800c1e40303401f030b01041c0b00c441a2a120b03d4507a42c61a900542d440318050442d000080280103280c1040d044041c6d0350350002990041b001c05103004a00c40c00808200c580c0b1080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 230791645 1250 230790395 230790401
    0x9030908010e100b19080a1712060402030c070b070c050d090b042603031302040501060503091e0c060d050f06090402100f02010b1509030c190303110705040606120e01 73
    0x100b45149400c6a08030200351036844e409107484210182102c040b002802040d0190b040d50381c0d00606d0f498025110342c00c20480300e00d4032041280c006c40350050030045155202e00c44200f0080026002d01d81c008045510340404c0800c0d50300c02076100001e40843d00d00200014003d0840c440e0440e2507200780786503055041d020300000415259400301c028141840c00074241c2c0c1f2804400c40c41d00c203680380041500c03082c40c0c003071004600c20b02c02c0c4c030040070340c0000c01e1040c4021120142e01030020440e050050110814001c500c1c3c07201c0c840e18030019071082e0f01042c00c0c80d00b024821040554002e000180703060300c028064004c41e100781d00d00c140c007a0302035480c1018400003180c01c5070700942c0140d900000c0d46081d03005080b0a1280c145510002442210b028007080310310b1010441864000d5000c5001059031504002c000d4503035000303030740786075003450b00c00b10340c106240e0940001414020304ca08240d507002400c2000d00c00a1034014014883d8a075209000f030216039801d20020555030801c1094400810140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 230792895 1250 230791645 230791661
    0x304031d04020c0a080906040b0c031b071805090c03010204150305150607080309030904090606140f0105031314060a09050d02030c0a110d120807030f1e0506031e010903090801 77
    0xf00034000062466075842a5030784801c110f558012001d100c0030640120b140043d0120f640160021962460250f100340901b00b80d00d5450215035102c1082841304103602011002c0100b24803070081483c0c5c513103040050030080c092008503015031001ca800140420781d8401d4040014083d2000c00039a2124019403c0d10043c8001d010f0b04460308002c420001004000116807161001090fa81008802000101901c1a040301a100c942d2216800e01080e409110031400301c90701100c1030303001c0b01400c2c400649580001020581c000e82d800c5520800e000c446650500d001600502740c44661070f00e4880e075002404d4024003a00c0303074481c9140c24503c440c0004110b8405040000003024520f8040d07a52001d51002030b203006030019445000440002c2804ae042075441100b516035a29a2a29860080071601c041e1070503148103003054110740700031000e5195010b0445078454042070307036502c200c00300b482c1080c04505a040e4500c1c0c16055104401706500c040403151080d40d500008594136410726098500382 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 230794145 1250 230792895 230792917
    0x20301051216050607080c01050c040905250e180f15010c0305030402190e070c110d020a0909030314150f09060306060904111002070e0106052506060306020304031d0402 74
    0x200c01c0600c900d182c135101400c1250f1043d603085251000c240409401c6d00c0e000d0311035040040c00032609024480c61802010b600045000000c8240116011084409400405002c003840061085008241c454020051040d03152110b00185d50400704080c0c0200d00c8100d890480309100040c400b0041c2d032045c2d0010b00a2030b0169121411a19950208215080c03861203441c0914001800002e0301d01c8031104480c03190f0380c00d445d0a4500036183c03e0180515031401000740c820740c0d07595041c0006070b07540b5a00760160380311940001942030f00d6103000d400030042d802a000024440c00c0400400813000585491400d50580d00740300300030060020302200e80e1080c1c0308950301d60040700009040d8200f040c5c09a43c403502800390031056041e18004941b059518981c8680160050315041c02003001010240c1d00500c6c403454403524107031400c008003402048807120400c0080d0f40314074100c24801035030804006580c00a070f00b15620300785403030081c09501e440381a2241c0401c0350503601307119107803030701c02d9a40340202 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 230795395 1250 230794145 230794183
    0x303020c0d0c06060608101406090a090e07060906020d03053103090b07080714010f151403070308070318080d03090203160f060309060219090f0e010b09010e0102011b02010203010512 80
    0x113040789019a2103280e141c243c3c0000c406e005810440c1c0c0d5050440000b003e0f3300400007401c0440c222a60306203c2d280d00018148004108200718a03640040c821140700040e14001441d07031150035a80c80c5204107205240011405104080042c04284a039841414484e80742c803d500359540c01e03c042603000b8068060b0800c0e9050048034045500303024014002d100c0360000045045000600f0310440b0068882c0b0f045003064840e003413103e810f440300c0080b00d400c001c500a08095107103580b00102403041034001010810840c0800801c03224182e4200040c00e12802070310074101028000a0081403010400ea10910580030310300c80400d0b208040c41e0a9440141303082240038104003059018000540044403119402c00c14075143c80c141403450001c01c0259521070305140d280142c0c501c1603c00a030090180d40c200d5800401520702000f08480f1101c13000c0c2007d0109401c010300503401402c03070000314030b0002c40302e2810b003070b440707a042d402103068400444540503903148940300e49940d0f1584500400d80012 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 230796645 1250 230795395 230795399
    0x30503191715010c05060705180307030f110a0305100c030f0e0c100e0909070501090e091c0c050321090a15020f0705030409060603110901080708040303020c0d0c0606060810 76
    0x64860407590b6203071042c14800341e402c0099a5191425808441850009001040550001906141d504d10300d4004400030b00c5440e0654030380c1540000d54030001010060100403404d00c2c1e480702d00070700c0021074224042d140841840f03501c440c090b001c0002c402e40080d10306121254003039081e2003060000540e15005018004400342403140030492180501d080c4403410b44031010329130381c01440c0c5100301518400341503913a25180c005883c50030241c00409a0390a000200512401c0c00140c03e89041d0074910740204000c100345040e1034400f5850b8010345507000000f0461640c0541c6860603c0380b82003407030f00c18415034440d8401502c401000200412652103074030002d221180c950003400c3c0e45000050900d01c0e000c00c076034030b043c40d56006d50300c00e40d185ca842d96002c008003a0180706000000114060842c81c0c83c00810001b800074130000c01038000d020100c004241410311a81c190b07a0300c1081d090803250390001000e0301428581c101c00b000c9135520309060300400d0461207500900d00821400802003c114 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 230797895 1250 230796645 230796661
    0x40b090103080d0c0e03101407210c0c210809071208180607050a030306060302040e060103021e13181109010c0305070602030420040606020c10020c03070305031917 72
    0x2c10402c0d454005c02040300744ca05940e90b0244444850f1850000c4001a402100c3c451004107560040004041c0110300b11120700c0124190002d09050354054000989030041c400150354140e1140c501504517030351940321011808407d200d01b20400d81c0c076210100c4560311100784a50b5000766014040408840b611280001182040a080d07003141c100d0210083c2d180450218165401c02e410595199100c142d110f0249501840741c000a44810b144c1075252505011002440070809012107040580c0010072400320400000a200c0e103807405040326640d0b03461207544e080d40440c0380c094882c88985100c000c48201e0340318030880e00300000081490342840c0d0302c100103680405900c00240d062100c100000c500251180c80254401c500c0340421180c2c2c9003600c590b000380407022002c00b602552034400140280ba40000d00c0d03004441d4222421a54030703800b8007040b400c180e00c1c140040d40602c03a0010100c1041004009080746401c0d08151031103100600c54104d07074100e21a040000f00111781c00c0814604 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 230799145 1250 230797895 230797901
    0x50f3312011107060204180b210109020409051b030c030d1407051005010e07030b1302220b03060102060f0123150c060702010e0304270905030403050a02040b090103080d 74
    0x4001031000010b51902e203095922070341d40c071000c0102d03119035000038107014801f00050010304c0e000c08514208802800d030004a1206686003001c40c00300100000314074000740702504600c0c51140c0c050010b00840801c0d10b04145c1d1061640344a0700902c1c2d035400600003a0800158043c500340c2c0c020003e1100c681e8615054982c50503294812000400401491001c01d6040002804480c6407610004441d80740c105c0503402c0c2030020f8950b10401d420070704e04a4541e5907200d42d5021401c440c0000594400c01146000e880c071034003040d0200506440080003030108028405140304000a80035a042c82d50b901081403500f80003401031007280340d450400c80c490324040c800052085640034240213408c07000000254003d41088140c07500c1030340b06004000c0b01907420b000f0040b503100610025814a41444c21074200c42d10385030441a80b0040b058007020700207100d50015401c0b1070304401629503d5403642483c0341c03503600c1c0e15000c4e0b0040d07041c20403040403420060070480c1225004901c4030308001c0035481e0307070000e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 230800395 1250 230799145 230799169
    0x8030406090804030209090609070e01080a2a030f0507140a1203030902060d0b010909050108071a09060c03041406211906081f020405010507081c050f33 67
    0x2100b1401c2c40040f0040e01d61528942c09040500c3c001d040c10300d083c013065860482c0350f80011080c076141d0001000451400216a0800e17036200340b4407a40c000700c11020f2008119409103510724101600300000070312a84100004030140902c0a8400d81900c49241c0c504100c00912002d030086c9003200c040000d1481000d42d0158a4401c4c907000c103800380140c000500035081605005001035031040c82104641c1c10400b804010321580384c082c40706600d006031464585a6a110300305440d402208001d00307130ba06141c1140d05269000704103940b034450054070103640740c000f80100641d0150807035101440c0e107051030a803003440b80a441c02102c140540404081426400390a142c0350005800b01c0101401d003601500e40900480c0c4001c5c500801c0c01421100a014805101811700344104010710050342d005044800f041e4003c1d460f959a94147d030130111000002040b030940c1a80f812781400640800f028a180c040d511214001002102c180100c0c03618416552011503241200d03184449c15040c01025018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 230801645 1250 230800395 230800403
    0xd14160216052215180b09070906031a10031b090e01050f0d060914010c080105030d14040b030c070c0b210a0609020c030a0206090607020a0b04060f020d1a0d0803040609 74
    0x265008084c021303c400711625400c42c00502505c90440c08002d01d007072054512215003110250701a00344000050320002050190004050b154282c4d0300304601018070fa0281c5481c00740c00350f43c180c2c03035450300100140486002ca54914603030003002c010462045848030142c40840501250036480c180c1003180c158405c880650300300c141c1121110208503a841544d2501d40905419180c070b84200c0e1541e800c440340740031501c0038070480d400148060b442c00100c1000710a064140000f01140f82c12117020540502c0d40240103111002082117030840d5450302078a0301c1c034070030300190301d15a40700d020124507800740100c1d45101d030f0800e12107c0c0e24807888103580c075040000c20310f00045040d00c8244840682e801010080026400040d01621255040219035070007080f210240c0070600b42040000d46400c00b07081e01800c031680c10808601401320340e41c4050100f40b02c0d08030843d62080e1402e01d80d0050f110740c00002d1003840c408183c40c01c207410202450071289074405d0041d03280d80c0d0740e0ba42e0300d4014154114162 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 230802895 1250 230801645 230801651
    0x509010e150409120f080105040924020913090b0a0603050d08071e0302120f060d0b07180314070e070509011107150918060311060d141602160522 64
    0xc070109555078032444c0180d08a60307034145070b0740807400b000c0e16941d4181d01c0140614a00100080860080380c6402c1074450a91460007500d201e001c46070029025089656500418107003c0038513450380380e07005491081c4580740301030700d03540c0d81d07014501119001d200242281e0401c000c10a802c0b40b1800710580d01c02084d0504462070040101c24070401300d0720910f0b42d404242d0004141070b502c1001c15841d507005044c0c1b00c014241e850401c0210710807a00001c00103240901001c08240354034041c10280740000314490802c44410f949040c91103204040101481140c01081008500e0000c50200c9512400258464514003805074004444107954041545100d001e409004100369500c0c061b40d031104000c5654001071a42400e42c003020288150980d1080e00d8a01001000090b44002c1c0f840c240c14400c541c11070703c8a0100b0303002006003468070400c505108880c2e00708a0304104002d001c0542602590072640c2c0151240ca1840d42e0102c3d03401030560000340d1100421815104020311907040c0c83e40351001c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 230804145 1250 230802895 230802911
    0x504090b150307051206041802011209020306040303140709030203120901030e0304090518030a081b120a0509010b04050f06060c0f0a0c03031b0314090a080307110a0509010e1504 78
    0x14103032030b002520290001880050644d405280c181c4004d81c1080c4100c50802500341d0070303ca1b2078100401d0290090500c01d00455291180c03561f41d000c909215000340560380d061400e858000c0091800f43c1414512866500103c0c00541c8107a00c82c00c107a80d03025008141503000403012160b1074108855640c101911800355100480d82800904001c00c44401c0c04102818954070032a0035012060070030889501c240884480d8a03881100550000c0ca001e2402c07060042d081100104c91160900040b05400e000c41445a01c035002c0d4800c81c49882c03800300030090041a4020003065850940d02c1964041502c1d0200303203940b070610300904100398160200d8a40b81c809803440d41c240030382c4500540320000c6a10f02002895084800c0d803180440701e60346080c1680c40b6903409400c07111031210b8071848800c081401c00950312542c03016000390110785c003100c0d21240c640c64401042010f1011036401640d4000002480d801c01d604d0395411b8501c400b0b220100da0b42d800c00c0d01c0052610b62220302ea4001e4076a010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 230805395 1250 230804145 230804179
    0x1103010f140601020c1e010c0618051011070b01031104020417060f010b120a090503040f03080405040c110a08070f0b01030609030e0109060903060b13150e0114010504090b 75
    0x48005200e070301e20890a01e45810b20019003088a40352101e4020148403601c04074066111280d810f68071401d09001828800790b040a00c02006500c1034440d0100031440c08a0034440300140c01d00c029a200c180500081e83d104141500c2800b40020060a0140c4200103100180103c0700e943c0d400b440c00f40c001402c00341da0b20700c40144445100c0200009410020170b1005007454840c0c480d024018030407029107848003078105c040f5031040040c41480b00d2942e5031a40341c1001014001c441c000d0072250120f031201d540b203040840702035116120792841240b4041090212a0040c40750803680c1c40d078100078103001d417440d885108103a4031505084841149100d148400100d103021030601841c01240002034011540c50041c003519071050480313060044a04003003106560000312101070303c1d80b084001c00c440090038007041c4071302c691000360b501c0a42410b0001190a03600021001100e21a6030100b10716680c4c0c81048c44104150780d4200d0003d00100403e000c020340c10f4100110307140c070203800011980407880c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 230806645 1250 230805395 230805401
    0x120e03030c04090f02120103110a03060f060603060e01051c0821070e300f0105040317010609050a030b15030a0308090c150703080606040807120c140a031103010f 71
    0x7000610003002103402d204880d02c91256203418110b00100710f184c50312000295482403c14171009101e0003140240080c076403202c0003001e00a42d4400c10500030103039440310403809000540195000a071601800040c0101c980e4070712030486602410480b00b0100c2000c1004030580c0074103050380d011108000400d0000300c42c1d941c40c840491174881031482e90816a2008000a44078003a0741d124808650300a0780390203041c600390a091104200a071216040303803810b2030604012030081c02455107000100000d00d600070507000e071800e02090314000c03140c1c3c031500c098071490074500660fa00a8208201400014a40726000d900843ca0703c10800c1104403980c0024a0a40f50013012400203c101051102c0c038203040115921116045403034654040d1090000c900b14015580041c080008004c00f06825849540480f009042d4420980d80d0b42501c6070484900708805003400c40301c801c2c44000000e01c1e10610860402c110070000c01a121041c030310707110400c000700060400da51655079401d40e0180002c10384 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 230807895 1250 230806645 230806651
    0xe0c042f04080f010c090806060f04020a1808070302040c1d040207030905030a030e1311070b040c03120503100e01120b0408040b0408100630050312070e0f1c03120e0303 74
    0xb0003c101c81454410003060501b4640c014400c42c5d106000303002c1c05682d102805004c000081c1c80068440601000888110905c0701c2c0341c001001041001207108200803d02406882c0241c60a202c40f0400030006c0320211303c60301c80e0744800005245da001d11460160010920781d8042d19000b4650790b100e44c0040d0402d01c6038442100451131820030305c11a03062444d84225041e60701c14041000d0700345030305100c4a620694000a001e040031000103408c115182900d480a0342c0c002890081d02020908060100e0b401603407014036640b151240010782c42900b030b041506982c81c1d400c54024030707561580c45402c1400041c00072545000240030100e501030304400074100516000008100d11000f140507581140d01b1504085244c20407000000304900c90314a00c60058082c03608a814400c42a01b0032a0440c0030f82d1007124440007a407014040303000d502202081c1400400c550068507002e800040000404400c0302028012450000b4000402d009000c01030342c006d051403002c260f5508111a190543d4030417 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 230809145 1250 230807895 230807923
    0x51c0c120c17071208060f0603040c0906030311062a0a11012c030301030308010b030a0209130c1106010303140a020a0203010c020f10020309070302040f021b010e0c042f0408 76
    0x8940c00c014404264800c4c078001480b030070000d0b61818041c2c0450b0786a030259114074003500380000400c0801403008490401411260020001907032a403500a100b04010721900c44940300700301c00b00d00e083c840001800c1103224003000c80c040c885656101c0c4480307a01f200300d108050013070350440c0401201c028002d410002261400b410004803441310340810b64041403000c08403640c010b100500020350468181810741b000c1030135031a10f035034614042802a00c80c1b0440d958210324014000760b4a0701154110381d8404605440b00f1694a5207202c12580d500000d10000d800100d00003011070010f01c64a000f051b048655105448a04c00c144d000304e0700752203611706072000680c0000800c101d81402400400b003540c940d0301c01980386050041070781d9500c40c52408040d220300c1d135a41d43d41f45d00c0c0d1341680c11110342c0140d80340c61402d030303d2400c62000d000b80264141200203000d50009a2040e1409110b00044840030450320480b07036011031104041284816410782c050b90b010003000c1464001080900b51b10105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 230810395 1250 230809145 230809147
    0x4090f0b0f01090c1409040e03040b04090f14040f08090f0303030f01090c0f09030308070c0213060314030c070e090c06130609050a0510140405120703051c0c120c17 72
    0x150091120131a10129214800c10000c0011228007840100c1154030001d0111408120b40c0880440d1b50f00b103200319440304040b05000100020341b0045070308025038a00e142c40c1d082104050618106160000841d0020b080c2e1443c9ea0500d00040c90a1016100141014144842d240041c1c008a0300d1035006440f04c8a40055401c010032040986005075244504103141c800e052514030f5902078405041408003c3c10f04c015500014a042c0c883e018605125400a018209240400c900b0a0003009580010754441c820844003840c0707403000000b12001c9810010003010164070b00000e40c039422038082c00170410b500a9940758903496540d10080c040b080101c2c204540050700e882c0b001703400003000740e014a0049038083c070200015902c00b081075404022500700b12200101540003000f0620071908180d5010f104100b1320b02c1440c000098002c10f40c1c3c441c3c000c81c0c8907400400c0700481450a1018180c0004128100080c0000c07400d001c02e1b01c560400b0304114a0311080b030350782d035850039600d0bc42c4180d01c440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 230811645 1250 230810395 230810399
    0x31902040b071421040e07180b181903060f0b090907140a05060a0e0f0a090f11040b0a0f0210020d0b0108071d0d08090612010515040e0604090f0b0f01 66
    0x410311490242c131503104003070600b07880580210010b034026403060708440403584000640003402481c814079014003141d907000105880310326845064004044902d003460540d62904901d09080d0562a0007a44180e1416901460f650300e2402604917008400f06107610354804030351381e8846040c0f89004074810340140107074030304080b100380c180b510301c80542d40725155411040050351111011180000c0c803030300c0c112022405110201e201250300115098102e50040400210107030700b54004620362180b11801d00014844000000041c001d034051400740c076904104c4d203100d603070041c0d000740344071403140c010385041500c00d0707240c80f00326048040c00e40c0f01c8540303684055201d907a008010710b80c400c0c043d00f003540c03580300003025242c0d00e0300742c80500724081c0b071100c43d1400a0248003c10f43d60005801000140e84100e08000301c04c840c8028480e0744d0142d400c01c1c00c0fa2a4510018040d50141d80000c807103100d0541e2044100310207040d910780252002186000d078a4003056103544098402d24001a615107254 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 230812895 1250 230811645 230811683
    0x351603020415081e040308310c0f05030f0709090213090803011a0c15130c030c08010605060703080406150503010912020c0d03091a120a0b15030705031902040b07 71
    0x65440a610703c460301322003c100000b904410380a8200e207007504a501d1103408920305480f460204041c40c00258503948040c020084444403840a82e80080d01c107880c0c243d1385009150383c0c0c0400c0180144541c12031001886615102d900090400780010110858070004940e40d204840511806a92a09001005110109420140061420840880314506000c80700069280c41140c60301c4035404207410017095075140b0304a00c4201c2c1035040100724001550306c1c64002c40d00e107040d104001e40303542408400205441c0583c103440a80f60941c41d03611140d0f42e40c0d0743e0070004040c2100c60903e030140e900004a02903d0901c11050400d00c2004104101840424060325152a1220241c0300c0c80b0310300c18050010354400000c2e41211a103408180030305e000400c2d00317a60340c040d100143c0c02e080d101c58108003500003240c00254041e5001e5440040003c03103403454a00038481101c4003000302c0e070308001180300a01d03006c1034081e82c4030b18090b006040c0354440c006503030540c0c0309403030540340e038560301c0c1d41d24101c0b07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 230814145 1250 230812895 230812921
    0x30901021c050910051e19020a02010f052203050109020f04050c04090e120c07030b0f0c160203012007020a0e10030803180a0335160302041508 63
    0xd2005a80580c180c21107071040249944602d1031800d001c3e44190703410600c81c3e801402541d2448070880034016820642c18040403098110b042c0014880c060185401030460022842d942c0704c035010303074410744a9019800141c59a91020b0100b0740030a07526004c911200d014202080c0286110b24008101c0030124010000f9200b01c41e0f0116109034908001c1c03014030783c4400201d804603843c00d040841c40d80c0f0303c1901e03035040c800d640280340d0495000007010f18600d9000728109090747e108d0302622950752201d014128046208492a8519400410442d0030342d0003041c2c0078110b1284020008100d420341078242c104c0e410344000a410314100b02181260451a080c25050054513540f20044041e02d440200041400e0781448090600c000000c080303491281d0a00c40031107510411030807200d855100780350060101c007580103034220000700c410a8003128442d144c032005072042c20355071056490b2120700300b00e00c0d40e1804020b10700906600b00710001c0c2209a40b000740d1400825030306d41000c40c1c542409070f0703410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 230815395 1250 230814145 230814163
    0x1d150904060e0607020c0a060c0503091305220b04170c070b1c110415050f0703080f07030203060306010e0703091401021917220b09010e0f010b06091e0604030503090102 74
    0x541d0884038a0705447d40315066104101d554600c3e20744002011410301c1c50440c483e400310079070020840c1035110000709031a0085801103400c40700300c062103e03096050940c401c56000c0000c00c1c5c1c90381480403030041800c80d140180040100c40c0441d141141c6040307540e10380403040c0e00000c1a02030115441c102e12050030302481c0c81124071041444815140d101040e01c1380b00c0c9010300b6072000b00c01d141e40381c41d0070710800c107403008100c00307024282e50340c9c00c2410081d041c3e2404607180a0040344003400100090f110b4001ea034014440900101b64a1342041409807070040000c02c2d0004043d6515024000f050911000c4100d000032030000594612402e4100c88071301c00c1d50b100400521000214079a80211400c3d0385990100b0301b141641c510380103000b90200c141d02c88030805010f1800c6942808039040065200b00900003c05088840300380702c0a04150a99940c0c48000d64881003d00c940c101034200540c04545403090301111001500e040d000180307080d0040e4000303036420341c80420000da065804204dc0c0304 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 230816645 1250 230815395 230815397
    0x1110060503010b030f060f130c030309260a06050405160e060306060301090302100e0724080f0702070603050a1401030803012c1f0f14040f02041d150904060e0607 71
    0x440c80b40300c000c00580e0342d1005800031f401000c5030700014821441001048483c1a404404403029542c0c90070010140011402400d903103030b002480440e1110100002600c13241e5030140070382415656074440d140140b030020300c00d580c240078905540ba0700c110b05290000c003404441e00001c031641404000c1c9403600070b005126a000f60b140c0b0346003a002c00d40014654590f141c1c4607a01080b14503400d00490f00b00415031f80b0084181050f05d04000c1e002800482c0944010031030f03502c40c4182e5641d034030754142102040d54000050b0b00300202c11301c1305500c2900100c1c1d20007c000c1c170210f44000241c51104642c1c03000d900a4131020000b000600c00f00f01100c0142100504a03900d51141c1c80540c0d9580c0c504400207010030710b00151503442101c4010713003842040f004041c2e1185000d40c190b65105980a05482103007407922582c0b42c031040d51906c03444d074820b8805a500101c1010322810003410025a002c030040d001c1c0c5000d020407031801c412591141550303441984250030105503c01042966883c0c0400649400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 230817895 1250 230816645 230816653
    0x15130509060d0b07050c0102040303270308090114090907110d0203090916030e011a04060801020c07030609020a0b030901021206041a090705040902210c040b030a020a1110060503010b03 81
    0xa4595a00710750b000900341c204901c04900d413030f8001e05442c2403282140c50709565001107000170a2580180280841e022100107036103201030520640003c142e0240001031100005000f4401c641d44582000d0b40c0b2011040109803030240301d0000284241c1080701e483c40058050b0807900c1c070445c800e1000e00c0c20b590440c0021030501d41a10001007401000070f241561101550840080ba244aa00015071184402000308200e100e2003504288107008002c009010b40d0030031000086551051088692080421010f0300b1150300303556403000508512841641d000b01c0c00c0301c021803180580d8000714007640303005000503034601c010000d06000400041040d48101d14001994080c0705c18100d071194800012540394003543c1d50003000340c0d041d00543d00040c0c07c0a00c0400c945a0094002c0c100e1320000380104100386807a680c0310176007034680c4641d00030380180c19000e0001c80c10303012594014000300ba170641049480f40030300c07110003440c1a00b043c0041a0884d1128020000e40c142030ec2450510f1400742c002d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 230819145 1250 230817895 230817901
    0x20c07081e0604030e0d1e020102060c0403110906030307151401050607020607020108070207120f2a03080d06051e0a0f0602030f0309011506170108030307090b0a0e15130509 76
    0x1082d11028020b0010b02444a40410000c1d107599018402c1d00300da074400c252409104144110340c12041d1102012070140c8111800300b684828145c05a600712580581d40c4420048840c00703216403903401505240c0c1502c8240300d00800506018008603043e2004500080d1402c4070b202c0c00c032441d02043c1c2c006030203114108135000250711070000b150602d98083c2482c0d103003131b21074140c124507111096108400503942208014100502c3c00e42d03015000c0d009942c2607200305143e035051203d400070610b240000000c684401c20000f0b4000004d0070781040d41010000d561036032070012490f01d46c03412f440902405407039114070712145800308850001e08003110340c0c141c0c01d9080250183d6a0711608147c0301040c81c0110002d40c0110094210701d141d420a000000d1b49169528400342111900c021080d941c2c140340000861a40300c0001541c0c4505659a100d228217841c0c172034407528a9000d440340e50100803188511a80356140c01c02c01000b480a460369196546800c04c0c10705480e60708036000b5501c1604502c00f4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 230820395 1250 230819145 230819203
    0x12070518010c210909020a03091106030106091203030e07090504051b030706030207260a08090d050403140c0301091104062304021c0515010e0303030f040b19020c0708 73
    0x140c3e10300e0702552988005010031107003d0b900704101d40e00a58125000090200d83c0d00e074150003030901c85114450a108054003c01003161030300007401180c0015000000c00c101300444c002c08030081700c0c000c0c180000c0110b14843c0c0241422000e400407041c00d40c40e041888204001042100c0c0128003c1402904842484000944880030b5210792010913802107103c2d0148850404408910754521002c0741006440d80100001e94010303500c6440498040744c0001c1c4045004243e802140301c031350b0350b000d280908556510300b04140c0b031462840320348154205d03e9040c1d03c09114504559020300864100e02d14070b081004103980440e001100b180e80450342c0101e03c15411204016a28000c503005a12621060800c0d1000040088901c103910308040038002c45155886114014071001e80c0ea07e0703154042202850b41d00e20059801e428802d41f600b0011b40031880380001107802c044480c410510ba141c0d508520016600030710b00d640c1107504088010040201c040115100101912052256109c0220341c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 230821645 1250 230820395 230820413
    0x501051804031409030c040905011d15010306020f040e07020a140d0905041a0306180d031107030305100b070507090501320f0406090507020c01021b01031112070518010c 74
    0x10f11900000008a0b0343c954959060241200a440141007040301c40d420741400707806800c24155801440d130342229084281d0174081103868642034021a5400306918594905e8025030000720340310081141440042034114040b50000d00604503540140b007813400a0030280c0002203981ca0084066100b10703d40c581c2c06400203015011184200d800140300781c680301041c3c5406185121580d80b50048504000900c5080c00c10361442d20500e808075518540350000c184c040f9200036004025000301071184600081c403a401095110201d0403005010759900e031482c40864000703135003c45041d005040300340f144e00c0c21849500e00401046914a1002f03014080c5a1034602202c030341070811031018640003040d0303100d54401404441018104100482c0c2c1c900c40c1c1d500400017500d42200500503512a4909584002486141280c03800e080d03100100300800150020500c0018010000105110000c1d0f84034140c1c008a11a803901c0e1203103551042422107850082080800440c1400701d402c1400010a020325 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 230822895 1250 230821645 230821667
    0x5060901141c0c12030306060305070503010e28020a02010509060610180f06050702010f030b150c100504080408070609030b070503070c050d1d0d0f02240409050105180403 75
    0x961168003500d09002c0c1d441c0103a5a81c20082e1003402203240028a00e190a0f8109040c24040c2d9000c00c403c03606c0340c4046003550b038181c03069400910180014030451400d02c4203580c102201c0e0220f41d20300f00390400907568121004d840d0811455010800965054080c01000da01a1090010f00300d18600b0000249070112074010020030805c4030680401c880c020810741c6d5000c1c004034081400300d61341d1600c000b80f00303a01c0507004900155040e010b2040310740c0280100250780300000d19011a250420204448036001303200c9009c03991082070f000c807200e65032910440d4025805410a140e4460401907968075001a41c0e1028042111540c42000860a4400d10070b0300510302e0b1400ba5565102c99204403030141d1092006052809035890800c1c060350071542d104024004500140c01d080303000030070881c4002e01148090189143c490709000103140c144556021300106000040c6a2100b00e00114500d80040c1c201d515142c3e5038400601292070081800c04914004e072945207a2481c1c1540c0052503001e0f09 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 230824145 1250 230822895 230822899
    0x10504020d12121e0f0203130204020906160f21050304110f060d0c0306170c1c0c0e04020310180b070509030f011b09060207030b0c0706020304030f030506090114 71
    0x2280d80b081c4052280c00c807032210a006110501c01085070800c1c000410758125208015180b405000c8619141c80e4000d5034854503002c440400603900980900001c0d5004904442c0d00580030407850140501c80c07800c000e021030098184003080030135481c0c00c903118000902405146010303014482d0ba80c0e64400b04480c0d0203603000341d0548071401103901146401d00b0140744554420808140c50306004200d903c070600640595509100c55503681f4030070a2208003000e62009103401007203101006042c000100300c0b8004034020006414101c40e101d20107075201d9034200c8027400c090482408154901003018100713582c00c46034100b1262605101c1640d030140210b000a11154a2500052144c3d000d1007e40e0089a000740c192030440b80e104e401c00707008241b030503051410a00809140e00205105000e180f0541c0c1c21500108440e0742144c44d1016003500003004c080c00d8850800007080002c1d150f0000d18042c80c481d80320403084e40700d032600c0981a220020045070048009400410414144e003040811207501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 230825395 1250 230824145 230824163
    0xd0503040506070c0503130803031927050f0f0d020106050f010e0f04240602070f050306010b31080c010e130914070f050a08010932100518010504020d 66
    0xd4544107007036003c0d40608401e09a03003282d0000703107480c010008510030715a00507a450040c0e032100cbe600341155109954412070a0300000c80c0080f50756051680b0101074001c004841400104441551038200303410181d28030f0340c02c04020603512903024001e007800390108442d045e8000b049000020000b02086000700e11810803515906519102c590104160032084052152004e40540c0c1204048102d403140c08010f1082120000e904c2815540c0001580c0d0f0042c0034207400d91800700b081c0601d41020011095150402c108445c0303014004000c203003019031544c4500403071860981403909048268040c1818086510084819070303650f107614111902c1d1200000415009500b851503505126a500074841d1082e00b202040100212050008490342100c441001c651100422800d0fa1504e22008000c001506c100a000301c8814400410311032902e0032000030300310445135907450907584851500c6281da44d00d0074804400130010070710010b540b11800900c0740e81860b5021410f0311004210140486030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 230826645 1250 230825395 230825417
    0x10f08070f0c08090a0e091204030b04022809051006032a09030f05010e12070f031d13060f08030403030210050601051c050106020606090103030c020910090212090d050304050607 78
    0x107030483c01c1d10542c1c8805810782c40d1043d220501541010310170307241c204031403146001c01406030300c042013100c06585d413001c281c901907101c550903c030300420043d07001000d1250b4100303240c040da4507014803840200140f54004c2400d00b40840d034072003c22110b400c00c41c2003600f0620200f206c5104090a84809003030410841c0f06a01c00d2042141c032003a158000520b8003521480c04810300c174054101034881c0340100195441041c195007070503541d124004000748022903036184480400e018140803a0031a03461022002c0100380c07100010340011810345c8003c01145c1c3c66206014000d407040c0407901401c0104000c61030207080da10065686c880e421034081d07080c2d0710741e0b00003030b11648100c050369050088604040400a610030340c54024040c00d000d64001840741000150040c60500390280c1200c0d05a2207051141c1e000b0303028400203c1004001c3d0845030000880042c00741500d10041448000c58980c4410030f040c200e884604080c03c000f4a002084010b00c244408500041503e50300100107003841d1038960 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 230827895 1250 230826645 230826653
    0x3060e04330c1e03020421060207061107140c151312031110051e04210c030219120503090109020d060903030e010e03191e050702010f08070f0c 63
    0x140a100079404541019011405940c1094010100761600b4400010140d03068004030b00728056846060f2090510281003503103902c200c11034032201ea010354005460300f00c26842d0401690340d0344210203004070002980750306101904035070450a002003000b41c40001048800141c0105c40078420042c407610008628102040c0030703c40100a060083c2c00c60104440350402408141c0001c80b42140e5014404510383c582002e480f603a8410321074117940d4410002001381c2d802600000030401c55104071207907030241055080313044140305c602c0303140c0d40d140d07401304e02d454024200707001c000e040070360742e1009000311001480e0350351b00407035010080c80c26030b84035a603485030b55015042c441c402a42000404090034148405070b001086000d000381ca09101120f0010041c90072103d04290002d0560820310845054911800d1049a0390081d85001c008051800c84010700240c041e801240118200144d40340031540c0284800700244070504140605182034540030b002e54044844d514208900c0c00d400800300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 230829145 1250 230827895 230827973
    0x3030c13080f0303040b070306060906030e0307060627141315020c100b0111210405040516020f0307171c021c06080703050a061d060a0c03060e04 64
    0x100301010450b081e911410351507949950007681c055070000d03203160000b801a8000e01a0504842d41c50350b4802d40c00c0c0c070300709044000300004d0082ea021400700708038602c0800c040d4010741c8041c10f42c0c00740e4588c40303820380c16030800343c1004102044222030500c5602010b141100c04940e60050b07000301e40c100740441920b045c1680c22800d18800b0301182c40820411642800000d1101c2c1200c449a81040f441e88a40010366070b8444c03a000380342c501d510943c4c020600c0c0e044840c119424040c1414600c2c14261114009001e407841110304800c2c20701d0f00498411450f9040186022948402c00914030300000e5803210b048418001c0b02c80074526400180c00040c80580440e0280004107a8404540328900d91800d02c00120004100c02d04081c14040080354080c000319194044079400002010000c00e680d070ba000180054954110309640c0c003503261720003080117100031841650030040003c3c2d00e2a034000090200d414a0b0401d0411810800c200030028132110070030008110440880455100803c8101c0300c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 230830395 1250 230829145 230829149
    0x270b030703060510020c03070e01181e020703020c0414040803010311031207050c0307230108100906180f0203010506090108040f12050c0111090a03080d020408010203040b151203030c13 81
    0xc2c07450b50301d8a501d41c08145ea03202046c0031001e480701159030714115500180300303028080c070401e00c2e08100c559006166105d484c500c03100f005143e201d94450f003008401c0740c0110406401507000000c0488592409109100782c0118180000d03a680c1080e4461000c40c0c001400014181403031050302070141d6400300505200018a81ca20300e9607039049103016500d079611001d5007402480750340e4000c80c4544400f00500d16042d05210342c400929a020011107231071401402145120404441c0415115058012280900b0304044605898440c581211003101c04d0003201202e540c0c030600050006941d58004c0b03480300002407a100419440e5030600091a04840400824841100004941c000d4008020742070b0f01103500d00070000800190f058402d14401c1c0d425650703010700720000520006d2041c00c00350209603070801c001810703c0d0301d8481140c2264030980d0140d0300d4120450401c2441c09508081d001d0003e0152040c0f1509c44100c84200c1d9030313000c05002c0b40c440420100c0c12016581c1305d0904800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 230831645 1250 230830395 230830399
    0x201050717070c0e130b0a11120a021306050703050304020d021305090c120115030b0c0f0f07301d03060103110a0e09030702040f0e06100501270b0307030605 69
    0x1035103060328540f040303d44010b0300c2098400d44218001420215910000004082d000350070303d5a5039503098901d1000f010b0294050220201c00d10000e04400e0b00302c09036900c0341800c0c002c0140d550120b8890000a091079034404420058100140c200007507000c070980790080d81c113550884522040f0300c0090340c400d1003201c081c50070a1900b4204203420b01c0000e2158410403061300e0004c450020002c01c1401c0e1071042400120480c800030042000580d42061160b000c2840400710307040c08901c030a030700c48035031050f40114600034003c9641018445000c09161026006100000c100326a0b04580700c240c000606452041c040d15200458200200701d03000520aa0010180c4a1541c1c4a1a0484607486140c804078051502c500010800703090701c210180c010304495000750f0400c1061b508000141c100c80122001c24ce844d003240c60000041003020501070100031380424200c904040005001e1030165075032406001c403451460403440d0710041c01c0070030740b0342031002c260392070740c424005801900603640095 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 230832895 1250 230831645 230831647
    0x1104060b070302072c0c0d0b0d05060f0c04060e040f182307030b150117040506180115031704050303030c0304110405061c03200a0b0f130201050717 65
    0x90101030f4045000001d4818807a05c032520001c1042c11541281c3d1034541d0003d0300307002c803030204140800e098050300c1e8091081d840442c440380c1001c042800100f8100c0304650036485a018403600b0b1500283c0640d101c0c891054260400d40f07007100040035102c80644060203942c0d9010705202e541c00c290481d484042501219585000652600342401c4100c04090014000b255184083c1e0440200b81401183d420052007506511040f98100c80b202a020030a81400b1803d159401c0c00540c01d007007203119502400250a99103840710850360001300e54059213055924081c1e2071117a03406205592815a9001401400a040c000300482d00c1d034032560308003541c1444040100040c45030038100941c429480b451411080c0f00a420502c41600c606950407036000c428000d400c868013008400100c0c0d618080d10b841c0c103110421041c001d050410b504801421a088140d27400240300842c540581c1042c1c07500b8610381c003442c0c6038604420700d4486e075800074100200014644140600128a1003048110312681 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 230834145 1250 230832895 230832907
    0x9020916090b1c060504060b1c060503060a0b100e0a061b0503030906040317040308130f0f05030a02070608010806180313060905010e060a09050909071a040f12030c1104060b 76
    0x126402c0c1c2c01c0f18101c0420700e040c40004112800d140c000c179012200c04200741414824030807840140940703000002000a5a42da8001429550801c005070186c860300344c001810700d00d40710502c500420b41644640038072002c0c148055090312844000300880d00381d45014005050394100d210141d4661800181061001005010700f03004c012070a14056071198031183c1840e0225540c0080240c4104d501401060668000903140e03200802e0800b020b510840c080f05140410baa40c0d10192011290161026800420325444c600e8040044802030b18560422804d40d41c90100c0036a03a40030001c2840c1c800ca0100c00e4080641c103820010355540540190005100a8440798014042c01c01407103054001220424544100d08106080f02c0030b5492507036421441ca8200b030309000842c00003030480c000b1842100c400103603400a025408480400440c16030f60740c2c52502e04400d4201c020381c3c12414108815541c280d0000c0c2d08400b40701929030380020176000221101e80081c00500703656000d80c8030341c4400121 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 230835395 1250 230834145 230834167
    0x30902030105090c0a06140a03020f0708030a0504020f1206060d32010c03020f03040f021201090303020706060806010b0307110c0a06020a0b09010e1015170a050c010309020916090b 79
    0xc0b400c413038020b9500c45141030355071400f182d8420300682c10303403c040010045906a1482600207001c02a00b289030380d450100e903a074405215074804c031940064103540300d00303000440c90850004121600211425115500807080b02c2d9200c10001c0d1045200c1c0c0080c085217400c001c40808032034035004262600030580d0307401d2109038115619120406e00c49510b0445105d201501a10a803034820309545221821540c1e955185500c0c2402d901c401e03644108140000342caa14007d009024250348281e4025803154a03602d0104107848894200d802c00b0b0300030343d005016891040d400d41c1e51205061600f41a00c01859003803d09141860605a42010721940d0106009030009501c0300f0700c0788600080300a907076a519510b82281e1940202411399000091044851035441c4c104080b02030022903020307081a9102001420a0300c241c0500a441c0c0010b40d0640a01c20140401da41c500e00a0030306020242d4581c1c00201d810f2001041c11501c2554041c0c03040c0c4883c0f0621003030b400382050340c0f40941d4a48040c84 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 230836645 1250 230835395 230835403
    0x3080a0206010905060d03090308030a0e011d4303060c051c050708070f020102040b0703020f0609060403050316170f060406120507030b07050c10020703200705010f03090203010509 79
    0xa6a07020501309800304200c4d08000240300130b0b154142c1d84020300c050a5590f5540ea6600141c1003503200b0b80c6030040e0078010300d000e1286d80224a00f08810510400d04509402e041c10b10040e180e021350205540b50308504ca108111000419041050700321070031036807650194020f4030383e410107069245406078120009030480000c0c01c041d00982c1e0713a003542d28014141d440035038004a406d000028a18004500d045000780c41d00407030f0712110300001d428a616a2105041c40d00700501c25801039000c81c1410910001c04d100d0640c1040f520405480c0e20318250f1400b07000d512015150304140360562a81c960ba00348205600310b08151000541c8195007019019850111410384c0c465109034508500040c000c02c103004001e0f900d0307601c840038203140351031526000031034400140407109000f820008008016070034000c11103030b40b032100c100684442c0c050170002d0042d0310300107403054000d0300764585400400d00080c0c01c0301115001d10306050340d00c8605a04034050051107070025010340c00c04050111101c4049 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 230837895 1250 230836645 230836649
    0x2e0e03030c0304270b0114090301230a110c1b0619110111070f02040507020c10020a061104120609061e0b040f020a09090b03150c09090a02040b090f0a03080a020601 72
    0x91001301d41020b6400c0000b0498203402d21950118581d802c00007243c214800240c55010b0004000090015164118100c9c0d01100c131744508841c200340b005c00407140000d20a8001000082070480d040c4000124056a19110103040545200f5042c1145400780c1d100c078200c4143d4004581035010100024002911000c074200c201c00455080440003034802c040301069600c2c0c0741c0c0100e096405c82d9496002e0000500001e843c517400c50144000510b4a40c582c690101403c1c80958010042c1e000c480c10840c00304c41900076110198082003001300070001209404000d245c0c0c0201d030000384015140703030820040190030b00010300c00641d110b810700000f0b0942e02141c00d441d4107560a05c0390354201c0c10000120304c9111a8400401c9040b44188401c54141d481118182405422038001c150385008420391258220b41c0400440e1000800d91014180050358503000050850250b04250826414015034010808264081e9110171b03d00c00c040d5071983c0e59030740259040140d90b80e88111350720000703446800c24 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 230839145 1250 230837895 230837939
    0x80d06170a03020d030c140d0905030304050d020f060c0304061d071503060807121e051501060f0c1214091305010f0e06061605150a0b2e0e03030c0304 66
    0x100d10341c580f13003070080c060901610000c0e03139100c0310014004c40c800120740060310070401180ea142580310005004000842c0694002d5000b008480710299009203005a984199a510f41002e402d0200c1d07024940207032600a5400400441c4000340344881200c1007690058a218501c1102e80000707002c40701d246c00c01d414a015507014010280c840151035514450b601c9404080300c6c043343c020020400c8624000464103008907580c0c1081410740710344c0e203000f011000f070361419030365840100300254003c500b107500d45009050801800840b610345c0d035503622a070100f40b42444408034400d2100784941c0308584440400174800070350340160a42540040c034090003480b2041c0c0002c500820090740c80e00300640318144c01085c991819050541d0892507001c810011583c070b201700c0407140114601401d031180b0443c1740b00400103a101c09003003040003800300595216441114041e07010108004841200584c0f0340c0d44c1000c8000c0380b00c540220f0300c0c61080142d0a440ca010101e00810320f0380d07480c880c51030b904c461 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 230840395 1250 230839145 230839153
    0x2a0f060201141006030905150106081005030c0d081b030705010c020c0111030f0901030603060f14150901030210090308030405010b01080a020414012d020606190f03080d06170a0302 79
    0x103182c8003482c55a03040c2d0710301c10200d042035810030456100350800d1040c11b11036000d45a8035a00309240d130f10f44075020b0300114046079070101000a03c115402208005100c1200140000794405022a400e4421b652000e805c4400c00a0f0306a229004047c040910660316011241d9510b03460422030300030484d113403103400140200c250300c3d14250310078486106641075aa001e54600a01d2000600065002c049c295042c103407a04000170200e40f00d4859480b100320011008241014003500345501004000c06515401000c404650565103611404a05496054412038002c1c408000d003980c031120a80e000a2449400208000803c0703c190040c0c510030500b070b282d0181036103c40800358181c0c020f500034208901248901c03907101e90b04c100130a41264846d95020703080c0004440c4111000e2548100380070140e4440300901c01039080c030215807804e041e2000d0083c1d02d291b0500304443d035900210302c80274165401c0454410308030a120362218000700311212400e04240041c0300b1312511115900415409030203 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 230841645 1250 230840395 230840411
    0x90604060c061d03220b03190501082103041103012c0c10030b010e040c0e0102120405090112061107030c05060f07080c0703020703060213180204030f2a0f060201 71
    0x2e4000c0252003014030304084c500f4140d0b09000c0560b00502400000c6100104010004541c2800c400450007501c10002503188511040184400d40d401a4030001c0258080d030807400f011845ca00c005540c00302002e0040d039480c0c40754205402282c9280c1c0005038154a090f0781c040801070001690021071004151000aa1098481e61515007030b102d04140d404c10b1144841d0030302248603038090050386105041500c0108403880204044540030807010010a007810f820346041c0da0100815024900c03600c044615090502002c10344041040c030400007450000c60050381040810340211542008424a00c1d8950500b400d00419030b20004405031458080d22002c103840400300b40b2128441c041548906150b5140d51900184950081c0c1c8103a045000c2d1038000310002e09107000138020040f000c031040004c0707820b00983e00e012035854452440024810030080000a84690400c5450303a04a41069018400400409002801440e001c108810200404901ca00844074a00c00b40c880301d0f402000030403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 230842895 1250 230841645 230841671
    0x61106070201050c0715090c0803041d0108100507090e0916090506032107020303030c0301050a060f0e01050706140f090c0301020a0207050904020406031401050402030d0903020f1302090604060c06 86
    0x2072015102480081030820140c5c02290a9003041c451301440c90800164a090315200c041c1d80380e05d2500108000d030000203042004020701034456061480c08603515015525000440e99140c94507000e0410060b101c0001a0000e030048803804006c0240340c02d059120304c1c10008581c0c41d65640b80c0904401d0b0022640880d0003055807080c80d106000c05402440d0491006103004c141c4c0c020642000c4080104000b1100180c40a0018600036006d000309561607505000402c0b4a02c43c4130341160b0100003c50210000c001ea1007224080d644d8001e0038580e41e118214203040700030300800d17044004d8245440c000c0c171048898007914a84a172040307909841d01c9078201d201f00740c02e0303100d00c02c104401039204100c18409031520100341c5401c14030040001032460341e0f075503420410019401c50861903964560401c001d509040c0500d5000005a203864040360b811a40020364803a0040450f40c02048000c0e020b060344402981111983c0d007000303218075112641c400d001084d4201c01041110154100020b140c110 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 230844145 1250 230842895 230842901
    0xf100908030402151b03031501080f04031206030606060c0507140d020108061305041a0603010920031005010b1e0717030a0b0d03200601050f010509040e0601061106070201 75
    0x4154811246480d64990303800b00322031640c050541c500001c0d4108501e0181705515508803030500d0446000c0c45e01ca103020b1003440d011115080a41e4180641c89082110031048909480d501a03031505100d095504ca240d055801844190002062280b400c0b101007155900906400b28080c402e1080700c401540710303000e10354424010a0030301d400c401d02c03600c804019801500032700c0d401500606640d1043c10005190030949070140d9081e581500c0003018131450300d11404043c1e501c110280d00038000080155920180c00048566548580110003400070300c0da0303810300032a0261100e5580501c0307196100c1d142602d89900420b01401c0014060402c03c2d010341d103450507940490341002c03010000780006000c400150388000c00511030310340d0f00c803028105583d80c0d0610080321030285c0d40c0e55005481300001c0090500200c05d040e01d940d4819001000a5a1030a07107403a403205080c40d1481c0c0b2000c0b030750003080141c62a221002e03a9409510000b05489912900310f0364006d03c030310101c846a80764560181e0032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 230845395 1250 230844145 230844161
    0x3060c0c0203030d090510050406021b1920100306050f12030f0319020f030703050c070507031101050c010f0b03070e040b0411060d0219120c0912080f04080f10 70
    0xd50004d022000c1c14040c00d500000c40c1c18001c1007a10b4021410a414000300c610454007110066804241000390484064807000a0180d03900246464040c440008424920700c5600500c07100d41c6120328010540000c41c07080e04108080c00c03020400801d00d00240142c0101c1c0221805440815011421480c0000d40c04034003282d25405140f03024030700b01a0a0090340002c01403c1c500341c50010030b0080c0d085620040900302584102e254807410501002000d4500c0605141c204490034481480031400100380c13442180da0041c80f002000400d1001a1541d0007483d0154000d54070b0880c80b881c04299980003029000012410f981c941c58813421213032030240080c1c602400c42202e10780068001511208020303940b10b40285051b0420f11100503d00690f4080804060921015506541c1041d0040308002c880160f02c0e200b804810440540142030b12850300c89d94484505e1060101d0512031400126544014001e4116a40742d0720f8230380055444803506c142071000d201e10f009440d0000e006100d6619 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 230846645 1250 230845395 230845399
    0xa050105012715030b0a03050105190e03030a1d10050115020607050a051804050705090406090509120d09020d08030f090105100510030b0a1805060301090b071b05120403060c0c02 78
    0x342e19820004200e44034603e0044810600d6034441c0804c6440c0d4844006000844c401d0002103070343d1030000c120640100001d0200031a0505106090040800210981750700401682000400c10302c11619815080b1391403450781414000d060300744616100c1500311505890314000030700140422440100d94600f0120f4a078000a501400200c80e078a21400062001421044003034080c0070003400018100e0b80d00f55041408110005070201c001c0c1800c0c01100000d102d031440c01c102d1460000c04003903da071921202c118440740005141400c003801035102c58000c940203070404441405915041c65240d0054a246085201d07010010305207100500480f031041244181e40013010385050248034180480f92090010b00da1200c18111841d120440204010030216000c55180440f21408400721070003d030032030340a03034180f401401c00715a2010105030416010310709645c0040e07844004103010703a002d07100240325000e5031500000048202000d0002d6a001d440200034004000109075046d00011400035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 230847895 1250 230846645 230846717
    0x9121a16031a0904021909060b0306090702070308041203110105010e07080907140105030405150702032709010b0c120a0c0311010905070e0c0c010203040818060a0c060b01050706050a05010501 84
    0x1400500304203140c0c00c090b100036429454403540f1001131405540c0c90360000b03009c403a4040200011850321300f655580101442c005000e840f401c41d1100318032803169004455160020041c03c00c20140b04000311602c02c91248001c11955031600510900c0f0030040da01c480006420001081c02003d012440404507450f00300001c5846025400660b01908018001da0ba80d0044158001e4010010b042d0b081c1f182c00326078051a42c0b816203801c814000d010b000c1e81c100854100030160b46071a1500c1d07000c3e5056600050f0b01c580c541c02e40740441498510492000101e1900c0458001801034000d007036060154801d4a03515400c0003501c2c095401c8940f1114050143d80c45400708000b84c0142d04134440d000454450154901303202c0c40c3c0301c1030a980c0f09481c01c4800c070000050204090000341141221820b01320382c41481d01d454003600130300303407600d803400a40b01654440b150101a8018012200d07220b80c0018203000ca071030144241d8008100910519001c100d07401c801c01e40140c0f43d01c400000c0c40001c04849 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 230849145 1250 230847895 230847901
    0x1504091d03091c02030a050607080a0e12031f15090e0606030a11040510021c030e100b0328020301060602012702150705060901140709121a16031a09 65
    0xba01c3c03110940c4041400e21506041c00941c8044c03180203071b014081c03401460075040207400207000502c0200a0002a49428085d0540500c0410000480c048500b06103071291662075030b00d0150003402d11a000c1034001071800042e85542d142e80d082c620b040030b440700c0341410b61fa11104200010102c40303441c0d0000741000060142140c5600644680400c0740c16034bc106070300e0310080345c00d40030f440c600000540e06c209aa044480301009480311540398614052080202160b8440c3d40c3d0b0001d9201d802096440e025807966544040116444000190303c0c1c15050031041c2340221190800381100b42d00a50070050089109030050048a0851484120388102e490b00c0040c409500c4100324001c0b03034862032411505520110040190401d03a001c0c5018000509104582d28211b403140d0407441c0e101400042040109134010040504940f104080c0e100154640c3c138010200c102100741c0c04078207940c01418040d00c1f00010402403104505514108141418108403116202d00419100d41c040840382c00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 230850395 1250 230849145 230849149
    0x50a050904241e0603121b080a05071a010b03010b0904060f0e1006020a0c05060c1005070e04110708030a0c02070b030906070305010522020c0307021504091d0309 71
    0xc10303544540030b003030001800314000101150940340340000d80300e05030b203a62000041420f01010481450804002080820315503992091681500c0e10b4101c140840246026054000304d030408082c1e5502a09007a9520000c0e04042e1641d0001c55007a02c0a0686039044003001a8408601303040c2c03585488180d04603840e02c030f032070011544021007080d003140c0c5903400020002c0411406402400000642c5001807410548204010185070301090071588210420b01c04075100d00b80317240135104c09640955962807100c804034980300e007507103002944a00c1e0104008072240d00110402210320221307401e0010002000a0346094007803408003500015007040420364000c6c042d03001040424160061301d10340c668482400c1d0300c03900201d461010a130230403020002c0c4580d00d0311509001d0103003240c00c54409095503901006a600711110b0800c840d9000400c102c80101c100155000554018505165110085440250307034000c0d03c21a00c1d51400c08206503941055540001031030000f05c0c000718200022481 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 230851645 1250 230850395 230850409
    0x40302070b0f0702060f090f1f052a0f1c1202181003020408060708070206040f02031f0204030606050f010c03080a0f020f03040b0603011505041a030a0c080610050a05 73
    0x40740c0b2080c1e15003045000d005840d20005401c0308040e59400c561508040d13404d1000109030042c1c02031091501d891420750660320361080066290251500325115a48103070000c00d001c20f0508501441c400c0003d2400e0a014002815407101e04240b054405200324260980c0107040030851210102c0c1a102140312500c02e40d41c080d003c0c0d04055880010349600c108081194188d150180c2d0000917000a000c0c40500800c00405c0d4000026180c8811a0314003424001d4690802400007000704029035420750035594200542c01e040c0d03802d031080450f0010b00c04a0340c0c000750701070301c01103441c0ca00785400007403070b481c2c03c1c2c01e48114580103031502c1141d80c9107544c0495013603070000e0010103196643c050b40c04000100d8800341040c0c241b01160155030b801c0c941080407406100814082c400e038105104001c640182c0f072006401c60342d0a0b0340106074404440d4400b101d0140380b0100903098401d4452901c140600c00d10903201705c804c03030b070151401900d5800800f0502c99541c0900343d00400701c10800c01690a20380 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 230852895 1250 230851645 230851657
    0x717092202070b01080304150801050f0405060a08030c010c02150402030a08030403020312010b0901080a060b180a0506030a06060914030d0e0f032a01030b032e0603061b08040302070b 80
    0x203005162003280d6985555030602138220700310581c000308050040d0302a1210303103840d11016040c54a4158075200c00900d400c201c06c1ca5560140da2501d01048440c1c03250020440a041c0a5054a1300d0302c0d0001c0741c9500908a0398400d000505c90400885035001190481d107015a0300a0041e2200f40c9050310350100340d61016004600310f00c8100b0204000200d081780e100e018202c0c0c1d8040c580d86464007000140700d020007078507010a15140003800c10a080c0307003400f125040c901c007000501c0c0d0510311000113248041650301040c2c102c0d400108109500d5015806107003560351903240c07142e11a032102e248200407040c0444a58159200803640d41065018812001001c20001c0c6428030f84c90030314001c01c0c00c1880d1118007001c0c03140c3d8900011482d55000004008804080c40c04001d04448100003956502d05443c4540010307800d81200314001d600c1c00480e10038a0400d00d4103015550352868584018840d0716013070b0303145131084004100304a01c074000c030781e00668242d401040b10f6070401c8a184680da1000d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 230854145 1250 230852895 230852959
    0xe0303040306060e060901091a01180909080309070803030c2703030d0903030c03090c090216020a03080703020705010c1101110c0d0b090705040b060f09150c03071709 73
    0x24080007000800394024440a46482d8400c3c03d540c2c240700090204078130060700705000960a201d03403810980300002413003c10510902c0c2004444245204161140d08140c014408050500c06400140a040c200550040a6410071149003036510303200a034807400700b91120b002140d02000350070014034584480d240b054000c184982e45e00c064141c00a850340d40b00c48e085490040c4c40784088028181c00d842446007140e05414103011420300d42e038a001c0e06d40d07400d00400c1d0300d40d64085451649a4280e103108641c03c3e5025280060840e02c90805800541003442c08034014841e044c0040307040c2d48900c4103404c3c41680513600c00260301c0320000565030000c8405003241c052144074000021503035072483c00c0401502945242801c0c0c209404014107000480e001240228140220302082c1d85480c1c04441601c00d0740320100b038480c0c05003800202805403118407070a00c3d0a01090044641c0004401044c6c1c2034450440840d0000380404190203074014010810782c81078420000c01034090303407074800000411342 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 230855395 1250 230854145 230854147
    0x1b02010605150c10061517011d0916030f1401020403030e091312030c022112130203010609020301050405070306050f01120212040302061b0c0304140d0b0a1a0d02060306010e0303 78
    0x10009070000700c640d164012405503c4d12070b10006117a400c1451f00c0110301aa000281d402d6043c95030000c0d26007100068401202c001c0c0300018585002441100e044201100600f01015a0307800c2c07807000701d40f4aa906460281000c00485168401403080303074100c85d455250250744021042c00c200205a008184254a110003819400010820f81c07141c40050802e803400a118100e0b4a80249810840f00070074000d02a03458100f4100690344003a03a100b0b00030036a400c4002c2e6160181d41c5600c845641300290550300b884008524500f05801440c16100305807020801540c0f03408084055400900c1843e4110b03a04020f0b0910702d511a403500014401c500b1409450031460701154001c80004440035070040c4c0003481400300c103040e4000481d44504051f1000c600f071889003410143c503882544281e00d04c9a0480f00b021685031548507456007050f8000180c82000d1030242030300000b801d150107048259148281c9540740520703140340302e8202c003078000c0d05841c116528035005642c202c5c08040e100354180302c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 230856645 1250 230855395 230855413
    0xf0d03050c0a06050109060e010503060c0901021510030b0c03071706060435030711100908060405160602030f0301120f080c0c1c0b070e01120f1b02010605150c 70
    0x1c00c0200b0003a95120304030009456242c48035250071511240c10148400582e5001044a9540050361a0704807808010305555004d0307150060303181c00328039910002e58a644c101044086645401e184040740d0060400c0d9005980cac000392152684411601300300407a240c0d0192041003c0e01416959118a015224502d040d40303500903402d0002a601c0c00901158a80030000c51058080b850884040c0c00b1200460500f44160b4548101003216020382d40550440c3c01740409040c81522108020202c1c082030b5002424981000d0741c54400c1905541e2001650340d40024001e440003007101c04003829825034a00710303401c0810400b030113140030303100341c0c1c0480d0b8408456010500f00c4006000360700081000340300102130702040c020004403642c00260760070341d00110f01c40441e2070200d90683c4040c0500d03052101809207001078403000d0b400a1401402440c1c02207800c14030317031503600240800d050805078401411110804034240c500324010720340c00608040e003481c4012030103070140c02c582440c1816100181c1c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 230857895 1250 230856645 230856667
    0x60501111f0608030c01020712080601140a0e04051306050c0c0d05090a03050111040f06090b030402060c010e010204081629070f020409030819090b2806081e0c0f0d0305 74
    0x45c21031180030b02165400141c420410030105890a10803000f810200d46515107040041c2c4540c00244400000840c0001d0341e41c112486400c1c1501c20000050040020b42002c91040c0499101140203c520514000c040740440100b50281d07980144800d008112102004000b02c855401010200d50010185400400003440a0251007a03200240e0300b000d45a0f46020001c0142070340c50340c051002e210800c03100303000200e2140c044a60141e01902d81c565280c4100b002e01e401409030350b0205409520200d40811403d80100d0701d00d100c0044c003144015081d4030385846800e1010022181c14141e1207490000142c440800050f10030300d400b0b1400340ca0b48140940114044d900c410b403048000644200c09c22940d00c84600208410b05110841000021295900c0b070100090240084072424030800403003110036040721105140510981e42404002c0c1d5807820555116102c22048010440340000c00e14050710000d0010030f0140003e222455129103203040c0b0141c00e841080581c200300b0104405500b507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 230859145 1250 230857895 230857897
    0x10506032d12070b07090905011503050405031c0606020c010206093706060e091c030f020702181605070f030806060c062809050c090604021204030507030201060501111f060803 77
    0x4900403413200364203190484000300304448079003084c444149440c006003d2080304415103203030030000d801d00085c030351a80e040c500e1441c018081c03900c0f8100a04900c10344015100e402c02c42c12a203c603000c86405211080041e615410200c4001089a011101c080c111119081c0e5901e6415500200c92180b800ba2641030b070610f10030444251130140d203418041007000a0010b10320391000c59072001c1e0003c150000c00100c40c6811140b110010035445030031034090b0880603412510702c01d60042680c442c02100009650341c034002150031080d042c41841c161101140610120740580340e20102034542603445580903100010090100e0750041014032030800307030800c100030450203100c4e21080d03240048000305903403800450342075411883c541003c0d40d0400181c0d001030740505543c02190040900d0b580d09001c5002270140d0302080f6100e0084005000034190004000c1c05202c2c060750082c0032454440005450740780402c68400343c01d5000700780302c1c41e00e40c041c01325025440d00e40300030120341255504401495 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 230860395 1250 230859145 230859157
    0x21503150904030f080709030305070b07091e0515040b0a1101021308060906070f050406030b12060c0a08011a0f0904090501063b0c0703020a23010506032d12 69
    0x86100c01c80f500030041c0d007105e40607902400d5450800da080d400d56500601c14001c2000003400002d0030404182010700070030428024103640b01c80008000c5451001a0468105102e2607000e40403600c400108214010222829182c0e07100d0002d2400b402580100c407040f00024014a483d542449207100810765141d44d14006c20079003004014030b00b81452403e05000014080c1e41c02c0c041c10440092010390400151030407602c2070b080000f5419110004524030b0309900e45554154021081000b0440030048090903448078165920082c40c2e0f21250111070101c65900041e0481da000d0003a0300d400081038008060040c3e000c0e0011500d0300113650b8060a41e001c5030080005078814200308901c60403450411800d000c3c003403070401c4042c441076801041c400c20150008000c10000a0300d082890b000304107200301c40760300072610b082c2c18501030160076a4624004107c6a80d508003004070701c1d24500000d0301e03000da01a0ba4400b804038000c0000e183d01408a51708001814066026242d984454010203022 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 230861645 1250 230860395 230860397
    0x1d060301090902030f0a02010207170a05030c01020a0807090501020c0f040212180c0103050f0c03131a0a0609020c070b03060a0801020418060503060c070b07050d0f0b010210020702150315090403 85
    0xc55802d9841018203041c100314010125034003040000c0c001d40c1e800a480000c4030300700c001c400008420b40031094100704203564081c00c035110019460340802015070007491000c500e603480460503141c02208071503520451203000d0040e84203114801c1145004400d1902d0a00010001450710315244200300720210101e4a039820300d010b440b030785100d01c2000c3c05040c841600900e010491480c00701c21803462001c0c0a40307401c48845011000074410318030001c8009065801015031007100884514607007254000311501c46807a0b040c0400015145194002e0362400e074580401b030300c01c039402d060b107030b1003280c00042c07500380c0c090103103040002e0168081c8002c00c003030080006c1c40c03a1140d9083d032800055072107a030300940c043c0d48803c040100c05440714082d40e20644e80300d2000c041c079441d0620212039a0280d0004000c00c1860b0084400c442c020300c0d48220101102a025a000d24030340003580d1003240180703640a5040580c0180010080c03001100850744548458480192490f031070010818256044800b24 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 230862895 1250 230861645 230861651
    0x3011e18060825030b060f0310060f0f0311041517060402180f04060f02070c080d0810061b020a030f14060c030c0702010c0c2c0a060602030a1d06030109 67
    0x4052030509004424180c2000d0083d2002002e0000160042682d00d1001510248606010801903900e203030700d9045960000381100d00c0b4600135041c200c020030b1144169452001c0e9142c002a014004004002c21281c211422030891800c0348180300240c038020342006005c40010364040b03501d0b801910401c0e003040c1842c0040c07605180c284140500341c0c0c40255540c2040b070b00482040600c0704280046503129500c400045503154031082d030744010340191000201458403503035010818400000300c900761260180e60700181074499481411544100740104c0c00044e070500501c00014111000c1d82403607610240801403450354a40700c24644224905044840080c0055100b080003000c100d02604000003420702855402c1c00b0012042600c9801002414400780b01c02c040284910440d2203001040c5401c0070780800c081d07826580414800c104211142e1918401c0401e00840c1c3d103100d41000c0d688250000e61a14664410945400c9080e8420407200700c1401410082030300c41c1400707140244080c41c03003c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 230864145 1250 230862895 230862899
    0xc03080a050c07080a0c061202041508070305151c08120c0403170901020307061d060108030309071715100909110405010501030504020f040b0f12030405010806060301080303011e1806 80
    0x5242464604e9002400d04d600051001021803181c1004c102124030a0a00440005154a42c000607001e10782c011031000c8030181150b4262504204211301c20603055408200550398101603143d54008003090940003618034421800c1540c1012444441070301501010381025900c101000645004031180700d41139070046810002c102401c488242c40c3c488126106007401c0644000039135a005011020b030005880360040b2801142d24041002d81e4050030043d684150b841d500850b0362039005845400300ea00c03d52030005060000403070001e542000640c003502c4503804050402c2c401c0c0e0380207090010341441107107001034a600b42e0700c90602450b100314244503030401200d040000f20340c0164801070502d41003804110040c0d03103005888095800803900080c03c030f01e450020541c0c00c00710302e0906070016000c84078195856400000b0f001160400d9a4221030b5a13900000d00c2540e004c00c6c4a51005035009100601031000040707091006510381e01d00b024025595210360003100c1e44000d40406c100741e079071401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 230865395 1250 230864145 230864167
    0x1903050613091a100b0f0d09060e0105011e08060105040b030f0a0b190b06071704080a08040801270605040f0c030305120c0c120304110402033301050301120c03080a05 73
    0x5840c0d4081312480c01100c94901e01120380c02d042c401c4200800c5e844400046207c1103035240c0d4009072516170062000c00154003418038041c001c18082c050041ca2414808190951480c010885020740d494000541860b074644411701000d0f16020600340d60501404001041a40c000c004003c1a01d004480d00056401c020000c00002100003802c5542c0c1da0401424207055182c01044031034403580400108803002400c04690300e030340115003006090b40070700b4044100b400186400750041d98a400000c02c482d0184860050141783d013040002801c50003400c00002240e0154810340d4002d001c2d074000890b4011540d0307580d800c59400c0d042280410400300b403076180c00010800c020382c0122140c0065180c00b0b411005244c1d85c0340100542c81c101d2200000207030401101034055520b211000e403040d0f442e0b0801461060030303c09808601c5d0b10008006900101a840e14902051038000c1038460034a0340c1d09014031200100320400c81038034a10b0304a0800030024408200914001d807159507015103401050708 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 230866645 1250 230865395 230865443
    0xb0405070f0f021903050304030314070f020106080a02091b0702060a030507030c02060621070506032706012102220f060f050a0603021303050d081506190305061309 72
    0x7602c5411036110455018101001011440003030360103090068aa580f940b4044000e0420200d010744481001401c0c407440d180c1111401032817003107c2d0000d00c5030b07645070840d0940d10400d0b5070700a54888500404a8150708014080180f143d000780c20451030040c1c5900420900d51001c50460b001a95500400045503810311030302c44002940d101034995401c0c040001400c0c0000c2e500440c46a40501c00c7d001092902084080024180071301050b44a113070040390750013407030b2003202d030406a82c400036401c12048501095007816a030341c410341940110b9995205400f04451003070201e8005040d00785c09060a0302240254100c22102d09001c5120b00084480405a43c0b450740410801d01c0c41da94140041c0d03483e80c3c03020090714401d10740140c45152980b83d14050a0155102a00c28010302c010391380600c0e0320a0303480f4861414581003407180d14030802441801d12031200c00c1d10091682c0101d1401d401e100e42c01c40303500060001c100b001503910140803507044507440d580c1150003844140402d002084144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 230867895 1250 230866645 230866667
    0x60c020901081501140f0301180614010602060712090203031b010c09031502090a121a010b030c070f261b0105040803070c0203070b030405010209010e0609030c010e040b0405070f 78
    0x40c00c01c4110010f0815100362040c004d15800c4108040880703115140d4440800408400070b00034800d080060f5240c40c9807401b5004c050351100e08102c0e0030030b1000c020580d018102e403000d41c02001d9507030750441c08807071500d945001050207580307540325070002d0703074040010300210001e402c6520000c00452802900f180e541c0c0b0201030510080b80c1c81040411800d20140c1c42d0341d01e50750405a514200d000000d8101c940da608032140381080c690750402030220410724482d208802c9407141c482662a43c020781503901045520404c000020024040020000d0200010003842207079114500035421300c0c0c0d400c05c0b00b140940e032407400030045100348040b074095220842c1910f1000080100f41842e80700d42c81244402881c1005000c01c10fa4041c046480030800800285441c00700b070798407410a441c0c402d020307500001841d0f00203010148448014a4507100311f4504120040c01080c0404020006450741c4421090481c1d1095a07003421a05640326030240f18030a14480c0d84003401894041e8016003910115 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 230869145 1250 230867895 230867909
    0x10306060305010b0901030e0a05011b1206120318170c090c04120212030c01020a0801080f061023062110120605090f07030506060114071e030216060c020901 69
    0x10100404c840c215190440324400d4080c030300410040da10629032464404103200080c415842c040c8801c0241e4050502840c4400c40c0e0394460002ca0028166201911200e001d100202100e5280c0785c0c000030f005d5106d1070302d042d080d5903000e1042582c03991600c1c40703000d10030103241043d00140642c070620702e401031025601001c42400c0c141094240089007405411195000340603582c11a0403402100c000c006881019a600d0029550340741c00c03d900801002007841441107902c14028807045040000ca060781c03107059402100e50000385001d8060000c000c100100e07094007071080b58228440e84038600208014600c030307205c004401c6000c000204040c80700500729880b141110400b0f108805024800380e030307a66000040070a4a0b1034015a041c02c189200a03031400303c0c0700300c00000040007401b00b54103101e00800d8895071078103c40d01440c41b1262180802c014a0f040d031460b40b11282c00000390792541020300900c100ca206036a807840d024400021a0031410108100c0c1e503002d401c40c03500403595409841c1c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 230870395 1250 230869145 230869151
    0x21f0e03030a150801051504141b0a030603021f020c01081e06040b060310030c12020102100e1e011a0a060f030f1b08040516030b0c0a02010f06080c0103060603 70
    0x65101090312400081d04840c0c2071500c3d80141c820452000081e440540794200003080300b03040c00b002c0712040440c00c12051340104d04050301c03016448403100c445481007502c19080310030620813000d9080c44c0e90122041200b8903503075030b00100250300c0d1010003220710301100d1820250240403032400fa103400c20008070107040052510400040e4441e00042d00c441e40c0b480780f1581c141e600c442c000034000c3c20035842e000d5048038000c42004446104404098201c1e4007481844110585418145080108500c40640940e100c6d21100074001c815030320a0340b20044002c01da44104000345c0c0180e68450405c204c51002e80e44441c1c51200340041020030030803161003102c40340001441c0c22406010444c403804131b501459a02c1580300008000c03900910130340e400020108010040d120300241aa0b0b03815213007600c2c40c2c03049181039480c03400c4440e00d040c181c0703070890350f070003000d0b80d030381c00c04640c80e6000400c2032046549914490061030709502a250180c90600301038a48036405000041c11100b03168050000c140c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 230871645 1250 230870395 230870411
    0x30712201b070f1e0b1c0e011109090c0421050111030106200703020a060207140607050a081602061602011b0308011703090604060309030818030307030f1b021f 70
    0x20541102c80c2107881451a00e0f580c4130224400410071400e40e030118200c02c4000616100100401001d5854285c25080c10030043c5d8026084900b00d039606201d201c801c0204000f00c4000b86050032240741e009035400c0c1128505900e5140300c01c0072500b00e40240440c0c440c140c0e91581081002c1c010036840c0302034100110f04561400c1030080065401c580007002004400b0043c03076041006119420140d07801070f001640050355020025070b60b006611841c000d0100130356021440340380c40c0c03007112420798000004106c0b001c45500c61003035a520820301d0f81e07540b4805594503001a19488054682450307030140b50009500a80005400310b80c200d03615401c030b0282d0f90f1400002a4006103402d054605c80100c80704a02c085540c0207203907214062415503c104049000111503500d6080300f9400d0348699070f0441d203521052564444000703000c041c1c0d411a00144009280d0364800c0d40506145c020500000c00d40300a4146551080d043d40314610300144c111005041c403501c1c0b1002070062102c81241c0c1041010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 230872895 1250 230871645 230871659
    0xf0a0902010e060c0f1c0201180c143c0d0f11031002030a0f0b011106010306150902030907170705011d1f030e0709020f030712201b07 59
    0x5410b8403000d204540101d01e460500c0300401003601d2880a03031003250ba14070340c809081da00318420f80038088019800c021010090469800030071020a41c0008400307003140c149a17101c050894030103001501716406401c1031500103200c4215190328000404c50107942020140e500303000942c15480a4003c020824856000841c00281d54010f240c100409400e20914503002904103032644003044a940d00100c280051040f02d5801000c1d00c00c07003590204500001040152166071461003070203802e422400040010860641151803031540d0119101310081e11020072400b2070700240e481c045030368405074040c003030b4010038440c4920b030b6000340b002401140c1c9840d00007403100d41062801222008040030882064a581521007031008505075881511000ca010003001010300c62804900b40c4105400026050101c0c030807030701d442000018240c610b030340c0d0000075070310383e541e08103e810841e83d03405910040c140c000480c480c1500880300d2066599a80c9034518550800b0504820199000070400f00201 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 230874145 1250 230872895 230872907
    0xc0f0e1c02060409090303051806040b0103030e010302070c09090b220303021b06090a0308070c03080105010f021c180e0c040510180b070201170601020601060e0d02060708030f0a090201 81
    0x203526141509400003118408560603000300d90200410350b0070514038608058060f004075118482d91550580700110b4800c0c0e0395034035030094501514202e040401400441d01c0b03403410b07990000c41030401619041180c0e6a03c0309052040d4041d80550380d0b0359544104003c00c072034115400210a815800a03420f8005504001c007a00d00f4009052503800036054217001100d1203161002040003007904d8540c5000060545c80d820109011400243c0d580001146140107401c0701580d1600359032800d507183e00745001980c1c802c0b0401c02030400c1d441010401a00c09981300b42000d080300e100e80d24248410031100030710100080c942c00c4041c240346132a040000604d609000d407403c6900444003004800d030000b4080e50118008081c9027003a40542e4400308070601c0c500020010700d4800c1e600d0701d40c480c4080261103010181501c0150050f00a24010040030b4458590380000c8038004101411112466000070459440740d2000c441c05a800b00811428a04620f0515800380301e8200620141046900080803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 230875395 1250 230874145 230874169
    0x100915060b090f0d14031b06070f0c140601030323040302060f031801020d021903150620190c060c1212090f0b0f0a0911310c0f0e 57
    0x101d483c10000b034025030750204d04030039007a00490910611600d12019648950241c034802d0740340c002401070580c03c041c00242c0b48c1c0c8616419902c00c14a81241d00003116008401c079015603440901071403000801105002483c000c40c03080e01d840d90102c4440c1040c0014601c0015495440c0000b03010400c056183e1500700d5292001008000381d80e661448413498a01d200005011115071002c80e419000d20003590003000c1080ca00b01c0c20404c00d80b800c207800c505903441c04882484081c1c510004100050043d0000e002042070014420004400e00072102c0c585070001040520b002100c1e004d44c010310115a107a000034081c40d2408001030304482e101c1072a036174a10139900c0e0400005d41c120340e101050562040484980c0305100001c107040c0d40c05c003405292407c1d1454065a0414070105a12480c14450301002c10750009030701c2c642c61009402c10203d5030880d500240c0c4090624001a00e40e510020f41c101380200101d000522158082c00060503421806000c43c2440002c448641c115a140c2c502000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 230876645 1250 230875395 230875399
    0x20f12070e1f0e0a0b0405150d140307030c0b06030a083009101508070b0d0b10090312052b0e0d03060e15060a0f0c0203100915060b09 59
    0x203450b1503440c05085282c4680c401000c010505200104141a43d03440d20340c001d00082e4018888040c1e07502c10401210400d850300e01d030f080200b20340c02040341000c0e42c450500c0350151381d00e41c424501c0e8098182c10b590180000b20005601b5043c5181000140d0309132a0700036100740c000308111805941d4091070351003091884400120503000a0420651420001d5112146080c1303c90f91420819106943d4010151081b10a00c0c10700c403140991900c0d09040d64121007010303000300030240c50320b03001c1e0b91183d0220403100d1801c0c2e1240300b6401ca42e10350104200303403010107544005100d859400d0022240c015500050104002044000441c511260b100045556a03010070f0040b5aa0220740c000107000340440b25215000e85401c0200c0660151b205804803190002601242c1ea1038841c4c803064014403100301c5500c134201f842512100ea1040106020000c0142000448802c0a4000038501851035210f03124854940700201e080100424101007200600041445500e04000300059070780200d44440f4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 230877895 1250 230876645 230876669
    0x1020a0e190801061d1803042606040c180501081f020c0d020102040f0515070308060a0806041230020a03141003020405070810030f030512090a020f1207 67
    0x74140d840200503032001030840000070094079030303181c0d0a05c4000048a184400f140d04000005a01d640d00818103514403200801862409042048408030715643d2194110500300318101000c0c4600304000c036a005a0198041c0768007246030420b5850044d5800b142d141eaa03c0c2082c0c0100014030b4002956441c11100d08580c40e004440c52480000a02442c41c50115610607500702d81209a010342c020010b86c1c0050103850b1402d0b85a005200c0081146804130310b425404000782d0300840c0c810085a5041070009014407881d5540300e0138240b030001d00ba134003506c0c00810250001c6040390070030b032442c0c24400d56041440102d422001030805d0644920303603100d803082c1c0018102e9000d42c42a444100451900e09010f030399403c061080315080c400d0340c04100c0c050b525000215104d24000c06405d8425038900340e4038600503085a5455142a0020b00100e003170110510401e000c2c5101b00426912415032003004000466190040164402248a04502442d2400d0300d800d00c450b40403900700281c4084140700 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 230879145 1250 230877895 230877919
    0xb132709080d020304210923040b03030703030c1205010608070c150e060609010906080601031b05090106031a012a050703050304060206070206060f010c06090606090f0c080901020a0e 80
    0x41c05284a50164048018400800c00041004160b03458600841100ca4000c91020031003054580210038065564810818941c0340600e846402803d03461b840041c0010a50081c000046031460308410001c90100c0d48460402c010194015a502e24030a403020050040c1c0d4503000c2c2c098503180014102030108100740301c21030103000c4640724402c10595072500030440d10250030714440c1c07a070300d042d10014418905c034000011031440360b005910541d45a60007602059195683d61140140305084030030307810f1481c2c80d0010719070f510720349528001c0c11035480208404060b0300c8032404c881400b1180a05205404441800203407040340341011428090400380020a10390512a1400b525036000801510001a000c107049a01003460740c0540032640071540c040c0c03512030401820300c4540800d2400030301c031500031401184154101c04002e9015042c0001c2d42038840e00040f054600d0910042115525030341c481008542c0a2100d0760b000007a44021401d20aa42c80b000740741c88c100f540042e03c14030039103100c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 230880395 1250 230879145 230879153
    0x3c03040f090b0f06030c0a110708121b1b040f1a04020702060409230112050d051b071715060a171e0606040501060e151309060b132709 59
    0x10f031410584009021580f40d03d0003c2d41075004d03034081194200004c0c2c00c61844420403c001540c0b200740ca55100c003400c1c08003000b1400313160729084041030811400c8058942c2d200f085060040f000e810205080b00042d6000d01014442641c486013422038041d46040802c0f01896500c50500d08500c3c0101c60260782c9005038000a40c2c00e0155803c076070444e52900c03019060080c81032030444c1c0d1803660342400210507039841c0d10040304280041c1c800391081c2c02446464401d01d120700b0080c14441e1240751219141e0f0055000d4900d052450340004400e003050416424444000b045500031140311101004020f152a00100b40040603a2160f0f2804010f1030f02c0208901c28188000504954a080a03405504080c02c0f010f07a2000d05035419805103240800200382e1502c20220404221005050789111082c007100585840d1700c0140000c2c1114124200451428014050740d0014400c680d50b4644581e641074427500600c0040c0d020104508103110780d10362541400b1030410b0f41e1000e140740005c0134181403c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 230881645 1250 230880395 230880409
    0x603091c0e062703120304060f021b100e030a050d0f021e070c0b09100e0111030c0106030501060902130b0306011403090607030609020322053c03040f090b 68
    0x1034550340500041604141070b50300d81c20b01030403035252003c2080a15202c2c0e040c5500d440c4400022000c180c0e0801c0080d0101d04c8a402c000e074074004901006150008010240d170105d03400c035014124035000207044a080f5035141c000c0903241c000c0480034529220300d0080281062056170701240469840704010411803c503035043d03825944508008612113003c0032250803480d8019602219010384031040460081d280e9000d03141e0000d0007510b801403003042e11409480403c41c10b4481d034104603603134200303204881040c030241000b43c25040c0042142800e5251681c291000c3c2c1d006080c5d00c900c18064035a1901e000b142d550100e460100185540e030f11418012921258114503a05c0740b69070001c1800300c0300e0b0b00002c11a10a518980c0c08004241d01c0f14011030a03840144c8507510303103041e0841c0d1031140e0b80c440000702b070700148118102c58001c07400032251f032603903900f00e40400c4011060090000c000e112052a0101c070007066405507290508040c451140b0210a000307104000342d5a200d004d071140c81e181c1e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 230882895 1250 230881645 230881667
    0x3050a032a1e0b091e06150f04090c060302071104050405060c0f040b04060e0102211b0715080f1501020a110402090a03051605010c11220204030b150603091c 69
    0xf103841ea500d041e0003007070f07a100a812140c0111955035000f03841949004212140941c01c80c4260b00c88101c03424040000c0000075030381690340640c1d600704c0c40b00002d4804c2c00e500010025920050b0303d884035824541c0b8103001100e000c0d80203604000422000074000b007215540155160310241d12200f50a001c011907000f5900510342d02e0780c0002d40854200d401901660300070030243d00311607500c41a03115070107007041c130784c5984640e14001348900b2481c3c502d003015808601207500110381da116580c03a80742044030040c01c0740e11b009c95115004c1c0055008456149a4010f0445244102034054040000d50312611203002810801ca24401e4407020b5071a60121044d2100c01003018031065102d0030156180d003011540c0c00c2c0314036021000001c0780d5004090003011281c0240b8040d141403001d00034490407034803401106030000140702d00b04e0602a528809403010354010040a400741c03903e0346851503074401c1101c0d011f00c210030070310803c40e0862000540c000d010081440901e10801300001c182c600b49100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 230884145 1250 230882895 230882903
    0x6040612080307080c0d090b061f09051e041103090607021c0c020f031f06121707170705010203010f0b1c0b061c020c0d050712050310030c03050a032a1e 67
    0x112117a02840340c03c810150203050304803801c0090392045d284662b00f1001c0c40714280702007056000c040190b0b180c10424281c01502980c0d10031410350b060300000c2e00b00c40c81901440700fa5100441480b00341c40040105650000060005060141d4600340c55650202c03054034610420806d030807030404540ba400201c0c0d042410150846904030740274a503c1402488412540041d140f400d2000030f105408a01c11000702c981001c190140412030310b400d0007955015410545100d403640302042480345c280c10080c0300a600034000180c6950611100c050144401ea104c001d580005000c2e001751080310454081c11041256000250382002201180884c0200a071b8100d24081d080706c60810001a5001400d400d8030301c1050300c0c02a042a0030541c0d01d40074080026110400514142100c1801000203540020400754a04840d581d60b07583d80007041000e030811191504000002000c141e0032041c000d0b005100340d04541c00324036990b020f2000c1c4010201000d00f02c400940e89030b04140c010100400d00b01508 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 230885395 1250 230884145 230884151
    0x9040302030c210d020310051f140901080c07170c0109170705060103230313030204050a061a0a1b030905010207290315030a0b06040612080307080c0d 66
    0x11508000c0e480c0d4100561200140c068040c100b020003124405100301c504151242d035050000d03d40280f030081d0001492103444010400b8045141d564518002e8a010110361042c200c5240380d4000a040320781d10105844aa4030234441c3c0d01442e07030465600e035480313440c202030039881c2c0009080180c407110080c00c218408007000103080f088024113412020340a809129015075a05440c95485494811444042c10b1740e000980103000141c40541100840700107441c0c034502903c102c0e5041410740d030042c04130b4804a014038004208605050280d903901a40c04241000103603d0102042280f00c3c2018413144600d200064a00d0020b00840c503c803c640c00314400451001b4040ca405003c0c80e516004003409480740103000a903c0c96800440c099951100702040c6407020890050401c40e0806408140614100301403460759840810011901314040c201c0701c040f60401f80140001c0320050307040318900d40800e1207010301003400181146e80045031440c0000280d9214944140e5a01452003d0b07046070b41 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 230886645 1250 230885395 230885401
    0x50d0f020a030b0105040b0109080607110f07060315080604020d03081306020c0304050405180a0b0c1c05071202120c09010c0f0f021003050106020a12050408010e1c0302040506120406090209 83
    0xf4448802c9043c0e8801362403c10526103240010b54810040303101700215903002500007200180f0030441d00c080c0b5458032045642c140c8100300d18606201c0745803c81c6000ac6e0b43ca45c00c00c071614030b841c001c00005082c0200a0882403e01d600480c0340350803070b04d4016052094030700c080351284656a003802c0055401135070454551407011044c5860b907116110f014412410007000c507101c0e01c440940812001c0d01d10000385240d5805640d0b21040c104014004900f001d07060040004030100c0e500000107100f1540e900041c1413070300d42c001414802008411041036481070100c0f00c1070f020303214040c4d900025111001c03511000d0b403030012540f0100c455401007240e461404038404100000d0303d00400301d4422250004600c47d000421000c030b5200344280c0c1c0c0141d0060f2851804103140075103600b040d45061800702d26164513481c0c1705080d20810068184c0310f600c0400341d211100c1700c40300c4403004014203240541c40c05281c1000150b40e40180845080140520000b203000c100140d409541500d6000d400010700b4a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 230887895 1250 230886645 230886653
    0xc05090d0507080105010803120f060402090913140f0d050f0408070305030301140d15050a0f1a0901050301060b1e040504090b010303170c0a14041e0510020d09050d0f020a03 76
    0x40b07110300c0340301100e40c02c003000411861800701c180c0325680089080292165030b82003c0b0ba104240c0500704c0e9801c0345d0b003049044040d8446804480c8120400005403040d402e0600e0110840c04031400f40c1001a000307610700b104105404074521290711042d2030410745072104040310000500c00c603404035420380f2420400008004020010314102d81d80544503c0c400300e814018048940303d8420014010700e0034100540e4007002d6544050b8000c9607406d4001003904070204680c00710f0300c00802c1c50800380c0b0880070881840c94030001542c00f402c400e80083c0310444ca02030381c01e403081c0542040b1044000801d2407820075800c0038001e56005100091041c01820001c1c2810001d64500303010650000d0082056140940000201140261804080f083c030f4110014401c40340d40c5043c0002083c1103104100c00182c0650208001d145503070030207181d0030401c1c6000b08100a03c982103c40c2c030213640080c6410610a50403968020441d641911041e19020300c40c41d03d4881c40c030308014001d611021a900c04401c0c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 230889145 1250 230887895 230887903
    0x3030603030207060305060102280b1f270e0a1a071103280513080f010506100206041104060801020a08010303030e15010306090809100e030105100e07030c05090d05 72
    0x80c1d0081d02960151511240214195142101d80f5400760348041044181d0b41c10304100d515200420300038850040d03085984403401104c0c00e03100d400310426107400f10b19640029021400007050684400510600e05099402812841201429080d41e40300d01d21614018180040d03c05207a205500c2003d1681c0792031411013540d002d82e80080000c500c0100d0040b10344c800021183d5581881d03c28044114002504241a00c0c0502143d000c02006010b0060050b40a4442e0310180919001400032009003601940c2100d0307005200910a00c8a80c65100e4940d070041070300380d04640c0000d00421910112130108025000030307070104085600c00540340340150b0b070050f071160580b4440d680c1030013011314104406650f1901d042d06115507254400040001a550b07a1003000ba5a02c65980a400c04621000040b400d00c81d020340c4902103080c03002200d0b180e15080c82101e90100f202105d00d07140b603060203007507401154005e210600381641ca05949218074000e60585000c0c0000504030b6000b40ea041c90300f1512 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 230890395 1250 230889145 230889149
    0x7050703050a03080a051b18062502030d031b08270c01090e010602070b07020312030705031522021b0615120c01050a0c0609060c050705160b16060e0703030306 70
    0xc45c510300390100343e040120702d00c00b00e1901c01d1b80726a203052181141d030f5640d910440c984100c2e07004004200e00b080c01e0072054406400007082101c4a102c0340701a006050800001c0d1054000305850b0030700e20b40c3c1c1c0003c800340c441c00030704141c58041016621800c800c9024000706104a01500c0760510004040f400002c5d918541d4100b83e980b4804250360780ba03460b645200c01c0c020350002d41c04c0454103012034030307440f00900701c1c0a0000303048610003403194079025607551064030a0070008070000208540301c0b175408403005540d4010380388140010203428032201c0700860700040701e0301d445c3c00040c1259201031840081d0104200c007004d42e41203091000c100c400705844180f403107016540604004e44044000701d00b240c0d000c001070f12828600840150300310303400c42906030100c560540d40ea5804011603034034481c52880141c1500d030300799100c0460910910f17060524880328000c9211440c280b2120940300295a0072070822602280008600c2c40c0c85c0300034100580400001340f2031820000305040d415006401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 230891645 1250 230890395 230890411
    0xe130c030602040305011b2a0b01080c0a080327010c06050a020912010213030314041a07020f030307050c010e040b09130b01050a0312080408250213060e0103020607050703050a0308 79
    0x10503007d48480c411550040c2c40d8448000c00c400120307034a441000304c803034001c03600c0010180b681065602d0f500c0c1c20302084282c00c429015401380304807030058101002d030b18000d1300910300190f0607d00c201d4000c107a100911700c1c010030500c0c0f60b10308180f65130740505c40e55940300794060801d00007840d1805015000750098481c0c940302d0600c42181c241c031079006100300d441074804640c403010f005003540c800f45c907000f0202e010498605420130001541c100e0f0306500c44051100a81d0481d59a241da004010040c82c4200c6028070942040002c41c0002d04009541e040421003801c0541036020f00c8000a40144804218107400002800800c512448500d07400640144224120440740c0d88034414045800d07687d0000511814141131320810302d034010710718030f0b0303103d88901101032030301030001c1c066681c41108544100111001c2c0c00300500b14946610b0b41080c07032000311010440355203400d100c2d03040540103210280c02400700040040074060180908409550820211846103002d86001007030420b044a00034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 230892895 1250 230891645 230891651
    0x30f030606170a1812020607020c0109060206160306050d030207090e0304060f0c020607020d150c140403080c030c0105010b0408120703050304061d16030605090105060a0e130c03060204030501 84
    0x40703200c500444207440700101c0e100c480121961412034881c01425902102c801035929400d40c2c0d4005500f0702131842d9050740c0b0798047c1034642005800a46000f02000c003060511040c11401c4c01100e42c00143c1c0c0741e204206003040800000b000c1003d6009200d10740100e50850900143d00b07007816000203041c002c54211600c00c000d500041d00c001e6031280510300854000420042c0108c14440c4200d0210810070b0000389000d00d05400e943c00140440b075140d500722821038801e125107803103206603c00c0400c00700040c10510103d958a4401c502d0318032480c000182043e4010541601034001041a1840c0e408194002c02c040d5842d00054922904039100c0c18065115003030b8501d05c0f0200101c1558603565064550901303549a40c5e85900c0500581d1000d030f203200c44109500040b10b082001040f5112022000c1007030880d0450815000391180100101c0842c0e041400388527050f1a444010b00c05c4035820030107008541c940b03040004035003002d40b00180001a1519001c41031226941c0107101301e9114030020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 230894145 1250 230892895 230892899
    0x207060801090c080f040309051305040b16140d06031407030507150f080a1506031e060506030f090708061e01061b1101091d06010f080c0307050d06050d030f0306 71
    0x41c01e4035491400303e030000701c2c0c0704082843c02002c0901d85030003038031a04041d40f01940768000701d054412011040c6030002c2d1100b081c00203000000402c0c5e038220324110002c05d54400b54050141400310017000c52000001c0010304600c010020ba8400d00165500c1000c02c0340d002400c2190342d54403043e50105489a0103044030004e08034071070000095441b4455140c1c48a244041e96082d11608401031007092850303244d94030203482c599200011000341c02c4580340000c0c1d5150b1100c41d13080c01c180c51484034104510f480814047e13560740d00162030b032004c2225280380300307a0b50711140c4900b03280c0158040d40c0940303c0c11f010b20032200c0c18410315000c0143d581041e158141e9842c80100d4032642100d1441400013128400f00010480b40c3c0620045460181021000720759280744215100341c1c204c11800061903000203010096074094200b61400b0072138501403460703041102d2401139034070010308003d00f4000300084480d903800241e0840d00c02004000c0c42044101d00c40e040c0901611005140000024a02200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 230895395 1250 230894145 230894159
    0x1103070b0708090a0c0905040804080d0c0303060f05011b02040204080f06040b16050306120f030706020403150902061b01180602030f0115020703030309060908031603050a0212040b04210207060801 86
    0x2441c2c100f6405c010789541407807400700408020400640280d071080e0080002003070041007000340a04c461410b03501e10f6246102401d0017412140141c025601c050100c6074204410780c0d100c0f8061903540f0b1aa080c15111908620000d0000d11403580458140c4c00f403007080208800022441d14442da0003039824102c42d0b0355881c2c8116203d520224280302181084c07001c01d00a05014002d010080c1d00351049940310220007070b00c2171950308916001c542c0d00fa000a414001c0045080c400300540d006010b05000e030161950000d00d090183d03842d1400902582045055441c1003504403491002c12254405d040c100e6030f00b015030203540300701d80f0116440781202c00095030701c45035114400300c41000d501400080341581d400b2005090310701020b8940c1610345040401254809004502a200090b00b400070007141030000b40940d180145080c07010f904c1070184c621304500103041d10740e00580c04420312849070f0f5603107460305202021a40816103000303007030644040382d5000684401039511540f03070f2083c0c680e07a03a44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 230896645 1250 230895395 230895403
    0xf0303020f370302120d0209040b030a0507050d06150303030516110715050d06080705240702040b0303120c13050d080f0a0c080c01021306051204030e011103070b070809 74
    0x5152440c4140942c5120100380903034050400511a206941104070901c0150841d41c0114000824190340000c9849081c9001c5c40f5030440b01405074040d004681950700d82c2070703c41100e441628001d090031468042040440e40c444214012000c6005860765113034100280140030448094a10085240c80d5141040c069620311003d03450740001044010b0a15116880115400e09480284202401034450744500d40c050744014040704002000d1092070030b010803d48030034108444071100e03405144a0b01850807074048820313060701a2808290901c6900200b4034500c9040c0956503140721410512001c0c61600001f090035160300141d450751540c540c403c000034054804402030103e01c00304090794034103c04802406282280703081108070048261200a0594080851a0a00e03503002918010311030882001801a04041c6403c0342440301e216031104117000c0281001c2d050040010500205030702c540c0d402600c5c2c10001054a07211201c51a1046180c401900c1c01e03000f06110b8800618080c400003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 230897895 1250 230896645 230896693
    0x40509061c0311160b07051c0504030602090f09070914060405030a06090c05090106050a08070c2a0b0d02072003031206030a060c180605040602030405190f0303020f 72
    0x1070075004090702169010760704411a0481145107000d003c4403010301210307014600c40201a03107081681d8525861070480c2c00e00c502500700c031003049440300156980c16800419102a683e100310300580e90301d400360000c4c00900c0d0310a08503601080400802c02119840701c400000c454400e804880d0700c100c403800708440f9000c0c500807150994810806100450010340204020703e0040300005941c0ba01e92000c6060070701c00343c00c004041080020001200c5611418082d0720482c0c0b031514007000003150f07403210914035158040c2041c0c00c0086200c48404802c4040120080c48082c0090356102c0d45100114013035080070a080d070340410341c4110f1800d0242151021490640f0041c0030b98640403001000c40e50980c0c01800203070300342c414803044000043c944e1140d04030342200e90f03e4405828103412108031541c07550b5048201001f070144020056550000b0541d02943c02c01c480c1650280811403042c170102e0b0a640c040c0704116148600003042c180c02040179419183c03103030b081e94030700480032580e00c10801c082 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 230899145 1250 230897895 230897929
    0x50a1b02030f0a14040911030403080106020a0c0303081005031009020f1005030115030e03030f160c0302030a2706030203060918070510020102090a08011d0a05060c07080d050c04050906 81
    0x20803511552500c5182c200c138000b03d40540250415440d08400800c5509000b14016500070000611080c16005921140140590310042013145003e40d00d9001c01c0b182440010184441c80d00801c060f1003440020101030100902100d1055402c0440c0c074002e0240110180e0007074010005840c920309002101543e05072040c0c803120f1071a4a4a03801001e0304000440721020169900c520750081801400114054203015000000505000043ca02c030310107011075a02c18400380042801c0020f40100685002c0d2502d4185604002ca9410140000b04d0140495101260070690046000ea8242d405140194000d555041daa030b0b0f180c400070000900c80c00052010360b80451010401c82c0340118070000501102e100150038201182c02240d46200345400090307070b6075160741c45010805034455042000039580c10080610300e030240c450945807880600b07803400c10500020306c0070034400400200c0c0d000c1a030483c0100725602c1d050703c11484035045030051500c40e207407540c0410820300e029580c89030241c40d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 230900395 1250 230899145 230899147
    0x6030b0a051504030501090c0504050a09021005090a0302030a08070515010311040b06120a0c031109060d09030c0b010f0f091406010804140102040306050f06032d010906050a1b02030f 80
    0xc01d0300304401e19207a850002c04407181008040700060081c0240242e00340300e1822404c0e514141810030054a9005100c8042c45182c602490007682d50845441d030719002d24200f072960341c0f008c00040303001075841c0d400194151040e45161f4080004440061405902810030340d40d443c03d801c409804d061030284009820310141c162903140520303043d8012605070000400391460001c0742c849000c071080d42280c08d0318a16a4072605031883c0b94142c0500e1820003008681c0c94545119000001e169000380250385410380e6440c4010000c241c0201286248590044640320041d0381d900301e02250a0b0881c040c000c0780c2c0d80803c0740011002c5090040c07a01c1c1880300641c807d950b5544200440f070140c0c0040041c0c8020111880540d10039000784018805103010f020089868a8000c080c0400c000e80640a207001e54041a0500904400e40100300c1b4406a1000d1224480340a00d400305c4c09031050340d0010301003a06d41070600c44800d04a500c204040314011100d06000c0075100800d989030300a0845501040c54 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 230901645 1250 230900395 230900399
    0x1208090915030709020d1506120e03031902030405010608011503060e0d080f1302100207050117010b0417010f051005030c0a0e010b09060c070f1809030c0f03020c04141006030b0a 78
    0x365900030740010a0106c90016844440004103040701d60181d0007007021600308651030341500b001e40218203000b80c15400a6241d400c1804100e4150f140172406554003030350100124040103800e40103107000308040170081c0400040f16811074038008107880120780d80b03880e02c1e103031781c0d0084004a680500d09425071500b501581d01c0c54010301002000404100f0001901c11001c1c0050703491003041580404503034020050581014005031644149081d955490400d00004101c4900644106d4044d034a0a0a0001c041002d400100340900445660041d416080c2820440d80c04c0c0c170b89081c1412120b048044503e1203c0740300520801802d24011141d9110540c00144014036488008041d441c8000d040039103000307050850f0701c1c14a01c058201c1010102e848100b00141c00000c5049511007c3c0b1076810800058540d6002d8101d400300748005084a103950301840030b15000b8000a0f492200c00b0304244010035a2156014100f102118801401442030402080300b80c400e01c55807040b10b00142004417424 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 230902895 1250 230901645 230901659
    0x1030e12030c0d23060a1d191407110f07051f0c0f0b0a0b010305040209010905070c05030409150803040b04060309061b0201060510021911150a05030717040305070b04020a12080909150307 82
    0x208c0d02d190703180102c0f034a0707007030f152601080440c405100f080b4036512000c2c100021101a03013082c0c00728a90180c658001d010a003c02d40e10502d860303401d2400f0b40c4030200c00d4100e07480141c61544140c3d2001d406403a1541000e401d00c04280281d521444003034400f00903ca010304010b400b142c60581d00079402086040052111144a0380300c10f8101e5801d04000301001810b99883d0318640c05900300b42c0b0016242e1003400f440038442c00d001c4020304200400765003040c4c1885030200075402141300e110304154880714488140b00c074907804209031500f661002c01400c1210100a0b029040754400d460241001c9503080324210701c0402c680c116000349400300c1d440010640c4071441c0b200600c486459000c11010420304044031a4801010b070a07045449030b0303490340740c44c000181c4481030b4410320320792603c207010420001030b034484c040302d1042c1c2d40001c5140d0585c0f51800452038088140d0011649004110450004d005850020b802802c03000c5408140c96911051000101210381e4641d40d01548041c40c107020070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 230904145 1250 230902895 230902921
    0x240315090f36010207030207050901050f031c0302090d03110624090a0b03060403170109020307210b040213141002060c0703020f06041101030e12030c0d23060a1d 71
    0x1809072440b4000418841400403422640300b101c088000d41d04c46142040941440070140c0c1c01007000300c604c4885650030001194a40e82e00c0a504c0c1e60360800440c101030140c1c06581a11044500940b0740c8900d02560320b0060002e200109030f001c014070520f400998802c01c0d052400e102880d003860260130255115090000502002d40700c2e41d43c0c02c3c0c50321030011244e1802c1203064070440c001d550340b040d10290440c5214011006070818203900d4010030800c402580c2040b40340007840c00020440c400d100245815400804170900c1203903010b80002043c3c1c0d000d01c001110a420340d00c44441000e010626102000f01e0312190440c81409030f0045c000048015662a01030505140a801036a00395001154079506020701241c044820040305030340c0040729603052044254920382e41340201282100c452010105010003032041c000000002809001b00d0b540d9000300800442c6901c0801c0e0f602c8242c00b402030120302c03c6520fa4054400e9040c0000c542a0302c10b940c3c09290341c131a01c030080300c0d100c00440c84c800c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 230905395 1250 230904145 230904211
    0xf07240e04020d0204061e0206040b0402011b0602030117150a020702120d091d0f0c09030f011107031103040608010e0604090f11030f07030302060105240315090f 71
    0x5104400462000c151524002002540c001190060350703641488806010a01080c28001e80c0c01a25403401e9900c03900000c2c5c086e00f0540060100003589d4a0b44012102656044103106c05108102404400c100513900950f0503034036007824038610b0390060455260750b03040c5d20110082e00811500401c4a00c2e5a0340e0040c204d4034000750441030507001400c44240791004448044000504540c4200a500010110428140c0c3c2e01401d103c407505201d46035251500000d010040d413034000040c1e0354103968081160790901d40004000344030f07880c0380349850300b6107402291054021420f000d80c0350f5076542001c000c41e400d4a0140d11040b1450342045142d0400580080c0b845400560300c1b0910000310f200c0d201d44060341c622922402c1740c204030340c2042c18141810540350344555480548140b001a401085240c1076440a488003183c20312844034a040100d60f0783e8040c1c0410300d001050001030a2015483d206003402a900d4100548038001c20210140086440c15101252240441c803811225900f80310 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 230906645 1250 230905395 230905397
    0xc0501110901120b0631140f014505090103050712033e010519110409060b190221070501090804120b1323011503060504050f0724 57
    0x10410414035140e0014146c414810f031500f50152000110004140f050040584001400000c4a50500340860300003081101a607051290103100001d111090080100144054041440703400000c2104003446164000d109824880c4070318000c2024205041c00c10704072580038008145e00e83c9000100000c0043d00c1c00c045041014480c0303002c80031824030388071a03041c00c60703600000302c10100303081e00d1154172852000c036018036410310080042400c0c2080400083c0d0f0f070304541c0851707c000b0213003450300103100315004078081600c1e00780b010504840c0c450140c020003220042801e150141300320241da95140d00f0281419094003051300420b185050341c00b500c0301503c0b0f1000455108610340da140e481f9003290b00600943c4268070303180000e003c03038032000340d8202450806204801705c690312071140c14000300d458141010130701601241c0c100381c00d612060302500c1509e03098401503200c1c81e0000280206030380c1035505100d10907810b140f0400108010302200c0e030400e690a03c2d049158800c0801021800c5588 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 230907895 1250 230906645 230906647
    0x1d09010c0234150807020f0616090b0403030e09070305090c060705031c050603010609060308030609040f0b04030206070305090c010c0b0c0c060406020705190804090504140307030c0501110901120b06 87
    0x20110482c948001001d807050704424102900604002041118010940c00c11980a0202070314181c0000c10541d401a40450780054010466241030312401180c0e48001c00d124000a00001410361206a0348212007041720084010780b907000046007a0703481a01d012074290415100314942c1e1810f14024101103201da01600d052110780d88910b40030b001d5103801500d9298484007000414902841140081c088000c010001542542c581380321030302004040501440414003c0303000c2c000341c0b2600e406105d92250382d0340071030b01d41898004e469000a0f12000c0c08a401d020100c1c05000020501a10101c0d040c0d5654490305043c7d201e442c901000500001c0c0c4984041154000c1c564080c007026105500540f00980c4e00c10710351900524160f00015030064443d80300d41008001102d410454086660100011509882d181483e01c020b0320003d0a9011502c000504281055040340441c00b0f04c5014400801528560701040a20380c841d004070b25000070b0400da03030088001c034298040b603800240a4111 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 230909145 1250 230907895 230907973
    0x4051302030a0b010602070603020c0309090a14040501090b15030c130e1207021e0d080d0209040603030806040e010e0c0402180a030305071401060f030803150603011d09010c02 77
    0x820b04050b03002d0340c180c1e5038071000c5005102c02901000311800502040c0707006c40c0390403218480280c50340141040c0c10321030311400700030506a0f0429080a1340e9860591940502c0b41424030f003c90003885081d00448030f03494003c0c0080c4404070480070b500c4600b0303409005000442009001c2180602402d800d0b580b6841e036800d101c40005408101903200140c5090302c0c10303a19a03a5004004d400380c00c2d200c40c25910015000748841a841c0c080481e280c45030b20514960700c7c0c3e0f1070304c4800d5000e802428040c58106240c0030000041c50b0303000150f14001d40003903a040142d004624202c07070a890700c0c460300e184142e000308510750042c10b03d580246802c58505a155048040d0440048e0a01c002079106800089001c00c0c41002c0c071200900d4108528071544c02002840d140104600008549100c084c010300d5000c40000d85648a040003041e42140003440e0030395968546180900c0e400d013032540803001c00003000000c0c851007070500c40c00c860070303032a5001800350241e1504514201070882010303002080000c000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 230910395 1250 230909145 230909149
    0x20a0e210303100e090712151103131e02090705090a0e0903030f07080106020a0201140903161701111803070306021317030a0801090507090b12100b031504051302 71
    0x2e540034410b03060007040c0541c6007600d002e034910b00c0500703940c5c501d802041c410000742000e98841589558090030f1007903040e41c1a00c0000040400010308860600004104050b510b1080c0200320f0580c410680e00e4156032100e0442990040d09100007508a0141e0780410301c0d41d400fa6001d0000072900802000c4520380b108108500742909407540b0407260300100500035828988080c0d1540200030386890003886d80f41c85402540c0d5551100d02030305002881070020420341c080c004940c0000005412a00040c0c00442c04141c126203502c511401428142400ca04c0b07508103009010314210400302c0c16050841403201c994441030381d11911603051041d480008002461400641036142c0020440b0704898a003c99131101c00401d2801e90540ba00f04000c0c2d1003200b6005001c09066a01c861400a81a600c4000948005d003084d0072071941d0010105000c2c5803415a0f14046210308400b1081400895903100d00d02c040d8002a215041035050350310b1108001c0c01c00354000c0c0c3e481650341111480c40016900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 230911645 1250 230910395 230910397
    0x204050a03080a26060906040e1c0906090b030c250308061309020d0303050a110705011d0705030d120603021309050705060c0c1e03010e1e01020a0e2103 67
    0x100448014801090080c60150489580130503034154519002d07142c1020300512030003074401080203114000d901c1c007042c0151070b960b100b940c00d0180c10040300c618064402001c5010504070700344000240750702c5d0f4086092072148407071100702d542d614510b0b410740d1120039011029412503802c401d2440d8040000720f1001030288040b040c141d0183d250000b044c00e0102c2031040ca404198034003041182807002010040c2c440c41c80e4a030020b9018500024940c0b26280b070784014104c41040a0010301003c00c07418203119040d80220406500d04680e2186034408940e90b0b515202c02e4864540c3c95000104030800a0b0300540c1982441034007900300041090326540045da140681d103800f040c21540d52540c1d201003142c10051130000d0113040301c4007401c00c0c0d000c0040355610031201d0040390090312691290100c0f02d51071184088440d6000b002402174200030710115548110785090041030340003a1605004e03003a018800c88006500d1541c50583c8046e0300070510810281500e0403c5241c400301c2c9016503c0c20040c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 230912895 1250 230911645 230911649
    0x7050f0303130c050603071202130906060e0a05040501050a271d0114010317090301020c010f050405120703050d02030601021f45080d050702010b09071106010504050a0204050a 77
    0x1860840391a44900f0322041460160700564062107041040c00328842d0040c41c6014101c4a1620250303485541301d0400d04070700362039404507007918103100c0049056034001802d807444a106a4a0750038142e0380340304100c00c1c0c0b0703001c0c441c2c240c00c4000d5040a0106159800d10300031821421440a41015501039041c0304540034202d40760075840d103a000300d8003407000a010711000c03c882121490b2040d41541c50f20078075000059218000e9500020300421544c03003c0d01620032000e1001c00030801201d9076840d9501a06080383c00315128012031400030750440080c400c2d07a0400b50995181d50400c0143d4032514000d61014122605512800045460f14103502003440080c607246e440c003081c00310b128425801c40700d809800170401428141412403442d041026110044014003000c9040e24400b81006000b40c4241000c0b80344450601e020803c5154054005c0d480704e5006555901c0c1c90356480508840501c54403110700c5403a0410001003006103420b4001f41d070004909440107142a40d154001002c0340455 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 230914145 1250 230912895 230912911
    0x2031015090501030614030c060a23030414030a05030c0d110c0a060f060501020c1005070b0a060303021b0d1704120507090606090308120406020403230d05190507050f0303 75
    0x90000c1c03000f541d2502620000b042c100c005076035610a0719002035100c0218030385150190401080840307000c2d120b03074880500303c03031100200300321481c14601140b540d034030845098620680c4000c2c01c14040400104680816059a03901d41c199195685240e903203500681046010981303900301170079141e401d88018014415034000428100c5400c0c0307084401e0328459030002d0f051906c0c20340d0800850b600400c845901d9881101d0f40620850b400400740c600d4000c080703001d40f689400108000d0300840c59440340d025280039030200d8001aa441e00c4401648100d40031007500100c10114000019040d9901c10b510f007030750710700440c2c00c164035401503000104100c80c09aa06070700c181e40c20001c00078184200e5010704001d15000890782e0454440c0d000500c900b07940c01103d9100100000d0074841140e064501a50b44402c402a46241010266030300a2141c40e000600f400340040b4450006d0049084a401000000e910781200c05000e40a89881e0006041aaa580104e503500c010545052008510807005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 230915395 1250 230914145 230914157
    0x102030402040c020721050319180803070f08030601031e09020a0e1023220c03090b1302040b03070602060f0703060605040e0901150e15030102070803060402031015 72
    0xc140104416600d222102c0300641d04105001c0c0580390700d440340c84001c810b00400038a0f0804032850001e16520801606c043c007011000030030580d1991181c0151201c3d812047c030002c0c040c4d110151940c6074800e5003001403065035003e1013a000148148013956028605040002d1401640c0c6040d400c0b014400040131411070b40c4a2980742140303030559005001d00702a0600303240310700c3e01450440301d00c550340c041c0940039240250844142e402024014a019801070801c0c0c2420065021000390114080d0144180c541851814181c1501c01e202d0202016000010301100b81c07203072911510010306400302070342c115450f5014031145880802405005000720760052103145400c0241d00311840740501340308205810705408104866201d0f041c0c8040c0c40f65003440103a1501c9d03020940340104160316418122070780c501c600051110600c19454800c11b1080b4941c107034103d01070201803c0b8070400000601c01c00062001c2015801d12383e0142d0350202c00c04003084d0301103880e11030f03a200c001d8001c00030302c0006030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 230916645 1250 230915395 230915401
    0x150c06070e0a060314040813180c09081b27040807060e190b0c12041101020c0f090406200403050c130b1f03020d0c0503100e040f030809070e09010203 66
    0x50128082c2c000380014601040540d070206490040804090030185c2002d801280c0d01071000103414280000342101800b07400750500310b541d1640034128540d0300c400415600e41c000142d82c0c4001c9080740c0b4840d49000c3d004126070b80e00040100805522220911490001d08084504820500714500840c000c07600d0300d803034001c945084826551000f0f01121a40c202040c3ca2660105802e95520300c9580010344054681c1c0c2c3c40c01031200ea0240d03503150403403034145409210603c2805040d400700303480280d081d00e040d0012441805000003405000c1a000352140b000103000c01d01c2035118074261846d09154002040b5440000b01c00d42e0040d030001d0707c850308500382e2000646132003040c0c1085ca07010fa0405002c490045400120345110368081460f0300300d1907030102454181700e0741c1240c42028107207004114000343c40d03000525607042103881c1d05c00e911841c480171510124840d0785505c590340c84481c07842c2c21a1250703002c6032540005040c4a0261207000c1002c250703600c3c0e14180c14070602010000580f039103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 230917895 1250 230916645 230916649
    0x5010905060a180b060f04092a06090608090304051f0f08060f010f02011d0d08250c060b060f03070315080606010309051011040503120c0c150c06070e 66
    0x5a80600382821041c43c00c0802e001c840800e402e0308942603004a545010ba40d40d10004c00d020154110310240d001d881c20544c0410054120108940c0162007a0302a50700014035200719a85886800355030041104e100701048600d01c161806036000604030b0075030303060650728004500707142110a821481c00b41d0741f1042c04003142c1d0150b03840341030b072905240170701c0e941c142000810b18020b4800442810001c1c5010414180c9000350006500130300b4101c100c1e00e04180d2400150348900c01c2c054801d00040312813000c1000e00078081c10b00707110b0034004139904410365034160342038604808001c0e0440b0ba05071030300c2481072255101b1020b48400c1c00c1c1015425920300c0c104000908590b84c03400000c40040d1200c9040c0000100040e09960001c020300300090980020b0030101e07d850640304000d9101404d290340040d001007280040d0040f91000e4040f500c882524010302805030080e0320082d9501e5001202a200e540707003030320002a1640c9002400351030a0000e0a640c0d05046045a2040c04144c118888544034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 230919145 1250 230917895 230917903
    0xf0b0a0212040303090506030403020a0c030b061002060609150a09021306030b0103021201090506010c0c03050a0b22030f140a110709060e010b0c03090307080c01030c080408070b09010b04060305010905 88
    0x100100880c00342c075290940d50050812012405081c0c000d8070301000007000c141c000c0068005554002c140d44a456a607803034490003541c02125414000e004055800e0105400002c2c158058032005240340c8241ea1882e07440b09511007034554040e0701c50b1380141c0000783ca03c0c948c40201501d3c20010500314a042c100707200501a2200107280904051040003d444d0712001001468155900d6000c0880c040c2c0314000100d441074039100015220384404100001007102c00a200510a0711802c0d519100303668540c000030100700110b404420311038400c4101c034006445002020b804103014202401c8404040401102d076402c240e0401c0c000c00c58000030381719016810082c5078020141c9800c18800c1c0d50907c044102d007401c2c188290415028085026090480103006880300880c01600715034100c5c1d86d515415607150a0516064042072914202411461150030200e1103542c10850040c81e0400943d07800007160700082c5005501d541e99002000290340d2805150011402100041261242c070301b807107410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 230920395 1250 230919145 230919163
    0x606080106050d02090f061f1d18010b030c07150905060603030c030a0e0a05040507050a0e060702150306040f050709030501290d03110304300b1f0f0b0a02 68
    0x3c40e486401d20500142e83e48109690702c00480f03503141a00d52642004030303c84002d245450000c07004c521b03e9242c01103031b1050b4840c044101c5401d010300d00d00680c209204407141030821060503001c081005100c040007010003150800d5a520086191262584030fa6409445410f8180c04a41e29072818109201042001c41d4220400300c000e182752500d0213603011365a02c200100381301401205610b400f2699110315440c03008260181c03082c00305207824031000f49503500030360703c101c041999500705a000d400d200066901091340504460b0111101d401c14414940000f00103e0380b0503150246034138000c000d0700980c2c4c010b102503150000f01a08528015094982404902c00c90031100c2501c4d41c0443c00e4981a1010080240e440c0028060181021251000300313aa5002c61440001750020ba00401c045c0c90f500e1002503c0292114860321140c1c407820702192080103072a04420001042800d1000170703c0c0c51494007120f0807580560364031142841d40782042e40c0910507841010404500d545c2d010301c10300360 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 230921645 1250 230920395 230920399
    0x71109040503071e061d060a0510170708010218030f01090203070b070204090f030306090b010509180712060f0501120b130e0c04090b040b0f0108030403030f14190906020307030c021504030f060608010605 89
    0x22a40c54107034002d41c00c5a10920bd03900b4180816000483ca521043c82000c0141002c280290f54481040d0507089916104031000340c000d204001100419200612500011590080103040d809281159901490b00001820f076840b541c3c441c48400014500c41c28145140c0c800c1e240401c0f05403070064902e00b240c0d05144030382e0501008001c6a115561912340c40e41240201d840d0b01c1c5019240d200c000c842203030306003a003a10b06074a0180701080e0300c00d00d02800c0d81180e6003661402c1c40e06980900004c00c1d00e0b01c600b000303a00542d003a186c12001019a0b08004d4118030046c0403100e4001c2044001400d9420000d020396100c2c41c100305100910040f160708590248290f0f1058483d0352403c0c1c04203a8a2140744001f030b0411043c51000c0684034454202c1e060340340311000b05140c4490044170003808488819086c0000708001060004007070b80007000755100340d1382546804403e915a5020301900c0400100c60300b0031003808000200c0090500b4010f503071402d00074800080c41320306259000f401c44540382c2081c0c1c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 230922895 1250 230921645 230921651
    0x60d060f0506090a030204050406020c071d07050a0f030509030d06090603020f030106080307030c081306020c03060a060f18060915140108060907030b0a0f0b071109040503071e061d060a 81
    0x1481c544403c6440c204886d070588000416680301d042c0304000740240e6080c02428000c05100055201c5041c07140000a5403118031400591150f803400c0e6034500c2020381d14004142480c441d49102c60080d40501c1d07200f042e00b0140c918201c00050b4007c02c840c0309800c0803012a5646000340158144050030a003480000e9000b0407640e41440070a40c0daa0150b144010100802c0356106820002c615048d102000c14050003080e8040e1556000f07503c4490158005000f40f0459000543c00c2c1003e014000468a44204030741b00c4501b044003d2440c030400c1d00d902c41001c1d4032004000f620884e503104803e05082c4140410010070306000320b6144000140c20900d04019144080c456141e136040d100641101d02e078180020100503400128a981c400c0754410410518400c4001503904110ac0090079040d102d4000010107124110030000d49000650b001351081d4400e0103441c00041c1021212507000c070201e171a4242c0c1070155507811042c0c03602c1401c0500084440010742c1c2146808100b801d4014001070414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 230924145 1250 230922895 230922907
    0x1a060403080304120903080a0e13091113200403020a09140a0b0f180a06060305100603020a050c0307060618091a27030a08011217090f060d060f0506 65
    0xa1a00024001800e6a600c03001620402c90260b228a030045034481200350301c038a541e1101030311400038503004501805076401c0c0080005801d10511480581c0403180611003400041437208034007001400b0b5000b5a03448a124000d503480796100d1154400030490299a02d00710f2050011240482d03105003400360820f014040c0326081410195804104242c0028103241030700c0000f419520b2010026801004080e0040422410700c5e0384603203e02d2141c04144007441d07682504600311601101e4100e80028030380810302056120b034008204031032807803410390b0038210400c4106080d0340c0026000c5891554482c400c20a0904440d04222144085841041204001e40faa01d03598603c544945a895004000081e504070b100041c40000b03556203d414074184120000c40d5669134810b0200d08d01007001c01d00005402c08809000154959200340c001d0a001c44034550f42c00305800120407180e1090081a29038100d8407060003615150101d01008a0120301c2e02c03003441c503c14916003040b03020702020001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 230925395 1250 230924145 230924153
    0x61b0c03030105090c0909100611030c060f06040603020a0b0d0c08070c1101091805010504150602330f0403030609060501140d02071a100501050306010e0f0d0b0a1a060403 75
    0x40e42c0c11114240c50242180d9143c4c0c12141071441542000c5500c50304030307002e0103000310a891003070055401a80f2211380001e2114402c030754134001d84210315007591160000800544581c0a1301c1c1e005000a40f001c5100c5440358002485071000b42c0040c0e4a07150003140c10310301e64099000d0300420000e241041040384c200510000c0c8019882c2c031001e004031102d554543c1c8540d01c00d200c1400117145030300d9000b5032904042c100c1d401528081c45030743d10450805105884c6c00034015161030407146140c00501804007401d403031801041c0801c10b4114508485441d00982e271202c00c107154401c440701522415a440e003840d029046462980054408900e448014012070344c01c06281d2440c3c40306000819103c044c0c50009402901c18114024101600300c0301c20010500302075001b60003038512040b10914240c8440045665010496865001030406411902d0301d0030400d80600c9290300103844000340e40c4903502c4001c09401c0c203840404010b0303628540c10a10320880d611001c2e11400841d038262500380b0f9615 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 230926645 1250 230925395 230925397
    0x219020a050c2b0510020c0732011b1203020d050a1413051e0f210711032406151603050a0c050115050f09060307030809030c060408061b0c03 62
    0x7003a280803055082c0f0403014014100504920203003994415913440c0f4030b104200303807929440e04c160004400004c08801006d000c01c4052034282c2019100c48a1800001004450344880d084555440c000030011110120f0f000900d4540c580312191005a6503083c3c840c4103030101c510081201c03100030714062124100350400c0100607003045000f8403480440c41079040c11400c11030200311203140050101a90300c01b0180c04100d40c11700050000a403940303000b2000e030444600084024040120404006040010b0381d0100203401600c400b40490b40c03034014101c4100000c415880647c181a03101d002000b1151421481c5030b200c1d1290503a1441c1050605a0751008102c01d4401c002e06009011501864282c0308091180c0000e800800134010740d00204140c80005000d0301995000f0300103000c1c18a01400d00b00c00403402448003800a00c030051070b503110883c03681c00c11170500340d050089405501c00c0b07540300800b0703002804900000c1c04e480c0c20880078001c8040c5001000381c080540034083e0300c1003400044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 230927895 1250 230926645 230926699
    0x6060306041106040801060e0a0e03131809080703090512030705190303110d060911091012060f0e15151209030d0204030605060109080106120303020d0219020a050c 72
    0x40c1c00b03a0540702d5481c001035402d00076908200340c650f20b050b10000300301845c0400c860048007280d030100101c07074540e10941e40b42c1c815101d4a56150407855410408c1a00e42000d0002c00506504009240d127410b5481c80e11692014106800151881900b840140303440c80c602d885a0a0690055182150b140c1e2016103030820310f81403c2008103031100e154180b501a40100c50803108a05a40303a499504040110007005140100c080706032500002403480903122046030710000d03001f06000100034201c078084625032950a0031110071500c445002a02c41840344200c4060109030440c8800d030304e00310050316001904c83c1601c80c4150f45541110044201d0030003140c116280615504505a980094051861080050b4003a04c0e61001900109104d520740c0240e025003801d07641e070a400c83d03580301c00b2420f0324202e008803412082a06140030000380258028000282c0b240380c05410900e0b042690407500c000366848001680185411074204102070040000b1782e03130708a9061018000c00e00a4071000c002e40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 230929145 1250 230927895 230927903
    0x20f0c040203180106030503030405071401080a0203100905090708160e040f140303160e09060105030114040e010603080a3911040c0906020c0d050d0810031403030f090606030604 78
    0xb022900f2410100c203202400e4111100900c5002c0d0740c0c0c81c010b903907503000b03c90a40b118016014089110440c180f1a0a0502d00503981c00300325487d0385035424000c0d0f0000e1301c0011180e500407000900c4d03034440c0c0a0144121001e10141000602d8280030741e0610711420010580740d62400c0062141c055a800f0b07071500150030112540841c1d40c03e142600480e01c2c00d50903c1c64610000c010400d0986601307840541d8203c0c01c1d681e1803e5240140b0600c80300e000151601400300303d050006200b140b0707004c0c0c0c40a440c060b00500114003c414842d1490031140190415101000000762800e021500000002c81c5414034107807801014129082c004281c1c03060144042060a4004030301c02030040c1d00e0030b43e40042070700400402c1542042640644411924812600940a200c812603e2443d02c4800fa481454000010f042c200701511421a5000d8004010710000c41c014040031000c588503201c1030300d03034100c164002c6580b41810f1002c02c030791f8032004002e80c00341ea00840c02c00c03105840100e0300580040e40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 230930395 1250 230929145 230929147
    0x25050307180b07121b0605010510020316110f1309050f0604030c030f0306052121030103110613030c180605010e011409120a020f04060f030305090103060b0a1806020f0c0402 76
    0xf116204035408800c518038007514028005e0100305100d45a402107040365000c4a2820300d8811044040e616030280404080b0144001803808011503420721211022a80080003206510078030000220a088072450300500d2550300c141110422104120181d180c00c1e24a00800151619a40007406032040c242e0090402c185001a46a814001e4102001504000b00307118100a00c00c0507000c82d0200d0101080c0c014070504000ba44585400c154071005c83c2040070095140d0380c03e507140e1100d00c0800ca921182c00003020081c1d01c1c0000e44244030100614418040400204d00e044c01000c1869130380314036103a0032458100100821380c5c10030460341412000b824950071426108540702c0260164041140e0030a0009108008407400400c421040324801c4a5208114401109100444038107000e00c80711442c511505002082c0118060f0600704814540401c0503503c60100120fa81c20400803e800305c0c6200d0303c1d00300c440800b41500d1003c1e0409100800100391a00c40c4141e40f004002442401154 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 230931645 1250 230930395 230930423
    0xb03060a021806030c2107090324110304050d020c01170702010615030c1d150d02070c0303030606020f010c021905070b040f030b0a02030705040303030525050307180b07 74
    0x34081940902d515801001c1d140c9a00d0309140309409603000b42581055100049881e07a10017040c1ca0036140500d0440d5a642031190442e901c1601918040c400711805805016441400301c0e014066500301c4885044482c1e200c0c10301d45844c80c60100e08c090342c481075411011400d049a43d000d1601341803500400fa80c21810b80f0b4803241a80100748603000072a014031000029942c0035050340041c0c42c0c41d4810303900c00302000c1c81d01c03e40c04242c7c550601015444004040503050301c2e01d1680c003508400c203484200502d0182c7d103a1310b83e40010100c0c1d204801190711900c1c20000b168060094000b041010070080c819680c01c0c4170000e4442480d000301403501400e40460400f070100811940d8080c019400306180e031a0344031010304421110610003110052506000551118018000d89010b407030305884050900b0b0469400340d001e010028103600349500613100058969516080442c400641519a1562400c211070000c020840500c155016501f12003010072403a0840022613540d16080010110120 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 230932895 1250 230931645 230931667
    0x10b030c013005190615050705030f040f03060f2a0903050709061e031106091219021e180c0c07060f1206050f0409060b12100c02010b03060a02 63
    0x40c03084a02021034001d40031010b4290982907205601401208010103240d8803005002030545009016103042c4009019100c082c06008501130041148120140c9040c40d01c40030503468036401940c44051070420340182001413180602c0340021504144000f840320034610052001c170515032004550000f900d4032404004203220b006a20003940d40712050750b1080d0759500c3c810015140034001d901880c0d241072030040b22400b0f00445142180c0c4d01524920410b0b65010030420306401c0041c00d19080035401d4034408450605000303680700c3c1b601ca6000d00c2c00307265581c0140700e902919022a842c0e5442c6001f12000f00f80d40b011030060039082603800d482d41d01d40c0c2325503070400180200109010340d442614030100f4520f80005682e030881803580d48050005048044140c02d4070050700c64190811040d40b0040d0362810030307401c00110f5501466000c10b001540c00081540951441c910148542105500c1c100c1e0f0007513805075a044222078070003409000c0b503180c0040c1d01c03240050b04091003503a00051001c00c0c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 230934145 1250 230932895 230932937
    0x3020d0f0503040209060f04020415170f04020d03030209030309060703030c020d1803080702043c06030305040501050a020c060d20030114010c03021507090806090f0606011d041104080d02010b030c01 87
    0x10f8001e24044040c2c40b030095601429034133003aa13060101410040c0000c88215491581078811600200721958010003510250025032080d04007903010700040000080301e8462030b00420300d0512aa80015100c1d11a080c001d00701132514514030100850342c00684a455242d035204410b0740c0d00250740554810042c800a0001c3c920b082007803404000f95018141c01090081d103050910034020850307132004010728828070484c0d615001c01800f0a4041c00203010035403042c4080c00d180361042c0101c910709800d82c0000f8510750892108000916124800032804405010240104403134010f8034a00f55410310703950301e0320341800c8468103041089411590003854800c0001000c001800198801700c0d040c4200c0040551107139000d5645944140000b0407502c03280021040c02d0704155034090f0106468690045451807120045000d07030b2501c040f5641c041d540c452061905c0c4115492010741c0d02c81c80c0281e4a130500100d0310030003040d645000b80170951900c02060092a40c81c0900c1c014000908140d00c420034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 230935251 1106 230934145 230934149
    0x7060311031302010e03010603110103110f030402040921030516021621050102030a0b01030b0909060a05060616060c030608071d0c120403020d0f0503040209060f040204 74
    0x1100000b054800c0200d20500d0904400080d28001909583c890340060b140700c10030041e06031080d03030903109440d14034000b0700440b401c2c0304c69001c41c81c030680002040a4002c64032003004404011394900c3c500c1c20122034156020400e01940c0d00240240341c2101c07250781c0040b1141355118954000115440c60b1828038068031100e83c14a110700c40200454000307079500304521303811180090303401c1c00914072800c02104005000141700c00014150b13105510024000c2c85e034a4107100000340007080384d5920800410022450303485003800300b1010b01c19040c91440c2c402698010108000541c0c0142ca0100700713070f980621001c1d0315400000e88600451141940100d442070300014203283c1720385240d40c41224100d00500740682c2d00005001040c3c100c0c2d003240141c101c3c11a0fa4100c81d0000503601094a03245480c5003503142a901044c410440501450310030b003081071808900351b0300e40c0c04543c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 230755395 230935251 := by
  have h0 := BRFrame.cov_init 230755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 230755395 ≤ n) (h2 : n < 230935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
