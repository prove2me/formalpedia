-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2580
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:08:16.562844+00:00
-- url     : https://prove2.me/submissions/2b6be85a-095d-4cb6-8917-891287e13ddb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 463848920 ≤ n < 464028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 463850170 1250 463848920 463848923
    0x1150806030a12110d030204080a0305090a090908190813140c061c14071b1103030c0106031101111509012706061409180c060c15070807090b0a0903 65
    0x124a044540203001130050444d10701d1420441c05841d003100354450007403081d1001c44134041c024100c45055a0380444180d407100a105600138261003003c680d103085403003141c4245100c0c0007030aa441011001e8184010f111a40709000c103d0801c041190a01030007000f8040c140d841819010a071240c00c0a150800d0f102c6548150403100203d03605002401a071010b41900e59041800c10584131300074500d01c0078040440d0000c000c102030360740305c60f00c11417600f130840c84483c01418407102c076211040010b030a540c008002001181e460f90300900a11444400b43c409100003428054000c4030300514007902c1c0e6980d410b0703170228480101700144601000303401101e01c10607090194081041c44056081241c030307462070241c85240c607042001c150100c070b04481c00c001110041100311a03543c1d980e548620507642d180c50250901400da222001070b21060064202c0c0c1c400345010382680e865005040c4210f540040141040017008400d0090403030300261040f06442025900942d2514100f40a03106032007940d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 463851420 1250 463850170 463850183
    0x2061605100c0c120203040e011a09041a0906030613020f0a150507050105060a060e0904020d0c080309090603060408040501110c060403060b03060a140105061b06010e0412020601150806030a 83
    0x1050048558400711a6810714032482016403c4c400c10002207a03280950b01a0401d984080c0005000240200c43c6620005413440e0f140d915001207400404c094034040c00c110406c004e007814030080603103098107109901c11001d8000b06400d14005000c000340701042e2101074001c10b4049401d0100d62903880844c0c0142240e00d5080c20100c0750000014000d5021031001c0c1e8895181101085851912480c100d0444070165290500c0719588000c101c100f80d00500102c1e072115454511400043d810064040145030b400c2c06582c94160300c10511901000003000188690451003c01c0005040c00040e00c003075900a1828840403070b040242c680c138020601203144c1d840343c0007080020405c01f440d00300c508034103026000d40311640c40d80c201440070b0700e040035501d0305500b101c42d00501c46410f2103006003940d440740014158882621000305800c280080e040070a04940d00000c1002f4400c82c00d000c1090010284004d2102d90326280d11903c015050080c0034013041301d94400304110381d4041280341e0060b6000038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 463852670 1250 463851420 463851431
    0xc0806060d09080706060b0a091e0b0d0b2805010306031a130510200c0d0f0207121b0506030f0a020a0302091009290d02090103060e01030c1a070206160510 68
    0x7c04002c6150000320300c0c00300150207400301007139406411181442c20070713180ea115108241480e01d0f03011a0340004284500380c2d5a907030324903c01c960715045a112a50340c4a0040d0081c00e4400184548071201600418141401c2900402c0094141c082c3c2c41c003900c82c00c0200c064291500b90039100d019084003409016842901a1890810301c41ea01030887c10742124500a0710500400880800d401a841394144a03003144051402043c05244400d00e80d0f03800340305484010392100c11150708040c041d20180d6441d10520014100700101000c0107000c0d01d07084480508501c0c10100c03465a124004001d101d2454011611820702c81c0603405480401c10001e1044640c0504680300a01e170725401e1050070350040c044040d0444414401c01c842c02c4410880c0400762401a8614020010350b0041c0388aa0406546500003d601c3c481943c0c10381c080e5228006440c0070501d010040c5c69005400c0082e07607202d1004000d0b8200590740e0f1011980d2810b10300340040000c014506015042c01070852240e500702d030905 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 463853920 1250 463852670 463852679
    0xc030b0a200c0a051e1005090d080709081e010b0d080a0f0302070c0e1e091b030f060c0a09080c010504050418021306050411041d34030c0806060d0908070606 69
    0x11145d550002c0d9010300f100c076204400111041034402c00c0d120101290032800103400400d1003008090b41c00003041c00c0414549945800c104d160032100c45a401e14150200c004a410181c01c0c022038485c0e11040312841c22070142c980710000d003840b8814015040c400785103c00c0304140d0280e0152089950808510200b0998600b0398000c0c0303103000c560480d803525528100c20785003200c11000501400c00c0c00010b1000c039030720300c2420303400c1808040e000d6494403485041c0580d44004010381e9100c1c154814a4035110b880c1c509003c1c103c688903820511480c0c06c10118880c4c1641d0020a0302c0450324220b03008a03900c210451564500c0034800c42c040c6d0419030038010f940820a10b5004507044410a0ba41040355014000d00e148041c0950701401200d460302d00445a00c10411101003500012120041c030290444011010329071003807401c4090220441281e110002a058803e0100888860a1814080c90617000151941c4546035a9646860341c403e04001402840ea00792400c80d680903c0401c14039894 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 463855170 1250 463853920 463853953
    0x615050c0d02010911120304090213050a0b030421050c01060801060f05060708070201030c1407030905010801060815010f0e12060105091602060708130f0c030b0a200c0a05 75
    0x30089846a400c42000103441485004209504440182e081d600d01d5020404040b9000a0f10107242c842404082102162407004202e841403803141000d40e40d1400c17052000001150b4000c11070060203200b0040490b6420034a8000d44041d2050a1a00184140256100c0c0074003c06046030750300e8580080344d462415809602074800d05400e01e07403103603955000c00a161107000402415813009004200041d4003c2d00107200c00d102d20700b0301061400383c1c80311405058111541c290000f6003604010011540c01c5600c6601401c49440d2692451502c41c5020b04507500c1302c0e201c02d0422403800d002c00c42c80303440380003169400d10f8002e010700b4903590700c120056980c040a02616100e0042c03940400d030303154501c14a4405142007034002d0003095840b0603007560365a800408441481c0c0f1416040000601c00070648902c0911401c003500d003884c10b604103100c9030303500104550001803030f1459850310310700c0341c10010241c441c134810300c0e99656800380d03030070360500700c0d0804002c00b02d1007000c520b8032200c0d03030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 463856420 1250 463855170 463855177
    0x9060f07140316020601050a050102150c09060304050a2607022214010e0108190b06010c020d05010504120201021e030604021312061a01050a05090d05100b01020c040504020121061505 80
    0xc0aa08a0705c0c26600c8404200d5090124803c09025a2001c3c1421109821141c1e805500040900c8428280600c40c00807500a62085408903503d80100306048104140c4203240c0e4207429a50010300e5100b05d101050b000203126061020b4881c445130642d011a0014441c0c5002441d80e02d800d040c0414810009004140f5400303004500d2032501d000e0004c0b4140600050404920b081d11010210320411a00c80107180c10000d401181000b20102c41100503807035010350201850301c81c50000440b4070700340c02e20807101810345000d4011a4010401e243d002d0550b0042401c08428504840d80d0740d441e10000980280b01d00300240d0092808081d000a161903126030694040d406002c1c2804114503071810702c10686031100c80c580c04210b0603c07a000c00940720358080c0c113030003a003d09010103144041d180d407450300c141c46d12100c41040d11550710102550303051040845040c001d0b9010b0080b0b00f0141e00180c0251120750034a148602034620418142e110703a08500d00030b21204105d881c0d0404000c800800303135030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 463857670 1250 463856420 463856461
    0x3060509100e0c090c07051216080f0403050c01140a12021204051f020c060a0207031b150f150e04151406010f230f0705010f06050f0909060f071403 65
    0x7406130000900b100300c20001c94414543c85405000440300e03202440c2d49503080001020041c0007491231f400300003000b24009001255a015240e500d032440c2d45016032401c020007030300c941000707045491400c0f6500c86101350f40b003040340d9040100c1601c00ca040c6400003030244410134180b0420078818407090043c045229003440c51000544503404804428942c00d9216a6400e2580c41d031003c4005203200d159070340504885803107460000c080d501140404c00100c503007100251160b0311070b1503994503042030b00d21454a40c545848c000b0b118041603645000b41c0d409242c490b1130f6100c43d400001604000f4010f461015070407080004002030038080e48098171810381224414089448400c40031420b6001e03110311110702c0310155000c04802000304a102d125007007004e11005240c418049040060000c5c0034460081e038580300c00254040c500000c205006c00f58003d01340c0030b40211070902400f88004201a40d20080014400030252100101240c4803080c1c40481070900b00040240046503028a1a201800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 463858920 1250 463857670 463857679
    0x1506032d1a010c030203030411060d021c051005030a0f062007030215010509070c0206130b03040203190b04060513171206191208040510050c101503060509100e0c 71
    0x14075107801034682c1803a030300b030280141e84144005000101d180c804052120409002d103170406420881d01e2090382c0144410b109000c0c40d516000700d02c40c4442c403445500110072407202040a1038030020076100d0030304078000360074100202c3c0d4240034030140d50400994070000700140013501540d140004855008008100c00500942c8041c2550300100320129040e0380004003850744c542c5800e5010342d00c203000d2103412a0131450901036000f50107080300d1240300414140ea4290781c4c915240c4101130070300e842c030030036010710300d0030252080301240c01c0c484400c2c0c0c400d40c484000a0382c0d855006820800c42c100140c000c0010404130128001610401e01415202102c100020182c0d2200810400050801d0000b50015841c0b0703071003007180d10000c0a2000030079000c1c1060a25041d01d0354003080440c084441c0c0d040100b0790000c0e403141c08440801040ca045143c1c10350411240d4091004141100c410f4030005e0411910742020070180c10003800b145410460a200c03c00070b08403060282034070350b01001d004034801d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 463860170 1250 463858920 463858961
    0x60f090e0103020a2706080a0201110a030e01050f040504090f030809060106050a031805120c1b031902041b030b0f150a0305040c030807050106030b06041506032d 71
    0x31800034108080c1640e80c014900c0300100e00300420f0490030384491070b07003601c3c008420125110101e0b0510807000a001d045003e0140201d440c00094602d6009911f00d1a0540c405032045c80420740c0b1010241c0c0804003481c007141d44031001c02102e8118091500002d503c2072030941450700300a68406046801482911401e41c80e40e6000c4100f40c99231024805c03031011800810036841c01902c40da000300c005002100f40c08680c103200e82c0303c162030002d03c500b11854070480003810603c2c81311308002c01d6841082140d2015444c00c0c65901081d15003a290300000000c2403046003020440d03480d078101600c2c055500007110340131981c5010080103071100c80c1c9040d005110001b00302049041c0406000100c0b91603480c09880d012405404600070300c0024401d484080714110044000350025009000803030041d070012406034158102000003010280c1510b1043e850b00c0014941d41d050404200e044400c1420001864040c4803603662a240c41180c0c080c1240740103002080c0d104403140c0c015521010b246415440303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 463861420 1250 463860170 463860179
    0xb090d110307020a0302060f0f0c0708010e030c0c1c050f060103121106010302210303010303052a0a0b0c0d0608030417010203010501080c070f060f0e0105150a090b0d020a060f09 78
    0x4491082c01c0001e50440480c0070140050b040c228000c201e682005074050b4a84101c0b200c101440e50048038100364660040340080180220034047c41c074000d500400a1890314090f0f01d0403941e40c000c8204568066030204800c210518403400c00c800b11b0507000000d840300d036401a91000d4980b042400201e42e40c1d00c400c805000294402e040703c840e41303a055001000c9036400d540170421040c0d400043c01940208c0340c400440d00081c18005503008501c20780340c9a4451606d61504014034140e0100350b002c0212901c84949008000504400c01d41d811034006041902e54480d030964a100b0b404c3c080305000d040200008001d40000007e001321080101c5040b40c00c001889810f0a0340710078801c4d54002141040451111244c000080028900c0743c035041031080c2181d5182015103030055001041c0640e10080000740c504203000e030503482895002109120f551000c0050010181030080c483c686503900d400c040640c550300d00b4080c811750000e10090300560360300002410407900b080300100181d1030820024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 463862670 1250 463861420 463861423
    0x1091b0801081e01020705071d010b030c041e080715030e0712080c0705040f020304020f03151501140408071805010b0909130606091a06181005070b090d11 68
    0x6050b01e21980140001c1d05442c0c002c80828040c2100d500c406541c20050000007840c208202d074000d00c2d042c1d04002c02139104101c1c000102c4c8c0140d004c400442c01c1041000282d118030421074081e50030b84e190001d214080800034004c0b84289402511242c8200d400200b00700a030412505900c481f15901400054801907081e0b031110f01522070303214064510640b03a0000b03056080507043c5030f580c0c24100c0b5890340d80c440c00a002e03a8500500e000d5a164000280000e5003000401c060700c1c0a800c6d401420b00c2c812200107440b40100017444d024600071072038103c80c1560b100d142e02810260745100015259500c41c844e031750f2651882c1c401c040c0180110310080c0c0c6d40443d60700805048500ba5440141000382241c1403001840c801801200c03207040c0444103030001505449402c1c050262031000080790009001759001800c1c40c6602c642c03088800b80484100d200711105084030314403003510195401c190040040da541d005001d00140340040340c008010000074002400441184182e0b2885018910301414070b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 463863920 1250 463862670 463862687
    0x52b0c0e13140f042d02010306080607210605090108030a02010b030a0b070503101809020109140604030f0606080303070c301d04020c030403020f0a080307140a060501091b 75
    0x240840c00260005407215641a4111381d000303000d05070003115004202403003009020745480c9104c2083c54090040190350381403207600c000c0d0035810001c0c0154100b0100141441610f050729000401000c015207140340704982240d0010f041c0a010b6154039611030070195281d030000300c4103a0042d8a460034030040c52800140444c0e100750031501151658a45620894403980300900d0001c114100003000580c10f40390074440c00400608540004507140c85100042280135140d01600307200c24203010020785503890100300c5084991117414000040602d1520001408050380014603600001c0100300c2c281c0c0d0400810900d0134840c1006140d2220b028100700038800f0300c00d0140040c0c00c0f40380c0320001064010201480d0081c61448145c411301982d60000301070b43d1000040c50902e4001040810850800104140001e8011102600c03628205122540c3c1c0c0e0065103005042e0100351828025a20402d210504aa9401c0f100c140503940c0c5841411001e49200429a014901c00e003c00c03c48051069400b0b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 463865170 1250 463863920 463863941
    0x50105120613030e010c120c17030115030b1f05130602010908030411041b050c060109052206060e151c02032e02070501060e0a020703052b0c0e13 64
    0x2103075403020b0545040f41e200c2580c00311941480850b03075000380031800400c01e002000303c6a5840d00c0f4540d01d11318088a03160000121a0241c544c2800140b142e50314080304801c080c40c4c1c0e03182c0014603456603000200d0401400101c040c5032040d03103c450042c40e03070040003042c2c1d214940380d1888045036502c4080703007205c5501c400501072440c1400071400258000c02c00003041c17840200042000c8407044405640d1001c00002c100100e080040c0e40c0b070b00941c3c02c1c400c081c01041451810005442c4c0114120701c420b1010030f030a03203644a900440e50411140d540048054001c621048034240740207070850500341a03a00b519071060254140460780107581e0300d2504405a0b010b070140601d00940c41e049075000040a040a080c01d80249801007180814405010641c2c010b40000c103500e450600400e00381140030f44400d0045004124400c003280d0403400b11051180030f242c4a00c3c1c0800e401864040d85d04071048c600764901c0c1400c00080d4061780c00306a441240c481162000c07000fa00c003405020841c0c0b5603222 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 463866420 1250 463865170 463865191
    0x4050d02060103081e0c070603020c071d040303051b1c050a05040c0b0a050412080d0513030512190905010b03160509040204020a030b0a120c0b0304110409080d09060501051206 77
    0xd181c541c006021511700b1562940c0180b60030035950007081800d050f05600054000b81d4040381144004100f0000c031030082c80c541711010000201c40b850403182d500300510203010303d0f484902184c1c1c0341001011b21250661030380025516080c0c03003500342d20f41c4581c0042c48901c460500d00419200922407140a0040394042d2060a0982c40c049800c1e50603080b0088100c2403020501001170f12401c0d00c090408014803800f0320683c0c6041d400190003ca58001c0c110380001c40311510307032a00094102007240c003050400c002011082d9034a51111490b03000001d5000324450601c5040420040c054010700c1107200220152280180b1500c0380d50b8854100b8415143d002211202040150a06a0043c1a104200c0c580450340d030340164041000030560781c0c44080305801d004506000e104c0740003121805404030140300c0345542040d4940d40181c076000c95800c1c0c4943e42d50620003080100e2a402c486140716802c03401d100c1a030366400c0c400000c0009110f101d0040c4508914407000c88804550644035032040c0c02c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 463867670 1250 463866420 463866427
    0x1513030b0f01170c0f1504030b0a06090209090a0906090c150e01030b0a0b030c09041503030e06070827151c0219140d0f02180f01200a170304050d0206010308 69
    0x60400940140005100e5044001b44040a40c01120300c40100040c500a00780203505007440c0c9445421070700c0c140d0000c820544140b02c0800300d13a0307980b801c16070800480c0070086a0550942424001494134040080072401c1d020f8001032200d03003004504c0380031041c80c0c550b296400701c0e640064040d41d21001c465540314400042c02d00c0605503032400703550404622503e9078202140103000c941100c11400c0f5100501d00541003c01c100355006c00c00106542c02036582509007841c55a8030f055134068034400703010600a0a0030b2400668a11005c00c000d02c00040c01c00d40a0784049201007481d510402c04034592494424020f010b101950088410924a191883c460700081030703000c40c0e10314180e07030759540103460400203055051010300030030141075100c1e1001a41c540c0c4d045c010420368107001c805503004080034141c0e4415a07070041c90341c01e61600508645411040d003550f01c6820004e048100504010405041c0c114000c0800c020b1440340d48902c08440000044100c2660f543c0380c244402044c120080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 463868920 1250 463867670 463867693
    0xb060a03110c2b0306030b04080304050a060c09051516060b0604090f0606120e0a08030910020c0703031106090d0e0a0803030403030b0a1208091513030b0f0117 70
    0x303034086000311074200d421508140ca00403000d400e2440202ca0300da40e01240c61801e0b211030b0091180b60604500508007001110f00d5a5100c2900400c02840a40744620210008080c00421700c01d11040c107600c000100941001c00364003505c0b45886024080c0580240e404044000444d6001c0b5199401008aa840080070650310a000b034070b03201418a40064090000084c1d10099003d44000c103c80080003185890078504005e02800200b4600603c20382007000d441c0d2944008110b803440f154104042690b2070741c43c02c840c11310f00004c0100902c201440000e51100f00311000ca4140c094074483e64550742c0400d013445095564007810307110a50503402c1446141e5072240203241700c2c05003101c041e00b00912681d03182c0407141941c10488095000c643c0700da40404451400351105000b4004003810204504d010740c4032005036000320200d5501503040d0071032050302c00c00c8080035102e101c11f14a40c850011034503840d1080100c4820395031020600d034110000b00e24181c1c007140c0000404a081e00809030348000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 463870170 1250 463868920 463868927
    0x10e010c0e04090f02060a020f010f02070816050309060706090b092a0a03080d05090c04112a011e0e0303160807030f0c0f021b0f01050d110a080402090a0b060a 70
    0x8450071121804c01d55403510058031028003a00b40e01c10150081e040c07000c1200402d9095884036101d11000c140304002050010741c0341400d0718150380340342c280740300c070700140d40b6246246d84600b4020a911601c00314041c2d0410401d0342081c00c1c030707901c28140e508207a258605003e46d100501003468803208041c0a044448800134031aa07020f09000410b0244941e80e69214044140e2003201b100740d10640b00c03400c001c00c00ea0200404401140241c50401900c400d44203000009e008a2032251226003ca07030340d540501c00c0c1c50070174040144502d40200700341051a50b595010015040705070a42d24284206562680f4000c01541d01c203c5451000201921818a04541400004007a4014941d545c80008441e0a151040c40d151000a0302c1d01c02c85a120940081e1810031f580d41510143c01286100300c040c0c2d00c2d101095400082d082c03c103e9241e8403840f8000d00a4002080307509008540451034012286d40503055074041c5000396410310194440c41c044030306030f40301544030310b0704010100036001c9060711 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 463871420 1250 463870170 463870181
    0x3080105190e0705120f010e0106050901021612050d03050405030930010614150406030504260304110306042f090103050703020120120a03060803030a0e010e010c0e04 73
    0x40034010030002a40b140185190400c040d81c00e00d0000c2d202203600d03024182d1010030f0603041694002c010040b50301d084000d4104c08014064881040f10100e4203000030b0740208014207148013202c040b04c0000741c840d007840c0c413410044030060340d0034801c2202040a080c02072080500035600a0003462078001c1c800c01388100044204034104503190b000810b940e1806502411200c615841c1c00049a040c2c50000030405000042c40c3e01da2003184001c8805101c0c2000304221030458002e420003050036603841c14404881c1c04218200d60070f12080e2070510340345141c05001944540e1041c084035100442003001d042c0d4400080b60010542200788207044a00e40c40680c00302c1040000c1504c49034829018004220b0314682031f442120103500843d8244115a0032104c9141e0b1510581030314041c209250004541c0c0b0251000c124881841c0016020000781c400e4201c4405400750700c003100c0d070300d05050420388028204414541c0c015480e00001d65044401802034004001c01a0780b00e0116403621400c1100422 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 463872670 1250 463871420 463871449
    0x230c010b2b1112060a0b030c09040b090c0a030b101a2703070909051b01021207080f030708070e040b0d03030b120a0305030f09070e010603150807090902041803080105 73
    0x101c1010354800580c0d0f8600402c14007068800242400f41021120001542e0f04000340750710a820003540c2c6800ca456000c0b40a40c8140c005d0001111071309c400582c14108103206000c41e03000301404102006003c40c001c0200d024a81e00380310744410750303600c00512007011501c140d480000d10040003003500e1a01040403040561502e041c261400940c00360002e864224503611000b081501d0f84499000c1c400e0900c4514048642034445407104078501000135181c8054041920b162080820903030180300305034090b03072044c039900b03039425507a4105a41c028140c06002c40e600c90021340b820400303154a0a1a0154014928000d88000656962541e090703020f000701400d4503030026542c04165030b91100800c400c014070750290715900d540c0d080c54105007080c1e080003080c0030308540c89880200710b404445800c25045680358580060b050105540701e051550040d40521f025114030349011401481c3c070b40c40090030a108403410841d22071b00b08601001c0044034500940403981c41c100400150402643c29103100703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 463873920 1250 463872670 463872683
    0xf1403010b031f15050a050907112d12040605070203011b03020403140610030308070e0901060f020d1b020f1804030503010f0902160210230c010b2b 65
    0x1500707054040391404402040c9954040040d10784080240c0484c4a0b8401e240b64003580800003500b880c01080e0303403518610500e4010199000000c0141d8820182c4610101c265000d40709200846c4811990380e901c01c140415450b100e40016024491000526262900225410a041c10300c1c11000780d030745d904400000e903095500d0f0b543c00ca1040c9204031300000c1c60007040e20016203850640c10881e0b101020202c1100d020303844441071149030100c1034603240499a144c0b5103030216607950001180c90041c03030740c040c2e50000040b000105405400c1000301c1801401542103038882020346030101c6000c1440b400400d02043c030440701308094201200c0011500038040c00b0750319003600c03c151034521030404403170580006501100602250200d80286401005180c206600b004041da5801d03000c0341420000a1081e031a20f010022850b0081c3c2d0710b03501d205415800c92400746412030310514141e005030505138a6519100c109281c600c0c108490349013028810390b410a441a038622543c802c500c483c8000d9a14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 463875170 1250 463873920 463873931
    0x180601021002040f0e01050a0803092101051005030d0e010c1e0c06030207061103071704171803010c030608030a030e010b120c030f0c010c06020f16050303070e09010f140301 76
    0x62820a0000700020a890000c4d45001ca1038070054404480b41a045544100b14600b0100b02d03003100002a603115580450b03100a8101003017141c080782c906009458031842d401d02d804c111103807000c85050000c950090303040d0307039100c080818221203100c003044070203000c500c8074014a4040746404842044000d1907194070012034050b529550744960f00c641c448000242c00040d6031b01000998021001ca584050007040d0960400e400054000b850054076000c00080900002d42403140d00172580701d00c214600b482d90343c0c85004810b0781c45c40ca071020204500a6007010180d0300c80310301c0ba2140400700e880d003001071802c011075004100c0140c603112075416840d42d02e5012030895541c5005c02000f400700030344014401d40345048285070030540c841e600004a50030111700740c0c00990f0081004e403007042e840b100041e0749172803500000c0345901942e40e001c0314807680c0306560810408004010350240b0456115120340c50400d2040150010090141c489403c203a0300c8200f000081c8281c0ca1107910030000d001045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 463876420 1250 463875170 463875193
    0x306091103010f1806020d0b04060e180706080c0715020c0304090e19080a050c0106120210110705010c030c12170f0408091c142104051f2303071b0218060102 69
    0xd4910700e42241120721a101c003070000082e4080d0924cc5040b0041001d0501d6501c1d00c00c016007100e40003001070a4869000603280c04014203541141703212001e01c0320444d290b500d004607803556034129002c0e05560519041c20249420300015600300042c80c0702d0440910744995030344141c0260400110302050080900003030b0100c000c05e019003009051007480c01801003c07980100460b44100344003200501a500d041804c8000b0080380420540740b0a080080e242c80d464039085a4004480b40080c00d1001400e0301c41c0841d0b540000724240c0140c0b8140705668036280d07130481049c1c0540c140c40c0140003203010040e8111740c0c107101110101080380302a096900344059118aa00318a002540301650740200348070706110b05241645007014007a40d0442c3e0704150030000401d00b1044001320004a0400c074203017651030b1074840e09581840c1403012509280382c0d807040141074440d82081d0351035800305003014041416030613801c10540060707800800c0c00f45141e0300319955001d030714405405241140104044100c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 463877670 1250 463876420 463876429
    0x40b0d0c0923010f0c02030705011b06050a020304050f0609060f04081b010506030f1501050d1103030a020109111005070b0a0e0a030e0a0e071e03060306091103010f1806020d0b 77
    0x104620442c0c0ca03445405014800185007038000003403407003070084090800c0c01507280041e0007000d8507401c0c00d0540298550f448454a004010000149400e00309401c0002d588580d0300998080d6104804407003036801d00c02105a1105011540c2d451540c0c410b400141c1c2c00702035080003a400a00440c0e405140000c3c1c400c0c1c00c404400d40d5900d01e00e25a4464050040030300701000074100d200c24131406000d001828116641030036106100d00340c407840e103506418042c409402d90f0b101400d038000f021643e859040036000303400f8000d05c01003510030200303d03511880b541c2014041558115010360b98145400304690380d0b8010218064401841e06544640560503442c0820490b4140b1780070348c81d003240000c0300a0402104035102d070001c249080030a01800411070f0408000c03003058505550440d4440b42c50201180203141c40c0e0300140010b0b0404080000344010f40c0c1000303807100001e078024041c02021103035450035540a40144c2d210307802c5508541001c68182c2d4050142501d1426011a14105240019 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 463878920 1250 463877670 463877699
    0x905040602070b0603060606090409051e07180614120a122c0d03270e0403030510060212070303020f0403110109080a03020601060807020c0d210302040b0d0c09 70
    0x880340c5079800180a014089030604596002d1002c400801040c030300100030031014001d5180030f9001c0d03520361800388100001400541010a420100c582000420100c510340e59006c82c443c0024030203a0001c142002482401801c040e2481c12070038491810001043c80b088003126980c18000e4000d020306070340040c0c95900d03e0304075000e01e6500c0684100059100d07883d98036400c15410040404002c80da019a202c540401030415058100140b801392404940481c4a841a50f0109810000c5002041c40360040a00c1c41c041c90007540e080040342e84400e50411110854050312015030b015401002217922054010001c0c0c034400e1501504240c801400d1076941d400a41048841403924a5240d000b56031240d81d14005041041c0100028655500c1c046d485840602983c0100103400000070300c0c80f0f0080089140307402c03010b0310140e03440f030207410884103c285039a08030703050500d000c1495140380d202e4001d0b203058501031039441e40b408244000d918000c010300c4003410180302104000180d48000034111 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 463880170 1250 463878920 463878923
    0x131d01230c07150605010314060a170f030c010f230f280209090c0a120b0402040305190309060203070327080a0b0604050708130b2e0806071e0e0604090504 68
    0xb04602d400c5c10005010b595420941c4048824070408002e04d07136903003040c40701c100c911a00c810300b07108040c0140a4100084000804110711001071110200401503000b5a06000000f0f000c100000084103140da204103898a565807034140c1c0008254400d41100c1082d8000c1c0c040700b60700b403010402030703015a4047c8022a00d40303c81c03680031911454500702050b1823a03011441d44850703840d14141d540050300c00c002c006262072040b81d03141903100460701d07958100ca01843c4c1040488400d15440b410b84880c0e503c81c000704800050b008100011102d0002054600300c65040c0c03141401c0710300110b2180100004c440a0b8400e50311040340001e203404050158101c014003855040c803140c42d04006010130b41e0000b07880704040110b080200404050319060344100b507a403000d0304100c0c0303446803c041740030701d0103d50011007171080826072402c0580c0914501000ca070700c00c034240c3e0082d6540550035203d10036014841d00c812002500352948143c494081c000014100400c1380e803c0a450319a001e04581c03044030b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 463881420 1250 463880170 463880213
    0x20f19090f080a050609030421020102031309020d1103070c02040b1503160e0a180c090e16030501050f0a030b040c180f0e010b030712020d02131d01230c07 68
    0x900c000d0204c24440e003036000f03030404011441c0a25002c044c031f0010136464a041800704c090181c0c2c004580c824001c84400170700820300c0800c6d00b919031018000950180442403111842c012900e400c0c00c18640540b0700c2400c440e11002c08441154090101070405841c160740d10200c078004120320001001d0155000750b1410083c0d0b510398012200141c00d0342c4034041c40e203214805400003080249104104581c410040d101c0201c3c028411940c2076804070559040700050441d41c0e01001070500b00450b414110078103682d800d11403a46d882c400e10458020309041a0703001551200b0520105081c40c4020380c001303109000070380713409680d01d003200030b40400703501005020b90f1504070351214002c040c0078441d02031114100800c444c036540c13000030707690750703041c4c401d803448004129290303c25035035400301c101d40c00b940150201210415100c00d0200400100c00d80001100400c401075104050500c101c040c4040824010410b1060091400c042ca5100424030b651511042046c080014400c1a008401809204 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 463882670 1250 463881420 463881433
    0x230070302062d0a020f0c0a080901021b0a0905100801020a03090c0e090a0308090c061908130803060f041b020a020a0801020c0c060a05070506040b0613020f19090f08 73
    0x3100f034408a0390050301212512440c00074403405801c44100160400440b110043c2c0d15041100c410b802170007103100000b43d5000b140c09507014414044010114103100740d007555009084440c028102c240700c450800d420070301807034090240d40c000ea440141c200ea80091040b00807951501e2441c2a6403201c8102c20000b41c0b00d05100302007244141d0810301a103400b10000241f49040664150384010424010b0100210b45000c150328081c2800b40a544c9140901141c0d5507841840e06550300f00c20400144002440d20310004000c030701080c2c0000f034800d0b4003a00140c615100c0e02e0820031407042030305a0582c0580d8031030018002c1c032004400c83e0083c80b030703980140182c00c0351401008003280d0654052422a4010030140152820206480038080000c40f0b001c0d890b0f0760180c0701142d683c099802c1c000c0141c443c2400b44405c1c4602e8000c954030900080702e45940b014540c207900c00680c01f030320124442004061140e02940d071148a04140e0010b040e10b010704403e5561441c509000050b5448000240c1041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 463883920 1250 463882670 463882681
    0x70503300903030904051807060809150408040905040c0e1e07111e0a060509030c060a090b060f010e04020a0302070b06030102183c030c0a0303023007030206 69
    0x11048409010520100c607824280c85a0119441c1c0c401c0600261145070f8642c00610201d4403124094080400a406c1320000754443c64007422484054034192080c0c400c41c540760301210600801c42e07103d6544125401e04191a112240020304000790044035040090f85c40841c1842c5009180e0340700d014903048e050f480b0001420842040c0d44007908407410400c00705203a26403044000384c003440855892007001c1341001050002c6082c4903c149008000500b03100a0214140c3c000001d80920002041500e0b119118080c0c42e90460305640d000510424002c000254a8503103601708045426040c1048000e43d040f442c00601264000318030600802c2d4040341c070301c00380030910203440d920010650003185408080c07a4000c20500525103000e21400340c0300d400301d002c51124507040902407580c051198178840c1103031920780c490f1048411140a88251080410140390900a1900301d80e0507070003504440c40c406440040c103c0d81716082001082d50f48040120b80300f4000d0007000e03100e00030b9000c0d090a0516 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 463885170 1250 463883920 463883983
    0x121009020a0f034502100c02032416053711060604090f060204060215090d08010e07020c1507170436090507051306180e070503 56
    0x4c15003002c02001d41000d194504412440c200c1690b10044490f0b122042c0e00c864001602610503003009410508900142c00c0d9250408880c108603031085080e9210040300c0c001d05801c0080101c1055000340c40031005c03803030381e151084080000030f025141152920144105144074403d0401001201c121940e411030303004060004822002c000070314101c9001d00025850581d9044094000c0e48112ba50310754881c2048002001100210703884002075490ba90354040280d169100409400c1c40c0180c0400050486070740840c0007461228030fa00d030000142d0800004010b40d02000300007000f50300c1040070301f544903a0303203000240076401c1d11406c1c03c0c2c4e5800c013460101142c1c00c01e244a44240c01050105200c105c85e0340c04070100038140003d1194601100001103040c3c0c0c2403000e14402c14914040202041c04008210f04081c0d9100350340c0004440e000104030000c42e400351040c10410a00070200c131803c8285900448082c036060000c440603e6200d4002034200803042d04021041035051003820341c1c1806 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 463886420 1250 463885170 463885181
    0x41a040302070303020115050d0615030b0c0301060305010501210b130608160501090609061b020d030203030a0c051317011103070f1101020306091302030a060c0c03090e010b121009020a0f03 83
    0x3000c009903901701c2c0c40c1401203408104d015400800c099103a043d0b5120101c90b0040d20be00940c0c0107213511001382000c80204009910071f024100009041500200b01540110000c4000c581f80504140e01b002c20010144018440355140a5000604954031020300c080b1b401854094200540a080003000000031070a9010141d48401d040c40a4410100446500124043c0c00c540b01030070302480c0c441a942410f0580700c00d54100a40c0080008044000e266000010354860001803408010040746190159064041d00c1d00c03000f0b000e44850b03c18003007100300c003604080030080c2c28004518400d8070781511916400440f0800c0c001280f80009082c0203512003005101e05940d44021495400e04070f01095000d00b0042040000020704610b01d01151400c0140100040e08140100000800c1d1200246080b0781440c040d0005900a2400b0558080c04094103049400c04060b03540340981106a40e642054010701d600030010002600090b2809140002c2201a030075a4802800200140d0054106e80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 463887670 1250 463886420 463886441
    0x504030905041509140609040b07021219080a140105040c0203070b251805010c02180106051803030309060103060b030307060501080a02151201091a030a112e0503041a0403020703030201 81
    0x130101406c2c022680c0301c00303044582003600407942c80c06660740d03940c042e403804400ea030140100c0e520000b0003100140c0742001010a550395540c1d20400380e1038500044003900c48054201e900c1b0f13401400108942d140c00d501c0400400410300607642003200d252560b0381100b41c102c51010f460240c40000d40d4400d030024482045001941c00d06c40714202e01c0c840350702c1d43c609641c000c680c14080880380380d509556a80040d6500300c05841d503e0103103981c60f400c00030400e401602080005094240c6e04a038a0329000c029607204500d024014a116031031034446a000c2c01c00301d102e00d034044c0800c105c4480803030201e00650b4040c1c51040024686040c0c5817045c091521840b0300e000c15030020501c00101c82d11100d8081504403411848085128000740c000c200140701080388041c1d151203851004010054015010079000d08100d40c0300728059420310f02010312880c200b45000b00c9034900340a0000d042c0c0110003079070b0424017171440c12140007400b4080b400d82e924140c505030b0260b031007908200f0800d03509024809a05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 463888920 1250 463887670 463887701
    0x2120d2705041e1508010b060901021504080c07030b0f070f080714041e150503010f1e0306020d0504110f0a03030c0812130b07021506040504030905041509 68
    0x114110114000040901d0140610450700c031104020281c1290400404614402400708040b8000c4510030390f50301c0e5144a035520550920501d03410b10700d01f80d030075140d1510040e005042401c0c924020a00c00074001802201c1c0d21006000120f81d1441c108030306009148201c5004200303003812120b000f401c8e0070042c811020031100c1407820f020650b10503401508281e032814078802c5c03a945402c40d0840750103140c0040300c03041041003508508a030038101da002203440c1c445202a03003010311542110300340700c02d01510610010b0380b0410003101340c4404542041c0c04480c43c00114440e00c5c1c2e42e0300410781c1c0c04225809000f0761654188800c0c002d0488480c040050101c8003100402c0d03402022440031902480090705110b1034941c03d1003440021401c80d41000c10f00c0c84618400d1070400170307107200f1800454065034407080780320010f0300c0580006040d0010f40782c01d0070a4400c550f1508100030252070000c00c1281008600310f0300140d692900e000e442c403151912600b941c03c00d410b1049000032594070342e08a00d0407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 463890170 1250 463888920 463888967
    0x303130f090f061203030e2a0906090705090909070e0106090e1503210c0f1e010c020307020f19090509010c170a0506010c0804030c15021b0f01030902120d 68
    0x4c0034003840300000d144d41800c0c0420041030f140c20309401c0c08c6905010002c1e2101d1502c180100c1d14001d040021f410700b08880a5503d902c0c0c5906010080900b1114880412401c000c459210724052040a40c4166000b04940d05107456174990803c0d414281c1c01103003c01c204103c10b0000d210001c081c1c0c0d501250302c0c2c034610100b525079030000e036582c0c1c2c00c9841c809103289000c058604100081007212426100241100c400700741c1111010707518805861111440c1c200694242041e901c1805600307181061075000310f060600c940c081018842662184c29405610b43d4805140d80e0003116514001f01948200041c4911b09405101c3c2520944aa644104800c2001059081d5a511005a009544020000b450f075075100700603108104020300c00b41074414082400801c00c68908081c6082d50f031215003142c100351003114260794510982038080d5003e48046914a17050820500b0b030000c20205140205904500707402240380141c02c80307020032040e0080d21007a04420740140024070381001c81c40e1000903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 463891420 1250 463890170 463890179
    0x30513061e57030605090103290f010303080c2214060703021203040203030906041e050d030c0f17070602041706130f03032007020102012007060b0303130f090f06 71
    0x103072a040545669000b0707410241c0749041c401d078040e0000e0480500600c000d561241020002e000c150307000c864800700c41c80c0c40900483c2e10030f000f040c05072041c410001c0c0a642595015524010000c18910b04102c00b44580c00d0b40746c00e4246030302d985034140c0c004184800d00741811540429942c5854500880c02004400b000990019869049164880c2c4240e100e03150b030320002c0d00754441c2800c040e42c007000216000c140d088083d103c1c1c050303200c4440030440c80e480d03030b510038040805091400540030541d500b01c2500403803556450b0b07001c140c0c821401515107040303d455102007500404004c0d22501d502007000c1c4400303a190001004029a904001c103811b1030940004c49050311109002450130342c0d001043e034101402070700504054480c04401040c100c0c1d01159003501604003400c142d006608003030300c001921882c030358403004e4014010036a80c40d205554803003002511642c2210741d018482041400f82c08100e00e95030784041c2601011210140340740c8601d01d000e17640400c0c1600d100d24541f000400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 463892670 1250 463891420 463891541
    0x1306030b071103041a130305010608060a0f0603031205072a0c140303041e0801020a0c060b090601050a0c050f0604050105040b1506162619030513061e 66
    0x2018000c5d98409039900d9103160081c3e004d500d5550300c02400b640c01d0100c0800c80100100c2c1061040e0f180e86420400480e000c204041614114413010f00820744694000e18100c0782904180d510212030b050002140c0d2040c10700d80c848070607014a4840101280119500700041d0ac10200010801e1070f000700c40181841c400203450348550700c102621491442c40030303403001041242c130000801000000715200d00d00c10402414542500030111030b001d10700f6103520746500c0c1100c205030080806a48690034418451410340b0a0300c480001600e040c13190300e080d003025520801186100d5403207100042481c1c20700c1c1c03030b001003940b00140a03288800d0410300c170811903888600948074000106500c4900c824000e003054030104600d5017440392800c03408194030f1020400381000700510f15100300da0b408030014040044003200c20543d29010480501e4010030f000c00c1c260740260f084030b1046502c80880310806405039049440030b031900704042c1c001000d6056481100000800d802d0304030201045442d05060218 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 463893920 1250 463892670 463892699
    0x30306030c0301090c060f200102032e0905130c080d02010506120613110d05160f0b1e1204060c021501050102150a06330912111306030b07110304 64
    0x7c0182c03105450309054440c2040005188100b1186150024083e030201d001c0e41c000c903036590030000900012803619002c02030407410800005a40f0340c0b401d042c400c40340094003000e025841c084603171644200204040d528410018030102d001045882c40191004e42901c100600d2507218100c1341c84070246669000c201c00ea4807a88030115480187c409160041a103001401e0751038005110140980420038001801c40040030a040090101135490022114010003406031700d41c0e10340d041c4400c40032103012005250154201c0f00e561810000405800418402d007224190703501a00c3c1e4500000040d014003c4907107880d0792039200400c56040c140080c0d912155080c0014030140600300240d90b030b003140c0c0e00010250000e030b176101e020103007024007541e944d0b16516100e801c0d04000c0401240101d0050154008951078154490400c080e140c0790b40c55041c0320070f190b4907080b018899248081a1541c841c80002e1445800b8141c108c1c04c1c807400003803003040880215031450740104401d00050201003400e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 463895170 1250 463893920 463893929
    0x203180f01170603011404051501090b1e06090904030504030b0a022802010e07090f0e0109111302090607060509011a0604090b0316060906180501080402100302090909030306030c0301090c 82
    0x100d040d80f40d2002003801080c004c02050b82604840e000d0004104001c20701c611220052803414400b0f03626446c82204030703503805070819072013204c8601d0040c4400c1c1200c60070141c4d2400820315400c0c4122080400d0b90f101080710210300085000509008002442c0c0da4180c100c084c0050450074402c90513a1002c0381d024031344aa401800e54a0036071a0400c0c801d40207181c0d0700750f1910941e00b10580d03450849015100c81c0a04448450400d40d1610b4a1501403040000e9030b6005003030b0180c110100300a20a078508000034015840750204000e01c0c641d1940f00c01800064441c0d140040e107840c04040e858211808030b5160b4121180c03c203078010b02503403000140c5080c2c8880000c000340203c507810009213001400c00550030b01c640c0100c0006442d030742140c40d80040b182c0301e0700c903420340150144803403c0383e40c9180115804180316002140150504840040480d00340c1e00380145031418890014804040450b00240c0d01d43c400400c000032b5007402d01c9080f012840950003403207854419a1000305c3c41c000e6024 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 463896420 1250 463895170 463895207
    0x1506180901180305030702070603051b0a020f01090f0204050105030309130c031805010c03060512031e0c011d0706031a0f04090212060708010501050408030315030c100203180f01 78
    0x4100302450030b502910705510042450992403420b46400f820740d400841e041e03009030060f80310000325940039009180c4a500784600c4c07094108580510b105164016140082c2144900d03101c1d0141240c0034420b00c500d05006124400c0d62102610401c0107a881c1600142e00980060100d08001c0c2c60703010741c11340028070104003c1103a60302c0602c101e00401d0780017800070603011107035542c4050100650110402602c80d550034000301c2d4581c020b200e4034921501802c6d6841d8402c200300d03404000d41100c4103a448004614a515280060799071600352804031003503038003034100c02c4056801004c2c2004104018407242c1010320010741140150300200b030703000030118056191180c2208040c3d03510303070000200703950007001a285408011a11542e602c01181c195022811aa0001c0780e158080c1c3c05480c201c1ea4118011403440e03694284c1d4041843c6100e8440b500351083c4085401295540302031062142e0f40355009644481d03a03005065070f58043d101c03415020b0b40951110203c0d40e60303c44a1003580301c0d42e000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 463897670 1250 463896420 463896469
    0x60522140f1504060b090403050a0c06060302060403060203160801060504140d020a0807080c01020c06030411031203070e0109090212010e0c0409050708061207140d0807061109031506 80
    0x24100c60810040c021254901e015401031103040510695003540500d00800c0304005004090062004e008400d4401402041d801d21803990b4540c0f140c481005868802c560201d91a556039000c01c80c2c0c0d4100c0d40084031059004170400100c40415080a4011030451038030040070b503d0180094001c0c0f207640a0502c1c81d09001e4042841d0b0380701c05516451040d4040c007210324640d60380b404181c035002c0501a014060261040c0c400c0c00d58030014000102c1310005050a2641d00c9903656040310504e020401c607003600420183e1545a9007400103148101143d0b101d200f41c000041000410180c4241c008032600b0f131040c0400e001805601c81b91a0641c2c2c4025144202034440500c2c0c003c25006680c800d59086081004008401d07921240e1280181c20903150844030b5030f05280d44585030182c50090b01010300f0f1901448107245030109010140600503c480ca02e04409510b8000644400b114440010b0b08001207082c110300f0b0030040c4450480b24804215a6800c15100040d0440e04c035100400c00c604000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 463898920 1250 463897670 463897703
    0x807030e0f070801021902010c0504140d02090c0405010906090b03040b13140a0309050f0d0b0615130510020a1e020109090f060302013c03020408060108030304060522 73
    0xc00948401c207105500b21072072a90398080c40d6000c0c2d844500c10001103075a0707a405000050050181850b14290740d00c507942440c0c00c0450514007240e1b00c490381e030f51103800d008000c400340e1102d02c00c043c014603c0310307115a59941008000750240c16a603008204124082c141004801d5003442940d41081d0b00925904107611501488070007900402c6014112a00d0001c420700c800400140c034110180c821b44036080d805a81d071040281148c1d0640c852904121803509250008240b104c0b0182e2091005204c0104402da001d01400d258102d601c0500f42541d00c038005100616044142c02003150305480140240c0a00341d89940004080c0304022001900016680045a000e683d00d40090001c804042064003041040328020704000c0c8000d13404a00d02d41c100c0f4034442505c0c0e08202c003c06d10100030021260301542c520032700407000360800c02010f500380008545064144541c0e402045071000854803410a07080ca03200321040541555800304100b0b03203140180c100c203551400e001ea00080c1011066028 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 463900170 1250 463898920 463898923
    0x304020102120c0f060109050124021e0102040807080c0607110f130b0a1505090607060209060f071b0f15230a03150b030f0a0204080111071a01060807030e 68
    0x1000c2c2d0b61a401c00b4041507000340c0400014003200003291482c03c966060b41e1b00c1c3c4800044070400c0c0284a5412140c4614015528005007030202189161040316101e03c0b0386280604900400f810031429650002410841c464003044110003a103400405050841c6000f00003550920840350020160b2801c085207050342d075500410000c044c10064064203000212030b041500501003100c0c864412690390b400801c88a024503050030700050240c84041c07410201d60100300703090b0003040c000c072481d5408101d44403403901c1d900d0192005030b00032440c2940700c8181e0718110300c0c1400d28030032060001040382002c12060b80c00700442400c0329908001000e1000411000b140c00c0d01030f540d4030030701000ea600c031400054002c020081c015440c02e0340e000c020b40504043c50315a290964818580049014004146030340101c0240d56004101e05900501d00b503581d15009007520760140045032802000709080d42802240800c083c030740840c40c142c88000c0c0d810701c2d00290603450b02604840400d070b80c43c60940d240020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 463901420 1250 463900170 463900183
    0x604050c1b0c040f0c080f0105151c06080303071202090604030f021f09140d05071a1b060114030607080a0e0304030f05030309240712062c01060905150304020102 71
    0x18060f2007404208440101c80c0090040c041c50322000a1300a00058186180090316038140c0707100520185400403900c1b650301540c0c0100c0e002e1003901480c1d40c81d0085021540c483d00c4e0041c04068051a16480c01034000f41584180c00c030030385291401046080181d0b80c6001c1210300f40c0c4c0d03010b00c45c2d6502000e039002160104900275200001c90014030200341c545500f04441c1000c44039181030b00913410382803905000b9802e404140080841d4890070040c030240c280a601c0c00f52160300740160703034100707060381c58803002545841001a240fa0000001400f00d030014043c000040b0005400820641c103106078010542100100440105d03595111401480711003401194015a000030043c14030401c82d040260720780c1e04c280c40481e400e110303000c100a00d10f1040003001822900c2d07844440c01a0b5038986095450703200c42c4824266030380d65080c01141d4520703015101144907018500711071401c0440329101035201010b8020a050010050003008942d48009044081d01a4030014544035103e03440140e19002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 463902670 1250 463901420 463901443
    0x11070b0d1e050a0906050115021c18061d060c0a1101140a02010b030c092e170a030306050105192015040b0a090f06021e031303080604050c1b 62
    0xb424201400f0781940f164000c9100140101e40030042a41c0e079070130911402080d4444507015810946003070407110380549440341900315605000003800d00703c411b108070804c0d4581003c40810300600b4020050414684c12003582001940e10030328200d0359420582c0e0300e07051001c0c01000b041c0000242e11a5134030581a6100d0f00900101301a100c0d041c030403019028000074001c15000e0310940450b1001d501d010503040b4080c142c52a09922414034042401c25407035480039004000181c0c80c0340002d039a02c10444500e480009500190214880ca490000d09644181d88110704003c000c0c050030000385100b5880d141140d50718180301c1000315007214200c10100d446000d50340c0601552007020300c0e0b0f214900b00c1c203102e02e2248000500603034031a060041140c442500107003820101703d21840c005a070300d9004003026060601544004103995890350080c5c0c2c4100e58803402910144100d100b09500b1080c0542c10400403074043c4404c0c0340500c40c5030758600030032601080341000d80e000c00078101000e100d11403140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 463903920 1250 463902670 463902731
    0x80913020a020307031d0d080711030a0c151d040c0c020603040c170723040b0a0602031b011107081b0307032105040210110f06041211070b0d 62
    0x81078041c2020b9141d40000d4410381c0451180c00f0090340307407606081134030868100240345c004038085507260000d00360405002202c008040d0f56412406907000c03c00c0c0d00003240300b43c074040c1032982080006c0b005000c2ea4000700040c0b0448008850740f660701c00e103294045910039280003c01410b0b502d030440d5581e0101e0070194010400001340000d0107000c00014040c4c503c1000507409080c0c001d00b503107030381e813117944a5000307249007104042c80000450b040d524200d03e002080800e0100c0c0440002d1360740c6890341d00c202c025a1000031441b01442d910208108500003c0008221800030030071000620b10034000010300d030003400203c0101200090b01598806201031045907125105483c000d808842c0b038a0703c40122216032001010341c60618010f0038070441d0702501c50351006226400980304c0c01d84100e0441d15900035440e00c100c40032010418240310b580034000402403c0900140a4990315282240c01d0b05a0416a003d002120034141102c039681800d80d00010044084103c0c1c04a0f54645110020071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 463905170 1250 463903920 463903927
    0xc150912031e180e06010f09060207060305370c0521070203071403090f0906011709010e0f0610050103050405190507090f020a0215011d04020d06020a0504032001050708091302 77
    0x12901c0d801c1000344600380c20f0b200e20410390031010041da2380c0c1c540e901c1110016400060180205842904055007204854000d2940303501b00b004124400803041140305c01d142c01513160380b4414085401181a24202d5040c402e140540319506185014052400b1020000b4a1004114414400c000b1201401d400045c0c0c03c04084104440649030b90003145000c9c0300b16011144806246488214207025060507110344100b07035600a10614001c0c4010103084c20b41d5a2910781141d0a4000d0003840d0850400201811043c9010001d44040030143c0e0013070360402d07260804000000300e00144041940018a60054220f285890000d141041d180c0107022801d08000e00c072102034506070084c228265807030702541d00070741044200c40c01d030180034440e030340648810030340da4a0f450b048503441d01e070481e0010745a0030300a071711502c800303081e64490446000058400034081040c0000c00c04001d94205482880b80003410074500020910b010707210002c0c00b034100c001a900740a64843c0c50220510f00000b005548 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 463906420 1250 463905170 463905179
    0x306100c230607020601080319080604110d09020a08010509120c0106050411041503111602060c0105040f0507060903081b0a0209180f030913090507030c150912031e18 73
    0xc50380400e940d030314050300c00c20b070002c01e107d040441624810a07a0210150082c250127070f0842e00381c0c201a141603006580c40a42e0807020902c000188a0b038800e0100c040361050061060011150403030380074001d164580000d1008240000c101d01011500481d009921124500352140c01003141da44899801071a00340780301c4419507906c5c05041100c1414244003030007c2488020750580342c010001000d48a401c00000243e480c21120214089002411090034000d40d1100719007122000d40b01502c1d15681d035004113003080001c00800b4050030071858048013041c5150341d801e0f401d010783d1800b228001c2200121502c40f9000b0804030101e15001004094241001b500e01c18044101110104607401b0300700215003452000802c0754015213000d402d500f00d2010131103080000b000005c404442500600300d00002240c0020181400b500290034107182f107240010340601038101c940d1114011114524180000ca90442425807416030115440085500810b00403a020381600722504400c0842000106 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 463907670 1250 463906420 463906423
    0xb031e090705040f0b03060c0307020f060a1a012102090409020d03030902040c26070905030f010222030b13050705060c1b010824040b0607030201020d110306100c23 72
    0x800300e03003003641c0c208100b0514021400c285c07000c0101075600360b0301c4000410000040305009540c466014416140c403189103000305814108107841082038a41c90306603140301800c490a0120071502c0c00d00300f10719510301c8a10010341a003039034010741201a0b400300f003100c01038544c1c0d00000070590b80105804440f00c22480d0140c003c141988099001e141b80503509503a4902409101d00c80510200e0303400c0c000c06000000d0450707c035004200c941042013034000002c45480401c90008071300c65100002d030b10780707803840c02c010080c90903000e404041500d458820000b1400c4608001e80206542c0c68075403454440341031903483c041079944841d42084000603030540044020818010301190f0042c0030710190038000045808940984505004424070032202e44074081c1c2900b0003030481000340c808550041c6010004209800c01001540980d40024410200700032074410341c0984041d0501180c20b60800b94013041c8450352108440f024030220403c42c00c10300c045880044401540c10044048240c010005d80d07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 463908920 1250 463907670 463907683
    0x1701140405212b06080a14060703020f0f090109050604060905120c030c010c17040e0403030e120a111612020108092a010e03070303092606010b031e09 66
    0x70b007100c40200d400030041007901140c05180400c00e14810362580c44040101d032810307202c10700e058141c0e940030020389141c050100d805028043c894285100240e90115810032000503c2242054410411000340d4000070060710f0032521303180c601c503072203441400050f100d03842242c00c40c65020101140000b01960301607040b5050351000d9480e00080400940240e03502c1540070b00181c0d00d42c12129036442254440c442c100c1625025244031000c801c903044d182c2c08550f10541041340140500f0003000149509802004205401400249940c02c2d00044142150050300700305801c00403400004549200d0810100ca0442244400254456942c0321440d00312281d401d0124046205000050400342010402c0c01644030007034507403400c810b41c1c0040401c441f4102c40182d814040e94651401554a003001080003940c401d0300d60340080c50800b000c152404c010400000b1400c1102c8580320100c100102c0d10702e0440e0b54031046152681c03502076200c00841180b030202004040c0b1001007044e100310004a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 463910170 1250 463908920 463908943
    0x203060f0102011a042309030a030b01020a050d18080f07090b01050708071b03050303070305040b060f031b040207051c092114100207210807091701140405 68
    0x4026440d160200580c01e880b22030303c04503068160034030f91143d01c0c18180c121200b4244c1c0f00f10440c454202000082d1440101940c01c1c5000360b1020911480c4c542d0984203248050074240010814a00e6903079900380c0d01d0030b45c00302e0b50003007000c1c1d24203074074003c11001080006861a401540d50242103695010350f03c06003881040b0700c1d60300300110a10154019011a040c807600306445a2400e05035031070b040118460b4401014141c40080400404150144051801861180d6000c41c041c109401e201c0c909403006400c0c14414505a104064203070340025a00208116a5a10301707041402603000400078040e288001e09680500300b002a05844007500380e1115800300e441d503031201d40d00c03440c5d1004054078640366000448100da41d0b0502245d1680c956140c0e00706600c003180e40c6e2440500c1d0540981e002248111640c040481c4070039000030307901251501100e030600d440e007103914000b00000c01402481c455203030740c0b14030119641542c000033342109124050492030f01c251030400e0303e052030381c030bc2e440e461 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 463911420 1250 463910170 463910179
    0x1032609030a08030f1005010801090e031c1505040b0609131d07170106031a100506040b0d0506090903121509010e0601081b040501121b020102070b0c1314130f020306 73
    0x81108500c2c40e411400e46e0320680d04c5275100d81c01c242c5000001c05180c0b021044c0780c801070105410b4161880446a03c2c110304c99004030300d2641c51060211080f9031034102da4451420812800d41c152220015900a480b044500c8812521070000b043d00030f00d4414044400c241070314003d410240c800188070000c40e1141c01880c940030f002c04409908803011400010030140d4440c1d203081da0808034017113098125290303020501c0e1041c0d50b6400584660310030382c00944200c4c00411040b103408124410b6a0b480030044e50b2001d900d00e0b240c00c5807910ad03c00d603111920800d00c0d2601141402d840c42040c9402800064000221075850710400c00c08600200e48050009040707000250300000c0c05995600c4103405c171040703181040d09180c01551018140d8a01458455440c00b1640e00514103c900b284043c01e160001645d40c00c0034107142403615401071465040490401a910b0701d4201c00d42c03407104680c90420070215948805000034080040111242e0311141080d140c1d0010303107000e41c02907000d18421038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 463912670 1250 463911420 463911451
    0x40503070c09060803030a090303021c0c090b07020d170403320307050a080f0c1504030212120a02180301050f0709050d111003060b0a030f1401032609030a0803 70
    0x100c2c0d0388141e03443c500480000d9003040c8086111a42035400c0100503034441d080141c1000380401d501982c0400c40481510303529120b000c6c00c28000d03040040c030b0026040c03203010580f420741075401003141524010002004004810343c95582000d80500b0780e0061940000c001a001000750042110061800498404509441181d0194001c00030892303c0d1240e00c0300261518055648812480d500007040300e8440341420486040c250905010510701901c24080311507503800d00303040082c94101c44100740021402d08000422845103203543c107542c0a0080d20001d0307aa002d5103038182020442c07002946030117600b044107002c5147d05c14407146229076500e540c0c6a02080c1e0390710401c52042c1902c40040c0c010000350100c0d03152030500c5540510345031004e0501040c107a64490541c2c3e902d9100c0d0141c42c0020740d8484c040c02c0703503808a024001102644045001155046454010f9602400303180e60350510f40910007400c07010141d4082c1e070000e00b8010b059030101c40442c100301d483c542c02102e480a1100808 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 463913920 1250 463912670 463912679
    0x3030e18011d06210609010b062a100e0c01030c051c051302090916050604051c1103120414100807301b0e030606011202040806040503070c 61
    0x24a00d65040754400b0808500c24800500e0082d00100042d0030540c1080c1184101c003141503070902c40b01540c2c000b82c001440285400c0000750308650408418511a8504000440d245104440c01046403184800e40751958095503e0701d9240c031041d80c43c034010752400c0000a00c84024082900120f210013a282030255071642001101c1510549112004c0d17200300140315451800103502c140e51044c0c150140d006020080c1c4c00284c030245044900e03252661109010250408141e040c0d48020801596810705050600b00000c00d1040700b100800020058020040c1c14801009444211600040d06035854028207924000c6568018055000c212103c010084814109400b10081c00621340e62060041d80b640390040352184071001210010ba94805e00443c0d1241048009900c1e14031041d0340090240d00c03014545411584884216060040c603400001c115100440c8040d80a0400d203400c074124030300c030050b0000030301550700040401e01c40c101c100300421000000810225000e40c003c010b901b40d03039 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 463915170 1250 463913920 463913959
    0x3030911030129120f03030117060402010801090b2805010212040b040603050702030d0e07060905010f0206012d03080d06120512070f1406010504052a090f090103030e 73
    0x10341e0245407003c04040300ca02c6078005400703140444414010903802c8006141d8000e680b4054503500d500500d500000010040d40903d80e00c10160148104050b00c554546070b00080c084d21014072504460f01c3d229a41c110340390b03458a45103441114000c500858414000346a1035402c3c1c1c1700d015181c0584109008015424415025074044450b00b4428524042c203148084000d840054848800d501c401d00c0395803600e00d010b00402c2c1c50a41c0380c00085c02e20034134001008001449550046041c800c02e160b40e550780c581d01141c9203040d40c2c01c0c003110b210200141b004500100340340745249046800000008020001004001c02c5142c0001400303008503910342070030055508248400402c42d61100d03526032031060701075002c2c140c4c007070107986800511303590354840b01809808a04890200d0300600014002e620f4203209180e0040113421294400c08408000700444890605030320446400c08031320328601d9030b90040c90310804e50018100701c0d0a0359403440d010304507003d040798540c410704501e0b0741c08031507a04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 463916420 1250 463915170 463915181
    0x3010207050c060a0905090103060c02120f0304060905031c0510171c030b0d030e01020111160b0c0f0406090906150801060818010e0c2409060d020c0109030309110301 73
    0x42020160000d140b480042100c103500044480301840b44441000a481e965600264001d5008400100d681c814000d802030030011513801442082d0030501418001500b000c003503950240e0f01100028000c0c1080c2866444c1d4010a080120140e52500d03512080b10007a410150064802c0e81e41c5141c06611100c002c000d01c60304014110300f551210302d40c80d095541c0c003602810750072481c3c10006179803d0701c1c80104821503052001a8003045044c00c010b942135a0901c0341c00b000083c0511800e04241201001e600b600f0400310014140e5400070000c10b038001440001c5843c45c2c0c0d15000c201e80c0d84d40c3c0d40e04c03014002480c01d2144255192420b50009041404071a114a00b0105070b500c10300d01341e08101c8113680040026190303c0c0703400403814003641200d009124101c0300c00507850040440301d10440030090f2850111078911540c50a5109520302401c80310243c03005005c003100c41544600c50451510001d002e2105450825800c000d802401d164061380540d40050280025420840269050500f07841 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 463917670 1250 463916420 463916423
    0x1a0306010e0115050a090308040303030e1504080d1d030a0801060f0503010605030a0c02010b031f200f03091009112b0620030c0316210911060703030507090503010207 73
    0x400e142c441d401e03c1d00c100d005145c480315a05005154036100d4a0312131158006030030031008207964a00c861310300b030310401c131200b00c150078090340000520b040e40d610000e034040c0d0303604a543c058540c0c100100110440c52010301004200c0120b0341c545650030401025806c0038807a040100d01500c10410026114408690586040380c803501c3c65911101718200c01090394203920b200315541c44010412964040c00100303d481e408401e0306600080121040d01281c4900b10400202440c00160700f070518407071004e90310b0105d210900d140e02c0c0d580e810b100d0b0f0300380500c28100e0000d2615080c1000e0802c0001c2400c003640003001d46a1044039205d60a4100341c2e04900e481244154884c2c140402c00501c640e0421a501180400c501c0c50102035680700d4900741d0026100e541e8210780210401002d0800d0800c0c00300100c202c0e15180784030070704288484410402c3e200001c440c0c10b48070140c81050280444860200c6003001d80902d41d00d00150800500802c0700342c5000b000a02c2c1c0075800280303860140290b074441d9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 463918920 1250 463917670 463917689
    0x14010e040804060804020604050301290a03031b021801030c090c030c02060f09031b01020711030703080a110106150203070210020d02031209070911070b0718030212101a0306010e01 79
    0x6043c5882030b250301a004000701d80c007940402000c1001d440a0065262044642d44250214503019812214124001600c0340c003e050078881000400c0c0d200d004042d00410750102e00c0001070072400811011f0035000c601c08652040480000200861105030700d084549001042212425016045042d200c60300381e02d10042e40441d0210b11b8424810350500c0c0c07c800200308492503e5440e0305000200341c040414207185175404038605080c0031a94510b401d001804402400b08142036070785900c802c2c010681200d04000b04040b404111314002d40c84900984060f9890504d10345007400000d50700d601c8640b040340901d0400091070300302400000d08041c103ca00d40c020707604042c1079440c82580f22070014240c4030b0754840d1890000340384030320780720b4946c110300300909250b80d4101505240e490a0009002c20041090390868805221940e004000c15070340d04603104114441540030395840c0601c499602d00c9101e20b4030035403042000d120000c0d804150340640541e010360fa82c40000000842007403150607000f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 463920170 1250 463918920 463918927
    0x906040303030b0d051b0a0512030a05070809090a0b0f0f1005070614250e0a050609030102070b011707090b0f040b01180303050a080c09010f0806030109060e0114010e0408 75
    0x3402070b000040f41e48005000d0003621121525407500e4017040c0c400310303c10392410194107442820010a031401500e8103503284030300f07a00d00c0d045040e913070b00c200e0f40300000704a0089001e42c00c00c408001252071424008200c01d04c24100448807100920415804501c64040301d588440d0500b090511032162a40080800665036420b8038143c1d030340ea12101040b40c003d581c840a00d035144000301941401a00c04480c1423410508000c0903030700b44461101d40609101c042e1012040d2a664054140305540050758010388a030102e01c08640640208200200302c54840b5002250200302507000200c84031640044a261b10360381c001c5001204d0b400302c2c1894000c0b4070014020668280342d08140a510010b1508001c0315206068602440d44241c200b180000e1001500540690340900c0054000780d49002c05c0b031410000d1070028010840c0580d90000340040140003985a035000e6200c1c0c0040c5802080510200da08200118002c142d003510001c03903410004000b00da84002850214843c07680416054038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 463921420 1250 463920170 463920173
    0x19270e070e01080f22080d1103150d061b0201050415020a080a02340c1401080a0f020c030c0a0b0108210904020d020d14070f020706050912070f140609060403 69
    0x200c8803030043c6011034a2564402070781510040c100003507600b07401003d60b1500c5100350700b10032050301c01c810aa0110080c041c0240400e40450a9000c21608011104425211301600d040405080443e61001045103004c04400dc15501034112921841c4a40d40d0701c0c0c2c40307003407202020b000c0b400b60480e690300140c80c40300040d01c40d11080d401007144801c105051040601c0304d411441c1c403d4081348003079001c0c0f001500031038108440c203204580035003071602525482d06103540000f86002c10080201040d41c1d150043ca450820030ba904983c078030b803003c1f01620741d10321003802e019981d552100c50880b0940403103400002ca100000c0f03005010444403411043c20044480784402d10f03a0800740c0c10950246c0c1c00c20034800c2c00300c6030784000c05520b50300140c0400c0c041d41c0301c4e0306080a281c0080115062040585001403000d9020444505844d182e0400039125400b800100350a20036201000482e44104e01010078003201c200030340350484e011801742c07100b030500d0385061204500804030391a4000c04180010310 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 463922670 1250 463921420 463921441
    0x19080a12081e1803070f0b0f0c0906070f050d0c02010210050906071815031a040c08071d0a0605190f0c08030a02120f0907080604020619270e070e0108 66
    0x241c0110303040c1080c010011106020300d0540d40002000c441b0a04814a903800708544034849507030010081055880c00e1801405001103407281c2041580f10f060b00003981701c1007040d19034861020f1170700042100c4200e0108000038042d8000e151050f03000d44030f8000c601084444500a284c842c820147c0640000d860324081038600090001070740c09a800c0d103c0002c1001e00002040032040305a981d80402e48003072040c0d840190740b20701007155008900341040c050319944c120641d1500442640303006c80665071000003400c081303da42c4a80343d0b8000181800047e1990b401009000020180e41c04042100300c10082074490360b0704401d030707400445c400141000200382c160014541c41030b00d03100007514140c02080032100e41d0204692151240d010841840701060003040198003501c0090001c054605080d00007915074040c40c0c651103c1e40032204c0f0b8206401c0d12500c1881884000c20f0700709031000104082000b07805a460007440c421001c4140054201c2e40b090b880c3c0c1c082e0310701c11703140c0f0145611494a001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 463923920 1250 463922670 463922731
    0x904111812032206030609050f010e0c0705060a0203061c0f12120203100602070f0509010b0901021914010b060703050d11040b0706140a09050d0e19080a1208 69
    0x81d110780418002150540e41c00214402c0c060b61050040d6030701c0d03040c6100507013118280e030060443c43d0b02d402d041240014406100701d0640b96442c0580540d9910300d0068407280c410010024031500501c414030910114a801440c050102210710840c1070007207640701103085074220b10180c04210754102100210f002c451003034488050ba480d001c0e050411400710982030741c1c019582e064165245880410416505001d00340c0600340401141104500e0400080c84411042c09843c940e000005212402c90707000704140307041001d940c007660190700c10901303050843c490040440d102c0d83d4200001c2c6e212038a4020111400d081c0d060b2106414031640072040340007040102c50b6403500500410021903060a50700103400c0c0148136000200301c000d000258582216070180810740c03100d0500509800080b400b0a402d16605518038162401c0d04642d0001450103030344e034250806031b001d60740b004070700c90b00301080c2070f501d0501400004048110740041229565000c03521640daa40d410410161000d104000342e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 463925170 1250 463923920 463923949
    0xe150d03050c03070b04050c15030105010207050103420b040e04120215190e0106080307121404230d021315030501061d0106090305060f04031205090309041118 70
    0x44030f04004d0259504901004203440c252001c4d441086820001c0c03504400010700d41540740d80c0141907515003c0041e641d003040780a220705168a8440e003503440c01038034034610103031180309404843d211a051510748074100c855503404000c1d00c009034041180f40ba00401c43d811a002501ca40d0301d01e503650345404c000c840c030550601086018100308d03440940012031400d4001e8056000140803500c440201000b213407810510f004440c3d0412000308202e003030100030b0380d1001c1d4102001c5c2c4420340400c441102c413110b502c80e241003844c00105011542e208122a100c038000d000c0320400206142e01820417900002411009600100b042008040e4800a0b00580510074003140e038645515102e90300d05003036820719041240040041460760440349446507103030740102014208840c8040c11a2034907911110001c2540d015000080042401c043c032422403061004181482000103044c03c0d1011071b1641c0c890350240780b0035400e041c0803c3e440e0100c1c00c02c0700c03070580d08045840401122502400308032207000c0301 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 463926420 1250 463925170 463925173
    0x4050904140601080105070207050a0e07050703140301080c0f030a0f08090d021e10090f0312050c16090c09050a0512010b0a090c201005060406120308010e150d03050c 73
    0xc01d10110007040024003800d15100013041303600d05041c0c0285060600e40c0201d120315685001005001391546403142c0202c607900d003460f544d02c180e04042c4d65540c1004031a2503000000030001403030140c0030600e0300c21240d01725100c07010303070b40e038081010740d603d40306403001d0100e0000800e08000119048001c02501e580581004290348036034002405181c031050029402c0c02c20090200d1072403a11381c1b00a00c043c0c81c141400c00e0010b00303040b42601c140c0c40500004240c140f03402c10300e105140c01041039403080882c10b01101c0b980e28040d03812640e064864403906240303030f040c00c0c903401d0000d0040c481d21041d00c1024009000c1e50345060708100715810b0880c84207a155695810a44c0749881e403a581001414100401003002c00c1c291000620480c1040b845141c101b4034100c051080450121f1000c20b80301310368030b001c20705440310000100180306917888180c8000d1410300300380c03c140d00b116000781290f04411080e0000d0b41c4000c1d8a807040e080e5407031000d07801004581c0300350000740104003078403072411510b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 463927670 1250 463926420 463926443
    0x50d08070509132009040c020f030d020d060b1603020709020f0909060607020d120f05120103021e0a090e0f010e030304031812060902040b01020f06071b060609020301061404060504050904 82
    0x40501c44134000c0101e10000d51007000501c4592070078980100500c0140b1480100144c00352500d00f80c0d2a80189243c10400a40001e1012182030b615040007014208410340c031591078503043da691780380d600c61a100b140903024109002030030ba40c41d4425649900000900704e8584403a032000c21011060040010b40c2c464000c0c003c10001d62101e1130a1240f5a03c61504908901070118002d0048990240c030324041050170002180c0030411400740504485d4165558208440043c2c41c070556031401c840706c00e810a0705940300103840b0052381c00c94141e044800042d0388903040980ca005007691f800b0241501141c1c02000441c000910511103044980580605510401e4070b8000c45c110300159100305030b9480ea191502d51082d450244250003625400340014000b80d614629210f07282d400051502d400d02860210440161080d00303004051942d2007003007000703da5150032102009400030302031070000a900954107100340f00004101d6050710400d1f00c03540e0400c1d02d070074100103107800700070700071035080300344c007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 463928920 1250 463927670 463927691
    0x908030a0309031b021503130506040507050a0506071a06010c050a0b0618060306150409050604140705030a151e0203040308060f0409030e10090807060804050d0807050913 75
    0x50000e40502615640c01103070050700c030306006052040e12600308100345880005200103980705280140541d0b407030a03030551a99078241120140c15030201d0094064000c0301c081204125020030100181e0310215403a03c645a2100140300c503500550b00001e0000d0400c071440704030100000780c0c080d4407400c14542000c1c92101c0741c0d141814004043d00444907940c1e10300070310980b8900f5401c42d070303000e1104080c0140507141c01000245c0d9110058098a0f00814413140c041c0180c54a411944e031061b04501100d8403414245800032403103542a241c0304d440c1c0101c00c40440e10340f802140244001e6000364901314444090300d030b0800140300c11000811b41c0103208161030400e103600d0020311300c0341d1b0081c3c58913400c519116081c00b441d0091030704168840da140c00c001e0350000b9002401c82d81429001c0d1030b0681c40d01e50055060f00c40c0e051a8000c07403154403039200000f0390300b680603400603c50341c03260081e1200300072144002d0340c5400064402401249007880020014144807000c03929a00c0134074408901010b00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 463930170 1250 463928920 463928923
    0xc1207050315070207050d050d080603010f06030804030507050603090715021c1107050604050109090f0f021314010513120201121e18121101060e0a0c0f0e010207060f0908 75
    0x180c45088010b0a56441000a10358041c1300c1c010090501b528480700703200440d540c0b076485451502140e01800071450106a0b50744095001ca41e2002155000b04030300d0ba12800c0004031a042071000320343c24401d111003c1400c0c00c10b8000d49000d80301c00340040c0410b03400c00e80c034003c500000111130021440f50100200c15002101d4442d0036801c0c1c60380710003594400d0a0711450402100c0d4000900a1008010400c82a40e002103500201d5802c1400001da4a031007080e02d90141c03043d015080326a50000c078080c100404810002022150210108484035120b140151858050b250789110404600c1070200301001c515241c210003944140340840c2c5d40d040d14a030031800c82d1224003488d00611035582c241803c0402a2142d4140046407981c8040e103424650364039109100e10442550400c520f087c0916040b1000750813030000340ca0a14220308561800040440050070380680c0c1c080055010443d41010b2409070449900600303040c0d0207004400c5c1000001c0d5200004128103908001244d100069003060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 463931420 1250 463930170 463930183
    0x603041106073002061501120e010b090708101203030b040507090611030415140708071101031a0f0913020409050d0306060503130f170a08010f0801020c0c12070503 72
    0x1080d052400b40410000310f0742d2107182000042e5006451120a0201180c0c0010324607a000001800f503003040f103031400040b5000f00401c5503a500460078601c481d01c1555041d00020310716441614205240d5a540b00111002c48007a90248000303e00c2035030a103c034443c20003014000c030380a03081c00314a1042100c041002c64808039a48400202101001d0145c0d0b0742c401c07910703140018802c00075824a414200b145d25403003d003020301403d02004035600c09507180030b2019100301340d030082c2c03101c0d445291500303040c0082e11212001034002450480b122071070030b142400e0441440005005840d00c00080e006001006002034403003610041e4444082c00141d80303900440061600c40c2c1c0280152100c2140d000d420340c1c00320b8202c0005e001040c01080121040b10b00d5128240d40c00c0410200d181c01c06045c84800d200d43c2e00d02c110508640010306803c2590454172050488401d400400c0c010b0755038202540c200d00030800b071a85a500f10b1072000e0030300d18198041000d45800502511901d81d51200064034100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 463932670 1250 463931420 463931423
    0x4030312180b0402040c0201021216140a02030a1b1e0606080706030b031009030f080601120f1d0304050a050f1306060f0201050f070903060203041b0602010204030203070f05060405060304110607 85
    0x706000300004c5051074041c50103c0480d43c00254141840080c40307460500340205402c140100c400b54003d80c10744684140450a00d500d08400c1d0fa4034034151000b5201e034020f00640700450304141184041a516130140c2e0103080e001201c40c0e0b603c3c1d00c480c031807140b0a62807440c00d807040c3d81c8600b4049109a0103000c000c004090549000a2620880b8203050801e80040e1411151034505114075011a8210802c102d8001c40781c9000444c558030300005031900107600e02c280d20b031580b610a82441c0b0340f4260b842a4040301c00c41000f41500b200c1803a03059502e204500a85400c6261b403a400c0001c0c1c20015034206011600420b5160900039010b941c2003100e00740d90040002880c0f0450020210340c0a03c642904500025441880303440c150902604251044c40001c15403a4000005828492040154180440e1604607940d01558820b4000c0c0070750410f0109a01c24007070300e04000b608200b04d80c1580c0480b030001d00103e0506e4600780800c2680c0d080200140ca041580d81c4019050342e030391000502465 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 463933920 1250 463932670 463932683
    0xc02010b1003060f21080309030c0709050105090f04080d0c090801020c25080c0d020f04060f1e050916020a050322060503090c120c091e1003080403031218 68
    0x240b90900c0100d41c0c04c001c3d44202c0000d840034581c048000c0020340300300d000e581c000c40290303034a468a0340454514401c4400204640c0200100810071001c503800440c101d4104541051081d06c40441c803104d041f4040d24000e09111041004010891103501709044d8103e190501050940d40e8004182c03d9174003580300a02c85421101056800c24916821855500c0c8103011809010f42400c02044d07517544240e915620801a0300d00d41400c5640750710105c0c0781c80038090804c1c030a1130364a216482110496003d2141150901010129512880c4450074200c030401130441c000c035120118441000d0000c40701071002c600840c1c42e2880421001c000034280803c1c400684110071131029400f0f000c90030721740c014204002042003441044000000e40017011482180c55070450f407400d90b100b03403030718a82070700d03060300014075000700103501815141c41440080c0b036011a400aa54040900303807069141d02000f407030b03040c00740014008244540b00c2481e924034408000a450b281c140d12005005158a40490300b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 463935170 1250 463933920 463933931
    0x18150c04030f11041b0f0c0c081b12210c2113060801030b06130f060608041202010c020601090c0e091311030115030f05100203130303051b07060c02010b1003 69
    0x701e0070940720340708118150801c81004151880c00c020104600c6040c0102040003c0e80c61f00e007032008854485000382002e41c11100b4120320184950521185895454070400b00009036541d00e03103010442595620200c1d4820301c1c665040c540025554000d010608218800d02001d411911166018403e450b03103002881e507200c106140740800d04100030303000b1008000000d001000001c002c00203054010074110341c080c203952070000f000c600608080ca8411102410090002a0b07a40c009217514003c50142131890610740c41c01000b039003a15000810040107900c040f0040010440a50000e10344120030b29124442d809900002410303580c099403103e180072450348440d0200240c1c0300703400e444a0420340c0280001d00c010f50030401c10601901c005010458442c03440301c100601030007400c40b070320b0312103604540302d013410003160038454040070302200482d00e00f10104d00030310f880c100786403625040d104101c1d10384080c1c0ea840d107000c1c001101903081035640fa40c034240d9682d900c00b492600b00000b551f400182 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 463936420 1250 463935170 463935203
    0x1081834230102031207080604140109020a110109050a082d0306130b09070309170708070b010e2431060b090d08070f0b0a021218150c04030f 62
    0x425041d80d03002030555204000352460710075000c1c0303004da001d100f90400c103074030b66214004517000d8a0480f201001d4075140800119520320383d81e0141200414a684440d042180d9184c11422183d60902c09020f5501c51808000020b0b900e20080001c0d290300c0c202c1c15101c402419051403605d0906202c620604008030400031a4103084e02c400c0d034090100102407040e50100404a029108094068010143c540d84604140720040c8000f8116031320240401da03545545040201c400d400098045944503018400011440c0881142c207024403540103020b0543c802e0410300c90f0070311000e0006035030007008181c2c40040c552200d20105c22010041166082d940e6007000da944100e40d41604900680c2d02c080c401c001d130a8a492a1041d0b055502860b802e44d540e003182000708207115128002090f03d00a00200502c050395030300581440122103250b14001d0311404440300350114000c400d983e8036484404a10070201520403419001110590810300d01900c030707240d5181c92035000c441990442000090001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 463937670 1250 463936420 463936469
    0x6030705071e02120d0c0305090d08031003060e030f030c0313120f2a0209180609030a1d130506150d0e07050a050d030e040f06120201081834 62
    0xb260421413406091540103040010b0f000b820b03204000f508200c8041003088180c1c58512080b4617035900100380c25203900d0400f0702880484900d000803582c107401d0941c0344940000000a41c0c0d085007035011698290703600d140c0c4106043d0801007984a501c4140429400031688080c00f20001d002a540c4a40000c2d0b00c0c3d81c000703407010420b000c401d07031051b02c542140c140b10404100f24000840c1d0494a020b0b41c1e8403400340543c0600744180c1c0a0f002402290240142014000010b000e025207540b18804004001c44403061182242003055803c401140e007660404141075106543c0318000404110590722100f40511503504a05440511241e560744060304030942000344400407e0121103140c0028113040c0420242074201c00b000b0203114540d0010035150b5a1500100581200c0d40000c00c60642c1d10100c85c00401685c440585c0481c01400100c1c1c1c07559800043c0c00301011014006180310502514503030540d0301520840e22035a1181d2902050064603100a84014410b00b02104481200790032481d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 463938920 1250 463937670 463937689
    0x50607140f0d0b06090301110409060803040b030703091412040f050a080a03080901060503060a051e0411120a060510082802010c0f30020a0b01030206030705071e02 72
    0x424014805120742041180c1a00469416080b110380108808441e070000c0741203402030b010304940c154280800040c1c0c0c049801c0c0a0000c44064000600c6042e903164401e40c0c4911403801112201c50301000011540c6010b504140f0300302c2d1085c8550301642502d0038450b404c0561690300c804a07414001020401c5003103044134500038102c2151100355413864084050f594000c01c0d0300041c140311612000494540081d840740700202006410741700e0b20710b8041800401001c0807905200c00140035008201080201d0a500b440740f0303442890000d00b03418420030000c001001c0404041d02c3d10494642c0030000b4401c0c06400c1c01140c06040090740641802d04c850708001c55148068040c4000844003000071040d10f0006544a4080c2001482e16480d810041c061a040305e0f07010300440d4001141d00440440222420582102d09400318000b5812040480e2142c40c1c03030801500d40c4850780300610252074054015034100000d070070402e14205159503280d144407548005604401503100b01181982400c2490 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 463940170 1250 463938920 463938947
    0xc101a130e06180f0a03020d0305090d0807110709060902090f030a0807020f1c0b0115020c0604030b0901060f081b04060b030f040206210610020703030813020102010b0904050607 78
    0x10320825041c4040180e41c0c002c02040c0d40101001c90380800201001445144988500c81c0c082e10719040703003800c021b950740380004181c400003072030440020341c1c044c400702c0c1c104558206030341c1d0f048294840040451760f00d0304a60a01401e8002c010001035a0342d0640320b03c40c002c01541d10701503203070b000000070440041207002c1e2085c00b0b9041054bc1f0400074002400b2111401c1c1e0480d01055040c0e04000458903401c0d80308008512a00c10301243d5083c043c80890450481d101510b07a82025400d40000b261210000c03080f03ea0002c109200500000c7d07903241d00700781d100b89424000034013a0380d122040f580340748103030340441d076242c100c0101522400300c00620300000c2c0d01c040e9014407030245407402c1140c1c0c0c0e2100818525460704203001090071550355070f04958046400d400c400c5080d2a0100581c01020800c0d00c20038803403604407014211960012826208680e003549602c006030351000c20030300c080551000c0490441d581c80460011a0f0f94107401d41c2d00075401903009050324030300a88050110101701e180b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 463941420 1250 463940170 463940209
    0x901082707030b100f061b0605041406091f0207020f090709090c080c04060c05010921080a091e1a070504060e2409010e030a080a080a090f02060c101a 66
    0x906100b117482050748401141d54a18041d00844804081c0580303084a540e002094203082102384402d026101c0c02d12a0b40602480640b4800d0700c4d00d04000350781d8544411030002d81e00d80810310f4441405982d010341320b1a1b00107021500e41c400f60030001200800b080740d00901141109400303100302c1a0724070805c1b40c480c00303504001d001c5050814401b0854040d5106050401203603058050400c0030079000300307031036030b9100d4141218034001d000d1913410041070b0342551002410200000706880600c0c02120300803500320f00500443c900740c0e03411703c0c001009008180c86588041e1566882d0a14060001d4402c980940e1420385139030410300004c5c40f100340558024071860400790080a415000001c9031300000c070403e000d0760340c0e400080060390300c05060841c0582c180544d40001c000c0c070008000500132080d00b541c40107100e0b907031007008034111800d400d005440c40741d000d1600710041c10314000514980d0f00443c00c1f0f80c1d50f080c160694a06031034403514410b000c01044081d4010320704291044042004d400712 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 463942670 1250 463941420 463941451
    0x405010e06010f0e011502010b03010e011d0c090412110f010207021c051002031506040b0406090501080f0c0f1611010f030c0815120706020a0c0b0c030901082707030b 73
    0x1c408004d1018180100400f40d5030144601008900035400b4016000d4054024041e110b0515095402000c014150403104200d980c04040000e00101e910010510001d00042440d10b81d920ba0b0403030140c045c007550742400602000c0900c070441c100180001c4803c11400969101e00c82e1041c05120604000d00101d826807850703441c00040c8010071040e6403450405001a120b554044d0240e40d21007108100b980c1010000074040743d030020380c42c0108241e030031540b620f1840c03641ea080111000c44084550b00c082100e80340215206ca100d0500500c03c0c00c0402d22110b040c2880ea41c901c080010103900c0469854280306507500c00395811001151180075075081c20002c074001688040c003c000020411449140ea000580403503075580040c00c500d11000404803805a5203c20300a07555009a49050320501628038001170014014001c8a8084103c0400346040103039003030056444450140041c03035540352003401c140c40c1c0301e0150482c4d5002880e0788002d162281c551304201210342d41c090f1860000c0c1c1c010700c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 463943920 1250 463942670 463942679
    0x709021204030c050705130204090e060405030a05030705071505061503060d0f020a09050f150f0a06032c0a140606010905120106090501060804050c0d0209130c0506030405010e06010f 80
    0x19035036540c410381600741814410140c0c40e103c1d00b000c41c0341d00050b5000021442044030f0740c00a03406070007603800c40202040700c1410020980d03500c000031a0020900c0d44100551185c03903125401558000130341e81006820582607540e002440352580c001c0d004a16070350300821002c1d01c2c0c0409aa03050410900000d481d50401c400030503d80c6910441c090310206151502104540b1000c07000340040002c1d02c0304214a00700140c808140090650f41b803820302c140c00d1034031103d6203001e46a01c58000c80c010154813080d490070034184c010305555200d4040d0020082c0712001c00c2c1c1032030b841c1c09843c03484003406000c1e035a0441c0381c8100c60141800140089900070001c000c440c2e6086407801058079800c48000c1a80f00c0c0b60224103025003401d4120100d2507040000005200e5000800240564402c00c02e03101b039071090901b88030145031013841c007070362002c0490003050a00402400c1c1001e035900950038060710940b03c4011400d1031740152011a4203039035655491500d454203100c0340e4058100035600a0344035141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 463945170 1250 463943920 463943947
    0x40305030a2304030504030c0611031b01090f0c06180f0905060316140a0e070816020c042301080f0c090a0219090e0106020706080114010e060f0705070902 68
    0x182590341c56681e500c0c0c558400d01c0866070001540110a020408600d050b00c0c004040e0780083c401280c501843c0c0038041082ca02410344400f028201c00001c0d4181129203000f520031140810340c00450307540c0d9040748030200e48103a907100c0100c2c1c000e2000032001464108010030b2a10a00c01d18040f01048200c2072010404142450086682e00390003c202d039165800005c0c10051840e6076000c010892210000309009050b9103246040c80444541710707416135039144c111480400f1a4020001355407100059411a03e07090b442042e10290300c1140c0102070854017240c100d0b4142154068402c0003410104410b1f00e0130748070103014005800291010102481c8500c0d030318104062840c0c400c10a0b1400240a00825419224081340754ae140010071941780034081d12460480c0640c02140e5880000841c03842c0c00001c22100711390340c60303440d001c007a17282c0600400100d850010940c1085909144841d0b643c1e14400545080c4d4603910080340e0b18035442c41c0c6035140c040da40d4002049a801030026850308443d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 463946420 1250 463945170 463945177
    0x7030b070c210e060721030b030a260a050315040b0303030a020d1103040b0a1b020d05030a0e1f0e010b010c021c05010501152c011103090406120303050f040305 70
    0x280110241030142d07140040d01e0b03030345600100b00d40060b4049840c100784071480217810722000e0b0402c03400001551b411011800d80d00a82a81500760344a00e240400041c1c042c600340e034132130741b40c4003007050140c055000c07000880d8807200340240050382c040188042400c56080001070103d08903030411000e40000701082d1680001415004695400724003115060a6900100c01301e542c5c0d40d1001c0d03940c4c60180f03003004401505580d0b45280502e0403001040c42e9100342c0c80b64040d080950002c1c140341c900140120f1f421390004012a0744207884101c80466480304000031b19001d515040520040d03207402001a040f5030000880480507070400b40d074901d41e0b91300b0158801c0401d406035202c1118000c0455401d400403600c5900810075071034440000785055204403031a8a030b80c52a990505c05980ba450044401c2d4420303049500141d4482d84d0481341036008216201440482d00162800c00361a500014100c50709580310701f00915182c1000820180d0620900e0b9011401540f81c041908190310000c000c0d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 463947670 1250 463946420 463946453
    0x24010b1201290a08190b0a090903050d020d090506070201110f0304021908010b010e0405040c050f0a0f06020303160201020a0e1507050a11090f0708070e0103090203030a0207030b070c 80
    0xb4101203003000d4405600a560718942c4000e00300d15a5850741c00001005808229200260f258964004200300740707542c0584164002c004042016160800079444010700c88007408400b804002c20480130070141d41d00243c40c0b132014030607002410b11010300b840342c14140d0091140b011a40341900b61003000802109070360031a0500d58089450741e0f1244007185c1030075040d0895052041820f10f00007140c5c0d10540002c10806000c1e66629889a2042e05010039990252001090300740c10b24014803603801c0400740d804d09403000500d50f14005640383c2c6c10a03d20748103500960010f0f040001000100d0310a9a171244039000248001c51506403103c0c001800080c150071450310030300f9608180c920340d14103081514007043d0804250b8031245101d2070110303400178a030440a4001c0301c00a0010741030038800e54005111f5102c0341c4880c1034a03510101d0458000105003d51418107a0350341c4140050303103041010340404100347d002020901c6c25400c220000b03020083c40c101c208443c1c035405200107010030b5084113011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 463948920 1250 463947670 463947689
    0x3040314011505012a30020c0103110409052e030512041410020f120c12120403030b04060e18011d0703030804050309030a030504140a0f030f02040e24010b1201 70
    0x902c8602d1b01102030b0a02640c446a04401542110048584007078540c8403c0529000c5520745154400190165240400f000201c0c40040c4000c109155040e08200e60000001c080c4401d0010f20603d10b0035101c2c0c01c1c18172a903011245000600802c40c081243e01401c140171501903090514160011440c42d0405002c0c500500b03015a03010b40d102c0c003c101e20701c8414903000c00d445610080d580e141916402032640b81040740b16032400400c1c2c9081060894a240c0003030030224103640d403240c50640151044112054015950f071304002400c08040c080140078410b800c140c600050031024a16003903800f800c002d11140c8419014135500c010b00010803500b00c80c2d02d400c1180341c3e81e80c1c6081c040c0c214094103544076058003480064070201a81304004200352842000700c5200b0312035001c10720078200e0050084003588610b010f024400f1500710f1800001c0355200400c00304d01071500403001130030144403159140010040047e001e040d144613040b910b01420004502d80d0524810f44038196403420b0620920440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 463950170 1250 463948920 463948997
    0xf0c10090c050622090905102007050312070e010305100f140d0f080903120408070324090308090d05070b06190305060907030c051e04020901020304031401150501 71
    0x2d1918a8500440700811100b00603807903940f041c2c01c101a0140320012030f13280c000e0001d920208588d503c90800c01d10000c0c5105103080e44461510405580400d030300742c546200078420140960500480340e441016a03648404421056500250503034001400e04440000224401e20042040300c919008031041e507120102e0410035403020a8854401c000e000d060f40305040720b44400d21120300010500c24400b074040365000b0304403001d01d4569000d6801004201e42000c00104041910566001d9100001c14508132608620555a40c01c071020707200201c012075086001c12034503038418040324014100c40c1c01d195240c00f01a03901c04400c05c0d0000c01c5070b071107270b80605160488401003140910145500a04031403403424400000c17640c9081d103200465404405040110380343c201004400000000d2100b51020041d2500c10003010350000b528250440c4000c1c80000301141c410051183c8520304400002010000d031a210440200503800103414041c0e10070a98140307804801c40c0740b1003100c0f000f090041d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 463951420 1250 463950170 463950187
    0x30b100305190612050d051206010507081b1609060506031306021b01020c0d09081009110a060306030b0c071509020f27070912170f0f0c10090c0506 65
    0x30641489030481d5410b2421001254900c10f043d44d21070218065400c40e214440300b0304003240c0c10702c1a504200340064908010034040c4d40200082d180306403048218a0801ca45100c1503491080c1142008501d5400200c0a4400800d003c000f0030291a500f1800d1089a0070300c0c01149081c4000b61041c0769256983d180d01c2c1c01d02c9804e50580c4d164020300c18001c1d0044110040c0903000c3e42110022031654044c0d13041040e00175004ac0080c0c011184000054441d02200082000090403010b80507107280d0010030301c906140d5161300c0c080c07019250b1030710002229801c508110000500c01840c0d1a4201001c000b04400706d441c075601c1c41c1145a450001241c05189807005c0b903000401d500302990401400e005180c11021000d6018101202c540c0502e10103544402046a2510702c41c462400d501d603410381e980000c0b554042c2d150700840d8408030500e1610500100c044829030025001a400c41c002040700c0d030440c2d4041c403003c5281768242d00244a1800c41d43c407203002500d22440381c14416400080c5c2d000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 463952670 1250 463951420 463951441
    0x1202181201061208040e011d160c06151e0f051c020907030207060c0306051e01020703080a09060801091e020a031404110a0603110a030504030908061f06030b100305 72
    0x1005042401014401c0f40010301d007511403a0418000c0c6180300c005840042280d015400112184244e101d87c064140d0310f450b8048000b248002e0706180c1040412110706010031000d0248020096519440d21070641c0341c0480b140040c61076120409a489401c1c804000c1101030640701c000707480c011140c004449010a1001301c1008003204000d4200d1241820014250380507405011040d0180409102a005000c401c400b20fa0b072a000710749e030009011104c00690b144540d4400011001030045540c4035841e6110002543c01c4428440300207008054180300390b990001d2282c0c0103007492401841849c070380e4900f4001000c5800c03940840d0a6012540411040c483c0d0802036904044e000303215420b06084c100f54161006450189000b400d80000004150340302b4032a8190004161940c01d05050b2369a00c00c402034600034100b90100503c12001042c44c04090002c180503c110004424100070160303003100e0700c8901584404d0030f141c5003807401c01c62070b119900310f11000c181604d030001e22551000842da = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 463953920 1250 463952670 463952681
    0xa031110091809031e170c09060c101803090302010311161406070c0f020603060a0503030f030f010e09030d200d09060605060f160f020618011202181201 67
    0x118444140d142801d220b006a444891078a000342d4400c011007107074280a81d0301554034600d2100140301075480f10301c00200c500d206070f041400c00d800c9610f4170743c00200090090300014564405600b00003a51116149607101f04401025500404582c00c40c1d06e0710043c101880030703c03000e4103054841c440c440e5800f100e1012900c028a040c0244542010340781040702c000c00c1540032a2415100346e50214461500912002800759400401e01c1031030b01c0181e0034810280c1000d80a2500b00084050128081c0d4040c8043c0c01c403606002503454903440c050505d078103050b006902c203051185e001002e0081c1900040122080c401c0c0f00765010030b90032055100314441c032140e2149031002c03800105241c6d00e020020f400215080b0301072001448111b48400130003031a4828188a00308034031003040415115214902c1d01420107006010407480c0c0052500480c0301640b181c4020820810110207440e410360f009255038094444100d8118148074042c504100c41d00b480c0e45529225141c010b8a4602100003500300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 463955170 1250 463953920 463953929
    0x20d03020f0702100c0201180506180a090204030b1e061008040f0519140607050415021204030b070f030e030313082205030618030904052505030105010e0a03111009 72
    0x300d001c4c000031180c00402100900508a0000d440f02461110030488411101c0c29a40e00400c1549050940200900450286c0d0090b90300561070720030000d2030100030300c06000218050649040a072a190881c6000c003042c0c4480079007000c408030203029441c5c03654250303c1c6200c13200e400c2c0110305880358100844864400b182c014102c0c414610342503030001070b0400e100c2d0b400d407251185071000c40030103480d40d441d55000c4501000241d4103100401c20402d8a0254108046590050361001021286116210b90061700b09641c000240c10501c40c205a210043c00203d9640307207000c01584041481c5941c5900c40900044004040d10b0034440c1402a4a411643c40540000c9600010150941e02c0321440c480d0f0b1107010320a000d05000034810713042124000c1c10b100200009103141191090401c40140400f401d82804e80140c14142142c045080c1c0c80c001c0b1101d16500c5207526980362800040080350058503207400b039a2035220410014492141c1c040c0340701070885001461500188044490300d500303502 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 463956420 1250 463955170 463955179
    0x5090109020307080c030106060e030a0209041707260702150c0717071d0709260d08010806060f030a0f14060a0c020d03020a080a0b030106050315180a03020d03020f0702 74
    0x6002500413000030b50116000d80c1500284846a03480300280d401f0907202d0300a80e095080740b0441001880c014210030341c400e11420032074111b070800c1c14400c0b0b01508400002c48030240c50102090070480034402c2c06402040d16144145410026404218004192101c84182050208103004011814081c02016017078010040840c03240c0c5842003507030340174248185404031601c4800031201109803004180b04401644460307040034585003105035035840726040a00509007490706041c0551050000c001070407810395442285505047c006401c010000d08114410034064400c000c980d200410850070321908108500e021141c00d0402100102e000f402103c0c00e4003600080100f010b10075400b0414400d45a800c03102e012429090035402c03403144000c114040b41d01103000600c0d600031900002c00d0844094004201c89603200c0200c0d00d415462440c107070450052104002d8200c94086455051107045c1e40201a118100d48010b5226000c0340310a008154000032502e00034801300c400c4528260b4007a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 463957670 1250 463956420 463956433
    0x5011e021b041b03060f0506070218130807050d1e120b030c15070606061713021f0e01230f0a0c05030a030c02010c080601091e090e160801020408060604050901090203 73
    0x15004001744100e000d0300003aa18074820200f010304210041d02c40040d405040f00b81d01800d4200381d6480c03402d0081c14040c905078841301d10700004586002a2402c648158010300c41002200c00c087c0559070080c00006e0781d6592540034407152580031442442240007440d001503844803000103c2e0411021840047e0007491030003900140c1c030800e80060510038020401042042e8032110b00720790400c04502e0702114400fa00d00410884d000000d0581c034034503c0101455a03008000c10201c03a0b042d1003600c25030129031422104035403541c019030141d444092960106801810600403030b541401122814150294007240d20380019015001c50820540c00c4401c60b9222442100014081d01000c0d09900046d428406940c000b24090341600d0f014050507142c10003800d06141c1080ca031201e10400e06410700e46101d0b80020750703e40c2031182e100b14150344c00c0500750f910020a0302c4420b80c001a84038580300c1c0e204200400c09158084be60342d0300281d003258085583e41302d00024a0142040c01c9001e5451b00400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 463958920 1250 463957670 463957721
    0x20f1210060801093605100b1809101e1401090c05070b01090e0a0b040f0308060d0b0c0904110a02060709090e03030a02030702150f0105011e021b04 65
    0x424041140c00329070310005944e80384d003240403d0303a010710403006801e2080145800306180d8151101002241103408264004407500d40320318101c640784e0b80304038240d5250000201e904007400c9994046503a514200007070308040c02030700d41c1c400302d84400102c4242da5500c21480000d2400d010209001d24178400d000e40100a0900c07042c80c0002c0c441d01c18a20b2608881d1242d40340190180e81c01c20780c0068500d1056880e0042c00e00141280c0c50300034045010b04440400080c0c3d20584580c043c60094000d052030850524001e020604003a0804d88103040c00001c0c4400202051400740e07000301d03100800c503120f4038018003242c0a050184030244400304c0c00f062880099500240d014858031150380d90900f203990b2420060100d8401c18009450f0b50400c00000b074036030500d600190781005843c03040b20000e54100d0f1005500010540e00380035110304400c01044250307800680c20b03800380f00745407070f240c480f40b403285020b0341d81c01444003000169084224441001d07a00ea5014540e00d407404007490074060b950 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 463960170 1250 463958920 463958941
    0xd0609110a091e05010b19050f0408030d0518190503120411010f11030a03090c03120804031101062312101e06050603130f060915050f0c040603020f12 66
    0x2803040350f074a014900c1480c00a0311040c09442d048451544000d403030280c5100c0c4954001d5400e011200a01000300b010301090704a01000b840241403103400b031610b511006803803005507240a00200c60754a047c2041000c00c4a01041405203155404204620850b061801e141507000d0007410106244080082009002d030302c900000041000740d8400d40c042c09407490070345000030b8080700b00010781e1040c040701e01031a019a0000c0000d9000e48107801c402a52036891040810341c0c4403141e0001044e0105010415811640c40040c143c0500002c0c04101c3c10404220b00803545c00d200b0600ea60724400511034291151103240130111900010344001c4008460020064000b40c5220000d0200c1281000062030f918400c4509440c0000c0520340b45864004009802c92685401580d8008022400f03030001280c510580c06040e00c50117210512030008400e240803900010300c0200360003144010001c4117403d620803101600c006040041e01c40c0c03400341c13138054140103031600344c0b618510010a1007242a10b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 463961420 1250 463960170 463960181
    0x70903050d09030c0603020d020702060403140d3f0608070f06080f01151b050a0c0902031308030c270a080304230411070b0a0501090b0d0609110a09 65
    0x2610484118540100341111190b880f8440503190040c410ba0500c0500d10a400628000e00d4004016040c05180d80008051754805c4e4000c076021600181e0701030f1105414058065000c5e01c42c100b8140a128030b08030320300041e009842401c512125441050140980c15031501d0846498074010403055444a05190343d800c00303030158180c6018121070000c0c10902c9a40c0c598170440344c4000304c124591a08484008081c00c90300f0410038044503103005000008682c1d25031003440d024100070f103405202c0d4146001c00558581101c4e1200d0300420400c10001c6420b00080c240382e6008695603500d86c1c44507085100c0e0f0240440b070a5280382082011100c002c07103100c04070003941c42200c6140b03c01d950380c19110b0fa02c0c0300314811114031203200245c800307800480c103c015000f0040940b02140c80074600020a880380d00c803180032900b10300210b0a01406250340d04c1010302624540408000c40350b50700000910050031a0130082441e61075040940070002c0d03100102d9030280c2c0c040e05240380c0300c0c0c035429a18040c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 463962670 1250 463961420 463961423
    0x90f040207080d1a0316090504020312120105010e04090302031603111614030606030a030c0201020304090c030c0201060f270f05070807030506100c03081b0c070801060504201c05070903 81
    0x1404c0d51400f080610740810407031540e180400701c00301c41c03500c0d01e50260042c10000304181c2e80344c0101c4005644c1c4c090100000d1000111094003020190f040c180003400f001040c2c6070b500d00030b500e411699000a5000801c44400c0021301a5128005950b0718040300c541540f01501c0000e4000c0c05540150740346181c441106444d02c01040d100308044a10038107075504030494040307a1580c007503004080480d000385e40c01c4811a0042c07042d28509610f800d41c07407041d6049141c0900000780e80d04000d0704020350a1041401030304009100d0000c0703524003c1c84149128048084a01e90312808a8200c000c0506501078010026220401c2c88a0302c0c00401c068400380003101d00c0030200f814000042d0880ca090080c52040780c84d00d85440c416401c0c17544041b10344202c010514846003100d14200e00c1012106005000c9600082c001000103d05007241c2e036080d04c029034071130741c0541d081c10304038100d0030541e1984444000031003010f16251080c0009251411035186034480d02d0601d09002d100804c4d44c0000098181c0303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 463963920 1250 463962670 463962701
    0x171803010e030c120c03093c01170f0a020a030b0405010e180109080a110c09090607091d0106050c1006091a01021b0f01020705060c0a050c0306010b090f040207080d 72
    0x22003c4c0b103540d10280c450780c1407211440c1c00030011102d483c170385140a40a16000c4030010307103440c18030700141c0c01460300d001c51218011074040c901d60407a40c0d1101c07404507100107225040fa400c3c1000100750b81040006403001c41c0c86600491100c1d43c00707109074403182d1501401403050106594503008407200d250251860542902000c081c8890360205005401000c0e51002c111450550008422100e46039100c0150905010340303507000000d5a0f41100c2a40203d02a03c068901410800000307002c040c8240c2c8103944040b000186115480b007a00601c1d41126124240035540c4c0e61003c000b60700382401101d00680442c030b00240402c03408125801101001240d5580c2d00074441c0e481c0059035260030b03040c0620511414003042c3d2500703040a42c2241404441801208c0d141c540705d40000750560400252101d050340018000700500c00d017000000e00c450340541c05042d65504090543da903034410300c4480740c0100c208100312149a1641d6044604031900519100c0c1c49840784144000038200700d15440303484 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 463965170 1250 463963920 463963933
    0xf070f0f0512060106050307110604060e010b040b1509030a080307090f0906030b0a0e070b070803040c09090203071703090a090f0b090618090304080a030525171803010e030c 76
    0x141c00c2180040c075054400e42c0042500340c0c41c0c5101110700b43e0000348450104440c404007406001e90070040e550007540324580100310900301c05085c6e82100c2000e15541e1185080100c2e0106075256050007500c1d00d40c403034182a540702aa000440d142c410f40c54002001003c000081101f0164408200d90030394a4050056050581d43d500343c5045d50035502000d008070342414049040385c6541d9110025960084007582c40d002e40d40c00f140c6556411a4000359112403000080100704a8002034150290100260400a4490b50380200c0d44e030f40c2c44c2d406000101008036840e000441010820344040351401400901402c2d107401d5a040034216807032005001e1410101180968030340200d0341440b5030009024a45030310181921034252030000b6000d69041c0c0000c02000c50802405c1c089103506c50302a454960340c800b890f10080300a4180c042c1c90b403420000c121401c00c0000e02040c145407611000b64140c64031100301d49000a070582d001c0e24a558150700c1c20070840c0314564044050100030b0140420b0741d04 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 463966420 1250 463965170 463965179
    0x7050a1703010b0313050c150d20070b0907030c06090501020d080c0d0c05070206070606031208010b0f030901150315060f050a09020309031c0b0f030109030807110f070f0f 75
    0x300d40001c0c0154114880184002812a0184642c5000c1d080c0a88100c1780c000301480d0100d0081d03041c84017200d02c95500060300300141002030007040501811440d52414280810710340740114007540f40020b0441c400300c00800c6c4800420080100510340015085004139500d05025080078000e100d00c0e07015004000c07100600900030011030344100e40c2c0480651900301c003c0609001032079802c01e40c0041c00818410312300541c59a8010701011486500300280c202e0540c20409842185852a1000c00800000501002051070151040c030340400c03030300b80c1d2680c40c2d10b401c55000d002d03003140c800300500310303014004144021500c2501c0200c03400d6204100294481e000944280a42d00445800c151444002c00c0074070703543e03401035038130049000c02ea03400c00c2d412469481d504015091030020702903e236a20b039502854171140d107025445049000b04105d00c0f4668028007410001403602080c03190403880d03104000001d000751401d0745986002e4400c0552540700850f0126181d000d00142c003d000700c030115 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 463967670 1250 463966420 463966463
    0x615090c070203060708060d0816020418050c04050a060b180f030f03040e04030302090901031109010504021206090901021c0518070501050d021602040f0903121b11010b0607050a 78
    0x901c0c41c1d402402418081d80c0300b40040c0d83c1c0210280002c0d0704045e22030124000700302c144010f045140d4050081c1031007094680100000d0315031201200c0ca05504078400680001c800180114915805580126550340d42c40c84080c02002d0b2230b0702041d51604005200c205401c07440c000b0380d113034030011034010380c814064109042c0c1d00d00301c04641504644c001c100900c10101ca900e01950701c02d119180262520022402007400601c0a920031a500d045a440345041840c00540e018050802a1011801c000d4800311100510402404081c000c904490104141c0720f0203404580003000c481d004007010300d0003c0c06100061800304e8a0090121080d840000d030204046601d2080b5074059580c04e040030039000d8814025808150341000c003105407018000181c9460040c0701e0340c3c030a901d0000940e1a11400d01a14600b804843c450b81e0030718000007508a0143d040c4020400e41c0d4618001420900241c0b2007030061802842659100e0340102d00f803070400030700003a040344180c800da440b060030001401156 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 463968920 1250 463967670 463967677
    0x12c010f0303051b010c18061403010302010c0312051302030c090601051b011b0f0e040e1f0f2a030b010207211401050a060b1603200615090c 62
    0x10200300091034200301091040700038190841081390075101515100302c0b200e08440081250f040440e281409170607120110008032002421075041c0703c0780382034124010170928481400000c0c10f00c20103854010626200d0f244440ea0751a2410701007102c0d05140342e02d114030f004c9022040b0b1081c406c100700d00d0355504040759140d02440d4107848440c1081a0304169411100c41000303120450365982a0904000d45140500c1c06a600c01c0e1716443d00034080b00c98000c06080d9030001b0701e400f0f00d0511000c14a00500010190342081c131800d1314445000c4c03010000e0019044501c54021030b5070820b11903034504004041c243c0713441e500310880d036042c10b102c0000c1542603440d040b208c00c0c0941c00085003007141c2c460b00180c0b20030520001c0f6042200070507075918018202c011201c08440345e90b5400401c9940705641c8110b0000e0211040c8032420701407640002c1046101c0741c82c00408001400b040c030303400441c01203003184512245409481381850500e0105441d405c0100c0964403403c41c903004a06000080d2046 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 463970170 1250 463968920 463968929
    0x10528060824030d030504020312030a090212011406040e070b040f0510080106080c070606080f0709200f130803120601140405061b0c0402070302160e0709150201090605012c01 77
    0xa00f06410036403070217900a200040041e6054017584502c12451984d0000031841600d00c4580000c0070f80c401e00500c828140d02f0100c41000741c2c5004060031161004440c2035504c901c00315000f1440420404541d420803c19500c00340010f8000720f000b18a603000f14601000b039481c2940c0c150040d0524150031940000e083c880d25002c9040d003030205074109102c0c40200750b041d01031b00c000318900356504541440e04460541660041d04040b0080c44408218081c03510a1100512400b103404d542c1d44160300640700c0c528025a42e00400904914000b95051032a0000c03c00b002c10f8070740f504e40d4154014140f000c1100c4444c00100552001111032a1450564043c1d502c00344c002414900c20101c42d922400c0016402c5210340718601c190901942c0750b000071315285200358060300310b1012134003214184880381d070041c0751003102250401403140c0d40041d1140440d884440040c4220708000400e90052946500280c110b42c00c00c07001141205408090904c42c00d0b00c00d40555200d10404100b50200c8130a008 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 463971420 1250 463970170 463970173
    0x62407030c050109080304240e030a0c0f170319021e07020d0204150302031b091b070b04081909080c01030c030209040603061e0b030601052806082403 66
    0x80240032a108a51004000c0d20920001858100d00d440312007071a00221821141f05007070107000d45030a41800d400d404000000315082c8000c4280040f22912802400b40220401c4601e00d1031000b030160840c40b5101c1d46400c14403103101d280c012404032a031035004849020b0018a40c07a07119a8244161003242c8445005080c0b40e040784040c0c40720300700d4690060788140c0c5e00076507801c446400742c1d0300c1d44101d001000c6070555200c0341601d0352051500340381c44400302d03410519041c10300310840d445181010740d00180003a207180e5030000700042401d203030041c4407010300340f540c1c2403041008111800000704440c41308014800c2d280c444411085a004c08240100c00740c1c0c0d045002e01c1034855002e5003107084055018140076080c42c45800206040750b00b50fa0040c1c504a40b00d0006244c28501d8040c0305202d49910070061024a8122000c2170380c03424103100307660007002795900c818880540e00c0900a200c0c011155010721090703071244000c05032541920b01004070505112004031002021021003c3c3c49006070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 463972670 1250 463971420 463971427
    0x1608130209060d050f060106090801230105060a02031903020912240705041206020405040c080f07050f0f0c0f060c041404020a05040e070906080a0b010206150123030624 74
    0x1810720102484010f41101d03544075042102c0d80c108400d109244c041d00b000d5903081816031a048419013035031400c400c0b000410303440e5107241d552180745a0b0700c941551b0042c1c0f1455076540407290120301d18800c1d410380c1e81415120b4812600c0c0c040c0c1c140c000746220401160042c0324040340809194481a2a04d25404d8000700908041e00d58402c0c4480d140c0d0000c41070038454102a078030349840c00c0c40080128100e90b555400030702401145083d01c60103614110520700f9020610f49080c8022000724090f246005005010a0581e50407a00c1804c03100e400300c004101a4030f03910420100740d601c0340907440707900c01c5007d0100050a00441441980d007203512041003410340710320b0001408003d43c42400000308000c0200000704582190320b46250051031113540d261030721850100000c2c05281d0260030f0b00d000c076081880c2400f00b031fa400901e05412103034034050183c1031151000160b5000c100320084c440030b1801140c080c1012143d0401440c4507090a4030301c54078544102805481d10f02c5041000340b5001002c1c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 463973920 1250 463972670 463972681
    0xa0b01050d0b150c01140702030c070320060f030a06090506061e070203030403030f0f05192601080d02010518071e0803030c030105180601050d09060b091608130209 72
    0xa4000c9002c440000d00011414840c0300c00e0210540e0000f000d84406031346401120510250050720580e10084510140d81481c0800c1103040e10b80b405403002034907070340e5405110041ca29041c008114151070040580d903451400c007070b02c2d03c01a007040711141c10440c5080000102e161803401064440c14006004600d001c2038414800e0b00c1c01070482c01d0120300e0506100220051724100300400285019171181c140a21006c0c030010041003103031524104014051000b103110200d554913000620269040c0800b02e940b0350400b84804160300b0b10300034080a440800011a01c5010420241502c80c0740e00038484c40ea280c91a10740420f83c040c01c40c8025038007054080101c41c1901b070015444101d05d031200c2c6102da03902d04280c2e1a40c2c0065a081d0702c44a0004010001442e048040d406048066211140c6600d420340002e8498001c030750b418408540c0710240c003000c100d15540000082800200318a03070ba41009407039440d00050105100c004a50000003082e03403100300f0781c801c440c150340c01024010107036581c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 463975170 1250 463973920 463973947
    0x1020a0c120312050c1905040315050a02090a0e1e01080606010e030f0d0e090105010c03171e040503040603060812030c0a030923070b0f0306101106010902040e0a0b0105 74
    0x32207030160b04100e5044500046510b0390301480d40603052105200c1d88038500c5940c084d840300d4a0459038000d00c2001c110400000d10216034801a540310084001241d980c2c142d56007001e03100303032210030740d000288404c08184500f20007103040c01420201d00d6200445850301c4074000c801420b01401d0b4040d4003100000d4500d41c4901081d8912227400740540d0807402000c031500b89001d4501701da00c008109228100501d030300f41400310070700608003460704541c2681a0307200601b80b08210390410721ba07015030074001480c5100f0b462095038280924040c2c6111840d10b405d0058a9030004e00501c00080d0610f40002116500054500850200d144025241d522000d541c0c072a10343c000140b0714149511540c40701d002c0b4941e61910b403401001d09030800020445074180c50304181040e0890b007400d070405c1c08507410451703044082d2a0310400590b10203031043d111090070f40d50741d2450301009000c0d100d80e0001251509140d006003040f66109040000f1544030f000c02001075440540700280003400601403549401c02 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 463976420 1250 463975170 463975199
    0x2070f1101090f0902090f0108060906041a0a09020d0b0a2319060c03021204152006090703051005040317040c0b03010b0901021b01085101020a0c 64
    0x301418481031007a9201c1c3c02900d142016401001078036404207440105080c00c2d210040e0504003440e0540181c03504000081c860440904903c0c01180c2e1540e0090420b0b101000640704194003e02c103404e642d6136000307142c0c06548040310750b6400300d08241c03100c0c4c0c003401c01200600642d84000351f034254605900f4003803400e0051140e80542d02c20300d600907030800c042c4518055405030204d030369414207039101d40c01c000c0e20300295410b05101d0f0440802003000b005442150345c1d10780c90410724007030200d210700035140074029043e0080c8441d07070b0084000384a220030000460000300c80c8240c00740e07a07001341e503011140e00712541200c0c0034011a04800d07000b8011842200c1e00b81d170051044052218464030b4595001803038200b45c226060740d200c00182c2065035a0100450342e07132039140700e403845020002000000d00c544405041342e0003400644c8007920840d031800c00000391082c11320301102903a80c4034907502e0740c04d4000c54a02c103840084489420019510104034020056080050074001900e0100c00420040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 463977670 1250 463976420 463976453
    0x3061409061605041d0a14040c090b04020c0303010909031107030b191d030d18080403020d02060705010c0c02150a0c1b030b1009050609090d0302091507140c010302070f 74
    0x3a003003001041c5540e05200f0400d90305c010318821600741c600040e90200f2103041040c00c0c1104030314070007048001150090140240d81040d54041a90354000d0301150180c003502d000152070340404800802c000c0041d81c0900f038860b0003943c075100d402d0007212402d521a521800090240e0b00540009002c001075042c030401c2480030b024000941885142510380c8404421180c5040d5801c0003076802400c1c1010300800c0306100300c2601c58042c01a10f956410040d100d2888028016902540b1980541da110b009451100303030000001d1015581c60000107106603a07041c0200d100b0b084da5164658004c40b000261100300c2400d49030200d4518050725440310090400044488040c1041004000144400d401c103008059000319a0015424181c035032040d0368000300031030b020390007c408100d200280000d004035080d440d820f0043e994608132021450314410103c2441d81060000f42e00d1040102040c4004600000c800c1a00c02002c50b4a004400740e02c08c1404c003030b1a00305100c8819010a528884826024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 463978920 1250 463977670 463977677
    0x308130f031b051b031b0d020405040f08041d0c09010c0f05030d151d0405063c041a060d02090a020d1515020c1305090c0910030614090616 61
    0x742c9541e6511481c1c07401c103c0741a911075000c030114000b9030604220348111041c042031941c400c90000c0001c54107250064501910031603e81c0e010805000c8801100303104141c00510040c1e649844002d0803c1c00d144103e00406501500300000d98040e02030401c4c1c0c1c2405005a54828084071141c659072850071106034290703068082041640b000c2c800c03d2045100c4641d03074940020945140a0680000f0b400501002d59020610340812001a0021425030f5020701e0048003904510f81e1041c1078110340274080000710810700000d14000c2e01444040c01071b0304c0703184600c1605c01c20a5461880c001413200945031103801c50703006100d42005203084e050781903120441034401800c2603261005402601d5012981076500d20001500b80325001c0f920300c4068903107015000812140220340c0114048820222940013000e40e1007000c201c0518090000ca82400d9006041c0c164a0400448500c440030040c03004441d40e92030510162070114030142c1c198400d4008501820050381c0b0502c1003c3c03452110301645080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 463980170 1250 463978920 463978967
    0x2030415050709080c1906080c0d02130e060f0109090c0201020c19030908030a080106050a1e030506100903050a1415010806010905090f07051c0c030f0308130f03 71
    0x2010301620449100307540726603e0140540c0b070940ea4900b40201038a03a140114208800030031000400c02500d002c4803540e107231805035643e40b050307048914003410f00119801c9000043c040e11001c41841018140d420250300700e4031603110401086030a4684800c52408604219020055441749a2040420031400c0c000035182000360140366041c10b811100c0c0e841c100d650f06080c4000d141c1d014400f0710180031400011071030004400c0000c5c0407008144035080402c04005901081a8421643c507490380003500070450800300103001c040c010b01401c845250040350307100f0744a181c0c030707104000341d004483d0084003900e403041064440c00510b20420a80860620405241e101c003154090b20b12402810740c4400760846505104014055a0780500000d144d58007203103a1010800c00800c10f81c1c1155000c80e4944620818100402004c1c031001101a002c408000800014025066860009580301e903031401c1032541d588280050314103540d24041c1070b485903051104002070003418029010345038108420310 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 463981420 1250 463980170 463980203
    0xc060f04080703050f0c0607050a0813080f0d030c090e0c070501090c0e1f0b0901080403030f0216020306010b160b060402070f08072315130c0f0e0a1e020304 69
    0x341442ea41c0c82140d560307000480c182c6600d2010f00001034108801c0301c1891500b001502c540d41c0d100840c50010384116000502000e00f505002840c4004000ca101038074520410031000c00c0e00c401407041c00601090601c0088101036214100c0e031002da640d0a224103045403a8201c0c01e104581005200700c1c4e0700c1d980c0e01c10083c04940d8003448030000b0656040b0005040c680764000e90200900c0d00301c50b005a001c8090f04bc07154140c0729058072000407080c40c140d409559241800c502400045200d0640d01d840007402e640c2d010b1010354041070860003681101c08599031468851301d60710030000b100401c5240c5442c2100042c41c0c2d5034111380c2168009201605002c560344440d0340304540584100c450203400074000c410004500c0b01031003102c1c1170070b10342147c9811247c11542c69191a441c405030346500280043d0841105021b00440702c4d401c069224402c5485400c10714640b84180101290514175400087c8007a009000e0601600d45500d003648192640c141000069040544102e5040985603000c58 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 463982670 1250 463981420 463981423
    0xc121116080409150501050a0e0409060e0c09010f08030910020a0215030405062809170a050c1b0f010804030e13020316030203040b16050d0203070302090a050f030c060f0408 76
    0x10005004402190703a541c0f4021100d0204c0302d14201130700c01d09030000400c02090b07070890103a401044450815000503c00d040015004040810000744010320b4a0701c90720115200013244404c100c0182d4030100243d88610f011140c0c1003591003020881d40c01001300c0c1b03030070342070003103240c082417002e4011900104001d50024024500104004c02d9101d004010082400001c018007030f003045010011752550540d403400051100001c40039405995161261202088070200407100250b044900003501c1d004841e1008126500c800001c00041c40f0b0361494000515414090314804c0d10010000d10031405c4040c01591000030040054003030092220300842562030b105250281c0704c2d810580160740307107021548803500070076a001c44800c01d17206000b0840010300000303800ea0000383c89000c1560001292008a441e44a4601c4090303c5034000f005014429030550003070064420704035001c0150584400a1048900c1403442d0103516501503414514242400c400501440c10542642d910b413503211003005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 463983920 1250 463982670 463982707
    0xf060e030f0d0f03180c140f090103061406102106090c0e03070605070b0a200c0c0a050607080a0332061504030b07030b01260411040c1211 61
    0xc004a191400c0e103c581940c544204011041445d624402c1455aa12102c40030229800341707030391054584803090141c1d070b12100ca8001401c4001e01842280da16480d10f903020f4000c2c40b81c00c50344d0b03d6200010481c1403074805104a44401c05642d140c13507803001840781c0001440140c2e8004001c6507601000b1488480038015407000317000c01d0b1074075114804002c051601e85600d5520203c01c01074140700941c002540b9007221a0041e030f15240108500030401d214401c070700715800c540b08042d08005080c003810840807402c2c01d8000011160b0130419a0f40e00180541481660001408148200124482e850281e8020f402c01480080224420248050351a01149400c43c00c18480780300002000854a444549a0688420750031070a09162a41d610340342034031005051001850b41301c210109240e40714088117082c0346848501c020089c500302d280180041003d5405481b4640c1400a01071942464000e01d18250001c0d515040c00d0b074048503001d4020a901070340740c0d03400102000503012045040d01c0c40b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 463985170 1250 463983920 463983943
    0x204090903050a091401051c1425051e030a09080c070e010b16140a060203010e04050d111b0102030f0711031e0706031107060903030e0c0105040f060e030f 68
    0x1003e9542c8181c00e00a01214250b6211400c4c1034070440780701c103032070b40e1110540d502810700c0b8400490a15071038102001420303074030990861945101041040083c4000c0c2c0501a04101c008542c51120201300c080351184500b202c00e5882440700c01e0020200d0030584000e41d032200c142d1400044150941c0e880d540b295000c0008012140e0040000340a00c030b42002000f80148071521507107103031210720807000014803074542000d080c1c0207528004540d80001440b170404c015921180855680da19049100340e001d8050f6020b40e41446103041080d4103d0113020242c02e1150001d00525440500e10050003c041c1082c402c18114001440001c0c1c1c0019400058044544184020f8450707845100074186021a00903120140308030385200300c00b00d4140802d008040c0d038280d260110b41014410000c0071107109400c00184841e191490003406c1c141d050303010340700340014032064a04002d160001122640120700541500070079a980800a0714000c4040002000c0e002d4251046040c141c07100381d0815080805 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 463986420 1250 463985170 463985177
    0x503120c03060f03010905071a0f0324030109020a03080309070b0d020a450518010504060504110906070614040309080d1e0e04061203021509010608030d0c030204090903 74
    0x1846698945902c0d1081c03046400e80003045155000e071103a940e102390900c00c3d024002071443d0104010340d0440101e4800040f041500c40d60f030f00302540721000160144034440c10074020711a200140d0715040c041c8080e10303a0001d008907640d50450711340998550026108091034400e100000903200307000e4001d4102408102001a03d030b002414001c0c241c100c40310603c204602801c403511111650801c0014084580c01c04110401b46103c1e0101d17485a40c2e072741101d64001c10407002902071010040369941030710030550b4180700300d036903560900007600e07206821608035074824401d094003424103034094010030740034050200d03160709164400c10300708800740c4060700002d60310802800516010005094151294a040d400001c3e5070808841190345902190040101d048078002465446410050182520111001c1a0401d51602942d26205108180484408000098484001880b9440403150000043c1d0324001c0c4c030005074401440c8080c14402407541c01d200124120032207200e99009207201c0d0308d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 463987670 1250 463986420 463986427
    0x3040f0308281706040b06120405011a030a020603090a0b19050105010e1e180a14010b0a0f0818120403110f0109053007051203040b0a0c0503120c 64
    0x101542072034081c0e4a1000c020b0703400001d2020030294400701038402031a01c0114032415031070b13800018014080c0c40d4411580b280012030b44115411000560070700983c1f15500070015407159880010001e000b83d8150360781a0054010750340903080140045a2102c0300d0000d86528403444c8d42c2ea0400e5840503142e036103035111902d5103ca04548240b2074103000d0074090038070382048802c89000a581100281480c1507452100f06101c145481b4826505d0000c1500611071101e46000c60240000342000000c1ca0010041c101c00008d1140c1c0c250115248424155980014110075100030f8608090140000c0c0c03031a95040c84901c0c5c0360506004071078802a1010b40c05680764518200036403490418111188105001421000280c2c0c220320610121403055541181900c041a80064240d19410507030032048444c0c1080c20301050045001d42c02d50320f0440d62010880e5074040f61035680d000314011000d40f9201044845007283c05440f41500c0c0b244101e007160314042015808000b015010346900c0d0100c01c0c0030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 463988920 1250 463987670 463987687
    0xe0406060e0a090203010b090f010c0b0c0a0e09101502101103010f06110a0b060f040609050709080f0c010e0604030213060e0a0903091203022a04050a02042603040f0308 74
    0x90300c2c9100241100d080c25403c5506240d4244603038070442104c20f114032407040c07400303100341d004080c0404000d41092402000345051455103d041c0d003c01d2101e40001c01000121100b450300d0300d01240607d45081c0d0341850b041c02e0081204010081c40040360030340c401c50300c14920510090290b40d0060021a103c2030700c82d403501012107a8885250080d609000c4c410a20301c00c041800141240710039001b960700e0107151150408178030107401aa03031054000d81400808500e4142da9005603014060f29a0f0340c8458030b07030b1090416101da40c03444804003540c00800400d10107602c00d8444440c15400107003002e140c10303525400260050340b1a141000740c2901c48504201e450780b81c03209240e00c007100341d0051145411036940105044a0360003400010307105550200140f501c00c21165440300c500740c40c0040103002100a01b00c0603214002824402e0b0304010024803858801c0c000e4808035000407112215507407114095035407181040000503403900c41800000b8018039000b09040056009494041e40d8a028 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 463990170 1250 463988920 463988929
    0x5030d050f01031e02010504092a02150a05040503040e0a0c0905060f040605160b071e020a11010503060316091a0f03030702011b0b0a0e1b0108160e0406060e 69
    0xc0403804812907000040000c1500d100054000d400c0b00c40081d10801c210744010b0741c0e1405590080d0801918003e402e1281580c0e980d40c1c20700201145111804807038112400b2650f03015100848010b006100b4085072120300140c024a421600c10300a43c0c0c1802c0c2c0f640146488598100d44c0d030a222a210140701c0407181d04040303040060070003540e00901d881610150f903c514450743c8a214100480051030329416003034070740d44400e81c80e4001400301460800f90302c0108200c2d8003881454050039a030b03070030741c0074075000040707003001c1e240e00030355840c04503500c40010f440319000207010035014025a070f070010104096411150180244a01c0000c190031024106111843c400450034045c00644c0c0d44445250b40000542d5011340d8240b03420b004c4052003018031600191004002003015000005200c3e0340107468100c1d0001403146000c98002c6451040d20341010345400c0e40590202d0300703100100308000d00c990a0003c045456050020b0200303d8003001c00d04482c19544202c00240e1119404891840c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 463991420 1250 463990170 463990181
    0x3061806031a0c04061103070203031303030212130e04030e03070905090d1409090403020a060501121502035a07090e0112021201020a170603071a0d1805030d 69
    0x42d410410356807810101081c0144a240241c20500410500c812460242041103920103a401350540340c41d01c503103041d241502c09441c00228054001d08420841740350009069072006005503001200003443d007411000c103408058010780801c00e003040419804e4908015100040040c102d0001d15458180c0b0050b09045050080400700b1140c50680e03032018040c5010f0700ca5142e01212149501d032140d1070203070b1810050600041001d8201000000c040b2032840c4029040e0380144003103855981d0748074410040307100843e0412105024a050300c080b41c1c46c441c101c0c403a030b00c0d1407564010707541c030340c1e50045040c0c7c81d01c1900b012825a01141606001c0c0850b640c0c8070741008070b608004c0c00043c1032010307645842005028082e5007c4160003c03200390368902e01c280c01d403420404021595031a0b0268020402d1202004240d640320381ca602041c0a400d002466a0413904203006814008410100d013002c80d0b480500d81c4c2c0ca0042e151401e40000c081d40c01070071403000348208000c41e526202d21005105417103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 463992670 1250 463991420 463991453
    0x40507061407051b0a030f030e040c05090303030f150a090f0e0606030d050a090b181f0c030e03030903031917041101051b070f0806010b03060105190306180603 70
    0x36818802d100010744000750b038035149000c4081000c503e803c00400300b0f40090042e800036001c24120141c2c4d60034190804c8000e00802c009640502c507100b03d69000707440e90f1040c2340b0100d070140e0080001880b0458400201500036040c070007090b20018014000400c40386481d00720b84440342d6505169400d4410038800d101d510309801014107035902e00100066150030b00085240c090100000750b80035260f10039141d00000d09840c1d600c2c0c0361a101451400e2448a0283d10058080c1c280d0f00d01c030b82120003101d030417800c0d81e002640e0303510002d152035941103d4060310300780f070716403d444140000200b0740e5045c07002e09050030b02c85c101038001d9103103140c00400e05000103a0f01a030a504100510012a04242c080c07900031900b030801a41d034402640d0b00307684000c000840003800d402110000f05511068440351000c661618045400070f1342c80c2c0780400400c5c441520106e0110f5002c02c4140715102d1101030303d01c4c0102c0c07141070000c2d0055942d2034107640800d030b419034080c403a0f1f90b4000500800c01c02c80f600e0308220 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 463993920 1250 463992670 463992707
    0x61b14010608160e061e0613030506250e0f03070b0702091303092d06020c1207180b060412080712110a0204180c0803030a11031b030a0b040504050706 66
    0x1503180200e400404000a000c00d4080d040007440e201051b005085d00800510f4044c140950b1030280da07582010031304590200311910700641c8042000c860001030310b2540b10b07610000e58900b810052000b030703598040401c010b58000d0900595000309980c14000c0c03100034004001343d0390796944103104100740303d80f000b07040c0500d0081580001010a511411650a6404088001810f426404d101c24040001c481c0034211039035004001044082e408a60b40f400c501d025180002803041500545807180d4050142c40301220510300c45400f4a40ca58100b039060140190440389010740324081000002c200000c19641e1120005885003000401404404540d0052820322005002c18641d00d481d10100d810183c0f0a42d03c07800300004180c21015100710a66001c0d011001b025036400f0140c0d1640c00c02c41e00360300020b03d405c4c0700c000520b840c0320450b441b48141402c030148441003943c0780c25454001402c00c10b980b42c2d446804032859292433184038002da02038402481c0c0c1c0c515105c0014900d003803041119688 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 463995170 1250 463993920 463993963
    0xa020408162102010e04050403020a05060a02040528030b09010e0d0e0d03030f0e1b03010e0105040305030a05090c0409113f010b090708042a061b14010608 68
    0x503490765181160b080c140c0300078032925001d07400122190341131118415401450300017880200b40e000140446060302c0b510a80305240c0d1401c24090480c0903078800c868100500e1009034405014078203070440c42c0c21064451410203a01c9866020701410102e4004030070380c0d540e00c1d1210310458100542c1c107080041d8900724681c8100700020a2103155401e0b40141410380380c80740d1600380d40e01c2d40c008031201805e0360308850076100300c03552840e000c4400b0400c0b10301a5103400b003101c20f0450180203075481030340c15481d180c0c0741d500c070303080362a00600004250004902545088101a68a0303000d00d40300680250302806d800f00d001c5041201002c01e0790341800202d501c03100b483d80501a11303903023810904514071400400010401c0c0c414090880b0008040d4003028070020024425003040009014900607950140c01400800d9899901003454900300103200701c0560402080e40f1400d8012610400031010000d600042e07502e02013042000c10704501940d44501c0140b001500030014001e4803500001d0034a00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 463996420 1250 463995170 463995179
    0x1106010506031017070302130b040f0501030c0b07030e0907120c0f231201300b13061d0601090c03020711040c09181b051920060a02040816 61
    0x215980300b4030480c0e20044d0150100c42e51400107102907402550080d050039094540c211041004208544103144500d01d050b00e100070b440c3d400e104031030507039a0010000c4501810007440314240c3d00052012403c1212502c94080309448030101540030b45010344038030118820071040ca50a40d4800207089041003410f05a0000003079000301915076880c0d82d20f0b04009482c841c410031040500c2846002155045403100001e10508880c10140e203646281c80300c0c014103042d508040100368031205000d040714a40402086001140402481e5990f01c01c0c8000141c000035450101030204c64408003928541260340104046400360042c055174040d42d190851038030b5001d41e101218241c226030620300035940c82842003001402200b650010b85603900d5222032041700500c0c500054880020044403e0781d2885540a00c940554180c2d03400c00c41e02e10314100c180340025022150f00c41e8500c00c2c000c804020000c40342501105100c4103006204510000d42d442e81020006803410240404003070b03054650140410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 463997670 1250 463996420 463996441
    0x9050f010807080f070201021e03060f03120409050c0702042a030905070b030907081c030c1d090a02091003050a0614060a0305072f070e09030d020706020c0d110601050603 75
    0x4d81c80200010400c0aa4517101800c0b80240519804464802c4040000304804100381c130103544111030031118030801da980303881803503107590300c041041e11100020301060201c2c503610b400483d8081c0e884148141420110b8000030140d03484144a10004214624014800130040025860000c001c1c14244440001550b807a541c43c80b0034411080846804808600d1600080c0000001820701004030b81a1f2455000c2e4801e42d0046490b0680110740b90030312140c2001e00a803040d0301c6411b420f058422540380b01e001801003004e80100380360140c3d94204014103080c1d4072040c11102c0c00d901664006258908121007a046070390942045010244011146920303035101021103030038012610b4081180e4070351000542d01500088440700010b03036081d214030b0f010032a903441d40d02c444d03848004640486a0780c485030958900b00b0341d400c101d15001005034071b80d118080c1d001020480e100340300c01841d1080d1001214240002030301807400041e22074000600c5010204461400342c101241c1861840c00e1144501 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 463998920 1250 463997670 463997687
    0xc0a06050f07090f2709020910061e050715062601060b07110112090807030f1e0f0311090d0b0117010b0306010303081915080d030605060703050906040f0609050f010807 74
    0x80c0c0c0c039840603a400c4036001c1c845400c030104240d4040c00362340f11828071507503030000240c1c54010000002c00d8030f101121004140b022601c8050b0300f80d161a845c08059172130705415040f1518a205040d5285c00c0001080d07404414812071804100440411007007003195039600b034844c2584103030281d80c003d100d800d0106c1c481d0398180d000d00c0024240380812092510050307001d02080302d009080d01700c021400c030b0203050300000c3d164903058540d55801c08a5083c2c04e110814018244010b030001007040d030b03800c0f4960b4020344c0310800c2c281e501c56041d0700340005400000c3d01401c1d032000071903600308518010031442c0c01c5aa110058010761340b00900c0341e01080b60102e40c0d40c2c24140b002508110b0098085411000349074045a0702900000c002d000070740030810080f1000500d8441d8075079900c21a4400c01c41c00f8840e101e91020b44100400c1640703000c0041e14112410f400440600c1d034440010040003a04100d02140700c40240204d8507121a4145803108002c0c0c5444481c60080c140b001e0401000329030350f44480071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 464000170 1250 463998920 463998959
    0x140706020d1e0e240d0609090323131403060f070c020f0f030307050c0915090f0711100605010f050c100e0336030a1203020c0a06050f07090f 62
    0xa50300e8a5480002c42c4206072080034100000c00e03104021040d1030400081551840001e0280306e829581c0140008039908440c019001420b90948014120790110841040d8101844401c0c104840c0c5070f240f20b05051071b58041600a0402071505605d414140003066100540d602030a04138900120040c11030720000c08009d00c52858200070741030960714003058000171039019007242c1c0c0b9442c1c10f02d846aa80c1e080c00d07d5107486840c42c040020009010060541120600a070100c50f4070744450610520780c110190140e07007840344210400e404a00200604004000c0300d09012580f103291100140c12600b65061030002c00c00d0420030411240000615000004104040004c041003400341b590f0039406100b08002400c082c6408410b10388501c5007500401e00890145500415020010135684031101d820051048110800f0040e649000364081d1000982420a64159150558a0350f04940088484940000d1104117201200380d02000c24000350075000a0316020605018005c4c2400c4600340710b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 464001420 1250 464000170 464000177
    0x20307121e020d0905120a020d0302090409080307020d270b0901120e0717011506081003060f02190311180402190801150201060311120109140706020d1e 67
    0x2488a0a00c0100d03807010085034604011500c4110005030b48000c1c2c04241002d84140c404c0d0303810038002c03c811908480c000040d40e001481d0041c0c011406801079040a080325034401d50b20022300c030119006100071841408141c0c003901c46015a00009130031400c0307200c220700e4810801e079009a12100c0e810114815100d40c141850707201c1c170322800100c480204c03c8040386440b5060540720031340703598006401c9068400703642d24280d481d035880b100142200c0c1d03944003064400e07010000030002c480c0266946a0400f2440c6040305003103031282c03a05004d80d81c900403100502c07036000941e080240c4072100103240a8901d17240c103000e02810021a07100c9030140b02c0c82c0300701890760404045490340d40c1d80c0c11101d80460940c03070040c0d040d0000354050140304091198840c0021000302e81304900f44103100f80030999a01c229800c019000320000d100c0344290085609030301d99641c02e05100894a234040752a01103041d00001d00605080040003401e1074902007090302409840e148080c80d55600c02c211040083c1e240c075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 464002670 1250 464001420 464001431
    0x7021804080d0e10090c0501110c0f150d230601080601120e190b06040b010c0f03200f0a030f02071809050309060c011413050303060f0316121502030712 67
    0x510090130a41410760111060b86016003141c10054500340910441e20262190100c0c5c2e20094141034480c50612402c59008200e448071b1162490648003101170301c0c1070340e051030741070282650300312044903e070717651007a00c1040c07040f824400620210b02440e8042020710304050b540c1011000605030740c400d010003160781a240c1c401c2c00368001d400c01007440c4401c1c00c2111480c44030300e03500701a200c511054802c580900d060140c80c2c64594001c0030110390160303112003000b0480b1440c0c2c50803039000300c0324a1054958000c80c81480c1050004024031991041d149000d80102c01180c500034201c1d0018041400035500002d60410281001800b44144400309110104603928503140203070941c400c10200340c2c1d0001c00410080a140c0b81540310070142e520340c03c40300c00c01d600d80c0249c2d5030000c0e02841c00202a13034000c100044081c14040c400c0001101d004d01280d1200c0304a0b010144a40e2203a00000d9a010080c60001c0507c007141200310403c60841d641186103007030851000300f9210361010824081520350 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 464003920 1250 464002670 464002691
    0xe030d05070f0624030303090b06040c050a05090303040506121603050c07020d0c0306140709080318010c0606050a090905010f060e160c051509010c0314010504090c03120507021804080d 81
    0x103407030701c214184140c100c0b140d131280c40b072038090700501d010b910640f0702c400342c2d10004003103081c60300ca0039040c5100b81d120182081040201100c031588500c3d0010b070140402d120024054035208050500325a80026070f0b0251b01d8020840c14030349820300c84801c100350a010901c40c0c2000044110b615050b0152107400d00042e45040c40d20240c8915803001317002514146004008005d0003c089001c1c1c07600d41d444428040d5544041c59482c0034000020340c100300c09500c09001907000701d00d00c3c1c1640d8445c00000c01d81990710b10014094900d07030382c015070b540c54a035400501080390a01c100d40000c0c0d000c10040200c40d0403c1580b0310301070700c0141002d00414680841c03450301d82c0540111100181d1010031503500200c072a0301c901c0103da05850110003903091540c4421864080c0c0a1000343f440f6580311003001340c2ca004200700162900207410b6401445089000c800b0a4440503030600c0c1c29100e888290b0f0300c1c11035105111030034608080d54640e0a04c1507081c44002503082040380c4038074504920214924125 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 464005170 1250 464003920 464003951
    0xf2d04060b03070305070801080607141c110a030b0a23010c06091a060607170a12020f030103031e05180f0d05100e030c060c0f040b0304030e030d05070f06 68
    0x36421000d01160702000f04922968035401a81c4121166074030b03d4451f90b80c58401d40d81c1c43c00c05480800119946140d180c9000d611403018180c4000400007a04c2c1d02c0d91214100740864500744505603070302c0f0000942003211a0140242090514184c40460209282c4146280001503420400200b13041080781815181e11a0011803045074104078200b103080d040d89459040c101e03440342d9007000c008640c40054403516255080e240343e42e03007007249100c40003848600c08a02d5800851281e0901230080030b01c255410031840602403482c035540c175107541ca50660034050900042000310340508488441c8900c04079034440305a6002403410030300d0104c015070410000703d03192a070306c510310703042404503944000f0700c480021070b40740b60300c94106c04210700d211451131a5128400d200c000080d9a22105c0402c51140300080241045000045250b041640707403103059035580d000f500c050340081c84581030003503c0c0c602800000481002400c2180c40c1982c90f0740d81458624064001514250742c400c0b20700044082c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 464006420 1250 464005170 464005181
    0x4031404080304050901050609090402091803040308121302130917030c1206120c0d06091a180316020111010902120109060e0d020a120e0604030c03020f2d04 69
    0x24218a9115521028156503a820510030540300340b031903800000d5a0300700102107469400b0090f0000103141d540c2d40902c200070401401d0041e05140c001c0040502c503500f03001600c0514850f601156079401240d0702c168800801030150205805c01080320001640ca011551030100034500010400000707900f814040d01160b5003044100390707000401c00c449000910000c12411031044a000110384500061000345030307910200c0c075010f51042600f01d0302c5203482e03100300904900c10302c000b144020090703842580c0324801510806612441a051040c203c035201581d00d16500e60703000031810442e4245030024000700d280c50103414882048816100c1c014290442c1342d51580242800c1202401030061900030141248140d58032898409188810314010070b40c1c02d034400255004041018085d01c1c1c00001d2030100d01c1e0841808801d08190900c0d807240710241000394020390140d40980d1450041c081c2d00d60406408600c5480c108049409140485030010550540d108491041505010100d0000c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 464007670 1250 464006420 464006447
    0x606060a2d08040629040209060d060306090302190b0a0e030d052a0408070b0906120c03070305070302120103080a0905040f090210021207020409020a0509071107051509090403 77
    0x50410111140c80d00200b000d4003aa2007088100008581c5040e41c401094400f0200707054444c1c0b40704510700e50b1610360043c114804004001c1071604405c1070901048822a5104070303070441e1210004024580c0600003803080010441409090076415564002107500c0204420750700e943d900e242002c10902013040d100344101e040c200f0846810608415082808001000d030f002954400010300c07610307410b03c19141192111070043c0f0f422402d005024035903400036024140c00c4841400194000200098040c2c0a5114100403d9032030a0152004050751401000b000616004028401c1c1040114584a0469400c144084e84590150000f19055411640190381c02030421304408010850750b44003a1009108a41d044400c50404100342d8075041c0c060542c03040c3c46003c0c0502c00241c03d1079007102d5000e0344005c100391145a100c1c0c0008822010550306000000c0c010501c010680000300425805403008540200c641300f0782d10a603e82d0740c42402e0f00a4021003000c07010404050045288400a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 464008920 1250 464007670 464007737
    0x10c02281a10050a1403060f060103140c04030210030501050d1401020f0c0601052b1113060303081008010605211606180e01030804170c04050a0212090606060a 70
    0x2e04002003001c049407081d00481e80b08244a03900000c0942000b51010100070003e00904043d0ba140012001c0c0150014501c5040c07540741c10345221501c282d19030440c480d41c140d0007400c0d103c1d41540144042800550030010a052800005000c1c0b130307940d035214070038036a40018400030007200800c0090283c058071040d000d10040104110988500104a00f41a1030060f51a4018038bd071100300c125001c007190001013480c01014221102180b4405240358182001500c1a00c4108408511100300c40450340240d0004103070b1000c0c02240914000305100412220000340311041c10200000d8045021002e40c4800981c0c0324408035a0903000d02c840750300c049030b8500410820f9a64840034100e200c2001540e4280b2886040c003041c0d001c0c108860741e050346e40203481d241c1064100303604551250300c282484010791241007940d0501d03598901801707104d034900d0a00540c440401000c904680714003d03150603015003061042010310f4aa8400b9941c03010308a10381a80c038400500481242007510070115581c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 464010170 1250 464008920 464008973
    0x5060906071109090d23090603040609050d170906040b19090605010e0610020f0a030f0c020a06110f0615040510031202060f0919030503100b0714010c0228 68
    0x900850314401c5ea40c002d13165000401c11807446500b48015001780c030b10031400148186005400c000c40075561140c4116070010b00704171326440d60b40c54608805020000910311518981100600e4030a0542054045c4002c0030181019903507008100001020030440200b00e0070400310341205500428070040e04008100919615000c2c1d00003a5202141c0042c081c80000495401c082c0c03000840c10f000b50408030140c886500259000c462100c11b4441003c00c10036007184160142c0c2d10903413918010501a02d45a80407481c42c14802d0a162036501507040f2500036200b00001111402880e0401000403500015a82d0320f80c1100103110a0070b42014040d42c5446108128003900010040d006201040081503295200c0c952580c0d1800c454512080011686100c000003e0107017000d1070700940c1c0060243d5140d62a0a8205900c2c3c1203200c05031a9040314603501307612407d007845080d20344002c6102520401042040040502c0303e5202822100044002401c05000b080c0220150404010b001d4117074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 464011420 1250 464010170 464010181
    0x2090a0f1202030f19110d060f0e07120201022d070b0a0e0d0816051903051905040e01030b0a1805010b03060114210c03010915140105060906071109 65
    0x54110700303010490091165809001c11000001a10b000700c00c1c640e04d0700003402050b59903101c620200301c00d103e80c000d0141a40440010b0b12800b480180007010000051050fa00040d81440c00c481903001a40800c03906405901503640410718440541c00304081d4540900320888041c3d00503419503402105015210340454240078200090211000d55600c0380840402035080040703120035660000d100c034004200c0c55460709640a95400c0040c0520305aa03803590120900e0b413000d41040780e01714006040011402000310000c100c0b03d040c8074103841c3c02400d0605100f50001450010301010301510110310010381802400e800102c490190f1480e000e51030320080c078006020303102d101e5500b4482c0c082c61002060801000c0d0400d41040b01c000d0403150b034012111100204180f00519800950140407400009610240542c12020703105586a4610405c54444502107030395001c54402c40f140c0c0100100410ba403250107032400200100c600c680e6400e04e520380302165103060309186400200c2c6408002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 464012670 1250 464011420 464011439
    0x150504050307030305061f0807020114010f0806011e0302120307060f020309010e1c0302130803040303090f0b09030a17090a0b04060e0d0f060902011103070b180a0302060a02090a0f 79
    0x1d58503102c0d80f400d000b240c03101402c11004844070034010007107c5800c1038144c901842046025001045800000b0f080a1015290820f41c0030982000d103807628101e100304211241005103600500c5100b965107162a10a442d000d030851980c032020b4401d4907140201c2d40c0951040c41124843c2e80e20020400c0502e03580111038010b0341086400d105123500c1c110142c10070300404600008850764207a10345100d01221f410650094011706010355181d8100b0002007a036070000c20003032021710b00075110070042c60300d824490b09207000590807411510005010141440c3c4001402d030b070300a0b83c17100507102c0e4142125200c2e1814000c0b060308035400308600700005955029000240262000c680d0380c500041001014000c116114030b00c0203040a01f140001000f080c640d90000501500c1450100403805040541070b1031031300711000549440c506c0b90180100d00d8642140d00b1000035a03200500314920140c0c0b0301039104c9600408054402d1340001d0810415665142d4120203001c23021441440d241e10707034041c0d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 464013920 1250 464012670 464012677
    0x30307020c011e0e151b030304050c0d080a050a050d02070c050a06030209011d010c142b05032701020a03050405010b010e031b030102210613051b071505040503 70
    0xd000c51045980c80030000c02c0401c3c4110502c9054a030300500e09084024410f014400c291450100001403101c0380d401c0c0394800442d020215054019a00c17804e041c1000350410291280240c403c00030540c000d0009420942581d01070801c6003080d68941014030002d4480380303e402c0c1503440e5948002895420040f0007035401054800c01e84140c01e8450310742c80250100d109400006d8085000d11201101c00c0340d407100c2240c203000381803429038031807010b554030a0442c4046100e402c2a075005200720134191340011040c43d401e9501082000c1c0e5210450001816034400a04003451040103507003042c001080b10104140c000b40710900031541da54100d08000c004000c19907080f5070035424608080401c1d8401c80566417642001009464498040d142c04880d528441209541554007404207105010707400405612103031186529440c0f9142180070040c0021403100c00460241c03600c018080c0a0041d42c2202c1c1d03100180b99842580c410b86810100380d40c4981c1e54550040c2030803d0100006c204c40403001c0d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 464015170 1250 464013920 464013943
    0x5031f030506040501361e0803190204121b0e0702030417070605040e092802030d02010e03180d0210020c101d040906090b07021e060609070503041403030702 69
    0xc1200c041b0100d540780480644001c4890b0000094140300034544141a820354405e11800c00202d111240e00d0715402d070366807202d100f0b9490200110401c0413085c0b5040c60503003c80301060341145018104904281c000001d010040c2c5246000505503203e1440c140c0c095010f408180910402403911441c004d590313038407901031302c1c06004000c0d4020030300c136000051b04001d035205500c1c0e05003414100003041112503c004d1a201c80f0340700303090013080c042840070b04508052005000460310002c09006040c60100c6071011070046a160121603510000003100380c940d8156005055460705140b07000044010800d18400303584101201040782c10540c00003650340c4102e00c2030710003003101401c444064810700c6003050842c001000d4038280000d549000c3e88980002c40c4190400a2066a181c0354500c9012003200c000d80541e11603909880300240c50100180c000340e50070002c001916180c00424640603000c1c101005202e404404a02007103040001c515400f071001049984074684454020340d0b0b1942c01c80d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 464016420 1250 464015170 464015173
    0x5060c030603070608010b0403060e1e100605240f04050303120a060510020a170d0f0b01090b07020a030f05010b030d03050601090e04330f0b040f180305031f0305060405 74
    0x600080850090705c105040760000c42d2141e051a24646417079010f0442c0842110841c081c0702a2801c0d824000c11103501489a480010100312042c08a040c04039031a540202d031150440300c181000e40002d0113034172100880041c50240c0c50304907070100f03140c0600407600480d030300d808046803c04101100100c0140f150758405000c1c050150b848050012004980c0c0c0100d0040e0080c507042c40110780081088560282041406403a0000440807a811911080c0031102c64903203900c2907011640c1e1000c0c03420702801c0e0380030015151008a900089043c00309201c010120110a0404001d0140c03c3d1f100e07000a06019003604c14401074142e0040050004403a81804a15400c074045080d05143c4501841031364010091003c440c602020040c682d500c222a540c5003d900d040907640a5003075015100351501940030100d662002d1703004100540d00d4120750345c64210701e03001c0200000002007510021503a05400e04650340c0c1c40c2d401914201081c51214a0418000c2c2100007041150004807944610b002d0030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 464017670 1250 464016420 464016433
    0x1e02070303020c0114010303020307030f0e090c190f09051e180115020303070e01031808040605120c2515060b030a0e210d0e0d02070f0e01052b05060c030603 69
    0x5040c0f45c55203400780400b5006074401d112103400079000301880044482c090078150201c404403c002200c0a000311015100c0c2040031607075110002c5614051007140307205091035007190408140040080c50070344266441b580404001d4078030411245d003c42c1a240000e460450207000a00c2403c0c06a0400c1c803840359000640d50010540603c08020b407401454296211111001c403140110050301c0707071000010400f102c1402d103100240e202d0b0001c00c001c21242e20781580b00e1900c01076000d103c44005140c069215002c101c260040c0035030342075040080800c2d5040c4107040403107083c070000e040880f000300d86426140200208540c030031080036603c140c04a04080c0811000c10380000c1e25040030141c0c842c408003150040a50504240300035060521005400050301502110f03880d107089002404c200160300282c5050140c41290226a4007414140e1100341441d49800045102a0100c0c1c228500c5ca9031004001c1090b0340329034880c1c41d40c45030460201c41c80360a080329800c0c86507100b81c0744280711384540c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 464018920 1250 464017670 464017691
    0x130e070306090218011d09010b1f02070803040807030605180a2105161401090602030412080c07080306061b0a0606050906030a02060913090212061608090a03031e02070303020c01 78
    0x189041e07452041c40010741d0440621b0340b0910f180050940c54042d500c0e40700b40c480d29110314001c2c00840503500c1d04c8694510720901c0103410034000b900850000d0708100418401e4000c0040c110040b0b030b6010400113815600e0400c107440000c4690555003c9002c2c40401c0014400b061406002c44200c20b1300400300c0245021098825204440300300f005004045c65880110300c220b2400b0300510340b260b0010805d02040d581d41c60072030784101c84c1103501c3c001e540c00300e0700c946501580351a44020000703501450104c080d103600c0218000140f285101c0d04000441e0030a2207128140b01c041c2200c1501103401061452511030080c0095000301c82c0075508000000e07130140340000d00074407502e0300901003e2400032201c050280c80140c03149070441c0f03d900c1e02101401a04c64a04480700008080b0107040c2e28142542c800100081e040828010850400c0c140068450041510441c0381e9040c20000b890445e0400100400b003504c0b000132110318070100d00740d824113405800038808078030094001c00210855 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 464020170 1250 464018920 464018959
    0x506010804050a0b0402130906090b091f09030e060d0f0509301b0a17030f13020103090c0b130b0c030f030a0b212a130e0703060902 58
    0x46802808550203c200b070004143d000302c0c800e4210340007400044580751000e03001020f480005000303c0d90142c0d640388407407d2180c024152500b04a07403402038412020000ca1643d6400c40401a4000403959040e2000030580030314900303800b124000c0e0149407140014440b1000414a40c44c4141407581401d001680324500424010046071241c50300b8010344c0c101285451000100f0f81d508070800c0700400c8202d12004c46041800d503469034410013040b0030241860a0f90b41c480d00b141e07801101035803d0003031084003211b210502c0d0b44403940c2e03441c02c207101090340012000343c81c81110142148000c00c80c003080d2081580300500c018108501d5000d04180c1d188400da0780780c42000c2000819420030320404410700e00c0c0c0802560030220b194008105130b4005800107a214494503150b60000c04802451044a0780906c00c04015180c41c1a061014844d2148202d1220700d0344e0f58864814034440420072003c0000c1c0c0d2050350400c02447c202c84141e91240b401c0c00c0245080082a07203c0c4880340803000203c000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 464021420 1250 464020170 464020187
    0x90603070e0d08220b0406030f09050307060b031204050a0506160605010303030c09060c080301120c170309040b10120e0a050a0c06080c030c0f070c0b071b050301060b0708160507090f050601 83
    0x7404405d441c60310346400310840041c111140d9542c803082d110011030700881d204202600402c9d010b1000010944d0101c8101441c0a000c00e500da100d40001740420044c1c0c1c0c4d108101641201c000340c6209036a030300c0e10301c20240d400400d0030303000381a07a14201c00482030581c10303030180351005140d0f111303240c18907120701084d144402c03281d000415041081005003d8081000010600c042c811020100301d5515110080c1e01e054012490050560020640c00c030301d45002c1c02580318049095405442001190304020650744c0001c440b844101c0d00d40030401c040d450100301860303119801c403003611a94001d514000709801c0d024403490000540382c40216004582943c100d900850003160305502d815030380a00c0c1e0790036400181040d100340007408000662920706a004100c0c21f4400d074401a05400d4210f141d074040000f0fa040303140640e2400d0402c0c45a09425412950800c1d0400c25460326151040c6180400c2c1400c05030007003d50003031810014840c02a0380008407a0159010244020381c0c0c1c260044079400d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 464022670 1250 464021420 464021429
    0xc060806030f0a172a01050604021603030504031e020109060b01090806073005040203150c040501050c0c040e0607030b01031a0105031023010e1005090603070e0d0822 73
    0x800c08141000028103404c05244401e805440d1075007020140803159084412140c1c41c100026007140c07003a05151428410389a100f10704481c110704102c2a0000b0704034a0881d00f8000b0103240d0390300b001c603017030600450300b0121846030b03119001c0890801d880024064100e00004494050804c02c00c0d042c258010144101a80c4c03991000f000c0664070150111400e141c4029a8846148030b0340070b0120040124400b545415201d100c04241d0703003480e10600d032030b10800909036201840703100b044c850310f0801103048500b1640d091a0041c1c0725043c1d651260b080c00b10300b83c812580586801c0002e844080b011500a108504a440402c5152128030066050341c1c408240c0108244010347c44680e40d41c042c0003d183c00131140c003071551001d41c4610350b400000107190082800303015040185040d56074041030b00d201e15042650500840455003801400d2070003110180e40c461a4040002003060b8803c00c080c0040d240000d14a100b000000d081c500b141d61703c001101c1c0d03c0c17141c01001018a241c06d161101048a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 464023920 1250 464022670 464022673
    0x6211302030a030c0f0c06030e15040b18120a020c12030c07030602070305370e0a090b061c15050301090b071b0b04140d08011805041a040c060806030f 66
    0x282c0c40da640895103283c03c220225404550058040041507400c408607001e8007a5807000214020751141242c54814440c41ca0100a2003c0041200041758950865040076081900c5007040d0b8050441a04000300c091443d40b0424000c1003c40940740d001070031102c608829121400301800c0444629200c1c802d07040d108007541e0000f101000080c50035401090f82c0c81c02072130400d060030340b0341100b4820030f507a03048060100341052a8803c030060450304440c0e04101607041483e580c100f10700214000c2c81c490710079140d030240c0d24101c10b040c2e030b151981110001104242c054203458001400c2d040104490641001c1c080c04651000c901c0d410144036584d141500106810340c0c5a690510884030341c034070030070f085090812800c0e200d000a0031307e14400b40998840c501504210074580c002d2807801040441c42010490300d440104008030108551102005210001107241c0e41e1b1418881400e07520b09000c021200c428104000a00145541020075a50b86982c1d001c0903850312000c16640341c0080c0700c3c0c00000e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 464025170 1250 464023920 464023933
    0x405151305070e0606041805010801150e060904050f10051f0501021e01230f150a0b030705040f1502010e06010f05090a0b0d0b0a0501050108040b0c0c010b0621130203 73
    0x41584030710560b408130780101800c2c0b41a450b4030b040100e03a02c2c0304091030050741c1c90b50014080c40e1028080c003241c40c02e4070303001c00c3c44d00b514140d541e0340d4a103005880c0754019002c00340410288081446550300ca10400d0301103542070383c1100c1c071040c010f1404441c0070400c1402c51200e502ea02c00c4000e20141104d10580c0101142201182c29400750400034504094642d03075801501000c0711003500000d20284c8610107500c240c0390480c0c0074892400002c0c0700c14090354442c81502280e689203400c2100341c0d558502c0c00c98890741c0703041c002e44561203141c10503100540c18400001d0103680305100c800804090342c2c02480310340b100d0428955200000e00802c259018491018052420040c2410303602408140000c070389d050007503011403c0205490021786044201c07004100344981d2034050680186001c4c40e104001d85001e4941c06c1c0c08203400f411401d82480c0004111041e01c10942209401160042c08a6a190034407071008000d940039510744030074041441d00240d0030b800031025404001d50064050101c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 464026420 1250 464025170 464025179
    0xc060210150e060414070215160206041502121302240405010f2c03190b04120c021002100b03060420031014062d040b06070605040515130507 62
    0x107030010040f42d00540e40c0c10031660801301c21550940144481e4020b041c0c0b012030003a2001685400500f06052a49442e09150003190b0010f00164015080001d070000c051000c085c1d10003a11594262803681e00c000b00900c150b810500264107482c51080f128a01c1120300c000b104a40c22040903c2c1c40c0095009000800007540100d02407a16160645000100c0c44880112814000b005022010200c503030103c035801c0c18102008114a003000140d40c00340102d41795910710203181801400100b201607100e40f6401828010901550f0b05940282a001c40410702c410080d51030354410000c01c1c0c1182403000110203401c2c007044a501030342e04002582d450a00021300c8104402c55908019007503c240c0544811854040c841d8600b030300300300a410401c50600c4820448042a405440c3d4007003c076840c400c0f403400d0030102ca2544003240903140400c0a030710303030400035040c6e0103a8403010706082d0030041007004004020550905107238034900c00708410744030680750f1801070070b18540051560b40f1000c0b081c00b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 464027670 1250 464026420 464026439
    0x906010e010212030c0a0e010516020609040b0402030f040b1303080a0c050f0d020d0507030b091f080a0312061e06031a12060609071107140301020f04030c06021015 72
    0x4103408180100d0f1140d40c0c25001040c9664012030b107403642e0120106007044240c0e03001900101d01e020901c1c215007402c01034001481c0d020300c3c00300024802c0000241e001c00903216500044500c4000410441d1a40340240e045e0552400c00c079000c0380e00d00003410000b03442d94000c000e0707240c025404d41c0c0c8035411965440c222100400e001151306d41400001c0c04a0381e1070f28040b500402003140510400350700c4200c4040a81c041c2c07500580071205140c02e0650b003000c207880b0f100e11103a0001c1000307841c1085460120028015040c9034100b0b8a00d8020984c0900a05420403118401500710f41d000300521591081520030054030010807058000e224803042240601ca60400b1404034211038506d000c802040d00050704074158111035102c0d5410042c1041624980030300d910fa40036225040100c0302c5140011450b880c0c2c891400340c5180c80c80d10390408000c1d901d0960540d44280c04000b1040c1d036036601c0341000c040c6502c8500c1918014400e110304883ca40055001d8588070b55458402120264140741c81d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 464028776 1106 464027670 464027687
    0xa050f0403140d112a240903070b030601141b1c0f020604080423041a03101a0d020f040f0606030608010204081c0c14030409050a0b090601 61
    0x3400c1d4400d9031114294822038405110a5002054000703040064450410420505440d22000040301000002d11841c1c2d000c60031a289d5580c5c824809140384412221b01d8000b030360b20241030800385050000f41c500503880c183c0c4074004141d644a13640ca888054417112512030000500511041d030402c00d07a1094601900c00340c40030b4a06625030b83e90520442c030496000c908559408030716540285601255004020424004032001c0700381d00101d041580c3c152486809021108500702005206003100340c00e140c48840c3e0714100a20801914009419083e6001100b034100ca00b00e5640d01d03c9010f151100ca444000349150402030300030b0880d4942d803c40d0190740e1040000b0f104d0003000103500000861444083c8021486e5a44115040300441c040204014007031660511168000701c090020f03500d142604002d1a81e894103140160390030443c00542000007040031500325441303011030 = true := by decide +kernel

theorem cover : BRFrame.Cov 463848920 464028776 := by
  have h0 := BRFrame.cov_init 463848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 463848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 463848920 ≤ n) (h2 : n < 464028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
