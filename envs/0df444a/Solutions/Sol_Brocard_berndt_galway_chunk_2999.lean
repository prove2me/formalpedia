-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2999
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:22:01.228439+00:00
-- url     : https://prove2.me/submissions/419a73d6-9ec1-405d-abb7-90e13be52a1b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 539208633 ≤ n < 539388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 539209883 1250 539208633 539208643
    0x9190f140610140a08030f0d020702061902010b0d0b01050f0307181e2313060606210e0c060309100e28020a03080c010b03100507110a0f0f0606120302 66
    0xd008004015043c8240207003400c1c50011300303c2d1400c00142d42000d2201007039038001c0d03106100607841c0982c200031900040e034a2038050461240c40c61448040c016813580041c1c01c440d00501e8280c412004000c2c2c2400049203004071906466007601c00d450305c1003503a40801d141c81c2194101c0903035001d28000c0480414160781c81007070b81c071500006014801201801e0041100d1040d0041101880035031090100141280145500600e41491180c260304840d1140382c211005070b0014000121440304042c0e00b605ca40901c10002c1e00030420070401c08018001c2d088e1741d0f590480171503003e240d0210000d55000401d00465000c0c01024106000002480c05141d840714116407000c491a0030400c4071110502800c0746005400d030380902248103060644d1508501071708070310030f103807070543d22520150410388084c03141031010182c904000ca414248500c0241c00c0040060610b5810b51044c6090004900f0780b06078071048a4018030001007038549403c102000d0b112036041195615141b4450600309540020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 539211133 1250 539209883 539209889
    0x10e061f11010f1b050c030d0b010905130501090606050c03030406091703010f03020907110316140708010510050d0b010e06030a02090c091302031006051b011107050609190f140610 79
    0x2a51180c0700c0c800f600170340c3e00e402080c0c0301c840b041d4004e0000e2408150a0f522692008105040480344190364000040604544408015990340c480300100010308150040c04046e09050a1450901000b11480ca94a010042c0003400d41c0740c55400000c05e100c04124070454550409050b581d80c0e40e150150f421030040c2070300c800c90240f07292000040c00b1500c0345004141e0024030001544c136048542c01da810300c5001011060303850180142a10381c41490810a41c0f00400c240000454a440c04414000c0000e0042e40018014025220000c00250340d5040c5c1d50b0640312002203448076500c0b04070110f85080c10215000307412040000910408018100140041600403035000c03211990045141080c2c0c0001d407074050350400d1002c020710046004101130114908405140200c440b8a0305800382580c0c90044462001c040c00185641445010300a540c1d102003001c2c020100d4240c141000b01d21220032136006042d00d071002030702e4000c212040c2d84031128400c4000c1207840c0390034450001c031803c1440344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 539212383 1250 539211133 539211161
    0x10f0c1104020f070c1a0301051e030115061b1101080705070803190b100e0d140102041e0902030f01090b04021c0c020708010b03100e0f0f0307020405010e061f11010f 73
    0x85c400040c2c10701152511409030600d0f5000e50301b580d280c5414805015030b01806002a115101c1ca148200e480034813814035942e820a10b1440394520740480036202d1281c0c130031200b00c00f41c00c62050780c020401c41080303100800403c1c6403101e07803940c401c074041362035000e00030b4010310018000003032040c90702d07240e4003240c22103031000340800220050000300f0071800406a15600819500102c0650364034220700c2141d4114010382503103c04800a00000342240c1c000d4020410004210109101008031101000090090820110303e181403039a00450300da4014480d4890203903c0d030050b00001d48480c4c040e981d01032102c4a0702400034200c80320700300c007401030251004018801ea40c000036048005008891072001c01801034412940c80c0c809982c050051040701d00070f02d1003080025860746004010800c103440c0c2800282d5202c05176841003006507901a032110300a20b60f5a010b0041c00e40d00c100140005007070303d01c603041c0d114400c00803e8407800d2603480418519480d1a4103a0003082c41074024015885c81c1c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 539213633 1250 539212383 539212403
    0x3120115031a04020a05120109090b131104020f041d060f0604030305190318050f15091f0e0115031203020c10050901060f03141b010f0c1104020f07 65
    0xc0304114201c0e124102402d818114030080740200c0d007020b030300801c0344c03601c585099498011980d191100110080e40034049040c1d45508200c28000ba131190650040b008000e4001c1120302921400461192101c495108a81c000340141640180070115001404001502c0c40c0d5a0040030105011003801ca0f0700300c1c000c0d41d50844040c164500242101e055950540700c00d0b0500355042501c031810141825020305141c3d17101c2105803007030603c84070702203003e102c0d00c010407420f03402e410240d0616910515102e08202581c05000c01c600d0701250359904045200024444040414911800b0741148000c2c08880c1d440c15640c6a00c04840e41e600c401580c0c050201003108050f024000c03030481c0324041c0c42c030f0899007040d12080800003094002a4202e04910004504143c590040040c007252944c411600c0203405e042e4004002000d0100740700c12059910105107002e0380d000042c2901446a000108010420642804006030304400c1025180090011501e480c8042c12685031a80300c000281c0f414440 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 539214883 1250 539213633 539213669
    0x30a0305070e0307030305090a090912030c020102090108191e15050306060a06180506030a050403080603060103030e22050109060501020708070f0e07031d0c12121902070305031201 79
    0x40c81e0b412000c4100600101426461910101c1d1190001c4030313010350118a01100041c56034450050070460390087d90080a00c400c0c03808040c040392440000c0c102964010b10400840f40c1e00824030a03400380030041d042200100303400e101c5009050745902d01594582d507461284400115a0200b101c001d035004851031b00300d440d401010f540e008101c07001c540c01b2120b50802d2000c288201d1031103c5900d40f0001340b4014a4884000074401c1d04100c441c0c0c94416600c900300018140d010403101d0b00328006401400700382d411a10001e21071001204024000d424948884031821608440c00c2403040c500c0d80200136a503142d04034030b00038151500c91107005120b4494082031101c00170400c04102c40d68448a01100b40c074040c01c01002c20802002042455034880c1b001080b0369441d1411041200400007404100480c40d007000300b28075258910303450940c03040c4540d042101c0200101d0345034001803101000142c0301c0140482c40e106284e0002400c0703000208034030030b81081440351281a07403070030084a41000d41c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 539216133 1250 539214883 539214887
    0x4050601061202070c120c0f03030203070c05040e0a082d03090d051216050c06040f0203070902041a070c0b040305010504150203060303070212030d2d0506100305070504090905030a030507 82
    0x1504e9005011000c1c886410401407503031031001540c551050581c03818180e07507041c000c100b081c0142c0c410740c0503030400680e010400c140b1030300c44000340c40f04480070002040860b50542d903800340c1841c001c00000001401301c1200d840c080d4020b040b49503604001411000c07050019100b40c000703440381011445a01c03041c0d405031340124103960743c200a084091501d0b0391894000490a82e00c040c2c400103005040000c030b84180000d019241c416402603032441c2004070340e0700c1494034020003a8056010b8138030500041c800203459080044100c0e0b0000c07641d0341c070740300582040004d1490320b52000e4040d020001d800001c01a06411052140e0300030105030500b04110000c803002c0e444100c8a166158004112203401441c1c0044040420b400c2402128200b0013400300c800c00b00c0d9040300c500c0da01005140b85804910790060989021400072083c1407000f400d00101240e006a09080ca581c149601c2c7c02c00070314164410340c00e55004000e1410b00348070110850501680b43d034000182900020b00344800262054 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 539217383 1250 539216133 539216137
    0x1202030609150c032d040c0e0106050406200613120903030e0103200a030e0c040c08010e1e0f090f0d0f050f0d09061b091406090d060504050601061202 66
    0x1144180380c4080c281e5032043c00114030b41c0002c010f10f01100e003241c07600c40402c915884007204041480e102c1112820701e4248403441c5001c66102c6614040d1000050204a52040691b4101c0b501400c0503805040d00b0300c07403075980c81c1c28002040c0445c411102003000306400c684a8408040c010070781900317128000c0d441140c0520f124000940410442d07061b064041d40b203507000c640c4030b105c04d2040e0306c0c00c00c1482180230a507900521058000a84035541149468010321240c80c841c082107400300725800140704081c1c50380308148940150400c404000400060b0010080c1141402d0b4914039989458026000045901c2c160789404a900c0348441c55aa0030f880021422240407041d01e8158840180d800c1c126242d50000c00001d840f01003d101c0d110756581c541c007911140714031130312003c9803c0d500562400200c120f4030701c00d8420084820020480600401c0741904032010a541c0b030750b540c0100301c2c0441c0c0e0340c0c0110400103007400e28010400c001e001d0082075203410384043c0d03556003802c1850314104034240c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 539218633 1250 539217383 539217403
    0x7171e0f030711010e0f0f01060b040e0606130803040f14030105060d2901030c03030e0607031b0609080310030b0903090105221d0601090b0c060615131202030609 71
    0x42022070002405881402d408030039000c004902d000805d41828208145110b0080440d0b0014007601031035a000c0c05004003030701c500070b0f02d941071034030b08888c0da85001d4020340128001c4500090000d1082d0b032259001c000f030500c50b001c90340d85540da00e0160640344098800c00400c01c1211452038050f01d03045c007845000b404000d110034000b0229807200c000003050581106d40080305999003080d406a083e5025000394020340140303910300e186040182ca20309500301041d1145a0810890002941017030500450000005544400480f289413143c02800042409000e4400100400c102c0d02c29580041003564825200207005842d011181d40e52405440491408510305001e0311000107548400c030f40c00346242e07120407007400e0f54405200c4e11041c118a80701c149040810104202541c21405030001000d08a40191900c00c0b904400e42d00c0704001f0f41100d01c106030543e83d13414544200c2069079501120034461718080c40d40d0f0508803a030900420b41c100c0c06070042400040c02007802041c80c40d28 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 539219883 1250 539218633 539218657
    0x304021504030f0b0a0e010e1c1701060c050c091504060e100b030c07060507020a050f0601030803070f0e03010e03120a1b050f070b100608100311010e030307171e 71
    0x500d081d15951010304840080581e20115628001c1900171b000134002c0d02510000d040c041c1c500e501071310041141154112282400340a044040b154894507058141c3d41141c043d40703490405080d25242c024180b1a0768038405a10030220030511074050040742988a1960045404004083d0b03640300342900c0710300440e0458800580203804206050302d4030011640aa182c4035601e00d800c403140c1d100c0003150340a450040c0140d020143c0c09040100030411072005540000c000c14103585195076025852000414900400c0a82c3c5120000e03203002d00903074131041000400034070004002c42d031740940e1f80d00048030002940c100040482e000c1260761003003034070130a2903d0340c1c004500500c041c16202a802003050883c075800c10040e032800f007043c481d08036004031440c09aa038940317850484010304142001c1c2c0b00c0014010710901c00c1000604900d680d030700d62102030801591703480110000038110300403031300c0242500400190800c40c000c003c81c0240f100007007910100c10540c5007659030714040c1c000e04000a107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 539221133 1250 539219883 539219903
    0xd02071401110c1302071b0b0901030f09020d050105091006140603040c030b0f0a240324140601031b050d0506120f07060e0414040b0711070b030402150403 68
    0x365441103030301030750400035402254500ba04100126810341c03004401488400c1c2d000c42d0100030421800c0c417124640320842443d083c6c40c1c1c103120a1000e180304802d40715040c5076458040c04005050790304001200e41c1c0040400407038041508000d4007904003110580c0a5015801203010300612600c90300003a01c9803506020341c01081c84040c0003055201600590b032510034588008000349282c040783d48690044e04081d043c0b801d080d81c3c818180d60300900d030b61850b01070109480180080929540c411240c021113960700d500c25540d244140485403100841e0700c0da05003849030130141e1f85112424040d000030307607003045038a0004c126107107540d13250749240300022020010707804d8419258019642104000300b42030800110045814508500084410201c1d002030008000c410707001403810380202d0f01580e081c880100d024001d640b1070b9200800003070080a14034045401d99210320004e055941410301100c11072078540c1c00d902c3c01d540084808900c901034160085800a070311109507801c607580500b901c0c0d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 539222383 1250 539221133 539221169
    0x13050a240612060218030d03020c0c0604030807020f1f260f0f06132a14040b0f07080c0a0c061805060c0f071805061c0305030a0b19080d0207 62
    0x40c004c1c0d40000219004460030000d100019581840f811000c4c0310b040c1c4005a0f1020b01c45c2105003000e50400d0604d104400901080000c07495000440d545140d040f03840c0140e51484400040359443c10301c0c000e000c0010600c071080c41c22034203c20211a0161a0101d0600c1018111b1130445a01012200203038100c1940e03010a0010020b1202d1603017284c001483d5010110380c0040c5a811100e000c00c00f000d81d426000b6a40c051450380c018032055514030340c6003a4032041c055100f8540d4a11807840703201c991950024240a00300345c10002e9601c03080e07005078400e40d503124900440b641c0303103c0c1d14026a98031040003000250740d4051884136030f4142c3c17101c00c0041910f00c0e000410065030030484424007280103440c05940c0c260030612507000500b44c023104030940805d80c0140b5404540c4028100d80c0076101038221502042400050b40b101c180c0d240c41d0040e9a599944040c82c064200040c4040c0c008001d5135800d040310003109460000d94440b5002c945213800106c204a0355226a803240b2143c0d440941c10350 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 539223633 1250 539222383 539222393
    0xb090f0112020607050f031309050a05040302071202030a1407081203041110021006060201050a110f1602060f0f09132310030b010803180109060e0913050a240612 71
    0x10b00301c040c1c003480503110a1b420700c5865130b06581c02040c19800019a4410600c0154410303c55290480d0b07200e4400c200601d45541e02039034030310480c0070f2a010703040a001d0800c11507a00704405115580e000742c40b9040300c039041050507a1851103002c1d802c3c0320701814801702c90b04001d04d030079030b845941c124640012040a983c11301000707510941741c2c481107005131040c4c1d000804050062000402e026400015285400c0001404450b640f6901c0c2d00300e04800c12422022007a0712040d60051005007400580f04111403002660505c508001300d403103240c0208144101d01890005841c4209055071403107091141e41c070941086598044031943c0184c165101203802c5035501842c0ca6010401c1d280f40100c0031b03201d4450143c4131909a003c2c40701640000703103a905901801e07007010186802801d207441c10714240300d8041c2c106015070250034022048600082c0352400020555144036402000f40d482c000d219081028070125000d42284031605014504200000c2c40d22844080301c4650700f0301c0c024422240c3d25 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 539224883 1250 539223633 539223637
    0xa1511130504110d05070806011407020306240a0e0106020c06090d12021905071503060602030a03020c1f020703080f0106120906020d110403170a05030c0d0f0f0b090f01120206 77
    0x11003c0c0c0c94109100400201c07140b403241501840040d154030001c1d03e407030b40004003440345482041c03081480510807900140c50004010307403c40c0c25504920b01140d000c0320700310800c003c01034032258402d941e80000a080e90760300b290305043c3e801c550301340c440301d000c81c1c81032003918480c0e0341080c0e40044025640402040c40001c403004a1b0301c0c20310655468070b88014011628184c0c040d0103460a800030032040100e0f40007910080d51903002d900b0300740320181c0381078000ba459000b0030b2083d00a1540006d005a1040c009004c0a402682c11084031807243110890181700080d0040315044022030010320202c2d038800b0036036881904803125680c8003500050201501c4d0068501c4800445d441902441000ca5101860141440c96240d10201c191124a141815031452b000400c102440304410010f0b682c401e41e00c0b80440f41c0c4201c45180c1c031aa5030309035105d000000c0802e101c03842e100f40c0ca8481c0000000305940c1001c3d80c2c0e040c0c220380000c03190b1a500d0524001103002e104039001c152400c40104014241200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 539226133 1250 539224883 539224901
    0x105010302031e1b0408030a030b0301050402010c021509090a140901060b0a1209050303331804021306080c030d0305011d040f0b04030f030f0c20010e0a1511130504 72
    0x1307001ca0400c520401c041d000341d04156840e8202080700c2d440b941c0e052003034502c0284220020700403428242c0002c0c0c0010f00e5403001900401854401940c1c28444a08459020034094002507040c038007049503000800303806406040a100410205007030310030500485050f1240301b04241e1030900c0d5040152071920840d4010f0f07400c02d840d103540d54045807007400507610801440c241d200f505d00c240480300c03d522140744500c4100614003180001151030b41d00621075580302901001200c0d40703444c00000c116511403104241114148003000c00c4a040c0421020203102050f0308480140056100940a80d51309005045e80c0d07140480070450b0140400d401280c100e400b90024042044440c2c90302041400111001d40100c1c00540501d181075600d4803407982c40c0c08014404000c84001600005e01c0c000007500c1d26214041c0e003088100c4c3d10751003907010f1917401030a50210781c41d50235549401a071800074400403c002d03600e010004103000126078200c48010203141002c1031543d0400c2c0801c001028609 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 539227383 1250 539226133 539226151
    0x13020f01050c15101802040e060d0c09020a120c09140607080d0b0a030203121213021f18030f05010e03090a1509090903030203090106050303210901090c060504030b0105010302031e 79
    0x32200166544917401e100340c03040c3c4944000350fa114180702c032290700c0000252107a80554500080c803c04104802030920a4500400c00984c0d100d5528a045400788940f00c1000c0c03c541c0391030210842e0641050502007107902444220313042e9411101000068001d02801810f48002084070350b40600e45584036014600d0002d2060501580725008a85000c03201d8aa0305020400081d0841c078400c01f8158081d407125118140d480c01c2403596000c1242c14035440c0e0030000c0d059800c40b502c06024001c6110b071096020407814542100d03a41c1c28a010f81070040744007500c8035440c0c402d41003e641c5000c41201d140d00b10103401e040705c051170070b00310b0780400c25503000160401c44410030100c2c4007481406070045d076071b0080e90051307181d0600810b185d00311441940000c1c4280d0080081ca07000700200c1340c414029040242c0a116159208007174030703000d040c44c0c1c42c00601c0780303031100004200340e1341240180090300e00070720161503140e0302c0344019070403448241c2d490300c0b00c1c142e4201da901000440c50112540301c5d07901 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 539228633 1250 539227383 539227411
    0x10110a0803010f090501320f1009052e0c0611030a0903180303081306110a05030f180a172703010b040513020402130e13020f01050c15 59
    0x154444a0080d002030b0000f01c0c80b83c1e1040701c10098414103004007805008150f400390800100e92038005100d0004011400001d02d0381750f0780700003c2d52070451084030460040c0082c1021242c0c03650003403220360350740140c620031905945c250904000031000d0083d001307101040c6415007048000241c0b0106204c541c122a4540c464505038294444000518000c0c0d0140d6008505a0703030519000d01000108280a64085491002080803d034062501500004140c000ca0342d00042c3e0b09100300a0b1800421001d00f407400000d074000b42540c031000641c0304181409a0540b240c941d04860000c41c4100034030051180d010880741c5011030040c01920103000c8800c0b201c54541414055810400a50500000210388200702600101d05080c040c0d8074056030704039004c100a04d05002058080d0f50421000b81c056540070403c40c0188030f5250f44000a0140700c1002c4000745009000b2081c0042401d01c1213000d0003440003442d01030350003802036405604500002d000101c040b190903001e00c14006081c9414540c003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 539229883 1250 539228633 539228653
    0x5040f05011a09090604030206070f050909040c05210a080f0c011401090507090819030e220605090c070b1f030501090b09030a02121e0d0b0f0303091011 67
    0x24031a4007021400061070038290103154007000750f0880020100307103064112408000000342d004c101d041c1c5c40302071406c000810344031040e401c580b1342c0211740007607400c40d10110500c070074042c41c0c0701107a007240e0301256075154000e0201e2602588801c0320b0083c010951080556100040140d40541240c0d042ca010311814508487c03002030035590b05400e01030311105c042c0014042c4107614090b0650082e068244140d8040c83c1441c031a6031190018035000d44215000c500c0c00405208003141c0210100040c1000b054921090485c000801c15a0a8800d40d03460817000080742c0c149101c18610428020300301509141c02078a803880c1c040c42c010710201c400261100f04403c03055061962b240918014400002d449091340751200c1200005080301c0388551040c40500c41e2943e00041e070460b45069407845a4689495408410001a0078000038503152004038440341c0e510155400074007050700490b08140c259404000f416100c0c490000300303d40100188506035000341c0603202108410340103804a03007990172 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 539231133 1250 539229883 539229893
    0x6030307050304062604111e0d0b10030c080601080d09060909090212121317030417011e0f0f060317090f1c0201090605040803030118020c011d0d0905060301050405040f 74
    0x6402c0303a0445403003c3c45d102107e014100003240842e810351102c40c101c3d078580c0180c00140c1c580c24501d8018040c0518a0004100301100c1580000a42d805003401b0780c056101c014843e01c4a40c2405810145d110385103601210078403030b0100d20f0441e18551645401c40741400000342c00b4106607a02645c10003540b1545503031039038040207050040340c0114119500d40c0444015180c07400b006a102914156070342484254604001c401c031022a43c200f004c05a0180b012002d05001d071584268281200354269011404841d6641101184201e0710380c0401841d1081032804003110042c1c04054a007030200c0342c003d055810003600070044084010300c02c0540c0c000e1000064242d075100b070305054050480e400000210758100780080054041818414142810103840503543e0005200b8010005030740103604040759071950440b401d030b00c2d0b40b00091249410b00c2a11304c030320001442d07409880340710301c03201f02408910500601e000d0f075200070596440c6900e01810440901000740058071044044841100016 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 539232383 1250 539231133 539231207
    0xf170a0c17090c12011e0203091504030806103f0203040c03020301060608071b02010c0f06050711010c0e0d060209062106090906070807020c0d080903060603030705030406 75
    0xc4000004103c2e1814850078401e42001003043c451075070b0f051003040a008a021901c1d240d580d0044100140c596958100b407918001501490881034450075081c4414184c0c001c0c07000b84240f20075036603500c04600850703040302d0020040d900214003000c604032104843c4647e4525018090054802680c04140340917144105c0c0d2080d81e0031110740540000400850400780102e0004110a0901041a2800d840043d202d180074a17101e030f21421402d284502161f024a1801905d540c0110b4401d241d4512031802d400281815510302020401c2d1400700c0d050441e05016000c820107440e6240c202e40d9400000b0301c04a42c180960888101d85c0070f12802c0d145850300f4025046001c1c0b90111003031000800201c112030850302405080c0522005030803c00b411030000f40c0c031500440d10380380040c01c0e583c43c030310200c0c01c00302d10741036407541310281d5402e040501961101a16605200300d040d0703a0f217500c0308010156603200d0168010903a80003448100700c0d45001e003052803000d4943c4403446c0100800c05880003001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 539233633 1250 539232383 539232391
    0x10e21030a020c0307050f1c0507090204230a050609151b07060305060a0b071202010e0d1106130c230409060e0105070c0b150d05030304120f170a0c17 66
    0x140c3c81548180614601040320500a01c1c041d00c65003034807031449001c114100e400050580002c00548030110801104100d008024504070303034210348403601e4142c3c03030f117004211100001c480810300d942c0a20502c0c0c0243c41000725000280310b14903100c01441031003018000c840c0010100e10341400760754640544040808641111031000d810000d0030024050308590000d04ae49000340340b10b01c4144100d80049048030305254020340741859030000440d0480c05490040c220003130301d00071b8020149145410100c04000e440441d400d5a001d5681c00082c044205903000c8050002d00c00c86008000054503200700c4402d45440c1312002d03054520071404101a01c1c54030400326030003555280b803001410428422140c001e4418a0308284502d1305403138126070a2009044810090a40041030405690701c540c0b00c840c05071b0000c11749440f46424240400108042c115403404655511642410584150568015140c03004c200c0c07100c07070700c9107003d000c01084410700c1d010038050f16038080c43c034070b101c03c20b01c00d171007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 539234883 1250 539233633 539233637
    0xc050d02031902010b090601110a0228060201020f030606090307030c0608181906020d06030f08030105090f0705120411060c070501030e0a0203070513140c0a0e01050405010e21030a 79
    0x14600520752220b8035440085026021a45451005041d5564032450250000310034030703241090f042001015418000750380380086d80300ca0749010710840ba5001046500c0c0103108101d80c0c07102c1a80e1420281d0030303441254005074034100c0c108002407061030400041c0000210180c200c65401d5160340d10f070224003015030003040100300580c0401c04241000c0c4503640700206010064134004840d1003c0074684514280000d0919030007040c0c11b100d103c0c40da40090700441c1c01c520001c61928150030464003640c002e0041c00d028030481c0c40003403440c1c292802c2807070040800c1e641d02890190f01a010b808001000340003110728140c00b0752411361940d1844c003c5d15012250401804c030340352424002404a400c2402400d10642108a8540141e40d000c0742101c11034ac4159901309410a05200e80e03c001c0595002c070001313030b544002c18080c0001c0c048001e000315070f10580320ba0130010780b1040103541c2800b072441214002070448040101c01c1c10500880340c070403101007002e40400e40001040c0341c25608086d07070882c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 539236133 1250 539234883 539234887
    0x130b0a24030c0602241021020a06030b0907080c0f1c0e01020906041a0d0218310f02040906030c0306151203030b011103040909031704081b0c4501150c050d0203 70
    0x408e40c501212640c0040c001d50600b04103008081000c1901520004c0c41d00051101d10000074050041000444113031100610803982c0d180c000100c200c2c080190304180200440ca0b004140941102c1407084805803080140304905240c50700500e0300d24114208010324401e0301c00e03c489041071416002821021070920820315100a1141c01c0c011601c1100d803011010600c0d088194903404a03145003513000d00e00c0860f012410030100540e49c80039100b1548034544a524207000003051040481840091b00d01c254014000000d01e50700040641d50135001c0c060018007511f0300b16000a001c1c0e44280365039101030500000045112090f542140c106a101054040c0c44c0c0c03488108041e4000a0440210881311016480b401c00345c0314035049024003600303401a918141c00c8800f00c0003040202035510309000f03046503c289500c03940840d032010f600749691031449403400f00c1125003041c04181d0705020b1041c1403031039150380303003d10070002402d400c070700f02003030148802101003c10320600007014500790b10f4006507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 539237383 1250 539236133 539236199
    0x105070c1103010903080a020a090e0a0204060909090c061d151801080c25141f0c140f0909010b03070e010503130b0a24030c06022410 59
    0x141100030704805892203a4500310b5000006500071400d00d4004207850344c010780710b0340d96030400d0f42c0e46c1d4003581050070340c0c001fa04108282d420f0550003e200b918519954582c045d6599248101a5211900024808403d40ca42803020074031410282035070050440c00058520030b000301040200420f01e1405140c94000074164082038076400d0b203010f40c44d0003841d0803401441c01d85008001030044210100f07032201269500364174946811b08049410760480d65411252046071400783d0f40e110704020b07294411340300403485c1c3e105114500c80c5001d10902900d4441d602e2822050301d10b46540711110300750101009102010140d183c1030300c45030103801054103aa1341c905000300b01604002c00402c282e410071000301f003084031a0340d400e1400e02d60325900c214801c1c11070712503c540302d0107099404406c0b00e90700381d20b080c49800304d10713035034401c800300c1c0e0103207003d005844c1c1c070b40c5404c90b00c450f5401c2c2c50085040c07081c103101001014000e9501d034410070700c040a4980b180c980703404410a6803441c091800b5884110118 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 539238633 1250 539237383 539237393
    0x30207030e19090e0313090c020703150905010b092e1206021822021620090108011a120321040b06060703080c0c011d07061701140d050c030105070c 65
    0x4107180c480308004606185942c600111b01641034020380c0d082d59180d10380c0a00003402003001c5805503511128840b0003581070a41d0200030204c680341541c6642c280750b200c20250800041c206e01400910001e42c602070030009458502c5508810707440c103200700d0048001850607030f40303840300c1082d84074550169864010100c0701240d4000307010a144180580b02c2165100307005c101c100070001a60190150b04d82c0b0794103010100c071450000c0c0241001d8040d03488203510841f00318102c41e10150844100740c9598032088031600303ca081e0340320702c001c1d81681a140c2000d8502900038080411010b0101c03481c160003001101d035000c0c2c01c00c50307100e9020608001d020400440070070035a8004010b40398107042148541b0b0003002e450b0003800c1000b4500c40002c59004030701080d00030410a51140d1140b041415051800c2030356000350384100c000140380c218060b1074100d90520784504a69203148103c07005042d050810002d5030354440308852034070440107164400d441c20b00038a841000c042d16040f0055005040c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 539239883 1250 539238633 539238641
    0xa02010b0303090f090702101d0105090c030601121b03060b01110a0b040803041a10051903020d02060c100f021b03090901030b15030f0105040c1203050a030207030e1909 74
    0x64400d420511403106240c5482e00803807891314003110400c5103030310703200c82c2a4104442c51804000381c90601e200f400c40302d851011801c000c582e0042c001c02c440d0b030300c04540e036464a01400d0781a03495004840108120000602c440106a000f1070080d14500f000610807441c0840a078002c482d0951100c1d11074109603001041009941e80c40710190002580ca6691210b01500c0100300030502040030011405202c40142c6c044c2d400c41400400716242c0c100a6804038600317003103110740c034402e00c07404188120300c68084646000300d0340d014140407244d0302907900f00400e035008a14103140b03612641590780410341da5405600c845803803001d00183d0b1803801000c0f10030f0301000e2601940c000d030303c20401d4291a80310000c50a04480c0c0000c10f184198986114072550355818030011a490311488508100b02c51045d4040d41c026449080510701c410764850840e20804142000a0085441804034199081c0203030020000640300389028508044810002081e642c2070003c029480c035a22941800000d14503c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 539241133 1250 539239883 539239901
    0x50a050f07050406020304061209080d0911010c050309040506041509060816031101080a0f0e0610050a0e040b060d0215030712022b2027090601030c090305030a050a0201 74
    0x1800600c3c00d802d054010703542e8400d501c14603081012620080c4500001035001821260f84035200f103036079808a0050b40080c2107180002d80d4034291980c00e6a03507640c040c01150740d6540c1d1000145003419800003c110041c0302c002d14240d005615508005420703059042a080500744d070b0000001c030281405407985c68900f006808040902d501a0244042200400d0340140d000007441c1216040c0d444403000c902400f0031b6543c1e030012a00303282e11080150300c081403003841a0b804030f0300640c9040e600c00402a5807640c40c031031480c01106013008100407402034400d00b648810007901888485000d03074003245119a00041103400d0010100c1800a03003680040045181520150150300b0544407070015400400301e00c029004404c0c4d283c0f1802c24450300713600548507000c8410580c0e104000000c00300c0010303500000b1004c14001c1801c88a40c51403100c031055210b8020041c01307100c01552b40d1001540103001120120050089400380000010ac0030402440f1549182d13403070030340718501d00714041d003554080c007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 539242383 1250 539241133 539241137
    0xd0c0206070b040f0c05041103060f0109050312091c0f0209040f0209010902040e0a0516230a09060909020c0a0201030e031b0102130f210314161101080601080f0702030904050a050f07 80
    0xda0f0308c4012200025a900910304460340e11200b40c0c1100140c2d001c811a80c0501c1e054005d0310021406400c1c9100a850311260a4030040002d01c280710300c14841d40641c820050411981044a001504001001c00c2e40140300d26030740b00c842c80309900068a548400d030302248100703030001000e1011801100711150441c0c541c04080c071090420112050307a803900c11309103d081017080f040b0710000c260b0b1655920300ca40702d80c2d66860358505482c440284091950701503038012607506040048c0700c002920880d400d103154031014260b80365440c0e004401410f1845005461380c4801d00c102c1e0a40850081c007150f40c42d980d14001a0785803020321440240010560103104c2a1114820070062004850003c070200403074500f070028030b045c0d1071505071040864840003549400d8082044040d8010031401d03600200e005044240710040d40c04c004440d40c3c0310071161a40011620004501010070544201383c0104a80c015241000411800320702225002c8620b040d41c80d466405004104c200c1034080c80d0080180c2c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 539243633 1250 539242383 539242391
    0x6030614030d0f14120402090105030303090706031505040c02071404060501020a11190e040302010f1a010f05090d03120c1b03180b0301150f050c0d0c0206070b040f0c0504 75
    0x3010020303446550103a8041d040c0f11a03480d540400a1040f141c44000080b40d000e02511498103880e402c15032442224121b014080e101c1c00031450f840c002050301d100c0e000c0c2ca4001d160103428228200c0c003400740c00c07402c800d1403031800c1404105591580101d8511660702c1d401815a0340c903060503030030300c141d1400318203000d80d261803020b100503640810103c0c00150803020203070307898030b504011491143e20450840050700c502031300400c204207d92040b03030003280698000d00401202c003604d9400c5504d100c0800e03410071049118001c09500034001546111701c541482414043d190300420792000d407110b400c0300003440e4065919289141489a40c007180c2c094a0007521050890502c050ba0980340d80c409400d00249404032150108612040d501505071082c0203a281d5070b40b0715841c40d01480002119010800000180c02c0452003081618040341010780201489144118240c580a500c0001a07800a90410050001c41e904014050149102d000c090b2610102400e1031304d21040340d600403511503810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 539244883 1250 539243633 539243669
    0xb1b0d0501081516140f070204060314011a091519060c060e070506030619091107061b0e04020a030f0218011803031707020f1c0f17041b03140106060306 67
    0x400310101d2801180c40d06415615032061b4083c082c2406092002035115040002c040200005242015803081d0240000e118880086c02000c8610070f24102054114506070300140900856070070100144e1380c040d00c01034000c000b030002c121580b0001d0704508042a508940740f03003040154031030707020044156405010200d0a10000840510020b01002e1041c03100345034a050140e456000040101a01442080102d21003882113020307410448040d50344900d0120700c0798031020b071505914500ca44660b1982c800180b0281040000d4208500c0c6508050ba21032203080d20214520003031440c0302181141000300b180a80006048084810204c1100101004208006a0440072021041c9820780040105550b06d81041b407905c00711407400725071031140011413642c105401944d030301c100c0d02540d9241480300b6503403003d40d1240f01400303c00c12031603002c900042c04580f000482c081d030183e4001e481c5050310f650340c0f242c2070781c07074a0200003030f020741d40d2114104411501807080400a142070f041410346126 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 539246133 1250 539244883 539244887
    0x30302211207050f0f032a07020f120a0606081e12040329070c020f030708060406051e0109050f01050406080d0806190803070c0504090b1b0d0501081516 67
    0x220142c1004244907003c118026070303401000545410107541100240c50b4600320b80c802e01e80c0000d0400801c841c00d0028007841044071158215860305401800009480410034207020584120110511a038010040440001443e6000c0c00c4020550440140811656080d00c0340170340c0012001c0b1142d0358030402e03c4003200141c840545040f00d4001d002c40c0d2000a217804580000640300604003950340303410080122043e0031036881450f0500940d410003140d9001c0c000d041e80c0d0311880c0034030b511075401180020002070013908059400051010721210f415810030080701c1e40c1c0030a8000c1500107450710704000407020101051401460100c4042c040e403441e16070b1031600d07250006000070801240e20000340241c0c4511140602c2115004040d00800d6a144205500d03500810380440e106080702400180a10703003402012034081d00946202c1264490b10700041003c01c59109000ca290002e01c000800c2c08118401c0034000c0441002400c8038041d42180c60f6001d0030b00031311040d0031840383c070f90f40ea038429 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 539247383 1250 539246133 539246167
    0xb06010509011d06070605010806180f1923030309010e0105061003020a1701090c02070b030f160201180b0f060111061902090d061e2f0c010603030221 66
    0x20000700381c0e210003105007004038404d446142c60180155080030300000340d80c3c900040091045407907180001c000586071003131a807202003840c10508580c0c03000415591481410b142d4504052041d0107015610a0034041c0040021480b41c03540f00d02e400102c20002e15200a0040c41d4040700f265000b08190302d450000240e040004030489030425501040350740c5030038094400302d03810301c103e0b2040400075a556610540a0030b00422018014000e1410025001c40843e040e01d02988010910690301d64482104020001e03481807490115903d0303c001d10080302c5800302c1001c5d0305000700e00503600d07490310000206a60002030241410088402403616110b03c0100701c05030070075401000000c01800108041c0041e019a10b40c09901002480820701000601d602c030071a941d810a0044050604c0a60b01004845e075283d440d8450050f13200e103444d004508049041c0d40c0303900f810221810440464030090848800360004c40269000001c00c0e004150009205925220701400084c80c3c4000050000d00741 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 539248633 1250 539247383 539247407
    0x5030a060b030a020405012409050310180b0f10150807080a09023a0c03080913140406180201021005070509030a12090b0403030e09181002070b0601050901 68
    0x103599035001d440c82e0b9020302004036850b40007441800f403075031590001018118101e010800a8182d1914030314954012101c0303104841005002e002001821032005d4040d01303128542c910540c40d03031402800094180300c200c9000e04c241100e417445620300f10b6405a54811603030005441208080d0131842105da00000c0300d035119a203840c105129448681c0c850b405481d4000000b03500c180d0380c2c08410b1845c41d105074014204200114103181a005a40e580c0e042000e0310400a0701d4511015070510100e04400000e244542d00036091384054481c02d201da200301c0d50007624118000b020f0109100601400d0f0007401d60440000882201e61605d80d1f001075601c00842e080b081d1a0741d199000104007034042c2003503c040120203400d884070b50500e482e003001403a020b1030b4280041385503aa40416002403d10555050702c0d491f0303d40c0c0e10130f41c3c440d00c00c00c1601038000704942420345072901240a0710500b802455401c0c3c00e0201e01586454907468000b0b880c0c070005042c40d041100500010110f80e0b44040e002002d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 539249883 1250 539248633 539248643
    0xc2218110c030d0902040513030f0f020c060301060201020c06090105061c06020903030c0a0501181a25020d020c09100501081902070c0e0a0608030a0e040f0509070302011805030a 78
    0x10380c040500d8811150060307807a505050b000c04500e00c14100c1c41600f100b469244202c60070003403035540310301000d42d101100d8006000510b003444206032441c09030350020002007a03401200e40f4428144009600f56009800290042c2d4000c200e4520201c1d08000c16078000007010000d000a180c14404100e19003d1400f4409070540d0150b140340c00d1240d5039044402f4000090b0a0703aa07590f459010300d5035100d000c02001c03141c41d86021028084848050fa16030000c0c0d901024500c0000074003d0a54500703c0054006111000c12501c41e0000304202046000018050340251020100281c0060300780144580c111317000e5549007040180e00c210116540f4140da909003814407817500c441c8141c00c161340000d10701401e550300c0000d0035001e012280f01554100c541d1140c200301d040c1c0d01d4520340c0302994020f01c100081f40d0700900c4a5440f2a006042e1181c40f0f403030103000000c880d13081e0380c00382c3e01382c078010340b040c803480d40140205006650780508010281c2038091080f00c039003890440403a0703072103075003a0b0302a03e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 539251133 1250 539249883 539249891
    0x501081605040506030133080408071a01060305090106091107061104090207050a111e010f020a0c03081b030f0403060b06070b0711100b0108040b09150c2218 69
    0x35900d8001d5003607802502c0044c0c0060380b01c0da100e1a91701001480745d81d1712034601d400301004151440007038422042180890790382c40400d445e13554400c8070a410441048032044028040401418001d0300350f01c0c000c0c80325503400329641c28045021401c4a91903045624410304107504480c12075507846c110388003079901c00300000b440c2e45da06132800d03214000d41d0010a41036000007280301c00d014002401d6540c1034010612051040d89040c2000b0103c03049038885507203a07101c00385501d103d40c0101859910f02e409401a5000c2002c16900d10448982940040390b880e80046840c60303240a44001c0d101c070500864004601c2d20704446c001a40354090f510009048544442c0d46501580b45c0f5002d8495495106160002a00b4442d002a10b0400c4401144c00341c1e12900015140322803071802085680e550684807143c458940307440b1a201710900130240d20041c4500720b0300e440c0303204a001001c0d20503014800c265031940c0c10002e00140801000322491040d490520080c4100d071049404107000d4a04410002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 539252383 1250 539251133 539251171
    0x90c0603270a050d09230f0f041404110108010e0c0313081801021002030606120405120705160915091d0313050414040b01210605011716050108 63
    0x8440300034501c00015260007034078002d070700708440040ca00c01d40540548580303031442c0d02c03150301010b10654040c106c070f00da440c0e44252100324244109014120b40700035108003800440e030b50104058812191011071142109020002441245e80707d550504a0929141c052545850441030785150003410180402d9800404582e00c2811460100051a8046801c0d03850704c507001d40e808080c58400742151b0142c003c0079940300c8050040c0c42142d01c9041d009183d0360414031540006520300030000c2085503d4419038100e50721110000000e08442031042005042101d8001c0382c802c07841000c2da02c246546410701d60384000134058540d8000030307951b00e0200080ea0100c00b130407090604d00300894410440c000011044448800c851802c03003036900546081c083c0303074440721114129020840d40900a00f8a80c80103121141520442400140c10401c40d116404019255503048400030703030212410802c03501091070850018045c680700c0d1480102e40e00c031818609000640b41d4a0010080c3c1c0f205655403580b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 539253633 1250 539252383 539252431
    0x2b18020105031806040f050c030f07090b150c01091e030f0309020d020405240a0e040b06060c070609031203200c070f090f11030108071a1c14090c0603 66
    0x80d001c3c0000c19403c0700d1803400e0606202002d01207002003038503d405a000c0200403428002584207800740c01c5c0c0010110701d80f500900a00600000f074450f0f0303208000c0c000d50707103440c1c00c0b4002400034a0340c02d90001030100e07060302e8507915604101038084034542c0d1000c00c00e00440d030809240f21070401d2070709004c10031039218400180da0010000c0025130241c50182880325049070b481d0500c0580c00c5000b9041000143c0c40c0c100000c442d100d10803411141000c1c00042c00080740e140b800c0340c0059002d807a035030030500c00444072400c0c114a5084603000800c001e004009200d001c4510518543c0f040c1020001d08a002d000d180030401402c00341c062030394000171000f046c54010416070004000d560721003101d15803540c41ca1070142085054080300782d030400002c002803030684d20840341290f074070314010082d141c07801601d20344651840440c0c8000c00070500140c5036402415030500b200c1001000b0004803040d501e40307003640da581d02402003074441d44100541c0ca02c82d1112802c8940100c241500d090b0a41078000d41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 539254883 1250 539253633 539253661
    0x102060c251a07020105090c060706020901110a0503130f05130e031c140a05160e06390105100308030405010b040e030a03050a050c04060c0609082b1802010503 70
    0xc20601e40c1a03614032004851088060090140e0740c02480147c480006c1d00d81d80380b5015201d1688140c007088488000703001503004150b001c2041c188008080007180c0d00b0b078102862010261920f0b040010754000d032100700c04524000d0005030400d0081c0c1410000425120b00b10b040c40c1211080d980c11030340350014030030070a4502060048400034020b015075203402000d8103058851140d00340100b800705519036118001c42e07204015511140403400700b90f9100700c800d00301c0c40e10b266420007010800728812950f181c01e003844000c5071822001a16075800c0000c401486030861403011a454407003842000107864001d101244d40004550380c89403501d0134601e00400c1422411070307002e03182c00b01100180744040058805e80c0300300e880130416607607004020829100100c51900c81110b04100503c0744600420640428600410000403020750981e90300d5210750010000282d00280072100340c1550b00199101c444000f02400203101051038401c9140700603c110310300905100000c80010302c84400e04e00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 539256133 1250 539254883 539254957
    0x100c1119060516140a060506043e040f0e0901090507140406080304060915030207170c0a05060106030204050a08031e0318060c030402010e0f031c0e150c07050102060c 73
    0x82c100c0c4c146129078202542d4012120b021030302c1e14144000a0b0403450188030311100c024800c401140e4401101200442d01440f81004911988550101103582c01e1755602510107050f0b5031800c14038290501e0a5400310080060070381c4040c0c4e0502041000080c1d010820310116070404141134400c4018200007000b5100c0341e040b00080348404100001c8541c0e00014800c112071001c0341100c4841d0f42004210283c0c46000d40141918005842600840060704010300e01e0705041c02c1620000803284e900c480c10070f08281c0c00303400020340110707091006151040f0658000c1403c04029454000c002c0721514803404059203c504450340800014038419032090003400f90321001058451500d40068000b004da0010b075016070000e05140d90702601c508022911007040100280104010040c00940000744061003c88008011000d038901c900c0340c9903036080d504030010131102c039a04e804110400502d0042c850380480d046520907402c1c026072071003c804451030081c03141d8044403401044ea03028049181865 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 539257383 1250 539256133 539256143
    0x90209040605130c032003060603040602070b07110d05070302190c0807090501090b09011412010f1e0509060708041101030204120b09010c1e0c11100c1119060516 71
    0x2000141c95000703502130610040346880030403224061034041c1c000c1032000f5414503c0d032402000801e1f005d02c4d108008e075510610801d0003514150b40c0c0d603141030b0819426180c180105440300c0c40030103029801d1044c1c0802760038a26003141081d000751030081d5500d0034442d5075440c040341d80c041a0180b000c0103034041c0143c400c0c00c00b00d81e121541c40c14240e00410007481250403e901c0d20340303d03942034945040000e04846142501441210380d000802949007a4505e120556640e103a4040311a45640d01503c1042200d2026203401c03600340c0701e401c0c001c1e2200107008810a41004040102c2280c008444131b03000b5400145510b4112500d10060f4000d00ca150031002e0703240400d91070301c42001001d260840c42140888000e000860f25984251141c1c106074800c0c0740040c034500a2443d0807441600c0110070103002e075500700301220762800030580c1407400400400006141001002c02c0c020030311060b5002c80c1060b1021580c51041804001e00042203000c3c0d00204a00041c181c0921400210706007070760354110b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 539258633 1250 539257383 539257399
    0x507061a03070e07020712031e0309021002150c0406081305101404031b0c12020d15090b0702060c1207030b040c09050a2c1305030a030b0127090209040605 68
    0xf400400441c50801c40b05640184921500855031a480030a4501ea0076450f4039102d4140b85400155011420946070601c1056078031440300d80507a607003412b00c610350303186a00900000358440031400105800189885500305080000302700035544000c1311548880100c5506601d445140b41050074020900e1441e080c40b030900b080c2d407201d11458070345075010714842e4070350400000c5000c484402c01d007100e000140c40c20901d90303800c101c2408680c03415603440344000c0402c00320b000c0c140d4030a0103c6810404000340180d50705184070402500c0394460f42c000680b030000300315a16004604410601c50a21400307044540c20001c01c1c88540290403c0c03228500040c000c0c418903440c41001080c0c1501ca2042500c0b40651940004102d000d81650f0a4011500d603080105060b801040c4007105801030803444280301d03400043d40100c2d10a01c042d20f841d40d481c1e5800303d5000e4010b00010005000c080c0055951f01d08291071200c04003078007101d0b1040380c0880c0d07009600c0d9003440e00002c0040401d030b8043e80d000981 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 539259883 1250 539258633 539258639
    0x40f030311190e09060d110f0409060e0303070305010b041401031d010504030c15060807120201020c130f052503090201140f04170a0f1e14030913020a0507061a0307 72
    0x100c1c0610080c07002c19125000b25581780010845e014403181c002800e080510a40e007815801d00040080d8650b10180010400d44a40c0d82c8100440d802042c4402c6150000710a0080c0c1c0e640c5405040c0c0102050a0458203003070400310380d40500c510359103c80341030540d07440306e0758415460701c00f030b43c02c1c41819807000300a6840c05040113410408074000441c0d091541e40600420f208061284a040d80e94802c0102001420010f4441804a802d4426410741c414010442c0b00782d0303241e01400400c2c0001440c04a00c0c644915824001d441014000310025010040003d6000d140d0758401084001c1c540303404070b108540e070700060700c440543d4440644180400181071101444030001072049070f520844600d401c4d203084030307c1e0741c4501040344010185001148010003050403410070014807a40c2e0400340b145a00d9550312051700b9461000310b24110741010509a1551174802c00f0541441c1d4111015807410700e0482000f005440b03495030041000da030301e80c00340c0080c450a01d48a0a106e00207000c4922182d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 539261133 1250 539259883 539259887
    0x130b06190e040e0114070302031b030603340902181903020a1502100b0d14030d02160302060907030309150201020702030313170705010c0605150d080301060201060509040f03031119 79
    0x2000781502070b100485c55010414a41c403901c00c82e4807804c0705116800881c490a500861640c0c000b80560342d0500c10f0202a5860382805400c00703010450101c0e0496804920945014081e00c05501c40032000c0d1060202c664001c0b10002c000d20710001c229020b4020445851300201c01060329000030390420249480403c3d4100c1601d02c2a850700c0091302214038008014000340251a40614032030340000c40c6401400c0012030410300a516906001e003a24240180d46410790126081010080101c2114034104000e050301400007030f07009845031b0042c3c214070f030460f00c02500d00080d0f0312800d101038100c00d0310010a24030039410b60316a07030b0f4003c00396643d9040e42a64140c400340a802a0b200049080710340000340c240c00980d01c02141c8041c0c407001e043c85803a1b180c01000300402040707007142d821001c00619160b0b5442c1c1d544d01c3d070580302e0075595481e5410018020301712029504118050f0380350106000200300b040040c000b45950520700818030325080c201c50071550085000301c452103100601c0003000c2d95 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 539262383 1250 539261133 539261141
    0x20f0d05070311061f1a070204090206211b090a170111040b07050f060411010305070309020d150b0f010207170a1403040e0703090f02010c020f030f0705130b06190e040e01 75
    0x80001d01001403498541d03104032009080344442085800c820440c100050405400c52b4038550300003000c183c2806030900180741110040d00c80480040c07002002c016403946001107008511095405250411200d0320214040452030b002d0400810030340d0720340110110b0250001211103e041020544455554820130a10340050108440f24051140c100e400303008001416445603070090102c44504140c00015401098042d2400d4101a1034034080b80158981002440c4111322820207050387c0e0b2001d10450702111407444080c0c0c80b07408120108451603a0000b40e02090f21100f541204406a0868019142130742800c802010a007196441050b02280440a801250f50000c0b410a80e941c55850803030888500e084c4c020040b0030340003420405540301d0301c030a80307001c1e1024111180040c104400030b840c10841310104009944070110600403800c0100056040d0080c0e0340d0180083c02001001031340500496a011542c1850300b0500d4059030721985601002d00d2001c0d1041180d032100c0500c0320701030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 539263633 1250 539262383 539262421
    0x4060806030c03010912050705240604050a15300807050c030a0305030a020c0f03030c0711030d02060103172a160b03010b070f0203011a10020f0d0507031106 69
    0x90140b00d68500a90406008002c10b00c0d600210319149944140d10070380d583c2d040703070b03000340d034544500d2807450000030354504400c84a890210300044e042c6803c3d401c0109031900240400c24442c1131210b9141d18070140030442c0283c405030350040c01c110058030f03415200c1603803c180b4150804000010310050000e103070003c08001d80035001341e0b40760b0b15402e030a056985240000080026108000044034498290f020f000240780100c19200c2c50f081c0c40303580c9403550b00700781d40b41c01005000007152402c205102900a0a45100360003400710f41040d2040a92603202c1440007902100340e49400c00304a4020404940010a4800041c2c016850482010322805c0740d0402145003031203001500b86104c01c00300c3e5907000f1555541c2d081803560382050310f070452942100f0001c0301c8909a011303d41c001a40c00b805440c0b00068000c0c80c40c07001c2c1500300108140108091018001d542040c00e2121090002181f4402420f080d81041a40c03a092443c04641c018543c41c00c1055500a401c140910710400c444d4208030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 539264883 1250 539263633 539263639
    0xd11180108070b0c101e060303030b03010e151f0f080105010f080a122312040c230d0c0902031503010c05090f090c07080c0705011403130b09100204060806 68
    0x20b050b8851000d15064840c0031103201c03040e400754100055841050f0000410015819440b83c2e251503500d1140041c1e580380d03002180480d884044d04081c9060034404c00c05850600c2c401040081c1006482600d80d5001602e1400d001c05d20b100040105072110308690014044c0402c40300100350790f0400c8074003e100170b0003201035423500518005004000042c60601040d00240034100e914034402055540388000c03109450100700c0e10070306041001c885406408445003042207140306162a281c8005900500d41028200640507031560402c28004c200c1e4250035103041e103210106078090f080c04d801811060303204501c0e0382d000004000c00c2c207250500062107464194000d01004510000940d01c90161150894001e01c0d4275954007410320f01403818a80240c400140c41d441c259040e12241f01c694041a1040c2c102e40c41b10134204071a5910003c030080402200784083d0440c14100b440c001d1165020a000d0284040e0b00c0128003820001d01c01545142191749007156620341d00e1101900792041260881e01c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 539266133 1250 539264883 539264893
    0x2120a0209130c080f09010609020c0a02030c030109030503150418150e071a0d060302060406170f01030f02040b032a0f03010c020316030309080a03090b06030a050c0d11180108 77
    0x82e00100b8011000c41c40e03029100d4402a0b1395450404a42d0080144102c003c1d40d02d17041c1c0050141400d1000341007841d10b40000d00710112040c01814503001842c04400e019a2414503840042640141500e4218606c0291682d100d4140c43c001000303070080014801c14a43c1f8020b1070710401c0881540030150b0034442c2018401c00411208454a6540034859640c048100c841d070140c1c4e03003140d1720041c04000341c40e010000300d09449801180c40c541040e001980171504168689250000031002c80d9404210018154400d40c10741d521001e031882c441e58000d000d10344030045140c00d96428004440600602034030344e101d01040d549440c003401c120408030750180c580c3c840d1072117185c10180500c05461903150000d52902030703200188a07019200000c242d04040d80c0e550080d0005aa480080a448945a50105000a007810421664000644828032a42c40741a03120001200400c041826401c00c503a00c5011400c0b5040101c0c10b824a021980d80c4032000b01c841074031884241c20a01c1c1640d00c4002203078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 539267383 1250 539266133 539266159
    0x8180c03030f12100b0a0c1407030506040506010803071511090d08031602010203041214040e0108010204050108070c0f02190e0c0301061107030309050609060733020a0909090602120a0209 82
    0x41c0c044d0b42c58040c0b13012030f850801c090074546000340c00b421015803040408124418656080300d0a00343d1680007204c050300844140010301504100260242c030540025510b400015a511406004034030340406520703454141010707568180806480800c1005042c0c603c1000c0ea62800c20910780c0119441c6148ca1071b584112a241441442928031981e88203007001c140c070490a178150ba5107500050801e503661000c000201e20140f01b081d40174003c0800b80c002503240e07403e160001d170000302d00804410410003500400030104560000c4c44081c0794058510703040c4107074075110744102e002e01500302048903001d0400744080f00f0030300002141256007640d20680c565000c0c840d1b00340c82e03440c0d9200180000d44011024062403070018014111020024240c40c0b80200560343c40d00410900c103880f0191021403d9240036404002e0f034440c01418000702c04624208018030301070700301b0000d40100b100156440b00c0a40802545a040341d0f0f4029011510350020300c5c0020700381002c2c0d444100010f018101c85d1441c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 539268633 1250 539267383 539267401
    0x11031c11131a04031a0402150d090515040f060b0a08120d1505060703120914060411042003060303070501050132010923120304080106080d08180c03030f12 68
    0x910709417030348500a107104140d2020960030010001d08142e80c400c1d03507a01c11880000142e4014003070200e400d20040384044d11340c204a42854403000c00c410105014204000015001112540c0c41035409507001600c500050013190002015801c080214425004c3d04403625a41501070210200c510340c044c07141541024030004640754900c0f405030000350601074240007902400141494500002c2e0005800c9610f440d191035041907402c82e2000340c1c0007070f41400140060748902c000d4810090740c080c00300c1e88a45880c813400019511481180c500040045001c5a509004580681350040000d10255854200d000400c6110f0340c90100d80074040540040c0816080d40801d242082c141c440d0440c0e03c0c41d1188005028880c408800b1300c5c8004485042e13000d5a4441181201d907005400440c0c0340c1b818030102500b12401900080216880030b0b2140320110780c07101c06c171540400c1c5920b00c004407900c5496641e03d04030700507440d11fa00d4000440e40c2d03810010b0034005094813440c0000c084000b40c950042d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 539269883 1250 539268633 539268637
    0xd090507050607051c0c06090c0e070c020f0d212f030405040906020d0f0204050102010f050405060c16080313020a09232208071211031c11131a 63
    0x1015030f04003d90184402c2444800d4175040e0701c00d428880170f595134980d078100c101c888000d000c40e58135079203160034002c5001851540d503010300c5034140814010a180c00154200c918412411310440c0c1a00c1c00e0b2080002c0600e00204180809000186c928040300c0080c08101c0000c0740459441403010406440110800710509070b1095a00511300d003070f04180c10f01c40a0f000c0c440c019141103400300071451000500b40708440e190006081c0050310303181001c00080c01e4500076010041024106014840480c0000c80c1c0941c02c20311520010740e450080742001102404241005001c4100100c1081841c0260301c420f400c4082c0b080700c90441e090b4039550194220b0700140d00e0101513000c4500071014103030610283c00c5c2c211130320058130341130700791203080b8820b000706480380032103280c0c40204448081240c00c003000321a05081e820039281e00390b000711201742d4034040c1340e48040c200403040d03000a079010350781c0d4000050340003e0f81c8075030b0381ca594a007068a003270001881500c0759817100e1070f1803040450480003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 539271133 1250 539269883 539269897
    0x80a02060c0a0c060c110f0c090a1e02030a0b1002061905010305100c020304050a0305031c06081203100e070e121b040e010609090b010f061409060c010b060d0905070506 74
    0x30340c3d030b030440029107a00d00240200501c4009000740b4009800e0460307820030056031124545e400411904280c030050203d5410090504200e250400548080c1d040e2003915803103140c60f801e400140c40e655091658800b5000300501300f5040380803003107030003103182d40428100e12614881681101c580c40c10240c2d2400c54209200181043d00000f94002494413035400c00f1260a40360b204490500d070f1141c1c00208441116401101d4990002070b040c2c2e0300341d02072964050703c040850400c1140a10303240121b0340720058015003400000000000a4000324503104a1028181d81c5c0008500351411800c0034000740d885004240c401c01091411203506200055601e200c4000c101407000749003e450b003403101810881c50845030360f5498410100f8254481c5c0f0800b41c0d1540103008000c40742d403411a61610000f0103400400400c0341965a40910380c1c03c0703108840340000300352240c030750340d03200c047c4443d0042130405080e0368055000251040040e40380e4220a9195004009032070100c0e40d1481080a1403040b4a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 539272383 1250 539271133 539271137
    0x6010503011203020705150a120204080303011203091e060206060a030c05010c03031b020706090803120f090f0a1104140f0103080304080c01050c0a09090506010c111c080a02060c0a 79
    0x801405104003005101e442d49220f80125544152190005143c400d820290120500c1000c6405010240d0090059401300d4003460118a4603062810894980c4030500810b08581c0034a541070302003500c01d840100c010000361111404840d0340c850050001d00d518410341d00180320f650007143c214a0402400401c8030384c81112513900c14038090040d50504481340e820303000c0c903581d40f1040594105180c0c0e0503c3d244496130182080c0fa041c100054048100f1382c00044c0507a1080c402025034241d0448055008200071041911640d03840a0f554600513400c516840d01380200c50b140d004005d000301030201d40500444061011140441a2449544044405d03881d07038441c06c0010404546800000c54105001c3d0700005d18041c3c4040f6110b0950b24107460344000c1d82c100182d11950f881e4000c0050001d010404c2040c000d90400200081c0b0310320041c1805030800e04411000011f90f07892584422441d402a100702c000c04a1034201084680c00080d042000f40c0a542c00082d560141481142c0319520a5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 539273633 1250 539272383 539272387
    0x15121404030f03090c14030d170106120b030f0601060306080a230a17030703050106030c020a020f061306030608010605030c13050907030c03212a0606050414040b0708060105 76
    0x80e407002c441c0b4824816001c0285561020300d000410152a5071402a110007081883c2c1d8050010038540313001c848180308000c02c40005e10407544426a080b2090440310749182c18506a41c1c4c07484440018207040d640c1135814403540010201a0101260440c1220b0326500c0801180e5960300200b0b449140c6141c2c010061a44144105014080060483c03c19502c40049400810442d620075610490403078820440000200400c00441d5050042a0151503645010f00c8440103202c00650b5500120030000d21481d00116010b80a40701d0405480030f4010075140341c1e0000307076283e10241c001c00d02c6020307401d125400d014011800e41800034070540803000190003040748100341c03074910b0002c01018080250302d00541d280000401c0c54023000c50059030042074500e01ca400b00d00740c8041e2003031500c0e003440c040c00079034000300040c40c2c011404400c00801107144110034031603601c1e01a009010302c0d007085512514050291141d4440002c0e03481c4110b00c0b5841c0d07000151111403080c0c44104040b2002c07400280c00b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 539274883 1250 539273633 539273641
    0xc030c100c1e030801090c0203070c050907030e1b130603020114070602070f08030f070914010315050a121a0c0d02091305040302031321060b0d05010204151214 70
    0x1103a028800071900a5402140d0418210b4004045411101c0c09800040024005001e80d68451140c0840c0341c200b40000d42c40e00105030356426500c0340074031a0714827521b0704100044a0324029089052800d07840c05c151900000101402c141d25012044250300958044442d0b264803070b01d030700c03540e4141d9070146c550310385000d118001c030f41207681300c940100c031216001c0c8642c4c1700041318202c00028640c400e111158507442d115149449140c80108001d040107030340e80081041c040e1014403921054400c4c07a001c0317011719031840041030072910b5610040e008000c000c0d0009550300e000c601c0c40500c0740b182141c045010100c03512000c06000c2a182044c921108000096101a10b40e004104101e0003512200030442d032251440c00302c1b102110103030301607000024001030101560304034801511002644000120300007079409031242a031480180344540c1c400514400f83d44042e403900200380e02c00c0c0299a503c6c3c88048104017072704149250004503282d01c9560000071400d0160121403c0f03080141d0030380c2d9607 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 539276133 1250 539274883 539274887
    0x302071a032512020705030d050a1406042f22141903061a0f01030603050a020d020d0804030807030207060503160311220e0f071b021801030308090c030c10 68
    0x8282c0341209100d10103400031141942d80c00546a054004c0c00919269440407000b6002e51b00d00034695141c00c4d01d0040746040c569600113505400c044155000a0960b041d0292a44e04090b80d0a014080d0703c690442400142086002040c4141e54444034240e1070300d0f4030421076405411030240320b035071480b590602d04840c1010100654182c1208030f0043c3d1490781ca46881c41141c245060811118502c0c000c2c1400506181e121040c00344020301c0c0400000b0b1554035055140c1c80c0c1c0410091058200b50040400e41da07034422841041c03a0446a802d0352190340385400051640000b20440150213003807000100c80c1e0040e0103880c420f8907211190f01c150964150110000c14420340f200d00541000e000d45910b070b042c2c981c0341803401c05191444541c02130501c1c091403d0b03041c00800a5911050007010041055072100300103098a414040b88001030166100003001b280f108440c010b141c28104000009050b44640f24a000e01701d95000e54a890f0700d048281511501483c0b10f15801213184e68070910114 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 539277383 1250 539276133 539276191
    0x90f080904110f0c1506010509040f0b04060806160807050319060801020d14090d14030a06030f03031b08010506031909020d0521040305060a0207110301090302071a03 73
    0x300014400100c4034600030508030150000d00c0e40000f160004101500b08100800041c1d010245982903c801e902e000c1c00000c1c1540301c1c05c912a80202e888111000134031005410964680e0001401880142c1c0c640740c040e6503904048810f10400c070b40d03120100d001580500c00b414006c032042e0313565600d10b60324404d107440030701d402c89158184596181c8000403404020320283c9000300110380c01007044107102c020401c0304540a04845070340c3d040380302e50100058005082114411610300c182c0d40300c0d03442c5034030b500c020a1640c2c40030740400d40894180c070030154954414440d042c8580450b110001410700300300d80c010780c240507c2c1e8100750f080000c901c048480e190421003107031341c0302c0e4040b64041c4030b1b601283e4845280310048a80f584140058500103c074602e0780c442c0d810810145504152860320385603a0759802a150460407a800160001031092448151242c1c100240080c40508a1460025903a154074410000c601a015902800210b0710804030b83c040c40c001c0205082000200820200d0380b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 539278633 1250 539277383 539277397
    0x311071b210b181509070f080d0e0105040806010b0706061401210e030706020c0c0d0309140d140705010306050d03021b0319030207051005040e1326041503090f08 71
    0x41003c80784868848003c1100fa4441029a194580c0300d0600c0c45480e45012600d800c441e101c01b070f0020040c07159a0000030b16444041c46481c140312010310590058501344901d400001c420f0141500100390b009250009141c00b40c071580d8100a00c0c0e6969560321364580a25102a0000702203014004040040d007101e0703110151541e0001906000303414a00d03286902c0a2411581541c020615100d48031081c000e0001c1624140c44400d6841150f680050146029001e0040d2541d034103020030000c3e485141810f11110f50000d26080381205200710036944200c0d5205a50007e42440070104a034103120602c42600c0380e16030010010240c02c00070900722541c0003e11250944910100f00000d014000c40500307145000747c004d0080b450800c41030141810703483c1c04042c10b00c20304010810101c0661200d450740500d41c00c60f044007100091526940c00800da06210103810144442550440030f41401003045035813081241082c202c40d10401c0e81502c071081ca003d0300456411015801050080008010b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 539279883 1250 539278633 539278651
    0x2120909130c0b04030b0609070801030203120708041710050a020412140127030305010b070b1612020f040603052a0d0e01050412110105160f0311071b210b 68
    0x507448112030002c51300a9841a40d81c040e102081c080182044162982c01650500e080e80740d40d03046401180d070b18128100c40c01005a00010000309001e0b9890503940a0003544020000314044814169035031211000701c01206d601e000003003003014003079100311012582c1c0a4000c0d200d000c2c803038943c420001d01100c0c402045540741d240240011862035107100c60504160b2220316000000c1c2002822184160443d040904c03082086c400424166014240c1c420000170300300d0064040c0d010b0480c0d004c014205841020ba0000c00e665a03191681d60180098590b1981d013008281e54000b8004250300000d0b402070280004840954110a1000000c0a03030400e10b50022a1100c185041103003151001c80c0c1c181d07400382c40803241b5881c2d65400080c034130920941c1e030300a10180c01c214000084c40c0c501c0710303485400d001c041190f4240042c041d412441240c5803007101b80f501c8140e0390600520044120852040c0200c02c0d90b80850850310b20003288100e600c1d8007980302034040c2e8555605107124005012075038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 539281133 1250 539279883 539279903
    0x152106090c0e10060f0e060c1501030b09100b06090108060a0b040f090f0b0a05090603070b0408010606030e070303020d05251103010e0c03061f0803120402010212090913 74
    0x208607610090402400a0703030200c8036074500507400090040080c1c0051040200e4880c000d00100d601c260406442e044c00c4814a40c1d8840304800985481e1b1110240e0040050b510000403d00c1f000c10f450b45d100b80c1c005000c0c5da000c0303a450403024040320040070360350b40c0c4424240141e40340e039441201803c0d44808081c0420b02441d03221511448650003541c400304110114410501446056019140d14001000c1090001c2d2040d000040c3c814091030040b01e000301652400600a5030f4104031000003821051106540c1d15200c0d4049406480300d40142000b10b4107201c0342c55084400001e8010440c0c0e0550301800c49c4800c2c054040365036900c40d103aa44043c0d01406006200211058603900b1003a201d640840201880b07482494203442074454100342c17035080340c2c4d000e80c1c1a480104038283d010910070034464240d07400e82940d1041500d240c00c1a0124480803920520b010b1440360540d01030b5000760220703100307041c1c800441003140c4102c0304855002003484010030070190f500d540e904089442645004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 539282383 1250 539281133 539281151
    0x61b0503040f090c030c0e09130303060b0708030402031b060f0f0f0c0109170c07090f1121010504020403110603040c15090306050109060e0c0a05070501140a152106 72
    0x3042c001010381028020f00e9941c1c81e403216644d01840b0b21300e0f4403c0103003419640300611100291f01600014507039208031690910a00406100b94400c5c00a040070300001900d41003d400c009841c1c2d0000c5804034064480c3c0310070325040a03255900104061402813000780780c201c9001764001c0c1c9030807410788400030030001d1020050480448000e005c0d107074154000026001180d081a2a0402d00980f02c040e6075481000b441a0302d0b08082110307400e480050501003016030900740c43d54018032085c0c202c4803401c4008070b00581c10840b61120000c21061000032a00182d0329402000120710440c0b1006000144015032490582004c0b8060340d4401e010310b0302341c6503da41d21500c0d1174601c0010550700c0d00003403c43c8014400c00000d8418240500440c01e02084002d04200c10605200000f43c00c00408240c007007060058240329038120350b44664050024803100d010410b076607004030781c141c400b20300c50b42c2000031905405802103008002c41e100340402c034400140d109184001030074510b205403645038850f1120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 539283633 1250 539282383 539282399
    0x6010b091309050d03021812070603020c0c0901030812010e090a0609020d0204090b060a0801140103020103091704060201020a0e0303070507180924150e2706090c120106061b050304 79
    0xa0501d10044e503c001d80e8402c0403100071000080700e40100c1d0703c600002111042d0b4050001005000d945807403d0069981e0540382d80a881e1000000c0c065034072101d002c0c0044100031a00000c1c10361100140101c0e04a42d813030b224040e40c100002c4070b050400382d210403518000700d02c003900031080c0e560001e00080c612a2081d000f103810340c0c580e604203480003c1c2c180c0c02d104050410f8913500000340082e000800c4401880640e00c901000180310283c10151555030300d0341449034003400010101d40e42c2c04200c4e41c0d0360341e50700d01901075000100c1305004034071499a003000504010003202d80b400d41c0b100c05401c083d41480b118010003555200c509503802c0d170b80c10790440081d07444080079509a0440c0040034540005800c1c44094035419440d4402d8103032100010032000e040c1c04800b076045880d401c085440b5004070148c440d0300050080480700395203e40400d00c10303040e40114181c0742c100700540d0001001e190b8003507e1800c1e101ca61044100091180b011003480084107085600c01b103204109803031500360340e8002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 539284883 1250 539283633 539283643
    0x23060907050c0a0b0114100507080c07170c030111040506093001050f01050a180504030513180b0405060d02190306050f090d08060a0b0c0a08040605071406010b09130905 74
    0x807101076490100500c01e40158001e40a03c2c03560403544d02c1003034215021f00070103038041d41400410601010519011402e07041c4030100213094bc407103c59076001c0c0020009559a0b1544601901070f510b450710f80c0582512001c216415102e0180c8075a00c0c101da113205110503001c6011005a401c0c29140841c500c403019000b40c2d00b40f84210b0b20007c034050604030030050b0503c00c180d00481c0720b0420880c08000341c070740290250303c004158800000d150b0392039040a50f4103205408200c0d0a0142400011480144003d20050201024403040000c012100180003c4807400e4800650203146107403210010301e450081c110000c9044801122426982e13038819040e100c0c01d40e031070145040e6078401c0081303110042088001c0c42c003032441d0005807800d013000842d402480f9401041e5018500080140160030204004210f0071f601c00000c0741d80e581d90321307001084c6402202c400c91700e1581103000200d00020005469040ea8840b00b4441e1074607002c6c0080050b001c40400803103091540307801c000c2d004507006001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 539286133 1250 539284883 539284903
    0x30b09030406020f030a081f03020604090f0b030109020f13090501050c0a0f0516030c240515010e030d2111070311061504020c010b0a090f23060907050c 67
    0x10046450360b041820203420060202914143e81c0e205201c455016607020507580d0700015080a00014403030911080380540c1d0032900003a40017080000c000030309504503030000703980414032107042204418a0003014242d81940c04003951005841499004901d0700548421450501c1d03280020000c0380d0f80d40301d03400e4600844441003a894081901440e840c3c00200441e4002402c0c03600610b44101c4061003d010650100003900b0050340c01a01400c2004009030f00890042101c82c101c0c40318801900c00c1c001d804111044032200e220f9044006095001d04038202d540e20005000e082c81d00b1200c0c01c02c0b9030000700c82c01c0d402882156400d400401c840c9034071469004903119040185c1c0e1388014200945503014096410400c0c0d0700032010024440c580440c40f03102c20604550140e5103240040d80c2c6800b42510300f0b11107510900100c00000d100020303601038031906100c08410300c40e000503103020012140a52046c014035040ba50002101d601e48000c40c6540f10a480c1413032421b08451100c11031610076100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 539287383 1250 539286133 539286151
    0x30a020406140405070504030b0c031803070b0601090f0f050d051e070509130f02090402040605040e0705040507030e030406050706060339060e010e03010b0d051c030203010b0a05070c030b 82
    0x500740c10310f05260065641c440c1140c202240703020f02c3c581d9180600308004044110038200800894076800c44180198080300c1c140046a84882c418145000c40c000156902e42c04264014030000d000c10080ca039181c200c8003000f50780f6150358a40b10a00c4a464940c0c1d004540038024040b600c0f02c105035943d80030301c500307440c17000502413a41000c0c01c0c486c24810290241714051244609900001d0252881d400c2e1164180c1d0110100d032242c0c40460007412031a0401e0340d0241c1000024802030310700041800441d0301c100c6081c0295107a080c0250103c2c1c442081c10700194000f00414465180070300d00030324030030b03210703250001c0e10070f99940b22100c2c1142d44114500d00c10013101c00c4c14400603d100c042d4030b00c0701400c5461042e0680342120250080d410304146505124521490350300c666000e6120f02181c074405030060403130f0100b51400c1c2e40c403060b04000400c1c01804810490565510074403d5a058419650f50a40340554009041e503141d04400e00460704015400400320001d1100c11035180986c4040c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 539288633 1250 539287383 539287409
    0x302091003021008010602120f0a0f090315090b0f0906010302060328021c110901110129090106030504023718110f030f0603070305030a120c080405070b09030a020406 73
    0x101b00d000307007005003401202102107014440342045120b000212034403001c407800d002900b42c2d95614190b0303518045a1000d0202ca90120090b40c080c580c6404c040116481040e5030f030b845586c0d1400c81d55000006039803155180c1d102800600050a040c8004c642100102192072200000141d40b0030442e100f40c02c2070f00400d60007168091066507048400c01c2440961541070100c1c0f54544000e500c50b005034841e15040003000703910781301c01400079400305400134106000781600c0d0786861403010200908464460158000000000d1002e100303118031406194002d03c0200f03104100b0b5000480d441c494a40d0100840b001c08a84411450750b040c10b01c020312510600038501c4c104401000100c80641d20301c2001c0c0c0804002c1201003034022400c0741c1c4e01144650b61314906490f81d5006c40c2c034128054100419900c00000c1d001242030700601e20342032401030304105016090145004840104082d40c005000394007420050000f200054040c0c40229009801c890b865412500020261946588141c85032404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 539289883 1250 539288633 539288639
    0x40908070b1e090609060f1302060301091d030f270907020f0d140313030201061d01141e04091e03050d0b061e0708301609030209100302100801 63
    0x88082c1d80d80465070b24064150761510070825900c0310002458050342e0030789040056044141c6205031003409030040d001e59242d684905520340140f00d0a80b1180400172944001511040008116a42007041c440b0140c1400d0401c58285405008100c2c2400400c0c0c01000100680d120101014400e40072070b8002d08110001c000e255083c1070900950100304404158a40300050225085980201100c0307800d20b00000b50b41403c80c014041500a07145040f500304004041c6c9058802c4d09040c0d50400096403d040710410821100c002d4109030740030040c0780c010307a10406141c60f6001903695030142c00b9066a00183c07032200f02c020340d0402c1089000c54800701d502c40010f01c642c03040100700c142c151b400c20b16003000c00000502403c00898640d83d6118000b5551040000340c1c001d84410707141d40b13441116403210000105000c001000e10b81d0f40201c1082000690700c0108030070815640d6510346850b0001c5046800388000c561b0000c10582d2600311110300000140c8800784000e03240c4000784d80e00b0380e180d41 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 539291133 1250 539289883 539289931
    0x60e041b0c110d06020d140a052215020f0c0c0301090f062003011e0806011a0717031810090201080a0209120f0604030906021203070f02100e030327070302040908070b 73
    0x10107040050f40078600344c104515024050782005c04207140107a00c1650481d50300d01603141100400c0c0507148140088de42e0b01140314510b01a01008900005541070381071400141800c903049200f010f00004100030800f80440c2d0b0f1680300804400a03105644000481100122543e0348280d0124140f54960002140c0060204104501400f0402c1c0070345100d514098100c41e0300780e21880e804554800c00500d40f0200300204d190381da002007010b0009512840c004200407102900703038040111178021801031001c100e42512500e800c03140e05071030305000c6454801c406c0009420811840340c000803990305500c1c0400040120901e86000f25006002500c3c0918008200c4080c1b40c3c440c000f9507000b0703258008581913901c1980c0d030003461031821144900d070b0801c08138900b650f800b00d1960180d16140c1c00d04004503011006510400c04151000150309040d10301d18171040720342112842c1030300005003e00c0149410340044011600a1060b20309033611516500e01c5620103540070b211402d284960040500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 539292383 1250 539291133 539291171
    0x6010315060e0114060313050a0b06120f0a080a0e041817070510020d0939030507031104060f090c0215090d03050903040906060e041b0c110d06020d 65
    0x850b480942855458101100321003900303c10158410040880001e02c03100045560610480d084012907420a01c0c42c1041c8d01e00031030540d162809040821b01143e100c2200103506480b2103004001860703005150707200c480190304031f02c4181040100703800041d180b581d00c0c2c0c0500d0003142071a000d080422400d0703180c4815500c10040d41d00303c0c02c0d4002d02c540070116002092035465180980005669415018015002094010001061351002356012100c8001c07419003041000da202085d0580e070481c104283c1038950462100034000d61003188244009103c4800c65010764070060404190726132949220044001241c01003044250787d40d659a900395410801041d4034401d00d40d0b4005c99040260001d5181c000c400700354414582c0f201e000c182209410003c0f18020490440c080280a03221180100000c1c240c440440c444c40c03d0400302c0201340218403040c89480010380b60f4040702c281d01d43e1080180310201030420b50210103010729002141e01c40c0004c007265100910005051441e0344143d050070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 539293633 1250 539292383 539292389
    0x30510080c09040b09120d0c0f08010803070f08040f06210506010519200c0111030a0215070201020904020f03091005060f0111010b0a3c05060c0f0601031506 69
    0x140d10401c0005080d40b203034104180c005410980e02412540c40078400d520385200000203140d44440040c0d4494003c0540d409840085001e5071100c40c03030450b198048480d40f100380101841c90300100001d50000c0c101030030085500e0b00c0354202c40d062980c0d403505207000f11800c0e03100c2d0003c15404820312031001e00324850603044462040e000c00c0281270240000301240100101d00c94150303401d201d41007555000f446070ba13000b03070003c000080c20564130805c4280c03070f103002416460115141c15858002d0440100a40b02401600d500911fa9010301920403c401e0744090300d8003055540c00c100c60000f50710b41c0d000030f0291403901401d8540d24203014800902d0100a440e65a192a20305014481c503680c1e04200780c080002c003482d01d0305c5001c8912121600500004664551080c000c0038005041c0c543c10140813440502e483da07481cad06d2240444180140124040c0c2215400c2c0c494505001e10700d441000f03011243c0d02c001c02c85081c506822013162a04c5001c0e041624248200700380a0400f5296005020107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 539294883 1250 539293633 539293649
    0x602030c070605130b07030309050a21030608150618090a12030c14030c09090f06030f0616030515040c021501090b0f0409171c0c050702090612030d0c030510 69
    0xb80c501003c141c01c1c1102070f85d0083d240343d4240050003109140c03094004808140d00001618414207280c0317010b0030140140c80b445190b1000c030740003500d280d90003845000c089600b95030203041441b502218035182d5101c0107240b15400840c6085014a0310500321305d41d0311441e0300b80002d03e6140801c0c1031070b402c04036121001000301420b10801c85080c0e0342c80700507000ea64640c0c20300b45460340c88400e034220250003500441900a0300f000e0811804414040b095401000700743d082d101600c5c1a01030031911004200c035055054108004500c000c14840d0703000681c000d1003088101d5820300e20301d0016003034500d0700e11103c006901c02d118010350404880402401403294000400142210601080c2115406030245105a90360011213080c40540c2c1d240301c0001190784030f241d030748803010340c000307100f5402c020020700e01a407800382d0000750304c0c0c001c60440315041c2d0010705c0c0b880c5980e1508100225100303003000900d018001130180c0e20070b0780850f024408030003009e900e01240d90300d0310340440a41c90090341c1c003200e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 539296133 1250 539294883 539294887
    0xa12060243110d0c0e0109090b0c090d0602120a0509030a0909020c0c040905280c0e09100614150f040e0705070804090506010e030d050a03020c010608070602030c070605 74
    0x60388200c01d0081660038240107880c10a0500740341452218a005804019040710040e400349041000c0c91040740161030001c029402c10b0b0b602c4038000c008813404080300810100704000031031112900c29011700030045008141e90310895150f0369410598006018510f28048070905101100c9414042d240c3d0103000d540095003054020000104650258031542801603800508a001e85106007c51424a10060300610101070a803401d290345000319042144203640040c3c0e014410341d105d00c0043c2c80e49401c00c50385001b840c04c2412324500464080e0039000c0d1f6101d040c0301044a80c000707000d8080101002044901403915107014420304110740518260440b400b04000c6c01d501e04030009503001d444490312825036540e18400d00f0340341e41c4503840001c2c1c44a0f10210300080d040107182c1009100300c00c00e981d2512001c10201c14555901c5801c0218004201d0038400241410320039405030940041c803100105459607501030380d81c1800000c2c1c100d480142c000003461054a031007005004011311881c0741c114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 539297383 1250 539296133 539296207
    0x3002030609090c060d0e070302061b070f03031205090a060f06050307120b01061b0f0809042d0203070315091d1501060503060d0624080a02010504050603060a120602 72
    0x1c409205145e0300c2503481d60354010042c04444200304103c091580640002c0d51079507400000004095041024000c03482200e02c0400c1b0364004465030f201700e0768942c03600710551208010381000340c03400514481c813520800c521500880e0300744c000d9035040c0404c01d4001408a0030b0101385810f01000360401004c1c114884122400500c0c0501120304588081c0703411f0031200e036a0f04010320781e0610054090b00840380e2050060a00000c64024602200121000c01c0360b4041c0c0110400d0420f801007149035510004e5145a460460540095a00c0802482c00003504503d01c140300c0040070043d007100d09a16950021b100043c0311501d02000304080745402842d40d400120803007a081d1005000340c204000300440400d416403644041c070b444013a03121f40c060010070403404441c0d44240103002c20440c2503100c0040011416030209481680c9074041c0d4540e46882c0c1031000713102d4503a0002d424a07400424440f03000505500c6100308078022f034030482d40544e9804a0342c01c085081d07000b4211740800c11984a20301 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 539298633 1250 539297383 539297389
    0x20a0602070f1a0c03031801150803120a021605060a11280c020603010303080601021c02070e15030105100603060b1305130b0a0b070303110f0304033002030609090c 72
    0x2003c440c40070704551400d40344042001e04a002e2a40460300c584400b10a000c0c4680c0030f038540760702040084000300300000710401c440d4030100350351098030020740080242c41111003c007400e46502c400381070030140c0f070070703451483c1145083c3c03507a00c0a40d940e4000200b4400010a180030f42083c0c2502604040e00381440c02c88421a94440c22403110000010341100304101801158034843c2c00741c004218a0b165a564140540420b9040314510b006002d0504008001c00f100c1c06070712044046c650080c804203080c040c504945000140078020010300b40109440569001d0081b50304c2540f18400100c00c3d140703030150203802d844a540255801010070b118135003110b811001c01d1011150b0481f580107848159a480400400654070a103802c00d95280001c01c164a03090024001a81319640402c80ea01c0b2058802044d4000d038541d0f855868010008140842d11560603042409200c0f00c080e421604d42901d55600c1e1001d40504422007074002c0300700b02d810701d09456403503400380d0104050440c8007504d40c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 539299883 1250 539298633 539298659
    0x20907030f360507091404140d021009151506020f010c0c08031315020415110d11030c01050109060302010e040902030703031103040b180901060c03080726070c020a060207 75
    0x14a0070003522008400140141040b620000b010004400c01500300240210f0b9410541101e05803904051112603c0423414005078650380000c2c01e030f000d40550300c3c0111100003d030004070380c240d039150321000480755584002e1091130342641028000c04a01c0c0d00e401c00c0a401d04c4402580c0745410392510aa901c581900078900801c03055004024680e039031755040d0406d0310402110400b400328a11900c1c40d45c1c40d504607a0040040d41c803071003a885500b1201d6002151032141d4044081001d81049008602e164000c0d86501d025296103816207050031420903000c1c1c21600d007644212a40c1d41c0f01c076420829540c00000c5c16064000036a018030442c9925000b1030760729002c510000742006050603542d00958018070584000e0045440302542e41e40c10b8651000003004e10040c1c0c10f2040b05040c0000913464010716880300d4440d4161070b02420b0359030300300e8103803809456882409580c0d400402d201c6032542400d241d0754411789058581440c6982d650041c0030403955282c0205065601441d400c1c08600c1c002c400c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 539301133 1250 539299883 539299961
    0x3040806061f05090a1206061802070818010c0206030f01140103020c21160c030b0a060f0b030c16051006170307061104030206131706071d0409020907030f 68
    0x83c102d599001400c04907110034959071142e0000000101d500341000340580020044a00106c1100301041c0ea16200f54100c0c840c0070f000500d0000f0401c1152600350200c108403c007000c0504141c2d85602d21500414003e9208480303d00700e084510006000d030825801071000107000c00c2ca002c50a00103d03240c01565643c00004113400038500c100e030340740c44442440840d415603080000348e407003940c002d00e030031788001a450100720f84015010000504100c5144103003070032142e0491145880341d1400b00d61044950000e0f100c10784d07458081100d04065004840285140c038443e6000b003102040c2030310b0340c40c112120b5412820540200401c1480110030000550380c400da00150005202d11000c05d40c0c2d02c480c4200c0d40000d4100c0b0000c1055001401d110300e007802250300460080c0d21001482d81c10544501044074a440800c1341401c3c03000a5a010070724034284000c0140002a25841540019030180341c00c44500001a45525014000c0249030240d0815103455050810606032403006804540f80014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 539302383 1250 539301133 539301137
    0x10f0209130b0a0824160504030305030403050c030a08010e0604060806280507020304050a0906030201050403031d03012904050910050717101a03042a09020c03040806061f 75
    0x2840a00c40b55440c2480d120080c01d910044460284014000d805050181241381d1070000101c2c0004820030110410900d1107040c5a503a246040d0960750305440036007020308103804002c0148040065084100010710903907005440d80c0c0306641c5080240c1074800380040200d405103041200c10403d030b0f90001466030304240706460103003940444495044030301c0c203000d040340a424181014004070640200041c0305403442502c001c80d000c0d440c2c0c03440000b501c01d00c0c80001c1c0011020001080424415803030120800d140c0b80301c8102c401c071403c00003403d41d29406074841c80e2101022400c01d14410841e0800128070b008d540a000d01c1c0307007400d4000d84503204a40080c40060710b910000324a188200320b90084400751101e5400b583c10328408503600710405028400340d040d001400b40c101e074040b09058138440c541c86184100580c41c0700c4410507410440001c1d00500103406007001c08c0c00300080c0082d048060305040150b445030f10745103100c1d00d4208090201c42c000c0e00f86402c000015801480760306003446140c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 539303633 1250 539302383 539302391
    0xa17070b0402150706091b0e071d04020405030d090f12200d0203060403051201090203150f040605030111032703070b150a0b03040b0702010501080309010305040507030f050f010f020913 81
    0x180001984d01c2480c600a002e03520740841c00003000712106584410b10b00c1e008011070390640b50900d00341010401d03520708022038030340c182d0b071910191034400c2c00601510142c405030819554401113898100913294042c08101e034a4024030408401c40094030051018008a44681c9441d89411081c542103800c2d10400505610200c0c00701e46500400681d065800f40c22140f00d03240504004000d40c01541d10000c0300c8018800016030351001c1c0c000d4a020314201c040170102c0000314001c00040c0610109039a03002a00c0300d00020301075900f8400c00c0101c0c0c0c107031a4820768030319080000d55500e181202d14940640c00d1103110300e420363b400005031031250780d1282c044406521580e41e21010a00100000fa5101c20040b50108042c1c40080241d030041d845200d241f0520303101c83d50140c0c240d4800340901c13103117139100740300040407988a074000c0ca030050f0180c010344d01d03e01c0e00c84c0c03958400032003030800681d1140e000c482c000c001034100344201118005144000c41c108108480010f1080c0c030450403804010341c40d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 539304883 1250 539303633 539303659
    0xf06080a02070b070804060b01020304300507150e0303040308030718090c050a030e0d081b091005070507090203060d1103010b04150501090515030c0f040b07050a17070b0402 76
    0x285604540e10380c0c0d00032600541e6403814103401445d0000480701214040e041200788400755000006407400d5501c003501c2642e00207401c080e00000c1c90394056181c000320602225030408207600b07000c110060003040140224621540002500d40041c450b0800d000743e00c10801040480c1c0214180c94026051786408140400001015882c8c0d0495070040c0c01902d28104c46144241c0c0c222004040c1c081e00754030144400c80c65044895164210450a180402d40311000201421401100c180c014440b20600500f00700c896004180c404025031900c4011620004111050000c1000150b000b8503409109524520386007020615640220a00400c48030201d10800d0300c07070f9401e4129054000e409401085048c0082c280000c1c11880c900c29507020402c001800304241c10302c003035520129605079074010310b5515159604030081e800311038500a0004280000704004040710010303c00140500000c240b020000e040810b02d68003442e10302c6001c020104928400511000b80b42c1c0c0d0300940403101c072806881 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 539306133 1250 539304883 539304901
    0xf021c0806031f0525020a03080a020d05011409010f08071214061f090c0503040807061103040c08100218010c1b180f181e0204020a0e190f0608 63
    0x5000452061110303c480c0c103501202d100350301062050301d0310844010000700c440395050040c4020040e18005802000c07040020a01901da002e0b0003045070000185000c0c072404d00001210800c2c0c02c400c020030340202e42d0800c540387c0780c80308901401c40c850ba8402400d19019000350307580b40a114000c184c0c009085e00c001030017560303070325901841012403d584052030810fa0018001c4142001d004051184200106201085200382d007844030054450501e10348032a161000690040c00c022030b241d54442e142c0c901030501c240013541c026486400301d414080d0a010105050401843d164516248148075880004014001c0c03c0602ca0007800c0c240021601818002d61080003c0d45444200c0d000e400d001400c100718205254110b581004200000030741c0200300000e407801c01407441e116004040d0103402003041c81d400600c3c40c4a240c900300292240c5540030500b40d0f000004c6050115103203031000c81d242d04180424a115000032022441e010381060000011140580221410001910700180c0c543c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 539307383 1250 539306133 539306143
    0x3090f0b1c0c020a1b0b16060617190f050a08030a0515060f071401020c0708010b0f0a030206030712091101110a02090c0c07050a090504031202070b0f0405030909010905070f021c080603 81
    0xf10b0b15200e800d680d0101c0c0c0c60141fa009041410481e40d0313505e40b207400141c01740026071040c4252201c0001d000d0b960000342e91241c000340100e86c1529040350310104100011030810140005a00c14000326880e03141c8010780cbd80403520000c0000c0e80880b000080d00f0781d140e0368802210300746820034a10303a85403541d504004401004050040b40b842d07200081d94440b00c0300000d204401c42e0359070030080c0200000017050001c0c4c09a0b070040c8941041c4ea000b41800146440300155a02c45480d00d8141440c43c2c0c03d2503040c0035151509800c1e101903028801c0744d101564400c083c14040341100005000600d6660b0203c1d400301001050f070241e203000424040007808051000320000c000c0205580c81c0070b40c484214400408095034101d02240000219500600d1603000f0b83c2c1d071007078004101010680d22041040402071004000310b81d5804200003411040c2d844031111400380ca403001c000205450032200c09454000c0310303002082554003060a1b00364030040107060035030b13200080c6481a075944030080824030b80 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 539308633 1250 539307383 539307389
    0x702060609181507050910020f0f0f0c01030e0f24010b07051b01030e060a050109060806090307030e0121060305071e030204090f0f1101021207050303040f03090f0b1c0c020a1b 77
    0x4980c0c13458080546a0019070041049e40b8501a11510780601ca01e542d07495803240c4545515800400710100d6a41c007991141821801c50019250166001c00840b4102284001d1000344400802c3c40492103070383d801455405054550340b2030b850440140c481c02d682c0d081c09003c018503513311582d880801c0c0d200e80c10150810711513800b01d40041c14000e10500c05000d0034002e054100b4501080003550400c00200707180500c006002031803a08581c0c1c1c6080362014440301e05141801001241c840600c003904440d400e042c3c803545e400086060640c6000c908200fa180e000d030310030310b05865805503040c84041d0031004072541101c000030000110310744444171007501903001d400c5540320001281030011b41580c0da610303410243e080d906114031240f80c1c4034860058000150596100b84002000a5040101600218040d0528625640e0759000e809920426070308180c11516000ca410010036009181d0b1100f40035034644c0500c40d0051a60000307541d04800c1c4809400742c0b10818000e4040c1091421440107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 539309883 1250 539308633 539308639
    0x40204090206040819060b01080c1209031902030a08070203041a1e13060207050a030b180a02060d02090f041a0d03030b060d06170106030c170705060307020606091815070509 76
    0x705103805c40082c8160146190160342d0b103402e0032900000396102d400d40d54480d0440204160522040e0b440e805042d641c0200041c420b803000b040760010050007418014991055940103640c1c4001519000300703414009041e100541d07106004c21b10042d00740070044081904013400c03c5480302000d607041c0403209a000036a4040b118001031030403501d4030390b04030602500c0441d000c886106980710240109402503201c00307413211405002003661507215400740040003501d141240c0f03c9180d5600064500e42c070620f034200310b19500046001c2c00d4104644544090380c0215020030619862080902000c15180e00c4580310300030741580482014000d601075880e071500a40140d4071000c014684900904280c0108070541e22240945c0004400501900e42600ea000007000718540c0352200500d2119a6039580d42401e008540010030b040c0c540f0700141d442031025034000c0c5100d023800000d02081c1030005e03002d803c00c140c1160303c84d00c0560300041c5401e400b400d480071045c01c40d503d502c011552401449501c80d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 539311133 1250 539309883 539309893
    0x30304030c0303030b180c030c0a020c13230610180e04060203100b09010e01180504020c010209040501061e0f0309020409050c031212040f05032203030e010c0503030402040902060408 80
    0x1415891340c880c06952000f03a91b9600344002042c2442c4190004039462880d8010810019040013280000351141d584140103c641c0c6040030b1300000c410944a065404000d951401c001400300001d030181802c440f607108102c45103040950110725001e50380c0848078103001203651030326910203440070924001c0000704400842824240740440181d40700303482d0010345204544010903525520710440302000350503150007000c01c00d081300545d4426454038640d2030b5a01c0c241c10010390394881d80010003001e0140f030001079581c3c02c8002004103d690680029041200300301012481a000620150800302241000c901403601d03400120054811114001c1d0050300300000701c0704107c0001003503248000100e0a8070800f00b8051851400b60007504001d03150b00034a04040b070041082c3c012091002e500030b000746c0cac1c0f030f01d40c0d45250298071509010382d0140e41142d0440800501d40d100600361420102480c1c00345940e107031500d919989000140004e44515602d0340800215580c04007124010b0558500340c034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 539312383 1250 539311133 539311139
    0x703021e030c0111030705030a090c1d0a060b0a08071b120c0302011d0a06020309031201120c0602030f030105060c010603060e0102180306070912030201090501090c0320130b030304030c 81
    0x80e16500a982c820119600f0040f20607080904141540c0c03140046940c1c06040d1341d6080d011101a140251094400500c050745c0031501074501400040800b80c1161000041e007010000c01c411104540d204441c0c40c10140315090301554400d01e4203401c0a03051500c14242d4400c0d00601d4640051b0700e00007031110b441c503081140904d030020484010300f40260000c1202c2e0130102e004080d200c0001c1c40c00805034000b0f4240d04001b400950145412407420802c84c1d080a0b94240041096007083e0000c0c0003072880e100d150020051300c0780182028004500c0518200348103030120b05154007060054900c0b444012840c00e002c0542507103e04000c40d0807000601c40d8001081805000750b0200c1c100c0d4039401555401d01816090000320180541d25a583c2c5407445450009080c10494000800305c0c119501c1c2d40c42c140c00716400340100340c0c035507000b03c1c440c00141b4550320b40b040030700c0300b50314076041c2c004160500c9070308039502d44440513012444480b0100b12034856100290461003a81c20003403050b02944004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 539313633 1250 539312383 539312443
    0xf22030c0b0703050702033109060305100b031513020406060f12110f1e030a1b0323060301020705070e1618050f15070b0a051b030c070302 61
    0x1030100c49016140e44140d64442c030000714182d035822a416405a8000c01224007c0c40616601500c00c0d000c039400502d000e0605542c160710180075500c8060810f843d450b060042c4041405103829031f80c02040e00300701d10011780000c20303100c011940144840c3c600342c10001c4c4015511a1901c441160f0040c001c01c03c41e0740300c00018010007000317072000001407041001d02c00300000d28415202c00840818400f0b0424180c50300c54a8250310603050030302c04640488550f480c207070503003014601880b18260045601190706c84a24640250074210f5000c141c180382c40102c00b0380401d40482d000b1040300f14440c00c250384200c08240179129604000740144141440003581d025211003482c0542d11001c000410190150811110f82007454040c040c19011709600708158500090f8240038a4005480d9007421040344007032400f00d800107041580d502c40b0130300030822048070070300c5240c0d44510542c0001d00b4107588030700b15002c58040207002c5041c030480040d044081c54001c110348440824a5150543c50101c04610 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 539314883 1250 539313633 539313647
    0xf11150a061e0e28090309210840180501051e010201151d0105060705060c07051f05060a0f14010806040e0d1107140d030516170405030609030708030f2203 68
    0x550b0703c204280423601620200390360109441c070340c11840203401c01315680101003c00c010854809a00483e008840c0c1c1c19031400070f00086c05140d5803120510f070030f161034011888030010040c0c00c8181480c00006229503503510444550700425824030402d0038001c14010b0740101000b07462581a00062940041d07005d03254200c0d00520038a90a600c0c040b0391f270715400d01082c0c1c0030f0444018400c1d040000080c00d040c0142000d000ca80d802501168018040140c2d80c045200d9a1803000014940b10030403c095400c0401d00c2900030000440400b42152800f210003000104d0350588a04001ca20004644036030f46135003250080e20108c070195a026803041c00050601c600d03050140c04d43c0c0c003d1010005011425040310801ca041c054020040f4461076501150281d10169405c0840101d114a90011510807180a810fa04510b80d44a64032400c02040500d0140c0051032400c6990041086000003580744013540e821402d400c00c80c0f90540c803030f0310b8801076044143c030207800c1d6101c0c0c98607103000b4581d200017 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 539316133 1250 539314883 539314889
    0x8130503100c020a0201260406020309011a1e060d020a020705010f090e0c0a0c1208060103060503010522150f0902100f0f11150a061e0e28090309 64
    0x30498001d410641d400400760380031460402c015030880100710000d540610060f06001d010340301815001c401d0900d40b60708111050342e05131100d6030b000c410131030300c148244110407210394555404501d0741c500c5400280049110310b90300c0c14680d0440090700c00c5448500c203541d000c0c480040150f440d600c1d0000025a00c0040340315413070006542d40200b0320311600070580c080695802e1041104c0d265160410f000d0660312102140d400c001c40392030f441e4042120003040c003010303903119510b02c0050b003040000181660300c1c5811071172090f40341005103d1244d801844507a1004003d00c9200c41c1141c10342448261f80c2240c0c6d031800851414403a045583d00d10300d5000314000b030720854102d58400d940d0f101c01c4900d20090840080440e01100840c600ca900038580b110141d88907004503400312924003009044200140c4e102c000307041d210007040c003600701460700082c02d0804500e0100c900b01e01e8062010809240a4040420b00e414280301201c20152004031100354401b42e00700b40720300010b80c5001094002284 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 539317383 1250 539316133 539316139
    0x310020a0e130e01240306182a050a180e1c020309041104060503070c06060f180c021f020f04030606170d03051b0d140903180904020d030305040f081305 67
    0x225403407644c451000404807491002c12481300c0d180c21580c1e21030048c00715011242e840b21046414200140c5a040e64001c6001a20040402200c0d040407049048141e900b10b58450848140103200f0012900e00f400c1010090340c01c04102c011080742d0050078415001040d042801030940c181c80216000001060700c1d14080e20100808034a44206861a0041c2e000d180001001040419000da100d00e22180445008680001c0c0c8a5540d00130107925803800c0d4081c400e415080302c682030520002e40f160f10109101e90014088102d00c140420300e01654040c2600c55099000c103170541d950b8003840c140c0340650f900800402c0f20f213444280d41c642030001d0b50103c400391f00c240da40003000700380702c1d014060059075803000c201440e40c10f0b070309550400d8025140c0200a42d036140c8001d41e0300d0704c032145503d0040035104091540c41c0004540d2802e09d0f00c2e00744003140a081540240030058031406007820510ba018903000070301d5182c0d40f0b030062869003141c1e4041c10090000c41c02c9800941c03083c420b0741c110f030811 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 539318633 1250 539317383 539317391
    0xc010c230d090b190f0e0618090a14070c050f010c05070204150b1804021215010206010815010e180a12030605030a0f020909030f030a0c080906060310020a0e130e01 72
    0x5088443c001c0c4141042c03207020110405820084c24002c1910190240e0542052220010b20501007001600a03050286c07046200303568146030750900414090300203120840070b111518511031888040d01c000392011080202c42110301e42070180030300c10f00030300ca46108020302c50b1920208009003ea04207000a0348210315002c0d2507801e0740c0c03500c59080c088030394808103213041c9441c4a5121800c007079424002508140c0810a115074071030301110040c0319800d11982824040c196000080c0340c58016004241d940d44411080c0e4004d4040e41c1034103045904c01418007447c0d545403100c007514144411b2103520507200d4450100b003080f00440140030649016641000403690f50002c00d95100100c1002a00901d81e00101a000d402c00003500c030741c044020030131203281450700f140700441640f080703c40c00300f000d6460b40c00a4400c0d61109106802800c04001400c4070f042000009865038460f0281084881d0f0010b00c5400960107103401c140d0800d03000f000d0010408040f0005006803416076a0b07003030b1951078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 539319883 1250 539318633 539318639
    0x6050a061e0806030a06060e070809160b0304020a0305010e0c1201021201140109030b01060306081b10030e1c11010b060c0d030b01030605040204150306060206090c010c230d09 77
    0x440c011801c040d0010300105002031007800c41c15030391003402516098050089540c014041611400f6081c0145040c0e003440c0c0840c50b10f124000c14041010340015116040000040001c1000f40d002906070b0b402400d805d0f03541d4030385200140081031583c0c00200b41e5400d0000b02901d074000450307071400c2d0340400d0f902c100700e403440758410900f01e01c03e01c0003a5501c0c9031000018810b1444110701040d0461040c103042e04466180d464050900c0c5003680b1000000b0f40340c081c01c0c845c0140912200340c15042c001f203606000e820401c001903510b600d00015000700350781c551000308260420040c044059502e183c25a01841810800a02d0110b009440980c2e17507083c8062044681480300485005c07200782c0740078054007811000b0440183c0104a0114101030321000081003030340d9284004d100502000d50070008841102402500384c900a46c003020543d0480f00030005001c50210f11007041050134078101034503107001e24015132413882581d00303403a165000466003465503034000303150242030589464080803159 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 539321133 1250 539319883 539319887
    0x5040e010c030c0816051e130602100c1d19140f1212130807090e0f060103021c021c030206041403040312030c0309120e011d0f012d0306050a06 63
    0x70050740d11150744002e51003119070b09441b44002d80810700441000d0351407100150303a4012141c02441c9084902c405c3c0a0382004011b40401c9100801d000460381072103044071659005c0c050200c100201400962906200070741da58403460000b17200c0201d0b0b0341e03400d134681d243c0030519a521000000c8038041d8400003440d060a180a01c0e4280c2030546210007840c940b010710426081d2500001e03142c401d0031142480101e0440d80130300444002d0100200005649101004e1462520f80c482180130240c0d0030000060000d619031040144c0c440d9402c0966841070983d620125611880416a10001d803000000d20410140d0100c1c1c0c0c98041d5003c0c06814038940100045252070b0710a521006040e504500300300310545020390810080e004085c280011650380316110501040000f0032908000f0310700086524196812100e0070071140c401e0702d2000401e4101102248140032050340310b50501030080000c030340f1003000400d1411544c4142614100e44421042e028014102d64050684500310103040403d81da8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 539322383 1250 539321133 539321147
    0xd0f0c0f090e060601030e1c1e03050f0105120708030706050405070b040e241c051c02100b04020f160c1a0706090507050d20010513150905040e010c030c 67
    0x2d076040c400340080d51540e400550042c0b0b040c1e08401030a004800c14108090303140d0030003031520700480e2507134803140001842c584004504040c0107814545860b0501c48c800c1c08a55100341954800ea50480c3e10102c0c14035a6458407089602c00f2841c5c0c07100252420402c4602d402850280c0c1c82001114074581d2508030040940c00307640140091559400300003200705185415065109075022a000d0320307102c4460105840082200910248c14110300a40042120406c164004216080d040014010307154500071340f601c04040045070903e440d5540c0140c2a41c4a81c101c414519011901c25910603c66016498541c000b80c0140d900c40c03141100081d01012090320408031100c04007080d4605003d82d40c541005241404081d074070341c851810086401d0300c07207000d88000c89001e452901440d6000f40c0d0140d0701d000f022203100f41048400e10442182a001170005016984024400c0414092a41044031115070070380c002d6030700a080070300645038000c040d4030040300e80c0700565080c8848203411505590794 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 539323633 1250 539322383 539322401
    0x4170a02031608031e1902010e0d11100509010b04150603060f0f290307020c1c080319020c01090b010305150c030a020a11011409100c02030906090d0f0c0f09 69
    0x10f90002c01c4040701242031000c4445c04c0421401e1524201081100c000442c6134a1031001405130b9542e00d84130307440c0442046003160241d010301d03040d880801c03007000d04e54803004032221a040940e20345000c20503d41007900400504040a0070810032003008050300001080d1510030800446e10302a404100c04650010032400d640c00031031144001441c0070581e44180e02c4040c080290100302404010251003050000c6001e8190340c0d0050014440f66410441450b03208010f00208000a920700c82c00641c0c0c03d015241c5c011030348003024010480b1100c03404c2c00303449484c0f1b8050203546452042e108010141425a05070307809001103c03c2d07182c000c2003003a07a0030029181101c0e811400d00c0042d005407110740091034800610b00d007a0b90750b91005030340c46080d00d815050a02260860b802040101c0508114514580c0c9000764180300d5940110006500c03449444407440c0a4200000d207101a5200c100ea040d50aa50003040303d042042c00d030802e031940c07940358003600303c00c4c001255001540741004d002c2c241c2c01d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 539324883 1250 539323633 539323649
    0x10609060207080c0d03120c3b061b0601030501050f0610091a0d0f05040b061c1205070f0606080d05090319020a052d040603200604170a020316 63
    0x29026100c041150f0845142c1044040020390003003500420b0003400b500904c2c0f401a102c0c1c0e420340203084010202e4031025440061881c04109d41148100c11062010741c0000c016514507039070308007080c2c841c1c2c00700c0c44215840816200c3c44000004105056100d9445680f5440c840b116503162102045142501001580c000a02100003445000500b088100788540700121452034121000900270965110091248840340d8607003c00080c40361214103140e09c00422210051141c0b868002580581011b1130f025108040d81c41843d682c203805401202ca41542044040d0f07507103021460614068085c50150b02240d004030300c04485a140030703009840403884010082e2104c2c040200b03c1c004c504186010a99114100000019442d1035003e81101214400c29000382e01001d4220079041d01e142100d242401a0700d80302040020034072203200c6100300da41d03420341e003020260640006507190140750061000142200303400a1401c50000b2078842403442a01941e4404201644107903040031580700c0c00407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 539326133 1250 539324883 539324893
    0x14060702041a1e0a0803070f0618021c030216120321020f030a2304030305040311030417060916120305070b0f07030b04051504091a0f01060906020708 66
    0x6250580040c040d1150b4101640b0b603054202000956880140f0010a803002c0c014800f80d02c581460506000034010f040c0080d40341c4070b80c0e91740d05411442c1c0a030000c1e02442d6101d00c090030032481240762041807500100b05400d100c131002800c480c680404c22044015100754900c000380321044141003000c45010007840e00c0d0f2011903490a481d4414110701154035040c50704a0321884109520240c0442440707002d8141c1c0743c1c40c10a0054003106e403114071a00740c071007001410341401c0c0c0004500da40d01a62624001c901f603111850240c40301b217039101d4116031902000c5004190340000e04103503c40125507604660954039400740840c0c58140751030354241241c500701c2c41840940182014035038040d00c240341807403070058103440b00b03015000c0a451014a00d4501b10501c42250ba140c02010794550084030f04101e1400c2030915100c0070854a0510750180b1b480f2103a1000340440400d41056551940c00001c8162a01c6c2c1c6910110101c03d00443c1c2c0400c1071400041810f910014560741034074a8140102 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 539327383 1250 539326133 539326147
    0x7060b0f011d010f09030503190206180d030e031e030901060506030c0405190b0403050303010f06020c010215190f0203060102060f0106020a08030402150d09060b010f1709010b1f02071406 82
    0x44c0d0404814011400b4460948030000000b4010401000d4080140454070411545414021304022001c1c4c88c0300500d202034240b100415801180b0101c5003c0c05080010b0340c1c03180e1410090070341c0580300e0049800150000401c01460880b001103210318000d00003005050780b0360381084010f00040d112000c0840d000d20051001d4182140703007802c00c3c00e4003180d41c1c01160ba60300102e00d5562064100322001d810101c01041040d242c00ca07030002810342400540b07030000001000039914558581402101e18240c80401d0100020890311008620711180c2841014002d80081c1d000c3c1d801070710454010311421000a0104000501c298160380e01640940115a00d50f00c81183d0f540018200740e9025811900d10400300543c0c078000c08010000007008506c140584c203001d402c88680c00e405c10305004001c036003000c0580d8000c0181001c0d220054000c401c0d031b00e801d02c02600601c24610304a40144828a03152072024080f100046e650450351b00300d81d03815031580b030188205a6002d191980006041c4100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 539328633 1250 539327383 539327387
    0xc0305042102090a0b0427030e040b03030a080115090f12080f070303090507090c121802040c08040b100605090607030c0b01120308371107060b0f011d01 67
    0x42404503003220501000700340030b41c00040c8070307103c281c9005140d95a2180300d03003038a00300380c05802c2c801c1401e66820044882408030588100084c80002170400c00e5070801c861042d51240e200301d0000070080c040700c4d201c84280303a018107030050a00801c41d500d060582400641c9200704040010341e000001c0c0015614600086c0c00034501d24481c04494850041c4100709001010402504c0714030f000c0e030b60200d00390200d4104241402c6407a040105014248070721480c4458006140c15900710074154000ba10301c40c000b045645c01c3c13440c2d40d0001c0d0700c181480c816443e216401285a4011030013030300013108a4840800e0440d007112a0300c18640818400d02c0f960103103103004009010301c20b000381042081c4413040da6a202c0030f618240c02004408504051040a155200c1d904035440b4078018200528241c0d24419001c142900030300000c000c00880f00f185070008440d030007a4141300c050500c0c0b9511012146080b40240600101090040001d803c5030003156124400c0729036070701c2c014031072002070880c12401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 539329883 1250 539328633 539328659
    0x3090b1e07050721020405060f240d0204030c061107050310020f070b070201020406020d020106120f03050705150105100206061e030106050604080a020111240a060509090a120c030504 80
    0x2640d01c3d004203140024042e030403070b0b06200000e1108055880086540c070400040310f4014210300d018441c002000c00b00342d110052802804402401d00d40102140d0340303004441e51040c1d941d005000e078008100001007261103400c079000d03034506454018800800b443e48503507a00d09882203030340c0f41e0301c0382c2507240940380260b0080c48103605c540301840c80c00340d046e00c030b0030120402078481c1401030b9800282000910b60521030703954103c1c46131009010340c3c1e01e48036101188454540c0090020300001c0b05402c1010300810445205aa001c01030303540c14202c04244080884091080602460301900585240c0e403001c01d600344140302c01005040b082414001a4202170108003007640c043d940d030000410903603200c6000c2e00c010310b4614002d002d8070100d440014141e090105410916038440c04058000090305664070b018415090446000e40d0348982100d400b6104540c0190380010352842406088040860058503c9015141d041d180c203940c000101c1c1c4903141850f004e400903206100500071898240a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 539331133 1250 539329883 539329897
    0x220f0311030a08150a0302040c090905010b04030b2e080a0308010e0f070c1407032a05030a08030604060302150d1d0304060c14060c030f0a0b0f0f01090812040303090b1e 74
    0x201171004580c82e0ba0101c0c0896a0400420001c150110700400119000e802468094501c4004941c106440d554850800c2c070400b130050241c60509845a030303110700341080200c600e060030142c0c048070300756280b5a0307d0305c980340300a0507400103c3c80c40021420307841020816009180c540d50404141e601d8034421128541c1460045078200c0c0700d40c400b14400e920409c2900061400f8172149000c180000d036056034a00c2c0d04030411403e01e2409072081205076000700c0d403a89403a410060480d5280e48031000039004085540000354485070b6003524440d071191450150448201e060b00420101c02040c0ca1481c41d01c0403500c1d9010a80c0c4200400c3c0700b141d11610f42c0c141c05500c21004070b00101004400d07182440e0341250b50004280011041203a9448003100d50354000c01e5001040108807601804200300601100b50980207216200c9446030781e92040702924003d247d4030003500c980240302e00800c542640148400e0300007515030300c0e0110b669204e41c4112070340060322050992000590035582d1a082c4c01c419 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 539332383 1250 539331133 539331139
    0x310030f0f05060a0e0c0d0b07080a0209040623010206150f210102091e0a051c171309140f0403020304080a030e0909061003020405220f0311030a0815 66
    0xc1c0070040090000c100180c041c2913009000324241c0030f071040b0589000008415140710740040c40600000c5084c820603642c120019250007041541c5800d0b500c8003903c1102041034110340380501c00034030560300010b910540c1e5030408810b10801540001242e88213400d40d200c0580c2c800c0040b035030300c0d186084c92000300821401342959000360766521090203030640407040282580d4000465a803645420700c1c001803d00f20641c1c509c00e1889060002c03c80d0300e4000d000d030601811517210760b030740d0100c030440c1f140e2420341d80700034506960000c40d10790301400d802040c80c040d505080c003400401d0b44034050050b65141d0207030541e8020b8580d90703522000503860b0041c001387c040d400b0400c004540c01c4400d00851088902984944844001601c24420007203801404408107801450a01c140f4042e04a05001101d40440c3d010070b5648074081210300041c5001800c41c141c200d00c01c41c80041001031800722070824040c1d100c50f01c2c072003000156161244511001900090301113070020380c0041008080c0d240500000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 539333633 1250 539332383 539332403
    0x7150309060e01061703120615040b0c071e0506032d01080604020a1a0706090302341703030412140c0604121b02150909040c0e0c0310030f 61
    0x140c984008581d0340709030b00e00443e511000c0078041c01e04180081d0441000040080d03182404007402c0c660b08000240030b41e441a0301c141c0400d4019140303c3c0655015044180000790390360650f850b02070380c1300744501c10601842c0f6034580d40c01c00341000b420004119980540542d186580d2920070040405c001c0006001000d0104000340e90b603500303070329958040d2010a00030401c0341000c0c0108040381072964408140318841ca812010a1210300d002d49410300c0d40304002050444c3c0f14602641030900520001707203110340c07000d80f12041c2500c0ca400d09040001c40314084229944503103620305c5003121164403824942c402c10204000a950500c80340d04d4a6081c40d101024011aa46422032940310201c00540d60340301350284001d00018101141503102142003004034100c0e407501000c6e090050030000b0f4421044a00b2540c040c8881a0848294010041640e4203c3c07403d0324000c0c0101e84240120404909680c0c00902da0700700e14800c80c0e010b0b008603840018075503d169501c1d203c080411a08517041050 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 539334883 1250 539333633 539333651
    0xc030d02070c09090804060e030a0f02010c0204060b03360705012a080309060a1a12030c06040602070c090203040f060507020f0f030c1209100503090703080406031b11071503 76
    0x42e12900b40d110788500d170415590341c5070480c010080d41d040440710b4825040f18041400007030303801030340c80d80301642800c1c0f0320204d1100b0b00001d170051607035034488071400c0000000c004281c50759140d403030114540c0e0807100c00d90640f4000001512952146000019072020000340038641c02003211110a03020004200b844000b80919425285010501203801070b502009110300340d03c080c070400d03601c071070841c804009860f240103040c900d02100542550040804c00c1100c1c4081da828422501100280c0c802c80b015401e0610341200203511141c825500c0119964020031a0342e558000c6900581c2c05c14203402e0400403d482d000000c1c00e000d4408819446154540307280310760b042c00600064407451000d1a01c610b07001c580075041000d18001ca110113001080f10703031031980d94040b10407441c014030729050780c4a54981100718a01844c0e030b0000303041244041000107505500d504402d40712200d03401121420300590b941540c104e201840300c004070341c000751014001d803200212003400c030100f2490040f5030b03401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 539336133 1250 539334883 539334899
    0x1140706020a2006060108010b0c07170c0102011d03070213060824070207080a0813170708070f0620010b0a090617030a0c110d120302090f0301020c030d02070c 70
    0x10044050101141c0c0b203000f000d00c0300e01c83e81d1028460000860140c0524580580001c00c01081400746015880020902c8001c80000f0040100500b60040078203901250803640d2035034075103140803030b0b60041d0708000c07070303440448900034100d410000d1460045003004500c5c0c1c01c001e01600c200001201d010f40d62500080c4003c0700300f00e02c496240700105101d44a01700d609261114a900406c03100540d0b0202d003040200c900000b40290f07006800800c49625191a038100090309000c0313034042072480104088042c162440401c40c0d204580ea00400c942404c2c1d81e03414000b6072000c4904c69400818a55018040c03030500601c0024282d40c400b400000b039441c402400202138285130741007451741c0d6a80d01c506200d85c40c88102140960b044850041d402c001620100801d50a12598028480000e0150040a9031228040409020351200f012103080c821901700a009412183e14a4850011008610001d05041c42101d40800318140594039200085003031401075803114004650340e011310803001545403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 539337383 1250 539336133 539336137
    0x2041a0a031103180f06010506071502040801060608070e011e0c03030b0406080d020f06010b071e0203010203130b0f04030203180310060608040506071407031b210216140114070602 79
    0x1d07000d04d08503c030300d0b440e03d403500e050164441200c007988041c00600036540d80c0d40030703501f40079070010880c1d4072114620160b130003a0203a035200c0005c03582010004290140c110050502c64003640e0368014241110500442d50f070103c00788a040078020f191000c4414a2140607010318407030280c10042150070705140400d003204c00720307401a41c4a400440310850750035030500c00003440c601100c0080a5039418140103418510031613000810410300d02c0c0003000c00d0303500c0d01416142c20760010000c548070b1900250040240070008030407510300020100003001d242d420050030b0b00464040d03004506005480c103c0700e082c20007a141d4194580725141460740d980c80c0c6405100b000e0501d960300e4107050305061600c0c902d0604007400540c00c1c401100040340440c01002c0c03ea81541d0307018034100c0400000030441b2103050301c00f2031000d80041001600c8100c441d03441c082c49000451194200c588803080305400042c408044c0c002c00d018219001b44030481c9600ca0500074004410982202d4500b0045036241c000700c0e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 539338633 1250 539337383 539337391
    0x10e030a080409140c030a09141f0b0102012003090c2206060f0c03030b04090b09070302130c0e09100b030a0b0a0b07020607120e0310020d0c020102041a0a031103 71
    0x3401d00002c0500115840b4025500001400100c100507400e09454402e02c0340001801d00d803d455440b0034070740a0082c5400c401d0150720205003520514024040c00c00014003804460038a40303420592020f049520511070603c2d0b0f0080c0750807103092403403111942005039101802004543c424540e00142681d54070f500d0b4070070703500e8040d0034041c200300810100301521040e40c030a401b44007802c1c800b040000d0b00101288011581480c00060b00c1d00343c0400580103183c0725101520b0049094200444148001000710070b4a001f01c500100006140c40f03401c040d114020484400921030070300c0c10ba054100244510381020a41d11f60b00c000342c7d2251200040c54204032041741c2e43e0303610740c1c0801185003090081c541c094210781d507915151140381d4002c21400c0c440c510740100300000842c01030503030502c507145c6c1500c6140020182c0d41424840c00e81080a5002902c10151440c582201051281d005100700c40840340303011942201078150401c0c401040e00300b048104145030b2140c07075800103d44980015441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 539339883 1250 539338633 539338643
    0xe011103060a0e060310090303150602030a1e050717160c0611030702090708190c0c200a0b031f0f24020601050f01020c0a09050711030a0503060906010e030a 69
    0x9a15000c1c0401001d02c0095004140c80551081400515103000c103001c03001028620021440da103181c58120024483c0b0040f015100c918450301007003030741c0d010000301202d99141e9110000b0301d45403550208039518040c1c0204c042003040002d10000f0f003401c005002e2110300314201da8205545521854403c90301d040381120a50118101071002940002d28000c00200c201d00071402c0200300d0f408142d640101074064028843d070100080d40480240303400d02c07004100c1403024080502c1c070700005030803000702c01c104aa07540d1803903008071030201080c0c0d602e0400910080c491542c0d185002e1946c8125070025101c0322401c0c0d1650081440120390050f428000c2620310108405186401d86502d0700c0c1c3c14001e0301c1441d090b03c2110307909100e640060701c030381503400c110b59071740d00005160f00603442c010140d49030a403c03109003e0300048548040e40001d01ca0b02564507540700394075018a240791248030300700e801e8000c03c0051010980d0b9040040c1410340c0a54107040034002c014034900080d15002c403001c0200c1e5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 539341133 1250 539339883 539339887
    0xe190e06130212310809010804290709090e030f0702210601053f0304030b040c050103230a0903110a21020a030915020a08030c1801170604050a0e0111 66
    0x2011081c800400c66032142c10401800c040e941e41c5d031307000c1d203a11588108504020180000c5400d1005034900e00891a03180112610070404016807000b20071000c54a16020921118000443d0345050090b2059082c0a0000e1494034219900000c884c0d082410260703007002c03101310362031007034000c0300e9112200490a100034103c641c508800c001600340c0c603144005009a80d4400320682544422514210250724801048214030200c004c03459802070f1f80c0003420f0b510510045c80b0078031090300e0540e410f95000780d80600c6500710f25803007500b070200601400070310650603800141c0710070125845805428030a03d401b1045d0050411140d15082d030079813095544051603284491160700141603a0301c090317842d00180102c090f180e113024084e54858840c2c0d5400003281895004e1080c400d1101a0902c3d9000b5543ca480e4204a241c500e2150000c4070740c0010803c420601c1c20741c0c2d40c010003140d069500b508074448450365800d0140809000701401c1d02080b40d45031a0b0303188120800f0300800080c40c450302c000c3d0b5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 539342383 1250 539341133 539341171
    0x60a06050a1a0d0507020f0d0302030402030706020601061706190b03091b03030706020d11070317060a03120e0316080309011b0c060c110904030e190e06130212 70
    0x102400959000020710380c188000c1c40180b80d820030640d00c20b1010a000001d01e9565001c0036410041400003041d154080d911031180c070250564055405a40242c08030f1300aa902d480b07059035a4202801000045620030040041500018441640c0004013400707580c00408401044410103140d50032562035800c020042080c80e1404100640308030045500c0a55100c0300e42c800300c2d4a038803236180b01409081e000640041d200c1c1d07050b0081d180200c1400d01195403984141001054503840300741d0b4200d40c245003401310b24240381c2809081c00f41c07600310000038003c98486409980300441002e03150303011300640e4030590140c0035048070310700100707000c8010315078a00440000510380081f4a2081c102600c005916602060391065114240d07072242c104015071040c20b0810600303c0c03400075511548210302d50308001c2016445002042c041b00191102905181010780a40c10320800380140c480c01c81c151800107400c0d1800b2080a408a004207400529280080c011500c0c180d200b110300b10615903400d04c4803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 539343633 1250 539342383 539342389
    0xf05010603083c0d150515090a06020a050712051603110a0f0803040b030c0403080315150c0a031808120c190807170d020a030504030f0e01080115050903060a0605 71
    0x43d04460100700d840300c01000c212811034240340251034001946507501c1e001e40c101c4203001080303500a4040104000d00b00c0e0080b00017172585a01c10342182e4066101d401c80000c4060002418801c1c44da4018040c0030300758140388a000c80c459a580051300e640c4100228810440184004070700030790302074448002c0050402081c020320f040d0542c095580d440100e00100440c410201c10f8500791000381c605260b80751a0110902c100703025903040940ba8010000920401324004040714491721802d0f9201007800000cbc0007600c4690003104d498030f40c15007040c0350000001f8402ca072400a100c4202d802034450a4823140fa40d4030b03240804c1c80361001c000340014a102c0303159003082a01000b5009084210450120f951a0107003070107901d400402c203500c0610100c00000d49801580c82402c6144800c64890042117402009080140e8068004c02e46181000d03610a129900c102e1048006071501017903a480d141702e10b0343c3c02c0702d0b403100c2c94100310087c44518016a0240f100b540604108a00412114108010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 539344883 1250 539343633 539343697
    0x603070501050c03030c0f07021e0a12050c0907211a0613091a09130311071a160501060b070303060e0708060105090f041806050c04030206070f0501060308 68
    0xc40c906102d001c1c0b240140c0b8101c00001c0300e602100072a80717992070701050107002d1400e00070f03554000d620414080380504075003a0343c8804440618101d800e06211551440c9064174640035400250440d004283c0e180e00c9414400d41c041d0b0840a945800800844100c2c548494416036411011000f620341d84051120aa40d140310071004004071082d81c0342000d02924080080307200e10952008a454400e40c400304200d201803001c131a01e0140800403240f0b000400c2d4207550080c00c0007100460019248984908000a41d25081d60b4002041410402401c0e1506089030440501c009803840d038282400c0001d8003c0c0a6100101000480b6907145c565602d400740503100550000b00d000240041005682c9501401050b00a00203082841d0707221900e40c04244460703c0c010900b40c20508046088031409010301d00b0b03240760790007100100b1540d101d030701e000307900c80c461444007a610890a1019401140110030010440c030300c074000005500d56290740b040055000141d8004504092400501a141c26808 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 539346133 1250 539344883 539344889
    0x6150905030c010c1e120302040e100e070e0a0b040305010207030215070804020f030f0f0601090c0905090604150f15080a1e0c120e0d021908070204090c090212060307 73
    0x2800300c540035000020f224410780f00000e000c0320f200048036401300700e01645c010034040d004008407601c100184000b601a50040c400c1543c141446d000040b240c084294400e015180911a201e1560301c683c90103e80ca103003d01355941d88000c0c200b400040140014006000035031242e400961540541d04000e8240f4040703001042100c0f48044c10441c0703250344500700c01d0744940c0c102c82c05114480c6490101e450068900c00300e8055101b8010b216010304800140346048442c2604144550050300004803110a110700c5400d8201e0040303c081070562a080e0007044c01e642d2a985010401507840f03900540c0300c40190f110328000410039030340240655000721303400d601104617281481070208141401803001c031400d040a480c203544100d1050450f1003400801049019010240826129104d40540710541000507070f01503c905108640380c0202440d1382c801c01604903000d10300f001e001e902880040c5c001040b0444440c0b581c4040840c8440b610305c05008680c103c10b8409000e0300d4904245443c22130160 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 539347383 1250 539346133 539346139
    0x60711010e01081005061e16050601050d0302030d090201021213030606120803240a030507091a010207030f0218070e040f0b03030d0207020d2405010605040b090f031006150905 77
    0x10100121014203d035240105c4070141c0300380d69118a0175070780503410f12403042c4a045410000503d414590b59070300000c8146030081c2c09891059982d0300400c00003d401080050140e0070a004c03010201e45541d101c020031a0041c01612000c170b41e000b02301d402c40d6200b440301030540305004c102401403010520030b401c043d00c00c1010208100303070661966680740c040201440340107a03c2c0550345d140d16480c0c05001c0b045c0c80005c2d128400098a91621640302c100a000300700c3c131940b03848400310002c4102c00e096450064182c019240090864480c1c02100d000700c101640c00501c51310040e101c80da00c407481c1e01e120303a841e5580c001d0300740414002c100507190010394400d10242804802c40041d6400b02c100e845500010400503510310251000c01c56000d13400b0009050340c074241110002314402d0800000d000f00e40e41030100104e13a02c42c401544c0318041c43c040d070b5416a0040c003604985041c521003507644000024225540300a84100d020305451254024075028043c078003684010581108403032019210407 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 539348633 1250 539347383 539347397
    0x50f031308010c0e040b010c02030105180c0a030b06010c0c24170103030e120a0b090c031608030d1d0a080a02010b0405010321050c0a0c210b04061505060711010e01 72
    0x400b0002c0c0130034800103180c0d1083d65a5110200ca5a02500ea10010740d0b40c090024000e034a0712145108107000c48207001d844901550088082900e0564000700a80340d0180f1510110389900e40112448618103c08882032000f0345008110141c0206a1041e00721400c50010401211403400405500c40d040244290428403401800040c0c0c000070040143d0030180c3c1e043d001620110f0b0790318034010002c280907006c03040000c24031110740008280560480c40036800c5400301e601341e400303452100d049445151802d800602c01d2039035100c0e154114000f2007900d5600500712226820072203082881610f0112050500042c41680c481d8080c02440b0f01c03203500722001c015561440d11210342125900f41c0294003150b00c80c041e0101d0380d0280081d00c80401000b4100e4081c2d1041d0301e421140880f4900030381d00c4017003a56240310042150519101d010396444400341c04151502e50f248005000c80300c00704800000300690204803a22500060103582d801007090380c0c0441c00700000075002c0701c1d00d0303c0018100861 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 539349883 1250 539348633 539348651
    0x1008010203040c0e0604060b0309010c080f090601030201030b3f0c010503010902070c150e031002030c3a05011403010621080f040b030411102703050f03130801 70
    0xc0741c8164040301d546144e4180305a840c0703070006000304605d030848241101c004c4240894400305600880011349161119001e03510b50b200c00708030703494040394a0f00095000800500065200303800481e030340c800c0038003d2602d00800b80c07180322205c80310b112002004180301406000310301000401c520f81c054108094115094114002451444140914074100380c00060001c10003181d40054402425200c92843c01c1384107200340140a035081e00c141707601c47d2042d4100501c001d00c5034070840e4001c43c100c486040c03502040d03042900704000743ea0380741100010070b40040e01c0040301019030200140c0724007c3c00a050360500c075070a0f203c4150389041c64000d80c9441c03014807220032000381078640c00440d00a403010407202032402179500d114140302d80900180201d40081c0e001e0081001d54050b85c40742101110024014007880503000e4601c4204000500c041c0c55030704044c003803102c1c0065030580d0f4200196116100d44409180ca080481441c24603400010306540178480c03074514a000d07003030442c001d01032428 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 539351133 1250 539349883 539349893
    0x3290910080a0b10030b0c13052209150f0905010e240a020c0d03060503061b0904020c01111b12131406091305060109050d020a1203050c01050f100801020304 69
    0x6400c1001014983c0b07240100d940400307960081c100031548141403030810728088002c14050303040218500303a1040581c101141c0f929081c6000001c0b0312400c42c03078905120303030000740102524801405440c04400f08014095295950169a903e43d280384800300311b20010327292241c2140d0144180440c00d401801460310f805d41c400891070107000200c08158015203400c1b88000003031144000c51242485a203070300001e800e802d030300450104c6c0c004905551059641110085c1d080b08200300d455813083d0108810074662a081c0e0280c090b1541a100001e10340f0038803401c0203a50740c4209071000710f560b01600025001c0030b04116046004129040ba5810502480000c61100c41d140c0030b1203120085a180d5180d07152221019100340780801070000e51070003108072019006000903505a8001602031034046500e080070fa100d100c1990703020380f00d48011032501241c2c60440700e21704811010010b08012004095409002e8107004403454000540b15042c502e0f10326209002a03805001d890f4014420003011071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 539352383 1250 539351133 539351143
    0x619030c14090a051005130e0106112d0a0b04112103030703200a110d0912020603130c0b0d050f07080a0c110a0615090b0310020a0329091008 62
    0x41040d295609011718000f002d5410b405010b0a060160303901800010313844082c0030708941210181e40741c05803603082c038142c102c1d00e0b4500c8106101d809070a228001801c1a4000502505481c0620944102c100259243c500c40c01c2c044c1d8094940b00116140b8000303628104c0c01c0d20168050000864070007851078000c5d59241e01004040c3c8041c1030341e811103d0702040e03240316501004030460002035074807650140003500783d02880d20b0a00c1a803080081c1c44003250701444004050f10301c640300001e0034400a03400c201403a880203080c00c54007155040c140001070540d004400192000c104032356104d04d400540002180e000410180185034204140a09143c0020850350440c15000c0d021072064100e83d0180e030b02401c03120a00c14981b2608002d00140411644081001450742c000501020751725040f182c107a84a1204c1c0c0d80d85031f0071850740468a49181d8ac000d180340811410007090b480c0c05a0a002ca204105802c1c2c10311850f1042a05101031a01c0203d00c1e0340800804040c40e801c80c1050f40b026510 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 539353633 1250 539352383 539352389
    0x1a04020306070c0807020d08070303051501021515060a1205100311040207050a15090203070806062d0409030c02130603120f0203090409050c0312041505090619030c14090a 75
    0x121254500403400d104029041716012038000e4030a5141d032551307252264159009000903000240b900340420100344a0f071408142e0720394164000c0c410003c101d030401c1000c01000e0302c99501e00c49010000710040d00c0341c0001c0c000b00001501c504400c018203499000503610024001c0c5d42420f501e820520024502c0f020200c0b018906540042e242c10107403910500c0e1082c1d42c800500780c0022000210203a00d1240c0090250b2882503090b44c52403a0303507400c0155108811348006038094403a541d00652181424140501d40c84030280607000101040081004c94251410940009658883c0b140030340c140410301c2c1001c18002401041194555212040c0f1400503d51840804c19580000b082d184d2080003660544000203008010b004020b140c5590340d50050780ca074074002d0107a0030030542145403900580e4100e43c0420a16180100c000004623120b2b0f01c40c0e100690300a1090101d4409c004200da920308049030b15407400a44e2401d092005060031602d454501b00500302000341e8001a286e00b0308141c11 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 539354883 1250 539353633 539353637
    0x100b09030303011208120f15010518010c0c27050c090d03031104180203010303020d021630030f0e0301110715020c060702030918220525031a0402030607 67
    0x51213030f20b0851414840c145001c590f280700c907014403c0c04050800c04a001e0550743c855001c0d1244040300548850081c0c83c5000f01c401c242203890070301c41d4060018800658402c42c8290350450701c49807071160112401c40c48007010214940e440d00303101403510a0707a4000c518136080300d0400d40004002807038000c414500070101601c81200d01c280000150985000d42580624080c3c10b005000c4607200a40091006500600c1000181011540081100601d2a07a41600a8900b90820031582c6d41120400e914445d40394514141ca628002c0d1189001281071095a4481c6652054400109030000b00c110301031003070b45800801d1074429081400c4445196004002c0103079244400d1148000340150180b00f8020300402e410048016400320080c5460742c011105e11250714041110b0b042c8001040390b00649030503c8408400c030101d034080f003400700188100204ca2280000701300c0c4602d070030341c26a6154068650007038180208a80c1c6c804140c000c0c1c46088c15125503103800d0f00026030b00c010107030112003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 539356133 1250 539354883 539354909
    0xa0e070c060b040f0902150901090306020a0207090f020c0601051009030605090a120504150305010f0b03060f0a091d01051b0c010b09190f0b03070b0f0c070806100b0903030301 77
    0x10070800356070071207031202d0303002002041949244c02c42c1e880500311030a0101e00c40c10785620701c4040341607030400359021554180e41e0400414103507920040294003e03036221003544a6a20001131102a500600e00810101c220242c0c03203d1021011900d0b000060b080279115070b0540341d1040703040e61700c01d100c20704998205001154039154001e0860a203040a03501808800c4d040b422030000c02d410400030300440b240b10054160010192608600b102d10030700611803c42072040040000d04003a0028681024000300500800d9800e6800101006c0c1903a012540f800d807102103007030941c146080180400c1c0040070082c0028034144620000010010f08071904a03d004503610076140d800f51702502c0d5403640a4407820b40344c100708030811ba00302c0040c0240c40c007003820013140d034000b02c2c25030240c07080d0908064002e0582e282040039400c1140c21030b000c49030720004184406400054100200c00003054014040c00590512110b4442048178035004541050130030040395072561000411241100d0640d46640e03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 539357383 1250 539356133 539356157
    0x11b090e2512110403060c080705090a06120b040614011b120c210815120601060f03020d050a270c0e2e050f030a0b010e22140c0a0e07 59
    0x80d006042014143c3c4403480c0c0403030040104421640441d983d05155124103540ba0390b1040221214822444d20310b401980c008000c200351070091310a0706605800f01340104080d41c5d07038008034040703071821b41c000101400d03403403c082155600702842d5141c410b050351840c00c24240c0c580b682c840c454440603a100400144c8103d0b401409010b52508540e6840940041002400c88000400182043da0550540c01541003520000d242c0300c0e10240464a42070080c0502d6880d00328249c1d11901e4440d02a41859002c0081090100b0070b44907942c854882da8034002504001c4401031000b00300c0b0a8071a285076110340e2500310224000c00c410b80219035040030700600941e50202404c001c44000210740640c02c5411826161030a00e00c210601034810035910905070105160406984124550700078114003001401408010030101c00c465114064540c010340103034180480201400c082241651010207070142d40400100902101002d00c4040b246900c9c0c1504142c1c401c05580c0002d8001d0b000c0c000001041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 539358633 1250 539357383 539357417
    0xa0614090603040602040305030703050a030c0f4e060b0705031c090204090b041104060f051302310503030a080106030e010b030618070e0c030117011b090e25 69
    0x90700030f990b108c0290b90f00c0344134070300c1c0140c01500544804000b1a041c0b41007000c10714401d0751003080404403540d4182664401501c0b00d10303241c41c400d82c0780400010708941250401c0c6400145000703180e80ca5510800c02d803a6518480441e811500140da4500e010442100030481c00400c2e1101c08081601405660704620740f044020812000025041424000582c00f8054440700740751146000e404804401c11a850411040700c0766401101d10010800c1004e02184c1015078105c5110400c441c0c0040c40c0a0700389650100b0307404145004080e02c0c0100410070000000c075006000280029001541800c181c50300141040c0310500a050070590785031400c020300013094010f801c90030300c00340a4552a041c00c13404803621000c0048048050311503110f00140700d18088035003d2080c0d10340092242181d0910907c200c00c0c2c00111450003240d902e9480c0303062882151884411120403580720348100f1450303c0400c80c0c1c1c11400414649a000b0355049041c1002e9401180c90340c3ca9507580b80c880202d800b03001c1c2d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 539359883 1250 539358633 539358637
    0x7080a0c06050f0105040507080405060a0b191e090e0601141c0506092a150c01050f0103061a0a210501050a0e010621080a0e0d030c020a0614090603040602 68
    0x3014214504010501c0800c0a064071624140c0d003007501d05100715907c40e030f01590440c9043e0f600800b81d600980000d42c1c070341450340c0b10b846605001044031092980300c7c00c40300c10303144550700f0809a00a088041d20400c00d02030711050010407801000b400750f5940c1c025415203e040511680d418024000d01012056880074003007940c10310090882a070120780d90030103641d03510003182d80300c1c0a40309580d84000400b8114980101041c1901c07541c91503400c8070307000d1010101c08204c0c1c4144000050040c0380c0301000078061a8030409282c400c01000b0340c514105081514000141950841216000c41c0001d45a02400205949070000c1042d00840d10711460505203011002c090000d51a05080c41082002904941000c3c881640203101140e119424101c0382180d017011030906114007031802000405010180c0480d0443d81060113180d9101804902b215103040310443c0050017550303510b000c6240c07000ca030901a100c01c1c07410350000d2140c40d507144000c2c800c410b4000c0c854400440014100101501 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 539361133 1250 539359883 539359907
    0xd0513090f06050306010609122d060504020901120b070807120c0302030f060307231c0b09010c0e150d110f280507060506030a020a06050c010b03060c07080a 69
    0xc040040c40156000c6000501c0395001d0305110307000d0400002142440b41341e01e1820380f0f91541c0102c200c4841560f88403c140c50010543c54440125441d80d41c41c8030001c044101900d010300300125040c0340c5481004640b80d4142c0010303032150000c1080802040c000900340b03500520f10305111020740ca46e9001562030386914259481040d05101d1064000fa505401075801101c03031010960b280d444c0c14042544500d0f15008904c004c4c042d403d8048000c03492000c0000300804054809101c5400200c4d050136801c1b031480701520900110000e1064816003445010b016014901e41900b0071628580056400640408540c0004001043d100e80465407a8003191207400351141c15595501982c2e800e07410790300040300c42044454031211595100004401014110445650300c0789480500da503070100401018207803075014464803070719000680b21000e0800281c18191104d0741c03580025070f080d0f42035891640941e400703a08820709000b41c03c9606030542d4202580806440d48415001408407003149240c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 539362383 1250 539361133 539361149
    0x20307090516090b091f05040905070c1e03090614120f100905040b040326090102091e060304060c11010c09030606082b020a1a0105100c050d0513 64
    0x2205200d01401254045a9424840e8070381142d007a944413000d900b10f0140d40241d5400c07a00520ba416011341c01e011030030110420324140036080644072980c180485204841031b40100e604c40e00580705100d140d80c1507540b4030040780000d4480103080e540c020701c041c13002d1159105000311055040e150041c01003d54100301d04488501d0101e1400e03580301b00304c00105449180c1400c031901c40c007052009190051501ca10b4101d500c2c0d514544481d94106c1e80100316005c0383c0f800009104c1c428210a001c034008601682084001684441c0d19008001c0c202644841c01c0c1e140903118038040131252180c00580740d0043c0c00407030000701000c0c9034409890108964191418951230b0140009010380c0091000069a014200400c68a42c64040c080e55442c13414140504e41000c0d09039050007541c0340b00307001509203d240b050303440a4030255110b041d5400041c004022032014980140140c0c20903030070f03040c8060f4492070000010300c881c1c3c441d0b644030702012020004200e0009900100d8039541101c081c0100b443c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 539363633 1250 539362383 539362391
    0x1203020c0f1b0a0b030f06100c050d020105071d0d060b0a0509040f0b15030a1106040909030507140d0f03090c05130e0c040b0105041202180115020f01020f120402030709 74
    0x7491a680c0c0d150034075021903c40c861044010034010484403d680c81601c40343c80e188000e07201c160401207115403881001c0104419405100c00140c0184850744c0f4007456500089182d0925002c094035406403d803c14087c10382d01d0504402580e02c1c0729034503100c590030500025036107071020082020441507404c0550404860002c0c44208101c1e0990f1142c41030151a4400241d03c4030f03400340c0d0041141e0301d855a03059205800d00340c041001080101c400400c02800386107000e6440c1c840c04161010401c05501107503012800c84240182c400c125004242c401018040b8640c285601510070072030b1030055000c145e50354000104105000254902800c0024032a0004c460300100f000054408085445060f0190091140860900b80141e045240058644604240c01c1040b02200041d02c0b0009036480f900e99001c0c950041010b04400b4043c202099166014540591020f4507020020703903000d001e60300c1007104801000d4484282d41c03001c4520321301c00000d502e8500000303103480d0b404c0d04000401d0b450 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 539364883 1250 539363633 539363653
    0x181902240313030806010305040c06050a0201060306060b0c160501090320061206040c0201050c19020c0d0812090604150c02211305091003080c0a0501090602070201090b071203020c0f 80
    0x40e0b41500c81100e100781d0b9180c0050703541e000114150796003038030010701081c2411003d02c841340c0194054203510320203100001c0e0007640c1e511101c0a4a0381c941c00060201d80004020060701814089100000342139802c1c584054580380001f00b4401d240d110190809441044c002000246c50100d203403020030090804e52a031070b40e0000c000c030010040c0c40042c802d80c644800c0c0c2c40b2403030060190502c14030b80c03600020f0400007000550100384070034550710411800398441410742552002c403261006401424040e80b18044032002d21681e01028002d03111a51003a803c01002500d06421042d246011002c041241d1456031003e03440d00c206015141c2103070051400c00e140705444000908030b52445c405007441360700e54860a0200025042c1d89080c110401e140f014400304401c60010480350003900200d40183c1c0c0740381c0360f031802c54071015000c40d105034001901c1c00c02d56034000c1c1500050b003001d2040078030b060529510070011614481a45040c95004a074401c400c04041c4030705100d400030341c019501c054213 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 539366133 1250 539364883 539364901
    0x40e07020a171b1c08060409020405012408220807050303150a0b0c100e1606120b0a0602150a15030c030b0c031009110f040602061819022403 62
    0x100040e40482c0080c0c00b414448681c005800600090124400b0b0b11203442413500311100000105056009134031110080016291442044d00808004c900c1d05546070828012516526000461804002d484414041c000c8810010142c0b400410720100c07442450f0752a00324918011050090302902010080044040007410323000402102207443c0740034103441e1486250075000f00e85002e0490b62000701c210a48032115071181c0f8143d4900f40440c2c1040d484000d105071146004d822610010302c51161000b40a034647c0909007030030f20103e801ca071149040c0320b002503840081d03800c004039240f0700380c001c14503410700b80c0d2103010000302c00b54503000440d8880c10245030703420341448219134007116280016004000242940d0068010340344020403030b072500e4003030001f40140da042501803510821107000707015481c1001307100414181e0098005c500e01014100b06030fa42c1e1035120282d40d0800110000201c0c00030004071980c030b90444e0405c43c50000a6000840d000c180310188902c90400814400940 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 539367383 1250 539366133 539366137
    0x2010c080d05090f16060302180312071101020109030c03051c0f0903020c0d03050306060d02090913140d09090c050d090303090c060e030601120204090609200114040e07020a17 77
    0x803082504680b00b010a0401300343e034895403041c0190308901155824031095119800400380d101c004102464400070081c0060b081c50700c0303002c84040f0882e0000300c4004100300b01c1815180c00b10240001c0181c2501d07600e01408441c40b8007001810454001016164001000e55030f840b030078180c110400c034540620f43c100c0000c01c8140c5051300076120f0003200c988136182c03a036004154190f040e5035250442d1602d2080c42201d070008151360b1030b1a60280141d6451381c40e55081603100e920800f000c1440180c040c18500240014501d1080c2c46810080038001c1c17441d04945420110b6120080028408441031000c54031343c00744400305111036003000086400e01d90b041d0131a65503140528609208142c0d50b12040d51508144042c094045d044a8010080c0c82c07140c010f8041e40500150001c2100d8038642d44034001c43d0035055040703071020340f00c45c600540c3c1c01d4410315000c002c11007130038180a0644420382e43c141c0c500440c462203140320300f8a40010f0040e4400d05c04208520f0703009250b0082d214400220314156 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 539368633 1250 539367383 539367391
    0x140316021203130b0d14160e01050c010f05060f062b11040306020a030605030313031709060d0507030608030c0304120302070302090708070e04092a1706061207050a1202010c080d05 79
    0x90510b1b103440484410018007e0051501c10101c000c2040704030303016603c92184e60740c5141845810f00502d1200c08007805404410108282c0000701482e05008025520f010340180502030f44080c09407845059034140f0300003000402c4e41c4440903030011459030310301801c011020181c404a000c9000001c1164039006090749960a4506004160f12102859900d0088800e01404694034031800c20208003003441d010000d608916031146040c0e10100030034280e0707201039654440700e9642c60030400b50f40c0e1300d44200009051001c02035860034a1008800d9541e0099005c0e0712100c640c05c001c00c00406001308500d4006540c0501018920310f08500058840501194850013041c480c4044882c103141520a100141d07a200d0080c50301036031020020304005429469528404c2d08030803012444400c1c100e50140c407855840020010361402e94148401031b00c08681001c442d510108043c450f550b82e10180b0415505400340d51014441103000481d030718600c0703900140016100040c0c00c00801e0303c5030051486 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 539369883 1250 539368633 539368657
    0x140f0a080124060305060603010b18040903051b0601051813051f0e070b04150e060d0b0102070f03050d0809120406110c0102060702120a02070f09020403140316021203130b 75
    0x1682d81c1d14078050302642c0085489561106041005020074900c0c0e50181840c03080118101d242441d4042c0403d0880f103071400c094010801c08101c07611130002d10309038010b2505102010744015458203000c2132090180d80003003d040304060b00003640c140c900800018250b074100b01117030150000406540440010f4280b00d1a40b141001c03881c00e11401c0004007002103030300c070444051403d403800010350184026283c02d0340c1000003e81c000307a240d039100000340c4008035000400180c01c512240002e440c00005601000d800036000004101040000c14108403015080c03d04121036554890486d0400010409409280a011801061103944460380d00d2903e94402c0840340c00301008c8005a83c0c5090841d10302d0b005034480c0080d002c402040d540a40310682d030b1401100c5829807500410001d00c1c0c110b80003042c08a44c040740030018482203038140e210f622144009946004444480b400a80380b1b179480107801800c41c1031a69850a10400031030b1200c8648001c414440340d01d0b61011403242d0310040074408 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 539371133 1250 539369883 539369951
    0xe06070207030b040f0311070e100f180207170d021801081311010c0f060b1f080a0207020d02190810020a020705270f070207090501140f0a0801 63
    0x41103000180400076650820040001642e85540314000d12030098003c40400410750b40600015504106240c041c200350900c0340d001e85808000c0042d604080da2112254400400080020b0381c043c0c18040b010140c0c2c03c8025031b0324982c40c01d080d0324540001e03040c100f844200040602c01e50700310b81c1c09840d0113502e034815005d029617410011074a03203606803062201c0c000c4e2040300e10002400c900d100c00d5010018140004850800d0301c0740d0100c101d8400040d0740140d1610607500c0145010915411400e11221b075043d003518203150001c01400004203040c1c9860341c00500802990b07600c001c0c100000d0390080c05882d00e511a18900c4159a039503214040c0680309030900810246014002d69400c68001c1e8002c00000313140500704105a4507405249129410313079150020302020041c4404d00c01c8040c22419810717806d010720002d152011503840241e81c0c0c0e250000512800f5101021403403420030469820106465071000240600540c3d8048503c80d80307030100b010b4150050351108580040d43d8003185c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 539372383 1250 539371133 539371141
    0xf0d0f0806011d0a0b0a020109170703200307020d11040b0a0b0f09120f0a15050f0a1d030313020901080102030f010b18040c0e03010c0315050d05010b0a090e06 70
    0x380300c003803060303074840d0200e0360404040200c03400240f40c00c0d4078018010700c50010300d0b81e105514651503010500910050751120240c8003800b210b03881e400b1140315003042040c6001210f0710010906680c00c1122840041c428545d600c2d4800e00300144c90003c1c0e0010914500b04809181201c3e031840c0c0d003000340e4022420001140040d14014181c64122131400181c0f83c5403000721840c2c1e0000780d01c07410600d544110a41814044035004200200b0380c0902c480042500c802036050166683e903022a584800b6400c20040110625030b049a03550000030380000818211041c01b01c04040c005000a1000341d0320022003002042c45860b101c1c0b540ca14000e03a4100e0940c0d0700c4600e018280e10003120f1440c012000c0c1c1700101701d4004070100802c0180c0580c050b8420f006610400074007511080b0084800080c0044d0192605250a10906110b0f8155040c1003000c500d40400d081000070551040c036215034072008600d82401029000070203152001007005811540744c044043c0149541d41401c021803041f10001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 539373633 1250 539372383 539372387
    0x1502070602030a0e18010b030f0117030a140702030f060a0e0307120503100905092a091504060b0f03010f06021216290610030c050706020d0e0f0d0f 65
    0x46058880641c091031418440b480292503650064410f96000100680c070444a01c51200c2e2860182c9402c202e2079603242001d00c00c00d80c00101c1a007011022510880400e052000004103c407000d00aa0415500c82000f05078151454056a8006901401a50455950180301188040c0304c2c0c007044004000b01c1c03005241403a80d03400380c5c0340001c0001d001e04650100c4107006101855100041030070f030380103031901d4000f0341040e00c00c147c5d000341080d40020075038503104142821582c131040c0e031914080d28040e010400542d022001900c00d409021016181c0d2030551140d40103d40038003400481d6590b1000f171580300c0c030714540c000d20400705c81080407200464041d1012402c0b1183c05d140c102454101071440c000c00c070075240f0400044481c000300c440b0080c1522030b01800340d12250603a1007181000d16040341802680c03801c00320010101442c1014030212260000296611550044401a01c0380d00c03951034007000301003036103240031107104507840794590920005408084045554424840e1482c030a01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 539374883 1250 539373633 539373643
    0x4031a09120922150f0608060108091b040e0d0801082b0806040914010c0e100f03090c1a03180613081305130905120c0c0928061502 58
    0x1181c0d840b40610070f1081c1d5442030501040080180360b0800540e202003000035010445040c1d00c100e5807400c4d602130820401d600030213000c0e8003190030b0821300d400303240c2900060b489802207015802c01c0749160080c50400d8550381d00c00c07405440d516048403034034210f1150107414024244248141d910402150460400402d000b9180b20503400040c51a03c0d40907001c103030344800000700000d4006a80360300030001710b200c1d030030b1019400541c40700025020401d810000c00000e0f241c642507000c2c01d040348800b90a141c1c09a20482051403614000412007014500384425480300e0f4811915010800700240809419100660050600710020340b44106154103103505c401c011039022030594180448103001c680f00d03400a245128000d5843d14105458030005656059551219120700340d44070790b00410000304012640c4040b54040c1041d0070101a16005c43d40c1c1e40881c1c58042c0034103150301c04a0404000745042ca2001a4500c0921050105001d01c01c001003815100e0f108408040d03106000300c850020074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 539376133 1250 539374883 539374897
    0x3090b1f0b181216030605010915180f0b03030309010509061003020108040f061b09060e0108010f09020c0f030c0d2607051e0313060b22090804031a0912 67
    0x50724081d0b1200c00400200125034200c00c0240d00520540002520030300d41c500f4003845c0b040000040c0381d410080702004551241441100098001a081c4614815a000400707542c920307940c003240344410801c1c90406403091603c0701c1d80510011050210079035041d00514420f10302042280e01c2e41d626045e9501c0e10800e00e10000c2c0c0440d0340c00300420b010800031110782842600801c004510f00b140d03514040310300510000824001050711909000c0c4640c408100060302c2c07401d1038101055410060110040d0181c5c2c07042e008820350002d094150700106002c28170107910702100341c1e038490310b80c4d81d08a0380790f40d0a03007100030004d0403030340c00f00d05220f200d902d501c1e425a036581400c3c07170301c1d80d6001c0e0705407540c1d8004803621100e010304130f030006070f411017503c002c612940c040643c03c0060025440d080e8150303a5201c030702500c12180b18103c6d5500e46042400880070003203410300410b548003a0b08200580b4800c0c0d8101818803002610741302076903104e40da9483d001d00300d90340485540d03041a1981f4a00c82c05912 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 539377383 1250 539376133 539376157
    0x1120515040e0d0e1807230d0603020a05030708150a0e030c0604060516020a0201110709060303090e0a0e0d0e0d0606060e0312030c27032d0c06120703090b1f0b 70
    0x1004641c6e40c900c40d001c82a0079080400c00008055110554124541c2010200314007454840e05c09204600b048243c41000789002d80003807101d5801d0101c403a444600da140f6036072403c003403440020344078902a0400d2055070159001d40b0f581d44c61040c403164031510101c8065402c14244404200d5213405807407503515084940d4041e00340e045050b80110350000b030001c1186018403844101182507291842114000c1d4402d440d090815460007903044008100240b41307200040c541030032400c4545c00412030b14140400c41c0351200d010707959100000e500311320702540504010300e40798001c5103441c2c100020341040359007100fc540064540c400040c080e888200c03030f500340580d01031107030440401c03901c01c08040307044440c429501c000c40d4850100b80741110b484000d034003e5041517540b0310300e66080c52a007120b03e500b18001c0c18101400101080c912701c150700400d0364800012000654480c801e034041c40d400c550200c456032090503e0348050748a0b03c98400c2e9a1880300071402e00040030744480c01111030b0301c5892 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 539378633 1250 539377383 539377429
    0x307151d011b0f0201180b071b05010c02010f0201151205011805100f0b0d0b060a0f030218040618050c0a0e1b0c030705010e1b01020303040201120515040e0d0e 70
    0xa50300d08642c0d0943c0c000490510503e00c0c1c510840c1030140381e41401901414420a4442115003010586c0c81200344041c8080891544107200a0364822880d4a107581c0a0070120302d17000c81814201c3c010100382d02c00ca0141601c0210200d8500c05d2601c0700443d960240009000c0300d05c420860070303e01102980000d09541c81240d0b01140136000d600502d0300c990b1b4081c80000c040000e0b00c08070701d00380000340084580095010030041c0a240c041a58809441d900325000e0f56142554042104165500003440000b80301c04001002c208294009105103102d41c13814042120766450202c0d40e03003083d4100d452180039082c0000c106070800345000e030712803d080000305041e80141485060381e5030082200b50700341e0004101c80b00210390240151620481d8040050443d102d0016148402c8100e880744141150010401d0002513a40513100303c00074035100c00006095243d4031600c0c0400035681c1016a0041c2c10803800701108103010a81e10852007103510b815800704194810420001c640b0300e5913510011171 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 539379883 1250 539378633 539378687
    0xd090201120e061602070e15041503031b081b0a0c06110606191d010801050105040203041101080a1b121a0a030303020310051f030f0c02030412020307151d01 69
    0x203040c1c451040b05440b801618880c5460742d583c020610b20481312281610940c0d0008e44040c1010705c10300c64501191800d5800702401c1d0380c0c004114000400019164207038291100b030611030590b044900442c02080c080311501001e0031804d0b140c19485030b09031829414408006145400340c100f040400c500340c006421140d568030700304182901c01405a1090309134603100464240e0885c10040f01501c503170900703003082d5031501c007815081d46d405800060045005005200000714086421504103d09091540003680da400341c50b03005001e540041e40d50316049031a1500c2e001c1d000004021b5104410a0a02c403000d0301c2c883d043e8401041c0f8002d950040c00c008020070210784207901031a0030a1425181c1e280969440c00060348051015030305041c0720b2980000500040d41501c14003540500d1040c1c20b110038030390840042e482e4015849000c0b21480f403240030004550303050007a030b0b02800760158055500a00c000008107030b800003070f10302040e001c10343c401040558000c51090f0b418101c00c80110020f580 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 539381133 1250 539379883 539379901
    0x1020c0c090405070906060c1103010923150117060a0908030c031503010603111306300203011409160b07030e13090602031e09070b031801020d090201120e06 69
    0x80040050310303c0d001d03004010079820350034022180240050341c1d849100e440300c0d0401440d80012008020b11a0b85450305042c0054251040f0300c4c08001c044d00111880a480360f852403c3c811141641401c802d9403800200765401c0f0005000e05080c6044106e0b15542c0c0c0e1000d0381412030740d104002500200c02400000c242800314401113921113152507000300c032443c056020a00756041034004540604808010050b54201142c4009812503014000d0041c0c0d45000003010b100102c0c4c42074050220ba00706080510b0500607508490f4203680500200001c01f00d80712140d84524041e82c2400365805035420720324003441441202004c0d507411400391440c203215580c0a0740c140e4800c0c09503d80100711400d0311600000c043c41078048840c09940096900d1501032042d400c103072401c00410280040110034407900c1040018404107884044204079501d4450b003020081400d07000c3c507090721541c000120400c3c2c030f48258210140142c400c1e04c0e0003091100d80404031080c0da400d5800e003100341d4410000a9100c034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 539382383 1250 539381133 539381149
    0x907090f0b1e0102070e010e07121401060e0103060e012919050a030608060718150c0206070215041404050f0412031a030304030b1605040810111b0a0b0901020c0c 71
    0x42c0705004644003141e440c02a8820300900342d0107401c007004184200f144040e00070320105a685d103002010442e10071411000111380c0c0041c000e810801175140134030903059001ea80800081c00d40e40c07040440c036603541c0c450316034102100e07400314942d4080c4070308400c461030400c4165000841006061074050792110b40889907600071070f410104250b00ca1000046804082c00700fa40160000e98032031404105c201c024144500266000001001000c402001340f80e50180703844181e03940c11503840f65251b0041c00003c0c00d640c60300d0131242809100280009001070030898085100c031003581c003806642d9802c0c0030600707401c1003250080c0c80203004094003440c580c803d5006801100c00c2903001e4011449403004645150840d4104a40301e00302c00d018001207520200c40c4403003010311407a060f440d082c1021182da49890380105600061516211900040d540c150159400d201e6007000c20700040700c81c1e424080d0b0342e801502c020388050309800701194501c50107000700c411400004004049920003041401914 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 539383633 1250 539382383 539382439
    0x501301806140c0d150314060601020f0c130e0705061b0706050703080a050405010908220e10061404050301140f0f01140f01020c04050403030b030d21020a030e01050907090f0b 77
    0x2c4100181e0200019040c52031170441c111fa440010031140c13600c0d50019103010940083c0144c551700030841000b040d5127113100842c9481e0740260103d500d00312521524030b0504180c011030350009011609880701c00e21840a001c190103200c0456445540d59030041d1a64031075540701400281e1400001050900301d50416500a880b40c000000d0080d00b6031604400342d00203046071007440b43c008403242c41141c4950b03a40700280513000b4000300c050070002400e020020040c400c003070034404c200c802c1c01c8a600d210400d039002003201074000c0c006c4011415501c2241d180c201d0350304c2100501c0c540490304003081c10b40c0380c5040c1d48103940d818859829110400140344108075a43c0e04500c5000e01d90681c64076613025407030043c0e100ea03c01041e6210528105810600c052460b41308118102c296041034241005040c10402c12051005036078860041048010301400305110786198280380c01d108120034000b80c01c0d4111000302c2d900700161500d01402e50107482c103900708164440300070f482248880704210241540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 539384883 1250 539383633 539383661
    0x40b0d0b07050d0c090e060f0a1703030103060507020d09030303020c01020f0c0703050c090c04060c0804031b0905100b0415051303060507030f0203010501301806140c0d 74
    0x1001425610508040c004075050400100e02140d82000300360355020384211300c80c0c182080d0031114280400100d20840c000d041d14031866607540f80e100d141e254400307140041d00945000c40c80380304641402e10b580380d2080c803086911b0f616110001e4820351005c209280b21210701d03901c00350018655101240a90403c1e00d189607155400c102c50801549040001e100c03940341e45c030280c80454035506000e4108070041400c1ca0007004d00c0810001d17101c034200211030540781103040ca140700009605200b64035020755007004000e0041c21030084400120390711076108503014080c09020a86d074000c0c01c0301c911040b134810210f040e0320a01c000d100d01002e1307003c4522041e600703103050f60409019000c01c0c0c1c55900c19038009d0b1500c035a100d050200e02c50341406661085294140150b246524250008201407029441c035000c40c00000d0141c04a20640c03c003103460794100b45801e12502c00300b103525030f441c0d1b074646004076400e074a4860b6a0100306c07818044144140e10509400703003460301c451802c0000d80400074501305 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 539386133 1250 539384883 539384899
    0x31f081009051c0c020301110a05160515040501051006050a0504060e06070f14070e131212051006170f070f0201020c0601090c0e0f060f0f2104031e050702040b 70
    0x1c528100648000c80301c6004e80c1c50b00101022030050608450394107034601c0740504100144290a0382000440d42c1e0082c1c0402e0701800c64406081240c00e0014a29580345e58503202c40a04c010b000c0e0540229018502c80304120701d070151780d044140c80c18854141c1001c04108140001c200c11740c015240c0c00020200901158640340746951000d18951840a00b211266141151584d00d000c040102c2c0015102420340ca03c41f84c00c103c0084140e000a0398001800c1d00c03500f510400c5103500c200070101d0f01e44140c03002803040c0d05213060440c0c48140103000e00707400517424442d01040e142c0b000b8500c0740a81450903450302d56482d03080045520124042070901550740170400208010b00401c0103034000c00801d100090400800c5100800c1d01c000a00c10721320400081011100541c0c441080b903410f07a8101601d6551514540d041c41c00314007800820b5108003014031810344008019100340c9100b98070030707035924140c0c3c1044440c90000c000c400303500c4c000040c02400380d200141003980c404071300f10600030708a030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 539387383 1250 539386133 539386153
    0x11090f0601081306110a02011508160311131a0321030121120203040e011409060402090406080106030c050907080709031104020c01020c011509060803220e040602031f08100905 77
    0xc4170a42c081c01d00900140c0d50384102000c140c0070f0314100301c09042c3d040094090382040ca41f00541c0d081081c00061b00c0300c0c2e08c0c5905071030300e952424a404200100404140180e0b000030100310317583c40f00f1200381400703800380b000d542d028402c0d2a0f03054007001c4000f962960039030342400e001c5680a429103881e0305840c1441c0400102095001807400c0007600d1a500031665241001c2107904541c0c0e06910409201d05400207503503456444640340c0b5841a000e45006844100c0d0400083c040c008590020686500e81030000c130510030b81401c000c05841e002c0d030b540c0d5030a0b220084111a0750200700d540301c0005852400c2030000a1340303520500480c140c0141f002d07050100102e00c160880c0d02a10804400341c2d51221881c5003d0700c141e00b141e00a00c050329080040c01d141001650312803081c0c001196218031441040c4074094484c4000d040a0501440244807a140600c0c20030025801900c2c04403035110030078010382c07054403400085000d549400025020205401e09550003900c060740c0221594080c4038014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 539388489 1106 539387383 539387411
    0x5011509240207150327020904030302030903070c1d180c01030f0204080708031329030910111e0a020a08070609050a11090f0601081306 60
    0x9048080d14404040f420301040740c2000001c84da9840107040038683c158003548210000c081090b14504140d400f400da40d01d503054000354070116443c0050002403094002c2d5412050f44030883e401c0610035600c034501a1b03440c1d00114000d0314414041d10f40707100d004815580203000085a243c44000100310030351121003885010341415143d00401c02c0c0100107a040720b0080c103289080c0c0d0318864a607040e840d200e0b40100e0354034500807040d41d000304650b0094001080c4911300a41c0340c064541c0043c90240c03c641000308040c1060050485041d07054000d4003504141101c84402d4a58440213a00c40d0340c00030302c001e010000c001e0301c284282d111094001941c0c03103a07103411655075500c0742e01c0e03803038800e02400f1444001800d41c06108205410000c8104070040740c4101111110103617541d00c80c450090710402c868440c001a1100041800c0d10012810003440c20b000701c80c00319406801c0141 = true := by decide +kernel

theorem cover : BRFrame.Cov 539208633 539388489 := by
  have h0 := BRFrame.cov_init 539208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 539208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 539208633 ≤ n) (h2 : n < 539388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
