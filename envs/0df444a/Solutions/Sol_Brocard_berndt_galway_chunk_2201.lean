-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2201
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:58:15.581974+00:00
-- url     : https://prove2.me/submissions/95a32ea7-64bf-4c84-ab88-6547603e8a8f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 395683453 ≤ n < 395863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 395684703 1250 395683453 395683487
    0x8011404050106050421020a0303080603060a0e060103060c11060408190e060f07020a0305010e0105100501020d020736150501080c03070c03050d09030206040212032a16030c06 77
    0x1e00140821508001a1025100d2501c0d8442000318240c00d200c0c5803c04806020303410202c101f1010061541c0180300d00d200e04d500390101c1d03407a40c407000b96190071500c0d604020091608501b00500000703100d50001002e48803685400101c80404801c5030307084c082d0540301121681c8001030603d41008a6008201e0f540c4554100090121072802c00304800d0b21494441540321f0741c00050940440d51804110409540c011000700958140555a28001c0000355055144030a4000002410b0b41c40001c0740c107070300819275018210280c601202000058680d040e86021401c1507044940500300b01038000340c2d4010301450200384002c00002004450089422060421104408100030850a0011250090300c10710f8007280708849400c00715414043c04203030b104124282a00301090590002d04940107034002c07115080700c01d0401c1007140d500d101c1e840e5050020000d405100642e11104001b5008500090054a5803002c130b80d8a1100da031000e03030704110358070110300c5401c3c000309503c400e0380c000907a03281c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 395685953 1250 395684703 395684711
    0x105090903092103120106122703030c020c06210108010b0d03080406061715180d1b02040c110c04060e040f0c0b0301080304080c1801030312060b030708011404 70
    0x12003c502e1449205000c1d2000248009403801c2840f4200100c604408400404900ca0b503100c0400070400703aa6542c02c04889400c01e200d0042040024100314840101d0902e101841070180d83c040c0c01a00d0001e02142c250300620400f01d105403100710091510701e408503503001c0105c00703049030b2090303400040c2c0002c021a80350070340c00a0703161601c1c2801b0703602c0c94141c10400b845070340310b1801c0300252120b40c22444d050003082c0c6070440b050340006401c010b150034451626405560f1010b0031240e19201e500c21500070f0340140500401280984208000c00302c100403016180340c51500850240d83c50703071180c000010701c40c5035040c4400d0000e110130302c40900c048805000c0c1c0307840c0545c664480d00000c1c0020b0100c5501c5503c07881080b8145890b0b100824030170300c2c0140c5a40e503d00e0229201c0d00907208401081c094200d8240d030b00d00d070901c0030f401d2040c91204580c0320f503420740d01c0c210392000144007035882403503890001259049104024600c14419980e80351f00c2d81d070520903c2a52080b000594900440c10 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 395687203 1250 395685953 395685967
    0x180302010e0d140f0409110a080f07051e09120a03140c060a0506060702190906060509061b030705100902270a0b031501030f02011b0b0705090d02180105090903 70
    0x3c00155110301e4114140855110403802c01c0440c12841250700c028591450155503070124411100500000155070300c9182e4a0350742c001680c4100d400840d5000000340b03007000400541c5440e040103042c0542c1c0b030001182051841004112901c084800400c1030342c3c0f10075012000c06500c5203288c11079440c51000d1f2402e1841c2d0b064190359580011342074511154882c0700054a40d211413094a0038107800070240384410314451525800034045000d210307280350801c1c1d004640c85014204503003040e1000340145e031a051902d888021030910030388000145000403c242d0b400702d50108910800250083c80000d001c0c80c0340e1040029442074054400d126120000102120b400c089a0b519440090002c0204242118000003410486110350340321034144007c00100130f1101161b14401070510031780391031842c041102034074043c45035910030041c0000301901c0003a076800e1113200540303180341029103103180c400712035030000ba09a41604e610700030348035038440100614039058030103a410010b6080950302d840c0e1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 395688453 1250 395687203 395687207
    0xb0409060519150509040e0303040c0f06020c0a05090c040b07080301180b01080f10120506090105070509031209011b0305180a081207080706020a0914030303010f27180302010e0d 78
    0x180c0c0343c40355014000c001c2241800c83d15640c10588280170094103403556445c0c949060200307010140140b600c1008208008100f8600025504a0505004003c507010b940341000708440408000c14420012109010020340304010401803c20719101f940703840e0b1250304040d0000c40903e01e407809040044c1c1402c0780c001d0140d81010400e9000104030715811007a035640016441a5501c0360300010001060407215001c0c410040b40ca180501c0c202c0b0002c0c4070580f00d20004840c540112109203a240c0c1084036403000fa040b040c00107040c1204181000d08204440c0c80030010a4035001805601082001420107554891303d60b8441c001070302100c3d1811514181400340382e071150b0032901d5408500c00041c18205107d01d05003690081a840340c0300755a0b0303158005000b01030048600c05e138040041e40020704100ba02d0040141c80c1a190101b9011203038515007031b204009482c0c11446c40e0403001001c2400142208603009840d614680204440f04001d01e0b490000d003106d100300c44200698111030785081141e5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 395689703 1250 395688453 395688479
    0x3180c0d1104051b03070c1b0602071509050a0b0a080f040c0603020a031b0c0311070b0307080a020d0c02210f1602130504111003050601140c03040b0409060519 70
    0x11080d81e00141c41d1341c5421034580c41000c40c89904082050110070000140c0e44481c150020500c44d0401100301c0400d4095030381c00d00203d0003103c001d40c1100c071003405a508188070300660b00362149040300f0a543e4442c0803480580c620380200014002c00108100c1d9950000d00e013540080b03014131a0a224a425119a020441c00340584d07010940c0000700680058401d0b0000070050741205001401100b003d44041c0403412981821030101d118641402c0b0740d204049084412a4181044145903903500c510846084500810441c440e40e401d000c00b5401e24414850800700302c0041e0000d040e40898034941d807624894540b91029040e01c10006540070604190503140d8405002103074108129051001540d801100600300c102d8500d004200801d01020750703600030102105844110250307003000d004805849048840c46e0226003642d01520020784035500401082154100341ca06080c0c407130003842c6055026034030550186449560a04c100d150506980b01120300b0419a0000c09240030b490103125 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 395690953 1250 395689703 395689733
    0x31409031c03020d0e07060e1c030f11010e01051807030305160c0e0c1e040305061906080d020f01060617010e04020f09070302130512030412060b030303180c0d 70
    0xd0003060140700c1d4060190b010388481c5402403005000078031445042c29620f21140c0304800c0055600a100d00042c1000c240310140581207402d03907860312005444c25203000d0001280c0800f08101d000544121010030b102e4501c00b840d0381000403825007040e4143d11141a01c0e59190700d21900079100c1000008d07004400c448400c0101c1e5501c02c034030845400c0200000300e0961060004804160410030010b02c440002e0041100700c0003040d04540d02088000054040c41c00014403030f912490202d050b20f48603141259040c04080740108010703856440b00b80c01e010400c40d03220003581c00f4030b00803400c105e02801a2005040b9528080e0940f2580c00440996010180710310a2080c00031001306043d520b8001182e0ba024802a01e140f41504103d40c00500950100140b0744070b020240300040746a10b0101030030121844520011400c1c2824407108a69030012140112000d540e00c00c8a4181918244007035031103181e90000c00c18150b0b1200d83c0803401c151080003a42d2042220444003800508005191000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 395692203 1250 395690953 395690983
    0xe0f040c030f06240f2d0e010312030209090c03190f060302091305030f071e20040606050405040b0118060917030a080103030c1a010b0309010f02030f040b040c03080406050703140903 80
    0x1d02c011094017540c6c1007541c0340f46520400c107003004180c80c5400f403c458126842000401448401400d0440490050803200c0303500500c0c040102d03036010000c2c40a150030540d00014800e4401640c1455400c880c950700b54149107035107030f050400a51034a0401298444d50710f80070301c100020256103007901c80c466101d0b0a080454046404414040180d4640034600700d04600b181140440d8180b20781c1804a0305080003108024886a05443c01e103401190304036501c43e19414106400c040130030018014466880b410400613841d501e515043d8518a50010070300c0303440e880911801d0221a50300481d5041203081c50303034030400c9a03a25503075014204504407605807806507212b01e920310b00541c04640b03600c00c05ca56100d030b120010690110341402140210712400c02040f5220005070201c0603404100e800c0040c2ea0300c0303280000e0200e18080f4020398482c0c810700c0d0740541117840c0c0c3c0d1000c0880e00a9003050300040c4c40070854104243d0400080240345481d1038089041091040020b5070340c015000c41100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 395693453 1250 395692203 395692229
    0x40b0d03110f030a03140705090a030605070c02030106140f090103031d01140c06060a080a0515060d0b190605150703110f011a030c0a0e0f040c030f06240f 68
    0x800090101c03215000da07090030389513280c0540100401800c00031601080702c40d80c00c2c01041c292400783c1d084a85021020300400d0320907145407609401058010303c0c940601c00c4020014005075420320900c006481810036101300c409400c024007090743c483c14403003406080104014030100c0c1c0c204030709841c0101d21a00c0d03260f0301c0c4000300040751285061048803a01010208031400a0b03140401c21030300c00c0d002940c040c00a16551110705030340d11940c0001500030742010400c3e112440c01407200340e61101700648075007034040706a920101202c43c112415458091508104041c8030018045c0f100245002c40c2c5c00c5026210500c44508280304042008003404203058025142c00e030244011210010480001c11940c290060343e0080d0301240d0b061a8800d0007001d00c2145076150405900040d43c40b0030340c000d4660350301d400ca01c50b040740d4090400c0d50358038840b460003c002110741c10b0701c030003041c4a800041a010079040106068406003842c0f50300000460509010b51015080705400b222920030210f1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 395694703 1250 395693453 395693477
    0x1a010c0b1302040902130b150418020c0102121303090909080d18051906140f040201050d090b0a14060102070302010228050607051b0703150c0509040e010f0b040b0d03 73
    0x81c00074168200d0094106020006e0b0718904560f03a48844c0c0e00070800c0d5000002c80d424000d061752640704034000c641c40000301e0807498101d016164050f004505d0410001450f1407400c1c03c1100803600229202c0344c1003400402e91204040c0c2c442803140c01412406800c0c0240d03031a581c3c0d8800207000b512481604142d58612943e01c0d4010b4203900c42c12035411205440c040c000700004140b4014410600792041d40c10824181c07071035000784000c0b51181e40400a210555100c070b038011601544015007001e055a1502e007500007003600b00300603500603072400e4030004a17114407060004404000500c07807419502f00e0301007003000d40d03004030310314403101c20703a00d440d1410750b0022104a20180f20058047c20078483c04081024064008004081e002d06885c10300c0b01004110055582e943d03800d000040010a00701c8000c00d048030250020b04c0724400c24244541807031400b80100301104e44c0381e2988861a9154000b40d004491584247e03160301809840a200c981d405001081041c10040001410025180060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 395695953 1250 395694703 395694709
    0x12c060427080421020913020d0803090c01031b12050a02040b040305010c0806120709051e1f0501030b01050f070c0308180406171b010e03101a010c0b1302 68
    0x400c2000c10780c4008440039030740d8201550290424002d0015188001516500124099290803002607008007044083e80e602201380403100b088041c1260009020b4216030002a002c8d0040e600c51134500c402041d4120000300018180d0300c1c890a00c0c3c0c280742c0e07441d81d104503441d403040c21403080c0e600108010400d41c0f034401083e0001e114551120400b600082004010030506400c074083c654410b540c5d074581a102c42e02003001e41c002102809c02d0b5980400303420045101a42c10003a8800490104019000007504091078003e00c221505440207880d01e004030341d0011076813520400340c075013840e00b002072008020000c0d005102c2d00044105109003c00e008040001c40e10808000c1c6503c100750645481020070801e08035581c01c076095110304d082c0310012454000d42c5003400005003910f402400102c12280584500c1c880030142641001700c01159506941c408024090255203801800100c60281e4400211b42507400545c00d1b041000c00e003410b10200d0100100349400c24490005080054a50702c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 395697203 1250 395695953 395695991
    0x21218150c030a02070e010801050606120402031501080604061b0c020609060d0c0504090c08040f0320060910050609010f030308092506110c011d03070803040e012c0604 74
    0x700c11480d00c00000d950685940c00300d440000c490002d00748030003e98941501138280d0b0012a555900705105108580c604030710070b54400e0304240042c2c150b0b42200c103036000c2002244000d800408080d8001c0052108100e03480c0304080f20115070026100c821038101704014202119424040e1040340080b42007206035035148200c032044040050f0410ec0c0000d41100030703095800500c0380d08880c0d49032103100f0321000c1c0641102441140d000560006503011179400303030340041d103418081002d88903070815000760040c1001401d000700c40b0000244500524032403004243c4100510b103c1c025041c00b001000001d204500c8a02039a40c9400e000b2801e0341c84100c0c05107006420b0031806501a96400f4012118551402030301c1951480c1c1d035038042651018264550300c009200f88a03000421111016405244000300b4041c924402001d07030720000d40d109105803030747d08542c0012062980d0314004100c815080303910040d0210465400e4104156814008618100300800c1c3d28080c503200c01d504201c1781c0401007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 395698453 1250 395697203 395697217
    0x12050f010203180f0a170d0b0d0506061003110a230301060e011b0317060f060c01020a08011205070620010c080106030c031107060e030c1c02121815 65
    0x2107441e80b42001d0511043e09520625122078001c10040040400703010548481117500718002007071804640c5102c40d19035000c104180d2185648000400d4540e0303c6006007182d85000e68001e01590400304100003d4044010614051500c1c1220048050070b240303041d203a1603100d90406d0500034500d60540c0c0210880c9031584c88280c200000085092900003503484a080000c0c1d1b502a101403a403c034010425203080c402902040303059205048a0b440411400d602801c040d0110300e14600fa5008101d541e001034440014694000c40c84101040d1701110050042c2001e4413500340455030340d114a91a441603000703440c01c01c0a624040135182c03806006800d0180e58550081019102c0303944000c240c41070030b0099400107070a000540c402e0a110b4090405540c443c85a40e92a1080658601c401802c0c1d040040d001c4e404184019600030720203005c152040c03c01001c62104011150b0002424100c08600d490a40389050044540410030109050f4a902060305d283c2d40302c441d08a002d01031402045 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 395699703 1250 395698453 395698483
    0x914070602030a080a0204060c170910050c010b0103090210030b0a030c03060903030c05090102030d1e060e150907051b0f01020d0f23060d0312020f030108190c1205 72
    0x22200003562680000184060b0540b07a81e0300180c1c2d20303103005030704c280c1c82144542c000050300e810001c40811807100100c560302c031040144520b0034000501207004c60206d558030310080b40c804126034511480a008030001c40c10309280070002420241d00080c620310780d0582d0903080603600c20040c0301903251000041d0223580c11100e1885c5076542e0303107005009000200700c1100064108440c10607811301980941d040094140c01940c20068004d50507801840100f004103021000c8407030703d0b00700c10854400d41e00580134802a0f10031918041403803200e03c04594440c4da009010388020040d45e00d90003000e81f2020300714514140c018041c1c00c01400c1c41c150044a8161055200180c107054042056000c424911440c0206008080031801c049604841c68021114003006d1040003400f189040c0310030300c0c00248a801c1040c8040340240c212412608003070054841000000018880324408110400036606500003d0030f090040d5070700c41ca500b0100307204102d01c0000784085003007080001d10003d041c0020007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 395700953 1250 395699703 395699713
    0x6160f02150a1b21020c0d0c030b071b15140f011517010306020f040f030b010303031118060901030e03030a05100e010e190b090906150406030b04060914 67
    0x402050007040e80540190310120782411008001402031040c1c0203440394214490b080301c00c030b2401c0015024451124400114015030f2001c540e2540c400015100d814045c005c808405811841c060a08403c05450b103028048081052280302c036040040c514904d0388001c214011101d40b0301a0405002d00e41907182c5403201031010052500c03141f4a1044c121801c0c0d90303c0c00f242c003a40781c500741c0764202a4107144c450102d02c50300600c08600316400400c07500740910b0009160607a240e21905003402d450304210b660030f0b40310004005041c0d04d401803140e44844458194585402c41e840040c242032180c5906d406030b07401041c0034810f43e0081e0710800b0229801300549680c2d240440c0070f44000c05080323400380c01e144104000803c03291940406107041e2048141d0003106a1140f240d400c80c440e5801d00c080e5640e940340c0031420b9590f01c4a0000354000c12102004000608101d9158100395001c5040c00d8050f6140110800104034a00700c42c94000d604404001b55900407410004003507030880c0341c0b5064038854 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 395702203 1250 395700953 395700979
    0x30209041104060909020607020d0f0c0e04170c101a0402070804051003050606040e0c0f07120e030d020c010311091207090b010504051f020a05100e100b06160f02 71
    0x802645001e144088808008580c1c50f035802c030302180c1d0404c002a421030f20600c000c0d00142040c1d80c032004500d000e40c0c049008030320b40d80e690b07a018503400c1d0010101442c1c2181840200483d50525880d00c20300d0321480381c2444058800350ba90349000e8603001d44542d0301e5070008010380140c2c2c035900d035038160090800d650710907150170304e190b0a40c482e204a501400000e5110500303076100340300f00707401101d000b04041d1600d46003035000c0302c540314041c01d8600b90303000030420342d0101150360b8001c12440380300e08205030800d5a103035409000c1582154034240203401c003000044409138042200a0800800d08000a0012071004131220314000d25040d0754001a03000e502c070040341c000254007011a1805a010300501484d803004440313500035481000e8000d680c0701d4103943e1a641c0460a2032082244c1e20490300c0d8101184c507810325114029584640706031396814030064400702484061908008401c050240c0f1220700003050451040020302081c00002d80710318000c01c14155100091560020500c07000441 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 395703453 1250 395702203 395702213
    0x50f061c0204140f06040509011509121109090f060a0c05090a08031e07080406033209070501031e020a1809020909090c010903171626040e0a02070c03020904 69
    0x20020b03c400f442400003c0e88280b861611008807000d49001908000459290a1060495190114005051028400004c200e44540003506060280582c40100b01900b103c0c080c004500e0020746403d200c0e8000d80315200c08203c0000d00030780c0004016900180c0341c501702000302c03894018114002c1d44400c3c2d511001807030300c60000140460004011005215182ca5503210b4094490000e008050f15003d10041105a01030f82c0600c80b100c2222400040441d8651142e90020b0751403c0c50b5504241a030051080300d0030208030940c003502003801c2c10480c0c440300d000559041920322842e4251a500042e03a201900d1040711034021480e641e84c82055850b44400b503040c040e400185070103000e0701940f80014841a070000b995103c6400c181c4615040230f04640718103064048600400644030410032404110034080412041c1c0385002c1c210200182d01d400100d040065004250705d003402000348803c0c808041d810b540e40d44c02c500380540040c0d0f40d2040313145c511000f803a59800a580b0144000401081c80 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 395704703 1250 395703453 395703479
    0x1111204090b01050c1b0f0402070b0f0603010e1b0d0c03200f061903021306110c01050901020d05070c0312050904060605130302060d14042109050f061c0204 69
    0x24003052014824826880e00440f0b260182000d40f005d2907000301904501c0c004450681c2000c0c02c809400c00c0302a11510700801c0c00da034401e44040701c1c000040004c000b405c1125440141d000003044009201901e64410510341e00d0421504582a480c40c204203000d035640c0d90001040794503408014480090342d2410130291400c6061100d103404c20460000244611f001c0ca5514040c9900429036400e008000044071910403031400c00005059080240405108110071001c00a02d55540c50040e080403007031800b0f05045640110700d0500c9030074003c000ca141c0e00455410780c118071600d407054541406081c900c28601d0103a20260400a81c041c4a40105030300c02c00800100209407014410b007541c500003161a0710450b144640a158039000a02c0149861401800e141d41c00d801c020031000c154407149251020203560440b107060700b904a45000c4807410f07200e2202e0490500300b83c54401c2c6072030089000b100002c51380d28854a0002003058615030382003107401202286180031501c60f500c50300828400c07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 395705953 1250 395704703 395704709
    0x909050c0412081306140304030806120319200a0b0403120c030b010806100905130615050307120603050619020d0606050301051806130e10050a1e0507021b01111204 72
    0x19881d041c070105c2c00701d00540c04080303120005a0400d25564864a04a0b000310b0040e00a0740e1012461800c068840d004101078040c00c0301c9201c0401c0da4600a810280240e107070142105400c114103003a038034180b50f010902040903600310301c01c4c0c0220303516480d0868041c0b02051005203441d10380200c508003107505602101e003120f400c0e20384409039101c0408020918001d40e407e00001684420b01740000d0800203400d02490f0998080402c2742c940382c4108480f9512040e60050000f04040104400d165028051240d5400b80c0c7d9400c02c5024295100d01d910395000408950850944850b4081d00d070009504984082c420f440d0b04101c42c45c0c4851000b00300380d01c00c1c410030348541031078420b0f5034900b442c0d14281c6014101c000d001d07448094018040c0300c041c0108611810b024090200e03490413155043c09014407403d0400c000058806040c03c5044100c0040400120001e2620341000710190700040c0d2202d5000001c1c00c2c5aa550034110012580b42c5011100040c0354003e411100c080c000350b00000e001070f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 395707203 1250 395705953 395705977
    0x20924070317040507031e0b01030b091c05090d020a120b071101330e07020c13050c0702040b0f040608030711010c020105040902251a01050a060909050c041208 70
    0x44000c080c01c1c9542e094a064401500d2508004003c100099403010030a2680c44078599003107100500d0744509010740000da20641c0d80c00401000c1110101080c0314100510310b005c801e20203941040d901c0101540552070303040b4021030303000303162009541e600e80005009080740c2d41d6138059000710345048040d502d400e86100c80851b641c8805184c0c0305606003c2c1c9540100c0d90038100c0d48075041589002003140b400c00c0c0405454450400c04903184110141c2248a01c0e42e80d00103000b402019014401602c1c00502400d442c3c2d4601400d1040564240046500054040f100840d201d201d48000500300040c03044a140e229107810b01c00101480d000c009003014500034480b00000000040054613610744481000340042c00410040c801200355902a001003204880780660a0302061182c1d0581c1800c80c030252190941000701c1f180c0b080301c074803000b805840c040d110007040b18501030014214041c240910504551160001125030007000150340080c581c0300c030054030a4100e03040090310783c0c3c00b00e0f4050003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 395708453 1250 395707203 395707217
    0xc09090b0f0c0d0b04090c1e05030a030f030c090801050916080601051c141e062802160507120c090b0102100216050703061d0a12030209240703 63
    0x2241000558078144103550300d540041c90034500c215480300074041e856485a10a039680c451a0124030318050020140107500303910000300c070150015000d0103072223500c0f20f813081c0d0203c4207040c0081c2d801403c0f40807e01c164200424001000c08055540388a142c1250b00c4942c070380300800000c12400601c0c0d08201c00010303880100ba540304d47c085500c80d03000b40103450300301e01060000910b2045514000c2140c5000c0c1c0280d004c00c0c00100311207428640c1c5000b044540041d51090441c50b41401e01c04d40d60451502d0660005c078041c920f490b4030003510441d000341c4000381d001c160740700307914403106411000c140c4c0003081d907400d00e0722017503a0314806081d00c50941e6583e4a403000801e21104610440d000351030140c00030310780000b01d40d00d41d9000c0d6020040400c91008030500c1c460008100f041014083c62186901081804980601c080c03004a00810380d0159072000e500400840c1864a00380c0340c41d0801d25025945130032a20100708440359102c1c00089900c941c030000c40103c2c52080c06003004501c03030b0b41d41d80703 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 395709703 1250 395708453 395708461
    0x50111130906050904020f150403030804021f090302061e030c03010815090c1c06020307110f0c060f0315060a0903020a0509012403180506010f06110a08160c09090b 72
    0x780484555010380d640104100c03010038050325010300011110350000b0580007654100700160742d59500158400c6002c07440d90400c3c00110728085c4c0c1446400d00110301c600c00b2420203203500500074205440701074040c41001550340e4000c1904024407040c0c1710301704500790380c0303047c6006d00c2030a41e031003449010118000c452060350001e51030100107000e002c003030008103007907000340c4108142070300e078000c502c400140c0050502c0e00042036400614410300250b1034454290780005456814241d03000e4082181f40c1109101e10300d140e69100c1640c0c038001d41c4401c065141d588900c10141006407580005520030000310f60f01d00c6007a0f00c403030400e0580340b003624020016980c030014480c07890020b01a401642d01c07001d5030b203404091f5010500b49110924540410000100c195000840b180e03450152010f07004000103000001c01c40031400001e104610340b4034440001255416103c4030410f4009048600c00201c0b002041801071441c00007a401c05440429a0369503000368004211101e002c50f403a000000000b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 395710953 1250 395709703 395709719
    0x406030804090e010b0d0b060f060306010903080306121c02010e120301060e01031e060504050c071106071b06031a040b0105090f0a1805091e03071e05011113 69
    0x1200d5020402904203420314000001404024814960a660754683c0d01416920742814004041c0160140017950800e0070070300401e020a0f031205130080300100140003650368080c0a072001c40340c00089040c0c0700c0d10380000181d009980d120420703c280c4076540300b545103c0007500031300b4841a115002001101d0841000c1602c960034200e2455090409000401c41e25002c0d100c4c0340400d0405160025400601c490300822110f008402c50f815155210380c00d1000c1e051900c9015044120070101500b44061641c4200315a000c0604650080f80040303014030420111505078400021201065200c1584a0340e00800608081012407102140003810103094102480780c040d030001c9c184d40c2d451400790325000380640d54000120240c1c002d1340d41240051503030700081030300107401c1c42e10101054604100910364030707203127504290b48c450b90980c0b07034428540790b00041190210f66002c4142e103481c04445000f0f4136900c241820180c000d5080080c01580d81e2903501c01071902d42200e10f2840755803070b110241 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 395712203 1250 395710953 395710961
    0x15090302030c060903011409071401050f03040305071401020d020a0e1002100c2007060e030304140405060103060513060509090f061f05130524060a030e0c040914070504 74
    0xc0d4160b0031040e100d11207418401c0040a01840240c000f04000c0702840e00b80b0a00007040b111034480d904065014040fa4400b00c0040e40340d1842403070301c075042600091102000f0701c0054001001d000000443c0c50030055403161401040728110000c540f1034054038543e4001c0e40c400e020000c001120000c2125403403502898145040f8903513401071440c415103040100041c07900c42c4d100001c0c001e07102d88000200f580b4040c4a154244400c02030f007107080c5041c0c806410403c403540c589210340c0007444144101c08014591500c075440441e00850b0079103d800041c1c0080c45103400040e00a080700c03494002005c040d810040c1103a000391581200c1d917491150040e11508251102c1c8410742020010a03d01d4204441c100040d8801c80101981e1550386d000040d40010b0041c0030b83d4049403180304224240708468200d0220030503030381901c844201801c000031010301c240700c80c403824190307600300c000e1200400700964422800b018108010030b9100e402c22030680901c100320780c0401d11030304c0740120326400c040c02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 395713453 1250 395712203 395712209
    0x9041208061c060509210c070f050319110a06050c060123010302030a060509090706080c0313030804030e090a0915091a070507050a03030501060e01020a0507090c0e10091509 76
    0x400366240c1c0344036903c04003e058040c26158091203040c000d40d9a0488800003c2242c0100e800c0d0a40e886954000c20740c240000d81d4483d410040c10701904022580300410000c900009a00904814654030306d000d201c01c11417200c0194010440000101c0c9250700a401440302c1c1500030100c0c0d1090f1303030f82d0103504a002e40b00c1000072403031100d04800d83c80c80d5000790085c42d04000340b00c002198107615a404501c00240844001e9803070b130700c076100800055421043c07080d0801c0c01100800e21f907240c40e88a02020540700d820080401555900081c1414031032203800d412400e00900648003410103100c820090219400250385c03281c03180c803a11400303500034840c2c3c15400b9409802604d0000282041e07079249030380140b0300000c4c000204680e100054003170090040d010b209840005495041c454028100100c8030841415544544544004150001050740c00c64800241c0860000c03e10242140c03145060034546410200c0031000d00c1d0802e40101069098580b0200c21110710f10440d0000c0724001c0c0984 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 395714703 1250 395713453 395713489
    0x1305120c060a1206030807061b140f0c01021201080f01060803070b13050a0b040302010c11031201030b0604020f0c0a0b0c0f03150d020d0309031514061c020904120806 73
    0x2c0091038030300a140c0040840100f50f000200c3d9540d94a44104075409000d084034200d507907903d801c610940043d00c000030f6a24901c1c241c480c8080c12580d11004d4801ca802c03000b032190010030b003103420b14425011a18904083d202c0040710b9651100c196544400c509511030141d42030150102d20440e0020685204540107070060310a40c444011803010940c4c810010758040c002e40f0707c5280459203808600e0301492181d800001c008003038140c0148485814689551217400401ca0210720901d0540300703038190780e000382c10758119031035a2002600070720031441004112000411b60741c00c01030000c550701d90b500f8080c1118100301c3d581c0340d603520b40610406c2d0740c402540905001046005000700014052103a02612164100b10b17182c000078002500200c00300d0000e104c101050041105e50000d0351006090314400781720034411040d50300c015110090445005c0c030070341d0f25200d480e40c901c102c5008500e5009401c0802c01d0420f400d0600640040c403032110003040c084408100d050414207014410342c40b0360 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 395715953 1250 395714703 395714707
    0x60302041b02010f0e1e1216060606080108030702010e190e04060606050703050403170d141005010201020c190812100801110f0a08040f021504030221250b1305120c06 73
    0x60029900b10800c06c0024200740b180700b015540080e10000100500101ea01c1a4020340071145013400a4a099410882c1004844070040006980000c10303540040c0d0709090441d0280200030104500c00e0700128580c560310310020307000072a0048054468000c5d406810705000700380e00c502e0162107034403600741d0050000c1c504100c1003001c142c22018980005a400000ca071800000e464008103940c00000c0e0040d00b13070414401c0c02000900c1c0c0030a0401882d081c0025424000f00c82070654a031014602d8600520b14440600810485580c0440790001d000c0c03da01206030030a9400700244d86680e01596405600c1d003107010002c41c500800340c1307600c180c0c200d1400d0704e4452090403c58030840c001d001107034524500950318005a5555a180484054800d013041c2ca45165004100e15036001000b20282c1d11211030312016001d4021a568580303420f24071180c4c04011110382c0c000e2a1460a070300c4140218000b040e0440d41c3d40a03000444100c460484107059980c5410301000e0301d991840d49025441501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 395717203 1250 395715953 395715973
    0x106050a1b0506041401150f1401020a11040b060d020c0c121603080c0309030a030e040f0911091308030405061e0f16030608060c0a08090604050a060f060302041b02010f0e 75
    0x410503052003601403203c000305901c1000e1f00c00b00711000300c40d00500c1046080c00b005002e003290400002221500910080c041e082058075030910448640681e14010368450300c1d252400e0705c82400322049034540500455032003080c591413613114606500343c079104003e09410b42c600c410703000449464008400c0b0003800c840740b45a550a0140e40405021002c90009000c0c02c4207581c1c00703000805013030f80a1b8568065000f000c1040104551642428074001860310071241b010400400101851040540304a00242c42e18072800c201200746602c0206808000010041040f60104d001030040000c5c2858085020100043c810b8140d0125a9011803108820019841109031031011110110303509001400d0f584400d5000d0a101048502c2e01a0110000b080700c0420340c443d006c0faa10410000140160781016904c0780c0d00c4084101c400b4152a07203c0c80320038400382d066032100008560042c008c0006640c5103505039090015a00c0300780255180a050348030b1603c01e1300410054080ca000508001c0d01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 395718453 1250 395717203 395717213
    0x906020d0503070c1410050c0c030405100306050a12020f060304030c02100e190509090d0c0303020717030403030f0e03090a12051e100e0102070809041a03060106050a1b050604 77
    0xe10314010001c4e095009000f0464820b080344104d046500504540001c03a40b4281c26100050003c1c091410204603290502c100031054409840301220844901420000c040340a083c2d00d40106074004c8241500180c0c41c01d0301c030318865082d4402d80e445490710310078004005040c042294050003058580105000500d428181e054076004c040c1001900038141401103528508170140c100d04100f1220024440391502440c42070703012174803c1c02800d11015105008000e041003140041c149a0081590020030400822050f4a0401d29144c55202c1c9810b0500074064074401c0e4070108514500704c50300d100000080122040c84501404002420b480c1c880e00d001c1303da841507800d40c0d00f4015a0b8115411010048020071112841802001109403040c140c3d404c4030009203200314160f104014150000e6070740001d40d001144100e40004154001e50707030007907044490000c0e0350f0303040c0200340004c214550490043d1411000c0340c0e480c1800c0742031007009030b01c46c1001d0060240081e4015800600010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 395719703 1250 395718453 395718457
    0x402060702090709150e01020106080a03140c010b061306030506090412200106030f0213050709061b060626060408041401050c150601030f0515010e010c0516030c060906020d05 77
    0x43d00520f041c1002030b60b1003c18801c3d10b049844540c000841c140740c0c00341d5941c0d090089001826000e0058210184c0039680a0080701800d000420482c202040c81c0c01041001c0d030240f2020390000d4112683c2d86080703014904101c2482c014403000c00c2c0751074081141410800011849941c0c849811030441500301402c0d5148004100d030405188414640380030008800c0c001c00c001584901302542c1510b84510400c40700000642d40d84100924182c10010403550010944085502c5420807402e851a005200d8600000c030580252a403400c10400003a001005440d11070300c11140d90358121190500c2d5906515208252005005190248070610500084180f0b85280c8601418400d1800312069929410088500300903c0d00c05004400c00201d543c160041c001c10b4160711108102c0e81c900303010058201c0001e1008141008440358100801c0e13402441c0e060100d64010045800e207140c2d04c0c8a03000e00102c20301040701d400907180300010360f46004080b80400d851458000c4c0c070408442000c101d41d00e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 395720953 1250 395719703 395719711
    0x22e05070c050d141e1b15280c080108010507020d021b0109082e0903021902060f0408101107050d050d020909150a0e0603030406120b030f1b0603040206070209 70
    0x24040180d85d503084c5280f400960740c2e800780c03907040e074aa2920080c820f080e13602c2151401e005030094096650f01c2e610092079160301403407055030050b18030f4540c82d103c507007946081c000390403607880c02002510f2103030400c44a070304903480803002740310350380c1c568004a0300e03140c0c0d00300100e000d640801103100440c40d0208034045000010316200c890203607201c0b5860f00c0c14058442c2484401c0c0d011034070440d5003000000600c0e1118408109104e0f15407150740095030b40c681d50210210003490b400400c4215038804007260410110010215140c60315285980d4455030305072070003551b1030b02d07201003400620070b09801d68901c1171b04500500154082e9020507512540400100b4102c2075003040384d0040c82c1d50720322029010340250a056440e41c1107400600100007103a4111700c8000d192041006400d076000401c450641d019442c02985484100304804060045c42c1d06082c1c0c58002c8184c103c01c0301d04001101001c0f0980d80c06003840c0754120a05001d42e9110039038019412a50812004001d420302c020342c2d03504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 395722203 1250 395720953 395720987
    0x60b1216210501060b1e120412030e2d01050417070c0807270e100b01030f0c02061608060901051011060708060315160807022e05070c050d 61
    0x1000310690b00c041c21202190010032050360701040070020910118448030801d041040304615002e02c44001d03d0f0102c0009000078100e0308100d820b0f8005a2103900040c0e00048041c0c1101c1c64100c10140643e04000c1c070980b14408a40f4690004000c0070050007268040c581000200c3c180c440c450009141030303800502c080d40c0080100e80f0014101c40d007041410020311240e0010715442c00d606000036140041121898407803402c0c0712000049140210706000e600343d0228000680582d0b00e070068000d48240481c401c022460655400d070001d8010032007900c2140c5a42440020141114064840c02000d64205410a00007001444030341000511032450600c1410303d52041289a60780718985002240d4520001e49508140440340c107040045800700c441410880c0e00034508007508c48210710082ea80030b030801c8007400c0440ca82500a102c400d1184030300070601c030110030504020030f034800c80c1c10024070f4205c5d00d06000124403d2080b410030105c240d01801030f00303c90883c4082261004041d09034002c1d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 395723453 1250 395722203 395722259
    0x1090c0215062806030b0406090b03071412030d0204080c0d05060c030705040b18041104050303070204020d0e0a05150a0507080714040f180e0a020d061a0607060b1216 73
    0x2410f10308095a4009010310366010030006155014030060f24641c0d442024880d00741040c05650369001f261100640b1281c40020140d030380182d0024a8a58408803040e4440c000040c2c0071a0b00703121a00100141c03001d0404444001c0310707285c1881865401590080e0240e04036a0200c1d081c98010001150421040d01d8024141034a450401c009a88082d040780e04404224032560b8445c01e0a0003040720b004540c03040d1a0400d0f103040003090312480f40010083c400c0d0350019035041c400e8065402011081000001c4529042c0249071169072103440c41c2107484000c2a440019420070b0841c01002d100301207035030f216212a00c1d196403e039038200c081c410041000a00788004100b03c801458600001c0140341142c40540301403401d2902240c1c0740b203a03420400d0b00004049170143c4c890101c140300d8072b41e200300001382e02e43c0d0003031022205000b12000258007103000504d5506110164002091680c1c0880d144480c1c04040321440e40d46e000141c242406980940f4410402084a07816150584502441c841 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 395724703 1250 395723453 395723509
    0xe0f04170d06121203020307050d020c0a05010903080106110705010504060c0c03060510030b1f0312170106031d060708070e030a080f07050601060c050a110d060e0601090c021506 78
    0x10076228950421114803030003c10f820144100d40011001000c80c0c0d0404503d50300303010400170700714891400c410030040c4e00002c2542104504000b04410260000004c221030403051600404091081c4180e01c0000c1c5902003000d0951004601d55040b80c02c143c607498581841c00105841c1005600c1013a078503032080c400300002051803802001d204001d01c040700e41c1694214a050704030403002904001c20b01c1c0300c0c9011070b00300354010b120b490241d03500144c400720485118002141c0c00b80c002c803000200b40c03401900009185170560018400c43c001d0100c8881186401d480c1a962036104442c50800160303110040380e140360040c170102506450140c1610840e0000e501c0303501c9568002802d1708280c082c0001c0c02030a10800344286c2e4090010352038070411200458648030b64401c40b40101800e01103002001821507a145809140100d602c01030901c0000000c0c0340c0d9903280c2b4424452408140e0603c0200040b242c8046411005c01c0e07a0040d0030315560700c40c2001e10443c0307007100c1440c2030030410000e000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 395725953 1250 395724703 395724727
    0x90b0f1e0d1d160e01170f010204080a0c050f100305090a0b090604020a08060403020a060c09050d060e0f030702061608041d091509060a0b030c0a09060801060e0f0417 73
    0x80202108404034500c45004810710601e40101083c1c4444031103800d800078050f9140c0c22142d03e045a944070401c01381250000f00281c03c0c09841030030054551301c00500000d01c40001b04103940c11901078031010b422140c0c4c900500032000d844294443d884090354a105801900a074809500a10103a044801d0116541d0703030904010317000e40d1251b1440e441001040f007140ba180070304201402d0b800f0064002c03030a00342c1c1c01030750311070003240010311964480300742101d024414900c2c00d008160041410341030f5101402d081c0000d013180d034111400c6020b580212000c1e00d1300007080703544450f4041c1184e4070b80302048419240c11600710001301c803009810400011090b1011200c0c0100080500c6c0308407441c01c181e22498582100501e00c040302101140420421120100391144d000a180c0000308d0780100110009007028009980c10350b008200e0400425510b00702e40c0140c0c00c0c1c0d613401008215031512513071130b049280c0c1e049400c0d652030182c0348002000503840e604200d1110801840c001e0402c0007030300817 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 395727203 1250 395725953 395725961
    0x50303040f090f0b0a03030c1e0b04170a0e0409080918012102060306040507110316030201060b0702032a0d06091110020607030e030705011b090b0f1e0d 67
    0x800c0d4404800700240040300440c810103400a1882000700f203860b90700e1002c540300e81941c2c44040c082c40250021841444035601110008400303042510b4200b501c5e0380b034402e0b0660003e460550720304000c1204050144100300c00ca6240783c1d41c0d900d130501010514010800504060f8100702d810a0041c0300a20044d00c0319200c131a0100340682800d01c1640c14051100700700011220420b4060440b403070701d240503844020031250420b0b0159408206a40c48140560f6641d550f603c0b148001c2c48005140310b141c508440da05801d991195009001c603981d03842e0004018010800065407580180703a181200d00d80d000b1103289400302000f00240c0803442540065040424041c064801c1c5450b1284401027092540305000281002c4614100c000b140410096903020000c1504040c0755441140180c0d448081040e0f072803443e0710000078005040b111411100710010003c40d00c020502514000c107030b01e4001400d84400340e00d00d1600e142029400985041401c0c0c8200303400009410420001840c1c11071802 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 395728453 1250 395727203 395727209
    0x120a050102030901060501171023030d030515120706050309070f08030417060f060f03070308030a0b09060a0605071e08120103020102071e030204050705090a03030225180507020705030304 82
    0x1800900e040c0015140000d123540c0e40081d410010108502d040165a610f0305607408500079071481c2a00e4511048c680160403e010f0b030600c12103100307069427507050700428401c03800d506000b0700d88580201030200070308861066813116042140d05000c140e2090014543c0004e001c3d00710360a01d50b039449400040b046507048100b0980000505201c002004150301010b000c2440c014215890311050321001d80d040900901e2151408005881e40d50340c040021038051a000b504055480c10282074a00040603c4180342e805003401c1c2000507882e02c2c2139030b28042110119110075140005c559070b40c107850954000e14001d16503443d4030f000701141a16010b00300c034031850701803c505541140006440c0c2400303a407000e00d5504442c0c08200e660303075040c0203072421254150786c082500e494256059900780108900c1e26004061712100006241d030016024900168182060540da01c0d14104600a203005015185a000b4103440b0700c40b11000c5036020303a610244a1050b030308107540b5880002e045522541c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 395729703 1250 395728453 395728471
    0x20d0804051929030402101412010f050f1f030612150b0301022508091810050108070c1e060c181502150a1e061706090705120a05010203 60
    0x2034030600810400c03941d00c030703c1030010b40711005140e4040d503c01482444020b2001380100d0f4005080b80e07002c0c1c0220108094003100055058540e039541e0b4070030380c00850900c034014001c901c0b000d0010741401c144003c400300b510050030105019001108401c61202000c8164042698032035000070010200ca0006490342e00c56000c6c600c84110240600382541c140c034111a120f80d104002e4107802e00c8205008200c90641c0500b980070180003810900024041c1c2c20090781c002c008018440c001c0001d088032603210b0650b05080316a4641ca44004403840c0004440341004184e4800c2480c020408440381c00c11091548828110300303030010b940d21000d6038101e0411101003070350003485100c0481a615040007034a001d08903010060481c20000b5a1441d1150603c100e0030355440200c0d403d815280c11005151803a000d1b010703002c0000990743e0740104400d20429030080001c04500f04403010210b40e99000302c051600400804e418201003040c4503501c0311629400b4420f0408034070006200b0300145100c0c0c5504 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 395730953 1250 395729703 395729749
    0x60305040204140105012001021c0608061b070b18010903050307091703070611040801090f0618120516050712020102240a09060906020309010b01091e03020d080405 72
    0xa032040c00140c1c3c1500340b010a41001e1100103010a9034024108800a205903ca40100100d24040c0c00e00a124000040201030003000b00789044140d07036003202c021501040100c541559034162400a42140c0c076016400e45402041078a0200f149191000d82140084128001e64220500040c3c212811044110042080481001078442e041840da500800c1800c481488186a01090380e44031712a2400080801e0b54076031008168014500c256405040d41c00001c100b64200350420f200068003d00f0100c5940d0b04020820400c0d28001c10441c0c0004d500481380d9803c00b500350026122600580140e9824200154101d800f080c6c00b042410000c040c0340b15040e4600d005800028140101d40ae02c0f820b14689400003440d520440c42c1c05a40d12241d0417600045400b064078007240982146840605101e0000c414405070740410743c01a510400240c03182c42016a66603203240070134400c01c03c040d01c42194031000b0009401e254025034400b92040c01c040785000e440d0700000e109650082d008603404911 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 395732203 1250 395730953 395730961
    0x1902091f09030b07210515061b010f0c0c03030b130f0504021008090d0e03070e07020d030e07050123090406060207081006030f030f03060f12051006060206040b04110901060305 77
    0x110060306401141c4ca2526012480400c3c0d0111442800c00405101c0140e480d030000e441d0944440101c40d8004000300074541c0c83c101040700b80400340c1042900c00a035443c3c140c03040b05080d1503214a940030310346030710340420084e000c3d1015801041101d52168002518209180c0403841c144200198180076010014003414035005001c07000c0040801001480f005405002d0613920001b03501c0c42d4400e0310725096021b59508000321f03042010396840b080c0306441e2101800462500410035440c1a02070f0b0750100300028601c9002c030703a2418140b1460703012641c000b130900020400121550145200404050b00e0101a00049000c403034150b03100c0d20040c1c21004050103c00010f1014400030034035800244149810758070f540c40f80146841008050101a0b0302040d0034074080e41068009000d90302840c4038030340e6180102030641d41d100400b1160781c024030900384840c203a107100b1001030701e07000d0740145040d50300d0b55911488a04003506c265600f020f5018101099903d4215542c040c1034660380100b000d0030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 395733453 1250 395732203 395732213
    0x11d03040e0603010605012102070210050c0f0a0b0115021c080f0106110d0c02040f050907060f170c030702030c07081f181712010e01060206070203031902091f0903 72
    0x2074068596486070b410150300308056a48940701a19440250880a000100704203807400240303e0703808001e4110b0400740302070500c56084406401100d044c0415100d100e8410700e55a0384680030303154010483c05131a0300501c011b1050040030800c42c20716004480181188a4001c074006800720107010014801c0e004000c8803121610043d8010039503800c2071520600707442d440c1c640740c4188030311540400950341d01040c15580e03550403c0310000800e01d41004581001e07458603498100900480c400304500800c05400720b0b2284a86001014003001060280e031242440844554405030070300085210520a101c04c0410600c05000205000001400041110386550081c44110359011550a140200c043e0b80c11048424900352f02d40d000501c015004000041c035000350107542510f8000d426810f00201c0c5074100c41104034140d8483d81c00f11419651111802c9039684000c07034902810804025007100ca42c40f164025240e01c40e0010001000e60450707222100311000c2601d4510001252001d08100f881 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 395734703 1250 395733453 395733479
    0x92c0c090102161e050114070204020a14070605090d0f0c06090f020a1403010f090b0718080109060b0f040c09030b25031509020315061e1908010503010605010f030e011d0304 76
    0x50030f007828989480303081601c1c3d41078021128027900841e000580756042d5841030217204200c51030009099240d00441c2040d03401004102c850074420701c940d01407003030924007469000c1e1184010340c2e02c0592240090391018050b2801c01c030b0884514521241c6040180da03950400409007070040006c00820b0413100406081d82c1c200d201000110703251000200200754010740e00384d0b020410b0b00341410303000c0403407400c44982555039016031195443d1281c03000400a042d0410320761840d04139074942a03003500c1000c101c22640c1100507070380410b441280400000f4660b28000b0742c0b000b1800502442c6041a10302e81d801d900008086000007551028210164058144c851015042e212803c50651510752004080603070510a264880c29000c900400c2200303111744106501c8604c1c0e22040e440ea14151207000302000102c5d07128010910765030000c1200d003070510410b003c992059403503603507a100c0c10358190020324034610307601150354943e0741700c19100f804419520701051121000b581c0d2a03140c5a8200b100c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 395735953 1250 395734703 395734709
    0x110121091a0c0c1513030e0a15050d0501140a030f0303020705150f100308040b0f07050709020a081303020d03020f0c0604030807120203010503032b0c092c0c090102161e 74
    0x441c3c240402d00c046110610003a0b003a07554182051f1001b184444001504101150711081c64540e0000e031142c070541e84640600500e10b2a0781040c442030341c07501200000d200748210950b030840b01c64501000810080c58848215a00030308005282103680e0720f803c0d0500c800d100c2240001400441801341c1e107080740289550000044100c5c9413030b05c0c150741d00d40702d01d0b200794411a0308a050100d00c122418000008552801e07602000315052a45e4498a81c0d000e500a0264500414100c0001421051198207a1105960f041d40540007a242d05a01503009420408840364514000e008604500384200400d6001d04d0003500c802c0756074542100000c1280c00520f410a00e010700600040255840000564803a15815209811248941103079148108100611052641e05040c2c0340304a03580c100100710705951a010301040e40d481c5400500c03070746e03a0300da10304201a03009010010b1400c1801401804984c501403050303070700c100517000c140c81c003240e503a03040300c8001c4040140c42c07003090107002918801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 395737203 1250 395735953 395735983
    0xe01061d010305060a0503030c0601060e100f0c0c0b0a0207080c040c08060d020d0506071d150a030b0310320903030c0f090604060309110121091a0c0c 66
    0x2011100001424038801449045040c5a2204040b03a10717a60f40c1d800748005008068110385c1c9030000381000c542d035004281700e4040400d008021203030b01800d00f8415003003002502d03203c0810b00320002e5412181c07028030305410350380003800c4940400e01c440c10600600e401380e5180d0041c002e042c01d20b10704608003501200168812440d200110032580c0c1c108492513845401120100301600d841d00119a440114081c014480d010350010400034030703000340d68103125500b030401202c0d4114006041c030100301d410075136806040f00180607901d0440c0c801d0700007552900e00942500d82c41c40300b11a106054030403100e0a0501510710a1602007100c1c0c0d0b01034500303c500d000500c10a42403c0070400c1e55249e10014140800e046000a00e04020484400403601360400103420156100c0e40c0d048014018610310b4000c4800d80c1e042d209038000c56214014019001100c46100000042011802c1c0000c1900f540115040070998065143d81c116a4614900c10884090300940d141007014a0034107080d056101250 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 395738453 1250 395737203 395737217
    0x30f070e0d0816031206080a11030a050613030e181501020a02040f09060b1804021207080604111314130203010603080d02091305010b07020409020409050d020715020106142412010e0106 81
    0x7a00f400502004140d8110640688019a589c0403a00f804a050707009012885044140800148515407820f40c05009544642401240c0d00c00c02600300c5046105540c40078905002c121001407000804e030348090140100c0701c2c0c2d01c8483e4085030580d00b08080d1080815581c0c1c24000c1448400c0c003031040c1e1250120307144400d40c0745800385084000e0018001a001e80070009105034010780030070001001d050031104445151500340b5025625031009094a8002c807001d1404c4940400c1130f01404a499003080c41e024429038030f4138001e00303070074586090070b81e49592200c4c0c001006c13440d4100200740142603031401580d9001c0503c24001080e102c100c07001074041c50000108010883c038030550307160650441d03004c9903000e40d900015000d007040c502c015240340a010a00c2040b250002542c0080b0340e110300c0c0304a03540c41c9610041c0c1c01c95000780300302c1c00d000c506554404103034a403030b000e0007185255010440c450001c084000b485260000384040c600300048030014000000d69501d01c2c1d00500f440c1c03402c54 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 395739703 1250 395738453 395738459
    0xb0111030301030b060a091506171302090606041802090109170a02060f0c0d1206210f081b0f01060f180902030304080f1b0105030f070e0d0816031206 66
    0x25030301d00c8144809007416039001c0c0402c03069901e161001008000d0b20806001c122040700c0c110141a002d4031980011400c020b0040c0d000c04c3e49010003600c214000c40b1408c581c10003680a001c21a9002010203600202c100300214442d40c42e4219502641d69040005840710a2800094000c20581d008141400c4642039100c2c030110002039a0901075505a4034283c50b8504079248403010b000d405940f00340da0040058000030306038000c035a0341040c00c2480341400344540e140448508480b2a12130900700254807000340001c1001c490070088254400d040c041e28003006495500000e48290000801c6600886030f103024204090080300c0c0544001a001c41505140180d009101301105445000c415110340d610002d642d4148143d3707004042d010245c40722400440d010303944070306d038003003a011500f0032481c2d0040c4194801e0b070642c0d2140c490103038100c10700c2d00c4481043d00d180e0303d22020103074040340d813004c4c01b000541084040d003030f401c4414105943c050803520740600b2190540c022001c5191500e5410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 395740953 1250 395739703 395739737
    0x11030109051f0b0904030503060112061a0309030702030f030706050f06131505060a11060a02070201020d0c14030a111902060a0c05030708030c0c0f0105190c1e0801090b01 75
    0xc4107202c1018081000c054610001040a040150440b90b40098854200403d054010008501c40e0030309036940c4540001c00c4d4a6442194503034003414401001c01c03804640028104c0c1c00854100345490100c80c140201580003c2c036181c00305d40410820341011400c1410005503020351a0400b0300d4008030100341c604400416401760a042103405c40c0c5849a04203c0e900690881c0035014100c0500700ca60748900d203403030241400380e00c9914101d00d8803035000007030002c841501c20381b40c3c1c3d6a4142c1c05022840010740e0200c4040d0103162080d9240c41d1102c04484001c0310402c01087ca002c0d40c3e8035910002180000b000c1d04155000b101d0810381d01002c4004401a50b07020f08440c002034941c2480c812041c90390074024914010b15100030004040003060105c8002d013413014181c588006002c80f0340d0150014a9503081c1c800a895080311030980543e41d0041c55000e421110036103289203003020050341d03201005190195405d1b903130404104020300604c22035245000e9091014420309202034074042d24401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 395742203 1250 395740953 395740963
    0x903100903080f1906060f091a0901030209220902100e01020a03050315030109060906060f1809020117040b0604060f0803030117070305030720090108061504021b0105041103010905 79
    0x41071110009100005500b130070f01d0030802c0290002d20400300103031925801e000d0510610070f003910300414000d44000502107442a010805803140c40519801c0c4041c580064000c1d40089000c2c41d03000d121929554482040c4032420b90102c551860041001c1c21940140181801890010f108020041c034028a9a907000240110030f1585458890b0383c90350340044015003403003014401949075090490540a0003060b422030881980561000c20007550b031403801c6040c861141c42003080344c6102580c1c6e2185604a944900b401038010306040440703840d0113121020520040714220342c100e90f0700c010302641e4101340c815240580480c1001c000c001d800c0c20a00d0f0760728001486070b4400c0301d00b0100100b06994040c42007a0013107074410212501c9030036918210a40032160446014601082c040d0451107140c150001d50407120b00201070500c1d602e44034854444243c4511041e030b0004c4d020403c0764107480015020705040740d05003000140d9800c0c140b41c00c0030b500c0365640b041840f80e230420156030046070001c19 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 395743453 1250 395742203 395742211
    0x9010b030f0405070519090c050c060c0705010b040609090606050405010605071b050a03050a1403031501030c0e09010b040611240712141f06020c010c0f0b0c090310090308 75
    0x107019102d64a51400914000003500125045a005007030b100c01c003603c2140c288141c84d082c0509100216003118100c419008000000706194000804224061801802003007018091800404c41600700b4001c1001d41e01c166010800e000e50716260780050101a03c640809040d046800348403552500c84010708a0140107005001c81140c0c0e04d102c81610000000c1900402c40580f407881003a5072810255150450480b00350b03090200704007030895054004c405c4a11411f405454200000c1e5035400440041148550000a02c412080c01d100140e07242582e241c000e040f900c1c3e203179a489040c40f00c0103100000c0110364981c294002c0d00c03c140d05000a41125194a0b0001c01d6090b460b51070160841d0300c1840140404440c40c5084240c500720040b16601c00d01ca8050880d01010080008071603510151640c0b00d86001030300700c99850388543d0310030080159202c0c000e0070107044054081d2640ba0400c1c1081e41e0702640e17460700041014860909000e12000707140320707481c01c00c400000354078007428140d4014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 395744703 1250 395743453 395743471
    0x507080627150409021002030310060306080d080901020d1a040b06040e0604110f030408030f130302101806020c030408010605060c06040204091415060f04020c03040e0403350609010b03 81
    0x1051030031241d03d9662224044a80081500505540c401e101035105e074001c1e1103460441c01c1c03100e0003180d25400ba028210446285000601585030000e004443c0741401401c0706a45c1e540801613030546900c40d005d80c0c2d50708401242d00c2d904501d80c00c0c0c100403c6032110684603004100500041100800307108015078001c0d02580d001c6400700e0301c02440030051081c0c1080c4034032200b0110503c4140321b100c0c4091071007420075482c03201c800d498003a0b2801c0340d51000d0381e00a0043e40820010040010682c03c01900b2240442c01990080d180f561201c069810094004000b68808281000611001d000c1c000003085d06031230b02440c14001c40704242c0c461078000e0020f80076985a1403950308005102e6480c42d00340e9207070301c10b03182032500f60a160b40245100f41c0d8103501c520440801e100c118a440d208940100350043e000703504e0645820842010400c0c028000d0b001c0c800f441c40d0400b20f5803141080440310046d0079080340302d1580041002c1528150203850b581c0100014030046c01000109000c40b07070401128 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 395745953 1250 395744703 395744731
    0x21504060b010207030b0406050f15060d0e012c100c020d140f04080d09080c0a0e0903040302030601030302060109180803040206030630060a0b18070903060507080627 73
    0x240051340340c500e031076100400d1040000104018000c1613032110340103940007010002e651b154044200e0b189401411410381c084410007010f8640c0c50340740e01c52000c80d01c0300c600100346071046040782c140320790302d14404090124800245681d4420280940c090591060100300312114007903400a680d46a138107500c03000d02041301c401e81c00090804e4143c4601807200910f841d9502c1d15640000d490301051807110011403060000460200c5011a9103003403032501902c901202c6281c070707010210311800506544101c0c0401c200102c0507841c20f000c2ca5010710f01039002071403e9498007502c50200c61900400515500c0600301500001c1e441a003220b0300181c041769410f031251aa08002103c5006050b54244e0000300404e002111042d6040c0070000f607441c0d801a64040e682c0e10800304255031001030082c0d800309409484090164482c0c01003070b00141145000c240300c945076901c10080701c100342c600704013150340182084001c1c500004035040101542c03a546120344506d0031f5140303890b0005404d600340f203100c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 395747203 1250 395745953 395745971
    0x90109050414040f03050d0609090201030e070e150a050907020f1b131d0a24090c0521060405010b0a061722080d020d0b0a0e010608060d2405010602150406 68
    0x403500940301106030b0881f04000390f555440000004195014040b40841c0c24000791003007000300402c01c40100c0d00311402400b02a134070940e5185503056032920301075000114031300c04103080e02ca2a41041c0b0541c03003500180341442c1642e2a0b00e1900c00f84288a0b43c01c08109420700b0126112030850620b0f2249611000c00c0d1036010080c07030540d4958401003c2114819107540f90144070701d090001410f082e9400c80b140c190108880c8441c242e400e00000503100b0200998100060300704080040f00114103148a001030b60249184181402815681903135641e4480d503487c80c0e40c0ca82481400c0082c035940c140b440e100710022118011480004262042d0803500160f03105100340d00c200600c10641e4040c011035516800030712003c0094111907030f11070b080c80c031341104040a810b00d041c81c2d40507903440700f18681e00c2c2d07860b041d002c50390700340c008220680204a020030200011403610503480000400d110b03040c1e10707000341003200c800c440f416032100c8110352021105000c00507070800d010360020b401510100d030040b2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 395748453 1250 395747203 395747207
    0x1e0f0706050711010e060a1d030703050a02090a0b12030d060605120a05070e1504090b0f1509041805010c03141003110303040f08060114040b0913050f030f090109050414040f03 77
    0x90f214030844e00061b00180c0c80c40c11070741c0142002c00d607240192484111690010505540740481d00008100783d1040072028054900b00c0c054550240310800041406c41d405008102c0751070400071000113a62000c42c10f50f02c4909203000714405080c1620b4213609185038003d52241055001d440009040d640310081004144100311040d1a0480503000c91880c4110103403041c0300358043d10865800c0752a000c18802903103032003400c000c0040c000529006d152440560003001690100010940c4681e550380190184e050024211078424041c01c000250320b600c108000d400d5a211000c0000303441c0d084410804044005001d08090342d40110005501d1808240402e2035489140c1100000e207c07400000176110000040b094140c8502b0b0726505010010075003440140c0d00c8001d4210340c440c09001c00541e60f0350203551144036aa004108a465810f81c0c00034090071039100e5505803030b0301d080000c0e001c9500d5070003038040c070700a1405503000c1203075030501c0224041ca2040a030000744561508805c0509140c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 395749703 1250 395748453 395748467
    0xb0f070f0f050d0207080705090c400329070c170d05070908070806072f060117060606072a140a060513051201020c1e0f070605071101 59
    0x640c00000c690800071807540c00f95840c14103200f0303800c461003800707004221809c004034042d024100c1800d03051704210511b0002110156021581003201c038002548940c0c884070901107201070b5044c03141252089055041c0284c0315189101c402d481c580c460311803088446ca14020742035102e601407514006038180c601c0c00060254691296006081000ca01c17008841140d5121501560f05500c0301d5420b103940e400c05644400c101d01c5090810380111002601c40c03402141620070640d5442c07080d0b858014083c42e200e0100c000170280324416030000307005000d0b491056204458402d001c8004000505c5c2ca4000100755219020f40101320404508103100c03403121b07070051032180039241c00b629248d19840701c0c902c509110641d080b0a214402c0641c00141890259044450648201060b070b500a4209401c6c0b19184502c000303000c81e190b500b001101e11100040c04445003200300640b8001410b180c910a05203050210010b04d18240c022200421505030044101d4070b2456201540c1e0025410b2400182c07840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 395750953 1250 395749703 395749733
    0x20607020d1b230120090d081b0106080d051215120a050d02060c07212109110402090109140303120c0309010e1b040e030d0c0203040e010b0f070f 64
    0x32542030b840851062144010f6180040819008112851041d009020041c08500c02405490020001c5065504200d003101242602914546251010b440701100c0c1d45441801c5161040c0d6440d0403c0c40582c0b401d000828445100b403a0040c01d220010184418540300a030210407181c044118800881e151281c88040280b000d00c1580c80d00a0705d030900c9622164040001c0c40180190b40008500e155410184e42c1080e411200002c65110040303110411701401c00c07518814410010841c40764940b08009400c442e418000c80420501e00c0e07480c00031810811002851310403801404804c034145d034800c01d0717001243ca60211030305101000c078011905611440382c804d250b03500d1a0040002161080009600404400c0c0c000c1101c071780054061500d03013286110240401000c1031010b001407805030080510207807030806907132030300000d0307400881240c251148410150300042010000c5001c410940b50050003003604091424010007103032121441130000080100950b000070342e091005c484694151 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 395752203 1250 395750953 395750963
    0x1504140d06021b0105010f12080904090b0106030e070801061a0322030e010e0409020109050d1505040b040203060108010c02030313031b060501050a050105041a07170313030f020607020d1b 82
    0x560355a04204482c5803c55000e40c41e100d6081c4000050341c0603141e038100044030300d200710301d180b8004559188281a0b105403205c0e0b0f4096265040c0d0008500200c40e0140241101c0d24005004143c0075405410403003141e00c1008181d1420f14200b10a0030944585946c074043c221220f80d80e5035401a64900e1030021441403248009440c02c1c103420103401c25403030383d25142c007620b500c00048541400c02c01038a8101000a000480c544401c10040c04c0803000340a4451156815040711403144120204984040b2030554001001030244801d6080502440b80585540341c02440b014000140182d40c030720025080700d41c8400c0842c2024203141c820985000c080d21103a18041c0081c4c12801d1010180c00280140c2e803040d04600c0c80052258058022142248c0c01a081da125010102d0b001c1c03011a00014401e48102023551031070501d202140005606c2401e85541105450f142070600500c01e2803022040c6040d540890305000e141a000a004075100c81c05150030554800c03100c1c004c1604010352000208 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 395753453 1250 395752203 395752207
    0x306070e1f03050a060b0a0e04050a09150f1514012607030e0d021f050c0906070317010614120709090f1b0c03050f130513090209061504140d0602 64
    0x59207035403540100e402111201000d1065648550301a0744c28400c030f400c2c500c08a8005c0e80b01c4100c40c140780c0c03c07407a44034000800004060707001d901d402449080300030722000701955480060300811480d20883d2402c82c06000d06100c118141401e01c0311741c2079403181d0103050190b080800d0201559500858110f406180b02c2e540240c202101d0280203008101190b02260040070180c41c8114400108485251128500c000d8980503e0340c00400070440034007013540c864000c00c18812144ca50070300501e000c51207991210104600d03000d400d20401010781080007008040040040095181c40646103482c41000ca4800f054480c6c25041d03d98003030b264001750a5500f005c0340c60007001519030041e5001c0c0074181500c040544424004c658400500c680140441c2c0280031209030000c0240250401001000b6a4028544c5400c001003070740f003191007820340d0540c84207242800c6051446103207070840f500360381b00d188004140018071210b0082d030241064003103280940751020382e00d00314401122900b1010440d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 395754703 1250 395753453 395753509
    0xf060408060f010803030915040206041d0f01081506010806040b030115090e0c01090b0c0f3304120507110a0605030912090105070602071b15030b030307020306070e 72
    0x2589584040b2403000c1005000e0000003005003001c4112446a02c040c40540260031914403046583c0e003014200741d80000c000d00011888040c145a40c0c04603c3e040104400a850a00d5242880010582040c40203400451405007042003159000d50400000d0070030010b030303540e6180410020981107981039815820825032211045444030302c50240c80c6121820b10a028004040c203a0b00d121141c1e980d8001503030b4407070800401031013034060039640700c4510a95207820149040d403890f0400d0010b0360031401c1400f0100800701d50100a450034403d10b00c2d44000c40f04d161a0310342c41c4104a0001030f5809120307001912108005654180d615040c0e001080420341c181c80300f000070210381044030005520710403460003a10008104094030100d10f4140d64480c50100a41c0d030741406034200200841d02440d404402442c00401c0d07080c0c00010f0038400da000e001c0324030481c0c0001e0583e018441301a009070010030801002d41c6011410310b40c4084107051182840a0020110310014024034016034840c030203650392 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 395755953 1250 395754703 395754719
    0x20904151503051e09122b051512010905030c0f0115080703080a110307030e0406060c02240903030703050301050406170312060112020c0c0418120e0f0604 68
    0x69402148003850510004201503085610139502550004540d000070f5005a0344075505a074007100450076a02180c851094802607030300b02805400303010414081d02c8240e00089070301401c0311640a00240042e08006400354101420340f00002e0042818410b81c0c40014000d411071101c240d840390450ba610308503216100c0d03c50318142c0c07036241a94203180030075408410901d503203030558180c0c0e000343c4080c0d49142c2c0c80103501e40c00b5103a90402d020850782d800c0c00000003031014107640c500a844895100e020b03241044121286a0441d2040c42007000742000561149411500e02e4a0b090901001c00840b494103e00c031802404007080d8544400201181010350000246040740c0c42500c091040d140ca940b880c02c46e90511904680056000307002204450031000c510035008981810001c00b0883e00500b0142640c0c00588010925889143c0d80c91003801c140c4034003c402001d401c40301e11150407603501d54110314070398041070003080b00c11155a0819501c4403c0645900340003480f081c2d03600e590340300c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 395757203 1250 395755953 395755991
    0x40b07050c0a050a0f06050715060e0702010e011107030e04020d23010506030f040201050901090e1315050702070b0c01060f09090b072d170106080906070e0102060403080604020904 79
    0x91500a044042c00001c05080c02c103041801e403500802c10a01c0c0505106084801341c012440940e1200e1490190640d074407002d03c5094045c0c01d10011003c1c0740c0c508510302034251145500006126894950415000440601564405a458035011301c0e0303c01c0080000f0040e000e19024040034a01d850780620064000d0070084105041c543c0d0b4460f040d0780d807002003040b5400100ca41200000315180020010341c404c074001e0a00c15014100001201d0b02c2d8120006a010201c8801c0c411006480f0410180103458008002188184000f480f052502c00002500da03035440c480c10b0b4420001081c2140000700a4100001601e01c03c6001c031746550303803481d41c0300c040c2c00c0904007500c0c12251b900108254910030301a403400c01c846001c005100b08e103140c1c4003000d0601d015060004014000c81005084c003039110129001304102ea542c04800c0c20312403090b03820400003600741418442c2c0340203c0d81150760003042c1c107903025415041400a60342c6000101d0064442c40c6d140503032081c501184c04c1000418416 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 395758453 1250 395757203 395757223
    0x807030201120501030506010902070f0b0c0a1211161509030c0c0617010e0601020c19080c0a12110409020d03090303020106050414040b0c1201030b1902072303040b0705 74
    0x18032440b24030240750034203007115028000501580c201600520170910541c00410586200b41110451041d05807100601650203035542c40e0031a0001446440265114400d03030010385450100304800b460b070715204d004901c54001d050030030030350096502e41404a00c001a100d00b585038842031100314001e15000f055201d040c1c50450f0394070310049011901c2c40c0309400c60400600c03400c001c956a642081e162020511005054504520a20480d4951522a0a002c000c103030098610028030508100100f0f042c80313929008980540910f200400c40d0b20300344030f45200c060381c000c512400142c0c980380110700034089100010350051696207255040551140100c0100c03400781d40204092901c0700c0411090f02ca00da10240003040b80782000c02e010a42c40c281c00c94028110303400301450001c2c0c0148044034504c09238001e8401015038000c01102d0064044a1010064040f00842c07900c0d005aa1b220f03013800740c0c0700e455146050075840480c01100d04104036005440d185170300680355059403a20369940c62000c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 395759703 1250 395758453 395758457
    0x12050909012106150816090b0d031b030e0d050d020706020c030703140a020d0f0c0b092b060e070f0f15051c02030c0304110315070c0f0503040807030201 67
    0x100001902080100c00b081c0911000000c03a0780320880d80c5921025101e90030140c20001c241443c0060124020040705603401021444d9020082c5403c640c3d40483c0c181c1d001580c020514840003100003a445400f0903410300c600361440342c01e540c2c1814210380c18140c0240c002e8000c540100040c013030210000320316240b40c05035821031720081d494103001c03610b500001c0080c681503400a2414000901030100a1580140e070400311180043c0980004a541c08010400e9800c484001000b00600107008080000340c8003110b00d051038046a900464000500c0b680400580cc1e6003506085040844040c0000d06680041d03080c0011000f64154546514461049411040908e00b00140b003080c9044004100c1c5e8686000355410001108240e941e94002ea41c0300580d540c1c1c0064940c00e408152001c0d6005010549031640ca038a0240740200c85081d001c003000744aa40040e41030542c20001107032450780001c051404c0c03401c0203000c1c9804001c0800c401e8009013140000b25020440120019161040368000d17 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 395760953 1250 395759703 395759719
    0x1505010b0909090703050c040e010213170601060801061d0103020d0e1b1926030d0605040c0302070b04080a17012c070806010302030c071505040201090906060207170703120509 77
    0x10506403951404c03e444014a2078002095852003450300764410342844900d031001501d0511802c5003058071000740c6c0c0100d4460520700301404401801044032602400841c00d017a481541002d40203040c13401150380000b0544850402443c05034440d40641750006003041c001d01298107001c28440d1100d40c1c0c0d50080022115110030020a40b42c00c03403036003008440c0351201d92034850409001c0c01d0044450b449001c9003542d0105c442d88203900400c014040500c10a40c0014002d06003403c000584d0019149601014010b00c01400890840300e401c503009903221000564070455044180d0b42c4c01105040740400c0100e40b000003c040c2a000200d0724028800c0600000340d40d9000b180c40540d16041d1b82403000640303d01e00040955000350300858100a1021a590a0142c15a1035499080c5010341844e0705544481c184811940c01840741c601070301d07100109026050620784020754603a00f600c200060155031200705500f100051101c903010b140c2002c110740000c02100390191140e40000d0080307004502e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 395762203 1250 395760953 395760961
    0xd020c062404020414090618040b0a060f06050d200f04030b0108010912030908120a0e07090b0d06050c090316030b090c0a0b0a0225030302070b030606161505010b0909 73
    0x4544212000d4951341c0017810302000d034900c14420001c10083c201034200042441c040c0704014041e54080c4254421516808c09280161401c01920441d6000180171101c0e01028000b03103030400192281e20f6003181000450858402c105810500100903003086034000186541c40445810018002e0303e020b081040e0451341d032858050300b00c0d1400400a04003081c1150880d140600c0b0360050f01240b4012180c0d5403d08a00f941240c40000c82074a418006079a905140d07402c0070710500203403004041310941008444149400710308002a07208009011566034000504181403010a444442401901711400c05030004503244807181c1a000030340f074401100c0c0000c0c02c21080050b85480503680174100c1c40010346032451250b00c54100718002c00c1507014184910300c009124810310800c0002c007888140044e0310303508002c6d003042c14079040f0300c100070300030000c00006803560744c00c5901100344601c1c082451442410400550300e00c42034202207079400e0000009030078040001404006000b00c1d448281521 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 395763453 1250 395762203 395762209
    0x370c0b060a060509060c0f0d030209010e0306071d01050c0d090503190f06091a101a190e0118080d030501050909060103061d070f0303020d050a080109020d020c0624 72
    0x724520034a00000c104100c00a1a0300301980079200013291181156050241e280c07849081c8201f5948600000e64081181c0040c1d6034030406c19540301000b035004d0890350400580080541c103a104072442600340b00071049013503034410000c840404c8044c0e01650740154111000420507181d611413140701e07210f25164001a0401d10126500c49a40148400e030340750100e60f55040a40400300c0305442d60780b010720007030f19001c800c02203a80c45031202c0303904000303503900780416082c0c502c4044a40c20039002c000d01c66100d480d1028500c20f000707507141d41040c0d030b200c80446004860381d01c0034070b080c0c4205550361100015443c00015403911032009940342408643c0e20b800a00c80301079011156407450350b001000410114259038071200c030312150fa60760001c0e240c8030f42e1201c2e4540301c45a0711400b4020030408080051507030603c80704409055600c0c0c42e41c54030b550704800401c1e50340107014058485038002580066084298110350003144210250703481460038207040c000d0800002c5007010300c40c5d240000400d8501d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 395764703 1250 395763453 395763469
    0xe0a0c030b03030a05040509070c0818040507141803030f0403140c120a02130f1805160509191d0102030a0b03011104030303052d041b030206370c0b06 66
    0x14080d541d90505047c07501e010014225000781105050100d081c2c2c0c03100210301e13580001d0406140c00d0111f112001500018001103a030020306030000c101020903000c038540d81d040122200c07054014814030f045ca2190380040d0861040941d1100402400200082003020b0681d43d04408800081600e4480b902c0400b40000305c10280351240e2103030090400c0d600145040400141040da01c15000111440344035259000c0f0b840d000c0e69010a00307070700715411041003020001c15403c10702c10040700020b0792500012032040240030f001c0700c44410302c8210200c0c8082a0342e04c10090354030540d950240f070341007106002c1d00079030044d10042851801c08841c403500d42414042e040004c10b4002d041841d00d071542e01d00f02c1c010031020349803d01c2c010040d281442e0100030900c10021a00100840c9026400c081c644490156107080e01e00c0d01540c1044410005651414290395944541c910890148024507450b4444152451810380d1082030700d00c003100c3c00a40c0481920700540c81207088030101c2c4c894104000d000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 395765953 1250 395764703 395764717
    0xe072006010b0d1d0f15010909020f0603150d0c260304051002103206030a021002011b02030309070b030906061908010c0c12030c021002090a0e0a0c030b0303 69
    0x7664080002c003d1110301c56208035403191401c160652410100c1d045981400b048004c02155907000242d80f07024401d01900c0c280c01130001a50030003000000c1c0d80491811403108801c144192804000681c48958030382c1170503001ca100400003104140b09152520080c43e82d40143e50f210110f09140381002601c0c0d0b15154441c1000b0002907042c10b151604204019000311001421409510000d4441003030320b000b0540e65142121080c00c401c4000081420380120800c2e070a000c00f00340e2000c2c0001a1008601c441e540c5405841210803174000500a0b4054070b443d03480b003036000c03c03214841c48103e0b134084042d5014460000a0354140b41d640d00030b0354210701064404007005d800400200301d040c0781c06c0b804040c0b140f071450100110f890391544520308450401e90444082846451070004122a43e0039a0059038900d04040196840e8414025542c2e83d0f0f04c04509005540041c0603038069030342c0c003108401000b400d15450f10a2800d402d1801c06170064550302008242043c8503200d1910f0f002c8151884 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 395767203 1250 395765953 395765969
    0x409061d0f04030801090506030c2205061903060203060604081b0f0301090c05061b03030c0c0d030203071b080f0705030c070609060f050d0605090a0902030c03030a05090603100e07200601 82
    0x140342d08122500300100002391410354184103101e03d44c0940d0f103558400c01427120440d0049c0c0042c400234808001502d50080c00750340301d8030201a01d000d0341c034101c40300d42d410340307070041001038883d920800410207520031500440101e01c584d148401403011790490840920000303440c000c90910b0041c043c1400d0ba030b44e4500050007009181408d11081c00c010014109080404100d80346801072000c1c41c50640d40b00740c4540802e5100000c01c034611510405c0040660303090f078078046185151845c001030200c6060020303089035850316201b2806200c0244166191003a0104820341d80380101d2400d10b95981c81100440040d02038070900007041c0e40207810200440e2803e807a4680301d402c82003812180c581c004031002c114550b540001140986403617071400d205558900b800200120f4500403d450040c0303103030090303100f94410810844800d03071000558035000000d848641e240c0c2c0741c0b103c10840d00300898100824101c0181c04225646034420f4812400072410200c040d90aca000005458480380c090040c0c40c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 395768453 1250 395767203 395767217
    0x62419030506031f0b10110606010c03050307030f0605040606030f050603030a0c0308090f0d0903201518030a0c0f090b0607080702240a030e0303100308090102030409061d0f0403 78
    0x140380740c6502601c8505001040f0006545c034001d000195107a481c102d4407000550210b512a003403031010441c0a810040900301005882c2d403030399004100d03101c000c00c2c400802d5102d03042042d410a06401c01d034080d000c003e109005003912104000c00502c0c40c1850f610f4080e0600010039024100801101c1c7d1032074041d910015070070f019072819202103074060302c404007920901c0c00c0b03170079080c1d010300604005541580d135400c10719245040c0805003c801a00703003041c00c401412003070002d90700d5100d00003c0140b0a02c1ca00d85a0041c84100300c640300001c1d01442d00b44c0581c05902003003014907012002990700c900c0e400708042c1d44503d0368800f100d00b41602d0f0f0342c00100810000000c6000c3d00042c242491004090f68034164906a00000c881002d19100200e07005c003245e03485101d9014000d040e07495036418000c604600d07180d80500e0708807509100103400d9000009410406920030300031500a8100140c090016958884407142002103040103a20703032a4002011555560002640c6800703140c151ba64070f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 395769703 1250 395768453 395768473
    0x100206101238040804051203030907051c0c0b130e0103030203090105030a060506070501090201030c11070510140f0c0c090f06120c190306060b03090a0b06241903050603 74
    0x2016004219620041d000503240c0140b02009040d11440b9a1003030704100d44440c500010f0020204640c1160192500284100700314804002090811a10100c13020099949600c040704400d60441c0d0002c2c007040c0401002050200ca504014040003956241c403060a41d6903040e4024030301070070f000c0240142c01c00c0000f042c1561050000d0350700256122000100e0558400008041d80d010300c9086820342d448d40501815984c16204280c580c1d0301d00d08105030b421000401803a203070441e03402214800d07012211400100c1340304070440481103d0701000180c0d911f1000001c01071982009111504522036186d54201605041c0101030144400304902081500d4040c200008181c03903400745551845a060a19055510004c440414801c0495128481400c40c200302003135600c2d03600154501c000400500002860016006440c1500002000d11585950340061030194003496032b00e2042c0d000b170415000c1d0300340c180000c014000d0284071031310010b0600001a0141c5004a0b03c444d8160040f1641c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 395770953 1250 395769703 395769743
    0x9050706050309030d09060c030e0c0102100e0c0a0b030901200306100c05070605210f040206030a1103100806060f1e04060905181203061e010c021002061012 69
    0x1031038000c50f02c00107403414401004904000c035900d00205a81860729500408545d540600c61540040070100103802c0d56002600042e50328668130b0300e0071510b143d6500900c1981c800520440b407001c0c1c2c000308490501691511001d01580068414044a518200ca16407400c1d5040c0a110044d600c090307001821980c4410401032451042540360086c0501d13074a0000001d0010300060000c0c0c4420f4642035120240326070290035407500608200b81c0003685105012081c040400155840380c0d040720a9603981e070790710311480c01801000e0a60b000441002c42404101180700d2800c40503581c0c40c1c01266620b0342c42100304402d051a07040d0250304124190014440d441c2c1c0c4607045d01d00d034080a00f005c6082607440c0002012100f084800d028100c103450000540c4a900388101c0c100c1d5403180314040e0130741c18141c0000f06030f410050b460401c09102c1c04c02c5409a039010b82200948240c005194540c113200c11000030f51a404202d0340402a8481c0e008007080c01425102ea40b19600c0d045000446140c4050340c603 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 395772203 1250 395770953 395770957
    0x1701120f0303021e270a0e0c37030515090702010b090a09020103060501080709091d010c090e011730040303111603020916050c03040e01030507090905070605 69
    0x205604254082108450644c03800d40400c1d40d001014618a564510104564500e0f504e0a07020308440303801c11040d02d005540b102c101380c064840342d294801598842181c10100b5100d0602e28884510164181e0701c824940e03100b40040d806240000c9610116400c10300710116a01150402d002d0155004090076a090140b009907201c0058000002c1480001c00001c83c610421101c0314a25516901d0b20030455a03d070144200030902820b1401c0181030451000e81001413502400c503007217a0303071072812205000001d803032100202d45034005c10050200c13503001000c21b03100f805a10040844480006014000c04020600242e0642d010f004d00c1c035043c190004044207541d4425400b164120107184400300c2d10750040004620a86402c2d40050460403610704044074416a11098072000d1030410261f02c0d0b0a11066005040c001c500304034513241c0c03000341e400b4040c0c400c0c1980948408075011820069106c0000d058a02600449440941c0e48400006171543c095000305203402c01403080080d1405840 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 395773453 1250 395772203 395772233
    0x30f070221030a0c0801080a0807110a03060e0115080c0904060603080a180501021b06090301060905010f0302092212020c04020a091503060f150e0405090706170112 72
    0x10603141e1040c14014454804a0900c5034801e0140000050002002140c4120461010a820186a10340c9090441525918490000b07840320400090a4040003040445080040c40c0240561540d54590809030000d1040408030380c0e580d80707024032031550030115960b088211040e103402403410021160034004821406031084030300642314803000c0b0005804d58050035190034581d40e40c2c480442085c0501d51105403d5100c02e066401c4140c1c141224845a80424101d01e01038811b43d0b030f50030b408800700b8010a40c80e481485200d240c030001244014400c0e1144040744d0003110b401d04540c5a0940b184003003014003c000c010700e1800102103000034200c07113896001c002d860040c1c400c89540344003c00c00341da000c0c41011002444241040c01500c1e0a44942240100c440c9810010035041940b000c2d0651910b00901c250a010000000310b514450208100c1800001d4028041e5051940182ea52425140950404600340140c1866082c3e1802405030403116940c5a22242c80c00da07445022191003224 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 395774703 1250 395773453 395773457
    0x103260f0403030206100909030c022e030c020d030506090a0b06160503030103140a02220e0f030a0905011b0206070213050405150c040308180f0a0305070501080a0c05030f07 76
    0x2010303026034000018040d01c0154000d8024101c10f140c00c0c160600e44410f01d401145000d40b50159900c08030f03910440c08800301e541034030380801c0a04046c842c90801d165192300c40300c160311180e4060a0070355058000755039402d80c0e5001c0f1440c4006c0d8580503811744e44101d940b90b400441c00b0001491428260700301d0840303064003400300351905041100c403400b045004282a1210391000004200304141a8156001c0101c400094a082840c40d400205188030b0002161900d240317200c440b1400c103c19074884001204030b481140c000340080800b507600da810007002000402d07201d40c0f0018680d4001d0414201d0707080500c04148004800f607080100c0d80e00320000c140e03040800d50b102200802601e208480c01280030380000c017a18017080c16074124003c0010b100954000050104000080c0c1d644284c40710b01207008120544005140301090420690310002070740b0640c000c0001043c001d000c202c410581e0b81c281d0f1003c03083d40d04c4482d0001912101d0f007690700000d20400c00180501b03658a890380d0043c841b4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 395775953 1250 395774703 395774707
    0x40b06040b030403050702181e06040b060c0a17091003020d02121906060e1c02030a0512040e091b041509060902090f03070302030d0522060801080c09010326 69
    0x2030900d55015003040303c0031400308000290402c00c1d4035210043c04c903040c200e65034119180c038001103004c00681410107210066a10903021400b20342d0b0300c1e0801c070100c51014141d1919817038864401c40d0344140c0c4002c00d031250280903105c070341c80e1056442141c944c0c2c000500961920441c80e04200c0095101a03c80b501c82c1c1d600b401a19840008100b10501800d8845a5540d8500c0342d00c814000320f80d0fa44d0700c4001485a40d640c086401d840309040b480300440d8000f100d005a16446c00071038200300b600d2a00402d54010500842044804d0790003070025500401d00000f240da540c09401e5a40304006005c0085e0b40149903880e0a6525060300035100c500b0382c0c02150504c455540c0e800300d050303510603008000503030380100b11400700b410f2000400c4515007084008080310786c950b4002c40e8840d0f8060100703404100b4000703401c01401154145048109035400807100342c0507902c21000304142000e0180942c0360141d4501c4c1180340c5410542c0c0c2d030581c0c0c0c12945c41c00d02c507590083c44015094813620100140982 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 395777203 1250 395775953 395775959
    0x5070302010b0d060b12060f0c090d060516110c130c1b111309081b0a0c0f0312030207200406031e060e030307020d0507060209030105070207060f020f0309040b0604 72
    0x9143c3c00580ca062082d01c0100340718042d0010400140294030300e404aa40c800410802502c0500f203456812107514100f0f1980c80f00313890042005100d000c140a0302c0c088c00c220620503414481d2410000f000215583c00c4001e00100d100c1540b100d0011400c10f50049581507040a10704955100500341256400c16902010040444809005507541c003920300a201c3c00c40051241041006180c0050111104110003042565400e003907010312205409004a4040c4011180034104481d040140e00181f40d102c0c900d80d980843c4504c0c00d50750100311408100400001580c1380a4005c0d07403a16039200306030700310f81c1c070780c1311880c2c180c0d180c4c2417410a44c80b50715420000041900546080910395800d04d02c01641c0c10a42440d0341030326180103411020394000c2041011403640030982100c400d1a610b07155030340d034000e0b04095001c1d02403041902d038194030300014418030640014944007200c900f51104034100e444030000f6a11001c4c08000d104440d0010407041c5a18581a8410b0b00045d00090200f41410f031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 395778453 1250 395777203 395777209
    0x120406020d140708040b01080c0105070b0705070c1401030b060c0d08151008091612080706020702061602120304062010021b0c030604080a0c15020309011a04060302030a0305070302010b 81
    0x20f40b942e1000c10440000d0006000640b2031143c01340c030240006191000c07940c00002c049204220000c1c01d080c0d40c45000c5024240300340c00321030041c1d4002c1c1d03c00302c03400d4460080c8072114040000c0c19003c281351148060990600c02c0030340b8510001c0c0400390455542c61142566101002001240030b0501213003208002d03a81c80c400c01c81d940707206a40c0c901c0545400b249a0340b4000d160907040502100030f000800100d00d0400b03521412a41c429100345c3c4850692415030080d0140318070007540320303d01044d4403000d500c1d552a410040d5000300c070315075254168000e03440d0300ca10a6000317035000a51030105440c0c10811000090f202c8807203503400c50b43d4900302c0c440d4020890b0000c0c07403040030310040c45418880a01c0100b01c1c03414040001c5015011030b0800780c0e038511031351142c40031545c240891b0f007001905200d020500302d00da040020078259600d10345114400d0003452007511564581140c85160b441a0070244182c2d01a25030140c010204006551001d598540000208908640d01c2c1d4840c5a507030b031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 395779703 1250 395778453 395778491
    0x506030a020d0608120a090b04050901031203020c030f07052505040c1803060c02160f060806030f06010306050129040603020f0d0c0807030e03160210181415120406020d 74
    0x5c60071900e00751144000d41000302103010560224885c06014070090001d543c40c2c4214030304403544184140300d0203030000300950190241d03032180002400007098000c201c1203402e0040000d02e10a0082d1101119000d400c260b02600c0c541288200010510b0144007600f0183d00c028442080360030140c501d400b0302070304800304101d00d07002181c2e241d499204040c14903404004000c01c2518a0f041141c2403414088600b0503034085124841c1041080303804a41142c60038419156a02424002d541c0c8660b100c0c1000c1014003801e10510459400e504403441d09017030b0400d0200794000c5c01c81c40d44c2e0710b0300c2d250940071400307500090150b04840408121800c50071505110708501d2040c0d9071141d40f01072400d0b180c043d0840704411030b00080f5030010007000440b0f041008042051590446040b07002d100c1000d070850340090020500340840c2200b080128a41da1204201450b511f0100c5203590b51403600a01c464a60145417001c0c94061500c1c00802d001500e80c4c1c001c0c00c0c24442000b800140c640200c58030a00407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 395780953 1250 395779703 395779723
    0xc030b061303061404030503150f12010c270308031f0303030f05070e03151b0d09110f031509030904060303080f15010e060c0709111c05010506030a020d0608 69
    0x2101d10000104200305143c081d81d03c409109a02c40c85441c90a43c07400b0b0640d20008210080c080840d0303502c0c80d2180d854211548040d8009008030b0000303244144403c0c000c1c4000e0f0041300104010440f2480c203000d20703544900b4400721080481c40d9062071071742d4124090300042c0082e101031303202018030b440e0070000c200048002c6000c3e0380d001c600201d60702c03c940215a4003174401001c02c10104c41204803602d00180c00710320541c0c4804041d203a030f5150308440c3c0d007480d146821000d0801002440c2c2500c01015003101c0c1070540240100340340c02d1815010803a05c424505010350705900300d403200b0700440210005060780710384c82c00181c0c4d2803d030301d0f100003a080354055007044000c100700f5001d2000107003040049a901118890020213226a1100081e140000c940c0825100700b800207480540d1000901036800201313040042840300300c081102080c856040020b001d10260705080c40e8414580c154001d050417108083c003060b145885c1d40500314065881604044030940e02d403200010f070312204004030040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 395782203 1250 395780953 395780977
    0x606090303070b0a1107110d020d02040e0f0c0409030806100c020307032d031409033d06060921020d081801050c060a15030b040303231003060c030b06 66
    0x414500b103660340d005c9503801500c1641c00001401204006041e18a88034030203501202d00241c22002c620000e40500c141f0b03035009400906280040102503070000300d400920240c04161042058500300b80710442d0441c81d000341c005141480422180e04041d102c0c5c80d00c0103428648000c8190b425008645441050b034821101d001e034010703000c03064656102000384051200c1181107005802c5860041c841c0d101112040b0141d000098411660382d010000c0040c01c034500341c5070b42201c00240301e0100510360b0351400d00d0b102a000d0003c00740c10a840d80318203800c3c2e910076213480f0b004c5410012090030303031100b0440703051403110003040351130150792401d9007159610311507444640e0383d600540302d00c410101542c828906001051042107400c00c40407441c031354041d914180c0040c0c000c101c5034000a1a20742c560018149400001c188428140e1540041000f1000900b1b442525030040401c00030602044030050300f000e144030f0b028400940103030001212912280f4011400703102e0b0038000780550744501c1d02d00c80 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 395783453 1250 395782203 395782223
    0x3060213050108060607020f040f1515020f1606080415140a11040f090b0312030a0e150105010f030c020309030d09080d1403010b0306041808030a052a03060609030307 73
    0x1440d82d000f2481076200c1da050f24038a04144440d40401c504218400306184a26116846c0e203a69001c0c0b580140400640022103150540e0340300403030311004041680d684010300410162860701140011803e000c814903038038410015240c030400325040700f0003800856038500c9207640c41c422042103008501800e04011015409801d00f0b241d09009c41d40d9903020f010081806110800c0780c0380704d9086110850706a210040b80c100100e03800a810714001e818004da41c008040240440ca000660011500d03111040455002c407022501c8540c103001c1c248111400a0401d64030278010034442c0d080341001c000c40e40122420401e2a500180c20012140011700001e85200020040d0750020001780345200c8060900b001503942402ca15511072205010701c445c58100000031038040c1e1540d900030b51a031464620146103003482444d045015500c265900d85415040c000843d01c00d100c58000100c3c001d4803d4884049940d01610300400c40d04000c02682e440b060a0242140c503480602c01000034611901c1c07801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 395784703 1250 395783453 395783459
    0x602010b030708160512030706060605030a0b06190f0c02270a0216080a090504020304080309061b0d0c030b1207081e0d050711041401180506030303040b1003060213 72
    0x1d840c20a05a210301c20aa001001418260100c8804001076900035034014400c505280300d501e04c1d5200f241c00c0100440d14007480082e9035580310000c1c40c0509460f942c2030200001c00020003055004840603c4820303851003844040150203400b4071341c1030507074504000c581c125031034001039030420080d1090380307600b0340d910749020100a00884172903122402e83d80441c1807031001041c1141c1f200249134003d00b0039034001401811a4024000c2000828000b4029503407840c0034903021505030001d65401c03040c0c0c420385010503031250001c908030051007200d41d04c1c0f50a00b00c0000741c05000c0c06090300320341c0a16607503403060881c0da2207841c19a8800e03680d0100801c101482c00300064030f00700e0701061601c000202440d00212110022861740000c998030300e4a2a160b02090803d104108421f0f502140e01900c1c2c0100026440c0340640418105c51444203507100140c4616540002c0d40d100702c0da82c0b039045d0005c000007000150900300060704200b501e45800d00301d584a50365081203134040c007a50903419215035010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 395785953 1250 395784703 395784709
    0x203060315040f0308060a090501080d1b030210020306120f03071406010b0301060804030e040e010f0605060708070206070804080604060902090705190809012c100b090a02090105130602010b 83
    0x418001068028080c0c1e440d243d101d10302c09024602000f0100010200401c0b110358840340c0040103810622030400c030b19691080c200760b9030300f0b0114025021a8901616050700c3e00c5500c00d641480f5016000384c5110103180f8840b4000350310007030110f6800074420100c404001c00170801040c840e10280700555840700d41d820001400520058040700b2a0b01c00300040c82003a0344403069a046940e9410441015201e92400360394040075000101e0300f040c0b130701d00c00820b8440705400908440f00b00c01c004011042d10340741800590f04c10500081c160308130400801006050020003044481d010310421740c201a100e107101070400c401500d0a44007952985108825807508500a0341c1001d01d03402e20a00c0c00700c04000e40d5007070071042e003200c0060005820001c0c0c041c40007904243da03402406680c10743c0030750107483d204c010406601000b00d40343c42100d50100541140780300d011081007005001d07000940d586250302020390301242d100c504120003848040e00c01103800340c081000c0c00c1c1540002c40d4080d551418 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 395787203 1250 395785953 395785963
    0x308031008010504020114030c070f0b06040501141c08040914040c050402041203031a190608061c1205070b0109060602010c0e100f05040b07050d120207020a121406010902030603 78
    0x401d0303a40b52000f03000050380c00c18042000b80030307052070b069126910074070071180a0003109006020581c079400960708000e0707a03900c402c0c4a040c0898042103aa40c071140421035071340000205d42e0304000c00c0c0d20300120440700311418200192103180b14030701d02526100d0309000d440d07240b40c0b4075101c02644001d000401284196a90207007409a40c1142050b140c182051481c1c000340c41c002e0103040e40e0340f20250840d40048012003e00e080038108135294484007294240364543c3e4843d400000343da2002040300d91408020320151401d002d40d4039041219592249100300f40d00071260800d200382005040b0014000c402124000c14134000e0014110303203455800390a441c4c99010140800c504071148603603e6851048803802112680391070081c00c01381e10020388451040d900400000c0034040b54071003c1090006401000c2540341d40d82e0071449040007080e80c141d0050140081d407200200006000481e00300ca070040c01d06016030b95a08540d24916402400d001c020713007201c2c4a5580010811003d4142000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 395788453 1250 395787203 395787209
    0x715050714010c020718020c0105070806030c010206090709020f0c0d02030d14131e02330a0507030813060f0903020d090f0e0601030e1608120f1911030403080310 71
    0x380420149800d000351203500c64014903c80c031180e001006201b040c513074141c969142c0514002c002c1428510740c05417410304100c813040d11900c04c1c00880d850b254400b0600038051001840101889414a40c40002035040f000b03902c044803400b071000300c2d1680e5040254504e18010342c1c01441d070700c14a4628000945052210590407110841c0a00c4074501f00c1048881072140c0212100b0101c851702d000c89100c1400c5140040d40c0003c1d03030390000408110340d9400c0118204100303081d0760440c0284040c000b05010340d0003808082002440020003090050240c035601112980000a4101c00c0e82d41e80002c6640e01000c800480d591342c5807503410580c042150100074000341c1040b002041c98181144074000090081d0082c260320f81001c150903034001c0d00310710304401100c0c0c1a595100719032028401105140d106440c83d91060031001a90f21001000f00c030f1900c5450000240f80c0881018150314446071207201c5010403560780d000350007221092004d400030b58440e6100c107030790b400d02013038102540b042c0da0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 395789703 1250 395788453 395788493
    0x206160b06101403040327260f03070f031e08070f020c030d030e011d150c07110f0a15030b0f040c020307031b02040f050109050a09031b0507150507 65
    0xf6400b0700c040041000340c941c8260b16181014a00700d03422a580b24500c4821001841c1c000740d1600812400c1c1c210400101c1d950705810815441210391081e26680c1e09413030300010954008000040c0171907181c3e040241414000c0c1011240800c40c060041c4020903800c1080d800202c05030140020140d1006d0349184e607076410320007841c80c400800d001070344800b01d4410032014180e41d103045285140c42900800c02c8442d2031405050006a03403c40241c40b880124448480d0040901c00940480105c2d804d0300e001030303000498820a0001302e0f0038005002c5c18803a8030b543c0100f40765000039928100711030401200340c07140e801140510014051000c11050b98000c0b52150f4200410038440c00d0380002a540041d07050301d0a40305400d542ea0100e1110b0001240c003941050038500030340040e41e0140c211030704079142c03613070708004a81e50342809000715410603c004001480c070000c000e1800e038105501445043c090307070a030bd103869950311003110f01482944d0801c02042022800030b091084215619601400e01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 395790953 1250 395789703 395789717
    0xf010605060d0e0c0306010303020309030f030a1209030e0d05030414180705090a080f0109031d031b03010b0303030f1602071a07030504090509100605150301030602070206160b0610 79
    0x8180000d10700e02941e66418a45a52030143c540100e0040140c41d10004020b07055800d07658581c20020b48917441664040c1c040e1264003890f001003100007045503007811490f40c490904188024a0102400c191882541008141000c03240d10b559104903107003d9a20a8004540d0350b40f80501c0a050080c0712500d0910a1188000300800040b49041c0f4942c44007552074140d0790340806000159a04009400c50000c07489114030a912900d01540042c000700d010b511420006003075002c820083c12018961117070107401015501d014050305c0019554882c03002400440c204440c800800e2842d00111550080c9111448c203011035141d40080008030045140b000c0e1030030341c0c1000054640b00b0101d8001280c40d0000007a40740c02d0501c00c20596014007061142800141410105282d441c2200080d0711a010724081001866143c581600900002c20040e0740b421a031941d103410009400510003a608100e003000782c45501c0607507119000c0c40134440c03030004a07542064401d003c84603d05082480a10120f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 395792203 1250 395790953 395790959
    0xc0510021812011401080304030c14060a0305060102032101031a0c030103140a02130b1918150801050903030916051c0c09110c011b080609040602070213050601020f0106 74
    0x1149040701e00c24005548400c00501c0d074040032401004400c00070348804c007038a000851464030200c001e008490042100001040e104c0707a00c82e555800d120001340d03101a0401945002c980250046948248140156410043c4002d00c81c08100c0300420100320390700d901070040c000c20800076038a5100010510303104c5a81e203000d07883c90440b4401070101800a500361041e00340d181001700203c4080d00da003c0c052205800b02c04e40c0070001b422242c079220b44a901801d400304181080038040d142141c210344640119000c1d800003c1c0020300307403540c89981d104400900498000000d0203079901449241006590b240b41804619050045038000602102c0005200700915620041f59400c1034100749140302c1c14486502d003090300d204540d0300100707000c1c1c00c1040158101e03082c00e0151549204110003130201000c030708100790500c48000549408244010003003581400d040c26039030350043c400c03680189405402d40015080b4500d0f2000640a507845104028480d40e05002070a44511114024070100742 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 395793453 1250 395792203 395792227
    0x70816090609020909012105150708180d0338150414010e060c012a090e1b070c0807030c050315040206030702071a030406060807150e011e0c051002 65
    0x5041c403072902125800c2d81040a1f0a50408032155029446000c541e145862019a0707203010380210384807408180c4090000e0444030705d10b904500421410b402801400d84401ca044d0020100c25010304c0000503030150003003400103100329456500008011500001e4180350402020b0740100548603c40c010900c1304002e2500094841d079400b881c242041c41143c1800d40c040b07003190091543c1c104c0d480d070909488102c04001100600c1031086c0c110090b4910700004542521039038243d100d07003400c0018010001e203c140c0f0006274021060b0480c2041850101c5549030788840301c00940145182e81c00c4002d00700104440b0281c6640104819005490b03800d242c814560401d61004101034050b03003001000902c4c06100740002802b40c0703c50018040807100712030302c070310042d0011034084540511308200480c40200000380101180c621160403060090660821200d00219640b03c60601820a03103c541c441c1003c40d501d0b00042166640c5001e000c400c0c10842e10b00844802400e01081c0704100c902d20b040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 395794703 1250 395793453 395793469
    0x907050a0807050d032c03010b0f011b14120a18030305070b040c0506040801090209070306230105131e090203011214100509030309150618090708160906090209 70
    0x210f00311541c00c0b0002c0d0030306068071080303000490564085550481d00318041c100c5500f00c07403100300c10f038001c200c600013a500b481003030382c1001b003000d010402050100101c140170300054230007288039511883c211010610550702d00007403601031411000c80400c8101406610000c0d034000040003143c0941110301e1910098110312590310302070840c2c500350000506106a440c151802800301a002c240d90b2591030500c02e00904018100700e11481e00c0c40c0c081414148280100015034030401e404100380100c006612030390896900303502e410f1010030b010301c010410300700f10b40c05c0003040038148001c4021940c1000401c80d000b16000441f405105200501000b10a00c1c62000c5550740f010342522207144015100340740040d14020b5000042c180410001ca0764400b20186025509444c12076242d9044e0750281003030a84101c4805401c9000d1003243c60381d0400c0c022603c2e80110440c026114010b455101c11824803442c030820349084844001c080208200500ca03500090515010440c1010381a00c0095544 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 395795953 1250 395794703 395794709
    0xf0f051204120207080f0a17030f06060705100c081f0e07030f180507050a0f0803070809011e05030603121314060f0315090a0b0306040b0702070f09050907050a0807 72
    0x1010302c000310401e041c002c110b0240035041403c202c8a6400600b40d0040d5034218002e811500035900d400c0da01c2c518404003099a02030803201403120402d03510a8103004c5180c011a1040d11345105c1c60b1025030042d0349500c80c0e012015440d42c0c0c1e4845500d8451038101e24545000319840c0c00c0031410204109211300c0243c09600700300176150105545008044810141043c1c1010100c412602d4000c2400c010002600200316041642d030086116600e100000060020b445041c00c01d8100304100f030006400031000740382025050400140d921004601a40c0110540307024101040c4004207009030384c5003c20040d01908c50007030549182900700d00017280b20342c0f11407148806000c4880000409507442c8000d46070b00b901440190f98a80c944400c0707010300761181c0c0141303a0141042001180081505000d42842c01a0244c0249a1910f5a81d1412540400104680c086000710140460403440c000030180092000d4500072030f043c1400c0e0b20705401e00f061580036a202c1d001888e0100424000400c0070011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 395797203 1250 395795953 395795963
    0x110f0306100e1008030409060e090f03040e06040e030c01060830030408071203020301031a0c070314130612060807051305190207060c1205071202280f0f051204 70
    0x142e500d0700e100c40319001125400442142c08003060205010005901540031201500a60841034844846440d101c00c0d00030200d0100f9003040205020790350f1820180c6030001d002030301c0016010740085103541150000328040541c0d945940042007800c03020800c0c0eaa14800340d0413030828007100e003c915030801550f420281e180800100005003403166010503070301e40da904079060a008100c002d07c0240258402d0008581c072000c07004042c1d0541d03480802ca14441c808102060f890700099440558401000e21400085840c4c10841c00301203444111554000304041d481d8041c0c902c1c0000000e40a03a801500f03c909954411601005203a440c486c000a040000341c83c0090b072a00c0e03030018100c46415070b40c92205144e0001900d0700400150f940023502c90001ca5807046030108000000b40290b030300c00d45140f80040c40381503038401406502d60050a403440d0070410142000268030104104100200c039150119070b510b84040c0c00c16820045284e8200214541b07141341c94410303080c1031480c8801500241c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 395798453 1250 395797203 395797229
    0x3090c01120b060a0c0c09060317090f041503020109140303030c0c07050d030f021b0907050d0f1a09010902030f040807050a02031c020f1204171504110f030610 70
    0x1d41c203203030b900520704188081e003c40d42d43c443c0c5500c0680703100c8845504a4035049511400109404141f00d1007044d294004c100725245501e103008100c00e40c000a04156001b1441609410f05688074411403070461180c1c00c229050038074500016000d8500d60303000b0041c082080130f00c1d10a90758044100c035400990504020303101c040d0b41c0042441d10710107401c49030700083c03401c480b00306064004071a445500900c0e400c581e0305c1480140715118005031100040e410810080204000c40d0051707000c1c02d0000708080300041c1a441d8411064282d4510b140c180c1c01e01d205c440c00701c2c90581480c3c04203901500164030309600d181040e9030b40098484000b04040e040240120340e441c100402840b000d17541c43c0d001003c440c41041c0c1802844405e1500b800b140015108403090403134609000310b044d2015a400d1413100e401c0528106039090b01c0c042d41c00e84d07109180100200c4480707441c40b4420090089000700011440540000c2c20f1160005040404c81d10030307440780c4100410500c030803e0b1042500c03d2810405 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 395799703 1250 395798453 395798477
    0xf0102180418080a0804060b100804080c0f0115060e0105040614031003230c0406030c0b0f0c06130506010504090f1b050301091b12030c0318090903050a1403090c01 72
    0xb10b00b481401d14002c2c058840014401c0c0400e60080490380514003500c410060f4000441c108250b41003001c407000d000c070744070798005030200c0d41a60142040318102c40540380001490800142198107403041983d100c1e40000303081c440b446e4003400c0342d460f1110030b003000b030f00e410b0034000c01030030120025103441082000007001803040c2183c0322040e002542c2c80b09002e0b92035800105001480c85818101500601c07540e01441c56520f814000d01c1c08598218101c1d804185c181402c80c0c600e0350214500c007219203001c0202131540702040045a00c514040b8511801c60400381c94071174100081a40081d01c264105500340e00496040c424589206a000c0101c6841604101e4044001c0140d540640e60651804c50348606002e5040c0071184558504a0500001a02e1b07807030b0025100c8101c032000d40000e00380300c030300f00c00240100c01030748804000c0d80070038610644e00d400b400159880c41004800241c1c0205031610160740240c0c00c0c840f40f006400403141546400ca18440e80c0c0d074824ac07032650400804042039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 395800953 1250 395799703 395799731
    0x3090503031b0403081c05060a050d2a060f0f020d0906050c010b1c060f09030e090a1404031709460f12020c01200c09070e01020f01021804 61
    0x1d43c021907000781c1c016100c884118990b00c5c1049031490307007088642030000144075894003041e5031096550081088100074000c2d1110344c001d41031105040d00c100000840300c1e601c400000484030080420b83ea8801108051203c014802030100321240107550100c44109400f0b908400001d003514454607105444807244444507001d06080d141550700440e00c00b80701d5181604004504080d2405081c0600038041a020401d04490100801a00048144410960341e19200c40c1c1550072040d62540840c0003140103403050110741080d581103002c140406480d13811800c0404203664000c0c294006040000b4101c1450174042d020002d11a40001070303801104000411884106102580c900403c1044081460306000c0c080c44e80e0b0b01a60148000070a512409200003602050110181e407100c44056600291403211a1154200345980c09050207a1520340c94403000e080c400c005a03694000c0910f00200064103102c0680300c032400e20323401000702941c081010400b80c80e0b4110b00f80c40c0040c0c110f148000c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 395802203 1250 395800953 395800957
    0x315031734080a2102091002030c07060509190801051012020d1b0b030408090117010f0918060c021c02030f03150103090206040b0d050109020711040917041d010603090503031b 77
    0x30451504084d03101002c0400795503020704103000c0181c8040081920503c81640d50340155000c041e0b03d6402000d050051520407406840031402c09051601c031f02040c0c1c040712640c401c05401c20030240e0354900800c503c0b010080c2c0020010940301c2d407441036118054000c01e407001c00404001c1c4c20021080004250700d40400c4802008041a80c0e14a03224105480c103804075070f11121009000500c1d00345d440c0303404040c49082c14100d920750707141150058034160400c00581504809040d070707402c40e154000d0210390305006100c07140c01681c2c0582070000300c0c07610301c070010022151014115032041c002124401070040440350481281c4000300c0740000c0800049003d01500f0a000390494400b04001522600e00406800b0f004c0c40810184071a81e20b40010604a0244100c0a08019591089048241020307808484014040e01e00c0e80c1c413080d50408044080d900c10351100c101588607180004100c05e183c1d00b80f0380900f0103403030103100b8034070651581c0790703039000242c81c0064800c0103030108545203040e101 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 395803453 1250 395802203 395802227
    0x6070905092202030f0706080612030a0c060c02010603300921110a1203020f030f04031e1e02010206090d020309011809050c0309100b010f0315031734080a 68
    0x11510b01a41f81e0340004c01040064030418018124440d10201400001c400e41d480720186643c1d9840252040c0c42c1ca01c09059001c16100c10355503181300c0440411840c03105591a262644100645820300812010040c1c03284245441000900c0340140314150b005a01c0d080d11500c60350700c82000081c03600b030816000b160301e89580d41c0006055000501042d1400900b039030784d4007a40940c0d0449011140b410b860b4420512072580d00c2504000a10000b5148081010600c821380c046407150f41c040d0765054401840c51b039a40c01c0c584e201d81d401ca0110341e4108032141c0d01050707001c094610300e42c00c0000a90b490145440e9541802207200041400d00c01c400380c1400208002e4909121300d0400c1040072445500c1a01e400c006030040c001c40c100005481d01880b400c94006035200200107010143c100c0051803000180040d2484007040040420100801030410410f2514101e03a2280d41302c1400c008840f5115181d200c0381a0131403203415040c90038450140d45604510407560700e40c1d0604040b2000d04c507e403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 395804703 1250 395803453 395803483
    0x280e030f03270c0d060221070206010f060c020d030203162004020702060403120c240e1c0f0302040506211b07060506060d0c0e0f010315150e09090607090509220203 72
    0x60300307c2030441d195242a130180b0025001d882061343c0303610030b032401d0054900588010600d200240070040c10040c0c030004200740240705503401c1c525004090885c2d4404010290358681c005510019091295180e1200342d0b03600310f904624140d1a030703010401502039440060420320f140914194418000c50000300c11603449003000c014400200e1210b09403003864110305000b60301d0302ca5130060740100040d6035480c2d40c000620f552400f400c006022105600414022000c1680a0000003019220940a88400c07415104004003049550800e40b0039900020000031906114414103104500c40100300c8039031503041840403c00317a0719400820414809c26941e5900719190005010032207500128030550488216408100d100300a4011801d407466032440c000e03101c000e0380082124080144024070341c901c1604010032881c1136600003036610300084480d1101c41c0c00080c20800c8165100d01102c000d400300320b4a85400741000380d00340c1c0c0d00f03007076410448945404440500e0300b0356400b0410074022503048 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 395805953 1250 395804703 395804737
    0x106080c2b0b2202010e040c0306080a08040e0903131404060e0a14010504360605040803070e010c03080c031f0605070311010203280e030f03270c0d0602 67
    0x5242002c410b0800312200308035900a4040e00240b660f140c80c070140116016581c0341d0702142c4900402c0002c1a1050851051580d2910300146009043c0f01d0030f03846030300903448a03843c0c5103404c00302503550790028070171501a0410810383c200c5802031644802a5842001003010750724900c0c0128000301107a0300a1a01810708004014440003503070082d403101c4140c0c044103401d990b82c42c2d0505c4151219600c000718026050085207820300090240c00c065845d0381c0e80110005445911141e0890f1000c1d281540c0318400081000700e8031b84c024065032540304081c0b92981202d1601e450080000030003425242c4c8814001000c00c4050320192540264510001c04958200381c0e2000090f1103540120011000b003600320001d852101010701c00d680c881c81c03001c0803401c081442900c01c8110415842d811b420700586c0c415000c00912010005001c40d089146101550381c20006915182070721a6007464031500d101072140c90f6402004501a00d0a0b0016103072002c0e100c041d498424040c1c000d62036103050348960b03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 395807203 1250 395805953 395806039
    0x316120519080414010906090b0708070b04060902090924130507090203071403010f030f02061b0109030e0d03020c010503130b04050127050601180230090106080c 71
    0x900010812907001ca507440f2403071301d840001074501110605c00d84004c03039800c060820800d5400402080309070310070801c00c0e00d0200c1c0c950f42d5070044502a85c0680d4030660b2401c0400c110b04003451000d41042940c030080860801010f01d00d152203816040c1e80c964003524001040701c081c040003e80450550000c1a1101d0316100c1e00140000d401c22110301001403070b03402411004059010440781600c0381350031400382e41400d40c0c40b66090580d407004c0c2260000810032071442060640c020401d074080b03030309001080b0b04c1c2d0380b400c0080c40c00b205007006a100d00c030000e800b1b100003500050817104210081c00e1144d101c0d030312481c60442c2c0104100d000340c0340201c140200400c00406501018415080c402160f046c1c070246a00094110b02c205c900600d141c0c03012005001100295101c8001390007802c01c00741c0703070a80341d0601c080c251810090424880303070740c000c020600f254010000303070b07000b0000002005502d28180345241d03128107841032203001d100e9180350080d2440c4402c00400b50690000300c1c0c2085142 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 395808453 1250 395807203 395807213
    0x2009130f17360607080c071e03150b0d06050c091009090e0f06010b0f04090617010f020c0706050c070e1003111e0103051905070c0c050316120519 64
    0x940031a010448070000ca0001c00c902d02d840b16100040c40103010b0398248183c56640c5050b540c441c1c00052118450b0036800a00c1c84101c10f401100420071520f0050818a1450324501c0b40401c1201440c1e020306009448082d0745500d886178407500d42007400861030307854481110400340b04400445402c0000c03054400c4c409038000d00e0000850f40280002c000c0303a0400640305841e2190000500e200c0e070080001000480e00b1300d17000e4000309030500364003480c19a40d00e810307508554803503106601081174400301818500d001c2c42410040300800c0d406510300040910441d855000b540100c0090140c00b1034440907155003001104058006954000c2c804d06001a00c411810b06500c011030300441d10440c0e040b01c41c00c0c0b140f00c40011000290480b0011a091310064018044c0104944001c0c2c040d08007000000000b40540c85c09084030380c44244603021319042040c81c005050300f045000754021130380d041c0c141c5684208801103a810203510840703400342340703841d504203554003078200d020b10300710015002441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 395809703 1250 395808453 395808487
    0x1e050a0b0102160b0301230d0f06140903041a1306030b0a09020a050405010c050f0a1113060806160c060c0f120c3203042009130f17 58
    0x900240c003158250944000d281c40d5040743c1d4003411007041018001081030703070300c9100010031881048400d1400b10800c070012510001d81c0100503104c191300b02c8190300c248060380c0315100c0d0003880c99241520500e051420680e5901c92441010340d00100c89181e050003a15003800c1d01d840b00c894200e2001840d6542c2d03401800707030180096151003414074220002d41189140700f02e408070032041e02e5070340c04c00d842c001c01540c058406000c2503840380102c13401985424030501442034240c1c41518909104034009003489601400500322034404c3e8602501440014800a85541d0058551141d46042c038488942242c1d24240540c0041002d82014685203400f41c0202003044005c03000d503a020400240d02e066541503031120b002e030001083c100d01a60b081000342c1b548504aa140e041911525411500b202079005c0d4401c503001d8842040c40380c02c12545804003d102c0c2c184101c100e0300001e40381041c013403d8016031090034009082d4541d001c00d2108100c20248180d458100f602c0b00b03103480307110801c0305844034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 395810953 1250 395809703 395809721
    0x30f0b0405150403120b0f03030309010c201f140709080c0906180601050f0c06061504060801090510120f0210021606030e192409020607061e050a 64
    0x1d0044202c010060101c4101c0240700c0d40d0141e4440318201a4000050020310044080c6500011002d00d00c642c2a2410001180500c17105000082c80009074075004102c4011121400a22680350105040391100007032a1212840540601e1144072513540c440c01c001c10300c8401c010f83d036120040410001c150403a11030781c100c0b602074056401041d00c403000c120302d4880032134140303034002a0a030720050742c00418103503d41d210b041818810302d044804014880e09800c91488042e040c0d101804100741c60402e06808450401e03130845107410a41000009072100b2814003070021401c0c3c0d02d1001070756003941d44c1c084000030082601c0304215040581080c80785141c0307001c0141d000e0703040d11940d200018030001d9848504040c200001c9100c50034401c0c110094002001c0c241220312611454044a060409204086a1240c0040d1a00c600c6001040ba14458041040300d03c040c07a085040d40581c460354115041554800780009804030f854071140c0d6007056402080030070302c0c41e1000704003640f100340d4080c00700 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 395812203 1250 395810953 395810963
    0x109081e0c0a08150604050105060304030e15040f031406010f0b0a030609050109022706090d03021005070906080a060f1401020a0b07180b03060d0609330b01020a110603090106030f0b04 81
    0x191741c60400b4081070f19000c1c4500740d00f14008100140103c0c1c0304204000043e58020314040e103003280d0444044454025400c1404086030340364080003003000407200303200c88103100c101034078142d850910461800381e1240b0400064400001d800f0396294400e61014018160b9603404102d90358480421000940001241e009420040c1080241c0d901000d0f881c2981120002c0c01d96150400b25010f1106427410315001704d040d403040c902c04d500b507611240181845004640e5400c2c1c4150f1500500801c0e918014021407041c914000040c86024042009241030300c00c425864048035160100403880c2c0000b11101401c5d590601050000c41c40c0c5c004420513410f9020206084020340303402940c0700501c815038200c2e0780702d0810705070f6000186907504180e03441405a44030b0011140020704c1e0031044898451200780d05d0f101c0c0600c0001d0312205d0702c1440506031088c07004020b40901a510b082e4004600300546102e2000400000c2c04803009402c0715010b0740d4000e08054404105182c03010300e0a8086c0d604070b070303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 395813453 1250 395812203 395812243
    0x1f02090f031903120f0f050609162f0313090f0209090a0e010212070806011709060721020408030d0b01020a08160201030906050903180109081e0c0a08 66
    0x40d403074000b4060184a4904046919103002680c050314901d4102d003180098507100c020641c03290000c0e1299504030a86800042000c0c03a100302044910040108a1005280d111082c1d80c08141d202a6460700380390120714820035503d20301034510400501c4020f0000510001808011500d40141c0d110100c4000c44000d0190302403070b022110590242440315a0071103060700004e2641e8003030790071072110b00d0710f0003000518002c5a0b00724003402e0303001202e0500104041030103020155a0040000411600d1160240c0c8141000042c0341c0e201c40d0b01038005005c101c1c010a01c880b022118a00381040840414421540c1d0b0740e656a2403034881d00070b00240d89a103854618407040c154004588148413a0303000c1400ea03c0d041c452100c2a5010b40000c3c07042e030401d40d40f05040400104a07110b5075019649100080d44c850301da240607541445003031200300d4100584048100190200000c1c6101044803103101005a181800440391500216812003980641848000610001d000c619107400c0507440801c85 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 395814703 1250 395813453 395813479
    0x21605030f03160c090507210207020f01030902010905090907080f030909040807080c03040924061e0309120c1e0c06080702101103091e030406111f0209 67
    0x1a12899121a004400d4004015100c000f80294801d8000c0d280320728200b80c1c0d01c81c0ca509000040b94001c139002408180d81c0c1d0000c07020780003101d5a11040040140c42036161900c50750101701d03582c1400d90301034140b40d101d50f90b41c800c6a000314040806090003404800980c03506411690f65074030948601c0310503000710513a0381c11400010007140c1200901038180c0c01e10780c5a0b96541005680200c1099031300040920000034020014002040209100c0340b01050031103140e0030190700ca682400d1031002c44144103e04006858002c001e0b01e0340103609080303103a11410040802e4000c0e018002c0c000b8451600c07030700d0942d00c403500701d0100104180251828400d403011905c0c040100c070b9140d4405070036484100d108001d00780c820710304298000200d20644110003281c09100d400c0d41c1c06811a075011600100400400b540c3c204441039242e0014075840c0c100e6581118a29200d1085001e00810803a01d2091800352040030070000c80c0a85176228a414211a0604508001e4114400d803a00c10151a2404c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 395815953 1250 395814703 395814709
    0xc05012c0307110d0507030b0c040f050f010f030f060e0c030a050f090a02130f180b060307031a04060209060a030f0c0504320d03090513050115080c0712021605 70
    0x41e8500c02d03400f1940f040344254070001c0251a4080c1d1034100e500c1e110b12079001c030001c1c42140d41180500302c10409140c0f82c80c10070005c1820300109400c0343e0f0058030040491440c1f41c1c0d0082c0000350b000381c1403d0019010154a04400180500350424a03d401c0c8100500041a40310401548140300042c0d042050b9150401014550745041c2c5042100340d00400e599009460401520200490580c100140082040d4030f03410554181d090f941003180c0c0c022024006021108048951003842100a0080642035686030710502d52005041103404541c03400140030044e2a40c102d4003004030042a01d80c0311200810010017904442c6404001d003400c00c10381c80c3e13585001310181d9080d0354400b03040d81d40c2d15002d0740e801a600c5001d8042500000552040c445da0f41e100e1364441524140641d0b10140d14900b814144841004000080c4442c0b500e0000100407000034195110707910078451401d4001912100042d1446001d405400340c551007030305034a959403d4000a41142c1c201d00c42040020031540c440c10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 395817203 1250 395815953 395815957
    0x2240a051003020a21020a060509090108030436110c07090b010813020f090109091b060504150c020402030a05091b031b0a081b031614040c0c05012c03 66
    0x3508045001003d00844d0203050b861305040601d805c2e001d0501c3d1094000a41c8603000d9800040451000503040c03101d8101000003c1c098800500214681882c12076800e4002401c010f0031840e210b4182008000000407d0b0000c43d1020494405e100442d1302c080c5074100c0c1c0c1d0081402c2d02042c454040b00165600c0e040c00755a00b00308058494070b0607035442c2ea40040c070345509080126401100d08125008541e1848950342c040c117440c0d00300103076041c903501c1c00c0c603295006800c0c506400070914508220003980300003118146d83c22001c0010f810b154011042d101310281c4440203500c03600201c104029221181e000d20301c600914411500b280604456503138000507100843c64140e008480c0c42400070150401d01070520801a14031f88080e0780e03411845007041c0e404482aa61640d114425526624041050014100130101980c14103450b100501e41001e040914050040341c40b2003d07013888602500b42c400c07a56801170300a00030f19500c201c03c0306080a00129032008004030400010400c080001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 395818453 1250 395817203 395817209
    0x15120e060109020304021c11040608010905060105120f03072409110625060e2503060f020705100905060c180409050a1407030302070504050c160302240a0510 69
    0x6000a42d08280700507020b0b60000300f0998102c103030000d9a01902c0080c00c01081800e00812030300000c841c2520401c0141c40d001e078040c261680c18500755001045010443d141106c200300c848000d9582c8100c0284d00308201c5000c401580c0c0000304580701030082c0c143c440c20100241e10f4082c400b0700c0110a05200301d400040c7e01511106d60106280341509000000b003420540441e82c500c1c1d0038100c0c070016000c604801c0011641c0a440d51031140c0780c0002001500c00d8071003400c0e1540c082c10500b5442c00740b200d01c944409098680c44801441080c0d2083d41112040307608282903c0c901e103448050540906140001268a031150800140301e204d010000d80e0b00e0f59a0714150307100d41c510740c4010130001c0c000d200000d031001e00440c00085c000a01c25041920800f0848001e0485107245003006814403000d54800da00a40c10300c0300b086442c844100881d6a40406517201c1c81081c038140c2070403440e1524580351905450003000c50486100580408248240012807080c0100d986181301180c40d0742241c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 395819703 1250 395818453 395818481
    0xa15030510110c1b0a05031009060b04020901082a160507080f0a1403280806010e0108010302040915050723041d070c08030a02040302041d0c12161512 66
    0x1138404240381c0400040d0070095004010b0700510b0b4546c0000303030403c40040c1c80c95511640d1a032410080004034014228000402c51f002c43c206002000081c002008c0213000b84403107d1901c2000c0c1c0d0600c030342d48a480d81a44038500700c94503500f00f088254491100b503907098a1500c1071660000d18148001202014004e2981c060718801c1031907680c481031210800d900c060705001c24016a40d04460b800582803210346c01c4035043c015031117400400783c09400054000f90401005030010034407039820070b180504580d4150f400290221050400705c454070949440003850504000c103004510740e1003080300054080c1d442007544100410224000d0f14800c9125000b107203044410030081954156032041d911045900303001200080584d690340655200f214041910395005c141071081d400c19100758030200356001403080301c075141e50103025941e030ba080000c40e05c9020342025400c6401c00a000c8007142c41c06101c0c0d403100c0a6141c81d401707a81e8400c9150f1103c001221442021140088c500881203042d80701 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 395820953 1250 395819703 395819713
    0xf0e070501051308010e01090201170105150d021204140d021501031b0305030c061e100e190504060506090c03070906080705160506011e030203030906030a15030510110c 74
    0x440d00650741c5030007480042c640f1010306400003900510a0141d0010440d0301c0c1c0000400d03c1303080c4005008020460500002914241c0042c4400d85500f204c0d060890b10800e0003903210000c1450400c040e10903000100255079501080c00204518020502d190b16041400e0340d00c06d82c40058100e9542200c145601440c032001c00c01080400d6000211013007200d0304404031002d441d165180c042c61075224800310035443d4090380070040c0450f0900c4450b95000d02035104140c0c1420801c0b00f4100c201c1c101d008111040700c49a002c9410550414002c00300c1d415000d8041c01a45800e05002008200850700d450080700a0400150151120301c01c9a10940c0d040d03d0f040d203590f0904401f1a4560030080115040c40410401c0220b000c1c400804100568881c038000c00304d96040610607100c6506d075031805804d000d04900c060005960100603101886002c0d03d6094903503540e48185000341c0000e44e050440740001241c0030062000100310202e1800180301b041c0705040c0c0304601c508491164110061441d006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 395822203 1250 395820953 395820959
    0x7020303030a09140f0d020c01030c020322170f0c0d0804030f08040902070b16110a0b100504020a0207080d050307080f1308030114190b0919120303020a030f0e07 71
    0x4581c0024400c90054085503442d5050032100e520f40f502c00c41c0305c4681580504c0c0390744126507042000e520b030b26200703103010b12400ea03031400041d543e030050358414084802c2c003a005003070981000d403e100060141040e082c1c0706a0243c0c2040c0d86428540c250341d4030b24000d0015090550900e4064841000e41c0300040c00e140c02c0ca03544614015180d078030400c0f544034404200c0003d0040e0340d80090b0044900070000c00800d401c181106c0103000b1880365580d0b00380101202280c1040348042405030b1400c0d00240c5815041d52084914611900c080d00304a070f00a101046203030180f90b0008501c010340d6030b42c0045900c20401e0090540b080c2c0022034000707001070400000a03050a82001003503410038020a200703020510b442e80c660b18240c000b40c00441616028282d40c000381e1078070700c0c00464180641c2586105070f60070050400c50f68031841c0c10b914000d0404041e884006450704030348034024031440c0c0b8120001450b0340346c0140a54480f080ca40006400c10001d0043d01689100759095590b5200c01031401510b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 395823453 1250 395822203 395822221
    0x3060607120908010504030f0e22110c03040303020304060f080115050a03020d240909080a0c02060c0a0b0402090c18040b060d11071a130f061e060305060a020702030303 74
    0x5600d2041c1c003003040400002482840901581307000d076100c2d440703a000b1814004001801191021100f80c458a225944183c81070028a04a4080808201d000c02d50300c403051812526441050044182da00c000a000014164040f01a00c1614121780d503d10040481c014111081c040038020040741c40240c07121240c04901543c024149000c4ca824098140306c0340d40d00c0d2804031604540700c1d0b0680c2800b040d507024070b40c0b6003011405c00381a000b20700304201022511340c1141c0f4005c141c403400500c5107a50990043d03503a00c005650503d1200011140200c5440c40c11807540041900c00b2070003a611240850380c0c0c03004480a645201d008186250096020042044081c0904450031504405d04118080360441d150040e200c608d40d039003400e182d44408a141c01640002c0580500c1e42da0801c0c4024044070f40d0020190011080c1c00c4071101240d0b40c12070528500811a51400c4040012150024010f14040d900982e0850340900d0a640c1940d07985030100e82640300e4110020b616820410010380014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 395824703 1250 395823453 395823473
    0x9090b13110d0f061d0c01170f0408070f061406010905100311090402070b010e07020a0218070302212e05061605060c030406150e070302030403140f04050a0b03060607 73
    0x14040c0c540603607203103155202e01341260f0268080704da0b0740d0041524140c02000410682003044020701e0101180811496103406803440078001120030f08081002c1400c0c0951413056680303150700300146000f106294984a0018070b407504030b52a00000a8001030903030741c014074034a0700702c8070007611301c60b04030001a00460041400651842d20f011041c0403100481d110fa20262500030300c6140f80042c01d50502001907021240203000703404540c005601b040058a5004503d003404881c0f172000d102a8803102c07030580c082e0003815a500141065418030480c0c0c518460b0040380100040542a1007427141d17185203042800040e20102030110100c01d04101905003c001403603400e2500700b952180c600c503640c40078107002081d110318100b84400300600c070a1203918490351420600c03000718580010728107164a140040b0052032481450b41c040f00190034540503554a001208400103c1503485d907180c00c03000b40c2030b000b9000b154083e0404960100302d2102202c1241c0c0110802008541807010300e940740c0080d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 395825953 1250 395824703 395824729
    0x1204090509011d01140606030c250204090317070915120b1002150a020a12050405030706090b240616050f1f0b0f10031d03030109090b1311 61
    0x1507607142548400103003c1245205808040340000c142d20345000684a400100580b0b02c5200308010000d00540c034003410202e0b098a2840f21001610015002c031940d071801e00e4500181d0010300340301c0c45004041c0c2c0a8cc0d440e403041001100754026458070702d400c0307588514070700500e2120f400c210b8503599841c0c0960501c40c0c1c4074a0b89131300031542104540101d10384098030814140580c0c00000c1040d0781c280b00c1856a903010300d00b0f00c5d085082015000c4000c00c100420b01c00d25070503d40d42c00105003070003400d10481d07035080e400500074441c034219171a10021810044a1001c40501c446d02c41516090509407004070314000105054105203218170040e1104040700c400302c030740340f0400d0480480c03801d00f4403280003c0442410702c0000d490440322910295440300c404684101a044c0c000500c6561300c545111901d00b003840c0004040200c000c0e40742c1c0241c104140e02400c0d1002000009410015420060035140310390785217035454444101000343c003550440000c081c03c1e5620908000c1c3c0c14420100c03091 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 395827203 1250 395825953 395825971
    0x606110a1b12060605042412020a03082a010902030622050f1b060306010516060b040e06090c04050402090a050a140a0f1b14070606051503010609050312040905 70
    0x75440e0707202c000b09410769840008440c0c8680707410301003100d86840c1c410b0b41040c402c0c03850750b280c11a150105281e00941680906240006982a2107095403a554180e201842d0303c84940c60307550025510303111140e6601051040c420440d072007084003000c0c0601034044030700d0f4040c00a0000707803100c21680030601080d0f08851081c481d03010380d10b03000c604200301c084070054005010b05908401502500d4403c18000c040c10700072441003081c4092641d00c82c00302c80c00d0080031110200300c10307410310b410383c09062804450b40c1e0140c10050000103941d00482c40e02d0281c0e40c48011502100300240c207100035140119000781d4840f0850001a1484c025034115036400401414002410315004c10501e856040c1511500002c80e518000002d00850030f110709031009042c000700c04920b02c01030100801000d110a58a403d100000c50b14104100e0700d40c10034006800d0060400c0c0007103052102c5271382950001d1181c6e200040c0a0b000002d0241070105d0160b02440164241d14502800c25614001804001d044004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 395828453 1250 395827203 395827253
    0x1050f09030102120906100b1b0c1e011101050108070b031801050412080f10050d020a03080706020712030606020c0f0d120f02071a0703080606070c180606110a 70
    0x10550703000c0c0700415103a902018508560b0401c2120f4074548600100b201c4001c051442e414041001034006941c0726905e04c2181400c00500380025908060150301090740040f1b00d80b41012501440c843d604013500300aa84480f00c00d02d6201c141807c0e95020b20400150350441c0809001c021804070041d503021094403030185121107180350003800c680040350103441011804001500e499404090903030804001d4456843d1800c000c0404041600f03144117113440741d440c0e042c14108540b0b94050100c002d41c2c110700b0b141c2d2501c44605141020354068801152850101b82d140e518150191080038180d8405c1d600a00351820080c2c14044900e14403440741341d220341c003020300c0d10019071950001010311802e070795802c1c641c618200010785001c44a800c9035185808800c8900414050714023034800035501494072000a8542030003180e02489640c40180214079900310100d2002c074400b0031168115183c90003003000c80d682d58012107016141a1100031036800501b03c00012070050440e91030007904c1c01d101d000e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 395829703 1250 395828453 395828467
    0x1401210813060806040c020c01080a060e09010f060b030f1b0c030319060501020f06040f08040b0c01091104021204020d052a1905012106050409050307022107030201050f 74
    0x30249402041101245180403802804020f07440f100042c1c10003016035040c4803007680010040d4855881120060410100c0701c001038140c111750b0090030003031900720050041c604105944501038144a2419400c0034101031000600040070030449219108058107800f06840d454108181d60400624503071100710103001120200c0340510003140600b6040740c0c06010260808214010744240794406810344d00000d5945d088100c000c80d4091344664082d0729803641c2206031800aa007809a074004058582003c24448034500c0158400c51703070203004081c1c071610303842e8080401069209203020310702c0c0b201501c0d02290050500203203845855108406540c0b807124140340f808528200c404601d40c2030380c82c0301d50b2501282002c490700c0090840641d0003001c1c40d410000007070511052480581d20310300b02c808480c0f4507098941c2c0024040c207401042800f1254490504a0384c0f81c01c002d6043c5d02c100c2a80b84110145918812440e0000080d10081c000e030528540040d103554222000c50000d03004108448 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 395830953 1250 395829703 395829713
    0xf0f01050d020d06150f0219020109030b13110906060409020306030f150702061005010f0c020a08060a0b04051302280f030803090f01050103030e1201060f0f1a4311040b010201140121 80
    0x501d01c26000202410000e421904285e9602c3f80e5410865021740da0700c03010b0200c00e49402048a054a0b4180700142c0d403600d071040400d141c8808490307000164007400d02d03e4119901510a09401890710768200d40386500c840c040000700300304e50311420b40450b240b0980c003446140034045c6083d40c03900041c00404016a204d032480e0074210122226001c10b40e442e008100d0a1030988038464025480c907811284004099003ca0b1000c10210105c103003045007000521031a04a603034500d00500700940003020756507503a03c3c00310081c0d0400c2d90b81e554240a2150044000c95051141a040303d405079181300480403004140003007055446004070031035480c0c03c8042804000e900000c0002c014818000110701c1c6004c3d110110116052144007190344100580f280915611980c00c800b580307100c1c20700c012892508018040c00700000e24100030825980902e4050144924000d540401e0170340f410711004407407100480c2203400041803400d000f60b800b00107001c003065001d0310318102c96034140710800e50b000719214 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 395832203 1250 395830953 395830973
    0x2031005012d030f0e070302030d1b0f0501140121020603070207090905163c05030609070503190203070308030c071b03020f06090f0f01050d020d06150f021902010903 73
    0xb0074800300e0f071541d0603582e01e2401c03407245001c02c0601d040544413003400d50f03001036111405180c0304410086c041e015002c00450072403101e0110360b0b1001d00d0594440c1e5520341a8040e0220f0401c51550042000000500715644600c40c200803040491445181c03805508101c0c00303400c0505003004511503d240400d41c084d49215081010b8020001451829040f10461806002c907030004401071124040b801c551040c0c0442d030000b519241c403900c4000240f4a40d52860f49080d42d0300407641485200300340010540302040134401d48506509503804803c2c0c2c903580b41a8043c840c1802905640030750404c0003c03a40700000b440e00441d65171600c502c0c00b4402e0b225440c2c500c546814076100349403110780c10402c52908540044a0090650362103007442103e1300000c125102c244a02802003807001e600362a268480e030220303407610344154011134031501c400c01d00800402d101d000d00d011101041c5801d4480d280285a210301c08005a40100b00194046603004a8440c3e400c038228140030300d812011000030003482d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 395833453 1250 395832203 395832287
    0x30a081915030605010f05010801030f050309042f090d150b0603040302030301060201060503060112110f130212090f0a12170a1b03090507061d040203100e0702010203100501 76
    0x19078001840c01c0d820035400b2100c040e032002201c1003140408101503600306003c14110f0b900315000c8426008a828118114800d40d10000d90103890300402c00020100c65028800400c54075207080c018031156501c9042c1031242c0510700341d004014540703040000307d0300c0c4100c0d0311041c0810000b050510400700407031900d8000f80c40490250f000800144035107070307091080030000e1200f14020007295240408a020310750503c040a0300030408520444015110180c4031030910401410701d0b0781440c61101d0a600940090b216410164a601c0200d80780f00350004100d40e888001001030440c18085641d003147c1104150603440c00d02040902c40c802c18400500285e03c03502900c40042400040b070080c100c0000302d00d20804050600d801c0b04800801e000242c004142c0d090340c00c094a84034919030f55017800030381c054181540180000100061034004101705011078100d1001c179903090302c13144000e82c02c0c1d000850b8903a159080c035040810070386d07214025500c410ac0b10f002e02c980b0754030103002d01d10390840c1980c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 395834703 1250 395833453 395833481
    0x130306020c0609070b0d0e01020c060c180f091f08030a052a071e030501110909071d0402070627051006030b0a110417070e0c040503030a0819 62
    0x880c0800e160401031020982c04072403c405407194906055019900b03000e1381c80340c034200955603012032000d20000d40c1250300341c00b401c0301120410700c0c05000008440d88441c0e1000b0702c104100c0c1c80c1c0d40311401c0110141c0a030500041408000d55564414101046070b59624042201c104070000a201e880900c000e0502180075074840c0d9072840c00110f0268102400881020205401101c52091110205d00d0000756417088003841c0c40d44800c860303041018107450304058103d5190030000c0c0100080100244201581520301c42c00694420106a6001c04500d29a103001c1d40780450940840c50243e0003400e0b41841482d0024a5000041010a0544901c0e0032040d0300c103450890a0305100c010040441004d0000358184241800c4d60707240001c800015000d480f0b080d803038190300703405103102c031702a1809804241e401000d107803aa5880c2d0382c1c0d2a1194440d14418041c03900100385181c03944800c031015600b020b80203614001150300d0855003042c0050090340040c001d50201c201044007801550041d140030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 395835953 1250 395834703 395834707
    0x103110d0203370c02251505090109030305030403020a1403071106090f1207091b0905180609040c030c080d030e030c0604030c050715030c181a0f13030602 68
    0x8142030321810480321002c400f2888030403403400100d501e950036404804080300d022841220343c0d4400e81c074114043c1d180c110b40f100705469000c002c01c1c1e4101c1c0c80084845000803034101c00c0b142102a0b42601c91401d00d6400140c12032000e2000c0b9024030000c40d080f0f4424411640000d2558445a641c044c400005000903000050780d24180050b00d000b2504045045416605c0e0011800c001090003110384e42c010b000d45040b88402c0c2107020140101802880c11802c2484404907420440c500807400a4100700410080c020204482c10b2254801d0400600c0100092092301e64000b000008070004000311118201e80c600400007418102c246002440c3c04002000d130b000b0f031140d000d002d4502c503001203445948240454941e204001903403e03000f40d014140342e860090f1909102d030800d0104d030000703031040381050100300c10140d060b84000c411140c5075403101044100c6024442091443e881a85924240f82031001c8814401000900e48517612202c441c0c5010b03d003c00400916256504c140e8000b640 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 395837203 1250 395835953 395835961
    0xb13052104060e01020d08131a041a15030d030e0f0d030c02070e06060a030b0303190e010906050c06181519050907062a140708010c0f0c060b0103110d0203 68
    0x1c40c0c3c1a03041090020300303d80d40e040d0038024074030701000b01500902800d40c00000700784805403007500188c00070032000c10741c80c0c9020b080641200c00300d0f0000c07641d1000c280e80003c41c0c0c260801011103030a40c004014001801d0802811009001c1c824030300426806540800e201005d0308110b21030f002080360b18042961010742801908086142d4803c80b80c503200441000750564902c4200c0d5140c44960500041d50000400481d1641c003c855030100c1564048005141c0c05405c010004083c039000d03a40c9042154650a00b26164000e4140140841d4404004100b0390700c440e8411070403440d6a00103c40180e00c8002d00e49000510558103070303400800d940d0071800309508a00075140e004000000078002f651818500400d03d0140e0145400c4c200d440e03600d002c820b55800320070700c001c481e0846080003003c400050401d882d4041071040560561070441c1101c0c61601890051512a960b520766154011081d16141c0280940582043c10166505c200d20001d00820b4060415100c00280050b160b2034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 395838453 1250 395837203 395837207
    0x60b0603160905010318021504030b0906060a060309020f040504030203090d060b040606030b010f0804081309020a120b0d0209060d0602041203020c0607020f060912060109020a021006030b1305210406 87
    0xb406801c41c074101400e182c0c2804520100c09100400c0950554a907104142c030b04000718298099600001e0141c0030070418040b03420f8000031280e0245078120381072a074441d60398005a080306d003d0700c8000e4104d1240392002070b06103040d5204c1c03680140240141c0b898481d0020008032000f08460048a581e81e80e03020100841c10144901e0000e4140d41c00e041002034050000a00703917100c289144410044039000107402c0100b1003059515a4503040c04d1000d000303407140c034208040c2d0071480202000a400d010341c4e0300c0c405020b01448207045000307804110311a005400b440400000241103a0b040202c44180a0000da0681700900081c002c80c519040083c0d8103241c002d003002c032143c00840c800c5500b80210300150759102c10148141e1000c0fa1440d64030340030341f004110101003c0c510a00207004643c0001059aa07075001071010785210341c203540098244807502d40480b4803a02019004804003400210788001c200c3c2c120700240c0c05030b0115061515a5140c041e01c84446200d204d9040c0d00201d41000655 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 395839703 1250 395838453 395838467
    0xe0a0b07020a05070e1b03090a080f070308060108040804050f032407140307020601050d150c03050709120c090c0207030c06090509070f02060c0f0412060b030c031c0309060b060316 79
    0x405c1c4081c00030141809a648078003135070b000301040302c512800404554044801c206400419030710000c15500d81000c082c801446400903481500880c2c00c06002507a07540c400c1110501c03490344a01103a00346400d00c0f09201500081c00b00c00e5030140324046246030412106401c4018140c605030700040c00b49040400100303581000001e4885000c9c0074401d018000f5000304030317141540d409841c0c0ba80c40c56180d08041c1844403000100b0440c10340341c121a80c0404e6495001184070712966100c403014651307118411880d000801703102900c0e500103100180421000d42d00004070800c030600c101c1c2c0d607840d00d80d00c2d4448151100e50083c1301251032540100311604001846540c17120700b40c1882505c0c1a10980f0181d100e56005041105091000031410386900820341558082c0c0b083e5100000795010b50302c1c054000b8254015510301c0780c4180080c05005146c0019800e542d101c22450101a01b000c032031054000c1d0090a104032100d40d103401c0120825120300003d14490b004800d0706280b81000050050080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 395840953 1250 395839703 395839709
    0x304030906051908070504090213060906020a02030a06090201210f0f0c0f0c02190e01081e0703060b180f0f09060114010c110312280903060e0a0b07020a0507 69
    0x10207003d0124201410780b00a1803481c603141c41c2045a00303650340b46811501445150450051b040c03000c10040160f00003107444a0039a003040c0c8618800d40c4d1510000d996a03d10004000d50582c062060040007461540210412600c181005070020308070002c03d000c0b04031050700c1c081d02280c1d01e051005546030300d8003914400500d02c400402c50340021440091442d180c803142441809082d00d034542c115103902c5c200c0c88000c5400c00d8283c4246450310300b01240a4804c0c42500140d102d0120041920101d0309000000f0f1110840240041d51451f030340c2401401d06012040c2e03004c1c041c803200030707664100c44c41c111780301d0004911403a202d40341910107603241072409050700340300340e02500060040d201c0c43c1c401410504400d003401c607010303800d91501310004515801201d415004451210800b01d82c842c001c0c28103402d0309038108403500c110701c40c0422800c0c440d41ca060005033300306c0401c1004c120075600254050111000707a03401450f480d25415a049030954900c0c0050b482414180c0600a09209110107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 395842203 1250 395840953 395840957
    0xd0503030a140c1b0c06041211060a0e09071206030812151e04150803041d0702060403112a1e0d02012604031701050102062802070b0103080304030906 66
    0x40d80c2048190702c401d0f8054490000213841c880140000c200078100a003500b241801000c02e0f0384d641d21003800d00009260100d0407292021100403000d200c0c41c043c402c3d58143e9240d80d8032040104c0f100006c0024044000e4480c138140840c541903044544064080d02c00558080c40c02c0694480e0041d0b400c0d0142038004206100c140d4140140c050036a41e410400b09810700c40700b072004422596040068028010542410707940c4184c42c1c40059242000f00c042c004031007400e00c2e038084058001e40041c20420048a0700401a0405400030380020701406140c20000d071031104542c2c142c00000d844038251483c8019202d203810001036500080d20b07107440c480b0440e902e05c87c0030314506154600400c0d019505220020b05000c0034000c1c41c0c030022408110700710104e99000600c1d40905290034083d00c842c5662012007503110b100070000c509940005032950055070b644010040081d1b0585c01c0076400e0441c00340c031450040d020803481021500240516028600450125540e0704152070082c1281d8403940c00841 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 395843453 1250 395842203 395842241
    0xc1207030e1005071b0b0a0b010f0801050603180d0e030c030309180a1814160501080a050903130303030b041401050901030f05070512160e1605090f0d0503030a 70
    0x20320140003103401421a000b054010480f40c60703421054079030b00c640e40c44401e140c2103150040000e0000c040c14a5004405200382003110340e072002d0044078141b030200b07000d8000c0340e01c0c40010803c6082000c01954004903030414008030b869800d10640c201085194140300040400c203170300303d00b46401e002c50303101c140c8114011b510340303e8420701113108800b844144241c46401d4100040700c0e458a80c000101500270b61803240300c0e8031010b103084c0742521080b00c540e01191150103030a0608803c21813100c401d4401c1611141483e6540c043c40e03202802c1c2c02403180340c0e580402d0120303035848001d890070940694402d89020914411200501080341c0001200c0440d04a034540100110f41790242c0150640e60032513603061120003182882407800c05944e02032034010507003000f20011000702052020700d10048500f0900e03819070350b005990b4003420660b954042c4a40f05841320b10303824055070081c0110040a022a845101d071b11002452040c20804241d613a07800001c20401070800070720642e100c01c00400c03800e403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 395844703 1250 395843453 395843471
    0xd110c0607090806071b0602120907031401020a0905091515070605090c2b150b0f030715030903020f030409141315050402040b0d080901020c010e03030d090f05060c120703 75
    0x1000c03000da004101b040700c00c840c1c84c0b220902ca10b98040300d003002000c2c15800c4a608048040c00d586000d40d03c0191011600d01c01c585c005000c1c10b0003180c45240e5a960740c015924144030411600d098064000150000c41c000708040b680c036030141042c001c1c2081c001081c0c45822905041c815240d00a00b404215080b21075440e9641e95141903c041c4400d4000a00303101201034401c031403200da54020040d0030504800c07210706403644c0381d401c10002400180c0d080c207581118042410790b611554002c0c00340c5c02c890802c7c8000201e110340c1c80b00c00e10a000344111110b400024061904540c820741000c4059074030381c051000085903010301550080000700b068520141b1940301c0e6000c00301c0e010a0880016260070200303095684940104800210080680e40700e0840c5140c0b0920b55801085114098000d044031285290f0003504140710800c1c01070091840d021020b0b009000070a40ba4900b29007540c2409111008200c0400c1068172840f207440c44d00d9565105a4442441d003c4000c2c0b506041505102d200c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 395845953 1250 395844703 395844707
    0x30109050616110f03071202030703081506091f0e1c0b18190318050a0504050a020c033408120a0b060a0503060a060302030f0c0d110c060709080607 65
    0xc958003000562045031400c80d4400b040365542c1103010303190b8040c860126070b0641414040014940d1501c0f60a10080d400c507400002d90b1603010b41c08018000c070b004c4600080c0301c5007030700703022001d9a803004040b689068a224002005540520030300010b4075008030580daa03a1350008000110000119101040d00c0700c2d51025103032200c4070a9001300000301200200f2400c40c0903000b10a50008450162019010951044408d940c0b04050590005007a031340d5001040c40200e031130f40141e0303601500fa1114641001c0611000c0c05000d05a15240ca0f070801038050031210a00c040c16030003212903680e500000105800300312036401c200e0070f14981100d00c903111001400070006c40e000c89204c0702011126503501c3c150701004200d540d0440d03030400c0b00090085c080f154040d00175481004202c5100c4031003501d0b02012401c0b800100c41c00c010070451300340402c0c2102000700241c0032014047c0c2d030200300f032240800d00440c81e41000e1100b100b140d009105101000350400501c00180c103160000b0044c500d000f40700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 395847203 1250 395845953 395845963
    0xe0c090906040b0a0c020102040314030c06070f09060c0f080301030c0906080312041214131a030c0f0d0f060b180906030d0e0d020d0c0f0b130b03130f06051503010905 73
    0x20136562150b0350112003803c035001390160b8000b5900500040101d91403108020307120390102c80e401013540210000142000d004000401b0140301680e60f4689242c00c0000580b6505580c03981079642009159250000803038420045002c3d500c52881001880d19002001c0281c0385140c009040b030b5001400b41580c1d50b0b0124505581c040c1d00506031240c022070020040d80e03800c500000000710380100042c030b41001c40c02c2241c00401c40d004408a480b0741440101800301074001541c4a20003480100700030258010b000001d4904100000c41c0003c581c40c408143e6812681c080e84141d4880f00040b40407400ca0100910301e03007841c03005448400161074100002500c0c0d801040c440c5042c8000301c0218001500d40c4140005143d5001d04507005540442c10172803c0c541140c46113010004a004c408250010080705490300350020341300f410105810b002205142d80c10003090300c103400044d02c440e6004111031120158200f0b000e018005410b0070801c03e07543c0d5040d00c1e240518020383c108603404c0009180010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 395848453 1250 395847203 395847211
    0x1020a05030705030a1d03032403072601020a1d040218043201030506010614030730050709050a0e0103061d10050f0f0c03060d0302010f0e0c090906040b 67
    0x5800c44d40e99449500410007041c0f00140d03094085880300203680060303000070045004412010f290320304009140b4040504107600c400983d01074000710000c0020304440f2a01c1001d541c02c01041000464600b0b021500b246c01c9201c8402c00508540d20103402000700b1100559001001d42c0d040d440c3c000200101008076204c621568011560b48041c003440f1641012500d61a55105411a00b02e980d40324000d4102d00c028002a140c074081c3c8000061128050810680050100b00880e03082d9590b890043c3c444c84000702e017080c00c2c0a003100d01c0c1240c80f89280450141e80d070200718001510300300b10703d0003880140707507030011030059803086411300010302403e078001d044036407120300416010003e4140351010749000200c00068452842418290403468110030321924181c0c0d00c08040340c6d11003485c440003030000d90300b0034501d400c20004140700b03042c4003030f00f5a107041c001c0c00085140c0b00e91040d07510881c0c010009800403030700712800400882c40c0c11a182d542004250300217018504090f181d505179088060 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 395849703 1250 395848453 395848457
    0xd1202030c090d020604080d05040f06020106060206040605250c030e04151a0f0720100509040518031305030c0a03080f160503030a0f2f0f0d0501090b01020f01020a050307 75
    0x154480f41150340702c0c821a00940b03031420507500200760352a03000c0c00c20b810a0084030004000403802188440c814800e50045405070b50003068640c0b25621644000c21010b421800e20303062943d52803c0500d100d41c0702d0a50b0b000c09513100390b00d41030a030800810001001c400e81c0d11a0f800e0503a0790030545011090038054980c200320980749604000c49420302d40c80b400c20103a0254402203000b01c00e0181c40c0b00425180c0b2548a44001a2003881b420071001990786c3e40c1d480c001c154244420035841c10554032499001c01c885400160342000c0b82c1c00503103903820048000c1100c400c0c058007408642402c0c07007400c500340019100380740d0050960b40c032004c0c81d01410001300414000442ca500351600d80d005031486858008041ea607582c100002424051310491800c07600784c60510440c50f0210380130001c2c208844482d0194045039404400101000d40e01a020201c0c0005041c041e680306205103100707075402030040302000142140c0300000642402c401003c00c05d41644148403032503c0f5038016080700d134040c90b64 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 395850953 1250 395849703 395849719
    0x4080f360102161707050d0609050f03120a02070f020d0606050301060b0909010b0f13032006030f01050402031816030b071805130f050901090b01050607170705030c0a050d1202030c09 80
    0xd01d0119213012650350100344e00c00350700c941007c188070140c5e001d03154840c01035054a000c0d4100d0104144c0e24070030034a044044004610010f59018002c2c1e01801103d07100d44101a0103a01640001d020241e9a800540c1c106940d1141080186401d20906001706421100d0f6410f0001007000110840c9052003840c0142500150580d00c0c0c4800c40c0482e000d400c1c07100702006089841c3e003804c40d646000900c41e280e0040d070305186620a480c251040d248201c0c3c80c0c24000c0b200e0707070034041440b005e0b40001c0c01c610140c0c907504441468010003401380003402c0c0d0360707606d00c4205c251039400d0102e80b051024244206001d060b900c00c0c01c5d50512504000c09031034060321000341c90707403070013020030002c001040503c2611458942802030400c41034110a500c0ca01410381d2940598907a1b0422400f485038080003004140a000e00f1100c47d01032001600685000f5802d81c0d0402d400d10f90042d04102d09030320101c030150030000406d00020780100c00000040c070300c07407001c506500c3c0040301c05035584500100c1c58455460 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 395852203 1250 395850953 395850989
    0x40c030b120105010e0a180f0203100e150c030f0103060c050f070501020c0d0306050f01030f0921030f0218090406110c0307020a08010507020604080f36010216 70
    0xc0d04141550300010742409072195008444500800302800b0b81ea0991a01d03002190168906024540e800380c1140703d05a00c0c60603070b6071015141c05a90b44101d07014020147d6821140900f40310f100500310f9082c018010204010400340d61031100107024029061050080c011a5845405180d06503135001c64002445450503109a41ca400343c8000c0035100349000503460304008041d0003408021030101c0448100c048007040c01c3d400c3e160140500e40d00104000400e2002d584a07802150350000c140d500003a1410003070b200c000000110210240700100408202404260b0600c91004011600c0008509241c00440d104c8403003075030402220301c5a0b4a81c00424140f0096500010641003540034159980d550110a183c8a070440e00007030703103d6110480009a1084103024061050b05282e01074009691160b070f82c1009034200b142c4070030540c9818405405840420a01c140b000b0b07104454481000100041c0240340001070151742c4d0454102c00e203140d054645000c25101a074020084400310018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 395853453 1250 395852203 395852207
    0x4032003070204020703110c0d12030b01180602010b090c0711010c1a090f0f030c030406110709050c091c0218070203130308030702061b03011404060e0f010e0123040c 73
    0xc1c0c08001e0741c06840020103004054226a900058003031000645200400c1442004402c039a51000900300400100c02e910649100303500a90b10002c05040014030501121411000c14500703400076400341c1e6640b4001403191034070071140c50780700d200d09441c903103040c0150780c60a1202c81181d4186041c08030b10b45c4910100182001d00003180103403c0c00801c3d1600d4800441a9585003040b426462405600f040000c5e02c0f1011041f2609150044000c41c03401d41f034117104030b0344444808102d8180340510000443e004100c0d00500e030003100ca0001c0306445960680070000103684420b000ea000b800c0364101100184c0b500d03018103184510641d80307200380344d40c0c103103041e41503109072000005445c02c1c80740c0100c01c00400170041c1d030040340700d54200c1c4e6140c1c2e0380c1408400404545411014088020300c0104440c50792140d0700c081c01c0708060404290703a41d0795150740c004800242c6120300b10240c00d200601240d5400d8482030300400e60806110510203c14040346d1710781c054644500d020785d0311000000d20540c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 395854703 1250 395853453 395853457
    0x92408060307230a0b0c0106060e060901020615060405151213050c1e060d0f1401080a0f051e0a050d0311093d0806040b010e01030e01060e01090c09050904032003 71
    0x1c04c82011745690341c1c4148103028001c0c0014001d850115500c00502129070926400f40c0d0394903c410703001403041780c8035100c80009001101200c07581c0030404000c045002d4035503014208090101c034480c151290441d02c9504651140100a5800c01b41d21082e10408240f0000710349100072410b8030030344e510b91410018500803c00c0007505941003100080c401c40c44002e2917202c400d428503c44c0301041004804200507412400a100d03400301540804890404034540c601c07030354445446441200c80b6004000100000340f0714002038180541c105c000c41209115090003113500f031050030b00d0204100621046511082c3c0110308100e40103c02220440e100d003000300a06000318410030703261164000c2d03030500300c580260807100c51100192420002ca141030405000f4204036407c161101004281904011801020218980da03520b64031040001044c01052041ca4082e00d2188004100e844020202130060a8283e00c298019841c000410000c01d07488281c40d01d01d1000c82150065800070408035a1540c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 395855953 1250 395854703 395854709
    0xd0b0103090210090e010f0e0f130c03030e0102150c0f1e030901091505060d020f2706030d0203091c05100c0503010918031e092408060307230a 63
    0x100050300c06a041541007442c40c4205c50108107081460b0b0380b111003185820200744501c0100c443c20401264145805200a661020300c8854800d10702005441d0141c840016034000e40220389090244151964144240803914950448001d90350501c10b0000e802c600c95020000303440003001c00c1e40044142007410340c5c100041c950400d10b41303d00784100c80038001c02400030115003d204005081040d8141801010b1040700001c000380c00c00c24054003407224100d81d010f02c4550003482400c40c407110300c0500050145540600030070b0342091501c502454070f0501240c113013109640c130a00441c40030380e40d40e445c0c0741550301505045808031141480d2aa00e001500c00c48003491500341000410a150b100000d1030484180e040b043c441a9001c04403860800603602e800b5000909880f100070943ca0102101002c81d00f40c0e14010244541d14941d00c0e138203880380d0b100541f0146061101e0a000ea0740b04900c2030b0070001c114040c08141c1c1c90424007960340205d0100ea001303c4039102d4040070b059680c2c50202001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 395857203 1250 395855953 395855959
    0x1a09030c070e06150d061e0e06040f09050f0a05010f061211031c0c061811012a050c040c090b041205010f050702010219050901090b03060a0815091c050d0b01030902 72
    0x60707483c003aa1507001ba040900500011001c2c00008500f580c4500d90700200b107842801810040351107160038000603160100b81c2c1403400d80c50b88190800140d0400c140322441000b203000d42001c00720743c03905a00b9102e40041c800c500c2d07802c040041c0480b07414074040314119070340110900b0190034864042418a0202e00003142d100c50202008000c01e078010b81c030381d40e107180301310020001c0d00103001d4042c03440c0301d030070002034000c500900103241c095018040c940c00e0915038041030b507601002e40359034102c00404810101c0322070304075421080e400d00382030081901d40040e9081c000002d90400e030a051450042c1c7c4610b4414009030601070741807040a40c49000403038070140c4240f280d0300c2d0280c0c3c080c1c00b175840004030030071108000c02400441403281e001e8446071071050b5a80c25085103010700c03034452604003900300303540b003000c041c8009403103c01000001680e01c6103076401d072064640b04803c00d060160781e0703e01c990941840300d0284d058a82c030404894014000b0400050818100401200249251100290 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 395858453 1250 395857203 395857207
    0x5010f0e0a0309050904030504150e060a03090b091203071d0316150e0a0b0a050c010911090901060b030a0c02010905070905150f0a301a09030c070e0615 67
    0x85103100200341c240070039000ea22a00c43c16940c540c10b0022840c0c04950140000e036007404103014804044c0c40d000303400b0340d4503e0a84000346c2824000340c090f920804010700842d5440320303000c04010034001043d5001200b0030240410030001100c480107032000508140c10043c1c20649404029144004528543d10140c00c07918461400e400c086031301c0e0a9406418a40d404018462601034440c40c209103d20f1b40251403010b5144c0b9015007090241c003c00d0b20042032141c240264a44203000744503240241d8065416040f054801c00c0620078041006009042240d0404c81c00348072004044080340c0d04643d0845000501d840d0580041740100008900200940510000041c03c440076030000d40c0240d6000d68025001c0726110100a051440d280d2001c1e0000100c2074104405c00d40010f007000583c09482d2120465025106408203101c441c0c0c008845501110740b83c140c103e2032004203107a028005e80c1c0218641918202c00c0307030b510030030343c070440c094510301030001034650301c1d0020403003054290748c06019 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 395859703 1250 395858453 395858471
    0xc06221a18120d08071106090601030c060f02031206120312061903030e1002010b030a140d050a171b120612061009150f060e0915031905010f 62
    0x10a05034090110000000201000c58034685000000a01100c03040001410f40d0100e0385000c0d1074102d4000c0c144010f100350f4a4001031144014810240300702c1000000d00110b6042d440c2441c04006c054201d50304000440e04c04800440e000011900603420450b070000d802e88d60500011030076a0300c3c50701200240030201d0703c02941003003120710394015003013120025880d0208510005000003d484090001741e032001040350a82407011459540d10b0051002080302d0150601080c030f003800400044652111003114205102024425150724201c2c0c1d00d000c42c03401c100c03514002c10f004902e0391100918560840850119152152402d072410390750018552201640c40e076166070071a00310355044c01031503030440003903200f07034003141c114031130b141600c0c0e0b0f240b409041a0024004040080c0010054180482e002c50070350100403a080080c0321940e03440741130040c00e1041c04420540980680360042841e80d807001c0d1564041455034564526400342c2008064a040050240020354401e01903645030070f40300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 395860953 1250 395859703 395859749
    0x5101a1e070b0114060706050c040f0f03030305090615010509033d0216150e0703060204031a0103030e040e190c030221030904090809040507031a030c0622 68
    0x540754a600a10340ca4060740c0c1c4c0c03862180e800c0200051a540d1000080106600150380c66000304e4100c50301d013510900702a114003208158110fa41c0241c0207a40c900c44042007090f41c10300400d5408000400600710700e003010454610340750180100c0c2c6051140215110007152030400ca10305030311500400321401c009501c03030061923040c41106650404600c482da2260444128002ca4154450750007019581c2c0c44551941c609410320440302c503038007030b44503243d9034440101004260b010710b00811005075168618541540440c896241c003161025442d1300410200c0e4010216005ca06420380300850070910390500c89041000e01c0a4022840c04481132400c00c0c030aa5120882c00d591003507072a456200058612000c10380c0380a0400051b40d4001c02080240741001c5d004081440d1088280509000405000505035901242c0820000382d840c12000181d24100940c5646a117054015180d5044408081403c51280e0001c043c41d04d07101c1c1c040f00c11941070002069004282c0d98840c0d1000c10124102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 395862203 1250 395860953 395860957
    0x7050c01110c01270602030603030c01020301141c11010f12060b0c010b0102031206040c0c05030d050403091d01091a1201060608060105210403020c03070305150a05101a1e 75
    0x10754469031901d1003030b002e820054580d048608102d025030140d869520394510006e5171004000d65050301061006083e50107090014502034a201040308a450115106100d070140c00200e103056400041400300c40455a0480301030401c64082c645aa0003814640d410b881240e418130b0f4200b902454880c0001e030100c2c862014102c2000d0540081c48083c40010049940340a4132003213a640c0340720000451a01c2c50164407040f03a0b14118200009030400382d45510f801c68204980341191aa210300800040640c0100102e01a0045041e01241070311502d100420300707401402004d00003540c41d0001055880084107000d0121401080c02a140900a50003030103802c3d148240d0022501f250b0200b841903000d201510000082d803c2906024202d500b11240c40c6407014206402b980030b4541c0b14006a1024004207003d540503800030000e90508a503103482c0c2c840000e0443d12150f01c0c00081c0440071311100300c0d00741107846885015812050120b1030b41e9036032059403c030020010704c082d010b511156643c80 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 395863309 1106 395862203 395862217
    0x503071e09020711090907080a06020c1c050408070e131b0b0d0c09080303060105031303090f06030b030f010603080409021b03030108010207121e0807050c0111 70
    0x1c104003242c2c4034002c241e540300d02c800d10344001d905003c09041d40000f41e9800404056141c04c2d10f40d612007501050050801e600081c08100060040150a06c0b0305440c078147c1c000c144410601500560041c0319a824502440c8000500c8141d02c4c40e00c1480f549141c20f0382c0d90400c2071a60b80300e00e42d1034030343d0200400030700e0300c2c7c00031610b8001c000140c0f140c0800a90001817043c105070f00039143d200d89510000c0725900410400c401c83e6031140c2580e4000d18040071114084642d840c05a86081058120445580b1200c4000802d80d5050300a0b05d882d090913400c0d6848007400b01102400e884450001070b0000508100800c000031a82d0b0003440481804100c01c0c03014284582414116842a405008660740104000040c4030301041c86d00d2403003080b0704080d41054003524001c40b20549582c013400910a904000440742c0d4040c80448984481d00d00c003c100d8410600072003112500301c40 = true := by decide +kernel

theorem cover : BRFrame.Cov 395683453 395863309 := by
  have h0 := BRFrame.cov_init 395683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 395683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 395683453 ≤ n) (h2 : n < 395863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
