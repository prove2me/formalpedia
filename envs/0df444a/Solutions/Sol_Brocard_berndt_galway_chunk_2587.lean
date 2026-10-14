-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2587
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:08:59.380313+00:00
-- url     : https://prove2.me/submissions/d8fa8cef-a03f-437e-ba4b-11914646a99a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 465107913 ≤ n < 465287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 465109163 1250 465107913 465107969
    0x5030402010c060c1101050c13090612060b010908010509010501060f02030309060f06040204080102130510020d14030408040308030412120b06041e150e010f0503060d0b071101090615050109 83
    0x84c09000c010600d840c1307041c609020303281c07083c4525032646450314407140c84e00006000b00e402569550f4240003061040c014008101d900ea190041004500068481c0040c1e500300d520707807c0913882c0d5007480104426807805420140c102c80c0580c0d81e6044014043c20100d880b03020540300c40b0345a410201c0411025440c08481942040c0000c00052800d65184007683c22a40b08a0640c01c0d00f40840b0420010380c035125260107481066030024000c4107822200080888003c1d507228808480c000c4041020f0045100c2503401643c0c0c0003141d15520305190030600100802c0b101450001046100301090060580c05298907039003001d41401e0606003071482401c00c07420b040b9412003014440070340003d5461000111000b40a03215150b0202e00d41c1305000041000300955055400d0100401c103000d07031030f201c1119508066402150002c81d0383c480443c00c03550884940c038120159824400d000052080c0fa80c09002d04e0f0070101e142d41c03480d50751080150368162041c41180003400017110722550036010802 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 465110413 1250 465109163 465109181
    0x1c08180402090303070c0e010b03161206121506230f042c011a15091201052403240a06272d0207020301020f0409150605030402010c06 59
    0x542007120b00c1c1d0201c0d10b190018203041d80d00b9041d103042001200101c56545024080c02a03805107145401d0802c880c0318001900c1880800c00d185107170031001c1d1143d5100101400380314003285070300003440c10b20014100d1201d00c0b94103100d00d0041e001840070018008902a4a01c44414207082c01d800410407119051400c001d607005500c0d66201c0c1c01000a4002c08c2d55052005000081c06194003480d0508507011140c1746040340700c03c40c8a981e015940c15901008a0001da490a40c0d81d080c2000824600035035903840d80020b40c200400e200f1f0120003100b02c0c0b4000e007a54841e1040c030329410401c0594590030101c000300c0040111540c008050f2a4082d2203a1082e00f140000c544c4c5035603002c090307a400556222001c00d0301c0b00d20745071035058032080c042c949101c074030081ca04240f6800707400e5025086000910283e206075000803044c08548081d01610341d50070901503680c2d25207580d80408806001c03252000f2259044000c00822554090003c8e24000c03078040e944c10b904400260364107401040030003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 465111663 1250 465110413 465110419
    0xc020c0f0111030406200309010917030c0d0806040e0c0a05090c041802030609010509090c09072a060c0f0903080f09060d06090b0d020d0611070507060801051c0818 72
    0x40582d49803000c10051004200994070035a43c45104005251400407101100c1065041001001504c0ea4050600c900703459000307070301a481002000c20342d461803140040c1306a55014140074044075541200030310b44035000665003841403440e0300120729150919105043e03440b207194081449182040c00a41d684110405a014901900e03403209690000441d414080103a0f000020441c842c20b03c4100c0f5801008280ca11202c1401d18542d9aa124040700e00c2e0140164001c00002d494031340701d2001c60050045112500600280d10010b03071480541c882d0b400c2d990203043c160800d444078814856031b810840b00b40ea44041c0740f0305542e02c51005601c0b03854206060442803200081707658419004220b841841540007582c0e82c03070000c40e0004e844201c810f65100e402c901e000340025031580c2070342c0713105c49600c404001140300303030a0b0714400240200440988103210300040440c03640d4205043c903059880c121064800600300d807040c20048822180000c0c000c800c00d002c0711b07005040c000d03a1401814001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 465112913 1250 465111663 465111677
    0x1050604180923030a030b060a020a0312020415021005010b25080f1204021201020405030c1318031112040b04030b0907170a0b0a0b030d0804050708010603060c030f0c020c0f01 77
    0x29181d000f10802c0d00070725909076030000140c1d5031003150548182c00c1c070008266006402c218010001039180c1280380006028880303207040386c40c00e0508541c1214050180d00710004600c040c0010020359400032440b0101c0c000303207440c0002c100155104141c2f00c0301c80703039035815072807203614140d940c1c00007650502c0445140700b040c4900760000d26070401800c1d6038005160041c04603d0640104004480b0503501c00216910402c02440f190b200494207280141c41030301c500009038024150000280082181072091858813040c00b010142d0028446842600101c00c545d1400c4903c40c054000b40302d140700d1518406010001080042d08958555502c06201421383e00e02c40d40d2501c02800203107140400d00c00580082d003440c0100814156001c0d040045500104941081075011075038078030300740c00181c003440034070130015040100400c003010140c100c100090107900e61303a24010001e00703004a003110110741400c0c41c0c6540800c3c1840707401e01ca612550b00610306450100244402030b0303140c07140c0c18100955 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 465114163 1250 465112913 465112943
    0xf070312020f030d0b030d0f02060a0915020309010219080606070201121805030928030b0907080d0e010e0603040c150c172d0a03180b040317010506041809 68
    0x2c148080c1c003811002d102c000c90300d40402c5080508100d2810303001c2d824050b0380860300442950004016a0010301200005982c2c9403070f040a4541c070110100030102140000308200c4001c2040d00038029150880c0e01e2680810130f4a84147e82600707045031216001802800410302562041e49460000c180300380380022091519080041005628401512070341d000084120b140e051900301201c010b070200c00440c08400c100c5001c04001c2940340703c058000106000451400c40091056030001c0010404945854142c0100508040aa440308501150f03100701407906038104071003140d01c00c50780701503803001c1c1d1030804480c0001c141c1c3d0554140c0c1000055940c240c005910082d0300308825260b03250b00740d2070383c0003429102c6503d550140b486681c0104d007140030030050340c20b006441c6840518140071540c0c3c0c42c4102d00e000c108000d614013a02c0302c1c840d442800b040c90340190810641c00010390a00800780c0e2154140006403245205884825440540d44920480c0c2e561206003100d20a000080d19900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 465115413 1250 465114163 465114193
    0x40803190902180712062d0f060314060a120f03030b060f0d0b06040609180b0a141f0921060e1e150705091305070504080f0f07031202 59
    0x1940400f03450304003101006005100790081c01052440070748a00c14024641485020080420854000316403041e116190300030044207105210040c0c1441c001300340c26990360b003400a001d0820b040c502802410503c0202d01107051840816055030030400d41a00000d0440c0c3c1c48036496451100281c0400d03696050400d417554070301e4020312114841032501a254650502400f04a07411500d140c0e1080c002000100450703034000c0d2641007207a005243ca603010303000107000c0c08003500c0340300715081c0d1054140d01c0200b645010b050464025903070950b50003000340070001c8401c030840454644c89010400e240c504001c00139802c8845403580d2001103608108540d281c2d500010b840402541143c07680048644000c0910801018101ca0b403020004100d0394500c01c4401c101440003402c00070070401c0000d41c02d0360903250301855001840e90180c0800092606400c0140180c0007401403880038000c07042d602e95150030010700c1102c02074208001c0c1101c01e2a550b2110a2420f4183c1050f0942c010302d4404030f0062 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 465116663 1250 465115413 465115429
    0x15150e0f091509160305010807030201020613050102040807090212060a0f0504181a0702060f04020901060f020109021509131401120f0501020408011a1f1b02061801080f040803190902 80
    0x10f081130b40030100c1c2e4980342c03a01900356601600034000ea64000401000545c1c0d0003d000c41d0006a00504901a40b00500340240684075075040111070b40700316000000c503911030f54007c1402c008101e81e00a22525804100040415903210b0000d90100e049000d1203149001e600041c5140342014a10303803182015031301c1c1042c0d003040309820403d0701c1c403180030092140d4050211070780c010109820201c1e545029800140e2960040c041c01c1c00700054000c5201081e4000d6100344606a0011324448428a040c100d013007099201201150040442c3c082020207070300d00f40a8540340e041d07010039142c3c040e030030310440303200c1002c201206a5200c201844c1c0c080c00300c2c80c00e1000b00040e0425000114103901341400b1452002c80806055000381c4289400c44001410070106402c0103c1754035156018076044649500158000d000c0694407040003c0d003030b60310800200c0c0e910000b030b0082e280d100042d62551941540000111809884c881f401c000083c0ca4aa07141141125010484400114850940c011540f24 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 465117913 1250 465116663 465116671
    0x1410091509051e180604030f030603051c021c020c0d03090f08030405030606010c1a061f030506190f030809010c0c080309031b1507060e0115150e0f091509 68
    0xc0081c0f820400b82c01280c0980b981e0740180c00030048541c500304048255901c900080c0090b0400c0000b00070348024910a401c0f0000039030700401181c0002c3c0300340c8070340c00d07160140305031010140c41000300c40307550050140c140030120502c90f0040c0018021040910880c40303403d0908504000c07000002280d20400760032039001911000c4015a1110309102c02d0600d042c1d4003611890500550303602080c00102e0302d03815524900341000c3d900610b07403241008180158050031072212034154281d180c4041507450f90109121f844200c034403000310400d00d0302ca04078050f01e0b4012003c400f01c03000c80a1011030004001441c043e0810300d0042c0030a00c580d19841c102d006160041401030700700280b11642454108102040c0d001c00020407070480d11100006603405801a44c020712100002c2001028006039a01c90650032030420000d0040c858004452402c100c1c56000d00d6040c192640780c102441841384496510401026101441c00109c0b042000001c01c00100300201030b00400140607450346804030b5284c02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 465119163 1250 465117913 465117931
    0x210051018020421050d0201050c18040f05181c022a0409060212150a050f012001050103031b0803060d080c070602010c0908060c0a050f070f0b060103141009150905 72
    0x13803012913181a9043c003c40000305401c5a04020502001c4140d000890b00155a001c1010b000031102c240030030040d201e40490300604528184c00c00004000c1145a003003c40305403010380c0c18140c13200d000c0f005007284d1040e905005038414044401c40a0075480d90201d840e12a0a01c1902144d81d80009820b44143e680c0c2110b4258010a4111881d00c52071041508690410342149a1000704804141000300502c1003c0c41010183c200e181039074010140c1c0c51032484c0c020205810301011442c06406031200b884100c000820341c2c074949207081c1060080808050780044034902d10340362002000b00d600c071541401d48001d83d041100ca20304080400401000b850aa000030684600d4500e000d802203c8035840341869400040801c04c1420200c01110203154660038a542ca0f43d8007400c02ca0f003075004a001c010545061100c5140502c0310303e903802440b0744426a001d0010012410103e0500081501c1d91071455403c080c0a00805860303420880d02404040100301c800c6036244451000d0320b000740c0d00024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 465120413 1250 465119163 465119219
    0xf06022b0c1202280903020a0e04030e150a0c1e0507050a17120f070c06020106031704210201050f0d061a07050303040b040611040303020d02100510180204 68
    0x5422074032040902e82d291000318204101d03002c050001d11100840821441d03030804000640740e000c1c071241e0380a1500685552070140d1103214080b24000d05880c20740c041214180701c000ba610f8112500400d4458140a90b400d20a070b80506450011840008842221008100e8101d4524074011021400e001d9401040070030322b8035050144280040e00850906440004104403420002a280c0820400d03125595a603010b4261038600c240280200284841460140040e410303905400090940340580240066030500b410611800d108600c1420400b140e00c21b080810030415000c1d0071002801814101e00c2c042108a0400c9039030b102c410400080e9a4801061150014200b040c40603441d0762500380340f42468685815599000040000340400c020800183c10840190448042c8003852002d407919982c0381d180180d220381010070701000600c5490521488810f0b81d001e040e0203200701d4003502c403110b41000241c09100c1100d480d0b0f0320b0381e00d8003000000340e8250090400c403506420301d180700c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 465121663 1250 465120413 465120431
    0x60712050307080f0601140c0c04150603150e040605130605011203180308030f18010212060906040b1018051509180c0301060509040f090b09010e0304030f06022b 71
    0x1501100001d4103c0d0b1510032050b017044001e903048035401042c481d1038503949888410051a85140c10451080141c10170308025096102608502c141c1c0151400f940f0300340407444003015071010181c590b00c510300d1100035260120300800c4107944429040944201040270314240703502d43c0416201d00707920807190142c1450340c945c00d140d841b4004031400c0c1010304040e44601e180da114001180405800740c003400f8041d0004c15001100000d40700040c1e100364000790f441b015000d2482100003012600b00b4051500800080c040d49000d202d5060035120040c4500d00e5026940070071601540d4070540803011a2400d02c02007025924035000405036010f01d9142952001d2400500c81004d03200102d20802100a400b40b0402146c41400d03a41500d03103502d40252120112400100a0310078415050703100e0703242860883c20306c180362003168030441420000341309090582080607500d1085100141c00c0c04588002c240000d40d0701e8005000348041d00c2c428940012850706910907403111000203600903540c6298003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 465122913 1250 465121663 465121667
    0xf1b05030d08090a03141c0506120c031b0a08060f0114060301031a100e09010c030606050406090509090f030309010504150b0607060f180f11060423060712050307 71
    0x10545800c010315001e00b45080c09000d15a9806010318001d082c4075048540143c40e041e040c0c00d0b1040c01c02c08404410f115441c0c042d20340018841642e445005111904010044c0a0000340352584248041c0090006420b07420b903080e0f914404142e01d55010345508800a5280c0302041086e000300400f02542445500d040c6001501e0110049160302400040c030040000c00c061035203a03400403112450701801c59490510704220350700070b50040c4800d04202c10511686020540c042c001c00b83c03480e00e0401910781c50f5603040e50140510720451000464424041c00b65040c20040140c0220030704084416007034040d44254290f82080b20180800c0e075541c41004240000351045400008640070200180300134038004c617102d4464400d01410030b80e29a00f00c802445101d42c00139440740002284442040101d1502e00b01c06c84e1900b000755031406600142085034940b51003220115103025118400020600040e40100b0765a8441103a218605000900104038107582e882c0200416560783c5690746840140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 465124163 1250 465122913 465122923
    0x30328090b09070e041e170a0e01090b031504020d0b03120a0318020f120a02031213090b0604050d08040312121401030809191d180f0a020d0f1b0503 65
    0x2c41908400350080c00045100b03c401c0c0c00811408032642d108059060901504d449502858402c1047c00010f100c00c17041d07071001c450070b1408800d90b211a000d0741c2d00d2408158a01095410221000d65940f0028180c41c19600030014008040700c003142c010750303003800281440c1c0000e220803908140002e003103405981c14864501d4036081140c405001c03140680101d1305000700031142c4c0d0300030905a2910400000b0400201c0030040d40201244c00c401041419134070180c0124000d816102a03410001ca480001d600030244170103005080e4a0805140208001003480122400e5903540d1040201001013500402e83c504a0611900c4118030740c000c0c0803e0404503613072035154030000341420005000080300300044032a000c01c03c40300f68800d20003103030003400300754219400407900b0703501c441080b4800c80d06001c00c1d0f40309000107100c164a4600d100181c0e40c9410002d200305074640c004481c85030051409600c1703800503034020010800c001c0507590b186680b2801c0f101d1a02010051500704014a1904000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 465125413 1250 465124163 465124169
    0xc050901120e06010302010305071b0804080f010b09040f02131a010905030d02072907110a080607020309040507140a02010f0f0c08010e0601052109070b0c030328090b0907 75
    0x2c10400e10b0808880391280300c18000281015262400b15a00e04d2041405400140030b1000150440d465460181070b5076016110305009400f40d0800c07480c0c12001840345c05c0103880003414800c601d586560381c0c6550041d90301ca0072a8804400780018a03070244a00c10031700000315400481100305210340c009800c803002503008500c0390380030101c0c1c00301c140d902040320340486000d100380e1031009104000b00c80e9a000d401c080d0514140c00405c4076024441c80d48080170000405440b403109040e01c90b981d6580b03d0350100e8501002d640104924500d50400d1f921080d07001110b0b18114400034101c014400b41ea9001c0441d100040c0c0d1030b000c2420a0090714440c212080e22403d10400c2801d0801e00040c019050510940d0140c40c00c1c080058150303401403048640240e5050080c05a0a079083c40280c80746100303851010107845600e1000c250440020116107074458160000d50640e9140060521482c142070714240c0340c500b407141051042d440d140112607500740b041106500c0c515141030140c2c5000240d074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 465126663 1250 465125413 465125447
    0x91a0906012c0702030d0903120b040e0a030f050712080709081b04020c010f060f09060f05060904090c170318090103030906080702030f1303050606030105061c03020a060c050901 78
    0x3031440c0b0b03140459910426884454a4a00400750341ea0600c180e065006207000c81c440d486c1007262000c20164000b0480b8080c0c0120901040001c9e0410248400c80b004c105501c4007541c000d03040440401d0141c00f000d221001c1074074041e0715000d200e80e40c001076080c0780f0340110013107000c40052006107500601e0b04c001419110303004004070255140503d082a85220003a0f015a40c00910390001c41002e401c0604a1502c20030b003031266640d6641d8644003e05c079846080c11913868680d02154403541e9854031400c172000100791a0800001d403040100908480c00102c2c3e2445a030070000401500c50b0710b484401241e9000550f45a90f200d42480501311600150f0601c078840303400c014000650040004815501d40e40740452041e0f8a0b801c0030f0386140b04401007040058000302d2041341c003001c1145c01c003084d00d02c03900517a049134075204141400e07140141e518650000d200d410b244d549484998135466101c1c0248101c0c0e0060500783c58040032510722100e03070390000301c000403240e200e542c01259130a0501a05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 465127913 1250 465126663 465126689
    0xf06050306090a0c08010512070b04152703021c0f0b10090e060a020a020f0307050325020f0f06120c0a1806050315060702040c32120406091a090601 65
    0xe00c0040c185c034414001c1d030380b1035a144000c80b00740c08002c000c000c000d0621480c2d2150382e903444d014001d172840d06072510341000401e0407a100c280905540c40d081c01a0a804040075029405c560801c107204840a0303072941e9000c004c000d85004200f2410288881e140500351698260818003e11004035102ea000300031524140035140500c9400007907044c0e80300d02d105000684540c1c0950301241080301002103650288008a4200305008002c0014904080882442659007501822511103410202d001075801104065002d8060a01280008600100800d02e84c070309407000490741c3c5840c0c0280c0d0f0004074240c0220748000d0345c50300014010065444d030f001000030b40e85010030082642c88000e18640d020205114414029201d031010b031a56140d00600520a0407088800100b60290306c04d0101c2c409000c52040001c01920480400a030110030860146040502096075901480182084461507aa2000800801e940c0c0c046007007003040c004004c112a05101000a00d00136043c1c02032400a012 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 465129163 1250 465127913 465127931
    0x50f06042c0a120207240f030b01091e08060f041e0f0f08120109231f0803030414120306090601090f092a0503060114040f06050306090a 60
    0x4252a8003150340c005040007422040040c03908144042034020b00142c3d0501002110b50f4001c21058213607004031203080d1180751812007020151072500c03d031502142c00803070416010343c46500710b00001681030600c4408030341d55001d41d2400c0d02001c50010401c01407107809001380c4405001d05a00440303040d50701e144038205510340c0710500029806c0e180140b00d0514016007004502203426a46039040a03485084807190704080035198400300f80e00032444200d20010444c544180300324889821020800e00c409100710320030070031052001d0700364100800300103c1d9070002c204202150028000d15000b41d9103a0500d0301e02446e007804400780b032001035000b2841c9207921065200a0701c0c1d01000c101c500641c0c0e40c80341c00050350074a006821204d03c101303840e5030104644143c2d0304000e5034450b0310841507007881c400701c844c0d2110000f20110341e00012000c0010558540c8224031745001910f40078140c5280541c1c0301d88464031780d807040d0701501c080307240441000b00c0c40c50203491060f44003808036000e01000103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 465130413 1250 465129163 465129191
    0x3150c08010e10030204020f0a020f0f190302010b03010504081b010b090a02090f120f0d1403040605060118060c0c0b1c0203180a140706090806010513090501050406050f0604 76
    0x110501409a0502c10500040c9003516520200401160007500071980c64540641c5802d03103034449404032015114031184c4c401140c40000d400340e82c0038188405401d07526442800301e16001d440c2ca40035400c6640341c3c010302c1c1c501e690a1040c1800f844c8604015070303840c2c510342ca09210f005c0703c120030500b869161203610303103241d1501d4000036800600d15038016078650310a0001200300c0207201300250010140d107045500004000f4407000b19442c0f2100712410b60302c105008840303624250315102c017500720510100300001d13180c1e005550883c80c141040d505890041c2134081541c1210340c0000002a0f000c4240014800c2c0140040d0203401403d10769443c007154004045c650b50010f408018440e031303000000480c8a0748a079840d500b2412600b081e01c04042d46810031070803492148900350640e000d025030001d02e1600035140e200c101c0b01220083c20b000d0303181100300134048050414150742036440f9020580064020302c151403145100758030000785400e110752000040c0c940149698090b5181180c1c14280403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 465131663 1250 465130413 465130427
    0x30d1103090f010c0b070917070b121509160905010804050a0f03050d020d0506040e0109021f0912051005010501050c0a15091a0124091e080304090603150c 68
    0x46030030b54140080001c40401250700040e41c9002034941c640351300070f2107007440d0311040c007208407200702001101041144031820348604052155208604013000300740800080c0c150300c161b1104075003c00c101080121004110041c2d41140c822007201c802d1241030501c00e80141040c8050103081c07034051460718043d9205603450544010142014140a28072000c1610403002c44016a00d110400e5465290303d42c0c10101403c0140d030f4552089040101d240043c03241445040d6859030000c0c0000c0317a806042084450420002c00098104031800401190f07403802a41c003450000e1141c801040d10141d2405240116001078028604221042204620240000480407080c4d9000b900303039116035645040d450014840080f00420f05420b00500b9450a680101c01e01e040300c100705500d0100a0404050301400e038400d40a1102240d10f10406100d07800d55681c03041d070101d6400e894400300d25121100700d45907401035030280141d01e03120141802042645001e007800c8a100d2201400015982d20002d0024 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 465132913 1250 465131663 465131677
    0x20a0c051911010c061104140301240e0c0f0a05040302091803031b07050f07030203060c0c06010e040501090209010915080318040506031f0501030c05100c03030e010207061802030d1103 81
    0x48201380090302070240c01e51008442a11003182a0f980da990341c1e41c40500140e000c0c494510035440c2046000c0905103501e012001c1002c41086104428245000360140782009003602940c2c050a12000c8180d0110724000c0c8031251041d12011346552543c07040004980c0020803c0c10100b825041d01d0001c90000000d590f0809090820300583c6005410a0f10b51406225800780c2a0310030581200b9460002150302010380c1c0c025030588a160303861090040e0244141c8142c1c1105500403030042200070b0500710b01a410070311550020904404039000107010800c20381203025050755603075100300c02200b094240f00080045002450034001c540c503c220180f60039980b030034055074031440028041d60b0180803d00d07210f28010307ca00491864005450f00500b000d02085414036a0001e01082a00d094070b4550b081000540c0c440300d1008213a40e007200602100e2007401d810b99024040c0c0b00010314180102c0c544148050a44e504040b03441c0105498480c02281071003d1080c02410256103810200c101d80107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 465134163 1250 465132913 465132917
    0x50f010605070308041101110303010b0a03060b1612030f1a0f043b030301030c080607211104080d080a1b0c260301090209040f0605240d020a0c05191101 67
    0x6c100c03040300060b9144028085183c8040c04004008580b040d5540e014240d809010341c3c08001541d140d6003040300e907115146a0854107000c1500c40c0c2c0006500c6051621840400c0c07501140300c2e9114003503102960031349140c4030320500041d00240c50b035041c030404c0c8048012040b2018052700c13400070080c600d038044401d440501850654220b20101c401050310040041c902c0d4222541d940c1d503410101036041e824040e00f0818011345001c6141c0c0351062041c18540c83c115000d099440301b90340502001010059000b280c0388409000010341e401c0c052006c00050040e585030794031949846143c131800c80e07004400c2900c0480c0d455071000720955000c81010380c1c0c00c0c0e00c00e01c4054184046565010601c0075003094908841c800000480c4800058010700070b407107025075040c42658440e002c0d40040d5205405803640204d4003100102010135003901100c001c40481071a1880c0584062410b0203030307402420300401007455142d9120030464100003d10408071000034080c03400c0c03215958900c41e90141200941 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 465135413 1250 465134163 465134183
    0x5011217070b1e010605120a0e0c060c010c1815080a09150b01181406070309050312091203040807270509070504151a1c0f050f01060507030804 63
    0x18000c00064200c0d014150408a542e0582c581105804080e0328680012030100500704000980d641c0a0b200341e03a00d40d80ca44010405c42d566850000000b0030b81200d0325100e0348180801081c03e9129035000b4210b500c22003001082e92442102e02070015490034401c4040007a16440c2000941c485e4070380d2444100c5185020342e040d4581c94a1180908000c3d030000d0408540d000c06520140900d900c41e908895007070726650104294031600070300b05070945c41000c024410948100e0310503d40b400007002c2e4180309080804085031070f84003003460124056042c101a503800200c15800d0310300341503c40c24400340400258a807a082c80d14458a809040c03144113144c1070005012140070203400d20060001d8403c00c0d0400161402210840e540c0c1c0040c0703e01030086203400440100f00d041c045e6800180c41c1c40c6d0621000f000d0741c282d02404541c0c811092032142e00108020810031103800d01819013480e4400c200400c040c1088402000604011b034000020300104100220010340c010760469800b54000003d10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 465136663 1250 465135413 465135443
    0x42108040506090118091409030304020f0f1549050c04030f060b010f0f080408031314030a18060804060e0309061c0c0f020a1412030721050112 63
    0x6608100400800d525594108401045030a1b07a903000c41c0e8009022a095030141d00c1d080c42d2162248001e40300690081040c030700300b0900d418400c03070784001c4450180001400404401810f942034214884078001c0c00c0c54601c501520610f220395a202c0116400b5543d00350200e52021500c0500041858548080d102d00001d4840d103200e1040e03400a40d0806044556072034a403610800400903203c0d850b001c60018020010380030720940058441c141c3d95100c03151a91290340b501d0607541c000600e03a050000c0000394030310000c0c410525030f000c40d845500041d034442c056070002070600b170b00c1c030780c0c02c02d0703001001640400c215a4040101c68003d5009140003030304585031000703c0d00350300ca0094071642043d80011003c50b07101d80c4c030b50758a0f20b600c0c0e8121300b04100d081480049440c000780415180069200600000c086104030f4002280b00c00803804550a00b0102e0385504207a0308104c40070004610b00070300c10300c410034202c0b245034103040f0307600e40400c1198148030303150320207121000c00030300100303040c01d000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 465137913 1250 465136663 465136667
    0x8070e040603060f1e05060a12060e19110405040308130606031202030d14010312050f0405031e15070801091a060d0509100c0e010c1a0c0421080405060901 68
    0x1c40510b40007441407211220801807240541003c5d6004081c4410980d009560362103203100f03490282c200140f201d4400b9141040101c81c0c1c0006010603144655110701e2a0003003170b01001481543c1200030422110301038281440713540c81600d02160340c0100c1c201800c00001941c001c6529900040406401640e032009003401c1c801456a600000e000c41004e8600046558001002d45098000008184180300000c6044030401c002840700400b001c00120440c40941e000304090715441c018203299904141d910800a80b0300462640c0c529190b1310000c01800b2440780500a2105c0500d901c21121003e09090034001c0100d001407244010342543d62002c10400c81449880030707079000e8014400c0d501c50704c445145400038081500c621009204507401f81c400c13070741907005035405003441b62503001d4400c0c0c42f6001583c0e91001658112102200c0c5162407918401007040b0f035000e028645000d54032241040051944240d03002064244002d90340f52040000d4040c2003102c090300e10584005850765084001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 465139163 1250 465137913 465137921
    0x213090804032a0906080c030109080708070816150516020606010e010201020d0509160f0b0f0d18030e01081003051c0e12010c09060c020f0405180d020c04060509010608070e04 77
    0x402103c05002080004214015400620039159001d040d140d07024a10020113003219a1944000c02192043c01844045a8a0030241c60740c80c1c06003d40618209120f4880c10b5408600b0008985c00030410085401ea1019440303201e901010714848900800c4070b003100a50f40342c2c4020001c9040192404801104c0d0340300390182c4850101c0c2c0d440a0107281064102d6544582544180241001e20b00c02c00203180c000301c40e50881107130300c21600e640c07409600b0120f0404681c40059030700d02007512280510280780c00301c00f0400a15001e50343e009002d8114000051511340043c2c030400e80b4600b51807007030001c503001084443c070340301c202403a44090f4030701e19005031416054100b45540c403c42c01800b0000000d4103400070020142d55589080040e40c41d0030041c0e0f4089000b05c0060340122420405500302d00f003503800380d6009050240804c1c03a0750551403805240596904c0c2080060b049000c0c40c840d40e003400d00402000e401c0444003a50a98100b800003418080b00400740b00400041d6810b4079099219940 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 465140413 1250 465139163 465139223
    0x120e090a0c03020f1201080c03011b030e010212070206070314070f08060d0f1415100501110c0301060b180901060206060918070f1502010b06161a01080109021309080403 74
    0x104164179103005c269002e0701483c091040426034042d24007080c40c20719040c0705055103002c0294070300c0d4018007410320445c02043c8141c18180259030811850119000ba07e003141c0c400d1001d58000c051724542800001c00341c60303145000002c11800c4009002c0004c0c5c00c0001044910302d203203083c113051364071840000e96039400652301512040c8414451001d1001312000381d00f400b0303a40021961655203404038040068030880e00e04408801d007800c1800303198401c2040c00c258910040803510701d01780081c0000d08480d030607801980f02000000d0012a0f040702003000380b15410080b10301d11034540c5020400b0b9180d000007000944581ba8140000d0303440d0110032a08110218140100c451f0309031225000103401015001d01032124040f100141c030440c1c8140940600b0402c00742090741498030113425032220070fa005c2000c8880c2d003c0c5413030b9280c1d48545108018001c4c0406000801d04c42001d0043c440e1b41e0f010007000b000700d50704109014000c68201012282129031021088681d460403880d05070149119071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 465141663 1250 465140413 465140437
    0xb0a0b041217040b0301030308070806031903050c1507030e0705100c02030a050106230405060a150504170c09100f141f1e0512150d0816120e090a0c0302 67
    0x441c004c10760351641d0014506a0b03129450b030351400d417295034007030f210034100701ca08581c5036010303d212021205203000d035040098400c0c240107040000d54281ea50070003048400003100500c00c041040b01207036240c0512044484550042d02ca52030a02000c511031400400800040c4407451241703004544080118901c095048402042480d03103c00004203400041030503c0c0c8103200917103140c49286014461035000d1100140b0000340d640c98000c4c00c0d0f520000503051314041c48010303c0f000036044003845665951560700009044554164420005620070244c81c10502612400040c03001380e138910388400c00d40780384403154070318504820b000604440005d92421140c1702c008075800540c5070407000740051000401027074150700c0441d100440e120b0080c008100502c800490100b030700904823003c2c0c520b884101a15580951080d03880f01c8601c1c2e40260b642031514103080c040340050100442c0b1100e0301d40381514100c0348484484ac001426880701030501040b05695295101c01c1a010354100c401c048a50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 465142913 1250 465141663 465141667
    0x6040b0304060f0f0221091006030c0f08072340051909050703050d020d0206070804030504171516031b1e0c02090a0204090b0a0b041217 60
    0x80e1410704040c10310508150820f80c18901d02c0320f0400450f0082d02e0f030090124040c0004c1c6081d0420300c501810000e8492201b0740140040b10301420010700442d00698000c0090700c45083c50142c05120f103800d143d00144d02c541104c4018040d65019003208450108010f12000f0301100502c0002d0440702a80c80c5018201001501100c645500100400350b5540e0900600c55900c407404094050720001c0341c256004121100001c4003841d02a4058116140514221803056481c1c3ea11946011600b82c10500940e101c0402804c1855040100550041103072600640e98141990098800e000300d0080280c1e4135108640e00e4000301c0100a190788010f004000c0e0034150620701404007510b05108403140020742014041b01840c7c0c0b0700c0e0a04158022965104900304400560742405030725404810000c00480700d81c03c0f400f41e0b4071261542d01504010700c0041c1d403103140c00c03404022104130b59261402401c42c03140030000d03890224292001c40d50500c5855100306040e10f010500301c4114814400b11100c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 465144163 1250 465142913 465142921
    0x328032604050c0102120306040f0f061d160c0f1103070315060e150409051f020301050901050d0b07050a0c080c01050402041113060c0201050702090a050f06040c02150606040b03 78
    0x84500d21030301490180c1d040e21295001a001240c880d40c65150b8000d11050400c0131500e41d007003a40c40b1101c070055002c00016240b2100c40408250303401d6912119074000f40440c01b903141004200660780143c1004c0518004002410024200c0510980040d20341444400000144a40030301c96104481d4010162012203440740b40482d5250460340c00d41050310b01d401c8006c00c1c1c07007607003180e1240038140b184060100c0490039400c11000c0c3c95921021030baa4003658014542e01085072507130b60001d0801e02d00240e201d41c1003070188800004168440da10034403552011030082500140150b4000c00c0614201d44e50b00704908003600c8114040400811540c00000ca4940101042d84440c0c040c610803502440001103c11004080b1700805681e4a0740c1081c442040008030f000f0600e03242c100784181000b60820005800003104098101c80c410212134840040202e100b16440e105940450212001c102107008504025510314140c5005006e0701280400301c0c500d030313442e1010b68009010181c00c082c0d0380c0c07030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 465145413 1250 465144163 465144227
    0x5030a030f03060b04180f09050a08071a0402212103040b0c0309070915050402040e090105070206100e10090e150901020f0702100e030327032803 64
    0x1c1c4121810002a15100700840e107107118804a400319070440c60903184241c810650709004114255101080c80d179100003030303000a58103100c1c24405d1402202c50940701c0249007060390000c440401d034000c043c0e080c0c00070000103a5480c0a00402c580341e4405a500c071000740c88450f0310b0720044a4400341c0303020340501d0001c0900e00c2480254452440751840308025201c1c41401c406a0106894401550b04003680500615605510070481d000d4080b11060510390f48101113410ada103c1c0d00a009040482410801840707824082c1303640007403840c8000c08141c907000f1580c11075165a4090030109840d02e5001c00c000e040300e403048402034541610200304820801440b9a500c0001c080d1102c0c403000b4800001d5103034007040c82030754500b03609800c403286804000d6082260121510031000c003407004001460b011610100301420010114559031840c0391850010000758110000f540c620a503c180284001d000441c0c2c090030010460a10501c0c030400d40c1d103010380b403d07510004903407100c924030310086d60180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 465146663 1250 465145413 465145427
    0x504030c2406080f0f0111120c091903020f0f0a14010c0803070315060c05100c020f0d020304090f0e0304170f01020c1c050307090b03130602032406070b0c0702040605030a03 76
    0x4084c0441d00d036001181d401c60b090300c03003001a000c00074009000300344500181509540c0e1184103109414070301007040f8000b85559040b50259600c008020b00144210f00300100c45268441003255400f10540d51400042e10204490240141c0f40e2903040001d40b159014041402c1040e038010700d4a9121302d07016000a00030004664044014018841d0005400d80105031200c505600b10014000c85800a2a0709014001c2e90542d0340461003541d4000c040c007201400b036940c0c1d40550741d02443c1c1c0d0b24548440c4001b070324110f030b0030300c00058507080d13003040c5402000044400310f446070340480d10b40b002c0c580101c2d07080480761038107483c455000182c10003034620b0104070008030f001b54150347c44058203420320481c0c05010440312903000c210031050921042d1440c201944c3c1c0b12002d001c0510800c0b500e555010180d80003500d08044005820f110050b54032560161802c03040420355056003491320507224401d91100141c61741d52a1100000e034134007035441d103030050303006800e015040b40c1010090349401440703e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 465147913 1250 465146663 465146683
    0x109020c0d05030c030406051819030e01030b0102030405040b060f040b07060524040e031c1d030c120d0f0e0d0806030729071a04150504030c240608 65
    0x19000750344031a841d460090040d2801801e540141070f081d41c1c0c84d030307132214002c5c0405010b0070350aa03844150600c0900081201305e004019041c82104448079a140183c0700604144400d818942032043c0203009903400001d890803150100d0f0f0100700d9071041d602245ea2886011024100c920000501040d13202c42c0200a0096601c00c2c4810082036840c0700f00c003500c0c0301071504034580c6c20b2421b0310407078a2460190014640d441c01c2c401524030b0035801c0046030004da40086440000561554004440c034446060a09410a10794015511384a001102030352101440300089103040800700d600d06194a0f16813241c0f0140500c0e071010040d1aa0348000709644130f040c1c504903800102d0b074200041c850f007030101c0c001c07085410f00420110040c0b100030b0034100c0003050b4081c402c081141401010701003203c428211903502c002c598030360039600306818002c015070700e44a0611100350070002808002640007842210702a0800c107840a0035201c164140d800781015240445107a0170300e100410720200c040340315500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 465149163 1250 465147913 465147937
    0xb0a0b040c170f0601091214010507030c030b090402100f052a01051308030c0a0e06040f030c0f08060703110c01061512090803010509060102070801090b0a0c02011a06090d0803010902 80
    0x142c0d50351401c5282200004a81c42800138204e0413042000100d41c2ca40113460714402e0350240d499500d803c1c101d500311501180c44030006500e59490580e025014800c885c00070340c00f0b4444c40842d243c1900070070708202e070000025040140034000c4028051043c801c1d01c43e00c4c880102c0790303403090b08030b07280403048a051070700390038099460705020650380505a09036040899105001368115660000002082d0f003102003c01d0a1080780c40c1e07907400c1c65a6a500401c007520740c0b108680019411400e200305002200d0b007200e10500210301c0b0500c065040090b200b540600c040c034000c10206102c50010740d880c06180c002c0c007003940c203240c0c000c21a8040d80510390f94a4000d070351541c560203801120207050b03e030078440240c070b000720800040c4900c0c2031030b0119a43c458018012503100340d5884a003c1e0071140320a01c1901c007002400c042c000f000c0d2460140300c045003142d1000341316007541d11401c42400c031401c8808620507040043c45c815103031140399801804070b07044bc0f94140c0320340e520390591b400396010b041d43c051 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 465150413 1250 465149163 465149207
    0x20a08070b0115111c090f08061b0708030609060a030b0708060f0f0d0b130803090a02010f09060f08041407080a021018090207080702130f270b0a0b040c 67
    0x9210700ca003d44000e8051301000521204030302c1000c485590a403900c0d0351080104030400031941469040680004004000c0203008a10301035509040408003004a4204207400300551400726132244d0036a6013004040301c611200751070b51000030b015541e03140d0000704000f944004008101c1d8100f03500a221f04820f507400e10040d40c0c0b141c20060684c42c5c1d142c6169210000001c000040303a041c1d840075510502202d070170161065039823190741c1e081c1c00c201e6180a00e648010f661404550f8809008100c0c01d01c40d060169005c0d04001002e008c2a103004180c0e81001511030000e824070010044602c1c10650440549400d030746c44100c2c141d2039082c1d88005034050080d41c00514041403054400e0301403801c44d1480001c80904040110000c0e600c06407068405040600c807036005640c8540281c40c09103200d04e40001c0140d80301203e0400c0e030306401021020490381c0340159920403049812a41110fa122229a1490713035040900c1000b0301c9645016500181b40614190100b5004102244000b00e80c3d2007000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 465151663 1250 465150413 465150449
    0x20d05040f02090708061008090a0503070507090f060b030103060f1e091406100e100e0a06061706061902030409060806060102150709180902180a0b030c060712020a08070b01 76
    0xf84a07650140e41c899007007c0a212101c51442c49100d003581c0054000c0199030b10786000d0b442d0070389940c11003007083c1d0b00da07007145c1c44c1041051402e214868031008160400d100491900122600c603020512010748102c0d11181c0780032030b031400c517403040d0454040103000018801424007000003e00c038015084a000722900c010300d01445001901500c00d00c07140c400c0806041c1000d510a80801020b002c201c588150404042201c2d140c01004038868400d80324001061860084020301502e48000a138850000c45018028140c4030201104c0440c050b41a00c444800ca40e114101d00d50700c80d42d4406058240303020300200382c0c807001041080c0a04801d07402c860a10f00d6408070152041d00544960740440d407d4003080001c0180304034100e80d050f48071140054200103c0d008610031300f501504100005120004018052449e4072404000d01402e0b00182104003941012402c60f22a00001414149545941820091080010501c1203602c040126140c141d00d18002151000a000b03010051340c40754812 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 465152913 1250 465151663 465151667
    0x4050103140609340f080c2d042711030708061306080f0a050106080a020913060e0a08090f0904020f041e0e03040f0503010203010509040b060301020d05040f020907 72
    0x1081c001c0000400380351254994191036003403140148481c40000345000c22001d003400000780742c01300b02c1e00241c81d03130440200b45080003049040001d0000640d80700070301280a891003c11046486011410410384c0689541110742210b4001c2d603200115010700040583c0400c0410404498410100b44081c0070f241401c00d180102da0004035901c1c0c0006c0c80c000d001a84e01d16151a0700262260744142c0041c1c0d180d200c0c40c85605110031079000e08034540c001c1c1146000c101c0244200380040144d072016028954082c6c0c0069410700703010b0030010a40e51001d003c0005d01a00354000841442110100c403100c4003180350030000da802501c3c2040c860720780c940b12070100382840ca0a65105541c000c142400c1c0f0f050300c408110007401400c118808400303054500300c410010f188204010000c00c0d074019074880340b030310803080c0030400b90744c015900990050004002d1030704c40e001e1240d0899840b03400e0301403a07600c540c040390090207002c041103203103801c2005200c14040482e04400c1507a0082d0bc0250b402c0d9111802 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 465154163 1250 465152913 465152951
    0x3070501151a161e02150406050412020a0e070c0308060411030105040203040f140f1c0e130e10020301330509010905090708011e03030c080f1204050304050103 70
    0x3260000409025118059202c07200100300426000d500106041d20350744840703801042c030a00c00c010b1013400e00035000c01e501c1d0240384600028a80038506d40381c0303401c000008280340214421480148510103010086582d524071100182600040090700c0d450000c0005042c00001c80d030940c08580b03494045111420503000714005c012070a10a80e103180d103408140002580001c00a450a8081c031030650000b480004150000003c83d0005180c9150141d105500703059034a12100301819054105036501600700702d0341c0d61652002c030380200b021003480d90000c0150504000d0f483d000d0080380140e40a400c5079501a5042c2c0d10380c00000ca0480c0c0702c88030300030414844c88220b94072140c1c008090040c0948140300230210b107081072400c089969560804120500c0b0250340d0080400c5140005011402c100c20030f0101c4002c00d80740d0043d146203507807006040d912581c007018105110002d01d601a4183d50b204943c1c2002e40840034650614103800c0a80d1240c006000b03490010f410302a602a001141c450 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 465155413 1250 465154163 465154169
    0x50906190e19031b0b06011715010503071e0c032a17071e020103050603060c030103031d10110c034b0a060b010c03081b0d0606020307050115 62
    0x1000304044810398503030068104102c0707011000c0210132040d44003030490803141801d5603841404d4a04050030207800140c501e01034040e42070075044003507040040702c0e500407004d047c41c5071080c00e00d282d5035115580d084461b680c07031a0710b0340500908503100e41b00150340640a02c4540e4002d559030100840010104400c01100c030120900c52945200b084001c100681824101540b0000c0020318000c440d50b203047c560504240c1005e100703800701541c40d0075943c00d4000c041e448102140030341300c1864205040e103168081800007804014800154580b071159090800b099502d008014101e84829814002c0040b40c00c1000c50915010f2195161641c0c180020782da80f03007650070740c0e039010003030488180e0b130100c2a080000c02801c03c0401d41c0300c80c1c01c0b180201d85c140c3c4010701c49028181000c1a4104081a00c840482950420021410030b4021075404070f00990040044814541d21052107501000c15020701117a5035120b40c13500d003002032244c0d000001000040c2c4520000d00840b440302e101d8034074000ca688 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 465156663 1250 465155413 465155441
    0x9230a0b06041b180f0806061206040209010b0a0306090501031b1a0409021309050c13061e03020d150b040e10030203030703080a02070b0109090b060906060405040c050d05090619 78
    0x5011080e0700c40c02001865440100c84a0380b40b040e85d44c1d851144283d040c158043c05081d008682440200c0c200518113404c00c2e19100010401800e0a5010903080b40d0305114284807048080744100e1083e10030b070405001402003440038001940c40b4149000111034511250003016a8108001781241114030b00f44414000440c215080070310b0445403001179804840c05004135580c04a010038510001e200d02c80c050b100340e814442c1c903411940340020441040350095014014044800341c1c4c0c2d60049038507482d043c1e55a2401607202c1c12482c48400242120440c440c88480403000049251301d08000038100711021003101c3d000c3c07904c03078103114400340186000194064208000400200e4069800203803c01000d07000117143c101c2c45e40758054001070a070844c2040c07540b645845410b00040c10080c0d600004215003525040c103201000806920a6104a6001d07585600010181600a005840c0c8415400d0b40c2031000e0300c0c01044c52a10f5a03000c95482000141c00b42450740c44c81c06074481c0d111441c41003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 465157913 1250 465156663 465156701
    0x204080f0c01320307033e0d0e2a0118030b0c1611090a021611030a020402160201021905030a0302090a260c0f09010909230a0b0604 58
    0x30182030001c440c03040076250780c00121200f01c0d290440752900158800c040b070361780008500d0008408141c441d0100b0040d180e40c480c440810004c20001480a40d41d02c1161035030942d642c001e0400c9410141840c036030100381e1070040300d0040451031104003071200300403001604603c0c0c1c030a00b4030064800b0020340ca80741545294020040c80010310f54140b064111aa0546881c10700c00345c0c1c0e0341d04580a003504c000700c0b242d5071a0181080d0504000c100a07400c00028075055003444441804040842109a405020b0500480e00034050345c0302400402c180341e030081c10940d9140000384290300040c0350950b00703e00510406906150340310300c81d030480580e40d0f80000558903010003080c00b100a5008500701035408860240c001944160408400312240b1030204900d800c14800031410b81000d01c0f5604590050383c0a1100f011030f90380d0000124151050f048000882c0d040d541802812920f04240140c02028a488802d2800400141c00211140b25005008065681c032062005540f21050002c1e181c2e004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 465159163 1250 465157913 465157937
    0x10807080601034806030b010210090c1d060a0e010e181603060905120913021e07051507020114060f0d0605160212040602030405090414070303030204080f0c01 70
    0x44800c800ca52107021084240080c050300f0b444403440ca041810721010b20481341e05030408015040c2040244000d04003044244001c00000c2c1d11103104000503040f4030f03951301c008c80030071030261a01406095060305451204806000c0e030403103010b098407030340e00c210400a00001e00040b08450706040c1c441658944089450f020302011184400e40c40f040c100d40181e019400412814100c400010360107403002040c842c09c2402c0044c1410700030076031001420802c011820507034548040120307481514180c010795503c03c28441c0600744248a13031110f0b211500050960500c04001401b2940c840c60440454240d210407005030708032600110340c4c20300070101c0d500080603442d00d4610984803420290403680031403556a2001c084030703130480380305184010203460700301e200f5410807103482d00d8003903412124034003070400340081e59a01451184c60310415015001604001074000d10800139103241085130b000944038580500a0340090140c2800d0784150304140360040e500062464040b0b6043c3c44100880300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 465160413 1250 465159163 465159173
    0x2071e0501050c030d090803062701060c050c030a03050a0f0f0801050607140607050a0f08040b040b18010207060204060e0928090f120807090303050f250b06010801080708060103 78
    0x82c3c42c80d4260750109104020620103140a805115842000c03a950b6914000d01004903c01290240c002ea21400e41010017480102843c540e0546000f03042ca080c8000940c50700303910380054115103d03054020039038140304168029002d003043d001280c80e541200e250032082103e646015604680c0010030280c0100424107100c8000e185660090003000c180b01d6100391118500442500e2560000d400060b81c1d040c083d5005c1001d001c00413442c501000c1c07038241a144c1804039800508050f101d121340401040c80c00010551a40200050b040259168007403820003100940161140c400846d0041e054007541d03140003090381e840b07444c800010001c0d03d5011500c44000d84916801e0b92880d60b99411710001040301140740d10f8a403071281c00039980f03085104000618a24014180301d05104001e8824800281c10505a440c242c803001d151b1911741039000405907011803c2c2d110b01c6480d42030b00c80d2003400c1c8100307a1000ca200b03280a1300c40185036661111150b07956031b181c0c031550003180c204c800141700041e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 465161663 1250 465160413 465160417
    0x7140c1011040803030f01050405421002030c01050a050112060b060f0d0209040605040e0601030f030207090e0c1f0219210f03050702190326100602071e050105 70
    0x49150396a03070300b807035103a6140c149541d005a03011980c40c680f042c0108528502401081d078028500d001e483c0c0241069103070444243c0c50b84900215201c0c241a040301143c00f09131039401030f180d0051528080d0401d0310400703512503004410b041d0a650038000007402c112140d01030581264004840da42000180d51681002007116402c0d09900c0401009036042c4510102c0c05030078694251000165030328144001c100c110b4407107500c03041c042c0e410b00c3d410145560001c200e042c1100d4106504030b421844500d412070038079016421a0a1644c030b40390140003a08400200004201c000f80c41a180c0408403094030142c4c090881b07103000059111600301c80d81010015a06c3c1c0310f240c03086c62070046428040007800b400c014946c60200000f00c0001101080740e905000b840d420070002c4c0081c010300394078a981c5500c100141100a000d200102d22003000458060f40c2c0520101c440c0d030120141420200c1119440100302d01c1520010320503080c000c103540d00c02c080310004100c00c0c89810031000b4079000c015a119 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 465162913 1250 465161663 465161681
    0xc0d05031005010c02150315130b010915080402120124090c080108101d03070308041703010e0103140a020910061106100e0c13030302070501030f020901020601060516020d0b07140c10 80
    0x810103c0b510807241d140c882400000200d109c80108903080e82200061920b90ba47d8409409058601c8040c4405900002815001a0155880017003144501e806502611841d1640104554a20584420404828620810342d00c12a0040c4124452240e040340d01a000b809604039542010400a010684907401780101d1041d50503500c0e02052091840d900310703004420164007040c9401e08100402c81c2c0b900100030060101c665a500311f5051081e94000c0e410140001805680c0403103641040d00c00401c4407481456009202d004a460000d9070018058241c0c0314500c0031070078061155005560200d180b611940c0540d248400d1700e0720b0501c210311f1ba410003400d8110f21100400900e2449901c1c50030f07840103180250005e00301d107494040010102e42e0002035012069105210164003680c3c0030641c20704440c41490301d5034481c411a814a1442c1d240014003d40c4900e0701e00b601003c10000d0541f285c030940845e21001402c447d0f580c00020280305040c192981908107002448404151f41e00c01c02c0e030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 465164163 1250 465162913 465162931
    0x14090115020c09102d0602070f060315030b04050c0306013c15020102040e0c045906010806150a0c171308070f0501050c030c0d05031005010c021503 65
    0xd11755803054001d01c0c440241c01c405402c92681c1d448041e0071044844000103003402c0c4001c1c404030b4502610700e40200410f001d803104150b1502c030549031080c0708400d0040a503402c00c2c6900300318203007131406903541c044401c041d5001e80a0400002107240d48481d041624640d4501c0320200001044188038012081c440156045a8080000300e5503031003c9180111a0545800040c0e0761800c1c545a0202c10314000c00c1a1740240080006001c003681102045440c032003400c40e1091a0103a96407070904091702c0200c1900005900300300c490302e406006c0314480c0024003041d490700068450000441c0c24500031245030750461300080f4118034007060140102880c07c1240740099400d4013940d076029a44041c2c2a42c05801e240c080750507086a4070070100d103002460b5400081400a2810054086031000c5d4031a02d030600c1808103103103a49050074811200840c000d1400da601092a43d90040c21035013040e1500680003170300c1400401da40d40100043d800454004202e084145001d580c3c0440f0340c2d00050075591 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 465165413 1250 465164163 465164191
    0x40f05130221250f060f05030601090b16020f060909131104020703110606040c0f1d030106060201020a080108030307020a08090f0307030b010501121505190e0114090115020c09 77
    0x504080c1844525881400c0f00c3d00000e10441074550b181c0c4074074550300315049000c0c132682c0030400207030090100607000c18070342045c54682e51601d0041c0c0350042e19610610444070001225008071820f0725540010700e108895082c52250550107100c00d90284034501a0000d010402045030000b14035038454542d803190a13078a59001140d03000c5402d0b40c0181c03004502143d085c1c040034a15403000e01031f06034440e009503810003650030001c400502d034001713800012083c8640e14015101c42c1c007141503006c5081401500a000b032580d41d0b20028000e6200501c0c1d58006003182c00003190790040803003224003a5003558010a000700054a85d49140d41c001d9070010380c031102c201c124580544042c40180000d5000307244541d0b040d890034001410040c000a41e011510b480c0c4008500c150b004450000103541080c0d80c51070445403108440c0400d900e80d60000e21024051100010b0722201700b0704644405401629408040e0340d8450302001e1821403a840e41c000340e00700c00b1403442d0313904211741070a40c8a0b801484a107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 465166663 1250 465165413 465165469
    0x8030f0705120c070302120c030c010e01021005090c09090708100c050d140f16200a08030c030105030c060c03030f061507030c0c060906020d030507090b0301080c040f051302 76
    0x28400e507020f4581800d55800000d420025450441d1040265071a60009031a07003c0c0d01600080c0c491400d206114140100c1c883c580340c0591003000304000030720035130504000d5420101c0c802035685e010071900b50703c24180310000890110001c030380718044542041c028421402c6c4010040041c01e00c1d49074000810070203002180003400b030707401594a032602ca40101103643c10030320f20300c80d0910f100034a480d03040403c091403d000036a0080d2254924400c02d00c0c0e61110240c0c1d03907011820641002806015200c0100501c010f4036600c000650407500114221103420300c601c07003401f403203005194641100b90420b000043d02044001c01d143c0d81301c40d000300001329803070207108400059003002c5415400900721031019810400b000031a1400f402e00c80c10648806403500e04000e590b02c0d04d1880e0b031000c00d41c50310003190f680340c000d0581c0401303000045002034036580c4a0141d141d990b10b100c0e000130301c114100f111043c408a00d6114041c0603168072120050146c040303400340801e101030701801008501141c2c11036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 465167913 1250 465166663 465166693
    0xb070b220602030603100216060b0d060203160206130b01060c031215051302030f13032606010201230610020f1014010e0903030f0a0b120f0708010608030f0705 70
    0x200a1144241c8005842c2d04042d800e051614901041c104e80141c410010720f08200084035002c0c10300d980c0482c0c0490b1203440d24011500c040302c141c000811030740c0003006205000c014003240c540c211000e5404c903240c0780e5801d1741800c5499142a409001c00c1a04001131000714840c00d00c3d07030f9070341c0d010341032242c1da84c80c1003d6080b003101c441d0702010490102c9481e0078025803912030450551012140b0007541182008550040c0040c4007074008041514191240300805010303c0003103d29081d0013910022050344101681c440c1907044550314015441d1084800405e0031400002e480c0c030194121100c032903562802401007442040416200354855a1004200780d0810070000704400b440d1300f80440d66451004481850503010707000400c0b541c456034100080e48000105482c0d014026444115107501c82d082c03000300a01c80c09007101d4000201090b919100c0c180000c130a03c07229590380c103c5215a47c0d0300c0090742240c00e00e0182c036040c0d410820030f000d50301300070a0240054a008a0648403101030403014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 465169163 1250 465167913 465167971
    0x110f030601090606110a050607030b12030a05041a03090c0f0406080610030201090509150402030c07021003090b1f03020d11031b0112060308030610121a09060102070b070b 75
    0x4062142e40b0f80300c1c1400525449000b03454011000d034005d1103089641e0707582c0b5448060041c1450205035688010401c1e070303a0380004040e031030103940741980d036078500301031000304298444d02800d00705c10049000a0803620050084034070522050b4064003404400c10200034080c481e2080c03041c2e0040e1900c1020940000a01c003103406415915500202c0615601c0090103c007100d620151003400003c0400c0242000c5450030314001d8022200183d0325a00e0400c288024007860101a4001c942c0c0e20b80e1800694045d07100300006406082d896980c1c0da5503441c80038164910303014901401411034003c20050400034030076002c540c842c100142001040e9800f280c40c104201c0e410654111110a04070403c1d44c2103141c5034048918504180441d03800e540b6450700a20000d80100e00848041c1d090350f800e0b03880b038030a111102048070720078021241401b42103c5800003103099940300309550008580f813507000203074020444500990031820000c21b500c1c0c08503003450050070800d0f404968445052003540c4c41d04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 465170413 1250 465169163 465169169
    0xa0210140a09140108040c0909030c06021218060106020a08030c1219060b090f01050c010e030310180204030b070f09150503070e010e1f020a0606080106081b0d110f030601 75
    0x30b61821424a030640c0040000e68400003141446030304014003005c80c036500d0221080c1c7c1c5140e1808500088031745000c07104000c0000024010910104140ca1000320600c0d180303002e9110042000c2090590303100280d1030706001c0c850a00540d005c10406070020341c161015662021144800d282041c0355014100c00040045480c2821862103850b448040000351040710301910500d40300d24100081100030601041e41d01e550345040c00008220300030818002d4001c000405144016240c40381001000030006c05164060503040c2540d12201c010700302c0340c0388240c40031240c0284501040e600ca002064550100c2c0e5544201000302006c000316245503515452400fa4460b5984d0325039902c4c0c140c2009043d42d80461100d41004441c01d06102c843ea13030498049801c5883e012145440c902010059250242c40b850040c8154100750b4000303503101c010341c001400c4443c664180c804003042920000703c0e040ca00c20030b036039002c50082210307004600c4407a40b0300d02201c3c0150145406070380700c2d4002403070860264 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 465171663 1250 465170413 465170417
    0xf0c080c2409061e0a091a0123030a0303051806090303191a010809012004030501060510121a130c030c0203121819030521090a0210140a 60
    0x2084460306401c903141950781c404490405001c050810b21000c010044c401d0158003460807050011403d29242c40c0d1003182d00d03560101e4040c000551502ea6807403421424402d588034203880713410030825034108141c44010036600401070401074503255029001400e0203004010704c1c0c0c4442200140241040141d68020385c0404000c1d0f07201e1402219151055203068003c1d500107042001c00210035030142c40000f450042403c0c650496619440224018041c40d01c01d03200a2601010301a00038200600420903280900001d0245944650901050540b52701010002951600342448003011591241c89079842c41040c150050440c0000110050070b144032003c0c0495031000c03558140c0f84c15120741c0e190300b9150700107141030010030380801050100082401d01541c0720f481d030b8030100300c0041c0152540c4a0a080309001c0c50304150500401540107203288006c0810140300c0245010310b103a554030f00c0b9404681c001c145044d2036600f88a00d864450703400c9414070140480c2054080315060144c01c0580c5c2c0d80d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 465172913 1250 465171663 465171703
    0x6010504140c130b0a03020711180a0c1e09030b090d050f1303080f0319060b0f03040507050a120302010b0a0f06260115030b06030402011b0c08070b0a18060f0c080c 72
    0x41d0418903100c038070707411143e884ac1c048200c002e6042c90795178070110b6101d14412400154080c5281c01a103a4560005040010400601008a1441d048000302d010b41c0e029441c0003150742d4900030343c1035681c03004680e03240105409014016004a040004008155495056540360b95503540c1d9000246c100b490910015440402000310b96412196510381c200e118046c240042e600d003215914107449000c000d0300342c4a4000001405000041011000a0070302501420303800f65500714600e401d0111402c21001542068590b046ca89032482007030060341c01a00c3c202c4943c2d80b410b02d050302c60040a148070309140c08075843c00d0500961050215000301560219403941c80e0768000d0040c01c42d40565411881403005009000251740d11155a1501054214444103002114184200000016407101c8175501c076460b4040f500c4074410020b02080c0a031911950604280c1040e006e503004d0440c007444c00010300380c403079840a4901c100c1218415074000c850061400342d0b00c00445041c0503001c54060b2100b00d030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 465174163 1250 465172913 465172927
    0xe0904140118060b01090605090d0219121217071d0907050a02070b032424120108030c0a112101060f120f0605220609030206010504140c130b0a0302 65
    0x1e21300903020110400d2a0030440c00c0d040c140301610f2400307000e03001c0307000d046144000d0341103407107043c8124000900c100424200f9a0b0314403080c3c19080041d04111080d103180510294280d0041000060300407451000ad09107550b0140f00701d4044503443c20380010124202c068604035261207801d10f0284150350b135055039885030030381c01070301c1d01ca001d42c05050888010404c0001840c440d991510300c6510f42e0341c011401003a03400000d41040c641d104c03903c1004030b44800c030003070181422000389000c0103010034072402603a8079200380e5104e015a000304202a0002c1580c0e07400200c4a00240a15150061401082000102d101c01036521045d0348401180e6543e00144030402280711404028074401c0c1000100e00355079510307658003243c3c0f15401800d49840f00701092500182c041030000340000750070301210f0905c050078001c0140c00c0d119425000750045000118070340c1001d00522603410400d81c4242e03020303111410031b16440e50003100b03005501100d5580200f05511101c1c003e040d2180d080da1b002d41c07a004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 465175413 1250 465174163 465174173
    0x3011202040b37080303130c0e010e01080d17040f0c1e080105090f0325080705060f09060c07020108060f0603100f09020406091e030813080105090d0e0904140118 71
    0x190b21041c002e840b002080f0100201c100002c1100c2c1e010340d00030f102200c0c91400e0301e08103071502c0303594000303014040c000350020032046072400855040300c0e19070041f40c04003170291a00307694034030343e802400a1103c00b200026004c100c015007440741c203a100d1900c041c2c6040c0d80b446205103007040440d01401d040300b0120101b1407203034240102600203201c4005800c411041100103550707803042100c00e40c041c0c146c0f01c5084a020f8007403603c21036511b400201441c2d03603c0d4907140c22030b260002280d030303810b1041d18440401c1480d80c002500511821900003400d1400d42c55400664407801e005001e2540681801c007400741949400d00614011350010020800081c01c00c0d01190780f448041e0030207043c0718818030041100580c0281c03100119031070030030441100122451002802052500080c0c1007c50002d40580003040a140c01d004641640008010a0301c4031000140c65200d0344189030006002c00020f00ea03d0311b415100035030841d00c54034150418501d44842c6a0940e0500003291900c141181cac0c032041800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 465176663 1250 465175413 465175489
    0xf0711100f0b01030e01180b04060e0d123b01020403050a0501050403020609030705030415021908090f061c020906210403090b0a09090e03160c1703040b03011202040b 73
    0xc50260b00030f11140c40d038440350407c0010b50243c094428844400442c091290580c407158541c8200e0090302c1000c0c190700710182500a83c1910500300500d05089904020404406901e0080319291115100c46444407a41036400d1810401410313554200800800a0802c00490701400d104600105803441c1504001e41004402000c41041e5001002058005080401101d0540714880c51b040d040c41a0200e0880c90155820b540001441381d20001209100720000070300210001100c00c0c0802c5d50140c001e0001e41e0080c43d648155144908001006601c0a5009400c1c14080900b026041c140402c0007610421050544a115544484103100900d544511002c4c050000c140802e03141c585609001000c2c0e0300c1a115102000707507104042d22400405004940f400b0340308070301046d900740c0a8108010b4000a5100d110a40c0e4010540f50124440c0842076604895405002e682142e184c5061111020740d40e00d0200c0e4031030750b1201141e000e65911902081852a48104200e01680c2200300360a01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 465177913 1250 465176663 465176681
    0x70b090706140702011805030303040605150a050303090d0807081b10090201200f030708040e071b06020906040e160e0303091e0a03080318010b04050f0711100f0b0103 73
    0x10301c242d4042910300200c1c1c1262001942032811989040c41d2000b030090010554100980c10301001040c04144011600024003070724650b9808504280c4180400010480e10b1240a8144d001806600c841d031420083c21400d450280f65140e240035240c9d0b031400f070143c1c400b180d000d00c000b40741d071114080a0002c0089101080310201c0401a580054001170141e2010740c5480b42c0800303903221442e07212003060110201c100b140000300c945400f40f502d40150990001d018240900f01c000700010724091143c05a010009080c800704900100140c81c2c0c0000b030b43c052175880e03030402e41c100b00020b00d645d00c2c000400c1c486d9000d0011030020408555000700786004048006200c1c3c3d005104410082e95036050300d80540c240001013045044514012900d0001141d00c05403440001100b000003981e40c500101141c60b90a6008009044c0c2800420084271b03010f40d001903d200b1070400061a40c0d008446444031581c2f03020807151020f0310b40b61040147c8040c0640d0158041c4c48000701345c0300303507050700601d650 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 465179163 1250 465177913 465177917
    0x20a030b010e030609370507030606050411070b0402041d0705011b1a22080403050d03090c210209040f0c060f0207140102010f0f06050f040516030c090e1e0f09070302040c090803070b090706 83
    0x16110540e1002ced0110300a050000d003d03490f01c00040b6045503100c0e44040d0b03011206036862450b41000e102c50545a030a107214003404185403103042e903040300e0b66003080803110703500c00c4284202100c0d03843c00c8800d660005040c9001207640c10358651b0aa85d124104200b5944628041c640e502c0c19898114142542d44065609050030300c2c030307980e0005901c143c698041d20a0011700c008080b036001e402d12010b08992034040d410030416024071003440701c1000d425510350b0040c0f15802c4c41c140c0c0d9a0049134018901c43c0c0c3d800041c4c2040e4400d02c80003500d42054030300f41c81c0510003c5072508501c100c0c0422940005111141180e8802e020889800d00650f03000d2090401c0341c04200c0e61038240c1907200100340d8017171800109030342c50031403101890003540f6500181914020f14140c900c3c0c03104100c1084009804283c14045503030001070b001c0404440e04a10503015000502580c5140d42d0030312001c0d24000b0340e968240715003c400420082e0040001d0105030780100c0c458800c9007482d0301b0050510f2040d41000003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 465180413 1250 465179163 465179171
    0xa2102190e1f0311070c0501080c0c06150a150e0a0504060f140a030b072c10080901290a0902030403091206020904020a030b010e0306093705070306060504 68
    0x705990364003220302c0c606490392512001c05824010850080c00030501c0c40526000101c0d107002881101030003101594020f803079a03e07142c0c83e0080100c0c110301072a0111340040d402030000420400340c094030403603035480c050444000e440c1c4a05003c24050343e0300c3d014800250b004030362403c2511b000510600101010b40d0308002c01070070700d0070b4814110180c1c0508000b4180c101034003c01902d60103018070007150017843c5611181003005004009400c06182e20840d07550410301580b0f06c815030344900310041130040c00440c000c1c2114401351480b480c010070182c2c40f956104800311010140c000645030038581c0030b400d1091000c1410420402e0381301178120359001c4e07106100f003000007500500190b0580c1d130800e0082c501c0381418038281020b0f100d000c40300c50b0014000303e541542213800d40c000d000700440903200d0201540c1b4000600d85d85000c1100d410401e1f9010442c0c88501c0784cae100303490303000c5e51804481600141404004113030043e40031100c1101d9550203400108140324140c490500038010880c0c0503c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 465181663 1250 465180413 465180437
    0x40b0411061c020318010e0706231206040b0324010905010602070b160c231005030a020a090305150603060c0a050307030b030c040609020418200a210219 67
    0x94001c002e40400404180d4000040750244040440240300e88060b080280046002d4003102500c60001d4414040800c1c007140100c01000ba41c503400300b52101c240001d040c101041d0380440c51200f40c02416480c0c0160f5a0461110582c81c10721000d62480e0290845050204101454000c4000c05911500c403c40c581801805900e6002c12040210b403488100241c03203503010070440b911503504a42c02050890200c800040003890034071000440c42415013541080101c580c2800b15203041d210700900001c80403c0051010205580039004000f000d18083c074841da200e5507010300e8130881d5680500300449032130421240c0d250070000554800002602ca60074000e2281002d4028000a031000013030584446011510b81c8040088880014004000740020742d942e40200d00203500c10f000d000064603200480000c0b181300c50145017108001e0f0301d03004540f19401c0001c0c01450f0804540307082008614040c2c07800285016030b0700310460b00070200c0140d0711a4001c81000c0443d40c52042203060200c145298 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 465182913 1250 465181663 465181687
    0x30105060d0b19143d140403120318170a0306030203030f0306030105060a03121407061401030311031c050603010b0a030506071d22020d0603061505030c060d0b0117040b041106 77
    0x700140340c1a05c0005102c07034070800013541d40c405101010049514041400010300c04214040c202c040c03101e840400c4246a10700036003000b04181c91001d02100c030f540407200160300684006001407440c078980003805540317070741c002411607100081c0ca08911002105200c0e02d80b82c00e02c10700b500010101c41e1962031502d950784107030046068039880420f1001101c0320030345464035501100c00040c2c2c072030404c00031525a645c80d98509407085c00254000f400000e00151841030000c100c0d90480c1010307241411401680c42007602401c8002c041c99015500c80c444501d15445001c064005103100390040e1142d460002001440814044032800b1415085c190300007441d216134240801d450300703500e595071301d10b40c209041c4400780c421001000360301e901d442800418403509600c002140d40c01c5016801c005c41d550820960344000b4804030591000e000c0040456060302c0c0c0d4010500002c0c107040243c580b0790b003148039052080c400c0364152841c110540820041110b29a034013080c60008071116401d0126a18034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 465184163 1250 465182913 465182989
    0x606050a050a09022b0c020c010203041805150907090315051005040f09050f070f1509060f020a02090a0603060b030a23010b061306020d020102030105060d0b1914 71
    0x80000c204c2c0c0c00120b0048401041c41d26044003514684540c20300906140610300030000700b0009401400b41c004c80e246150b10101c02c5800300d66045904546090580c051000140b2001d4400c05c1a10400042d41c03040c1c2c5c81e00c0607a1b40c4500c006468140c0c229145007064458841c0c118441c0456504d4902041010340080802d039081e61010b980000702800340b03081603801032101d40e0010b803861044541c01001d819000580d0820740309000d440381d4a05aa541c803982644a004422001241224505000349841210b602d0b40c00c240910481c3c500d090300d900452103196080d100d42c41400e465001c284244801303401801c60508044e40140010060350f150309003143e46c0f03410070004c20342c0349003202081d010094011040844000700b0345951242c0040740f54101685074070270b81c07015004481c11248090300610a5a04852010340b0a61030a42c0e00302d80080141000c4d41d0300b9500542c0c905500f40402c1a162000c4060080c0c0507850070328040010402449407007850f004180b8026820100c00c0850384408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 465185413 1250 465184163 465184169
    0x9030b0c0307050c01290a030c05101e05090a0b0306091f05040612050606030a03020c060d1b031e09170304030e0d08030a05010e010e070f0509030709090606050a050a 73
    0x90150700c9440e0310310704603418850203811111075820104904d002e90082c01000209403080f1404400c40315185044c02642c0e501440050180d0001d0b1a00700500e080c6401c40b904992064980b1030f003c81013031807800c6045400e6405003070006001180d0031450f41050700b100000382c10b00320542c03400d501e0000e0009514180c000e04003c0096a070711900190031070082e08003c05814000c00074031091b07486090508040000200c03d450510821012a071b050030042201400141c145d800340100c420b6070380602109500080c81041180c2d62808405d41d1080b4410b01c10180604540e000300d0500d440f42d8400c480241040e0807100710740e21b00580040020b6030801180d07a125082410079460350741d03a00701aa550589100b440f034000c00c1c0000c42100300224600114450142d00701304100a9896190285c03522600b40950901d1207840d90110785214011a40303100300030300e60f150492401e04803001017402c1c54280c0c0e004002c41c80d214440e42040201c5d5024801c0503040035180b0448036450000010144d502c60300c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 465186663 1250 465185413 465185431
    0x80c0d0606081009061104050d060b01020a020a03050f06090c1012060305240f070f0c020d140307050c030613080304050c0910140d080306040e030c0615010f09030b 72
    0x110401015411a400074402c1d0025200390310b03650007106002e0700c00200d00b00c0301a45419411302c4485080000d0754180c034405484001582c1555030394034010f00f54107000e503041d485210010401030b03031181e18040246100da005400400e03c0b07522450b1400a018080e0200354101204d00d03180d0f902c44a403503882c10040380c41c000800428410041d00140341680002d0224050783c1d90004140c5401c0442803030b0560008003c402d5541d928840342150001901c5400010704a08110500315100b030750000c40560004040130200301403a134900c8040c0c542e44008080076040032440d84148402484241030990055028280310324000c4200c00c0040d0060b00c0081601c000400401d00707020080103005c1030482c001d840c01403981000268152882900e01c18101c04c0c480d8000300400c18100382c01009078040e40034070001e0454407004100405000310071284a05403100348040d1001440401c0428060651000c0c09a15000c0520005007032218800719942403010f12741c0d00b040029240d03452503a00c11510 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 465187913 1250 465186663 465186679
    0xe010f02070e1605070501020c010c1103030f06010e1306150f0908060406050702030c010903050d0605220c0e06071202150f0a02030a0e030a020c030c0f03060402040b03160e0f0f01080c 81
    0x1011041e10980179588014200f90b1001c206426130203c154010580d8178030f1510b4800c41014041d081075580d2004982070800507038042c5c042203c41d4014201d25841c4000204044100116102e07a802290b000b03610258500d804114400071490300000030300600c19840c607090351040d04201c407240d9a0207003d000102001c5d40c907070000d10101d2080c0240c0d2819050308d4020f00070f80e4000c0c10001c083d90090f071401800301d403034030380009100e01e070000e42e442042104201002900c105a80f8500041503d00c01400034007550300441189070381d9000c010403402d841800303003440051100000034604013403800d50320364506c0c0300000c0c080580c0c0440103d80d80710445030b07000b5a580d918090740d040604410440b106040c800494000905500402c0c4036580b050f080d0201c5000b40101803c100301104c100b110f164054003c4808980541816004072185800260031280c2d0722003032a030068000d118a03880300380500c0c008018400c480206000041c0c00500040c49800c0d42e506100e40c1986030304a10701511b00c01c03205 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 465189163 1250 465187913 465187951
    0x2070b250819090b040f02010207060807200c0a0e010e1005010210020d150b0d05160f05070c0b0412060c05030c0909061302041e05030a081e04080604030e010f02070e 73
    0x1154015002c0035a204044c1900360a02d8038054410350b4412000b280940078100020410500c5650704511035403d6686203a1200070040c51403107071404441c028029400313280750100d1191a0140085d0041540340452141d0350726005c032010380e0b540c0c09404001c0ca45034200b4204000c0c2c1c1d00242048080014080c0182d580c002910304000070200340c1521101b05840c424001101460b00c800380c031395030f024a082480242e1303c0241054050210400c01400704101403511400b032032294014024007403207948060344441d2640c800d050f60341c03c030780d100640340c40c1d000c0c1a80040040d039000f1210350a031141001c03821810311341c45d8015507020b4445400d009000c0c2c2400955140d0390301603d003100d0354408500315552901c1302408010098610700c1c601d01c0083d1550001028240082c41c40e5103107420058280c140752102001d140400d008103141014200188804901c216044c030000e03000703521a4407611000000c40d4000750016101c0751102c0d055401400040000511207500142e12611200c0070910f4241 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 465190413 1250 465189163 465189211
    0x40206071e050a060506011b030927050c040f0e1b0c03070209090c0f0913060213090e03040303030b090f0103020103020306030a050615010806092806050402070b2508 73
    0x1036410300290543c0700c2e40242c1c0081c002c0c00c1c3d02482c0210001e07a82e10b540c629001c0031100c00c00744081d00040002c0e41d051170070003007010201c440842c0084443e1151060361940c12407841900c3d015584842c540718001000c000d5003070500b624100421301a00b00c03a01c40e203071065504445412400f031144420387c1c00a04810689001d0040b20045640203150b903200b03040442c00f0701d94403841074a0b002d0040c8080350101200d482c0c00310501380301d41ca804c40c40c4103510100c1d03034a05c00a900010000714040001000200f00c403c0c050045440d04071110006544031840d5083c000d080d0381a6200d5503009840f00000c1c40144079181c05a581565020300b405607403900d494010034034000703d600c4050140d004250a0003080045c0c9401c40342103000981e510100c5480311800c01c4910401950035206525014100b54241e100143c0e4030110101c2d9401c000990541d100d000c00c1c00d988c01058103d80000c0001c080200e5200c884000507521460544c003a45080540301c4003500b203401c0905200482041030403640003001c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 465191663 1250 465190413 465190463
    0x7020c060d06090203070e042315031203090a0c0605072a17060108010b06280905040507020c0a060306080316081b0307150225020d231504020607 64
    0xc2443c0c5401c41d81c0b4500080f00a00e224991094144145d0401004014141d01800c200d021407401c01000b880329154607141440390842606040d8140c021030ba90b42c60b6008a0034040e51003200c0500c0580340b001f980d889d00d86240e1034550404c2050000502c00344002c01d0400615440c46141d50300d1500c011400505d03a00510f004a512004805102c0c00e2a608000000314850341211170382c2c0b0080c44181d400c2d6080001500602c11a03502c03051200c120b01280913a14002417010305d4040c01c0034100c8648990203d020f440040300d00f031000d0790041200b0b80081c280107401e00d00030543c1e80340c108509800e2a0600da103038070441c0d944001007030110581505000700c1c0c0c800c940c0c01540c0da02040b400403142d81c0d40c1a8880d0010507007610440e1042290004c1000f10b8022965100e0102e506104a05047e00100605540540b4240d0f005907842d001100000c460a002ca0344030f01d030912690001843c9001003d18200400c0c1007001c10301103010500c0b006844103000d580d2600e9104031240051050300041c1504d034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 465192913 1250 465191663 465191669
    0x807050327070e0a06030807150f0507050a0f020a0203030f090f030a05010b030d08011a0307051b0601080d090f121a1509130b04170909010e090d0807020c060d06 71
    0x200303044101c01c001001c000918508540640308010f04681c1e942d00040220b403020710002e44509420400d900014064000408100c8420200010b0340000340a02e542194021525070000c503034001240142182c21002008105074076100405014540d47d02003034584c000c2d9081252440c2c000308064102d0b66402c0844058a640507085440300e02d001d0400e40d02074250304071000e019018401c0000d040700d00c682006410782da00d001266a41d000c0c1000c9100d0a81c1c00105150100241031102c0d00e4010010b181d2142c1442c0c10000600c03195061012030780c1010420182036042c405030f00b504000c13014000b00e500701254188922040500c5540c1070268071401c000d021164000300c45003c11205a00601c0140300804098805c08141c2c0d491507010310f803090362280040e042250000025002503902900012031060810065003407100c0040415011007080e0001060b00c00c180041258440b01007001e40c1c400c0c00c040c6416020350411306400b0f91031350360151080f0f002d0000081d5524907104290008002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 465194163 1250 465192913 465192961
    0xd050306012007030308060108070518060d0213080706180905040c05031609151d180d020708011103060915220e010f0e07050409050a050d0c030206060a030308070503 73
    0x680e070402c402d402c3e202c910301d0008401140240c40858a40e500c1446003a01c03412858460501c6c000001c1c140c100400d020440959000303504001c4001a40d071540058628440050090803441c0e081811460420105802103810891402c45003000d68500d003000b0401c45580440000d5540c07114101152100080e42003560144500a9000003104500100742c04440c0e03002c500301711888582d165164544550b00c184a1074144441042c0c0195691803070b940d4101000e6030020403004007090354035051030b021301000009600300083c10002c6040070f01842c40c00c10f08800001d4075500c2e00a00041c10304c070300034181c0c100d0500c0e0380c020021a0f480f90705601c00c8160204403001805c2a05040d80d002410b42030440961079401e0042072010101d49000c5e00e0202c40d95400580b4510f03041c441403200030f2030306603010744c1e04d8440c0c002403402248041c0640c0c20101c01a6640700c1c0c1c5144182406480d0050151001c0d0040070103080c10030209511034903ca4100e102490866980d881707a00c0100400c820a11a04807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 465195413 1250 465194163 465194207
    0x1309091109070804031d0901180b030d0c1703092e0212180f0d050702060d15030b0c070812090a050f0708010c020105100515040305010504150b03030a020d05030601 72
    0x566403c81c038941d1003a4482d030b51745044810b003c4020520103003c0041581c0001450006104420754025803e90710001c903080098685441400a07141249d0f208120003c115922544014001d003c40351400d030001c07000c890380c42c500f0580a4641c3c0c0f004400000804003c03401600d004c84c0f03484a1035051810114907040d5210280f01c0c800d050902806e80d152645211025800c00882101040d464040a04203018200c4690b81041c107440035446600304a034008020441d0381c200350403034860348410440c0810112405d41c114900044d0964000d0041000100b00307025810019a05400704e500c5d102e480e40800000c0e4a03106031181c41d1007501c03a001005401141c1c0c6d003841d214000658081140c01510003806407010f01c00301a4220350042e40c00c1529402c128006011500b0070680310040144030030b402d14600707560b1f62961801c40e1350589048a103e85900c000b848000441d0045459149048000c0d628000712404060f5441a400306100d060101c0800000c0d46a0b02800c0d03c202525607120442d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 465196663 1250 465195413 465195421
    0xf03050d0e0306040203071a221505040e0619030503181906080105060307020a0b0702061e0105010e04050c040503010204030516060801060503010b0d060506160303050604021309091109 81
    0x2644400c5a5410080010440c1003951076500e40007039118082c80e0041d01410680f41031400c14480300c10011401c001d226820131189101040d0105440f0001c41c11269148002e400e0503806c2858680f401e030180c04004042c04280b1641541c0c000d11a044401282d4515506204140c111181c41d215032001e00140004540c08602c0c0e281c03000601c030035000445190b1124441c091500e1006103040c0a440001000317100140880e09002d00115040603c90044035215042030b5991014900121000401a0849000e00c46203288503040c0d844034842c5403c40400640c1082c1c0001c240702e100004c450311a07030700c4001140030301481d1303011100a0000a002595110703281c4c1041959108030207441c48880c100f1040c0000d03002c1c072910329a81a61100c0e91064910307440c05c0c81301415500000740080d0345a0340c03200001740d540d841500403c0c088852592158a80520f414060121640185020f01980c010444444c0d8034100f17401d0031301a2008c150f000100c3d01c0480c02e02c0c160005450340b0032908280034270240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 465197913 1250 465196663 465196673
    0x50d05010c03060b1e07060908220605031e180d09050f090103020f15040f060909051008100905010219090f1d04080c0f0d03050a0e07120204090201090f03 68
    0x21030300218440c0c03028052240c0e04c103003070280340c400c1125410745030300c40c0010700f811035000038003d000450003520003044e0b210041c0c540b94401c0c2e102d6550540842d00c0840c2e903081c401c86502e03210004011508092342913181100c00c0b404a01507040e1800d52400c81c00c00000c50244230242c00c880d0495401e0125441c42c1000d80d809081d01156010341c6100c2c4100600c0710107149445494103058030b902425802031820361500384006c1c2d00c000c1101c61035280050001040311900c14110600030222503855500d1603140c40204d808030388029010340140c00ba148024014040001841000c00e4010364000a1080050410500a02a10011414980c621400700042c150300804410980310001e40040015a403101d5040000300f410b44410012000e000006000c10b43c0e00004c0c01540d54030809071461500c0e40008a820090081850000701c4d5a8106020803212684101c0f01c039400160b0041c0740642c2403201c000c50320381005400070b11954803035036003800f10791040046000421084a00300c0d0825100c3c604 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 465199163 1250 465197913 465197921
    0x703200703151104081207140105090604060b041b120f0e030d0b03060708042004050a0911010306050a0510031523090106120b040b030a050307050f0a050615030106050d0501 76
    0x100c003002d58103140c04190302005080403541210211401402407582e2035019420f650046103040d1400103a41000e01c082030001e0113901d2181081030050702d0b03240f07071500d801021551540503050090380b82c030104000002d1880c9405203943d1042c2000740440180c420740780060840d4080d1146000d080a412400c1c980307000003c0c16807282042e1042c80710301c3c5968245943c4950464003000080e03c1c0d070001c04c003c11486c4c4042d111101ca00030403000c400188901090130b6820954145100c269290381c1d031750034004198a40d8400e600700b40317001d2140b0351a090000b0005045409a0f82c400c03445211034405241c069070044500000001030004c180d036803100c029020b0001380103448000154009503c1c07140c42d180c0003d0341a506c042c0c4506075070481403603a90004040e002019500283c1ea1610b5091a6030104510710b1282c1c828002169188410301d02141440004e00c07599100e03a0044400340001800403880c182d100728a880c20f0881e160f0f492001a014055a0340416044600b481c00c0d071042c8003040d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 465200413 1250 465199163 465199193
    0x3306070605010f080d1b1b143f190803071103090d030521010f03020a0e06060703050c0c09010f03110d0221030d110405130b060703200703 61
    0x420f070510700e0740c2c40740116101e43c0c1000701940000c15010410f05094241484a0071041c043c41944403403030b50b04c01200c0035419541c2c100320102900d03641c401c8050701e000100010310160710000c200b0007510346451401001640c0c103885410041c0d20b12103000545003000520584c9150f070704a403109a4190822409950040c0c0740c1000041c0800d09903000c1d0b40c0700004803116200c4c040c013007800c468040e40341112590031010302d40c0c00c00e450200394404071141c464125806010f2550240190502e5481004100782d0582d11881c0f18802200803c4101d40c0c0340800ea43d0141c0e00350414582d42d801284805041c0b6615000681e400308070000081007001240c81800b0542e88038150441d5000030250070070200611126000798002050000d00603505541d0282c00000c15030302c000c036400c0443c5a2450340a440d500e0304142c05010000c20100258944503001109a80031500104000c40420010850a226020000e818080700407903079000e412100402a100802900a4858032500c07032402ca0095a4000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 465201663 1250 465200413 465200429
    0x21009030209070c050c01201c0f03060b121003120314090c1f1101090f1106071e02060c03030f040c05180412020f030c0d080f330607060501 62
    0x2d0009071200e00400c00712007034540100050007841c45a0300116a1149101c2803403508078949800070300150400c0040003444a25004c4002c208541c2d010024252800801410105420000104607030030590f0304480e080110300c890000d240d90303495402e00720150103901c01020136800450394000d03a94942d00c0003002c10600e000810094561000c1c007981c40505420407a4040c030444400c0c0c40040021542880c425070380c0c18a080c9103120846100e0031608010010360f07540d11016203000c01c00946c2c00580c625880119142410f0044076100c00b40381c030382000499000e0824400002e415540e85905460000c1c5450b012607690307180469801300091400d0386c2c00c079a40c448900000c40c4a00e008841c01c0003162031a61180e4581d500c58913181c19138240d8205e2a81503024400c0c0c0d0000380c8100b40001d0842c1e84818009080b09940310400a000382e000030b00940c421081c420600c20781c054010001801e080c0780042d881d0b0600301c0c085a02c22010a402003984d80100005070601c1000141d8001c41c0c101c5a0300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 465202913 1250 465201663 465201679
    0x71206090e0606130b041a190b040b0708041a0c0f06070e060d060b04030515090105060609010503060102010621030e09090a0f050a050303180f0706080109090303090210090302 77
    0x58614681980d614165600c2160042c10000d1140c0c1011040240c008880d02404140d4882a10100b0107d410b5107843d4003040350200c90f521028141400100d030741100c800e0402648505d0003040034018011030161080380c0c400091044244260745007900c015200590b85941100e030742d00f04000990b071042442c840f46005200c0341c0c1ca4485008220355104040c2c680f680c907800712840e010003003641e012108129a9540d640400b0138241c4402d4080c0020b0f500c00c2e0001c0c1140407410070030081ca000014400036650b0704080812103c0d845a2041c1c071112402803e21940301d858500047c0d0240000350800d030781c00d540721001c1d420101c5500d00b00340b0959001351a2207003144460b205104107802d04903805482d59008508050018212101d884081c40c0100241c0c2c001c0d5800c1e5440505540c000d6522a00e015402c150b40805007006010203051081440002c10b5010f10705080a010000144543c11501d0b81e207041c403106042c000d170080fa401c01c3e4020100e20a5610426010b06002c03804d000c164094084 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 465204163 1250 465202913 465202919
    0x6050c09040b101209020a030c06020f0f0607090608180109030e12010b240706020a030c08060607050d110a06060905070f0c050303160e181609030c05060a1403071206 73
    0x4881ca46a02840e00c071355881c000700c0f414000c00c40203051204022a00081d0500c0c000000c500c402803c68054412903000c0c0c200c102c0007a80c0e6a140185281c1c3d440c50035002803061000c0d07a500101c01d2400c07982c180c10404451f6580f1049521440c2d80040c03005115402d00d001d990405900550b203090a207822600c1d020703a4030300c4803100e600301d40300d1008a90300540140003000c031100c1c0195a84061800c1a462503103031400558510040c0c3e08040c800101007070301c03280c1d00400c0d141c110b42c0311a44920281c40c40b9050036010344440d55074519698072201400f100001500800b0f10600c02c3e41d00e1b55800000038404103a85042410003424103c50100000c6c0c908904081103500c034490011489030088011801c54407230055201c03007080c0c480075660038481703c0c0350f5501e0350351154143c0035008412000100c0d01407403c210b0300b1405002560101d010031041c0003043c80026020182039042d6801a0b80550700c1d084c1643e400d80b024480c1c032901d0565003102204214a0a40c03200645410071507005092180c02e0f5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 465205413 1250 465204163 465204169
    0x5010b0a0903061a0618030c06120a050a0b0d0804150305010b1e0424020c0f0307170c030303040c060201060909020a060e180903070b1006080103030503070c06050c09040b 75
    0x40c8020050006051010030000b041c00c9030000714070785041102e004040e88120000900310790088041d0f000b04030103c144001145818448000290000d9600e00e00d01142a09507615080780240f40700c00969548000c40d46c8941d5503071042c0222103015015200d0700b4142c0c1400c81da00e030850f106203883c2641c01306844039694400d00031541200c4050030907508090100d003080281d1440d1030b00d1074a01040c180b10010f029001c450340c528182950070101c91803600b56401c02801c00070580d0205000350044800d5191355100003607040c040751203040c001c0d103001c42c01c00030a50401c3d101641c407075410320011040c04280104c3c042124104d4195800801078656500c52400a89080210181d0f11498641080141c580240c40001e0b4107080240744079502100c08080031907840054881d80455400461494208503542c10015044184404074240440c54844014a80c4205000040412401102040c01c1034003c00742d42d41440ea01040602c018500f82080903500d030002100d00c3c0c40b860800701e004410381 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 465206663 1250 465205413 465205417
    0x90c0a1805010f0609030311160906080d020a17180306090c1e030616030912022401030b01300b0621060612121201050a1502030706090305040305010c0f0305010b 71
    0x50403d40361603035086c0c519182070780d44003c3c08041310280d000b0340d1034014103140d490f85400090102c1e00c0002a20b6407c26810b54035060850f40e0041c203544c0401d840030013107507025842e41648005101c4655aa50032000141d4640c0f000d030b01d8540e0944103c506000f00c00401041c0c0d940c03100c10175520040da6900307038400b403481030820380c00320794254110704045155140703514141d01015a240c240880c1000c0389036101024a42035042e200d0050b003140f0f081007011601407804910300a40030340071075900c0d4155100d520900b081132045902c41d030300455800451102c4c0080b0b48c03129110f01c000d202c2e4000954207040040900407205a4443c080e00384109482c1524032040e00b18074410140204100c4d5601000d22036541550080701000b0321174001d0401e224081c1038024071500e05d0082d00000254580018001013007050b0300060381a1039011042080c86600006859003d030b04982d003c2604409400d082c0d840e445190000b901070350070828000c2540307400511781096600d4917a001c12051703988044a02c01c078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 465207913 1250 465206663 465206669
    0xe090114010e040305070303140703052202010e0904022d01080a020f03060f0102031c0b151c15030b090102070201020c0105040503070b0c01060b03101404090308040308090c0a1805010f 81
    0xb0080e100045004030344503d0180c203005209060024800030405440300342050210341803000030342c86004101c6401c8030001c4104881b10402000306c80c4101c264006010410001c501070301421501d400501950b0300c0a20051b80b00610a070b0040c0441c90200b07042100300b5081e214503020580500c0030440030106442120741080058042c40d007035440310010010305890ba204e0150442c032042c00117100b8014200b6400d00085010303540082d111400e4010701504600180c02940c1e0b81c5410312400f49245540d60701c3c1c0303600b0f0005030800180d480044000c1c603090241070b04003401070380d04030041000c01d4405500420b8868001d8003220720310400740004417500c0c45035014058058000c40c0c8104013501280010f030103110078400005c1030701e031b444480d241e0f559003044807075030340141c1000b50030440f501c6000140700340320000f941c0c20b21420681c5d80740603003512000751006041004080020380c0000050141d151200001040102520340c0c6454400c0344007414880f04400a01d044000542961081403810403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 465209163 1250 465207913 465207929
    0x4050619080c07171305041b03050c13030b0705070609060c021005041104021803030a5c100b1318030e060c0106120b0a0e0714030102130e09011401 65
    0x114142001e03240200d41002001403145100e01401081e180c0c4c41c1e019040750726440803048008023200c40700060907920094035915104200b08000c10081130880c90b0034058942054540303403580c541c42c0048901d8440c290020744003d192941d1441008003640005009809560031945851803402217002128010789000340644489186e400036400d00342c000c1c049801c0718440c5c0c00f0820311440042800c42e8081c4c1c4111001404011075019070104003000c0180c0218548070134038001090b802c012103070401800880d04042240301c000190b05c0b081c01c014485440111042c0c544135907490590310040c01d0010704861003603e089c60314000a039494401c0442800e41880c2800040000342c40680e00e002c001801c0f603030000010030002e4081c1400b4000d5400034080000e101412480780e05003240c0e0307580b0281003910420700704881c010ba100e0002403c5070554602c142170000510031000020b00a21500408045032040c414001841541d8507001611541c03c0c0b600a100c1c0300380d41141c0b5405030030309000c1e50303030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 465210413 1250 465209163 465209183
    0xc230c0103050606070b0112061404120c2405090706020a05150601110f030702040c1b331b08040201020717280320120f04050619080c07 60
    0x209584030350070003500500064000307841d000b00ca4951680481090b0041102c0340c00101c0a0300c08c000c01f40c4030b1045049980089a4440e04003551250303000c085080c102805c06c5150300c1c0480c24411880c00000110001e60708108090070204c0d00075014000880744015a4007078118002420350000c03810381c0e12940e100015140011001440d03656030540908068100030703085140c0d9a21030000c01011030751f03111100080d6242c022510420040d0341d003948440c4100000042855920011501c008080a03801003202181085003c50030b50b202029003100480c1c50a03032401c0c040e02c01072961100e22120384d07407000d941205010310002c2d6050113050b14004d0050380240002c01903c0b01c501a001501d55440c4103943e00903485080344e401002041d10070545241441c1008010950001c16150b290085902200205002d607690707245c9520364082101030810780041c00035420214002100c01a00b4000c020710b0303c900c040d6014140003443d2802c80740202c0c01500c04503012180c42800c1e21081503000a1041e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 465211663 1250 465210413 465210433
    0x8060a06180902030c0c010926090a060f0c0618020a0f0b0406080411151209060405030405040b0102030403020a06200c03030d020c0307060614040f060b07030513030f030c23 76
    0x1000a44c0300401d01041e4007410301c80c080e002d290038010742d07814074001c101c41c440c11441100810f00b994104034961003112010082c0781030030b4036489034010840701107080000005200940640e00c8003041d960003070449181405104040502c1c0200e140c5060003070b10241a01615100316004078140f138001c1c40d00c0b000c0309000401c100c0e0f1054414640c041d1141c501031245918103400700e81170560002c2c2d402d00c0e543c40400d21801152445211541c40307072010000305450304013502c40b0b40e00c0344540d0181c1c3d402951111441049a40200304a900640d0302030910b201641d50b442d80101b2101301c6016104464410b079445500009002551004141d4014090340c82c001c43c441c0044020750000f41003180781c1c0800d10054020030344030310a000042000c0c4d40507100700610042048121880c85103425401d07460004107000000140082d039829503494100b03070756540c10814400c803a01425500041640c20f814000d102015030280b00c004a4a10403884011090b030b1200074942ca161003a510042d0030703405440c1403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 465212913 1250 465211663 465211679
    0x4060e090c1204021903060204061d1302130503030409020304060b101d0409060203131203021218070305060901090201090f0e0a0c0e1c12030506150c03040506030708060a0618 77
    0x10b907800130700c010068002c0c501c0f6101310145a40c150350058520990100701000010b8000030307500440f030072807944401880954400901da1103004800000c0c4194003150150800300310414950213402e000382200c0d2a1b954402c0f82402030742c401c9600311480380c180041c0c3d4030f50707003480f0000404c1c90144d6110030000348450904440544110b04040b98030544030440100419414401103008000a14100304070f0159402e00c5558030120800210816204204226071031004c031120a401040310499840355400c40c5040b01c0c03810006810151141c050308041c09580f4605500c4240c81174400e0700e58127440d50303407068850181c0c02240302e04403505c0b801c00001151004c55900902c0f0220880c10207101040588000c2a241002d10711159443ca80c2c402940050104080104164424518043c0f0061074020b0105040c00c4500044102501010030080702100b000e2099501a020141400e9181d1038207010052908100341c1d01c0f14000c00d071802000c20b0417807041d0044290746405003614110603150000c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 465214163 1250 465212913 465212947
    0xc050c070e0705070f140c190605070f02060a26010b040303111e0706141905070507090513020906090705160c03050f010608150108070b070f06060b04060e090c 70
    0x15901007100400c01040040e0a035848940c0150140c60161444842c2004a602e0544075414a81c80b071003605c8e03548903400c07031a880b0344000e440321440c01a23180d034040d203805040703840701d680c0003035120502103140300200354403a2450156114840d0501010b08402c06240300040c02801089100501000140f011a00030382813069128a600c04a400c0002c0844002100501e490120000e5802030b503802c00c00ba81e4840741d00900801241e0102e860207011008100c2c1c1c1c03183c440852014444003141410500405210340801407501c0d8905201354500030706141c000c00c0041c00d00320f102e10403a074040703809800c0c212002c0d841103480b034071035070300c0c011204038991040503818100302c0d05480c108502000186e41407145041c0508402c001103400750800c03909034180310b10000038041c517092a90042042510002d2a4012142d01d800201d42e2640b560401c1c1400316030520000e003285080c000001240320403075000304211600782c0d40b60308801c000c100030841110010380342d44000910030f010110402290b880 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 465215413 1250 465214163 465214171
    0x711070521011a01110309030c190b160309120b010303050c010f021c0506221a060720060f1b0f060a050906070806030312150d150c050c070e 62
    0x4108101e519100780303003500d0351044038901c14000c819103000c0c1941c00001101042e0600d0700a14204120f4201081d9208080082c942c80341d0b5500120702400181d01360204042c00031108942d64915600b420012545600300041b0001003c01000083c401c0c11034030828075041c1e0203c600065030b46507483c1259180c00080b40300c4813170356a900d0445004d0b0624401800451f007050720418142c10354243c00c00880d10300800c144c2c0201e2003018440d07504c0c81d2031140340c1c2070b404400d81c1c0001c0c440d00d00c90858008050320040f10b138001c100083d00400380a65500b0551a220015541080e00283c40050184034021802e40c40d80071401030110b0030528911282500110440c3e0088030002c041004141d0b10300b0340282d130101000c96580043c07100e952400d00000c4d900140c00d06101e0020b040c00c0012a07500c4c400c81003801142c6c40c410010030402c650801601c1c0c00361034020890f2001d81c6441c144130300614118a41040618a0403140c080110b00520075a042081503902070400d242c0780103440381170312500030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 465216663 1250 465215413 465215449
    0x51c0e0a081e030c0a0b0a0608010b03060c0a09120b04021201020c190f05121c1b080601090e07021e01060b04030308090106090f06080d02010516110c0d030e010807110705 75
    0x1c0140741344010704000031280c480c02441c540c1103508201140c02d08550690700314450300c0c0d0402c80068216140092100d13044203403541020b41e00ca442e03a804440a4466070415228580503005440500124204c00b5019600032500034898117892000b840c00c0b0304c80c1460b003101d65002403034681585801e010300f07111828001c000140c0b60030784598465080501d0b02090b04a13110010441b030f92888070152405143e104071800420072442c8040e0a9040403a11030501400c00c00701000040040e44a070304003000a042c1076060f4201c500305104065200c501c84401a181c5100c1e90411803400304e07050060a0454094008080c600350440c0ca040394620402000314010359260840040d0103007461107018001c58442800041c85418014014141014440b4400c11607040005100c1002e165071500c108040b004c0c2481802070b100d585d2042d062404c81d490840d40074800500880900d03400041018000e50240d0312240d440c0d035410400c0d1107100c51204449100e0388040320a11640c10300c030030708041e060b10720 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 465217913 1250 465216663 465216667
    0x402010801050d06150f1e050108010504050a0f09060e0d03050402060d0509070f061d010c0308150312131a0a0c031b021c030206100305030706050c07051c0e0a081e03 73
    0x1724124800c200555202299694040000f000880c03074142e0203a0140700c80b4190940701c140f6142c002016908180500e038807603582c80c4003199000c8250b901240b1440040c0038140003c0b05d15041190003001400c1801080c1d004110f19400d82c94400d2284a204030b50082c200307030038100030301e50007401060024441070715489900c10100d81409010140001003015694066a4081140507124000c940c4104c40307051218034602100000c1d040366041d03030b004180e820985070b13500350900001e250480010014207807401c0068000c0c140e83e66403100744d054500c00a503c061800003548001c98a02c2004201030000c0c20307420760100024843d182c0340742054081c6450b00c040d175101d40c0004400f10003a001c3e40c4020030030265101d00705034060041a070b1012400601880f06440c507218075484c0c0c81101001811643e6070340c0080d4207103043c802910b50454001c0111840c0510303038038070720034040b10a01c0304c140401c1024000c90041c0c80d0124040e01030303c1d215009042a100c41e003004000701107000c1c203140c03094041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 465219163 1250 465217913 465217931
    0xc08010204180914071814090307031805040c0302070b06030d020a06050604141608010e01080a1403070602120f0105040c30020c011a100906180e0c071a0402010801050d06 75
    0x800c222090107001d8805c20314080944500811049480106e1603401d035601940411200f00d23404026a880c094041c03d21002d504114803c21805400903005981e0080c6410700005646034180d001d0702d415841210030846030b80f201020181c3d1542514161401640403065040009000f80c000d25080000584040741101805060703040d18030040f2800900300b48541c455280c0030b903101ca038940c01400386444a880e50f50501d980141c0311030790310401404070340800103a15010310040084600e6190800c1085448e05140c0088d6500f20b24291500b0a40c25041000030820b483c041c41107811041503a02c03184640203042c20003905080b94070303200f1450210410b4041c08104a1400207081044000000061050080c0000703034903014280e00d02e9005a5180b00900d04003a040410202550708500301140c5411404c520b1001d562180e0700401d04182814040c001e0000d03103103003d0007482c2d01c500240c284103446519050060581100e0190004e40c0101c010032041c01c00d014455203880c01100e0128081c42 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 465220413 1250 465219163 465219203
    0x9190e0105040b0403020114010b0412050c040203011202010f2a05031c0b040c08060d1403040b12072d03180813051503150f1305090a0c080102041809 66
    0xc81d0190f0f036109060302080109075080c4520041c201020701000c0340fa50500600121031301031800b5901c03a16141a05103814003a04201441201100920540d641c1d80c440740004c06060070171130101c0c003003a1800c012030241402905c0102208408208103101c004a5807100101d0104104080e00c40b804200202d034095403401c000d00d07200303004440000c40d1070510b40090004075809104880d003007001d12814400240d40740c068020019410400c440005c6030f1810043e82148181d034450705019000045204403410444041c03442500c0e00d49881522940c0c00c45121040848114a813140e074500d140d98941a50080c0d0200c040c0301c800f142c0c640711a1032a035650280651002800d62080728000800f0031591804a500009200d0380000d0340f070031401c100303804400e20308014440a2003a0014048119591940c101c80c0c40d400606810a2280e410070a250759100c100c416800e4401002e040008103584905008640c2104d204600c000b8200210b081404010001c003541100d503003c00e165803400c010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 465221663 1250 465220413 465220421
    0x50a09051809060c04050d06020304061119021c0509040c02030d06090e06070e0901090e10091505010b04080714120a12020622140709050109090c0504050609190e01 72
    0x4050442a403101d00b4a800720700d141480041c01100b0040d0308100500c526215120700544047d1700050258036500d0f146001c5001c2c003e4000940406003020400d2102484020384040c101211502521002104031600240c01d060030302c002000310304200401221400c1c190720003200c1211503c10f032400c2031421001d000c1034a02503441000f00365107607160100303500d60920506800110714103011701450003140114800b5a4144104840207548850382c50b003201c4240300091400506200801050185103032845d0041c1c4161040060140b92000102c5d00c140306404550954284100906d0000d2602901c401400b0481c10140e030401d90440380e0030000c0307004100b403044280c880e00c4000c0c00300700019002894610028404510f255406d40c0b0206105200181f103840c107500080c0c01d81c42110803481441c070b002c1442c1c2c00602c245140030000a4840249d512410030640b02c0c94902031541d940c1e90401c829104140c6069a105555401040c1c203a0980b1104c102601000d0340f02190166408416a00311 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 465222913 1250 465221663 465221689
    0xc0604060906090e07080f04061b0903120206040c0b090f0402041d0c04050607060c0516050c150c0c010305180a031218030804020405070203091903030924050a0905 72
    0x407a00d004418000b0640040449000d80000c03103910040d881d1841c0f00900d909406084440c504102c2c40c04542408100c1d00810f07480400c11440c2d05801188032401060f03c6103d100c140c0345a14528401e004191000c04c40038099034201030000901c504000a0075125400705121784e5028001407004080780d00d4900260000707040c844034410201c00245000400c070301000f072147c081c542040005200c0f942e108810740340a140c0181001460041903001590a41f00359641c005a90382c4036240e650800c103000a20f48986c00c1c050301c007410402220100081c40e40102c0c40d503070354140c0001d0b01b0040154400d511a07680443c889a84100d0550300c940e4090a0a05545040d40000c140f80742403e8614441c0c06212200c04a803003203080e0410340754a00500340301002d00028440c076203d03008501c220b40700b0401c2d542e08903c0144070f03000f009404000c52a40070680c0c0b00403070105e1240c02d00000c031507030041c140b8055400844541111180b1105080b01d06074050b12861050080003500454940c90f424012521 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 465224163 1250 465222913 465222917
    0x10e0603150d122712081c05070909020f03010509040c030c0308030105030601060e090609041401021c0507020a0308130201030f0e012c0a0609060b03060f0703050112020a170c060406 80
    0x442c007101c04010100150444000300b250620703000200d0f40b030038100d2107404440602c0c04146501d174261400740c2e024414042041c032031600880300c003642199030742c0c0a64013840311511190702c1e140c0d80700701c036a041c0d001d208032502e000310302400104114203214070010340c06031203403188820081d241c0d0303038041c0450304d90740090f99010b9005c030040c01507050411425002d090384e802c10b000c2002403030000502203400104800d0083d503604c000300b41001181c0031301107400800304000755211210030901a480c42c01c40307502d290700d05007844003080034680041200e0f440107405585140c1c25aa0b2030420741d9085060b5034049041603950000003030400a144a10070011601000124069001c1405500a2003208000200004012110740d80503040003803c54850340e4400c0000c1a032442d9030a01100900703100401a0700b60140c00108086001480d00302849100f81d500c0400c050b0b44c8826039602e0780041500025005944050300b0b000388454000d205280d094800c0894581c00c03003040100301950030503480140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 465225413 1250 465224163 465224183
    0x1e060e0f070b1218070503010c050a0e09150d1a070903121e110712030e121b04020c16030804080d030209061e1306210b010e0603150d 59
    0x18285005210700d030002c040c2124090300b0702c140c90000d095500310181c0003040040b200200344941590a0001c0b000500009000704441054400050429402141040b0005552403c02000c601d00b0b45820340c0100b01a4211000081400003444141201410166560300c950302c07219900305034880619100e03580c1740e0742d003441492031891700d01c078440c0c1c01c940c110041c005592951400e5802900c0008448151450245001824824683d06066a82d0000300810705d1525501043c150000c90074500108141c2d011450101a001000d4681b880c1450415034404021980720141ca001d401901700421410f0a603040b0003191000c0d0031402902e5802142c414801003000c0102640a01c5036288115a6080961506030f913500084ca0798820500175603001c3c0ca035141480f80005181094511400c42030501207903854441c440030b0001030302c810015002200112031030038007160340d004410040740d068580d056688022010000b60742c100800040305901a08814080c6a4800b50100304090040170055 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 465226663 1250 465225413 465225433
    0x812060315160305073603020604090b090709060c03050a1e08040203060901090308010b0d14070c061503030c02090c090604060302030a0b0a0806010b0309011103150103050a181e060e 80
    0x3d0240d41000308144203114032000c145540c1c1c00411003d55600748412200060903140d6031030007182942e03682001e500b008001c030b0b0120762100542e0140b06c0e8200300300e403411070986d50079808440c21542d500440c0001aa640c40c05d50021b8051009021055118205071500d03119103240006540503002488000880316000d10040d0300b4144011038110404200a0207080da040e10302a249900601c00c840c508200000d200501080c550301a11004420380c84a81c4030307003032010004102034100101910004d1400b82200075000030010058126a03050300c40114541ca00d808001c400f8034000c042640c01d64080100042a6480d40000c20260900b40c0303005889050101d428421198500380e05802845801c10a110b40c00b0001400f90449030107483c002d07a03903550344c090075001d082030181003c9100c40120601020004510800c407101c80280e030300f0042a900c0108401c19507030340882c0080d03c454088110801300d10074401000c0c0704182c0d101500041c403c142d48107000c4075105001c0260b5070300260150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 465227913 1250 465226663 465226667
    0x3020d060b1005130e22050a140105010e01051e0301020d0f1404051914010c0c021207050f1201020705060c04180207120302070f15020c010e0703081206031516 70
    0x3000719030b900e1500710b0030300401180c1d2804082c0c40f8001c25143c0e10b01c2c040054408115226452980c40d5294004801c60b82c2c1417410503610080441c00b152142c0c07101c15800001541445064100c59466640c584540d1a01040c8400e002088182c0080840c0101c008074050f102400201030809003d0750004ea000a02441c02003168500308100d402d5501810074800440d43c006184001c50603118841400350607685010030785c200d00c1ca6142c81c801c1d4208040c4401d5140c005140d0030485e80251010924482640056901ca1600340246507100c9014185002541807404140c84114088400149400e02540321140f500340c04890550384507000003028800540f040d20000c4480441140c15030400881b0354810505c00f0390920f4003000c260b8041080340600600900510041303410440f0445404516203081d0041e60180485682075070030114110b601000020310f9200710707034100c0031160524192072007840100c078024150540c140b19039400400452000d0390701074029401504005806684643c0c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 465229163 1250 465227913 465227929
    0x303060f0a0f03110d0507030606060f030504050607050313060e0124080a020402180d052a01050409050703020f0c010606080703050402010c0210050c0a060603050c0a0305100b03030403020d060b 85
    0x803080c020502940d0401400075054000340075241d001c000a080702d1100c6000c12001085504043e00b50300c1840b8001083c0002c1e540080300b03507240e030354070300c03180741940d5105406848c420344000b0015803004000a06080c402d02c061070300a459149009a9040952901400c0e68840c0d00202da16035514003080441c0d240c004140c0a141001128900c80c062070011265103940c0a440048e000b941c000505140154481524041c030300c0d801801d42404121504225a8402c0380c599011010408410110994032190b0301461884205039526443d1074105045540500b4002e4511018141c0034445140142c0c4014041c00398213a51100004200f85003400c0246440340107010f40040c549000e0520000d41d0707228201ca00c1081d01500c9003045c0c2041c005040702c46214455140c15180110140b0780c0412100790060411640035804940014001004001c4820b2140c81300401c2d960001661070720700d494603040340e0040300d40101601e00700f0380e40e80c010821071503003002c04650180c0c0e50b5821075400c0c905051 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 465230413 1250 465229163 465229189
    0x1e12010e071a04061407060e060f150a06030207110a0605070b0705040b031503070312030b0a080d020a0308090f060a020301030b1305120c01020d0e071a070507050906030f010c02030306 81
    0xc01a100c06504925079101441103000d80d600b0070980174420401c04000000300c42107250700c0380d42000700e8070010620640300c01e01a6405403003003001201054000302d102c8004000e40c00014280c10250f80740800540080d40486011614000c640000700780c265500501d0800624032500d03407681c0c1d101c107071400c5240454000d060700b082c03110901080c0a102e10207000c1d242c2c0f0062100f50140e070b00000d05c0010340ba103d1507500042c04402c0807011250141c0c0e0580191091b00401c1d16000d02041c0c807034500caa12266003000510060340007030100700c0424071034281c0c10b4020341d03003400b51080c2c1030800203c5401c114040790b0320381e0301e00c2d0000010410480c0b1100080c0e8401c404a5443e103000c5601e0380e5240c0c8410030a07840420500010504d03040041d020f50459428507001703001000701c0c000680b1940d443e11500c2c8100100b0426111116440030341010450340740c1a8041c01520303a05040c00304014070030b080581031035050b104824114071039600904c02c0d5070300b1a04540045881e840c240d8100896400fa4030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 465231663 1250 465230413 465230429
    0x414010b1e0307110d050a090315090b070e0307060903050a03270e060a0e0f0f3103030c08010e190b03030a020705041512140307020d0f020418050307021e12010e07 72
    0x21403494016423084101e0140d0780c1c0158400340300701c508030805024114030440505061000020b100b9010303023080c1448070010040e0259014156240c0301560f400c0c2e0780344000341c680c1d000200b00c440064481d0070608612041d01660703040500503210b0494065046401c07102044102d1360500126143c0f4048100081c02c0e13000c8072031461f203042c0540d5844a4409000440c00354505030204c0c0011003a41c2d01d404010b00203d000104421041d01c0d02c04800c4200082500840d00d0b08a5842800307104000c21816104200c1e0000d0716030325041c68007a045903408000c1c0380e07040d0307603400c40801a590038401018451241e42c01800b0460801c0c0400c01103543d00f0700503400c5000e58000c2085400781e0003000400568001800640002685050710b0441c80b422400941c00110f200c01c4008000c03600300f401043d94000c2d50b040141c900c00f2003c0760b525100000b80070f05154801cac060200140750841844d8410720381e1107640310231503000601141001002904880c81c80e51205074034040180100032220040204e2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 465232913 1250 465231663 465231667
    0x70b01050603041e0203190f15051317130b19230702120a150c0315050f0406031415060f1014071a070206060414010b1e0307110d05 58
    0xba035650462030313401141e000010901050341002e650b000e1080004000300300081600600091821a441040d0f40c2d0b01110201024a0f0300005d8120600c01c1c141f0aa030a11352040504105444285c0d41d110100030300000302e20708009408000201009a0004003200714640742c840710003440d149200c0070307040151010441d0813040780b46042c009102e0309410254072a03d20307980340500c0c00401c070644c0c500030b204802e034400c0d410440d0401040021340341140d00e40240811446404180850945100b11508452250f0a0406000b9450103146040c0314217401440041c00c65902d580308003400403014285020780d0420001d10350111315001e0050380c0301c902200c0600189000c03c0028014400001d6a1410085408070700c80e02105d40008540180350044200d4246d9520440c4444194100b00c40070030050080c20003280d07150500340107003015441600414510b60b0308000341111300b600b12510380004240010804046a60351800031405425266104030300308202403003a070b15003492914154104202 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 465234163 1250 465232913 465232921
    0x22b0e06060f0d12080403020d09030f03080c16030e0411040506030a0203070908010e0a1703070c0624180b011b08030a0b1306050f010207031707031107030305070b01050603 76
    0x46512a4014802c40781520026a200b0100c0c00d0b45501010050500421a0901100d540c20800c0a8400c5210380d0846064540414046414128a2000400ca801c01b0380d4107400207802042c1c0168495040c417185130800d402c1c4081c01e030307000300d104034107401041e4021b4804400741000c0c003c0c9907c01c41100030032481c00c2d1924020424a01c0003d001200e41d59021012604080c4240301b0b5000a000740c20092118100e18490181c461328008000c0f0390000c144046107596488100030740348595400c6c2c86008a032401030305c4120181a454200c500c101034011264002d04070802c05000c007070081624005d4036110005050022590301102c110b0600a08100d120510504e1120816070141c0c03240490380c4a031202024031001d000400c40031588950f2982501e903123003250f54083c404440c0e00b210040c500542003001a40c441a003800042d02501d1031501d1249080d554000034800588a480c01e81d030400c850719241401c2540541080f0001140001c8840601881407441405000700325041455410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 465235413 1250 465234163 465234191
    0x10030c0801140d02060409020d0518100c11070b0c060114060f0703031e090203010c111504170307081b040f180b04060f0503010e070302010e09100801022b 68
    0x50501c02c241e400e4400801c1c894103501c9242c0d1050304260f000c2c00041e00e460b101c0311114007941209002079070303941c40c1c100000e980525100c0c804640d00381c21713405401072684621030031001e000034219103410b001a001c004d400703100d41000098000c00968940607118805000c2c00c13814810103a02416802140b0810000ca60380c40104882c1150b810454103544c4036003903c1d041c1e000c0c019480460340da2004070000114a010940c0240c0c00686c400c5008002d0041c43d46e00a03074412080c1c0200b5140f030350002c01180e140440004c5480c3d00240240ca41d01c40d01c1140080da400707503902c1122000000781d51242840688030300150405180d4130400e020380d0520f0f0038590301c42520441480381d00008810140001021a9a58004040d40802130b0083c4031203074440409400d04055481103d0196182840c443c003480320102d4040142e903416075a007444444000304124000c80043c0090411032010500061145400d00c0108000d10a007080e562140d51001c082400341c0f46210940010a81016054140300c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 465236663 1250 465235413 465235427
    0x312032d01030c061d0306100501020607170a0902040e03070f05060115360e0610090e0a050c19020a17070309090e0a080d051f0602060601140705010c0c0210030c 71
    0x80d025280860b00f03080712281032240805e0740310038140c150060100340720340314580d42c0c4144140c42080c2c08903049511014421514850810704800d020054880403503200d1100303401050700750303000070800f20382e80003c0f030300603425984280011260b100f04162500c0405c00c0520071170f40142641c2031008141548501d000e000d1203c104080090b054000e80110403a2004041d4408800344864000762260b4a4030350300d0303182c0300059650728450fa44402420100f5486066548182d58016000340c289442e000045005404060181808080248102c0ea0141610540140e20003010380c01002c3c221000d0a00c0001941c00200f06c1019030300400184010940000701c1c14112445a6000191210300c411214141501d51030020030001d00040c0e0501c141355541c2225005180780381d48000d0380ca0450480c914024a94411200542c203c08006007a642c052040043c941e0922448540b410303a0700e82e60b16086540418051000c00d102606c1c007415402c03c08030350390392410681000c00000c0400007000c2c1c556 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 465237913 1250 465236663 465236669
    0x812040c0b03041a0417120106090b0c1e01200d0b1e0d020102031b071e0302031903030609020703021b01030b30070f17010207020607060203060312032d01030c 70
    0x1546080d00483c00300400580c00c8100407503c240b06c682c4a842d1189000101d1000307200715000038030b80d94404038400340d140d03049800c1c845510004240013443d440c003990180d46035481600041d580c0700b44009140c400382ca9545640002c0c8158030703646d505200f080d0000c81c0c0c00b0100701c174000c4071002084c1c7c0c0d032341800440b80c03000680c5c1100d074813806400e50b200403455440f0740343d64040d0101b0340032905280040001490f0064500002c09660924250210f41e000c03140c5901c0007039803660014250452140c029140100d0701070081c940030070050b803a00e503c1c0f01a039200300c2c000c0300140d0004407106503003500b40c007940d5407004003464140301540da154000f41d100520032a0000302c4090700240302c440d41c401807001000d0b80604d1016507000c5c95440c001c0c082140318920a0b0401002011403160320702c0010b01c00c07204601d46c010911400d021702c503200c2a000b0b410045c2102d801d4459000c180c24141020000395101b08145030341c0c21641c20150a0b00406820424114102c10b4050320062001405800ca85425 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 465239163 1250 465237913 465237953
    0x3040803090f0d0f0e09090622080a080109050612100e16060305010503060a060602030a0e01180902090a090b0d110d0b040b01031403030f06010311070812040c0b0304 73
    0x60340c5440c0c01103810a036903042c0c4400e851196680320060283c001c0c1c0003641042c0d254035055a4224128144140307642c046441c42865004440015280741030030300140362089580d080746c1070600c40307a5904034042d405244014042440c1d030004005684050040580c401e2054420700228060144c420340d0b075600b000303010702c0c1007511801082000e030810001e01c64a0000c07038034044100c550721000039000344001e0041c180070f802080c0000d07800c06500d000b448200c50345a802545400080c200460707055817001010b030704100072a800c121660181c4e00c2c9a00207050b940a0060707568203c00200148030200c3e034441004642440c11000c031581d0354014a8074190303000099a40102ca003940041e00341044428000c19555080c028001800403c4188a05982c8105808100300300ca91407081d6590208035111007402040000042c5103511a4110194407240c60060a007081c030b09a94000701c80e007055961082d10703c4a1410401409501c11030940140051710501e49035003000d032140851641ca9a0350125 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 465240413 1250 465239163 465239167
    0x90f170a030518041104060f0503190b1804060522020312030c0721030b06030f2a0c01020702030c01180e091c020c03161503050c0d06121214030408 65
    0x51001012109504600002441040201c0c18034503405051b401c24000e11001802c43c070b000341519401007089034065000c0a0103000c00034013904041c0003034080d00c001c164010380700b40e00b2042c5d1841d116041e140160301c120b0001ca16840c226400740030f010502c0402e100450300200041001d178401080e1f0524081030300030f01031b40d01da0320508101c03000e104003440200a65440c0c03007004a04642e0101c0801c10001694007070250355960010010f40c0d0000b074030b00e4450310300440701007034191b04064404c0d20845c10140540808080301204000c054002c0c4030b500055940005500c170441c9402d005244070100242400002514001d2000043c0c21140c0100e1007204005008520801000c200c0c00c0350818141d117a0104001242000039100c1e41c2044038640039100300e81040f4507100d003005003901030f9800c07448070010340401100308402410300a0b02e8627603422400c204504a401d000d020300b1000c0d1030b15001c1c00110520038a0060f1403401071319040b000b04040011070098406c4240d08072600181c1040c2210b1b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 465241663 1250 465240413 465240427
    0x50604092c030c0601050405152103030108070509060301060f051302070c06090e0f071b0204090f080712030e03030a022104200307081903110706090f170a0305 70
    0x803078203040649007214030340d2010560740c0d400c1c40c000000745190200c06054031001c0c1d0365842400180c88042da001030200c8803500a103034081c10031940c0038036040400b0001c00d10100464070702c18199402a01f1983c103d41080c403080c002d03410722854203130f04400143c00800c0340c10326210075200c40a00c2c6001d0380e031203180308501c911a582420f030140c8041641128038800b0341e9544910240c006e5185104400400940c03000044651007002c03102c52150300c6903100c180c1265440e407105105a41364000490740651344018290101c2c10800860100500c90070140b40e0302c0c0420700300030807020820811002054202800600000340c0401a69040601c5074009600c030340c4000c030f442402d400859070f920380720080c903c100024402c20682480f84004c6040c0300c1044c60240b001416182c5400d401110803982c445134510038a2031070000c4c0c0300411406450612514005112143e080134400e0340000b00007a4050018880b4500f051244001000380e002c220b018045402d1449480c4e9451400242c140103001c1240b07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 465242913 1250 465241663 465241691
    0x90405040807150204170d0c121211180a150806060714160b07050327030604050c0415140d052d010b06030105061801030603020618120705060409 64
    0x1030b800c000d9000442d021814035003034100000390030a10802d0080a145070080e22030711000b05d15001c3d20441c40e602c1612070301d000c2c0c039081440b200e5035496204110030040d071059004418481d00b060f03100070201445e5615041c10640d6218545c04420921a12000030100f10300c4075264046020b00d062410316040170740e180400a000d038000c0c02409000c8040e181850307000c030600070545860454280c0c241102c06911003401130000d01449000402650082105551601000f0f00210707031a502c920080b03410700d2114000c0ba040800c1550101d80070ba10401d05508146418040c0c601d080030f401a068400c1440e1042ca4488031081d502043d00404400c03100400303115040c03003a914140c6001954103110b030070b04504208207141071030340c40003654a80b0240c00c16a14000c0e0480b170403214020f0602e8103000702828150104024110483c2c189555800d00000607203130301000d00300100c0181c1c9c80c04800c031541c4040c0100d0841c0ca01c01e1070001d40007120140455a12001560286c404007800000e007aa403420203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 465244163 1250 465242913 465242917
    0x30c0c0907050f2709180709020a020c120109020301110d060b0702010c06020d200403020a0b03060f060f160c0e0a05060105030a0b01020a05031614010501030302070303080c12090d0e03120904050408 87
    0x3655070800e4001c41005000140300a10002c6ca80081c01250b0340d2950b00c22002041380102180e001c010303040440304e510580340034003200b0b904001072000040e80e102e03141d00007421100e11102c04140c40401241c1808611108d20981c001014403d051a01d4410a940000c00d000c0420b2001031030554085400190721605500403801b05c84981c5549410354010a4004041c1d001880100d106d00f8442002107110030400096034060705018044413140403106081081c41c0c0c1011a06510800080c850305451071030514074210014001e40450340d480742095440b0002c010010200f42403107040c181840226640007046a602403600c03000058210040c00040f400d114034000060400e10000c40c1c001c182c40a02031040908900c40c080411400c40624001030980d0700910020740541c111341400c202003030095042d50741c044030141c1c05524000c00440041c00c1182c0c01d0300d01c0b0303032564442c8000c107400769001005012042030450007440e10a103a035951030360278404c02034107131f00413500e48000c1000c00c00c040c01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 465245413 1250 465244163 465244237
    0x3120c030f060b040945061b12140f06030304030b010e061206100b0711030d030c0201050a060b070f06020c03070f050606010c0f060507050408030c0c0907050f 70
    0xa03080c00b000e682c407109000719030040d0065005003850414549002c01c0d910303442c4c110020b400900748031304c400003040500344420310166901000025414420001d01c1030712500d0b0700780728074010081007512403410041c102c03d001a000c0809a02d01001c0760b0342212001080c035442803079004a40307440c0d40d81c100840d085005a6200408603903824001048845042c0a0306200b0b2500ba504078500030106420b0341d698110955038134a030f218904205004021501c4011301c0b10758011076500100000b1400842c2c6408400c01d40840002e50302e15690248030390a010f61a0014400700b81400030a00b040300d40340c800e11509000802d440007040702340041001540646604d1083c81c000e13039898100078200044920715602084880d1b00404001800c558001c1e00c040308480c1c0c0140721040061169620340f0b00074480900b804060120500c0000303000003040006001244440c0043c1c20120403a405220700400040c0185007840000d0041c048001c6204040d0790340a40c0010740e100b2050000d4071908a2045499 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 465246663 1250 465245413 465245441
    0x602101e0606050d05060402160b0a02041502030706060b0a05090105090a030516080f0105130f020102010603023a02150a0c08070b1801050f01170f06041407060c03120c03 75
    0x9000100e0a803c0340292a1001c030704203080c01030b5a02c2c901000100e101d108000c4600540030400480840d0f201604540c1c0212601c01c0189401c0e100e007401c4089408020783c003030041e400010000c0420241c0e024070300040c414056074a042001d092800380076400388211403410050003040221042d80e031082400f0045d0b400000f503644946045005040300c0301c05026a0441e48a001c0c400c041c019014810f040c81100d10744032a60088049e681c0c0c0100100680d54282c2c115901d503000031000d40d035000070100b01c035040020703a0560744103103090841070178500d450740006202c800c440c0c9001680303d07844526011601c4508039541d40c000c442094403014146030024150840104080c0c080100c0c010b000c0b070240319919082c0c00f16201c0c0560860070384074100c508082ca2031a100042085813089039507582214404c80035105e00c80381c40394149241510403202540e0110725481700c00d480341e0090000c080603280300e14002901c5201c644002d0316402c000260403010603550744440342a17034805d510150400c0618 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 465247913 1250 465246663 465246671
    0x6050109090c0605120c030402040209031515010215060103020c070803210603010b0d02090a020d11040603050f2a0c0a0b090c0f0901180b10030c080f010602101e 71
    0x34140d00d8005107010031040300ca480c242d4002140d210301410a6940d42c207007032800314200d03070345107881e142e81c50304060710890300702c0e0b0248072040e080d580038080407041c06245002c0311204d140c000c4c0d0381411814400761140c107640000030a0000c0c00c0140b80d0842d4015400e08000d40c1da20321401909240c01503540c4400864000418000301e25140341c1c80c92460b641c490300c0f000c003036506c4410425080760000c1d0350003684038103291403602c01414031002441c0e12440400d4014100307031518004800361400c21083d1114000e00040a004d00c41c1c052050581010004060020514082d8680007410007480e1140c041c408203505c4043ea1083d4903000c80b01140400000c0e150340801601d000340d00c0205c10784804405000b0040b0403e21401d0001c0d1422018400804565040e40707840c2030138a240c03010211045003580ca1740f0108003640c480c400900350800243c1c1d000a110480e541c1c002b0034040b006000403c0008200c4010048689c0c001610142400005d500080e0211210007000c1000b0400c5031005440d820 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 465249163 1250 465247913 465247919
    0xa060807140f151c0605011d1302070b010906060c08030f1510020610080c100e03121903060e0f0402041a040606121a010c0b070e130c030b0406081c0903060501 70
    0x703520080c001c0c81130424003a04030b1950040399102514024042d8a001841c00c0c0d040341b03030362000e11403d45c81c0c00c1809030140002d908926081c10682e44000c5060b40c0a121180040101c100903200d000024000e51a0580714a0b5995946511521010f0140102c2e80c400001003490007a91618a0380070000023001125030f014254406034464108541ba10101e000340301c400200ca01c00440e0136481d02030005c10303034103d030b10390640c041d02c02e2420b0300c11032601445000119410b2078400d0f00240004c21868404410303189a85100a0507100e8581102032664510700611110b1520a00b0450304103504031008204503a108110700c0c103140d2054009588141032200000d00c0320b4014507a0301c1c482900f14010300c10491000c814405100d00103204900250300741962a0118454000351500940d452605000305506040000c120090410f0300c0121260340c0c0514542060f0944614058408192001e20205251421280e00c0d503504080c034180d40250054100a401d12800303d0201541e4080020403403561 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 465250413 1250 465249163 465249199
    0xa0e0d200604050c01210c09150e1509030102120c19111b0a15030204050a05010e0901050f12031204020312070503031303030e010509150a060807140f 66
    0x2200e1022040160000c8050450314202286041c4500d40003802890380c03120303000c011a20100c03e410000c2c01703041c002030020200742d661300441e03400041c6e90392508610f80c10320401210454068010030148690008000d0f2140c40701108085054a107404040e00c4003d600082070180c421040b003080c50304152400c021502094102400c144805803c00c18003580740708005848800880c56004040d031301003101c0c10580d0600c40c100410609000c6c03c16584182e507140b410400407211000d0201294000c00c0078000c2c1c0c02c0402c4007034020502481e04034511041140458840c00041c0141d6026600b8104001900d841c0c0080c800d0007041c0c0300c02101c1c2c0c0d440c4040e2200e0403810f4203441c100c0c13190144012080d074624a15083e00c030b000740c001014519684400c400c0b0400710014040c11400d154545000d080c00d031000380f0505100b0640440688400c00b0982c0e03910410900013040c034845140707400d41c01d0144c0340000030702c44140d50502c4d4601020788420303000600442d08000b01d19502206600ca0780c43d03210 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 465251663 1250 465250413 465250427
    0x70e040c3b040b030307152028120b030c0604120b131e0302120307030b040b030f07180b1005180109060f08130c0801021c06120201080a0e0d 62
    0x503611007420349090300800410041d0746400025507410b40c002d00c40100420000002a142c080b520300b00017485080e4100710f18050800d09094103d91003000c100307100455030440038410340c040007485084100b00c44460141c109414407840801d95035840c103070044541c50800c11002024001050651034a6031149001307200c401d10309003140c0102e801c002044148003000d01c40134045da8040b02c0e800228010414820240401d044107401718441d8107441014010000b0041d805203900c0d50780402d401c40c0e00c200f80000d80e095049054082e03400300229400361900403964106840e10240c05410b000607556102001e000201c4400d507200302d00303195040c0150b1b0084010095620224042c2000c1c01a040054455001611400700031620301c050800c0e007a88203080b116030140e0301d0700703510075420741ca62500c0e03107000c046130003031690380e035002850102c1002d201a8442494074040002d11245007003268024403072031050b000a040c4001600490030160094001c01d00254441c07044400780210b2510040a074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 465252913 1250 465251663 465251747
    0x201080403120e062e06080c0703091d0f280b0411120108191203090f0b01030c0f0e0103050d0c0309030f0c050103060b2b060512061b03070e040c 64
    0x40b11195921a217086020507500850300c69844028465849504800b0107500142c1c0881c00c001c01c40300c0124500c100c5100b02a41a50740400b28643c500e000600d408459001401155440e0400d0300100c442014000c5185910f082c00400400c2c5ca10862000c035024180c0380072051251580030400d009406000903a04d4100c0305120112180e8044410801c0300c1640300e454043c056044145c40c1e0001e0500a800c07020b50184100e0f0000c201d04015140d8052040702a002210595441d640c20032210000d008d60318094048050f004c00103503d150350f072564405010842c3c4d07041c441c0894050062501038000f00d0015508075180c900050301c035141601130b82e0800d009050110b4600540071610030140410b6502060b0050400d02150700c800c0c4038183c1405d46000c4d00c500940c2c680300301048640300c0c2803c00d801d4200503c01031015051607840303042c0c0b00400304114011000c084c4100000c25a0041c031340c41510606460000d03112140010403225802c1840082d401c08804441c0f2115a5600b07030a21001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 465254163 1250 465252913 465252961
    0x2411040e09010b0d1a070e0d050a111009120201020316150f0606021b0406170304090b04090b0c0f070b150307080c01050417010902101106010504090201080403120e06 73
    0x41e03140300040110b070910300c1a01518800c2c0c80741450341140c0e00700c1084d580000382c60074502e21f1070310800005602400040c00031100d58114502140030043c00b4181c0100891044514224654908c0300c01080c40d43c851040c400d2100407240c8100270759009100300c8940d8040502117181c0305915003040204c030310170fa003014401e2500d03020390324918041d2486414103456159015011143d00803c1c0340d4a070010140100394000d0b540c280c000781d10704484140c0c4003081020000b450312246040d880a04a030030004505001d10b0915045400140940944603400f18a11460075200c43c01c0300c412034014000d03442d005200000304014021040948440c10010000440480d00c641d911102042d07114140f41d44000e000c2002440188000c0a280ca812402c3c00c0d0300000010700e101441d00083c0c1c910581080c2c40e0081500421310100e1100c05000050140c5800d031400c0c4008000361340024000503008001600300820080a00801c070490707040180101e021000311081d5080030480c5440507403040d00003103c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 465255413 1250 465254163 465254171
    0x305060705130e071d0f1c060b040905030906310e1b03160c0816020111010b180603102406091505070c090504060911010c2411040e0901 60
    0x280f03a001d061801d44900c0b0503503201e000055092150414542c041401643e200482040744041520707050410100880c00c0001610703200c507142881e20407140c030020014051800c0c00100400b040c00001202c9807000107171140c603580c488002c0c048210306603a1240c60400c03462040000303203603001e602c0b0020640c0c407007a81c0c00801e5140c03080880384541a890030005094018400902100520b050075640c440c070508014100d0000b594039602994030100e54a035940c2d120b4040b40c015964060703101e46101519100800c000041d000010703c0e032150100c605220440c1d80c8001402e16102030214142991421509110300d10000c00119030310800c402001001c25182440001c101d0321074002101141c891000c040400ca801202c115070590250005848086000c0c20000e0318420900c945407103a07006010004068a0078030f404030400b6402100c1703a04009030081103401260f090032001407282c620010400420001c000d2410281aa0245a0380501d0000c500000c51a0302c27040110301c40d00156000300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 465256663 1250 465255413 465255419
    0x14220f0b040c0221130b030a0c0221071a070201050406050c090f06070314030f0103030306060f0203220909050f0114160819090503070b06010e130b0406030506070513 73
    0x1004a40e000d481d0320b00181e018110900440c4849003080302d0034001c2e480c006190845130544c0351112030302548003074034400d0000200504050180316040006a06102800c81c1d82010300c0503c02c1040d6884030481e207164001000001c202403446000c40040c0304038003544491501c0d10380a0f009210458043c0c17021400d240020b0030600c0120203d882141008054442c3e22024405000305030300842e108600f4041c1e800c0640c1d00025003500503510800000324500c1d00c960444c5001403d07120107520130018005900300c04000300d5004401c0c0c42042540307403020342c20008814105d44d2640d0495001111051620035044123201d00401c454034449031000003400a40e14030045900d810b481140c0c442003d480202c1c0580c801440f50912641100c043e6000310b540b8030503250102e045440c41c00e0201d4041e0700004004c401c0140d03191596500010900b0600340c3d201c40c0f0310103e00008542c1c401c5c040c4030b035640c04030340119685543c002409590014101e4006142191000d440ca0341300400188805000713500c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 465257913 1250 465256663 465256669
    0x30b1f060f0f1809020702040b0a120c081204090b0f040f1a060f0906130807060504060f111902060409020403030512160f111507091403070f14220f0b 66
    0x3001403c840110450341c014504000800207400940341260700c00e44500c90101c6a54400c0c04036001740503030102c07665824916241c07031801c02e036040d802509160001c9441c0c000c0d9544210503101155155413021406c07410901c0000d01c0e0449541c4060382c072928101c14460f00102c6a40080f070b140e0107151041c240202c2e010104400c5004624405c0b444400401810509040020290480d940300c8003010381210b4a640081d42402c030540c1082000550105040001c654844251481c90340e40303060140e003c00344d010f24107484840211060022040341e148403421512100100c6004104075602151119100d20700142254454402a04600081030108400c1c000e41070b04d040c000302507505e0300d000c0c41c14081c03000d40c1d500202e030340481c9450081018078811800600c20720381c0f155201e680e81880c15800e0842c05444c1501000d05036010b988204002d0080304007507001d2405842d40e00307640524401101d00040c0f00015940480e480c3c003c03032400c035078000254036000003444490141c01840003000c6035081c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 465259163 1250 465257913 465257927
    0x3101506030e03030a110f0f0a081f1403030c16080f070b0a081506030423120f070822030203120901050702120c0d030e1e0307030b1f060f0f 62
    0xc1c0b050b400030000b0904904150340040c4061014103600d9007007081c1c018060045420041e4107165803040011104070091388840c03851fa019a070000380c40c84d0740742d203030000e40380b40003890146240c44200e20f04041e205940820540700147c0103602190031245c03100307900000b0010b4070310404401b8400d801d1b409521000c040b80040c19903100d1f48026060620184007220321000c09821010520052448800c13652256401103115074010149031780f070282444880105450031071602c0c00d85070080e0400082c400c0450040341d444142d41c08186482d441d05080c0181d1510844000b4490001100d6100c0750500c01048840e0840b17000702d040e95506046d002c620241481120751860003d02d080059800510700400c8510400c040740003111140109080428040707041c038001900490082c20001c400740c5007696a00c21840d1264100000ca0810390002c250707141240e01005041901c4040060300c2074801394003003560b4545003103080301201c1d030300c100240c101d0100041540015295a07003004a050107054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 465260413 1250 465259163 465259181
    0x90603010c051c020405100309020a17070501080a0b030109120801140f1002070e2403030a05070b070c0c0b07120201090302030d0f021623010b0112050c090310150603 73
    0x154585407003c40341010060703c141451a5101039424071001c01d5039100c041c4001ca03000c80c1620700180d0b200355401002614140d81d4840c43e42010700e603080c61254440490344600b11a028201403003180c9590007601c1c00303072980c101523540543ca04065a0103000000c0340d01c0005030780d20703107440900d6602d452246c3c0c55202038011035508240c0c40c10300744605003000c0e00071038600c0c40184140e0300d04d29115901a84d281905880c070b50007000d10079220600306405924007400350182140158500101244082c1035409000030140201541d400012200c2c0c0c0103040c0d81888a521018440f040d94480e4469003054105050948003094403200d458250b900506c40c440036180c158000750304015400f403008014041c2000901c1d0496024055032030b9070a0300b00e10361800c0314885c103c0c021000c604200580d1340100b44249440450f03042034914080342c0d80040d00da0304980502500800d199481d190610140d1040c140d203990944180c03075251000900c41d40c4500003105a803e00e0140c3e40d6503a8204600313444c165a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 465261663 1250 465260413 465260417
    0x306010f08010510050d0e010e1c090806070e24030a0e0c090a111b030a11031206040c0e27060105090a0918020a0905041b030506062209060b090603010c 67
    0x1500c2003e40d401500601b509074a40750000c9400c4da2002c82850944108101d5440036074014142a110104034085a4050086601e0225a12441c00040c503907202d5010341510284100c0c0302e410034040c0c03500c0000001c0e041042201078481113102c00364070842c0c0c0c0121840000c00e8038103511790b100f4203404603034040f40403002000d04500c1d0301c070f50721410000c19100c1409040003004000300422001c034a010000382d980c2d11406140c9509074000080d111000059120406410400ca041865403607105065049107003174600180403443c204c410790701901e1201a260f400100003c50b15004030141d40750040ca441d8400c100780c0310b625098019503440c00744030607041c0c2c00a628a802d2091311078580c003610b556a1141040a004c80315038000c038800709815005601450b48800070042405801e0003002c5400c80c1c00140c5615040c0766442c0c02e502d40030050042403060403c00d0f11003a840c9008100b075860302c60542e0040082243e10314224009014103000036008c0c0f07000d2000144149010305c20034804880f65 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 465262913 1250 465261663 465261679
    0x402030309010f020708011a090121121403012d080a02011112030408030103110603041a090a080c0109021e030a1412040306060602010e300702150306010f080105 71
    0x88006443c00140400e0b200d007184100740000070048424007915940000c81c0b00c03403250059003c4140503070070b04140c00c02035000c90310b00c0c11580995046030070a66141e401440d001040f035000f40040b0f0300e824003e40032a0a203400400046980341d44000340580b105071201085070710340d04901907a00d80c11018410710000e60000312240016500034081540d03000079031030a60706408601444004550426074040d50301c0d0501100502c1040041c03110b11550900444035070f0b0440c1b810b941c60310700012080d03a598000000e00c101080d03100c4020040912030544c0201500c4d183e8428a003c0e07030003015540d400764411618410319440c0607072811420a030784c40003d00a416001175644980307040e1401000406254030407240301c10b0783e00009001902c0070318491300b80070600600e404c4000313094800705154008181c01c40c82a8101d034070203d0400980e02e5254076003801400e081d60028003420b0094050180d00f120006c00c40c1a1103400c0e4100031446801e007601c840b070000b04d0025003101e00e51000d01580341c0040340703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 465264163 1250 465262913 465262927
    0x30c17010e0109121218060e1b0603010b0d0209101107091413080403050109030521090604110a0503010207082a060630011a030d0206010905040602160507030201080a0504020303 78
    0x410030f558502c40181c171300c001c80c0c2c00d000b42078540c0295210440c00d1701c503182d88040d42d10703210b0000c1c401940c00c0c001002d05408565036031000103c45100601c5002c8011100080d1940c041c03104d901500d507180c500400b403804041c00200d02909207504142010a40e02820401180103165803180703802d181203100c812a000e9442800110403041041826038103040306100002c000b03203090065070311081c030958420f92135208401e81071240d69a80041c40020300c030007004004c041034000070000c4d4841d400c900d140d4110018032010400d03e0a00d504a00d4141d4000a24042848800401801c2c3e0400410820154242101705401e01c102201c540500c103400041c0400c4251a010501040221200001b010841d070b0340101c00c0500712000140c01c031036035100c407072007460841000f50520340102c0940c00380c03c0c450418200251a9041401031904003560342000c2014001c1c59415180c01407000c40c2c2841003c1e0306030800507070f90715240c8001ca002407849800191180194010741d4000c0e80c1c060000d44c10202 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 465265413 1250 465264163 465264167
    0x120213030f020d120903050606040e0307120e0a17120306010c06050c090406030b18031303170405060a08010f05060708040302102a0203060a02090a050105070606030c17010e010912 79
    0x4400300702640d000244580000106010484214040e0041c0c0c8507400d01520703524009083c030078001c004510840c0ba01820381c0c542d01001c411510b02541c03048500d175039440500ca0544030780c845000b1250300005044808074003000000394a4000100540450701803a5901d41840a0f512080302d00701d0004034000020360008510b50013154000328403001c003d08145111000c070b012100190300c2a180040b619041c0b100a202d15040245c0324090745003d1460701c0001104880701c008188001415072401e0480920b1b42480f0905403805008000c14070f5603503070903100380141012000c0c02104410202100000345030301c4d10302c08903101c49600400071410185103408020540c5081c075600b00600c81003415484040480314501c4404111103d02d00400c0c00160042c545009001040109640d1040050300352643d01e51200c1006c542003483c140799541c0031031600d44060b0106034801000c0540b080c201007040c0350240003080243c51544002c00081c00c13a200344500b130b41c0b41e2000c060940100f003007490b00014 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 465266663 1250 465265413 465265433
    0x70e09090712030f08100e0c0c03040504090b0103021504080a06020c0a06060609081605090109110c0a030314090a0c17120309071403031207030903032a12021303 71
    0x10001809491920b960303610703400030300040c00301c0031000241d0240c10001c4145c0c00040305504510224a0791025078109003040340a8040581040104000401c940c5042e46042040780c0103401c000d0001d02c00c09150b894041401c900a0204a204010188948407030580c11402c0c2d804403400c007001400207000d40d4950702d000f03612072600c0320a40d0169240d2040072035150300a034002050a03503103440c446407800800c1400c01d41740c0384100242404803801001265141a4540e0555101210004030b001886007da132141c443c984110480380148203160040c15090381c017800c00b46027540100b00301075a55a04907501c035000d09100816000d0281d0084c0081c0140c1e9501c0403214005404a079000850918015501e401c116034204141c0c2c480e94043c003c10b210384800101112080c3c00841c1000111602c0a8081d60010542c20030196110048014584241c001c1c21501c3c2083da104d030001200760f882042c035150a0348011002c1000445042286092482201c110102136024104098150b964161400c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 465267913 1250 465266663 465266671
    0x3110d1802040b030a12050306042307030b010e0d020f010c0f051b090f0406110405060c01020904060506090d0f0303020f04030b1b0301150c05070806090303040302160f0e06120f0c18070e09 83
    0x1c0399440c80380756104010707c0b4bc0c034805003c640ca01c4125130303d0300c107000030155007108a846040050045000e0110380b20385400d01b02d5194125441d0b88030905100049179618200080038040400e6030012000703005000c0742e1108040110030a0000c0c1140440c2400fa01f10000c0d210340c0c42650310500080e0102c2c60b01d52080c3c0100c411050224902070f031701c1c40081d03030700c0c0c00030403614405960000d03102d6424a014410b0a00a0105560450030700d080324000581c030904010014024900c09512081014401c0d070490321b15840118440351165200d09016000d008115540c404451124085a240a070200c0c1901d040b188866841c8005404c5c40780c08942c0d01280c1a07003191544200c80c40420920001d000d550701c6420040003c584074030b06414000d00e012007020780000f00c00076075139041c81480454900c0c041510180001c4250a0f240e180210310151400311880f2954041c424601d8504007000c90320900505040701d601403502544040500100001c1d65072102040340c0c90b950b40e00d2414003058080c1c1c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 465269163 1250 465267913 465267919
    0xb0c2505010b010315181d0c0102010e1603030f0225050418120c03140c0c2814060d060b132c04030917070510170703110d1802040b030a12050306 64
    0x59403100c600030303c0450701f030031a1707460b181d40009402c80801d590921521444175001e000070403800c80040c0401d040719005001c090200b0262550074006a03008110001c1d605080700c5007202003104030b5940740300040c80c0e070040d24030943c1418086425407030143c031040009074000c004403200700c000f03010071b40740c40c000410100c00307115003465440a18070320070010700050006140688104101c2d50104120451411002815100c20680c40c4c583c00004902d0748054800000042e042d48030450000b6500d40107007008680e50508104000c03c0141002c400307800000e4141100200864a4800c0c03100b0501e15181202808440c50440c24410300340302562541007806400c20b800d400b42c0b10091482a25481010110517501c0810204200d0038401c5c6107441c1a94117141211402c100c91004500c600c00140c03c103000c140e1148640c14440c490749080307030554a03a240080004122040d04040c03851014441a4403c5144c52581d8503141000310306c00380c840354018000000c44405000544050304040c24840e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 465270413 1250 465269163 465269171
    0x2070b03150d06020405040b010c11011404031202070e0a0c05090603040c05030a0b0f060117070c02060c01020a030911060f07062a120f0b0a030b0c2505010b01031518 73
    0x780340d88a039088020940d018002c0580d6507400c0c1000d00c825210010405810002c1c11150800030504030356880314880000d1800c01e5000c00121002221401307a50009401c0450301d20810072901d400080c1c4000707c0e003c80d0344400642d03441301d5114045814001d0765030082001000540c01620384030004542c0103200e44003c1280540355800300c4d2501a024002319085000340d030500c0700c111001004a039010400b442d0401814403201c0c0400b41c5000050480300500c0710301a122021035440740c090b00d000c0380d0004021911100c40704401000f03080c034100280c8145240807102480c90804400315680c2501e000700c0c2601e400030a40c0d0702030041843d0702258200c941544540c2c00c912448251100518401d503440350355408004500304101c983d9445410310191800e06540f44c1c0341c0302c07800b44034100c9030440b58525181e0365031902062648114510b1780c511303510b540d01c0300c2012080c0c500c02080d035a0054000b0400394070341d00300540886881c002c820b81d441101c00f0040105400d0a024080b1a02082030041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 465271663 1250 465270413 465270451
    0x1006140f1b01090f1a041703092a0a17032b290405010503060a0e1903270e0c0c150c04230f06070203150a05040b0f0702070b03 56
    0x9070031904000360880310701d04d200741403a060141000b40c4428406907204000c0c0c2c03074109035031170b01019120b00703034000e550b40310100015241c1d12042c405810562501c0c2c4421011406074105071040c17240c604100c900c00c070001e08020071620000c00400c00640d1040004500e45102000e440c18014020b46130040000b82d2902c03034003809400e0340141c209180c001800c00c0001d44c0b202d061604484110190140128904030041009030740004200781c02c211405400030340c0d0000c4410340c500f811140503c041d2941d41d2201408101940844585000240d028a50344000700d80340703448844030001d1242206034401301d130101d41501d01100040110300c810382c08903400d1705020042c202e03040d24101e4041450702c0000c070703081003544002c0d107100220b0355602c10003603808481100021840b0707000b0039116000702c1000c6020302c04c544007000658240038420880000d2407030301808174809441d00310b504035011000640400c0b0f5001c66010303030078000c8031582c01070002c5c20300301020955a034100403c0c28000d84070709841c0c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 465272913 1250 465271663 465271717
    0x31009090c060e12031c0c1b030e010504050a0e0403020f0604170a1110051005010c050307081b1009050d110607080702011503061410061e05041d1006140f 68
    0x1308141c14003600041500065104054220341e8101c0c5998140848008c0c0c140001c4070b10801e104140b82d05040c211f2240b01800012140b5000c1c54001e00d401c0f503418240800e200000f01c5465104904c40d50866007400d0f907218903a0348502050b100205280104800700d007c413044103015258603905842c0180d035400803564043e1034408844000c0781e820343d5640c1800400c2e000407070400041d02c000c1c02d2440c410200b555070241d81e03224800c1c0182c010300340455002001c0c50083c10340c82581e042d46044440c403c1c1c03c201401d00404e42d4000c21182d070b2180b00c1350200b10341c0c06002200360500307504000d001e00f952050402d440c0c07000000e00301402c5540c0c0b900ca441c04092181c4c0b851002d1802084005581007541203079004820024116030031549040c0010400b03e0780c828148481d482e0141e01c200344281060384161030324012a08180b02d180d042081801100344141c52643c4038107040018219100c0da02c1d5025a040c1000043e060000181000403041c0c0b406910001e01504100e1020301040d07050b58811 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 465274163 1250 465272913 465272917
    0x1811010e04061401020c01020714190504050115031401150813021908070906050f060c0c06070b040b070e030303070f17010e1806060109050405040602070215031009090c060e1203 78
    0xf09100c8042160440c000356410003000d184024203000400d10300d414070001e0740c042010701d607038036120720900c0035544240042140e00308014040500140040c0d61500d0070600b580c0451000da80000b4684000544d401c0004001203040b00c4030a10180303031100700740c4421140c03014002c110180c40e904084150700140c40d5540c800c002501110200200581040c0d002400e00c105540640420380c240391040c807040c6d0f6592144480c0000c101c800d20b0380c603020380d040c0500300410b0355000340c4c8c00000801d101d800c2c0610f0044091040c1d00c02c0030002d14a0f0369810082c2c90000aa03403102e5019401803000840302d07401141ca03842d0f0720109090500c0b0300100700b0004010300038241c200c00030b80e4049005000104121901800ba14a41d01c80a0403039031030b0071000245003c9081c89a42d01c210b072205c0114060000c6a0704880d04d41e500a84510012502c0800144180c0d00513030f0140c2a030008110001000d95040c450441416072080708003078034034940702c4100c070410800c04000c1d038040c4110200003441002000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 465275413 1250 465274163 465274169
    0x110114011815080705030c0618090403020f060108010207060e06040c050603090c060f0714070b03040611040b0c0a0c0503010605010c1b05060304060902040c08010303080f0a0209030a051f1811010e0406 88
    0x1000b013103d5070410050508040740415241c0c06800e082c091b540c800d00d1005081006507070251580070340b540c0e46003412407400c000c105815810f0f014600c00401c0440c810b400034080680949002c0c84400819030006540d45003c031340240003a90760050510242c03405200458002070014100c902c80c0003000000b44440c0d20021181007003140001c4d0344c00030000c000072000f6102c448d00c0041c11200b4501507010005100050004200c0c0c0ea442c0d1042c14400c403e9420388024080111059413903204403048265146030219040c0c803507580703207540041c02c1d140c140101c00c01e80300e069403800000203030307507945000c1480740c2000d010500c80b070200c0100f01502c0d044091885580900004140c030403450041c4011901040d150700304000c031080050012a42111100703802201180c100c00e0560b40750b08a800080c090501443d91502500c000350050080002d0300c6034084c112031140d0340003141c405540e1000c6590301041c40340818400d40c1d80c2004140307086a460550300040c117141c1d2110460800050442e01590 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 465276663 1250 465275413 465275429
    0xf060801031a250206040b060904020d030c1a040320010b2b02030a210c020105070f03020c0a1205011104060f0c081323033904061401110114011815 65
    0x81c00c20050020b47d41503690010340658400c5180e04113030300440e4000c003035500007400f4405200e131800d01b00320501c45140d14450030542181d049040038030f4000d00104600c00030407c1400000c0c0c4511034100706100b207031184440144000440200032440b0201c062100502e9002d1500c904d800c01c000d0386040c0170582c0f0182c80340b40140c0e928407186020340c401c19042c0c4016000c00108180700310050740c00c81e0031140ba15401140b0801e14000600d0102e1600c0841da200f40e0f0803044403440021607a004c040c0201d4280c0c440c2c002030140c002c00285032400c07806140304010000d80444420022240a40e4000c4c0146000701e0320a132410056001043d05aa0242c1c0030b0001c00d8050f074246e120075890101d2110741001d04034041d025202d12414181102d031205140490303e0300b000703244100e18030b4001184400100c2c0c0603106029450f80c8001b0306001000034408a03010801c44035089452200610a40d00c03500105c2c01611116401c0c16860b070b00a00c11101c85006240d590461040780d821030706401d2004258030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 465277913 1250 465276663 465276673
    0x1e03121f0807120f02041d0c1201140f04151a10030c17070c14030a02150106021f1107050c0a050103061a0702011412010f060801031a2502 61
    0x21029400c00400d070341c000942500100350601c1403072800b8480c195410f410251400411005000207001000e001c0300e803282601800300c031414202d4012a007000004011111700b00e5201d9a4040c0c1400e0b25011400312000e810008000342c00f00080c49201070f0092300411400e00300b10841d207109400ca501d4242c900f91444560081180ba82c64804c051820705405842c051042c4400c44d4005012000782013541c05081c90010001000280724400b2040c0d85a00890149090040882025160313030013004410f0040c0100081712100c020140d004904842a03503000700740000c82c2007113850b80c030480459a000080c1d11922040d5544c880040a4804180202e000d03040000b481010016994400e074022410b041c1008410400602d21090350028840c480200a82e101c405100482e941c42482c6240c220580001c140f105100e15101c0b0200e060b0340031300c541001a19110342003525aa50240710041a0408401561003041e2081038105c0d0071808907907021001507001021058036610070041500141c1c48 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 465279163 1250 465277913 465277951
    0x209040807200f040914030d02120109140a0c1e08160e010516020310060b031008031218121b06060a03030504030818030d032c1e0312 59
    0x180340c80c1d25007507003019441a9403200300600450360511101c0c20300762085030740d504440184006009264000c001d006d058982d1600008120740080d00190950103c100d0007000100348100d0030301c591007050310b00561444950341d0700c40003240036241024240c0c0c204091a20006051309016200210b402d00701e4849003c140b6010741400801100c01c40000c3c100100b01c1070240b481e9800c14100c5203070702d64101048401d0b84171800130a1038101c11002e610036032840c140d40000c611003a48040e502508100030b1441d1030035603883c14290b40b80a414401052142c016020410b12201c0c2c0300c41c0000a03071018103984958900f94608203543d000b584840d400c2040f919180402c81e60180f002c9603215078103c4440c02d2103402c5442c001c1450086000041c00601c0004081c01402e43c04140001e401c1002411150101f411650007030180100900b00308116030119520300e13044400a80c0102d034102681c000306101c85800c2c030356808540005080e180140010842e51034a031445c1601244a0b00361000503040e00c1c55 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 465280413 1250 465279163 465279173
    0x109091505040209190605090a09020a081b0d0614150114270d051f050109140601050904090b04120e0901140108180a0c0302010318020117070c0209040807 68
    0x4010508104018a06400c10005955841c84217400c0180c00402c913408260011414000340b1041e00725550100f150010020080790780e42100120620a40c1e10111140da16940d00755221195040c500310411380c0440320700a41405451060114081c0002180c41c0684d1102006605000e442440d29071001768140c442d2560400720005aa03240c100030301c0d01c0c01c52001c0031070203145151821010f050000c841c0b040002d03503509510481543e0401c0a40307004040382030720480e640c0301d04241220000c5c01c2c4400012a20f400307200d450007070104801d1842d910b40c0e80e800119200e6100d04d02c8564800d0341c41c0327090001f007008540900c1c4190300c6801c00d040c00c5405154090a80c0c0c5d0840002c920a400c400011f0001c0021282641066142030030414519210746000452004041d020314055201d04040341d418417010207210300c200c074000c1e04d04019100200034103a01d500d01103032010b4042a044031001030028182817a45a10143c1ea20702611183c03032550010341c0b000c2e4180c50030703079a01c5030100380b101c1440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 465281663 1250 465280413 465280433
    0xc15020d0e0705011b0212010e030a050309070e07021b0102010f18020f0d05100c09030f0506070e0a050f0d0c0302100801060807080403081f030803090d0e03013e03010909 75
    0x1c002400d20064521786203200c0c890f4000c040600031700408040340100340712502504006005221281500c4c0ca070015103400a046030002c40302d00e003191041c2d110024012085252681c06900c0031b078094145115184075030300c491800342560904640da00e80e5100010301542c42080a04407483d0040041006503004018000c095501a54400e00c4c14180403000039a00054044000310f442c0d2000c120119400d10584070f04040d584042e05045161620a0401031b010035114407a8006807100d880c0034001c0c00c00e100c0c0b050010b0081640080040e40c140d0424606000400304d075612034881c030400e00c1d03107aa0204c1c0707207410301c0c40c0e00c0404540d50600504c00740d90098407050340040ea038640f0390b92900d41520010003000f00035003541c40e00514518015a00d0751341d603010001442d00842443d54900308514810740d9002c1d13200b28040042d28903442d0802500c3c0c107004446c1506600c2240403800562004104410403d030a0000c50300d60315682e00d444a0a6010080d50003001c1c10130000a50741940c0c00c0500881c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 465282913 1250 465281663 465281669
    0x90203011a090402150702100e04180222110a05041a030906040b18060403021c090b04090b0a03060c0e09090c0907030c02030d0608030c070f08030405010c15020d0e07 73
    0x49000420788107480d242d142d103459101e50116010b07008081c0c1d01d01ca0002500c54060041d400403010407580b40400d4000c0607007101039400781c0f01040303031290100c040b41003030400ca18000d510134100211000c081085000c000003002c400c42000a0070300b00c051052003903a10030305035180400c0002c60304200311400728551400b4040740076401c519501e40b03e89482d03100d510042008007415103900c0801c00c41b0341003074403140c0d030718015004860160806040c080e640c1c10207090b1660604049689891410748240b040c40101c0d1030b880b8049040c40d08041c00c0700c01612450341c102d030304801500800030114806000d40182e44a054862901c0030200000b4484100402410f00700a544a0100c0e0b4980e0340700c1e60001a84541c0302d03d0000340c1c142c4010806c074190f00c10740e24203202d45420210080ba170aa0302100400e00c2c0011101107415450742d072080001c1c61f0019201d80450f03508203100401095020f40110b01c1070610031800d80c80e40a0500c100c03981260080e006040e440d990b01d02c010b14076150100100005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 465284163 1250 465282913 465282941
    0x5011d0d050409020729090f01020f040e420d02100f0509190509101208070804171e0f0a0f050a050304030b0f011509031b0503030d09020301 62
    0x185a03210341001c0c215208500c41d95480d2540021501c00380100840c40811203200c80703000c5400e40710307490035050840e0350590700c901d0140994820305803910014403c46008070a1071405c1e0341820700d08500081c829a0050441801c04024202e01d04509040c10703410010002c42d141c0900c407201d04917580034600441e040c00320f01600400d0140c80243e0350380450070b03001a11918202a40c00801082100c00d4000c803c02650042c0003428160000044500d0b4101501c0041d58810010741d0f0364030114542c6c070101d10542605001503001070020552030070041c4841030103128100d1402ea03640c451650380010000c40340d40541c0082c4ca041d071403050f16030100c02c0891030060040c2201c0ba84135507142c0d01e0309503c1d0002020008801044010040240611480150842c058030b1f20307140d4909280c80d09082c200c03051600b580d405c81c004601840d00f10180307400b0004c5a80c40c1c3c003003c0e0030340e550b0403620a0990b000c1025124090030004032a07401708010030075400405000f044a4500e48140350944405141c4106 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 465285413 1250 465284163 465284173
    0xa0b12040b0f0105180601231804050402061b240f130308060f01120c0c0201120e0a0602070305090d111503091002210403050306090105061204030305060a0806010305011d 75
    0x1180e50791765000515002c0d0250003d540b40e4071003138010707600980010784052030180c96004150703900d5240340203007400d13005508501040039440000c010032a10210b60007540008244011040482c03040c03055913000c0c11100480d031003403070b0400c2c600120b080ca0414017103202d030200e42040380e1613481c44140c0c1c1d04482e11580750081010566800307080018000d05c83d50003512050501c41c0c25038419100002e05c8a4492030400148540c3ea100620311542204180d01242141c12803119900c000d210b1058000701d00000703480c0300f142d107680e401c001e9032010314150108207060090001c2680c400c0704c0c1100b65840b03075220112058024040c0240e002605040c0c02104200b88100814400c02252502c0412920350b0010313a03442800c1e01c458900116040ca0a01d0020b044081004060700039004500900080303030440720030307039948003000454401c1400d44001000004c0c04580000d010350070241e04078200070f050074821600c07003089514241090b070060322243e4455140c0b401c0420f2a50085000c810400040d02c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 465286663 1250 465285413 465285419
    0x60303030c031a1e0904120e1e0d0f050607090503010b0a051e04020408150403031107050309090903090d0605250807110c0a0b190504060c08090a0b12040b0f01 70
    0x11012240641d0f82c00c0c021507483c2003042c84001c9040840b5507602c40240f0b052103a00303043c100103690490301140e820214050035410715080c50a465850003840030359180146400c0c0250511210440649003261241c04010030840000e105000b514801c3d82196210400c603454101003600752189038000034044c0f00314050610550310740c01d9503444000c2c3d1524070203081d14401404100244640e52014189010305041c40c0e4141408004d804e0040c1d000b84d50910960b498451091001e11454500401982c420004040c030f42c2004d82d04541c2c00f1150001340c0f1b061010400c08105a1010744000f110602c2e503c2d000c00c8404031140c000e11190725520201405840b00001014000d0b401c043c010704244071000c900090200000c1104a0640c4400744c0b041c0382055641c441031a0b02c2c0c120b001090448038103c42c0b00c2009520039400d4508807445a0388010700755099807140c54641d03225000c65600701c001d106010402000c018000d0070709203001741c10140c403032400b420a0078108d2006814603205e100d00784010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 465287769 1106 465286663 465286691
    0x8070c150e060a1b030c05160f08030301050604120602090312070b1f1206020f07031701080d020a0b1302030a0c061103190804080f0409060303030c03 66
    0x1d81c40d0078010707010402c00d40250705400c00055081c0045681207007492a0a0356154000e0815560740d04480e120349092074001c40e94407411058000c01000020b201280380c0c4004c0c4422009541994140400550140f18601c501c010305941c05c401c4a05224455044031203510700103044030201441c0901c0f03454160821030b025581440484001140704c9007030030012014807010290744001c1c07410040114000048250f081d44c4080c1e00340003400120940d07a0007020010f000f40c985120f0b5804006c240503100398140c000e8038141c1c01880540c094aa0005038000300740354024001090f594554141b90512202008040d50512811241e081441041000c0c0380c1903c007640e40e000010b245145901d580d034800c40c883c6440959220345407407080e9220781411500544141001307481c01c00051503941040e0801c1d000300d251036503144401c00c20140c151040107000394072410207201c0c20514a250b = true := by decide +kernel

theorem cover : BRFrame.Cov 465107913 465287769 := by
  have h0 := BRFrame.cov_init 465107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 465107913 ≤ n) (h2 : n < 465287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
