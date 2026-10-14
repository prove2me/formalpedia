-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2244
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:07:03.440439+00:00
-- url     : https://prove2.me/submissions/51b3caa5-56b5-41f1-9cee-f0041d6d7ffc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 403417266 ≤ n < 403597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 403418516 1250 403417266 403417283
    0xe0a060e19050301021810080106090512010b130204090b0f0a0303050c03040f06170c0711090c0c010e060103110109060509090406020708071208090d08150103200403230307 76
    0x860107203540280c906500c03458040d400024485000414048044807501d4101c54181c84044411421140071138240034000118500920502c642d14020840c1c0d01c80020440000c00c0c0c082141d00490060081e0364081e1003565000b0600713000c015098040c03e120340d401640c000452a20300c20000d00840314510003d0180700700090303008504030301481107030054945480d24000d0541e464400030505004070340c40c0b0b1000510310000c14a80c800700000c503924140c010500140304e02c001c8080181d0742034040c1803209032034401c000e0910343ca1000c0c0140c010160300c6501500c0c0c10343c03450410f040380e40b54082a0604000c025007040c085950030800307070361441d841a6040303482540c941c506600288120640900702000200749001000200c0454800000041e034600d02503846015080c2e9032130f600010444086100315000900c41e43d0201c0508004000525000c0750404013020048260503464110054400001509000344800001c4100c10031441003107114018212040307070368981c001d440004100c9d28 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 403419766 1250 403418516 403418539
    0x20102a0507080303010f090f020f19090f091a03010b09040f0f06020f03070f0207211e050304140f220617010b030c1009062006070806010e0a060e 64
    0x4010403001c80034200140c220381c0c2d607584442251081007842c2c85a030b03012a00340801a50510324030b0080d103000d11032003e8524281079403504100e01c0b60b0360340c400d6041049403600c40044c0c16610440042c0c010b11102400141410301c900344e8150201c09100c07024040c3c0c0c10600c0384404bd440e030101d2240c2c07054020441c124204143d140100e415000700b4809451503002240c01d0f07001080a00086001d05081c0d03c41c84107500301517405989031304e094030807105114400b003010401d09520130004a051441020a103507411490300941c0c443d811100e03c280e5555202180900483d45240101200d229003142c11031140c0700d021001810b0000000740c098a1300000204403840001d0503080680035004151040d00b8122140c54841c1c000c280b00c00059100b071041040c40c0341c5074200680c14815031003540d034a00240ca42410000c0d900c040c0c600c060815403c0d0040f403900c4c00000c0034800d0a0150b081644e81010764100000010114000d100764103100c0c80107440f041048030303017045c0800c0741b00d8416141540503c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 403421016 1250 403419766 403419773
    0x10c1b08010207080c0d0207082d030d0204031b0510032a020c0a060314010626010b030402130506031015090e0c0315070f1202040320102a 61
    0x5000540c4010368940c00420300f842003080d100083c0c00c0304031400c0100d451034030425600300da0300c41c018800c80d0079a40050310b580e05503800c95444a08400405a2500340110f002050a40f0b95030218104a00b07903640030600f4001c0100540b02d49a03025808088240d80c0c6061070b0000c4c8010828110a80505a54a0840032240c0d400070307240314031320f140f480c220a1101082d20040c0d1030b48028010203110311a202c0010610324040d101d50304507040480100c008aa08101c002c1c0d40c00f480f08100030031880c40070103000d214004000350241c06030000040b02d644038281032040c0442e80e480c0d129400140c60809040180d01d03200041c0c952101103004d032002c18180c0303040110690041c41c0350440140d282c10055040300c1c000001400a182d40d50650488000f14880c0001c005d28400668510f00043c8003c0c41c15030142d4401d5580300345d10b0004480041c505980c1e5a504103072a110f603140e1040b00244902c403181e0901d02900c0c504201080780c10140100e8107542d0120b102d010107001101c185000f10076070340090 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 403422266 1250 403421016 403421063
    0x2a0608071b06140a20070525050a03060e010c17070c02040f06090204030506100510080a0f0c0f02070608011203050f091c0b070e0a05011d0a0909110f010c 68
    0x2030b403c020798080f81e9410140c100c0d4000c1d107a00301c594007811301c40d0180450716203003460885061a030894041c100004409610928003401c1d1000140c0c01034501c4000304456a640c01940003c500c01c1e10b0000d4801c80840504e800d5450080306030381440390100348000c8a8500c600a01d610140c146400060403c05200060080640e20704d0101040e00c0e103400843d401000b58001c1041e0b0b03000b50115452503641a00b0f880c0141d060b0b00881740c00400202d500e80c0403074002c0c074010760010205400410004015641d1b9011103605030384480000e00e611103003403406a01032000c00c014144502c0d101c1032560401d03400512050111500804001f00055503c00103c0d030700f8243d560700300000b04070410001c000154113900400d0720406641c4100c00c00040303280c080c01407500d844550400b40848901c40e02e448010354101c04d00d0018042103a00c042464442c540d9600b51035005028800b000107084007103820302496140c2c006101a0290040c01d0450510b603070442e151408035580510701c0f1540c8002202d14200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 403423516 1250 403422266 403422281
    0x702010b09010e0a020a140a170a0b061611041505190f14030a0605010e01170307020109150203160b071215090e150406021905090d1e2a0608071b06 65
    0x24801402304071591015403004410710700350b04421642c1510345420100324202c50480c40480d902c04820007a1000c61803d6405031200e160090040c410059a0304010400341d48650080c05861020f4410500c41440c01081341d48082d4a401c050070740941c2007020820100b440742c0100083d40c02d00d4100100641c0c0c04001c581e500b42e91100f400c0c0001d50791f6442080c070a4000303016815580c2101782000411302d070000706032039185405079941c3d40e813103146c0390201c00c2907510b020140003180402c0003001070f410380d6101d20351038492080130352011368074142c00b0041c8400d001c40a4034102600784419a0140042054000251012280c0010701c01c041c84581510b0104500d00386580f15444004120603c02998040c0c14041542514402024540041181e0a204454809600c445c000180c880401c0c03184c0000a100c032a0010303030782000c2c2d141d52642c08103003800c0039100e280c01001c0051005808102e0700300b48004d1409080040150408038000f9000315230f60030001081d2054560030205024890304242d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 403424766 1250 403423516 403423547
    0x20a051b0f0604080705120d05180d050f06150a081b01030212010b0421080711060906040e06041a09040b040606091803031104050a09020f1b060702010b09010e0a020a 73
    0x43d943d580c1d40803d40e84034405889002d02c1040c0401c0c0403400603002007015240c604066075070a2400070f000d909265205001e4010b107804c100309241c014002003080240c40200e00d024001040c2c5d9107041102000300100043e441801907800c030004000c014130001d40201320310b0f010108010500b5004004800034003a91680c4100840804000514800280014801c0c1c0760f02d900916590f2140c1c40300413240c407601e02001002c2200410030380c00859003840c0c1c10081101c0040c0f000c0c0c43c3c02b407050001882c0303400039005089a45294018465a8030b4644144803402c000002035003d21054800010b415900c018000391040032030310001820000c49500042c082c1600b00c1042001440b1082072000294042c1d2084000c240340c1013580c2030b00e00220b010364048490090040c402c032410301444102941009040342524441440300354000a50440c24000e05e81004000300300c180341822000b0b0039210034220880c022044c1d41d00601c070801d042801d0317603400041144096940c461108040f200c1c10900c01c07004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 403426016 1250 403424766 403424779
    0x91107080c121209101b0f110106060f0912020d020d031209080301030302011424060c100506090109020313080c1606030501060e011d0f0d06050a0912020a051b0f 71
    0x200d1000c01040b00381e1300584400007154210404103402c031049800c3c00182d000040c1c0c60514003006148655003c0e18100030b030307150041c09640c501d00c009003035590325002080864a4401c01c00c0c4156805090702000306041400c030200401240c0114607400b2142d8400b030300501540304840d081c9405854400d440750481d4408128210b6907003031005181e04280021401075007002ca03007010401807650401e00420030424011080c0200c00c81078211590303040211745d0030244c140700515a480b0107006494500001c440d0225151805808000c11240140c00c8556900d10600501a12100c08550341e40402d0380100300f550388025120381c0c1498600e60180d2001c00400440000c1a0301d40e0681000e07041b914141c84500c6031001c001b005503117030450105461180c3e0301c03c4510404520b820400c41c0d03200c0c1005000441140c3c00c91300da00043c3c6030201d40702694035032116418030030003102000310301140e6040d101409412859075200c1d40c40e0400150b02c0071900a01d4441204c140e03840703e41d401031142004010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 403427266 1250 403426016 403426027
    0x90904020f1f050a030f0e120a020114012301020a0305090409110d0624030206030c0d0204050604080a030e06070305070213060b1b01060b0f030712020d09030c0606091107080c12 78
    0x24401d61021a040780001d0500c06c841d90990768500030740f22003d001c14080c0003100c0008240d00390320b42001c4624011503488941e2640004007403019103001c1c0140f442044a0b00d8602c52800b10018a05202c142c1154400c40d98000481d80c01300694660b824210381c00310309040709042c400c28070b4400d210801c0d400920b000c0603c0c10424207034000000031651404e03103144100309180b40489040035100c040e422140400000d4240c460181c0141003036036407003800504040d02c440c040386154102e50820320041d0f00c105080700a0541260140d010914125a60389c0b5107451960010030a001d80d450003402901c1488130903160b0589a00040040c0550006054540207034482281416020080c90422546820008100c200210048459154100d0070040c5191070f03505040b00c0554152078420303d46503080c0f000f22900303c0140600b181880c000d5403080a01c80080c1003180444000390b11680515107413900103801c00c40e982e07080d10450307504002416214401e8001150529402560240206800244 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 403428516 1250 403427266 403427329
    0x50c040e0a03200d0c0c09050403080a050c0a050f162f0a031106070c030203030a091409060a060509010507020d050d021e06180f010501090b0102010c05090904020f 72
    0x141e103105203000b07039144240340032a200810001c01e02002d04940a8120300010859107000b24621512a03100398500c812095640c540c88040307032400d5078110001429441442402451400340a810088002540d4a00f0070342100c040e10911526810015440c800304e9160b02c1a0208440c4038000351700280101c0301294041c1c2c000d900d00c80868040d010401c1c2000c030b1030b500350038805004e40c1a41e500170094444114001c0c2002025005004100c800301007030300c400300040e20700340702130306001883d5222054800d09280402c2d2820a41d0100b45020f04000020080103a5a40c0d600000301c0c0c48900701180e46002020040300c003032041d03c1002e9089400ba0181c1c000304000056440300da030a4560a490f6440c3d42500b62030040180c05504613515030000c0e020600c001c0003034031003140e0b21495204a40080400070910703030035510309900040005a40f5401c01409507020700410900320b00310f180052403c42414005601489c0180c03000c0c0c0282440c0601c5002c90302d80d410303880154a011a00240301c080402c6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 403429766 1250 403428516 403428523
    0x17011d090f100c1d0603040305130f080a03080f040b06120f0307140606010504030c0e0a0209040c030506010219020a0b0f0702120604051219031a10090f05060301061209050c040e 78
    0x51400d00054220b040c000b021028004c200381c1d07001009102615540315901c048034146c00034000c00b030b1a240780080c0080d0f6661492140d0000304140005001da1001504000d04500001402c5125100c80d01041000003206500310581c044400c982100c50400032012a0b4508000c903204c81005200004102041c003ca00404c00c51002c002c0084581d1030b56a0001100c3c94001c51100030f2515a01070340600c04002100350055001c04034020050030b02200d0741c002000e4034410454100442c1c0d03030314240495175905011036103810100e00095101603a641d4046a0120b4007031003070b103041c1e0034041071503521884194102c0d426140c004140b41800c9411800054503003906a07802c5a1502c6002c080b258094140c40950754005808502c940d145402c0f414142c1c09842420300345d80c42c840103c14414803071740c0e0341148010306521980e0f41c040100d050280c440d526030b1583d00550711603001880104040e40d401a0f0310403419840716000f0402403118980300c0d03e00034140442a500038181100c0c0c004048001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 403431016 1250 403429766 403429781
    0x30e1e01060609060203032217090f1f03020310080d020f06010501090501050901030906140a0c080c0304050c0d050a0b070503071b0c1e0302120d17011d090f10 70
    0x40020007425035510020303070780c5000510441c1e026804c18000114040c40d00ba4641449843c81d400384880c0c410a0ba6600c010305400c1d80545000309404580c06103030b8208099800328601c0c099401c005400045d105603140d5000590040c42050b070008000390400e64141c1c041f40080c8616022100c2940d1401c201035120131030004c00003034520030300c0f00014040d1b108003a0b500844506855492806d28a800114083c0c00078444c181e9400c0c1e1121400444041e85e00042c40c800d9484100002c2d80940c2810001c0c11842c2c0075140c90900002442888046400410104040d5074100c80007400f030310b03031464080c0c00c0031180e03400036008100d0380081000c12a0030500440c0b041c1d995540e141507101144010716914403045d00c01030080114280300740600656546007000040000f03207105909030381c030750014012100c250300b03940081c3c0018458038030840d00112031a1442d080703510790844942c108044c200440c0580807800c903880b01d551020941c80c20040c05940c0800d4800d00685414070050a08803000d01901c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 403432266 1250 403431016 403431073
    0x19110406021c091202041d0d020c040c0201021c02030622020304020a050303070c171204090b0306330103020f070c0e0c0c100c090b0a030c1b02030a0f03030e 69
    0x8040302e410240c1c1c82041d0306015034031885021035269226409000080c031910441c0003400c0314104480b45481401c00c02c900368241140c0c028030504c1d40c40d0041c402a20801c210300403d580c014000c110409101d5840700003000b43c070500040e03d030b5441c8000202080c40c15010104442e500039008091190f2f5500103502c194001d0b01e00d581000e66620916503244034040000d0511050781009014080f40c41175580040c3d00648219031030301a048506a05550090307103e051066524080d0b4550303401d091000035070000d1040b000100d8603406030715860480b001e0240703109000035075075000351480c1c1c00ba82c140c400c0d40701c014654545030501071030030020030b04003400384c020a001c0d810000384444070240103d4000d064284090159060003490381e001a10f0700a03041003c1c4821940d0100d040d0040d90003030441000d281d40e010802410034007002d00fa0340080078070803058030043c448120150310005000c003200e562024080041c64028241100105010300700c0d001c09002d10b05007600b080f0007000d12078181404c2c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 403433516 1250 403432266 403432303
    0x18090204060609030807110f060f1c050603030418060e012601110a0305150d0c0f140a0b09040b030303090c1504060c02060703020a060c0302041404141911040602 71
    0x40b580c82c1591140c1180c48000c041d180100005000540c40d0078403032030220006000b0a0324003883c9800543d0a800103842000303494804035a03041038003101011110f040018071410040d900b4400042038aa208078003586840e180e18000d2103500c006540d00c010010101207845002c656161b50000c9541c075002d248020701c00d64149104034400e801885680c1c1400109400c040c90130043e05003c2c2c02401c00100031f65800c80b1200031492070390710340c162560450782c0320f14180345000341041104140025281c02075510f0001d20380701e60429445840c2a4001c0c0e5441601d4983c0301c4c12224000780151044240c0341d41c03d80008014400100400201c00700021811113441c040c2c4041b0061441c1d89015a115810010300005101005030800e08010000c81f4040c0c415034556461035240c0c1401d9480340c483c1e00001035070001e010440500181640c140c030340011201070024040613807a503650104081e000030307603203c0102c0c0b454203024031950110051007a4064280d4941e9600c55001c2d44840001080011003079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 403434766 1250 403433516 403433519
    0x270603020901110c0616050a021818070b1c0b030109110a0e090316050f01090308151f03020a09031a04030801051203030411130e1e010b030a110301061809020406 71
    0x44007080781c40007604043c00403406c2c0701501e440350445550300041911180600d1140e0005070721044001c60300c0140d03a001a064070300b00710b0807604101e651046807004603006920284110640740d800c98070054586070080c10400b8003005404014821040302030751640c039060b200c20800407003000c00080c5034421520480100e546614554102c40111070b4541d00d90410072034143c0e01c50400d81d12a072114011011951010030f00e0840e50b003101e00c02c480c1603000c9602c40042107843d215002502d2031082d8142ca0820303880000b000c1c0703c0310800200c00403400389600401c40b008140d10402c40c900082d0340000400b000314001c807404201050050300c0560000b14100300109103420120b02903260072039090021465541e6503264440e5590120130003560005215610401d10360a6000d042203c0f90032202034140d03601c552114000d500f000030268145ca90515907444150764010800300c1400f40c0100b20b2000c1c6c03105040c0001d0042446800060b0f04031410041c80b00c617104d2580c441c130152031007501c0411078136 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 403436016 1250 403434766 403434797
    0xe100906031802010e04020f040302270a0905060403030b0102100f060819020102030f0f040e010e06040c1803021507120203070510090b07051e040b0904050a0605060901270603020901 80
    0x100d403010003038082040c0541c1c040c5d880c140b0360b004140300718162400c5400c00303482e640001c0e140d00c13112400c0340710300d518000805080010b40c40d000f03800003c00b803820412891903070754140d2141002840a0700741540e4040200340e6034001c0c084640c0c0d02241941c10408102c44100e40300040c4018041c0300c4175071250568038900c1e00460495410544c4e0160001e6080000589600303110342d0240b2021a80801c0902c40059080c1e10550094042c241841a0000c0e900e072580600044544030030b80300040105620884442c03400b07001c101d405070b0350151001d6401c03041c5990004141e105015000b09079000924451480e83d42c044041e0500500c5101913802410100f00f9030300076074000910103030110020001242849000750003c00c030524005060814000300c002c2d03130324400d8002e54820400d401c0c0004038001e0310325040c0b10703055004a040c00b04104903410400031070081d014a20109040c04004040c1c16501c185149100a115164000124201e40c0ba81c0006001c1e41021203100e0200300c18440410341c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 403437266 1250 403436016 403436051
    0x9030d0b0307060519090b18010f0305010308030115020c0d05010903081f1716080601171501050415090c0e0a090218041508060f040b0903160803070e10090603 70
    0x11941103907103060405c42c0d009902001c48105682d404148030540e200041c0006421001d4054503100c894030b081d16166190001d4142d032440301d04142054941001440004c0300d84042c3e07030551b00742031100ca926503144c0c038060746809814642560700c4241480802c0801905401104105109079103201040e102c0032040c3c0e0442c411110f044504440301c80090103140c00c915014075004001404444071402d4074000481d1600c016000f002c00c42c1c000e80018444520b21138801c0c2c01507a00384008220181443c110f01e03401100c180607040c420307038507640e42c903010a403005c40c2c10014042810f4104403281c40c016010b0854001c00b0710070360040071030038000180c0c80640c0c8241c88079500c02d072085207007440451003008000d0156a60300c10105500380d0010070003540810209100310400e0b100300b103560906040c00e10b54040d0090000c44203034010807002c400d0b000910590401c4a9201c21402d8a0707032241c1d0429540d04041c0d01c407998014020030840364030241c0c09411a4100c40968408010340d0b040001c0310200c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 403438516 1250 403437266 403437269
    0x411010810050d0809040507030c0305090a1a1803120f07090e0f250c051902030d0513050907050d05060301200d020f0c030a03050115080c070c030b09030d0b0307 71
    0x20901c012004200310300b01401c00c0441c2c80d102e445401d00d0000c00300700103422078105441e441c0020f1350b03400c822401340ea003620440b9000b8400314003c00301406035582d0741e40360209014486130aa90705002058003065a50b400e01010301d05082641c0d01da04444131054481d000445074003e120380e003000401d00c854092200e14090314269100080250303104503140200f9800640708040c120000107000e0400210400350018400c041e940c1e607003c1c0e45c241d09010f0700d0a120300044404004101003070b000141da0010301184030040f181021912055080e0848800c0b0710158052600071103480100814590300000074480b01024030300c02c00850319020145801c8503085c40c141a2900b0100c06013000048104003d8003180408030009403501d152125285072517000b44c42d8034031240e80003041106ca216054081e40f40500010098655a03d00c0f50304010716000c03014003002c1c203c071000074155043c0005070580c03501a40c1c01c4483c0000c1803c110452070341d290f000a0704c80710340c6c51501d0785031801c0c0c0c90302150341d90 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 403439766 1250 403438516 403438531
    0xd0b0a05090703050423011e11090d060608010c03020307110d021213030203011505090901050606040302130b0d1b14060a05090d12020a140109120509030717010504110108 75
    0x904503610300c102500202405001958034003c80707024842150019150906d000b0140390011030701c000f0207010303445080b1400264451050810071000010b03000c0605454880500b2a2405501045428214010415a0015641c40d403c004021042039016001540116459581ca1841c0b03c843e850f00c48c1c03182c8462881c800140c00c020208192044104041d118444007480d410282556950000782164440f803000003252005010070030051900d4aa4664000740354002404a0b2410030001070b128440c0d804002d10403145800c503c1040081a40038500510000d020b0700507410660400841941c00100001d880c5081ca400119503502c650065481c0110090125800c4c010505030941e030707070703085002c6280e00245c0403051000840c400d640c2c036200010305034000c0c244491003400d150428840070038030a81e442e0305000c42000026100032214410350718030316016031181c0c0701c0e10000b4107201041c0c0c054a54903030543c5092900f80d0065000a0041d4422400ea481c032248002c0150380f403e80803242607 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 403441016 1250 403439766 403439779
    0x60f0203070b1609180608010c020615010f050d0e160609080601030605090c1005070201090e060d03030908042303060108060f04170904020a0509010e1f050c160303050d0b0a05 77
    0x1810006a646441e44040b03003401e0062130151612094441c6802c00040e9011480d00c4803400c0085d64401c2c40340400205041c8064102850100c5040c044000402c0c1c51504100d1030b500d038001e40b24460b1056402c50a0742d40014040035080c5005566114401940e14007184401080026002c2c00703207004d402154880f60103005660700c0d44e15010000e010040558199000ea4440d01042d61b032a605801540c0e6800d4803a80d0701d0342c00384d000041951031203030000c02110701c090040c441569505803038a08440e0303040c034002c20080c0491a00304071500450b8000181d10103030704c1c080c0007141d00500000e208200c064048414076130369100016510107090354038548400d000000b142c04a41351010f000020840140c0007480c0007481700c085022a07118443c1c100c0002e00108000050f90b81c0408040040c0070101c85000050004c02d40c901c4800d00c2e680444000d02c90b00003401002950280001d0103a801c114400142e00c85d500c4c03d002c0d10300d0307201100e211546464007520740c8062910000c003500780d400140c8078 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 403442266 1250 403441016 403441021
    0x1f2115060c02040e0a1a010e070909090609050f03041d01141c05070603050603160e0a09030c0804080106080f010c051902160b09100815091003050307050601060f0203070b 75
    0x780c40000c011201a0303002501c03603005113810f2204124944107184660040e455242d00c0012003d82880c3c107070030000440d0080e01c113110015030b00803540003d54000b004002403410440c5006001402a40c200801901442d81000501070340400a8000c852a00043d8503464074442c44400020b40b09004070384100c041c03110300013003604203200c114000c10b000c5540c2100c82c58080e03c0b4545810f040364418000291035900704083d030b0405000c41c415520010003155800c500340000c0780c5002e8001000d22021a5035000948180740c03040e40c0e80c01106410a080300d68a545541c601d6000c0c01c001e0080d0307040c1d0b00c11060031200461b0148510100c48400e5130702d070342c00c1c010110141e5640c42900d582490842c4115a040302041c00c214400e40c00808502c145a82d40d09040414800c01001d401d00740f505002c0a581081810940308240c0794044900301c881c40303600d50b10701d141c003109042c154102404074030011034130504010000070094162001510b501c04c202c0200e420403607403481003c80013064420311101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 403443516 1250 403442266 403442279
    0x90114060a1214030c06040210020a120e040902043201030c06050f0c100b040c0302071505040f1a06190b0a110c04020a0e0a050607020a141f2115 64
    0x580036286100310300e00f061200da405049407468014521842d640d030040002c2c8000c5141001c100c16084681e80060542001c05840e000c00d12100319040d80c1c00c1c44442488240159a190700003001c0ba07134000e0080148224150914070034000154103035041d14111130040d034120b81c076100f106040b60351180800c00d8860600b50101c030690071004084c081100140482c100030304040c004040c3d06a5003440000d180740d040003c210503a1120503030401403510400c1f40c00c02051a007141162400404d034404a6942c407680303031104000f1a520806000031403402000580c420180c4e400d14080c0c142220100b103042c0400b1440c1d00344142c0c600c030b25407042804005550f8024041d0750380c09080328001b000d0701c142c1001000450160781c400341034400040c201090b000494074003c00c0380d40190030140c0700340741042aaa030101d0100300c01d50003851001d01c80101040320035a66036180d00c0442c1030070a40d0f08504e400c111800b0380796180415054490384160402c45144464510604e00782818030031241e0340041c03500300e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 403444766 1250 403443516 403443539
    0x70524010e180114090a060c0806060405060c070302220b04020412020d05120f070c35010f1b080601030506090a0e0f030703110715090e0c13060503090114060a 70
    0x14a0b50300326540340e620942e03002100c5240e09106402d094003a285803c0f45141030300032905402200418030040b0401e20407036403505c0080c2c074143d8600392a12540d40004646071f901c2c2090b030f035000a6100181708401d88080085074800039403c1d0694809000c208102c604210070b9002d00d000d0040900e0000340050054500f548109421a01543c21b0311260841071411007aa54040b0240c0e1080e608001545000c00400075841d100800342d0790510780f01c0064401c401444041c00c202c01d01070440c1e0400960005500c01c0d8403400051000e0703003080100301c1d8400403102ca02224801903401099180300000c00950080c0100e920070302c1e00805510f03140c2c0d214a4548010201c0e6a0300440d544a40d803004a041c5004000401290f07020340c40303591180c03001d41c840714603000c480e8108442a0340c0002e503030300c816a004a0b404047e20450402c81b50b0f10ba8502a504041e40500341c441c1c041c100b441400040d6482d0020011800340c80d20400902012410fa45140035a44090700c0e0740d608441c0114007005482000d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 403446016 1250 403444766 403444801
    0xf08030711060d020c0a08092b02011103040f0f05040f090308190207080708040e0108070e01060806120129010905030705040f02090907030b2e0305071202070524010e 73
    0xd076801400d25005c82055490060300080c11100d034140014a0070103482c0036644002045841d8000402d0460f4507800c8a00c0c11503400d80090621006101400c0029414000e4501402d85a050307502c1980c2e982c0d1303c4060552243c070405015900c0d12101240125440c068540f00a8064888990b55241c80c8141c51b0891420365810008560900046000844e400001c081c840c3c052000c041e200d600f41982c2c001c01500c10b034808821540b000301300f00b010701643c043c118110340883c1080100c83d40da40c4041400904a01401c1210354a40801031401c052000e0410f001103501c20714940203050000019140e8914030b0045541c150f000c000104481c2c9416049005000780e903040150401a04001141043c0e10035944070000ca07850300d095000c24100101c441c10520740c60502c942111176005c600418040000071013400300341e25180007820090240c141c006002e02c28010031595400c8509025440341c6440d4502a6030282002140110b0140c841010f030588918014061341030f2540c4001c401e107400715 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 403447266 1250 403446016 403446037
    0x6050a0806010c0201030b13090606060f0c0f02040b0a0806090c01110c040b2e02010b03030f041e03051002130506040312051c15080115060206060d051509070f0803071106 75
    0x250400c2c0c1f00705803075008580c01e040800d1000071450403510304d40b520646815407c00c100b044030218400082540c0041c0300700700d058000c2040c04050800c4e00128019120008803d078026882c136000150402c00020980d00c10340c1503400350740c1c103460b0003001120b010300f8403646c940c038590201e0701214091030168424881444018501c20384000b128288071506142c3e4001666104201c403a00701c0308a13028000c3c1054001c003100510303c3d000c0000c0c025481405540100001c0c1003044651200f0010b68180040147d50801d080b500d440c926400c100010350300201c614048200142000110750401005860a8aa10110405141c3e001d00c00c11500c0740c11003140c40c00b40707084211201c1c44d454154401c81544406400b00d08150b00d040030b02c0c0e9030940314004a4071440c524801020003425a001c00c6050b04650200c07882004080c081c02c02501c1d0900c1d00504080c081110014800361800009601045511020003080c13043e070b0f01c0301110385034000c802000d84001103200d0003070f00a1900e50010f1161411 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 403448516 1250 403447266 403447271
    0x90b0d06051906262d0f01150503060321040f080706270315020702031603051203041a060604080105090a110406180906060e10060906050a0806010c020103 68
    0x544100040c0409010110380e00c80410b105070520195902035600b400318102c81110111100c0504075140c02c00e003000f840c1411151030306002424014032107110450b40c1d1302d103690320081414450000d40c802c28003885524019442000e1554540f40103900f0b591050f100140584a070541c109000075008405104000040104000c04150110807862440c007808181005001d4582440d401514280d902981c86500d408800c148100c400700e010300c13000036a0361105107a08600d0945902030301178051030f00001d41c07602401240d5040c0341503528140c0c046900400c1251019512071005545ca40301c161405410356440005903500c801d1403441540e004000a0310303036480c0c95914050b0700c0c05c42e04241c58901040e00485000c0051041704128181d000604a8041000c6880c041b0700c09113020310101c1e01d40100d900c42d040c034020b028407540443c009160038459810740b85840180095140300500561002c91841e0101242242c41a019520b20340ca543e140c002c46502c070a401501e035000c00742c208a0400d078 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 403449766 1250 403448516 403448519
    0x150f04230106020106081b1f0201061205061e0c040314070e0901050a0b2d0418050706030c0305150607060e030d0917030c0306150c030406050307021c090b0d06 70
    0x468035414500030b210075400005c0d45810840b03d2402c0540301c071403c03540280111001d40f005d644125141c800740c070111040240400c040002a4017410382907001804141400920205108011986d50b110340b40314100180c6000d00076400c3d808200042c1c40c1c503201c24a007804248006100740c0c8528a840d042c480c200c4030001c0c0c0d00c071000b62109400b1a00c440490f5154428040010395901070504c032902c2c2114520b00d5003d4109104040d0795607040007003042034200c10700c612191519800440c80b036640348400d10460301c0300e044c0700340e441c50103216410010f4500404150308034400d11400d401072030540c1c05102c0d01071500c01002416084101d040d1903695030344c908114100410801000c4002c0540c03c0818441802c0c248054181c0c1c60407040c10030038504008010445a03404c0072650f02c450115500d0581008000307243d03045009455080d00f43d88070000b00410200c1d04400614415a4254203d441840c0c0c54208030b9150401a0004d0000c1907400c4002e00c0344000041c040c2030102d050312000201c15 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 403451016 1250 403449766 403449821
    0xb040e010b0f0f2106010c210302092106010902030c0a0525030801060e06030423100204060c020906100c02010f05070204090f021005040b071209050324150f04 70
    0x180e00c4440d6030003200c403902c0031142942c49841ca44c541e01c5402404c000325122001d44a20074814001c80f407201c407034103141c10300c586168020760550f01c00d14400f400b19442584102c030081e08140100c410540c0d0381c031031440005404512070080780c0c45052000324050911101080680d00351308191800381e030b02c40d00e14000300010002441403070016800b03950703012895490b000c1c0107882c09590804090003000304004020104601026004c000703034003005000b00c0c0390764400d0042c0c2081070200d203140301c05000140015125611a8842100e03900884078003505032030306820005115006558840031801c4403040c50050744c0911003100307540300720f420300c1403034011190700040c1203403205c84084403010b13400300b80c40d001e40c14020f8084001080505000385098107280304190280a500b0300208100c0091400c4045c15200d13000c035030010440170741100c608001142880103449100c3c0b01191154950500041740000725104514040c2000783c2007410688298040c000541041100241d40c7c191401c15003640 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 403452266 1250 403451016 403451047
    0x52407080d1406010e03010b060909090c060a02030a09050d0b04240f02180109030309030f0309271443050a080a09110d0c0503010e0c04060b040e010b0f 67
    0x82d1280c1410002c8610b40080050462140c0400c0517009138940301c030020aa80307442d400c881c01003404981418060b5500707030f4500e18000c01c0c0d200180e0810000b00b41d604440340c000000c1c0c040c90901d501c0d0940c01d5511041030000400840e038000e0030095a2501040105941030401c889040c4e88810718658100c08600c20400e880002c0d001800300c0340c1c00142d40004030344651414949039403d180100c115403464030000c25409030b40c04090038840c07052180d40205801440804010302c0341c4ca0b22031040040320240a85c05001d42507000c07101505088448220104940d20144943d5510754030a80400103400a0151403002c2140259041216402e00443c2c802c000f1054145217250341d5426540c0800140c000c00f481c102400d203101560034215101300180c01080a0302c10404103079015441500103007000b00b184c00071a8401c40d0503501c1d010341403a00e04408100390088420070748051100da03503640480c80840c4210703c2003a840c04000c000500c10100791200400420420035602428128509141000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 403453516 1250 403452266 403452281
    0x905040c0c03080f13020108130b0109090510200a021018031206120206090613420509010c0b1f1d040b100b0304051501052407080d 58
    0x21545101d45501090b034415035040d0700c00c42103600300740582440c04111400b15080d03c002070501070340e8000078145007520002e087c0d4042d000800c070310044d651540d0100c0149400701c8252024011035005600800c0749018010a101c2d842c0c810001d0a0702c2c2450100a5420005103d01103002d810000803603200c441c040d5103e1281c81280d899104600c03868080c02c920301c80c40507080c1c3e040c00c244040000d9800301a40ba47c240360182e403925910014900011228490041ca500c0b000d15480c001203a13010341e040300c07001c40041640010281124000c41c1c0883c0110034024481c41c96003045d9808081c620a8016011140042c10b05505540240d601e000701c040041b5402540000d20607a207210000c1c8108600004040755200f00350721540e0100501460400240b000d4905a0f040000c116600c010142d600c0083c0090000103071281040d1810b04c0e101e8043e402d1804e60074400c840041040e03d005242d01380030300c81e1248020041031000ca200040394000070002d450f070f68014090f00d4005545c5000302e95 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 403454766 1250 403453516 403453541
    0x5150720010306080d09060507140303040501052202150c0a050d2105010303020309090c0c0106030312060e100e0718180509030906070b0402030c12030a08010602240601090504 77
    0xc00225012000600321030443c0d0020b16180e02c0b0000a2201a411000f034034140e4405203009940e54081d420000c81c1a05800b04802c3c19100000800c818407006511550060354415072040080e8104281000303448010300000e5071051030307907021610100e100e100408106040c10305580b452071040e25850704111b000250304001c070725a09640020b209030309103003c4040014100411482d410368500941d00c2c058039064900980303140d00402c40c82501d1100b80c80540c0c1d840c1c2c001380915500c1e460001c020380210205103165500701403010070800b1000c200c0e607209007000f0304a405a00e1078121410500740e1302400c48424802101c0301c0b0f2610148624000000c1c00038a0b440030001c11b40c1d05101400c40303400420a50190f0414860001c003a92100c00711803505403c003070a4001a221400040d040101d102900c640c80201d402410841640200113400f404185031580022a1f0740c91b801a40c0720303054050490209881c00c24440e486010344201c036504540c042c545216429114000b00d41121034296451 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 403456016 1250 403454766 403454813
    0xf06180a0e07020f0303010609090903090305030a0504091505100f0e09040c06080a0c020d030e010f0204091407020606011407030e1909060605090d06050910050c0301090c020f07051507 81
    0x41203a43e01008150007a80e2240003c601d15031421348020201e4140d0f024000e0361a840742980c00c28188a00182c40c0078603040415240e59202e5210042c1c80703a88140304a9285500b40b62840050503013070035000003107820180c0b51031451400c1c0d440032550304c0350300900202800f0610f481c1c01c019480740009079110f03e100d401100005400c02101a01c01e14008041c03030502070502c9035440003a03501180c1c40120045604020410b41c21110314540900405e880f142021341c404a40023131400042d0b000f0280300c8881d4078a600450320360503000c030703220081140c00902281d200c40400086060303a20040051a0091401c078200980c00000282c090501801c03d085280324400248801c0d1828820700d0000c1c8540d090062900c601c0c0030102e24807119841000d0031850b511030014070141d0b401c2c0300300c068203249420100002d241c000d00c02c000d42e4000303004141109182201711642e0500001e1458025005100240003141c9000c2c00c11440401540c2d05400da00410702c0150b000482003800c0302c60704000880d60 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 403457266 1250 403456016 403456021
    0x21030f0c060f1a0402130b031e090a021002030c0604030503040c09020a1d0a030b06090705120405250506031611030a02010b0312070c03060b0102011b1107060e0f06180a0e 75
    0xf061500321200b0340c46100718410030403684e602402d1700704201103401c1840240c0d100d0756100c1556940740313985908850b10301c00b95402c1100a20020459101c814422600c600c101220348a0881e034a010708080b20460768000004100802d0107980950782c014814a0070650480e110041001680c01040d600000705584090900112003d4103034540480c1d004e4030507481891441c1c407082d501e5080035220501600d9101c0100d002907120710102c0705203c0d6185088501da08192511954602400e000380c540352021850003850659044140422200c2c000c0441c1c0c00c44e2030301e00007442c0c032061040d060401d0200001929201e04024800b070602c10506400019802c4045024541016040c40f00010301c001c08020100015400038100c1080d01d40000c40098148075202c0180c0c0180107040c80c6a52610309070101601c203580c8107600104464040d0261607a49907680c4041d5208002040c001c3d500c50302c00800100740d8107240c005040ca1031031030144280251700440c08501c0c0c0c109150041e5440c0d0300501c04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 403458516 1250 403457266 403457291
    0x180f0b0d03051e0f0d0e01240e1f03031d130603020909010b09041401240303020d08011a130504140108071220030309090f1021030f0c060f 61
    0x18200402215800d0741d240020240c2121145d00c07481d0140b01c0b000355101c4200e011000709601441110070440c4072405a4038084c4904500000e281c455280c100006a000030b0340b802030007407c5480c01c0301d0441090380b002c2c00c1d40d03400d5905550071440380c0020522003141c000e81342d40e22040d85105000d28400060714a05500500000d08001003103443c4581c141a104402902c0d44c0841d40d03442a0070010159841800103500b502402c5544400540b5443c00318040c110081504c44500c1242c2c4a80c007125400f000c1c0c40c4040d5070022007441030007003505824200d0f14010b0b0750940200702000c40000391042c0ca0341c4031000101200c5000c0d0f2401c0340c100d24500140a004010403084000d410041802503000d5000d030303221f26921403131000d07001800320039600310b0519031020810384820b454020096842e80c5450419542c4500085076100a02c80141200060104000a4186403c0d003803000c0801c04001d2074800b0f03243c030f6510001701c3d0200040038913210003003006481400050994010007042c40c003800300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 403459766 1250 403458516 403458547
    0x60301110304050d08130501020403050607081e010306150f090204090c08040803060d080f0a020a120c03080c0903030705030d0207031805060d09110a090905060f01180f0b0d0305 78
    0x3010006410400c24840440c0c0000303a800c034048410b00c0c088403242d13501d200d902003a201d00c0c00010315541c00490080100034011030124414151580e450b42d03150b541c07010800c161204030361b4a0b042c803601d150060011414a07042000c502d80003403035000380a51344003160321440b08039503c902c40680c0d01041c1440544030ba03000d0342e0100c1480341f6215080e42020f4403211114480070306800d01c182000c40140b006c009100c0309807403001e611050752a440b500d4102019441c0e00c260402142c9005031440b1007c2ca0314052a02645030b1074241d0307251507803943d50208401d05035009080b0b103076051100f40120800114200700804410400160258a4840b985005402d40c00c1d40380250a0748000e4035400c1c401e0344c0b14002650400c288810000c0364050103414a083c40c420040c0c0c00c2d80d0004050302012804d00c0c0203402007241144504101d580e69581d06500407007110f028010080340110500003c4a9610b00d5000078286042004000514400940001d07a65600c1ea01e01100880c1001c90420f210a4510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 403461016 1250 403459766 403459781
    0x203010e0309090711070506040e04050708030a02030a031503020a060903030e01031b0810031707030813020306040b0903040e24010315091515030209030610030201080601050702190905060301 84
    0xc0c0114200b1250000181020a004254004010302c401c0d40c1e6581800c2001040002c0030003420b0150346036110015812015811141542c1c540b06001c0001b502d0707840001121041c5c0c40e15030181d8104051600210060318440c0040c5c034004a805001002681d03a41d505a801440e50340c03588103141b480c40c81d016040d00003c214103410300d8540f1844800c40d0710340e0040700d52080120710b40038000d980c1b413201c4171980914580000d44001626920500030440240003007268600946864032107a46443c18400459400c2a000b5059081100480c0000300e5810b62a9000310780b05c0b003601d041c0fa8544403081d0400d101207902c2503040003400154803c819402030700c00307030270300c4203280070310911642446284410030300f4416212200d40c0c501580394600e61400580c006080050071460500108410060182d0030000d0040c1c07080c010b11000c981e4885194524804070395068441c41000da0368040103403019084110183d0304240d81c1705c81d80120b81d1300c445d05480540249034000901e81040000c0c1404c64000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 403462266 1250 403461016 403461041
    0x80108010606090e0c0c1015050d080403080a050f07060209040b060c070b0d02071505060306060d050a03081e1f0f060e0d06230f0627061912020301 65
    0x108141480010350100c00034059800307180c10b0711344945450703007120300781d1041460000c1d060003140040b0103440e03074640140154280f0030000c2c5202907251170803c100d1050040d402840e804081200b00300040e001005001d407010a030800e9810b00c03100d100c0310b07655a800303000c04440c1c965002521020529051140b41807040090300c10746d049c0a003402c600b41c0e0f9100c041c020b10700d10320b03030104030602080020380480c0e40295020f0304103555010380304050030280006076181e6100b4041d41000444a081034288881c1c1e0341d8100f0001c1500300d5544d141558010300c0500300704080c105829403d1044104c0d10082d9006840081c1503000821503581c0c01e00040740315401c4210481c90718082000201d62101d0801c0035035074102c440d091080090301d03025000b802581c807041e01002c0340003caa211108134481c19441f41d494410310403001da4801c0f00f0003502d0110040d2142d02c2010195000c8400380a550038203511041c00761101007000302c00500b4800b01a043d40c02002c030034242c09a03900442c00c0030301800040304c14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 403463516 1250 403462266 403462271
    0xb0306010b180420220e1003030f030f0207140601080102130e1302180108010b040b0a06030c200a02010e100c030809101b20060c0f04170d08010801 65
    0x445066100720b0360000325582c3c0c4220344071001c0b0542c1390241030700400e00b41a030780e01e4656101c1a0696004590840740e8801900c4210143d0000b42035103e00c011502c00d02244111421550459800f075841020030b0000108166541601024003100391005010489c0150140c25024011040c600d01e001c80580210520764014003840000a510300c0c01c100c151901c50344044d0580c0e440209130f0103030401150002e540300d209400250250107640369594140e8003a0402441140707141410303c0191a03420b041740f80c01024840040003400d119600c4023010311001d1400c0780000403330300c4050300d0710019204400705035000f0181d07880440d0703041903034040c4420054440c281d010f0142c44001d04004415040035091240f07000000703045c4182400044203c8800403010040300440c5c0c4146c1740c40402810110b0041200400e081c00c12000d1074189030413211000000b45a295a03400268190350020400c0620b01d80041c00041840001c0c0380001400385142002858062000e2a0050013580c040e0302c0a02140d2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 403464766 1250 403463516 403463527
    0x3060117190c1202010c120801031412030a0506040b1002030a180f1202060d05040c061202130b13031401050f1006020607030b060705010911012003070f08040503030703030b0306010b 80
    0x80a8001c640c08035151503800c003a001d0420b00046c1e0784502c4d0403800406040382d0f40d8842080d0b40c4c2090480381030301c0c000c62021402000d8a04401c0c0d0b5000d9100442c8005d00013031001510040135038214603803000000c0c10108900f07660401040e11025803441d8080503820100e8035103400c951200003011b0b0288001c020880191074001010480400d60040546000400090800390345500046540c180c4000408011924141c200350020682c20700400e00065804440c03c41c03c851213000741c131509480105820300040c500818808162711402504078440c0e841840007011805202c1004101c40c081000402c0f94540344c25401d4001200901080c1090840d4109220b502e6001410710742c440411308001415403141c1d0300003105c1c0d0142c0c420050856007096510020001000c6009d1101a003c0e200e2a0780321002016540c1c1842004106041981c800e05c951008928a01e01c040904c1d4000c0f01007503e450f484a002c40e0031540081029401300e030300c45240b81034074202009100c0c01818018515820403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 403466016 1250 403464766 403464773
    0xc1b0a050d060c0c140105040c050d120c03140a02010209030d0201060e1303050d0906020c060c0a020a030e060408060702160504020702060d0209040b0a1202091005010207050904060b0306011719 85
    0xa018000c00030300304503590f43d4008a040d02814600040070f41107404041c01a04010350103002c0c1c24100c1e811207038900e41146c0020a0709041a05e40b000702d502c000c81d4141010401c000316076061b00d0784801da0400c414150505450003860004003050310715a800565162120300602d86000f481800c103404580c9403803000c11526000040d40f0703070808000c9010400000d070700c1c1130465a6009803141032a11926180703041003000800c0c2d00401d0f40b2450002075600b43c0d50f44856002c224020681e01750b016800003080540003030301c248441912035800409c420305040d282c101036403510b00308aa00c24003684c0400c0314181c000c219954050000c0104490035413900b4500c1d4003199941c001c045401c078405401160b003a000c1d030303110741080c80d000307a0203080440910341d0760301c42d05c000d036005032400c5e0302508285006c00d01d01840c000c004029608180c0080620074a8a014800b0203000140f041e03c0d0780741d6541c1c1b4503180d6582806030324001c002c441a208240504440c8480c281100511107418402c0c0100c00311000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 403467266 1250 403466016 403466029
    0xb0a0e1e0f100b030a06050402040609030b0f040b010501050d14100501021c1b02130e0607030605030303010e060f06040314210a080604020d0e0610030c0b03040807060f0b03030c1b0a05 81
    0x20740300640c07000b5131a80c580c805002e010b0101074000c65480360000c200841c445510104107001c4901442c28450300b600c4100c0180200001034a018094120b0700006021550081008040d0110820800984088441308180340c2007429100035003100008507041203071f907034100100c808601d0200e811013000b01441ca0043c043c0b011000aa05c3c0191b04000007205640d6040b05a000100490302e082c0400d401462541c0d44032070048079403001007450134002190b60309000003920b0580703106481404194440d0420880700d8407071540c2c20750f8000003c001c003000107510007134084c01d489900d9000f466100b840302440d1400c000e488440c1c003032200061100d41c000660100e1496000350058800507510300748041a030340640007500083c8080e104110034418050325544622088a0007114002d240f20740b00c0031001d0b01c92005850242c5039a00521001012038401d6202000310038840100007120505240440c0c2950004044041c0d84e8100080390101e480e101c011503000004110b8100e101c3c01d0408001410 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 403468516 1250 403467266 403467269
    0xb2509050910120309081204050310111611041802010816090b0f09040f0c17060d02090106030c0327170906030c070606050a0609090b0a0e1e0f10 64
    0x300d500301001042480707103110b01e44006400048260410700d070080c100601048241d00c0744502910400f55140951590401650b0a81d45d0041c0038201054600b40c800c00648201041f656002d0810000c00f100503002080100602c0d200f106030f04041100c0300104000c89134841e00500241203c0148130300180c2e82300206940c400030f4144440c51086c80341404039480c0f516908485660301c00020040140f00751100501b421f4981280d09102d40c02c0b00002c03081c0bd960030b03000d880c400b040c1e102080240c01c2c1c69282805a000d503000d007244042e41d07402e03000548039007420307407148021980e1200c900d4422941806078058000f600c041c410704950241d1407451b031043d24410080c08103000040096245541c1c8812035885400040250341c4a00b0b00c60400c1801ea40400d0b0211401464010006107904107604000211190740e262010501e00c2e120241c03003d017006010b80b036444003040c0c102250758a20021940d008401071072050400d51440c81d40c2c174502800140a0180c281014020480400030420b1042c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 403469766 1250 403468516 403468519
    0x20a150506151e03091e0d050a0f0e18190e0714010c02030d0e0a0e060d0201050c01021207031e0b0d1b171005010b0c0a140a0c030b250905 61
    0x1903881108002c3d140c0d01c5100d1541c0041d50b81d8001084c024107480015a0803006041030210800c143d0041c59520b5482c98030407000340206605228802c9124081c024108207002c940c20324083d840781c4d210000354030030f0740289110b81500503c8180710b11030344881010782000d52148010481d0032140303c1b6031a038440c407030702c41c80540c2e840004224025034440d10301c4a034200d1703015003194031480b0b0280e03025210081c0205c0c1c050094039580000509110440321b214007a1101a0140f03000c150030350011600c6074080181040c2540d02048020040050708440d28428203595400241041c56852015005040e004008600340c1c1032840c0607000d070350b913072014170a0740e540001c0c4504044e4030356403641201c6440741e008d081c2c94000b8500c008201007021404c1e5100407800703171081049a8984100c0700c010f0040414003441079020000b0240083e400703180c5c0e060b00619190840b100a803050740e4818450003d5003003100d49041d00c40230300c000303d0003100061400d20341903400711020741d0111100034102d0701c2611446 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 403471016 1250 403469766 403469809
    0xd090504020a180b0301030516030308070e401103010e06040b090703020306180f180111040308090405010501030513111f0201050709050a06090b1315020a150506 71
    0x401489015000e0104600c00c24110400190340d1006124019042440f064a0300e009270305075007510b460078640c003400f500ea140e110168162110003040366003010035a20700382c004652081030085101c07840000d0b1030441c040b400e010300070001c20204a10302249581186400e504141c0c0181d503060f40e800c00d40b4151049581901000d5503490000340182100e60001900710340e903174062000c0564140c0045101d840c00b41c0700c11002920b901c543e001100412181104070402c207030b0200314041281e29040b0082c00a110003c5810700c50b944110344244c3c856401215a1040054244250304140c0556070041c0807d0030100101d00d40501e0703d40c407402c00c0c510020812014440aa280e5640d28a0a00c400c03000403c00b4413000d464900c800790080c6020340e40ba1000c2040b034200020300e031501222000039124150f0b902c407100d40c601403070303001140c120412a80c2ea11540031710110f405913000c0038102030129994010030302d480480c10008425020180c0c6951110b08000800140c3e0700d030980d0400301503140d101003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 403472266 1250 403471016 403471027
    0x50f030c0706060f0f08030301140409060e0d020709050c03010e01060c031704081206150a030b0d1a18060c0403020d050c04060b0a02010b0102031201062a061401080d09050402 77
    0x4040491003400e00c020705142c5011000700300ca244c07180c488401d40f0280561201c6858580c2003182e070760b01091090303045031208200400400d06260f000600118842c070004254406880106411b01214156400c010791180c01c00300011821805444d410081c2e5594961465040881d14030401905014400620040303211820401d80f0039041850541c0141d4841d017140d007458a8021a41c1e4001400d40203402c2241c80803038244e143c03101040100444101c540c0d8508140c041080c3c0140000804540d44032064104c910007244034000340c1400700688014000f01d61502e45603049074000080c004243c9940714200700404d500e0300e03404650a82e5011100718540d10014035256282c016000d03800342e040303400c0100003d80c3c840f00c40c1c040c2c048550160003d0000e600418012643c034080d41c1d0302c00ca4042000001084401d001c2c406e050ac034400004412032180c0c050008032003c04812907000c4076010303503928034204d80007035440027a405401c02e24081c00d627404881c0741c02803400019002d228461940000c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 403473516 1250 403472266 403472281
    0x18150c1b050c06130e070e01030c020607080f0903070c0e040204180510020d0f020d140c0f090409050a120809061e0f0a150b070204060b0405090f06031212100510050f03 74
    0x1c904d4001c00b8004c10f1a00649480c0100420151f5403c004d240400d0524160040a80c00402c811707200315035543c1c0380da0701607a545258140248000d04000850b01080081001191081030300e0030141010002c9268a400c0600c144001c4449000d015180b06015000342c4001400203c2c24500c82009100c01580798200520540014005c525210104507c00030f00e040c040007164000003c4100b60140c03840c11503494020440080c03049502c4c088500400300880c0080d441c050740001c0744640104201e640d041d2040d941d191243c4548580c03034002c5481e20b0100407421400300a078a07400400e400c034998803000040c0c44509545405441c0651070107404000501c000c25960000d00007600303103010070400d6603481403880700a9000b05400d030b002d80e041031004250808054103d8049403006449022140d0729104030700307011403026010301c0d41130040c0f21842800c0c0c60008040c00800e500c60220392803d090503089464107100980c0b150780912440d804840220f0703084410740b00c00340700804400d5502d5440c2c20 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 403474766 1250 403473516 403473547
    0xc03040e0412030c020102090d0318030615030b0604060302010507030507020f2d0402030103020a05150706060b04230102190c03050f060702061b0d18150c1b050c06 72
    0x200304828048030401008107214261450903040141034074100201060110128240d10600900541001085051400081c45020281d16010800170315802481d180da6900050380c5103043c0c4c4140d1040801401e205000e030303103006603410500c01c81d020050340c0d1941d80082c0583c001c17220054103100c0e010406d00c0a54861004005607240002c2c81c0c16000032200501540b40507413100074040c1c49411442103600c500b42413085078141d9400900c1004414580000c1000b1003404e200c154001760001c1c4070100000f50b041c042c00c405050403e40440c0c86508002d00b910740301400c5070309042c0e0003129848c40c041c1c0d03980100f02e06841070b0120808802072000e0f03042c041d413140415030000b01240f0908100b84100034000c500350380581003550070b80e05103440d403403003074480107010341181600001c00300069418094541e02010044001d240004a07069140c0c407803403100d0880ea030b28100304940b104401c501c00d0340c8c03159298800e032501c55040200307074040d900d030643c4d109049002c95001d08800540c1e200e1500f0b03c7e9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 403476016 1250 403474766 403474769
    0x302091806190905220f0b041b09020d0506100903141203040602030406060b04030c3005060f0c0f0712051308010905120301080d200106030f020f060703020d03020c0304 74
    0x19410303856282c1d03443d048100102000c65811120581c403a045142080081c04c844049a8011220b0341e6207240a45480c1c0000038080c0044658010550500d50a4940403521704014042c3d000016250010303e00c0283c241d0301c0080005109800c40c01c03081c810079801c00c0800d01a80d8200c8000038040d8908002d080c907112401c0344160405c9408020401013000c0d6070002c1d8803451242c0800d00c5415941c208125140c007440c0002031004608110034000030b1a020001c400b021941c90100320034a41c844071803101c1107029242a039840d0458000c02036101d03415402c003034100700140082e914010302d0482080c41801842c4006001200340040509020721404c1a501d2921001c289000f10658841e80c884c001d014541e401c0340d090090500c81e000101c90745066904a81c02c181c050841a03075203079800c480c00c1c2100ea9008001c8d5403a8109200f49407402d1041d107010718424001038582031a80c0c0104010f08100803003043c8206402c01c02480083c0e07000c59810500056030801585802003180750b2070550085 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 403477266 1250 403476016 403476049
    0x9050721020904290a030201021515090103030206071e0f030506060f0f07060506031b010c0c260f07120f06090501050403031b0c0507140406080111090a060302091806 73
    0x1303040c1e03081003080302c40b90202c403448203022000b5440382c103000034030552046501c4040d015800c04010b0902c0000345e007419070390040807458034107400003001c0e0004032890000c2c0c0050300140d000301c082005542d08a06c0700350621101c1c04a8035401030301248014090056200c800c804c06442d80042102921443d055400701d080d41c2000c0d94544c122400004501c1e00954400d80f00982420003007101401c001c0b40007020360f11542c001c40ca0310b1807079100649180c01c40c104115480b1001e840000f8480e041c408100354881c284600080300d26680581c4185003101800082100d074101200030840b03010b4103a41e0300101035001320041011031072403d145004044842000d0155400c00c1e0030401010381c9070380050f4842d088061440c1659a03000170440c0c42010801005109030b026070003c0c4044d1411a90b07800c1c3c00080200082640350312552017500b942c3c0c080900038542354010503000418134004004401401051a04504200101001403003c40c0c10708420301400290300086030094445a8040c5101c1c0c42e07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 403478516 1250 403477266 403477271
    0x908010c260c040504051302040f0b01020c150712140403050a02090f1005041a0303300f0705070602070209151e0607020f011b0803060102010609050721020904 70
    0x59214081c0030304441401429407403155800030015546901c4546001c2c0718600e252904240c1044107100007804042d01411032400d0b021030f0400107a440b03010710f1808410700103001c40e20043c61800a407401d00c440b10154420140400b181142c1c1c54241c09440425410083c2c11446600820080d07540a540c205002c2d0315480014010040c444000348102d640c81c8260303800300085ea0b9102503a1500081552448080015802c0404c600d19050b0030443d00101060702c0c0c0490030b03618400184c5183d11803011b4120454030100110348060700b40701c075007180169230310680c2607920341070100801e184802450f20301030042c08035a142c01d0010650550b0b030229406000c5100d01e0404000740410364885401a510030031441ea20031000501c01d170450542507401070b21003418000796500b084890480204201d041010740d0700d003e03125859240c813559503180034891ba41e0303503130038800c0009080d00c03290313001084414244420300c4411503211041c4a03892401e5050841e100c1c07184080100a4132541d141a03501a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 403479766 1250 403478516 403478531
    0xb150c0c09074b120c1814040501080109230309040f0e0106050f0109091109091e0f07140a12020414011101060f050108040f050d0e030d140316090801 66
    0x9003207902c01d03c00c200c0010396210f0252041c03100164200708070301050000744030301e6100244c401d058000700d0f440403003820711400341ca003061030012000c415035101c02c00e268940003800e41d039410540300e5580034140820090007091229220728240c0305411074061181400c1018020300042c0600a4902d9400c000788140903104540c04c1400c081c280422440045519054000440d8640540f41c0c80c6050410703141c4c0004185000e95a800501807520903425180d0100000c0400e0381c0c0d0b400403d4412104880065940040d0311039140181c04020980c208150181c0c0034080d0740c0380c01111401a408881151981d40e1110080c216416202c1d46805030340c80e800800c010520304011130304480e024900f0b0380c48220072240342c0980342c00d9454501c21000d0a0040c510103004075489503090660060081c194030341d44084503651a0b00c4d084505994900065034070700400f045103014005460603601e17625110140300581c001e100d08520014242c00900080340f14400b8101d0b00610144000f400740310000c0000c0c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 403481016 1250 403479766 403479827
    0x1303050307140f0d02120d02090612040309120b0a020703020a020901080c010f0302180108042d020f091506300403030c02060c03061005040909060b150c0c0907 70
    0xd203403050800a401a22400c0d20724481c0044c0c0989000c0f2240d00070801d40764100303445803440e80704280115009400300400c0c2030030b403034420003045a07101e070030096405458507003401040c520154000e0003010b5461f200d11004140c891000d160080c0d17594000503a00d510601e0140c0c50409140c01c02500049030b03600009441e00081001003640c1c03c2a00c0c1c8501c00b0100d1002103080f80300781407000781501e10100ba128202c2d48210341e80e9a2081c03046181030112184500c0102d51960703640c07402d1031545c0200c06040c085050403900310150301c1d401d0305e0003490b9050640b00840a03186000b040d60280c1c40105113103004050200101e070400c0d1407809056034080b041b5154800600048a0a40101e420305900912051002a005201d511070340c06c42d909613140c20b010841c0789002404500c080000c14000422041c100e48540d180a80c8986e00010300d0f0348642c4107000580040601c6d040c403912041c004d889540c0d50124001c0040c060031a1a045207990740c140564003e4061941d00003510b480e400703419101d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 403482266 1250 403481016 403481033
    0x31109040e0d020c060705101a0d0606180b010c0b101e0e13050a081c0c03050720030702040e0a1406040b0a050c090112060e1009050a0506151303050307 67
    0x51000d0341c2d00781e5503000c11100610100b0302c03032100020a6235001d00d002d000d03802e40076800b03888440311000f0018508400440051600360b441001612503554402c010881f215200b13075140e0440b02903a00a000b104090350020b0180a072602000c0e1034488038100051483c0915668803002d0000d4100440a004801c1c4050f0204800303401440031003580e080200740304161000c500b0075803990040c001c0038410b03000d540e1904076802080003240c01d0f00941620031449440d502810082d5407140e40c002880b4a40501c00900021407034441c203105003519010b0400c8008080301320f802907501501c0114900310080384007071502080c000c02900708076403284009880c1c0400f0072481c1c0501d00410a0505c5900c45025940c00c030f0310140d07000c000f244010840b076940d55000b6480d13a00000000326000a8031580c410110708982c0c0203c41141314403480303150034080600300b4815290400d03011102085180f40c4000405c0380d8000007003c030040b0200110b01c594a9140c400300b031a026650080542c0d80701d42662400d140d6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 403483516 1250 403482266 403482283
    0xb040e06150c0c03100501050f0105071718030c011e0522031a0f0c040608070203070b010e1006090f060315152a020904020405060102010b030f0f120f070201031109040e 74
    0x440d00585c4424400e41c005c0e802040d0588a000308219001c200190041d50f042d405400708503542203041080003d44015030003c0e001001c0616402c1140c0c15800040500b082d5091900506000007600324200c02200c0c0040480d03800c007141050382c0c3d00c410000b2006000e481140c41c1225000f001c0303402104008082050120003c00313030500d01c0540d00d51880444100504a9080c42c2404090004004641c8540c1c6c010b5008042030068900c0c00c03409860388811074009130481c0310b0148104050029050031805010010501860070051203428a40560300800300c80c41048200744e15805000f004d483e40408900080c009583d14456502007514081d0601141858407100881035000c47e18810f011004507481c400d50060540c806559580d0800c4001c1a01801003811903581d41d540c0b10aa03182001140d148800140041c207050200c0b000203071a21074440724803400c480c0c2c280864802c0c0c5151109840242e98242008100d08403120400340c001c3c0645041030b035003c1d003000d0314500b0049021070b80d900c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 403484766 1250 403483516 403483519
    0x1d041b03051006021519141b09031c030e030c0f07060908251a0304060b030718090318090b0a0603020322050f0105100608010e010b040e06150c0c 64
    0x8074682d2507050442c002c69040c0700710000b61300310010141e49009155942d07a0300284000c9907a04103240082200304507220b400d1100f800300d10103014086105020302e5601400310302c400029140030300c0c03000441d480c0d01220301d14503c2070200010398500140250041418002c000307040b07942301c81c1c0d1060320642c2e4948000c10f801142c01764a0303000c07482c180304207146400d40e20400300418241240d2102c0d1002e852243c0c003595680609807901003107603d041844115080780740504103450741000d0030328008584c0141c0225100360f010020410400203c03200d04c8411691107170300001e0040c8141000e6981e1403503074003850a020428038001c12505030382d6001103d410300641d20024078a0315003a00b40d04a100c1500d4131100400308001ba240691260304100304554402c900350340b00386c2c0c24442004c1c25103505031680a401900c00310148a4994000704482c01007119940240b00f9500d804ca540030548114001c5101c0f450360000003514986505031030185205410196031b030354804041d0f0a40d00e9420022109 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 403486016 1250 403484766 403484771
    0x91d03030f07180f050603090a020312040e09070f0608042d030f030501050f150409050a02042c07050901030e06010605041502060c0f0c1005090703120305161d041b03 73
    0x210703105075000f03481030549844c92811000c6a00b0130081000c40e4100a103049124031442d101c240040c0c8003131244c0c140d061000c0410701d81f11400c1030102d0313040400080c80c140d04d079070001004214010105e06c00c00704840b1181800c1d034403515070782000000800d0b6524400304406a046100301d44006a81c0300076820303070090b035602c5c0700034044142c104c00744c0c0c40a1250035070008c41c405108490f03140400511459501d80c01000d451300e0380d514001e005842085a00c0b0303c09070385c0804d003080043c0f401980700300854410017544400c01003a940e4000000c2d0007820003c2007140210311039032164025070111401e02d244030121942c1c2d41c1c0d03840700100141d009000c0c10302c40d1a40c080611500900006c0c0050041c1c0c0d00c100b0060900555900450845e04080c030411603901c20034a104040d08824072400380200b1031100640300302811403c20082d94031002019904140c41c040070810340804502da48040001c0900d000b170810ba40000034101601001800c096001e03217001004a20001c201660042e0150252070a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 403487266 1250 403486016 403486037
    0x904081e16030f0e030601031b08060f01030611120103061a2e02150f091c030c030c05070206160809040f0204030212060c0708090a12030509011710091d03030f07 71
    0xb2240481c650400e135405030b100302c1c01440041e02c1036a608214103490300103120055903c1d8119460501c1c140c0340c8651f0040d50300014004e020940c0103070300b83c1c0718420481c03503d40740146016018a107814403002d8049681c441040d0658840004402e07004a0020854040001e0901d00c0b001c42c200c081c44440c3c504505905404c00781d17400465204032075000b0318a590300d650340f5041800c4207081c005002c081b40340180c0c4400740c5100c1d9190b40204480003d5a000205126164030107000c03240f126252400b80002440380900503519241100c0d9014041b40a41501c020701e480c004030503008420000340c0c0181000704182c22007070319901420491f80201c56811100403462650382c0c0b81d880c1a1401c5800355400c00c005004038621000510300020041d29006010396200c2260030076000c14002140000c6001422a02d20740c2d02801c030210118000e00032030140d040407060008040b0503485000100e5443c3c20081945600e50051040480d03100420f480d507030324040c004250384082c201c52072004951201272 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 403488516 1250 403487266 403487297
    0x81b0f091306080c06070204090b040b0f150d02190f140405160c08070c1a0a030b010f0f14042303120a020307170c07030b18010b0904081e1603 63
    0x3000c044a1000c0c029000c4c440058040c07000d80c0d400031405036046610341d03110720000303030700c1400f41489039000700002040e6040900d044050303808c01030800a14101e00048c091055591082c43ca02d10a41c112070196650785565440804075145074041c200010a0200c0051101e84411070064800e0086408114030b41c4e4032000f800a80b505048034100203250100c5040014001ca802040a140203503680c4c2c0641ea61850440ca040e000144081010380c40800e0040b00c06401d8003c40c454a0300c00d0030841c4818142003801800c481880e43d0b144100f0040348140400802c50f03a00322009020900041c68016800c4101d2580801da039481c528024410b11848041d021900c0c4190f8808160607400b80d0300c0c18a40340c80b001d0001c4a02c45074121031100410a44e10021400c02c1014015446400883d105c0c1c070b0a80c03d003501d401d000e440a001581d041014411095462424085c2c3c031a0384110320301c2d201c116400003130710b0104a0790645a01000b00040100342e401c648583c00b011940710b40d48500d0301414016 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 403489766 1250 403488516 403488521
    0x5012012040603061e1205120406030c080a0911061c09050309090601050406080c092b050d0203070302030429070b040506060a03110f031002040603090515040503030106081b0f0913 79
    0x5205d951641800d81800000361080b0242045401902110404e10740d5188003805940142e020b040030079a6039200488040c0c00c052050b50002144c2410081c084494955802219805070440c8c0320701c0c0700041d62180000e914080c01740f40c01248408004802e020b1801176500e44c4200d0160b0310417180900080c58544c4180210b606a42d8039079a00c400d41d840d41030441c4c80d03d802c00c1000b00c3e408120500c50103071645980c01d442d58401c400303c1d5040481019410458100728040c2c90040854004112030000300c0d40000403101110303040d8400c0c54400d054120312a0b9019800314401109860004049003403000f4458030a026500800566116071511b07400c208003815644002040101485038490061400c9640140c5408003d0300303480034200120181012a400380c0c1080000c240d0340d0355510f00b4414104070394005001b1210318100a41010748402d0b0ba030303000520400d401c0104d9000007484210451002003074030f101e801c41d495158094507900c05401d0b0070040045000d8500440c0c011141e18031070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 403491016 1250 403489766 403489799
    0x20f04180b180c01120209030709230a0c0e0d050f120309010c031e0e07050402161104050702150405070803070303060602100c051602060705151905100501201204060306 74
    0x503103528005c034130001184000b940150424039418041c096000800031014001d00210f0a5250100c0d10001c0141401c0c0e40650009090400200d1038640c01041064020040d503044290490b11428914031501d80030f0f1034207030b100b9a00e018501450081d421075006510145014056000007030219446d000c070110f0840314404802100090940180041e18051b6030044100084100903289510b4a0340007150917030341714054110000b01c070b1001c1b20b810301c42c403005031006004003102d05205038280b00400a56403d07051030900f4030024441d020030308201d001c02c0024024202c4c0c2043d00d072100d440713080240090107544600d9001d40107100300c50400050b47d1240041890b00382c1c9400e41070a01d9820854542100081c049030083c0c000c00c52540441c2c420442c00701400300c502c4815825103485071000307000c1d424401c00301507081e0a2a043c0110090b603680043c0641d4803c2c41d21200095602d1504c804421088140e0341c0c072401441180e46451101c14014000d40b15903031001c0c00110342c3e40c4210030481181 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 403492266 1250 403491016 403491019
    0x726030a0c150b0612042a0503011107022b15020a08070804020a0e10050a1e0524090f040507020a03020f030a020303010510030b0306100302040b04090302030304020f04180b180c 78
    0x4101e11803100c0224010380d90024040d1200000e410b114071f40f043c2004c20b160300c009621203104402006a840c00340111440001244c1d0311505100ea2940403030b4913452030703000c0d82042c800c0750103140c1142c44407501f1500c51160061201000d020903052100c00035403100c070030400041d080c0c2c400038490314001d038401c42c00b4070750203030203100300501e00034400604080c0a0800d212480010364005a240d0b92101060098004201400f103a040b01004243c5a282141e0110b40600020000492404c001c480d20920300c00d0840440fa55450310180050002d0b10003d480320341c02490b040520a002e540090100d0007103100b6021903003818116500f5542ea4050740c0b41a0700103900800041c851428901d448103c0b4100300e00b0082210440707200000e0804004032a40001400c1c05141001036141a004405010780296020800200709490080d164400100b01900601c0d90400c030210507113543d4003c0340700c00b60003821411070681c00d01d45861014801d80310f195554124901440c21041c000c00d246086030300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 403493516 1250 403492266 403492279
    0x20a0906060c0f020411041d0702070f0b07030c0803010815090115030201140c0703120e0a030c03030804030c0203060a0c020c03030301120b040507090c0807020f0c030726030a0c150b 80
    0x2050351140009034074080f04030b17002a11201c003a00e41c0c42a40c0041e101405900321182880d0080d180d413400f0106004090301c013194441e480c02c01940404506a805840d4040d02c00c65844045007030a4600c5001034000801a1744000000a04420033040050940b07034107000000c0305481d2480b51600340c44081d81c2d03001c078121300c03401c04100640c000c81e8102502c48041140601700b01c14210468280141da07801500c902641ca0340303101400354080312090703102404903080c00015045468441148c20b950100034281310054010a062501850411603040d032700074210780052811701e410740702410f00c030448100503100c0c0603000320640c80c021050302d05807100c0120340490502603407075004072004054400d071094000c41c0000b00300d4002d80d000d04128001c5640300d4007010f05010b00c00901d0880442e0580318560000060040e0743d40d00442c1c00c00869404000c1600429100804035402000c00e0040110f0381c030001905050260300900481c3c1d00a00450564045003100b04180c810303105810030740c917407040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 403494766 1250 403493516 403493537
    0x612013207021b0d051005090c0910030f03050a03020c07080d30050c0c0109051617060a05180f010b0a0f060903030c060204152118020f040902060313020a090606 71
    0x1001344507061803e0060080300c607407203070a101900860f503041d0303401c81e911b4004031815152801c19601094221001050030006c26185454261422403065070090410000161001741c3e0782c42601a500301da01c0400945120f1035039040b030079a848141c101e07201d0202d0064041c83c000c06020510190384a03105a001800690121440d40c00624009150000507001445010120b220920501c1070040c80b800003007041c5104c0d01c48404070344045601c0007840e5094030f5000035400c400400c2582d0070074000003001c107540c0c90301822954000d19260841c100d80c42040d07855182400150421501400203441c0d809c2c540d1b4071804201142c20141c000c14000c10b0b0f030720a04000080c0308041200e8010701440c401030906440c2d0035824141084940050001400c000c141c107091164020203030001920564200b043e03000b1400040f0003520007071b01c082c0c0701d1192900f0041e4140c40c0c0750003c4600b55401000d041c1d80f0314140d0b241c1e0468560031344042e0f01030542e420000c150440588900030640d00d40d03484440a01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 403496016 1250 403494766 403494769
    0xb030f150f010c06020a0903080d230402030c010f050915120106030204080604030f0507020a0e061504050f0609030f150406060605030c040302130e07080a1b030b0612013207021b 78
    0x83d440748803441d01f04500340c0c1001001c12400c0d4040c0c0307900c1c0d03406080419010740b25803031050504141c4180396510400b0701c090000583d00000c6441c0f860401b0b09195428050051003a44c075402282d50464010132a01c400c1185102448020400060078890b400840d9823a08000c4089004d02e0140d0580ca80c0f248000c01c1c0420300400c11038004101d5860034501d4200075502003112460f5aa0160220b00200341c24448241f400726400e1360046051b03240783d800c082c90900028000240301005a0142030000380401c159201881184120804001103501030705050521f20380d1725508480651341c02c1d240c0140031844504c1501141d015055184290f400c040c155020030a02c0013500c05410307209580c441c0400030a40d0184643c0e802005000058062084241001c21400b0302121a010903854107020030f00000f4051040180c0140041ea401d1802c4081c00c101d140c0141030310140106650070001d020710000200303070341e24192540700039880350b0341c1c0d00c5540301660307501405041032103901c030320658084a6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 403497266 1250 403496016 403496021
    0x82404031b0f03030b030606040e07091109090106020607081315020d022803110310062118030909020325021011071a07020c0f0a0b030f150f010c06 65
    0x807012440028038107450742e07460700a2140701820450100f6180c0c4d03c00c0c501480d081c002c00360f000e5010780301400b10140254840e900c66015008680c000d541e03400c1d4085001800400340c4011142c0544910029616400083d50314841120321300300142c035010004030b4001c1d44c1c03c0881903c503400440c4005409610700c0807406504903d0050a81940c24400620300610407076aa565526404440d604a04800039006040e40c42c0c6440d1301c0c5500c8400c2040c0300c602c1c0301190000040310b69070320b070591102d0b00624611400c244441c1013000c550381401c0f000c0800398001c44010704401c2c0720b80c813212002c5a0b5580760b08140d00040318009114400701d80d000000d45009810800325460500c1034460b40054441c40030104c3d1054070300001200c8000c40c84c04100980c20121140c000a6259000c59502d0440310095a418100000c0c80c0038415003490000d5948920030b2000207000c050075015100c2ca04031034100181322040302e540c9611441d842070440302e070805001c084d0919030f060b901c8100d009c40c1502d450f0003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 403498516 1250 403497266 403497287
    0x3010509041713080f0d0824030709020a1b051b150a02060a0b030c1c050102040b0a0c0c0e06030a060e0313081b0108011d090705120708240403 63
    0x20400c1e2000300d0020041d251500616680824400f95a030f1181003c0046103051000046002554450342c040c85009802c0750b4a02ea10014410020901444c01c094a0070107240f0042c1c0309405108000300443c00310101e070090b1494030180d43d180045036880075000d004052007084041c20903081008031041d41408400000e0902c03001400004105000c0e44407a581d9a000d0b40b400001604200e05009810b4624051802420000c90082020740c1415001400140e00b0388403400443c261008507e0800000b0b40555004284140140f5180c040c2c410b40070341b848800303400071501d00408100100300407011490076800398401034010100b10180c1e50b6144007d081c4e03001380c00006d20003801010b0304204002008400303070407010040c1100208800c200c10106401007001410b1000d614014002e00b00248140e00c6020301040300b5030720321349035405024244859908865001001c01e21800024600022a0400c88680d501220503a807880d00d01e40014a294240101510f01503c000c600400d1050b0384841 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 403499766 1250 403498516 403498523
    0x209060904050115060c0b0c0c060c13180204050111070f1203020c0d030c020a0603020c061303120c05092103090d05070f090c030f0c02120f0403060f090203120a050301050904 77
    0x245821135401c611601e5009600110000b0f118040d90700c1000901940c1300e0f04a028001c442e8100100c0f0720a050b15004004c02510011001150701c0c0080440c85030580002c00500d0300d9120290000340303032800690701c103005031404a50443da22400071a000202d03441240c3c04003090050aa003880d440040a0700420350640840c801d4107034000e2903941e01044030060300d1194560302d80084c1d447c41444011003040c6d00101c1418810b000103040700801049041e0710460b10118401040154a420344181404c1614042428a000c5000703010903000b000501ca03c0380d0071118000c096803d032015000038002c103111807549400522220801b801c00c0b1008c6c6501034841c000b51200320b42c40740b0b05948038503020b038854012503456010046825400d0b20641c0640c00060505002e0800c100724040d540f8400407092441a0000140c1090b652101200740c1e0061584440b00344400008824850060308448c20264840e004410603800b046414000b100c0e880d24040e02c82c01d0541e80307842d08200552800400a5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 403501016 1250 403499766 403499771
    0x191106070c080f0c03062503020c0d030f0b030706020307060504050114090d030621020d03030b0303160218040308010e0a021920030a050d02090d050115080d0503010302090609040501 80
    0x2040000c0d0704640c8480a00001001441458441190140f60043d480480390103900050300b4000c138042040030918200a4450001701507070a0f507031048000348204441d5800038012200581070455154100d10120070303012000b8402c080e0404101925890940308050240e401041284002209034000d90f510030b000310000039400c05545045444c1c05011508440c46403c540c1c01058a00d4061080c8005417202101c001490000030401500c040034074a40a4400d0070088143d81c10140309070040b4441c804e001c0c0031340e52500c5c0b184040c49801c0e50441800c921400710050910f810780221001ca0b84903603099a100c1c10b45034a04002a1240384000d8500240e1076020815605e00d081690040564081e03d6540c00e02c041c1c1c01c490200c4060002c0d40640340f42030b00100040f40195a000c0103031407401c80c9881005070740c0c1078101c1c0041c002d07180c4800010720650030144003c0c511041800035100700c400900545d1402c002e4802d04944c64402400000d60040300880401e00c00d0070b001e000164000d2250000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 403502266 1250 403501016 403501027
    0x6090f0e0a09080c07031a06010e0405090a05010e0d031b0f050c0f150105101d1e030f03071e030c06050a14090c0f0108090304060806060d0504030e04060503191106 72
    0x1070240c0c1d913111007900d0070194820f0104100f042a41e070314000d1464440c580318221424000300007000d001c25503d99921554440c00407030181e01c414031140e6281c990003c000c11809003074005079604c51882200c0080131a180c52012138003802c014a041028101c582c0c0d03072103202c08900b60700340c8041d004209582ca0912a0188007400340c04108025040848030000d004030541c500700400c180c64080c0802001007042c68895600364012909031540c07426000c0713900404c03500300c01800c1404a00b14200035a4107120f0740e000c1c542040c0300880141105070080010681e82c2c2c6c5500141d102c0e0030545440100014860b8403030101180507540440c3d0805606600455800c07020802c0c1000c400b000d848992803a000051100c3c0c141c58003c0c040c1031001400e0905803203901d4041c01c403a440b40075070701c1350701c1c140649000040e106a40b4042142ca4401d940d074810403950034541402010440c0d410440e5000e036140c4503002c1210300d4000380803072410394000751820b20000030355500512141e20038191034224005110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 403503516 1250 403502266 403502273
    0x1203100915171c030e030f0403110301242606150a12020a0e1308280c0837051207080c0304081c02070b04020a06090f0e0a09 55
    0x20721596010305140e01800c03141401103001040c20342854030411070380030450310381c071142da907078a00400b61945080016034000703100b010b0750a40c441c0c00c841c00d00803c80040c0100411400e441260078059090f400ac00030182e103186503134265958034038040515a030a03001009a01040016440c101c2c00f01c002543e1582c15202c0743e20b207040410b5400c0541901c0340a02d0110310305180104a0042000000554a01c149070700483c030317540d00e5405000c491200b8540021074008403183d0b00b0031682d030f200e1001d0b60f541040b0550f20000700c01e2103c541c00410800705c12180c1941c0b10f140100c2041d42c03c108000e1a001650907100301c0c0c0400d20300110421032004250007000310f03409090442039031490b02c5407030756552040200d00002c0e030000d0030711003031120203000c1c80b00f85400720301030ba640310381c1c04845d5581d100382041d10381015100010300915018000100401000300700c00105000f203200751102e404003510b81c0710613203e03401035020b070b154054000039082011803600918150400b480e01000110b51b480f07500c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 403504766 1250 403503516 403503521
    0x20a0c0f08190e0114090a0f180c020303060907030b0f06190314040c030206070615030c0501021e06130212030c0606011103090d02040f0209032e060812031009 70
    0x50640da40300740400e280095040350811902e440b1142c3c41e000c428101c4400c0060883e000702e41058070400300120f1401559104c04892001078408002988041c903900c1d11030766018603030b00d080960307001d0070291484102800081076038050741c2c00502c0250140d80e1f10500b14000c0c00c0e004a01a40715075034003103541003921504003d00301d02e1410092220904086000038081d40c4200d4040381d80d96121004000109007481101416207904480c0340e07580306a1414945e01900021206c1c000c48004e031032000007081032070741108040f13510a03002e03980100c0c4508846841c01528032404182c540100380000e859040085104000310702c0140251b4a0728240c1103028916000f501120785c0c180e01c60401e00c2003039a000740c42e0082d807080344001189014550f6000c90500403c0110090090f602c0e1401ca041005007038066801c509009411110b1029000110003040842d01610180f802c08003140d558000aa501964082d182010000d1540084032407448000340d0004050f005003608000d00402c2140550 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 403506016 1250 403504766 403504793
    0xc090c030601110a1509141f060803130e0703020d02030c090a05090103051015050613031b03080f1602030d02010504170a120e1c090e0604050402090406020a0c 70
    0x5118254581c030340000058155a00c52061400725401103150a00040035100c020341c0b01c01e440800850102502e2034101640140510714840b075000e80300b45c40c081c801e909031500700c1da660410000d120b040d6403480b880c1d03124402c81d034030360742d140244610503c121184010642e41109081c81c006282808111142080381c1045d1340070303403038448005524a00c0d490061402c1000d0328086906560035451175075081d540e400310040f190402911585968030445810f24480c0c002d24000c0c2c83c00b5a64071401d40011901d00d420301041380d07080d0322040c1c0c514422004aa410064a03401342c41b0500d009001c566200c03581c1c0008407008540e802c003030381541c0162424000d03500440c6183d000429103040524003881403204004071100b4000b400d20404d401d095110368400012020580009030b858031808416040501c01c0d082410655194001d00d0005944004a201120000c100403050758031400e04000c02c0c1c400507107020f548030300b4081c0401e000c5441a4001e04035020f85043c4242c4416940c3d0302c081c1d104030170 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 403507266 1250 403506016 403506031
    0x70e010f12091a0702030a0807030924020a020f030c0c010c110613030303060b270a03060501060f090503010c05070312060503070b12180d0c0c1701060f0b030f0f090c09 74
    0x3c102040c260f096140c42c1454000da201d001a40c10b2160300940104074400c014250402c15441322459418410000c03800340001484900704a01e074202e074058600a0740c0034800318001489500060118036901000783e407001e044100c040c00c051803500004440203154410b042d20700c90082000c03501c2c08e649807801000c0707120490640541151440c14042e044070402c0d0301071616200e0030440142c145c5c020030040080e0341448420408080c1c40d080106080344003a0704001d081510f0b03d0004076009400c500d05200c03a02c074654441d5900c1b03465000b07050076542a40034840c0424000c0c055000082d0054000b0440b004c081000010215500c1002034500083c07544490000d60002844040e11016a100c842c0c0c8409400700842d83c4034003284056984040507040c99041018105c414010080112401c2e8000c0400900501c1c0146501c00070342d0081001d44140320000a2200c0006000501c650030340780310b44c84140200310903544034181840091b10040107680c1c2801070300400856582d40864450207500b8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 403508516 1250 403507266 403507283
    0x409090f03020d09180e15040303020414010918051803160b130507091a0d060c08090d02070b0913021c0501080334050a0803070314070e010f1209 64
    0x5800d0190402d0101c4511000300700c1342400c10700c051440008840840840305500040048a844074070341094880410b02c10380d41507c40c24003060603415005001910305110000304122820001507079514418451450401d00c0c00c1890040182d0650006903c2141d44c03515039020704800d6030a41c00e50340308802080c084031801c0d504806000c4240400e60348011408502000010300c1c0c1c4a00755244100d108401800d0f0304da0481c403000d100a019801752801f80640301691004462800d00e0181901d107441000207401200040c185200c00a64190720500980160040714200510150b142e071089a00030341200c5c14890381100c400c940d10003458207911004060014680c504141410382d0b1040e03200010300d9205005400d4010300c003a610480612003030414420314003203034190850083c04607002400501686141c2428081440011403164050365000c00c1a1040d0741d0360340701003160540d801c1000445845c5116590350240c485480000c200b8103000c0000c2011f0110031060390548501180c2e07000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 403509766 1250 403508516 403508543
    0x6050a080c0f18040b041a09060d080304060b0f15090301060602030c121303080c0f0d1d01050307090f26010603020108241005030412080108060714040909 68
    0x55128280580148038180c03100d14092140c5140382c0036018505200d00100358600c600440765603158072802c44058060820300c1003c440010310a00303d880001c0c018010ba04000029503a0320700005603099041c2e1002d100c1d800d545075500d80500401c48034692940100707410000800a503141d042070800b032094907040d107550320f0040003803500717545007130b07200b402594000c0c03107078003012000880e04500e259980424188c0300c04492034501005c113100d03800640b0740c240000b4210900c100c08148a00740c400d00c20100c403902c2441c100100d441c2c0682e000d501c8084240300d0448100e5610640096400c0700892401e4003119844913400b101b030106d140c0c000304002c40c12100145020081c180c00c080c1100104008001c0e040c40d680000e405594002d060340401c4d24101c1e0780c0742c408040324194540640c0040c01011b1075035910b14020b4100e50090b90141c500078560003421416502ca03001e002d06a0303142070301501e202d4480d030200b9520034240d5021144400001d12002c141501c50703100e0844484d00444800d000301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 403511016 1250 403509766 403509787
    0x20d05040f06140c03010b0c1006090203061504030803060603090a141b180c03100b0a020105180a030f03020c100912080106090609060f0e09280606020c060d060b040605 74
    0x280c01c00c251803a4426444000c0100100884060306d0440c0c2c222280c845c0e4403802d41d02060f041110301d14000440514040e80401c4a504941c06144124801c1c0d40c1d42055100c140d42c04800707400b440c48018540d800400014420b814840d000e150000907030780c00c58554a8865680c01b01ca4a004891250303564010301e41c0743c01c0680d0018010b820500305550100c0c9880810000390700d00d00c001003031204003e2001000c281c0c036a012030948401003500342c140030303107a990b0321300020f001c0c0105640c140e41d440120011303500ea1100210700d51700304903415184c03000030740c1040ba000e038040e41004010500300c1c0148500382d6240041e0f03000701444540b040d241409400c1030080007400110043e000030040003400d990a02105400c040c045d815124030f0b007040c81c498140c1c050121000544411a140c020100509210802d040c2d00c410282e0701110380d842071201080e41b0050802c844580c400c1d240141e000b04600082c5003030500040c40c5032442c0310781c00704070a6180e03000c1642c198015801800022000124402d00c13 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 403512266 1250 403511016 403511021
    0x3050307080a18230f12011e090312050403090b0f0310050a050607060b0f0301061404050a020306030d080405011b03090302010e0c0d140a050105010b0a110703170d14090313050315041203020d05040f06 88
    0x1149520008010103d62790700d00506000070303051020107550366480400c0505024082600c01800640074595032126942a40c444a801c01c0e500c0981042d03004002081e6442c04055407019180c2c083e00941c100b13081a2184806000c0b103400c1103030080038150103811140c50a006003030103844030304035040070000b4403814481240c60040c860180b1a2060017800b0040e600860325400c100014a0700354119151410090b0041480e0010001c400702020880b0480380e130542c2003652307000d009800812910800143c21600e03030003150301e000e40c8440c0c0120f000c0c000480030120140c0321260b100c200c680d6280140e0b542030848000381c100360855940482d0210100b580083c254095402490182c800c10785075a584411108804018152400d03000c01c045103e04030340e0b8052540e5024800c020a42810000815626940440d00b0a80c0b108919500407a040c180000c0c014a100c4194500c0d54160390b0315100c402041501c0c59110081540030045030a550203d8080e040c0143e0140360b401c50a6140703450002c04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 403513516 1250 403512266 403512311
    0x6050307080109021c110907022a120105101806030b0a020319090206070215070203010c11010c1e031503060606050d0c1707050a0903050307080a18230f1201 69
    0x406040308501170000401042c40b00316003500039600c207020f54440a0050b0308018400b41550301040301c818555400c0400c05444007015107083c2c441888803401e03030f0399243c2a648201c0d50858001841c40c0c082020002655908008213010040007a00e16125640e081185000343c40c500c07042c5401105002e446400310002e8000d5808044040200070f1840c0d02155141c01a44d06c0a84a000c518101c000c1000b2102e0440d128a94010000c00070360300140740c0035016140d804020091580780192101c05ca40c00341101d81c086d041c001100a00c401d0a000084000d0004881a004840d01c00300c0300200207044d44c0142c2001d00403d0322600d0301d410481c0c070550110307541c0c00f8910081246849010b8010080304191940201c0c051614075503e504c0c482090301c1d0540b150780b00074620700c000500d502c00e125115024005214003640c500803200004048110340b10541c0c0a50003402da03444444d1107480c011825590040300c40900344125a452a00000384507080001c60312101d82d460350380350940741401d52843c51 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 403514766 1250 403513516 403513549
    0x10050a0b010507170d020706050403080702010f060e0f040309080d0207300f02120717190b0f0a1107060b04050610141b0d02031209060c1c0605030708010902 69
    0x1070403c4842e854003400540341e200c90350304001001490860781e01c0319030121500c198020b03034140b0050800345402481d1280441d07003000154640b07526000303a03103c1c1d0b02a060860740031140b940000d454600c5140621000500203c0910140c6400018030759002e0004229400712600680402c3e840c0c006183e50410043c8405000d01c200c1582d070008020009404050180e0040c5044070207a52610209210714151100400b007841a108001070f20752050000d2a1943d804400740c5114036064010454241954500100b0b101640c2c0001016805003d540300e40c01050b5100101c3c40540c1d01c0c00c102115402035109503003440e00ca50600b64581424000c258001c1415200720154191008000304042d068508650388034600064a0130a0030306042050301c03580204041d41e2440d1030700c1201075526400616035954103802840052003407140804c0c0e0620031007604806914200c00ba0740745140e501562008070340002e0350b401011406481c10880d40c1c000c0e29180000265502c0580100140c0c40350024609 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 403516016 1250 403514766 403514777
    0x1050403081513060b040f080a03080105100c0204110316022803020304090c030e0708010605090411120a1203060b03130b06270a06060305061806030f10050a0b01 71
    0x840080d5001840507030090001e48284201c0011100040b10340020980b0140028100b060202d501d01141c8000c000f1200310141010301c450340d941e4450346418036081c000e40840c00c010010001800c3c95104040746031058a8806460704ca1540060700b03c3c1c405420111b80540003000700000c07250301e8544194840010b000400c80e4088807a012680066407040ca51180c1841180315401c141c02013059501a1030045400e0210b42d41d40d10009004008000d0700c00568458684005000001031180303000b80e60010380708954640c1d40e9151032802ca05114413050b0006228802c0202c10700080c0b012040e031030b200d000d5017144400d81c06401000c0e20f1940d0031850300c1313150800500000d00300b841d86100003076511181042d21a558400000d6051420080d51450311001c2c45080c4c070b01410455680c6d20032242c0075030420002d525403408408031071089401c980c105843e014032041c400c602140c0107a12038402422501400c03a406c6400b03082109445945481c1c540350340070300c545400d4500824040900a2800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 403517266 1250 403516016 403516021
    0x3080a170604140610030906021605071710021c050412230301290a0302120f0c1e0c011a040c02060c0a05030a06090c020f07060306080a081b06130308090105 69
    0x50f81800380307000c4c0c031540c41030760b007000c0a0610320701a8114618494204404644a00d03004c1c0301c094800d50000000c580c90300507a80040380005490710380c0700003114140300400910441c003481000a5200c0c0c0c03610b03016200300030607100007140c2c035029440c4224440d03214482090140381c0b024100f40610300c8280d5600200c00300e000b8903d0411002d9a0440b6280a01580401c035440c43c0480204400b900301188000001180200d039a0160010210700c5582100501160786040083c003030a8400d940c0c0c041601c00412281c881c9201040346c0004419541648a140100664102d401c43c2d01440b013403404c403074a24078103c52529051207040802109800a030120b0320300341003085210310070b8030340c81024800d001c00424010003066001d1400b40032003030810031002d00046406035607915400d80c20801803086c00c0c0d000c102c0a01c00d000d84422103240c18001d2070700281c103945055003a000070415881c0442034190001b00c800b070400a090140c85800d102c5941d0682508005151010041007803029a0400d0309 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 403518516 1250 403517266 403517291
    0x108060c070f060b04060b030124121a130f23040b091603030305150a030305190e09100510030e0a1e0b09010c0207050307080307061503080a170604 65
    0x2100e1a05501c0402d15405503010302c1e000c0f00504c88040c00355000752508801050300c03091000114182d4140082400602071503010041d22040350f56011800100508145030007030300141c1124604403a40c540c01400000b2003408184001c85001182e818591664411418404039200742003c1c0340301c2441188080c01c1181c03c0e00c420f8040608000c01c590392050010384030110911460540c02c2c06d084442075201d58a0034020090001a01c0c0c09002d24a0141b420729286031014011003181e0b40340e00c1e001c0c1015407150040100c034140041c42070610202c4c2c0e840070303802d42d01e09810b60303c65140000c008201d181408140812042d03082080404e00d0b180003000c9895410000303400072215809040700350041c0640c0e08605402c0c071200b00c010159451503092000062064010414021243d42203a880ea41e0300c1c800c05966198074403808880d90010080c0d50f010400319003040140410600480c819903940c0e96424070b040e440240510002040c02d4011840051001d0403250840e1040b9418000c041c03d010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 403519766 1250 403518516 403518541
    0xc04060b03011208032d040b0105120616120501090e060c030708150f1c060507020316121107090f0606050405030d080403020123010807060c031707051309020909010806 74
    0x31070113000118040002842900c8414001c66104c0c4642500c20303421440203901625440c0a607021252191400004500d41c00c05805202c1c289030101c00410310b945408204d940e40103e2500d0307030010000000000c0e0500b01ca20301505008190303900c00058488810315160b420240041c01d40c20070f10b079082007800071039035110448580081551038103007040d01d55000000d1881c01c048a090360440c3d5451b0303000e0a100c501092649886000e0304040c4400e03a50350300201d0300d034031408807242c0b64140381074079100104401051307070804002103083c214012804030781d084c0d01d001c29a60041c2e46558860711442c0d0030074168003d9400030a060305000b820141800e002a440c2c090304200302e0104024140068145807003500700c0b04042c1c040c1d000301d0800e0311140090105035903090160761080d00c156400080c0071485600459112609603070f80001c103081d00111107402c100f019005108020081c03100041c0140065100340013062071200042e607410703041d414040b4005059002049582043e0104189004100e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 403521016 1250 403519766 403519799
    0x5070f05011d03030706050114120c060a0305222118030f051e030c210405090403090b0f0306280902070303140114030f0303090c0d230c04060b0301 65
    0x2016040c02c2126403011070300d03501602c00007410346810f100001950210345203001014080548024080190741089503a864001d0300c01c0c0b9400a1382085104101486688103503008060321454181c030300f0281d40307003440c5840441c005031908212624001150a440c15a000c0154140d0501c911f00b0003854003403140c01c02c403500c00903144407140c00308041004028422059003042c60090300400c00004540c8959030380001d41140228440c4c0030506401c0c040348090320803401458011140f6090414040c03040702c2d00c02400440a2047c110004100b80c00c000c000341944031070003604540c0302d15040301000400c81d10410406240c01c4407511410101d0701040012094030503402026070f07543e47c45d03c0e0031401006032604c9842981c5480c8008500100350000e01c0c7c1002804408a6084030001d0400701d07260700c030950311440c03140c3c80745000f00441c7c10069441036900e4015401e07a071a01004040302a40090b00b50503035951508490052461864075128400203000b02c01c040c282158180641d5030b0200700003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 403522266 1250 403521016 403521047
    0xc0914030c0405041a0106050a030609020f0403020d150e0a0c061e03051f030b06030111030f070309021210050f0106090812070206190c02090a14040b09011d030705070f0501 76
    0x3c440c00642400400002e031441c40315007001c2d4007120742e5035010003001600326400210010b1300f4040c0024110216009a0740c000c2d9288135a585042c1c61a42004020a65024110b0300d00c1c1d80310fa1a2590032495103d0441c01445482c0a80040000f504d4481441c1d00940c10960030b101e804451483e0f001d0841030b0054050b1028200040d4a0b22030115500c4000300074104940143c018400110800a810f4440e5006003400c2e0000c1c0300c04000b840c3d648155000481d900e8680e1440768001501d6075100740c10183c40c0c0b5001400401c10006003e003150308210740d016100051319194801d0200e50401840401d0050004c0d1402070031290501c0019511034030383c80010081c000012034103809666414041328003810300001c0e0b11000e030588100103080840f407154240e00c501b01034000a11030211a001c0e481e102040c050001d4401e03611355540c014031410152040010307650f120403034040484440c05032440011a90025501c0319181c0c13802c0c070b01d00f070003c0d0009581900d11003010820742e6000040840038410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 403523516 1250 403522266 403522271
    0x30708011d0408030f2a1201080309060d0c050409021603200705010e300d050f0301120c030b0c04090b040e0622051f0e010507050a1803050d030c0914030c04 69
    0x110000c908440042e0040c001c11050b02c12041c0300d0711b020b044c82c01400010320150300055580e036502d11040e164054401d807035070000b50400c10000300840070f0388010000d940d40e06100341001c3d1900c0a40d002c90700074010843d0712081025a0109058002d50000d10806c10a80413004240c49010440e850741c84500c186414081720800204031540c614040e00105441107803144591250f0010310b12130f4825444100540d030080e8074100365128803a004440d080d038002d02076a4034503480d1600d04080e03641c500b14142c5240c41507480c08000103058040d40d03801540e01c0c8083d180c07103c0c01c0100000840341c0d40b981a500c02d0303242c0600700340d02d10404148960f0102c3d00380c90100003c16154103142e45140011001001c60040c0141e900301c0381000740451186601d03001042100301c9400c00320608840c826904072021440038480c1e580c3c81d83c450700d4070114101c498060f2003440c075500c0c2e59041c9849074000c040c0c804607443e0072200700d4030fa0380405200c000f0940100d00552085080d00840d80b0f50f11445904c0f03016a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 403524766 1250 403523516 403523521
    0x10051602040f02030709030b09030a051911100507020d08100909021206040c140d051e030d140f090303100b090a150f11070e0a15030206030708011d0408030f 69
    0x191076a00c0101d00320030703040d000d541d249070000000704108140d00048454101500100b5070b10b030130010980e1132070816619070343e2030507100c02c01c8801c1c00742441c4601c07420084a41c11000c4000030a01a00701c1550b80c094002c241070901c408040d00703141c880d0102c1800c104021003002201c4201064480c111603081d10001428103850002c2044001ca020000425104000a2000b00441007101e401107512100300c0c0d038801c0060004200c001c503001d0784050010751001c44e004640c0301480403d00c1c801c007002c034203c9207040b40c1c0d40003210980d01c8002040544000740d20400041c0300f01c000c2180c1e8844c1c900c401442c9180760501c80180c0d00721050040032140c4602148002d0a5101c00d80c5080c003405c1040f14059030450680801462000d034441c3c2c200005a0340c2ca4900c0c04210700041200a8400050071442d01c1c0e61055a480c00600103000000030381c40c03081000001584540d4000c60080d07030a80d1b100c09096040c00c00c02d00300d4454010301b081d07088401c1e07030800011031040801c0c1c83c1c1000c91280c0102040c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 403526016 1250 403524766 403524769
    0xa06151106090f0304230a080615041407030c090f1d0606090d0b04110901170d110a03140d060b0706061a04060e0f0319020405060301061508070207150906020c10051602 74
    0xb06c0220800c2e50008160310002ca9100400510544502c00d203500008003d28404140820740c0c00e900d000e002040c4451010a509074066005032244134040c0c6000c03991a5659080d042e15400300340d00107002c11107911034a08200c41c10400183d4008401d4801500c4c1600b40380101e8207120352064058940b10b808404202003000054024403d110020400c0c004d55840e82858804002503900044162242d8184000014011421100c0161600d406010850202c0c2c0b400d0742c0081c0610035440d4100820030a1108017889407090b00087d082d03031040152214000e240520840340c091304a20311210900340c807995a1951101100c2c01c0e9070852400b03d01d88a81240880d03114503a40d03c5080d414010791040082001a5501404915001f00c40501054440c0700c1414203c032003900403901e404545202d1804164003a2000c40d4101d0007520454440d159030340141c080a07040c85a44100040e03140100300549581001fa039860507204880c41011000104409030251050105900201041c1d01c40142035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 403527266 1250 403526016 403526069
    0xb0a0905030a06052a090618040e0f0d08010308090d08070b09060604060b19111e0a200109140111060a020702092406030a06151106090f0304 62
    0xc2001408464a5510b1854410003800e01156025841d4643c41d0743c08072202c1c407400764811510b1000b42818644041901408000e600c4103141111060f0305c0c004000b080d8039580703c0c2103240442e07a80900304480341901c089082444076808402040340348001400070035824812140303021400c851081c1d8648141c0ba194909010380c03940a04091125802c02c0081c1078007091207407240104440801250761101e103c02c1c05030040005d61103001104081d0501d03800e0207541d415078001d4044080b1800c03180400803030803150894600340c0104c1c0d04039003121b400708184240b80d00360401502c0c10b03102003010311000007003c030002d41c8a02c000c0041171180c54203490b4014180401600e500801b40c03041441c2440480020f90f04c015000c0380542c00840009844003100840c20014800446090b5200d01c44182041096080500108103a5690f8000001c0d2246401c0441c1e202226949417652010b400280c6c243c20540c0040180c91070ba000705000281503c00401107400740d4841908010800744400c522845 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 403528516 1250 403527266 403527269
    0x130f0305060c0a0905011b0f24110906070606030f030f030b010c020108040b0a020d020c03070c050f010203040b0c0309130f0515030c15090406030311061302010914150f121003020102070b0a09 84
    0x101d0a856200c008c144496a14880220030340403030b002c2024159003448000f120074015183c07111200600c4031400c1407401c1001000c1a5010b9840130501d5a120344640b0510f00a40714220042401a00ea80002c29018019410700c02c00074206001120110f0300080e041d200010801040710b806a0001004422254140d60610350b2406c002c5450354100c6000780d90f07a520600f415500040d22800c00100d81c9069a03201c45909410307406181441d140c0666903085812580400810f40401d0240300819150361a00c40303a010704400c00424160220050030003110009080c0600c05052282c1440c240d4400144000051406984004003d41c168051120b54018144507560040c1410000011300d03511120f90703683c0e4404603064905c50388807a40c41160251103800020b000c00c9240d402000f260803c610b001e0158040500200708444000c083d034980b5138000390148184840128011107105c04c0784200e20f6000e1444082500c0079411a000030f540c4200521038020300075400a00d10f441503104001010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 403529766 1250 403528516 403528523
    0xd120206041104060b0a110f030a030c0e0301061a0a140a0c0b130b15040605090f01050a0e01061d0612010303030608010b1c060e0f0a0510111e0d02130f0305060c0a0905011b 76
    0xa031540903440e2b00801a04032402480300186407140c021a5618040c800c0404803409070150b48202d80200040f82050b4000c021210280300c5201d0307400c181c80c59031100074007000c0300315039900c12205000d1a000301012800350000e280440e41d181c00400040747d20380c140d500091070340d48075140e4904440006002c2d000a030400b94019000505015540c840d4260050581e03030103d601c0c1d10115207400c1030450300002441f403d00003400c105408180d6120004078078440e1000a450240f0b024849000c40007802c2c420390044000950f00c0608000d0703a0700c03c1c440c003040c4a1044407207440075414441d50030f01c1c0500141001e0601603644480030341e4454108140c1c20180c20071000e440b4141c1480c01e0032500c446000c1c442e4410182001891020031a10100316178801c54400904204065084001c40040d0011012803200c40d500b0030410712a900034144803002448074100a400c900d0552800038200308002e044103109901c1880b1501816410501d441d043e80c0080ca030101e01c0200b401a190140701c10718002030b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 403531016 1250 403529766 403529773
    0x5031f0305013314120f0703051e060a110408060405030a03050703051618090f02040f290c01020405040f1407081003110d120206041104060b0a110f 65
    0xc1080010342107050300844907919600000286484422410540110542c980062180c240403002071240700080e849406080b0b003c100d01c080d0700443c60091201c200314050b5210800030402c000e8100403645003000030f01d01e41c001035442400c004d55a9100135081600d1542c0705d0200790a10007002041e1030061070206c08481c03850403d42495a240d074040c207030400c0020309103000201001c4c06401607900030282c04200813401e20701410100c4400c0c18049524040100c0e807440080e00c1082c502a920303000342906001641e55281c015a40d9014a16900074821486902003001c0c4840c03804041161914074001d80555580f4148501c0740240306e103412250703100340b50085c202c41184407a4825042c5d0300ca80500e60086072140401074903150411540034100a645c0001480020f10305205041000300250807210035102c41d0f601c1c0c8880c102d081034800b0050348810f08000c00c0c48019000491680c41c29102000b5441c00d041100110b4426488898180154440d0003240311004210509100c0180801d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 403532266 1250 403531016 403531019
    0xf012726070c0b04031703040c150e03011a0108011205010f060e01090b0f030606010f0c15141b04030609020105071403090f180a0903020f0a030527090103020105031f 73
    0x80c0c80c1600600c200340c902c90960301c00840e1241e0301a0849081d01c0d0044440c03406040c624541100c55400148100c402d00700c4c800001421001d40050988009880c2d15101c40b090703030f0b80303003810301310f032848620000e0349a410104000c1c1a60040c00c1c0605540200c60340000c20403960501c6400341a220094200c070600d0200e001454a00144189044e00c401c05000c3c4082101c10080010b0040d48a0586a02d9003110022514540c0614500c91048880d82041110320039507480742c540e441c444401010b81291078541a03031110362200110344e4040c02000302110b94054403800383c2154000c1303000003010241d81d9074402c03082d603001c0c03420f5a0006602c400700042d185049514540c4a07006542e000b8014040e06540040c6460490401106d098070420840029958800444040c0100000a40940c0140794001c0d003518424004140c0c00c078040d8a03820703a0350044a158869a41c4000300041c0a6490301621090325a501441c140c11282c092130655100e480e42d070303030907a40344010701300001190888100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 403533516 1250 403532266 403532333
    0x108090304081506010e041a0402160209160816020d081b03090a0b07030c050d052805070206060609100f05041d040506070507020d030327140f0127 65
    0x24503111307442c02c1c2d0b100c0c40c1c844460700a0100b80c036403074440804080708034070034045a414035a0250112141d10100960000308035004a4220b406c03e03105403503c46d008420918820b030b08558090303000010580f031802c1c0071f03002003802501c0d06034402a40302045080d03000710300861256049850303056034850b080c0380d4908100142a07547c01c030174031044980c04000400590140c0c007900c1803141e500c0c40c5480c1c041c94200c44500000003070400601003986402d1000101045108003100d440740b100142800180904000c50007078900381000f442c042c400d500400c800d0545031224466055242028109416017602c500000e0b036060107190402d000c69421102c03175001807059450320034000d5003c1c0c81903c415880c1c100341203030903104040c0c0182d00041d03618890f1000070301c603902045c0c5e80340d15541008030380200f03010050380922941500351840c450315038940500c5102805402901005070b0000c212201c100c034031004010445841082090100101c1c4e0700501065010782c0301c1501c05142c40d01c0c0001240c54 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 403534766 1250 403533516 403533553
    0x2070309030b0c1b0d05041206150b03040c1a180f06030a02040f08010905031b010b09010f0806130201020606040b030c1201021201140a0312030e0f071802030f06010809030408 77
    0x1928100149000c5031601445840412030301c91040784e590b06c40d403810f41019404060340290f40300840351250f88142011100095021040181040c5010f181c2d40381841e0810300c40786803164111400214103002d0031401450180100e400382c1e002980410250041c0c6400100304400845455070131940000410400c41e18560042003502d0203100d030b03016800e032030781c7c0e45a08862b1000c000a107154400c0003506e000700000599140380c95006000444d40c0640c0c0000315001d50700a0344010001e03118441c060081e990140b0615074414106110b2941091964000039500c03400600780901030780d81c1e844010071030740301401a20001a8007500440241c080c14102c20f00070340c49408007114900448001003002d901403a002aa00c0701e005102c00c8100c2d045444120300078030840d0701c00050681e21000c41c220100280000b1360450844400707041c4a5141154529908601c6040380180034810000c001c09500144102c43e0041c0f000c2c03038882015511020001d183d446590010001d81c070034848440e902c000020b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 403536016 1250 403534766 403534777
    0x1509030f0215010b0304020d1b060e0a0905070806120c041a01021c02030730090305011107020d080a051201030606080706080408030f0a06120609021509010503070302070309030b0c 79
    0x140d00316402e6581902c5102e10100702030080360714102080000c140035203005c0a100d00d80501500d00030506c200c2d44285498807041b954014000315400a68040061810740401e100511422200307102030702e00a80c00a0105400070295449074090358200c01c0d00d00300c00c0094003003c00000c0c10401001d11021351000340d204855140714011303c030f15180402d121600b14020010b803896500118249442c40c3e0358900b000c814402078018a41c1407d54103c400c0860800d50714a040303c54075a425803d0460600c64250307a081c56600aa0290401c18500180c90700b4075040d0342d141e0032401c3c160301c684011008550511803159040b80841c22030001009021803a400740084034004002c45540036602c0c401900c04810455011702501e40500000340f902d05c00313145140d0f100310a04000a40755032680c1800c4010070102070141c1d41035584003501011820040d4204001102d0320481c103080c40003442c002080c5100007001c50003015000f00340341c01054041e01c5e052024650080d1406e0031490404408152038116 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 403537266 1250 403536016 403536047
    0x1e020d300e010b060403050a0b04061b0c12090b040e0c040e1009050603010c0f0809150a06080609031207050a0306091b030b0406080c060a0908010507031b170103030c150903 76
    0x20074190340c03c20b1400008a5003102d9201c80504946450307511810902400104140c8080c0d8440f00c01c21404501c944400202c0300c0c43d607c540131600414100f0700540481000b01c003040c040318150602c011503405060783c088911000010303000e90f44680300184240644e600c107454001e01a4180104110640120000d4442d4803c04122580c0c0e00320815007610640c09119011401c0b071040520303424480d83c0d81903031090f00c003400c407008000c100b41302c10808141204c0c15212143e46000605c410003040c465260070140c00301c000c43c00c4c000209103203410540c0117011a000d2200024030301c60018080c2c1c0001004080140c001c00501348004072001119111441000010389880340d240d5107440e151064100b5541d464008016456850b0280445688109800d805003c44c05600191031a02401207500c102655903010400313050780d01408489040c10200d900501070440c0496070300e44541d13241141100c1d01840c24500c40c881070305080300381c02160000e4007401e1f81400600381c21300d60000c0e03004891218 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 403538516 1250 403537266 403537271
    0x5060409020d0b0310270308010e040204020918070f0e060315130204080a0314070515061201020d150f031e0305041517060312070b0606040806010e06011e020d300e01 73
    0x3640700c4c41c40d2606d02c188500502203254040140408001404140e9005102910061402504c0c1c00001e0095440d01510084855030300d0030420160303803003101070491740554140044041c1e1550001003c1e800001d051001c40c0e00f54041d007100075903c4e40c6004620040f60b404c03c540c1c90f0b8448c0380c401d45501c1448819004030f820204910001a425070850702200d4101c400341c96210740003a540390a212000c1c1c4810303449900401a80d00c2e1503401e02c010b26240704441d60029104000d603440740c00d074580748c2d031004401c07184040013000424000000c4c41c4074010301307064109043c00285005d4800b03006542058040c16501d1191130342250308400c103285a1203842030007209035500c4c0010156648080e21428140303003c140304150000d40c021034034940203900182600e0416031600e0b0900d140600903840414981140350038407400f543c20240b0b6000360020803440d100490b0040401960755106000303d0410800002c856208482c21308103806c1d5015010303c5a00c2d51480442c6086026003840d0001d501e0302e52 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 403539766 1250 403538516 403538561
    0x60108070e011202040e031327110304060c0219080a030b0402040f062d02030d110a080712060b180301110909061c05100c0f030605060409020d0b0310 66
    0x1070014038141295868104000d2400d91a420302c0003505138000844a0f521060000c8448060001460000307402c0310103a03081200001d0581900c0d8040c6520041a01c3d1700c0d0504044210800900b12540543c000c50b02152022007000b040345010755144003070858046583e0690b08110000000348a5400e142e80c042c841e048503102000100d100f14402c1c2c01c401407030140100021070003031041c0c0e212240c4140c3d003050305031224000000d003480f0314002000140c0001800400d60401c511036a11121500c0c0c9029050100310000601414005807a520912201009880d41450036030098000b0384604184541c0382c003000d00b80618100c0d18000d40620a5090161100122a8800a8520100004101c42c2e00c0380c8803c014000c2801717228101c42e0024001a00b00000300710200181d085010400c0300000701d080b4603c41c0200340003210540c15080509240d003c00142d9110426101a14a50100144d403242c0090303a0400034510000d4041d00740c010f00d0300da105981219030020014584602c07940d040c64 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 403541016 1250 403539766 403539779
    0x7030c1e050a0606090b010f120f0e0706020d020607210b06070203010c0207080f060f1302011e0e0114030601020604110d020d0b060406062a060f140402150703050904200c06010807 79
    0xc4423292905c000031060741c24240704241c190400e802500044000040c142034000c02c85080071000c0c0c00007009a4019801a007809904002141d80100c46162180c025000310014012040caaa00c00c14200303906e6650f2200180e940100321414191700900070803400700e10002c040d40f00c000b1845021024003440c0c00e4010340c00400306d0101c2c0308800100c907201e07444c4d85d0011303100d0041f000c0042c141d04100801e01c5040381c0c1e07420401c000c5031401440e2a00c6082c8956075000416403046101d00400001060040c000c0c60b98002402c00c2d0025032002e0780b0700140c1503120100e040c4e0360784000d001c0d501500d007007810f43c04c0c0000500b5070ad000c1e00c802d4a00b4444e00d030315020143ca4240d0306242a1040c1c01403160042283da601c681c01001c1180301d03e0300410118440c0c1d06200650301c0041154013103007002c41c140021841d100d280000e1102c01c030340102c1c1c02d003d0145c80207000341c015021401d0086407503420701d000143d591004042d491190320342c1d06031a00035908400d680e4080034010304d4680c1c0b04010010886 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 403542266 1250 403541016 403541027
    0x140f030c1c14060d0812090a020901180b01050c060f040809130b040e0604020a170114010b090406051207050603060a030803010602030c070905010b27150a0306090207030c1e050a0606090b01 83
    0x104c0c0c1c1000e02c907807420148030164034800380020101c110304c0c0180420324005990b0160700c54000c002071103040200c140d92440d40c3c1d04071000704c0000307414001c0401c420000034a01003242640032720000b01051641c4d0390703801c15103034510520140c00d0303000060a452646403107a551201c0207100d000e80381042140301900c07489c0c1c0e841e40d041e1030180d8444110001040005903c02030301c1c468014000010403c03007005c0c0540031144d43c080e00315040810000c92001d4143c06d152050000400b011138405041204050469484008034013401e03014900000004000b500e41407042001980e01000d980d0b03503581d6800c802901e03074000c03070510b00c15801480b0700042c000030b603070040c107042e035100d102d1562504140400070507165080084141911101043c5907855075030341c0f8011001c49000040d41d66442c00603560003070403641c40c4e0300a0302d00c05105200c114007282d840440b01007225400041808846000c0740c40404010b4a13000040c0944260b2540d00c0800041d0b07003002e42290304c0746030180019886072006549 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 403543516 1250 403542266 403542289
    0xd060315060f0b0f0909042904031e0302160303050609090c0109050f0d14030406122007020105070b0a1406060a0206060927010c0906140f030c1c1406 66
    0xda00d480c14001d0010400700002020780c0c402c02e0403131920701250f10010800300c1100f194141d0b10720034144245003485140e8000643c41c030f400304441180f2440c0c203940180c0401c0f0901c501c00b0944100411400015010740d040b5485545540e00b481c04d50360b4a03190080243c00300f11016406564901701040042ea000541c43d9491001616000595400c200910a2010300b00c0c0485a2044c0c804481c038000c1410803000013000b480340405135aa0390b040c410003402050101c07605031117161810030303060b40e240e2801d81d0070086071190016440c1d4a243c94001294240106000a001141c0540034000c4007079866119a10110b44141011043c1d512201040454081e601698025030070080005150785082005268804ca9000c140c1104288624a000558000c00c4150403180e545103107140441d41c101c081030008104c14585030218294081c1c440b01e680c003c0d0f0050704000d03500400415028410708042d2030031521000760541065940d03205900c0030300317206440c40c5a050008404a212030411103034504 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 403544766 1250 403543516 403543529
    0x504030b040b070311030a0f051003110d061b0302040f0b030603370501050a0609061a030912160209010e06010c260a08010f080a0327050301020d06031506 68
    0x94155980c0d2a0b0b007101ca03a005010070100742e40c0700355078146060203101840c000d28503440002522a6504400310480724003030301440702400121010800944412500780481b001a149810320f00014541100034141601a03200109031090540341981d40c07680c0a48210f03458040b101d40c0c0740b981e1b0025000103200c152902c80d01a00306006003220304000c81e1081c550700d0040f000c4181e009040c5240c0300b0f09414810011101f6035119000c2c00208401400b420000c0d1294030010031099103800c01c04100c80c0840e401021180344003100050443c0414821103920780c41c111800c42d07440d182084940e580e03006607101244204592000400c0482182850510860046c2c5500314082e066031152542c003d180181c0d0118480003c81707001080c2384480c0900701301461070b164403801d9410040703141d1b00007181e5000707000c0fa541b220f0064070121b54003100f0000b15503012900d010b00400c3c40c0c0381c15100d424081d08215095070000428200015196000030300310780c026600b41d140c2101007505001078844911801 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 403546016 1250 403544766 403544783
    0x15090b01090b0d14010c08090d08011509030b010f0e100b0405041a0402130807080a0305090108060f0d0503030a0e071a0901090f090501090e030703170709080105010305060115050403 80
    0x40c440c0e1203071948840e25148008110301d9816040c0d54882800700c451440c80c002d5a510b03400c034a0100f03a04020b0081c3c0000c0000041d0442c046440001041c1000c14440c034568405022280348005016206040185412105c06805580c4032540525118040d00c81d446c40340309801d0008070020020607402d800d407000b950201d441c040c070302820000079052824441d80541d980d10b88841e21603071107100411000c150200b044c0c4407146845203990600159500540030390f080b100c2240e0000368460203d074100b0070709081001490300d8a20202d0503894407040d00d04d401444003455001030040010286208010313413002800156043c80d00c1c540c941c01e42d4802d0351561880e054081103954074800152401000c1854400071070f03070740c078401810064800d07403243c0d200c0d5a54100500c045041303030040740c8860407010015032400d1410303070f00105210004010b181142190390b02092420784203d001e40e0040116400900003540c4a007425a1541c01c28800c0c01407800f650700803091054007600a8404413501702611 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 403547266 1250 403546016 403546019
    0x50108152404090f0605030d02030315090a02040b07030c021e0121020c0601030c030606050d02060904050a02040512100507170a111303060c080c040b040614070c080a15090b01 77
    0x2110150881e51501401d030100034080801c480415104000c841c091402c401309003035241a0030300d41070003c100c00d40c1302190010401c000140d40c480e42c1080b1206030503200e80d2560399070a015407001b80070710f4200c1109072000050190516078004800e000c07240c001c0320041d0140b0301e4040c0e81558502210081400303d0b140e00f1031420520003103051070b802100550005850300315252001414441e0907001294a00d052180c1401800800e00c601c0010b03100a845103094050700790005075003030241d0a85188610b441e100058099480380d01907600800d800381c20180c01a04c00c110107900ca00c03d0901c41655985450000349101d4452500801e14800b02d40c9641b80c59213aa1306000e01a000c588105089100d0030030640c29441c018003000e00046014417000103880c4040a002400400c001c2c100511180c4240400c1c4041c0403080c00305d82c100c0d92142000080302e4140700c00c0745603070b014402000d024160360700c40002d0001c2c0049003070003000b403140d20078048115009080c00106d602d2031030050f01c01d0003810700 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 403548516 1250 403547266 403547299
    0x280e03031c090501020409061e090c0507112b0b1003080a1209050601061205070801051315120b06091e060f1c0606050a0602010608030a1b080403030905010815 70
    0x20400b002c0c00b450004d0319142e110140c80b4183c0e030b0f15900020701c241c40d480d8a564089031620b07981001d08544c080c05d000d50400c4140c014064010080058034030191500d60805556448510b010b03485038051801c090a5012000c84c0b01080113034009480f14440b00c00042c0c8401d88203042c80741941d6015903101d06119001604a540921640e0031210541e50b9941c200017040080041500a1076070b96540c1900510f403910520a4440c054030100601c03a000b401400550b483c0c007884c04480c9040400059803034a2540f9804100c00c19a0003814400403901c0c841003400000d821140c811402910380340501d403200e0102c035081c01e0b204030107102c00c07411002c08078541d4503107100781030f5071740f54020080c1300c51030310072032004a403043c2c144012038100d9a6104104407509002c0d808500402e101c0c0001c00c45d491510380007030b03180e00c47c0c0c01c102820403400355608525100b6056003402210b42000e803050325280c0724600680142528015540403640f013400060707502c1000030700c11180d50805010310307103120b45151 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 403549766 1250 403548516 403548521
    0x1e08030322080c0604020a06020c0306010326040906061107060c17070b090c0f01090f0b0f0f0408010209041404121d030a0308150a08030f0f280e03031c 67
    0xca0907008826589030600215110708007801005070000701500036820240704001ca640706030f41c04507066400003c0e04030303c1d60303901040c0141165048a1103001d400e94843c64003003685c0c8580b01b060710984010402103180307002a80034506070f03455500d450610180e2655880d5849115204180c0005d104445400007e641c901e00f4840141082cbe01441c10056581e80d40d51201d03074102c0d01d080e26903018201c9002a0315060004202c2400282049007405080c80046c09000c126070007403200307030340e00090b40d41015403400c3c04680d148001303051059102c58854a40d02c1c040e60200440c203202d94181890f40b040310150070502030040d0384c400340080b031180000a081c1c503024480c00442c2015030440e004140a501c050000801c1ea51007503941c40030381c0c9880848038180070a0108000c0c000c0984880511000d800081143c12041d1403400450720b5078800355034103115100308042c9414042c0e40070319880581b90701521010481e00c403901c500b4400251802810703940c0c01800c05420b4005203c884c031008402455 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 403551016 1250 403549766 403549801
    0x90a0b0904060b0103091a04051209010c2006131503020f09040e1006090b0306011d01062a11030f0c010e040f09020604060509010f050406020c01080924011e080303 72
    0x1810301191401c6c0c07039105c00c0f42c803800e4a030840c0700d0070000d04200010424103001c00320f20120b08003a41410310422400081c00313004800002084810f04c0c00e0007580d540809012891101402090280d0f02d0b005281541d118031410b2052082000f000c43c001700b2440c0c00f134000da50590b000c0060080c10550840104000380c15181824421030055020178801c8039000d00904005c3d000000003c28950034035018180360210507800208008000e003040150340400344225130440d102d914002c90240c0441c030024080010710425a28051090f0000004105002c1ca41c5a10710404800791030341d51036030b0b0240030389488601907905d0000b401640d5000312071405178441070071b0b0901000c00141001c7c07160702042c20b0303900c00d03001400841c0000c05d4196440da030020b1801d01e8001985041400d251800c5000f96603070311a000c440e81441480400244a400f0820080442901c046a00010802d040080414665080c082c140440700c4450502e040914419000d00465442c0d50055245035254124501400000f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 403552266 1250 403551016 403551019
    0x9060207050114071509050115090207020901120c0905040506040c080a150c0201020d09051018050c100e1008070e0109060206160c12180f05061b031314090a0b0904060b 74
    0x501c81041010002445000b080d07d129000015440f503080710f9101200002e6070014107070b60f004201c5d5400585a040851781101c04001d04201d90480a01d40126451903035000050114038060030007050000c000761240c003480c0140a02c4070115251154640c0318420904080c14a102d40100380c40d225255510210000c5c441e0310006040c140001b15070800d85141620590711944180142c0000010a10071680c20040900c1c02c0e402c004200e41c0c8064440c0c0b00c2108003449194106c48014201340115200820210001c00c1c40c03a14040f810005014807106641c42030000e502054058015400381c50f820040d10311680080203942c1d2980c40d03040c1100c2c1100c22030b2080003000e0016034005503a962940541c0e1f25242c07558554800c01d10304020104001e81c3c00720035420b10b9042c040045444007811a104031161000443c61035042010b9140740d171007886008a14164144000105035528107910708141c0c07404c8071070b00280d86800304001c3c01e5401803040c4c20303403007440603010500060556001000d120f40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 403553516 1250 403552266 403552283
    0x7030e0a110f1008040b0f0910050a090f0f06060503031317031303080c060a15030201030203071e030b091008190501060e010e0a0e060114210f0d0906020705011407 72
    0x4410b00494118610342d20341401107001c220a200401044000207584031099800340f000c2c038505407261942da21501c84100884030b603510040341551202d0781010250640156040402c00e43c20726022040340c0c15600165040c1d498524007143c01d140200441d82d120500360a000d5034a8204603045602241d5403098540e42c0c03008200d02d4609040c0325010078011400340546944901c1d401e0350040c00c001008081c00c110320314145440c4640c0c602180074806407074080c82c0058407546c50507015076150b92980200701104100070200414194145c0181c1c1045800f035542074030307546483d907503010610f56a006003422504040724420a4025000c8410b0040e402640003003095a507680c000c44400000307030044600c0d03801d10400c1040500d005c0c01000da6040c4488020411980f4101014001c60440f01209104002480c81c14460f800a401011400400d8406884d10010840a26550340d1500010b0030301103540c04e28005080c90000c140d0744e00f11981a1600d9a006100c0c00c42a43d03650301802c1c08846620 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 403554766 1250 403553516 403553539
    0x1002010204080105040804081606050d0c0201022106030106050618220c0915020a0c061805091003030806030f07060804080d0e15090313170307171207030e0a11 70
    0x2424018140200e0140c1b071076541c1c03181011001410300c03440f004100c4140b0f107840b1040202590143c100d941c004580b80001508452569003240a84140d01004688025414402c500445c06e411164020513040700200048c036511824400c05000e0300383e41000c00c0c8800e8540d65841d0a183d00c220b6002e140d0303481058442031440e5881c5c1e0884600042201c0002c90035101804078401d0182e041045030011f00042c02280403568601c00e2105590107100704026105101c034501c4030322186490082d241c000c000c0b00040c50240c2102c0e0300c00000d0302c400e60001d000f5202060090a01064000c5100c0d6102d020786031880c1050030584415402070821112150104a00d9610402602c035a624522005016106c4c2c0d41c41d59083c007040e28009020711039550410400008041d019090303200c102c9202422889510f00aa01210b055000d0b00c10040c040d601c8281c5440200c00202c0000c00c10008291480030446d00c03141e90403011900c9101c036400d0a0751042e560b00c004113281b01c02d400020000144400f5606 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 403556016 1250 403554766 403554779
    0x60f120302071503150e0a050c07150c05091e13020901080f1b18010f0302030717040203030705060c070c0e0f1512010c030c020c030606011e1209080903061b091002010204 75
    0x10103650b8412107070fa41c0c0306c1040c000101d1190048a40000001d84072605011054580da11040e01401c0401743d020b070380c1c21400c0500740c060300035a0030040009280e1029094000382c04080301c0c104665091081468145081080b01d41c2c0c03099402044040c1d56144150741c6244441240d020090522001c0d080b854031205000e01e109402003441010781d181c4c00c00141940340c00586000c00680d1114180b41c0140104440c0562007580090545200c583c9003085449500200b4214070881d403020b40140912030801040c1560b0100402103e413140c00514075140c0d4034041c0e5024040c0507180410b50882d0000401c00034050302142c208220340080601c100a152024042d003190b82c42c0940380301180d1180c0040c206290184580326a203103003030700502014901000002d03c00840d0320100ea102c0c400030360703002d0361452045201906804c1042410011085903042c4269160401c50100d4402d1195100286159607811004440d59084901241c10f03c0040000c10120304414808402199424000010074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 403557266 1250 403556016 403556051
    0xb030f13020a06030905010b01321c0b090901090812150414072604031110050718150c030302090402070206181503070804060b0f0d0303060f120302071503 68
    0x1081e036520700042c509611b15105080d5020401c0031418004001c080b8501c00302c51484803000c0075282e45400c084131654071440203180c015007a01d04005444060500340044203035001d1502c100c011150041c0310303611640000e00741d9841e06001014114144021100907401e05912074022080100103102a0300010110707040314030001040700c49808220500c68565008100180e240c0c400760070400080448140e222801200600020100311941d00349401042c81404080c1c015914410144060304201e81d00070261030f150a01800000c20700c00c000204010b801401c803010306d02ca9100c400314901e003610140d000350000c00e65160029003c1103880d005a650300014010740b080100c80902d80b000a00070b00400d48800741c586000c00304100103001900350844d4006a000c5c1c0e0140005c9140300c2d20202151135078100110068100d82c03008840010550160414419030310181c0c05201300c01e40e559580346001c020428082d000d6000b032a018003107146130142149552906060100321403c110b01d00a01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 403558516 1250 403557266 403557269
    0x3200a0c080d0e0615010c11060f070b011d0a0216030e03160909060606080402181e070c0308060a0b2d191404030b01050405090f0303130218010b030f13020a 69
    0x100c41d0025000c1005881c40845410b070700f03003c00c2c40c207e0106e01d86541c401640084107100340d0302c164404078041c4c02c00110101182c0d4601c0c0d01c06100c0b842c6507500c404407001c190000d4240d801c2c000b10000080e8400031984291503102c0140c2c160200010380703c3d102541e81d0142c604c52035825019502c1d08803261360305154050000c2030800000503103008603060903401c0307403060381090081101240c18400903030350740c1c48007015052042c0b188074010b458520340d40142c071000113000781c1101440d03420814100e0f08071b17080b01c0c10300d4020780310780c0d229507561000c0100b80943e0b1300588110038010320258180c9051600080d014100081e401e1440e0a02c200032070701a50000d07070503055800150340760181c80e1035204000d95017101000c0d011906280c115034420060450501605001e2641c81d800281040c5007001004100d030340344810f4075501d040c1900c00046500c0301840c2640031f0054980140c9050480ba401a4103d48440c0040c500791b4072200c1035905480702c00707407050b00d2079145000c202e0090385c1c6440c42d07d030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 403559766 1250 403558516 403558541
    0xc03080c010e03310e0708180a030f080a06030503030a090201090806090c01020f0f060c0a031404140d021c03230a05010e13051e071e0603200a0c080d 66
    0x50130740b030801c0f024000401c201000c841082440003001160480c6035417580040f11303810401c1c09550764105a00c4074400f01e0440602d94450a030b1007605164100540c0c1910b46d035195512140d658030003407881c00b62146440002c10540c070030070008122140e240e0010b20602e10501d000c0700c80681e00c0c0c08991034090240c810660130f410040d1000a50342c0c0400c183c0c198010540c028042002ca10480582c890000504c1a00b28100009a2004d07451180c0e000350380e03041c40113100350302c02e0a19040c913100383c11a285076420140b10707400b1614840d03400018088103241c90008158161002c030002103001e0540e16040c1301350448101c9400f0710720480c0d41c1005102d0f00c0f000000003510742c9050242c0780c40b0880030f0001c02d1003144000c000c0000c6a0081100581200a03980389205804200081c519100030b90b4090101403107025840352407911001114403c603900350f6800c0c80525494001d01c2c240400204601414040401c80101c2d15809281030400d03160160340410f0403c0341003d070803030a903145c072003000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 403561016 1250 403559766 403559797
    0xf0703020d0920031614281406040b0304060908190f0f08130b1504060f03060f060b03011814070503060306010e0601050d0213080a1b0605070c03080c010e03 69
    0x900c1c0d000c030348070292040754000c078020200403051170204046461680526105d038034030410595855110140b85030300c0d1035100c10302044846040b654000c0e07501c410303002c0d0a00110b0002031040e030501d003c000b0b80b002d032507015004d68510349a42d56030400414007008215003044040c00f01d4404d2580502a2404880080e141c80d17403030041111008100c1741901d03150340203101883c0c040c051020181c0c00c10203a01580300000303041644816220b0711090300000b0380d0b10703031050410300045243c0d104d204910084074450032041c8180e4904401e0402550344502404140007014001041402c0442c46046da078408030201c0000d502c507010101003440142200e0b50b0340800d2001041c41142c3c101040803500501c425a000901e900740000002c0c00303031040d0060901d020f078010683c24150340400000c40024200d003c00c4400e44c4c0013034034003010303683c49000340c81e44a40514400014030074080c43c210740840358850710500b4441e080d81d50303510860b00040350b001000e6580d1006585c10640400003020981d0040702d80 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 403562266 1250 403561016 403561043
    0x30204020a05070b090a0305181201110c010e0105090c0d140d1d010825020c090703090302120c030d090812010f14030c10140d02041e1205060f0703020d09 68
    0x49000c04d400941140380c0c1360b102103980c5010175806425551141000c0c10140d60150060002449070a10ba007607515165290030180d48202d060040144110000040240030860401c0343c0142242d104880890031608061a1040a4584040f4080d13101d03100c0c4030010405525000004c1c503080403002c0100100d41d23900b21500d81100030440700c0044460918091b4810300d0031500b550183d80a1030003a200328500364802c5401a030003400712880704040a8041541c41ca0310072001000391403070400540c00360142000048000c074503002126003024510340117510f024101e45602008210541003503407101030510810b01441d081d4070100c3e000b0032a000007000d02604043c0384544183c15070311b045200381d0000307500800a4440c214103a159810a040901140000c503403500c203207100d149036203408244002030200d103900d0784245603501c14004040d81600c0315229290f2140d03144c001c807400b900e1684081d00042c3c40c03810b9a54003076070000c030b1842c01505080302810118181ca405003401c540c01403e43e02c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 403563516 1250 403562266 403562273
    0x6060f040e01141f050306060702150a1106012106060e07021b0f0d060b010302040e0f0403090b0703050d11040518150a1a250f140d27030204020a0507 66
    0x1841c840f2400708540b41202485810b151500b800d20340500c400074068040006149561200c0030307542d042d83c0240404590901800b50072200c1d5201d141c3d9440402c500c40210001d000d00054014140c0740701e954606a4028241e1411401f5111807004079403080d15040003081d40521481414003407600c80c1c005140081c495014054038821b41c080c664065030250b880034896130344a4071103080c240c2e080b8800107806c9aa040048010f072003940c000728941c2c80f6a4042c48602d00705481c21500c200e0003652010782d61031329448a04290b00c0b45000250000700141305542040200d42d11003404412b070740d02d0b01440e041d03a91010400643c20301c100c00e03d141503420108084440c0803042250401401c0700c1044449003001c000601400d44020500e0121001003201c2600c0c0714001d56000e82500b032200807820b243c840f40341103800c074403000d201244d000c140e0a803031044c0d0032000500c035421000f0300d4540d91000c1d084140800c22400702d00342d140260580c909800009038441d0310042c0200c4078699074240c0c9e42c025604 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 403564766 1250 403563516 403563539
    0x10050d050a1a060a03081605070b03090105010e0606030c0a0c050d020106140316060f121b0e0906090106140f040e160507050304090b0607060e07061205100e06060f040e01 75
    0x800d024034240702e00c0b082109030344c0c5544e104400d6a0b0300034140b1f40c48042459a9041160524100510611405101140356181840a0b620800e2590020b00c0b5680e26150020805070043c0e82c003d40050061001c074681d40368060180295111a207030031180e68200741c8a161401d88282d0036080543d650b0101404411641c2c0e20750300e002c0400350f0080218074141340c0d170b80566612901c42c43c010007201204010017984510500300010040040074021000030148180ca8101c0142041010401f80e095070005c40c10f180c1400307071080354001e11a07109a881e040080c2c8404164495403068a5410804900b50b00303401d1000d400545000d03804da030344618111000b0042e050154800c2d00c1805828085a00000c20000884060340c6e0750f08404500041b0400c085180c902852100805440c1800c010107a03c2000150000c1200c0342c954845d6042154080d1143c04c80308103550b0281c0101d13180106100d0181100345040e000030020348800d1600c2400701c0c10b24065041341d0882115004403000401400302c465 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 403566016 1250 403564766 403564793
    0x7020301063803040f14030a0201060f05030d080609090a02060708090a06020718020a050f16060c03270503070813290a0e031204030b0406050a0b011710050d050a 71
    0x311040300c480da05180d00440c2d0790000410050055051041000800000021074150808454222038481300301c10310281c041c2885001c0c40052440d8004006420300e000075070003030504010303141c1c500300d92181c0050014034034004154501600c1200003400c01a2591002020114080d114007601d400084040113001010303603112104560040134240a142c000380d229503a040000e032401a030f07400b11607400340c03103a00500300e00c2c400c001000300b030045c260030b000604401d0b42e41c4a0070003001100021002074080303034141082a030303e010b02d10f07458102403443d000c1001c02c554020412681848510b0703aa00340203520180d0088406100304004000060864cc1400c044800c21440701034030740a01400c1c0401c9015003152081042003d0140080c242c50038000d03031a40a0b20114190355580d100d007820450020b05850885032140f0303103000200d2540b070302e1081c1c148240b0140d6035402900415203519550483c0601149030a80a60000062640d201500844030b184603102900e6519018203200f00c080250 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 403567266 1250 403566016 403566089
    0x1b03060a0509100c031803110709020f090d0f0803090321070e010807140301090b13020408030906030c0d0606030c031404020a05010f0507141c050a020a060906020702030106 76
    0x209018012804400f188103001c1c1c050b5180002444907002904801038181c00d681043e03c3d043d041514014558170140211031215a036003111146075840b04035104030300c590b61504818040a00c800e0b080c41c42c08104000e42c0d43d02451003844501078644a01045030b00c1520107002a5000146e280c02c4407041c2402c0c10803124070b503902904c0a1600741405402d2035041d0f00201d04001460700001c03546401202000c940590310203c441e101d41e15085054000c1041980c0036100d010721101c8030300d14030042e00849084e1500c80d4003071414004801c040c03000941001e00314066800c414042c1c84007100c91882180700606960b5800325200494690140441c1d0400c4902c0e207501950741c04000142c0c4420500318201e032400e02c1c00c000070315000c80307040310030380580300c002000da941a90104081c1d020002da103141c60b043c0ad600141800241c00e41c00d50b010320440c40518056001000c80c40c02280856005402140c011400940381a81c503030300181c215080340d0000e01c001c1640c9d00900004811003d01c48075040314 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 403568516 1250 403567266 403567271
    0x50313120506090303070c11040f0509030a0207050916050c0f030705010209040b060315090a0e0f07080c010f090b07081902010f05090304050135040807060c030b09271b03060a 77
    0x8003454004c03c47d20040714040c21012060780c0e50703c50358032160f0043c500c0e5002000c0800450405548294495006c2c0742c2a00051080c900c011509150000361607000c0c061385801b0514828640c5070a440b031781c0001c0c901304094018101c140d0300840c0d040c0014075085120750001a5100703446c0d81008120358280c00107600030740c1d0500030010095820b083c01925448122080285565881105009046001c40101642c06280303a0310003940c40000d0001c00340c50425007640e80c480240b1004503a19550b020840000602c103540800c2140f42000003819264005ca0300c291406c0320088102c002254010006001070f0f5466408140082c841d110302c81c2c20407040d001862a15240100003044c0e03c1503050b803c20302c2d281244590032510390354140741e0200c1903070703002900301450a03040c55034490b00800410340c2c0040c10100700b100c07014840d2081c10141c030070040440c07046031914000c0044004203100307001c80c42c0e2141003030000703801010007200a406c400c011030215880c02d210140340c1400700107042016100d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 403569766 1250 403568516 403568521
    0xf03020c030919050a0806160e0603070c03090f0b0307090f18110405040c020a030e0108011d0703061a1c0507050a050d060b16032003030a0207050313120506090303 72
    0xd00c00320440708040e0044401a15042810745a00c070040302d03e5002540c05181120006035006020613060312072648181004068510040151040c040304141c00754411130400000b04150300a09200d6100d41c0a880c0602c2d107243c44050b0b4801a11990f0440d43c1401b4000c0108001d03198080054005404848a400c408034506101d01074200c40200242071180d44900c000000003800030155002494010420b00c400c0340c107000c010791224140310b01500015000c040c84c01d41540100410790403101c0030303141100020f400e110006095280640714404240d19048001011402d1009001e4403480941e10300e9682c410350042e00e444121014103440c84503041004000303401c3d80000c01c0d90039150701da003001a500c414805590008040a0b08600d240740004221040d40c26a110040c92706a8031944810108050701c0741d0940c0ca00410001850007940100009003640c0c10540140120504c518110303800e0850051102004000603000300102d9031010154500380300c000c11485412500150240d482c2d070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 403571016 1250 403569766 403569787
    0xd02030f0a1b02031804020c070e010302100c02060307050304051009060b030d0c080a0e12010509030310080a020d1514040b040c06081306090f060218030106090b031009060b0307060c030f0302 84
    0x90007440031140c0302210180200345c039a02c1d10303011594840342c02402c0d21030094075000840030065003800145d003c0c0c0e0781401c2c48454580036200314064950000c003444d0860707a81c0001107480f030b800103004651500802580c486c00c0c410768000c501045110700d202082110b0b01030107141c42c0c04011200502007144c2091814041114a011104514a03c0c0341610320700c48000e0100c2c140301c1c01600e5080066203090300f0044031b42004000345001d5210010080c2161381d0355610a5541c00445101950202c0c0d00703040000003891050101090030030710900814002101900c40a03c00703021101520020203031010041000710010740000940402c0c01c0c40750041c00c00e0400410100750042000340941d58881074502071001c503803040c4068a40c016029942c0d0b500251a9042410700300c6441402507007061707404580d200d4076002d0780e5505900074000348118030032405c10102034176180ca0305076555561250040b116481c10b103d10b0300900202d8983c640003078030514005008911108140c0308041c418420303640307603 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 403572266 1250 403571016 403571023
    0x140706030c02121b1218010206011a1804061203020307050610121101020a0602041502012d0b0d061d0715050409051005031f0f090807080f0d02030f0a1b02 68
    0x1030b20030151a42c51303001a4102e480d1401040d00348181c0d81e0400441c07280c0450080400360052098280d094403210b90b45c034403440e9103100380b803075071581803e00c00d1150812041002c4e26840340100c00820108000b80c2d11f81e4146150401e000c025001070300300086003070038070804014080c4c0081c0114840e640952078224512038604204800030008070040d420801e0aa10030090118180d82040045541c0d50f56a0300070101c40e0180300c1280099424503d90180c200f003890800b001d2150750858401d903480d10690003000404c2204089503100c85108000c1010036090700c1034544854000040c6903d442c40201241e00d0600d056202c90300e1030741024284c080295001c0180c0b8202d035502c00012070291640c3c203552000c0c0032580c000303542620403050f01d4400205034940e88011480c151004000d000e00b1110400d05545040300040c10b500000c2004200003141c80000f49001d01c900c002c1c260511800d001208142c1e4000d480d08040741c0c8415050102e044003603c2810107280c80001010000e003d0907402945 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 403573516 1250 403572266 403572277
    0xe0a17070b030103022b05061006080f04030203180103020d240b0f090f03011b020616020c0d1101050c030307170a09050d050310120503040914131e140706030c0212 72
    0x8414421b64000d0f0810f4641050344507607400360a0b20141c0c5040303020b0b603400098500c070300c000040001c0c010070550460440d1840c062038140d800740d844c0c2850385154600c00713150305c0f25460405500b0450343d404071886109103008a8455002c6195400c07481071914072034080c41c1c00542c0608000c200e11b40078155808200d4042d450103644100c88600300c60000384c0140408140940b242c4101c4c48031401203607010545601c103003603442d00b00c01644540d03c001c0f42c1d80c5c004080e246030440342144144020070070400c2210402501490706a01d0241c0d5900030506680040d80c2881c0441c204440540d0a401200e03860b0ba070241d000d010400c5030840781e0300d07840e1759001400e2110f001d00c1400030215000c90180003580c00900320000103071084041c0c920f0996a43c0d0b00c01d22600700c071319142404103210303c000e400d0414060510f0b000201d20341c4a2589610145540c0c0c952031102d0380c0110700d0a40c0001d41c4120b05178055945001c060210240781000180a17601141c04900464002c2d02c1c40108040c8000240c60 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 403574766 1250 403573516 403573549
    0x609071b0f06180605010501120e1b042c0c09130204050a1104030b190e07270c0519030b0d0b06040905010e0a060c050301050a150e0a17070b03010302 66
    0x401c403424034181007008140440c508088250504203440c18401c41da04a01d0407110b007030740c54003030b41d18102d4640301c2161461a4941300a4104280f0740c000940c40c89000c030100700c0000c00c0040d412811025241802001c1c41071101c3d501540381500e000102c081c0000070b89410280d0300789040d4a49284d0002034070a40100080c0305544c1c450110b8030103110b903070084000320314030400b5603500e98482c00c1c01d0007040001c849641e80c900d492004030074041558014044600901c9004013040c40c18150800d01448a0700031141406085546405240042e03010341202811a038982e40d548041140500e82407800c031441c2c1500341420254a41e40a4450b40d0407034450741d411680194090700c036100010081c18140c1c8000d01298209203c40c0c15903140451202c0c020751240034200403900380944150b032240001d201d820b500c2541c0280070070841c0100300c0c4d00ba1808034140b402d1055008030f800020b10b106416000700a11021468190b11060340c1000800060030315100d0140c150343c5554001201034002a0817030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 403576016 1250 403574766 403574783
    0x510080a0c180810060b07081e1611030d09050f010c05070b1b06160c03030b0f090a0203091204030c062102070b0604051617150301090503030609071b 66
    0x1050880c4a01c1c14101d504569001d8041c00b203540344503042c0e882d44422000142e940c586100010824110800c03134107103da00c480e040c5e00342800c070383c080300b2500d0b1400740242c1c0d00d80040100243c1030415600039a2035600c9441181a258900340625140015030f00840c0c040c844810340500096481e6111841440b900f441c0c101a000e0440c901a410035103181c1c44052200d00100d6000b010704d81e428401020144c20300102c902d0b44d60f580b14007500300c3e054480d002e1701080c001d054040111380309400840c034141016088807800c080000200f00c0c10729003112005e010b0381d404000d0005d10b2406200400e41403004105c0c5505060950b181c140d441c00aa104920a00c4011305c0501c0c841e04402180f8001c10500d84411919005d0303a00b050b0241000440f20b0300d100303904d0b140011301c200104002c3c1090321401940c1300c00c040b400400b00030440e07010144c091000c00611100b4040c0a41d024000c8c03501e16440755000e5500c2e420701c03c040c03060b00b0740f010b0022030034041d002c0c518502c0000c10501e00c00030103800c0b4202 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 403577266 1250 403576016 403576031
    0x60a02030f06121f090b01090b0117010605030714040825060f02031b0f0304080705010807170610020f011503060e0a03081902070206072103021c021e03070207030c0510080a 76
    0x3424020080d00c2001003c036840f0800005440d03c062740413206a20084c0c03115503145401e400c0c030210740003090003894041802031021403980b0344100d0500b03100300c02e1a98581d113044e8840310124980740310301001a0080041031400d019280350300f03846c00010046420440c0301c040c0d110320081e48900900031034070a5403a03c0000c180c0140c0702005590103266009080e20f94403519034086030b84a03103003400b525002c0344500b404202118812045001040400e014441850b241c20301080800340d076555030582140702e403084103520b40c03c0a00c25080842c0c8054405034200b03180d85091070590b151445243c0d400c2e00415908404070760040d445c141d001002406c119141c1482925800003030003056400b94000402140b9030081000c0d07503410314003000d160810451042d54911080f81a80b2455185c0e062000400085040d03480050300076000000c0040126865400e00d43c07004e000c81d4004684150040c1d001803010014411080e01002c00740809070349018030540c00c0748000c3e01c803800107401030059990340c284 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 403578516 1250 403577266 403577323
    0x7110712050303063102032214011104120311010b0406090b13063503031608060f03030a0c111302031608040206040317070c06030b01020d110703020603040c08060a02030f0612 77
    0xa0201d0383d00e00c9520202e1602d403236051401030900d510210308040d40c85d1207090500c091092066504803440c1e00100c00454280ea5012600900c4074030b0744c0c09296485801c400040da4a50054201420070f206000502a044008103d90302081103500000302c1d00c0d244082c4800c40044014945e14521010003540381068844101040070001c60740c0381c024007001c030500840180d00141c1d103e81c030341981e803840c14944840d002c1210f0507000151050b8503500402485065501810010b0b00c168001d107140c41d1108032090100d41c500d003e4201c1c00070305a84c0001003190300c00f14080c248490a5040c64a2011442e0960200b166486a400050300b25131541818980f0b88001e1401c603040c1d0b651100142805558440c401f030054012840301c3c5000d400343c014a820b4840c030405541803190b502200070007445185400b84000d41d8005001034954030514407000c50400c904121030b41c06411605030050341c910300081c5100841901804a622800070510a290903010000300180d04103038000000303020761074411 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 403579766 1250 403578516 403578541
    0x80c0319050909010914010e0c04181d0d1b0f1a01050306090c01020307120e0d0503030a0b090402090412050904090302061f0b030711071205030306310203 68
    0x1a0380444044029103001080d400000790603590410b0301d040e2101e98a460030041520f2040d00140541856480100015000ca1820307a400401c044050351815481c0d0440d5003d0540c01807402440382d4548011404050032401900c0c000710002c40586000b6040c0500148004104d4080c0c100d80e083c0303c0307900018414003500c00107580e40d001c00d22402608000d281d07440c1c4e10009100700c0b4885c0c01050001505010042444420b50105a01035442c01d0001e41d50101c001030803401c3c034800c00c00d045d0034032079098460041545440e801071006688920f040f04030700081d1025000968011554901448010b80301d400019030056401500760070603041c500400c5407103000348154650300605080a0304189900450b502d0300a4100c50144a9050001046030007441080c5c17180c0408008100006220148a045102c030000000401d5481c102c0d030396a100b11034000b4401054a41d42c0001003844040c0c6410641c090000d4100e51b0018083e00540a00707107070303054400540741c1c0d5442e000070000301c0300c15001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 403581016 1250 403579766 403579777
    0x1009080a030e0307051e2b0b0a0b06040f1703040515071b0f0806060d080306010f0507080f0d0b03122203050105070306180203040c03030c050328020c061303080c03 72
    0x181004a207221940001c0d5410204d22111038020225000b1011072440307080400f40a0184081f0304600d800240e9540c5401c3d130328003d000da94100d5440c1c00825150303480308010b00c0201024214041032505040303d1480c05a8044040c2a071680100010802c588440e004281d06504000050762541c8030380c01c02d81d00242c04d504014820020f40f100103d1030b219990191429101c8550480320b0b00d0303071442e09000c20308084540245c0a01001d100250096108843e400e070350344000c3c9801820002c1d00c1e903a2240d1604240b00d81d05d43c60002056962240d812446040315424044004001d0480ca203400e40e42140f14010049800d52900c1c0100c3c4100c1c0c00800390000219449002048640751009008004203041e0003503001610810151044e04011802564025600881c032000d0700d51640d501650403240d10314089556000038021440082d820b40300c5a02c003032280113401c1c20b0a2050403002070419101c1c0308894407030102800424a8854600e07201c0c000d6030f40c403c01a0f03580d8a20b05201c02d01e9030103030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 403582266 1250 403581016 403581019
    0x103080304030516120e0103060e060603091f0f0b0d0f061a0d08030601030c051c0f1404050c030601050a0b030105090604090c060207030b150f01140919051009080a030e030705 77
    0x1401c013000b0003841d000003080200d075503683e00d20328240302001101500c500b44901c02003861408042043e914140c401190400d0410741101c0311040e2009082c2c02c07810920304004686540d45810b6001883e09000d462240c2c4811601c030501001a031340c842c45a50340c1502c006d041c0d80d58400c404065644074060621031040014814030701d6001c02d01d003802c3c540d4003c485190010b810480040b00c601d01403020b071203004003a0701c40d1140004003114507100802ca400110320540b43c40f0032110a003003c0c0401c2c150702407400380010740f44101290003031500c0c2ca64181d002a010300c60012007040f450998400f030f0780c11340c0c07003c50700c071202902d80c000040c001c0c0c011050301402e03102d80c28000083d1070f60000784d2403084034424113198889a8070248030810315000c900401d6001000903088840c01e600c50a00d41100301c1c0c060010307500f000c0c211004955407a07522111455070ba6590b00c42800641b41141c0c3c0c00300c0c9030380746207045886107046c62511070702d07010440d00007401d000005c405840160b40038010040a0b040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 403583516 1250 403582266 403582297
    0x7050306010f201509010c0810151205090c030705030c010f03090c05060c0d030b10051c0906060f03021306051c030207090203191b0e0f040b030d0804050610050901030803040305 78
    0x842e00713041031051209444091042d864100d61145460003596141e01c19100d01d10380a0002d480c5c1500104850090180541000704081c4c0250882c2c1091040c2c0f8001d02e045001410038010b40c00a05207000c409810062084c0e005080b145002d82c3e000c5a03103150030107689404240384400d441d01d0105502c240d081664489800300c0c3e060341d031620005404c890741d20596014446800e100c800d102e04024680b5441c0005201003005155200074800f40805a00c50f4450004d000f02154035040100c4101d90415440981c54841c100154503201c8600e0684000301c2000b007021a2a100001d4080300c5003c01c0d8580001801b50494141802800b4803801481c440034259581c0c90b0000c8400150100ea002e80041c480c513010090b10070400c00d54001d1100700d0240c68000480340c1040070088900e501590095207c0e0704e1f00420405a2024001076400c0603580e11900071604051811030b0809a00404102c101000700c41300700003031368601501d00d04403900700141517a80d48584c1800c071580e01c62209080746000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 403584766 1250 403583516 403583533
    0x929121e0c030d0c02060f0315030a20060c031602060d1407090603150603050a0f021305090105061204060504020109030b0f010f060203040e0a0e010e0d08090607050306010f20 77
    0x24042041d4402007011400c0e01c282122640098034091501d92000e50445018880100e541c80f59000440d040020100901c05840310307900002d240201440d01214040079204241d13070400350200500c070112600700c803a14201b010b024034035913903401b4459980d03d814a80e210003405540380c010480381c655207004028004400f00c0c0c80a2000d00400765111000280c83c0c80c00019490700ca445104585141460b0410b403061410504074081d1001600c0702c1042035448000040d11400c910090441242d04407055080034900020030010600c16072001c0c1c0207810030800c4040003000b054041e540700354081c6001610392602d0004844015480c0c00080011039000701748000c001207841150b041b40c800b24810b540075a25140c0803600d90040b40314503601c91500501041031603034541c111004103041a00001161105140380502e814000c0d100d200106000b00d081c0700c0020428019158001c0d00f5007400c900c4c508142e00000c004514050041003044200c082d010b0701200340d04c030b00403000c0078210108e502d0b0b070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 403586016 1250 403584766 403584823
    0x1b090408070b3c040b04021f02060f060a03051002032503090b09161208070803160306050a050f0603090a2a080105010e070c08130609092912 62
    0x903103040c1000607020003416522003058814128000c0f0564402034031460707880700d5403030a40402000d001240d101c002a82c2c6d15880c3c40d005ea10a802c10012507005004a080081004600240140c0010700480742200288041103000411455038140c03c030b0016601d950700f40b00540c04940c09900b80c0b00002040d000c0a0303000c0d501d03401c104102409058108510b03110044c0061344c1d00c0f00120926148a6201010007906100b5540c9202041c040c850581c42d08450303680e982c03102c0c0d00459401e9540820481d144504c03d5061040c000582010784108030010705250000d812064070300d0996111303400c008001050603406000002e46251b00c50b40f1900110b00b8007000c04d85c204d800c0220700e01f01440180c000160705105006450499041101002040d29140b0003110401c083c95400d80d0780c40410804040d00c0300c030880106c002003c85507181151541400080e905954441c1e0b250300800a650f00081c4901c103101840f280440e000300c501004002c0b41c2c50003181000c200c4943c07601880d08001c840440d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 403587266 1250 403586016 403586041
    0x10b0a05130b0c061807050f01021002032d0c0d050a0b031b01030e070b040e070c0b010e27070513090b01030609140303010617101815081b090408070b 66
    0x50350001c000e9800c3c6a41762519035440d00ba94041688a9034020b110801090400051200d07820390306105403007800c940240a48140d0703000381c404901c9400c0c03007209009810050300004000120031000e0911505285150b107406004513160716410035511030100c0c41c821019401004450070140c2a64090b620400400078000301400d411400b080c00c01e00003003112680412a0425580c03266a000e08240c00c01407001c441d40e40050520003407190540504010900350103409000340101990f03c034441c68004c0b07500515022007810346141d41e03001c84101010b294007044440545005075207070b180d280f09162a12018140103403010380380c00c200b100003206001d6180c002c0c42c00540140d0311407007401d01c0130803403130354a100c244100c8001034400c0b0820610f84202402c51030f0044906c02c0c001680544441d02c841d92040100410308203142e803600e504602583d901c000c20003c000003400303031481c403072490140180d010103660894401d070800c13800142080307107603c251800c8a422840c903882c58500161510709 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 403588516 1250 403587266 403587277
    0x50a0609060f03020d080a0c05030c1c0905221b020a2132120405010b01030b180903160c080705272e061b0b010b0a05130b 54
    0x4149040a90101e8440301c190144421030740d000e00f410044282644411b502900500442000c0155075400c41c0003042d41080581414034004002c2e180c40c2124120f807004510b8001c80752410703c896494100030541d207910124038600014000c40e00c1507240b91900d1001081112030144120030015442c050250340083c0c03c00701284604001c1282c8207103035921000309140c201d013020000d900b442d940e641c204500c290b01e90307012200945c110351403501c48450010700c0c0c0250707559070b00300760020041005202c0c003401911400c09080c241001107600600206d076642c200046542081103404001c14070381c0204204a0312214020181418510b0703141c98445a4030502d8801c00e17410b4400c80001289c14640003d40304d102c855014001549200040e6580c6a00c0c000104040c0c00e480800046014072241c42400d144002c480011001c811800d00902400710903000ca21110481c00b4462004001804c01c60603a0549484061458039a41c6e2041c0c03c4859215400f800d01c0342540c00d440001c0d0440d40e9101400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 403589766 1250 403588516 403588529
    0x1032901090b191b0519060506090115030902011e270b09151c0204180e0c010e1522050303071112030706091223041512050a06 56
    0x989140c1d680c455416034050286102c00240c00a500f4038442c6004900781a40f406003210324051a030390549038942800d41c8403003090214018030203c10b0400c0b005114940d48040308035100c4645505042c07100a650041091520074142e4600c0c101055a01600503004004c06007035a51342c5514500c40010420304542c22084480c6408031081d9603a020203e404400707071034200c84094200f11081082004080009000c0c4900c0300d401c2009207c1c204000d1181050f941c541203000d60383c2c610f0719402c0800030304413184201c00d05103000b040c188000000324650284213824078102c04840030749800900c03464807100004040b07040006144465840d6550510722181552141b1241310359100f051640702e1203807800003030024000325119403940ca821a03422030b10741c0d0140102c0b410080d07503544480403990100d006071024004100140044d6034410700e000d4064124143d07480a1211b024400e4583d0300840c096030601c0303d81460396002c900e1003400c0b4002003480e20f9005001ca4203105001c1d41c0144810701615 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 403591016 1250 403589766 403589777
    0xe0109031b050d050703140309061f0f0e1008060f090d0c02030303160e27090102120a02030a0902060d050f070e01020a03050915040b0d0c080103150b01032901 70
    0x207921085081c035078403040c1d03400c10042c014000d500344040301c1d0782d8403240086062217800d001d09400d9401d10805944641d0310140240308030709115031000781030030104403010301c10610a02d041c00729514450703500c01100c9106c00010360580340c1421044d014030302500001d8070361050398100104054880c00003401900c0c910300b558428600107100b00c4480e58000d0380a034150b4001c1010800a420900000a8445a41c0b50a4912680d10f41c00100382c032110340c1c0d054445c1d0b5400d26400340848a4159620b401000c00c0c0000c610b0000110345e403900c6020000c0c0414643d540c0800002c421102c1c036040000c103203900030b10302a5030f03c92000d40c4c0d80017400c1c2030b1801c580003050240060b4007a8012801d052644405800070180000955400c444944c0100521600040c03441c0d64540d10503203044c0039101800c290240c803a10b50f07071811040ba0031659582091810070061100400118030300c1114281896094240480c03541e41e01401a005804410403081d00303051100c00c0380102555018240d01c480c0001da860 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 403592266 1250 403591016 403591037
    0x714061905010605090607031e0c0204150f03170d09030504151d0d140f010c080a0902130c0314010f0602070608090d03050709170601091b0f03020f04090e010903 71
    0x80741e40c00d0180b0b20204030200200e0106182c1403002c0c1404522031725160034182103400b904050708045040000100c2d040400020451800d4050302e000e040342841c0300c5200c07a20b01241e216004a6504c00a0540401854200c0443da0302d5803c8071000c040d008000e00c450402da207001001070380300344079001d500700c04d040045460358172400c9400841c4008401c45425120294100411000c2c00300b0101c0d92407480c1c401c0003041010a2051211f0603804000000b50041c451201401545000f81151003a5240c170540000680d903c4444010540089000081d8550f03071850a60042810101c410301190701c6c00d000252034072020000d0801d40e200baa00f9182c89565551090b105440203071400c240540101c80f050103060f21aa03c5942c1c419078034505035888070360381c5000a1410f519005005141d40100b40180304e0325002e400760490301500b0850008409100100040034201c845110b10101354000800102c0d4291040175600900700d211410060b00c0d2001d4106d80c0242125107040f804074890910717 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 403593516 1250 403592266 403592311
    0x717070c17071a1e130605011719060b060c010c020106050d110909010b06070506011a03010605071407210b130206041419120b01080f071802071406 65
    0xc0c0c1e41103550140350030343e094403001e444a800310001805402d040000c00c21040f003003403003070445501402000600c1440d10a00e410840260303407058002d9240b54543d0040700f16008000100c2c614041240c1c1428850148149002d0b4068002426840d034031040218090070021810340c442c45040790a500204180da680f0b0080c400c0d24550700002401138505106200018285980003980c03103001b00e400002c02529a00005055070042e010940e0a40d00c230b0301c01484240680340c0701a03880d0030720000b160304542c94818018814030070441c00a0000e12007484035100160208814405080d10034100340101d00e031001c0455804c000c0e10b0042d54003c0e5120046181a209804c80709662500641154a01070604e10300e041c003607150414090700481494848959002c00f516200082c0800d1062706144440d0744c240345458441c103030091200707600842500200352200003a100c040341c00c0c049071a0b54007407428054100901600340040c000e012200102024500003103110791140c0442c2c05c484209001440 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 403594766 1250 403593516 403593563
    0x5031008061308130506041d0a06031e0615060c0b0f0105010903020114090402030c0c0607080f0117250e1509040b1f2603210717070c 59
    0x16441c0e0590100c10b140203010455601c01000308440210750001000d0b610700c0400c0d000c3e485540407440d51210401900300c00021602038031703003040c51440d007840784074250b03190340304220008005003c06800d003016000400c0090f401019541500714a0b0044142d5200405040041c0a94045070341e101e000e4001a042d100e590482c0781a50810f0f510144420308540c01074580300007910034100c05010a000d810f00b01d40c2c480c001140b055030b10a0955440b16030060040b4170740000a08100140302100e000c12444c10402070380241110808810305640505000d0a14205801010001050301d0094101050248085054421254802c3c14800300380e503901119400407203503069480c0e000e1442d2022802080d0001d40550700f20750900c00d420001140d0400c41950450304d60b2020786022080c00901c41c0c3e05200728000141186103002842c64518413a00311103802801100761f030300130302808010461451250030110b280c04181404042e444c1080c0e00d0103054040c00d220308a070000003203144408101d0862 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 403596016 1250 403594766 403594771
    0x16061b090f030b01030204021e0a050a090602060615090a0b270a0f060e0103020c03180301150302210c0d05010b0f04060e0a0f0e010c030b0f030a120c11100503100806 73
    0x141c24402070342181e00b00000313584180b101030321882039500c0001e072241100002b0800e50140d6103950f075035a80302c50000b800c0c2141d01d510540940d04400f003003120648903c0e0117400b03050071004800b541e41074400001004072046801140c01d90601240756203102c0907240888405101100b240400000e2500030810240500d02400d64040e403591020007041380542c03903050341c5210505002d800c080d481c84c2030710f2440e0440030070611003c00806024045080c02c0c442c041010020504e0707850740604640204000304070007400070b0703459040760110085418051020b8124440d000b403000e0aa00402e04143d406050391400d5188a692a072481c001d49291502c00d0000300c900c03840414000d507441c100354000500707401900c1d610840d11500403890483c800c1c494125102541d880014015442034240940711003d413800780e0003503204002040100c5d1407040c14840080091400c90070340c001c00d02e0000421014601969040030560342d00001180d040700145110b03101d03020788074405940e20300c8030a0740c40d44113 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 403597122 1106 403596016 403596023
    0xf0c0506030a1a0316030206030903090a1e0e0412110c030105270a02090f04140d0503090c012d02030c060106050307020f0309060f16061b090f03 64
    0x420f614070040e090a9004010400c00d0000048a0186070f02001e0320500001c000503407810402c00c104c4090702d00150404001c1d59549403c0c0511125201d502c04040072221703c049001212016400d101e84c1c1c001003030008d20070410303509417000e2068441080c1e0300e01034001541656203090250900032115140c61010048448640003c403000545c04030b0021340081c020403026a6503070003e070740c008003d25441d400e81d4a40c0d00e00300c0000d01e227804c040036a07030058107000a03941c3c0d04480503510071040380c03095400981144004443c1c01d808408021400e801072210f5001108000e1100c0c00d250881e070040701d24064183c00803500d001c1090b44140005000081084040c1d40d040c031840008851000c0110305110000380040c11070300548448a00f40200800e211141148840d00d0915944d0844010046041e80c10010307100d56031105101008180203d10025078490203c081e031084942 = true := by decide +kernel

theorem cover : BRFrame.Cov 403417266 403597122 := by
  have h0 := BRFrame.cov_init 403417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 403417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 403417266 ≤ n) (h2 : n < 403597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
